"""
ICAM VOILE : moteur de recherche d'entreprises et d'emails (tourne sur GitHub Actions, 24/7)

Sources combinées, dans cet ordre :
  1. Wikidata        : entreprises françaises avec site officiel (Hauts-de-France puis France). Gratuit, sans clé.
  2. API gouv        : recherche-entreprises.api.gouv.fr (entreprises actives, 50+ salariés, par département et secteur).
                       L'IA Groq retrouve leur site, puis le script vérifie que le site parle bien de l'entreprise.
  3. IA Groq         : brainstorming par secteur quand les deux autres sources ne suffisent pas.

Pour chaque entreprise : visite du site (accueil + pages contact / mentions légales / presse / partenariat / recrutement),
extraction des emails publiés (y compris emails "protégés" Cloudflare et écritures [at]). Max 5 par entreprise.
Résultats écrits dans le Google Sheet (onglets Entreprises, Contacts, Etat). Le Google Apps Script crée ensuite les brouillons.

Les logs GitHub d'un dépôt public sont visibles : le script n'y affiche que des compteurs, jamais d'emails.
"""

import html
import json
import os
import random
import re
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from urllib.parse import urljoin, urlparse

import gspread
import requests
from google.oauth2.service_account import Credentials

# ---------------------------------------------------------------- configuration

SHEET_ID = os.environ["SHEET_ID"]
GROQ_KEY = os.environ.get("GROQ_KEY", "")
SA_INFO = json.loads(os.environ["GOOGLE_SA_JSON"])
BUDGET_S = int(os.environ.get("BUDGET_MIN", "52")) * 60
GUESS_GENERIC = os.environ.get("GUESS_GENERIC", "0") == "1"  # contact@domaine si rien trouvé (risque de rebond)
GROQ_MODEL = os.environ.get("GROQ_MODEL", "llama-3.3-70b-versatile")

MAX_PER_COMPANY = 5
WORKERS = 16
BOT_UA = "IcamVoileBot/1.0 (+https://icam-voile-lille.netlify.app/)"
BROWSER_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")

COMP_HEAD = ["Entreprise", "Domaine", "Secteur", "Cible", "Statut", "Ajout le"]
CONT_HEAD = ["Entreprise", "Domaine", "Email", "Prénom", "Cible", "Statut",
             "DraftId", "ThreadId", "Envoyé le", "Relancé le", "Source"]

# Wikidata : types "entreprise" les plus courants
WD_TYPES = "wd:Q4830453 wd:Q6881511 wd:Q891723 wd:Q783794 wd:Q167037"
WD_HDF = "wd:Q18677983"  # région Hauts-de-France

# API gouv : départements (Hauts-de-France d'abord) x sections NAF
DEPTS = ["59", "62", "80", "60", "02", "75", "92", "93", "94", "78", "69", "13", "33",
         "44", "35", "31", "67", "76", "14", "29", "56", "17", "34", "06", "38"]
SECTIONS = {"C": "Industrie", "F": "Construction", "D": "Énergie", "M": "Ingénierie / conseil",
            "J": "Numérique / médias", "H": "Transport / logistique", "K": "Banque / assurance",
            "G": "Commerce / distribution", "N": "Services aux entreprises"}
SECTION_CIBLE = {"C": "ingenieurs", "F": "ingenieurs", "D": "ingenieurs", "M": "ingenieurs",
                 "J": "ingenieurs", "H": "bateau", "K": "bateau", "G": "bateau", "N": "bateau"}
TRANCHES_50_PLUS = "21,22,31,32,41,42,51,52,53"

IA_SECTEURS = [
    "nautisme, voile et accastillage", "équipementiers et distributeurs sportifs",
    "industrie et ingénierie en Hauts-de-France", "énergie et environnement", "BTP et travaux publics",
    "bureaux d'études et conseil en ingénierie", "banques et assurances régionales",
    "transport, logistique et maritime", "agroalimentaire du Nord", "startups et ESN lilloises",
    "automobile et ferroviaire", "chimie, matériaux et plasturgie", "immobilier et promotion",
    "brasseries et boissons du Nord", "mode et textile du Nord", "grande distribution et enseignes nordistes",
]

NAUTIC = re.compile(r"nautiq|voile|marin|bateau|yacht|ocean|mer\b|surf|sail|boat", re.I)
LINK_KEYS = re.compile(r"contact|mentions|legal|l%C3%A9gal|légal|presse|press|partenari|sponsor|mecenat|"
                       r"mécénat|recrut|carri|emploi|equipe|équipe|team|about|a-propos|qui-sommes", re.I)
DEFAULT_PATHS = ["/contact", "/nous-contacter", "/contactez-nous", "/mentions-legales", "/fr/contact"]
EMAIL_RE = re.compile(r"[a-z0-9][a-z0-9._%+-]{0,40}@[a-z0-9.-]+\.[a-z]{2,10}", re.I)
BAD_LOCAL = re.compile(r"^(no-?reply|ne-?pas-?repondre|dpo|rgpd|gdpr|privacy|donnees|data|abuse|postmaster|"
                       r"webmaster|admin|test|exemple|example|user|nom|prenom|name|email|your|votre|"
                       r"sentry|wordpress|wix)", re.I)
BAD_EXT = re.compile(r"\.(png|jpe?g|gif|svg|webp|css|js|ico|pdf)$", re.I)
PRIORITY_1 = re.compile(r"communication|marketing|partenariat|sponsor|mecenat|rse|rh|recrutement|drh|evenement", re.I)
PRIORITY_2 = re.compile(r"contact|info|hello|bonjour|accueil", re.I)
GENERIC_LOCAL = {"contact", "info", "service", "communication", "marketing", "direction",
                 "accueil", "commercial", "support", "rh", "recrutement", "hello", "presse"}


def log(*a):
    print(datetime.now(timezone.utc).strftime("%H:%M:%S"), *a, flush=True)


def now_str():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M")


# ---------------------------------------------------------------- Google Sheet

def open_sheet():
    creds = Credentials.from_service_account_info(
        SA_INFO, scopes=["https://www.googleapis.com/auth/spreadsheets"])
    book = gspread.authorize(creds).open_by_key(SHEET_ID)

    def ws(name, head):
        try:
            w = book.worksheet(name)
        except gspread.WorksheetNotFound:
            w = book.add_worksheet(title=name, rows=2000, cols=len(head))
        if not w.row_values(1):
            w.update(range_name="A1", values=[head])
        return w

    return ws("Entreprises", COMP_HEAD), ws("Contacts", CONT_HEAD), ws("Etat", ["Clé", "Valeur"])


def load_state(w):
    return {r[0]: r[1] for r in w.get_all_values()[1:] if r and r[0]}


def save_state(w, st):
    w.batch_clear(["A2:B200"])
    w.update(range_name="A2", values=[[k, str(v)] for k, v in st.items()])


# ---------------------------------------------------------------- utilitaires domaine

def norm_domain(d):
    d = str(d or "").strip().lower()
    d = re.sub(r"^https?://", "", d)
    d = re.sub(r"^www\.", "", d)
    return d.split("/")[0].split("?")[0].strip(".")


def base_domain(d):
    parts = norm_domain(d).split(".")
    if len(parts) >= 3 and parts[-2] in {"co", "com", "org", "gouv", "asso", "net"}:
        return ".".join(parts[-3:])
    return ".".join(parts[-2:])


def name_token(name):
    """Mot distinctif du nom pour vérifier que le site correspond bien à l'entreprise."""
    stop = {"societe", "société", "groupe", "france", "entreprise", "compagnie", "services", "international",
            "holding", "industries", "industrie", "sas", "sarl", "sa", "the", "les", "des", "et"}
    words = [w for w in re.findall(r"[a-zà-ÿ0-9]{4,}", name.lower()) if w not in stop]
    return words[0] if words else None


def clean_name(n):
    return re.sub(r"\s*\(.*?\)\s*", " ", n or "").strip()


# ---------------------------------------------------------------- IA Groq

def groq_json(prompt, retries=3):
    if not GROQ_KEY:
        return {}
    for i in range(retries):
        r = requests.post(
            "https://api.groq.com/openai/v1/chat/completions",
            headers={"Authorization": f"Bearer {GROQ_KEY}"},
            json={"model": GROQ_MODEL, "temperature": 0.7,
                  "response_format": {"type": "json_object"},
                  "messages": [{"role": "system", "content": "Tu réponds uniquement en JSON valide."},
                               {"role": "user", "content": prompt}]},
            timeout=60)
        if r.status_code == 429:  # limite gratuite atteinte : on attend
            time.sleep(30 * (i + 1))
            continue
        if r.status_code != 200:
            log("Groq erreur", r.status_code)
            return {}
        try:
            return json.loads(r.json()["choices"][0]["message"]["content"])
        except Exception:
            return {}
    return {}


# ---------------------------------------------------------------- sources d'entreprises

def src_wikidata(st):
    scope = st.get("wd_scope", "hdf")
    if scope == "done":
        return []
    off = int(st.get(f"wd_off_{scope}", 0))
    loc = f"?item wdt:P159/wdt:P131* {WD_HDF} ." if scope == "hdf" else "?item wdt:P17 wd:Q142 ."
    q = f"""SELECT DISTINCT ?item ?itemLabel ?site WHERE {{
      VALUES ?type {{ {WD_TYPES} }}
      ?item wdt:P31 ?type ; wdt:P856 ?site .
      {loc}
      FILTER NOT EXISTS {{ ?item wdt:P576 ?fin }}
      SERVICE wikibase:label {{ bd:serviceParam wikibase:language "fr,en". }}
    }} LIMIT 300 OFFSET {off}"""
    r = requests.get("https://query.wikidata.org/sparql", params={"query": q, "format": "json"},
                     headers={"User-Agent": BOT_UA}, timeout=120)
    r.raise_for_status()
    rows = r.json()["results"]["bindings"]
    st[f"wd_off_{scope}"] = off + 300
    if len(rows) < 300:
        st["wd_scope"] = "fr" if scope == "hdf" else "done"
    out = []
    for b in rows:
        nom = b.get("itemLabel", {}).get("value", "")
        if not nom or re.fullmatch(r"Q\d+", nom):
            continue
        out.append({"nom": nom, "domaine": norm_domain(b["site"]["value"]),
                    "cible": "bateau" if NAUTIC.search(nom) else "ingenieurs",
                    "secteur": "Wikidata " + ("Hauts-de-France" if scope == "hdf" else "France"),
                    "verif": None})
    return out


def src_api_gouv(st):
    combos = [(d, s) for d in DEPTS for s in SECTIONS]
    i, page = int(st.get("api_i", 0)), int(st.get("api_page", 1))
    if i >= len(combos):
        return []
    dept, sec = combos[i]
    r = requests.get("https://recherche-entreprises.api.gouv.fr/search",
                     params={"departement": dept, "section_activite_principale": sec,
                             "tranche_effectif_salarie": TRANCHES_50_PLUS, "etat_administratif": "A",
                             "per_page": 25, "page": page},
                     headers={"User-Agent": BOT_UA}, timeout=30)
    if r.status_code != 200:
        st["api_i"], st["api_page"] = i + 1, 1
        return []
    data = r.json()
    if page >= min(int(data.get("total_pages") or 1), 40):
        st["api_i"], st["api_page"] = i + 1, 1
    else:
        st["api_page"] = page + 1
    names = [clean_name(x.get("nom_complet") or x.get("nom_raison_sociale")) for x in data.get("results", [])]
    names = [n for n in names if n]
    if not names:
        return []
    ville = {"59": "Nord", "62": "Pas-de-Calais", "80": "Somme", "60": "Oise", "02": "Aisne"}.get(dept, f"dpt {dept}")
    res = groq_json(
        "Pour chaque entreprise française ci-dessous (département " + dept + "), donne son domaine web officiel "
        "uniquement si tu le connais avec une bonne certitude, sinon null. "
        'Réponds en JSON : {"r":[{"nom":"...","domaine":"exemple.fr ou null"}]}\n' + "\n".join(names))
    out = []
    for x in res.get("r", []) or []:
        dom = norm_domain(x.get("domaine"))
        if dom and "." in dom and x.get("nom"):
            out.append({"nom": x["nom"], "domaine": dom, "cible": SECTION_CIBLE[sec],
                        "secteur": f"{SECTIONS[sec]} ({ville})", "verif": name_token(x["nom"])})
    return out


def src_groq(st, known_names):
    i = int(st.get("ia_i", 0))
    secteur = IA_SECTEURS[i % len(IA_SECTEURS)]
    st["ia_i"] = i + 1
    excl = ", ".join(random.sample(known_names, min(120, len(known_names))))
    res = groq_json(
        f"Liste 25 entreprises réelles et actives en France (priorité Hauts-de-France), secteur « {secteur} », "
        "susceptibles de sponsoriser un équipage étudiant d'école d'ingénieurs (Icam Lille) à la Course Croisière "
        "EDHEC (régate). Varie PME, ETI et grands groupes. Exclure : " + (excl or "aucune") + ". "
        'Cible : "bateau" (visibilité de marque) ou "ingenieurs" (recrutement). '
        'JSON : {"entreprises":[{"nom":"...","domaine":"exemple.fr","cible":"bateau"}]}')
    out = []
    for c in res.get("entreprises", []) or []:
        dom = norm_domain(c.get("domaine"))
        if dom and "." in dom and c.get("nom"):
            out.append({"nom": c["nom"], "domaine": dom,
                        "cible": "bateau" if c.get("cible") == "bateau" else "ingenieurs",
                        "secteur": "IA : " + secteur, "verif": name_token(c["nom"])})
    return out


# ---------------------------------------------------------------- scan des sites

def fetch(sess, url):
    try:
        r = sess.get(url, timeout=12, allow_redirects=True)
        if r.status_code < 400 and "html" in r.headers.get("Content-Type", "html"):
            return r.text[:2_000_000], r.url
    except requests.RequestException:
        pass
    return None


def cf_decode(hexstr):
    try:
        k = int(hexstr[:2], 16)
        return "".join(chr(int(hexstr[i:i + 2], 16) ^ k) for i in range(2, len(hexstr), 2))
    except ValueError:
        return ""


def extract_emails(pages, base):
    found = set()
    for h in pages:
        txt = html.unescape(h)
        txt += " " + " ".join(cf_decode(x) for x in re.findall(r'data-cfemail="([0-9a-fA-F]+)"', h))
        txt = re.sub(r"\s*[\[\(]\s*(at|arobase)\s*[\]\)]\s*", "@", txt, flags=re.I)
        txt = re.sub(r"\s*[\[\(]\s*(dot|point)\s*[\]\)]\s*", ".", txt, flags=re.I)
        for e in EMAIL_RE.findall(txt):
            e = e.lower().strip(".")
            e = re.sub(r"^(u003e|x3e|2f|mailto:)", "", e)
            loc, _, dom = e.partition("@")
            if not dom.endswith(base) or BAD_EXT.search(e) or BAD_LOCAL.match(loc):
                continue
            if sum(ch.isdigit() for ch in loc) > 4:
                continue
            found.add(e)

    def score(e):
        return 0 if PRIORITY_1.search(e) else 1 if PRIORITY_2.search(e) else 2
    return sorted(found, key=score)


def has_mx(dom):
    try:
        r = requests.get("https://dns.google/resolve", params={"name": dom, "type": "MX"}, timeout=10)
        return bool(r.json().get("Answer"))
    except Exception:
        return False


def scan(c):
    dom = c["domaine"]
    base = base_domain(dom)
    sess = requests.Session()
    sess.headers.update({"User-Agent": BROWSER_UA, "Accept-Language": "fr-FR,fr;q=0.9"})
    home = fetch(sess, f"https://{dom}") or fetch(sess, f"https://www.{dom}") or fetch(sess, f"http://{dom}")
    if not home:
        return c, "Site KO", [], ""
    page, url = home
    if c.get("verif") and c["verif"] not in page.lower():
        return c, "Domaine douteux", [], url
    links = []
    for m in re.finditer(r'href=["\']([^"\'#]+)["\'][^>]*>(.{0,200}?)</a', page, re.I | re.S):
        href, label = m.group(1), m.group(2)
        if LINK_KEYS.search(href + " " + label):
            u = urljoin(url, href)
            if base in urlparse(u).netloc and u not in links:
                links.append(u)
    for p in DEFAULT_PATHS:
        u = urljoin(url, p)
        if u not in links:
            links.append(u)
    pages = [page]
    for u in links[:9]:
        got = fetch(sess, u)
        if got:
            pages.append(got[0])
    emails = extract_emails(pages, base)
    status = f"OK ({min(len(emails), MAX_PER_COMPANY)})" if emails else "Aucun email"
    if not emails and GUESS_GENERIC and has_mx(base):
        emails, status = [f"contact@{base}"], "Deviné (contact@)"
    return c, status, emails[:MAX_PER_COMPANY], url


def first_name(email):
    m = re.match(r"^([a-zà-ÿ]{2,})[._-][a-zà-ÿ]{2,}$", email.split("@")[0], re.I)
    if not m or m.group(1).lower() in GENERIC_LOCAL:
        return ""
    return m.group(1).capitalize()


# ---------------------------------------------------------------- boucle principale

def main():
    t0 = time.time()
    w_comp, w_cont, w_state = open_sheet()
    st = load_state(w_state)
    comp_rows = w_comp.get_all_values()[1:]
    known_domains = {norm_domain(r[1]) for r in comp_rows if len(r) > 1}
    known_names = [r[0] for r in comp_rows if r and r[0]]
    known_emails = {r[2].lower() for r in w_cont.get_all_values()[1:] if len(r) > 2}
    total_comp = total_mails = 0

    while time.time() - t0 < BUDGET_S:
        cands = []
        for name, fn in (("wikidata", src_wikidata), ("api_gouv", src_api_gouv)):
            try:
                cands += fn(st)
                st[f"err_{name}"] = 0
            except Exception as e:
                n = int(st.get(f"err_{name}", 0)) + 1
                st[f"err_{name}"] = n
                log(f"source {name} en erreur ({n}) : {type(e).__name__}")
                if name == "wikidata" and n >= 3:  # requête trop lourde : on passe à l'étape suivante
                    st["wd_scope"] = "fr" if st.get("wd_scope", "hdf") == "hdf" else "done"
                    st["err_wikidata"] = 0
        if len(cands) < 40:
            try:
                cands += src_groq(st, known_names)
            except Exception as e:
                log(f"source groq en erreur : {type(e).__name__}")

        fresh, seen = [], set()
        for c in cands:
            d = c["domaine"]
            if d in known_domains or d in seen or base_domain(d) in {"wikipedia.org", "facebook.com", "linkedin.com"}:
                continue
            seen.add(d)
            fresh.append(c)

        if not fresh:
            save_state(w_state, st)
            if st.get("wd_scope") == "done" and int(st.get("api_i", 0)) >= len(DEPTS) * len(SECTIONS) and not GROQ_KEY:
                log("toutes les sources sont épuisées")
                break
            time.sleep(20)
            continue

        with ThreadPoolExecutor(WORKERS) as pool:
            results = list(pool.map(scan, fresh))

        comp_out, cont_out = [], []
        for c, status, emails, url in results:
            known_domains.add(c["domaine"])
            known_names.append(c["nom"])
            comp_out.append([c["nom"], c["domaine"], c["secteur"], c["cible"], status, now_str()])
            for e in emails:
                if e in known_emails:
                    continue
                known_emails.add(e)
                cont_out.append([c["nom"], c["domaine"], e, first_name(e), c["cible"], "Nouveau",
                                 "", "", "", "", url or f"https://{c['domaine']}"])
        if comp_out:
            w_comp.append_rows(comp_out, value_input_option="RAW")
        if cont_out:
            w_cont.append_rows(cont_out, value_input_option="RAW")
        save_state(w_state, st)
        total_comp += len(comp_out)
        total_mails += len(cont_out)
        log(f"lot : {len(comp_out)} entreprises, {len(cont_out)} emails | cumul run : {total_comp} / {total_mails}")

    st["dernier_run"] = now_str()
    old = sorted(k for k in st if k.startswith("emails_"))[:-14]
    for k in old:
        del st[k]
    st[f"emails_{datetime.now(timezone.utc):%Y-%m-%d}"] = int(st.get(f"emails_{datetime.now(timezone.utc):%Y-%m-%d}", 0)) + total_mails
    save_state(w_state, st)
    log(f"fin : {total_comp} entreprises scannées, {total_mails} nouveaux emails")


if __name__ == "__main__":
    main()
