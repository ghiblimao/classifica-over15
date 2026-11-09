#!/usr/bin/env python3
"""
Bot Over 1,5 – partite più adatte alla strategia (versione semplice)
====================================================================
Per ogni partita del giorno calcola, con un modello di Poisson sui risultati della
stagione in corso:
  1. P(0-0 al 20')               – probabilità che la partita sia ancora 0-0 al 20';
  2. P(Over 1,5 | 0-0 al 20')    – probabilità che, partendo da 0-0 al 20', finisca con 2+ gol;
  3. P(scenario completo)        – le due insieme: 0-0 al 20' E Over 1,5 a fine partita.
Le partite sono ordinate per la terza colonna.

Dati: football-data.co.uk (gratuiti, nessuna chiave necessaria).
Uso:   python bot_over15.py            (oggi, apre il report nel browser)
       python bot_over15.py --automatico       (avvio pianificato: report + Telegram, senza finestre)
       python bot_over15.py --configura-telegram (collega il tuo Telegram)
       python bot_over15.py --prova-api-football (verifica la chiave API-Football)
       python bot_over15.py --web docs         (usato da GitHub: crea la pagina web in docs/)
       python bot_over15.py --giorni 2 (oggi e domani)
       python bot_over15.py --demo     (prova con dati inventati, senza internet)
"""
import argparse, csv, json, math, os, random, sys, time, html, webbrowser, unicodedata
from pathlib import Path
import urllib.request, urllib.parse, urllib.error
from collections import defaultdict
from datetime import datetime, timedelta, timezone

# ======================================================================= CONFIG
# Fonte dati: football-data.co.uk (gratuita, nessuna chiave). Codici delle divisioni:
CAMPIONATI = {
    "I1": "Italia – Serie A",        "I2": "Italia – Serie B",
    "E0": "Inghilterra – Premier League", "E1": "Inghilterra – Championship",
    "SP1": "Spagna – La Liga",       "SP2": "Spagna – Segunda División",
    "D1": "Germania – Bundesliga",   "D2": "Germania – 2. Bundesliga",
    "F1": "Francia – Ligue 1",       "F2": "Francia – Ligue 2",
    "SC0": "Scozia – Premiership",   "SC1": "Scozia – Championship",
    "N1": "Olanda – Eredivisie",     "B1": "Belgio – Pro League",
    "P1": "Portogallo – Primeira Liga", "T1": "Turchia – Süper Lig",
    "G1": "Grecia – Super League",
    # Altre divisioni disponibili: togli il # per aggiungerle
    # "E2": "Inghilterra – League One", "E3": "Inghilterra – League Two", "EC": "Inghilterra – National League",
    # "SC2": "Scozia – League One", "SC3": "Scozia – League Two",
}
# Campionati "extra" (file in formato diverso, senza risultati del 1° tempo). Togli il # per escluderne uno.
CAMPIONATI_EXTRA = {
    "NOR": ("Norway", "Norvegia – Eliteserien"),   "SWE": ("Sweden", "Svezia – Allsvenskan"),
    "DNK": ("Denmark", "Danimarca – Superliga"),    "FIN": ("Finland", "Finlandia – Veikkausliiga"),
    "AUT": ("Austria", "Austria – Bundesliga"),     "SWZ": ("Switzerland", "Svizzera – Super League"),
    "POL": ("Poland", "Polonia – Ekstraklasa"),     "ROU": ("Romania", "Romania – Liga I"),
    "IRL": ("Ireland", "Irlanda – Premier Division"), "RUS": ("Russia", "Russia – Premier League"),
}
# --- API-Football (facoltativo): completa i campionati che football-data non ha ---
API_FOOTBALL_KEY = os.environ.get("API_FOOTBALL_KEY", "")
API_FOOTBALL_URL = "https://v3.football.api-sports.io"
MAX_RICHIESTE_API = 90           # il piano gratuito ne concede 100 al giorno: ne teniamo 10 di scorta
# Campionati da prendere da API-Football: paese (come lo scrive API-Football) -> nomi dei campionati.
# Sono le serie A e B europee che football-data non copre. Se nel log compare un campionato
# "non incluso" che ti interessa, aggiungi qui il suo nome esattamente come appare.
API_CAMPIONATI = {
    "Netherlands": ["Eerste Divisie"],            "Belgium": ["Challenger Pro League"],
    "Portugal": ["Segunda Liga", "Liga Portugal 2"], "Turkey": ["1. Lig"],
    "Greece": ["Super League 2"],                 "Austria": ["2. Liga"],
    "Switzerland": ["Challenge League"],          "Denmark": ["1. Division"],
    "Norway": ["1. Division", "OBOS-ligaen"],     "Sweden": ["Superettan"],
    "Poland": ["I Liga"],                         "Finland": ["Ykkonen", "Ykkosliiga"],
    "Romania": ["Liga II"],                       "Russia": ["FNL"],
    "Ireland": ["First Division"],
    "Czech-Republic": ["Czech Liga", "1. Liga", "FNL"], "Croatia": ["HNL", "First NL", "Prva NL"],
    "Serbia": ["Super Liga", "Prva Liga"],        "Hungary": ["NB I", "NB II"],
    "Slovakia": ["Super Liga", "2. liga"],        "Slovenia": ["1. SNL", "2. SNL"],
    "Bulgaria": ["First League", "Second League"], "Ukraine": ["Premier League", "Persha Liga"],
    "Cyprus": ["1. Division", "2. Division"],     "Israel": ["Ligat ha'Al", "Liga Leumit"],
    "Iceland": ["Urvalsdeild", "1. Deild"],       "Bosnia": ["Premijer Liga"],
}
# Se football-data oggi non ha le partite di un suo campionato (calendario non ancora aggiornato),
# il bot le prende da API-Football usando questa corrispondenza.
FD_SU_API = {
    "I1": ("Italy", ["Serie A"]), "I2": ("Italy", ["Serie B"]), "E0": ("England", ["Premier League"]),
    "E1": ("England", ["Championship"]), "SP1": ("Spain", ["La Liga"]), "SP2": ("Spain", ["Segunda Division"]),
    "D1": ("Germany", ["Bundesliga"]), "D2": ("Germany", ["2. Bundesliga"]), "F1": ("France", ["Ligue 1"]),
    "F2": ("France", ["Ligue 2"]), "SC0": ("Scotland", ["Premiership"]), "SC1": ("Scotland", ["Championship"]),
    "N1": ("Netherlands", ["Eredivisie"]), "B1": ("Belgium", ["Jupiler Pro League"]),
    "P1": ("Portugal", ["Primeira Liga"]), "T1": ("Turkey", ["Super Lig"]), "G1": ("Greece", ["Super League 1"]),
    "NOR": ("Norway", ["Eliteserien"]), "SWE": ("Sweden", ["Allsvenskan"]), "DNK": ("Denmark", ["Superliga"]),
    "FIN": ("Finland", ["Veikkausliiga"]), "AUT": ("Austria", ["Bundesliga"]),
    "SWZ": ("Switzerland", ["Super League"]), "POL": ("Poland", ["Ekstraklasa"]),
    "ROU": ("Romania", ["Liga I", "SuperLiga"]), "IRL": ("Ireland", ["Premier Division"]),
    "RUS": ("Russia", ["Premier League"]),
}
PAESI_IT = {"Netherlands": "Olanda", "Belgium": "Belgio", "Portugal": "Portogallo", "Turkey": "Turchia",
            "Greece": "Grecia", "Austria": "Austria", "Switzerland": "Svizzera", "Denmark": "Danimarca",
            "Norway": "Norvegia", "Sweden": "Svezia", "Poland": "Polonia", "Finland": "Finlandia",
            "Romania": "Romania", "Russia": "Russia", "Ireland": "Irlanda", "Czech-Republic": "Rep. Ceca",
            "Croatia": "Croazia", "Serbia": "Serbia", "Hungary": "Ungheria", "Slovakia": "Slovacchia",
            "Slovenia": "Slovenia", "Bulgaria": "Bulgaria", "Ukraine": "Ucraina", "Cyprus": "Cipro",
            "Israel": "Israele", "Iceland": "Islanda", "Bosnia": "Bosnia", "Italy": "Italia",
            "England": "Inghilterra", "Spain": "Spagna", "Germany": "Germania", "France": "Francia",
            "Scotland": "Scozia", "Albania": "Albania", "Estonia": "Estonia", "Latvia": "Lettonia",
            "Lithuania": "Lituania", "Belarus": "Bielorussia", "Georgia": "Georgia", "Armenia": "Armenia",
            "Azerbaijan": "Azerbaigian", "Kazakhstan": "Kazakistan", "Moldova": "Moldavia",
            "Montenegro": "Montenegro", "North-Macedonia": "Macedonia del Nord", "Wales": "Galles",
            "Northern-Ireland": "Irlanda del Nord", "Luxembourg": "Lussemburgo", "Malta": "Malta",
            "Faroe-Islands": "Fær Øer", "Andorra": "Andorra", "San-Marino": "San Marino", "Gibraltar": "Gibilterra",
            "Kosovo": "Kosovo", "Liechtenstein": "Liechtenstein"}
PAROLE_ESCLUSE = ("cup", "pokal", "coppa", "copa", "coupe", "beker", "taca", "kupa", "friendl", "women", "femin",
                  "u17", "u18", "u19", "u20", "u21", "u23", "youth", "reserve", "primavera", "super cup", "supercup")
# Quota di gol del 1° tempo: per ogni campionato viene calcolata dai suoi risultati reali.
# Dove la fonte non ha i risultati del 1° tempo, si usa la media reale degli altri campionati analizzati
# e la partita viene segnalata come "1° tempo stimato". Questo valore serve solo se non c'è nessun dato reale.
QUOTA_RISERVA_SOLO_EMERGENZA = 0.45
URL_DATI = "https://www.football-data.co.uk/mmz4281/{stagione}/{codice}.csv"
URL_DATI_EXTRA = "https://www.football-data.co.uk/new/{codice}.csv"
URL_CALENDARIO_EXTRA = "https://www.football-data.co.uk/new_league_fixtures.csv"
URL_CALENDARIO = "https://www.football-data.co.uk/fixtures.csv"
PESO_STAGIONE_PRECEDENTE = 0.5   # a inizio stagione si usa anche la stagione scorsa, con peso ridotto
MIN_PARTITE_STAGIONE = 80        # sotto questo numero di partite giocate si aggiunge la stagione precedente
MINUTO_0_0 = 20             # fino a quale minuto deve restare 0-0
SHRINK = 5                  # partite "virtuali" di media campionato (evita stime estreme a inizio stagione)
MIN_PARTITE_SQUADRA = 4     # sotto questo numero di partite la stima è segnalata come poco affidabile
TOP_TELEGRAM = 10
TELEGRAM_TOKEN = os.environ.get("TELEGRAM_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")
PAGINA_URL = os.environ.get("PAGINA_URL", "")          # indirizzo della pagina web (se pubblicata)
# cartella del programma (funziona sia come script .py sia come eseguibile .exe)
CARTELLA = os.path.dirname(sys.executable if getattr(sys, "frozen", False) else os.path.abspath(__file__))
CARTELLA_REPORT = os.path.join(CARTELLA, "report")
FILE_CONFIG = os.path.join(CARTELLA, "configurazione.json")
# ==============================================================================

try:
    from zoneinfo import ZoneInfo
    TZ = ZoneInfo("Europe/Rome")
    TZ_UK = ZoneInfo("Europe/London")
except Exception:                                   # Windows senza tzdata: approssimazione ora solare
    TZ = timezone(timedelta(hours=1))
    TZ_UK = timezone.utc


def iso_dt(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


# ====================================================================== MODELLO
def quota_residua(t, s):
    """Frazione dei gol attesi che resta dal minuto t al 90' (s = quota di gol del 1° tempo)."""
    if t <= 45:
        return s * (45 - t) / 45 + (1 - s)
    return (1 - s) * max(0, 90 - t) / 45


def costruisci_modello(finite):
    """finite: dizionari con casa, trasf, gc, gt (gol finali), ht (gol 1° tempo o None), w (peso)."""
    con_ht = [m for m in finite if m["ht"] is not None]
    tot = sum(m["w"] * (m["gc"] + m["gt"]) for m in con_ht)
    s = sum(m["w"] * m["ht"] for m in con_ht) / tot if tot else None     # None = nessun dato reale
    d = defaultdict(lambda: {"hn": 0, "hf": 0, "hs": 0, "an": 0, "af": 0, "as": 0, "g": 0})
    for m in finite:
        w, c, t = m["w"], d[m["casa"]], d[m["trasf"]]
        c["hn"] += w; c["hf"] += w * m["gc"]; c["hs"] += w * m["gt"]
        t["an"] += w; t["af"] += w * m["gt"]; t["as"] += w * m["gc"]
        if w == 1:
            c["g"] += 1; t["g"] += 1
    mod = modello_da_totali(d, s)
    mod["n_ht"] = sum(m["w"] for m in con_ht)
    return mod


def modello_da_totali(d, s):
    """d: per squadra partite (hn/an), gol fatti (hf/af) e subiti (hs/as) in casa e in trasferta."""
    H = sum(v["hf"] for v in d.values()) / max(1e-9, sum(v["hn"] for v in d.values()))
    A = sum(v["af"] for v in d.values()) / max(1e-9, sum(v["an"] for v in d.values()))
    forza = {t: {"att_casa": (v["hf"] + SHRINK * H) / (v["hn"] + SHRINK) / H,
                 "dif_casa": (v["hs"] + SHRINK * A) / (v["hn"] + SHRINK) / A,
                 "att_trasf": (v["af"] + SHRINK * A) / (v["an"] + SHRINK) / A,
                 "dif_trasf": (v["as"] + SHRINK * H) / (v["an"] + SHRINK) / H,
                 "giocate": v["g"]} for t, v in d.items()}
    return {"H": H, "A": A, "s": s, "s_reale": s is not None, "n_ht": 0, "forza": forza}


def analizza(match, mod, campionato):
    """match: dizionario con casa, trasf, kickoff (datetime)."""
    casa, trasf = match["casa"], match["trasf"]
    neutro = {"att_casa": 1, "dif_casa": 1, "att_trasf": 1, "dif_trasf": 1, "giocate": 0}
    fc, ft = mod["forza"].get(casa, neutro), mod["forza"].get(trasf, neutro)
    lam = mod["H"] * fc["att_casa"] * ft["dif_trasf"] + mod["A"] * ft["att_trasf"] * fc["dif_casa"]
    resto = lam * quota_residua(MINUTO_0_0, mod["s"])      # gol attesi dal 20' al 90'
    p00 = math.exp(-(lam - resto))                         # nessun gol nei primi 20'
    pover = 1 - math.exp(-resto) * (1 + resto)             # almeno 2 gol dal 20' in poi
    kickoff = match["kickoff"]
    return {"ora": kickoff.astimezone(TZ).strftime("%d/%m %H:%M"), "_kickoff": kickoff,
            "campionato": campionato, "partita": f"{casa} - {trasf}", "gol_attesi": lam,
            "p00": p00, "pover": pover, "pscenario": p00 * pover,
            "affidabile": min(fc["giocate"], ft["giocate"]) >= MIN_PARTITE_SQUADRA,
            "ht_stimato": not mod["s_reale"], "quota_ht": mod["s"]}


# ====================================================== FOOTBALL-DATA.CO.UK
def scarica_csv(url):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (bot over 1,5)"})
    with urllib.request.urlopen(req, timeout=60) as r:
        dati = r.read()
    for enc in ("utf-8-sig", "latin-1"):
        try:
            testo = dati.decode(enc); break
        except UnicodeDecodeError:
            continue
    return list(csv.DictReader(testo.splitlines()))


def leggi_data(riga, fuso):
    """Data (gg/mm/aa o gg/mm/aaaa) e ora (UK) di una riga, convertite nel fuso italiano."""
    data = (riga.get("Date") or "").strip()
    ora = (riga.get("Time") or "15:00").strip() or "15:00"
    for formato in ("%d/%m/%Y %H:%M", "%d/%m/%y %H:%M"):
        try:
            return datetime.strptime(f"{data} {ora}", formato).replace(tzinfo=fuso)
        except ValueError:
            continue
    return None


def intero(x):
    try:
        return int(float(x))
    except (TypeError, ValueError):
        return None


def campo(riga, *nomi):
    for n in nomi:
        v = riga.get(n)
        if v not in (None, ""):
            return v.strip()
    return ""


def risultati_extra(codice):
    """Campionati extra: un unico file con tutte le stagioni (colonne Season, Home, Away, HG, AG)."""
    righe = scarica_csv(URL_DATI_EXTRA.format(codice=codice))
    stagioni = []
    for r in righe:
        st = campo(r, "Season")
        if st and st not in stagioni:
            stagioni.append(st)
    stagioni.sort(key=lambda x: x.split("/")[0])
    if not stagioni:
        return []
    def partite(st, peso):
        out = []
        for r in righe:
            if campo(r, "Season") != st:
                continue
            gc, gt = intero(campo(r, "HG", "FTHG")), intero(campo(r, "AG", "FTAG"))
            casa, trasf = campo(r, "Home", "HomeTeam"), campo(r, "Away", "AwayTeam")
            if gc is None or gt is None or not casa:
                continue
            out.append({"casa": casa, "trasf": trasf, "gc": gc, "gt": gt, "ht": None, "w": peso})
        return out
    finite = partite(stagioni[-1], 1.0)
    if len(finite) < MIN_PARTITE_STAGIONE and len(stagioni) > 1:
        finite += partite(stagioni[-2], PESO_STAGIONE_PRECEDENTE)
    return finite


def stagione(oggi, indietro=0):
    inizio = oggi.year if oggi.month >= 7 else oggi.year - 1
    inizio -= indietro
    return f"{inizio % 100:02d}{(inizio + 1) % 100:02d}"


def risultati(codice, oggi):
    finite = []
    for indietro, peso in ((0, 1.0), (1, PESO_STAGIONE_PRECEDENTE)):
        if indietro == 1 and len(finite) >= MIN_PARTITE_STAGIONE:
            break
        try:
            righe = scarica_csv(URL_DATI.format(stagione=stagione(oggi, indietro), codice=codice))
        except Exception as e:
            print(f"  ! {codice} stagione {stagione(oggi, indietro)}: non disponibile ({e})")
            continue
        for r in righe:
            gc, gt = intero(r.get("FTHG")), intero(r.get("FTAG"))
            if gc is None or gt is None or not r.get("HomeTeam"):
                continue
            hc, ht = intero(r.get("HTHG")), intero(r.get("HTAG"))
            finite.append({"casa": r["HomeTeam"].strip(), "trasf": r["AwayTeam"].strip(), "gc": gc, "gt": gt,
                           "ht": None if hc is None or ht is None else hc + ht, "w": peso})
        time.sleep(0.5)
    return finite


# ============================================================== API-FOOTBALL
class ApiFootball:
    def __init__(self, chiave):
        self.chiave, self.usate, self.bloccata = chiave, 0, False

    def get(self, percorso, **parametri):
        if self.usate >= MAX_RICHIESTE_API:
            raise RuntimeError(f"raggiunto il limite di {MAX_RICHIESTE_API} richieste impostato")
        url = f"{API_FOOTBALL_URL}/{percorso}" + ("?" + urllib.parse.urlencode(parametri) if parametri else "")
        req = urllib.request.Request(url, headers={"x-apisports-key": self.chiave})
        self.usate += 1
        with urllib.request.urlopen(req, timeout=60) as r:
            dati = json.loads(r.read().decode("utf-8"))
        time.sleep(6.5)                          # piano gratuito: max 10 richieste al minuto
        errori = dati.get("errors")
        if errori:
            raise RuntimeError("; ".join(f"{k}: {v}" for k, v in errori.items()) if isinstance(errori, dict) else str(errori))
        return dati.get("response", [])


def norm(t):
    return unicodedata.normalize("NFKD", t or "").encode("ascii", "ignore").decode().lower().strip()


def modello_da_classifica(api, lega_id, stagione_api):
    gruppi = api.get("standings", league=lega_id, season=stagione_api)
    d = {}
    for blocco in gruppi:
        for gruppo in blocco.get("league", {}).get("standings", []):
            for riga in gruppo:
                nome = riga["team"]["name"]
                h, a = riga.get("home", {}), riga.get("away", {})
                giocate = (h.get("played") or 0) + (a.get("played") or 0)
                if nome in d and d[nome]["g"] >= giocate:
                    continue
                d[nome] = {"hn": h.get("played") or 0, "hf": (h.get("goals") or {}).get("for") or 0,
                           "hs": (h.get("goals") or {}).get("against") or 0,
                           "an": a.get("played") or 0, "af": (a.get("goals") or {}).get("for") or 0,
                           "as": (a.get("goals") or {}).get("against") or 0, "g": giocate}
    if sum(v["hn"] for v in d.values()) < 20:
        return None
    return modello_da_totali(d, None)         # la classifica non ha i gol del 1° tempo


def scarica_api_football(date_ok, fd_senza_partite, s_media):
    """Partite dei campionati mancanti (e di quelli football-data senza calendario aggiornato)."""
    api = ApiFootball(API_FOOTBALL_KEY)
    cercati = {norm(p): {norm(n) for n in nomi} for p, nomi in API_CAMPIONATI.items()}
    for codice in fd_senza_partite:
        if codice in FD_SU_API:
            p, nomi = FD_SU_API[codice]
            cercati.setdefault(norm(p), set()).update(norm(n) for n in nomi)
    gia_coperti = {(norm(p), norm(n)) for p, nomi in FD_SU_API.values() for n in nomi}
    leghe, esclusi = defaultdict(list), set()
    for giorno in sorted(date_ok):
        for f in api.get("fixtures", date=giorno.isoformat(), timezone="Europe/Rome"):
            if (f.get("fixture", {}).get("status", {}).get("short") or "") not in ("NS", "TBD"):
                continue
            lega = f["league"]
            paese, nome = lega.get("country") or "", lega.get("name") or ""
            if norm(nome) in cercati.get(norm(paese), set()):
                leghe[(lega["id"], lega["season"], paese, nome)].append(
                    {"casa": f["teams"]["home"]["name"], "trasf": f["teams"]["away"]["name"],
                     "kickoff": iso_dt(f["fixture"]["date"])})
            elif (paese in PAESI_IT and (norm(paese), norm(nome)) not in gia_coperti
                  and not any(p in norm(nome) for p in PAROLE_ESCLUSE)):
                esclusi.add(f"{paese} – {nome}")
    print(f"  API-Football: {sum(len(v) for v in leghe.values())} partite in {len(leghe)} campionati da completare")
    righe = []
    for (lega_id, stagione_api, paese, nome), prossime in leghe.items():
        etichetta = f"{PAESI_IT.get(paese, paese)} – {nome}"
        try:
            mod = modello_da_classifica(api, lega_id, stagione_api)
        except Exception as e:
            print(f"  ! {etichetta}: classifica non disponibile ({e})")
            if "plan" in str(e).lower() or "limite" in str(e).lower():
                print("  ! Interrompo le richieste ad API-Football per oggi."); break
            continue
        if mod is None:
            print(f"  ! {etichetta}: troppo poche partite giocate"); continue
        mod["s"] = s_media                     # stimata: la riga sarà segnalata
        print(f"  {etichetta} (API-Football): {len(prossime)} in programma")
        righe += [analizza(m, mod, etichetta) for m in prossime]
    if esclusi:
        print("  Altri campionati europei oggi, non inclusi (aggiungili in API_CAMPIONATI se ti interessano):")
        for e in sorted(esclusi):
            print("    -", e)
    print(f"  Richieste API-Football usate: {api.usate}")
    return righe


def prova_api_football():
    if not API_FOOTBALL_KEY:
        raise SystemExit("Nessuna chiave API-Football configurata.")
    api = ApiFootball(API_FOOTBALL_KEY)
    stato = api.get("status")
    info = stato if isinstance(stato, dict) else (stato[0] if stato else {})
    piano = info.get("subscription", {}).get("plan", "?")
    rich = info.get("requests", {})
    print(f"Chiave valida. Piano: {piano} – richieste oggi: {rich.get('current', '?')}/{rich.get('limit_day', '?')}")
    oggi = datetime.now(TZ).date()
    partite = api.get("fixtures", date=oggi.isoformat(), timezone="Europe/Rome")
    serie_b = [f for f in partite if norm(f["league"].get("country")) == "italy" and norm(f["league"].get("name")) == "serie b"]
    stag = serie_b[0]["league"]["season"] if serie_b else (oggi.year if oggi.month >= 7 else oggi.year - 1)
    try:
        mod = modello_da_classifica(api, 136, stag)       # 136 = Serie B su API-Football
        print(f"Stagione in corso ({stag}) ACCESSIBILE: il bot può usare API-Football."
              if mod else f"Stagione {stag} accessibile ma con pochi dati.")
    except Exception as e:
        print(f"Stagione in corso ({stag}) NON accessibile con questo piano: {e}")


def scarica(giorni):
    oggi = datetime.now(TZ).date()
    date_ok = {oggi + timedelta(days=i) for i in range(giorni)}
    calendario = defaultdict(list)
    paese_codice = {paese.lower(): c for c, (paese, _) in CAMPIONATI_EXTRA.items()}
    for url in (URL_CALENDARIO, URL_CALENDARIO_EXTRA):
        try:
            righe_cal = scarica_csv(url)
        except Exception as e:
            print(f"  ! calendario {url.rsplit('/', 1)[-1]} non disponibile ({e})"); continue
        for r in righe_cal:
            div = campo(r, "Div")
            if div not in CAMPIONATI:
                div = paese_codice.get(campo(r, "Country").lower(), div)
            k = leggi_data(r, TZ_UK)
            if (div in CAMPIONATI or div in CAMPIONATI_EXTRA) and k and k.astimezone(TZ).date() in date_ok:
                calendario[div].append({"casa": campo(r, "HomeTeam", "Home"), "trasf": campo(r, "AwayTeam", "Away"),
                                        "kickoff": k})
    righe = []
    tutti = {**CAMPIONATI, **{c: nome for c, (_, nome) in CAMPIONATI_EXTRA.items()}}
    fd_senza_partite = [c for c in tutti if not calendario.get(c)]
    in_attesa = []
    for codice, nome in tutti.items():
        prossime = calendario.get(codice, [])
        if not prossime:
            continue
        try:
            finite = risultati_extra(codice) if codice in CAMPIONATI_EXTRA else risultati(codice, oggi)
        except Exception as e:
            print(f"  ! {nome}: risultati non disponibili ({e})"); continue
        print(f"  {nome}: {sum(1 for m in finite if m['w'] == 1)} giocate in stagione, {len(prossime)} in programma")
        if len(finite) >= 20:
            in_attesa.append((costruisci_modello(finite), prossime, nome))
        else:
            fd_senza_partite.append(codice)
    # media REALE della quota di gol nel 1° tempo, dai campionati che hanno il dato
    reali = [(m["s"], m["n_ht"]) for m, _, _ in in_attesa if m["s_reale"]]
    if reali:
        s_media = sum(v * n for v, n in reali) / sum(n for _, n in reali)
        print(f"  Quota media reale di gol nel 1° tempo (per i campionati senza dato): {s_media:.1%}")
    else:
        s_media = QUOTA_RISERVA_SOLO_EMERGENZA
        print("  ! Nessun dato reale sul 1° tempo oggi: uso il valore di emergenza (partite segnalate)")
    for mod, prossime, nome in in_attesa:
        if not mod["s_reale"]:
            mod["s"] = s_media
        righe += [analizza(m, mod, nome) for m in prossime]
    if API_FOOTBALL_KEY:
        try:
            righe += scarica_api_football(date_ok, fd_senza_partite, s_media)
        except Exception as e:
            print(f"  ! API-Football non disponibile oggi ({e}): uso solo football-data")
    return righe


def righe_demo():
    random.seed(7)
    squadre = [f"Squadra {c}" for c in "ABCDEFGHIJKLMNOPQRST"]
    att = {t: random.uniform(0.7, 1.4) for t in squadre}
    def pois(l):
        k, p, L = 0, 1, math.exp(-l)
        while True:
            p *= random.random()
            if p < L: return k
            k += 1
    finite = []
    for _ in range(12):
        random.shuffle(squadre)
        for i in range(0, 20, 2):
            h, a = squadre[i], squadre[i + 1]
            gh, ga = pois(1.5 * att[h] / att[a] ** 0.3), pois(1.15 * att[a] / att[h] ** 0.3)
            finite.append({"casa": h, "trasf": a, "gc": gh, "gt": ga,
                           "ht": min(gh, pois(0.65)) + min(ga, pois(0.5)), "w": 1.0})
    mod = costruisci_modello(finite)
    base = datetime.now(timezone.utc).replace(hour=14, minute=0, second=0, microsecond=0)
    prossime = [{"casa": squadre[i], "trasf": squadre[i + 1], "kickoff": base + timedelta(hours=i // 8)}
                for i in range(0, 20, 2)]
    return [analizza(m, mod, "Campionato DEMO") for m in prossime]


# ===================================================================== OUTPUT
def nota(r):
    n = []
    if r.get("ht_stimato"):
        n.append(f"1° tempo stimato ({r['quota_ht']:.0%})")
    if not r["affidabile"]:
        n.append("pochi dati")
    return " · ".join(n)


def pc(x):
    return f"{x:.0%}"


def salva(righe):
    os.makedirs(CARTELLA_REPORT, exist_ok=True)
    giorno = datetime.now(TZ).strftime("%Y-%m-%d")
    # posizione in classifica per probabilità, poi ordine per orario di inizio
    for i, r in enumerate(sorted(righe, key=lambda r: r["pscenario"], reverse=True), 1):
        r["pos"] = i
    righe.sort(key=lambda r: (r["_kickoff"], r["pos"]))
    p_csv = os.path.join(CARTELLA_REPORT, f"over15_{giorno}.csv")
    with open(p_csv, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["Ora", "Classifica", "Campionato", "Partita", "Gol attesi", f"P 0-0 al {MINUTO_0_0}'",
                    f"P Over 1,5 se 0-0 al {MINUTO_0_0}'", "P scenario completo", "Attendibilità"])
        for r in righe:
            w.writerow([r["ora"], r["pos"], r["campionato"], r["partita"], f"{r['gol_attesi']:.2f}".replace(".", ","),
                        pc(r["p00"]), pc(r["pover"]), f"{r['pscenario']:.1%}".replace(".", ","),
                        ("ATTENZIONE: " + nota(r)) if nota(r) else "ok"])
    corpo = "".join(
        f"<tr{' class=poco' if nota(r) else ''}><td>{r['ora']}</td>"
        f"<td{' class=top' if r['pos'] <= TOP_TELEGRAM else ''}>{r['pos']}</td><td>{html.escape(r['campionato'])}</td>"
        f"<td class=p>{html.escape(r['partita'])}</td><td>{r['gol_attesi']:.2f}</td><td>{pc(r['p00'])}</td>"
        f"<td>{pc(r['pover'])}</td><td class=v>{r['pscenario']:.1%}</td>"
        f"<td class=nota>{('⚠ ' + html.escape(nota(r))) if nota(r) else 'ok'}</td></tr>" for r in righe) or \
        "<tr><td colspan=9>Nessuna partita oggi nei campionati selezionati.</td></tr>"
    pagina = f"""<!doctype html><html lang="it"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Over 1,5 – {giorno}</title><style>
body{{font-family:Arial,sans-serif;margin:20px;color:#222}} table{{border-collapse:collapse;font-size:14px}}
th,td{{border:1px solid #ccc;padding:6px 9px;text-align:center}} th{{background:#1F3864;color:#fff}}
td.p{{text-align:left;font-weight:bold}} td.v{{font-weight:bold;background:#DDEBF7}} td.top{{font-weight:bold;background:#E2EFDA}}
tr.poco{{color:#888}} td.nota{{font-size:12px;text-align:left;color:#B45F06}} .wrap{{overflow-x:auto}} p{{max-width:820px;font-size:13px}}</style>
<h2>Partite del {giorno} più adatte alla strategia</h2>
<p><b>P 0-0 al {MINUTO_0_0}'</b> = probabilità che la partita sia ancora 0-0 al {MINUTO_0_0}'.
<b>P Over 1,5 se 0-0</b> = probabilità che da lì arrivino almeno 2 gol.
<b>P scenario completo</b> = le due cose insieme. Partite in ordine di orario; <b>Classifica</b> = posizione per
P scenario completo (1 = la migliore del giorno), con le prime {TOP_TELEGRAM} evidenziate.
Righe grigie con ⚠ = stima meno attendibile: <b>pochi dati</b> (squadre con poche partite giocate) oppure
<b>1° tempo stimato</b> (la fonte non ha i risultati del primo tempo per quel campionato: la quota di gol nel 1° tempo
è la media reale degli altri campionati del giorno, indicata tra parentesi, e la P 0-0 al {MINUTO_0_0}' è meno precisa).</p>
<div class="wrap"><table><tr><th>Ora</th><th>Classifica</th><th>Campionato</th><th>Partita</th><th>Gol attesi</th>
<th>P 0-0 al {MINUTO_0_0}'</th><th>P Over 1,5 se 0-0</th><th>P scenario completo</th><th>Attendibilità</th></tr>{corpo}</table></div>
<p>Modello statistico semplice: non considera formazioni, infortuni, meteo o motivazioni. Usalo come filtro, non come certezza.</p></html>"""
    p_html = os.path.join(CARTELLA_REPORT, f"over15_{giorno}.html")
    with open(p_html, "w", encoding="utf-8") as f:
        f.write(pagina)
    return p_csv, p_html


def pubblica_sito(cartella, p_html):
    """Copia il report del giorno come index.html e aggiorna l'elenco dell'archivio."""
    os.makedirs(cartella, exist_ok=True)
    open(os.path.join(cartella, ".nojekyll"), "w").close()
    pagina = open(p_html, encoding="utf-8").read()
    pagina = pagina.replace("</h2>", "</h2><p><a href='archivio/index.html'>Archivio dei giorni precedenti</a></p>", 1)
    with open(os.path.join(cartella, "index.html"), "w", encoding="utf-8") as f:
        f.write(pagina)
    arch = os.path.join(cartella, "archivio")
    giorni = sorted((x for x in os.listdir(arch) if x.endswith(".html") and x != "index.html"), reverse=True)
    voci = "".join(f"<li><a href='{x}'>{x[7:17]}</a></li>" for x in giorni)
    with open(os.path.join(arch, "index.html"), "w", encoding="utf-8") as f:
        f.write("<!doctype html><html lang='it'><meta charset='utf-8'><meta name='viewport' content='width=device-width,initial-scale=1'>"
                "<title>Archivio classifiche</title><body style='font-family:Arial,sans-serif;margin:20px'>"
                f"<h2>Archivio classifiche Over 1,5</h2><p><a href='../index.html'>Classifica di oggi</a></p><ul>{voci}</ul></body></html>")
    print(f"Sito aggiornato in {cartella}")


def invia_telegram(testo):
    if not (TELEGRAM_TOKEN and TELEGRAM_CHAT_ID):
        return False
    dati = urllib.parse.urlencode({"chat_id": TELEGRAM_CHAT_ID, "text": testo}).encode()
    try:
        urllib.request.urlopen(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage", dati, timeout=30)
        print("Messaggio Telegram inviato.")
        return True
    except Exception as e:
        print("Telegram: invio non riuscito –", e)
        return False


def telegram(righe):
    giorno = datetime.now(TZ).strftime("%d/%m")
    if not righe:
        invia_telegram(f"⚽ Over 1,5 – {giorno}\nNessuna partita oggi nei campionati selezionati.")
        return
    migliori = sorted(righe, key=lambda r: r["pos"])[:TOP_TELEGRAM]
    testo = f"⚽ Over 1,5 – classifica del {giorno} (top {len(migliori)})\n\n"
    for r in migliori:
        testo += (f"{r['pos']}. {r['ora'][-5:]}  {r['partita']}\n"
                  f"    {r['campionato']} · scenario {r['pscenario']:.0%} "
                  f"(0-0 al {MINUTO_0_0}' {pc(r['p00'])}, poi Over {pc(r['pover'])})"
                  + (f"  ⚠ {nota(r)}" if nota(r) else "") + "\n")
    if PAGINA_URL:
        testo += f"\nClassifica completa: {PAGINA_URL}"
    invia_telegram(testo)


def configura_telegram():
    """Procedura guidata: chiede il token del bot Telegram, trova il chat ID e manda un messaggio di prova."""
    global TELEGRAM_TOKEN, TELEGRAM_CHAT_ID
    conf = json.load(open(FILE_CONFIG, encoding="utf-8")) if os.path.exists(FILE_CONFIG) else {}
    print("CONFIGURAZIONE TELEGRAM\n")
    print("1) Su Telegram apri @BotFather, invia /newbot e segui le istruzioni.")
    print("   Alla fine BotFather ti dà un token (es. 123456789:ABCdef...).\n")
    TELEGRAM_TOKEN = input("Incolla qui il token e premi Invio: ").strip()
    print("\n2) Ora apri su Telegram il bot che hai appena creato e mandagli un messaggio qualsiasi (es. ciao).")
    input("   Fatto? Premi Invio…")
    try:
        with urllib.request.urlopen(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates", timeout=30) as r:
            agg = json.loads(r.read().decode()).get("result", [])
        chat = [u["message"]["chat"]["id"] for u in agg if "message" in u]
    except Exception as e:
        raise SystemExit(f"Token non valido o Telegram non raggiungibile ({e}).")
    if not chat:
        raise SystemExit("Nessun messaggio trovato: scrivi al tuo bot su Telegram e rilancia la configurazione.")
    TELEGRAM_CHAT_ID = str(chat[-1])
    conf.update({"telegram_token": TELEGRAM_TOKEN, "telegram_chat_id": TELEGRAM_CHAT_ID})
    with open(FILE_CONFIG, "w", encoding="utf-8") as f:
        json.dump(conf, f, indent=2)
    if invia_telegram("✅ Bot Over 1,5 collegato: riceverai qui la classifica ogni giorno."):
        print("\nTutto pronto: controlla Telegram, dovresti aver ricevuto un messaggio di prova.")


def carica_configurazione(automatico=False):
    """Legge Telegram da configurazione.json; al primo avvio a mano propone di collegarlo."""
    global TELEGRAM_TOKEN, TELEGRAM_CHAT_ID
    conf = {}
    if os.path.exists(FILE_CONFIG):
        with open(FILE_CONFIG, encoding="utf-8") as f:
            conf = json.load(f)
    global API_FOOTBALL_KEY
    TELEGRAM_TOKEN = TELEGRAM_TOKEN or conf.get("telegram_token", "")
    TELEGRAM_CHAT_ID = TELEGRAM_CHAT_ID or conf.get("telegram_chat_id", "")
    API_FOOTBALL_KEY = API_FOOTBALL_KEY or conf.get("api_football_key", "")
    if not automatico and not API_FOOTBALL_KEY and conf.get("chiedi_api_football", True):
        print("Facoltativo: con una chiave gratuita di API-Football (api-football.com) il bot aggiunge le serie B")
        print("e i campionati europei mancanti.")
        chiave = input("Incolla la chiave e premi Invio, oppure premi solo Invio per saltare: ").strip()
        if chiave:
            API_FOOTBALL_KEY = conf["api_football_key"] = chiave
        else:
            conf["chiedi_api_football"] = False
        with open(FILE_CONFIG, "w", encoding="utf-8") as f:
            json.dump(conf, f, indent=2)
        print()
    if not automatico and not TELEGRAM_TOKEN and conf.get("chiedi_telegram", True):
        risp = input("Vuoi ricevere la classifica ogni giorno su Telegram? (s/n): ").strip().lower()
        if risp.startswith("s"):
            configura_telegram()
            print()
        else:
            conf["chiedi_telegram"] = False
            with open(FILE_CONFIG, "w", encoding="utf-8") as f:
                json.dump(conf, f, indent=2)
            print("Ok. Potrai collegarlo in seguito con l'opzione --configura-telegram.\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--giorni", type=int, default=1, help="quanti giorni analizzare a partire da oggi")
    ap.add_argument("--demo", action="store_true", help="prova con dati inventati, senza internet")
    ap.add_argument("--automatico", action="store_true", help="avvio pianificato: niente browser né domande, solo report e Telegram")
    ap.add_argument("--web", metavar="CARTELLA", help="genera il sito (index.html + archivio) nella cartella indicata, per GitHub Pages")
    ap.add_argument("--prova-api-football", action="store_true", help="verifica la chiave API-Football e la stagione accessibile")
    ap.add_argument("--configura-telegram", action="store_true", help="procedura guidata per collegare Telegram")
    a = ap.parse_args()
    global AUTOMATICO
    AUTOMATICO = a.automatico or bool(a.web)
    if a.web:
        global CARTELLA_REPORT
        CARTELLA_REPORT = os.path.join(a.web, "archivio")
    if a.prova_api_football:
        carica_configurazione(automatico=True)
        prova_api_football()
        pausa(); return
    if a.configura_telegram:
        carica_configurazione(automatico=True) if os.path.exists(FILE_CONFIG) else None
        configura_telegram()
        pausa(); return
    if a.demo:
        righe = righe_demo()
    else:
        carica_configurazione(AUTOMATICO)
        print("Scarico i dati da football-data.co.uk…")
        righe = scarica(a.giorni)
    if not righe:
        print("Nessuna partita in programma nei campionati selezionati.")
        if a.web:
            p_csv, p_html = salva([])
            pubblica_sito(a.web, p_html)
        telegram([])
        pausa(); return
    p_csv, p_html = salva(righe)
    print(f"\nReport salvato:\n  {p_html}\n  {p_csv}\n\nPartite in ordine di orario:")
    for r in righe:
        print(f"  {r['ora']}  #{r['pos']:<3} {r['partita']:<30} 0-0 al {MINUTO_0_0}' {pc(r['p00']):>4}  "
              f"poi Over {pc(r['pover']):>4}  insieme {r['pscenario']:.1%}")
    if a.web:
        pubblica_sito(a.web, p_html)
    telegram(righe)
    if not AUTOMATICO:
        webbrowser.open(Path(p_html).resolve().as_uri())   # apre il report nel browser


AUTOMATICO = False


def pausa():
    """Tiene aperta la finestra quando il programma è stato avviato con doppio clic."""
    if AUTOMATICO:
        return
    if getattr(sys, "frozen", False) or len(sys.argv) == 1:
        try:
            input("\nPremi Invio per chiudere…")
        except EOFError:
            pass


if __name__ == "__main__":
    if "--automatico" in sys.argv:              # avvio pianificato: scrive tutto in bot_log.txt
        log = open(os.path.join(CARTELLA, "bot_log.txt"), "a", encoding="utf-8")
        sys.stdout = sys.stderr = log
        print(f"\n===== {datetime.now(TZ).strftime('%d/%m/%Y %H:%M')} =====")
    try:
        main()
    except SystemExit as e:
        if e.code not in (None, 0):
            print(e.code)
            if "--web" in sys.argv:
                sys.exit(1)
            pausa()
    except Exception as e:
        print("\nErrore:", e)
        if "--web" in sys.argv:
            invia_telegram(f"⚠️ Bot Over 1,5: errore durante l'analisi di oggi ({e}).")
            sys.exit(1)
        if "--automatico" in sys.argv:
            invia_telegram(f"⚠️ Bot Over 1,5: errore durante l'analisi di oggi ({e}).")
        pausa()
