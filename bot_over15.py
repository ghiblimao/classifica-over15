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

Dati: football-data.org (chiave gratuita).
Uso:   python bot_over15.py            (oggi, apre il report nel browser)
       python bot_over15.py --automatico       (avvio pianificato: report + Telegram, senza finestre)
       python bot_over15.py --configura-telegram (collega il tuo Telegram)
       python bot_over15.py --web docs         (usato da GitHub: crea la pagina web in docs/)
       python bot_over15.py --giorni 2 (oggi e domani)
       python bot_over15.py --demo     (prova con dati inventati, senza internet)
"""
import argparse, csv, json, math, os, random, sys, time, html, webbrowser
from pathlib import Path
import urllib.request, urllib.parse, urllib.error
from collections import defaultdict
from datetime import datetime, timedelta, timezone

# ======================================================================= CONFIG
API_KEY = os.environ.get("FOOTBALL_DATA_KEY", "")     # oppure scrivila qui tra le virgolette
CAMPIONATI = {"SA": "Serie A", "PL": "Premier League", "PD": "La Liga", "BL1": "Bundesliga",
              "FL1": "Ligue 1", "DED": "Eredivisie", "PPL": "Primeira Liga", "ELC": "Championship"}
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
except Exception:
    TZ = timezone(timedelta(hours=1))


def iso_dt(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


# ====================================================================== MODELLO
def quota_residua(t, s):
    """Frazione dei gol attesi che resta dal minuto t al 90' (s = quota di gol del 1° tempo)."""
    if t <= 45:
        return s * (45 - t) / 45 + (1 - s)
    return (1 - s) * max(0, 90 - t) / 45


def costruisci_modello(finite):
    gh = [m["score"]["fullTime"]["home"] for m in finite]
    ga = [m["score"]["fullTime"]["away"] for m in finite]
    H, A = sum(gh) / len(finite), sum(ga) / len(finite)
    ht = [(m["score"]["halfTime"]["home"] or 0) + (m["score"]["halfTime"]["away"] or 0) for m in finite]
    tot = sum(gh) + sum(ga)
    s = sum(ht) / tot if tot else 0.45            # quota di gol segnati nel 1° tempo nel campionato
    d = defaultdict(lambda: {"hn": 0, "hf": 0, "hs": 0, "an": 0, "af": 0, "as": 0})
    for m, h, a in zip(finite, gh, ga):
        th, ta = m["homeTeam"]["name"], m["awayTeam"]["name"]
        d[th]["hn"] += 1; d[th]["hf"] += h; d[th]["hs"] += a
        d[ta]["an"] += 1; d[ta]["af"] += a; d[ta]["as"] += h
    forza = {t: {"att_casa": (v["hf"] + SHRINK * H) / (v["hn"] + SHRINK) / H,
                 "dif_casa": (v["hs"] + SHRINK * A) / (v["hn"] + SHRINK) / A,
                 "att_trasf": (v["af"] + SHRINK * A) / (v["an"] + SHRINK) / A,
                 "dif_trasf": (v["as"] + SHRINK * H) / (v["an"] + SHRINK) / H,
                 "giocate": v["hn"] + v["an"]} for t, v in d.items()}
    return {"H": H, "A": A, "s": s, "forza": forza}


def analizza(match, mod, campionato):
    casa, trasf = match["homeTeam"]["name"], match["awayTeam"]["name"]
    neutro = {"att_casa": 1, "dif_casa": 1, "att_trasf": 1, "dif_trasf": 1, "giocate": 0}
    fc, ft = mod["forza"].get(casa, neutro), mod["forza"].get(trasf, neutro)
    lam = mod["H"] * fc["att_casa"] * ft["dif_trasf"] + mod["A"] * ft["att_trasf"] * fc["dif_casa"]
    resto = lam * quota_residua(MINUTO_0_0, mod["s"])      # gol attesi dal 20' al 90'
    p00 = math.exp(-(lam - resto))                         # nessun gol nei primi 20'
    pover = 1 - math.exp(-resto) * (1 + resto)             # almeno 2 gol dal 20' in poi
    kickoff = iso_dt(match["utcDate"])
    return {"ora": kickoff.astimezone(TZ).strftime("%d/%m %H:%M"), "_kickoff": kickoff,
            "campionato": campionato, "partita": f"{casa} - {trasf}", "gol_attesi": lam,
            "p00": p00, "pover": pover, "pscenario": p00 * pover,
            "affidabile": min(fc["giocate"], ft["giocate"]) >= MIN_PARTITE_SQUADRA}


# ========================================================= FOOTBALL-DATA.ORG
def fd_get(path):
    req = urllib.request.Request("https://api.football-data.org/v4" + path, headers={"X-Auth-Token": API_KEY})
    for _ in range(3):
        try:
            with urllib.request.urlopen(req, timeout=30) as r:
                return json.loads(r.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            if e.code == 429:                     # troppe richieste: aspetta e riprova
                time.sleep(65); continue
            raise
    raise RuntimeError("football-data.org non raggiungibile")


def scarica(giorni):
    oggi = datetime.now(TZ).date()
    date_ok = {oggi + timedelta(days=i) for i in range(giorni)}
    righe = []
    for i, (codice, nome) in enumerate(CAMPIONATI.items()):
        if i: time.sleep(6.5)                     # piano gratuito: max 10 richieste al minuto
        try:
            partite = fd_get(f"/competitions/{codice}/matches").get("matches", [])
        except Exception as e:
            print(f"  ! {nome}: errore ({e})"); continue
        finite = [m for m in partite if m["status"] == "FINISHED" and m["score"]["fullTime"]["home"] is not None]
        prossime = [m for m in partite if m["status"] in ("SCHEDULED", "TIMED")
                    and iso_dt(m["utcDate"]).astimezone(TZ).date() in date_ok]
        print(f"  {nome}: {len(finite)} giocate, {len(prossime)} in programma")
        if len(finite) >= 20 and prossime:
            mod = costruisci_modello(finite)
            righe += [analizza(m, mod, nome) for m in prossime]
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
            finite.append({"homeTeam": {"name": h}, "awayTeam": {"name": a},
                           "score": {"fullTime": {"home": gh, "away": ga},
                                     "halfTime": {"home": min(gh, pois(0.65)), "away": min(ga, pois(0.5))}}})
    mod = costruisci_modello(finite)
    base = datetime.now(timezone.utc).replace(hour=14, minute=0, second=0, microsecond=0)
    prossime = [{"homeTeam": {"name": squadre[i]}, "awayTeam": {"name": squadre[i + 1]},
                 "utcDate": (base + timedelta(hours=i // 8)).isoformat().replace("+00:00", "Z")} for i in range(0, 20, 2)]
    return [analizza(m, mod, "Campionato DEMO") for m in prossime]


# ===================================================================== OUTPUT
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
                    f"P Over 1,5 se 0-0 al {MINUTO_0_0}'", "P scenario completo", "Dati affidabili"])
        for r in righe:
            w.writerow([r["ora"], r["pos"], r["campionato"], r["partita"], f"{r['gol_attesi']:.2f}".replace(".", ","),
                        pc(r["p00"]), pc(r["pover"]), f"{r['pscenario']:.1%}".replace(".", ","),
                        "sì" if r["affidabile"] else "NO"])
    corpo = "".join(
        f"<tr{'' if r['affidabile'] else ' class=poco'}><td>{r['ora']}</td>"
        f"<td{' class=top' if r['pos'] <= TOP_TELEGRAM else ''}>{r['pos']}</td><td>{html.escape(r['campionato'])}</td>"
        f"<td class=p>{html.escape(r['partita'])}</td><td>{r['gol_attesi']:.2f}</td><td>{pc(r['p00'])}</td>"
        f"<td>{pc(r['pover'])}</td><td class=v>{r['pscenario']:.1%}</td></tr>" for r in righe) or \
        "<tr><td colspan=8>Nessuna partita oggi nei campionati selezionati.</td></tr>"
    pagina = f"""<!doctype html><html lang="it"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Over 1,5 – {giorno}</title><style>
body{{font-family:Arial,sans-serif;margin:20px;color:#222}} table{{border-collapse:collapse;font-size:14px}}
th,td{{border:1px solid #ccc;padding:6px 9px;text-align:center}} th{{background:#1F3864;color:#fff}}
td.p{{text-align:left;font-weight:bold}} td.v{{font-weight:bold;background:#DDEBF7}} td.top{{font-weight:bold;background:#E2EFDA}}
tr.poco{{color:#999}} .wrap{{overflow-x:auto}} p{{max-width:820px;font-size:13px}}</style>
<h2>Partite del {giorno} più adatte alla strategia</h2>
<p><b>P 0-0 al {MINUTO_0_0}'</b> = probabilità che la partita sia ancora 0-0 al {MINUTO_0_0}'.
<b>P Over 1,5 se 0-0</b> = probabilità che da lì arrivino almeno 2 gol.
<b>P scenario completo</b> = le due cose insieme. Partite in ordine di orario; <b>Classifica</b> = posizione per
P scenario completo (1 = la migliore del giorno), con le prime {TOP_TELEGRAM} evidenziate.
Righe grigie = squadre con poche partite giocate, stima poco affidabile.</p>
<div class="wrap"><table><tr><th>Ora</th><th>Classifica</th><th>Campionato</th><th>Partita</th><th>Gol attesi</th>
<th>P 0-0 al {MINUTO_0_0}'</th><th>P Over 1,5 se 0-0</th><th>P scenario completo</th></tr>{corpo}</table></div>
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
                  + ("  ⚠ pochi dati" if not r["affidabile"] else "") + "\n")
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
    conf.setdefault("football_data_key", API_KEY)
    with open(FILE_CONFIG, "w", encoding="utf-8") as f:
        json.dump(conf, f, indent=2)
    if invia_telegram("✅ Bot Over 1,5 collegato: riceverai qui la classifica ogni giorno."):
        print("\nTutto pronto: controlla Telegram, dovresti aver ricevuto un messaggio di prova.")


def carica_configurazione(automatico=False):
    """Legge la chiave API (e Telegram) da configurazione.json; al primo avvio la chiede e la salva."""
    global API_KEY, TELEGRAM_TOKEN, TELEGRAM_CHAT_ID
    conf = {}
    if os.path.exists(FILE_CONFIG):
        with open(FILE_CONFIG, encoding="utf-8") as f:
            conf = json.load(f)
    API_KEY = API_KEY or conf.get("football_data_key", "")
    TELEGRAM_TOKEN = TELEGRAM_TOKEN or conf.get("telegram_token", "")
    TELEGRAM_CHAT_ID = TELEGRAM_CHAT_ID or conf.get("telegram_chat_id", "")
    if not API_KEY and automatico:
        raise SystemExit("Manca la chiave football-data.org: avvia il programma una volta a mano per inserirla.")
    if not API_KEY:
        print("Primo avvio: serve la tua chiave gratuita di football-data.org")
        print("(la ricevi via email dopo la registrazione su https://www.football-data.org)\n")
        API_KEY = input("Incolla qui la chiave e premi Invio: ").strip()
        if not API_KEY:
            raise SystemExit("Nessuna chiave inserita.")
        conf.setdefault("telegram_token", ""); conf.setdefault("telegram_chat_id", "")
        conf["football_data_key"] = API_KEY
        with open(FILE_CONFIG, "w", encoding="utf-8") as f:
            json.dump(conf, f, indent=2)
        print(f"Chiave salvata in {FILE_CONFIG}\n")
    if not automatico and not TELEGRAM_TOKEN and conf.get("chiedi_telegram", True):
        risp = input("Vuoi ricevere la classifica ogni giorno su Telegram? (s/n): ").strip().lower()
        if risp.startswith("s"):
            configura_telegram()
            print()
        else:
            conf["chiedi_telegram"] = False
            conf["football_data_key"] = API_KEY
            with open(FILE_CONFIG, "w", encoding="utf-8") as f:
                json.dump(conf, f, indent=2)
            print("Ok. Potrai collegarlo in seguito con l'opzione --configura-telegram.\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--giorni", type=int, default=1, help="quanti giorni analizzare a partire da oggi")
    ap.add_argument("--demo", action="store_true", help="prova con dati inventati, senza internet")
    ap.add_argument("--automatico", action="store_true", help="avvio pianificato: niente browser né domande, solo report e Telegram")
    ap.add_argument("--web", metavar="CARTELLA", help="genera il sito (index.html + archivio) nella cartella indicata, per GitHub Pages")
    ap.add_argument("--configura-telegram", action="store_true", help="procedura guidata per collegare Telegram")
    a = ap.parse_args()
    global AUTOMATICO
    AUTOMATICO = a.automatico or bool(a.web)
    if a.web:
        global CARTELLA_REPORT
        CARTELLA_REPORT = os.path.join(a.web, "archivio")
    if a.configura_telegram:
        carica_configurazione(automatico=True) if os.path.exists(FILE_CONFIG) else None
        configura_telegram()
        pausa(); return
    if a.demo:
        righe = righe_demo()
    else:
        carica_configurazione(AUTOMATICO)
        print("Scarico i dati da football-data.org…")
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
