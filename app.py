import copy
import math
import json
import urllib.request
import urllib.parse
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta

import streamlit as st

# ── Konstanten ────────────────────────────────────────────────────────────────
CARBS_PRO_STUNDE = {"Z1": 30, "Z2": 60, "Z3": 75, "Z4": 90, "Z5": 90, "Mix": 70}
INTENSITAETS_FAKTOR = {"Z1": 0.85, "Z2": 1.0, "Z3": 1.15, "Z4": 1.25, "Z5": 1.3, "Mix": 1.1}
SONNEN_FAKTOR = {"keine": 1.0, "mittel": 1.1, "stark": 1.2}
POWER_ZONEN = [(0.55, "Z1"), (0.75, "Z2"), (0.90, "Z3"), (1.05, "Z4"), (float("inf"), "Z5")]
HF_ZONEN = [(0.60, "Z1"), (0.70, "Z2"), (0.80, "Z3"), (0.90, "Z4"), (float("inf"), "Z5")]
CARB_ANTEIL_NACH_PCT_FTP = [(0.55, 0.35), (0.75, 0.50), (0.90, 0.72), (1.05, 0.87), (float("inf"), 0.95)]
WIRKUNGSGRAD = 0.22
HOEHENMETER_CARBS_BONUS_PRO_100HM = 8
AUFFUELL_BUFFER_PCT = 0.82
POI_SUCHRADIUS_M = 3000
POI_TYP_NAMEN = {
    "fuel": "Tankstelle", "supermarket": "Supermarkt", "convenience": "Kiosk",
    "grocery": "Lebensmittel", "bakery": "Bäckerei", "chemist": "Drogerie",
}
SCHWEISSRATEN_PRESETS = {
    "wenig":  [[10, 150], [15, 200], [20, 250], [25, 320], [99, 420]],
    "mittel": [[10, 250], [15, 300], [20, 350], [25, 450], [99, 600]],
    "viel":   [[10, 380], [15, 500], [20, 630], [25, 800], [99, 1000]],
}

DEFAULT_PROFIL = {
    "name": "Mein Profil",
    "ftp_watt": 270,
    "hr_max": None,
    "schweissrate": {
        "preset": "mittel",
        "kalibriert_ml_h": [[10, 250], [15, 300], [20, 350], [25, 450], [99, 600]],
    },
    "flaschen": [{"name": "Trinkflasche", "volumen_ml": 950, "anzahl": 2}],
    "softflask": {
        "volumen_ml": 450, "max_anzahl": 4, "gel_anteil_pct": 70,
        "malto_ratio": 2, "fructose_ratio": 1,
        "salz_normal_g": 0.7, "salz_heiss_g": 1.0, "temp_heiss_grad": 25,
    },
    "riegel": [
        {"name": "Mango Fruchtriegel", "carbs_g": 30, "zucker_g": 18, "gewicht_g": 40, "aktiv": True},
        {"name": "Hafer-Heidelbeere",  "carbs_g": 40, "zucker_g": 12, "gewicht_g": 50, "aktiv": True},
    ],
    "elektrolyte": {
        "name": "Raab Elektrolyt-Pulver",
        "portion_normal_g": 3.5,
        "portion_heiss_g": 7.0,
        "temp_heiss_grad": 20,
        "mineralien_pro_portion_mg": {
            "natrium": 0, "kalium": 0, "chlorid": 0, "calcium": 0, "magnesium": 0,
        },
    },
    "koffein": {"pro_cap_mg": 50, "aktiv": True},
}

# ── Backend-Funktionen ────────────────────────────────────────────────────────

def watts_zu_zone(watt, ftp):
    pct = watt / ftp
    for grenze, zone in POWER_ZONEN:
        if pct <= grenze:
            return zone
    return "Z5"

def hf_zu_zone(hf, hr_max):
    pct = hf / hr_max
    for grenze, zone in HF_ZONEN:
        if pct <= grenze:
            return zone
    return "Z5"

def berechne_carbs_pro_h_aus_watt(watt, ftp):
    pct_ftp = watt / ftp
    kcal_pro_h = (watt * 3600) / (4180 * WIRKUNGSGRAD)
    carb_anteil = 0.50
    for grenze, anteil in CARB_ANTEIL_NACH_PCT_FTP:
        if pct_ftp <= grenze:
            carb_anteil = anteil
            break
    return round(min((kcal_pro_h * carb_anteil) / 4.0, 120))

def get_schweissrate_ml_h(profil, temp):
    preset = profil["schweissrate"]["preset"]
    raten = (profil["schweissrate"].get("kalibriert_ml_h")
             if preset == "kalibriert"
             else SCHWEISSRATEN_PRESETS.get(preset, SCHWEISSRATEN_PRESETS["mittel"]))
    basis = raten[-1][1]
    for bis_grad, ml_h in raten:
        if temp < bis_grad:
            basis = ml_h
            break
    return basis

def berechne_wasser_pro_stunde(profil, temp, sonne, indoor, zone, frueh_start):
    basis = get_schweissrate_ml_h(profil, temp)
    faktor = (SONNEN_FAKTOR.get(sonne, 1.0)
              * INTENSITAETS_FAKTOR.get(zone, 1.0)
              * (1.3 if indoor else 1.0)
              * (0.9 if frueh_start else 1.0))
    return round(basis * faktor)

def berechne_gel_rezept(profil, carbs_pro_flask, temp):
    sf = profil["softflask"]
    total = sf["malto_ratio"] + sf["fructose_ratio"]
    malto = round(carbs_pro_flask * sf["malto_ratio"] / total)
    fructose = round(carbs_pro_flask * sf["fructose_ratio"] / total)
    salz = sf["salz_heiss_g"] if temp > sf["temp_heiss_grad"] else sf["salz_normal_g"]
    wasser = sf["volumen_ml"] - carbs_pro_flask - 1
    return {"maltodextrin": malto, "fructose": fructose, "salz": salz, "wasser": max(0, wasser)}

def berechne_koffein(profil, dauer_h):
    if not profil["koffein"]["aktiv"]:
        return {"caps": 0, "plan": "Koffein deaktiviert"}
    mg = profil["koffein"]["pro_cap_mg"]
    if dauer_h < 2:   return {"caps": 0, "plan": "Nicht nötig (< 2 h)"}
    elif dauer_h < 4: return {"caps": 1, "plan": f"1 Cap ({mg} mg) nach Stunde 2"}
    elif dauer_h < 6: return {"caps": 2, "plan": f"Stunde 2 und 4 (je {mg} mg)"}
    elif dauer_h < 8: return {"caps": 4, "plan": f"Stunde 1, 4, 6, 8 (je {mg} mg)"}
    else:             return {"caps": 5, "plan": f"Stunde 1, 4, 7, 9 (Doppel), 11"}

def berechne_riegel_plan(profil, carbs_aus_riegeln, dauer_h, zone):
    aktive = [r for r in profil["riegel"] if r["aktiv"]]
    if not aktive or carbs_aus_riegeln <= 0:
        return []
    carbs_pro_runde = sum(r["carbs_g"] for r in aktive)
    runden = math.ceil(carbs_aus_riegeln / carbs_pro_runde) if carbs_pro_runde > 0 else 1
    return [
        {"name": r["name"], "anzahl": runden,
         "carbs_g_pro_stueck": r["carbs_g"], "carbs_gesamt": runden * r["carbs_g"],
         "zucker_g_pro_stueck": r.get("zucker_g", 0), "zucker_gesamt": runden * r.get("zucker_g", 0)}
        for r in aktive
    ]

def berechne_alles(profil, dauer_h, zone, temp, sonne, indoor, frueh_start,
                   distanz_km=None, hoehenmeter=None, watt=None, ftp=None, hf=None):
    if watt and ftp:
        carbs_pro_h = berechne_carbs_pro_h_aus_watt(watt, ftp)
        carbs_quelle = f"Watt ({watt} W @ FTP {ftp} W)"
    else:
        carbs_pro_h = CARBS_PRO_STUNDE.get(zone, 60)
        carbs_quelle = f"Zone {zone}"
    carbs_basis = round(carbs_pro_h * dauer_h)
    hm_bonus = round(hoehenmeter / 100 * HOEHENMETER_CARBS_BONUS_PRO_100HM) if hoehenmeter else 0
    carbs_gesamt = carbs_basis + hm_bonus
    wasser_pro_h = berechne_wasser_pro_stunde(profil, temp, sonne, indoor, zone, frueh_start)
    wasser_gesamt = round(wasser_pro_h * dauer_h)
    sf = profil["softflask"]
    gel_anteil = sf["gel_anteil_pct"] / 100
    carbs_aus_gels = round(carbs_gesamt * gel_anteil)
    carbs_aus_riegeln = carbs_gesamt - carbs_aus_gels
    anzahl_flasks = min(sf["max_anzahl"], max(1,
        1 if carbs_gesamt <= 70 else 2 if carbs_gesamt <= 200 else
        3 if carbs_gesamt <= 400 else sf["max_anzahl"]))
    carbs_pro_flask = round(carbs_aus_gels / anzahl_flasks)
    wasser_aus_gels = anzahl_flasks * round(sf["volumen_ml"] * 0.69)
    flaschen_kapazitaet_ml = sum(f["volumen_ml"] * f["anzahl"] for f in profil["flaschen"])
    refill_ml = max(f["volumen_ml"] for f in profil["flaschen"]) if profil["flaschen"] else 950
    wasser_zusaetzlich = max(0, wasser_gesamt - wasser_aus_gels)
    auffuellungen_noetig = (max(0, math.ceil(
        (wasser_zusaetzlich - flaschen_kapazitaet_ml) / refill_ml
    )) if wasser_zusaetzlich > flaschen_kapazitaet_ml else 0)
    el = profil["elektrolyte"]
    el_portion = el["portion_heiss_g"] if temp > el["temp_heiss_grad"] else el["portion_normal_g"]
    fuellungen = (1 if flaschen_kapazitaet_ml > 0 else 0) + auffuellungen_noetig
    el_gesamt = fuellungen * el_portion
    min_profil = el.get("mineralien_pro_portion_mg", {})
    mineralien_gesamt = {m: round(min_profil.get(m, 0) * fuellungen)
                         for m in ("natrium", "kalium", "chlorid", "calcium", "magnesium")}
    if temp > el["temp_heiss_grad"] and el["portion_normal_g"] > 0:
        faktor_heiss = el["portion_heiss_g"] / el["portion_normal_g"]
        mineralien_gesamt = {m: round(v * faktor_heiss) for m, v in mineralien_gesamt.items()}
    riegel_plan = berechne_riegel_plan(profil, carbs_aus_riegeln, dauer_h, zone)
    koffein = berechne_koffein(profil, dauer_h)
    return {
        "profil_name": profil["name"], "dauer_h": dauer_h, "zone": zone, "temp": temp,
        "watt": watt, "ftp": ftp, "hf": hf, "hr_max": profil.get("hr_max"),
        "carbs": {"pro_h": carbs_pro_h, "gesamt": carbs_gesamt, "basis": carbs_basis,
                  "hm_bonus": hm_bonus, "aus_gels": carbs_aus_gels,
                  "aus_riegeln": carbs_aus_riegeln, "quelle": carbs_quelle},
        "wasser": {"pro_h": wasser_pro_h, "gesamt": wasser_gesamt, "aus_gels": wasser_aus_gels,
                   "zusaetzlich": wasser_zusaetzlich, "flaschen_kapazitaet_ml": flaschen_kapazitaet_ml,
                   "refill_ml": refill_ml},
        "softflasks": {"anzahl": anzahl_flasks, "carbs_pro_flask": carbs_pro_flask,
                       "rezept": berechne_gel_rezept(profil, carbs_pro_flask, temp)},
        "riegel": riegel_plan,
        "wasserflaschen": {"konfiguration": profil["flaschen"], "kapazitaet_ml": flaschen_kapazitaet_ml,
                           "auffuellungen": auffuellungen_noetig, "refill_ml": refill_ml},
        "elektrolyte": {"name": el["name"], "portion_g": el_portion, "gesamt_g": el_gesamt,
                        "fuellungen": fuellungen, "mineralien": mineralien_gesamt,
                        "min_pro_portion": min_profil},
        "koffein": koffein, "distanz_km": distanz_km, "hoehenmeter": hoehenmeter,
    }

def hole_wetterdaten(latitude, longitude, datum, start_h, dauer_h):
    end_h = min(23, int(start_h + dauer_h + 1))
    params = {
        "latitude": latitude, "longitude": longitude,
        "hourly": "temperature_2m,relative_humidity_2m,precipitation,wind_speed_10m,cloud_cover,uv_index",
        "timezone": "Europe/Berlin", "start_date": datum, "end_date": datum,
    }
    url = "https://api.open-meteo.com/v1/forecast?" + urllib.parse.urlencode(params)
    try:
        with urllib.request.urlopen(url, timeout=10) as r:
            data = json.loads(r.read().decode())
        zeiten = data["hourly"]["time"]
        result = {k: [] for k in ("stunden", "temperaturen", "luftfeuchte", "niederschlag", "wind", "wolken", "uv")}
        for i, z in enumerate(zeiten):
            h = int(z.split("T")[1].split(":")[0])
            if start_h <= h <= end_h:
                result["stunden"].append(h)
                result["temperaturen"].append(data["hourly"]["temperature_2m"][i])
                result["luftfeuchte"].append(data["hourly"]["relative_humidity_2m"][i])
                result["niederschlag"].append(data["hourly"]["precipitation"][i])
                result["wind"].append(data["hourly"]["wind_speed_10m"][i])
                result["wolken"].append(data["hourly"]["cloud_cover"][i])
                result["uv"].append(data["hourly"]["uv_index"][i])
        return result
    except Exception:
        return None

def berechne_durchschnitts_wetter(wetter):
    if not wetter or not wetter["temperaturen"]:
        return None
    n = len(wetter["temperaturen"])
    avg_temp = sum(wetter["temperaturen"]) / n
    avg_wolken = sum(wetter["wolken"]) / n
    avg_wind = sum(wetter["wind"]) / n
    sonne = ("keine" if avg_wolken > 70 or max(wetter["uv"]) < 3
             else "mittel" if avg_wolken > 30 or max(wetter["uv"]) < 6 else "stark")
    return {
        "avg_temp": round(avg_temp, 1), "min_temp": min(wetter["temperaturen"]),
        "max_temp": max(wetter["temperaturen"]), "avg_wolken": round(avg_wolken),
        "avg_wind": round(avg_wind, 1), "max_uv": round(max(wetter["uv"]), 1),
        "sum_regen": round(sum(wetter["niederschlag"]), 1), "sonne": sonne,
    }

def parse_gpx(gpx_bytes):
    try:
        root = ET.fromstring(gpx_bytes)
        ns = {"gpx": "http://www.topografix.com/GPX/1/1"}
        name_el = root.find(".//gpx:trk/gpx:name", ns)
        name = name_el.text if name_el is not None else "Unbekannte Route"
        points = []
        for trkpt in root.findall(".//gpx:trkpt", ns):
            lat, lon = float(trkpt.get("lat")), float(trkpt.get("lon"))
            ele_el = trkpt.find("gpx:ele", ns)
            ele = float(ele_el.text) if ele_el is not None else 0
            points.append((lat, lon, ele))
        if not points:
            return None
        def hav(la1, lo1, la2, lo2):
            R = 6371.0
            p1, p2 = math.radians(la1), math.radians(la2)
            a = (math.sin(math.radians(la2 - la1) / 2) ** 2
                 + math.cos(p1) * math.cos(p2) * math.sin(math.radians(lo2 - lo1) / 2) ** 2)
            return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
        dist_km, hm_auf, hm_ab, kum = 0, 0, 0, [0]
        for i in range(1, len(points)):
            la1, lo1, e1 = points[i - 1]
            la2, lo2, e2 = points[i]
            dist_km += hav(la1, lo1, la2, lo2)
            kum.append(dist_km)
            d = e2 - e1
            if d > 0: hm_auf += d
            else: hm_ab -= d
        return {
            "name": name, "distanz_km": round(dist_km, 1),
            "hoehenmeter_auf": round(hm_auf), "hoehenmeter_ab": round(hm_ab),
            "start_lat": points[0][0], "start_lon": points[0][1],
            "points": points, "kumulative_distanzen": kum,
        }
    except Exception:
        return None

def suche_nahe_pois(lat, lon, radius_m=3000):
    def _haversine_m(la1, lo1, la2, lo2):
        R = 6_371_000.0
        p1, p2 = math.radians(la1), math.radians(la2)
        dphi, dlam = math.radians(la2 - la1), math.radians(lo2 - lo1)
        a = math.sin(dphi / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dlam / 2) ** 2
        return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))
    query = (f"[out:json][timeout:12];("
             f'node["amenity"="fuel"](around:{radius_m},{lat},{lon});'
             f'node["amenity"="supermarket"](around:{radius_m},{lat},{lon});'
             f'node["shop"="supermarket"](around:{radius_m},{lat},{lon});'
             f'node["shop"="convenience"](around:{radius_m},{lat},{lon});'
             f'node["shop"="grocery"](around:{radius_m},{lat},{lon});'
             f'node["shop"="bakery"](around:{radius_m},{lat},{lon});'
             f");out body;")
    try:
        d = urllib.parse.urlencode({"data": query}).encode()
        req = urllib.request.Request(
            "https://overpass-api.de/api/interpreter", data=d, method="POST",
            headers={"User-Agent": "FuelingPlanner/2.0 (cycling nutrition)"},
        )
        with urllib.request.urlopen(req, timeout=14) as resp:
            els = json.loads(resp.read().decode()).get("elements", [])
        treffer = []
        for el in els:
            tags = el.get("tags", {})
            roh = tags.get("amenity") or tags.get("shop", "")
            treffer.append({
                "name": tags.get("name", "Unbekannt"),
                "typ": POI_TYP_NAMEN.get(roh, roh.capitalize()),
                "strasse": (tags.get("addr:street", "") + " " + tags.get("addr:housenumber", "")).strip(),
                "ort": tags.get("addr:city") or tags.get("addr:town") or tags.get("addr:village", ""),
                "dist_m": round(_haversine_m(lat, lon, el["lat"], el["lon"])),
            })
        treffer.sort(key=lambda x: x["dist_m"])
        return treffer[:3]
    except Exception:
        return []

def schaetze_dauer(distanz_km, hoehenmeter, zone="Z2"):
    v = {"Z1": 22, "Z2": 24, "Z3": 28, "Z4": 32, "Z5": 32, "Mix": 25}.get(zone, 24)
    return round(distanz_km / v + (hoehenmeter / 100) * (6 / 60), 1)

def erstelle_plan_text(e, wetter_info=None):
    lines = [
        "=== CYCLING FUELING PLAN ===",
        f"Profil:  {e['profil_name']}",
        f"Dauer:   {e['dauer_h']} h  |  Zone: {e['zone']}  |  Temp: {e['temp']} °C",
        "",
        "--- KOHLENHYDRATE ---",
        f"Gesamt:      {e['carbs']['gesamt']} g  ({e['carbs']['pro_h']} g/h via {e['carbs']['quelle']})",
        f"Basis:       {e['carbs']['basis']} g",
        f"HM-Bonus:    {e['carbs']['hm_bonus']} g",
        f"Aus Gels:    {e['carbs']['aus_gels']} g",
        f"Aus Riegeln: {e['carbs']['aus_riegeln']} g",
        "",
        "--- WASSER ---",
        f"Gesamt:      {e['wasser']['gesamt']} ml  ({e['wasser']['pro_h']} ml/h)",
        f"Aus Gels:    {e['wasser']['aus_gels']} ml",
        f"Flaschen:    {e['wasser']['zusaetzlich']} ml zusätzlich",
        "",
        "--- SOFTFLASKS ---",
        f"Anzahl:      {e['softflasks']['anzahl']}",
        f"Carbs/Flask: {e['softflasks']['carbs_pro_flask']} g",
        f"Rezept:      Malto {e['softflasks']['rezept']['maltodextrin']} g  |  "
        f"Fructose {e['softflasks']['rezept']['fructose']} g  |  "
        f"Salz {e['softflasks']['rezept']['salz']} g  |  "
        f"Wasser {e['softflasks']['rezept']['wasser']} ml",
        "",
    ]
    if e["riegel"]:
        lines.append("--- RIEGEL ---")
        for r in e["riegel"]:
            lines.append(f"  {r['name']}: {r['anzahl']}x  "
                         f"(Carbs: {r['carbs_gesamt']} g | Zucker: {r['zucker_gesamt']} g)")
        lines.append("")
    el = e["elektrolyte"]
    lines += [
        "--- ELEKTROLYTE ---",
        f"Produkt:  {el['name']}",
        f"Portion:  {el['portion_g']} g  x{el['fuellungen']}  =  {el['gesamt_g']} g",
        "",
        "--- KOFFEIN ---",
        f"Plan:     {e['koffein']['plan']}  ({e['koffein']['caps']} Caps)",
        "",
    ]
    if wetter_info:
        lines += [
            "--- WETTER ---",
            f"Temperatur: {wetter_info['avg_temp']} °C  (min {wetter_info['min_temp']} / max {wetter_info['max_temp']})",
            f"Sonne: {wetter_info['sonne']}  |  Wind: {wetter_info['avg_wind']} km/h  |  Regen: {wetter_info['sum_regen']} mm",
            "",
        ]
    lines.append("=== Ende des Plans ===")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# STREAMLIT APP
# ═══════════════════════════════════════════════════════════════════════════════

st.set_page_config(page_title="Cycling Fueling Planner", page_icon="🚴", layout="wide")

# Session-State initialisieren
if "profil" not in st.session_state:
    st.session_state.profil = copy.deepcopy(DEFAULT_PROFIL)
if "ergebnis" not in st.session_state:
    st.session_state.ergebnis = None
if "wetter_info" not in st.session_state:
    st.session_state.wetter_info = None
if "gpx_data" not in st.session_state:
    st.session_state.gpx_data = None
if "pois" not in st.session_state:
    st.session_state.pois = None

profil = st.session_state.profil

# ══════════════════════════════════════════════════════════════════════════════
# SIDEBAR – PROFIL EINSTELLUNGEN
# ══════════════════════════════════════════════════════════════════════════════

with st.sidebar:
    st.title("⚙️ Mein Profil")

    # ── Name ──
    profil["name"] = st.text_input("Name", value=profil["name"])

    # ── FTP ──
    profil["ftp_watt"] = st.slider(
        "FTP (Watt)",
        min_value=100, max_value=500, value=profil["ftp_watt"], step=5,
        help="Functional Threshold Power – deine Schwellenleistung in Watt. "
             "Wenn du keinen Leistungsmesser hast, lass den Standardwert."
    )

    # ── HRmax ──
    hr_val = st.number_input(
        "Max. Herzfrequenz (bpm) – optional",
        min_value=0, max_value=230,
        value=profil["hr_max"] if profil["hr_max"] else 0,
        step=1,
        help="Deine maximale Herzfrequenz in Schlägen pro Minute. "
             "Wenn eingetragen, kannst du den Plan auch per Herzfrequenz steuern. "
             "Leer lassen = Zone manuell oder per Watt."
    )
    profil["hr_max"] = int(hr_val) if hr_val > 0 else None

    st.divider()

    # ── Schweißrate ──
    st.subheader("💧 Schweißrate")
    st.caption(
        "Wie stark schwitzt du bei 20 °C?\n"
        "**Wenig** (~250 ml/h): Kaum nasse Kleidung, kein Salz im Gesicht\n"
        "**Mittel** (~350 ml/h): Normale Schweißmenge, Standardwert\n"
        "**Viel** (~630 ml/h): Stark nasse Kleidung, Salzkristalle, immer durstig"
    )
    sw_optionen = ["wenig", "mittel", "viel"]
    sw_labels = {
        "wenig": "🟢 Wenig schwitzen (~250 ml/h bei 20 °C)",
        "mittel": "🟡 Normal schwitzen (~350 ml/h bei 20 °C)",
        "viel":  "🔴 Stark schwitzen (~630 ml/h bei 20 °C)",
    }
    sw_idx = sw_optionen.index(profil["schweissrate"]["preset"]) if profil["schweissrate"]["preset"] in sw_optionen else 1
    sw_sel = st.selectbox(
        "Schweißtyp", sw_optionen, index=sw_idx,
        format_func=lambda x: sw_labels[x]
    )
    profil["schweissrate"]["preset"] = sw_sel

    st.divider()

    # ── Koffein ──
    st.subheader("☕ Koffein")
    profil["koffein"]["aktiv"] = st.checkbox(
        "Koffein einplanen",
        value=profil["koffein"]["aktiv"],
        help="Koffein verbessert die Ausdauerleistung ab Stunde 2–3. "
             "Das Skript plant automatisch den richtigen Zeitpunkt."
    )
    if profil["koffein"]["aktiv"]:
        profil["koffein"]["pro_cap_mg"] = st.number_input(
            "mg pro Kapsel", min_value=10, max_value=200,
            value=profil["koffein"]["pro_cap_mg"], step=5,
        )

    st.divider()

    # ── Wasserflaschen ──
    st.subheader("🚰 Wasserflaschen")
    for i, fl in enumerate(profil["flaschen"]):
        with st.expander(f"{fl['name']} (#{i+1})", expanded=True):
            fl["name"] = st.text_input("Bezeichnung", value=fl["name"], key=f"fl_name_{i}")
            cols = st.columns(2)
            fl["anzahl"] = cols[0].number_input("Anzahl", 0, 10, fl["anzahl"], key=f"fl_anz_{i}")
            fl["volumen_ml"] = cols[1].number_input(
                "Volumen (ml)", 100, 3000, fl["volumen_ml"], step=50, key=f"fl_vol_{i}"
            )
    c1, c2 = st.columns(2)
    if c1.button("➕ Flasche hinzufügen", use_container_width=True):
        profil["flaschen"].append({"name": f"Flasche {len(profil['flaschen'])+1}", "volumen_ml": 750, "anzahl": 1})
        st.rerun()
    if c2.button("➖ Letzte entfernen", use_container_width=True) and len(profil["flaschen"]) > 1:
        profil["flaschen"].pop()
        st.rerun()

    st.divider()

    # ── Riegel & Snacks ──
    st.subheader("🍫 Riegel & Snacks")
    st.caption("Trage hier deine mitgenommenen Riegel mit Nährwerten ein. "
               "Deaktivierte Riegel werden nicht eingeplant.")
    riegel_zu_loeschen = None
    for i, r in enumerate(profil["riegel"]):
        with st.expander(f"{'✅' if r['aktiv'] else '❌'} {r['name']}", expanded=False):
            r["aktiv"] = st.checkbox("Aktiv (einplanen)", value=r["aktiv"], key=f"r_aktiv_{i}")
            r["name"] = st.text_input("Name", value=r["name"], key=f"r_name_{i}")
            cols = st.columns(2)
            r["carbs_g"] = cols[0].number_input(
                "Kohlenhydrate (g)", 0, 150, r["carbs_g"], key=f"r_carbs_{i}",
                help="Kohlenhydrate pro Riegel laut Nährwerttabelle auf der Verpackung"
            )
            r["zucker_g"] = cols[1].number_input(
                "davon Zucker (g)", 0, 150, r.get("zucker_g", 0), key=f"r_zucker_{i}",
                help="Zuckeranteil aus der Nährwerttabelle (steht unter 'davon Zucker')"
            )
            if st.button(f"🗑️ Entfernen", key=f"r_del_{i}"):
                riegel_zu_loeschen = i

    if riegel_zu_loeschen is not None:
        profil["riegel"].pop(riegel_zu_loeschen)
        st.rerun()

    if st.button("➕ Riegel / Snack hinzufügen", use_container_width=True):
        profil["riegel"].append({
            "name": f"Neuer Riegel {len(profil['riegel'])+1}",
            "carbs_g": 35, "zucker_g": 10, "gewicht_g": 45, "aktiv": True,
        })
        st.rerun()

    st.divider()

    # ── Elektrolyte ──
    st.subheader("🧂 Elektrolyte")
    el = profil["elektrolyte"]
    el["name"] = st.text_input("Produktname", value=el["name"],
                                help="Name deines Elektrolyt-Pulvers oder -Tabletten")

    st.caption(
        "**Normalportion:** Die Dosierung laut Packungsanleitung für normale Bedingungen.\n\n"
        "**Heißwetterportion:** Viele Hersteller empfehlen bei Hitze eine höhere Dosis, "
        "weil man mehr schwitzt und damit mehr Mineralien verliert. "
        "Steht oft auf der Verpackung als 'bei starker Belastung' oder 'bei Hitze'.\n\n"
        "Wenn dein Produkt keine Unterscheidung macht: Beide Werte gleich setzen."
    )
    cols = st.columns(2)
    el["portion_normal_g"] = cols[0].number_input(
        "Normalportion (g)", 0.0, 50.0, float(el["portion_normal_g"]), step=0.5,
        help="Gramm pro Flasche/Portion bei normalen Temperaturen"
    )
    el["portion_heiss_g"] = cols[1].number_input(
        "Heißwetterportion (g)", 0.0, 50.0, float(el["portion_heiss_g"]), step=0.5,
        help="Gramm pro Flasche/Portion bei Hitze (höhere Dosierung)"
    )
    el["temp_heiss_grad"] = st.number_input(
        "Ab welcher Temperatur gilt 'Heiß'? (°C)", 10, 40, int(el["temp_heiss_grad"]),
        help="Ab dieser Außentemperatur wird automatisch die Heißwetterportion verwendet. "
             "Typisch: 20–25 °C. Schau auf die Packung deines Elektrolyt-Produkts."
    )

    st.caption("**Mineralien pro Normalportion** (optional – steht auf der Verpackung):")
    min_mg = el.get("mineralien_pro_portion_mg", {})
    mineral_labels = {
        "natrium": "Natrium (mg)",
        "kalium": "Kalium (mg)",
        "chlorid": "Chlorid (mg)",
        "calcium": "Calcium (mg)",
        "magnesium": "Magnesium (mg)",
    }
    for key, label in mineral_labels.items():
        min_mg[key] = st.number_input(
            label, min_value=0, max_value=5000,
            value=int(min_mg.get(key, 0)), step=10,
            key=f"min_{key}",
            help="Wert aus der Nährwerttabelle auf der Produktverpackung. 0 = nicht bekannt."
        )
    el["mineralien_pro_portion_mg"] = min_mg


# ══════════════════════════════════════════════════════════════════════════════
# HAUPTBEREICH
# ══════════════════════════════════════════════════════════════════════════════

st.title("🚴 Cycling Fueling Planner")
st.caption("Berechne deinen persönlichen Ernährungs- und Trinkplan für die nächste Ausfahrt.")

# ── GPX-Upload (AUSSERHALB des Formulars – funktioniert sonst nicht) ──────────
st.subheader("1. Route")
route_modus = st.radio(
    "Wie möchtest du deine Route eingeben?",
    ["Ohne GPX – Werte manuell eingeben", "GPX-Datei hochladen (von Komoot, Strava, Garmin …)"],
    horizontal=False,
)

gpx_data = None

if route_modus == "GPX-Datei hochladen (von Komoot, Strava, Garmin …)":
    st.caption(
        "Exportiere deine Route als GPX-Datei aus Komoot, Strava, Garmin Connect oder RideWithGPS "
        "und lade sie hier hoch. Distanz, Höhenmeter und Startkoordinaten werden automatisch ausgelesen."
    )
    uploaded_file = st.file_uploader(
        "GPX-Datei auswählen", type=["gpx"],
        help="Dateiformat: .gpx – kann aus den meisten Radsport-Apps exportiert werden"
    )
    if uploaded_file is not None:
        gpx_bytes = uploaded_file.read()
        gpx_data = parse_gpx(gpx_bytes)
        if gpx_data:
            st.success(
                f"✅ **{gpx_data['name']}** geladen – "
                f"{gpx_data['distanz_km']} km | {gpx_data['hoehenmeter_auf']} Hm aufwärts"
            )
            st.session_state.gpx_data = gpx_data
        else:
            st.error("❌ Die GPX-Datei konnte nicht gelesen werden. Bitte eine gültige .gpx-Datei hochladen.")
            st.session_state.gpx_data = None
    elif st.session_state.gpx_data:
        gpx_data = st.session_state.gpx_data
        st.info(f"GPX geladen: **{gpx_data['name']}** – {gpx_data['distanz_km']} km | {gpx_data['hoehenmeter_auf']} Hm")
else:
    st.session_state.gpx_data = None

st.divider()

# ── Hauptformular ─────────────────────────────────────────────────────────────
with st.form("planungsformular"):

    # Route-Details
    if gpx_data:
        distanz_km = gpx_data["distanz_km"]
        hoehenmeter = gpx_data["hoehenmeter_auf"]
        lat_default = gpx_data["start_lat"]
        lon_default = gpx_data["start_lon"]
        st.info(f"📍 Route: **{gpx_data['name']}** | {distanz_km} km | {hoehenmeter} Hm | "
                f"Start: {lat_default:.4f}° N, {lon_default:.4f}° O")
    else:
        st.subheader("Streckendaten")
        cols = st.columns(2)
        distanz_km = cols[0].number_input("Distanz (km)", 0.0, 500.0, 80.0, step=5.0)
        hoehenmeter = cols[1].number_input("Höhenmeter aufwärts (m)", 0, 8000, 800, step=100)
        lat_default, lon_default = 51.0, 10.0

    # ── Intensität ──────────────────────────────────────────────────────────
    st.subheader("2. Trainingsintensität")

    intensitaet_optionen = ["Zone manuell wählen", "Nach Wattleistung", "Nach Herzfrequenz"]
    if not profil["hr_max"]:
        intensitaet_optionen = intensitaet_optionen[:2]
        st.caption("💡 *Herzfrequenz-Option: HRmax im Profil (links) eintragen, um diese Option freizuschalten.*")

    intensitaet_modus = st.radio("Intensitätsmodus", intensitaet_optionen, horizontal=True)

    zone = "Z2"
    watt_eingabe = None
    hf_eingabe = None

    if intensitaet_modus == "Zone manuell wählen":
        zone_optionen = {
            "Z1": "Z1 – Erholung / sehr locker (30 g Carbs/h)",
            "Z2": "Z2 – Grundlage / aerob (60 g Carbs/h)",
            "Z3": "Z3 – Tempo / Sweetspot (75 g Carbs/h)",
            "Z4": "Z4 – Schwelle / hart (90 g Carbs/h)",
            "Z5": "Z5 – Maximalintensität (90 g Carbs/h)",
            "Mix": "Mix – wechselnde Intensität (70 g Carbs/h)",
        }
        zone = st.selectbox(
            "Trainingszone", list(zone_optionen.keys()),
            index=1, format_func=lambda x: zone_optionen[x]
        )
        if profil["hr_max"]:
            hr = profil["hr_max"]
            st.caption(
                f"**Deine HF-Zonen** bei HRmax {hr} bpm: "
                f"Z1 < {round(hr*0.60)} | Z2 {round(hr*0.60)}–{round(hr*0.70)} | "
                f"Z3 {round(hr*0.70)}–{round(hr*0.80)} | Z4 {round(hr*0.80)}–{round(hr*0.90)} | "
                f"Z5 > {round(hr*0.90)} bpm"
            )

    elif intensitaet_modus == "Nach Wattleistung":
        st.caption(f"FTP aus Profil: **{profil['ftp_watt']} W** – die Carbs-Menge wird physikalisch aus deiner Leistung berechnet.")
        watt_eingabe = st.number_input(
            "Durchschnittliche Leistung (Watt)", 50, 600,
            value=max(50, profil["ftp_watt"] - 30), step=5
        )
        zone = watts_zu_zone(watt_eingabe, profil["ftp_watt"])
        pct_ftp = round(watt_eingabe / profil["ftp_watt"] * 100)
        st.caption(f"→ **{watt_eingabe} W** = {pct_ftp}% FTP → Zone **{zone}**")

    elif intensitaet_modus == "Nach Herzfrequenz":
        hr = profil["hr_max"]
        st.caption(
            f"HRmax aus Profil: **{hr} bpm** | "
            f"Z1 < {round(hr*0.60)} | Z2 {round(hr*0.60)}–{round(hr*0.70)} | "
            f"Z3 {round(hr*0.70)}–{round(hr*0.80)} | Z4 {round(hr*0.80)}–{round(hr*0.90)} | "
            f"Z5 > {round(hr*0.90)} bpm"
        )
        hf_eingabe = st.number_input(
            "Durchschnittliche Herzfrequenz (bpm)", 60, 220,
            value=int(hr * 0.72), step=1
        )
        zone = hf_zu_zone(hf_eingabe, hr)
        pct_hrmax = round(hf_eingabe / hr * 100)
        st.caption(f"→ **{hf_eingabe} bpm** = {pct_hrmax}% HRmax → Zone **{zone}**")

    # ── Dauer ────────────────────────────────────────────────────────────────
    st.subheader("3. Trainingsdauer")
    dauer_schaetzung = None
    if distanz_km and hoehenmeter is not None:
        dauer_schaetzung = schaetze_dauer(float(distanz_km), float(hoehenmeter), zone if zone != "Mix" else "Z2")
    dauer_h = st.number_input(
        "Trainingsdauer in Stunden",
        min_value=0.5, max_value=24.0,
        value=float(dauer_schaetzung) if dauer_schaetzung else 3.0,
        step=0.25,
    )
    if dauer_schaetzung:
        st.caption(f"💡 Geschätzte Dauer aus Strecke + Höhenmetern: **{dauer_schaetzung} h**")

    # ── Wetter ───────────────────────────────────────────────────────────────
    st.subheader("4. Wetter")
    cols = st.columns(2)
    datum = cols[0].date_input("Trainingsdatum", value=datetime.today() + timedelta(days=1))
    start_h = cols[1].slider("Startzeit (Uhr)", 0, 23, 9)

    wetter_auto = st.checkbox(
        "🌤 Wetter automatisch abrufen (Open-Meteo API, kostenlos)",
        value=True,
        help="Ruft Temperatur, Wind, Sonne und Regen für dein Trainingsgebiet ab. "
             "Funktioniert nur mit Internetverbindung."
    )

    temp_manuell = 18
    sonne_manuell = "mittel"
    indoor = False

    if wetter_auto:
        if gpx_data:
            st.caption(f"📍 Wetterstandort: Startpunkt der GPX-Route ({gpx_data['start_lat']:.3f}°N, {gpx_data['start_lon']:.3f}°O) – automatisch übernommen.")
            lat = gpx_data["start_lat"]
            lon = gpx_data["start_lon"]
        else:
            with st.expander("📍 Standort für Wettervorhersage anpassen (optional)", expanded=False):
                st.caption(
                    "Hier kannst du den Startort deines Trainings eingeben, damit die Wettervorhersage "
                    "stimmt. Die Koordinaten findest du z.B. bei Google Maps (Rechtsklick auf den Startpunkt).\n\n"
                    "**Beispiele:** München: 48.14, 11.58 | Berlin: 52.52, 13.40 | Hamburg: 53.55, 10.00 | "
                    "Wien: 48.21, 16.37 | Zürich: 47.38, 8.54"
                )
                cols = st.columns(2)
                lat = cols[0].number_input("Breitengrad (z.B. 48.14 für München)", -90.0, 90.0, 51.0, format="%.4f")
                lon = cols[1].number_input("Längengrad (z.B. 11.58 für München)", -180.0, 180.0, 10.0, format="%.4f")
                st.caption(f"Gewählter Standort: {lat:.3f}° N, {lon:.3f}° O")
    else:
        lat, lon = lat_default, lon_default
        st.caption("Manuelle Eingabe der Wetterbedingungen:")
        cols = st.columns(3)
        temp_manuell = cols[0].slider("Temperatur (°C)", -10, 45, 18)
        sonne_manuell = cols[1].selectbox(
            "Sonneneinstrahlung", ["keine", "mittel", "stark"], index=1,
            format_func=lambda x: {"keine": "☁️ Keine Sonne", "mittel": "⛅ Teils sonnig", "stark": "☀️ Vollsonne"}[x]
        )
        indoor = cols[2].checkbox(
            "Indoor-Training",
            help="Heimtrainer/Rolle: kein Fahrtwind → mehr Schwitzen (+30%). "
                 "Auch bei offener Garage oder Keller aktivieren, wenn kein Fahrtwind vorhanden."
        )

    # ── Bedingungen ──────────────────────────────────────────────────────────
    st.subheader("5. Weitere Bedingungen")
    frueh_start = st.checkbox(
        "Frühstart (Beginn vor 8 Uhr morgens)",
        value=(start_h < 8),
        help="Bei frühem Start ist es kühler und die Sonne steht tiefer. "
             "Das reduziert die berechnete Trinkmenge leicht (Faktor ×0,9)."
    )

    # ── Submit ───────────────────────────────────────────────────────────────
    submitted = st.form_submit_button("🚀 Plan berechnen", use_container_width=True, type="primary")


# ══════════════════════════════════════════════════════════════════════════════
# BERECHNUNG
# ══════════════════════════════════════════════════════════════════════════════

if submitted:
    wetter_info = None
    temp = float(temp_manuell)
    sonne = sonne_manuell

    if wetter_auto:
        with st.spinner("🌤 Wetterdaten werden abgerufen …"):
            wetter_roh = hole_wetterdaten(lat, lon, datum.strftime("%Y-%m-%d"), start_h, dauer_h)
            wetter_info = berechne_durchschnitts_wetter(wetter_roh)
        if wetter_info:
            temp = wetter_info["avg_temp"]
            sonne = wetter_info["sonne"]
        else:
            st.warning("⚠️ Wetterdaten konnten nicht abgerufen werden (kein Internet oder Datum zu weit in der Zukunft). Manuelle Temperatur wird verwendet.")

    ergebnis = berechne_alles(
        profil=profil,
        dauer_h=float(dauer_h),
        zone=zone,
        temp=temp,
        sonne=sonne,
        indoor=indoor,
        frueh_start=frueh_start,
        distanz_km=float(distanz_km) if distanz_km else None,
        hoehenmeter=float(hoehenmeter) if hoehenmeter else None,
        watt=float(watt_eingabe) if watt_eingabe else None,
        ftp=float(profil["ftp_watt"]) if watt_eingabe else None,
        hf=float(hf_eingabe) if hf_eingabe else None,
    )

    st.session_state.ergebnis = ergebnis
    st.session_state.wetter_info = wetter_info
    st.session_state.pois = None


# ══════════════════════════════════════════════════════════════════════════════
# ERGEBNISANZEIGE
# ══════════════════════════════════════════════════════════════════════════════

if st.session_state.ergebnis:
    e = st.session_state.ergebnis
    w = st.session_state.wetter_info
    gpx = st.session_state.gpx_data

    st.divider()
    st.header("📋 Dein Ernährungsplan")

    # ── Intensitäts-Info ──
    if e["watt"] and e["ftp"]:
        pct = round(e["watt"] / e["ftp"] * 100)
        st.info(f"⚡ Leistungssteuerung: **{e['watt']:.0f} W** = {pct}% FTP → Zone **{e['zone']}** | {e['carbs']['quelle']}")
    elif e["hf"] and e["hr_max"]:
        pct = round(e["hf"] / e["hr_max"] * 100)
        st.info(f"❤️ HF-Steuerung: **{e['hf']:.0f} bpm** = {pct}% HRmax → Zone **{e['zone']}**")
    else:
        st.info(f"🎯 Zone **{e['zone']}** | {e['carbs']['quelle']}")

    # ── Kernkennzahlen ──
    cols = st.columns(4)
    cols[0].metric("🍬 Carbs gesamt", f"{e['carbs']['gesamt']} g", f"{e['carbs']['pro_h']} g/h")
    cols[1].metric("💧 Wasser gesamt", f"{e['wasser']['gesamt']} ml", f"{e['wasser']['pro_h']} ml/h")
    cols[2].metric("⏱ Dauer", f"{e['dauer_h']} h")
    cols[3].metric("🌡 Temperatur", f"{e['temp']} °C")

    # ── Energiebedarf ──
    with st.expander("🔋 Energiebedarf (Details)", expanded=True):
        cols = st.columns(4)
        cols[0].metric("Basis-Carbs", f"{e['carbs']['basis']} g",
                       help="Carbs aus Zone × Dauer")
        cols[1].metric("Höhenmeter-Bonus", f"+{e['carbs']['hm_bonus']} g",
                       help=f"+8 g pro 100 Hm Aufstieg")
        cols[2].metric("Davon Gels", f"{e['carbs']['aus_gels']} g")
        cols[3].metric("Davon Riegel", f"{e['carbs']['aus_riegeln']} g")

    # ── Softflasks ──
    with st.expander("🧴 Softflasks / Gel-Mischung", expanded=True):
        cols = st.columns(2)
        cols[0].metric("Anzahl Softflasks", e["softflasks"]["anzahl"])
        cols[1].metric("Kohlenhydrate pro Flask", f"{e['softflasks']['carbs_pro_flask']} g")
        rez = e["softflasks"]["rezept"]
        st.markdown("**Rezept pro Softflask (selbst mischen):**")
        st.table({
            "Zutat": ["Maltodextrin", "Fructose", "Salz", "Wasser auffüllen auf"],
            "Menge": [
                f"{rez['maltodextrin']} g",
                f"{rez['fructose']} g",
                f"{rez['salz']} g",
                f"{rez['wasser']} ml",
            ],
        })
        st.caption("Alle Zutaten in die Softflask geben, Wasser auffüllen, schütteln. "
                   "Maltodextrin: 2-Teile, Fructose: 1-Teil (optimale Darmaufnahme).")

    # ── Riegel ──
    if e["riegel"]:
        with st.expander("🍫 Riegelplan", expanded=True):
            st.table({
                "Riegel": [r["name"] for r in e["riegel"]],
                "Stück": [r["anzahl"] for r in e["riegel"]],
                "Carbs/Stk (g)": [r["carbs_g_pro_stueck"] for r in e["riegel"]],
                "Zucker/Stk (g)": [r["zucker_g_pro_stueck"] for r in e["riegel"]],
                "Carbs ges. (g)": [r["carbs_gesamt"] for r in e["riegel"]],
                "Zucker ges. (g)": [r["zucker_gesamt"] for r in e["riegel"]],
            })
    else:
        st.info("ℹ️ Keine Riegel eingeplant – entweder keine aktiv oder Carbs vollständig aus Gels.")

    # ── Wasserflaschen ──
    with st.expander("🚰 Wasserflaschen & Auffüllstopps", expanded=False):
        wf = e["wasserflaschen"]
        cols = st.columns(3)
        cols[0].metric("Flaschenkapazität", f"{wf['kapazitaet_ml']} ml")
        cols[1].metric("Auffüllungen nötig", wf["auffuellungen"])
        if wf["auffuellungen"] > 0:
            cols[2].metric("Volumen pro Stopp", f"~{wf['refill_ml']} ml")
        st.table({
            "Flasche": [f["name"] for f in wf["konfiguration"]],
            "Volumen (ml)": [f["volumen_ml"] for f in wf["konfiguration"]],
            "Anzahl": [f["anzahl"] for f in wf["konfiguration"]],
            "Kapazität gesamt (ml)": [f["volumen_ml"] * f["anzahl"] for f in wf["konfiguration"]],
        })
        if wf["auffuellungen"] > 0:
            st.warning(f"⚠️ Du benötigst **{wf['auffuellungen']} Auffüllung(en)** unterwegs (je ~{wf['refill_ml']} ml). "
                       f"Plane Tankstellen oder Supermärkte auf der Strecke ein.")

    # ── Elektrolyte ──
    with st.expander("🧂 Elektrolyte", expanded=False):
        el = e["elektrolyte"]
        cols = st.columns(3)
        cols[0].metric("Produkt", el["name"])
        cols[1].metric("Portion", f"{el['portion_g']} g")
        cols[2].metric("Gesamt", f"{el['gesamt_g']:.1f} g ({el['fuellungen']}x)")
        min_data = el["mineralien"]
        if any(v > 0 for v in min_data.values()):
            st.markdown("**Mineralien gesamt:**")
            st.table({
                "Mineral": [k.capitalize() for k in min_data.keys()],
                "Gesamt (mg)": list(min_data.values()),
                "Pro Stunde (mg/h)": [
                    round(v / e["dauer_h"]) if e["dauer_h"] > 0 else 0
                    for v in min_data.values()
                ],
            })
        else:
            st.caption("Keine Mineralwerte eingetragen – im Profil (links) unter Elektrolyte ergänzen.")

    # ── Koffein ──
    with st.expander("☕ Koffein-Plan", expanded=False):
        koff = e["koffein"]
        if koff["caps"] > 0:
            cols = st.columns(2)
            cols[0].metric("Kapseln gesamt", koff["caps"])
            cols[1].info(koff["plan"])
        else:
            st.info(koff["plan"])

    # ── Wetter ──
    if w:
        with st.expander("🌤 Wetterbericht", expanded=False):
            cols = st.columns(4)
            cols[0].metric("Temperatur (Ø)", f"{w['avg_temp']} °C",
                           f"min {w['min_temp']} / max {w['max_temp']}")
            cols[1].metric("Sonneneinstrahlung",
                           {"keine": "☁️ Bedeckt", "mittel": "⛅ Teils sonnig", "stark": "☀️ Vollsonne"}.get(w["sonne"], w["sonne"]))
            cols[2].metric("Wind (Ø)", f"{w['avg_wind']} km/h")
            cols[3].metric("Regen", f"{w['sum_regen']} mm")

    # ── Hinweise ──
    hinweise = []
    if e["temp"] > 25:
        hinweise.append("🌡️ **Hitze (>25 °C):** Trinkmenge regelmäßig prüfen. Elektrolyte erhöhen. Alle 30–40 min trinken.")
    if e.get("hoehenmeter") and e["hoehenmeter"] > 1500:
        hinweise.append("⛰️ **Viele Höhenmeter:** Energiebedarf deutlich erhöht. Regelmäßig essen, nicht warten bis Hunger kommt.")
    if e["dauer_h"] > 5:
        hinweise.append("⏳ **Langdistanz:** Magen-Darm-Training ist wichtig. Keine neuen Produkte am Wettkampftag einsetzen.")
    if e["zone"] in ("Z4", "Z5"):
        hinweise.append("⚡ **Hohe Intensität (Z4/Z5):** Frühzeitig essen (ab Minute 20), alle 20–25 min nachlegen.")
    if e["wasserflaschen"]["auffuellungen"] > 0 and not gpx:
        hinweise.append(f"🗺️ **Auffüllstopps nötig:** Plane {e['wasserflaschen']['auffuellungen']} Stopp(s) ein. GPX-Datei hochladen für automatische Tankstellen-/Supermarktsuche.")
    if hinweise:
        with st.expander("⚠️ Hinweise & Empfehlungen", expanded=True):
            for h in hinweise:
                st.warning(h)

    # ── POI-Suche ──
    if gpx and e["wasserflaschen"]["auffuellungen"] > 0:
        with st.expander("📍 Tankstellen & Supermärkte entlang der Route", expanded=False):
            st.caption("Suche nach Einkaufsmöglichkeiten in der Nähe des Startpunkts (OpenStreetMap).")
            if st.button("🔍 Jetzt suchen", use_container_width=True):
                with st.spinner("Suche läuft …"):
                    pois = suche_nahe_pois(gpx["start_lat"], gpx["start_lon"])
                st.session_state.pois = pois
            if st.session_state.pois is not None:
                if st.session_state.pois:
                    st.table({
                        "Name": [p["name"] for p in st.session_state.pois],
                        "Typ": [p["typ"] for p in st.session_state.pois],
                        "Adresse": [f"{p['strasse']}, {p['ort']}" for p in st.session_state.pois],
                        "Entfernung": [f"{p['dist_m']} m" for p in st.session_state.pois],
                    })
                else:
                    st.info("Keine Einkaufsmöglichkeiten im Umkreis von 3 km gefunden.")

    # ── Download ──
    st.divider()
    plan_text = erstelle_plan_text(e, w)
    st.download_button(
        label="📥 Plan als .txt herunterladen",
        data=plan_text,
        file_name=f"fueling_plan_{datetime.now().strftime('%Y%m%d_%H%M')}.txt",
        mime="text/plain",
        use_container_width=True,
    )
