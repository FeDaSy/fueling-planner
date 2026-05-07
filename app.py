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
    "grocery": "Lebensmittel", "bakery": "Baeckerei", "chemist": "Drogerie"
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
    "schweissrate": {"preset": "mittel", "kalibriert_ml_h": [[10, 250], [15, 300], [20, 350], [25, 450], [99, 600]]},
    "flaschen": [{"name": "Trinkflasche", "volumen_ml": 950, "anzahl": 2}],
    "softflask": {
        "volumen_ml": 450, "max_anzahl": 4, "gel_anteil_pct": 70,
        "malto_ratio": 2, "fructose_ratio": 1,
        "salz_normal_g": 0.7, "salz_heiss_g": 1.0, "temp_heiss_grad": 25,
    },
    "riegel": [
        {"name": "Mango Fruchtriegel", "carbs_g": 30, "zucker_g": 18, "gewicht_g": 40, "aktiv": True},
        {"name": "Hafer-Heidelbeere", "carbs_g": 40, "zucker_g": 12, "gewicht_g": 50, "aktiv": True},
    ],
    "elektrolyte": {
        "name": "Raab Elektrolyt-Pulver",
        "portion_normal_g": 3.5, "portion_heiss_g": 7.0, "temp_heiss_grad": 20,
        "mineralien_pro_portion_mg": {"natrium": 0, "kalium": 0, "chlorid": 0, "calcium": 0, "magnesium": 0},
    },
    "koffein": {"pro_cap_mg": 50, "aktiv": True},
}

# ── Backend-Funktionen ─────────────────────────────────────────────────────────
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
             if preset == "kalibriert" else SCHWEISSRATEN_PRESETS.get(preset, SCHWEISSRATEN_PRESETS["mittel"]))
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
    return {"maltodextrin": malto, "fructose": fructose, "salz": salz, "wasser": wasser}

def berechne_koffein(profil, dauer_h):
    if not profil["koffein"]["aktiv"]:
        return {"caps": 0, "plan": "Koffein deaktiviert"}
    mg = profil["koffein"]["pro_cap_mg"]
    if dauer_h < 2: return {"caps": 0, "plan": "Nicht noetig (<2h)"}
    elif dauer_h < 4: return {"caps": 1, "plan": f"1 Cap ({mg} mg) nach Stunde 2"}
    elif dauer_h < 6: return {"caps": 2, "plan": f"Stunde 2 und 4 (je {mg} mg)"}
    elif dauer_h < 8: return {"caps": 4, "plan": f"Stunde 1, 4, 6, 8 (je {mg} mg)"}
    else: return {"caps": 5, "plan": f"Stunde 1, 4, 7, 9 (Doppel), 11"}

def berechne_riegel_plan(profil, carbs_aus_riegeln, dauer_h, zone):
    aktive = [r for r in profil["riegel"] if r["aktiv"]]
    if not aktive or carbs_aus_riegeln <= 0:
        return []
    carbs_pro_runde = sum(r["carbs_g"] for r in aktive)
    runden = math.ceil(carbs_aus_riegeln / carbs_pro_runde) if carbs_pro_runde > 0 else 1
    return [{"name": r["name"], "anzahl": runden, "carbs_g_pro_stueck": r["carbs_g"],
             "carbs_gesamt": runden * r["carbs_g"], "zucker_g_pro_stueck": r.get("zucker_g", 0),
             "zucker_gesamt": runden * r.get("zucker_g", 0)} for r in aktive]

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
        1 if carbs_gesamt <= 70 else 2 if carbs_gesamt <= 200 else 3 if carbs_gesamt <= 400 else sf["max_anzahl"]))
    carbs_pro_flask = round(carbs_aus_gels / anzahl_flasks)
    wasser_aus_gels = anzahl_flasks * round(sf["volumen_ml"] * 0.69)
    flaschen_kapazitaet_ml = sum(f["volumen_ml"] * f["anzahl"] for f in profil["flaschen"])
    refill_ml = max(f["volumen_ml"] for f in profil["flaschen"]) if profil["flaschen"] else 950
    wasser_zusaetzlich = max(0, wasser_gesamt - wasser_aus_gels)
    auffuellungen_noetig = max(0, math.ceil(
        (wasser_zusaetzlich - flaschen_kapazitaet_ml) / refill_ml
    )) if wasser_zusaetzlich > flaschen_kapazitaet_ml else 0
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
                  "hm_bonus": hm_bonus, "aus_gels": carbs_aus_gels, "aus_riegeln": carbs_aus_riegeln,
                  "quelle": carbs_quelle},
        "wasser": {"pro_h": wasser_pro_h, "gesamt": wasser_gesamt, "aus_gels": wasser_aus_gels,
                   "zusaetzlich": wasser_zusaetzlich, "flaschen_kapazitaet_ml": flaschen_kapazitaet_ml,
                   "refill_ml": refill_ml},
        "softflasks": {"anzahl": anzahl_flasks, "carbs_pro_flask": carbs_pro_flask,
                       "rezept": berechne_gel_rezept(profil, carbs_pro_flask, temp)},
        "riegel": riegel_plan,
        "wasserflaschen": {"konfiguration": profil["flaschen"], "kapazitaet_ml": flaschen_kapazitaet_ml,
                           "auffuellungen": auffuellungen_noetig, "refill_ml": refill_ml},
        "elektrolyte": {"name": el["name"], "portion_g": el_portion, "gesamt_g": el_gesamt,
                        "fuellungen": fuellungen, "mineralien": mineralien_gesamt, "min_pro_portion": min_profil},
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
    return {"avg_temp": round(avg_temp, 1), "min_temp": min(wetter["temperaturen"]),
            "max_temp": max(wetter["temperaturen"]), "avg_wolken": round(avg_wolken),
            "avg_wind": round(avg_wind, 1), "max_uv": round(max(wetter["uv"]), 1),
            "sum_regen": round(sum(wetter["niederschlag"]), 1), "sonne": sonne}

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
        return {"name": name, "distanz_km": round(dist_km, 1), "hoehenmeter_auf": round(hm_auf),
                "hoehenmeter_ab": round(hm_ab), "start_lat": points[0][0], "start_lon": points[0][1],
                "points": points, "kumulative_distanzen": kum}
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

# ── Hilfsfunktionen ────────────────────────────────────────────────────────────
def erstelle_plan_text(ergebnis, wetter_info=None):
    e = ergebnis
    lines = [
        f"=== CYCLING FUELING PLAN ===",
        f"Profil: {e['profil_name']}",
        f"Dauer: {e['dauer_h']} h  |  Zone: {e['zone']}  |  Temp: {e['temp']} °C",
        "",
        "--- KOHLENHYDRATE ---",
        f"Gesamt:     {e['carbs']['gesamt']} g  ({e['carbs']['pro_h']} g/h)",
        f"Basis:      {e['carbs']['basis']} g",
        f"HM-Bonus:   {e['carbs']['hm_bonus']} g",
        f"Aus Gels:   {e['carbs']['aus_gels']} g",
        f"Aus Riegeln:{e['carbs']['aus_riegeln']} g",
        f"Quelle:     {e['carbs']['quelle']}",
        "",
        "--- WASSER ---",
        f"Gesamt:     {e['wasser']['gesamt']} ml  ({e['wasser']['pro_h']} ml/h)",
        f"Aus Gels:   {e['wasser']['aus_gels']} ml",
        f"Zusaetzlich:{e['wasser']['zusaetzlich']} ml",
        "",
        "--- SOFTFLASKS ---",
        f"Anzahl:     {e['softflasks']['anzahl']}",
        f"Carbs/Flask:{e['softflasks']['carbs_pro_flask']} g",
        f"Rezept:     Malto {e['softflasks']['rezept']['maltodextrin']} g  |  Fructose {e['softflasks']['rezept']['fructose']} g  |  Salz {e['softflasks']['rezept']['salz']} g  |  Wasser {e['softflasks']['rezept']['wasser']} ml",
        "",
    ]
    if e["riegel"]:
        lines.append("--- RIEGEL ---")
        for r in e["riegel"]:
            lines.append(f"  {r['name']}: {r['anzahl']}x  (Carbs: {r['carbs_gesamt']} g, Zucker: {r['zucker_gesamt']} g)")
        lines.append("")
    el = e["elektrolyte"]
    lines += [
        "--- ELEKTROLYTE ---",
        f"Produkt:    {el['name']}",
        f"Portion:    {el['portion_g']} g  x{el['fuellungen']}  =  {el['gesamt_g']} g",
        "",
        "--- KOFFEIN ---",
        f"Plan:       {e['koffein']['plan']}  ({e['koffein']['caps']} Caps)",
        "",
    ]
    if wetter_info:
        lines += [
            "--- WETTER ---",
            f"Temperatur: {wetter_info['avg_temp']} °C (min {wetter_info['min_temp']} / max {wetter_info['max_temp']})",
            f"Sonne:      {wetter_info['sonne']}  |  Wind: {wetter_info['avg_wind']} km/h  |  Regen: {wetter_info['sum_regen']} mm",
            "",
        ]
    lines.append("=== Ende des Plans ===")
    return "\n".join(lines)

# ── Streamlit App ──────────────────────────────────────────────────────────────
st.set_page_config(page_title="Cycling Fueling Planner", page_icon="🚴", layout="wide")

# Session state initialisieren
if "profil" not in st.session_state:
    st.session_state.profil = copy.deepcopy(DEFAULT_PROFIL)
if "ergebnis" not in st.session_state:
    st.session_state.ergebnis = None
if "wetter_info" not in st.session_state:
    st.session_state.wetter_info = None
if "gpx_data" not in st.session_state:
    st.session_state.gpx_data = None

profil = st.session_state.profil

# ── Sidebar – Profil ───────────────────────────────────────────────────────────
with st.sidebar:
    st.title("🚴 Mein Profil")

    profil["name"] = st.text_input("Profilname", value=profil["name"])

    profil["ftp_watt"] = st.slider("FTP (Watt)", 100, 500, profil["ftp_watt"], step=5)

    hr_max_val = st.number_input(
        "HRmax (Schläge/min, optional)",
        min_value=0, max_value=230,
        value=profil["hr_max"] if profil["hr_max"] else 0,
        step=1,
    )
    profil["hr_max"] = hr_max_val if hr_max_val > 0 else None

    st.subheader("Schweissrate")
    sw_labels = {"wenig": "Wenig schwitzen", "mittel": "Normal schwitzen", "viel": "Stark schwitzen"}
    sw_optionen = list(sw_labels.keys())
    sw_idx = sw_optionen.index(profil["schweissrate"]["preset"]) if profil["schweissrate"]["preset"] in sw_optionen else 1
    sw_sel = st.selectbox("Schweissrate", sw_optionen, index=sw_idx,
                          format_func=lambda x: sw_labels[x])
    profil["schweissrate"]["preset"] = sw_sel

    st.subheader("Koffein")
    profil["koffein"]["aktiv"] = st.checkbox("Koffein verwenden", value=profil["koffein"]["aktiv"])
    if profil["koffein"]["aktiv"]:
        profil["koffein"]["pro_cap_mg"] = st.number_input(
            "mg pro Cap", min_value=10, max_value=200,
            value=profil["koffein"]["pro_cap_mg"], step=5,
        )

    st.subheader("Wasserflaschen")
    for i, fl in enumerate(profil["flaschen"]):
        cols = st.columns(2)
        fl["anzahl"] = cols[0].number_input(f"Anzahl ({fl['name']})", 0, 10, fl["anzahl"], key=f"fl_anz_{i}")
        fl["volumen_ml"] = cols[1].number_input(f"Volumen ml ({fl['name']})", 200, 2000,
                                                 fl["volumen_ml"], step=50, key=f"fl_vol_{i}")

    st.subheader("Riegel")
    for i, r in enumerate(profil["riegel"]):
        with st.expander(r["name"], expanded=False):
            r["aktiv"] = st.checkbox("Aktiv", value=r["aktiv"], key=f"r_aktiv_{i}")
            r["carbs_g"] = st.number_input("Carbs (g)", 0, 100, r["carbs_g"], key=f"r_carbs_{i}")
            r["zucker_g"] = st.number_input("Zucker (g)", 0, 100, r.get("zucker_g", 0), key=f"r_zucker_{i}")

    st.subheader("Elektrolyte")
    el = profil["elektrolyte"]
    el["name"] = st.text_input("Produkt", value=el["name"])
    cols = st.columns(2)
    el["portion_normal_g"] = cols[0].number_input("Portion normal (g)", 0.0, 30.0, el["portion_normal_g"], step=0.5)
    el["portion_heiss_g"] = cols[1].number_input("Portion heiss (g)", 0.0, 30.0, el["portion_heiss_g"], step=0.5)
    el["temp_heiss_grad"] = st.number_input("Hitzeschwelle (°C)", 10, 40, el["temp_heiss_grad"])

# ── Hauptbereich ───────────────────────────────────────────────────────────────
st.title("🚴 Cycling Fueling Planner")
st.caption("Dein persönlicher Ernährungsplan für lange Ausfahrten.")

with st.form("planungsformular"):
    st.subheader("1. Route")
    route_modus = st.radio("Eingabemodus", ["Kein GPX (manuell)", "GPX-Datei hochladen"], horizontal=True)

    gpx_data = None
    distanz_km = None
    hoehenmeter = None
    lat_default, lon_default = 52.15, 10.41

    if route_modus == "GPX-Datei hochladen":
        uploaded_file = st.file_uploader("GPX-Datei auswählen", type=["gpx"])
        if uploaded_file is not None:
            gpx_data = parse_gpx(uploaded_file.read())
            if gpx_data:
                st.success(f"GPX geladen: **{gpx_data['name']}** – "
                           f"{gpx_data['distanz_km']} km, {gpx_data['hoehenmeter_auf']} hm")
                distanz_km = gpx_data["distanz_km"]
                hoehenmeter = gpx_data["hoehenmeter_auf"]
                lat_default = gpx_data["start_lat"]
                lon_default = gpx_data["start_lon"]
            else:
                st.error("GPX konnte nicht gelesen werden.")

    if gpx_data is None:
        cols = st.columns(2)
        distanz_km = cols[0].number_input("Distanz (km)", 0.0, 500.0, 80.0, step=5.0)
        hoehenmeter = cols[1].number_input("Höhenmeter (m)", 0, 8000, 800, step=100)

    cols = st.columns(2)
    lat = cols[0].number_input("Breitengrad (Latitude)", -90.0, 90.0, lat_default, format="%.4f")
    lon = cols[1].number_input("Längengrad (Longitude)", -180.0, 180.0, lon_default, format="%.4f")

    st.subheader("2. Intensität")
    intensitaet_optionen = ["Zone manuell", "Wattsteuerung"]
    if profil["hr_max"]:
        intensitaet_optionen.append("Herzfrequenz")
    intensitaet_modus = st.radio("Intensitätsmodus", intensitaet_optionen, horizontal=True)

    zone = "Z2"
    watt_eingabe = None
    hf_eingabe = None

    if intensitaet_modus == "Zone manuell":
        zone = st.selectbox("Trainingszone", ["Z1", "Z2", "Z3", "Z4", "Z5", "Mix"], index=1)
        if profil["hr_max"]:
            hf_zonen_text = "  |  ".join(
                [f"Z{i+1}: >{int(grenze_von*profil['hr_max'])} bpm"
                 for i, (grenze_von, _) in enumerate(
                     [(0, "Z1"), (0.60, "Z2"), (0.70, "Z3"), (0.80, "Z4"), (0.90, "Z5")]
                 ) if i > 0] +
                [f"Z1: <{int(0.60*profil['hr_max'])} bpm"]
            )
            st.info(f"HF-Zonen bei HRmax {profil['hr_max']}: Z1 <{int(0.60*profil['hr_max'])} | "
                    f"Z2 {int(0.60*profil['hr_max'])}-{int(0.70*profil['hr_max'])} | "
                    f"Z3 {int(0.70*profil['hr_max'])}-{int(0.80*profil['hr_max'])} | "
                    f"Z4 {int(0.80*profil['hr_max'])}-{int(0.90*profil['hr_max'])} | "
                    f"Z5 >{int(0.90*profil['hr_max'])} bpm")

    elif intensitaet_modus == "Wattsteuerung":
        st.info(f"FTP aus Profil: **{profil['ftp_watt']} W**")
        watt_eingabe = st.number_input("Durchschnittsleistung (W)", 50, 600, profil["ftp_watt"] - 30, step=5)
        zone = watts_zu_zone(watt_eingabe, profil["ftp_watt"])
        pct_ftp = round(watt_eingabe / profil["ftp_watt"] * 100)
        st.caption(f"Entspricht Zone **{zone}** ({pct_ftp}% FTP)")

    elif intensitaet_modus == "Herzfrequenz":
        hr_max = profil["hr_max"]
        st.info(f"HRmax aus Profil: **{hr_max} bpm**  |  "
                f"Z1 <{int(0.60*hr_max)} | Z2 {int(0.60*hr_max)}-{int(0.70*hr_max)} | "
                f"Z3 {int(0.70*hr_max)}-{int(0.80*hr_max)} | Z4 {int(0.80*hr_max)}-{int(0.90*hr_max)} | "
                f"Z5 >{int(0.90*hr_max)} bpm")
        hf_eingabe = st.number_input("Durchschnittliche HF (bpm)", 60, 220, int(hr_max * 0.72), step=1)
        zone = hf_zu_zone(hf_eingabe, hr_max)
        pct_hrmax = round(hf_eingabe / hr_max * 100)
        st.caption(f"Entspricht Zone **{zone}** ({pct_hrmax}% HRmax)")

    st.subheader("3. Dauer")
    dauer_schaetzung = None
    if distanz_km and hoehenmeter:
        dauer_schaetzung = schaetze_dauer(distanz_km, hoehenmeter, zone if zone != "Mix" else "Z2")
    dauer_h = st.number_input(
        "Trainingsdauer (Stunden)",
        min_value=0.5, max_value=24.0,
        value=dauer_schaetzung if dauer_schaetzung else 3.0,
        step=0.25,
        help=f"Geschätzte Dauer: {dauer_schaetzung} h" if dauer_schaetzung else None,
    )
    if dauer_schaetzung:
        st.caption(f"Geschätzte Dauer basierend auf Route: **{dauer_schaetzung} h**")

    st.subheader("4. Wetter")
    datum = st.date_input("Trainings­datum", value=datetime.today() + timedelta(days=1))
    start_h = st.slider("Startzeit (Uhr)", 0, 23, 9)
    wetter_auto = st.checkbox("Wetter automatisch abrufen (Open-Meteo)", value=True)

    temp_manuell = 18
    sonne_manuell = "mittel"
    indoor = False

    if not wetter_auto:
        cols = st.columns(2)
        temp_manuell = cols[0].slider("Temperatur (°C)", -10, 45, 18)
        sonne_manuell = cols[1].selectbox("Sonneneinstrahlung", ["keine", "mittel", "stark"], index=1)
        indoor = st.checkbox("Indoor-Training (Trainer/Rolle)")

    st.subheader("5. Bedingungen")
    frueh_start = st.checkbox("Frühstart (vor 8 Uhr, kühler)", value=start_h < 8)

    submitted = st.form_submit_button("🚀 Plan berechnen", use_container_width=True, type="primary")

# ── Berechnung & Ergebnisse ────────────────────────────────────────────────────
if submitted:
    wetter_info = None
    temp = temp_manuell
    sonne = sonne_manuell

    if wetter_auto:
        with st.spinner("Wetterdaten werden abgerufen…"):
            wetter_roh = hole_wetterdaten(lat, lon, datum.strftime("%Y-%m-%d"), start_h, dauer_h)
            wetter_info = berechne_durchschnitts_wetter(wetter_roh)
        if wetter_info:
            temp = wetter_info["avg_temp"]
            sonne = wetter_info["sonne"]
        else:
            st.warning("Wetterdaten konnten nicht abgerufen werden – manuelle Werte werden verwendet.")

    ergebnis = berechne_alles(
        profil=profil,
        dauer_h=dauer_h,
        zone=zone,
        temp=temp,
        sonne=sonne,
        indoor=indoor,
        frueh_start=frueh_start,
        distanz_km=distanz_km,
        hoehenmeter=hoehenmeter,
        watt=watt_eingabe,
        ftp=profil["ftp_watt"] if watt_eingabe else None,
        hf=hf_eingabe,
    )

    st.session_state.ergebnis = ergebnis
    st.session_state.wetter_info = wetter_info
    st.session_state.gpx_data = gpx_data

# ── Ergebnisanzeige ────────────────────────────────────────────────────────────
if st.session_state.ergebnis:
    e = st.session_state.ergebnis
    w = st.session_state.wetter_info
    gpx = st.session_state.gpx_data

    st.divider()
    st.header("📋 Dein Ernährungsplan")

    # Kennzahlen
    cols = st.columns(4)
    cols[0].metric("🍬 Carbs gesamt", f"{e['carbs']['gesamt']} g", f"{e['carbs']['pro_h']} g/h")
    cols[1].metric("💧 Wasser gesamt", f"{e['wasser']['gesamt']} ml", f"{e['wasser']['pro_h']} ml/h")
    cols[2].metric("⏱ Dauer", f"{e['dauer_h']} h")
    cols[3].metric("⚡ Zone", e["zone"])

    # Intensitätsdetails
    if e["watt"]:
        pct = round(e["watt"] / e["ftp"] * 100)
        st.info(f"Leistungssteuerung: **{e['watt']} W** = {pct}% FTP → Zone **{e['zone']}**  |  Carbs-Quelle: {e['carbs']['quelle']}")
    elif e["hf"] and e["hr_max"]:
        pct = round(e["hf"] / e["hr_max"] * 100)
        st.info(f"HF-Steuerung: **{e['hf']} bpm** = {pct}% HRmax → Zone **{e['zone']}**")
    else:
        st.info(f"Manuelle Zone: **{e['zone']}**  |  Carbs-Quelle: {e['carbs']['quelle']}")

    # Energiebedarf
    with st.expander("🔋 Energiebedarf (Details)", expanded=True):
        cols = st.columns(4)
        cols[0].metric("Carbs Basis", f"{e['carbs']['basis']} g")
        cols[1].metric("HM-Bonus", f"{e['carbs']['hm_bonus']} g")
        cols[2].metric("Aus Gels", f"{e['carbs']['aus_gels']} g")
        cols[3].metric("Aus Riegeln", f"{e['carbs']['aus_riegeln']} g")

    # Softflasks
    with st.expander("🧴 Softflasks / Gel-Mix", expanded=True):
        cols = st.columns(2)
        cols[0].metric("Anzahl Softflasks", e["softflasks"]["anzahl"])
        cols[1].metric("Carbs pro Flask", f"{e['softflasks']['carbs_pro_flask']} g")
        rez = e["softflasks"]["rezept"]
        st.markdown("**Rezept pro Softflask:**")
        st.table({
            "Zutat": ["Maltodextrin", "Fructose", "Salz", "Wasser"],
            "Menge": [f"{rez['maltodextrin']} g", f"{rez['fructose']} g",
                      f"{rez['salz']} g", f"{rez['wasser']} ml"],
        })

    # Riegel
    if e["riegel"]:
        with st.expander("🍫 Riegelplan", expanded=True):
            riegel_daten = {
                "Name": [r["name"] for r in e["riegel"]],
                "Anzahl": [r["anzahl"] for r in e["riegel"]],
                "Carbs/Stk (g)": [r["carbs_g_pro_stueck"] for r in e["riegel"]],
                "Zucker/Stk (g)": [r["zucker_g_pro_stueck"] for r in e["riegel"]],
                "Carbs gesamt (g)": [r["carbs_gesamt"] for r in e["riegel"]],
                "Zucker gesamt (g)": [r["zucker_gesamt"] for r in e["riegel"]],
            }
            st.table(riegel_daten)

    # Wasserflaschen
    with st.expander("🚰 Wasserflaschen & Nachfüllen", expanded=False):
        wf = e["wasserflaschen"]
        cols = st.columns(3)
        cols[0].metric("Flaschenkapazität", f"{wf['kapazitaet_ml']} ml")
        cols[1].metric("Auffüllungen nötig", wf["auffuellungen"])
        cols[2].metric("Refill-Volumen", f"{wf['refill_ml']} ml")
        fl_daten = {
            "Name": [f["name"] for f in wf["konfiguration"]],
            "Volumen (ml)": [f["volumen_ml"] for f in wf["konfiguration"]],
            "Anzahl": [f["anzahl"] for f in wf["konfiguration"]],
        }
        st.table(fl_daten)
        if wf["auffuellungen"] > 0:
            st.warning(f"⚠️ Du benötigst **{wf['auffuellungen']} Auffüllung(en)** unterwegs (je ~{wf['refill_ml']} ml).")

    # Elektrolyte
    with st.expander("🧂 Elektrolyte", expanded=False):
        el = e["elektrolyte"]
        cols = st.columns(3)
        cols[0].metric("Produkt", el["name"])
        cols[1].metric("Portion", f"{el['portion_g']} g")
        cols[2].metric("Gesamt", f"{el['gesamt_g']} g ({el['fuellungen']} Füllungen)")
        min_data = el["mineralien"]
        dauer_h_val = e["dauer_h"]
        if any(v > 0 for v in min_data.values()):
            st.markdown("**Mineralien gesamt:**")
            st.table({
                "Mineral": list(min_data.keys()),
                "Gesamt (mg)": list(min_data.values()),
                "Pro Stunde (mg/h)": [round(v / dauer_h_val) if dauer_h_val > 0 else 0 for v in min_data.values()],
            })

    # Koffein
    with st.expander("☕ Koffein", expanded=False):
        koff = e["koffein"]
        cols = st.columns(2)
        cols[0].metric("Kapseln", koff["caps"])
        cols[1].info(koff["plan"])

    # Wetter
    if w:
        with st.expander("🌤 Wetter", expanded=False):
            cols = st.columns(4)
            cols[0].metric("Temperatur (Ø)", f"{w['avg_temp']} °C", f"min {w['min_temp']} / max {w['max_temp']}")
            cols[1].metric("Sonneneinstrahlung", w["sonne"].capitalize())
            cols[2].metric("Wind (Ø)", f"{w['avg_wind']} km/h")
            cols[3].metric("Regen", f"{w['sum_regen']} mm")

    # Hinweise
    hinweise = []
    if e["temp"] > 25:
        hinweise.append("🌡️ **Hitze:** Bei über 25°C deutlich mehr trinken. Elektrolyte erhöhen.")
    if e.get("hoehenmeter") and e["hoehenmeter"] > 1500:
        hinweise.append("⛰️ **Viele Höhenmeter:** Energiebedarf ist deutlich erhöht – regelmäßig essen!")
    if e["dauer_h"] > 5:
        hinweise.append("⏳ **Langdistanz:** Magen-Darm regelmäßig trainieren. Keine neuen Produkte am Wettkampftag.")
    if e["zone"] in ("Z4", "Z5"):
        hinweise.append("⚡ **Hohe Intensität:** Gel-Aufnahme frühzeitig starten, alle 20–30 min.")
    if hinweise:
        with st.expander("⚠️ Hinweise", expanded=True):
            for h in hinweise:
                st.warning(h)

    # POI-Suche (nur bei GPX und nötigen Auffüllungen)
    if gpx and e["wasserflaschen"]["auffuellungen"] > 0:
        with st.expander("📍 Nachfüllpunkte entlang der Route", expanded=False):
            if st.button("Tankstellen & Supermärkte suchen"):
                with st.spinner("POIs werden gesucht…"):
                    pois = suche_nahe_pois(gpx["start_lat"], gpx["start_lon"], POI_SUCHRADIUS_M)
                if pois:
                    poi_daten = {
                        "Name": [p["name"] for p in pois],
                        "Typ": [p["typ"] for p in pois],
                        "Straße": [p["strasse"] for p in pois],
                        "Ort": [p["ort"] for p in pois],
                        "Entfernung": [f"{p['dist_m']} m" for p in pois],
                    }
                    st.table(poi_daten)
                else:
                    st.info("Keine POIs in der Nähe gefunden.")

    # Download
    st.divider()
    plan_text = erstelle_plan_text(e, w)
    st.download_button(
        label="📥 Plan als .txt herunterladen",
        data=plan_text,
        file_name=f"fueling_plan_{datetime.now().strftime('%Y%m%d_%H%M')}.txt",
        mime="text/plain",
        use_container_width=True,
    )
