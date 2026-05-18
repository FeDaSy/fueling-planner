# =============================================================================
#  CYCLING FUELING PLANNER
#  Copyright (c) 2024-2025 Felix Manasov. Alle Rechte vorbehalten.
#
#  Dieses Werk ist urheberrechtlich geschuetzt. Die Nutzung der Web-Applikation
#  unter der oeffentlichen URL ist ausdruecklich erlaubt und kostenfrei.
#
#  VERBOTEN ohne ausdrueckliche schriftliche Genehmigung des Urhebers:
#    - Kopieren, Reproduzieren oder Vervielfaeltigen des Quellcodes
#    - Modifizieren, Abwandeln oder Erstellen von Ableitungen (Derivative Works)
#    - Weitergabe oder Veroeffentlichung des Codes (ganz oder in Teilen)
#    - Kommerzielle Nutzung oder Einbindung in eigene Produkte
#    - Entfernen oder Veraendern dieses Urheberrechtsvermerks
#
#  Kontakt: Anfragen zur Lizenzierung oder Kooperation per GitHub-Issue.
#
#  This software is proprietary and confidential. Source code is made visible
#  solely for the purpose of deployment on Streamlit Community Cloud.
#  Visibility does not constitute a license to use, copy, or modify the code.
#  See LICENSE file for full terms.
# =============================================================================

import copy
import math
import json
import urllib.request
import urllib.parse
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta

import streamlit as st

# ── Optional: Browser-localStorage für persistente Profile ────────────────────
try:
    from streamlit_local_storage import LocalStorage
    _LOCAL_STORAGE_OK = True
except ImportError:
    LocalStorage = None  # type: ignore
    _LOCAL_STORAGE_OK = False


def _merge_profil_mit_defaults(geladen, defaults):
    """
    Mergt ein geladenes Profil rekursiv mit den Defaults.
    So bleibt das Profil kompatibel, wenn neue Felder hinzugekommen sind.
    """
    if not isinstance(geladen, dict) or not isinstance(defaults, dict):
        return geladen if geladen is not None else defaults
    result = copy.deepcopy(defaults)
    for k, v in geladen.items():
        if k in result and isinstance(result[k], dict) and isinstance(v, dict):
            result[k] = _merge_profil_mit_defaults(v, result[k])
        else:
            result[k] = v
    return result


# ── Konstanten ────────────────────────────────────────────────────────────────
CARBS_PRO_STUNDE = {"Z1": 30, "Z2": 60, "Z3": 75, "Z4": 90, "Z5": 90, "Mix": 70}

# ── Progressive Carb-Multiplikatoren (Zone × kumulierte Zeit) ────────────────
# Relativer Ansatz: Multiplikatoren werden auf den tatsächlichen carbs_pro_h-Wert
# (aus Watt oder Zone) angewendet. Dadurch ist der progressive Plan immer konsistent
# mit dem physiologischen Verbrauch in der Glykogen-Speicherbilanz.
#
# Herleitung: Matrixwerte / Zonen-Flachrate (CARBS_PRO_STUNDE)
#   Z1 flat=30:  10/30=0.33, 20/30=0.67, 30/30=1.00, 40/30=1.33, 50/30=1.67
#   Z2 flat=60:  35/60=0.58, 55/60=0.92, 68/60=1.13, 83/60=1.38, 90/60=1.50
#   Z3 flat=75:  50/75=0.67, 70/75=0.93, 85/75=1.13, 90/75=1.20, 90/75=1.20
#   Z4 flat=90:  60/90=0.67, 85/90=0.94, 90/90=1.00, 90/90=1.00, 90/90=1.00
#   Z5 flat=90:  gleich Z4 (GI-Limit verhindert höhere Absorption)
#
# Deckel: min(rate, 90) – Absorptionsgrenze für Doppelquelle Glukose+Fruktose.
# Wissenschaftliche Quellen: Vøllestad & Blom (1985), Jeukendrup (2014),
# Gonzalez & van Loon (2016), Impey & Morton (2018).
PROGRESSIVE_MULTIPLIKATOREN = [
    # (max_kum_min, {zone: multiplikator})
    ( 60,  {"Z1": 0.33, "Z2": 0.58, "Z3": 0.67, "Z4": 0.67, "Z5": 0.67}),
    (120,  {"Z1": 0.67, "Z2": 0.92, "Z3": 0.93, "Z4": 0.94, "Z5": 0.94}),
    (180,  {"Z1": 1.00, "Z2": 1.13, "Z3": 1.13, "Z4": 1.00, "Z5": 1.00}),
    (240,  {"Z1": 1.33, "Z2": 1.38, "Z3": 1.20, "Z4": 1.00, "Z5": 1.00}),
    (9999, {"Z1": 1.67, "Z2": 1.50, "Z3": 1.20, "Z4": 1.00, "Z5": 1.00}),
]
INTENSITAETS_FAKTOR = {"Z1": 0.85, "Z2": 1.0, "Z3": 1.15, "Z4": 1.25, "Z5": 1.3, "Mix": 1.1}
SONNEN_FAKTOR = {"keine": 1.0, "mittel": 1.1, "stark": 1.2}
POWER_ZONEN = [(0.55, "Z1"), (0.75, "Z2"), (0.90, "Z3"), (1.05, "Z4"), (float("inf"), "Z5")]
HF_ZONEN = [(0.60, "Z1"), (0.70, "Z2"), (0.80, "Z3"), (0.90, "Z4"), (float("inf"), "Z5")]
CARB_ANTEIL_NACH_PCT_FTP = [(0.55, 0.35), (0.75, 0.50), (0.90, 0.72), (1.05, 0.87), (float("inf"), 0.95)]
WIRKUNGSGRAD = 0.22
HOEHENMETER_CARBS_BONUS_PRO_100HM = 8
AUFFUELL_BUFFER_PCT = 0.82

# ── Glykogen-Speicher (g pro kg Körpergewicht) ────────────────────────────────
# Basis: Muskelglykogen (~80%) + Leberglykogen (~20%).
# Quellen: Jeukendrup & Gleeson (2010), Burke (2015), Hawley & Leckey (2015),
# Tarnopolsky et al. (2007) für Geschlechtsunterschiede.
# Werte konservativ in der Mitte typischer Messbereiche.
#
# Geschlecht: Frauen haben bei gleichem Körpergewicht ~10–15% weniger Muskelmasse
# (FFM-Anteil m: ~42%, w: ~36%) und damit weniger absolute Glykogenkapazität.
# Carbo-Loading-Response ist bei Frauen zusätzlich gedämpft (20–30% vs. 40–50%
# Steigerung bei Männern), wenn der absolute KH-Anteil <8 g/kg/Tag liegt.
GLYKOGEN_SPEICHER_G_PRO_KG = {
    "Männlich": {
        "untrained": 6.0,          # ~450 g bei 75 kg
        "trained": 8.0,            # ~600 g bei 75 kg
        "trained_loaded": 11.0,    # ~825 g bei 75 kg
        "elite_loaded": 13.0,      # ~975 g bei 75 kg
    },
    "Weiblich": {
        "untrained": 5.3,          # −12% (geringere FFM)
        "trained": 7.0,            # −12% (geringere FFM)
        "trained_loaded": 9.0,     # −18% (Loading-Response gedämpft)
        "elite_loaded": 10.5,      # −19% (Loading-Response gedämpft)
    },
}
# Performance-Schwellen (% Speicher-Rest)
GLYKOGEN_ZONEN = [
    (0.70, "optimal", "🟢"),    # >70%: voll leistungsfähig
    (0.50, "gut", "🟢"),         # 50–70%: noch alles ok
    (0.30, "achtung", "🟡"),     # 30–50%: erste Leistungsabfälle möglich
    (0.15, "kritisch", "🟠"),    # 15–30%: spürbare Schwäche, Substratverschiebung
    (0.00, "hungerast", "🔴"),   # <15%: akute Bonk-Gefahr
]

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
    "geschlecht": "Männlich",
    "alter": 30,
    "koerpergewicht_kg": 75,
    "trainings_status": "trained",
    "schweissrate": {
        "preset": "mittel",
        "kalibriert_ml_h": [[10, 250], [15, 300], [20, 350], [25, 450], [99, 600]],
    },
    "flaschen": [{"name": "Trinkflasche", "volumen_ml": 950, "anzahl": 2}],
    "softflask": {
        "flaschen": [
            {"name": "Softflask 450ml", "volumen_ml": 450, "anzahl": 2},
        ],
        "gel_anteil_pct": 70,
        "malto_ratio": 2, "fructose_ratio": 1,
        "salz_normal_g": 0.7, "salz_heiss_g": 1.0, "temp_heiss_grad": 25,
    },
    "riegel": [
        {"name": "Mango Fruchtriegel", "carbs_g": 30, "zucker_g": 18, "gewicht_g": 40, "anzahl": 3, "aktiv": True},
        {"name": "Hafer-Heidelbeere",  "carbs_g": 40, "zucker_g": 12, "gewicht_g": 50, "anzahl": 2, "aktiv": True},
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

def berechne_progressive_carbs_plan(zone, dauer_h, carbs_pro_h=60):
    """
    Berechnet stündliche Carb-Empfehlungen progressiv nach Zone und kumulierter Zeit.

    Relativer Ansatz: Multiplikatoren aus PROGRESSIVE_MULTIPLIKATOREN werden auf
    carbs_pro_h (tatsächlicher Verbrauch aus Watt/Zone) angewendet. So ist der
    progressive Plan immer konsistent mit der Glykogen-Speicherbilanz (kein Überschuss
    der Zufuhr über den Verbrauch in späten Stunden → keine scheinbare Speicher-Auffüllung).

    Deckel bei 90 g/h (Absorptionsgrenze Dual-Source Glukose+Fruktose).

    Returns: list of dicts mit Stunden-Breakdown.
    """
    def multiplikator_fuer_minute(kum_min, z):
        z_key = z if z in ("Z1","Z2","Z3","Z4","Z5") else "Z2"
        for max_min, mults in PROGRESSIVE_MULTIPLIKATOREN:
            if kum_min <= max_min:
                return mults[z_key]
        return PROGRESSIVE_MULTIPLIKATOREN[-1][1].get(z_key, 1.0)

    plan = []
    total_min = dauer_h * 60
    kum_min = 0.0
    stunde = 1

    while kum_min < total_min - 1e-6:
        start_min = kum_min
        end_min = min(kum_min + 60, total_min)
        dauer_min = end_min - start_min
        mid_kum = (start_min + end_min) / 2
        mult = multiplikator_fuer_minute(mid_kum, zone)
        # Rate = Ist-Verbrauch × Progressions-Multiplikator, max. 90 g/h
        rate = min(round(carbs_pro_h * mult), 90)
        carbs_g = round(rate * dauer_min / 60)
        plan.append({
            "stunde": stunde,
            "start_min": round(start_min),
            "end_min": round(end_min),
            "dauer_min": round(dauer_min),
            "carbs_g_h": rate,
            "carbs_g": carbs_g,
        })
        kum_min += 60
        stunde += 1

    return plan

def haversine_m(la1, lo1, la2, lo2):
    """Abstand in Metern zwischen zwei GPS-Koordinaten (Haversine-Formel)."""
    R = 6_371_000.0
    p1, p2 = math.radians(la1), math.radians(la2)
    dphi = math.radians(la2 - la1)
    dlam = math.radians(lo2 - lo1)
    a = math.sin(dphi / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dlam / 2) ** 2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))

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


def berechne_carbs_pro_h_rohwert(watt, ftp):
    """
    Wie berechne_carbs_pro_h_aus_watt, aber OHNE den 120-g-Cap.
    Das ist der echte physiologische Verbrauch – der Cap gilt nur für die
    Zufuhr (Darmabsorption), nicht für den Verbrauch.
    """
    pct_ftp = watt / ftp
    kcal_pro_h = (watt * 3600) / (4180 * WIRKUNGSGRAD)
    carb_anteil = 0.50
    for grenze, anteil in CARB_ANTEIL_NACH_PCT_FTP:
        if pct_ftp <= grenze:
            carb_anteil = anteil
            break
    return round((kcal_pro_h * carb_anteil) / 4.0)


def speicher_zone(prozent):
    """Liefert (status, emoji) für einen Speicher-Rest in Prozent (0..1)."""
    for schwelle, name, emoji in GLYKOGEN_ZONEN:
        if prozent >= schwelle:
            return name, emoji
    return "hungerast", "🔴"


def berechne_glykogen_bilanz(profil, dauer_h, verbrauch_pro_h, zufuhr_pro_h,
                             hm_bonus_g=0, start_voll_pct=1.0,
                             progressive_plan=None, zufuhr_skalar=1.0,
                             cardiac_drift_rate=0.0):
    """
    Berechnet die kumulative Glykogen-Speicherbilanz stundenweise.

    Args:
        profil: Nutzerprofil (für Körpergewicht & Trainingsstatus)
        dauer_h: Gesamtdauer in Stunden (float)
        verbrauch_pro_h: physiologischer KH-Verbrauch in g/h (Basiswert, Stunde 1)
        zufuhr_pro_h: tatsächliche KH-Zufuhr in g/h (Fallback wenn kein progressive_plan)
        hm_bonus_g: zusätzlicher KH-Verbrauch aus Höhenmetern (gesamt, wird verteilt)
        start_voll_pct: Speicherfüllstand zu Beginn (0..1)
        progressive_plan: optionale Liste aus berechne_progressive_carbs_plan()
                          mit stündlichen Zufuhrmengen; überschreibt zufuhr_pro_h.
        zufuhr_skalar: Skalierungsfaktor für progressive Zufuhr (z.B. 0.8 = 80% des Plans).
        cardiac_drift_rate: zusätzlicher KH-Verbrauch pro Stunde als Anteil des Basiswerts
                            (z.B. 0.04 = +4%/h). Modelliert steigenden RER durch Cardiac Drift.
                            Stunde 1: ×1.0, Stunde 2: ×(1+rate), Stunde 3: ×(1+2×rate), …

    Returns:
        dict mit Start-Speicher, stundenweisem Verlauf, kritischer Stunde, Empfehlungen.
    """
    gewicht = profil.get("koerpergewicht_kg", 75)
    status = profil.get("trainings_status", "trained")
    geschlecht = profil.get("geschlecht", "Männlich")
    speicher_tabelle = GLYKOGEN_SPEICHER_G_PRO_KG.get(geschlecht,
                                                     GLYKOGEN_SPEICHER_G_PRO_KG["Männlich"])
    g_pro_kg = speicher_tabelle.get(status, 8.0)
    speicher_voll_g = round(gewicht * g_pro_kg)
    speicher_start_g = round(speicher_voll_g * start_voll_pct)

    # HM-Bonus gleichmäßig über die Dauer verteilen
    hm_bonus_pro_h = hm_bonus_g / dauer_h if dauer_h > 0 else 0
    verbrauch_eff = verbrauch_pro_h + hm_bonus_pro_h

    # Progressive Zufuhr-Lookup vorbereiten (Index = Stunden-Schritt 0,1,2,...)
    prog_lookup = {}
    if progressive_plan:
        for s in progressive_plan:
            prog_lookup[s["stunde"] - 1] = s["carbs_g_h"] * zufuhr_skalar

    # Stundenweise Bilanz (volle Stunden + ggf. Reststunde)
    stunden_liste = []
    speicher_rest = speicher_start_g
    kritische_stunde = None

    h = 0.0
    schritt_idx = 0
    while h < dauer_h - 1e-6:
        schritt = min(1.0, dauer_h - h)

        # Cardiac Drift: Verbrauch steigt pro Stunde um cardiac_drift_rate × Basiswert.
        # Stunde 1 (schritt_idx=0): kein Drift. Stunde 2: +1×rate. Stunde 3: +2×rate. …
        # Physiologisch: steigender RER durch Dehydrierung & Ermüdung bei gleicher Wattzahl.
        drift_multiplikator = 1.0 + cardiac_drift_rate * schritt_idx
        verbrauch_eff_drift = verbrauch_eff * drift_multiplikator
        verbrauch_h = verbrauch_eff_drift * schritt

        # Zufuhr: progressiv wenn vorhanden, sonst flat
        if prog_lookup:
            rate = prog_lookup.get(schritt_idx, list(prog_lookup.values())[-1])
        else:
            rate = zufuhr_pro_h
        zufuhr_h = rate * schritt

        # Während der Fahrt können Glykogenspeicher nicht aufgefüllt werden.
        # Überschuss (Zufuhr > Verbrauch) wird oxidiert, nicht gespeichert.
        zufuhr_effektiv_h = min(zufuhr_h, verbrauch_h)
        defizit_h = verbrauch_h - zufuhr_effektiv_h
        speicher_rest -= defizit_h
        # Speicher kann nicht über Startwert steigen (keine Glykogensynthese während Fahrt)
        speicher_rest = max(0, min(speicher_start_g, speicher_rest))
        rest_pct = speicher_rest / speicher_voll_g if speicher_voll_g > 0 else 0
        zone_name, zone_emoji = speicher_zone(rest_pct)
        h_end = h + schritt
        gedeckt = zufuhr_effektiv_h >= verbrauch_h
        stunden_liste.append({
            "stunde_bis": round(h_end, 2),
            "verbrauch_g": round(verbrauch_h, 1),
            "verbrauch_g_h": round(verbrauch_eff_drift, 1),   # g/h dieser Stunde (für Tabelle)
            "zufuhr_g": round(zufuhr_h, 1),
            "defizit_g": round(defizit_h, 1),
            "gedeckt": gedeckt,
            "speicher_rest_g": round(speicher_rest),
            "speicher_rest_pct": round(rest_pct * 100, 1),
            "zone": zone_name,
            "emoji": zone_emoji,
        })
        if kritische_stunde is None and rest_pct < 0.30:
            kritische_stunde = round(h_end, 2)
        h = h_end
        schritt_idx += 1

    # End-Status und Empfehlungen
    end_speicher_g = stunden_liste[-1]["speicher_rest_g"] if stunden_liste else speicher_start_g
    end_pct = stunden_liste[-1]["speicher_rest_pct"] if stunden_liste else 100.0
    gesamt_verbrauch = sum(s["verbrauch_g"] for s in stunden_liste)
    gesamt_zufuhr = sum(s["zufuhr_g"] for s in stunden_liste)
    gesamt_defizit = gesamt_verbrauch - gesamt_zufuhr

    # Empfehlung: notwendige Zufuhr für kein Defizit
    zufuhr_noetig_pro_h = (verbrauch_eff - (speicher_voll_g * 0.35) / dauer_h) if dauer_h > 0 else 0
    # ↑ Erlaubt 65% Speicher-Verbrauch über die Dauer (typische sichere Reserve)
    zufuhr_noetig_pro_h = max(0, round(zufuhr_noetig_pro_h))

    empfehlungen = []
    if end_pct < 15:
        empfehlungen.append(
            f"⛔ **Hungerast-Risiko!** Speicher wären am Ende bei {end_pct:.0f}%. "
            f"Zufuhr unbedingt auf min. {min(120, zufuhr_noetig_pro_h)} g/h erhöhen, "
            "oder Intensität reduzieren, oder Strecke verkürzen."
        )
    elif end_pct < 30:
        empfehlungen.append(
            f"⚠️ **Kritisch:** Speicher am Ende bei {end_pct:.0f}%. Plan funktioniert, "
            "aber wenig Reserve. Letzte Stunde wird hart, Antritte vermeiden."
        )
    elif end_pct < 50:
        empfehlungen.append(
            f"🟡 **Eng kalkuliert:** Speicher am Ende bei {end_pct:.0f}%. "
            "Geht gut auf, aber Pacing & Fueling konsequent durchhalten."
        )
    else:
        empfehlungen.append(
            f"✅ **Komfortabel:** Speicher am Ende bei {end_pct:.0f}%. "
            "Plan hat Puffer – auch bei leichten Intensitätsschwankungen sicher."
        )

    # Für Empfehlungen: effektive Durchschnittszufuhr nutzen
    zufuhr_avg = gesamt_zufuhr / dauer_h if dauer_h > 0 else zufuhr_pro_h
    if zufuhr_avg < verbrauch_eff - 30 and dauer_h > 3:
        defizit_pro_h = verbrauch_eff - zufuhr_avg
        empfehlungen.append(
            f"📉 Durchschnittlich {defizit_pro_h:.0f} g/h Defizit aus Speichern. "
            f"Speicher schmilzt um ~{(defizit_pro_h/speicher_voll_g)*100:.1f}% pro Stunde."
        )

    if zufuhr_avg > 100:
        empfehlungen.append(
            f"💡 Zufuhr von {zufuhr_avg:.0f} g/h (Ø) ist hoch – Glukose:Fructose 1:0.8 "
            "und Training des Darms (Gut Training) sind Voraussetzung."
        )

    return {
        "koerpergewicht_kg": gewicht,
        "trainings_status": status,
        "geschlecht": geschlecht,
        "g_pro_kg": g_pro_kg,
        "speicher_voll_g": speicher_voll_g,
        "speicher_start_g": speicher_start_g,
        "speicher_end_g": end_speicher_g,
        "speicher_end_pct": end_pct,
        "verbrauch_eff_pro_h": round(verbrauch_eff, 1),
        "zufuhr_pro_h": zufuhr_pro_h,
        "defizit_pro_h": round(verbrauch_eff - zufuhr_pro_h, 1),
        "gesamt_verbrauch_g": round(gesamt_verbrauch),
        "gesamt_zufuhr_g": round(gesamt_zufuhr),
        "gesamt_defizit_g": round(gesamt_defizit),
        "kritische_stunde": kritische_stunde,
        "stunden": stunden_liste,
        "empfehlungen": empfehlungen,
        "zufuhr_empfohlen_pro_h": zufuhr_noetig_pro_h,
    }


def cardiac_drift_rate_auto(temp_c, indoor, zone="Z2"):
    """
    Schätzt die Cardiac-Drift-Rate (Anteil des Basisverbrauchs pro Stunde)
    aus Temperatur, Trainingsumgebung und Intensitätszone.

    Physiologische Grundlage:
    - Cardiac Drift entsteht durch Dehydrierung (sinkender Blutdruck →
      kompensatorisch höhere HR) und Hitzeakkumulation (Coyle & González-Alonso 2001).
    - Indoor ohne Fahrtwind: ~2× stärkere Kerntemperatur-Akkumulation.
    - Höhere Intensität → mehr Wärmeproduktion, schnellere Plasmavolumen-Depletion,
      stärkere Glykogen-Entleerung → ausgeprägterer Drift (Wingo et al. 2012,
      Lafrenz et al. 2008).
    - Jede 10 bpm HR-Drift ≈ +5–8% RER-shift → +4–6% Carb-Verbrauch/h.

    Rückgabe: float, z.B. 0.03 = +3% Mehrverbrauch pro Stunde.
    """
    # Basis aus Temperatur
    if temp_c < 15:
        base = 0.02   # kühl: geringer Drift
    elif temp_c < 25:
        base = 0.035  # moderat
    elif temp_c < 32:
        base = 0.05   # warm
    else:
        base = 0.07   # heiß
    if indoor:
        base += 0.02  # kein Fahrtwind → mehr Kerntemperatur-Anstieg

    # Intensitäts-Multiplikator
    # Z1/Z2: niedriger Drift, viel Fettstoffwechsel, geringe Wärmeproduktion
    # Z3: spürbarer Drift, Schwellenbereich
    # Z4/Z5: starker Drift durch hohe Wärmelast & schnelle Glykogen-Entleerung
    zone_mult = {
        "Z1": 0.7,
        "Z2": 1.0,    # Baseline-Referenz
        "Z3": 1.4,
        "Z4": 1.8,
        "Z5": 2.0,
        "Mix": 1.2,
    }.get(zone, 1.0)

    return round(base * zone_mult, 3)


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

def geschlecht_alter_wasser_faktor(profil):
    """
    Korrekturfaktor für Schweißrate nach Geschlecht und Alter.
    Basis: Sportphysiologie-Literatur (ACSM, Kenefick et al., Gagnon & Kenny).
    Frauen: –8% absolute Schweißrate (Barr et al., Kolka et al.)
    Alter 50–59: –8%, Alter 60+: –13% (Inoue et al., Mack & Nadel)
    Carbs und Koffein: keine Korrektur (<5% Unterschied, zu gering für Praxis).
    """
    faktor = 1.0
    geschlecht = profil.get("geschlecht", "Männlich")
    alter = profil.get("alter", 30)
    if geschlecht == "Weiblich":
        faktor *= 0.92
    if alter >= 60:
        faktor *= 0.87
    elif alter >= 50:
        faktor *= 0.92
    return faktor

def berechne_wasser_pro_stunde(profil, temp, sonne, indoor, zone, frueh_start):
    basis = get_schweissrate_ml_h(profil, temp)
    faktor = (SONNEN_FAKTOR.get(sonne, 1.0)
              * INTENSITAETS_FAKTOR.get(zone, 1.0)
              * (1.3 if indoor else 1.0)
              * (0.9 if frueh_start else 1.0)
              * geschlecht_alter_wasser_faktor(profil))
    return round(basis * faktor)

def empfehle_glukose_fructose(carbs_pro_h):
    """
    Wissenschaftlich empfohlenes Glucose:Fructose-Verhältnis.

    Basis (Jeukendrup 2014, Fuchs et al. 2019, Viribay et al. 2020,
    O'Brien & Rowlands 2011):
      - SGLT1 transportiert Glucose: max ~60–67 g/h
      - GLUT5 transportiert Fructose: max ~50 g/h
      - 2:1 ist der etablierte Standard bis ~90 g/h
        (60 g Glukose + 30 g Fruktose nutzt SGLT1 vollständig aus)
      - 1:0.8 (= 5:4) ist die neuere Empfehlung für > 90 g/h, optimal
        bei sehr hoher Zufuhr (~120 g/h: 67 g Glukose + 53 g Fruktose)
      - 1:1 wird in der Literatur nicht klar gestützt → wird nicht
        mehr verwendet
    """
    if carbs_pro_h < 60:
        return (1, 0, "Nur Maltodextrin/Glucose (SGLT1 noch nicht saturiert, Fructose nicht nötig)")
    elif carbs_pro_h <= 90:
        return (2, 1, "2:1 Maltodextrin:Fructose (klassisches Verhältnis für 60–90 g/h, etabliert)")
    else:
        return (5, 4, "~1:0.8 Maltodextrin:Fructose (>90 g/h, neuere Forschung, optimal bei ~120 g/h)")


def berechne_gel_rezept(profil, carbs_pro_flask, temp, carbs_pro_h=None, volumen_ml=None):
    sf = profil["softflask"]
    if carbs_pro_h is not None:
        malto_ratio, fructose_ratio, _ = empfehle_glukose_fructose(carbs_pro_h)
    else:
        malto_ratio = sf["malto_ratio"]
        fructose_ratio = sf["fructose_ratio"]
    total = malto_ratio + fructose_ratio
    malto = round(carbs_pro_flask * malto_ratio / total)
    fructose = round(carbs_pro_flask * fructose_ratio / total)
    salz = sf["salz_heiss_g"] if temp > sf["temp_heiss_grad"] else sf["salz_normal_g"]
    vol = volumen_ml if volumen_ml is not None else sf.get("flaschen", [{}])[0].get("volumen_ml", 500)
    wasser = vol - carbs_pro_flask - 1
    return {"maltodextrin": malto, "fructose": fructose, "salz": salz, "wasser": max(0, wasser)}

def berechne_koffein(profil, dauer_h):
    """
    Dynamische, körpergewichts- und dauerbasierte Koffeinplanung.

    Wissenschaftliche Grundlage:
    - ISSN Position Stand on Caffeine (2021): 3–6 mg/kg optimal,
      3 mg/kg liefert ~95% des Benefits von 6 mg/kg mit weniger NW
    - IOC Consensus (2010): Aufteilung Initial + Erhaltung möglich
    - Burke / Hawley / Jeukendrup: 1,5 mg/kg alle ~2h als Maintenance
    - EFSA: Einzeldosis ≤ 200 mg, Tagesgrenze 400 mg
    - Halbwertszeit: ~5 h (CYP1A2-Genotyp-abhängig 3–10 h)

    Strategie:
      Initial-Dosis  : 3 mg/kg zum Start (~30 min vor Belastung)
      Erhaltungsdosen: 1,5 mg/kg alle 2 h ab Stunde 2
      Cap (gesamt)   : 6 mg/kg ODER 400 mg (EFSA), je nachdem was niedriger ist
      Letzte Dosis   : spätestens (dauer - 0,5 h), damit nicht zu nah am Ende
    """
    default_return = {
        "caps": 0, "plan": "Koffein deaktiviert",
        "gesamt_mg": 0, "mg_pro_kg": 0.0,
        "timings": [], "cap_grund": None,
    }
    if not profil["koffein"]["aktiv"]:
        return default_return

    mg_pro_cap = profil["koffein"]["pro_cap_mg"]
    gewicht_kg = profil.get("koerpergewicht_kg", 75)

    if dauer_h < 1.5:
        return {**default_return,
                "plan": "Nicht nötig bei < 1,5 h Belastung (kein nennenswerter Performance-Effekt)"}

    # Ziel-Dosen
    initial_mg_target = 3.0 * gewicht_kg          # 3 mg/kg pre/Start
    maintenance_mg_per_dose = 1.5 * gewicht_kg    # 1,5 mg/kg pro Erhaltungsdosis

    # Anzahl Erhaltungsdosen (alle 2 h ab Stunde 2, letzte spätestens dauer-0,5)
    if dauer_h <= 2:
        n_maintenance = 0
    else:
        n_maintenance = max(0, math.floor((dauer_h - 1) / 2.0))

    total_target_mg = initial_mg_target + n_maintenance * maintenance_mg_per_dose

    # Sicherheitsobergrenzen
    max_acute_mg = 6.0 * gewicht_kg
    max_efsa_mg = 400.0
    cap_grund = None
    if total_target_mg > max_acute_mg:
        total_target_mg = max_acute_mg
        cap_grund = f"6 mg/kg Sicherheitsobergrenze ({max_acute_mg:.0f} mg)"
    if total_target_mg > max_efsa_mg:
        total_target_mg = max_efsa_mg
        cap_grund = "EFSA-Tagesgrenze (400 mg)"

    # In Kapseln umrechnen — Sicherheitsgrenzen dürfen durch Rundung NICHT
    # verletzt werden. Erst kaufmännisch runden, dann bei Überschreitung
    # auf floor zurückgehen.
    total_caps = max(1, round(total_target_mg / mg_pro_cap))
    actual_mg = total_caps * mg_pro_cap
    safety_limit_mg = min(max_acute_mg, max_efsa_mg)
    if actual_mg > safety_limit_mg and total_caps > 1:
        total_caps = max(1, math.floor(safety_limit_mg / mg_pro_cap))
        actual_mg = total_caps * mg_pro_cap
        if cap_grund is None:
            cap_grund = (f"EFSA-Tagesgrenze (400 mg)"
                         if max_efsa_mg <= max_acute_mg
                         else f"6 mg/kg Sicherheitsobergrenze ({max_acute_mg:.0f} mg)")

    # Sonderfall: einzelne Kapsel ist bereits > 200 mg → über EFSA-Akutgrenze
    if mg_pro_cap > 200 and cap_grund is None:
        cap_grund = (f"Kapsel-Groesse {mg_pro_cap} mg uebersteigt EFSA-Einzeldosis "
                     "(200 mg) – ggf. teilen oder kleinere Kapseln verwenden.")

    # ── Verteilung: Initial-Dosis + Erhaltungsdosen ──
    # Wenn die Gesamtdosis gedeckelt wurde, Initial proportional reduzieren,
    # damit lange Events nicht front-loaded werden.
    roh_total_mg = initial_mg_target + n_maintenance * maintenance_mg_per_dose
    if cap_grund and roh_total_mg > 0:
        scale = actual_mg / roh_total_mg
        initial_mg_planned = initial_mg_target * scale
    else:
        initial_mg_planned = initial_mg_target

    # Initial-Caps absichern: max. 200 mg pro Einzeldosis (EFSA-Empfehlung
    # für eine einzelne Koffein-Aufnahme bei gesunden Erwachsenen).
    initial_caps_natural = max(1, round(initial_mg_planned / mg_pro_cap))
    max_single_dose_caps = max(1, math.floor(200 / mg_pro_cap))
    initial_caps = min(initial_caps_natural, max_single_dose_caps, total_caps)
    remaining_caps = total_caps - initial_caps

    # ── Timings: pro Maintenance-Slot 1 oder mehr Caps bündeln ──
    timings = [{
        "zeit_h": 0.0,
        "caps": initial_caps,
        "label": f"Start (~30 min vor Belastung): {initial_caps} Cap"
                 + ("s" if initial_caps != 1 else ""),
    }]

    if remaining_caps > 0:
        if n_maintenance == 0 or dauer_h <= 2:
            # Keine Erhaltungsslots vorhanden → restliche Caps an den Anfang anhängen
            timings[0]["caps"] += remaining_caps
            timings[0]["label"] = (
                f"Start (~30 min vor Belastung): {timings[0]['caps']} Cap"
                + ("s" if timings[0]['caps'] != 1 else "")
            )
        else:
            # remaining_caps gleichmäßig auf n_maintenance Slots verteilen
            base_per_slot = remaining_caps // n_maintenance
            extra = remaining_caps % n_maintenance
            end_dose_at = max(2.0, dauer_h - 0.5)
            for i in range(n_maintenance):
                if n_maintenance == 1:
                    t = round((2.0 + end_dose_at) / 2.0, 1)
                else:
                    t = 2.0 + (end_dose_at - 2.0) * i / (n_maintenance - 1)
                    t = round(t, 1)
                # Erste 'extra' Slots bekommen einen Cap mehr (Front-Load)
                caps_this_slot = base_per_slot + (1 if i < extra else 0)
                if caps_this_slot > 0:
                    label = f"h{t:.1f}: {caps_this_slot} Cap" + (
                        "s" if caps_this_slot != 1 else "")
                    timings.append({
                        "zeit_h": t,
                        "caps": caps_this_slot,
                        "label": label,
                    })

    plan_str = " | ".join(t["label"] for t in timings)

    return {
        "caps": total_caps,
        "gesamt_mg": int(round(actual_mg)),
        "mg_pro_kg": round(actual_mg / gewicht_kg, 2),
        "plan": plan_str,
        "timings": timings,
        "cap_grund": cap_grund,
    }

def berechne_riegel_plan(profil, carbs_aus_riegeln, dauer_h, zone):
    aktive = [r for r in profil["riegel"] if r["aktiv"] and r.get("anzahl", 0) > 0]
    if not aktive:
        return []
    return [
        {
            "name": r["name"],
            "anzahl": r.get("anzahl", 1),
            "carbs_g_pro_stueck": r["carbs_g"],
            "carbs_gesamt": r.get("anzahl", 1) * r["carbs_g"],
            "zucker_g_pro_stueck": r.get("zucker_g", 0),
            "zucker_gesamt": r.get("anzahl", 1) * r.get("zucker_g", 0),
        }
        for r in aktive
    ]

def berechne_alles(profil, dauer_h, zone, temp, sonne, indoor, frueh_start,
                   distanz_km=None, hoehenmeter=None, watt=None, ftp=None, hf=None,
                   carbs_pro_h_override=None, wasser_pro_h_override=None, mix_intervalle=None):
    if watt and ftp:
        carbs_pro_h = berechne_carbs_pro_h_aus_watt(watt, ftp)
        carbs_quelle = f"Watt ({watt} W @ FTP {ftp} W)"
    elif carbs_pro_h_override is not None:
        carbs_pro_h = carbs_pro_h_override
        carbs_quelle = f"Mix-Intervalle (Ø {carbs_pro_h:.0f} g/h gewichtet)"
    else:
        carbs_pro_h = CARBS_PRO_STUNDE.get(zone, 60)
        carbs_quelle = f"Zone {zone}"

    # Progressive Carb-Plan berechnen (Zone × kumulierte Zeit)
    # Nur bei >45 min sinnvoll; darunter flache Rate verwenden
    if dauer_h >= 0.75:
        prog_plan = berechne_progressive_carbs_plan(zone, dauer_h, carbs_pro_h=carbs_pro_h)
        carbs_basis = sum(s["carbs_g"] for s in prog_plan)
        carbs_pro_h_avg = round(carbs_basis / dauer_h, 1)
    else:
        prog_plan = []
        carbs_basis = round(carbs_pro_h * dauer_h)
        carbs_pro_h_avg = carbs_pro_h

    hm_bonus = round(hoehenmeter / 100 * HOEHENMETER_CARBS_BONUS_PRO_100HM) if hoehenmeter else 0
    carbs_gesamt = carbs_basis + hm_bonus
    if wasser_pro_h_override is not None:
        wasser_pro_h = wasser_pro_h_override
    else:
        wasser_pro_h = berechne_wasser_pro_stunde(profil, temp, sonne, indoor, zone, frueh_start)
    wasser_gesamt = round(wasser_pro_h * dauer_h)
    sf = profil["softflask"]
    gel_anteil = sf["gel_anteil_pct"] / 100
    carbs_aus_gels = round(carbs_gesamt * gel_anteil)
    carbs_aus_riegeln = carbs_gesamt - carbs_aus_gels
    # Softflask-Pool: alle mitgenommenen Flaschen zusammenrechnen
    aktive_sf = [f for f in sf.get("flaschen", []) if f.get("anzahl", 0) > 0]
    anzahl_flasks = sum(f["anzahl"] for f in aktive_sf)
    total_vol_sf = sum(f["volumen_ml"] * f["anzahl"] for f in aktive_sf)
    wasser_aus_gels = round(total_vol_sf * 0.69) if total_vol_sf > 0 else 0
    # Rezept pro Flask-Typ proportional zum Volumen befüllen
    sf_detail = []
    if anzahl_flasks > 0 and total_vol_sf > 0 and carbs_aus_gels > 0:
        carb_dichte = carbs_aus_gels / total_vol_sf
        for f in aktive_sf:
            cpf = max(1, round(carb_dichte * f["volumen_ml"]))
            sf_detail.append({
                "name": f.get("name", f"Softflask {f['volumen_ml']}ml"),
                "volumen_ml": f["volumen_ml"],
                "anzahl": f["anzahl"],
                "carbs_pro_flask": cpf,
                "rezept": berechne_gel_rezept(profil, cpf, temp, carbs_pro_h, volumen_ml=f["volumen_ml"]),
            })
    carbs_pro_flask = round(carbs_aus_gels / anzahl_flasks) if anzahl_flasks > 0 else 0
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
        "carbs": {"pro_h": carbs_pro_h, "pro_h_avg": carbs_pro_h_avg,
                  "gesamt": carbs_gesamt, "basis": carbs_basis,
                  "hm_bonus": hm_bonus, "aus_gels": carbs_aus_gels,
                  "aus_riegeln": carbs_aus_riegeln, "quelle": carbs_quelle,
                  "progressiv": prog_plan},
        "wasser": {"pro_h": wasser_pro_h, "gesamt": wasser_gesamt, "aus_gels": wasser_aus_gels,
                   "zusaetzlich": wasser_zusaetzlich, "flaschen_kapazitaet_ml": flaschen_kapazitaet_ml,
                   "refill_ml": refill_ml},
        "softflasks": {
            "anzahl": anzahl_flasks,
            "carbs_pro_flask": carbs_pro_flask,
            "gesamt_volumen_ml": total_vol_sf,
            "flaschen": sf_detail,
            "rezept": sf_detail[0]["rezept"] if sf_detail else {},
            "ratio_info": empfehle_glukose_fructose(carbs_pro_h),
        },
        "riegel": riegel_plan,
        "wasserflaschen": {"konfiguration": profil["flaschen"], "kapazitaet_ml": flaschen_kapazitaet_ml,
                           "auffuellungen": auffuellungen_noetig, "refill_ml": refill_ml},
        "elektrolyte": {"name": el["name"], "portion_g": el_portion, "gesamt_g": el_gesamt,
                        "fuellungen": fuellungen, "mineralien": mineralien_gesamt,
                        "min_pro_portion": min_profil},
        "koffein": koffein, "distanz_km": distanz_km, "hoehenmeter": hoehenmeter,
        "mix_intervalle": mix_intervalle,
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

def hole_wetterdaten_fuer_route(gpx_route, lat_start, lon_start, datum_str,
                                start_h, dauer_h, zone, distanz_km):
    """
    Holt Wetterdaten an mehreren Punkten entlang der Route.
    Ab 80 km werden automatisch zusätzliche Messpunkte alle ~60 km gesetzt.
    Die Uhrzeit je Punkt wird aus der geschätzten Ankunftszeit berechnet.
    Gibt (merged_wetter_roh, punkte_info_liste) zurück.
    """
    GESCHW = {"Z1": 22, "Z2": 24, "Z3": 28, "Z4": 32, "Z5": 32, "Mix": 25}
    speed = GESCHW.get(zone, 24)

    # Messpunkte bestimmen
    if gpx_route and distanz_km and distanz_km > 80:
        anzahl = min(6, max(2, math.ceil(distanz_km / 60)))
        # Gleichmäßige Verteilung, letzter Punkt bei 95% der Strecke
        km_punkte = [round(distanz_km * i / (anzahl - 1), 1) for i in range(anzahl - 1)]
        km_punkte.append(round(distanz_km * 0.95, 1))
    else:
        km_punkte = [0.0]

    alle_roh = []
    punkte_info = []

    for km in km_punkte:
        stunden_offset = km / speed
        punkt_h = min(23, int(start_h + stunden_offset))

        if km == 0 or not gpx_route:
            plat, plon = lat_start, lon_start
        else:
            plat, plon = km_zu_gpx_koordinaten(gpx_route, km)

        verbleibend = max(1.0, dauer_h - stunden_offset)
        wetter = hole_wetterdaten(plat, plon, datum_str, punkt_h, min(2.0, verbleibend))

        if wetter and wetter["temperaturen"]:
            alle_roh.append(wetter)
            punkte_info.append({
                "km": km,
                "lat": plat,
                "lon": plon,
                "uhrzeit": f"{punkt_h:02d}:00 Uhr",
                "temp_avg": round(sum(wetter["temperaturen"]) / len(wetter["temperaturen"]), 1),
                "regen_mm": round(sum(wetter["niederschlag"]), 1),
            })

    if not alle_roh:
        return None, []

    # Alle Messwerte zusammenführen (Gesamtdurchschnitt über Route + Zeitraum)
    merged = {k: [] for k in ("stunden", "temperaturen", "luftfeuchte", "niederschlag", "wind", "wolken", "uv")}
    for w in alle_roh:
        for key in ("temperaturen", "luftfeuchte", "niederschlag", "wind", "wolken", "uv"):
            merged[key].extend(w[key])
    merged["stunden"] = alle_roh[0]["stunden"]

    return merged, punkte_info


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

def _overpass_pois_aus_elementen(els, ref_lat=None, ref_lon=None):
    """Hilfsfunktion: wandelt Overpass-Elemente in POI-Dicts um."""
    treffer = []
    for el in els:
        tags = el.get("tags", {})
        roh = tags.get("amenity") or tags.get("shop", "")
        poi = {
            "name": tags.get("name", "Unbekannt"),
            "typ": POI_TYP_NAMEN.get(roh, roh.capitalize()),
            "strasse": (tags.get("addr:street", "") + " " + tags.get("addr:housenumber", "")).strip(),
            "ort": tags.get("addr:city") or tags.get("addr:town") or tags.get("addr:village", ""),
            "lat": el["lat"], "lon": el["lon"],
            "dist_m": round(haversine_m(ref_lat, ref_lon, el["lat"], el["lon"])) if ref_lat else 0,
        }
        treffer.append(poi)
    return treffer

def _overpass_request(query, timeout=12):
    """Sendet eine Overpass-Anfrage und gibt die Elemente zurück."""
    try:
        data = urllib.parse.urlencode({"data": query}).encode()
        req = urllib.request.Request(
            "https://overpass-api.de/api/interpreter", data=data, method="POST",
            headers={"User-Agent": "FuelingPlanner/2.0 (cycling nutrition)"},
        )
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode()).get("elements", [])
    except Exception:
        return []

_OVERPASS_TYPEN = [
    '"amenity"="fuel"', '"amenity"="supermarket"',
    '"shop"="supermarket"', '"shop"="convenience"',
    '"shop"="grocery"', '"shop"="bakery"',
]

def suche_pois_entlang_route(route, km_spaetestens, radius_m=500, km_fenster=25):
    """
    Sucht Einkaufsmöglichkeiten in einem Fenster [km_spaetestens-km_fenster … km_spaetestens]
    entlang der GPX-Route. Nutzt eine einzige Overpass-Polyline-Query (around:<r>,lat1,lon1,...).
    Bevorzugt Stationen, die nah an der Route liegen (≤ radius_m) und möglichst weit
    hinten auf der Strecke sind (lieber kurz vor dem Bedarf als zu weit vorher).
    Gibt POIs mit 'route_km' (km-Position auf der Route) und 'dist_m' (Abstand zur Route) zurück.
    """
    kum = route["kumulative_distanzen"]
    points = route["points"]
    km_start = max(0.5, km_spaetestens - km_fenster)

    # Routenpunkte im Suchfenster samplen – alle ~2 km für die Polyline-Query
    sample = []
    letztes = -99.0
    for i, d in enumerate(kum):
        if km_start <= d <= km_spaetestens and d - letztes >= 2.0:
            lat, lon, _ = points[i]
            sample.append((d, lat, lon))
            letztes = d
    if not sample:
        # Fallback: nur den Endpunkt nutzen
        idx = next((i for i, d in enumerate(kum) if d >= km_spaetestens), len(kum) - 1)
        lat, lon, _ = points[idx]
        sample = [(km_spaetestens, lat, lon)]

    # Overpass Polyline-Query: around:<r>,lat1,lon1,lat2,lon2,...
    coords = ",".join(f"{lat},{lon}" for _, lat, lon in sample)
    parts = "\n".join(f"  node[{t}](around:{radius_m},{coords});" for t in _OVERPASS_TYPEN)
    query = f"[out:json][timeout:12];\n(\n{parts}\n);\nout body;"

    els = _overpass_request(query, timeout=12)
    if not els:
        return []

    # Für jeden POI: nächster Routenpunkt im Fenster (+ etwas Puffer)
    km_lo, km_hi = km_start - 2, km_spaetestens + 2
    ergebnisse = []
    seen = set()
    for el in els:
        osm_id = el.get("id")
        if osm_id in seen:
            continue
        seen.add(osm_id)
        tags = el.get("tags", {})
        roh = tags.get("amenity") or tags.get("shop", "")

        min_dist = float("inf")
        best_km = 0.0
        for i, d in enumerate(kum):
            if km_lo <= d <= km_hi:
                dist = haversine_m(el["lat"], el["lon"], points[i][0], points[i][1])
                if dist < min_dist:
                    min_dist = dist
                    best_km = d

        ergebnisse.append({
            "name": tags.get("name", "Unbekannt"),
            "typ": POI_TYP_NAMEN.get(roh, roh.capitalize()),
            "strasse": (tags.get("addr:street", "") + " " + tags.get("addr:housenumber", "")).strip(),
            "ort": tags.get("addr:city") or tags.get("addr:town") or tags.get("addr:village", ""),
            "lat": el["lat"], "lon": el["lon"],
            "dist_m": round(min_dist),
            "route_km": round(best_km, 1),
        })

    # Sortierung: erst nach Routennähe (≤300 m bevorzugt), dann möglichst spät auf Route
    ergebnisse.sort(key=lambda x: (x["dist_m"] > 300, -(x["route_km"])))
    return ergebnisse[:6]

def km_zu_gpx_koordinaten(route, ziel_km):
    """Gibt die Routenkoordinaten am nächsten GPX-Punkt zur gegebenen km-Position zurück."""
    kum = route["kumulative_distanzen"]
    points = route["points"]
    idx = next((i for i, d in enumerate(kum) if d >= ziel_km), len(kum) - 1)
    lat, lon, _ = points[idx]
    return lat, lon


def berechne_resupply_stopps(profil, plan, route):
    """
    Berechnet kombinierte Wasser- und Carb-Resupply-Punkte entlang der Route.
    Stopps liegen an echten GPX-Routenpunkten (nicht am Start).
    Wasser: Stopp bei 82% verbraucht (~18% Reserve).
    Carbs:  Stopp bei 80% der Tragekapazität verbraucht.
    Stopps innerhalb von 15 km werden zusammengelegt.
    """
    if not route:
        return []

    distanz_km = route["distanz_km"]
    if distanz_km <= 0:
        return []

    # ── Wasser-Stopps ────────────────────────────────────────────────────────
    wasser_stopps = []
    wasser_zusaetzlich = plan["wasser"]["zusaetzlich"]
    auffuellungen = plan["wasserflaschen"]["auffuellungen"]

    if wasser_zusaetzlich > 0 and auffuellungen > 0:
        wasser_pro_km = wasser_zusaetzlich / distanz_km
        km_bisher = 0.0
        wasser_aktuell = float(plan["wasser"]["flaschen_kapazitaet_ml"])
        refill_ml = plan["wasserflaschen"]["refill_ml"]

        for _ in range(auffuellungen):
            km_stop = km_bisher + (wasser_aktuell * AUFFUELL_BUFFER_PCT) / wasser_pro_km
            km_stop = min(km_stop, distanz_km * 0.95)
            rest_ml = round(wasser_aktuell * (1 - AUFFUELL_BUFFER_PCT))
            wasser_stopps.append({
                "km": round(km_stop, 1),
                "wasser_rest_ml": rest_ml,
                "wasser_refill_ml": refill_ml,
                "braucht_wasser": True,
                "braucht_carbs": False,
                "carbs_rest_g": None,
                "carbs_einkauf_g": None,
            })
            km_bisher = km_stop
            wasser_aktuell = rest_ml + refill_ml

    # ── Carb-Stopps ──────────────────────────────────────────────────────────
    carb_stopps = []
    aktive_riegel = [r for r in profil["riegel"] if r["aktiv"] and r.get("anzahl", 0) > 0]
    carbs_aus_riegeln = plan["carbs"]["aus_riegeln"]
    kapazitaet_g = sum(r["carbs_g"] * r.get("anzahl", 0) for r in aktive_riegel)
    total_anzahl_r = sum(r.get("anzahl", 0) for r in aktive_riegel)
    avg_carbs = kapazitaet_g / total_anzahl_r if total_anzahl_r > 0 else 35

    if aktive_riegel and carbs_aus_riegeln > 0 and kapazitaet_g > 0:
        carbs_pro_km = carbs_aus_riegeln / distanz_km
        CARB_BUFFER = 0.80

        km_bisher = 0.0
        vorrat_g = kapazitaet_g
        carbs_verbleibend = carbs_aus_riegeln

        while km_bisher < distanz_km * 0.90:
            km_stop = km_bisher + (vorrat_g * CARB_BUFFER) / carbs_pro_km
            km_stop = min(km_stop, distanz_km * 0.95)
            if km_stop >= distanz_km * 0.88:
                break
            rest_g = round(vorrat_g * (1 - CARB_BUFFER))
            verbraucht = round((km_stop - km_bisher) * carbs_pro_km)
            carbs_verbleibend = max(0, carbs_verbleibend - verbraucht)
            einkauf_g = max(0, round(min(carbs_verbleibend, kapazitaet_g) - rest_g))
            carb_stopps.append({
                "km": round(km_stop, 1),
                "braucht_wasser": False,
                "braucht_carbs": True,
                "wasser_rest_ml": None,
                "wasser_refill_ml": None,
                "carbs_rest_g": rest_g,
                "carbs_einkauf_g": einkauf_g,
                "carbs_verbleibend_g": carbs_verbleibend,
            })
            km_bisher = km_stop
            vorrat_g = rest_g + einkauf_g

    # ── Stopps zusammenführen ─────────────────────────────────────────────────
    MERGE_RADIUS_KM = 15.0
    alle = []
    used_carb = set()

    for ws in wasser_stopps:
        merged = dict(ws)
        for ci, cs in enumerate(carb_stopps):
            if ci in used_carb:
                continue
            if abs(cs["km"] - ws["km"]) <= MERGE_RADIUS_KM:
                merged["braucht_carbs"] = True
                merged["carbs_rest_g"] = cs["carbs_rest_g"]
                merged["carbs_einkauf_g"] = cs["carbs_einkauf_g"]
                merged["carbs_verbleibend_g"] = cs.get("carbs_verbleibend_g")
                merged["km"] = round((ws["km"] + cs["km"]) / 2, 1)
                used_carb.add(ci)
                break
        alle.append(merged)

    for ci, cs in enumerate(carb_stopps):
        if ci not in used_carb:
            alle.append(dict(cs))

    alle.sort(key=lambda x: x["km"])

    # ── GPX-Koordinaten zuweisen ──────────────────────────────────────────────
    for stopp in alle:
        lat, lon = km_zu_gpx_koordinaten(route, stopp["km"])
        stopp["lat"] = lat
        stopp["lon"] = lon
        stopp["pois"] = []

    return alle


def schaetze_dauer(distanz_km, hoehenmeter, zone="Z2"):
    v = {"Z1": 22, "Z2": 24, "Z3": 28, "Z4": 32, "Z5": 32, "Mix": 25}.get(zone, 24)
    return round(distanz_km / v + (hoehenmeter / 100) * (6 / 60), 1)

def erstelle_plan_text(e, wetter_info=None, wetter_punkte=None, resupply_stopps=None,
                       export_context=None):
    """
    Erstellt einen umfassenden Plan-Export als formatierten Text.
    Bildet alle Daten aus der App-Ansicht ab, inkl. Glykogen-Bilanz und
    Cardiac Drift.
    """
    ctx = export_context or {}
    profil = ctx.get("profil", {})
    ist_indoor = ctx.get("ist_indoor", False)
    ist_konstant = ctx.get("ist_konstant", False)
    konstant_g_h = ctx.get("konstant_g_h")
    bilanz = ctx.get("bilanz") or {}
    drift_rate = ctx.get("drift_rate", 0.0)
    start_voll_pct = ctx.get("start_voll_pct", 1.0)
    zufuhr_skalar = ctx.get("zufuhr_skalar", 1.0)
    gpx_data = ctx.get("gpx_data")

    sf_res = e.get("softflasks", {})
    wf = e.get("wasserflaschen", {})
    sonne_label = {"keine": "Bedeckt", "mittel": "Teils sonnig", "stark": "Vollsonne"}
    zone_namen = {
        "Z1": "Z1 (Erholung)", "Z2": "Z2 (Grundlage / Aerob)",
        "Z3": "Z3 (Tempo / Sweetspot)", "Z4": "Z4 (Schwelle)",
        "Z5": "Z5 (Maximalintensität)", "Mix": "Mix (gemischte Zonen)",
    }

    WIDTH = 78

    def hline(char="─"):
        return char * WIDTH

    def section_head(title, emoji=""):
        bar = "═" * WIDTH
        prefix = f"  {emoji} " if emoji else "  "
        return ["", bar, f"{prefix}{title}", bar]

    def sub_head(title):
        return [f"\n{title}", hline()]

    def kv(label, value, width=20):
        return f"  {label:<{width}}: {value}"

    def bullet(text, indent=2):
        return f"{' ' * indent}• {text}"

    lines = []

    # ════════════════════════════════════════════════════════════════════
    # KOPF / TITELBLOCK
    # ════════════════════════════════════════════════════════════════════
    lines += [
        "█" * WIDTH,
        "█" + " " * (WIDTH - 2) + "█",
        "█" + "🚴  CYCLING FUELING PLAN  🚴".center(WIDTH - 2) + "█",
        "█" + " " * (WIDTH - 2) + "█",
        "█" * WIDTH,
        "",
    ]

    # ── Übersicht ──
    lines += sub_head("ℹ️  ÜBERSICHT")
    lines += [
        kv("Profil", e.get("profil_name", "—")),
        kv("Erstellt am", datetime.now().strftime("%d.%m.%Y, %H:%M Uhr")),
        kv("Trainingsmodus", "Indoor (Rolle / Heimtrainer)" if ist_indoor
                              else "Outdoor (Straße / Gelände)"),
        kv("Dauer", f"{e['dauer_h']} h"),
    ]
    if not ist_indoor:
        if e.get("distanz_km"):
            lines.append(kv("Distanz", f"{e['distanz_km']:.1f} km"))
        if e.get("hoehenmeter"):
            lines.append(kv("Höhenmeter", f"{e['hoehenmeter']:.0f} m"))
    if profil.get("koerpergewicht_kg"):
        lines.append(kv("Körpergewicht", f"{profil['koerpergewicht_kg']} kg"))

    # ── Trainingsintensität ──
    lines += sub_head("⚡ TRAININGSINTENSITÄT")
    if e.get("watt") and e.get("ftp"):
        pct_ftp = round(e["watt"] / e["ftp"] * 100, 1)
        watt_label = ("Leistung (Durchschnitt)" if ist_indoor
                      else "Leistung (Normalized Power)")
        lines += [
            kv(watt_label, f"{e['watt']:.0f} W"),
            kv("FTP", f"{e['ftp']:.0f} W   →  {pct_ftp}% FTP"),
        ]
    elif e.get("hf") and e.get("hr_max"):
        pct_hrmax = round(e["hf"] / e["hr_max"] * 100, 1)
        lines += [
            kv("Herzfrequenz", f"{e['hf']:.0f} bpm"),
            kv("HRmax", f"{e['hr_max']} bpm   →  {pct_hrmax}% HRmax"),
        ]
    lines += [
        kv("Zone", zone_namen.get(e["zone"], e["zone"])),
        kv("Quelle", e["carbs"]["quelle"]),
    ]

    # ── Wetter (nur Outdoor) ──
    if wetter_info and not ist_indoor:
        lines += sub_head("🌡  WETTERBEDINGUNGEN")
        lines += [
            kv("Temperatur Ø", f"{wetter_info['avg_temp']}°C  "
                                f"(min {wetter_info['min_temp']} / max {wetter_info['max_temp']})"),
            kv("Sonneneinstrahlung",
               sonne_label.get(wetter_info.get("sonne", ""),
                               wetter_info.get("sonne", "-"))),
            kv("Wind Ø", f"{wetter_info['avg_wind']} km/h"),
            kv("Regen", f"{wetter_info['sum_regen']} mm"),
        ]
        if wetter_punkte and len(wetter_punkte) > 1:
            lines.append("")
            lines.append("  Wetterverlauf entlang der Route:")
            lines.append(f"    {'km':>4}  {'Uhrzeit':>7}  {'Lat':>9}  {'Lon':>9}  "
                         f"{'Temp':>6}  {'Regen':>7}")
            lines.append(f"    {'─' * 4}  {'─' * 7}  {'─' * 9}  {'─' * 9}  "
                         f"{'─' * 6}  {'─' * 7}")
            for pt in wetter_punkte:
                lines.append(
                    f"    {pt.get('km', '?'):>4}  {pt.get('uhrzeit', ''):>7}  "
                    f"{pt.get('lat', 0):>9.4f}  {pt.get('lon', 0):>9.4f}  "
                    f"{pt.get('temp_avg', '?'):>4}°C  {pt.get('regen_mm', '?'):>5} mm"
                )
    elif ist_indoor:
        lines += sub_head("🌡  TRAININGSUMGEBUNG")
        lines.append(kv("Raumtemperatur", f"{e['temp']}°C"))

    # ════════════════════════════════════════════════════════════════════
    # KOHLENHYDRATE
    # ════════════════════════════════════════════════════════════════════
    lines += section_head("KOHLENHYDRATE", "🍬")

    strategie_label = (
        f"➡️ Konstant ({konstant_g_h} g/h jede Stunde)"
        if (ist_konstant and konstant_g_h is not None)
        else "📈 Progressiv (steigt über die Zeit)"
    )

    lines += sub_head("GESAMTBEDARF")
    lines += [
        kv("Strategie", strategie_label),
        kv("Gesamt-Carbs", f"{e['carbs']['gesamt']} g"),
        kv("Pro Stunde Ø",
           f"{konstant_g_h} g/h" if (ist_konstant and konstant_g_h is not None)
           else f"{e['carbs']['pro_h_avg']} g/h"),
        kv("Basis-Berechnung", f"{e['carbs']['basis']} g"),
    ]
    if e["carbs"].get("hm_bonus"):
        lines.append(kv("Höhenmeter-Bonus", f"+{e['carbs']['hm_bonus']} g"))

    lines += sub_head("VERTEILUNG GELS & RIEGEL")
    gesamt = max(1, e["carbs"]["gesamt"])
    gels_pct = round(e["carbs"]["aus_gels"] / gesamt * 100)
    rieg_pct = round(e["carbs"]["aus_riegeln"] / gesamt * 100)
    lines += [
        kv("Aus Gels", f"{e['carbs']['aus_gels']} g  ({gels_pct}%)"),
        kv("Aus Riegeln", f"{e['carbs']['aus_riegeln']} g  ({rieg_pct}%)"),
    ]
    if sf_res.get("ratio_info"):
        lines.append(kv("Glukose:Fructose", sf_res["ratio_info"][2]))

    # Progressiver Stundenplan ODER Konstante Aufschlüsselung
    prog_txt = e["carbs"].get("progressiv", [])
    if ist_konstant and konstant_g_h is not None:
        lines += sub_head("➡️ KONSTANTE ZUFUHR PRO STUNDE")
        gesamt_k = round(konstant_g_h * e["dauer_h"])
        lines.append(kv("Pro Stunde", f"{konstant_g_h} g"))
        lines.append(kv("Dauer", f"{e['dauer_h']} h"))
        lines.append(kv("Gesamt-Menge", f"{gesamt_k} g"))
    elif prog_txt and len(prog_txt) > 1:
        lines += sub_head("📈 PROGRESSIVER STUNDENPLAN")
        max_rate = max(s["carbs_g_h"] for s in prog_txt) or 1
        lines.append(f"  {'Stunde':<12} {'g/h':>7} {'Menge':>8}   {'Verlauf'}")
        lines.append(f"  {'─' * 12} {'─' * 7} {'─' * 8}   {'─' * 20}")
        for s in prog_txt:
            stunde = (f"{s['start_min']}–{s['end_min']} min"
                      if s["dauer_min"] < 60 else f"Stunde {s['stunde']}")
            pct = s["carbs_g_h"] / max_rate
            bar = "█" * int(pct * 14) + "░" * (14 - int(pct * 14))
            lines.append(f"  {stunde:<12} {s['carbs_g_h']:>5} g {s['carbs_g']:>6} g   {bar}")
        gesamt_p = sum(s["carbs_g"] for s in prog_txt)
        lines.append(f"  {'─' * 12} {'─' * 7} {'─' * 8}")
        lines.append(f"  {'Summe':<12} {'':>7} {gesamt_p:>6} g  "
                     f"(Ø {e['carbs']['pro_h_avg']} g/h)")

    # ════════════════════════════════════════════════════════════════════
    # WASSER & ELEKTROLYTE
    # ════════════════════════════════════════════════════════════════════
    lines += section_head("WASSER & ELEKTROLYTE", "💧")

    lines += sub_head("WASSERMENGE")
    lines += [
        kv("Gesamt", f"{e['wasser']['gesamt']} ml  ({e['wasser']['pro_h']} ml/h)"),
        kv("Aus Gels", f"{e['wasser']['aus_gels']} ml"),
        kv("Aus Trinkflaschen", f"{e['wasser']['zusaetzlich']} ml"),
    ]
    if profil.get("schweissrate", {}).get("preset"):
        preset = profil["schweissrate"]["preset"]
        preset_label = {"wenig": "Wenig-Schwitzer",
                        "mittel": "Mittel-Schwitzer",
                        "viel": "Viel-Schwitzer",
                        "kalibriert": "Kalibriert (eigene Werte)"}.get(preset, preset)
        lines.append(kv("Schweißtyp", preset_label))
    if wf and wf.get("auffuellungen", 0) > 0:
        lines.append(kv("Auffüllungen",
                        f"{wf['auffuellungen']}×  (Ø {wf.get('refill_ml', 0)} ml/Mal)"))

    lines += sub_head("ELEKTROLYTE")
    el = e["elektrolyte"]
    lines += [
        kv("Produkt", el["name"]),
        kv("Portion", f"{el['portion_g']} g"),
        kv("Anzahl Portionen", f"{el['fuellungen']}×"),
        kv("Gesamt", f"{el['gesamt_g']} g"),
    ]
    minerals = el.get("mineralien", {})
    nicht_null = {m: v for m, v in minerals.items() if v}
    if nicht_null:
        lines.append("")
        lines.append("  Mineralstoff-Gesamtmenge:")
        for m_name in ["natrium", "kalium", "chlorid", "calcium", "magnesium"]:
            if minerals.get(m_name):
                lines.append(f"    • {m_name.capitalize():<10}: {minerals[m_name]} mg")

    # ════════════════════════════════════════════════════════════════════
    # GLYKOGEN-SPEICHERBILANZ
    # ════════════════════════════════════════════════════════════════════
    if bilanz:
        lines += section_head("GLYKOGEN-SPEICHERBILANZ", "🧬")

        ts_label = {"untrained": "Untrainiert",
                    "trained": "Trainiert",
                    "trained_loaded": "Trainiert + Carbo-Loading",
                    "elite_loaded": "Elite + Loading"}.get(
                        bilanz.get("trainings_status", ""),
                        bilanz.get("trainings_status", "—"))
        lines += sub_head("SPEICHERSTATUS")
        lines += [
            kv("Körpergewicht", f"{bilanz['koerpergewicht_kg']} kg"),
            kv("Trainingsstatus", ts_label),
            kv("Glykogenkapazität", f"{bilanz['g_pro_kg']} g/kg"),
            kv("Speicher voll", f"{bilanz['speicher_voll_g']} g"),
            kv("Start-Füllstand",
               f"{int(start_voll_pct * 100)}%  ({bilanz['speicher_start_g']} g)"),
            kv("Verbrauch (echt)",
               f"{bilanz['verbrauch_eff_pro_h']:.0f} g/h "
               f"{'(steigt mit Drift)' if drift_rate > 0 else '(konstant)'}"),
            kv("Speicher am Ende",
               f"{bilanz['speicher_end_pct']:.0f}%  ({bilanz['speicher_end_g']} g)"),
        ]

        if drift_rate > 0:
            lines += sub_head("🫀 CARDIAC DRIFT")
            verbrauch_basis = bilanz["verbrauch_eff_pro_h"]
            verbrauch_end = verbrauch_basis * (1 + drift_rate * (e["dauer_h"] - 1))
            lines += [
                kv("Drift-Rate", f"+{drift_rate*100:.1f}% pro Stunde"),
                kv("Verbrauch Stunde 1", f"{verbrauch_basis:.0f} g/h"),
                kv(f"Verbrauch Stunde {int(e['dauer_h'])}",
                   f"{verbrauch_end:.0f} g/h"),
            ]

        # Stündlicher Verlauf
        stunden = bilanz.get("stunden", [])
        if stunden:
            lines += sub_head("STÜNDLICHER VERLAUF")
            if drift_rate > 0:
                lines.append(f"  {'Stunde':>7}  {'Verbr.':>8}  {'Zufuhr':>8}  "
                             f"{'Aus Speich.':>12}  {'Speicher':>9}  {'Rest %':>6}")
                lines.append(f"  {'─' * 7}  {'─' * 8}  {'─' * 8}  "
                             f"{'─' * 12}  {'─' * 9}  {'─' * 6}")
                for s in stunden:
                    aus_sp = ("✓ gedeckt" if s["gedeckt"]
                              else f"+{s['defizit_g']:.0f} g")
                    lines.append(
                        f"  {s['stunde_bis']:>5.1f} h  "
                        f"{s['verbrauch_g']:>6.0f} g  "
                        f"{s['zufuhr_g']:>6.0f} g  "
                        f"{aus_sp:>12}  "
                        f"{s['speicher_rest_g']:>7} g  "
                        f"{s['speicher_rest_pct']:>5.0f}%"
                    )
            else:
                lines.append(f"  {'Stunde':>7}  {'Verbr.':>8}  {'Zufuhr':>8}  "
                             f"{'Aus Speich.':>12}  {'Speicher':>9}  {'Rest %':>6}")
                lines.append(f"  {'─' * 7}  {'─' * 8}  {'─' * 8}  "
                             f"{'─' * 12}  {'─' * 9}  {'─' * 6}")
                for s in stunden:
                    aus_sp = ("✓ gedeckt" if s["gedeckt"]
                              else f"+{s['defizit_g']:.0f} g")
                    lines.append(
                        f"  {s['stunde_bis']:>5.1f} h  "
                        f"{s['verbrauch_g']:>6.0f} g  "
                        f"{s['zufuhr_g']:>6.0f} g  "
                        f"{aus_sp:>12}  "
                        f"{s['speicher_rest_g']:>7} g  "
                        f"{s['speicher_rest_pct']:>5.0f}%"
                    )

        # Empfehlungen
        empfehlungen = bilanz.get("empfehlungen", [])
        if empfehlungen:
            lines += sub_head("EMPFEHLUNGEN")
            for emp in empfehlungen:
                clean = emp.replace("**", "")
                lines.append(f"  • {clean}")

    # ════════════════════════════════════════════════════════════════════
    # SOFTFLASKS
    # ════════════════════════════════════════════════════════════════════
    sf_flaschen = sf_res.get("flaschen", [])
    if sf_flaschen or sf_res.get("anzahl", 0) > 0:
        lines += section_head("SOFTFLASKS (selbstgemischt)", "🍯")
        if sf_flaschen:
            for f in sf_flaschen:
                r = f.get("rezept", {})
                lines.append(f"\n  {f['anzahl']}× {f['name']}  ({f['volumen_ml']} ml)")
                lines.append("  " + "─" * (WIDTH - 4))
                lines += [
                    kv("Carbs/Flask", f"{f['carbs_pro_flask']} g", width=18),
                    kv("Maltodextrin", f"{r.get('maltodextrin', 0)} g", width=18),
                    kv("Fructose", f"{r.get('fructose', 0)} g", width=18),
                    kv("Salz", f"{r.get('salz', 0)} g", width=18),
                    kv("Wasser", f"{r.get('wasser', 0)} ml", width=18),
                ]
        else:
            r0 = sf_res.get("rezept", {})
            lines += [
                kv("Anzahl", sf_res.get("anzahl", 0)),
                kv("Carbs/Flask", f"{sf_res.get('carbs_pro_flask', 0)} g"),
                kv("Maltodextrin", f"{r0.get('maltodextrin', 0)} g"),
                kv("Fructose", f"{r0.get('fructose', 0)} g"),
                kv("Salz", f"{r0.get('salz', 0)} g"),
                kv("Wasser", f"{r0.get('wasser', 0)} ml"),
            ]

    # ════════════════════════════════════════════════════════════════════
    # RIEGEL
    # ════════════════════════════════════════════════════════════════════
    if e.get("riegel"):
        lines += section_head("RIEGEL & SNACKS", "🍫")
        gesamt_riegel = 0
        gesamt_riegel_carbs = 0
        for r in e["riegel"]:
            lines.append(f"\n  {r['anzahl']}× {r['name']}")
            lines.append(f"     Carbs: {r['carbs_gesamt']} g "
                         f"({r['anzahl']}× {r['carbs_g_pro_stueck']} g)  "
                         f"|  Zucker: {r['zucker_gesamt']} g")
            gesamt_riegel += r["anzahl"]
            gesamt_riegel_carbs += r["carbs_gesamt"]
        lines.append("")
        lines.append(f"  GESAMT: {gesamt_riegel} Riegel  |  {gesamt_riegel_carbs} g Carbs")

    # ════════════════════════════════════════════════════════════════════
    # KOFFEIN
    # ════════════════════════════════════════════════════════════════════
    _ko = e["koffein"]
    if _ko.get("caps", 0) > 0:
        lines += section_head("KOFFEIN-PLAN", "☕")
        lines += [
            kv("Kapseln gesamt", f"{_ko['caps']} Stk."),
            kv("Gesamt-Koffein", f"{_ko.get('gesamt_mg', 0)} mg"),
            kv("Pro kg KG", f"{_ko.get('mg_pro_kg', 0):.2f} mg/kg "
                            "(Ziel: 3–6 mg/kg laut ISSN)"),
        ]
        if _ko.get("cap_grund"):
            lines.append(kv("Sicherheits-Cap", _ko["cap_grund"]))
        lines.append("")
        lines.append("  Einnahme-Plan:")
        for t in _ko.get("timings", []):
            lines.append(f"    • {t['label']}")

    # ════════════════════════════════════════════════════════════════════
    # MIX-INTERVALLE
    # ════════════════════════════════════════════════════════════════════
    mix_iv = e.get("mix_intervalle")
    if mix_iv:
        lines += section_head("TRAININGS-INTERVALLE (MIX)", "🔀")
        total_min = sum(iv.get("dauer_min", 0) for iv in mix_iv)
        lines.append(f"  {'Zone':<5}  {'Dauer':>7}  {'Anteil':>7}  "
                     f"{'Carbs/h':>8}  {'Watt':>6}  {'HF':>6}")
        lines.append(f"  {'─' * 5}  {'─' * 7}  {'─' * 7}  "
                     f"{'─' * 8}  {'─' * 6}  {'─' * 6}")
        for iv in mix_iv:
            anteil = (f"{round(iv['dauer_min'] / total_min * 100)}%"
                      if total_min else "")
            watt = f"{iv['watt']} W" if iv.get("watt") else "—"
            hf = f"{iv['hf']} bpm" if iv.get("hf") else "—"
            lines.append(
                f"  {iv.get('zone', ''):<5}  "
                f"{iv.get('dauer_min', 0):>4} min  "
                f"{anteil:>7}  "
                f"{CARBS_PRO_STUNDE.get(iv.get('zone', 'Z2'), 60):>5} g/h  "
                f"{watt:>6}  {hf:>6}"
            )
        lines.append(f"\n  Gesamtdauer: {total_min} min  "
                     f"|  Gewichteter Schnitt: {e['carbs']['pro_h']} g/h")

    # ════════════════════════════════════════════════════════════════════
    # GPX-ROUTE
    # ════════════════════════════════════════════════════════════════════
    if gpx_data:
        lines += section_head("GPX-ROUTE", "🗺")
        lines += [
            kv("Streckenname", gpx_data.get("name", "—")),
            kv("Distanz", f"{gpx_data.get('distanz_km', 0):.1f} km"),
            kv("Höhenmeter ↑", f"{int(gpx_data.get('hoehenmeter_auf', 0))} m"),
            kv("Höhenmeter ↓", f"{int(gpx_data.get('hoehenmeter_ab', 0))} m"),
            kv("Anzahl Trackpunkte", f"{len(gpx_data.get('points', []))}"),
        ]

    # ════════════════════════════════════════════════════════════════════
    # RESUPPLY-STOPPS
    # ════════════════════════════════════════════════════════════════════
    if resupply_stopps:
        lines += section_head("RESUPPLY-STOPPS (Wasser & Carbs)", "📍")
        for i, stopp in enumerate(resupply_stopps):
            needs = []
            if stopp.get("braucht_wasser"): needs.append("Wasser")
            if stopp.get("braucht_carbs"):  needs.append("Carbs")
            lines.append(f"\n  ┌─ STOPP {i + 1}  •  km {stopp.get('km', '?')}  "
                         f"•  [{' + '.join(needs)}]")
            if stopp.get("lat"):
                lines.append(f"  │  Position         : "
                             f"{stopp['lat']:.5f}° N, {stopp['lon']:.5f}° E")
                lines.append(f"  │  Google Maps      : "
                             f"https://maps.google.com/?q={stopp['lat']:.5f},{stopp['lon']:.5f}")
            if stopp.get("braucht_wasser"):
                lines.append(f"  │  Wasser auffüllen : "
                             f"~{stopp.get('wasser_refill_ml', '?')} ml")
            if stopp.get("braucht_carbs"):
                einkauf = stopp.get("carbs_einkauf_g", 0)
                lines.append(f"  │  Carbs kaufen     : ~{einkauf} g")
                if einkauf:
                    lines.append(
                        f"  │     z.B. {math.ceil(einkauf / 35)} Riegel (à 35 g)  "
                        f"oder {round(einkauf / 25)} Bananen  "
                        f"oder {round(einkauf / 0.85):.0f} g Gummibärchen"
                    )
            pois = stopp.get("poi_ergebnisse", [])
            if pois:
                lines.append("  │  Einkaufsstationen:")
                for rank, p in enumerate(pois[:3]):
                    adresse = (
                        p.get("strasse", "")
                        + (f", {p['ort']}" if p.get("ort") else "")
                    ).strip(", ")
                    marker = "⭐" if rank == 0 else "  "
                    lines.append(
                        f"  │   {marker} {p['name']} ({p['typ']})  "
                        f"– km {p['route_km']}  – {p['dist_m']} m zur Route"
                    )
                    if adresse:
                        lines.append(f"  │       {adresse}")
            lines.append(f"  └{'─' * (WIDTH - 3)}")

    # ════════════════════════════════════════════════════════════════════
    # FOOTER
    # ════════════════════════════════════════════════════════════════════
    lines += [
        "",
        "═" * WIDTH,
        "",
        "  © 2024–2026 Felix Manasov. Alle Rechte vorbehalten.",
        "  Nutzung der App erlaubt. Kopieren/Weitergabe des Codes untersagt.",
        "",
        "  🔗 App:  https://fueling-planner.streamlit.app",
        "  📚 Doku: https://github.com/FeDaSy/fueling-planner/blob/main/BERECHNUNGEN_UND_APIS.txt",
        "  💬 Feedback: https://forms.gle/xrj1fAKduJtJYy5B7",
        "",
        "═" * WIDTH,
    ]
    return "\n".join(lines)


def erstelle_plan_pdf(e, wetter_info=None, wetter_punkte=None, resupply_stopps=None,
                      export_context=None):
    """
    Erstellt einen visuell ansprechenden PDF-Plan, der alle Daten der
    App-Ansicht enthält (Carbs, Wasser, Glykogen-Bilanz, Cardiac Drift,
    Softflasks, Riegel, Elektrolyte, Koffein, Mix-Intervalle, GPX, Wetter,
    Resupply-Stopps).
    """
    try:
        from fpdf import FPDF
        from fpdf.enums import XPos, YPos
    except ImportError:
        return b""

    ctx = export_context or {}
    profil = ctx.get("profil", {})
    ist_indoor = ctx.get("ist_indoor", False)
    ist_konstant = ctx.get("ist_konstant", False)
    konstant_g_h = ctx.get("konstant_g_h")
    bilanz = ctx.get("bilanz") or {}
    drift_rate = ctx.get("drift_rate", 0.0)
    start_voll_pct = ctx.get("start_voll_pct", 1.0)
    gpx_data = ctx.get("gpx_data")

    LM = 12         # left margin mm
    W = 186         # usable width mm
    LH = 5.5        # standard line height
    LH_TIGHT = 4.8  # compact line height

    # Color palette
    CLR_PRIMARY = (45, 90, 160)          # dark blue
    CLR_PRIMARY_LIGHT = (220, 232, 248)  # light blue background
    CLR_ACCENT = (220, 100, 50)          # orange accent
    CLR_TEXT = (40, 40, 40)              # near-black
    CLR_MUTED = (110, 110, 110)          # gray
    CLR_GREEN = (60, 150, 80)
    CLR_AMBER = (220, 165, 50)
    CLR_RED = (200, 70, 60)
    CLR_TABLE_HEAD = (50, 75, 130)
    CLR_TABLE_ALT = (245, 248, 252)
    CLR_BORDER = (200, 210, 225)

    sf_res = e.get("softflasks", {})
    wf = e.get("wasserflaschen", {})
    sonne_label = {"keine": "Bedeckt", "mittel": "Teils sonnig", "stark": "Vollsonne"}
    zone_namen = {
        "Z1": "Z1 (Erholung)", "Z2": "Z2 (Grundlage / Aerob)",
        "Z3": "Z3 (Tempo / Sweetspot)", "Z4": "Z4 (Schwelle)",
        "Z5": "Z5 (Maximalintensitaet)", "Mix": "Mix (gemischte Zonen)",
    }

    def _s(text):
        """Latin-1 sanitization for fpdf2 (no emojis/unicode in core fonts)."""
        t = str(text)
        replacements = [
            # Strip Markdown-Markup
            ("**", ""), ("*_", ""), ("_*", ""),
            # Typografische Zeichen
            ("–", "-"), ("—", "-"),
            ("'", "'"), ("'", "'"),
            (""", '"'), (""", '"'),
            ("≤", "<="), ("≥", ">="), ("→", "->"), ("←", "<-"),
            ("·", "-"), ("•", "*"),
            ("⭐", "*"), ("✓", "[OK]"), ("✅", "[OK]"), ("✗", "[X]"), ("❌", "[X]"),
            ("█", "#"), ("░", "."),
            ("≈", "~"), ("Ø", "O"),
            ("…", "..."), ("´", "'"), ("`", "'"),
            # Sektions-Emojis (entfernen)
            ("🍬", ""), ("💧", ""), ("🧬", ""), ("🍯", ""), ("🍫", ""),
            ("☕", ""), ("🌡", ""), ("⚡", ""), ("📍", ""), ("🚴", ""),
            ("🫀", ""), ("📈", ""), ("➡️", ""), ("➡", ""), ("🔀", ""),
            ("🗺", ""), ("🗺️", ""),
            ("ℹ️", ""), ("ℹ", ""), ("⚠️", "[!]"), ("⚠", "[!]"),
            ("📥", ""), ("📄", ""), ("📌", ""), ("📉", ""), ("📊", ""),
            ("💡", "[Tipp]"), ("⛔", "[STOPP]"),
            ("🟢", "[O]"), ("🟡", "[!]"), ("🟠", "[!]"), ("🔴", "[X]"),
            # ZWJ + Variations-Selektor (für Emoji-Kombinationen)
            ("‍", ""), ("️", ""),
        ]
        for src, dst in replacements:
            t = t.replace(src, dst)
        # Mehrfache Leerzeichen am Zeilen-Anfang entfernen (wenn Emoji weggefallen ist)
        return t.encode("latin-1", errors="replace").decode("latin-1")

    pdf = FPDF(orientation="P", unit="mm", format="A4")
    pdf.set_auto_page_break(auto=True, margin=18)
    pdf.set_margins(LM, LM, LM)
    pdf.add_page()

    # ── Helpers ──────────────────────────────────────────────────────────────
    def reset_color():
        pdf.set_text_color(*CLR_TEXT)
        pdf.set_draw_color(*CLR_BORDER)
        pdf.set_fill_color(255, 255, 255)

    def section_main(title, subtitle=None):
        """Big section header (used for top-level groups: Carbs, Wasser, …)."""
        pdf.ln(4)
        pdf.set_x(LM)
        pdf.set_fill_color(*CLR_PRIMARY)
        pdf.set_text_color(255, 255, 255)
        pdf.set_font("Helvetica", "B", 13)
        pdf.cell(W, 9, _s(title), new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True)
        if subtitle:
            pdf.set_x(LM)
            pdf.set_fill_color(*CLR_PRIMARY_LIGHT)
            pdf.set_text_color(*CLR_TEXT)
            pdf.set_font("Helvetica", "I", 9)
            pdf.cell(W, 5, _s(subtitle), new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True)
        reset_color()
        pdf.set_font("Helvetica", "", 10)
        pdf.ln(2)

    def subsection(title):
        """Smaller subsection label inside a main section."""
        pdf.ln(1)
        pdf.set_x(LM)
        pdf.set_text_color(*CLR_PRIMARY)
        pdf.set_font("Helvetica", "B", 10.5)
        pdf.cell(W, 6, _s(title), new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        # subtle underline
        pdf.set_draw_color(*CLR_BORDER)
        pdf.set_line_width(0.2)
        pdf.line(LM, pdf.get_y(), LM + W, pdf.get_y())
        pdf.ln(1)
        reset_color()
        pdf.set_font("Helvetica", "", 10)

    def kv(label, value, label_w=55):
        """Key-value row, label left-aligned bold, value to the right."""
        pdf.set_x(LM)
        pdf.set_font("Helvetica", "B", 9.5)
        pdf.cell(label_w, LH, _s(label),
                 new_x=XPos.RIGHT, new_y=YPos.TOP)
        pdf.set_font("Helvetica", "", 9.5)
        pdf.multi_cell(W - label_w, LH, _s(str(value)),
                       new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    def body(text, indent=0, italic=False):
        pdf.set_x(LM + indent)
        pdf.set_font("Helvetica", "I" if italic else "", 9.5)
        pdf.multi_cell(W - indent, LH, _s(text),
                       new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    def note(text, indent=4):
        pdf.set_x(LM + indent)
        pdf.set_font("Helvetica", "I", 8.5)
        pdf.set_text_color(*CLR_MUTED)
        pdf.multi_cell(W - indent, 4.3, _s(text),
                       new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        reset_color()
        pdf.set_font("Helvetica", "", 10)

    def colored_pill(text, color):
        """Small colored pill (e.g. status indicator)."""
        pdf.set_fill_color(*color)
        pdf.set_text_color(255, 255, 255)
        pdf.set_font("Helvetica", "B", 8.5)
        width = pdf.get_string_width(_s(text)) + 4
        pdf.cell(width, 4.5, _s(text), fill=True, align="C",
                 new_x=XPos.RIGHT, new_y=YPos.TOP)
        reset_color()

    def table_header(cols, widths):
        pdf.set_x(LM)
        pdf.set_fill_color(*CLR_TABLE_HEAD)
        pdf.set_text_color(255, 255, 255)
        pdf.set_font("Helvetica", "B", 8.5)
        for i, (col, w) in enumerate(zip(cols, widths)):
            last = (i == len(cols) - 1)
            pdf.cell(w, 6, _s(col), border=0, fill=True, align="C",
                     new_x=XPos.RIGHT if not last else XPos.LMARGIN,
                     new_y=YPos.TOP if not last else YPos.NEXT)
        reset_color()

    def table_row_alt(vals, widths, alt=False, font_size=8.5,
                      align="C", border_bottom=True):
        pdf.set_x(LM)
        if alt:
            pdf.set_fill_color(*CLR_TABLE_ALT)
            fill = True
        else:
            fill = False
        pdf.set_font("Helvetica", "", font_size)
        for i, (v, w) in enumerate(zip(vals, widths)):
            last = (i == len(vals) - 1)
            pdf.cell(w, 5.2, _s(str(v)), border=0, fill=fill, align=align,
                     new_x=XPos.RIGHT if not last else XPos.LMARGIN,
                     new_y=YPos.TOP if not last else YPos.NEXT)
        if border_bottom:
            pdf.set_draw_color(*CLR_BORDER)
            pdf.line(LM, pdf.get_y(), LM + W, pdf.get_y())

    def progress_bar(pct, width_mm=80, height_mm=3, color=None):
        """Draws a horizontal progress bar at current cursor."""
        x = pdf.get_x()
        y = pdf.get_y() + 1
        # Background
        pdf.set_fill_color(230, 230, 235)
        pdf.rect(x, y, width_mm, height_mm, "F")
        # Fill
        fill_w = max(0, min(width_mm, width_mm * pct))
        c = color or CLR_PRIMARY
        pdf.set_fill_color(*c)
        pdf.rect(x, y, fill_w, height_mm, "F")
        reset_color()

    def status_color_for_pct(pct):
        """Returns RGB color for a glycogen-rest percentage."""
        if pct >= 70:
            return CLR_GREEN
        elif pct >= 50:
            return CLR_AMBER
        elif pct >= 30:
            return (235, 130, 60)
        else:
            return CLR_RED

    # ════════════════════════════════════════════════════════════════════
    # TITELBLOCK
    # ════════════════════════════════════════════════════════════════════
    # Hauptband
    pdf.set_fill_color(*CLR_PRIMARY)
    pdf.rect(0, 0, 210, 22, "F")
    pdf.set_xy(LM, 6)
    pdf.set_text_color(255, 255, 255)
    pdf.set_font("Helvetica", "B", 20)
    pdf.cell(W, 10, "Cycling Fueling Plan",
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align="L")
    pdf.set_x(LM)
    pdf.set_font("Helvetica", "", 10)
    untertitel = (f"Profil: {e['profil_name']}  -  "
                  f"erstellt am {datetime.now().strftime('%d.%m.%Y, %H:%M')}")
    pdf.cell(W, 5, _s(untertitel),
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align="L")
    reset_color()
    pdf.set_y(28)

    # ── Übersichts-Kacheln ──
    pdf.set_x(LM)
    box_w = (W - 6) / 4
    box_h = 16
    eintraege = [
        ("Dauer", f"{e['dauer_h']} h"),
        ("Zone", e["zone"]),
        ("Temp.", f"{e['temp']}{chr(176)}C"),
        ("Carbs gesamt", f"{e['carbs']['gesamt']} g"),
    ]
    for i, (label, val) in enumerate(eintraege):
        x = LM + i * (box_w + 2)
        pdf.set_xy(x, 28)
        pdf.set_fill_color(*CLR_PRIMARY_LIGHT)
        pdf.rect(x, 28, box_w, box_h, "F")
        pdf.set_xy(x, 30)
        pdf.set_text_color(*CLR_MUTED)
        pdf.set_font("Helvetica", "", 8)
        pdf.cell(box_w, 4, _s(label), align="C",
                 new_x=XPos.LEFT, new_y=YPos.NEXT)
        pdf.set_x(x)
        pdf.set_text_color(*CLR_PRIMARY)
        pdf.set_font("Helvetica", "B", 14)
        pdf.cell(box_w, 8, _s(val), align="C",
                 new_x=XPos.LEFT, new_y=YPos.NEXT)
    reset_color()
    pdf.set_y(48)

    # ════════════════════════════════════════════════════════════════════
    # ÜBERSICHT
    # ════════════════════════════════════════════════════════════════════
    section_main("Uebersicht", "Trainingsplan-Stammdaten")
    kv("Trainingsmodus",
       "Indoor (Rolle / Heimtrainer)" if ist_indoor
       else "Outdoor (Strasse / Gelaende)")
    kv("Dauer", f"{e['dauer_h']} h")
    if not ist_indoor:
        if e.get("distanz_km"):
            kv("Distanz", f"{e['distanz_km']:.1f} km")
        if e.get("hoehenmeter"):
            kv("Hoehenmeter", f"{int(e['hoehenmeter'])} m")
    if profil.get("koerpergewicht_kg"):
        kv("Koerpergewicht", f"{profil['koerpergewicht_kg']} kg")

    # ── Trainingsintensität ──
    subsection("Trainingsintensitaet")
    if e.get("watt") and e.get("ftp"):
        pct_ftp = round(e["watt"] / e["ftp"] * 100, 1)
        watt_label = ("Leistung (Durchschnitt)" if ist_indoor
                      else "Leistung (Normalized Power)")
        kv(watt_label, f"{e['watt']:.0f} W")
        kv("FTP", f"{e['ftp']:.0f} W   ->  {pct_ftp}% FTP")
    elif e.get("hf") and e.get("hr_max"):
        pct_hrmax = round(e["hf"] / e["hr_max"] * 100, 1)
        kv("Herzfrequenz", f"{e['hf']:.0f} bpm")
        kv("HRmax", f"{e['hr_max']} bpm   ->  {pct_hrmax}% HRmax")
    kv("Zone", zone_namen.get(e["zone"], e["zone"]))
    kv("Quelle", e["carbs"]["quelle"])

    # ── Wetter ──
    if wetter_info and not ist_indoor:
        subsection("Wetterbedingungen")
        kv("Temperatur (Durchschn.)",
           f"{wetter_info['avg_temp']}{chr(176)}C  "
           f"(min {wetter_info['min_temp']} / max {wetter_info['max_temp']})")
        kv("Sonneneinstrahlung",
           sonne_label.get(wetter_info.get("sonne", ""),
                           wetter_info.get("sonne", "-")))
        kv("Wind (Durchschn.)", f"{wetter_info['avg_wind']} km/h")
        kv("Regen", f"{wetter_info['sum_regen']} mm")

        if wetter_punkte and len(wetter_punkte) > 1:
            pdf.ln(2)
            pdf.set_x(LM)
            pdf.set_font("Helvetica", "B", 9.5)
            pdf.cell(W, 5, _s("Wetterverlauf entlang der Route"),
                     new_x=XPos.LMARGIN, new_y=YPos.NEXT)
            cols = ["km", "Uhrzeit", "Latitude", "Longitude", "Temp", "Regen"]
            widths = [20, 25, 38, 38, 30, 35]
            table_header(cols, widths)
            for idx, pt in enumerate(wetter_punkte):
                table_row_alt([
                    str(pt.get("km", "")),
                    pt.get("uhrzeit", ""),
                    f"{pt.get('lat', 0):.4f}",
                    f"{pt.get('lon', 0):.4f}",
                    f"{pt.get('temp_avg', '')}{chr(176)}C",
                    f"{pt.get('regen_mm', '')} mm",
                ], widths, alt=(idx % 2 == 1))
    elif ist_indoor:
        subsection("Trainingsumgebung")
        kv("Raumtemperatur", f"{e['temp']}{chr(176)}C")

    # ════════════════════════════════════════════════════════════════════
    # KOHLENHYDRATE
    # ════════════════════════════════════════════════════════════════════
    strategie_label = (
        f"Konstant ({konstant_g_h} g/h jede Stunde)"
        if (ist_konstant and konstant_g_h is not None)
        else "Progressiv (steigt ueber die Zeit)"
    )
    section_main("Kohlenhydrate", f"Strategie: {strategie_label}")

    subsection("Gesamtbedarf")
    kv("Gesamt-Carbs", f"{e['carbs']['gesamt']} g")
    kv("Pro Stunde (Durchschn.)",
       f"{konstant_g_h} g/h" if (ist_konstant and konstant_g_h is not None)
       else f"{e['carbs']['pro_h_avg']} g/h")
    kv("Basis-Berechnung", f"{e['carbs']['basis']} g")
    if e["carbs"].get("hm_bonus"):
        kv("Hoehenmeter-Bonus", f"+{e['carbs']['hm_bonus']} g")

    subsection("Verteilung Gels & Riegel")
    gesamt = max(1, e["carbs"]["gesamt"])
    gels_pct = round(e["carbs"]["aus_gels"] / gesamt * 100)
    rieg_pct = round(e["carbs"]["aus_riegeln"] / gesamt * 100)
    kv("Aus Gels", f"{e['carbs']['aus_gels']} g  ({gels_pct}%)")
    kv("Aus Riegeln", f"{e['carbs']['aus_riegeln']} g  ({rieg_pct}%)")
    if sf_res.get("ratio_info"):
        kv("Glukose:Fructose", sf_res["ratio_info"][2])

    # Progressiver Stundenplan ODER Konstante Aufschlüsselung
    prog_txt = e["carbs"].get("progressiv", [])
    if ist_konstant and konstant_g_h is not None:
        subsection("Konstante Zufuhr pro Stunde")
        gesamt_k = round(konstant_g_h * e["dauer_h"])
        kv("Pro Stunde", f"{konstant_g_h} g")
        kv("Dauer", f"{e['dauer_h']} h")
        kv("Gesamt-Menge", f"{gesamt_k} g")
    elif prog_txt and len(prog_txt) > 1:
        subsection("Progressiver Stundenplan")
        # Spaltenbreiten: Stunde · g/h · Menge · Verlauf-Balken · %
        cols = ["Stunde", "g/h", "Menge", "Verlauf", "%"]
        widths = [38, 24, 24, 80, 20]
        # Summe = 186 = W ✓
        table_header(cols, widths)
        max_rate = max(s["carbs_g_h"] for s in prog_txt) or 1
        ROW_H = 6.0
        BAR_H = 2.8
        BAR_PAD = 4  # Innenabstand links/rechts in der Bar-Spalte
        for idx, s in enumerate(prog_txt):
            stunde_lbl = (f"{s['start_min']}-{s['end_min']} min"
                          if s["dauer_min"] < 60
                          else f"Stunde {s['stunde']}")
            row_y = pdf.get_y()
            alt = (idx % 2 == 1)

            # Alt-Row Hintergrund
            if alt:
                pdf.set_fill_color(*CLR_TABLE_ALT)
                pdf.rect(LM, row_y, W, ROW_H, "F")
                reset_color()

            # Spalten 1–3: Text (Stunde, g/h, Menge)
            pdf.set_xy(LM, row_y)
            pdf.set_font("Helvetica", "", 9)
            pdf.cell(widths[0], ROW_H, _s(stunde_lbl), align="C",
                     new_x=XPos.RIGHT, new_y=YPos.TOP)
            pdf.cell(widths[1], ROW_H, _s(f"{s['carbs_g_h']} g"), align="C",
                     new_x=XPos.RIGHT, new_y=YPos.TOP)
            pdf.cell(widths[2], ROW_H, _s(f"{s['carbs_g']} g"), align="C",
                     new_x=XPos.RIGHT, new_y=YPos.TOP)

            # Spalte 4: Progress-Bar (manuell mit korrekter X/Y-Position zeichnen)
            pct = s["carbs_g_h"] / max_rate
            bar_x_start = LM + widths[0] + widths[1] + widths[2] + BAR_PAD
            bar_width = widths[3] - 2 * BAR_PAD
            bar_y = row_y + (ROW_H - BAR_H) / 2
            # Hintergrund (hellgrau)
            pdf.set_fill_color(225, 228, 235)
            pdf.rect(bar_x_start, bar_y, bar_width, BAR_H, "F")
            # Füllung
            fill_w = max(0.5, min(bar_width, bar_width * pct))
            pdf.set_fill_color(*CLR_PRIMARY)
            pdf.rect(bar_x_start, bar_y, fill_w, BAR_H, "F")
            reset_color()

            # Spalte 5: Prozent-Text
            pdf.set_xy(LM + widths[0] + widths[1] + widths[2] + widths[3], row_y)
            pdf.set_font("Helvetica", "", 8.5)
            pdf.cell(widths[4], ROW_H, _s(f"{int(round(pct * 100))}%"),
                     align="C", new_x=XPos.LMARGIN, new_y=YPos.NEXT)

            # Untere Zeilen-Trennlinie
            pdf.set_draw_color(*CLR_BORDER)
            pdf.set_line_width(0.15)
            pdf.line(LM, row_y + ROW_H, LM + W, row_y + ROW_H)

        # Summe
        pdf.ln(1)
        pdf.set_x(LM)
        pdf.set_font("Helvetica", "B", 9.5)
        pdf.set_fill_color(*CLR_PRIMARY_LIGHT)
        pdf.cell(W, 6,
                 _s(f"   Summe: {sum(s['carbs_g'] for s in prog_txt)} g   |   "
                    f"Durchschnitt: {e['carbs']['pro_h_avg']} g/h"),
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True, align="L")
        reset_color()

    # ════════════════════════════════════════════════════════════════════
    # WASSER & ELEKTROLYTE
    # ════════════════════════════════════════════════════════════════════
    section_main("Wasser & Elektrolyte")

    subsection("Wassermenge")
    kv("Gesamt", f"{e['wasser']['gesamt']} ml  ({e['wasser']['pro_h']} ml/h)")
    kv("Aus Gels", f"{e['wasser']['aus_gels']} ml")
    kv("Aus Trinkflaschen", f"{e['wasser']['zusaetzlich']} ml")
    if profil.get("schweissrate", {}).get("preset"):
        preset = profil["schweissrate"]["preset"]
        preset_label = {"wenig": "Wenig-Schwitzer",
                        "mittel": "Mittel-Schwitzer",
                        "viel": "Viel-Schwitzer",
                        "kalibriert": "Kalibriert"}.get(preset, preset)
        kv("Schweisstyp", preset_label)
    if wf and wf.get("auffuellungen", 0) > 0:
        kv("Auffuellungen",
           f"{wf['auffuellungen']}x  (je ~{wf.get('refill_ml', 0)} ml)")

    subsection("Elektrolyte")
    el = e["elektrolyte"]
    kv("Produkt", el["name"])
    kv("Portion", f"{el['portion_g']} g")
    kv("Anzahl Portionen", f"{el['fuellungen']}x")
    kv("Gesamt", f"{el['gesamt_g']} g")
    minerals = el.get("mineralien", {})
    nicht_null = {m: v for m, v in minerals.items() if v}
    if nicht_null:
        pdf.ln(1)
        body("Mineralstoff-Gesamtmenge:", indent=2, italic=True)
        for m_name in ["natrium", "kalium", "chlorid", "calcium", "magnesium"]:
            if minerals.get(m_name):
                body(f"   * {m_name.capitalize()}: {minerals[m_name]} mg",
                     indent=4)

    # ════════════════════════════════════════════════════════════════════
    # GLYKOGEN-SPEICHERBILANZ
    # ════════════════════════════════════════════════════════════════════
    if bilanz:
        section_main("Glykogen-Speicherbilanz",
                     "Wie sich die Glykogenspeicher ueber die Dauer entwickeln")

        ts_label = {"untrained": "Untrainiert",
                    "trained": "Trainiert",
                    "trained_loaded": "Trainiert + Carbo-Loading",
                    "elite_loaded": "Elite + Loading"}.get(
                        bilanz.get("trainings_status", ""),
                        bilanz.get("trainings_status", "-"))

        subsection("Speicherstatus")
        kv("Koerpergewicht", f"{bilanz['koerpergewicht_kg']} kg")
        kv("Trainingsstatus", ts_label)
        kv("Glykogenkapazitaet", f"{bilanz['g_pro_kg']} g/kg")
        kv("Speicher voll", f"{bilanz['speicher_voll_g']} g")
        kv("Start-Fuellstand",
           f"{int(start_voll_pct * 100)}%  ({bilanz['speicher_start_g']} g)")
        kv("Verbrauch (echt)",
           f"{bilanz['verbrauch_eff_pro_h']:.0f} g/h "
           f"{'(steigt mit Drift)' if drift_rate > 0 else '(konstant)'}")

        # Endwert mit Status-Farbe
        end_pct = bilanz["speicher_end_pct"]
        status_clr = status_color_for_pct(end_pct)
        pdf.set_x(LM)
        pdf.set_font("Helvetica", "B", 9.5)
        pdf.cell(55, LH, "Speicher am Ende:", new_x=XPos.RIGHT, new_y=YPos.TOP)
        pdf.set_font("Helvetica", "", 9.5)
        pdf.cell(40, LH, _s(f"{end_pct:.0f}% ({bilanz['speicher_end_g']} g)"),
                 new_x=XPos.RIGHT, new_y=YPos.TOP)
        if end_pct >= 70:
            label = "Komfortabel"
        elif end_pct >= 50:
            label = "Eng kalkuliert"
        elif end_pct >= 30:
            label = "Kritisch"
        else:
            label = "Hungerast-Risiko"
        colored_pill(label, status_clr)
        pdf.ln(LH)

        # Cardiac Drift
        if drift_rate > 0:
            subsection("Cardiac Drift")
            verbrauch_basis = bilanz["verbrauch_eff_pro_h"]
            verbrauch_end = verbrauch_basis * (1 + drift_rate * (e["dauer_h"] - 1))
            kv("Drift-Rate", f"+{drift_rate*100:.1f}% pro Stunde")
            kv("Verbrauch Stunde 1", f"{verbrauch_basis:.0f} g/h")
            kv(f"Verbrauch Stunde {int(e['dauer_h'])}",
               f"{verbrauch_end:.0f} g/h")
            note("Quelle: Coyle & Gonzalez-Alonso 2001, Wingo et al. 2012. "
                 "Berechnet aus Temperatur, Indoor/Outdoor und Zonen-Intensitaet.",
                 indent=2)

        # Stündlicher Verlauf
        stunden = bilanz.get("stunden", [])
        if stunden:
            subsection("Stuendlicher Verlauf")
            cols = ["Stunde", "Verbrauch", "Zufuhr", "Aus Speicher",
                    "Speicher", "Rest %"]
            widths = [25, 33, 28, 34, 28, 38]
            table_header(cols, widths)
            for idx, s in enumerate(stunden):
                aus_sp = ("[OK] gedeckt" if s["gedeckt"]
                          else f"+{s['defizit_g']:.0f} g")
                table_row_alt([
                    f"{s['stunde_bis']:.1f} h",
                    f"{s['verbrauch_g']:.0f} g",
                    f"{s['zufuhr_g']:.0f} g",
                    aus_sp,
                    f"{s['speicher_rest_g']} g",
                    f"{s['speicher_rest_pct']:.0f}%",
                ], widths, alt=(idx % 2 == 1))

        # Empfehlungen
        empfehlungen = bilanz.get("empfehlungen", [])
        if empfehlungen:
            subsection("Empfehlungen")
            for emp in empfehlungen:
                clean = emp.replace("**", "")
                body(f"* {clean}", indent=2)

    # ════════════════════════════════════════════════════════════════════
    # SOFTFLASKS
    # ════════════════════════════════════════════════════════════════════
    sf_flaschen = sf_res.get("flaschen", [])
    if sf_flaschen or sf_res.get("anzahl", 0) > 0:
        section_main("Softflasks", "Selbstgemischte Carb-Gele")
        if sf_flaschen:
            for f in sf_flaschen:
                r = f.get("rezept", {})
                pdf.ln(1)
                pdf.set_x(LM)
                pdf.set_fill_color(*CLR_PRIMARY_LIGHT)
                pdf.set_font("Helvetica", "B", 10)
                pdf.cell(W, 6,
                         _s(f"   {f['anzahl']}x  {f['name']}  "
                            f"({f['volumen_ml']} ml)"),
                         new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True)
                reset_color()
                cols = ["Carbs", "Maltodextrin", "Fructose", "Salz", "Wasser"]
                widths = [37, 37, 37, 37, 38]
                table_header(cols, widths)
                table_row_alt([
                    f"{f['carbs_pro_flask']} g",
                    f"{r.get('maltodextrin', 0)} g",
                    f"{r.get('fructose', 0)} g",
                    f"{r.get('salz', 0)} g",
                    f"{r.get('wasser', 0)} ml",
                ], widths, alt=False, font_size=10)
        else:
            r0 = sf_res.get("rezept", {})
            kv("Anzahl", sf_res.get("anzahl", 0))
            kv("Carbs/Flask", f"{sf_res.get('carbs_pro_flask', 0)} g")
            kv("Maltodextrin", f"{r0.get('maltodextrin', 0)} g")
            kv("Fructose", f"{r0.get('fructose', 0)} g")
            kv("Salz", f"{r0.get('salz', 0)} g")
            kv("Wasser", f"{r0.get('wasser', 0)} ml")

    # ════════════════════════════════════════════════════════════════════
    # RIEGEL
    # ════════════════════════════════════════════════════════════════════
    if e.get("riegel"):
        section_main("Riegel & Snacks")
        cols = ["Anz.", "Name", "Carbs/Stk", "Carbs gesamt", "Zucker gesamt"]
        widths = [18, 78, 26, 30, 34]
        table_header(cols, widths)
        gesamt_anz, gesamt_carbs, gesamt_zucker = 0, 0, 0
        for idx, r in enumerate(e["riegel"]):
            table_row_alt([
                f"{r['anzahl']}x",
                r["name"],
                f"{r['carbs_g_pro_stueck']} g",
                f"{r['carbs_gesamt']} g",
                f"{r['zucker_gesamt']} g",
            ], widths, alt=(idx % 2 == 1), align="L"
               if False else "C")
            gesamt_anz += r["anzahl"]
            gesamt_carbs += r["carbs_gesamt"]
            gesamt_zucker += r["zucker_gesamt"]
        # Summenzeile
        pdf.ln(1)
        pdf.set_x(LM)
        pdf.set_font("Helvetica", "B", 9.5)
        pdf.set_fill_color(*CLR_PRIMARY_LIGHT)
        pdf.cell(W, 5.5,
                 _s(f"   GESAMT: {gesamt_anz} Riegel  |  "
                    f"{gesamt_carbs} g Carbs  |  {gesamt_zucker} g Zucker"),
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True)
        reset_color()

    # ════════════════════════════════════════════════════════════════════
    # KOFFEIN
    # ════════════════════════════════════════════════════════════════════
    _ko = e["koffein"]
    if _ko.get("caps", 0) > 0:
        section_main("Koffein-Plan",
                     "Dosierung nach ISSN 2021: 3 mg/kg + 1,5 mg/kg alle 2 h")
        kv("Kapseln gesamt", f"{_ko['caps']} Stueck")
        kv("Gesamt-Koffein", f"{_ko.get('gesamt_mg', 0)} mg")
        kv("Pro kg Koerpergewicht",
           f"{_ko.get('mg_pro_kg', 0):.2f} mg/kg  (Ziel: 3-6 mg/kg)")
        if _ko.get("cap_grund"):
            kv("Sicherheits-Cap", _ko["cap_grund"])

        # Einnahme-Plan
        pdf.ln(1)
        subsection("Einnahme-Plan")
        for t in _ko.get("timings", []):
            body(f"   * {t['label']}", indent=2)

    # ════════════════════════════════════════════════════════════════════
    # MIX-INTERVALLE
    # ════════════════════════════════════════════════════════════════════
    mix_iv = e.get("mix_intervalle")
    if mix_iv:
        section_main("Trainings-Intervalle (Mix)")
        total_min = sum(iv.get("dauer_min", 0) for iv in mix_iv)
        cols = ["Zone", "Dauer", "Anteil", "Carbs/h", "Watt", "HF"]
        widths = [24, 30, 26, 36, 35, 35]
        table_header(cols, widths)
        for idx, iv in enumerate(mix_iv):
            anteil = (f"{round(iv['dauer_min'] / total_min * 100)}%"
                      if total_min else "-")
            watt = f"{iv['watt']} W" if iv.get("watt") else "-"
            hf = f"{iv['hf']} bpm" if iv.get("hf") else "-"
            table_row_alt([
                iv.get("zone", ""),
                f"{iv.get('dauer_min', 0)} min",
                anteil,
                f"{CARBS_PRO_STUNDE.get(iv.get('zone', 'Z2'), 60)} g/h",
                watt, hf,
            ], widths, alt=(idx % 2 == 1))
        pdf.ln(1)
        body(f"Gesamtdauer: {total_min} min  |  "
             f"Gewichteter Schnitt: {e['carbs']['pro_h']} g/h",
             italic=True, indent=2)

    # ════════════════════════════════════════════════════════════════════
    # GPX-ROUTE
    # ════════════════════════════════════════════════════════════════════
    if gpx_data:
        section_main("GPX-Route")
        kv("Streckenname", gpx_data.get("name", "-"))
        kv("Distanz", f"{gpx_data.get('distanz_km', 0):.1f} km")
        kv("Hoehenmeter (aufwaerts)", f"{int(gpx_data.get('hoehenmeter_auf', 0))} m")
        kv("Hoehenmeter (abwaerts)", f"{int(gpx_data.get('hoehenmeter_ab', 0))} m")
        kv("Anzahl Trackpunkte", f"{len(gpx_data.get('points', []))}")

    # ════════════════════════════════════════════════════════════════════
    # RESUPPLY-STOPPS
    # ════════════════════════════════════════════════════════════════════
    if resupply_stopps:
        section_main("Resupply-Stopps",
                     "Wo Wasser auffuellen und Carbs nachkaufen")
        for i, stopp in enumerate(resupply_stopps):
            needs = []
            if stopp.get("braucht_wasser"): needs.append("Wasser")
            if stopp.get("braucht_carbs"):  needs.append("Carbs")
            pdf.ln(1)
            pdf.set_x(LM)
            pdf.set_fill_color(*CLR_ACCENT)
            pdf.set_text_color(255, 255, 255)
            pdf.set_font("Helvetica", "B", 10)
            pdf.cell(W, 6.5,
                     _s(f"   STOPP {i + 1}  -  km {stopp.get('km', '?')}  "
                        f"-  [{' + '.join(needs)}]"),
                     new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True)
            reset_color()
            pdf.set_font("Helvetica", "", 9.5)

            if stopp.get("lat"):
                kv("Position",
                   f"{stopp['lat']:.5f}{chr(176)} N, "
                   f"{stopp['lon']:.5f}{chr(176)} E", label_w=40)
                kv("Google Maps",
                   f"https://maps.google.com/?q={stopp['lat']:.5f},"
                   f"{stopp['lon']:.5f}", label_w=40)
            if stopp.get("braucht_wasser"):
                kv("Wasser auffuellen",
                   f"~{stopp.get('wasser_refill_ml', '?')} ml", label_w=40)
            if stopp.get("braucht_carbs"):
                einkauf = stopp.get("carbs_einkauf_g", 0)
                kv("Carbs kaufen", f"~{einkauf} g", label_w=40)
                if einkauf:
                    note(
                        f"z.B. {math.ceil(einkauf / 35)} Riegel (a 35 g)  |  "
                        f"{round(einkauf / 25)} Bananen  |  "
                        f"{round(einkauf / 0.85):.0f} g Gummibaerchen",
                        indent=4,
                    )
            pois = stopp.get("poi_ergebnisse", [])
            if pois:
                pdf.ln(0.5)
                body("Empfohlene Einkaufsstationen:", indent=2, italic=True)
                for rank, p in enumerate(pois[:4]):
                    adresse = (
                        p.get("strasse", "")
                        + (f", {p['ort']}" if p.get("ort") else "")
                    ).strip(", ")
                    marker = "  *" if rank == 0 else "   "
                    text = (f"{marker} {p['name']} ({p['typ']})  -  "
                            f"km {p['route_km']}  -  {p['dist_m']} m zur Route")
                    if adresse:
                        text += f"  -  {adresse}"
                    body(text, indent=4)
            pdf.ln(1)

    # ════════════════════════════════════════════════════════════════════
    # FOOTER auf jeder Seite
    # ════════════════════════════════════════════════════════════════════
    # Manuelle Footer-Zeile am Ende
    pdf.ln(8)
    pdf.set_draw_color(*CLR_BORDER)
    pdf.set_line_width(0.3)
    pdf.line(LM, pdf.get_y(), LM + W, pdf.get_y())
    pdf.ln(2)
    pdf.set_text_color(*CLR_MUTED)
    pdf.set_font("Helvetica", "", 8)
    pdf.set_x(LM)
    pdf.cell(W, 4,
             _s(f"Erstellt mit Cycling Fueling Planner  -  "
                f"{datetime.now().strftime('%d.%m.%Y %H:%M')}"),
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align="C")
    pdf.set_x(LM)
    pdf.cell(W, 4,
             _s("(c) 2024-2026 Felix Manasov. Alle Rechte vorbehalten. "
                "Nutzung der App erlaubt, Kopieren/Weitergabe des Codes untersagt."),
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align="C")
    pdf.set_x(LM)
    pdf.cell(W, 4,
             _s("App: https://fueling-planner.streamlit.app  |  "
                "Doku: github.com/FeDaSy/fueling-planner"),
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align="C")
    reset_color()

    return bytes(pdf.output())


# ═══════════════════════════════════════════════════════════════════════════════
# STREAMLIT APP
# ═══════════════════════════════════════════════════════════════════════════════

st.set_page_config(page_title="Cycling Fueling Planner", page_icon="🚴", layout="wide")

# Session-State initialisieren
if "profil" not in st.session_state:
    st.session_state.profil = copy.deepcopy(DEFAULT_PROFIL)

# ── localStorage: Profil beim ersten Aufruf aus Browser laden ──
# Hinweis: getItem() liefert beim ersten Aufruf evtl. None (Component muss erst
# laden); nach einem Rerun ist der Wert verfügbar. Wir versuchen daher mehrfach.
_PROFIL_STORAGE_KEY = "fueling_planner_profil_v1"
_localS = LocalStorage() if _LOCAL_STORAGE_OK else None
if _localS is not None and not st.session_state.get("_profil_storage_geladen"):
    try:
        gespeichert = _localS.getItem(_PROFIL_STORAGE_KEY)
        if gespeichert:
            try:
                profil_geladen = json.loads(gespeichert)
                st.session_state.profil = _merge_profil_mit_defaults(
                    profil_geladen, DEFAULT_PROFIL
                )
                st.session_state._profil_storage_geladen = True
            except (json.JSONDecodeError, TypeError):
                # Korrupte Daten — als geladen markieren, damit nichts überschrieben wird
                st.session_state._profil_storage_geladen = True
        else:
            # Noch nichts geladen oder leer — bis zu 3 Versuche zulassen
            attempts = st.session_state.get("_profil_storage_versuche", 0) + 1
            st.session_state._profil_storage_versuche = attempts
            if attempts >= 3:
                st.session_state._profil_storage_geladen = True
    except Exception:
        st.session_state._profil_storage_geladen = True  # Fehler stillschweigend

if "ergebnis" not in st.session_state:
    st.session_state.ergebnis = None
if "wetter_info" not in st.session_state:
    st.session_state.wetter_info = None
if "gpx_data" not in st.session_state:
    st.session_state.gpx_data = None
if "resupply_stopps" not in st.session_state:
    st.session_state.resupply_stopps = None
if "wetter_punkte" not in st.session_state:
    st.session_state.wetter_punkte = []
if "intensitaet_modus" not in st.session_state:
    st.session_state.intensitaet_modus = "Zone manuell wählen"
if "intervalle" not in st.session_state:
    st.session_state.intervalle = [{"zone": "Z2", "watt": None, "hf": None, "dauer_min": 60}]

# ══════════════════════════════════════════════════════════════════════════════
# ANALYTICS: GoatCounter (privacy-friendly, cookieless, einmal pro Session)
# ══════════════════════════════════════════════════════════════════════════════
# Dashboard: https://fueling-planner.goatcounter.com
# - Keine Cookies, kein User-Tracking, DSGVO-konform ohne Banner
# - Hit wird nur einmal pro Streamlit-Session gezählt (nicht bei jedem Rerun)
# - Lokale Entwicklung (localhost) wird ausgeschlossen
GOATCOUNTER_ENDPOINT = "https://fueling-planner.goatcounter.com/count"
if "_gc_tracked" not in st.session_state:
    st.session_state._gc_tracked = True
    try:
        import streamlit.components.v1 as _gc_components
        _gc_components.html(
            f"""
            <script>
            (function() {{
                try {{
                    // Nur auf produzierter Domain tracken (nicht localhost / 127.0.0.1)
                    var host = '';
                    try {{ host = window.parent.location.hostname; }} catch(e) {{ host = window.location.hostname; }}
                    if (host.indexOf('localhost') !== -1 || host.indexOf('127.0.0.1') !== -1) {{
                        return;  // Skip tracking in local dev
                    }}
                    // Pfad & Titel manuell setzen (Iframe-URL ist nicht aussagekräftig)
                    var parentPath = '/';
                    try {{ parentPath = window.parent.location.pathname || '/'; }} catch(e) {{}}
                    var parentRef = '';
                    try {{ parentRef = window.parent.document.referrer || ''; }} catch(e) {{}}
                    var img = new Image();
                    img.src = '{GOATCOUNTER_ENDPOINT}'
                        + '?p=' + encodeURIComponent(parentPath)
                        + '&t=' + encodeURIComponent('Cycling Fueling Planner')
                        + '&r=' + encodeURIComponent(parentRef)
                        + '&rnd=' + Math.random();  // Cache-Busting
                }} catch (err) {{
                    // Tracking-Fehler ignorieren – darf die App nie blockieren
                }}
            }})();
            </script>
            """,
            height=0, width=0,
        )
    except Exception:
        pass  # Sollte das Component fehlen: App läuft trotzdem weiter

profil = st.session_state.profil

# ══════════════════════════════════════════════════════════════════════════════
# SIDEBAR – PROFIL EINSTELLUNGEN
# ══════════════════════════════════════════════════════════════════════════════

with st.sidebar:
    st.title("⚙️ Mein Profil")

    # ── Profil speichern / laden ──
    with st.expander("💾 Profil speichern & laden", expanded=False):
        if _LOCAL_STORAGE_OK:
            st.success(
                "✅ **Auto-Save aktiv:** Dein Profil wird automatisch in "
                "deinem Browser gespeichert und beim nächsten Besuch geladen. "
                "Funktioniert ohne Login, nur in **diesem Browser auf diesem Gerät**."
            )
        else:
            st.warning(
                "⚠️ Auto-Save derzeit nicht verfügbar (Komponente fehlt). "
                "Bitte unten manuell speichern/laden."
            )

        st.markdown("**Manuelles Backup / Geräteübertragung:**")
        st.caption(
            "Lade dein Profil als JSON-Datei herunter, um es als Backup zu sichern "
            "oder auf einem anderen Gerät / in einem anderen Browser zu nutzen."
        )

        # Export
        try:
            profil_json_export = json.dumps(profil, indent=2, ensure_ascii=False)
            sichere_dateiname = (
                "".join(c if c.isalnum() or c in "-_" else "_"
                        for c in profil.get("name", "profil"))
                or "profil"
            )
            st.download_button(
                "📥 Profil als .json herunterladen",
                data=profil_json_export,
                file_name=f"fueling_profile_{sichere_dateiname}.json",
                mime="application/json",
                use_container_width=True,
                key="profil_export_btn",
            )
        except Exception as ex:
            st.error(f"Export-Fehler: {ex}")

        # Import
        upload = st.file_uploader(
            "📤 Profil aus .json laden",
            type=["json"],
            key="profil_upload",
            help="Lade eine zuvor exportierte Profildatei hoch. "
                 "Fehlende Felder werden automatisch mit Standardwerten ergänzt.",
        )
        if upload is not None:
            try:
                geladen_raw = json.loads(upload.read().decode("utf-8"))
                st.session_state.profil = _merge_profil_mit_defaults(
                    geladen_raw, DEFAULT_PROFIL
                )
                # Storage-Flag zurücksetzen, damit der neue Stand vom Auto-Save
                # am Ende der Sidebar ins localStorage geschrieben wird
                st.session_state.pop("_profil_last_saved", None)
                st.success(
                    f"✅ Profil '{geladen_raw.get('name', 'Unbenannt')}' geladen."
                )
                st.rerun()
            except json.JSONDecodeError:
                st.error("Die Datei ist keine gültige JSON-Datei.")
            except Exception as ex:
                st.error(f"Fehler beim Laden: {ex}")

        # Reset
        st.markdown("---")
        if st.button("🗑️ Auf Standardwerte zurücksetzen",
                     use_container_width=True,
                     help="Setzt alle Profil-Einstellungen auf die Werkseinstellung zurück."):
            st.session_state.profil = copy.deepcopy(DEFAULT_PROFIL)
            if _localS is not None:
                try:
                    _localS.deleteItem(_PROFIL_STORAGE_KEY,
                                       key="profil_reset_delete")
                except Exception:
                    pass
            st.success("Profil zurückgesetzt.")
            st.rerun()

    st.markdown("---")

    # ── Feedback ──
    st.markdown("### 💬 Feedback & Support")
    st.markdown(
        "Fehler entdeckt, Frage oder Verbesserungsidee?\n\n"
        "[![Feedback geben](https://img.shields.io/badge/Feedback%20geben-%E2%86%92-blue?style=for-the-badge)]"
        "(https://forms.gle/xrj1fAKduJtJYy5B7)"
    )
    st.markdown("---")

    # ── Name ──
    profil["name"] = st.text_input("Name", value=profil["name"])

    # ── FTP ──
    profil["ftp_watt"] = st.number_input(
        "FTP (Watt)",
        min_value=50, max_value=600,
        value=int(profil["ftp_watt"]), step=5,
        help="Functional Threshold Power – deine Schwellenleistung in Watt. "
             "Wenn du keinen Leistungsmesser hast, lass den Standardwert (270 W)."
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

    # ── Geschlecht & Alter ──
    cols = st.columns(2)
    profil["geschlecht"] = cols[0].selectbox(
        "Geschlecht",
        ["Männlich", "Weiblich"],
        index=0 if profil.get("geschlecht", "Männlich") == "Männlich" else 1,
        help=(
            "Biologisches Geschlecht – beeinflusst die Schweißrate und Elektrolytverluste.\n\n"
            "Frauen schwitzen im Schnitt ca. 8% weniger (in ml/h) als Männer gleicher "
            "Fitness und Körpergröße. Das beeinflusst die berechnete Trinkmenge und "
            "den Natriumverlust. Kohlenhydrate und Koffein werden nicht angepasst – "
            "hier sind die Unterschiede zu gering für die Praxis (<5%)."
        ),
    )
    profil["alter"] = cols[1].number_input(
        "Alter (Jahre)",
        min_value=15, max_value=90,
        value=int(profil.get("alter", 30)), step=1,
        help=(
            "Dein Alter in Jahren. Ab 50 Jahren nimmt die Schweißdrüsenaktivität "
            "messbar ab (50–59: ca. –8%, ab 60: ca. –13% Schweißrate). "
            "Trainierte Masters-Athleten sind weniger betroffen – bei Unsicherheit "
            "den Schweißtyp (wenig/mittel/viel) manuell anpassen."
        ),
    )

    # ── Körpergewicht & Trainingsstatus (für Glykogen-Bilanz & Koffein) ──
    cols_kg = st.columns(2)
    profil["koerpergewicht_kg"] = cols_kg[0].number_input(
        "Körpergewicht (kg)",
        min_value=40, max_value=150,
        value=int(profil.get("koerpergewicht_kg", 75)), step=1,
        help=(
            "Dein Körpergewicht in kg. Wird verwendet für:\n\n"
            "• **Glykogen-Speicherbilanz**: 6–13 g Glykogen pro kg, "
            "je nach Trainingsstatus (Muskel + Leber)\n\n"
            "• **Koffein-Plan**: körpergewichtsbasierte Dosierung "
            "nach ISSN-Empfehlung (3 mg/kg Initial-Dosis + "
            "1,5 mg/kg Erhaltung alle 2 h)\n\n"
            "Hat KEINEN Einfluss auf Schweißrate oder Kohlenhydratbedarf "
            "(die werden über FTP/Zone bzw. Schweißtyp individuell skaliert)."
        ),
    )
    trainings_optionen = {
        "untrained": "Untrainiert (Hobby, <3h/Woche)",
        "trained": "Trainiert (Standard)",
        "trained_loaded": "Trainiert + Carbo-Loading (2–3 Tage geladen)",
        "elite_loaded": "Elite + Loading",
    }
    aktueller_status = profil.get("trainings_status", "trained")
    if aktueller_status not in trainings_optionen:
        aktueller_status = "trained"
    profil["trainings_status"] = cols_kg[1].selectbox(
        "Trainingsstatus (Glykogenspeicher)",
        list(trainings_optionen.keys()),
        index=list(trainings_optionen.keys()).index(aktueller_status),
        format_func=lambda k: trainings_optionen[k],
        help=(
            "Bestimmt die Größe deines Glykogenspeichers (g pro kg Körpergewicht):\n\n"
            "**Männer / Frauen:**\n"
            "• Untrainiert: 6.0 / 5.3 g/kg\n"
            "• Trainiert: 8.0 / 7.0 g/kg\n"
            "• Trainiert + geladen: 11.0 / 9.0 g/kg\n"
            "• Elite + geladen: 13.0 / 10.5 g/kg\n\n"
            "Frauen haben bei gleichem Gewicht ~12% weniger Muskelmasse "
            "(geringere fettfreie Masse) und damit weniger absolute Glykogenkapazität. "
            "Beim Carbo-Loading ist die Response zusätzlich gedämpft (20–30% vs. "
            "40–50% Steigerung bei Männern), außer der KH-Anteil liegt sehr hoch "
            "(>8 g/kg/Tag). Daher konservative Loading-Werte für Frauen.\n\n"
            "Quellen: Jeukendrup & Gleeson (2010), Burke (2015), "
            "Tarnopolsky et al. (2007), James et al. (2001)."
        ),
    )

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

    # ── Softflasks / Energiegels ──
    st.subheader("🧴 Softflasks / Energiegels")
    st.caption(
        "Gib an, welche Softflasks du dabei hast und wie viele Stück von jeder Größe. "
        "Das Gel-Rezept wird automatisch proportional zum Volumen berechnet."
    )
    sf = profil["softflask"]
    # Migration: altes Format ohne Flaschen-Liste
    if "flaschen" not in sf:
        sf["flaschen"] = [{"name": "Softflask", "volumen_ml": sf.pop("volumen_ml", 450),
                           "anzahl": sf.pop("max_anzahl", 2)}]

    sf_zu_loeschen = None
    for i, f in enumerate(sf["flaschen"]):
        label = f"{f.get('name', 'Softflask')}  ({f.get('volumen_ml', 0)} ml × {f.get('anzahl', 0)})"
        with st.expander(label, expanded=True):
            f["name"] = st.text_input("Bezeichnung", value=f.get("name", "Softflask"),
                                      key=f"sf_name_{i}")
            cols = st.columns(2)
            f["anzahl"] = cols[0].number_input(
                "Anzahl (Stück)", min_value=0, max_value=20,
                value=int(f.get("anzahl", 1)), step=1, key=f"sf_anz_{i}",
                help="Wie viele Softflasks dieser Größe nimmst du mit?"
            )
            f["volumen_ml"] = cols[1].number_input(
                "Volumen (ml)", min_value=50, max_value=2000,
                value=int(f.get("volumen_ml", 450)), step=50, key=f"sf_vol_{i}",
                help="Fassungsvermögen der Softflask in ml"
            )
            if f.get("anzahl", 0) > 0:
                st.caption(f"→ {f['anzahl']} × {f['volumen_ml']} ml = "
                           f"**{f['anzahl'] * f['volumen_ml']} ml** Gel-Kapazität")
            if st.button("🗑️ Entfernen", key=f"sf_del_{i}"):
                sf_zu_loeschen = i

    if sf_zu_loeschen is not None and len(sf["flaschen"]) > 1:
        sf["flaschen"].pop(sf_zu_loeschen)
        st.rerun()

    c1, c2 = st.columns(2)
    if c1.button("➕ Softflask hinzufügen", use_container_width=True):
        sf["flaschen"].append({"name": f"Softflask {len(sf['flaschen'])+1}",
                               "volumen_ml": 250, "anzahl": 1})
        st.rerun()

    # Zusammenfassung
    _aktive_sf = [f for f in sf["flaschen"] if f.get("anzahl", 0) > 0]
    if _aktive_sf:
        _total_sf_vol = sum(f["volumen_ml"] * f["anzahl"] for f in _aktive_sf)
        _total_sf_anz = sum(f["anzahl"] for f in _aktive_sf)
        st.caption(f"📦 Gesamt: **{_total_sf_anz} Softflasks** · **{_total_sf_vol} ml** Gel-Kapazität")

    # Gel-Rezept-Einstellungen
    with st.expander("⚗️ Gel-Rezept Einstellungen", expanded=False):
        sf["gel_anteil_pct"] = st.slider(
            "Gel-Anteil der Carbs (%)", 0, 100, int(sf["gel_anteil_pct"]), step=5,
            help="Wie viel Prozent der gesamten Kohlenhydrate aus den Softflasks kommen. "
                 "Der Rest kommt aus Riegeln."
        )
        st.caption(
            "Das Maltodextrin:Fructose-Verhältnis wird automatisch nach der Carb-Rate angepasst "
            "(wissenschaftlich optimiert, z.B. 2:1 bei 60–80 g/h). "
            "Hier manuell überschreiben falls gewünscht:"
        )
        cols = st.columns(2)
        sf["malto_ratio"] = cols[0].number_input(
            "Malto-Anteil", 1, 10, int(sf["malto_ratio"]), key="sf_malto",
            help="Verhältnisteil Maltodextrin (Standard: 2)"
        )
        sf["fructose_ratio"] = cols[1].number_input(
            "Fructose-Anteil", 0, 10, int(sf["fructose_ratio"]), key="sf_fructose",
            help="Verhältnisteil Fructose (Standard: 1)"
        )
        cols2 = st.columns(3)
        sf["salz_normal_g"] = cols2[0].number_input(
            "Salz normal (g)", 0.0, 5.0, float(sf["salz_normal_g"]), step=0.1, key="sf_salz_n"
        )
        sf["salz_heiss_g"] = cols2[1].number_input(
            "Salz Hitze (g)", 0.0, 5.0, float(sf["salz_heiss_g"]), step=0.1, key="sf_salz_h"
        )
        sf["temp_heiss_grad"] = cols2[2].number_input(
            "Hitze ab (°C)", 10, 40, int(sf["temp_heiss_grad"]), key="sf_temp",
            help="Ab dieser Temperatur mehr Salz ins Gel"
        )

    st.divider()

    # ── Riegel & Snacks ──
    st.subheader("🍫 Riegel & Snacks")
    st.caption(
        "Trage hier ein, welche Riegel du dabei hast und wie viele Stück du davon mitimmst. "
        "Aus der Gesamtmenge berechnet der Planner, ob du unterwegs Nachschub kaufen musst."
    )
    riegel_zu_loeschen = None
    for i, r in enumerate(profil["riegel"]):
        anz = r.get("anzahl", 1)
        label = f"{'✅' if r['aktiv'] else '❌'} {r['name']}  ×{anz}" if r["aktiv"] else f"❌ {r['name']} (inaktiv)"
        with st.expander(label, expanded=False):
            r["aktiv"] = st.checkbox("Aktiv (einplanen)", value=r["aktiv"], key=f"r_aktiv_{i}")
            r["name"] = st.text_input("Name", value=r["name"], key=f"r_name_{i}")
            cols = st.columns(3)
            r["anzahl"] = cols[0].number_input(
                "Anzahl (Stück)", min_value=0, max_value=50,
                value=int(r.get("anzahl", 1)), step=1, key=f"r_anz_{i}",
                help="Wie viele Stück dieses Riegels nimmst du mit?"
            )
            r["carbs_g"] = cols[1].number_input(
                "Carbs/Stk (g)", 0, 150, r["carbs_g"], key=f"r_carbs_{i}",
                help="Kohlenhydrate pro Riegel laut Nährwerttabelle"
            )
            r["zucker_g"] = cols[2].number_input(
                "Zucker/Stk (g)", 0, 150, r.get("zucker_g", 0), key=f"r_zucker_{i}",
                help="Zuckeranteil (steht unter 'davon Zucker')"
            )
            if r["aktiv"] and r.get("anzahl", 0) > 0:
                st.caption(f"→ {r['anzahl']} × {r['carbs_g']} g = **{r['anzahl'] * r['carbs_g']} g Carbs** mitgenommen")
            if st.button("🗑️ Entfernen", key=f"r_del_{i}"):
                riegel_zu_loeschen = i

    if riegel_zu_loeschen is not None:
        profil["riegel"].pop(riegel_zu_loeschen)
        st.rerun()

    if st.button("➕ Riegel / Snack hinzufügen", use_container_width=True):
        profil["riegel"].append({
            "name": f"Neuer Riegel {len(profil['riegel'])+1}",
            "carbs_g": 35, "zucker_g": 10, "gewicht_g": 45, "anzahl": 2, "aktiv": True,
        })
        st.rerun()

    # Zusammenfassung aller aktiven Riegel
    aktive_r = [r for r in profil["riegel"] if r["aktiv"] and r.get("anzahl", 0) > 0]
    if aktive_r:
        total_stueck = sum(r.get("anzahl", 0) for r in aktive_r)
        total_carbs_r = sum(r.get("anzahl", 0) * r["carbs_g"] for r in aktive_r)
        st.caption(f"📦 Mitgenommen gesamt: **{total_stueck} Stück** → **{total_carbs_r} g Carbs** aus Riegeln")

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


# ── Auto-Save: Profil in localStorage schreiben, wenn sich etwas geändert hat ──
# Wir vergleichen einen serialisierten Snapshot, um unnötige setItem-Aufrufe
# (und damit unnötige Reruns durch den localStorage-Component) zu vermeiden.
if _localS is not None:
    try:
        profil_snapshot = json.dumps(st.session_state.profil, sort_keys=True,
                                     ensure_ascii=False)
        if st.session_state.get("_profil_last_saved") != profil_snapshot:
            _localS.setItem(_PROFIL_STORAGE_KEY, profil_snapshot,
                            key="profil_auto_save")
            st.session_state._profil_last_saved = profil_snapshot
    except Exception:
        pass  # Fail silently — sonst wirft die App bei jedem Rerun


# ══════════════════════════════════════════════════════════════════════════════
# HAUPTBEREICH
# ══════════════════════════════════════════════════════════════════════════════

st.title("🚴 Cycling Fueling Planner")
st.caption("Berechne deinen persönlichen Ernährungs- und Trinkplan für die nächste Ausfahrt.")
st.caption("© 2024–2025 Felix Manasov · Alle Rechte vorbehalten")
with st.expander("📄 Nutzungsbedingungen & Lizenz"):
    st.markdown("""
**NUTZUNGSRECHT (ERLAUBT)**
Die öffentlich zugängliche Web-Applikation darf kostenlos und ohne Registrierung für
persönliche, nicht-kommerzielle Zwecke genutzt werden. Das Aufrufen der App-URL,
das Eingeben von Trainingsdaten und das Herunterladen der generierten Pläne (PDF, TXT)
ist ausdrücklich erlaubt.

**URHEBERRECHTSSCHUTZ**
Der Quellcode dieser Software ist urheberrechtlich geschützt.
Die Sichtbarkeit des Codes im GitHub-Repository dient ausschließlich dem technischen
Deployment auf der Streamlit Community Cloud und stellt keine Lizenzierung zur Nutzung,
Kopie oder Modifikation des Codes dar.

**VERBOTENE HANDLUNGEN** *(ohne schriftliche Genehmigung)*
- Kopieren, Reproduzieren oder Vervielfältigen des Quellcodes (ganz oder in Teilen)
- Modifizieren, Anpassen oder Erstellen abgeleiteter Werke auf Basis dieses Codes
- Weitergabe, Veröffentlichung oder Verkauf des Codes an Dritte
- Kommerzielle Nutzung des Codes, der generierten Inhalte oder der Berechnungslogik
- Entfernen oder Verändern dieses Urheberrechtsvermerks

**KEINE GARANTIE**
Die Software wird "wie besehen" (AS IS) bereitgestellt, ohne Garantie jeglicher Art.
Die berechneten Ernährungs- und Trinkempfehlungen ersetzen keine professionelle
sportmedizinische Beratung.

**DATENSCHUTZ & ANALYSE**
Diese App nutzt **GoatCounter** für anonyme Aufrufstatistiken — **keine Cookies,
keine IP-Speicherung, keine personenbezogenen Daten**. Erfasst werden ausschließlich
aggregierte Werte (Seitenaufrufe, Browser, Land). Das Profil wird lokal im
Browser-Speicher (`localStorage`) gespeichert und verlässt das Gerät nicht.
Mehr Infos: [goatcounter.com/help/gdpr](https://www.goatcounter.com/help/gdpr).

**Geltendes Recht:** Deutsches Recht (UrhG) und EU-Urheberrecht.

**Lizenzanfragen:** [GitHub Issues](https://github.com/FeDaSy/fueling-planner/issues)

---
*Cycling Fueling Planner – © 2024–2025 Felix Manasov – Alle Rechte vorbehalten*
""")

# ── Trainingsmodus ────────────────────────────────────────────────────────────
st.subheader("1. Trainingsmodus")
trainings_modus = st.radio(
    "Wo trainierst du?",
    ["🚴 Outdoor (Straße / Gelände)", "🏠 Indoor (Rolle / Heimtrainer)"],
    horizontal=True,
    help="Im Indoor-Modus entfallen Route, Wetter und Frühstart – du gibst nur die Dauer an."
)
ist_indoor = trainings_modus.startswith("🏠")

st.divider()

# ── GPX-Upload – nur Outdoor ──────────────────────────────────────────────────
gpx_data = None

if not ist_indoor:
    st.subheader("2. Route")
    route_modus = st.radio(
        "Wie möchtest du deine Route eingeben?",
        ["Ohne GPX – Werte manuell eingeben", "GPX-Datei hochladen (von Komoot, Strava, Garmin …)"],
        horizontal=False,
    )

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
else:
    st.session_state.gpx_data = None
    st.info("🏠 **Indoor-Modus:** Gib unten nur die Trainingsdauer ein – Wetter, Route und Frühstart werden automatisch ausgeblendet.")

# ══════════════════════════════════════════════════════════════════════════════
# 2. TRAININGSINTENSITÄT – außerhalb des Formulars (Mix-Builder braucht Buttons)
# ══════════════════════════════════════════════════════════════════════════════

st.subheader("3. Trainingsintensität" if not ist_indoor else "2. Trainingsintensität")

intensitaet_optionen = ["Zone manuell wählen", "Nach Wattleistung", "Nach Herzfrequenz"]
if not profil["hr_max"]:
    intensitaet_optionen = intensitaet_optionen[:2]
    st.caption("💡 *Herzfrequenz-Option: HRmax im Profil (links) eintragen, um diese Option freizuschalten.*")

intensitaet_modus = st.radio(
    "Intensitätsmodus", intensitaet_optionen, horizontal=True,
    index=intensitaet_optionen.index(st.session_state.intensitaet_modus)
    if st.session_state.intensitaet_modus in intensitaet_optionen else 0,
    key="intensitaet_radio"
)
st.session_state.intensitaet_modus = intensitaet_modus

zone = "Z2"
watt_eingabe = None
hf_eingabe = None

ZONE_LABELS = {
    "Z1": "Z1 – Erholung (30 g/h)",
    "Z2": "Z2 – Grundlage/Aerob (60 g/h)",
    "Z3": "Z3 – Tempo/Sweetspot (75 g/h)",
    "Z4": "Z4 – Schwelle (90 g/h)",
    "Z5": "Z5 – Maximalintensität (90 g/h)",
}

if intensitaet_modus == "Zone manuell wählen":
    zone_optionen_full = {**ZONE_LABELS, "Mix": "Mix – Intervalltraining (Zonen detailliert eingeben)"}
    zone_raw = st.selectbox(
        "Trainingszone", list(zone_optionen_full.keys()),
        index=1, format_func=lambda x: zone_optionen_full[x]
    )
    if profil["hr_max"]:
        hr = profil["hr_max"]
        st.caption(
            f"**Deine HF-Zonen** bei HRmax {hr} bpm: "
            f"Z1 < {round(hr*0.60)} | Z2 {round(hr*0.60)}–{round(hr*0.70)} | "
            f"Z3 {round(hr*0.70)}–{round(hr*0.80)} | Z4 {round(hr*0.80)}–{round(hr*0.90)} | "
            f"Z5 > {round(hr*0.90)} bpm"
        )
    if zone_raw == "Mix":
        zone = "Mix"
    else:
        zone = zone_raw

elif intensitaet_modus == "Nach Wattleistung":
    st.caption(f"FTP aus Profil: **{profil['ftp_watt']} W** – Carbs werden physikalisch aus der Leistung berechnet.")
    # Einfach-Watt oder Mix?
    watt_modus = st.radio("Watt-Eingabe", ["Einzelne Leistung", "Mix – mehrere Intervalle"], horizontal=True)
    if watt_modus == "Einzelne Leistung":
        if ist_indoor:
            watt_label = "Watt (Durchschnittsleistung)"
            watt_help = (
                "Beim Indoor-Training auf der Rolle ist die Leistung konstant oder sehr gleichmäßig "
                "(ERG-Modus) – Average Power und Normalized Power (NP) sind nahezu identisch.\n\n"
                "Trage einfach die **Durchschnittsleistung** ein, die dein Rollentrainer oder "
                "deine Trainingsapp (Zwift, RGT, Wahoo, Garmin) anzeigt."
            )
        else:
            watt_label = "Normalized Power / NP (Watt) – empfohlen"
            watt_help = (
                "**Normalized Power (NP) eingeben, nicht Average Power!**\n\n"
                "NP berücksichtigt die Intensitätsvariabilität deiner Fahrt und "
                "bildet den tatsächlichen Stoffwechselaufwand deutlich präziser ab.\n\n"
                "**Warum NP?**\n"
                "Average Power wird durch Ausrollphasen, Abfahrten und Ampelstopps "
                "nach unten verzerrt – der Körper verbrennt aber in harten Intervallen "
                "überproportional mehr Kohlenhydrate. NP gleicht das aus.\n\n"
                "**Wo finde ich NP?**\n"
                "• Garmin Connect: 'Gewichtete Leistung' in der Aktivitätsübersicht\n"
                "• Strava: 'Normalisierte Leistung' (nur mit Leistungsmesser)\n"
                "• Wahoo / TrainingPeaks: direkt als 'NP' oder 'Normalized Power' angegeben\n\n"
                "**Faustregel:** NP liegt bei typischen Ausfahrten 5–15% über der "
                "Average Power. Je variabler die Strecke (Hügel, Stopps, Sprints), "
                "desto größer der Unterschied."
            )
        watt_eingabe = st.number_input(
            watt_label, 50, 600,
            value=max(50, profil["ftp_watt"] - 30), step=5, key="watt_einzel",
            help=watt_help
        )
        zone = watts_zu_zone(watt_eingabe, profil["ftp_watt"])
        pct_ftp = round(watt_eingabe / profil["ftp_watt"] * 100)
        watt_label_kurz = "W" if ist_indoor else "W NP"
        st.caption(f"→ **{watt_eingabe} {watt_label_kurz}** = {pct_ftp}% FTP → Zone **{zone}**")
        if not ist_indoor and watt_eingabe == max(50, profil["ftp_watt"] - 30):
            st.info(
                "💡 **Tipp:** Trage deine **Normalized Power (NP)** ein, nicht die Average Power. "
                "NP findest du in Garmin Connect als *'Gewichtete Leistung'* oder in Strava als "
                "*'Normalisierte Leistung'*. Bei gemischten Fahrten liegt NP typisch 5–15 % über "
                "dem Durchschnitt und ergibt genauere Carb-Werte."
            )
    else:
        zone = "Mix"

elif intensitaet_modus == "Nach Herzfrequenz":
    hr = profil["hr_max"]
    st.caption(
        f"HRmax aus Profil: **{hr} bpm** | "
        f"Z1 < {round(hr*0.60)} | Z2 {round(hr*0.60)}–{round(hr*0.70)} | "
        f"Z3 {round(hr*0.70)}–{round(hr*0.80)} | Z4 {round(hr*0.80)}–{round(hr*0.90)} | "
        f"Z5 > {round(hr*0.90)} bpm"
    )
    hf_modus = st.radio("HF-Eingabe", ["Einzelne Herzfrequenz", "Mix – mehrere Intervalle"], horizontal=True)
    if hf_modus == "Einzelne Herzfrequenz":
        hf_eingabe = st.number_input(
            "Durchschnittliche Herzfrequenz (bpm)", 60, 220,
            value=int(hr * 0.72), step=1, key="hf_einzel",
            help=(
                "**Hinweis: HF ist weniger präzise als Watt für die Carb-Berechnung.**\n\n"
                "Die App ordnet deine Durchschnitts-HF einer Zone zu und liest daraus "
                "einen festen Carb-Wert (g/h) ab.\n\n"
                "**Cardiac Drift:** Bei langen Fahrten (>2 h) steigt die Herzfrequenz "
                "bei gleicher Leistung durch Dehydrierung und Ermüdung an – die HF "
                "zeigt dann eine höhere Zone, als die tatsächliche Belastung ist. "
                "Das führt zu Carb-Werten, die den echten Verbrauch überschätzen.\n\n"
                "**Besser:** Watt-Steuerung mit Normalized Power nutzen, "
                "wenn ein Leistungsmesser vorhanden ist."
            )
        )
        zone = hf_zu_zone(hf_eingabe, hr)
        pct_hrmax = round(hf_eingabe / hr * 100)
        st.caption(f"→ **{hf_eingabe} bpm** = {pct_hrmax}% HRmax → Zone **{zone}**")
        st.warning(
            "⚠️ **Cardiac Drift:** Bei längeren Einheiten steigt die HF bei gleicher "
            "Leistung durch Ermüdung und Dehydrierung an – indoor sogar verstärkt, "
            "da kein Fahrtwind zur Kühlung beiträgt. Die Carb-Berechnung über HF "
            "kann dadurch die tatsächliche Intensität überschätzen. "
            "Falls ein Leistungsmesser vorhanden ist, liefert **Watt** genauere Ergebnisse."
        )
    else:
        zone = "Mix"

# ── Mix-Intervall-Builder (nur wenn Mix gewählt) ──────────────────────────────
if zone == "Mix":
    st.info(
        "**Intervalltraining:** Trage ein, wie lange du in welcher Zone/Wattleistung/HF fährst. "
        "Der Plan berechnet dann gewichtete Durchschnittswerte für Carbs und Wasser."
    )
    intervalle = st.session_state.intervalle

    intervall_zu_loeschen = None
    for idx, iv in enumerate(intervalle):
        with st.container():
            st.markdown(f"**Intervall {idx + 1}**")
            cols = st.columns([2, 2, 2, 1])

            # Intensitätseingabe je nach Modus
            if intensitaet_modus == "Zone manuell wählen":
                iv["zone"] = cols[0].selectbox(
                    "Zone", list(ZONE_LABELS.keys()),
                    index=list(ZONE_LABELS.keys()).index(iv.get("zone", "Z2")),
                    format_func=lambda x: ZONE_LABELS[x],
                    key=f"iv_zone_{idx}"
                )
                iv["watt"] = None
                iv["hf"] = None
                cols[1].markdown("&nbsp;")

            elif intensitaet_modus == "Nach Wattleistung":
                iv["watt"] = cols[0].number_input(
                    "Leistung (W)", 50, 600,
                    value=int(iv.get("watt") or profil["ftp_watt"] - 30),
                    step=5, key=f"iv_watt_{idx}"
                )
                derived_zone = watts_zu_zone(iv["watt"], profil["ftp_watt"])
                iv["zone"] = derived_zone
                iv["hf"] = None
                pct = round(iv["watt"] / profil["ftp_watt"] * 100)
                cols[1].metric("Zone (abgeleitet)", f"{derived_zone} ({pct}% FTP)")

            elif intensitaet_modus == "Nach Herzfrequenz":
                iv["hf"] = cols[0].number_input(
                    "Herzfrequenz (bpm)", 60, 220,
                    value=int(iv.get("hf") or profil["hr_max"] * 0.72),
                    step=1, key=f"iv_hf_{idx}"
                )
                derived_zone = hf_zu_zone(iv["hf"], profil["hr_max"])
                iv["zone"] = derived_zone
                iv["watt"] = None
                pct = round(iv["hf"] / profil["hr_max"] * 100)
                cols[1].metric("Zone (abgeleitet)", f"{derived_zone} ({pct}% HRmax)")

            iv["dauer_min"] = cols[2].number_input(
                "Dauer (Minuten)", 1, 600,
                value=int(iv.get("dauer_min", 60)),
                step=5, key=f"iv_dauer_{idx}"
            )
            if cols[3].button("🗑️", key=f"iv_del_{idx}", help="Intervall entfernen"):
                intervall_zu_loeschen = idx

    if intervall_zu_loeschen is not None and len(intervalle) > 1:
        intervalle.pop(intervall_zu_loeschen)
        st.rerun()

    cols = st.columns(2)
    if cols[0].button("➕ Intervall hinzufügen", use_container_width=True):
        letzte_zone = intervalle[-1].get("zone", "Z2") if intervalle else "Z2"
        intervalle.append({"zone": letzte_zone, "watt": None, "hf": None, "dauer_min": 30})
        st.rerun()

    # Zusammenfassung der Intervalle
    if intervalle:
        total_min = sum(iv["dauer_min"] for iv in intervalle)
        gewichtete_carbs = sum(
            CARBS_PRO_STUNDE.get(iv["zone"], 60) * iv["dauer_min"]
            for iv in intervalle
        ) / total_min if total_min > 0 else 60
        gewichtete_wasser = sum(
            berechne_wasser_pro_stunde(profil, 18, "mittel", False, iv["zone"], False) * iv["dauer_min"]
            for iv in intervalle
        ) / total_min if total_min > 0 else 350

        st.success(
            f"**Zusammenfassung:** {total_min} min gesamt | "
            f"Ø {gewichtete_carbs:.0f} g Carbs/h | "
            f"Ø {gewichtete_wasser:.0f} ml Wasser/h (bei 18 °C)"
        )
        st.caption("💡 Wasser wird im Plan mit echter Temperatur berechnet – diese Vorschau nutzt 18 °C als Schätzwert.")

    st.session_state.intervalle = intervalle

st.divider()

# ── Hauptformular ─────────────────────────────────────────────────────────────
with st.form("planungsformular"):

    # Route-Details (nur Outdoor)
    distanz_km = None
    hoehenmeter = None
    lat_default, lon_default = 51.0, 10.0

    if not ist_indoor:
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

    # ── Dauer ────────────────────────────────────────────────────────────────
    st.subheader("4. Trainingsdauer" if not ist_indoor else "3. Trainingsdauer")
    dauer_schaetzung = None
    if not ist_indoor and distanz_km and hoehenmeter is not None:
        dauer_schaetzung = schaetze_dauer(float(distanz_km), float(hoehenmeter), zone if zone != "Mix" else "Z2")
    dauer_h = st.number_input(
        "Trainingsdauer in Stunden",
        min_value=0.5, max_value=24.0,
        value=float(dauer_schaetzung) if dauer_schaetzung else 1.0 if ist_indoor else 3.0,
        step=0.25,
    )
    if dauer_schaetzung:
        st.caption(f"💡 Geschätzte Dauer aus Strecke + Höhenmetern: **{dauer_schaetzung} h**")

    # ── Wetter (nur Outdoor) ─────────────────────────────────────────────────
    temp_manuell = 20
    sonne_manuell = "keine"
    indoor = ist_indoor
    wetter_auto = False
    lat, lon = lat_default, lon_default
    start_h = 9
    datum = datetime.today() + timedelta(days=1)
    frueh_start = False

    if not ist_indoor:
        st.subheader("5. Wetter")
        cols = st.columns(2)
        datum = cols[0].date_input("Trainingsdatum", value=datetime.today() + timedelta(days=1))
        start_h = cols[1].slider("Startzeit (Uhr)", 0, 23, 9)

        wetter_auto = st.checkbox(
            "🌤 Wetter automatisch abrufen (Open-Meteo API, kostenlos)",
            value=True,
            help="Ruft Temperatur, Wind, Sonne und Regen für dein Trainingsgebiet ab. "
                 "Funktioniert nur mit Internetverbindung."
        )

        sonne_manuell = "mittel"
        temp_manuell = 18

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
            cols = st.columns(2)
            temp_manuell = cols[0].slider("Temperatur (°C)", -10, 45, 18)
            sonne_manuell = cols[1].selectbox(
                "Sonneneinstrahlung", ["keine", "mittel", "stark"], index=1,
                format_func=lambda x: {"keine": "☁️ Keine Sonne", "mittel": "⛅ Teils sonnig", "stark": "☀️ Vollsonne"}[x]
            )

        # ── Bedingungen ──────────────────────────────────────────────────────
        st.subheader("6. Weitere Bedingungen")
        frueh_start = st.checkbox(
            "Frühstart (Beginn vor 8 Uhr morgens)",
            value=(start_h < 8),
            help="Bei frühem Start ist es kühler und die Sonne steht tiefer. "
                 "Das reduziert die berechnete Trinkmenge leicht (Faktor ×0,9)."
        )
    else:
        # Indoor: nur Raumtemperatur
        st.subheader("4. Raumtemperatur")
        temp_manuell = st.slider(
            "Temperatur im Trainingsraum (°C)", 10, 40, 20,
            help="Die Raumtemperatur beeinflusst die Schweißrate. "
                 "Typisch: Keller ~15 °C, Wohnzimmer ~20 °C, schlecht belüftet ~25–30 °C."
        )
        st.caption("🌬️ Kein Fahrtwind beim Indoor-Training → Schweißrate wird automatisch um +30% erhöht.")

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
        _gpx = st.session_state.gpx_data
        _distanz = float(distanz_km) if distanz_km else 0.0
        _punkte_anzahl = (min(6, max(2, math.ceil(_distanz / 60)))
                          if _gpx and _distanz > 80 else 1)
        _spinner_text = (
            f"🌤 Wetterdaten werden an {_punkte_anzahl} Punkten entlang der Route abgerufen …"
            if _punkte_anzahl > 1 else "🌤 Wetterdaten werden abgerufen …"
        )
        with st.spinner(_spinner_text):
            wetter_roh, wetter_punkte = hole_wetterdaten_fuer_route(
                _gpx, lat, lon, datum.strftime("%Y-%m-%d"),
                start_h, dauer_h, zone, _distanz,
            )
            wetter_info = berechne_durchschnitts_wetter(wetter_roh)
        if wetter_info:
            temp = wetter_info["avg_temp"]
            sonne = wetter_info["sonne"]
            st.session_state.wetter_punkte = wetter_punkte
        else:
            st.session_state.wetter_punkte = []
            st.warning("⚠️ Wetterdaten konnten nicht abgerufen werden (kein Internet oder Datum zu weit in der Zukunft). Manuelle Temperatur wird verwendet.")

    # Mix-Modus: gewichtete Carbs und Wasser aus Intervallen berechnen
    carbs_pro_h_override = None
    wasser_pro_h_override = None
    mix_intervalle_snap = None
    if zone == "Mix" and st.session_state.intervalle:
        ivs = st.session_state.intervalle
        total_min = sum(iv["dauer_min"] for iv in ivs)
        if total_min > 0:
            carbs_pro_h_override = round(sum(
                CARBS_PRO_STUNDE.get(iv["zone"], 60) * iv["dauer_min"]
                for iv in ivs
            ) / total_min)
            wasser_pro_h_override = round(sum(
                berechne_wasser_pro_stunde(profil, temp, sonne, indoor, iv["zone"], frueh_start) * iv["dauer_min"]
                for iv in ivs
            ) / total_min)
            mix_intervalle_snap = [dict(iv) for iv in ivs]

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
        carbs_pro_h_override=carbs_pro_h_override,
        wasser_pro_h_override=wasser_pro_h_override,
        mix_intervalle=mix_intervalle_snap,
    )

    st.session_state.ergebnis = ergebnis
    st.session_state.wetter_info = wetter_info
    st.session_state.resupply_stopps = None


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
        if ist_indoor:
            st.info(
                f"⚡ Leistungssteuerung: **{e['watt']:.0f} W** = {pct}% FTP → Zone **{e['zone']}** "
                f"| {e['carbs']['quelle']}\n\n"
                "*Indoor-Training: Durchschnittsleistung = Normalized Power (kein Unterschied bei "
                "gleichmäßiger Belastung auf der Rolle).*"
            )
        else:
            st.info(
                f"⚡ Leistungssteuerung: **{e['watt']:.0f} W NP** = {pct}% FTP → Zone **{e['zone']}** "
                f"| {e['carbs']['quelle']}\n\n"
                "*Eingabe als Normalized Power (NP) liefert die praezisesten Carb-Werte. "
                "NP findest du in Garmin Connect als 'Gewichtete Leistung' oder in Strava als "
                "'Normalisierte Leistung' - typisch 5-15 % ueber der Average Power.*"
            )
    elif e["hf"] and e["hr_max"]:
        pct = round(e["hf"] / e["hr_max"] * 100)
        drift_hinweis = (
            " *(Hinweis: Bei langen Fahrten steigt HF durch Cardiac Drift an – "
            "Watt-Eingabe wäre präziser.)*"
            if e["dauer_h"] >= 3 and not ist_indoor else ""
        )
        st.info(
            f"❤️ HF-Steuerung: **{e['hf']:.0f} bpm** = {pct}% HRmax → Zone **{e['zone']}**"
            + drift_hinweis
        )
    else:
        st.info(f"🎯 Zone **{e['zone']}** | {e['carbs']['quelle']}")

    # Mix-Intervalle anzeigen
    if e["zone"] == "Mix" and e.get("mix_intervalle"):
        with st.expander("📊 Intervalldetails", expanded=False):
            ivs = e["mix_intervalle"]
            total_min = sum(iv["dauer_min"] for iv in ivs)
            rows = {"Intervall": [], "Zone": [], "Dauer (min)": [], "Anteil": [], "Carbs/h (g)": []}
            for i, iv in enumerate(ivs):
                rows["Intervall"].append(f"#{i+1}")
                rows["Zone"].append(iv["zone"])
                rows["Dauer (min)"].append(iv["dauer_min"])
                rows["Anteil"].append(f"{round(iv['dauer_min'] / total_min * 100)} %")
                rows["Carbs/h (g)"].append(CARBS_PRO_STUNDE.get(iv["zone"], 60))
            st.table(rows)
            st.caption(f"Gesamtdauer der Intervalle: {total_min} min | "
                       f"Gewichtete Carbs: {e['carbs']['pro_h']} g/h | "
                       f"Gewichtetes Wasser: {e['wasser']['pro_h']} ml/h")

    # ── Kernkennzahlen ──
    # hat_progressiv_data vorab berechnen (wird auch weiter unten bei der Strategie-Wahl gebraucht)
    _prog_vorschau = e["carbs"].get("progressiv", [])
    _hat_prog_vorschau = bool(_prog_vorschau and len(_prog_vorschau) > 1)
    _carbs_subtitle = (
        f"Ø {e['carbs']['pro_h_avg']} g/h (progressiv)"
        if _hat_prog_vorschau
        else f"{e['carbs']['pro_h']} g/h"
    )
    cols = st.columns(4)
    cols[0].metric("🍬 Carbs gesamt", f"{e['carbs']['gesamt']} g", _carbs_subtitle)
    cols[1].metric("💧 Wasser gesamt", f"{e['wasser']['gesamt']} ml", f"{e['wasser']['pro_h']} ml/h")
    cols[2].metric("⏱ Dauer", f"{e['dauer_h']} h")
    cols[3].metric("🌡 Temperatur", f"{e['temp']} °C")

    # Geschlecht/Alter-Korrekturen anzeigen
    _ga_faktor = geschlecht_alter_wasser_faktor(profil)
    if _ga_faktor < 1.0:
        _korrekturen = []
        if profil.get("geschlecht") == "Weiblich":
            _korrekturen.append("Geschlecht (Weiblich): –8% Schweißrate")
        _alter = profil.get("alter", 30)
        if _alter >= 60:
            _korrekturen.append(f"Alter ({_alter} J.): –13% Schweißrate")
        elif _alter >= 50:
            _korrekturen.append(f"Alter ({_alter} J.): –8% Schweißrate")
        st.caption(
            f"ℹ️ Angewandte Korrekturen: {' | '.join(_korrekturen)} "
            f"→ Gesamtfaktor ×{_ga_faktor:.2f} auf die Trinkmenge. "
            "Kohlenhydrate und Koffein bleiben unverändert."
        )

    # ── Energiebedarf ──
    with st.expander("🔋 Energiebedarf (Details)", expanded=True):
        cols = st.columns(4)
        cols[0].metric("Basis-Carbs", f"{e['carbs']['basis']} g",
                       help="Carbs aus Zone × Dauer")
        cols[1].metric("Höhenmeter-Bonus", f"+{e['carbs']['hm_bonus']} g",
                       help=f"+8 g pro 100 Hm Aufstieg")
        cols[2].metric("Davon Gels", f"{e['carbs']['aus_gels']} g")
        cols[3].metric("Davon Riegel", f"{e['carbs']['aus_riegeln']} g")

    # ── Ernährungs-Strategie wählen ──
    prog = _prog_vorschau          # bereits oben berechnet
    hat_progressiv_data = _hat_prog_vorschau

    if hat_progressiv_data:
        carb_strategie = st.radio(
            "🍽️ Ernährungs-Strategie",
            ["📈 Progressiv (wissenschaftlich empfohlen)", "➡️ Konstant (feste g/h)"],
            horizontal=True,
            help=(
                "**Progressiv:** Die Carb-Zufuhr steigt mit der Zeit, weil der Körper "
                "zunehmend auf externe Energie angewiesen ist. Wissenschaftlich optimal "
                "für Einheiten ≥ 2 h (Jeukendrup 2014).\n\n"
                "**Konstant:** Du nimmst jede Stunde dieselbe Menge auf. Einfacher "
                "in der Praxis – z. B. wenn du lieber gleichmäßig isst oder mit einem "
                "fixen Gel-/Riegel-Rhythmus arbeitest."
            ),
        )
        ist_konstant = carb_strategie.startswith("➡️")
    else:
        ist_konstant = True  # Kurze Einheiten: immer konstant

    # Konstant-Slider (nur sichtbar wenn Konstant-Modus UND lange Einheit)
    if ist_konstant and hat_progressiv_data:
        konstant_default = int(e["carbs"]["pro_h"])
        konstant_g_h = st.slider(
            "Konstante Carb-Zufuhr (g/h)",
            min_value=30, max_value=90,
            value=min(90, konstant_default), step=5,
            help=(
                "Wähle eine feste Carb-Menge, die du jede Stunde aufnimmst. "
                f"Empfehlung für {e['zone']}: {konstant_default} g/h (basiert auf deiner Leistung/Zone). "
                "Max. 90 g/h (physiologische Aufnahmegrenze)."
            ),
        )
        gesamt_konstant = round(konstant_g_h * e["dauer_h"])

        # ── Gel-Rezept an gewählte Konstant-Zufuhr anpassen ──
        # Das Glucose:Fructose-Verhältnis hängt von der tatsächlichen
        # Carb-Aufnahmerate ab (Jeukendrup 2014):
        # ≤60 g/h: nur Malto · 60–80: 2:1 · 80–100: 5:4 · >100: 1:1
        neue_ratio = empfehle_glukose_fructose(konstant_g_h)
        e["softflasks"]["ratio_info"] = neue_ratio
        # Alle Flaschen-Rezepte mit neuem Verhältnis neu berechnen
        for f in e["softflasks"].get("flaschen", []):
            f["rezept"] = berechne_gel_rezept(
                profil,
                f["carbs_pro_flask"],
                e["temp"],
                carbs_pro_h=konstant_g_h,
                volumen_ml=f["volumen_ml"],
            )
        if e["softflasks"].get("flaschen"):
            e["softflasks"]["rezept"] = e["softflasks"]["flaschen"][0]["rezept"]

        st.info(
            f"➡️ **Konstante Zufuhr:** {konstant_g_h} g/h × {e['dauer_h']} h "
            f"= **{gesamt_konstant} g gesamt**  \n"
            f"🧪 **Gel-Rezept angepasst:** {neue_ratio[2]}"
        )
    else:
        konstant_g_h = None  # wird im Bilanz-Abschnitt per Slider gesetzt

    # ── Progressiver Stundenplan ──
    if not ist_konstant:
        with st.expander("📈 Progressiver Carb-Zeitplan (stündlich)", expanded=True):
            st.caption(
                "Die Carb-Empfehlung steigt über die Zeit, weil der Körper zunehmend auf "
                "externe Zufuhr angewiesen ist: In Stunde 1 liefern Glykogenspeicher noch "
                "viel Energie, ab Stunde 3+ sind sie weitgehend aufgebraucht. "
                "*(Quellen: Jeukendrup 2014, Vøllestad & Blom 1985, Gonzalez & van Loon 2016)*"
            )
            # GI-Warnung bei Z4/Z5
            if e["zone"] in ("Z4", "Z5"):
                st.warning(
                    "⚠️ **Z4/Z5 – GI-Paradox:** Bei hoher Intensität ist der Carb-Bedarf am "
                    "höchsten, aber der Darmblutfluss sinkt um bis zu 70% → Absorption ist "
                    "begrenzt. Deckel bleibt bei 90 g/h. Bevorzuge flüssige/Gel-Formen und "
                    "isotonische Konzentration (4–6%). Carbs vor dem Hochintensitäts-Block "
                    "vorladen statt während!"
                )
            # Tabelle
            _max_rate = max(s["carbs_g_h"] for s in prog)
            header_cols = st.columns([1, 1.5, 2, 3])
            header_cols[0].markdown("**Stunde**")
            header_cols[1].markdown("**g/h**")
            header_cols[2].markdown("**Menge**")
            header_cols[3].markdown("**Intensität**")
            for s in prog:
                row = st.columns([1, 1.5, 2, 3])
                stunde_label = (f"{s['start_min']}–{s['end_min']} min"
                                if s["dauer_min"] < 60
                                else f"Stunde {s['stunde']}")
                row[0].write(stunde_label)
                row[1].write(f"**{s['carbs_g_h']} g/h**")
                row[2].write(f"{s['carbs_g']} g")
                # Balken-Visualisierung
                pct = s["carbs_g_h"] / max(_max_rate, 1)
                balken = "🟩" * int(pct * 8) + "⬜" * (8 - int(pct * 8))
                row[3].write(balken)
            st.markdown(
                f"**Gesamt: {sum(s['carbs_g'] for s in prog)} g "
                f"| Ø {e['carbs']['pro_h_avg']} g/h**"
            )

    # ── Glykogen-Speicherbilanz ──
    with st.expander("🧬 Glykogen-Speicherbilanz", expanded=True):
        st.caption(
            "Zeigt, wie sich deine Glykogenspeicher über die Dauer entwickeln. "
            "Verbrauch über die geplante Zufuhr hinaus wird aus den Speichern gedeckt. "
            "Bei <30 % Speicherrest steigt das Risiko spürbarer Leistungseinbrüche."
        )

        # Verbrauch ohne 120-g-Cap (echter physiologischer Wert)
        if e.get("watt") and e.get("ftp"):
            verbrauch_roh = berechne_carbs_pro_h_rohwert(e["watt"], e["ftp"])
        else:
            # HF-Pfad: Zonenbasierter Schätzwert (max. 90 g/h in Tabelle).
            # Verbrauch und geplante Zufuhr liegen nahe beieinander → Bilanz
            # zeigt wenig Defizit, was für gleichmaessige Fahrten korrekt ist.
            # Bei hoher Intensitaet oder Cardiac Drift kann der echte Verbrauch
            # hoeher liegen – Watt-Eingabe mit NP waere praeziser.
            verbrauch_roh = e["carbs"]["pro_h"]
            if e["dauer_h"] >= 3 or e["zone"] in ("Z4", "Z5"):
                np_hinweis = ("" if ist_indoor else
                              " Fuer genauere Ergebnisse: **Normalized Power (NP)** im Watt-Modus eingeben.")
                st.info(
                    "ℹ️ **Hinweis zur Speicherbilanz:** Da du HF statt Watt eingegeben hast, "
                    "basiert der Verbrauchswert auf dem Zonen-Durchschnitt (max. 90 g/h). "
                    "Bei langen Einheiten oder hoher Intensitat (Z4/Z5) "
                    "kann der echte Verbrauch hoeher liegen als hier angezeigt."
                    + np_hinweis
                )

        # Welchen Plan verwenden wir für die Bilanz?
        prog_plan = e["carbs"].get("progressiv", []) if not ist_konstant else []
        hat_progressiv = len(prog_plan) > 1

        col_in1, col_in2 = st.columns(2)

        if hat_progressiv:
            # Progressiv-Modus: %-Slider
            zufuhr_skalar = col_in1.slider(
                "Wie viel % des progressiven Plans isst du tatsächlich?",
                min_value=50, max_value=120,
                value=100, step=5,
                help=(
                    "100 % = du folgst dem Plan exakt (empfohlen). "
                    "80 % = du isst weniger als geplant (z.B. Magenprobleme). "
                    "120 % = du isst mehr (z.B. Gut-Training ermöglicht höhere Mengen)."
                ),
            ) / 100.0
            zufuhr_avg_anzeige = round(
                sum(s["carbs_g_h"] * zufuhr_skalar for s in prog_plan) / len(prog_plan)
            )
            col_in1.caption(f"→ Ø {zufuhr_avg_anzeige} g/h über alle Stunden")
            zufuhr_pro_h_fallback = zufuhr_avg_anzeige
        elif ist_konstant and konstant_g_h is not None:
            # Konstant-Modus (lange Einheit): Wert kommt vom Slider oben
            zufuhr_pro_h_fallback = konstant_g_h
            zufuhr_skalar = 1.0
            col_in1.metric("Konstante Zufuhr (g/h)", f"{konstant_g_h} g/h")
        else:
            # Kurze Einheit oder kein progressiver Plan: eigener Slider
            zufuhr_default = round(e["carbs"]["gesamt"] / e["dauer_h"]) if e["dauer_h"] > 0 else 0
            zufuhr_pro_h_fallback = col_in1.slider(
                "Realistische Zufuhr (g/h)",
                min_value=30, max_value=120,
                value=int(min(120, zufuhr_default)), step=5,
                help=(
                    "Was du tatsächlich pro Stunde aufnehmen kannst. "
                    "Standardwert = was der Plan vorsieht."
                ),
            )
            zufuhr_skalar = 1.0

        start_voll_pct = col_in2.slider(
            "Speicher-Füllstand am Start (%)",
            min_value=50, max_value=100,
            value=100, step=5,
            help=(
                "100 % = perfekt vorbereitet (Carbo-Loading 2–3 Tage, Frühstücks-KH). "
                "80–90 % = normal gegessen, kein Loading. "
                "60–70 % = nüchterner Start oder schlecht erholt."
            ),
        ) / 100.0

        # ── Cardiac Drift (automatisch) ──
        # Wird ab 2h automatisch eingerechnet auf Basis von Zone, Temperatur, Indoor.
        # Bei < 2h ist der Effekt vernachlässigbar.
        drift_rate = 0.0
        if e["dauer_h"] >= 2:
            drift_auto = cardiac_drift_rate_auto(e["temp"], ist_indoor, e["zone"])
            drift_pct_auto = round(drift_auto * 100, 1)
            drift_rate = drift_auto  # standardmäßig aktiv

            # Transparenz: zeige was berechnet wurde
            _ort = "Indoor (kein Fahrtwind)" if ist_indoor else "Outdoor"
            verbrauch_end_auto = verbrauch_roh * (1 + drift_rate * (e["dauer_h"] - 1))
            st.info(
                f"🫀 **Cardiac Drift automatisch eingerechnet: +{drift_pct_auto}% pro Stunde** "
                f"(Zone {e['zone']} · {e['temp']}°C · {_ort})  \n"
                f"→ Verbrauch steigt von {verbrauch_roh:.0f} g/h (Stunde 1) "
                f"auf **{verbrauch_end_auto:.0f} g/h** (Stunde {int(e['dauer_h'])}). "
                f"Du kannst die Rate unten manuell anpassen."
            )

            with st.expander("⚙️ Drift-Rate manuell anpassen", expanded=False):
                st.caption(
                    "**Was ist Cardiac Drift?** Bei gleichbleibender Wattzahl steigt deine "
                    "Herzfrequenz über Zeit durch Dehydrierung und Hitzeakkumulation. "
                    "Das erhöht den RER → mehr Carbs werden verbrannt.\n\n"
                    "**Quellen:** Coyle & González-Alonso (2001), Wingo et al. (2012), "
                    "Lafrenz et al. (2008).\n\n"
                    f"**Auto-Schätzung:** {drift_pct_auto}%/h. "
                    "Setze auf 0%, falls du Drift ignorieren willst, oder erhöhe, "
                    "wenn du weißt, dass du persönlich stark driftest "
                    "(z.B. schlecht hitzeadaptiert, wenig hydriert).\n\n"
                    "**Zonen-Einfluss:** Z1/Z2: niedrig. Z3: moderat. Z4/Z5: stark. \n"
                    "**Temperatur-Einfluss:** <15°C: gering. 15–25°C: moderat. >25°C: hoch."
                )
                drift_pct_manual = st.slider(
                    "Drift-Rate (% Mehrverbrauch pro Stunde)",
                    min_value=0, max_value=15,
                    value=int(round(drift_pct_auto)),
                    step=1,
                )
                drift_rate = drift_pct_manual / 100.0
                st.caption(
                    f"→ Stunde 1: {verbrauch_roh:.0f} g/h | "
                    f"Stunde 2: {verbrauch_roh*(1+drift_rate):.0f} g/h | "
                    f"Stunde {int(e['dauer_h'])}: "
                    f"{verbrauch_roh*(1+drift_rate*(int(e['dauer_h'])-1)):.0f} g/h"
                )

        bilanz = berechne_glykogen_bilanz(
            profil=profil,
            dauer_h=e["dauer_h"],
            verbrauch_pro_h=verbrauch_roh,
            zufuhr_pro_h=zufuhr_pro_h_fallback,
            hm_bonus_g=e["carbs"]["hm_bonus"],
            start_voll_pct=start_voll_pct,
            progressive_plan=prog_plan if hat_progressiv else None,
            zufuhr_skalar=zufuhr_skalar,
            cardiac_drift_rate=drift_rate,
        )

        # Kernmetriken
        c1, c2, c3, c4 = st.columns(4)
        c1.metric(
            "Speicher voll",
            f"{bilanz['speicher_voll_g']} g",
            help=f"{bilanz['koerpergewicht_kg']} kg × {bilanz['g_pro_kg']} g/kg "
                 f"({bilanz['geschlecht']}, {bilanz['trainings_status']})",
        )
        if drift_rate > 0:
            verbrauch_end = verbrauch_roh * (1 + drift_rate * (e["dauer_h"] - 1))
            c2.metric(
                "Verbrauch Stunde 1 → Ende",
                f"{bilanz['verbrauch_eff_pro_h']:.0f} → {verbrauch_end:.0f} g/h",
                help=(
                    f"Mit Cardiac Drift +{drift_rate*100:.0f}%/h steigt der KH-Verbrauch "
                    f"von {bilanz['verbrauch_eff_pro_h']:.0f} g/h auf "
                    f"{verbrauch_end:.0f} g/h in der letzten Stunde."
                ),
            )
        else:
            c2.metric(
                "Verbrauch (echt)",
                f"{bilanz['verbrauch_eff_pro_h']:.0f} g/h",
                help="Physiologischer KH-Verbrauch ohne 120-g-Aufnahme-Cap. "
                     "Inkl. anteiliger HM-Bonus.",
            )
        defizit_pro_h = bilanz["defizit_pro_h"]
        c3.metric(
            "Defizit/h",
            f"{defizit_pro_h:+.0f} g/h",
            delta=f"{-defizit_pro_h:.0f} g aus Speicher" if defizit_pro_h > 0 else "deckungsgleich",
            delta_color="inverse" if defizit_pro_h > 0 else "off",
        )
        end_pct = bilanz["speicher_end_pct"]
        _, end_emoji = speicher_zone(end_pct / 100)
        c4.metric(
            "Speicher am Ende",
            f"{end_emoji} {end_pct:.0f} %",
            f"{bilanz['speicher_end_g']} g",
            delta_color="off",
        )

        # Verlaufstabelle
        st.markdown("**Stundenweiser Verlauf**")
        if ist_konstant:
            st.caption(
                "📌 **Lesehilfe:** *Verbrauch* = was der Körper an Carbs verbrennt. "
                f"*Zufuhr* = konstant {zufuhr_pro_h_fallback:.0f} g/h jede Stunde. "
                "*Aus Glykogen* = Differenz, die aus den Speichern kommt. "
                "Bei konstanter Zufuhr ist die Speicher-Entleerung am Anfang höher "
                "(wenn der Bedarf die Zufuhr übersteigt) und sinkt, sobald Zufuhr = Bedarf."
            )
        else:
            st.caption(
                "📌 **Lesehilfe:** *Gesamtbedarf* = was der Körper an Carbs verbrennt (konstant bei gleicher Leistung). "
                "*Deine Zufuhr* = was du laut Plan isst (steigt progressiv). "
                "*Aus Glykogen* = die Differenz, die dein Körper aus den Speichern ergänzt — "
                "früh hoch (Speicher kompensieren geringe Zufuhr), später gering (du isst genug). "
                "Das ist korrekte Physiologie: progressive Ernährung schont die Speicher zunehmend."
            )
        zufuhr_spalte = "Zufuhr" if ist_konstant else "Zufuhr ↑"
        stunden = bilanz["stunden"]
        # Mit Drift: eigene g/h-Spalte zeigen, damit der Anstieg sichtbar ist
        if drift_rate > 0:
            tabelle = {
                "Bis Stunde": [f"{s['stunde_bis']:.1f} h" for s in stunden],
                "Verbr. g/h 🫀": [f"{s['verbrauch_g_h']:.0f} g/h" for s in stunden],
                "Verbrauch": [f"{s['verbrauch_g']:.0f} g" for s in stunden],
                zufuhr_spalte: [f"{s['zufuhr_g']:.0f} g" for s in stunden],
                "Aus Glykogen ↓": [
                    "✓ gedeckt" if s["gedeckt"] else f"+{s['defizit_g']:.0f} g"
                    for s in stunden
                ],
                "Speicher rest": [f"{s['speicher_rest_g']} g" for s in stunden],
                "Rest %": [f"{s['emoji']} {s['speicher_rest_pct']:.0f} %" for s in stunden],
            }
        else:
            tabelle = {
                "Bis Stunde": [f"{s['stunde_bis']:.1f} h" for s in stunden],
                "Verbrauch": [f"{s['verbrauch_g']:.0f} g" for s in stunden],
                zufuhr_spalte: [f"{s['zufuhr_g']:.0f} g" for s in stunden],
                "Aus Glykogen ↓": [
                    "✓ gedeckt" if s["gedeckt"] else f"+{s['defizit_g']:.0f} g"
                    for s in stunden
                ],
                "Speicher rest": [f"{s['speicher_rest_g']} g" for s in stunden],
                "Rest %": [f"{s['emoji']} {s['speicher_rest_pct']:.0f} %" for s in stunden],
            }
        st.table(tabelle)

        # Diagramm: Speicherverlauf über Zeit
        chart_data = {
            "Stunde": [0] + [s["stunde_bis"] for s in stunden],
            "Speicher (g)": [bilanz["speicher_start_g"]] + [s["speicher_rest_g"] for s in stunden],
        }
        try:
            import pandas as pd
            df_chart = pd.DataFrame(chart_data).set_index("Stunde")
            st.line_chart(df_chart, height=240)
        except ImportError:
            pass

        # Kritische Stunde
        if bilanz["kritische_stunde"] is not None:
            st.warning(
                f"⚠️ Kritischer Bereich (<30 % Speicher) erreicht bei Stunde "
                f"**{bilanz['kritische_stunde']:.1f} h**."
            )

        # Empfehlungen
        for emp in bilanz["empfehlungen"]:
            st.markdown(emp)

        with st.popover("ℹ️ Wie wird gerechnet?"):
            st.markdown(
                f"""
**Speichergröße:** {bilanz['koerpergewicht_kg']} kg × {bilanz['g_pro_kg']} g/kg
= **{bilanz['speicher_voll_g']} g** Glykogen total (Muskel + Leber).
Werte für {bilanz['geschlecht']}, Status: {bilanz['trainings_status']}.

**Geschlechtsunterschied:** Frauen haben bei gleichem Körpergewicht ~12% weniger
Muskelmasse (geringere FFM) und damit weniger absolute Glykogenkapazität.
Carbo-Loading-Response ist zusätzlich gedämpft (Tarnopolsky et al. 2007).

**Verbrauch pro Stunde:** Aus Watt × Wirkungsgrad und KH-Anteil je % FTP
(siehe Energie-Sektion), aber OHNE den 120-g-Aufnahme-Cap – der Körper
verbrennt, was er verbrennt, unabhängig davon, was du nachschieben kannst.

**Defizit:** Verbrauch − Zufuhr. Das Defizit kommt aus den Speichern.
Kumuliert ergibt das den Speicherstand zu jeder Stunde.

**Zonen (% Speicher-Rest):**
- 🟢 >50 %: voll leistungsfähig
- 🟡 30–50 %: erste Leistungsabfälle möglich, Pacing wichtig
- 🟠 15–30 %: spürbare Schwäche, Substratverschiebung Richtung Fett
- 🔴 <15 %: akute Hungerast-Gefahr

**Quellen:** Jeukendrup & Gleeson (2010), Burke (2015), Hawley & Leckey (2015),
Tarnopolsky et al. (2007), James et al. (2001).

**Limitationen:** Das Modell rechnet linear und ignoriert die natürliche
Glykogen-Sparwirkung bei längeren Belastungen (Substratverschiebung zu Fett
mit der Dauer). Es ist eher konservativ – im Zweifel hast du etwas mehr Reserve
als angezeigt. Bei sehr variabler Intensität (Bergetappen) ist der Mix-Modus
genauer als die Pauschalrechnung.
"""
            )

    # ── Softflasks ──
    with st.expander("🧴 Softflasks / Gel-Mischung", expanded=True):
        sf_res = e["softflasks"]
        cols = st.columns(3)
        cols[0].metric("Softflasks gesamt", sf_res["anzahl"])
        cols[1].metric("Gesamtvolumen", f"{sf_res.get('gesamt_volumen_ml', 0)} ml")
        cols[2].metric("Ø Carbs pro Flask", f"{sf_res['carbs_pro_flask']} g")

        ratio_info = sf_res.get("ratio_info")
        if ratio_info:
            r_m, r_f, r_txt = ratio_info
            ratio_display = ("Nur Maltodextrin (kein Fructose nötig)"
                             if r_f == 0 else f"{r_m}:{r_f} Maltodextrin:Fructose")
            st.info(f"💡 **G:F-Verhältnis:** {ratio_display} – {r_txt}")

        sf_flaschen = sf_res.get("flaschen", [])
        # Prüfen ob alle Flaschen gleiche Größe → ein gemeinsames Rezept reicht
        alle_gleich = (len(sf_flaschen) <= 1 or
                       all(f["volumen_ml"] == sf_flaschen[0]["volumen_ml"] for f in sf_flaschen))

        if alle_gleich and sf_flaschen:
            f0 = sf_flaschen[0]
            rez = f0["rezept"]
            st.markdown(f"**Rezept pro Softflask ({f0['volumen_ml']} ml):**")
            st.table({
                "Zutat": ["Maltodextrin", "Fructose", "Salz", "Wasser auffüllen auf"],
                "Menge": [f"{rez.get('maltodextrin',0)} g", f"{rez.get('fructose',0)} g",
                          f"{rez.get('salz',0)} g", f"{rez.get('wasser',0)} ml"],
            })
        elif sf_flaschen:
            st.markdown("**Rezept je Softflask-Typ (selbst mischen):**")
            for fd in sf_flaschen:
                rez = fd["rezept"]
                st.markdown(
                    f"_{fd['name']} · {fd['volumen_ml']} ml · {fd['anzahl']}× · "
                    f"{fd['carbs_pro_flask']} g Carbs_"
                )
                st.table({
                    "Zutat": ["Maltodextrin", "Fructose", "Salz", "Wasser auffüllen auf"],
                    "Menge": [f"{rez.get('maltodextrin',0)} g", f"{rez.get('fructose',0)} g",
                              f"{rez.get('salz',0)} g", f"{rez.get('wasser',0)} ml"],
                })
        else:
            st.info("Keine Softflasks eingeplant – im Profil (links) Softflasks hinzufügen.")
        st.caption("Alle Zutaten in die Softflask geben, Wasser auffüllen, schütteln.")

    # ── Riegel ──
    if e["riegel"]:
        with st.expander("🍫 Riegelplan", expanded=True):
            st.table({
                "Riegel": [r["name"] for r in e["riegel"]],
                "Mitgenommen": [f"{r['anzahl']} Stk" for r in e["riegel"]],
                "Carbs/Stk (g)": [r["carbs_g_pro_stueck"] for r in e["riegel"]],
                "Zucker/Stk (g)": [r["zucker_g_pro_stueck"] for r in e["riegel"]],
                "Carbs ges. (g)": [r["carbs_gesamt"] for r in e["riegel"]],
                "Zucker ges. (g)": [r["zucker_gesamt"] for r in e["riegel"]],
            })
            total_mitgebracht_g = sum(r["carbs_gesamt"] for r in e["riegel"])
            bedarf_g = e["carbs"]["aus_riegeln"]
            differenz = total_mitgebracht_g - bedarf_g
            if differenz >= 0:
                st.success(
                    f"✅ Mitgebrachte Riegel liefern **{total_mitgebracht_g} g Carbs** – "
                    f"Bedarf {bedarf_g} g gedeckt (+{differenz} g Reserve)"
                )
            else:
                st.warning(
                    f"⚠️ Mitgebrachte Riegel liefern nur **{total_mitgebracht_g} g Carbs** – "
                    f"Bedarf {bedarf_g} g → **{abs(differenz)} g fehlen** (Resupply nötig)"
                )
    else:
        st.info("ℹ️ Keine Riegel eingeplant – entweder keine aktiv oder Carbs vollständig aus Gels.")

    # ── Wasserflaschen ──
    with st.expander("🚰 Wasserflaschen", expanded=False):
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
        if profil.get("geschlecht") == "Weiblich":
            st.info(
                "💡 **Hinweis für Frauen:** Frauen verlieren aufgrund der geringeren "
                "Schweißrate im Schnitt ca. 25–30% weniger Natrium pro Stunde als Männer. "
                "Wenn du mit den berechneten Elektrolytmengen kein Kribbeln, "
                "Krämpfe oder übermäßigen Durst erlebst, könntest du die Portion leicht "
                "reduzieren. Individuelle Tests (z.B. mit eigenem Schweiß-Salzgehalt) "
                "sind genauer als pauschale Schätzwerte."
            )

    # ── Koffein ──
    with st.expander("☕ Koffein-Plan", expanded=False):
        koff = e["koffein"]
        if koff["caps"] > 0:
            cols = st.columns(3)
            cols[0].metric("Kapseln gesamt", koff["caps"])
            cols[1].metric("Gesamt-Koffein", f"{koff['gesamt_mg']} mg",
                           help="Summe über alle Kapseln")
            cols[2].metric("mg pro kg KG", f"{koff['mg_pro_kg']:.1f}",
                           help=f"Bezogen auf {profil.get('koerpergewicht_kg', 75)} kg. "
                                "Ziel-Bereich: 3–6 mg/kg laut ISSN.")
            if koff.get("cap_grund"):
                st.warning(f"⚠️ Dosis auf {koff['gesamt_mg']} mg gedeckelt — "
                           f"Grund: {koff['cap_grund']}")
            st.markdown("**Einnahme-Plan:**")
            for t in koff.get("timings", []):
                st.markdown(f"- {t['label']}")
            st.caption(
                "Wissenschaftliche Grundlage: 3 mg/kg Initial-Dosis (≈ 95 % des "
                "Benefits von 6 mg/kg, ISSN 2021) + 1,5 mg/kg Erhaltung alle 2 h. "
                "Sicherheitscap: 6 mg/kg pro Event ODER 400 mg (EFSA-Tagesgrenze)."
            )
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

            # Messpunkte entlang der Route anzeigen
            _wpunkte = st.session_state.get("wetter_punkte", [])
            if len(_wpunkte) > 1:
                st.markdown(f"**Wettermessung an {len(_wpunkte)} Punkten entlang der Route:**")
                st.table({
                    "km": [f"{p['km']:.0f}" for p in _wpunkte],
                    "Uhrzeit (gesch.)": [p["uhrzeit"] for p in _wpunkte],
                    "Ø Temp. (°C)": [p["temp_avg"] for p in _wpunkte],
                    "Regen (mm)": [p["regen_mm"] for p in _wpunkte],
                    "Koordinaten": [f"{p['lat']:.4f}°N, {p['lon']:.4f}°O" for p in _wpunkte],
                })
                st.caption(
                    "Die oben angezeigten Gesamtwerte (Ø Temp., Sonne, Wind, Regen) sind "
                    "der Durchschnitt aller Messpunkte. Die Uhrzeiten sind Schätzwerte "
                    "anhand der Streckenposition und der durchschnittlichen Fahrgeschwindigkeit."
                )
            elif _wpunkte:
                st.caption(f"📍 Messpunkt: Start ({_wpunkte[0]['lat']:.4f}°N, {_wpunkte[0]['lon']:.4f}°O) – "
                           "Für Mehrtages-Wettermessung eine GPX-Route mit >80 km hochladen.")

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
    if hinweise:
        with st.expander("⚠️ Hinweise & Empfehlungen", expanded=True):
            for h in hinweise:
                st.warning(h)

    # ── Resupply-Stopps ──────────────────────────────────────────────────────
    # Berechne ob überhaupt Stopps nötig sind
    braucht_wasser = e["wasserflaschen"]["auffuellungen"] > 0
    _aktive_r = [r for r in profil["riegel"] if r["aktiv"] and r.get("anzahl", 0) > 0]
    _kapazitaet_g = sum(r["carbs_g"] * r.get("anzahl", 0) for r in _aktive_r)
    braucht_carbs = (_kapazitaet_g > 0 and _aktive_r and
                     e["carbs"]["aus_riegeln"] > _kapazitaet_g)

    if not ist_indoor and (braucht_wasser or braucht_carbs):
        with st.expander("📍 Resupply-Stopps entlang der Route", expanded=True):
            # Kurze Zusammenfassung was gebraucht wird
            summary_parts = []
            if braucht_wasser:
                summary_parts.append(f"**{e['wasserflaschen']['auffuellungen']}× Wasser** (~{e['wasserflaschen']['refill_ml']} ml)")
            if braucht_carbs:
                fehlende_g = round(e["carbs"]["aus_riegeln"] - _kapazitaet_g)
                summary_parts.append(f"**Carb-Nachschub** (~{fehlende_g} g fehlen)")
            st.info("Unterwegs benötigt: " + " | ".join(summary_parts))

            if not gpx:
                st.warning("📌 Lade eine GPX-Datei hoch, um genaue Stopp-Positionen und Einkaufsmöglichkeiten entlang der Route zu sehen.")
            else:
                # Stopps berechnen
                resupply = berechne_resupply_stopps(profil, e, gpx)

                if not resupply:
                    st.info("Keine Stopps notwendig (Kapazität reicht für die gesamte Strecke).")
                else:
                    st.caption(f"**{len(resupply)} Resupply-Stopp(s)** berechnet – "
                               f"Suche im Umkreis von 1,5 km um den jeweiligen Routenpunkt (OpenStreetMap).")

                    # Stopps anzeigen (ohne POIs)
                    for i, s in enumerate(resupply):
                        needs = []
                        if s["braucht_wasser"]: needs.append("💧 Wasser")
                        if s["braucht_carbs"]:  needs.append("🍬 Carbs")

                        st.markdown(f"**Stopp {i+1} – km {s['km']}** &nbsp;|&nbsp; {' + '.join(needs)}")
                        st.caption(
                            f"📍 **{s['lat']:.5f}° N,  {s['lon']:.5f}° O** "
                            f"&nbsp;· [In Google Maps öffnen]"
                            f"(https://www.google.com/maps?q={s['lat']:.5f},{s['lon']:.5f})"
                        )

                        # Wasser-Zeile
                        if s["braucht_wasser"]:
                            wc = st.columns(3)
                            wc[0].metric("Position", f"km {s['km']}")
                            wc[1].metric("Wasser-Reserve bei Ankunft", f"~{s['wasser_rest_ml']} ml",
                                         help="Noch im Tank (~18% Reserve)")
                            wc[2].metric("Auffüllen", f"~{s['wasser_refill_ml']} ml")

                        # Carb-Zeile
                        if s["braucht_carbs"]:
                            einkauf = s.get("carbs_einkauf_g", 0)
                            cc = st.columns(3)
                            if not s["braucht_wasser"]:
                                cc[0].metric("Position", f"km {s['km']}")
                            cc[1].metric("Carb-Reserve bei Ankunft", f"~{s['carbs_rest_g']} g",
                                         help="Noch in Trikottaschen (~20% Reserve)")
                            cc[2].metric("Einkauf nötig", f"~{einkauf} g Carbs",
                                         help="Gummibären: 85 g/100 g | Banane: ~25 g | Riegel: je nach Produkt")
                            if einkauf > 0:
                                st.caption(
                                    f"💡 Entspricht z.B.: **{round(einkauf/25)} Banane(n)** oder "
                                    f"**{round(einkauf/0.85):.0f} g Gummibärchen** oder "
                                    f"**{math.ceil(einkauf/35)} Müsliriegel** (à ~35 g Carbs)"
                                )
                        st.divider()

                    # POI-Suche an den Stopp-Punkten
                    if st.button("🔍 Beste Einkaufsmöglichkeiten entlang der Route suchen", use_container_width=True):
                        with st.status("Suche Einkaufsmöglichkeiten …", expanded=True) as status:
                            for idx, s in enumerate(resupply):
                                status.update(label=f"Stopp {idx+1}/{len(resupply)}: suche im Fenster bis km {s['km']} …")
                                s["poi_ergebnisse"] = suche_pois_entlang_route(
                                    gpx, s["km"], radius_m=500, km_fenster=25
                                )
                                gefunden = len(s["poi_ergebnisse"])
                                st.write(f"✅ Stopp {idx+1} (km {s['km']}): {gefunden} Station(en) gefunden")
                            status.update(label="Suche abgeschlossen", state="complete", expanded=False)
                        st.session_state.resupply_stopps = resupply
                        st.rerun()

                    # POI-Ergebnisse anzeigen
                    anzeige_stopps = st.session_state.resupply_stopps or []
                    for i, s in enumerate(anzeige_stopps):
                        pois = s.get("poi_ergebnisse", [])
                        deadline_km = s["km"]
                        st.markdown(f"**Stopp {i+1} – Deadline: km {deadline_km} | Einkaufsmöglichkeiten in den letzten 25 km:**")
                        if pois:
                            empfehlung = pois[0]
                            maps_base = "https://www.google.com/maps/search/?api=1&query="
                            for rank, p in enumerate(pois):
                                adresse = (p["strasse"] + (f", {p['ort']}" if p["ort"] else "")).strip(", ")
                                maps_url = f"{maps_base}{p['lat']},{p['lon']}"
                                dist_label = f"{p['dist_m']} m zur Route"
                                km_label = f"km {p['route_km']}"
                                badge = "⭐ **Empfehlung** – " if rank == 0 else ""
                                st.markdown(
                                    f"{badge}[{p['name']}]({maps_url}) · {p['typ']}"
                                    + (f" · {adresse}" if adresse else "")
                                    + f" | {km_label} | {dist_label}"
                                )
                        else:
                            st.caption("Keine Station im 25-km-Fenster vor diesem Stopp gefunden (Radius 500 m zur Route).")

    # ── Expertenansicht: alle Berechnungen offenlegen ──
    st.divider()
    with st.expander("🔬 Expertenansicht — wie wurde das alles berechnet?", expanded=False):
        st.caption(
            "Vollständige Offenlegung aller Zwischenschritte. Für Sportler/innen, "
            "die genau verstehen wollen, woher jede Zahl im Plan kommt. "
            "Alle Formeln und Quellen findest du in der "
            "[ausführlichen Berechnungs-Dokumentation]"
            "(https://github.com/FeDaSy/fueling-planner/blob/main/BERECHNUNGEN_UND_APIS.txt) "
            "(kein GitHub-Konto nötig)."
        )

        # ───────────────────────────────────────────
        # 1. CARB-VERBRENNUNG (carbs_pro_h)
        # ───────────────────────────────────────────
        st.markdown("### 1. Carb-Verbrennung pro Stunde (`carbs_pro_h`)")
        carb_quelle = e["carbs"]["quelle"]
        carbs_h = e["carbs"]["pro_h"]
        st.markdown(f"**Quelle:** {carb_quelle}")

        if e.get("watt") and e.get("ftp"):
            watt_e = e["watt"]
            ftp_e = e["ftp"]
            pct_ftp = round(watt_e / ftp_e * 100, 1)
            kcal_h = round((watt_e * 3600) / (4180 * 0.22))
            if pct_ftp < 55:
                kh_anteil = 0.35
                ftp_label = "< 55% FTP → Regeneration"
            elif pct_ftp < 75:
                kh_anteil = 0.50
                ftp_label = "55–75% FTP → Grundlage"
            elif pct_ftp < 90:
                kh_anteil = 0.72
                ftp_label = "75–90% FTP → Tempo"
            elif pct_ftp < 105:
                kh_anteil = 0.87
                ftp_label = "90–105% FTP → Schwelle"
            else:
                kh_anteil = 0.95
                ftp_label = "> 105% FTP → maximal"

            st.markdown(
                f"**Eingabe:** {watt_e:.0f} W bei FTP {ftp_e:.0f} W → "
                f"**{pct_ftp}% FTP** ({ftp_label})\n\n"
                f"**Schritt 1 — Kalorien/h** (Wirkungsgrad 22%):  \n"
                f"`kcal/h = (Watt × 3600) / (4180 × 0,22)`  \n"
                f"`= ({watt_e:.0f} × 3600) / (4180 × 0,22)`  \n"
                f"`= {kcal_h} kcal/h`\n\n"
                f"**Schritt 2 — KH-Anteil:** {int(kh_anteil*100)} % "
                f"(intensitätsabhängig)\n\n"
                f"**Schritt 3 — Carbs/h** (4 kcal/g):  \n"
                f"`Carbs/h = (kcal/h × KH-Anteil) / 4`  \n"
                f"`= ({kcal_h} × {kh_anteil}) / 4`  \n"
                f"`= {round((kcal_h * kh_anteil) / 4)} g/h` → "
                f"**{carbs_h} g/h** (Cap 120 g/h)"
            )
        else:
            # HF- oder Zonen-Modus → CARBS_PRO_STUNDE-Lookup
            st.markdown(
                f"**Modus:** ohne Wattmessung → Festwert aus Zone {e['zone']}: "
                f"**{carbs_h} g/h** "
                f"(Tabelle: Z1=30, Z2=60, Z3=75, Z4=90, Z5=90, Mix=70 g/h)"
            )

        # Höhenmeter-Bonus
        if e.get("hoehenmeter"):
            hm_bonus = e["carbs"]["hm_bonus"]
            st.markdown(
                f"**Höhenmeter-Bonus:** {e['hoehenmeter']} Hm × (8 g / 100 Hm) "
                f"= **+{hm_bonus} g** (verteilt auf {e['dauer_h']} h)"
            )

        # ───────────────────────────────────────────
        # 2. PROGRESSIVER STUNDENPLAN
        # ───────────────────────────────────────────
        prog = e["carbs"].get("progressiv", [])
        if prog and len(prog) > 1:
            st.markdown("### 2. Progressiver Stundenplan (relative Multiplikatoren)")
            zone_e = e["zone"]
            st.markdown(
                f"**Basis:** carbs_pro_h = {carbs_h} g/h, Zone {zone_e}, "
                f"Dauer {e['dauer_h']} h\n\n"
                "**Formel pro Stunde:**  \n"
                "`rate = min(carbs_pro_h × multiplikator[zone, kum_min], 90)`"
            )
            rows = []
            for s in prog:
                mult = round(s["carbs_g_h"] / carbs_h, 2) if carbs_h > 0 else 1.0
                rows.append({
                    "Stunde": s["stunde"],
                    "kum. Minute": f"{s['start_min']}–{s['end_min']}",
                    "Multiplikator": f"× {mult}",
                    "Rechnung": f"{carbs_h} × {mult} = {s['carbs_g_h']} g/h",
                    "Menge (g)": s["carbs_g"],
                })
            st.table(rows)
            st.caption(
                "Quelle: Jeukendrup 2014, Vøllestad & Blom 1985, Gonzalez & van Loon 2016, "
                "Impey & Morton 2018. Cap bei 90 g/h (intestinale Aufnahmegrenze)."
            )

        # ───────────────────────────────────────────
        # 3. CARDIAC DRIFT
        # ───────────────────────────────────────────
        if e["dauer_h"] >= 2:
            st.markdown("### 3. Cardiac Drift — Aufschlüsselung")
            temp_e = e["temp"]
            # Basis aus Temperatur
            if temp_e < 15:
                base_rate, base_label = 0.020, "kühl (<15°C)"
            elif temp_e < 25:
                base_rate, base_label = 0.035, "moderat (15–25°C)"
            elif temp_e < 32:
                base_rate, base_label = 0.050, "warm (25–32°C)"
            else:
                base_rate, base_label = 0.070, "heiß (>32°C)"
            indoor_extra = 0.020 if ist_indoor else 0.0
            zone_mult_dict = {"Z1": 0.7, "Z2": 1.0, "Z3": 1.4, "Z4": 1.8, "Z5": 2.0, "Mix": 1.2}
            zone_mult = zone_mult_dict.get(e["zone"], 1.0)
            final_rate = (base_rate + indoor_extra) * zone_mult

            st.markdown(
                f"**Basis-Rate** (aus Temperatur {temp_e}°C, {base_label}): "
                f"`{base_rate*100:.1f}%/h`\n\n"
                f"**Indoor-Zuschlag** ({'Indoor' if ist_indoor else 'Outdoor'}): "
                f"`+{indoor_extra*100:.1f}%/h`\n\n"
                f"**Zonen-Multiplikator** (Zone {e['zone']}): `× {zone_mult}`\n\n"
                f"**Formel:**  \n"
                f"`drift = (basis_rate + indoor_zuschlag) × zonen_multiplikator`  \n"
                f"`= ({base_rate:.3f} + {indoor_extra:.3f}) × {zone_mult}`  \n"
                f"`= {final_rate:.3f}` → **{final_rate*100:.1f}%/h** (Auto-Schätzung)"
            )
            if abs(drift_rate - final_rate) > 0.0005:
                st.markdown(
                    f"⚙️ Du hast die Drift-Rate manuell auf "
                    f"**{drift_rate*100:.0f}%/h** angepasst."
                )

            verbrauch_basis = bilanz["verbrauch_eff_pro_h"]
            st.markdown(
                "**Stündliche Verbrauchssteigerung:**  \n"
                "`verbrauch(stunde) = verbrauch_basis × (1 + drift × (stunde − 1))`"
            )
            drift_rows = []
            for i in range(int(e["dauer_h"])):
                mult_i = 1 + drift_rate * i
                drift_rows.append({
                    "Stunde": i + 1,
                    "Multiplikator": f"× {mult_i:.3f}",
                    "Verbrauch g/h": f"{verbrauch_basis * mult_i:.1f}",
                })
            st.table(drift_rows)
            st.caption(
                "Quelle: Coyle & González-Alonso 2001, Wingo et al. 2012, "
                "Lafrenz et al. 2008."
            )

        # ───────────────────────────────────────────
        # 4. GLYKOGEN-SPEICHER
        # ───────────────────────────────────────────
        st.markdown("### 4. Glykogen-Speicher")
        st.markdown(
            f"**Körpergewicht:** {bilanz['koerpergewicht_kg']} kg  \n"
            f"**Geschlecht / Trainingsstatus:** {bilanz['geschlecht']} / "
            f"{bilanz['trainings_status']}  \n"
            f"**Spezifische Speichergröße:** {bilanz['g_pro_kg']} g/kg "
            "(aus Tabelle, geschlechts- und trainingsspezifisch)\n\n"
            f"**Speicher voll:** `{bilanz['koerpergewicht_kg']} kg × "
            f"{bilanz['g_pro_kg']} g/kg = {bilanz['speicher_voll_g']} g`  \n"
            f"**Speicher Start:** `{bilanz['speicher_voll_g']} g × "
            f"{int(start_voll_pct*100)} % = {bilanz['speicher_start_g']} g`"
        )
        st.caption(
            "Physiologie: Glykogen kann während der Belastung NICHT aufgefüllt werden "
            "(Insulin supprimiert, GLUT4 inaktiv). Überschuss aus Nahrung wird oxidiert. "
            "Quelle: Jeukendrup & Gleeson, Sport Nutrition 3. Aufl."
        )

        # ───────────────────────────────────────────
        # 5. WASSER / SCHWEISS
        # ───────────────────────────────────────────
        st.markdown("### 5. Schweißrate & Wasser")
        wasser_h = e["wasser"]["pro_h"]
        ga_faktor = geschlecht_alter_wasser_faktor(profil)
        intensitaet_f = INTENSITAETS_FAKTOR.get(e["zone"], 1.0)
        indoor_f = 1.30 if ist_indoor else 1.0
        basis_ml = get_schweissrate_ml_h(profil, e["temp"])

        # Residual = sonne_f × fruehstart_f (Werte sind nicht direkt im Ergebnis gespeichert)
        bekannt_faktor = intensitaet_f * indoor_f * ga_faktor
        residual = (wasser_h / basis_ml / bekannt_faktor) if basis_ml > 0 and bekannt_faktor > 0 else 1.0

        st.markdown(
            f"**Schritt 1 — Basisrate** aus Schweißtyp-Preset "
            f"`{profil['schweissrate']['preset']}` bei {e['temp']}°C: "
            f"**{basis_ml} ml/h**\n\n"
            f"**Schritt 2 — Faktoren (Multiplikator-Stapel):**  \n"
            f"- Intensität (Zone {e['zone']}): × {intensitaet_f}  \n"
            f"- Indoor: × {indoor_f}  \n"
            f"- Geschlecht & Alter: × {ga_faktor:.2f}  \n"
            f"- Sonne + Frühstart (kombiniert): × {residual:.2f}\n\n"
            f"**Schritt 3 — Endergebnis:**  \n"
            f"`{basis_ml} × {intensitaet_f} × {indoor_f} × {ga_faktor:.2f} × "
            f"{residual:.2f}`  \n"
            f"`≈ {wasser_h} ml/h` × {e['dauer_h']} h "
            f"= **{e['wasser']['gesamt']} ml** gesamt"
        )
        st.caption(
            "Sonne (× 1.0/1.1/1.2 je nach Bedeckung) und Frühstart (× 0.9) sind "
            "im residuellen Faktor zusammengefasst, da sie nicht einzeln im "
            "Ergebnis-Dictionary gespeichert werden."
        )

        # ───────────────────────────────────────────
        # 6. GEL-REZEPT (Malto:Fructose)
        # ───────────────────────────────────────────
        sf_data = e.get("softflasks", {})
        ratio_info = sf_data.get("ratio_info")
        if ratio_info and sf_data.get("flaschen"):
            st.markdown("### 6. Gel-Rezept (Malto:Fructose-Verhältnis)")
            malto_r, fruct_r, ratio_label = ratio_info
            st.markdown(
                f"**Entscheidungsregel** (Jeukendrup 2014, Fuchs et al. 2019, "
                f"Viribay et al. 2020):  \n"
                f"< 60 g/h → nur Malto · 60–90 g/h → 2:1 · > 90 g/h → 5:4 (≈1:0.8)\n\n"
                f"**Bei deinen {carbs_h} g/h:** {ratio_label}  \n"
                f"→ Malto-Anteil: {malto_r} · Fructose-Anteil: {fruct_r}"
            )
            for f in sf_data["flaschen"]:
                r = f.get("rezept", {})
                st.markdown(
                    f"**{f['name']} ({f['volumen_ml']} ml, {f['anzahl']}× mitgenommen):**  \n"
                    f"- Carbs pro Flask: {f['carbs_pro_flask']} g  \n"
                    f"- Maltodextrin: {r.get('maltodextrin', 0)} g · "
                    f"Fructose: {r.get('fructose', 0)} g  \n"
                    f"- Salz: {r.get('salz', 0)} g · Wasser: {r.get('wasser', 0)} ml"
                )

        # ───────────────────────────────────────────
        # 7. KOFFEIN
        # ───────────────────────────────────────────
        koff = e.get("koffein", {})
        if koff and koff.get("caps", 0) > 0:
            st.markdown("### 7. Koffein-Plan (körpergewicht- & dauerbasiert)")
            gw = profil.get("koerpergewicht_kg", 75)
            mg_cap = profil["koffein"]["pro_cap_mg"]
            initial_target = 3.0 * gw
            maint_per = 1.5 * gw
            if e["dauer_h"] <= 2:
                n_maint = 0
            else:
                n_maint = max(0, math.floor((e["dauer_h"] - 1) / 2.0))
            roh_target = initial_target + n_maint * maint_per
            st.markdown(
                f"**Wissenschaftliche Strategie:**  \n"
                f"- Initial-Dosis: 3 mg/kg (ISSN 2021)  \n"
                f"- Erhaltungsdosen: 1,5 mg/kg alle 2 h ab Stunde 2  \n"
                f"- Sicherheitsobergrenze: 6 mg/kg ODER 400 mg (EFSA)\n\n"
                f"**Deine Werte** ({gw} kg, {e['dauer_h']} h, "
                f"{mg_cap} mg/Cap):\n\n"
                f"`Initial = 3 × {gw} = {initial_target:.0f} mg`  \n"
                f"`Erhaltung = {n_maint} × 1,5 × {gw} = "
                f"{n_maint * maint_per:.0f} mg`  \n"
                f"`Roh-Ziel = {roh_target:.0f} mg`"
            )
            if koff.get("cap_grund"):
                st.markdown(
                    f"⚠️ **Gedeckelt auf {koff['gesamt_mg']} mg** — "
                    f"Grund: {koff['cap_grund']}"
                )
            st.markdown(
                f"**Endergebnis:** {koff['caps']} Kapseln × {mg_cap} mg "
                f"= **{koff['gesamt_mg']} mg** "
                f"(**{koff['mg_pro_kg']:.2f} mg/kg**)"
            )
            st.markdown("**Einnahme-Plan:**")
            for t in koff.get("timings", []):
                st.markdown(f"- {t['label']}")

        # ───────────────────────────────────────────
        # 8. VERTEILUNG GELS vs. RIEGEL
        # ───────────────────────────────────────────
        st.markdown("### 8. Verteilung Carbs auf Gels & Riegel")
        gel_anteil = profil["softflask"]["gel_anteil_pct"]
        st.markdown(
            f"**Profil-Einstellung:** {gel_anteil} % aus Gels, "
            f"{100 - gel_anteil} % aus Riegeln\n\n"
            f"**Berechnung:**  \n"
            f"- Carbs gesamt: {e['carbs']['gesamt']} g  \n"
            f"- Aus Gels: {e['carbs']['gesamt']} × {gel_anteil}% = "
            f"**{e['carbs']['aus_gels']} g**  \n"
            f"- Aus Riegeln: {e['carbs']['gesamt']} − {e['carbs']['aus_gels']} = "
            f"**{e['carbs']['aus_riegeln']} g**"
        )

        st.info(
            "💡 Alle Formeln, Quellenangaben und wissenschaftliche Begründungen "
            "findest du in der vollständigen "
            "[Berechnungs- & API-Dokumentation auf GitHub]"
            "(https://github.com/FeDaSy/fueling-planner/blob/main/BERECHNUNGEN_UND_APIS.txt) "
            "— öffentlich einsehbar, kein GitHub-Konto erforderlich."
        )

    # ── Download ──
    st.divider()
    wp  = st.session_state.get("wetter_punkte", [])
    rs  = st.session_state.get("resupply_stopps") or []
    # Falls Stopps noch nicht berechnet: jetzt nachholen (braucht GPX)
    _gpx_dl = st.session_state.get("gpx_data")
    if not rs and _gpx_dl and (
        e.get("wasserflaschen", {}).get("auffuellungen", 0) > 0
        or e.get("carbs", {}).get("aus_riegeln", 0) > 0
    ):
        rs = berechne_resupply_stopps(profil, e, _gpx_dl)
    # konstant_g_h ist nur gesetzt wenn der User die Konstant-Strategie gewählt hat
    _export_konstant = konstant_g_h if (ist_konstant and hat_progressiv_data and konstant_g_h is not None) else None

    # Export-Kontext: alle UI-State-Werte bündeln, damit Export alles abdecken kann
    export_context = {
        "profil": profil,
        "ist_indoor": ist_indoor,
        "ist_konstant": ist_konstant,
        "konstant_g_h": _export_konstant,
        "bilanz": bilanz,
        "drift_rate": drift_rate,
        "start_voll_pct": start_voll_pct,
        "zufuhr_pro_h_fallback": zufuhr_pro_h_fallback,
        "zufuhr_skalar": zufuhr_skalar,
        "gpx_data": _gpx_dl,
    }

    plan_text = erstelle_plan_text(e, w, wp, rs, export_context=export_context)
    pdf_bytes = erstelle_plan_pdf(e, w, wp, rs, export_context=export_context)
    dl_col1, dl_col2 = st.columns(2)
    with dl_col1:
        st.download_button(
            label="📥 Plan als .txt herunterladen",
            data=plan_text,
            file_name=f"fueling_plan_{datetime.now().strftime('%Y%m%d_%H%M')}.txt",
            mime="text/plain",
            use_container_width=True,
        )
    with dl_col2:
        if pdf_bytes:
            st.download_button(
                label="📄 Plan als PDF herunterladen",
                data=pdf_bytes,
                file_name=f"fueling_plan_{datetime.now().strftime('%Y%m%d_%H%M')}.pdf",
                mime="application/pdf",
                use_container_width=True,
            )
        else:
            st.info("PDF nicht verfügbar – `fpdf2` nicht installiert.")
