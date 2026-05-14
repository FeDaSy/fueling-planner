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
    Wissenschaftlich empfohlenes Glucose:Fructose-Verhältnis nach Jeukendrup (2014).
    Basis: SGLT1 transportiert Glucose (max ~60 g/h), GLUT5 transportiert Fructose (max ~50 g/h).
    Erst ab 60 g/h ist Fructose sinnvoll, weil SGLT1 dann saturiert ist.
    """
    if carbs_pro_h <= 60:
        return (1, 0, "Nur Maltodextrin/Glucose (SGLT1 noch nicht saturiert, Fructose nicht nötig)")
    elif carbs_pro_h <= 80:
        return (2, 1, "2:1 Maltodextrin:Fructose (klassisches Verhältnis für 60–80 g/h)")
    elif carbs_pro_h <= 100:
        return (5, 4, "~1:0.8 Maltodextrin:Fructose (optimiert für 80–100 g/h, max. Darmaufnahme)")
    else:
        return (1, 1, "1:1 Maltodextrin:Fructose (maximale Absorption >100 g/h, beide Transporter voll ausgelastet)")


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
    if not profil["koffein"]["aktiv"]:
        return {"caps": 0, "plan": "Koffein deaktiviert"}
    mg = profil["koffein"]["pro_cap_mg"]
    if dauer_h < 2:   return {"caps": 0, "plan": "Nicht nötig (< 2 h)"}
    elif dauer_h < 4: return {"caps": 1, "plan": f"1 Cap ({mg} mg) nach Stunde 2"}
    elif dauer_h < 6: return {"caps": 2, "plan": f"Stunde 2 und 4 (je {mg} mg)"}
    elif dauer_h < 8: return {"caps": 4, "plan": f"Stunde 1, 4, 6, 8 (je {mg} mg)"}
    else:             return {"caps": 5, "plan": f"Stunde 1, 4, 7, 9 (Doppel), 11"}

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
                       konstant_g_h=None):
    sf_res = e.get("softflasks", {})
    wf = e.get("wasserflaschen", {})
    sonne_label = {"keine": "Bedeckt", "mittel": "Teils sonnig", "stark": "Vollsonne"}
    ist_konstant_export = konstant_g_h is not None

    if ist_konstant_export:
        carbs_zeile = (
            f"Gesamt        : {e['carbs']['gesamt']} g  "
            f"({konstant_g_h} g/h konstant via {e['carbs']['quelle']})"
        )
    else:
        carbs_zeile = (
            f"Gesamt        : {e['carbs']['gesamt']} g  "
            f"(O {e['carbs']['pro_h_avg']} g/h progressiv via {e['carbs']['quelle']})"
        )

    lines = [
        "=" * 62,
        "  CYCLING FUELING PLAN",
        "=" * 62,
        f"Profil : {e['profil_name']}",
        f"Zone   : {e['zone']}  |  Dauer: {e['dauer_h']} h  |  Temp: {e['temp']} °C",
        "",
        "--- KOHLENHYDRATE ---",
        carbs_zeile,
        f"Basis         : {e['carbs']['basis']} g",
        f"HM-Bonus      : {e['carbs']['hm_bonus']} g",
        f"Aus Gels      : {e['carbs']['aus_gels']} g",
        f"Aus Riegeln   : {e['carbs']['aus_riegeln']} g",
    ]
    if sf_res.get("ratio_info"):
        ri = sf_res["ratio_info"]
        lines.append(f"Glukose:Frukt. : {ri[2]}")
    # Stundenplan im TXT: progressiv oder konstant
    prog_txt = e["carbs"].get("progressiv", [])
    if ist_konstant_export and prog_txt and len(prog_txt) > 1:
        # Konstante Strategie: einfache Zeile statt Stundenplan
        gesamt_konstant = round(konstant_g_h * e["dauer_h"])
        lines.append("")
        lines.append(f"  Strategie     : Konstant {konstant_g_h} g/h jede Stunde")
        lines.append(f"  Gesamt        : {gesamt_konstant} g")
    elif prog_txt and len(prog_txt) > 1:
        lines.append("")
        lines.append("  Progressiver Zeitplan (Stunde -> g/h -> Menge):")
        for s in prog_txt:
            label = (f"  {s['start_min']:>3}-{s['end_min']:>3} min"
                     if s["dauer_min"] < 60 else f"  Stunde {s['stunde']:<2}      ")
            lines.append(f"{label}  {s['carbs_g_h']:>3} g/h  ->  {s['carbs_g']:>3} g")
    lines.append("")

    lines += [
        "--- WASSER ---",
        f"Gesamt        : {e['wasser']['gesamt']} ml  ({e['wasser']['pro_h']} ml/h)",
        f"Aus Gels      : {e['wasser']['aus_gels']} ml",
        f"Aus Flaschen  : {e['wasser']['zusaetzlich']} ml",
    ]
    if wf:
        lines.append(f"Auffüllungen  : {wf.get('auffuellungen', 0)}x  (~{wf.get('refill_ml', 0)} ml/Mal)")
    lines.append("")

    lines.append("--- SOFTFLASKS ---")
    sf_flaschen = sf_res.get("flaschen", [])
    if sf_flaschen:
        for f in sf_flaschen:
            r = f.get("rezept", {})
            lines.append(f"  {f['anzahl']}x {f['name']} ({f['volumen_ml']} ml):")
            lines.append(
                f"    Carbs {f['carbs_pro_flask']} g  |  Malto {r.get('maltodextrin', 0)} g  |  "
                f"Fructose {r.get('fructose', 0)} g  |  Salz {r.get('salz', 0)} g  |  "
                f"Wasser {r.get('wasser', 0)} ml"
            )
    else:
        r0 = sf_res.get("rezept", {})
        lines += [
            f"Anzahl        : {sf_res.get('anzahl', 0)}",
            f"Carbs/Flask   : {sf_res.get('carbs_pro_flask', 0)} g",
            f"Rezept        : Malto {r0.get('maltodextrin', 0)} g  |  Fructose {r0.get('fructose', 0)} g  |  "
            f"Salz {r0.get('salz', 0)} g  |  Wasser {r0.get('wasser', 0)} ml",
        ]
    lines.append("")

    if e.get("riegel"):
        lines.append("--- RIEGEL ---")
        for r in e["riegel"]:
            lines.append(
                f"  {r['anzahl']}x  {r['name']}"
                f"  (Carbs: {r['carbs_gesamt']} g, Zucker: {r['zucker_gesamt']} g)"
            )
        lines.append("")

    el = e["elektrolyte"]
    lines += [
        "--- ELEKTROLYTE ---",
        f"Produkt       : {el['name']}",
        f"Menge         : {el['portion_g']} g x {el['fuellungen']}  =  {el['gesamt_g']} g",
        "",
        "--- KOFFEIN ---",
        f"Plan          : {e['koffein']['plan']}",
    ]
    if e["koffein"]["caps"]:
        lines.append(f"Kapseln       : {e['koffein']['caps']} Stk.")
    lines.append("")

    mix_iv = e.get("mix_intervalle")
    if mix_iv:
        lines.append("--- TRAININGS-INTERVALLE (MIX) ---")
        total_min = sum(iv.get("dauer_min", 0) for iv in mix_iv)
        for iv in mix_iv:
            anteil = f"{round(iv['dauer_min'] / total_min * 100)}%" if total_min else ""
            extra = ""
            if iv.get("watt"):
                extra += f"  |  {iv['watt']} W"
            if iv.get("hf"):
                extra += f"  |  {iv['hf']} bpm"
            lines.append(
                f"  {iv.get('zone', ''):4s}: {iv.get('dauer_min', 0):3d} min ({anteil:>4s})"
                f"  Carbs/h: {CARBS_PRO_STUNDE.get(iv.get('zone', 'Z2'), 60)} g/h{extra}"
            )
        lines.append("")

    if wetter_info:
        lines += [
            "--- WETTER ---",
            f"Temperatur    : {wetter_info['avg_temp']} °C  (min {wetter_info['min_temp']} / max {wetter_info['max_temp']})",
            f"Sonne         : {sonne_label.get(wetter_info.get('sonne', ''), wetter_info.get('sonne', '-'))}",
            f"Wind          : {wetter_info['avg_wind']} km/h",
            f"Regen         : {wetter_info['sum_regen']} mm",
        ]
        if wetter_punkte and len(wetter_punkte) > 1:
            lines.append("  Verlauf entlang der Route:")
            lines.append(f"  {'km':>5}  {'Uhrzeit':>8}  {'Lat':>9}  {'Lon':>9}  {'Temp':>6}  {'Regen':>7}")
            for pt in wetter_punkte:
                lines.append(
                    f"  {pt.get('km', '?'):>5}  {pt.get('uhrzeit', ''):>8}  "
                    f"{pt.get('lat', ''):>9.4f}  {pt.get('lon', ''):>9.4f}  "
                    f"{pt.get('temp_avg', '?'):>5} °C  {pt.get('regen_mm', '?'):>5} mm"
                )
        lines.append("")

    if resupply_stopps:
        lines.append("--- RESUPPLY-STOPPS ---")
        for i, stopp in enumerate(resupply_stopps):
            needs = []
            if stopp.get("braucht_wasser"): needs.append("Wasser")
            if stopp.get("braucht_carbs"):  needs.append("Carbs")
            lines.append(f"Stopp {i + 1}  –  km {stopp.get('km', '?')}  [{' + '.join(needs)}]")
            if stopp.get("lat"):
                lines.append(f"  Position      : {stopp['lat']:.5f}° N,  {stopp['lon']:.5f}° O")
            if stopp.get("braucht_wasser"):
                lines.append(f"  Wasser        : ~{stopp.get('wasser_refill_ml', '?')} ml auffüllen")
            if stopp.get("braucht_carbs"):
                einkauf = stopp.get("carbs_einkauf_g", 0)
                lines.append(f"  Carbs kaufen  : ~{einkauf} g")
                if einkauf:
                    lines.append(
                        f"    z.B. {math.ceil(einkauf / 35)} Riegel (à 35 g)  oder  "
                        f"{round(einkauf / 25)} Bananen  oder  "
                        f"{round(einkauf / 0.85):.0f} g Gummibärchen"
                    )
            pois = stopp.get("poi_ergebnisse", [])
            if pois:
                lines.append("  Einkaufsstationen:")
                for rank, p in enumerate(pois[:3]):
                    adresse = (
                        p.get("strasse", "") + (f", {p['ort']}" if p.get("ort") else "")
                    ).strip(", ")
                    marker = "  * " if rank == 0 else "    "
                    lines.append(
                        f"{marker}{p['name']} ({p['typ']})  –  km {p['route_km']}  –  {p['dist_m']} m zur Route"
                    )
                    if adresse:
                        lines.append(f"       {adresse}")
            lines.append("")

    lines += [
        "=" * 62,
        "  Ende des Plans",
        "=" * 62,
        "",
        "(c) 2024-2025 Felix Manasov. Alle Rechte vorbehalten.",
        "Nutzung der App erlaubt. Kopieren/Weitergabe des Codes untersagt.",
        "https://github.com/FeDaSy/fueling-planner",
    ]
    return "\n".join(lines)


def erstelle_plan_pdf(e, wetter_info=None, wetter_punkte=None, resupply_stopps=None):
    try:
        from fpdf import FPDF
        from fpdf.enums import XPos, YPos
    except ImportError:
        return b""

    LM  = 10    # left margin mm
    W   = 190   # usable width mm
    LH  = 6.0   # standard line height

    sf_res = e.get("softflasks", {})
    wf     = e.get("wasserflaschen", {})
    sonne_label = {"keine": "Bedeckt", "mittel": "Teils sonnig", "stark": "Vollsonne"}

    def _s(text):
        t = str(text)
        for src, dst in [
            ("–", "-"), ("—", "-"), ("'", "'"),
            (""", '"'), (""", '"'), ("≤", "<="),
            ("≥", ">="), ("→", "->"),
        ]:
            t = t.replace(src, dst)
        return t.encode("latin-1", errors="replace").decode("latin-1")

    def nl(pdf_obj):
        """Move to next line at left margin."""
        pdf_obj.set_x(LM)
        pdf_obj.ln(LH)

    pdf = FPDF(orientation="P", unit="mm", format="A4")
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.set_margins(LM, LM, LM)
    pdf.add_page()

    # ── Helpers ────────────────────────────────────────────────────────────────
    def section(title):
        pdf.ln(3)
        pdf.set_x(LM)
        pdf.set_font("Helvetica", "B", 11)
        pdf.set_fill_color(210, 225, 245)
        pdf.cell(W, 7, _s(title),
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True)
        pdf.set_font("Helvetica", "", 10)
        pdf.ln(1)

    def kv(label, value):
        """Two-column key-value row. Always starts at left margin."""
        pdf.set_x(LM)
        pdf.set_font("Helvetica", "B", 10)
        pdf.cell(62, LH, _s(label + ":"),
                 new_x=XPos.RIGHT, new_y=YPos.TOP)
        pdf.set_font("Helvetica", "", 10)
        # multi_cell must land back at left margin after finishing
        pdf.multi_cell(W - 62, LH, _s(str(value)),
                       new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    def body(text, indent=0):
        pdf.set_x(LM + indent)
        pdf.set_font("Helvetica", "", 10)
        pdf.multi_cell(W - indent, LH, _s(text),
                       new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    def note(text, indent=8):
        pdf.set_x(LM + indent)
        pdf.set_font("Helvetica", "I", 8.5)
        pdf.set_text_color(90, 90, 90)
        pdf.multi_cell(W - indent, 4.5, _s(text),
                       new_x=XPos.LMARGIN, new_y=YPos.NEXT)
        pdf.set_text_color(0, 0, 0)

    def table_row(vals, cws, font_style="", font_size=9, border=1):
        pdf.set_x(LM)
        pdf.set_font("Helvetica", font_style, font_size)
        for i, (v, w) in enumerate(zip(vals, cws)):
            last = (i == len(vals) - 1)
            pdf.cell(w, 5.5, _s(str(v)), border=border, align="C",
                     new_x=XPos.RIGHT if not last else XPos.LMARGIN,
                     new_y=YPos.TOP  if not last else YPos.NEXT)

    # ── Titel ──────────────────────────────────────────────────────────────────
    pdf.set_x(LM)
    pdf.set_font("Helvetica", "B", 18)
    pdf.cell(W, 11, "Cycling Fueling Plan",
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align="C")
    pdf.set_x(LM)
    pdf.set_font("Helvetica", "", 10)
    pdf.cell(W, LH, _s(f"Profil: {e['profil_name']}"),
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align="C")
    pdf.set_x(LM)
    pdf.cell(W, LH,
             _s(f"Zone: {e['zone']}  |  Dauer: {e['dauer_h']} h  |  Temp: {e['temp']} °C"),
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align="C")
    pdf.ln(4)

    # ── Kohlenhydrate ──────────────────────────────────────────────────────────
    section("Kohlenhydrate")
    kv("Gesamt", f"{e['carbs']['gesamt']} g  ({e['carbs']['pro_h']} g/h via {e['carbs']['quelle']})")
    kv("Basis", f"{e['carbs']['basis']} g")
    if e["carbs"].get("hm_bonus"):
        kv("HM-Bonus", f"{e['carbs']['hm_bonus']} g")
    kv("Aus Gels", f"{e['carbs']['aus_gels']} g")
    kv("Aus Riegeln", f"{e['carbs']['aus_riegeln']} g")
    if sf_res.get("ratio_info"):
        kv("Glukose:Fructose", sf_res["ratio_info"][2])

    # ── Wasser ─────────────────────────────────────────────────────────────────
    section("Wasser")
    kv("Gesamt", f"{e['wasser']['gesamt']} ml  ({e['wasser']['pro_h']} ml/h)")
    kv("Aus Gels", f"{e['wasser']['aus_gels']} ml")
    kv("Aus Flaschen (extra)", f"{e['wasser']['zusaetzlich']} ml")
    if wf:
        kv("Auffüllungen", f"{wf.get('auffuellungen', 0)}x  (je ~{wf.get('refill_ml', 0)} ml)")

    # ── Softflasks ─────────────────────────────────────────────────────────────
    section("Softflasks")
    sf_flaschen = sf_res.get("flaschen", [])
    if sf_flaschen:
        for f in sf_flaschen:
            r = f.get("rezept", {})
            pdf.set_x(LM)
            pdf.set_font("Helvetica", "B", 10)
            pdf.cell(0, LH, _s(f"{f['anzahl']}x {f['name']} ({f['volumen_ml']} ml)"),
                     new_x=XPos.LMARGIN, new_y=YPos.NEXT)
            body(
                f"Carbs: {f['carbs_pro_flask']} g  |  Malto: {r.get('maltodextrin', 0)} g  |  "
                f"Fructose: {r.get('fructose', 0)} g  |  Salz: {r.get('salz', 0)} g  |  "
                f"Wasser: {r.get('wasser', 0)} ml",
                indent=6,
            )
    else:
        r0 = sf_res.get("rezept", {})
        kv("Anzahl", sf_res.get("anzahl", 0))
        kv("Rezept", (
            f"Malto {r0.get('maltodextrin', 0)} g  |  Fructose {r0.get('fructose', 0)} g  |  "
            f"Salz {r0.get('salz', 0)} g  |  Wasser {r0.get('wasser', 0)} ml"
        ))

    # ── Riegel ─────────────────────────────────────────────────────────────────
    if e.get("riegel"):
        section("Riegel")
        for r in e["riegel"]:
            body(
                f"{r['anzahl']}x  {r['name']}"
                f"  (Carbs: {r['carbs_gesamt']} g, davon Zucker: {r['zucker_gesamt']} g)",
                indent=4,
            )

    # ── Elektrolyte & Koffein ──────────────────────────────────────────────────
    section("Elektrolyte")
    el = e["elektrolyte"]
    kv("Produkt", el["name"])
    kv("Menge", f"{el['portion_g']} g x {el['fuellungen']}  =  {el['gesamt_g']} g")

    section("Koffein")
    ko = e["koffein"]
    kv("Plan", ko["plan"])
    if ko["caps"]:
        kv("Kapseln", f"{ko['caps']} Stk.")

    # ── Mix-Intervalle ─────────────────────────────────────────────────────────
    mix_iv = e.get("mix_intervalle")
    if mix_iv:
        section("Trainings-Intervalle (Mix)")
        total_min = sum(iv.get("dauer_min", 0) for iv in mix_iv)
        cw  = [22, 30, 32, 30, 34, 26, 16]
        hdr = ["Zone", "Dauer (min)", "Carbs/h", "Wasser/h", "Watt", "HF (bpm)", "Anteil"]
        table_row(hdr, cw, font_style="B")
        for iv in mix_iv:
            anteil = f"{round(iv['dauer_min'] / total_min * 100)}%" if total_min else ""
            table_row([
                iv.get("zone", ""),
                str(iv.get("dauer_min", 0)),
                f"{CARBS_PRO_STUNDE.get(iv.get('zone', 'Z2'), 60)} g/h",
                "-",
                str(iv["watt"]) if iv.get("watt") else "-",
                str(iv["hf"])   if iv.get("hf")   else "-",
                anteil,
            ], cw)

    # ── Wetter ─────────────────────────────────────────────────────────────────
    if wetter_info:
        section("Wetter")
        kv("Temperatur", (
            f"{wetter_info['avg_temp']} °C  "
            f"(min {wetter_info['min_temp']} / max {wetter_info['max_temp']})"
        ))
        kv("Sonne", sonne_label.get(wetter_info.get("sonne", ""), wetter_info.get("sonne", "-")))
        kv("Wind",  f"{wetter_info['avg_wind']} km/h")
        kv("Regen", f"{wetter_info['sum_regen']} mm")

        if wetter_punkte and len(wetter_punkte) > 1:
            pdf.ln(2)
            pdf.set_x(LM)
            pdf.set_font("Helvetica", "B", 10)
            pdf.cell(0, LH, "Wetterverlauf entlang der Route:",
                     new_x=XPos.LMARGIN, new_y=YPos.NEXT)
            cw2 = [20, 28, 54, 32, 28, 28]
            table_row(["km", "Uhrzeit", "Koordinaten", "Temp (°C)", "Wind", "Regen (mm)"],
                      cw2, font_style="B")
            for pt in wetter_punkte:
                table_row([
                    str(pt.get("km", "")),
                    pt.get("uhrzeit", ""),
                    f"{pt.get('lat', 0.0):.4f}, {pt.get('lon', 0.0):.4f}",
                    f"{pt.get('temp_avg', '')} °C",
                    "-",
                    f"{pt.get('regen_mm', '')} mm",
                ], cw2)

    # ── Resupply-Stopps ────────────────────────────────────────────────────────
    if resupply_stopps:
        section("Resupply-Stopps")
        for i, stopp in enumerate(resupply_stopps):
            needs = []
            if stopp.get("braucht_wasser"): needs.append("Wasser")
            if stopp.get("braucht_carbs"):  needs.append("Carbs")
            pdf.set_x(LM)
            pdf.set_font("Helvetica", "B", 10)
            pdf.set_fill_color(240, 240, 248)
            pdf.cell(W, 6.5,
                     _s(f"Stopp {i + 1}  |  km {stopp.get('km', '?')}  [{' + '.join(needs)}]"),
                     new_x=XPos.LMARGIN, new_y=YPos.NEXT, fill=True)
            if stopp.get("lat"):
                note(f"Position: {stopp['lat']:.5f}° N,  {stopp['lon']:.5f}° O")
            if stopp.get("braucht_wasser"):
                body(f"Wasser auffüllen: ~{stopp.get('wasser_refill_ml', '?')} ml", indent=6)
            if stopp.get("braucht_carbs"):
                einkauf = stopp.get("carbs_einkauf_g", 0)
                body(f"Carbs kaufen: ~{einkauf} g", indent=6)
                if einkauf:
                    note(
                        f"z.B. {math.ceil(einkauf / 35)} Riegel (a 35 g)  |  "
                        f"{round(einkauf / 25)} Bananen  |  "
                        f"{round(einkauf / 0.85):.0f} g Gummibaerchen",
                        indent=12,
                    )
            pois = stopp.get("poi_ergebnisse", [])
            if pois:
                pdf.set_x(LM + 6)
                pdf.set_font("Helvetica", "B", 9)
                pdf.cell(0, 5, "Empfohlene Einkaufsstationen:",
                         new_x=XPos.LMARGIN, new_y=YPos.NEXT)
                for rank, p in enumerate(pois[:4]):
                    adresse = (
                        p.get("strasse", "") + (f", {p['ort']}" if p.get("ort") else "")
                    ).strip(", ")
                    marker = "* " if rank == 0 else "  "
                    body(
                        f"{marker}{p['name']} ({p['typ']})"
                        f"  |  km {p['route_km']}  |  {p['dist_m']} m zur Route"
                        + (f"  |  {adresse}" if adresse else ""),
                        indent=12,
                    )
            pdf.ln(2)

    # ── Footer ─────────────────────────────────────────────────────────────────
    pdf.set_x(LM)
    pdf.set_font("Helvetica", "I", 8)
    pdf.set_text_color(160, 160, 160)
    pdf.cell(W, 5,
             _s(f"Erstellt mit Cycling Fueling Planner  |  {datetime.now().strftime('%d.%m.%Y %H:%M')}"),
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align="C")
    pdf.set_x(LM)
    pdf.cell(W, 4,
             _s("(c) 2024-2025 Felix Manasov. Alle Rechte vorbehalten. Nutzung der App erlaubt, "
                "Kopieren/Weitergabe des Codes untersagt."),
             new_x=XPos.LMARGIN, new_y=YPos.NEXT, align="C")

    return bytes(pdf.output())


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
if "resupply_stopps" not in st.session_state:
    st.session_state.resupply_stopps = None
if "wetter_punkte" not in st.session_state:
    st.session_state.wetter_punkte = []
if "intensitaet_modus" not in st.session_state:
    st.session_state.intensitaet_modus = "Zone manuell wählen"
if "intervalle" not in st.session_state:
    st.session_state.intervalle = [{"zone": "Z2", "watt": None, "hf": None, "dauer_min": 60}]

profil = st.session_state.profil

# ══════════════════════════════════════════════════════════════════════════════
# SIDEBAR – PROFIL EINSTELLUNGEN
# ══════════════════════════════════════════════════════════════════════════════

with st.sidebar:
    st.title("⚙️ Mein Profil")

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

    # ── Körpergewicht & Trainingsstatus (für Glykogen-Bilanz) ──
    cols_kg = st.columns(2)
    profil["koerpergewicht_kg"] = cols_kg[0].number_input(
        "Körpergewicht (kg)",
        min_value=40, max_value=150,
        value=int(profil.get("koerpergewicht_kg", 75)), step=1,
        help=(
            "Dein Körpergewicht in kg. Wird für die Glykogen-Speicherbilanz benötigt: "
            "pro kg Körpergewicht speicherst du je nach Trainingsstatus 6–13 g Kohlenhydrate "
            "als Glykogen (Muskel + Leber). Hat KEINEN Einfluss auf Schweißrate oder "
            "Kohlenhydratbedarf in der bestehenden Berechnung."
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
        st.info(
            f"➡️ **Konstante Zufuhr:** {konstant_g_h} g/h × {e['dauer_h']} h "
            f"= **{gesamt_konstant} g gesamt**"
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

        # ── Cardiac Drift ──
        drift_rate = 0.0
        if e["dauer_h"] >= 2:
            drift_auto = cardiac_drift_rate_auto(e["temp"], ist_indoor, e["zone"])
            drift_pct_auto = round(drift_auto * 100, 1)
            # Slider braucht ≥ 1 als min — sehr niedrige Auto-Werte aufrunden
            drift_pct_default = max(1, int(round(drift_pct_auto)))
            mit_drift = st.checkbox(
                "🫀 Cardiac Drift einberechnen",
                value=False,
                help=(
                    "Bei gleichbleibender Wattzahl steigt die Herzfrequenz über Zeit "
                    "(Dehydrierung + Hitzeakkumulation). Das erhöht den RER und damit "
                    "den Kohlenhydratverbrauch pro Stunde leicht.\n\n"
                    "**Physiologische Grundlage:** Coyle & González-Alonso (2001), "
                    "Wingo et al. (2012) – kardiovaskulärer Drift bei längeren "
                    "Ausdauerbelastungen, verstärkt durch höhere Intensität.\n\n"
                    f"Auto-Schätzung für Zone **{e['zone']}**, {e['temp']}°C "
                    f"{'(Indoor)' if ist_indoor else '(Outdoor)'}: "
                    f"**+{drift_pct_auto}% pro Stunde**."
                ),
            )
            if mit_drift:
                drift_rate = st.slider(
                    "Drift-Rate (% Mehrverbrauch pro Stunde)",
                    min_value=1, max_value=15,
                    value=min(15, drift_pct_default),
                    step=1,
                    help=(
                        f"Auto-Schätzung: **{drift_pct_auto}%/h** "
                        f"(Zone {e['zone']}, {'Indoor' if ist_indoor else 'Outdoor'}, "
                        f"{e['temp']}°C).\n\n"
                        "**Zonen-Einfluss:** Z1/Z2: niedriger Drift (gemütliches Tempo). "
                        "Z3: spürbar (Schwelle). Z4/Z5: starker Drift "
                        "(hohe Wärmelast + schnelle Glykogen-Entleerung).\n\n"
                        "**Temperatur-Einfluss:** Kühl: 2–3%. Moderat: 3–5%. "
                        "Warm: 5–7%. Heiß: 7–10%+."
                    ),
                ) / 100.0
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
    plan_text = erstelle_plan_text(e, w, wp, rs, konstant_g_h=_export_konstant)
    pdf_bytes = erstelle_plan_pdf(e, w, wp, rs)
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
