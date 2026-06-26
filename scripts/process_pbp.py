#!/usr/bin/env python3
"""
CMS Medicare PBP Data Pipeline
================================
Downloads CMS PBP Benefits JSON data for a given year, processes all plan
files, and injects the updated data constants directly into the HTML app.

Usage:
  python scripts/process_pbp.py --year 2026 --html pbp-plan-comparator.html

Requirements:
  pip install requests  (or uses built-in urllib)
"""

import argparse
import io
import json
import os
import re
import sys
import urllib.request
import zipfile
from datetime import datetime, timezone

# ─── BENEFIT CATEGORY LABELS ────────────────────────────────────────────────
BENEFIT_LABELS = {
    "1a": "Inpatient Hospital", "1b": "Skilled Nursing Facility",
    "2": "Physician/Outpatient", "3-1": "Emergency Care",
    "3-2": "Urgently Needed Care", "3-3": "Ambulance",
    "3-4": "Outpatient Mental Health", "4a": "Part B Drugs",
    "4b": "Basic Vision Exam", "5a": "Basic Hearing",
    "5b": "Inpatient Psychiatric", "6": "Preventive Services",
    "1a1": "Dental (Preventive)", "1a2": "Dental (Comprehensive)",
    "1a3": "Dental (Orthodontia)", "1b1": "Dentures",
    "1b2": "Dental (Other)", "4c1": "Routine Vision Exam",
    "4c2": "Eyeglasses/Contact Lenses", "4c3": "Contact Lenses",
    "7b1": "Hearing Aids", "7b2": "Hearing Exam (Routine)",
    "7f": "Fitness Benefit", "10b1": "Over-the-Counter Items",
    "10b2": "OTC Items (Expanded)", "13a": "Transportation (Non-Emergency)",
    "13b": "Transportation (Routine)", "14c2": "Meals (Post-Discharge)",
    "14c4": "Meals (Chronic)", "14c8": "Nutritional Meals",
    "14c16": "Food/Produce Allowance", "14c21": "Healthy Food Allowance",
    "19b3": "Telehealth/Remote Monitoring",
    "2-1": "Mental Health (Outpatient)", "3-5": "Substance Use Disorder",
}

# Cost-sharing category map: cs_key → (category_code, label)
CS_CAT_MAP = {
    "er":   "3-1",   # Emergency Room
    "uc":   "3-2",   # Urgent Care
    "amb":  "3-3",   # Ambulance
    "phys": "2",     # Physician / Outpatient
    "mh":   "3-4",   # Mental Health
    "prev": "6",     # Preventive
    "inp":  "1a",    # Inpatient Hospital
    "img":  "2",     # Imaging (same as physician in most MA plans)
    "lab":  "2",     # Lab (same as physician in most MA plans)
}


# ─── HELPERS ────────────────────────────────────────────────────────────────

def safe_float(val):
    try:
        return float(val) if val not in (None, "", "N/A") else None
    except (TypeError, ValueError):
        return None


def extract_copay(component):
    """Extract dollar copay from a CopaymentComponent dict."""
    if not component:
        return None
    flag = component.get("bdCopaymentAmountYesNoMinMax")
    if flag == "1":
        return safe_float(component.get("bdCopaymentAmount"))
    if flag == "3":
        lo = safe_float(component.get("bdCopaymentMinAmount"))
        hi = safe_float(component.get("bdCopaymentMaxAmount"))
        if lo is not None and hi is not None:
            return (lo + hi) / 2
    return None


def extract_coinsurance(component):
    """Extract coinsurance % from a CoinsuranceComponent dict."""
    if not component:
        return None
    flag = component.get("bdCoinsuranceAmountYesNoMinMax")
    if flag == "1":
        return safe_float(component.get("bdCoinsuranceAmount"))
    if flag == "3":
        lo = safe_float(component.get("bdCoinsuranceMinAmount"))
        hi = safe_float(component.get("bdCoinsuranceMaxAmount"))
        if lo is not None and hi is not None:
            return (lo + hi) / 2
    return None


def extract_tier_copay(component):
    """Extract per-stay/visit copay from TierCopaymentComponent."""
    if not component:
        return None
    amt = safe_float(component.get("bdCopaymentTier1Amt"))
    return amt


def fmt_tier_cost(cop, coins):
    """Format a tier cost as '$X' or 'X%'."""
    if cop is not None and cop == 0:
        return "$0"
    if cop is not None and cop > 0:
        return f"${int(cop)}" if cop == int(cop) else f"${cop:.2f}"
    if coins is not None and coins > 0:
        return f"{int(coins)}%"
    return "$0"


# ─── PLAN EXTRACTION ────────────────────────────────────────────────────────

def extract_plan(data, filename):
    """Convert a raw CMS PBP JSON object to the slim plan format."""
    try:
        if not isinstance(data, dict) or not data.get("pbp"):
            return None
        pbp = data["pbp"][0]
        chars = pbp.get("planCharacteristics", {}) or {}

        # Identity
        contract_id = pbp.get("contractId", "")
        plan_id_raw = pbp.get("planId", "")
        segment_id = pbp.get("segmentId", 0)
        plan_uid = f"{contract_id}-{plan_id_raw}-{str(segment_id).zfill(3)}"

        name = chars.get("planName", "").strip()
        org = (chars.get("organizationMarketingName") or chars.get("contractLegalName", "")).strip()
        geo = chars.get("geographicName", "").strip()
        ptype = chars.get("planTypeLabel", "").strip()

        if not plan_uid or not name:
            return None

        rx = chars.get("isOfferRx", "No") == "Yes"
        snp = chars.get("isSnp", "No") == "Yes"
        snp_type = chars.get("snpType", "")

        # MOOP & Deductibles
        plcs = pbp.get("planLevelCostSharing", {}) or {}
        moop = moop_oon = ded = part_b_red = None

        if plcs:
            moop_obj = (plcs.get("maxEnrolleeCostLimit") or {})
            moop_dets = moop_obj.get("maxEnrolleeCostLimitDetails", {}) or {}
            moop = safe_float(moop_dets.get("inNWMoopAmount")) or safe_float(moop_dets.get("combinedMoopAmount"))
            moop_oon = safe_float(moop_dets.get("outOfNWMoopAmount"))

            ded_obj = (plcs.get("planDeductible") or {})
            ded_dets = ded_obj.get("planDeductibleDetails", {}) or {}
            ded = safe_float(ded_dets.get("inNetworkDedAmount"))

            lcs_dets = plcs.get("planLevelCostSharingDetails") or {}
            part_b_red = safe_float(lcs_dets.get("csbPartBPrmReducAmt"))

        # Rx deductible & tiers
        rx_ded = rx_tiers = None
        rx_mail = False
        rx_tc = []

        rx_obj = pbp.get("rx", {}) or {}
        if rx_obj:
            rx_details = rx_obj.get("rxDetails", {}) or {}
            rx_setup = rx_details.get("rxSetup", {}) or {}
            rx_setup_dets = rx_setup.get("rxSetupDetails", {}) or {}
            rx_cs = (rx_setup.get("rxCostShare") or {})
            rx_cs_dets = rx_cs.get("rxCostShareDetails", {}) or {}

            rx_ded = safe_float(rx_cs_dets.get("costShareDeductibleAmount"))
            rx_tiers = rx_setup_dets.get("tierCount")
            rx_mail = rx_setup_dets.get("mailOrderPharmacyNetwork") == "1"

            tiers_obj = rx_setup.get("rxTiers", {}) or {}
            for i in range(1, 8):
                tkey = f"rxTier{i}"
                tier = tiers_obj.get(tkey)
                if not tier:
                    continue
                pre_icl = tier.get(f"{tkey}PreIcl", {}) or {}
                dets = pre_icl.get(f"{tkey}PreIclDetails", {}) or {}
                cop = safe_float(dets.get("preIclRetailOneMonthCopayment"))
                coins = safe_float(dets.get("preIclRetailOneMonthCoinsurance"))
                rx_tc.append(fmt_tier_cost(cop, coins))

        # Benefits
        med_ben = []
        supp_ben = []
        bo = pbp.get("benefitOfferings", {}) or {}
        if bo:
            medicare = bo.get("medicare", {}) or {}
            for item in (medicare.get("medicareBenefitOfferingDetails") or []):
                if item.get("boInNetwork") == "1":
                    med_ben.append(item.get("categoryCode", ""))

            non_medicare = bo.get("nonMedicare", {}) or {}
            for item in (non_medicare.get("nonMedicareBenefitOfferingDetails") or []):
                if item.get("boInNetwork") == "1":
                    supp_ben.append(item.get("categoryCode", ""))

        # Cost sharing per service type
        cs = {}
        bd = pbp.get("benefitDetails", {}) or {}
        for info in (bd.get("benefitDetailsInfo") or []):
            cat = info.get("categoryCode", "")
            bdet = info.get("benefitDetails", {}) or {}
            if not bdet:
                continue

            # Determine which cs key(s) this category maps to
            cs_keys = [k for k, v in CS_CAT_MAP.items() if v == cat]
            if not cs_keys:
                continue

            cop_comp = bdet.get("CopaymentComponent", {}) or {}
            coins_comp = bdet.get("CoinsuranceComponent", {}) or {}
            tier_cop_comp = bdet.get("TierCopaymentComponent", {}) or {}
            tier_coins_comp = bdet.get("TierCoinsuranceComponent", {}) or {}

            # For inpatient (1a): use tier copay amount
            if cat == "1a":
                inp_cop = extract_tier_copay(tier_cop_comp)
                if inp_cop is not None:
                    cs["inp"] = {"cop": inp_cop}
                continue

            cop_val = extract_copay(cop_comp)
            coins_val = extract_coinsurance(coins_comp)
            if coins_val is None:
                # Try tier coinsurance
                tcoins_flag = (tier_coins_comp or {}).get("bdCoinsurancePercentageYesNo")
                if tcoins_flag == "2":
                    coins_val = 20  # standard 20% default when flag says coinsurance applies

            for k in cs_keys:
                if k not in cs:
                    if cop_val is not None:
                        cs[k] = {"cop": cop_val}
                    elif coins_val is not None:
                        cs[k] = {"pct": coins_val}

        return {
            "id": plan_uid,
            "name": name,
            "org": org,
            "geo": geo,
            "type": ptype,
            "rx": rx,
            "snp": snp,
            "snpType": snp_type,
            "moop": moop,
            "moopOon": moop_oon,
            "ded": ded,
            "rxDed": rx_ded,
            "rxTiers": rx_tiers,
            "rxMail": rx_mail,
            "partBRed": part_b_red,
            "medBen": [c for c in med_ben if c],
            "suppBen": [c for c in supp_ben if c],
            "rxTC": rx_tc,
            "cs": cs,
        }
    except Exception:
        return None


# ─── STATE INDEX ─────────────────────────────────────────────────────────────

STATE_NAMES = {
    "Alabama": "AL", "Alaska": "AK", "Arizona": "AZ", "Arkansas": "AR",
    "California": "CA", "Colorado": "CO", "Connecticut": "CT", "Delaware": "DE",
    "Florida": "FL", "Georgia": "GA", "Hawaii": "HI", "Idaho": "ID",
    "Illinois": "IL", "Indiana": "IN", "Iowa": "IA", "Kansas": "KS",
    "Kentucky": "KY", "Louisiana": "LA", "Maine": "ME", "Maryland": "MD",
    "Massachusetts": "MA", "Michigan": "MI", "Minnesota": "MN",
    "Mississippi": "MS", "Missouri": "MO", "Montana": "MT", "Nebraska": "NE",
    "Nevada": "NV", "New Hampshire": "NH", "New Jersey": "NJ",
    "New Mexico": "NM", "New York": "NY", "North Carolina": "NC",
    "North Dakota": "ND", "Ohio": "OH", "Oklahoma": "OK", "Oregon": "OR",
    "Pennsylvania": "PA", "Rhode Island": "RI", "South Carolina": "SC",
    "South Dakota": "SD", "Tennessee": "TN", "Texas": "TX", "Utah": "UT",
    "Vermont": "VT", "Virginia": "VA", "Washington": "WA",
    "West Virginia": "WV", "Wisconsin": "WI", "Wyoming": "WY",
    "District of Columbia": "DC", "Puerto Rico": "PR", "Guam": "GU",
    "Virgin Islands": "VI", "American Samoa": "AS",
    "Northern Mariana Islands": "MP",
}

# Sort longest first to prevent "Virginia" matching before "West Virginia"
SORTED_STATES = sorted(STATE_NAMES.keys(), key=len, reverse=True)
NATIONWIDE_GEO_KEYWORDS = {"national", "nationwide", "all states", "all 50", "50 states"}


def classify_plan_geo(geo_lower):
    """Return 'nationwide', state abbreviation, or None (county-level)."""
    for kw in NATIONWIDE_GEO_KEYWORDS:
        if kw in geo_lower:
            return "nationwide"
    for state_name in SORTED_STATES:
        abbr = STATE_NAMES[state_name]
        # Exact match or name appears as a standalone word
        if geo_lower == state_name.lower():
            return abbr
        # State abbreviation at end after comma: ", VA" style
        if f", {abbr.lower()}" in geo_lower:
            return abbr
        # Full state name contained, but guard against substring issues
        if state_name.lower() in geo_lower:
            return abbr
    return None  # county/region level


def build_state_index(plans):
    """Build {n:[nationwide_idx], s:{abbr:[idx]}, c:[{i,geo}]}."""
    n = []
    s = {}
    c = []

    for i, plan in enumerate(plans):
        geo = plan.get("geo", "").strip()
        geo_lower = geo.lower()
        classification = classify_plan_geo(geo_lower)

        if classification == "nationwide":
            n.append(i)
        elif classification:
            s.setdefault(classification, []).append(i)
        else:
            c.append({"i": i, "geo": geo})

    return {"n": n, "s": s, "c": c}


# ─── DOWNLOAD ────────────────────────────────────────────────────────────────

def download_cms_zip(year, timeout=180):
    url = f"https://www.cms.gov/files/zip/pbp-benefits-{year}-json.zip"
    print(f"  Downloading: {url}", flush=True)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        data = resp.read()
    print(f"  Downloaded {len(data)/1024/1024:.1f} MB", flush=True)
    return data


def process_zip(zip_bytes):
    plans = []
    with zipfile.ZipFile(io.BytesIO(zip_bytes)) as zf:
        json_files = [n for n in zf.namelist() if n.lower().endswith(".json")]
        total = len(json_files)
        print(f"  Processing {total} plan files...", flush=True)
        for idx, fname in enumerate(json_files):
            try:
                with zf.open(fname) as fh:
                    data = json.load(fh)
                plan = extract_plan(data, fname)
                if plan:
                    plans.append(plan)
            except Exception:
                pass
            if (idx + 1) % 1000 == 0:
                print(f"    {idx+1}/{total}...", flush=True)
    return plans


# ─── HTML INJECTION ──────────────────────────────────────────────────────────

def inject_into_html(html_path, plans, state_index, year):
    with open(html_path, "r", encoding="utf-8") as f:
        html = f.read()

    ap_json = json.dumps(plans, separators=(",", ":"), ensure_ascii=False)
    si_json = json.dumps(state_index, separators=(",", ":"), ensure_ascii=False)
    bl_json = json.dumps(BENEFIT_LABELS, separators=(",", ":"), ensure_ascii=False)
    updated_at = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

    # Replace AP (all plans array)
    html = re.sub(
        r'const AP=\[.*?\];',
        f'const AP={ap_json};',
        html, count=1, flags=re.DOTALL
    )

    # Replace SI (state index)
    html = re.sub(
        r'const SI=\{.*?\};',
        f'const SI={si_json};',
        html, count=1, flags=re.DOTALL
    )

    # Replace BL (benefit labels)
    html = re.sub(
        r'const BL=\{.*?\};',
        f'const BL={bl_json};',
        html, count=1, flags=re.DOTALL
    )

    # Replace or inject DATA_META comment block
    meta_block = f'<!-- DATA_META year="{year}" updated="{updated_at}" plans="{len(plans)}" -->'
    if '<!-- DATA_META' in html:
        html = re.sub(r'<!-- DATA_META.*?-->', meta_block, html)
    else:
        html = html.replace('<title>', f'{meta_block}\n<title>', 1)

    # Update all year references and plan counts throughout the HTML
    plan_count = f"{len(plans):,}"

    # <title> and toolbar heading
    html = re.sub(r'20\d\d Medicare Plan Advisor', f'{year} Medicare Plan Advisor', html)

    # <h1> heading (e.g. "2026 <span>Medicare Plan</span> Advisor")
    html = re.sub(r'\b20\d\d\b(<\s*span[^>]*>\s*Medicare Plan)', f'{year}\\1', html)

    # zip-desc paragraph (HTML + JS string)
    html = re.sub(
        r'all 20\d\d Medicare plans',
        f'all {year} Medicare plans',
        html
    )

    # zip-meta coverage line  (e.g. "8,083 CMS-filed 2026 Medicare")
    html = re.sub(
        r'[\d,]+ CMS-filed 20\d\d Medicare[^<]*',
        f'{plan_count} CMS-filed {year} Medicare &amp; Part D plans across the US',
        html
    )

    # stats row "Total Plans" number
    html = re.sub(
        r'(<div class="stat-num">)\d[\d,]*(<\/div><div class="stat-lbl">Total Plans)',
        f'\\g<1>{plan_count}\\2',
        html
    )

    with open(html_path, "w", encoding="utf-8") as f:
        f.write(html)

    print(f"  Injected {len(plans):,} plans into {html_path}")
    print(f"  State index: {len(state_index['n'])} nationwide, "
          f"{sum(len(v) for v in state_index['s'].values())} state-level, "
          f"{len(state_index['c'])} county-level")
    print(f"  Updated at: {updated_at}")


# ─── MAIN ────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Update CMS Medicare PBP data in the HTML app")
    parser.add_argument("--year", type=int, default=datetime.now().year,
                        help="Year to fetch (e.g. 2026 downloads pbp-benefits-2026-json.zip)")
    parser.add_argument("--html", default="pbp-plan-comparator.html",
                        help="Path to the HTML app file")
    parser.add_argument("--zip", default=None,
                        help="Path to a locally downloaded .zip (skips download)")
    args = parser.parse_args()

    print(f"\n{'='*50}")
    print(f" Medicare PBP Data Pipeline — {args.year}")
    print(f"{'='*50}\n")

    # Step 1: Get zip data
    if args.zip:
        print(f"[1/3] Loading local zip: {args.zip}")
        with open(args.zip, "rb") as f:
            zip_bytes = f.read()
    else:
        print(f"[1/3] Downloading CMS data for {args.year}...")
        try:
            zip_bytes = download_cms_zip(args.year)
        except Exception as e:
            print(f"  ERROR: {e}")
            sys.exit(1)

    # Step 2: Process plans
    print(f"\n[2/3] Processing plan files...")
    plans = process_zip(zip_bytes)
    print(f"  Extracted {len(plans):,} valid plans")

    if not plans:
        print("  ERROR: No plans extracted. Check the zip format.")
        sys.exit(1)

    state_index = build_state_index(plans)

    # Step 3: Inject into HTML
    print(f"\n[3/3] Updating HTML app...")
    if not os.path.exists(args.html):
        print(f"  ERROR: HTML file not found: {args.html}")
        sys.exit(1)

    inject_into_html(args.html, plans, state_index, args.year)

    print(f"\n✓ Done! {args.html} is ready to deploy.\n")


if __name__ == "__main__":
    main()
