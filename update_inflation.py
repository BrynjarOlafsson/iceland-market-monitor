#!/usr/bin/env python3
"""Update market_data.csv inflation_yoy from Statistics Iceland's PXWeb API.

`inflation_yoy` contains *percentage points* (e.g. 5.6 means 5.6%).
All other market series remain unchanged. New CPI months may be appended
as CPI-only rows, so inflation can advance before the monthly CAPE update.

Run from the repository root:
    python update_inflation.py

Optional offline test:
    python update_inflation.py --response-file example_pxweb_response.json --csv market_data.csv
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import os
from pathlib import Path
import re
import tempfile
import urllib.error
import urllib.request

URL = "https://px.hagstofa.is/pxis/api/v1/is/Efnahagur/visitolur/1_vnv/1_vnv/VIS01000.px"
REQUEST = {
    "query": [
        {"code": "Vísitala", "selection": {"filter": "item", "values": ["CPI"]}},
        {"code": "Liður", "selection": {"filter": "item", "values": ["change_A"]}},
    ],
    "response": {"format": "json"},
}
MONTH = re.compile(r"^(\d{4})M(\d{1,2})$")
ISO_MONTH = re.compile(r"^\d{4}-(0[1-9]|1[0-2])$")


def fetch_api_response() -> dict:
    payload = json.dumps(REQUEST, ensure_ascii=False).encode("utf-8")
    request = urllib.request.Request(
        URL, data=payload,
        headers={"Content-Type": "application/json; charset=utf-8", "Accept": "application/json",
                 "User-Agent": "IcelandMarketMonitor/0.2 (public CPI data integration)"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=35) as response:
            result = json.load(response)
    except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError) as exc:
        raise RuntimeError(f"Statistics Iceland API request failed: {exc}") from exc
    if not isinstance(result, dict):
        raise ValueError("Unexpected PXWeb response: expected JSON object")
    return result


def parse_month(raw: str) -> str | None:
    raw = str(raw).strip()
    if ISO_MONTH.fullmatch(raw):
        return raw
    match = MONTH.fullmatch(raw)
    if match and 1 <= int(match.group(2)) <= 12:
        return f"{match.group(1)}-{int(match.group(2)):02d}"
    return None


def parse_pxweb(data: dict) -> dict[str, float]:
    """PXWeb 'json' format: columns metadata, data [{key: [...], values: [...]}]."""
    cols, records = data.get("columns"), data.get("data")
    if not isinstance(cols, list) or not isinstance(records, list) or not records:
        raise ValueError("Unexpected PXWeb JSON structure (columns/data missing or empty)")
    code_list = [str(c.get("code", "")) for c in cols]
    output = {}
    for row in records:
        keys, values = row.get("key"), row.get("values")
        if not isinstance(keys, list) or len(keys) != len(cols) or not isinstance(values, list) or len(values) != 1:
            raise ValueError("Unexpected PXWeb record shape")
        # Reject any unexpected CPI or indicator values, even if the API query is modified.
        for key, code in zip(keys, code_list):
            if code == "Vísitala" and key != "CPI":
                raise ValueError(f"Wrong index in API response: {key}")
            if code == "Liður" and key != "change_A":
                raise ValueError(f"Wrong CPI measure in API response: {key}")
        months = [month for k in keys if (month := parse_month(k)) is not None]
        if len(months) != 1:
            raise ValueError(f"Cannot uniquely identify observation month: {keys!r}")
        raw = values[0]
        if raw in (None, "", ".", "..", "..."):
            continue  # PXWeb explicitly marks some early annual changes as missing.
        try:
            value = float(str(raw).strip().replace(",", "."))
        except ValueError as exc:
            raise ValueError(f"Unparseable CPI inflation rate for {months[0]}: {raw!r}") from exc
        if not math.isfinite(value) or not (-50 <= value <= 100):
            raise ValueError(f"Implausible CPI annual percentage change for {months[0]}: {value}")
        if months[0] in output:
            raise ValueError(f"Duplicate CPI month: {months[0]}")
        output[months[0]] = value
    if len(output) < 12:
        raise ValueError(f"Too few valid observations returned ({len(output)}); refuse to publish")
    return output


def merge_csv(path: Path, inflation: dict[str, float]) -> tuple[int, int, str]:
    with path.open(encoding="utf-8-sig", newline="") as handle:
        reader = csv.DictReader(handle)
        cols = reader.fieldnames
        if not cols or cols[0] != "month" or "inflation_yoy" not in cols:
            raise ValueError("market_data.csv requires month and inflation_yoy columns")
        rows = list(reader)
    by_month = {}
    for row in rows:
        month = row["month"]
        if not ISO_MONTH.fullmatch(month) or month in by_month:
            raise ValueError(f"Bad or duplicate CSV month: {month!r}")
        by_month[month] = row
    if not by_month:
        raise ValueError("CSV has no existing market data")
    first_month = min(by_month)
    changed = 0
    appended = 0
    for month, value in sorted(inflation.items()):
        if month < first_month:
            continue  # Published market-data history starts in March 1995.
        text_value = format(value, ".12g")
        if month not in by_month:
            by_month[month] = {column: "" for column in cols}
            by_month[month]["month"] = month
            appended += 1
        if by_month[month].get("inflation_yoy") != text_value:
            by_month[month]["inflation_yoy"] = text_value
            changed += 1
    if changed == 0 and appended == 0:
        return 0, 0, max(inflation)
    # Atomic write: if parsing, validation or I/O fails the published CSV stays intact.
    temp_name = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="", dir=path.parent,
                                         prefix=".inflation_", suffix=".csv", delete=False) as handle:
            temp_name = handle.name
            writer = csv.DictWriter(handle, fieldnames=cols, lineterminator="\n")
            writer.writeheader()
            writer.writerows(by_month[month] for month in sorted(by_month))
        os.replace(temp_name, path)
    finally:
        if temp_name is not None and os.path.exists(temp_name):
            os.unlink(temp_name)
    return changed, appended, max(inflation)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv", type=Path, default=Path("market_data.csv"))
    parser.add_argument("--response-file", type=Path, help="Read saved PXWeb response instead of fetching API (test only)")
    args = parser.parse_args()
    if args.response_file:
        with args.response_file.open(encoding="utf-8") as handle:
            response = json.load(handle)
    else:
        response = fetch_api_response()
    inflation = parse_pxweb(response)
    changed, appended, newest = merge_csv(args.csv, inflation)
    print(f"CPI data: {len(inflation)} valid months; latest {newest}, {inflation[newest]:.2f}%")
    print(f"CSV updated: {changed} inflation values changed; {appended} new month rows appended")


if __name__ == "__main__":
    main()
