#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ZimVAT - Automated Zimbabwe VAT Return System (ZIMRA VAT 10)
============================================================
Captures accounting transactions, validates ZIMRA fiscal evidence, computes
output tax, allowable input tax, adjustments and special transactions, and
produces a VAT 10-style summary with a full auditable calculation trail.

RUN (VS Code terminal):
    python zimvat_app.py                          # desktop UI (Tkinter)
    python zimvat_app.py --demo                   # seed worked example, then UI
    python zimvat_app.py --demo --report 2025-01  # console report, no GUI

Data: SQLite (zimvat_data.db) + settings (zimvat_config.json).
DISCLAIMER: rates, thresholds and schedules change with each Finance Act -
verify against current ZIMRA public notices before filing.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import sqlite3
from dataclasses import dataclass, asdict
from datetime import date, datetime
from decimal import Decimal, ROUND_HALF_UP
from enum import Enum
from typing import List, Optional, Tuple

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP_TITLE = "ZimVAT - Zimbabwe VAT Return Automation (ZIMRA VAT 10)"
DB_FILE = "zimvat_data.db"
CONFIG_FILE = "zimvat_config.json"

STANDARD_RATE = Decimal("0.15")          # 15% since 1 Jan 2023
D0 = Decimal("0")
ONE = Decimal(1)

# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------

def q2(d: Decimal) -> Decimal:
    return d.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)


def to_d(x) -> Decimal:
    return Decimal(str(x))


def money(d: Decimal) -> str:
    return f"{q2(d):,.2f}"


def pct(ratio: Decimal) -> str:
    return f"{(ratio * 100).quantize(Decimal('0.01'))}%"


def tr(s: str, n: int) -> str:
    s = s or ""
    return s if len(s) <= n else s[: n - 2] + ".."


def vat_of(amount: Decimal, inclusive: bool, rate: Decimal) -> Decimal:
    """VAT portion of an amount (15/115 when tax-inclusive)."""
    if inclusive:
        return q2(amount * rate / (ONE + rate))
    return q2(amount * rate)


def base_of(amount: Decimal, inclusive: bool, vat: Decimal) -> Decimal:
    return amount - vat if inclusive else amount


def period_shift(period: str, k: int) -> str:
    y, m = int(period[:4]), int(period[5:7])
    idx = y * 12 + (m - 1) + k
    return f"{idx // 12:04d}-{idx % 12 + 1:02d}"


def period_options(count: int = 36) -> List[str]:
    now = date.today()
    cur = f"{now.year:04d}-{now.month:02d}"
    return [period_shift(cur, -i) for i in range(count)]


def due_date_of(period: str, filing_day: int = 25) -> date:
    """VAT 10 is due by the 25th of the month following the tax period."""
    y, m = int(period[:4]), int(period[5:7])
    y2, m2 = (y + 1, 1) if m == 12 else (y, m + 1)
    return date(y2, m2, filing_day)

# ----------------------------------------------------------------------------
# Domain
# ----------------------------------------------------------------------------

class TxType(str, Enum):
    SALE_STD = "SALE_STD"
    SALE_ZERO = "SALE_ZERO"
    SALE_EXEMPT = "SALE_EXEMPT"
    DEEMED = "DEEMED"
    CREDIT_NOTE = "CREDIT_NOTE"
    DEBIT_NOTE = "DEBIT_NOTE"
    PURCHASE = "PURCHASE"
    CAPITAL_GOOD = "CAPITAL_GOOD"
    ENTERTAINMENT = "ENTERTAINMENT"
    PMV = "PMV"
    IMPORT = "IMPORT"
    SECOND_HAND = "SECOND_HAND"
    BAD_DEBT = "BAD_DEBT"
    WHT_VAT = "WHT_VAT"


TX_LABELS = {
    "SALE_STD": "Sale - standard rated (15%)",
    "SALE_ZERO": "Sale - zero rated",
    "SALE_EXEMPT": "Sale - exempt",
    "DEEMED": "Deemed supply - own use / gifts",
    "CREDIT_NOTE": "Credit note - sales (FCN)",
    "DEBIT_NOTE": "Debit note - sales (FDN)",
    "PURCHASE": "Purchase - local (registered vendor)",
    "CAPITAL_GOOD": "Purchase - capital goods",
    "IMPORT": "Import - VAT per bill of entry (CF47)",
    "SECOND_HAND": "Purchase - second-hand goods (unregistered seller)",
    "ENTERTAINMENT": "Purchase - entertainment (blocked)",
    "PMV": "Purchase - passenger motor vehicle (blocked)",
    "BAD_DEBT": "Adjustment - bad debt written off (VAT portion)",
    "WHT_VAT": "Adjustment - withholding VAT credit (certificate)",
}
LABEL_TO_TX = {lbl: TxType(code) for code, lbl in TX_LABELS.items()}


@dataclass
class Transaction:
    id: Optional[int]
    tx_type: TxType
    date: str                       # ISO YYYY-MM-DD
    description: str
    amount: float
    currency: str = "USD"
    fx_rate: float = 1.0
    vat_inclusive: bool = False
    tax_code: str = "B"             # fiscal codes A/B/C/D/E
    supplier_name: str = ""
    supplier_vat_no: str = ""
    fiscal_invoice_no: str = ""
    attribution: str = "MIXED"      # TAXABLE / EXEMPT / MIXED
    evidence_ref: str = ""
    months_elapsed: int = 0
    notes: str = ""

    @property
    def period(self) -> str:
        return self.date[:7]

    @property
    def amount_functional(self) -> Decimal:
        return to_d(self.amount) * to_d(self.fx_rate)


@dataclass
class AuditLine:
    step: int
    category: str        # OUTPUT / INPUT / INPUT DENIED / ADJUSTMENT / SUMMARY
    tx_ref: str
    description: str
    rule: str
    base: Decimal = D0
    tax: Decimal = D0
    note: str = ""


@dataclass
class VATReturnResult:
    period: str
    entity: str
    tin: str
    vat_no: str
    currency: str
    due_date: str
    boxes: List[Tuple[str, str, str]]
    audit: List[AuditLine]
    warnings: List[str]
    total_supplies: Decimal
    output_tax: Decimal
    total_input_tax: Decimal
    net_vat: Decimal
    ratio: Decimal
    surcharge: Decimal
    interest: Decimal
    days_overdue: int


@dataclass
class AppConfig:
    company_name: str = "Kombayi Wholesalers (Pvt) Ltd"
    tin: str = "2001234567"
    vat_no: str = "2001234567"
    functional_currency: str = "USD"
    registration_threshold: float = 60000.0   # USD equivalent, 12-month turnover
    filing_day: int = 25
    require_fiscal_invoice: bool = True
    bad_debt_min_months: int = 12
    penalty_rate: float = 0.30                # late-payment surcharge
    interest_rate: float = 0.10               # p.a.
    fixed_apportionment_pct: Optional[float] = None


def load_config() -> AppConfig:
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, encoding="utf-8") as fh:
                return AppConfig(**json.load(fh))
        except Exception:
            pass
    return AppConfig()


def save_config(cfg: AppConfig) -> None:
    with open(CONFIG_FILE, "w", encoding="utf-8") as fh:
        json.dump(asdict(cfg), fh, indent=2)

# ----------------------------------------------------------------------------
# SQLite persistence
# ----------------------------------------------------------------------------

def _connect() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_FILE)
    conn.row_factory = sqlite3.Row
    return conn


def ensure_db() -> None:
    with _connect() as cn:
        cn.execute("""CREATE TABLE IF NOT EXISTS transactions(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            tx_type TEXT NOT NULL, date TEXT NOT NULL,
            description TEXT DEFAULT '', amount REAL NOT NULL,
            currency TEXT DEFAULT 'USD', fx_rate REAL DEFAULT 1,
            vat_inclusive INTEGER DEFAULT 0, tax_code TEXT DEFAULT 'B',
            supplier_name TEXT DEFAULT '', supplier_vat_no TEXT DEFAULT '',
            fiscal_invoice_no TEXT DEFAULT '', attribution TEXT DEFAULT 'MIXED',
            evidence_ref TEXT DEFAULT '', months_elapsed INTEGER DEFAULT 0,
            notes TEXT DEFAULT '')""")


def insert_transaction(t: Transaction) -> int:
    with _connect() as cn:
        cur = cn.execute(
            """INSERT INTO transactions(tx_type,date,description,amount,currency,
               fx_rate,vat_inclusive,tax_code,supplier_name,supplier_vat_no,
               fiscal_invoice_no,attribution,evidence_ref,months_elapsed,notes)
               VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (t.tx_type.value, t.date, t.description, t.amount, t.currency,
             t.fx_rate, int(t.vat_inclusive), t.tax_code, t.supplier_name,
             t.supplier_vat_no, t.fiscal_invoice_no, t.attribution,
             t.evidence_ref, t.months_elapsed, t.notes))
        return cur.lastrowid


def delete_transaction(tid: int) -> None:
    with _connect() as cn:
        cn.execute("DELETE FROM transactions WHERE id=?", (tid,))


def fetch_transactions() -> List[Transaction]:
    out: List[Transaction] = []
    with _connect() as cn:
        for r in cn.execute("SELECT * FROM transactions ORDER BY date, id"):
            out.append(Transaction(
                r["id"], TxType(r["tx_type"]), r["date"], r["description"],
                r["amount"], r["currency"], r["fx_rate"], bool(r["vat_inclusive"]),
                r["tax_code"], r["supplier_name"], r["supplier_vat_no"],
                r["fiscal_invoice_no"], r["attribution"], r["evidence_ref"],
                r["months_elapsed"], r["notes"]))
    return out

# ----------------------------------------------------------------------------
# Calculation engine
# ----------------------------------------------------------------------------

def calculate_return(transactions: List[Transaction], period: str,
                     config: AppConfig, today: Optional[date] = None) -> VATReturnResult:
    today = today or date.today()
    rate = STANDARD_RATE
    ptx = sorted([t for t in transactions if t.period == period],
                 key=lambda t: (t.date, t.id or 0))
    audit: List[AuditLine] = []
    warnings: List[str] = []
    step = 0

    def A(category, tx_ref, description, rule, base=D0, tax=D0, note=""):
        nonlocal step
        step += 1
        audit.append(AuditLine(step, category, tx_ref, description, rule,
                               q2(base), q2(tax), note))

    # ---------------- OUTPUT TAX ----------------
    std_value = zero_value = exempt_value = deemed_value = output_tax = D0
    for t in ptx:
        amt = t.amount_functional
        ref = f"TX#{t.id} {t.date}"
        tt = t.tx_type
        if tt in (TxType.SALE_STD, TxType.DEEMED):
            vat = vat_of(amt, t.vat_inclusive, rate)
            base = base_of(amt, t.vat_inclusive, vat)
            std_value += base
            if tt == TxType.DEEMED:
                deemed_value += base
            output_tax += vat
            A("OUTPUT", ref, t.description,
              "Deemed supply - own use/gifts at open market value"
              if tt == TxType.DEEMED else "Standard-rated supply @ 15%",
              base, vat,
              ("Fiscal invoice " + t.fiscal_invoice_no) if t.fiscal_invoice_no else "")
            if tt == TxType.SALE_STD and t.tax_code not in ("B", ""):
                warnings.append(f"{ref}: standard-rated sale has fiscal code "
                                f"{t.tax_code} (expected B).")
        elif tt == TxType.SALE_ZERO:
            zero_value += amt
            A("OUTPUT", ref, t.description, "Zero-rated supply @ 0%", amt, D0)
            if t.tax_code not in ("C", ""):
                warnings.append(f"{ref}: zero-rated sale has fiscal code "
                                f"{t.tax_code} (expected C).")
        elif tt == TxType.SALE_EXEMPT:
            exempt_value += amt
            A("OUTPUT", ref, t.description, "Exempt supply - no VAT chargeable", amt, D0)
            if t.tax_code not in ("A", "D", ""):
                warnings.append(f"{ref}: exempt sale has fiscal code "
                                f"{t.tax_code} (expected A/D).")
        elif tt in (TxType.CREDIT_NOTE, TxType.DEBIT_NOTE):
            vat = vat_of(amt, t.vat_inclusive, rate)
            base = base_of(amt, t.vat_inclusive, vat)
            sign = -ONE if tt == TxType.CREDIT_NOTE else ONE
            if t.tax_code == "C":
                zero_value += sign * base
            else:
                std_value += sign * base
            output_tax += sign * vat
            A("OUTPUT", ref, t.description,
              "Fiscal credit note (FCN) - reduces output tax"
              if sign < 0 else "Fiscal debit note (FDN) - increases output tax",
              base, sign * vat,
              "Evidence: " + (t.evidence_ref or t.fiscal_invoice_no or "n/a"))

    # ---------------- APPORTIONMENT RATIO (s17(3)) ----------------
    taxable_turnover = std_value + zero_value
    total_supplies = taxable_turnover + exempt_value
    if config.fixed_apportionment_pct is not None:
        ratio = to_d(config.fixed_apportionment_pct) / Decimal(100)
        ratio_note = f"fixed percentage {pct(ratio)} per ZIMRA-approved method"
    elif total_supplies > 0:
        ratio = taxable_turnover / total_supplies
        ratio_note = (f"taxable turnover {money(taxable_turnover)} / total supplies "
                      f"{money(total_supplies)} = {pct(ratio)}")
    else:
        ratio = ONE
        ratio_note = "no exempt supplies - full input tax credit"
    A("SUMMARY", "", "Apportionment of mixed-use input tax",
      "VAT Act s17(3) - turnover method", taxable_turnover, D0, ratio_note)

    def mult_for(attr: str) -> Decimal:
        return {"TAXABLE": ONE, "EXEMPT": D0}.get(attr, ratio)

    # ---------------- INPUT TAX & ADJUSTMENTS ----------------
    input_claimed = purchases_local_value = capital_value = D0
    import_vat = notional = bad_relief = wht_credit = D0
    seen_fiscal = {}

    for t in ptx:
        amt = t.amount_functional
        ref = f"TX#{t.id} {t.date}"
        tt = t.tx_type
        if tt in (TxType.PURCHASE, TxType.CAPITAL_GOOD):
            vat = vat_of(amt, t.vat_inclusive, rate)
            base = base_of(amt, t.vat_inclusive, vat)
            if tt == TxType.CAPITAL_GOOD:
                capital_value += base
            else:
                purchases_local_value += base
            if config.require_fiscal_invoice and (not t.fiscal_invoice_no or not t.supplier_vat_no):
                A("INPUT DENIED", ref, t.description,
                  "Input tax denied - no valid fiscal tax invoice (vendor VAT no. "
                  "+ fiscal tax invoice required)", base, vat)
                warnings.append(f"{ref}: input tax {money(vat)} denied - missing "
                                f"vendor VAT no./fiscal invoice no.")
                continue
            key = (t.supplier_vat_no, t.fiscal_invoice_no)
            if key in seen_fiscal:
                warnings.append(f"{ref}: possible duplicate fiscal invoice "
                                f"{t.fiscal_invoice_no} ({t.supplier_name}); "
                                f"compare with TX#{seen_fiscal[key]}.")
            seen_fiscal[key] = t.id
            claim = q2(vat * mult_for(t.attribution))
            input_claimed += claim
            note = {"TAXABLE": "fully attributable to taxable supplies - 100% claim",
                    "EXEMPT": "attributable to exempt supplies - no credit",
                    "MIXED": f"mixed use - apportioned at {pct(ratio)} (s17(3))"
                    }.get(t.attribution, t.attribution)
            A("INPUT", ref, t.description,
              "Input tax per valid fiscal tax invoice", base, claim, note)
        elif tt == TxType.ENTERTAINMENT:
            vat = vat_of(amt, t.vat_inclusive, rate)
            base = base_of(amt, t.vat_inclusive, vat)
            purchases_local_value += base
            A("INPUT DENIED", ref, t.description,
              "Input tax denied - entertainment expenditure (blocked, VAT Act s17)",
              base, vat)
        elif tt == TxType.PMV:
            vat = vat_of(amt, t.vat_inclusive, rate)
            base = base_of(amt, t.vat_inclusive, vat)
            purchases_local_value += base
            A("INPUT DENIED", ref, t.description,
              "Input tax denied - passenger motor vehicle (blocked, VAT Act s17)",
              base, vat)
        elif tt == TxType.IMPORT:
            if not t.evidence_ref:
                A("INPUT DENIED", ref, t.description,
                  "Input tax denied - no bill of entry (CF47) for import VAT", amt, amt)
                warnings.append(f"{ref}: import VAT {money(amt)} denied - bill of "
                                f"entry reference required.")
                continue
            claim = q2(amt * mult_for(t.attribution))
            import_vat += claim
            input_claimed += claim
            A("INPUT", ref, t.description, "Import VAT per bill of entry (customs document)",
              amt, claim, "Bill of entry: " + t.evidence_ref)
        elif tt == TxType.SECOND_HAND:
            claim = q2(amt * rate / (ONE + rate))     # 15/115 of consideration
            base = amt - claim
            if t.supplier_vat_no:
                warnings.append(f"{ref}: seller appears VAT-registered - claim normal "
                                f"fiscal-invoice input tax instead of notional input tax.")
                A("INPUT DENIED", ref, t.description,
                  "Notional input tax not allowed - seller is a registered vendor",
                  base, claim)
                continue
            if not t.evidence_ref:
                A("INPUT DENIED", ref, t.description,
                  "Notional input tax denied - no seller declaration/records", base, claim)
                warnings.append(f"{ref}: notional input tax {money(claim)} denied - "
                                f"documentation required.")
                continue
            notional += claim
            input_claimed += claim
            A("INPUT", ref, t.description,
              "Notional input tax - second-hand goods from unregistered seller "
              "(15/115 of consideration)", base, claim, "Records: " + t.evidence_ref)
        elif tt == TxType.BAD_DEBT:
            if t.months_elapsed >= config.bad_debt_min_months:
                bad_relief += amt
                input_claimed += amt
                A("ADJUSTMENT", ref, t.description,
                  f"Bad debt relief - debt written off and {t.months_elapsed} months old "
                  f"(>= {config.bad_debt_min_months})", D0, amt,
                  "Records: " + (t.evidence_ref or "n/a"))
            else:
                A("ADJUSTMENT DENIED", ref, t.description,
                  f"Bad debt relief denied - debt only {t.months_elapsed} months old "
                  f"(< {config.bad_debt_min_months})", D0, amt)
                warnings.append(f"{ref}: bad debt relief of {money(amt)} denied - "
                                f"12-month rule not met.")
        elif tt == TxType.WHT_VAT:
            if not t.evidence_ref:
                A("ADJUSTMENT DENIED", ref, t.description,
                  "Withholding VAT credit denied - no withholding certificate (FR-31)",
                  D0, amt)
                warnings.append(f"{ref}: withholding VAT {money(amt)} denied - "
                                f"certificate reference required.")
                continue
            wht_credit += amt
            input_claimed += amt
            A("ADJUSTMENT", ref, t.description,
              "Withholding VAT (10%) credit per withholding certificate",
              D0, amt, "Certificate: " + t.evidence_ref)

    # ---------------- NET POSITION, SURCHARGE & INTEREST ----------------
    total_input = input_claimed
    net = output_tax - total_input
    due = due_date_of(period, config.filing_day)
    days_over = (today - due).days
    surcharge = interest = D0
    if days_over > 0 and net > 0:
        surcharge = q2(net * to_d(config.penalty_rate))
        interest = q2(net * to_d(config.interest_rate) * to_d(days_over) / Decimal(365))

    A("SUMMARY", "", "Total output tax for period", "Sum of output tax lines", D0, output_tax)
    A("SUMMARY", "", "Total allowable input tax for period",
      "Valid input tax + notional + bad debt relief + withholding VAT credit", D0, total_input)
    A("SUMMARY", "", "Net VAT payable / (refundable)",
      "Output tax minus allowable input tax", D0, net)

    # ---------------- VAT 10-STYLE SUMMARY BOXES ----------------
    boxes: List[Tuple[str, str, str]] = []

    def B(section, label, val):
        boxes.append((section, label, val))

    B("OUTPUT TAX", "1. Standard-rated supplies (incl. deemed supplies)", money(std_value))
    B("OUTPUT TAX", "2. Zero-rated supplies", money(zero_value))
    B("OUTPUT TAX", "3. Exempt supplies", money(exempt_value))
    B("OUTPUT TAX", "4. Total value of supplies", money(total_supplies))
    B("OUTPUT TAX", "5. Deemed supplies (own use/gifts, incl. in 1)", money(deemed_value))
    B("OUTPUT TAX", "6. TOTAL OUTPUT TAX", money(output_tax))
    B("INPUT TAX", "7. Local purchases - gross value (incl. blocked items)", money(purchases_local_value))
    B("INPUT TAX", "8. Capital goods (value)", money(capital_value))
    B("INPUT TAX", "9. Import VAT claimed per bills of entry", money(import_vat))
    B("INPUT TAX", "10. Notional input tax - second-hand goods", money(notional))
    B("INPUT TAX", "11. Bad debt relief", money(bad_relief))
    B("INPUT TAX", "12. Withholding VAT credit (10%)", money(wht_credit))
    B("INPUT TAX", "13. Apportionment ratio applied (s17(3))", pct(ratio))
    B("INPUT TAX", "14. TOTAL ALLOWABLE INPUT TAX", money(total_input))
    net_disp = money(net) if net >= 0 else f"({money(-net)}) refundable / c/f"
    B("NET POSITION", "15. NET VAT PAYABLE / (REFUNDABLE)", net_disp)
    if net < 0:
        status = "Refund / carry-forward position - no payment due"
    elif days_over > 0:
        status = f"OVERDUE by {days_over} day(s) - surcharge & interest apply if unpaid"
    else:
        status = f"Due {due.isoformat()} - {(due - today).days} day(s) remaining"
    B("NET POSITION", "16. Filing/payment status", status)
    if days_over > 0 and net > 0:
        B("NET POSITION", f"17. Late-payment surcharge @ {to_d(config.penalty_rate) * 100:.0f}%",
          money(surcharge))
        B("NET POSITION", f"18. Interest @ {to_d(config.interest_rate) * 100:.0f}% p.a. (daily)",
          money(interest))
        B("NET POSITION", "19. TOTAL DUE TO ZIMRA", money(net + surcharge + interest))

    return VATReturnResult(
        period=period, entity=config.company_name, tin=config.tin,
        vat_no=config.vat_no, currency=config.functional_currency,
        due_date=due.isoformat(), boxes=boxes, audit=audit, warnings=warnings,
        total_supplies=q2(total_supplies), output_tax=q2(output_tax),
        total_input_tax=q2(total_input), net_vat=q2(net), ratio=ratio,
        surcharge=surcharge, interest=interest, days_overdue=max(days_over, 0))


def taxable_turnover_trailing(transactions: List[Transaction], end_period: str) -> Decimal:
    """Taxable turnover over the 12 months ending end_period (registration monitor)."""
    total = D0
    for k in range(12):
        p = period_shift(end_period, -k)
        for t in transactions:
            if t.period != p:
                continue
            tt = t.tx_type
            amt = t.amount_functional
            if tt in (TxType.SALE_STD, TxType.DEEMED, TxType.DEBIT_NOTE):
                vat = vat_of(amt, t.vat_inclusive, STANDARD_RATE)
                if t.tax_code != "C":
                    total += base_of(amt, t.vat_inclusive, vat)
            elif tt == TxType.CREDIT_NOTE:
                vat = vat_of(amt, t.vat_inclusive, STANDARD_RATE)
                if t.tax_code != "C":
                    total -= base_of(amt, t.vat_inclusive, vat)
            elif tt == TxType.SALE_ZERO:
                total += amt
    return q2(total)

# ----------------------------------------------------------------------------
# Report formatting (shared by GUI and console)
# ----------------------------------------------------------------------------

def format_return_text(r: VATReturnResult) -> str:
    W = 100
    bar = "=" * W
    sub = "-" * W
    L = [bar, "ZIMRA VALUE ADDED TAX RETURN - VAT 10 (summary)".center(W), bar]
    L.append(f"Vendor               : {r.entity}")
    L.append(f"TIN / VAT reg no.    : {r.tin} / {r.vat_no}")
    L.append(f"Tax period           : {r.period}    Due date: {r.due_date}    "
             f"Currency: {r.currency}")
    last = None
    for sec, label, val in r.boxes:
        if sec != last:
            L.append("")
            L.append(sec)
            L.append(sub)
            last = sec
        L.append(f"  {label:<58}{val:>20}")
    L.append("")
    L.append("COMPLIANCE WARNINGS / NOTES")
    L.append(sub)
    if r.warnings:
        for w in r.warnings:
            L.append(" * " + w)
    else:
        L.append(" * None - all evidence checks passed.")
    L.append(sub)
    L.append("Generated by ZimVAT. Verify rates/rules against current ZIMRA notices before filing.")
    L.append(bar)
    return "\n".join(L)


def format_audit_text(r: VATReturnResult) -> str:
    W = 176
    lines = ["AUDIT TRAIL - CALCULATION STEP BY STEP", "=" * W]
    lines.append(f"{'#':>3}  {'CATEGORY':<16}{'SOURCE / TX':<20}{'DESCRIPTION':<42}"
                 f"{'RULE / BASIS':<46}{'BASE':>14}{'TAX':>14}  NOTE")
    lines.append("-" * W)
    for a in r.audit:
        lines.append(f"{a.step:>3}  {tr(a.category, 16):<16}{tr(a.tx_ref, 20):<20}"
                     f"{tr(a.description, 42):<42}{tr(a.rule, 46):<46}"
                     f"{money(a.base):>14}{money(a.tax):>14}  {tr(a.note, 30)}")
    return "\n".join(lines)

# ----------------------------------------------------------------------------
# Demo data (period 2025-01)
# ----------------------------------------------------------------------------

def _demo(t, d, desc, amt, **kw):
    base = dict(currency="USD", fx_rate=1.0, vat_inclusive=False, tax_code="B",
                supplier_name="", supplier_vat_no="", fiscal_invoice_no="",
                attribution="MIXED", evidence_ref="", months_elapsed=0, notes="")
    base.update(kw)
    return Transaction(None, TxType(t), d, desc, amt, **base)


DEMO_TXS = [
    _demo("SALE_STD",      "2025-01-05", "Wholesale sales - fiscal series A (Jan)", 400000),
    _demo("SALE_STD",      "2025-01-31", "Counter sales - tax inclusive", 23000, vat_inclusive=True),
    _demo("SALE_ZERO",     "2025-01-08", "Maize meal & rice sales (zero-rated)", 120000, tax_code="C"),
    _demo("SALE_EXEMPT",   "2025-01-31", "Residential rent - Avondale flats", 50000, tax_code="A"),
    _demo("DEEMED",        "2025-01-20", "Goods taken for own use (staff kitchen fit-out)", 6000),
    _demo("CREDIT_NOTE",   "2025-01-22", "FCN 4521 - goods returned by Delta Foods", 11500,
          vat_inclusive=True, evidence_ref="FCN-4521"),
    _demo("PURCHASE",      "2025-01-03", "Electricity, telecoms & trading premises overheads", 120000,
          supplier_name="ZESA/Powertel", supplier_vat_no="200011222", fiscal_invoice_no="FI-1001"),
    _demo("PURCHASE",      "2025-01-10", "Packaging & raw materials for resale", 100000,
          supplier_name="NatPak Industries", supplier_vat_no="200033444",
          fiscal_invoice_no="FI-1002", attribution="TAXABLE"),
    _demo("PURCHASE",      "2025-01-25", "Stationery - non-fiscal receipt (kiosk)", 500,
          supplier_name="Chana Stationers", attribution="TAXABLE"),
    _demo("ENTERTAINMENT", "2025-01-12", "Staff entertainment - restaurant", 2600,
          supplier_name="Gourmet Inn", supplier_vat_no="200055121", fiscal_invoice_no="FI-1003"),
    _demo("PMV",           "2025-01-15", "Passenger motor vehicle - Toyota Fortuner", 30000,
          supplier_name="ZimMotors", supplier_vat_no="200044556",
          fiscal_invoice_no="FI-1004", attribution="TAXABLE"),
    _demo("CAPITAL_GOOD",  "2025-01-18", "Delivery truck - Isuzu NPR", 60000,
          supplier_name="TruckCentre", supplier_vat_no="200077889",
          fiscal_invoice_no="FI-1005", attribution="TAXABLE"),
    _demo("IMPORT",        "2025-01-19", "Import VAT - machinery spares", 6750,
          evidence_ref="CF47-778812", attribution="TAXABLE"),
    _demo("SECOND_HAND",   "2025-01-21", "Second-hand pallets - informal seller", 4600,
          evidence_ref="Seller declaration SD-114", attribution="TAXABLE"),
    _demo("BAD_DEBT",      "2025-01-31", "Bad debt written off - Chirwa Enterprises (inv FI-0221)", 1200,
          months_elapsed=14, evidence_ref="Debtors ledger extract"),
    _demo("WHT_VAT",       "2025-01-31", "Withholding VAT - Ministry client", 3400,
          evidence_ref="FR31-55667"),
]


def seed_demo() -> bool:
    with _connect() as cn:
        n = cn.execute("SELECT COUNT(*) c FROM transactions WHERE date LIKE '2025-01%'"
                       ).fetchone()["c"]
    if n:
        return False
    for t in DEMO_TXS:
        insert_transaction(t)
    return True

# ----------------------------------------------------------------------------
# Rules & help text
# ----------------------------------------------------------------------------

RULES_TEXT = """ZIMVAT - ZIMRA RULES ENCODED IN THIS SYSTEM
======================================================================

LEGAL BASIS
* Value Added Tax Act [Chapter 23:12] as amended by Finance Acts; administered by ZIMRA.
* Standard rate 15% (effective 1 January 2023); zero rate 0%; exempt supplies carry no VAT.

REGISTRATION & FILING
* Compulsory registration when taxable turnover exceeds USD 60,000 (or ZiG equivalent)
  in any 12-month period (Dashboard monitors this).
* VAT 10 return due by the 25th of the month following the tax period; payment same deadline.
* Late payment attracts a 30% surcharge plus interest at 10% p.a. (computed daily here);
  late-filing penalties also apply. Verify current rates - they change via Finance Acts.

FISCALISATION (evidence rules enforced by this system)
* Sales must be fiscalised (Fiscal Memory Devices / FDMS e-invoicing with QR validation).
* Input tax claims require a valid fiscal tax invoice showing the vendor's VAT registration
  number and fiscal invoice number, or a bill of entry (CF47) for imports.
* Fiscal tax codes: A/D exempt | B standard 15% | C zero-rated | E special (verify) | F/G levies.
* Credit/debit notes must be fiscal (FCN/FDN).

OUTPUT TAX
* Tax-inclusive amounts: VAT = amount x 15/115. Tax-exclusive: VAT = amount x 15%.
* Zero-rated (examples): maize/mealie meal, rice, bread & wheat flour, salt, milk, brown
  sugar, diesel, petrol, medicines & medical supplies, fertilizers, agro-chemicals, seeds,
  exports.
* Exempt (examples): financial services, insurance, residential rentals, education
  (registered institutions), medical services, public transport, burial & cremation.
* Deemed supplies: goods taken for own use, gifts, staff benefits - output tax on open
  market value.

INPUT TAX & BLOCKED ITEMS
* Full credit where goods/services are used wholly for taxable supplies.
* No credit for expenditure attributable to exempt supplies.
* Mixed/general expenditure is apportioned: allowed = input tax x (taxable turnover /
  total turnover) - s17(3). A ZIMRA-approved fixed percentage can be set in Settings.
* Blocked (no credit): entertainment expenditure; purchase/lease of passenger motor
  vehicles (s17). Capital goods qualify for input tax in full in the month of use.
* Imports: VAT paid at customs is claimable with the bill of entry (CF47).
* Second-hand goods from unregistered sellers: notional input tax of 15/115 of the
  consideration, provided seller declaration / purchase records are kept.

ADJUSTMENTS & SPECIAL TRANSACTIONS
* Bad debt relief: recover the VAT where the debt has been written off in the books,
  is more than 12 months old, and the output tax was previously declared.
* Withholding VAT: appointed agents withhold 10% of the invoice value; the supplier
  claims the withheld VAT as a credit on the VAT 10 (keep FR-31 certificates).
* Refund balances may be carried forward or refunded by ZIMRA (subject to verification).

DATA
* SQLite database zimvat_data.db; settings in zimvat_config.json.
* CSV import header: tx_type,date,description,amount,currency,fx_rate,vat_inclusive,
  tax_code,supplier_name,supplier_vat_no,fiscal_invoice_no,attribution,evidence_ref,
  months_elapsed,notes  (tx_type codes match the Type dropdown, e.g. SALE_STD, PURCHASE).

DISCLAIMER
Operational aid - not tax advice. Confirm all rates, thresholds and rules against the
latest ZIMRA public notices and the Finance Act before submitting any return.
"""

# ----------------------------------------------------------------------------
# GUI (Tkinter)
# ----------------------------------------------------------------------------

class ZimVatApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1200x740")
        self.minsize(1080, 660)
        ensure_db()
        self.config = load_config()
        self.last_result: Optional[VATReturnResult] = None
        self._build_styles()
        self._build_header()
        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=8, pady=(6, 4))
        self._build_dashboard()
        self._build_transactions()
        self._build_return_tab()
        self._build_audit_tab()
        self._build_settings()
        self._build_rules_tab()
        self.status = tk.Label(self, text="Ready.", bd=1, relief="sunken", anchor="w",
                               bg="#E7ECF2", font=("Segoe UI", 9))
        self.status.pack(fill="x", side="bottom")
        self.period_var.set(period_options()[0])
        self.refresh_all()

    # ----- chrome -----
    def _build_styles(self):
        st = ttk.Style(self)
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure("TNotebook", background="#F4F6F8", borderwidth=0)
        st.configure("TNotebook.Tab", padding=(14, 8), font=("Segoe UI", 10))
        st.map("TNotebook.Tab", background=[("selected", "#1F4E79")],
               foreground=[("selected", "white")])
        st.configure("Treeview", rowheight=24, font=("Segoe UI", 9))
        st.configure("Treeview.Heading", font=("Segoe UI", 9, "bold"), background="#DCE4EC")
        st.configure("TButton", padding=5)
        st.configure("Primary.TButton", font=("Segoe UI", 9, "bold"))
        st.configure("TLabelframe.Label", font=("Segoe UI", 9, "bold"), foreground="#1F4E79")

    def _build_header(self):
        self.period_var = tk.StringVar(value=period_options()[0])
        head = tk.Frame(self, bg="#1F4E79")
        head.pack(fill="x")
        tk.Label(head, text="ZimVAT", bg="#1F4E79", fg="white",
                 font=("Segoe UI", 16, "bold")).pack(side="left", padx=(14, 4), pady=10)
        tk.Label(head, text="Zimbabwe VAT Return Automation - ZIMRA VAT 10",
                 bg="#1F4E79", fg="#CFE0F1", font=("Segoe UI", 10)).pack(side="left", pady=10)
        box = tk.Frame(head, bg="#1F4E79")
        box.pack(side="right", padx=14)
        tk.Label(box, text="Tax period:", bg="#1F4E79", fg="white",
                 font=("Segoe UI", 10)).pack(side="left", padx=(0, 6))
        self.period_cb = ttk.Combobox(box, textvariable=self.period_var,
                                      values=period_options(), state="readonly", width=9)
        self.period_cb.pack(side="left")
        self.period_cb.bind("<<ComboboxSelected>>", lambda e: self.refresh_all())

    def _status(self, txt: str):
        self.status.config(text=txt)

    # ----- dashboard -----
    def _build_dashboard(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Dashboard")
        cards = tk.Frame(tab, bg="#F4F6F8")
        cards.pack(fill="x", padx=10, pady=(12, 4))
        self.kpi = {}
        defs = [("Output tax", "#1F4E79"),
                ("Allowable input tax", "#2E7D32"),
                ("Net VAT payable / (refundable)", "#B26A00"),
                ("Total supplies", "#5B3A8E")]
        for i, (title, color) in enumerate(defs):
            f = tk.Frame(cards, bg="white", highlightbackground="#D5DCE4",
                         highlightthickness=1)
            f.grid(row=0, column=i, sticky="nsew", padx=6)
            cards.columnconfigure(i, weight=1)
            tk.Label(f, text=title.upper(), bg="white", fg=color,
                     font=("Segoe UI", 8, "bold")).pack(anchor="w", padx=12, pady=(10, 2))
            v = tk.Label(f, text="-", bg="white", fg="#1B2A3B",
                         font=("Segoe UI", 15, "bold"))
            v.pack(anchor="w", padx=12, pady=(0, 12))
            self.kpi[title] = v
        info = ttk.Labelframe(tab, text="Compliance snapshot")
        info.pack(fill="both", expand=True, padx=10, pady=8)
        self.lbl_entity = tk.Label(info, text="", anchor="w", font=("Segoe UI", 10))
        self.lbl_entity.pack(fill="x", padx=12, pady=(10, 2))
        self.lbl_due = tk.Label(info, text="", anchor="w", font=("Segoe UI", 10))
        self.lbl_due.pack(fill="x", padx=12, pady=2)
        self.lbl_threshold = tk.Label(info, text="", anchor="w", font=("Segoe UI", 10))
        self.lbl_threshold.pack(fill="x", padx=12, pady=2)
        self.lbl_warn = tk.Label(info, text="", anchor="w", font=("Segoe UI", 10))
        self.lbl_warn.pack(fill="x", padx=12, pady=(2, 12))
        btns = tk.Frame(tab, bg="#F4F6F8")
        btns.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(btns, text="Recalculate", command=self.refresh_all).pack(side="left", padx=4)
        ttk.Button(btns, text="Load demo data", command=self.load_demo).pack(side="left", padx=4)
        ttk.Button(btns, text="Export return (CSV)", command=self.export_csv).pack(side="left", padx=4)
        ttk.Button(btns, text="Export report + audit (TXT)", command=self.export_txt).pack(side="left", padx=4)

    # ----- transactions -----
    def _build_transactions(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Transactions")
        form = ttk.Labelframe(tab, text="Add transaction")
        form.pack(fill="x", padx=10, pady=(10, 6))
        self.f_type = ttk.Combobox(form, values=list(TX_LABELS.values()), width=44, state="readonly")
        self.f_type.current(0)
        self.f_date = ttk.Entry(form, width=13)
        self.f_date.insert(0, date.today().isoformat())
        self.f_desc = ttk.Entry(form, width=44)
        self.f_amount = ttk.Entry(form, width=13)
        self.f_cur = ttk.Combobox(form, values=["USD", "ZiG", "ZAR", "GBP", "EUR"],
                                  width=6, state="readonly")
        self.f_cur.set("USD")
        self.f_fx = ttk.Entry(form, width=8)
        self.f_fx.insert(0, "1")
        self.f_incl = tk.BooleanVar(value=False)
        self.f_code = ttk.Combobox(form, values=["B", "A", "C", "D", "E"], width=4, state="readonly")
        self.f_code.set("B")
        self.f_supplier = ttk.Entry(form, width=26)
        self.f_svat = ttk.Entry(form, width=13)
        self.f_fiscal = ttk.Entry(form, width=13)
        self.f_attr = ttk.Combobox(form, values=["", "TAXABLE", "EXEMPT", "MIXED"], width=9)
        self.f_attr.set("MIXED")
        self.f_evid = ttk.Entry(form, width=20)
        self.f_months = ttk.Entry(form, width=4)
        self.f_months.insert(0, "0")
        self.f_notes = ttk.Entry(form, width=44)

        def put(w, r, cp, lbl):
            tk.Label(form, text=lbl, font=("Segoe UI", 9)).grid(
                row=r, column=cp * 2, sticky="e", padx=(12, 4), pady=3)
            w.grid(row=r, column=cp * 2 + 1, sticky="w", padx=(0, 12), pady=3)

        put(self.f_type, 0, 0, "Type")
        put(self.f_date, 0, 1, "Date (YYYY-MM-DD)")
        put(self.f_desc, 1, 0, "Description")
        put(self.f_amount, 1, 1, "Amount")
        put(self.f_cur, 2, 0, "Currency")
        put(self.f_fx, 2, 1, "FX rate -> functional")
        ttk.Checkbutton(form, text="Amount includes VAT", variable=self.f_incl).grid(
            row=3, column=0, columnspan=2, sticky="w", padx=12, pady=3)
        put(self.f_code, 3, 1, "Fiscal tax code")
        put(self.f_supplier, 4, 0, "Supplier")
        put(self.f_svat, 4, 1, "Supplier VAT no.")
        put(self.f_fiscal, 5, 0, "Fiscal invoice no.")
        put(self.f_attr, 5, 1, "Attribution")
        put(self.f_evid, 6, 0, "Evidence ref (CF47/FR-31/decl.)")
        put(self.f_months, 6, 1, "Months elapsed (bad debts)")
        tk.Label(form, text="Notes", font=("Segoe UI", 9)).grid(
            row=7, column=0, sticky="e", padx=(12, 4), pady=3)
        self.f_notes.grid(row=7, column=1, sticky="w", padx=(0, 12), pady=3)
        ttk.Button(form, text="Add transaction", command=self.add_transaction,
                   style="Primary.TButton").grid(row=7, column=3, sticky="e", padx=12, pady=3)
        tk.Label(form, fg="#666", justify="left", wraplength=1000, font=("Segoe UI", 8),
                 text="Purchases need vendor VAT no. + fiscal invoice no. to claim input tax | "
                      "Imports need bill of entry ref | Second-hand (unregistered seller) needs "
                      "seller declaration | Bad debts: enter the VAT portion + age in months").grid(
            row=8, column=0, columnspan=4, sticky="w", padx=12, pady=(2, 8))
        form.columnconfigure(1, weight=1)
        form.columnconfigure(3, weight=1)

        bar = tk.Frame(tab, bg="#F4F6F8")
        bar.pack(fill="x", padx=10)
        ttk.Button(bar, text="Delete selected", command=self.delete_selected).pack(side="left", pady=4)
        ttk.Button(bar, text="Import CSV...", command=self.import_csv).pack(side="left", padx=8)
        ttk.Button(bar, text="Refresh", command=self.refresh_all).pack(side="left")

        cols = ("id", "date", "type", "desc", "amount", "supplier", "evidence", "attr", "code")
        heads = {"id": "ID", "date": "Date", "type": "Type", "desc": "Description",
                 "amount": "Amount (func. ccy)", "supplier": "Supplier",
                 "evidence": "Fiscal / evidence", "attr": "Attribution", "code": "Code"}
        widths = {"id": 50, "date": 90, "type": 260, "desc": 300, "amount": 130,
                  "supplier": 150, "evidence": 150, "attr": 80, "code": 50}
        self.tree = ttk.Treeview(tab, columns=cols, show="headings", height=14)
        for c in cols:
            self.tree.heading(c, text=heads[c])
            self.tree.column(c, width=widths[c], anchor="w")
        self.tree.tag_configure("odd", background="#F6F8FA")
        ys = ttk.Scrollbar(tab, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=ys.set)
        ys.pack(side="right", fill="y", padx=(0, 10), pady=(4, 10))
        self.tree.pack(side="left", fill="both", expand=True, padx=(10, 0), pady=(4, 10))

    def add_transaction(self):
        try:
            d = datetime.strptime(self.f_date.get().strip(), "%Y-%m-%d").date()
        except ValueError:
            messagebox.showerror(APP_TITLE, "Date must be YYYY-MM-DD.")
            return
        try:
            amt = float(self.f_amount.get())
            if amt <= 0:
                raise ValueError
        except ValueError:
            messagebox.showerror(APP_TITLE, "Amount must be a positive number.")
            return
        try:
            fx = float(self.f_fx.get() or 1)
            if fx <= 0:
                raise ValueError
        except ValueError:
            messagebox.showerror(APP_TITLE, "FX rate must be a positive number.")
            return
        try:
            months = int(self.f_months.get() or 0)
        except ValueError:
            months = 0
        t = Transaction(None, LABEL_TO_TX[self.f_type.get()], d.isoformat(),
                        self.f_desc.get().strip(), amt, self.f_cur.get(), fx,
                        bool(self.f_incl.get()), self.f_code.get(),
                        self.f_supplier.get().strip(), self.f_svat.get().strip(),
                        self.f_fiscal.get().strip(), self.f_attr.get() or "MIXED",
                        self.f_evid.get().strip(), months, self.f_notes.get().strip())
        insert_transaction(t)
        if t.period != self.period_var.get():
            self.period_var.set(t.period)
        for w in (self.f_desc, self.f_amount, self.f_fiscal, self.f_evid):
            w.delete(0, "end")
        self.refresh_all()
        self._status(f"Transaction added (period {t.period}).")

    def delete_selected(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo(APP_TITLE, "Select a transaction row first.")
            return
        tid = int(self.tree.item(sel[0], "values")[0])
        if messagebox.askyesno(APP_TITLE, f"Delete transaction #{tid}?"):
            delete_transaction(tid)
            self.refresh_all()

    def import_csv(self):
        path = filedialog.askopenfilename(title="Import transactions CSV",
                                          filetypes=[("CSV files", "*.csv"), ("All files", "*.*")])
        if not path:
            return
        ok = fail = 0
        errors = []
        with open(path, newline="", encoding="utf-8-sig") as fh:
            for i, row in enumerate(csv.DictReader(fh)):
                try:
                    t = Transaction(None, TxType(row["tx_type"].strip()),
                                    row["date"].strip(), row.get("description", ""),
                                    float(row["amount"]),
                                    row.get("currency") or "USD",
                                    float(row.get("fx_rate") or 1),
                                    str(row.get("vat_inclusive", "")).strip().lower()
                                    in ("1", "true", "yes"),
                                    row.get("tax_code") or "B",
                                    row.get("supplier_name", ""),
                                    row.get("supplier_vat_no", ""),
                                    row.get("fiscal_invoice_no", ""),
                                    row.get("attribution") or "MIXED",
                                    row.get("evidence_ref", ""),
                                    int(row.get("months_elapsed") or 0),
                                    row.get("notes", ""))
                    insert_transaction(t)
                    ok += 1
                except Exception as e:
                    fail += 1
                    errors.append(f"row {i + 2}: {e}")
        if errors:
            messagebox.showwarning(APP_TITLE, f"Imported {ok}; failed {fail}.\n"
                                              + "\n".join(errors[:6]))
        else:
            messagebox.showinfo(APP_TITLE, f"Imported {ok} transaction(s).")
        self.refresh_all()

    def load_demo(self):
        if seed_demo():
            self.period_var.set("2025-01")
            self.refresh_all()
            self._status("Demo dataset loaded (period 2025-01).")
        else:
            messagebox.showinfo(APP_TITLE, "Demo data for 2025-01 is already in the database.")

    # ----- return tab -----
    def _build_return_tab(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="VAT Return")
        bar = tk.Frame(tab, bg="#F4F6F8")
        bar.pack(fill="x", padx=10, pady=(10, 4))
        ttk.Button(bar, text="Calculate / refresh", command=self.refresh_all,
                   style="Primary.TButton").pack(side="left")
        ttk.Button(bar, text="Export CSV", command=self.export_csv).pack(side="left", padx=8)
        ttk.Button(bar, text="Export TXT (report + audit)", command=self.export_txt).pack(side="left")
        self.ret_text = tk.Text(tab, font=("Consolas", 9), bg="white", relief="flat",
                                state="disabled", wrap="none")
        ys = ttk.Scrollbar(tab, orient="vertical", command=self.ret_text.yview)
        self.ret_text.configure(yscrollcommand=ys.set)
        ys.pack(side="right", fill="y", padx=(0, 10), pady=(0, 10))
        self.ret_text.pack(side="left", fill="both", expand=True, padx=(10, 0), pady=(0, 10))

    # ----- audit tab -----
    def _build_audit_tab(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Audit Trail")
        self.audit_summary = tk.Label(tab, text="", bg="#F4F6F8", anchor="w",
                                      font=("Segoe UI", 10, "bold"))
        self.audit_summary.pack(fill="x", padx=10, pady=(10, 4))
        cols = ("step", "cat", "ref", "desc", "rule", "base", "tax", "note")
        heads = {"step": "#", "cat": "Category", "ref": "Source / TX", "desc": "Description",
                 "rule": "Rule / basis", "base": "Base", "tax": "Tax", "note": "Note"}
        widths = {"step": 40, "cat": 110, "ref": 130, "desc": 270,
                  "rule": 300, "base": 90, "tax": 90, "note": 220}
        self.atree = ttk.Treeview(tab, columns=cols, show="headings", height=18)
        for c in cols:
            self.atree.heading(c, text=heads[c])
            self.atree.column(c, width=widths[c], anchor="w")
        self.atree.tag_configure("odd", background="#F6F8FA")
        ys = ttk.Scrollbar(tab, orient="vertical", command=self.atree.yview)
        self.atree.configure(yscrollcommand=ys.set)
        ys.pack(side="right", fill="y", padx=(0, 10), pady=(0, 10))
        self.atree.pack(side="left", fill="both", expand=True, padx=(10, 0), pady=(0, 10))

    # ----- settings -----
    def _build_settings(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Settings")
        fr = ttk.Labelframe(tab, text="Vendor & system configuration")
        fr.pack(fill="x", padx=10, pady=10)
        c = self.config
        self.sv = {
            "company_name": tk.StringVar(value=c.company_name),
            "tin": tk.StringVar(value=c.tin),
            "vat_no": tk.StringVar(value=c.vat_no),
            "functional_currency": tk.StringVar(value=c.functional_currency),
            "registration_threshold": tk.StringVar(value=str(c.registration_threshold)),
            "filing_day": tk.StringVar(value=str(c.filing_day)),
            "bad_debt_min_months": tk.StringVar(value=str(c.bad_debt_min_months)),
            "penalty_rate_pct": tk.StringVar(value=str(c.penalty_rate * 100)),
            "interest_rate_pct": tk.StringVar(value=str(c.interest_rate * 100)),
            "fixed_apportionment_pct": tk.StringVar(
                value="" if c.fixed_apportionment_pct is None else str(c.fixed_apportionment_pct)),
        }
        self.sv_require_fiscal = tk.BooleanVar(value=c.require_fiscal_invoice)
        rows = [("Company name", "company_name"), ("TIN", "tin"),
                ("VAT registration no.", "vat_no"),
                ("Functional currency (USD/ZiG)", "functional_currency"),
                ("Registration threshold", "registration_threshold"),
                ("Filing day (day of following month)", "filing_day"),
                ("Bad debt minimum age (months)", "bad_debt_min_months"),
                ("Late-payment surcharge (%)", "penalty_rate_pct"),
                ("Interest rate (% p.a.)", "interest_rate_pct"),
                ("Fixed apportionment % (blank = auto s17(3))", "fixed_apportionment_pct")]
        for i, (lbl, key) in enumerate(rows):
            tk.Label(fr, text=lbl, font=("Segoe UI", 9)).grid(
                row=i, column=0, sticky="e", padx=(10, 6), pady=3)
            ttk.Entry(fr, textvariable=self.sv[key], width=34).grid(
                row=i, column=1, sticky="w", padx=(0, 10), pady=3)
        r = len(rows)
        ttk.Checkbutton(fr, text="Require valid fiscal tax invoice for local input tax claims",
                        variable=self.sv_require_fiscal).grid(row=r, column=0, columnspan=2,
                                                              sticky="w", padx=10, pady=6)
        btns = tk.Frame(fr)
        btns.grid(row=r + 1, column=0, columnspan=2, sticky="w", padx=10, pady=(2, 10))
        ttk.Button(btns, text="Save settings", command=self.save_settings,
                   style="Primary.TButton").pack(side="left")
        ttk.Button(btns, text="Delete ALL transaction data", command=self.clear_data).pack(side="left", padx=10)

    def save_settings(self):
        def fnum(s, default):
            s = s.strip()
            return default if not s else float(s)
        try:
            cfg = AppConfig(
                company_name=self.sv["company_name"].get().strip() or "Unnamed Vendor",
                tin=self.sv["tin"].get().strip(),
                vat_no=self.sv["vat_no"].get().strip(),
                functional_currency=self.sv["functional_currency"].get().strip() or "USD",
                registration_threshold=fnum(self.sv["registration_threshold"].get(), 60000.0),
                filing_day=int(self.sv["filing_day"].get() or 25),
                require_fiscal_invoice=bool(self.sv_require_fiscal.get()),
                bad_debt_min_months=int(self.sv["bad_debt_min_months"].get() or 12),
                penalty_rate=fnum(self.sv["penalty_rate_pct"].get(), 30.0) / 100.0,
                interest_rate=fnum(self.sv["interest_rate_pct"].get(), 10.0) / 100.0,
                fixed_apportionment_pct=(None if not self.sv["fixed_apportionment_pct"].get().strip()
                                         else float(self.sv["fixed_apportionment_pct"].get())))
        except ValueError as e:
            messagebox.showerror(APP_TITLE, f"Invalid number: {e}")
            return
        self.config = cfg
        save_config(cfg)
        self.refresh_all()
        self._status("Settings saved.")

    def clear_data(self):
        if messagebox.askyesno(APP_TITLE, "Delete ALL transactions permanently?", icon="warning"):
            with _connect() as cn:
                cn.execute("DELETE FROM transactions")
            self.refresh_all()
            self._status("All transaction data deleted.")

    # ----- rules tab -----
    def _build_rules_tab(self):
        tab = ttk.Frame(self.nb)
        self.nb.add(tab, text="Rules & Help")
        txt = tk.Text(tab, font=("Consolas", 9), bg="white", relief="flat",
                      wrap="word", state="disabled")
        ys = ttk.Scrollbar(tab, orient="vertical", command=txt.yview)
        txt.configure(yscrollcommand=ys.set)
        ys.pack(side="right", fill="y", padx=(0, 10), pady=10)
        txt.pack(side="left", fill="both", expand=True, padx=(10, 0), pady=10)
        txt.configure(state="normal")
        txt.insert("1.0", RULES_TEXT)
        txt.configure(state="disabled")

    # ----- refresh / export -----
    def refresh_all(self):
        period = self.period_var.get()
        txs = fetch_transactions()
        self.last_result = calculate_return(txs, period, self.config)
        self._refresh_dashboard(period, txs)
        self._refresh_transaction_tree(period, txs)
        self._refresh_return_text()
        self._refresh_audit_tree()
        n = len([t for t in txs if t.period == period])
        self._status(f"Period {period}: {n} transaction(s) | Net VAT "
                     f"{money(self.last_result.net_vat)} | Due {self.last_result.due_date}")

    def _refresh_dashboard(self, period, txs):
        r = self.last_result
        self.kpi["Output tax"].config(text=money(r.output_tax))
        self.kpi["Allowable input tax"].config(text=money(r.total_input_tax))
        self.kpi["Net VAT payable / (refundable)"].config(
            text=money(r.net_vat), fg=("#B26A00" if r.net_vat >= 0 else "#2E7D32"))
        self.kpi["Total supplies"].config(text=money(r.total_supplies))
        self.lbl_entity.config(text=f"Vendor: {r.entity}   |   TIN: {self.config.tin or '-'}"
                                    f"   |   VAT no.: {self.config.vat_no or '-'}"
                                    f"   |   Functional currency: {r.currency}")
        due = date.fromisoformat(r.due_date)
        left = (due - date.today()).days
        self.lbl_due.config(text=f"VAT 10 due date: {r.due_date}   |   "
                                 + (f"{left} day(s) remaining" if left >= 0
                                    else f"OVERDUE by {-left} day(s) - surcharge & "
                                         f"interest apply if unpaid"))
        turnover = taxable_turnover_trailing(txs, period)
        threshold = to_d(self.config.registration_threshold)
        if turnover >= threshold:
            self.lbl_threshold.config(
                text=f"Trailing-12-month taxable turnover: {money(turnover)} - "
                     f"threshold {money(threshold)} exceeded: vendor registration / "
                     f"VAT 10 filing required.", fg="#B26A00")
        else:
            self.lbl_threshold.config(
                text=f"Trailing-12-month taxable turnover: {money(turnover)} - below "
                     f"registration threshold {money(threshold)}.", fg="#2E7D32")
        self.lbl_warn.config(text=f"Compliance warnings on this return: "
                                  f"{len(r.warnings)} (see VAT Return / Audit Trail tabs)")

    def _refresh_transaction_tree(self, period, txs):
        self.tree.delete(*self.tree.get_children())
        for i, t in enumerate([t for t in txs if t.period == period]):
            vals = (t.id, t.date, TX_LABELS[t.tx_type.value], t.description,
                    money(t.amount_functional), t.supplier_name or "-",
                    t.fiscal_invoice_no or t.evidence_ref or "-", t.attribution, t.tax_code)
            self.tree.insert("", "end", values=vals, tags=("odd",) if i % 2 else ())

    def _refresh_return_text(self):
        self.ret_text.configure(state="normal")
        self.ret_text.delete("1.0", "end")
        self.ret_text.insert("1.0", format_return_text(self.last_result))
        self.ret_text.configure(state="disabled")

    def _refresh_audit_tree(self):
        r = self.last_result
        self.atree.delete(*self.atree.get_children())
        for i, a in enumerate(r.audit):
            self.atree.insert("", "end", values=(a.step, a.category, a.tx_ref,
                                                 a.description, a.rule, money(a.base),
                                                 money(a.tax), a.note),
                              tags=("odd",) if i % 2 else ())
        self.audit_summary.config(
            text=f"Apportionment ratio {pct(r.ratio)}   |   Output tax {money(r.output_tax)}"
                 f"   |   Allowable input tax {money(r.total_input_tax)}"
                 f"   |   Net VAT {money(r.net_vat)}")

    def export_csv(self):
        r = self.last_result
        path = filedialog.asksaveasfilename(defaultextension=".csv",
                                            initialfile=f"VAT10_{r.period}.csv",
                                            filetypes=[("CSV", "*.csv")])
        if not path:
            return
        with open(path, "w", newline="", encoding="utf-8") as fh:
            w = csv.writer(fh)
            w.writerow(["Section", "Line", "Value"])
            w.writerows(r.boxes)
        self._status(f"Exported {path}")

    def export_txt(self):
        r = self.last_result
        path = filedialog.asksaveasfilename(defaultextension=".txt",
                                            initialfile=f"VAT10_{r.period}_report.txt",
                                            filetypes=[("Text", "*.txt")])
        if not path:
            return
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(format_return_text(r))
            fh.write("\n\n")
            fh.write(format_audit_text(r))
            fh.write("\n")
        self._status(f"Exported {path}")

# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description="ZimVAT - Zimbabwe VAT return automation (ZIMRA VAT 10)")
    ap.add_argument("--demo", action="store_true", help="seed the worked 2025-01 example")
    ap.add_argument("--report", metavar="YYYY-MM",
                    help="compute and print the VAT 10 report to the console (no GUI)")
    args = ap.parse_args()
    ensure_db()
    if args.demo:
        print("Demo data seeded for 2025-01." if seed_demo() else "Demo data already present.")
    if args.report:
        res = calculate_return(fetch_transactions(), args.report, load_config())
        print(format_return_text(res))
        print()
        print(format_audit_text(res))
        return
    try:
        ZimVatApp().mainloop()
    except tk.TclError:
        print("GUI unavailable (no display?). Run: python zimvat_app.py --report YYYY-MM")


if __name__ == "__main__":
    main()