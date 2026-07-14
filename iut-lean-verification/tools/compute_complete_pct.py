#!/usr/bin/env python3
"""実 IUT 完全証明率(complete_pct)を target_ledger.json の status から機械計算する。

complete_pct(柱) = round( Σ(weight*status) / Σ(weight) * 100 )
status は独立監査(AUDIT_RUBRIC.md)が埋める実装度 0..1。実装者が手で付けない。
どれか status=null の柱は「未監査(None)」を返す(=まだ数字を出せない)。
"""
import json, os, sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
LEDGER = os.path.join(HERE, "..", "target_ledger.json")


def compute(ledger_path=LEDGER):
    d = json.load(open(ledger_path))
    out = {}
    for k, p in d.get("pillars", {}).items():
        items = p.get("items", [])
        if not items:
            out[k] = None
            continue
        if any(it.get("status") is None for it in items):
            out[k] = None  # 未監査
            continue
        # 厳密有理数で計算する。status は 2 桁小数の実装度なので Fraction(str(...)) で
        # 誤差なく評価し、丸めは Python round()＝銀行家丸め(round-half-to-even)。
        # 旧実装 round(float(num)/den*100) は 54.5 等のちょうどの同点で /den*100 の
        # 浮動小数点誤差(54.50000000000001)により銀行家丸めの境界を誤って跨いだ
        # (例: Σ=54.5 → 誤って 55)。同点は規約どおり 54 に丸める。
        num = sum(it["weight"] * Fraction(str(it["status"])) for it in items)
        den = sum(it["weight"] for it in items)
        out[k] = round(num / den * 100) if den else 0
    return out


if __name__ == "__main__":
    res = compute()
    print(json.dumps(res, ensure_ascii=False))
    # 未監査があれば注記
    un = [k for k, v in res.items() if v is None]
    if un:
        sys.stderr.write(f"未監査の柱: {','.join(un)}（target_ledger.json の status を独立監査で埋めるまで complete_pct は確定しない）\n")
