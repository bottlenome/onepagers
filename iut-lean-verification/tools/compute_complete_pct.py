#!/usr/bin/env python3
"""実 IUT 完全証明率(complete_pct)を target_ledger.json の status から機械計算する。

complete_pct(柱) = round( Σ(weight*status) / Σ(weight) * 100 )
status は独立監査(AUDIT_RUBRIC.md)が埋める実装度 0..1。実装者が手で付けない。
どれか status=null の柱は「未監査(None)」を返す(=まだ数字を出せない)。
"""
import json, os, sys

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
        num = sum(it["weight"] * float(it["status"]) for it in items)
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
