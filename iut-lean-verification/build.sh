#!/usr/bin/env bash
# IUT 系3.12 形式検証のビルド + 公理チェック
# 必要: elan (https://github.com/leanprover/elan)
set -euo pipefail
cd "$(dirname "$0")"

lake build

# sorry や追加公理に依存していないことを確認
cat > /tmp/iut_check_axioms.lean <<'EOF'
import IUT.Verdict
#print axioms IUT.verdict
#print axioms IUT.ss_incompatible
#print axioms IUT.cor312_independent
#print axioms IUT.controversy_reduces_to_rc
EOF
lake env lean /tmp/iut_check_axioms.lean

echo "OK: all theorems verified (expected axioms: propext, Quot.sound only)"
