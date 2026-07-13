# 独立敵対的再監査: q9tl — level-9 実 Tate 曲線 E_{3⁹} = M^×/q^ℤ

- 対象: `IUT/Q3TateCurveL9.lean`（prefix `q9tl`・414 行・commit f516532）
- 申告分類: **[実／本物の先行建設(b)] FOUNDATION**・complete_pct **0 前進**
- 監査日: 2026-07-11
- 監査者: 独立敵対的監査（本コードの著者でない・既定スタンス SKEPTICAL）
- 判定サマリ: **genuine clone・実 u₆ 消費・axiom clean・0 前進確定（A=54 据え置き）**

---

## 0. 結論（先出し）

| 検査項目 | 判定 |
|---|---|
| genuineness（3 が実 wild-splitting u₆ を消費するか） | **YES（本物）** |
| q = 3⁹ が u₆⁹ で本物構成か（q9tl_ninth_elt） | **YES** |
| q9tl_zeta9_unit は N(Y)=ζ₃ を実証か（assert でない） | **YES** |
| 位数ちょうど 9 の非空虚性（q9tl_3_tor / q9tl_zeta9_tor） | **YES（非空虚・実証明）** |
| axioms = [propext, Quot.sound] のみ | **YES（7 対象全て）** |
| 禁止タクティク不使用 | **YES（コード 0・grep ヒットは日本語コメントのみ）** |
| double-counting（q3tl 再ラベル／hollow capstone） | **NO（新規 level-9 曲線・別物）** |
| 台帳判定 | **0 前進・A=54 据え置き・target_ledger.json 不変** |

---

## 1. Genuineness — 3 は実 u₆ を使うか（設計 §2.1–2.3 要件）

設計（audit/level9-theta-kill-detail §2.1–2.3）は、群元「3」を **実 wild-splitting u₆
（=q9psU6）から** 組み、`3 = (6, ⟨q9psU6, q9ps_u6_unit⟩)` とすること（posit された
`(6, 任意単数)` 模型に落ちないこと）を要求する。実 Lean 定義を精読して確認した。

### 1.1 元 3 の単数部は実 u₆

- `q9tlU3 : q3kU.carrier := ⟨q9psU6, q9ps_u6_unit⟩`（L92）
- `q9tl3 : q9tlMx.carrier := ((6 : Int), q9tlU3)`（L97）

単数部は arbitrary unit ではなく `q9psU6` そのもの。`q9psU6` は
`IUT/Q3KummerPiSplit.lean:443` で `q3kNeg (q3kMul q9psWinv q9psWinv) = −(w⁻¹)²`
＝**実閉形式単数**として定義される。単数性 `q9ps_u6_unit`（L446–450）は
`−1·(w⁻¹)²` の実因数分解＋`q3k_unit_mul`／`q3k_unit_inv` で構成される真の証明。

決定的なのは、u₆ が **wild 分割恒等式 `3_M = π₉⁶·u₆` の実閉形式**であること:
`q9ps_three_split`（Q3KummerPiSplit.lean:466–484）が
`q3kMul q9psPi6 q9psU6 = q3kEmbed q3rqThreeElt` を、`3 = −λ²`（q3rq_three_eq_neg_lambda_sq）
と `w·w⁻¹=1` を用いた実基底計算で**本物に証明**している（assert でない）。
したがって u₆ は「3 の実単数部」であり、CLAUDE.md §2.2 が警告する
`3 := (6, 任意単数)` posit 模型に該当しない。**[実] の剥奪不要。**

### 1.2 q = 3⁹ は u₆⁹ で本物構成

- `q9tlQ := ((54 : Int), tateNpow q3kU q9tlU3 9)`（L101）— 単数部は U₃ 内で u₆ の実 9 乗。
- `q9tl_ninth_elt : tateNpow q9tlMx q9tl3 9 = q9tlQ`（L344–348）は
  第1成分（`q9tl_npow_fst_val 9` ⟹ 9×6=54＝rfl）と
  第2成分（`q9tl_npow_snd q9tl3 9` ⟹ tateNpow q3kU q9tlU3 9）を `Prod.ext` で貼る本物証明。
  「9 乗トリック」q^{1/9}=3∈ℚ₃ が実 M 単独で閉じることを、外部仮定なしで成立させている。

### 1.3 q9tl_zeta9_unit は N(Y)=ζ₃ を実証（assert でない）

- `q9tl_normBase_zeta9`（L62–80）は 3 次ノルム多項式 a³+ζ₃b³+ζ₃²c³−3ζ₃abc を
  Y=(0,1,0) に代入し、実環書き換え（q3rqRing.mul_zero 等）で `ζ₃·1=ζ₃` へ簡約する実計算。
- `q9tl_zeta9_unit`（L83–86）は `q3kUnitMem q3kZeta9 = q3rqUnitMem (N(Y))` を上の等式で
  `q3rqUnitMem ζ₃` に落とし、`q3rq_zeta_unit`（既存の実単数性）で閉じる。**assert でない。**

---

## 2. 位数ちょうど 9 の非空虚性

### 2.1 q9tl_3_tor（[3] の位数ちょうど 9）— L304–316

証明の骨格（実 Lean）:
1. `[3]^k = 1` を仮定 ⟹ `q9tlProj.map (3^k) = 1`（q9tl_proj_npow で冪を射影の外へ）。
2. `quotientProjN_ker` の普遍性で `3^k ∈ q^ℤ`、すなわち `∃ t, tateZpow q9tlMx q9tlQ t = 3^k`。
3. 第1成分（付値）を取ると `t*54 = k*6`（`q9tl_pow_fst`＝54t・`q9tl_npow_fst_val`＝6k）。
4. `omega`（純 Int）で `0 < k < 9` に整数解なし ⟹ False。

**非空虚性の確認**: 6k=54t は k=9t を強制し、0<k<9 の範囲に整数解が存在しない。
仮説 h から本当に矛盾が導かれる（trivially-true / vacuous でない）。付値合同は
**実 M^× の実付値成分**（e(M/ℚ₃)=6 の第1スロット）に由来しており、fudge でない。

### 2.2 q9tl_zeta9_tor（[ζ₉] の位数ちょうど 9）— L320–338

証明の骨格:
1. `[ζ₉]^k = 1` を仮定 ⟹ `ζ₉^k ∈ q^ℤ`、`∃ t, ...`。
2. 第1成分 `t*54 = 0`（ζ₉ の付値 0）⟹ `t = 0`（omega）。
3. t=0 を代入 ⟹ 第2成分 `tateNpow q3kU q9tlZeta9U k = q3kU.one`（U₃ 内 Y^k=1）。
4. `q9tl_zeta9U_pow_ne k`（L286–298）が `q9tl_zpow{1..8}`（U₃ 内 ζ₉U^k=Y^k の橋）と
   **q9yp の Yᵏ≠1（k=1..8）** を消費して矛盾。

**非空虚性の確認**: q9yp の `q9yp_y{2..8}_ne_one` は実 q3kMul で計算した Y^k の
特定スロット成分が非零であること（例 Y²: 第3スロット 1≠0・Y³: embed ζ₃・ζ₃≠1）から
導く実証明であり（Q3KummerYPow.lean:160–209 で精読確認）、trivially-true でない。
`q9tl_zeta9U_pow_ne` の match は k=0 と k≥9 を absurd で排除し、k=1..8 を各 q9yp 補題で
閉じる網羅的分岐。**位数ちょうど 9 は本物に非空虚。**

---

## 3. Axioms & 禁止タクティク

`lake build IUT.Q3TateCurveL9` EXIT=0・no sorry。`lake env lean` で以下を列挙実行:

```
'IUT.q9tl_3_tor'       depends on axioms: [propext, Quot.sound]
'IUT.q9tl_zeta9_tor'   depends on axioms: [propext, Quot.sound]
'IUT.q9tl_zeta9_unit'  depends on axioms: [propext, Quot.sound]
'IUT.q9tl_ninth_elt'   depends on axioms: [propext, Quot.sound]
'IUT.q9tl_exists'      depends on axioms: [propext, Quot.sound]
'IUT.q9tl_3pt_pow9'    depends on axioms: [propext, Quot.sound]
'IUT.q9tl_zeta9_pow9'  depends on axioms: [propext, Quot.sound]
```

**7 対象すべて厳密に [propext, Quot.sound] のみ**（新規 Classical.choice 皆無）。

禁止タクティク grep（`sorry|admit|simp|decide|by_cases|rcases|ring|nlinarith|native_decide`）
の唯一のヒットは L44 の日本語コメント「sorry 皆無」＝タクティクでない。
コード本体は `omega`（純 Int：付値合同・整数解排除のみ）・`rw`・`exact`・`show`・
`induction ... with`・`Prod.ext`・`congrArg`・`Subtype.ext`・`match` のみ。**違反 0。**

---

## 4. Double-counting / hollow capstone 検査

q9tl は q3tl（level-3・Q3TateCurveL2.lean）の再ラベル／再輸出でないことを確認:

| | q3tl（level-3） | q9tl（level-9） |
|---|---|---|
| 曲線 | E₂₇ = L₂^×/27^ℤ | E_{3⁹} = M^×/q^ℤ |
| 基群 | L₂^× = ℤ×U₂ | M^× = q3kU = ℤ×U₃ |
| q | 27 = 3³（付値 6） | 3⁹（付値 54） |
| 元 3 | (2, −1)＝**自明単数 −1** over U₂ | (6, u₆)＝**実 wild-splitting u₆** over U₃ |
| torsion | 位数ちょうど 3（[ζ₃]・[3]） | 位数ちょうど 9（[3]・[ζ₉]） |
| 新規消費 | — | q9ps（u₆・three_split）・q9yp（Y^k≠1） |

q9tl は q3tl の立方トリックを 9 乗トリックへ写経した **別の level-9 曲線**であり、
q3k/q9ps/q9yp を新規消費する。特に q3tl の元 3 は自明単数 −1 を単数部に持つのに対し、
q9tl の元 3 は実 wild-splitting u₆ を単数部に持つ＝**質的に新しい実対象**。
capstone `Q3TateCurveL9Data`/`q9tl_data`/`q9tl_exists` は上記の実定理
（abelian・proj_surjective・period・ninth_eq・[·]⁹=1・位数ちょうど 9）を束ねるのみで
新規の空虚主張を持たず、hollow capstone でない。

---

## 5. 台帳判定（Ledger decision）

- q9tl は **foundation**：本モジュール単体は何も kill しない（テータ群・剛性・橋の kill 本体は
  後続 q9mt/q9mr/q9mb で未建設）。したがって実 IUT 完全証明率を担う実対象は
  **まだ台帳項目に消費されていない**。
- CLAUDE.md §5 / 完全証明ファースト規則に従い、**complete_pct 0 前進**が正直な帰結。
- `target_ledger.json` は **不変**（A の各 status を動かさない）。
- `compute_complete_pct.py` 再実行 ⟹ `{"A": 54, "B": 18, "C": 41, "D": 18, "E": 42}`
  （A=54 据え置きを再確認）。
- `graph-meta.json` の pillar-A `complete_note` に本監査の記録を **追記のみ**
  （complete_pct=54・progress_pct=99 は不変）。

**過大主張なし・水増しなし。genuine foundation → 0 前進確定という期待どおりの正直な帰結。**
