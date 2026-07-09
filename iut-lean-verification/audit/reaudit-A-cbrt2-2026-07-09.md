# 柱A 再監査（実 ℚ[x]/(x³−2) 商環体の実例化後）2026-07-09

- 監査者: 独立エージェント1名（opus・敵対的・実 Lean 定義のみ・自己申告非共有・compiler で `#print axioms` 自検）
- 契機: ℚ(∛2)=ℚ[x]/(x³−2) を**真の quotCRing 商環＋実体**として実例化（12 モジュール）した後の A 柱再評定
- 基準: `AUDIT_RUBRIC.md` / `target_ledger.json`

## 結果: **A1 0.5→0.7**（A 柱 complete_pct 34→36）

| id | 前回 | 今回 | 判定 |
|---|---|---|---|
| **A1** | **0.5** | **0.7** | **昇格**（真の商環 ℚ[x]/(x³−2)＋証明済み Bezout による体化） |
| A2 | 0.5 | 0.5 | 据置（完備化・p 進距離は本作業に皆無・数体であって局所体でない） |
| A3 | 0.5 | 0.5 | 据置（単一3次拡大・x³−2 は Galois ですらない・自己同型群/逆極限未構成） |
| A4 | 0.5 | 0.5 | 据置（π₁^ét 触れず） |
| A5 | 0 | 0 | 据置 |
| A6 | 0.5 | 0.5 | 据置（π₁ からの体復元なし） |
| A7 | 0 | 0 | 据置 |
| A8 | 0.5 | 0.5 | 据置 |
| A9 | 0 | 0 | 据置 |

## 監査の核心判定（A1 昇格の論拠・実 Lean 検証）

以前 A1=0.5 の理由は「carrier が ℚ×ℚ 対（`GaussianRationalField`/`QuadraticField`）で**真の商環でなく次数2のみ**、`SimpleExtension` の一般商環機構を経由しない直積模型」。今回、監査者が実 Lean を追い以下を確認:

- **carrier は文字どおり quotCRing の商環**（ℚ×ℚ 直積模型でない）: `ctfRing = simpleExtRing ct0Field ct0PS 3 ct0_bound = quotCRing (polyCRing ratRing) (simpleExtModulus …)`。`quotCRing S E` の carrier = `Quot (idealRel S E)`、`idealRel S E f g = ∃h, f+(−g)=h·E`。`ct0Field.ring ≡ ratRing`（実 ℚ）、`polyCRing ratRing` = 実有限台多項式環 → **carrier は文字どおり ℚ[x]/(x³−2)** の主イデアル商。
- **Bezout は本物に証明済み（仮説引数でない）**: `cbc_bezout` は完全な body を持つ `theorem`（次数3固定ユークリッド鎖・8葉・実除法 `field_division_exists`・完全割り葉を `clf_linear_factor_root`+`crt_two_not_cube`（∛2∉ℚ の実無限降下）で矛盾）。`#print axioms` = `[propext, Quot.sound]`。**deferred だった honest 仮説 `SimpleExtData.bezout` の初の実充填**。
- **体性は Bezout 由来**: `ctf_has_inverses = quotField_of_bezout … cbc_bezout`、`ctfData.bezout := cbc_bezout`。
- **非空虚**: `cta_alpha_cubed`（α³=emb(2)）・`cta_alpha_not_rational`（∀c, α≠emb(c)＝∛2∉ℚ）・`nontrivial`（1≠0）・`ctf_emb_injective`（ℚ↪ℚ(∛2)）——いずれも axiom-clean。崩壊/自明な環でない本物の3次拡大。

→ A1 文言「**実際の商環として構成**」に、ℚ(∛2) が真の quotCRing 商環＋体として初めて正面から答えた。直積模型 0.5 を**質的に超える**忠実な部分ケース → **0.5→0.7**。

## 満点(1)にしない論拠（正直な限定）
単一 f=x³−2 のみ（一般既約 f の Bezout は未）・逆元は∃形（全域 inv 付き IUTField インスタンスは未）・次数理論/{1,α,α²} 基底なし。A1 の「K=ℚ[x]/(f)」を一般 f と読めば満点 1 は不可、0.7 が上限。

## プロセスの健全性
- これは撤回後 **2 度目の実 complete_pct 前進**（B5 積公式 0→0.5 に続く）。**自己申告でなく独立監査確定**——監査者は自ら `#print axioms` を走らせ、carrier が quotCRing 商環か・bezout が仮説でなく証明済みか・非空虚かを実 Lean で検証した上で 0.7 を付けた。
- 中間値 0.7 は「0.5 の忠実な部分ケースを質的に超えるが満点1未達」の初の適用（`_status_scale` に明記）。過大（1）でも過小（0.5 据え置き）でもない двусторонний な評定。

## 次手（監査示唆・A1→1 と他項目）
- A1→1: 一般既約 f の Bezout（一般拡張ユークリッド互除法・PolyBezoutQ の hlead_oracle を ℚ で討つ）＋全域 inv 付き IUTField インスタンス＋{1,α,α²} 基底・次数理論。
- A3（実 G_K）: ℚ(∛2) を含む**Galois 閉包の塔**を制限準同型で逆極限へ組む（単一非 Galois 拡大では動かない）。
