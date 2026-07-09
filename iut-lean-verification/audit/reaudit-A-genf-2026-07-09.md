# 柱A 再監査（一般構成器 ∀既約f, ℚ[x]/(f)体 の実装後）2026-07-09

- 監査者: 独立エージェント1名（opus・敵対的・実 Lean 定義のみ・自己申告非共有・自ら `#print axioms` とフルビルドを実行）
- 契機: 一般構成器 `gefField` + x³−2/Φ₃ の二実例化の後の A1 再評定
- 基準: `AUDIT_RUBRIC.md` / `target_ledger.json` / 前回 `reaudit-A-cq3-2026-07-09.md`（A1 0.75・限定(i)「一般f構成器なし」）

## 結果: **A1 0.75→0.80**（A 柱 complete_pct は 36.0→36.4 の丸めで **36 据え置き**）

| id | 前回 | 今回 | 判定 |
|---|---|---|---|
| **A1** | **0.75** | **0.80** | **前進**（満たせる一般構成器＋2実例で限定(i)解消） |
| A2–A9 | — | 変化なし | 据置（gefField は実数体構成のみ・Galois/π₁ 等に無関与） |

## §4 修正の正直な経緯（本ラウンドの核）

一般構成器の実装途中、一般既約性の定義 `pibIrreducible` の約元量化子が有界性を課さず（`∀ d, pdbDvd d f → …`）**偽**だった: 非有界冪級数単元 d=1/(1−X) が任意の定数項≠0 多項式を（多項式余因子で）割り、単元でも同伴でもないため二分が破綻。よって一般構成器 `gef_field_exists` は**充足不能な仮説**を持つ**空虚な一般化**（§3 の toy 主語リスク）だった。

独立エージェント2名（x³−2 と Φ₃ の既約性担当）が**それぞれ独立に反証を機械証明**（`cti_pib_false`/`cqi_pib_false`）し、§4 に従い**定義を「∀ d, IsPoly d → …」へ本物化**（約元を真の多項式に制限）して再証明。これは「正直な限定を消さず・sorry で誤魔化さず・定義を本物に置換して証明し直す」§4 の模範例。

## 監査の核心判定（実 Lean 検証・監査者自身が #print axioms 実行）

- **(a) 修正後 pibIrreducible は忠実**: `∀ d, IsPoly d → pdbDvd d f → (単元 ∨ 同伴)` は K[X] の標準既約性（多項式約元は単元 or 同伴）。旧非有界形の反例は排除。空虚でも過強でもない: `cti_irreducible`/`cqi_irreducible` が全枝を本物に discharge（根の枝は実 `crt_no_rat_cube`（∛2∉ℚ）/`cq0_no_rat_root`（Φ₃ 有理根なし）に落ちる・surrogate なし）。監査者が証明を読了。
- **(b) gefField は満たせる本物の一般構成器**: `gefField : ∀ f (deg≥1,lead≠0,pibIrreducible f) → SimpleFieldExt` は仮説を取るが**空虚な∀でない**——`gfiCbrtField=gefField ct0PS 3 … cti_irreducible`・`gfiCq3Field=gefField cq0PS 2 … cqi_irreducible`（GenFieldInstances）で**異なる次数の2例が同一 gefField から**体化。前回 scout/監査が要求した「一般エンジン＋充足具体例」をちょうど満たす。
- **(c) hBez・体性が本物**: `gef_bezout` は `pgbBezoutQ`（実 ℚ 有界余因子 Bezout・hlead_oracle choice-free）+ `pib_gcd_unit_of_not_dvd`（実 `pdb_dvd_trans`）+ 単元正規化の実合成。体性は quotCRing 由来。全 axiom `[propext, Quot.sound]`。
- **(d) 残る限定**: 逆元は依然∃形（全域 inv 付き IUTField なし）・{1,α,…}基底/次数=[K:ℚ] 理論なし・既約性は f ごと手証明（Eisenstein 等の一般判定なし）。満点1には遠い。**0.85 は過大**（total-inv/基底の近接を含意するが無い）。

→ 0.75 の限定(i)「一般f構成器なし」を satisfiable な degree-parametric 構成器＋2実例で解消＝前回監査が名指しした「A1→0.8 マイルストーン」に到達。**0.75→0.80**。

## complete_pct への反映（正直申告）
A1 status 0.75→0.80 は台帳に反映。だが A 柱% = round(Σ(weight×status)) は 36.0→36.4 で**いずれも 36 に丸まり据え置き**。**A1 は実質前進したが 0.82 の丸め閾値未満**——過大主張しないため 36 のまま（guard exit 0）。柱 A を 37 にするには A1≥0.82（全域 inv or 基底/次数理論）or 他の高 weight 項目（A3/A4/A6 各 12-14）の前進が要る。

## 次手
- **A1→0.85+/1**: 全域 inv 付き IUTField インスタンス（∃→Σ' 構成的リファクタ）＋{1,α,…}基底・次数=[K:ℚ] 理論。これで 0.82 を越え柱%が動く。
- **A3（高 weight 12）**: gefField で円分体 ℚ(ζ_{3ⁿ})=ℚ[x]/(Φ_{pⁿ}) を作れる基盤ができた（一般 f 対応）→ 塔＋制限準同型＋逆極限で実 G_K。柱%を動かすには A1 より A3 の方が weight 高い。
