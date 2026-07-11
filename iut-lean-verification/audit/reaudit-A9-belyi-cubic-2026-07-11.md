# 独立再監査 A9 — 実 Belyi 三点分岐 (BelyiCubicReal.lean / blc)

- 日付: 2026-07-11
- 監査対象項目: A9「Belyi 化 / 遠アーベル幾何入力(実)」weight=10, 前回 status=0
- 対象モジュール: `IUT/BelyiCubicReal.lean`（prefix blc・新規）
- 監査姿勢: 敵対的（既定=模型/代理）。立証責任は「実」主張側。自己申告値・設計書・ヘッダ `[実/...]` 主張は非採用。判定は `def`/`theorem` 本体のみ。
- **status 判定: 0 → 0.1**
- **柱A complete_pct: 50 → 51**（compute_complete_pct.py 由来・Σ_A=49.54+10×0.1=50.54・round 51）

---

## 1. rubric 分類（blc）

- `classification`: **real**（初インスタンス帯・moves_complete_pct: yes）
- `principal_object`: 実 ℚ（ratRing）係数の実 polyCRing 元 blcF = 3X²−2X³（実 Belyi 多項式）と、その分岐軌跡 {0,1,∞} の構成的完全決定（上界 blc_branch_locus ＋ 下界 blc_fiber_zero/one ＋ ∞ チャート blc_infty_chart）。
- `is_it_a_stand_in`: **no**。担体は PS ratRing（= ℕ→ratRing.carrier の実冪級数/多項式）で、ratRing は真の商 Quot 構成（quot_exact_rat 等）。Nat/Bool/Fin 身代わりでない。blcF は psSingle/psAdd による実 polyCRing 元。
- `self_declared_external`: なし（`*_model_scope` 型の実対象外部宣言なし）。§4.2 の正直な限定 7 項は「何を含めないか」（Belyi 定理・noncritical・cuspidalization・スキーム・π₁）であって主対象自身を模型と自認する記述ではない。
- `moves_complete_pct`: **yes**（新主語クラスの実対象＋実定理・A9 status 0→0.1）。
- `evidence`: `blcF`(147), `blc_branch_locus`(529), `blc_fiber_zero`(290), `blc_fiber_one`(400), `blc_infty_chart`(782), `blc_infty_unit`(805), `blc_deriv_eq`(208), `blc_eval_F`/`blc_eval_fun`(496/735), `blcData`(838)。

---

## 2. build.sh 実行（EXIT / sorry / axioms tail）

`cd iut-lean-verification && export PATH="/root/lean4/bin:$PATH" && bash build.sh 2>&1 | tail -40`:

```
'IUT.blc_branch_locus' depends on axioms: [propext, Quot.sound]
'IUT.blc_branch_locus_rat' depends on axioms: [propext, Quot.sound]
'IUT.blc_fiber_zero' depends on axioms: [propext, Quot.sound]
'IUT.blc_fiber_one' depends on axioms: [propext, Quot.sound]
'IUT.blc_infty_chart' depends on axioms: [propext, Quot.sound]
'IUT.blc_belyi_exists' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```

EXIT=0・no sorry。

## 3. 監査者自走 #print axioms（scratch: lake env lean IUT/AxCheck.lean）

build.sh に載らない残り load-bearing 対象を監査者が自作 scratch で列挙実行:

```
'IUT.blc_infty_unit' depends on axioms: [propext, Quot.sound]
'IUT.blcData' depends on axioms: [propext, Quot.sound]
'IUT.blc_deriv_eq' depends on axioms: [propext, Quot.sound]
'IUT.blc_eval_fun' depends on axioms: [propext, Quot.sound]
'IUT.blc_rat_no_zero_div' depends on axioms: [propext, Quot.sound]
'IUT.blc_map_infty_fiber' does not depend on any axioms
'IUT.blc_branch_locus' depends on axioms: [propext, Quot.sound]
'IUT.blcF' does not depend on any axioms
```

全 A9 load-bearing 対象（blc_branch_locus, blc_branch_locus_rat, blc_fiber_zero, blc_fiber_one, blc_infty_chart, blc_infty_unit, blcData, blc_belyi_exists, blc_deriv_eq, blc_eval_fun, blc_rat_no_zero_div）が `[propext, Quot.sound]` のみ。純計算対象（blc_map_infty_fiber, blcF）は公理ゼロ。**Classical.choice / sorryAx 皆無**。scratch/olean 削除済（git clean）。

---

## 4. プローブ所見

### 4.1 主対象は REAL か
YES。blcF は `polyCRing ratRing`（実 ℚ[X]）の実元（psSingle E (blcThree E) 2 と psSingle E (E.neg (blcTwo E)) 3 の psAdd）。ratRing は M115F の真の有理数商環（Quot ratRel）。blc_branch_locus は任意の零因子なし・6·1≠0 の可換環 E 上の幾何的言明（実 formalDeriv＋実 evalSum＋零因子論法）で、blc_branch_locus_rat が実 ℚ へ具体化（blc_rat_no_zero_div=ratIUTField 整域性＋構成的ゼロ判定、blc_six_rat_ne_zero）。

### 4.2 決定的プローブ — A9 か A1 か
**A9（Belyi/三点分岐）である。** 理由:
- blc に **商環 ℚ[x]/(f) も体化も逆元探索も既約性も一切登場しない**（A1 の主語＝quotCRing/quotField_of_bezout/gefNFInv/pibIrreducible は blc に不在）。
- 主定理 blc_branch_locus は特定写像 f=3X²−2X³ の **ramification（分岐）についての幾何的言明**: (i) 上界＝二重根 (X−a)² があれば臨界点 a は Df=6X(1−X) の零点で、そこでの値 y=f(a) は必ず {0,1}；(ii) 下界＝blc_fiber_zero/one が y=0,1 に実際に二重根があることを陽な因子分解で証示；(iii) ∞ は blc_infty_chart で全分岐 e_∞=3。上界＋下界の対で「分岐値集合={0,1,∞}」を構成的に閉じる。これは「{0,1,∞} のみで分岐する被覆」= Belyi 写像の定義的性質そのもの。
- grep（belyi|tripod|dessin|noncritical|three.point|branch, blc 除外）= **既存出現ゼロ**。主語クラスは genuinely 新規。
- 対照: A1 テンプレ `CubicPolyQ`/`CbrtLinearFactor` は x³−2 の商環体構成・既約性（根⟹t³=2 矛盾）が主語。同じ evalSum を使うが用途/定理/主語が別。

### 4.3 再輸出（M270F+M274F）チェック
**再輸出でない。** formalDeriv/formalDeriv_mul_linFactor（M270F）・evalSum/evalHom_id_mul/evalHom_stable（M274F）は補題として**消費**（機構は正当に使い切る）されるが、blc_branch_locus は M270F の sep_repeated_factor（「(X−a)²∣f ⟹ f と Df が共通因子」の generic 分離補題）の再述ではない。blc_branch_locus は臨界点での**具体値 y=f(a) を f 固有の構造で {0,1} に釘付けする新規定理**（Df(a)=6a(1−a)=0 → 零因子なしで a∈{0,1} → y=f(a)∈{0,1}）。値一致の再確認だけの定理は置かれていない。

### 4.4 ∞ チャート / e_∞=3 の非空虚性
blc_infty_chart: f(1/u)·u³ = 3u−2（u≠0）。blc_infty_unit: 右辺の u=0 での値 = −2 ≠ 0（blc_two_rat_ne_zero 経由）。全分岐 e_∞=3 の非退化な顕示（付値ではなくチャート恒等式・§4.2 で正直に限定）。空虚でない。

### 4.5 psDvd 罠チェック
blc_branch_locus の重根仮定は **有界明示因子分解**（g : PS E, hg : IsPolyBounded E g 2, hfac : 等式）であって psDvd（∃q, g=d·q）ではない。§4.2 item 5 に明記の通り、a≠0 で X−a が単元化して psDvd が空虚に真になる罠を意図的に回避。定理は非空虚（下界 blc_fiber_zero/one が実際に仮説を満たす witness を供給）。

### 4.6 過大主張チェック
本体に **Belyi の定理（全曲線）/noncritical Belyi/cuspidalization/tripod π₁/スキーム・エタールサイト/A8 Tate 接続の主張は皆無**。blcP1=Option E.carrier（点集合）、blcMap は点写像、blc_map_infty_fiber のみ。π₁ ゼロ。§4.2 の正直な限定 7 項が実スコープと一致。過大主張なし。

### 4.7 二重計上チェック
ratRing/polyCRing（A1）・formalDeriv（M270F）・evalSum（M274F）は材料消費のみで新規 A9 定理を建てる。π₁/デッキ群/円分体/Gal（A3/A4/A5/A6/A7 主語）は本モジュールに一切登場せず主語 disjoint（§4.3 の宣言と本体一致を確認）。二重計上なし。

---

## 5. status 決定と正当化

**0 → 0.1。** blc はリポジトリ初の実『Belyi 化／三点分岐幾何』主語オブジェクトを genuinely 新規に建設し、実分岐軌跡決定定理（上界＋下界＋∞ チャートで {0,1,∞} を構成的に閉じる）を非空虚・clean-axiom で供給する。これは A1 の数体商環構成でも M270F+M274F の再輸出でもない（§4.2/4.3）。よって status 0 を脱する。

**0.1 上限（0.15/0.5 でない）**: 「遠アーベル幾何入力」の実体（π₁^ét/dessin/Galois 作用/cuspidalization）は依然ちょうど 0 で、実装は Belyi の**多項式/分岐軌跡側**のみ（title 前半 Belyi 化の第一歩）。数学内容は初等（導関数の零点＋評価）。P¹ はスキームでなく点集合 Option K、e_∞=3 はチャート恒等式で局所環の付値でない。忠実な部分ケース(0.5)には遠く、A5 の初回 0.1 と同格の「初の非自明な実主語インスタンス」帯に留まる。

**0.05 でない**: 新主語クラスの非空虚・clean-axiom な実分岐軌跡決定定理が genuinely landing した前進を過小評価しないため。

---

## 6. 結果の集計

Σ_A（weight×status, A9=0.1）:
A1 8×0.85=6.8, A2 8×0.65=5.2, A3 12×0.75=9.0, A4 14×0.55=7.7, A5 10×0.15=1.5, A6 14×0.55=7.7, A7 12×0.4=4.8, A8 12×0.57=6.84, **A9 10×0.1=1.0** → Σ=50.54。総 weight=100。

**柱A complete_pct = round(50.54) = 51**（compute_complete_pct.py 出力 {"A":51,...} と一致）。前回 50 から +1。

## 7. 変更ファイル
- `target_ledger.json`（A9 status 0→0.1）
- `graph-meta.json`（pillars.A complete_pct 50→51・A9 note prepend）
- `graph.json`（gen_graph.py 再生成・BelyiCubicReal は PILLAR 辞書で既に A 割当）
- `dashboard.md`（柱A 二軸 complete_pct 50→51・A9 note prepend）
- `audit/reaudit-A9-belyi-cubic-2026-07-11.md`（本記録）
