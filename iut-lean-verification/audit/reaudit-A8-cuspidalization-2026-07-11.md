# 独立再監査: A8 楕円 cuspidalization の幾何的基体（Q3TateCuspidalization / q3cu）— 2026-07-11

**監査者**: 独立・敵対的監査者（実装者要約・設計自己予測・ヘッダ `[実/…]` 主張・目標数値を非共有／判定は Lean 本体のみ）
**対象**: 柱A A8「楕円曲線/Tate 曲線の実被覆・cuspidalization」（前回 status 0.57・weight 12）
**契機**: 新規モジュール `IUT/Q3TateCuspidalization.lean`（prefix q3cu）が cuspidalization half の幾何的基体を主張。
**敵対的既定**: 模型/代理。「実」主張の立証責任は実装側。表示 52 の誘引（Σ_A≥51.5）に引きずられないこと。

---

## 判定（結論）

**A8 status 0.57 → 0.60（+0.03）**。設計自己予測 0.62（表示 52）は採らない。
**柱A complete_pct: 51 据え置き**（Σ_A = 44.12 + 12×0.60 = 51.32 → round 51。B18/C41/D18/E42 不変）。

一段落理由: 本モジュールはリポジトリ初の**実 [2]-同種**・**μ₂ 完全性（Klein 等号）**・**実開曲線の [2]-制限射**・**[2] 非全射 witness** をすべて本物・choice-free に建設し、前回監査が名指しした 5 gaps のうち 2（μ₂ 完全性・cuspidalization 基体 half）を discharge する。据え置き（0.57）は過小。しかし title 語 **cuspidalization proper の核心＝cuspidal 惰性群と π₁ 再構成アルゴリズム**（IUT 荷重の担い手）は 0 のまま（原理的ブロック・正直申告）で、開曲線も K 点の影の subtype にとどまる。substrate-only ゆえ +0.05（0.62）は cuspidalization 核心に迫るとの過大評価。前ラウンド（実 Tate 曲線＋2-捻れの土台建設 = +0.07）に対し本ラウンドは既建設 E₉ 上の自己同種＋等号昇格＝より周辺的で、+0.03 が honest。

---

## 1. rubric 分類（q3cu）

- `classification`: **real（部分・昇格）**。complete_pct を +0.03 動かす（substrate half のみ）。
- `principal_object`: 実 [2]-同種 q3cuSq: E₉(ℚ₃)=ℚ₃^×/9^ℤ → E₉（x↦x²）・その核＝ちょうど Klein 4 群・実開曲線 E₉∖E₉[2]→E₉∖{O} の [2]-制限射。
- `is_it_a_stand_in`: **no（同種・核・μ₂完全性は本物）／partial（開曲線は K 点影の subtype）**。q3cuSq は実 Grp Hom（Quot.lift・map_mul 証明済）。μ₂完全性は実 ℤ₃^× 補題。開曲線 q3cuOpen/q3cuPunct は `{x // …}` subtype でスキーム/エタールサイト/位相なし＝K 点の影。
- `self_declared_external`: cuspidal 惰性群・π₁ 再構成アルゴリズムを「0・原理的ブロック（柱E EtaleTheta 前提）」とヘッダ限定 1,2 で自認。
- `moves_complete_pct`: **yes（+0.03）**。実同種＋Klein 等号＋基体射＋非全射は新規実対象・置換。ただし核心 0 で cap。
- `evidence`: q3cuSq (78–92)・q3cu_sq_eq_square (96–99)・q3cu_mu2_complete (204–271)・q3cu_ker_eq_klein (279–293)・q3cuOpenMap (315)・q3cu_fiber_coset (322–334)・q3cu_not_surjective (358–366)。

---

## 2. フルビルド（自走）

`cd iut-lean-verification && export PATH="/root/lean4/bin:$PATH" && bash build.sh 2>&1 | tail`:

```
'IUT.q3cuSq' depends on axioms: [propext, Quot.sound]
'IUT.q3cu_mu2_complete' depends on axioms: [propext, Quot.sound]
'IUT.q3cu_ker_eq_klein' depends on axioms: [propext, Quot.sound]
'IUT.q3cuOpenMap' depends on axioms: [propext, Quot.sound]
'IUT.q3cu_not_surjective' depends on axioms: [propext, Quot.sound]
'IUT.q3cuCusp_exists' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```
**EXIT 0・no sorry。**

---

## 3. 独立 #print axioms（監査自作 scratch・全 A8c load-bearing 対象）

scratch `IUT/AxCheck.lean`（`import IUT.Q3TateCuspidalization`）で下記を実行し、実行後に scratch/olean 削除:

```
'IUT.q3cuSq' depends on axioms: [propext, Quot.sound]
'IUT.q3cu_sq_eq_square' depends on axioms: [propext, Quot.sound]
'IUT.q3cu_mu2_complete' depends on axioms: [propext, Quot.sound]
'IUT.q3cu_ker_eq_klein' depends on axioms: [propext, Quot.sound]
'IUT.q3cuOpenMap' depends on axioms: [propext, Quot.sound]
'IUT.q3cu_fiber_coset' depends on axioms: [propext, Quot.sound]
'IUT.q3cu_deck_free' depends on axioms: [propext, Quot.sound]
'IUT.q3cu_not_surjective' depends on axioms: [propext, Quot.sound]
'IUT.q3cu_ppow_dvd' depends on axioms: [propext, Quot.sound]
'IUT.q3cuData' depends on axioms: [propext, Quot.sound]
'IUT.q3cuCusp_exists' depends on axioms: [propext, Quot.sound]
```
**全 11 対象 = [propext, Quot.sound] のみ。新規 Classical.choice / sorryAx 皆無。** 失格事由なし。

---

## 4. 決定的プローブ（本体判定）

### 4.1 q3cuSq は本物の実同種か（A5c 再ラベルでないか）— YES
`q3cuSq : Hom (q3tCurve 2) (q3tCurve 2)`（78）は `map := Quot.lift (fun a => (q3tProj 2).map (q3tGrp.mul a a)) …`＝実 ℚ₃^× 上の**平方**を実商群 E₉ へ降ろす。well-def は a⁻¹b∈q^ℤ ⟹ proj(a²)=proj(b²)（q3t_proj_eq_iff 経由・実証明）、map_mul は可換性 q3cu_sq_hom_aux で証明。**A5c の `q3tcHom : Hom (q3tCurve (m*n)) (q3tCurve m)`（Q3TateCoverTower.lean:114）とは domain/codomain（自己写像 vs レベル替え E_{qⁿ}→E_q）も map（a↦a·a vs a↦a）も別物**＝再ラベルでない。リポジトリ初の実自己同種。**本物。**

### 4.2 ★ q3cu_mu2_complete は本物に証明されているか（Klein 等号の要）— YES
`q3cu_mu2_complete (u) (hu: u·u=1) : u=1 ∨ u=q3tNegOne`（204）。
- witness: `obtain ⟨a, ha, hpa⟩ := u.property`＝IsZpUnit の**実∃-witness**（ZpUnits.lean:38 `IsZpUnit = ∃ a, x.val 1 = mk a ∧ ¬3∣a`）。整数対角像に限定されない**任意の** ℤ₃^× 元 u に適用（u.property から取得・choice 不要の Exists.elim）。
- 分岐: `hcase : 3∣(a-1) ∨ 3∣(a+1) := by omega`（hpa=¬3∣a を消費した 3分律・**結論を仮定していない**）。
- 核: `q3cu_mu2_level`（175）が hu を `congrArg Subtype.val hu`→各レベル n で `zmodMul(3^n)(j)(j)=mk 1` を取り出し `quot_exact` で **3^n∣(j²−1)=（q3cu_diff_sq）(j−1)(j+1)** を、`u.val.property hn` から塔整合 **3∣(j−a)** を実導出。次に `q3cu_ppow_dvd (m+1)`（素冪 Euclid 反復・euclid_int の n 段帰納・126）で「片方の因子 j∓1 のみ 3 と可約」を使い 3^{m+1}∣(j∓1) を得て `Quot.sound`。
- **⊆ へのフォールバックなし・結論の秘匿仮定なし。** hu を実際に消費し、非空虚（q=9 で μ₂⊂ℚ₃ 実在）。**本物の証明。q3tt 正直限定 3「Klein ⊆ のみ」を等号へ discharge。**

### 4.3 q3cu_ker_eq_klein の → は mu2_complete を消費するか（q3tt 再輸出でないか）— YES
`q3cu_ker_eq_klein`（279）→ 方向: `⟨k, u, q3cu_mu2_complete u ((q3cu_ker_iff k u).mp h), ha.symm⟩`＝**mu2_complete を直接消費**し u=±1 を供給。これは逆包含 **E₉[2] ⊆ Klein**（新規）で、q3tt_klein_torsion（Klein ⊆ E₉[2]＝← 方向・既存）の再輸出ではない。**本物の新内容。**

### 4.4 開曲線は実際に使われるか（飾りでないか）— YES
`q3cuOpen`（302）が `q3cuOpenMap : q3cuOpen → q3cuPunct`（315）の**定義域**、`q3cuPunct`（298）が終域として実使用。q3cu_open_sub（306）で包含 E∖E[2]⊆E∖{O} を実証明。`q3cu_fiber_coset`（322）はファイバー＝Klein 剰余類の双方向 iff で非空虚（← は a=y·x⁻¹∈Klein を q3cu_ker_eq_klein 消費で構成）。**飾りでない。** ただし subtype ゆえ scheme/étale/位相なし＝K 点の影（cap 要因）。

### 4.5 q3cu_not_surjective は本物の正直装置か — YES
`q3cu_not_surjective : ∀ x, q3cuSq.map x ≠ q3ttW1`（358）。[1]=[(1,1)] は付値パリティ（1 奇）ゆえ平方像 [2k,u²] に入らない（q3tt_class_eq_iff→2∣(1−2k) の omega 矛盾）。E(ℚ₃)/2E(ℚ₃)≠0 の影を定理として顕示。**本物・非全射の正直申告が消えていない。**

### 4.6 過大主張・再輸出・二重計上・hidden choice — NONE
- 惰性/再構成の overclaim なし（ヘッダ限定 1,2 で 0・原理的ブロックと明記・スキーム/エタールサイト/位相を主張せず・[2] 全射を主張せず＝non-surj を定理化）。
- q3tt/q3t の正直限定は**不変更**（q3tt ヘッダ限定 3「Klein ⊆・μ₂完全性未達」原文のまま／既存ファイル無改変）。
- 二重計上なし: A5c/A4（レベル替え商写像・q 平行移動デッキ・コンパクト曲線）と主語 disjoint（自己同種・捻れ平行移動・開曲線）／A9（多項式/P¹ 不登場）／A2/A6/A7（mu2_complete は輸出先 cusp 集合決定＝A8c 帰属）。
- hidden choice なし（§3 の全 A8c 対象 [propext,Quot.sound]・obtain は Exists.elim・witness は IsZpUnit ∃ 形）。

---

## 5. 評価判断（substrate vs inertia — 数値の決定打）

| 観点 | 実測 |
|---|---|
| 実同種（初） | 本物・real・A5c 別物 |
| μ₂ 完全性→Klein 等号 | 本物・choice-free・gap 4 discharge |
| 実開曲線＋2 本の射 | real だが subtype（K 点影・scheme/étale/位相なし） |
| [2] 非全射 witness | 本物・正直装置 |
| **cuspidal 惰性群** | **0**（原理的ブロック・柱E 前提） |
| **π₁ 再構成アルゴリズム（cuspidalization 本体）** | **0**（原理的ブロック） |

cuspidalization は本来「cusp 惰性を用いて開曲線 π₁ を群論的に再構成する**アルゴリズム**」。本モジュールはその**幾何的基体（曲線と 2 射）**を建てるが、**惰性群も再構成アルゴリズムも 0**——すなわち IUT 荷重を担う anabelian 核心には未着手で、これは玄関に相当する。5 named gaps のうち 2 を discharge した前進は本物だが、+0.05（0.62）だと「substrate が cuspidalization half のほぼ半分」を含意し過大。前ラウンドが**曲線オブジェクトと 2-捻れそのもの**を建てて +0.07 だったのに対し、本ラウンドは既建設 E₉ 上の自己同種と等号昇格＝より周辺的ゆえ **+0.03 が単調性に整合**。

→ **0.60 を採用**（Σ_A=51.32・表示 51）。0.62（表示 52）は境界クロス狙いの過大評価ゆえ不採、0.57 据え置きは 2 gaps 本物 discharge を過小ゆえ不採。0.61（Σ_A=51.44・表示 51）でも表示は同じだが、substrate-only を honest に映すには +0.03 が妥当。

---

## 6. complete_pct への反映（適用済み）

- `target_ledger.json`: A8 status 0.57 → **0.6**。
- `tools/compute_complete_pct.py` 自走 → `{"A": 51, "B": 18, "C": 41, "D": 18, "E": 42}`（柱A 51 据え置き）。
- `graph-meta.json`: pillars.A.complete_pct 51 据え置き・complete_note に本ラウンド dated A8 entry を prepend。
- `tools/gen_graph.py` → graph.json 再生成（modules=619 edges=1217）。
- `dashboard.md` 二軸表 柱A セルに A8 note prepend（51% 不変）。

**コミット/プッシュはしない。**
