# 独立再監査記録 — A5「実 tempered π₁^temp」 (2026-07-10)

- 監査者: 独立敵対的監査エージェント (opus, Claude Code)
- 対象: `IUT/Q3TateDeck.lean` (A5a, prefix q3td) / `IUT/Q3TemperedPi1.lean` (A5b, prefix q3tp)
- 依存精読: Q3TateCurve / Q3UnitsGroup / Q3LocalField / TateModuleZ3 / CyclotomicTowerLimit / TemperedPi1 (M364F) / DiscreteRigidity (M333F)
- 既定スタンス: 模型 (立証責任は「実」主張側)。ヘッダの `[実／...]` 主張・自己申告値・dashboard/design doc は判定に不使用。判定は def/structure/theorem の本体のみ。
- 判定: **A5 status 0 → 0.1**。柱A complete_pct **47 → 48**（`compute_complete_pct.py` 機械計算・下記）。

---

## 1. ビルド (build.sh tail)

`cd iut-lean-verification && export PATH="/root/lean4/bin:$PATH" && bash build.sh 2>&1 | tail -40` の末尾:

```
'IUT.q3td_infinite_order' depends on axioms: [propext, Quot.sound]
'IUT.q3td_deck_free' depends on axioms: [propext, Quot.sound]
'IUT.q3td_fiber_orbit' depends on axioms: [propext, Quot.sound]
'IUT.q3tdData' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_extension_exact' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_deck_realize_ker' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_exists_unconditional' depends on axioms: [propext, Quot.sound]
'IUT.q3tpGalAct' depends on axioms: [propext, Quot.sound]
'IUT.q3tpData' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
Expected: standard axioms only. mono_implies_bi is axiom-free;
bi_implies_mono_classical requires Classical.choice (the point of M1-2).
```

EXIT=0、成功行 `OK: all theorems verified, no sorry.` 確認。

## 2. 監査者自身の #print axioms (IUT/AuditA5.lean を自作・実行後削除)

`lake env lean IUT/AuditA5.lean` の出力 (verbatim・全24 load-bearing 対象):

```
'IUT.q3td_infinite_order' depends on axioms: [propext, Quot.sound]
'IUT.q3td_period_inj' depends on axioms: [propext, Quot.sound]
'IUT.q3td_ker' depends on axioms: [propext, Quot.sound]
'IUT.q3td_deck_free' depends on axioms: [propext, Quot.sound]
'IUT.q3td_deck_transitive' depends on axioms: [propext, Quot.sound]
'IUT.q3td_fiber_orbit' depends on axioms: [propext, Quot.sound]
'IUT.q3td_deck_over_proj' depends on axioms: [propext, Quot.sound]
'IUT.q3tdPeriodHom' depends on axioms: [propext, Quot.sound]
'IUT.q3tdDeck' depends on axioms: [propext, Quot.sound]
'IUT.q3tdData' depends on axioms: [propext, Quot.sound]
'IUT.q3tdDeck_exists' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_extension_exact' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_incl_injective' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_proj_surjective' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_deck_realize_ker' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_deck_faithful' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_exists_unconditional' depends on axioms: [propext, Quot.sound]
'IUT.q3tpGalAct' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_gal_act_mu' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_gal_act_deck_trivial' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_gal_act_one' depends on axioms: [propext, Quot.sound]
'IUT.q3tp_discrete_not_finite' depends on axioms: [propext, Quot.sound]
'IUT.q3tpDeckRealize' depends on axioms: [propext, Quot.sound]
'IUT.q3tpData' depends on axioms: [propext, Quot.sound]
```

**全て `[propext, Quot.sound]` のみ。Classical.choice / sorryAx は一つも無し。** scratch (`IUT/AuditA5.lean`) と stray olean は削除済 (git status clean)。

## 3. 身代わり / 過大主張プローブ (本体判定)

### 3.1 デッキ群 ℤ の主語は本物か
- `q3tGrp := QpUnits 3 isPrime_three` = `prodGrp intGrp (zpUnits 3 isPrime_three)` = 実 ℚ₃^× の群提示 3^ℤ×ℤ₃^×。Q3UnitsGroup の `q3uEmbed`/`q3u_embed_inj` で実 ℚ₃=ℤ₃[1/3] 内へ単射同定 (A2=0.65 監査済)。Nat/Bool/Fin 身代わりでない。
- `q3tQ m = ((m:Int), one)` = 実 Tate パラメータ 3^m (第1成分＝実付値 m)。
- `q3tProj m = quotientProjN ...` → 実商群 E_q=ℚ₃^×/q^ℤ (`q3tCurve`, A8=0.57 監査済)。
- デッキ群 ℤ = `intGrp` = 本物の加法群 (ℤ,+,0,−)。**主語は全て実対象**。

### 3.2 q3td_infinite_order は外部 Prop 仮説ゼロで discharge するか
- 文: `theorem q3td_infinite_order (m : Nat) (hm : 1 ≤ m) : discRig_infiniteOrder_hypothesis q3tGrp (q3tQ m)` (Q3TateDeck.lean:117)。仮説は `1 ≤ m` のみ、外部 Prop なし。**theorem** であって axiom/hypothesis でない。
- `discRig_infiniteOrder_hypothesis` は M333F (DiscreteRigidity.lean:54) が定義した Prop `∀ n:Int, tateZpow G g n = G.one → n = 0` と同一。M333F はこれを「本層では決して自前で導出しない」外部 crux と明記していた。
- 証明本体: qᵗ の第1成分 m·t=0 (`q3td_zpow_fst`)、`Int.eq_of_mul_eq_mul_left` (m≥1) で t=0。実 ℚ₃^× の**自由 ℤ 付値成分**を使う genuine な discharge (抽象 IUTField K 上で不可能だったのは K^× の付値が rank 0 になり得たため。ここは主語が実 ℚ₃^× で第1成分が本物の ℤ 付値ゆえ導出可能)。**名指し外部仮説の実 discharge を確認**。

### 3.3 q3td_deck_free / q3td_deck_transitive は非退化か
- `q3tdDeck m : GAction intGrp` (act t x = qᵗ·x) は実担体 `q3tGrp.carrier` 上の作用 (GAction は act_one/act_mul 則付きの genuine 作用構造・GaloisCategory.lean:50)。
- free: `q3td_deck_free` は qᵗ·x=x ⟹ t=0 を infinite_order 経由で証明 (空虚でない)。
- transitive: `q3td_deck_transitive` は proj x=proj y から `quot_exact` で mem(x⁻¹y) を得て**実 ∃-witness t** を返す。非退化。

### 3.4 A5b: tmzLimit は本物の ℤ₃(1) 逆極限か / 無条件性 / 実 Gal 作用
- `q3tpGroup := prodGrp tmzLimit intGrp`。`tmzLimit := limitGrp tmzSystem` (TateModuleZ3.lean:171)。`tmzSystem = natSystem tmzG tmzT ...` は実 μ_{3^{n+1}}=`cmrGrp (n+1)` の塔 (遷移 `tmzT` は実指数読み替え・忠実性 `tmz_iota_cube` で ι(t y)=y³)。**真の逆極限 = 実 ℤ₃(1)** (A7=0.35 監査済・A3 の ctl 機構)。積 (prodGrp) でなく inverse limit。
- `q3tp_exists_unconditional : Nonempty Q3TemperedPi1Data` (:245) の infinite_order フィールドは `q3td_infinite_order 1 (Nat.le_refl 1)` で充填＝外部仮説不要。M364F `tmp_exists` は `hInf : tmp_infiniteOrder_hypothesis K q` を引数に取る (TemperedPi1.lean:224)。**無条件化を確認** (質的前進)。
- `q3tpGalAct s = fun x => ((tmzActHom s).map x.1, x.2)` (:136)。`tmzActHom` (TateModuleZ3.lean:300) は成分ごと実 Galois 作用 `cgarAct` (実体自己同型の μ への制限) で s∈`ctlProfinite` (=実 Gal(ℚ(ζ_{3^∞})/ℚ) 逆極限)。`q3tp_gal_act_mu` で μ 部は tmzActHom s (χ 冪)。**fake でない実作用**。

### 3.5 過大主張チェック
- 定義本体のどこにも「全 tempered π₁」「位相的被覆」「非可換 θ」「全 G_{ℚ₃}」「全 ẑ(1)」の主張なし。
- q3tpGroup は commutative 直積 ℤ₃(1)×ℤ (pro-3・可換)。Grp は離散群構造で**位相なし**。gal_act は円分切片 `ctlProfinite` のみ。
- 正直な限定 (位相なし・離散商 ℤ のみ・pro-3・可換・円分切片・p=3) はヘッダに明記されている (消去・弱化なし)。**過大主張なし**。

---

## 4. 構造化ルーブリック出力

### A5a (Q3TateDeck)
- **classification**: real (partial)
- **principal_object**: 実 Tate 被覆 ℚ₃^×→E_q=ℚ₃^×/q^ℤ のデッキ群 ℤ (=q^ℤ⊂実 ℚ₃^×) の実主語上の作用。
- **is_it_a_stand_in**: no。主語 q3tGrp=実 ℚ₃^× (3^ℤ×ℤ₃^×↪実 ℚ₃)、q3tQ m=実 3^m、q3tProj=実商射影。ℤ は本物の intGrp。Nat/Bool/Fin 身代わりなし。
- **self_declared_external**: 併設の M333F/M364F 仮説付き機構 (discRig_infiniteOrder_hypothesis 引数版・temperedPi1Data) は残置 (§2(a) 昇格規約)。本モジュール自身は core 対象を外部と自認していない。
- **moves_complete_pct**: yes (実対象・外部仮説の実 discharge)。ただし離散商 ℤ のみ。
- **evidence**: q3td_infinite_order (:117)、q3td_period_inj (:91)、q3td_ker (:107)、q3tdDeck:GAction (:130)、q3td_deck_free (:157)、q3td_deck_transitive (:171)、q3td_fiber_orbit (:182)、Q3TateDeckData/q3tdData (:197,:218)。

### A5b (Q3TemperedPi1)
- **classification**: real (partial)
- **principal_object**: pro-3 tempered 群 π₁^{temp,(3)}(E_q)=ℤ₃(1)×ℤ (両成分実)、拡大 1→ℤ₃(1)→π₁^{(3)}→ℤ→1、実 Gal 作用付き。
- **is_it_a_stand_in**: no。tmzLimit=limitGrp tmzSystem=実 ℤ₃(1) 逆極限 (μ 塔)、intGrp=実 ℤ、tmzActHom=実 Galois 作用。抽象 ẑ (M364F の zhat) を実 ℤ₃(1) へ置換。
- **self_declared_external**: M364F TemperedPi1Data K/tmp_exists/tmp_infiniteOrder_hypothesis は残置。q3Ring が IUTField を持たない (A2 恒久限定) ため新 structure を立てた旨明記。
- **moves_complete_pct**: yes。ただし profinite 端は A7 既算入の ℤ₃(1) の再消費・拡大は自明直積。
- **evidence**: q3tpGroup (:60)、q3tp_extension_exact (:90)、q3tpDeckRealize/q3tp_deck_realize_ker (:111,:117)、q3tp_deck_faithful (:123)、q3tpGalAct/q3tp_gal_act_mu (:136,:149)、q3tp_exists_unconditional (:245)、Q3TemperedPi1Data/q3tpData (:179,:221)。

---

## 5. status 決定と根拠

**A5 = 0.1**。

- **0 を脱する理由**: 初の実 (非模型) tempered 対象が実曲線に接続。実主語 (実 ℚ₃^×・実 Tate 曲線・実 ℤ₃(1)) ＋外部仮説ゼロ (q3td_infinite_order で M333F/M364F 名指し crux を無条件 discharge・q3tp_exists_unconditional で M364F 条件付き存在を無条件化) ＋全 axiom clean。身代わりでない。
- **0.5 に遠い理由 (全 A5 target の忠実な部分ケースでない)**: (1) 位相・解析構造ゼロ (Berkovich/rigid 被覆理論そのものでなく K 点の群論的影)。(2) 離散**商** ℤ ＋ pro-3 ℤ₃(1) のみ・compact E_q の**可換** tempered (IUT 本丸 punctured 曲線の**非可換** θ-Heisenberg 構造は範囲外)。(3) 拡大は自明直積 (分裂中心・最も退化)・profinite 端 ℤ₃(1) は A7 既算入対象の再消費。(4) Gal は円分切片 Gal(ℚ(ζ_{3^∞})/ℚ) で実 G_{ℚ₃} でなく A7 超の新 Galois 内容なし。(5) pro-3・p=3 固定・幾何的 Tate 加群 q^{1/3^n} 成分未構成。
- **0.05 でない理由**: 外部仮説の無条件 discharge ＋実担体上の自由推移デッキ作用 ＋両端実の拡大 ＋無条件存在が全て clean landing した「初の実 tempered step」を過小評価しないため。
- **0.15 でない理由**: A5b の第2成分 (ℤ₃(1)) は A7 既算入対象の再消費が中心で新規実構成でなく、非可換 IUT tempered 構造が完全欠落ゆえ「質的な第2実部分」とまでは言えない。

## 6. 集計

- ledger `target_ledger.json` pillars.A A5 status: 0 → **0.1**。
- `python3 tools/compute_complete_pct.py` → `{"A": 48, "B": 18, "C": 41, "D": 18, "E": 42}`。
- Σ_A = Σ(weight×status)/Σweight×100 = 47.74 → 丸め **48**。柱A **47 → 48**。
- graph-meta.json pillars.A complete_pct=48 に更新・complete_note に本ラウンド前置。progress_pct=99 据え置き (2 新規実モジュール追加だが骨格被覆は既に飽和域)。dashboard.md 二軸表 A 行を 48% に同期。
