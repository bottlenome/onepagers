# 独立再監査記録 — A4「実 π₁^ét（Tate 曲線の格子方向 pro-l 逆極限オブジェクト・忠実/普遍作用）」 (2026-07-11)

- 監査者: 独立敵対的監査エージェント (opus, Claude Code)
- 対象: `IUT/Q3TatePi1Etale.lean`（A4a・prefix q3pe・NEW）／`IUT/Q3TatePi1Comparison.lean`（A4b・prefix q3pc・NEW）
- 依存精読（主語が本物かの裏取り）: `IUT/Q3TateCoverTower.lean`(A5c q3tc・既算入)・`IUT/Q3TateDeck.lean`(A5a q3td・既算入)・`IUT/TemperedTower.lean`(M374F ttwInverseLimit/Zp/ttwProfiniteToLadic/ttwDiscreteComplete)・`IUT/TateCoverGroup.lean`(M188F tateProfinite=zhat 裸 ẑ)・`IUT/LocalCFT.lean`(padicSystem/Zp/toZp)・`IUT/Profinite.lean`(limitGrp/InverseSystem/limit_universal/limitProj/zmod)・`IUT/Q3TateCurve.lean`(q3t・A8 監査済実 E_q)・prior audit `reaudit-A5c-cover-tower-2026-07-10.md`
- 既定スタンス: 模型/A5 再消費（立証責任は「A4 固有＝副有限 π₁^ét オブジェクトの新規実建設」主張側）。ヘッダの `[実／昇格]` 主張・design doc `audit/A4-real-pi1-etale-tate-detail-2026-07-11.md`・実装者要約・dashboard 自己分類・目標値 0.55 は判定に不使用。判定は def/structure/theorem の本体のみ。
- **判定: A4 status 0.5 → 0.55**。柱A complete_pct **49 → 50**（`compute_complete_pct.py` 機械計算・下記）。

---

## 1. ビルド (build.sh tail)

`cd iut-lean-verification && export PATH="/root/lean4/bin:$PATH" && bash build.sh 2>&1 | tail` の末尾（A4a/A4b 対象を含む）:

```
'IUT.q3peLimitAct' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_limit_act_natural' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_fin_faithful' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_limit_faithful' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_fiber_orbit' depends on axioms: [propext, Quot.sound]
'IUT.q3pePi1_exists' depends on axioms: [propext, Quot.sound]
'IUT.q3pc_universal_cover_equivariant' depends on axioms: [propext, Quot.sound]
'IUT.q3pc_completion_act' depends on axioms: [propext, Quot.sound]
'IUT.q3pc_pi1_universal' depends on axioms: [propext, Quot.sound]
'IUT.q3pcSurrogateAct' depends on axioms: [propext, Quot.sound]
'IUT.q3pc_surrogate_nontrivial' depends on axioms: [propext, Quot.sound]
'IUT.q3pcComparison_exists' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```

EXIT=0、成功行 `OK: all theorems verified, no sorry.` 確認。

## 2. 監査者自身の #print axioms (IUT/AuditA4Scratch.lean を自作・実行後削除)

`lake env lean IUT/AuditA4Scratch.lean` の出力 (verbatim・全 20 load-bearing 対象):

```
'IUT.q3peStep' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_step_deck' depends on axioms: [propext, Quot.sound]
'IUT.q3peLimitAct' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_limit_act_natural' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_deck_over' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_fin_faithful' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_fin_act_inj' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_limit_faithful' depends on axioms: [propext, Quot.sound]
'IUT.q3pe_fiber_orbit' depends on axioms: [propext, Quot.sound]
'IUT.q3peData' depends on axioms: [propext, Quot.sound]
'IUT.q3pePi1_exists' depends on axioms: [propext, Quot.sound]
'IUT.q3pc_universal_cover_equivariant' depends on axioms: [propext, Quot.sound]
'IUT.q3pc_completion_act' depends on axioms: [propext, Quot.sound]
'IUT.q3pc_pi1_universal' depends on axioms: [propext, Quot.sound]
'IUT.q3pc_pi1_act_via_cone' depends on axioms: [propext, Quot.sound]
'IUT.q3pcSurrogateAct' depends on axioms: [propext, Quot.sound]
'IUT.q3pc_surrogate_natural' depends on axioms: [propext, Quot.sound]
'IUT.q3pc_surrogate_nontrivial' depends on axioms: [propext, Quot.sound]
'IUT.q3pcData' depends on axioms: [propext, Quot.sound]
'IUT.q3pcComparison_exists' depends on axioms: [propext, Quot.sound]
```

**全て `[propext, Quot.sound]` のみ。Classical.choice / sorryAx は一つも無し。** scratch (`IUT/AuditA4Scratch.lean`) と stray olean は削除済 (`git status --short` 空＝clean)。

## 3. 身代わり / 過大主張 / 非空虚 / ATTRIBUTION プローブ（本体判定）

### 3.1 q3pePi1 = 逆極限オブジェクトは本物か（身代わりでないか）
- `q3pePi1 l := ttwInverseLimit l`（TemperedTower.lean:86 で `= Zp l`）、`Zp l := limitGrp (padicSystem l)`（LocalCFT.lean:90）。`limitGrp`（Profinite.lean:167）は整合族 `{ s : ∀ i, (S.G i).carrier // Compatible S s }` を担体とする**真の逆極限群**。`padicSystem l` は ℤ/l^k の割り切り逆系（zmod=intGrp の実商）。**Nat/Bool/Fin 身代わりでない・ラベル付きコピーでない**。π₁ オブジェクト＝ℤ_l=lim ℤ/l^k は本物の副有限群。

### 3.2 q3peLimitAct は逆極限オブジェクトの実曲線塔への実作用か（単なる裸 ℤ_l でないか）
- `q3peLimitAct m l k : GAction (q3pePi1 l)`、`act := fun γ x => (q3tcDeckFin m (l^k)).act (γ.val k) x`。carrier=実曲線 `(q3tCurve (m·l^k)).carrier`（A8 監査済実 Tate 曲線）。γ∈ℤ_l は第 k 成分 γ.val k∈ℤ/l^k を通じて実曲線 E_{q^{l^k}} に作用。act_one/act_mul は q3tcDeckFin の作用則から本証明。
- **単一段では ℤ_l の作用が有限商 ℤ/l^k を経由するのは副有限群の作用として当然**。逆極限オブジェクト固有の内容は (a) 段間自然性 `q3pe_limit_act_natural`——γ.property（整合族条件 `(zmodTrans …).map (γ.val (k+1)) = γ.val k`）を**本質的に使用**して塔ステップ q3peStep と作用が可換することを証明・(b) 全段横断の忠実性（3.3）。整合族なしには両者とも証明できないため、これは「実曲線塔上のファイバー関手への副有限 π₁ の作用」として genuine。**裸 ℤ_l で実曲線未接続、ではない**。

### 3.3 q3pe_limit_faithful は逆極限段で忠実性を本物・非空虚に証明しているか（A5c 名指しギャップの discharge）
- 有限段 `q3pe_fin_faithful (m n) (hm:1≤m) (j)`: act(mk j)[1]=[1] ⟹ (n:Int)∣j。quotientProjN_ker→q3td_zpow_fst 第1成分 (m·n)·t=m·j→m≥1 左簡約→n·t=j。実証明・∃仮説受けでない。
- 逆極限段 `q3pe_limit_faithful (m l) (hm:1≤m) (γ) (h: ∀ k, act γ [1]=[1]) : γ = one`。`Subtype.ext`＋`funext k` で各成分 γ.val k を Quot.ind で mk j に落とし q3pe_fin_faithful で l^k∣j、Quot.sound で mk j=one。**逆極限レベルの忠実性**（全段自明作用⟹γ=1＝ℤ_l 元を全塔が分離）を choice-free・閉形式 witness で証明。**非空虚**: 各段で q3pe_fin_faithful を実使用（空虚な∀でない）。作用が左移動なので「基点 [1] 上で自明」=「その段の作用が自明」ゆえこれは genuine な作用忠実性。**A5c 監査ディスカウント(1)「q3tcDeckFin は well-def GAction だが忠実性未証明」を正面 discharge、しかも極限段で**。

### 3.4 ATTRIBUTION（決定的）: A4 固有の新規か、A5 再消費か
- A5c 監査（reaudit-A5c-cover-tower-2026-07-10.md §5・ヘッダ限定）が**明示 defer した 2 件**:
  - 限定(2)「塔の逆極限 ℤ_l との接続は M374F 既存機構（ttwDeckTower）の消費に留める（**実逆極限の幾何的実現は後続**）」。
  - ディスカウント(1)「有限デッキ q3tcDeckFin は well-def GAction だが**忠実性/自由性未証明**」。
- A4a/A4b はこの 2 件を正面で埋める: (i) 逆極限オブジェクト q3pePi1=ℤ_l 自身が実曲線塔へ作用（q3peLimitAct）＋段間自然性（q3pe_limit_act_natural・整合族使用）＝「実逆極限の幾何的実現」。A5c には**逆極限オブジェクトの作用は皆無**（段ごとの有限 ℤ/l^k 作用のみ）。(ii) q3pe_fin_faithful＋q3pe_limit_faithful＝忠実性 discharge。
- 主語の対比: **A5 の主語** = tempered 拡大 1→ℤ₃(1)→π₁^{(3)}→ℤ→1（A5b）と有限中間被覆＋有限デッキ ℤ/n（A5c）。**A4 の主語** = 副有限 π₁ 逆極限オブジェクト ℤ_l＋その忠実な自然作用＋普遍性＋surrogate 昇格。q3pe_limit_act_natural・q3pc_pi1_universal・q3pcSurrogateAct はいずれも**逆極限オブジェクトを主語**とし、A5 の deck ℤ/ℤ/n の再輸出ではない。
- **判定: A5 深化の変装ではなく、A5c が明示 defer した A4 固有の逆極限オブジェクト層の genuinely 新規建設**。A5c の有限デッキ q3tcDeckFin は**材料として消費**するが、逆極限オブジェクト・その自然性・全塔忠実性・普遍性・ẑ 昇格は A5 に存在しない新規実対象＝**二重計上でない**。

### 3.5 q3pcSurrogateAct は裸 ẑ の genuine 昇格か・非空虚か
- `tateProfinite := zhat`（TateCoverGroup.lean:151・M188F・裸 ẑ=limitGrp zmodSystem＝本文精読で裏取り）。
- `q3pcSurrogateAct m l k : GAction tateProfinite`、`act := fun σ x => (q3peLimitAct m l k).act ((ttwProfiniteToLadic l).map σ) x`。裸 ẑ が Ẑ↠ℤ_l（ttwProfiniteToLadic・M374F 実 Hom）経由で実曲線 E_{q^{l^k}} に作用。act_one/act_mul は ttwProfiniteToLadic の map_one/map_mul＋q3peLimitAct の作用則から本証明。
- **非空虚** `q3pc_surrogate_nontrivial`: σ=toZhat.map 1・x=[1]・2≤l^k のとき q3pe_fin_faithful で l^k∤1 を用いて作用が [1] を動かすことを証明。**裸 ẑ が実曲線を実際に動かす**（身代わりでない）。CLAUDE.md §2(a) 名指し昇格例「Tate surrogate→実 π₁^ét」の作用レベル第一歩。

### 3.6 q3pc の再輸出成分（新規深度の限定）
- `q3pc_pi1_universal := exact limit_universal (padicSystem l) …`＝Profinite.lean の既存 limit_universal の π₁ 主語への特化（機構は既存）。`q3pc_universal_cover_equivariant`・`q3pc_completion_act`・`q3pc_pi1_act_via_cone` は rfl 級橋。深い新規内容は A4a の q3peLimitAct＋q3pe_limit_act_natural＋q3pe_limit_faithful＋q3pc の surrogate 昇格に集中。

### 3.7 過大主張チェック
- def/theorem 本体のどこにも「全 π₁^ét（ẑ×ẑ(1)）」「一般双曲的曲線/Spec」「位相/スキーム/エタールサイト」「μ 方向 ℤ₃(1)=A7 との接続」「anabelian 逆再構成」「Aut(F)/圏登録」の主張なし。q3pePi1 は pro-l 格子方向スライス ℤ_l のみ・「被覆」は K-点群の全射準同型（q3peStep/q3tcHom は Grp の Hom）・q3pcSurrogateAct は GAction（圏登録でない）。ヘッダの正直な限定 7 項（pro-l 単一 l・compact E_q・格子方向のみ μ 方向不構成・位相/スキーム皆無・anabelian/圏登録なし・surrogate 併設・0.5 帯明記）が**実スコープと一致**（消去/弱化なし）。**過大主張なし**。

---

## 4. 構造化ルーブリック出力

### A4a (Q3TatePi1Etale)
- **classification**: real (partial)
- **principal_object**: 実被覆塔デッキ群の逆極限 π₁^ét オブジェクト ℤ_l=q3pePi1=ttwInverseLimit（=limitGrp padicSystem・真の逆極限群）が実 Tate 曲線塔 E_{q^{l^k}}(ℚ₃)=q3tCurve(m·l^k) へ作用する層（q3peLimitAct）＋段間自然性（q3pe_limit_act_natural）＋有限/逆極限段忠実性（q3pe_fin_faithful/q3pe_limit_faithful）＋ファイバー＝軌道（q3pe_fiber_orbit）。
- **is_it_a_stand_in**: no。ℤ_l=limitGrp padicSystem（Nat/Bool/Fin でない・整合族担体）・carrier=実曲線 carrier（A8 監査済）・zmod l^k=実 ℤ/l^k。
- **self_declared_external**: 併設の M374F 外部仮説・A5c ヘッダ限定・tateProfinite surrogate・profPi1_trivialTower は残置（§2(a) 昇格規約）。本モジュール core は外部自認なし。
- **moves_complete_pct**: yes（A5c 明示 defer の逆極限オブジェクト層＋忠実性を新規実建設）。増分は小（格子スライス・位相なし）。
- **evidence**: q3peStep(:59)・q3pe_step_deck(:92)・q3pePi1(:104)・q3peLimitAct(:109)・q3pe_limit_act_natural(:123)・q3pe_fin_faithful(:152)・q3pe_limit_faithful(:211)・q3pe_fiber_orbit(:236)・Q3TatePi1EtaleData/q3peData/q3pePi1_exists(:263,:299,:314)。

### A4b (Q3TatePi1Comparison)
- **classification**: real (partial) — 深度は A4a に依存、本ファイルは比較/普遍性/surrogate 昇格の束ね（一部再輸出）。
- **principal_object**: 逆極限 π₁ オブジェクトの普遍性（q3pc_pi1_universal＝limit_universal 発火）・完備化/普遍被覆比較（q3pc_completion_act/q3pc_universal_cover_equivariant）・**裸 ẑ=tateProfinite の実曲線への主語替え**（q3pcSurrogateAct＋非自明 q3pc_surrogate_nontrivial）。
- **is_it_a_stand_in**: no（tateProfinite=zhat は裸 ẑ だが実曲線に作用する形で昇格・q3peLimitAct 経由で実担体）。
- **moves_complete_pct**: yes（surrogate→実昇格の作用レベル第一歩・A4a と束ねて）。ただし q3pc_pi1_universal 等は既存機構の再輸出。
- **evidence**: q3pc_universal_cover_equivariant(:63)・q3pc_completion_act(:76)・q3pc_pi1_universal(:88)・q3pcSurrogateAct(:117)・q3pc_surrogate_nontrivial(:150)・Q3Pi1ComparisonData/q3pcData/q3pcComparison_exists(:169,:208,:225)。

---

## 5. status 決定と根拠

**A4 = 0.55**（0.5 → 0.55）。

- **0.5 を脱する理由**: 前回 0.5 の baseline は「副有限-π₁ 機構は本物だが**非自明な実インスタンスが皆無**（自明塔 lim Gal(ℚ/ℚ)=1・抽象 ẑ surrogate・2-root cover のみ）」。A4a/A4b は初めて **(a) 副有限 π₁ 逆極限オブジェクト ℤ_l が実 Tate 曲線塔へ忠実に自然作用（q3peLimitAct＋q3pe_limit_act_natural＋q3pe_limit_faithful）** ＋ **(b) その普遍性（q3pc_pi1_universal）** ＋ **(c) 裸 ẑ surrogate の実曲線への昇格（q3pcSurrogateAct＋非自明）** を全 axiom clean で landing。A5c が明示 defer した 2 件（逆極限の幾何的実現・忠実性）を正面 discharge＝設計が 0.55 の基準とした「a real limit group faithfully acting on a real cover tower of a real curve, with universal property + surrogate promotion」を満たす。0.5 帯を質的に一歩超える初の非自明実インスタンス。
- **0.6 に遠い理由（0.55 上限）**: (i) pro-l 格子方向スライス ℤ_l のみ（全 π₁^ét ẑ×ẑ(1)・μ 方向 ℤ₃(1)=A7 は二重計上回避で意図的に不構成・一般素数/l 未達）・(ii) 位相/スキーム/エタールサイト皆無（「被覆」は K-点群の全射準同型・Berkovich/rigid でない）・(iii) compact E_q のみ（IUT 本丸 punctured 曲線の非可換 tempered π₁=θ-Heisenberg は範囲外）・(iv) anabelian 逆再構成/Aut(F)/圏登録なし・(v) A4b の一部は再輸出（q3pc_pi1_universal=exact limit_universal・rfl 級橋）で深い新規は A4a に集中・(vi) p=3/q=3^m/単一 l 固定。
- **0.5 据え置きでない理由**: A5c 明示 defer の逆極限オブジェクト層＋忠実性が genuine に新規 landing した前進を過小評価しないため（A5 再消費でなく A4 固有の新規）。
- **0.6 以上でない理由**: 上記 6 限定が残り、位相/スキーム/全 π₁^ét/anabelian 未達＝「実 π₁^ét」の完全形に程遠く、half-notch（0.05）が妥当。

## 6. 集計

- ledger `target_ledger.json` pillars.A A4 status: 0.5 → **0.55**。
- Σ_A = A1 8×0.85 + A2 8×0.65 + A3 12×0.75 + **A4 14×0.55** + A5 10×0.15 + A6 14×0.55 + A7 12×0.4 + A8 12×0.57 + A9 10×0 = 49.54（分母 Σweight=100）→ round(49.54)= **50**。
- `python3 tools/compute_complete_pct.py` → `{"A": 50, "B": 18, "C": 41, "D": 18, "E": 42}`。柱A **49 → 50**。
- `graph-meta.json` pillars.A complete_pct=50 に更新・complete_note に本ラウンド前置。progress_pct=99 据え置き（骨格被覆は飽和域）。`tools/gen_graph.py` 再生成済（modules=615）。`dashboard.md` 二軸表 A 行を 50% に同期・全体平均行を A50 に更新。
