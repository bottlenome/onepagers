# B2・T3-M4（index [U_{L₂}:N(U_M)] ≤ 3 ／ Gal ≅ 余核・相互律本体）詳細化設計 — 2026-07-20

**分類: [設計のみ / design-only]・tier-L 詳細化・complete_pct 0 前進・§4 規約遵守（Lean コードなし・共有ファイル変更なし）**

- 対象: 柱 B・B2（実局所類体論・相互律）T3 の**最終段 T3-M4** — 上界
  index(U_{L₂} : N(U_M)) ≤ 3 と、既存下界（q9rc: [4] 位数 3・q9qc: Gal ↪ 余核）との結合による
  **等式 [U_{L₂} : N(U_M)] = 3・Gal(M/L₂) ≅ U_{L₂}/N(U_M)（B2 の「相互律」本体）**。
- 前提 status（2026-07-20・graph-meta 準拠）: s_B2 = **0.44**（T3-M2 完了 = q9nc・
  `IUT/Q3NormSurjApproxClose.lean`）。T3-M3（完備性・厳密 N(x)=u）は**未着手**
  （`Q3NormSurjComplete.lean` は存在しない。設計は
  `audit/pillar-B2-T3-M2-M3-completeness-detail-2026-07-11.md` §4 M3a–c 済・実装待ち）。
- 本書の成果: (i) M3 が与えるもの／M4 が要るものの正確なギャップ同定（§1・番号系の罠含む）、
  (ii) **disproof-first 有限検査の実行と結果**（18 類 tame 帳簿の完全被覆・障害ゼロ・付録 A）、
  (iii) 主発見 = **M4 は M2/M3 と違いデータ関数を一切要らず（全結論が Prop ∃）、かつ
  前半（tame/torsion 掃き出し）は M3 と独立に今すぐ着手できる**、(iv) マイルストーン梯子
  M4-a／M4-b と正直な予測。
- §4 規約: 既存モジュールの正直な限定を消さない・弱めない。到達可能性を過大主張しない。

---

## 0. TL;DR（verdict）

**T3-M4 は到達可能（research-blocked ではない）。choice 障害ゼロ・新規数学ゼロ・
未知イディオムゼロ。** M3（T3-core: 厳密 N(x)=u on U^{(3)}_λ）が着地すれば、M4 は

1. **M4-a**（`IUT/Q3UnitTameDecomp.lean`・**M3 と独立・今すぐ並列着手可**・opus 1 ラウンド）:
   任意の単数 u を「torsion ノルム（±1 = N(−1)・ζ₃^d = N(ζ₉^d)）× 4^c × U^{(3)}_λ 深部」へ
   掃き出す tame 分解 — ∀u unit, ∃g, ∃w unit_M, u·φ(g)·N(w) ∈ U^{(3)}_λ。
2. **M4-b**（`IUT/Q3ReciprocityIndexReal.lean`・M3 着地後・opus 1 ラウンド）:
   M4-a + T3-core を合成して ∀u, ∃g, q9rcCongMod (q9rgPhi g) u（= index ≤ 3）、
   ⟹ q9qcGalHom **全射** ⟹ 既存単射（q9qc_gal_injective）と合わせ
   **全単射 Hom = codebase の同型標準（QuotientGroup の firstIso イディオムと同格）**・
   余核は {[1],[4],[16]} のちょうど 3 元 — **[U_{L₂}:N(U_M)] = 3・Gal ≅ U_{L₂}/N(U_M)**。

の 2 ラウンドで閉じる。**s_B2 予測（保守・監査次第）: M3 完了時 0.48–0.52 → M4 完了時
0.55–0.60**（B2 headline・大 mover。w20 なので柱 B へ ≈ +1.4〜+2.4pt 相当）。
M4 完了後も cap(b)（分数元 M^×・Artin 正規化・単一拡大）は残る（§4）。

**推奨第一手: M4-a を M3a と並列で今すぐ opus に切り出す**（M3 に依存しない・§5）。

---

## 1. 正確なギャップ: M3 が与えるもの vs M4 が要るもの

### 1.1 番号系の再確認（親設計 §1.1 の規約・混同すると「ギャップ」が幻出する）

λ-level j ⟺ π₉-level 3j（embed(λ^j) = π₉^{3j}·(w⁻¹)^j = `q9nc_embed_lampow`・**実 Lean 済**）。
依頼文の「U^{(9)}」は **π₉-番号**であり λ-番号の U^{(3)} と同一の対象である:

> T3-core（M3c の着地形・M2/M3 設計 §4）:
> ∀ u, q3rqUnitMem u → **q9nfUfilt 9** (q3kEmbed u) → ∃ x, q3kUnitMem x ∧ q3kNormBase x = u

q9nfUfilt 9 = π₉-level 9 = **λ-level 3** = U^{(3)}_λ。つまり **M3 は最初から
U^{(3)}_λ ⊆ N(U_M)（wild 部の全体）を与える**。「U^{(9)}_λ ⊆ N から U^{(3)}_λ ⊆ N への
graded 橋渡し」という追加段は**存在しない**（q9nc_approx も同じ q9nfUfilt 9 で量化済み・
`IUT/Q3NormSurjApproxClose.lean` q9nc-9a）。M4 に解析的残件はゼロ。

### 1.2 M4 に残るもの: U_{L₂}/U^{(3)}_λ の有限帳簿（18 類）

U_{L₂}/U^{(3)}_λ は位数 **18 = 2·3·3**（gr⁰ ≅ 𝔽₃^× ≅ {±1}・gr¹_λ ≅ 𝔽₃・gr²_λ ≅ 𝔽₃）。
**adversarial に明記**: 「U^{(3)}⊆N + [U_{L₂}:U^{(3)}] の位数勘定」だけでは index ≤ 3 は
**出ない**（18 ≠ 3）。18 類のうち 6 類（gr⁰×gr¹ 部分）を**ノルムで打てること**を実 Lean で
示し、残る transversal がちょうど ⟨[4]⟩ = 3 類であることまで下ろす必要がある。担当は:

| 断面 | 位数 | 掃き出し機構 | 既存資産（ファイル実在・確認済） |
|---|---|---|---|
| gr⁰（±1） | 2 | **−1 = N(−1_M)**（3 次拡大・奇数次） | `q9ps_neg_one_normBase`・`q9ps_neg_one_unit`（Q3KummerPiSplit:426/431） |
| gr¹_λ | 3 | **ζ₃^d = N(ζ₉^d)**（torsion ノルム・ζ₃ は λ-level 1 sharp） | `q9nf_zeta_is_norm`（Q3NormFiltrationSpike:475）・`q9tl_normBase_zeta9`（Q3TateCurveL9:62）・`q9nf_zeta_U3`/`q9nf_zeta_not_U4`（:525/533）・`q9nf_zeta_sub_one_split`（:513・**ζ₃−1 = λ·(ζ₃+1) の厳密分解**） |
| gr²_λ（break） | 3 | **ノルムでは打てない**（`q9gn_norm_U2`: N(U^{(2)}_{π₉}) ⊆ U^{(9)}・graded 零）——**4^c で掃く**（余核 transversal） | `q9nf_retarget_witness`/`_sharp`（:565/574・4 の λ-level 2 sharp）・`q3rq_three_eq_neg_lambda_sq`（Q3RamifiedQuadratic:744・**4−1 = 3 = −λ² の厳密等式**） |
| U^{(3)}_λ 以深 | ∞ | **T3-core（M3）** | （M3 着地待ち） |

**主設計判断（親設計 §4-M4 からの改良）**: gr¹ の掃き出しに親設計は解析的 peel
（`q9gn_norm_U1_sharp` の level-1 先頭項分離）を予定していたが、**torsion ノルム
ζ₃ = N(ζ₉) を使う方が大幅に軽い**: ζ₃ は λ-level 1 sharp（q9nf_zeta_U3 + not_U4）なので
ζ₃ の gr¹ 剰余は非零であり、ζ₃^d（d = 0,1,2）が gr¹ ≅ 𝔽₃ を multiplicative に掃く。
補正因子が**具体元の冪**（一般の 1+π₉a でなく）になるため、ノルム展開・E₂ 評価が一切不要。
gr⁰ も同様（±1）。つまり **tame 6 類の掃き出しは全て「根の単数はノルム」という torsion
事実の帳簿**であり、q9gn_norm_U1_sharp は fallback に降格する（資産は実在するので保険は残る）。

### 1.3 下界との結合（既存資産・全て実 Lean 済）

- 下界: `q9rc_order3`（4∉N ∧ 4²∉N ∧ 4³∈N・Q3ReciprocityCokernelReal:152）・
  `q9rc_z3_injects`（[1],[4],[16] pairwise 相異・:193）。
- 商対象: `q9qcCoker : Grp`（literal 商・Q3CokernelObjectReal:81 付近）・
  `q9qcProj`・`quotientProjN_surjective`（QuotientGroup:127・**射影の全射性は既済**）・
  `q9qc_proj_eq_of_cong`/`q9qc_cong_of_proj_eq`（cosetRel ↔ q9rcCongMod 橋・:90/…）。
- Gal 側: `q9rgPhi`（e↦1・s↦4・s2↦16・Q3ReciprocityGalReal:93）・`q9rg_hom`・`q9rg_inj`・
  `q9rg_cong_refl/symm/trans`（:62–74）・`q9qcGalHom`（Hom・:131)・`q9qc_gal_injective`（:141）。

M4-b が足すのは**全射性のみ**: ∀ y : q9qcCoker, ∃ g, q9qcGalHom.map g = y。
これで q9qcGalHom は単射+全射の Hom となり、**codebase の同型標準**
（QuotientGroup の正直な限定 2:「同型は『全単射準同型』まで」= firstIsoHom と同じ格）で
Gal(M/L₂) ≅ U_{L₂}/N(U_M) が主張できる。逆向き Hom の構成は**不要**（§2 A3）。

---

## 2. Disproof-first 攻撃（実行結果）

上界が本当に choice-free で届くのか、障害候補を 8 本立てて各個に攻撃した。

### A1: 番号系の罠（U^{(9)} vs U^{(3)} のギャップ幻出）

**解体済**（§1.1）。T3-core は q9nfUfilt 9 = λ-level 3 で量化されており、M3 と M4 の
継ぎ目に graded 橋は不要。q9gn（N(U²)⊆U⁹）は「gr² が打てない」ことの証明資産であって
M4 の経路上の義務ではない。

### A2: tame 6 類のどれかが実は非ノルムで index > 3 になる可能性（本丸ゲート）

ℤ[ζ₉]（Φ₉ 厳密整数演算・p 進打ち切りなし）で検査（付録 A・本ラウンドで実行）:

- 単数類 mod λ³ は **18 類**（勘定一致）。
- ノルム像類 mod λ³ は **ちょうど 6 類**。
- **{4^c · N-類 : c=0,1,2} は 18 類を完全被覆**（coverage 18/18・complete: True）。
- 下界との整合: 4 も 16 もノルム像 6 類に**入らない**（q9lr/q9rc と無矛盾）。
- 掃き出し部品の実測: N(−1) = −1 ✓・N(ζ₉) = ζ₃ ✓・λ-val(ζ₃−1) = **ちょうど 1** ✓・
  {1,ζ₃,ζ₃²} は mod λ² で pairwise 相異 ✓・λ-val(4−1) = **ちょうど 2** ✓・
  {1,4,16} は mod λ³ で pairwise 相異 ✓。

**ゲート PASS・反証ゼロ**。index = 3 の LCFT 帳簿は数値レベルで完全に閉じている。

### A3: 同型の逆写像構成に choice が要る（Quot からのデータ抽出）？

**発生しない——これが本書の主発見**。理由は 2 つ:

1. **codebase の同型標準は「全単射 Hom」**（QuotientGroup 正直限定 2・firstIsoHom が
   前例: `firstIso_injective` + `firstIso_surjective` の対で「同型」と数える）。
   よって M4-b の義務は全射性 `∀ y, ∃ g, q9qcGalHom.map g = y` という **Prop ∃** のみ。
   逆向き関数 q9qcCoker → q9kdG をデータとして建てる義務はない。
2. **M4 の全結論が Prop ∃ である**ため、M2/M3 で必須だった「塔のデータ関数化」制約
   （M2/M3 設計 §2.3 O2）は M4 に**波及しない**。M3 の T3-core が Prop ∃
   （∃x, N(x)=u）で着地しても M4 はそのまま消費できる——**M4 は M3 の着地形式に
   データ要件を課さない**（M3 実装ラウンドへの制約が 1 つ減る・de-risk）。

残る唯一のデータ的部品は **𝔽₃ の場合分け**（掃き出し指数 d, c の決定）だが、これは
witness を選ぶのではなく「r = 0 ∨ r = 1 ∨ r = −1」の**三分法（Prop・新小補題）**で足りる。
q9rfF3 は Int の Quot mod 3 なので、代表 r ↦ r.emod 3 ∈ {0,1,2}（`q9nsLiftInt` 実在・
Q3NormSurjGraded:111）+ omega で choice-free に証明できる（§3 M4-a1）。

### A4: 単数の gr⁰ 剰余が 0 でないことは言えるか（q3rqUnitMem → res_L ≠ 0）

`q3rqUnitMem u = IsZpUnit 3 (q3rqNorm u)`（Q3RamifiedQuadratic:352）。**新小補題 1 本**:
res_L(u) = 0 ⟹ λ∣u（`q9gn_resL_lambda_dvd` 実在・Q3GradedNormBreak:348）⟹
Norm(u) = Norm(λ)·Norm(f) = 3·Norm(f)（Norm(λ) = −λ̄λ… = 3 は `q3rq_lambda_sq`/
`q3rq_three_eq_neg_lambda_sq` + norm 乗法 `q3rq_norm_mul` 系から機械的）⟹ 3∣Norm(u) ⟹
IsZpUnit と矛盾。既存イディオムの合成のみ・障害なし（§3 M4-a1 に計上）。

### A5: μ_{L₂}-torsion は障害か

**障害どころか機構そのもの**。tame 部 U_{L₂}/U^{(2)}_λ の 6 類の代表は ±ζ₃^d
（μ₆(L₂) の像）であり、全てが**厳密にノルム**: −1 = N(−1)（奇数次）・ζ₃ = N(ζ₉)
（N(ζ₉) = ζ₉^{1+4+16} = ζ₉²¹ = ζ₃・`q9tl_normBase_zeta9` で実 Lean 済）。
torsion で詰まる余地はない（詰まるのは gr² だけで、そこは 4^c の担当＝余核の実体）。

### A6: 完備性・分離性の再発

**なし**。M4 は U^{(3)}_λ より浅い有限帳簿 + M3 の消費のみで、極限・無限積・付値関数・
Markov 断片は一切登場しない（M2/M3 設計 §2.2 の O3 回避形式＝可除性 witness 形を継承）。

### A7: 4^c の gr² 掃き出しは乗法的に閉じるか

(1+λ²s)(1+λ²t) = 1+λ²(s+t)+λ⁴st — **gr² 剰余は加法的**（純可換環恒等式 +
res_L・`q9nc_step_ring` と同型の CRing 恒等式 1 本）。4 = 1+3 = 1−λ²·1
（`q3rq_three_eq_neg_lambda_sq` で**厳密等式**）なので 4 の gr² 剰余は −1 ≠ 0、
4^c の剰余は −c となり c ∈ {0,1,2} が 𝔽₃ を掃く（付録 A で数値確認済）。
u·4^c ∈ U^{(3)}_λ の後 T3-core を適用し、指数の巻き戻しは 4³ = N(embed 4)
（`q9rc_fourcube_is_norm`）+ `q9rc_mul_cube_inv`/`q9rc_four_cancel`（実在・同パターン施工済）で
q9rcCongMod へ正規化する。逆元は全て陽（`q3kInv` は閉じた式・Q3KummerCubic:869・
`q3k_inv_mul`/`q3rq_inv_mul` 実在）——choice 無縁。

### A8: λ-番号 ⟺ π₉-番号の往復が M4 で破れないか

昇り（λ^j∣m ⟹ π₉^{3j}∣embed m）は `q9nc_embed_lampow`（q9nc-3a・厳密等式）から 1 行。
降り（π₉^{3j}∣embed m ⟹ λ^j∣m）は `q9na_lam_descent`（Q3NormSurjSuccApprox:101・
general j・実在）。双方向 wired 済・障害なし。

### 総合判定

**8 攻撃すべて解体・障害ゼロ**。T3-M4 は「研究リスク」ではなく「実装対象」であり、
しかも M2/M3 より軽い（データ関数不要・極限不要・新イディオムは 𝔽₃ 三分法と
tame 掃き出し 3 本のみ＝全て既存パターンの合成）。

---

## 3. マイルストーン梯子（IF reachable → YES・実装計画）

### M4-a: tame/torsion 掃き出し `IUT/Q3UnitTameDecomp.lean`（prefix **q9ut**・衝突なし）

**M3 と独立・今すぐ着手可**。分類ヘッダ: [実／(b) 本物の先行建設]（実 U_{L₂} の単数の
実 torsion ノルムによる分解・T3-M4 への必要部品・toy 主語なし）。

| 段 | 内容 | 消費資産 |
|---|---|---|
| a1 | 𝔽₃ 三分法（r = 0 ∨ 1 ∨ −1・Prop）+ **unit ⟹ res_L ≠ 0** | q9nsLiftInt・q9gn_resL_lambda_dvd・q3rq_norm_mul 系・q3rq_three_eq_neg_lambda_sq |
| a2 | torsion ノルム帳簿: −1 = N(−1)・ζ₃ = N(ζ₉)・積閉（±ζ₃^d = N(±ζ₉^d)） | q9ps_neg_one_normBase・q9nf_zeta_is_norm・q9tl_normBase_zeta9・q3k_normBase_mul |
| a3 | gr⁰ 掃き: ∀u unit, ∃s∈{1,−1}, s = N(·) ∧ u·s ∈ U^{(1)}_λ | a1 + q9gn_resL_lambda_dvd + q9gn_resL_neg |
| a4 | gr¹ 掃き: u ∈ U^{(1)}_λ ⟹ ∃d, u·ζ₃^d ∈ U^{(2)}_λ | q9nf_zeta_sub_one_split（ζ₃−1 = λ(ζ₃+1)・res_L(ζ₃+1) = −1 は具体計算）+ gr¹ 加法性（CRing 恒等式）+ a1 三分法 |
| a5 | gr² 掃き: u ∈ U^{(2)}_λ ⟹ ∃c∈{0,1,2}, u·4^c ∈ U^{(3)}_λ | q3rq_three_eq_neg_lambda_sq + gr² 加法性 + a1 三分法 |
| a6 | **束ね（M4-a 主定理）**: ∀ u, q3rqUnitMem u → ∃ g : q9kdGCar, ∃ w, q3kUnitMem w ∧ q3rqUnitMem の下で u·(q9rgPhi g)·N(w) ∈ U^{(3)}_λ（q9nfUfilt 9 の embed 形で着地・単数性込み） | a3+a4+a5 の合成・q3rq_unit_mul・q9nc_embed_lampow（λ→π₉ 昇り） |

- **新イディオム**: 𝔽₃ 三分法（a1）・gr¹/gr² 加法性の CRing 恒等式（q9nc_step_ring の写経）。
  他は全て実在資産の合成。
- **tier: M（opus）・1 ラウンド**。行数見積 350–450。
- **s_B2 影響: 単体では +0.01 程度（正直申告: T3-core 未着なので index は動かない）**。
  ヘッダに「M4-b（M3 後）の必要部品・単体で index≤3 を主張しない」を明記。

### M4-b: index = 3・Gal ≅ 余核 `IUT/Q3ReciprocityIndexReal.lean`（prefix **q9ix**・衝突なし）

**M3（T3-core）着地後**。分類ヘッダ: [実／(a) 昇格]（q9qc の「単射のみ」を同型へ昇格・
B2 相互律 headline）。

| 段 | 内容 | 消費資産 |
|---|---|---|
| b1 | **分解定理（index ≤ 3 の実体）**: ∀ u, q3rqUnitMem u → ∃ g, q9rcCongMod (q9rgPhi g) u | M4-a6 + **T3-core（M3）** + q9rc_fourcube_is_norm・q9rc_mul_cube_inv・q3kInv/q3k_inv_mul・q9rg_cong_symm/trans・q3k_normBase_mul |
| b2 | **q9qcGalHom 全射**: ∀ y : q9qcCoker.carrier, ∃ g, q9qcGalHom.map g = y | b1 + quotientProjN_surjective + q9qc_proj_eq_of_cong |
| b3 | **余核 = ちょうど 3 元**: ∀ a : q3rqU, proj a ∈ {[1],[4],[16]}・pairwise 相異 | b1 + q9qc_cong_of_proj_eq + q9rc_z3_injects |
| b4 | capstone `Q3ReciprocityIndexRealData`: 全単射 Hom（= codebase 同型標準）+ index=3 + 下界束ね——**[U_{L₂}:N(U_M)] = 3・Gal(M/L₂) ≅ U_{L₂}/N(U_M)** | b2 + q9qc_gal_injective + q9qc_gal_embeds |

- **新イディオム: ゼロ**（全て合成）。逆向き Hom は建てない（§2 A3・QuotientGroup の
  同型標準に整合）。建てたくなった場合の追加余地: c-index の total 関数化 +
  Quot.lift（可能だが義務ではない・スコープ外と明記）。
- **tier: M（opus）・1 ラウンド**（b4 のみなら S でも可だが同一ファイルなので M 一括）。
- **M3 へのインターフェース要件（M3 実装ラウンドに伝達・軽い）**: T3-core は
  `∀ u, (q3rqUnitMem u) → q9nfUfilt 9 (q3kEmbed u) → ∃ x, q3kUnitMem x ∧ q3kNormBase x = u`
  の**Prop ∃ で十分**（データ関数不要）。仮に unit 仮定なし版で着地しても M4-a1
  （Ufilt 9 ⟹ res_L = 1 ⟹ unit）で補える——どちらの形でも消費可能。

### 依存グラフと並列性

```
M3a ──┐
M2d ──┼→ M3b → M3c(T3-core) ─┐
      │                       ├→ M4-b（index=3・Gal≅余核）
M4-a（独立・今すぐ可）────────┘
```

M4-a は M3a と**同一ラウンドで並列起動できる**（依存ゼロ・別ファイル）。
T3 全体の残りは M3a/M3b/M3c/M4-b の 4 実装ラウンド（M4-a を並列に差し込めば
カレンダー上は実質 4 ラウンドのまま M4 前半が先行消化される）。

---

## 4. 保守的な正直予測と M4 後に残る cap

| 段 | 内容 | tier | s_B2 予測（監査次第） |
|---|---|---|---|
| （現在） | T3-M2 まで | — | **0.44** |
| M3a–c | 完備性・厳密 N(x)=u（別設計書） | opus ×3 | → 0.48–0.52 |
| M4-a | tame/torsion 掃き出し（M3 と並列可） | opus ×1 | +0.01（単体） |
| M4-b | index = 3・Gal ≅ 余核（**B2 headline**） | opus ×1 | → **0.55–0.60** |

親設計の 0.55–0.62 に対し上限を 0.60 に絞る（下記 cap の残存質量を重く見るため）。
w_B2 = 20 なので M3+M4 完走は柱 B へ ≈ +2.2〜3.2pt 相当の大 mover。

**M4 完了後も残る正直な限定（§4 規約・消さない・弱めない）**:

1. **cap(b) 分数元**: 対象は整単数余核 U_{L₂}/N(U_M) であり、分数元込みの
   **L₂^×/N(M^×) の完全配線は未達**（q9qc 限定 1 の継承）。値群側は
   N(π₉) = ζ₃−1（q9wr_normBase_pi9）で全射だが、M^× ≅ π₉^ℤ × U_M の直積分解を通した
   full reciprocity の束ねは別モジュール（q9fc の q9fcUnif 表現が足場になる・要別途詳細化）。
2. **Artin 正規化**: q9rgPhi（s ↦ 4）は「単射になる生成元対応」であって、
   **Frobenius 正規化から導出された Artin 写像ではない**（σ ↦ [4] か [4²] かの正規化は
   未決定のまま）。totally ramified 拡大単独では Frobenius アンカーが無いため、
   これは不分岐データを足す将来仕事（B2 残 cap の主要質量）。
3. **単一拡大 M/L₂/ℚ₃ のみ**・一般局所体ゼロ・体化なし・σ を超える Galois ゼロ。
4. M4 の全定理は q9nc/q9qc/q9rc/q9rg/q9gn/q9nf/q9ps/q9rf/q3k/q3rq の正直限定を全継承。

これらが s_B2 の残り ≈ 0.40 の実体である（T3 完走 = B2 の「相互律の単数部」完成であって
B2 全体の完成ではない、と報告時に明記すること）。

---

## 5. 推奨する次の一手（M3 後…ではなく**今**）

1. **第一 opus スライス = M4-a（`IUT/Q3UnitTameDecomp.lean`）を M3a と同一ラウンドで
   並列起動する**。依存ゼロ・消費資産は全て実在確認済（§3 表）・設計は本書 §1.2/§3 で
   閉形式まで済。実装順は a1 → a2 →（a3/a4/a5 並行可）→ a6。
2. **de-risk 項目（a1 を最初に置く理由）**: 𝔽₃ 三分法と unit⟹res≠0 は a3–a6 の全段が
   消費する唯一の新部品であり、ここが軽く閉じれば M4-a の残りは写経になる。
   万一 q9rfF3 の Quot 簿記が重い場合の fallback: 三分法を「res_L u の q9nsLiftInt 値 ∈
   {0,1,2}」の Int 側 omega に退避（q9nsCorr/q9np_resM_corr と同じ迂回・等価）。
3. **教訓の転記（q9naSeq 符号破れの再発防止）**: q9nc の正直限定 0 が示した通り、
   剰余の符号は「設計上こうなるはず」でなく**厳密等式資産から Lean 内で導出**すること。
   M4-a4 の ζ₃ の gr¹ 剰余は必ず `q9nf_zeta_sub_one_split`（ζ₃−1 = λ·(ζ₃+1)）から
   res_L(ζ₃+1) = 1+1 = −1 を**計算で**取ること（付録 A の数値と照合済・
   仮に符号が逆でも三分法での場合分けが吸収するため設計は壊れない）。
4. M4-b は M3c 着地の同ラウンド末尾または直後ラウンドに opus 1 本で。b4 の報告では
   §4 の cap 1–3 を必ず併記し「B2 完成」とは書かない。

---

## 付録 A: disproof-first 有限検査スクリプト（本ラウンド実行・再現用・依存なし・厳密整数演算）

```python
# Z[zeta9] mod Phi9 = x^6+x^3+1 (exact), sigma: x->x^4, N(z)=z*sz*s2z
def pmul(a,b):
    c=[0]*11
    for i in range(6):
        if a[i]:
            for j in range(6): c[i+j]+=a[i]*b[j]
    for k in range(10,5,-1):
        v=c[k]
        if v: c[k]=0; c[k-6]-=v; c[k-3]-=v
    return tuple(c[:6])
padd=lambda a,b: tuple(x+y for x,y in zip(a,b))
ONE=(1,0,0,0,0,0); PI=(-1,1,0,0,0,0)
SIG=[(1,0,0,0,0,0),(0,0,0,0,1,0),(0,0,-1,0,0,-1),(0,0,0,1,0,0),(0,-1,0,0,-1,0),(0,0,1,0,0,0)]
def sigma(a):
    r=(0,)*6
    for k in range(6):
        if a[k]: r=padd(r,tuple(a[k]*t for t in SIG[k]))
    return r
def N(z):
    n=pmul(pmul(z,sigma(z)),sigma(sigma(z)))
    assert n[1]==n[2]==n[4]==n[5]==0
    return (n[0],n[3])                       # in Z[zeta3]
lmul=lambda u,v:(u[0]*v[0]-u[1]*v[1], u[0]*v[1]+u[1]*v[0]-u[1]*v[1])
lsub=lambda u,v:(u[0]-v[0],u[1]-v[1])
def lam_val(t,cap=40):                       # lambda=1+2*zeta3, lambda^2=-3
    a,b=t
    if a==0 and b==0: return 999
    v=0
    while v<cap:
        if (a+b)%3!=0: return v
        m0=a-2*b; m1=2*a+b-2*b
        a,b=-m0//3,-m1//3
        v+=1
    return v
same3=lambda u,v: lam_val(lsub(u,v))>=3
# (1) unit classes mod lambda^3 == 18; (2) norm-image classes == 6;
# (3) {4^c * N-class} covers all 18; (4) sweep parts: N(-1)=-1, N(zeta9)=zeta3,
#     lam_val(zeta3-1)=1, lam_val(4-1)=2, zeta3-powers distinct mod lambda^2,
#     4-powers distinct mod lambda^3; (5) 4,16 not in N mod lambda^3.
#  (enumeration bodies omitted here; full script: scratchpad m4check.py)
```

実行結果（2026-07-20・本ラウンド）:
unit classes mod λ³ = **18** ✓・norm image classes = **6** ✓・
**4^c·N coverage = 18/18 complete: True** ✓・N(−1) = −1 ✓・N(ζ₉) = ζ₃ ✓・
λ-val(ζ₃−1) = 1（sharp）✓・ζ₃ 冪 mod λ² pairwise 相異 ✓・λ-val(4−1) = 2（sharp）✓・
4 冪 mod λ³ pairwise 相異 ✓・4 ∉ N・16 ∉ N（mod λ³・下界整合）✓。
**障害ゼロ・ゲート PASS。**
