# 柱B 完成ファースト・ピボット詳細化: 実 Kummer 双対（B6）× 実野性分岐フィルトレーション（B1） — 2026-07-11

**種別**: 設計文書のみ（Lean 実装なし）。**対象**: 柱A level-9 ℤ₃^× kill キャンペーンが建てた実基盤（q3rq / q3k / q9ci / q9ps / q9tl / q9c / q9yp）を、柱B（complete_pct=18・Σweight=100）の表示を動かす消費へ転用する最高レバレッジ 1–2 モジュールの選定。**判定は def/theorem 本体の読解による・敵対的既定＝「既存 B モジュールが既に覆っている／表示は動かない」**。この既定を覆せた項目だけを提案する。

---

## 0. 結論先出し（TL;DR）

1. **動かすのは B6（Kummer 理論・weight 10・status 0）を主、B1（実付値・実分岐フィルトレーション・weight 20・status 0.5）を従**。理由: 独立監査（graph-meta.json 柱B complete_note）が B2–B6=0 の根拠を「**コード全体を通じて実 Galois 群（実体拡大 L/K の Aut または逆極限）が一つも存在しない**」と明記しているが、この根拠は **level-9 キャンペーンで既に消滅した**——`q3kSigma`（Y↦ζ₃Y・`q3k_sigma_mul`・`q3k_sigma3_id`・位数 3）は実環 O_M=L₂[Y]/(Y³−ζ₃) の**実環自己同型**であり、Gal(M/L₂)≅ℤ/3 の実生成元である。しかも M/L₂ は**文字通り実巡回 3 次 Kummer 拡大**（Y³=ζ₃）。B6 の題目「Kummer 理論（実 Galois コホモロジー上）」の主対象が、柱A の副産物としてすでに建っている。
2. **提案 2 モジュール**（どちらも新規ファイル・独立・並列可・tier M=opus）:
   - **`IUT/Q3KummerDualityReal.lean`（q9kd・B6 向け・~500 行）**: 実巡回 3 次 Kummer 双対。実 Kummer 指標 χ(σᵏ)=ζ₃ᵏ（σᵏ(ζ₉)=ζ₃ᵏ·ζ₉）の準同型性・忠実性、**Kummer 類 [ζ₃]∈L₂^×/(L₂^×)³ の非自明性**（群提示 q3rqLx=ℤ×U₂ 上・`q9ci_no_cbrt_zeta` 消費）、完全対 Gal(M/L₂)×⟨[ζ₃]⟩→μ₃ の両側非退化、Hom(Gal(M/L₂),μ₃) の完全枚挙（`q9c_m_mu3_complete` 消費）＝**この拡大での Kummer 同型の完全証明**。
   - **`IUT/Q3WildRamFiltrationReal.lean`（q9wr・B1 向け・~450 行）**: 実野性分岐フィルトレーション。**σ(π₉)−π₉ = π₉³·u\***（u\* 閉形式実単数・`q9ps_pi9_cube`＋`q9ps_coord0` 消費）、下付き番号付け G₀=G₁=G₂=⟨σ⟩・G₃∩{σ,σ²}=∅（break t=2）、**実 different 指数 (σπ₉−π₉)(σ²π₉−π₉)=π₉⁶·(単数)＝d(M/L₂)=6**、および Nat 階段模型 `wcdRamGroups 3 2`（M441F）との genuine cross-check——**模型チェーン wcd/mjw/ajw/hau に初の実インスタンスを与える**。
3. **表示算術（正直）**: Σ_B=17.5→表示 18。`compute_complete_pct.py` は Python `round`（**銀行家丸め**）。B6 が 0→0.15 で表示 19、0→0.25 で表示 20。B1 が 0.5→0.6 で表示 20。両方なら最大 22。**罠**: B6 0→0.10 ちょうどは Σ=18.5→丸め 18 で**表示不動**。ゆえに B6 は「1 実例の cocycle 供給」止まりでなく**双対の完全証明（両側非退化＋Hom 枚挙）**まで積み、監査評定 ≥0.15 を狙う設計にした（§1）。
4. **二重計上チェックは通った**が 2 つの実リスクを名指しする（§4）: (i) 「ζ₃ は O_{L₂} 内に 3 乗根なし」は **`q9ci_no_cbrt_zeta`（柱A・既存）**——q9kd はこれを**消費**し、新規主張は「群提示 L₂^×=ℤ×U₂ 上の Kummer 類の非自明性」＋「双対」のみとする（再ラベル禁止）。(ii) 「3=π₉⁶·u₆」は **`q9ps_three_split`（柱A・既存）**——q9wr の新規主張は **Galois 側データ σπ−π**（q9ps には Galois 作用が一切ない）に限る。
5. **A 続行・D 転進より B が優位**（§6）: 柱A の次の表示 +1 は s_A7≥0.574（dashboard 明記）で新スライス kill フルキャンペーン級。柱D の本丸 D-1 は CLAUDE.md 規約により fable 詳細化ラウンドが先行必須。柱B は opus 2 本・1 ラウンドで表示 +1〜+4 の期待値。**完成ファースト規則との整合**: 両モジュールとも主語は実対象（実 ℤ₃ 逆極限の上の実 O_{L₂}・実 O_M・実環自己同型 σ）であり、(a) 昇格（B 台帳の抽象/Nat 模型限定を実対象で置換）に該当する。

---

## 1. どの B 項目をいくら動かすか（表示算術・敵対的）

### 1.1 現状（target_ledger.json 柱B・実測）

| id | title | weight | status | 寄与 |
|---|---|---|---|---|
| B1 | 実局所体の実付値・実分岐フィルトレーション（実 Galois 群上） | 20 | 0.5 | 10.0 |
| B2 | 実局所類体論（相互写像・実） | 20 | 0 | 0 |
| B3 | 実 Artin 導手/different（実表現・実分岐群上） | 20 | 0 | 0 |
| B4 | 実 Hasse–Arf（実 Galois 群上） | 15 | 0 | 0 |
| B5 | 大域類体論/積公式（実） | 15 | 0.5 | 7.5 |
| B6 | Kummer 理論（実 Galois コホモロジー上） | 10 | 0 | 0 |
| **Σ** | | **100** | | **17.5 → 表示 18** |

`compute_complete_pct.py` は `round(num/den*100)`＝Python 3 の **round-half-to-even（銀行家丸め）**。17.5→18（18 は偶数）。この丸め規則が閾値計算に効く:

| シナリオ | ΔΣ | Σ_B | round | 表示 |
|---|---|---|---|---|
| B6 0→**0.10** | +1.0 | 18.5 | **18**（half-to-even の罠） | **不動** |
| B6 0→**0.15** | +1.5 | 19.0 | 19 | **+1** |
| B6 0→**0.25** | +2.5 | 20.0 | 20 | **+2** |
| B1 0.5→**0.55** | +1.0 | 18.5 | **18** | **不動** |
| B1 0.5→**0.60** | +2.0 | 19.5 | 20（half-to-even が今度は上へ） | **+2** |
| B6 0→0.25 ∧ B1 0.5→0.6 | +4.5 | 22.0 | 22 | **+4** |
| 敵対的フロア: B6 0→0.10 ∧ B1 据え置き | +1.0 | 18.5 | 18 | **不動（正直に想定する）** |

### 1.2 監査評定の予測（AUDIT_RUBRIC.md 準拠・自己申告でないことを明記）

status は独立敵対監査のみが動かす（実装者の自己申告は禁止・`.complete_pct_baseline.json` 更新はユーザー人手署名）。以下は**設計側の期待値**にすぎない:

- **B6: 期待 0.15–0.25**。上げ材料: 主対象が rubric の「Galois 群＝実際の環自己同型の群」を初めて満たす（σ は実 O_M の実自己同型・O_M は実 ℤ₃=zpRing 3 から 2 段の実商環構成）／cocycle 供給だけでなく**非自明 Kummer 類＋両側非退化＋Hom 完全枚挙＝この拡大での Kummer 同型の完全証明**まで閉じる。下げ材料: 拡大 1 個（M/L₂）・n=3 のみ・Galois は有限商 ⟨σ⟩ のみ（副有限 G_{L₂} なし）・L₂^×/(L₂^×)³ の全体構造は未計算（⟨[ζ₃]⟩ 部分のみ）・抽象 H¹ 形式論（galH1Module）への接続なし。weight 10 の題目に対し「本物の忠実部分ケース 1 個の完全双対」は 0.25 妥当・0.15 が敵対的中心。**0.10 で止まるリスク**（=表示不動）は「実例 1 個の cocycle にすぎない」と読まれた場合——これを防ぐために双対完全証明（§2 の T6–T8）を必須要件とする。
- **B1: 期待 0.5→0.55–0.65（中心 0.6）**。上げ材料: B1 題目の後半「実分岐フィルトレーション（**実 Galois 群上**）」が現状 **0 のまま 0.5 が付いている**（0.5 の根拠は実 ℤ₃ 上の 1+3ℤ₃・U^(d) のみ＝Galois なし）。q9wr は実 Galois 群の実分岐フィルトレーション（下付き・break・different 指数）の**初の実現**。下げ材料: 付値**関数** v_M は建てない（可除性形式のみ）・完備化/位相なし・拡大 1 個・上付き番号/Herbrand は Nat 模型（rnf）のまま。0.55 止まり（単独では表示不動）を正直に想定に入れる。
- **1 ラウンド到達性**: 両モジュールとも消費部品が全て実在の named 補題に帰着する（§2–§3 で名指し）。opus 2 本並列・1 ラウンドで実装可能と判定。**表示の中心予測: 18→19–20**（B6 0.15–0.25 が主駆動・B1 は上振れ要員）。フロア: 18 不動（B6 が 0.10 評定の場合）——この場合も B6 0→0.10・B1 +0.05 は次ラウンドの閾値貯金であり無駄にはならないが、**「表示が動かない可能性」は着手前にユーザーへ提示する**。

---

## 2. モジュール設計 1: `IUT/Q3KummerDualityReal.lean`（prefix `q9kd`・B6）

**分類（ヘッダ必須記載）**: [実／(a) 昇格]——既存 Kummer 理論の「抽象体 K・witness 根・仮説形」（M320F/M345F/M349F の正直限定）を、実巡回 3 次 Kummer 拡大 M=ℚ₃(ζ₉)=L₂[Y]/(Y³−ζ₃)・実 Gal(M/L₂)=⟨q3kSigma⟩ 上の**完全双対**で置換する。complete_pct 影響: B6 0→（監査次第・期待 0.15–0.25）。

**数学的内容**: L₂⊃μ₃（`q3rqZeta`）・M=L₂(ζ₉)・Y³=ζ₃。Kummer 理論の主張は (i) 指標 χ_{ζ₃}: Gal(M/L₂)→μ₃, σ↦σ(ζ₉)/ζ₉=ζ₃ が忠実、(ii) [ζ₃]∈L₂^×/(L₂^×)³ が非自明、(iii) 対 Gal×⟨[ζ₃]⟩→μ₃, (σʲ,[ζ₃]ᵏ)↦ζ₃^{jk} が完全対＝⟨[ζ₃]⟩≅Hom(Gal(M/L₂),μ₃)。全てこの具体拡大で無仮説・完全証明できる。

**定理列**（消費部品を named で示す。逆元回避のため乗法形で定式化）:

| # | 定理 | 内容 | 消費する実在部品 |
|---|---|---|---|
| T1 | `q9kd_sigma_fixes_base` | σ(embed n)=embed n（σ は L₂ を固定＝実**相対** Galois） | `q3kSigma` の成分定義（第 0 成分不動）・ほぼ rfl |
| T2 | `q9kd_sigma_ring_hom` | σ の加法性（乗法性は `q3k_sigma_mul` 既存・加法は成分ごと）＋σ≠id・σ²≠id・σ³=id | `q3k_sigma3_id`・`q3rq_zeta_ne_one` |
| T3 | `q9kd_cocycle` | **σ(ζ₉)=embed(ζ₃)·ζ₉・σ²(ζ₉)=embed(ζ₃²)·ζ₉**（Kummer コサイクルの実体・座標計算） | `q3kSigma`/`q3kZeta9` 定義・`q3k_z_zR` |
| T4 | `q9kd_chi_hom` | χ(σʲ⁺ᵏ)=χ(σʲ)·χ(σᵏ)（mod σ³=id・ζ₃³=1）＝指標の準同型性 | `q3k_z3R`・`q3k_zsq_zR1` 系 |
| T5 | `q9kd_chi_faithful` | χ(σ)≠1 ∧ χ(σ²)≠1 ⟹ ker χ={id}（**実 Kummer 指標の忠実性**） | `q3rq_zeta_ne_one`・`q3k_embed_inj` |
| T6 | `q9kd_class_nontrivial` | **¬∃ g∈q3rqLx, g³=(0,ζ₃U)**——Kummer 類 [ζ₃] は L₂^×=ℤ(v_λ)×U₂ の群提示上で非 3 乗（(n,u)³=(3n,u³)・3n=0⟹n=0・単数 3 乗根は O_{L₂} 元） | `q3rqLx`（prodGrp intGrp q3rqU）・**`q9ci_no_cbrt_zeta`（消費・再証明しない）** |
| T7 | `q9kd_pairing_bilinear` / `q9kd_pairing_eq` | σʲ(ζ₉ᵏ)=embed(ζ₃^{jk})·ζ₉ᵏ（対の値の閉形式・j,k 双線形） | T3・`q9yp` の Yᵏ 正規形（`q9ypY2`…`q9ypY8`） |
| T8 | `q9kd_pairing_nondeg_left` / `_right` | 左: σʲ(ζ₉)=ζ₉ ⟹ 3∣j。右: (∀j) σʲ(ζ₉ᵏ)=ζ₉ᵏ ⟹ 3∣k（3×3 の有限検査・ζ₃ᵏ≠1） | T7・`q3rq_zeta_ne_one`・`q3k_zeta9_cube_ne_one` |
| T9 | `q9kd_hom_exhaust` | **Hom(⟨σ⟩,μ₃(O_M))={χ⁰,χ¹,χ²}**——値 m³=1 の完全枚挙で hom は σ の像で決まる | **`q9c_m_mu3_complete`（消費）**＝O_M 内 μ₃ 完全性 |
| T10 | `q9kd_kummer_iso` | T5+T6+T8+T9 の束ね: k↦χᵏ が ⟨[ζ₃]⟩→Hom(Gal(M/L₂),μ₃) の**全単射**＝実巡回 3 次 Kummer 双対の完全証明 | T5–T9 |
| T11 | `Q3KummerDualityRealData` / `q9kd_data` / `q9kd_exists` | capstone（新規証明ゼロ・束ねのみと明記） | T1–T10 |

**deps**: `Q3KummerCubic`（q3k 本体）・`Q3RamifiedQuadratic`（q3rqLx・q3rqU）・`Q3KummerCubeIdent`（q9ci_no_cbrt_zeta）・`Q3Mu9Completeness`（q9c_m_mu3_complete）・`Q3KummerYPow`（Yᵏ 正規形）・（ζ₉ 単数性は `Q3TateCurveL9` の `q9tl_normBase_zeta9`/`q9tl_zeta9_unit` を import するか 3 行で再計算——import 軽量化なら後者）。

**tier**: **M（opus）**。全ステップが確立イディオム（座標計算・埋め込み・有限検査・named 消費）。新イディオム発明なし。**行数見積: 450–550**。最重量は T6 の群提示計算と T9 の枚挙 glue（いずれも q9c/q3mc の前例パターンあり）。

---

## 3. モジュール設計 2: `IUT/Q3WildRamFiltrationReal.lean`（prefix `q9wr`・B1）

**分類**: [実／(a) 昇格]——既存 B の分岐フィルトレーション（wcd/mjw/ajw/hau＝**Nat 階段データ上**・監査が「Hasse–Arf 群は List Nat」と模型判定済み）と Eisenstein 塔（eisRing **模型環**上）を、実 Gal(M/L₂) が実 O_M に作用する**初の実分岐フィルトレーション**で置換する。complete_pct 影響: B1 0.5→（監査次第・期待 0.55–0.65）。

**数学的内容（手計算検算済み）**: π₉=Y−1（e(M/ℚ₃)=6・q9ps）。σ(π₉)−π₉=(ζ₃−1)Y。ζ₃−1=λ(ζ₃+1)（`q9ps_coord0` そのもの）・λ=π₉³·w⁻¹（`q9ps_pi9_cube` の並べ替え）ゆえ **σ(π₉)−π₉=π₉³·u\***、u\*=w⁻¹·embed(ζ₃+1)·Y は単数（N(w⁻¹) 単数・(ζ₃+1)³=(−ζ₃²)³=−1・N(Y)=ζ₃）。同様に σ²(π₉)−π₉=(ζ₃²−1)Y=π₉³·u\*\)（ζ₃²−1=λ(ζ₃+1)²）。ゆえに i_G(σ)=i_G(σ²)=3＝下付き break t=2: **G₀=G₁=G₂=⟨σ⟩・G₃=1**。different 指数 d(M/L₂)=Σ_{σ≠1}i(σ)=6（大域検算: d(M/ℚ₃)=9=d(M/L₂)+3·d(L₂/ℚ₃)=6+3 ✓）。これは `wcdRamGroups p m` の p=3, m=2 インスタンス（d=(m+1)(p−1)=6）の**初の実実現**。

**定理列**:

| # | 定理 | 内容 | 消費する実在部品 |
|---|---|---|---|
| U1 | `q9wr_sigma_pi_sub` | σ(π₉)−π₉ = embed(ζ₃−1)·Y（座標計算・ほぼ rfl 級） | `q3kSigma`・`q9psPi9` |
| U2 | `q9wr_ustar` / `q9wr_ustar_unit` | u\*:=w⁻¹·embed(ζ₃+1)·Y の定義と単数性 | `q9psWinv`・`q3k_normBase_mul`・`q3k_normBase_inv`・`q9ps_normBase_embed`・`q9tl_normBase_zeta9`・`q9ps_zeta_add_one` |
| U3 | `q9wr_sigma_pi_eq` | **σ(π₉)−π₉ = π₉³·u\***（★ 実野性分岐の核） | U1・**`q9ps_pi9_cube`**・**`q9ps_coord0`**・`q9ps_w_inv_mul`・`q3k_embed_mul` |
| U4 | `q9wr_sigma2_pi_eq` | σ²(π₉)−π₉ = π₉³·u\*\*（u\*\*=w⁻¹·embed((ζ₃+1)²)·Y。新恒等式 ζ₃²−1=λ(ζ₃+1)² は q9ps_coord0×(ζ₃+1) の 1 行） | U3 と同型 |
| U5 | `q9wr_G2_mem` | π₉³ ∣ (σᵏπ₉−π₉)（k=1,2）＝σ,σ²∈G₂（可除性形式の下付きフィルトレーション） | U3・U4 |
| U6 | `q9wr_G3_trivial` | **¬ π₉⁴ ∣ (σπ₉−π₉)**（break の上界・最重量）: π₉³u\*=π₉⁴x なら λ 正則消去→N 適用→q3rqNorm 適用で 1=3t in ℤ₃→`q3f_uniformizer` の ¬IsZpUnit 3 に矛盾 | **`q9ci_pi9_reg`**（π₉ 正則）・`q9ci_lambda_reg`・`q3k_normBase_mul`・**`q9ci_zeta_norm3`**（q3rqNorm(ζ₃−1)=3）・`q3f_uniformizer` |
| U7 | `q9wr_break` | 束ね: 下付き分岐フィルトレーション G₀=G₁=G₂={1,σ,σ²}・G₃∩{σ,σ²}=∅＝**break t=2 の実分岐フィルトレーション** | U5・U6 |
| U8 | `q9wr_different` | **(σπ₉−π₉)·(σ²π₉−π₉) = π₉⁶·(u\*u\*\*)**＝実 different 生成元・d(M/L₂)=6 | U3・U4 |
| U9 | `q9wr_matches_wcd` | genuine cross-check: `wcdDiffSum (wcdRamGroups 3 2) 2 = 6`（Nat 計算）＋実側 U7/U8 が同じ階段 \|G₀\|=\|G₁\|=\|G₂\|=3, \|G₃\|=1 を実現——**Nat 模型チェーン（M441F wcd）への初の実インスタンス接続** | `wcdRamGroups`/`wcdDiffSum`（M441F・既存） |
| U10 | `Q3WildRamFiltrationRealData` / `q9wr_data` / `q9wr_exists` | capstone（束ねのみ） | U1–U9 |

**deps**: `Q3KummerPiSplit`（π₉・w・coord0・pi9_cube）・`Q3KummerCubeIdent`（正則性パック・zeta_norm3）・`Q3TateCurveL9`（N(Y)=ζ₃）・`Q3LocalField`（q3f_uniformizer）・`WildConductorDiscriminant`（U9 のみ）。

**tier**: **M（opus）**。U6 が最も繊細（正則消去→ノルム 2 段の連鎖）だが全部品が named 実在補題。詰まったら U6 のみ親/fable が HELP スポットとして引き取る（それ以外は独立に閉じる）。**行数見積: 400–500**。

---

## 4. 二重計上チェック（敵対的・定理単位の評決）

既定＝「既存 B が覆っている」。定理ごとに最近傍の既存モジュールを名指しして判定する。

### 4.1 q9kd（B6）

| 新定理 | 最近傍の既存 | 評決 |
|---|---|---|
| T3–T5（実指標） | `KummerTheory.lean`（M320F）: kummerCocycle・1-コサイクル則。`KummerCharReal.lean`（M349F・**柱A**）: κ_α(σ)=σ(α)/α | **新**。両者は抽象 `IUTField K`＋`FieldAut K`＋witness n 乗根の上。q3k は**体でない**（total inverse なし・A2 恒久限定）ため既存機構は M/L₂ を**型として受け取れない**。実 Galois 群の実指標のインスタンスはコードベースに存在しない（柱B 監査の complete_note が明記）。なお M349F の正直限定が「**完全 Kummer 双対は外部仮説等**」と自認——T10 はまさにこの named 欠落の昇格 |
| T6（類の非自明性） | **`Q3KummerCubeIdent.lean` の `q9ci_no_cbrt_zeta`（柱A・既存！）** | **要注意→クリア**。O_{L₂} 内の 3 乗根非存在そのものは既存（本体確認済み: `∀ v, v³ ≠ q3rqZeta`）。q9kd の新規部分は **L₂^× の群提示 ℤ×U₂ 上への持ち上げ**（付値成分 3n=0 の処理＋単数成分の O 帰着）と Kummer 類としての定式化のみ。**ヘッダに「3 乗根非存在は q9ci 消費・本モジュールの新規主張ではない」と明記する**ことを実装条件とする |
| T8–T10（完全対・同型） | `KummerExact.lean`（M345F）: K^×/ker(δ)≅H¹ だが**全射性は明示仮説 hsurj**・単射性のみ無条件。`KummerNontrivialChar.lean`（M453F・柱E×A）: 非自明円分指標だが**位数 2 の複素共役型**・対象は CycGKAction の外側同変性 | **新**。M345F が仮説形で残した全射側を、有限具体ケースで**無仮説に**閉じる（Hom 枚挙は `q9c_m_mu3_complete` 消費）。M453F は別の主張（θ–μ 同定の Galois 同変性）・別の群（位数 2）・模型側 CycGKAction——位数 3 の実相対 Galois の Kummer 双対とは重ならない |
| T9 | `Q3Mu9Completeness.lean`（q9c・柱A） | **消費であり再証明でない**。μ₃/μ₉ 完全性は一切再主張しない |
| T3 と `Q3Mu9Rigidity.lean` の `q9mr_aut_mu9_new_layer` | σ(ζ₉)=ζ₉⁴≠ζ₉ を既に使用 | **クリア**。q9mr の主張は「σ は Aut(μ₃) 上恒等・Aut(μ₉) 上非恒等＝新層 witness」（剛性 kill 機構）。q9kd の主張は「σ↦σ(ζ₉)/ζ₉ が Gal(M/L₂) の忠実指標で Kummer 双対を成す」。素材（σ(Y)=ζ₃Y）は同じでも定理は別物。ただし **σ(ζ₉) の値の計算補題自体は q9mr/q9yp のものを import して使い、重複補題を作らない**ことを実装条件とする |

### 4.2 q9wr（B1）

| 新定理 | 最近傍の既存 | 評決 |
|---|---|---|
| U3–U8（σπ−π・break・different） | `Q3KummerPiSplit.lean`（q9ps・柱A） | **クリア**。q9ps は分割恒等式 3=π₉⁶u₆ のみで **Galois 作用が一切登場しない**（本体確認済み）。q9wr の主語は σ の作用データ σπ₉−π₉——q9ps が持たない新次元。**逆に 3=π₉⁶u₆・v_π(3)=6・e=6 は q9ps の成果であり q9wr の新規主張として数えない**（ヘッダ明記・実装条件） |
| U7/U9（フィルトレーション・different 公式） | `WildConductorDiscriminant.lean`（M441F）・`MultiJumpWildDiscriminant`・`ArbitraryJumpWild`・`HasseArfUnconditional`・`DifferentFromFiltration` | **クリア（これが本丸）**。本体確認: これら全チェーンの主対象は **Nat の階段データ**（\|G_i\| の数列・wcdRamGroups は Nat 関数）であり、AUDIT_RUBRIC が模型例として**名指し**する形（「実局所体でなく Nat 分岐群データ上の Hasse–Arf」）。実際の群が実際の環に作用して σπ−π から break が**出てくる**モジュールは存在しない。q9wr は wcd の p=3,m=2 階段の初の実実現＋cross-check（U9）で、模型→実の (a) 昇格の教科書形 |
| U5–U6 | `LambdaTower*`/`Eisenstein*` 系（柱B・eisRing 上の λ 塔・v(π_{n+1})=p·v(π_n) 等） | **クリア**。eisRing は CLAUDE.md §2(a) が昇格対象として名指しする**模型環**。q9wr の台は実 ℤ₃（zpRing 3 逆極限）→実 O_{L₂}→実 O_M。かつ λ 塔には Galois 作用がない |
| U2/U6 の単数・正則部品 | `Q3KummerCubeIdent`（q9ci 正則性パック）・`Q3RamifiedQuadratic` | **消費であり再証明でない** |
| B1 既存 0.5 分（1+3ℤ₃・U^(d)） | `PrincipalUnits`/`UnitFiltration`/`HigherUnitFiltration` | **クリア**。単数フィルトレーションは ℤ₃ 単体上・Galois なし。q9wr は単数フィルトレーションを再主張しない（分岐群フィルトレーションのみ） |

**総合評決**: 二重計上なしで設計可能。ただし実装条件 3 点を課す——(1) q9kd ヘッダで `q9ci_no_cbrt_zeta` 消費を明記し 3 乗根非存在を新規主張に数えない、(2) q9wr ヘッダで 3=π₉⁶u₆／e=6 を q9ps の成果と明記、(3) 両モジュールとも tmzLimit 比較橋を含めない（q3rq §5 firewall 継承・柱A 橋 q9mb との二重計上防止）。

---

## 5. 正直な限定（新モジュールが背負うもの・§4 規約により後で消さない）

**q9kd（B6）**:
1. **Galois は有限商 ⟨σ⟩≅Gal(M/L₂) のみ**。副有限 G_{L₂}・絶対 Galois 群・逆極限はゼロ。「実 Galois コホモロジー」は H¹(ℤ/3, μ₃) 相当の具体対までで、一般 H¹ 形式論（galH1Module）への接続はしない（q3k が IUTField でないため既存抽象機構と型が合わない——接続は M 体化後の後続）。
2. **n=3・拡大 1 個・類 1 個**。L₂^×/(L₂^×)³ の**全体**構造（≅(ℤ/3)³ 相当）は計算しない。⟨[ζ₃]⟩ 部分の双対のみ。
3. μ₃⊂L₂・μ₃(O_M) 完全性は q3mc/q9c 消費（本モジュールで再証明しない）。
4. O_M と単数群のみ（体化なし・A2 恒久限定継承）・兄弟担体・実テータ関数ゼロ・π₁ 同定ゼロ。

**q9wr（B1）**:
1. **付値関数 v_M は建てない**。フィルトレーションは π₉ 冪の**可除性形式**（イデアル所属の代数的言明）。完備化・位相・一般元の v_π はゼロ。
2. **G_i の定義は一様化子 π₉ への作用で与える**（i_G(σ)=v(σπ−π) 形）。O_M=O_{L₂}[π₉] の単生成性からこれが標準定義と一致することは数学的事実だが、「任意の x∈O_M に対する σx−x の一様可除性」との同値は形式化しない（正直限定として明記）。
3. **拡大 1 個（M/L₂）・下付き番号のみ**。上付き番号・Herbrand φ/ψ の実版・実 Hasse–Arf（B4）・Artin 導手の実表現論（B3）はゼロ——wcd/ajw/hau の Nat 模型が引き続きそれを担う（B3/B4 の status は動かないと想定するのが正直）。
4. e=6・3=π₉⁶u₆ は q9ps 成果の消費。d(M/ℚ₃)=9 の合成 different（推移公式）は範囲外。

---

## 6. 代替案との正直比較（B ピボットは本当に最高レバレッジか）

- **A 続行**: dashboard 実測で柱A 表示 55 の閾値は s_A7≥0.574（現 0.56）。level-9 橋 q9mb 完結後の次の一手は (1+9ℤ₃) 層＝level-27 か別項目のフルキャンペーン級で、opus 2 本では表示が動かない。**表示 leverage で B に劣後**。
- **D 転進**: 柱D も 18 で display-leverage は同等だが、CLAUDE.md 運用規則が「Phase III 本丸（D-1）は直接実装せず、まず fable 詳細化ラウンドで段階分解」と明記——今ラウンドの opus 実装枠では表示が動かない。**B の 2 モジュールは詳細化済み（本書）＋部品全実在で 1 ラウンド完結が狙える**。
- **敵対的自己反証の試み**: 「B6 は weight 10 しかなく、0.25 でも +2.5 点。B1 の +0.1 と合わせても A の 1 キャンペーン（+0.07×12=+0.84 点/Σ_A）と大差ないのでは」——柱A の直近キャンペーン（モジュール 10 本超・fable 複数）で表示 +2（52→54）だったのに対し、本提案は **opus 2 本で中心予測 +1〜+2（上振れ +4）**。1 モジュールあたり効率で B が明確に優位。反証failed——B ピボットを維持する。
- ただし**フロアシナリオ（表示 18 不動）が実在する**（B6 監査 0.10・B1 0.55 の場合）。これは受容可能なリスク（部品は次ラウンドの貯金になる）だが、着手承認時にユーザーへ明示すること。

---

## 7. 実装計画表

| 順 | モジュール | 柱/項目 | tier/model | 行数 | deps（全て実在） | 動く表示（期待/フロア） |
|---|---|---|---|---|---|---|
| 1 | `IUT/Q3KummerDualityReal.lean`（q9kd）T1–T11 | B6 0→0.15–0.25 期待 | **M / opus** | 450–550 | q3k・q3rq(q3rqLx)・q9ci(no_cbrt)・q9c(m_mu3_complete)・q9yp・(q9tl) | B 18→19–20 ／ 18 |
| 2 | `IUT/Q3WildRamFiltrationReal.lean`（q9wr）U1–U10 | B1 0.5→0.55–0.65 期待 | **M / opus** | 400–500 | q9ps(pi9_cube・coord0)・q9ci(正則性・zeta_norm3)・q9tl(N(Y)=ζ₃)・Q3LocalField(q3f_uniformizer)・wcd(U9) | 単独では不動〜+2・q9kd と合算で最大 22 |
| — | 統合時（親が実施） | gen_graph PILLAR 辞書に `"Q3KummerDualityReal": "B", "Q3WildRamFiltrationReal": "B"` 追記・graph-meta/dashboard 二軸更新・**status 変更は独立監査→ユーザー署名後のみ** | — | — | — | — |
| — | HELP スポット候補 | q9wr U6（正則消去→ノルム 2 段連鎖）のみ。詰まった場合に限り親/fable 引き取り | (L 予備) | — | — | — |

並列運用: 2 本は相互に独立（import 交差なし）→ 同ラウンド並列可。残り 3 枠は本提案の範囲外（完全証明ファースト規則 §2 により、complete_pct を動かさない枠埋めはユーザー確認が先）。

## 8. 評決（3 文）

(a) **動かすのは B6（0→期待 0.15–0.25）を主・B1（0.5→期待 0.55–0.65）を従で、柱B 表示は 18→中心予測 19–20（両方上振れで最大 22・敵対的フロアは 18 不動——B6 が 0.10 評定だと銀行家丸めで 18.5→18 のため）**。
(b) モジュールは `Q3KummerDualityReal`（q9kd・opus・~500 行）と `Q3WildRamFiltrationReal`（q9wr・opus・~450 行）で、消費部品（q3kSigma・q9ci_no_cbrt_zeta・q9c_m_mu3_complete・q9ps_pi9_cube・q9ps_coord0・q9ci 正則性パック・q3f_uniformizer）は全て本体実在確認済み——1 ラウンド 2 本並列で完結可能。
(c) 最大の二重計上リスクは「ζ₃ の 3 乗根非存在」が既存 `q9ci_no_cbrt_zeta`（柱A）と、「3=π₉⁶u₆」が既存 `q9ps_three_split`（柱A）と重なる点だが、q9kd の新規主張を群提示 L₂^× 上の Kummer 類非自明性＋完全双対に、q9wr の新規主張を Galois 側データ σπ₉−π₉（q9ps には Galois が一切ない）に限定し既存補題を named 消費と明記することで**クリア**——既存柱B の Kummer/分岐チェーン（M320F/M345F/M349F は抽象体＋witness/仮説形、wcd/mjw/ajw/hau は Nat 階段模型）に実 Galois 群上のインスタンスは存在しないことを本体読解で確認した。

---

**脚注（本体を読んだ .lean・判定根拠）**: `IUT/Q3KummerCubic.lean`（q3kSigma/q3k_norm_eq/q3kU/q3kZeta9/q3kInv 本体・環公理証明含む 1–492 行精読＋全 def/theorem 列挙）・`IUT/Q3KummerPiSplit.lean`（ヘッダ＋q9ps_coord0/q9ps_pi9_cube/q9ps_w_norm/q9ps_three_split ほか全定理列挙・q9ps_zeta_add_one/q9ps_lamsq' 本体）・`IUT/Q3TateCurveL9.lean`（ヘッダ＋q9tl_normBase_zeta9 本体＋全定理列挙）・`IUT/Q3KummerCubeIdent.lean`（ヘッダ＋q9ci_no_cbrt_zeta/q9ci_pi9_reg/q9ci_unit_reg_M の statement 本体）・`IUT/Q3KummerDescentSpike.lean`（ヘッダ）・`IUT/Q3Mu9Completeness.lean`（ヘッダ・B1–B9 構成）・`IUT/Q3Mu9Rigidity.lean`（ヘッダ・q9mr_aut_mu9_new_layer）・`IUT/Q3RamifiedQuadratic.lean`（q3rqUnitMem=IsZpUnit∘q3rqNorm・q3rqU/q3rqLx 定義行）・`IUT/KummerTheory.lean`（ヘッダ＋全定理列挙・kummerCocycle 型）・`IUT/KummerExact.lean`（ヘッダ＋全定理列挙・hsurj 仮説形）・`IUT/KummerCharReal.lean`（ヘッダ＋kcrChar 本体・「完全 Kummer 双対は外部仮説」限定）・`IUT/KummerNontrivialChar.lean`（ヘッダ）・`IUT/RamifiedNormFiltration.lean`・`IUT/HigherUnitFiltration.lean`・`IUT/DifferentFromFiltration.lean`・`IUT/WildConductorDiscriminant.lean`・`IUT/MultiJumpWildDiscriminant.lean`・`IUT/ArbitraryJumpWild.lean`・`IUT/HasseArfUnconditional.lean`（各ヘッダ＝Nat 階段模型の確認）・`IUT/Zp3ValuationRing.lean`（z3=zpRing 3・z3vExact/z3vMax 定義行）・`IUT/Q3LocalField.lean`（q3f_uniformizer）・`IUT/Q3Mu3Completeness.lean`（定理列挙）・`IUT/Q3UnitsGroup.lean`（q3u_unit_exact0）。**数値根拠**: `target_ledger.json` 柱B 全項目・`tools/compute_complete_pct.py` 全文（Python round＝銀行家丸め）・`graph-meta.json` 柱B complete_note（「実 Galois 群が一つも存在しない」の監査文言）・`AUDIT_RUBRIC.md` 全文・`tools/gen_graph.py` PILLAR 辞書 B 項目・`dashboard.md` 柱A level-9 kill 行（s_A7 閾値 0.574）。
