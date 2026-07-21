# B6（Kummer 理論・実 Galois コホモロジー上）深化詳細化設計 — 2026-07-20

**分類: [設計のみ / design-only]・tier-L 詳細化・complete_pct 0 前進・§4 規約遵守（Lean コードなし・共有ファイル変更なし）**

- 対象: 柱 B・**B6「Kummer 理論（実 Galois コホモロジー上）」**。現状 s_B6 = **0.18**（w10・
  graph-meta 2026-07-11 の敵対的決定「q9cq +0.03」準拠）。既設: q9kd（完全 Kummer 双対・
  `IUT/Q3KummerDualityReal.lean`）・q9ci（立方恒等式・`IUT/Q3KummerCubeIdent.lean`）・
  q9cq（立方剰余群 rank≥2 下界・`IUT/Q3CubeQuotientReal.lean`）。
- 本書の成果: (i) B6 が今証明しているもの／候補 4 本 (a)–(d) の正確なギャップ同定（§1）、
  (ii) **disproof-first 攻撃の実行と結果**（§2 — 候補 (b) 有限レベル Tate 双対と候補 (d)
  単数 Hilbert 90 は**数学的に偽**であることを特定・候補 (a') と rank-4 は数値ゲート PASS・
  付録 A）、(iii) 主発見 2 件 — **q9kd 正直限定 1 の「galH1 接続不能」は M326F（Grp ベース）
  に対しては誤り**（接続は今すぐ choice-free で可能・§2 A1）、および
  **生成元 {ζ₃, 1+λ, 1+λ²} には隠れた関係 ζ₃ ≡ (1+λ)²(1+λ²) mod 立方が存在**
  （rank-4 実装の地雷・§2 A5）、(iv) マイルストーン梯子 K1/K2 と正直な予測（§3/§4）。
- §4 規約: 既存モジュールの正直な限定を消さない・弱めない。到達可能性を過大主張しない。

---

## 0. TL;DR（verdict）

**次の B6 増分は到達可能（research-blocked ではない）— ただし候補の半分は偽なので選別が命。**

1. **K1（第一スライス・今すぐ・choice-free）**: 実 H¹ 同定
   `H¹(Gal(M/L₂), μ₃(O_M)) ≅ Hom = {χ⁰,χ¹,χ²} ≅ ℤ/3` — q9kd の実 3 元群 q9kdG・実
   q9kdMu3 を M326F `galH1Module` に**そのまま instantiate**（M326F は `Grp` のみ要求・
   IUTField 不要——q9kd 正直限定 1 の想定ブロッカーは M320F にしか当たらない）。σ の μ₃ 上
   自明作用は**仮定でなく計算**（`q9kd_sigma_fixes_base`）。Kummer 写像
   δ: ⟨[ζ₃]⟩ → H¹ の**全単射**まで閉じ、リポジトリ初の「実 Galois 群の実 H¹ を実際に
   計算した」モジュールになる。opus 1 ラウンド。
2. **K2（rank≥2 → 完全 (ℤ/3)⁴）**: q9cq の named target
   `L₂^×/(L₂^×)³ ≅ (ℤ/3)⁴` を生成元 **{[λ], [ζ₃], [1+λ], [1+λ³]}** で閉じる（下界 2 段 +
   立方 Hensel 上界 1–2 段・q9ut/q9cl の確立イディオム再利用・数値ゲート PASS 済・付録 A）。
3. **偽・封鎖（着手禁止の明記）**: (b) 有限商上の cup 積 Tate 双対は**恒等的に零**
   （奇素数巡回群で x∪x=0・H¹ が 1 次元）。(d) 単数レベル Hilbert 90 は**偽**
   （H¹(⟨σ⟩,U_M) ≅ ℤ/3 ≠ 0——B2 の余核 ℤ/3 と Herbrand 商から従う）。本物の Tate 双対・
   体レベル Hilbert 90 は副有限 G_{L₂}・体 M^× を要し research-blocked（§2 A3/A4）。

**s_B6 予測（保守・監査次第）: 0.18 → K1 後 0.21–0.23 → K2 完了後 0.28–0.33**。
**推奨第一手: K1 = `IUT/Q3KummerH1Real.lean`（prefix q9kh）を opus 1 本で**（§5）。

---

## 1. 正確なギャップ: B6 が今証明しているもの vs 候補

### 1.1 現有資産（全て実 Lean・ファイル実在確認済）

| 資産 | 内容 | 場所 |
|---|---|---|
| q9kd 完全双対 | 実 Gal(M/L₂)=⟨σ⟩（`q9kdG`・3 元・実環自己同型 `q9kdAct`）× ⟨[ζ₃]⟩ → μ₃ の両側非退化・`q9kd_hom_complete`（Hom(⟨σ⟩,μ₃) = {χ⁰,χ¹,χ²} 完全枚挙）・`q9kd_kummer_iso`（k↦χᵏ 全単射） | `IUT/Q3KummerDualityReal.lean` |
| q9cq rank≥2 | L₂^×=`q3rqLx`=ℤ×U₂ 上 ⟨[λ],[ζ₃]⟩≅(ℤ/3)² ↪ 立方剰余群（`q9cq_rank_ge_two`・非立方性述語形） | `IUT/Q3CubeQuotientReal.lean` |
| q9ci 核 | `q9ci_no_cbrt_zeta`/`_zetaSq`（O_{L₂} 内 ζ₃ の 3 乗根なし）・立方 3 成分恒等式 E0/E1/E2・正則性パック | `IUT/Q3KummerCubeIdent.lean` |
| 抽象 H¹ | `galH1Module`（**`Grp` のみ要求**・:105）・Z¹/B¹/`galH1Group`=H¹（:230）・**自明作用機構 M326F-5**（`galH1TrivialModule`:259・`galH1_cocycle_of_hom`/`galH1_hom_of_cocycle`:267–280・`galH1_trivial_coboundaries_trivial`:303・`galH1_proj_injective_of_trivial`:317・`quotientProjN_surjective` 消費:368）・`galH1KummerHom`（κ→H¹ 合成:383） | `IUT/GaloisCohomologyH1.lean` |
| 抽象 Kummer 完全列 | `kexKummerMap`/`kexIsoHom`（単射は無条件・**全射は明示仮説 `hsurj`**）・`kex_trivial_ker_eq` | `IUT/KummerExact.lean` |
| Hilbert 90 | `hil90_theorem`/`hil90_H1_trivial`（**resolvent 明示仮説**） | `IUT/Hilbert90.lean` |
| cup 積 | `cupProduct`: H¹×H¹→H²（`cupH2group`=Z²/B²・pairing は入力） | `IUT/CupProduct.lean` |
| B2 新着 | `q9qcCoker : Grp`（U_{L₂}/N(U_M) literal 商）・`q9qcGalHom` 単射（`IUT/Q3CokernelObjectReal.lean`）・T3-core `q9cl_norm_surj`（U^{(9)}⊆N・`IUT/Q3NormSurjCompleteLimit.lean`）・tame sweep q9ut | B2 s=0.52 |

### 1.2 候補 4 本のギャップ

- **(a) Kummer 完全列の Galois コホモロジー同定** `L₂^×/(L₂^×)³ ≅ H¹(G_{L₂}, μ₃)`:
  完全形は副有限 **G_{L₂} = Gal(L̄₂/L₂) がリポジトリに存在しない**ため不可（§2 A2）。
  しかし**有限レベル形 (a')** `H¹(Gal(M/L₂), μ₃) ≅ ⟨[ζ₃]⟩ ≅ ℤ/3`（inflation 像＝
  「M で立方になるクラス」の部分）は**今すぐ可**（§2 A1）。数学的にも正しい形:
  |H¹(⟨σ⟩,μ₃)| = |Hom(ℤ/3,ℤ/3)| = 3 であり、81 元の L₂^×/(L₂^×)³ 全体と同型になるのは
  G_{L₂} 版だけ。有限レベルで 81 を主張したら**それは偽**（過大主張ゲート）。
- **(b) 局所 Tate 双対 / cup 積 H¹×H¹→H²≅ℤ/3**: 有限商 ⟨σ⟩ 上では**恒等的に零**で
  双対にならない（§2 A3・偽）。
- **(c) Kummer ↔ 相互律（B2 接続・ノルム剰余記号）**: (a,b)₃ = χ_b(rec(a)) の実装は
  **rec の全射性 = B2 T3-M4-b が前提**（未着地・`audit/pillar-B2-T3-M4-index-detail-2026-07-20.md`
  §3 M4-b）。B6 側から先行できるのは K1 の χ 側だけ。順序依存として §3 K3 に退避。
- **(d) 巡回拡大 M/L₂ の Hilbert 90**: 体 M^× が無い（体化なし・A2 恒久限定）。単数レベル
  H¹(⟨σ⟩, U_M) で代替すると**偽**（§2 A4）。research-blocked（かつ一部は偽）。

---

## 2. Disproof-first 攻撃（実行結果）

### A1: 「q3k が IUTField でないため galH1 と型が合わない」（q9kd 正直限定 1）は本当か

**半分誤り——これが本書の主発見 1**。実際に型を突き合わせた:

- `galH1Module (GK : Grp)` の要求（GaloisCohomologyH1.lean:105–113）は
  **M : Grp（アーベル）＋ act : GK.carrier → Hom M M ＋ act_one/act_mul のみ**。
  IUTField はどこにも現れない。q9kd は `q9kdG : Grp`（:144）と `q9kdMu3 : Grp`（:218）を
  既に持ち、作用 `q9kdAct`（:154）の準同型性 `q9kd_act_mul`（:160）も証明済。
  σ の乗法性・単位保存は `q3k_sigma_mul`/`q3k_sigma_one`（Q3KummerCubic.lean:518/511）・
  `q3k_sigma2_mul`/`q3k_sigma2_one`（:845/839）が実在。**接続に体化は不要**。
- IUTField を本当に要求するのは **M320F `KummerTheory.lean`**（`kummerNthPow (K : IUTField)`
  :103 以下全て）と、その再輸出である M345F の具体部分のみ。q9kd 正直限定 1 は
  この 2 つに対しては**正しい**（消さない・弱めない——K1 のヘッダで「M320F/M345F の
  体ベース具体機構への接続は依然未達」と継承明記すること）。

**残る作業は 3 種の小部品だけ**（全て choice-free・§3 K1 表）:
(i) σ|μ₃ の閉性（σ(x)³ = σ(x³) = 1——`q3k_sigma_mul`×2 + `q3k_sigma_one`）、
(ii) 作用の自明性の**計算**（m ∈ {1, ζ₃, ζ₃²}（`q9c_m_mu3_complete` 消費）を場合分けし、
embed 元は `q9kd_sigma_fixes_base`・σ² は `q3k_sigma2_comp` で 2 回適用）、
(iii) χ 冪の乗法性 `q9kdChiPow (mul j k) = …`（9 ケース・q9kd に未収載の小補題）。

**注意（de-risk・§5）**: M326F-5 の自明作用補題群は `galH1TrivialModule GK M comm` という
**定義上自明な作用のレコード**に対して述べられている。実作用モジュール
q9khModule（act = q9kdAct の制限）を「= galH1TrivialModule」と**構造等式で**同一視する
経路は funext + Hom 構造 ext + structure eta の簿記が要り滑りやすい。**推奨は再証明経路**:
B¹ 自明・Z¹↔Hom 往復・射影単射の 3 補題（各 5–10 行・`galH1_trivial_coboundary_eq_one` 等の
証明体をポイントワイズ自明性仮定 `htriv : ∀ g m, act g m = m` の下で写経）を q9kh 内で
直接建てる。これなら M326F の既存補題は**消費**（`galH1_proj_injective_of_trivial` は
既に一般形 :317 なのでそのまま使える・`quotientProjN_surjective` も一般形）。

### A2: 副有限 G_{L₂} は本当に無いか（完全形 (a) のゲート）

**無い**。`Grep "profinite\|逆極限.*Galois"` 相当の探索で、Galois 側の逆極限は
円分指標塔（`CyclotomicResTower`/`CyclotomicLimitIso`・ℤ/3ᵏ 商の塔）と A4 の π₁ 極限系のみ。
**体拡大の Galois 群として実現された群は ⟨σ⟩ = Gal(M/L₂)（3 元）ただ一つ**
（q9kd 正直限定 1「副有限 G_{L₂}・絶対 Galois 群・逆極限はゼロ」は正確・維持）。
よって `H¹(G_{L₂}, μ₃) ≅ (ℤ/3)⁴` の**左辺は現リポジトリでは書けない**。ただし右辺
（= L₂^×/(L₂^×)³ の完全構造）は群論だけで書けて到達可能——これが K2 であり、
「H¹ 側は将来の副有限インフラ、K^× 側は今」という分業が honest な形（§4 cap 1）。

### A3: cup 積で有限レベル Tate 双対は作れるか — **偽・着手禁止**

奇素数 p の巡回群 C_p の 𝔽_p 係数コホモロジーは H*(C₃;𝔽₃) = Λ(x)⊗𝔽₃[y]
（deg x=1・deg y=2・y は Bockstein）。**deg 1 では x∪x = −x∪x ⟹ 2(x∪x)=0 ⟹ x∪x=0**
（3 は奇数）、かつ H¹ は 1 次元なので **cup: H¹×H¹→H² は恒等的に零**。
`cupProduct`（M350F）を q9kdG に instantiate しても得られるのは零対であり、
「非退化対 H¹×H¹→H²≅ℤ/3」は**定理にならない（偽）**。整合性確認: 本物の Tate 双対は
H¹(G_{L₂},μ₃) ≅ (ℤ/3)⁴（81=3⁴・付録 A で確認）上の**交代**非退化対で、非退化交代形式は
偶数次元 4 でのみ可能——1 次元の有限商へ制限すれば零になるのは必然。
q9kd の非退化対（`q9kd_pairing_eq`・Gal×⟨[ζ₃]⟩→μ₃）は **cup ではなく評価対**
（Kummer ペアリング）であり、これと混同して「Tate 双対済み」と報告しないこと。

### A4: 単数レベル Hilbert 90 は成り立つか — **偽**

H¹(⟨σ⟩, U_M)（実作用・非自明）に `hil90_H1_trivial` を instantiate する案は**数学的に偽**:
巡回群の Herbrand 商 h(U_M)=1（局所体の単数群）と **B2 の実結果**
|Ĥ⁰| = |U_{L₂}/N(U_M)| = 3（下界 `q9rc_order3`・上界は T3-M4 で =3 へ）から
**|H¹(⟨σ⟩,U_M)| = 3 ≠ 0**。resolvent 仮説は単数係数では**破綻すべくして破綻する**
（Hilbert 90 は体 M^× 係数の定理・π₉^{-k} 込みの分数元が本質）。体 M^× はリポジトリに
無い（体化なし・恒久限定）ので、候補 (d) は**偽（単数版）+ research-blocked（体版）**。
副産物の positive な読み替え: |H¹(⟨σ⟩,U_M)|=3 の**下界**は将来 B2×B6 接続の実定理候補
（周期性 Ĥ⁰≅H² 経由で q9qcCoker と接続・§3 K4 停留所・本ラウンドでは設計しない）。

### A5: rank-4 の生成元選定 — 数値ゲート実行（付録 A・本ラウンド実行）

Z[ω]/3⁴（厳密整数演算・λ=1+2ω・λ²=−3）で単数 4374 個を全数検査:

- |U/U³| = **27**（∴ |L₂^×/(L₂^×)³| = 3×27 = **81 = 3⁴** — q9cq named target と一致）✓
- **{ζ₃, 1+λ, 1+λ³} は 27/27 クラスで独立** ✓（{ζ₃, 1+λ², 1+λ³} も可）
- **地雷 1**: {ζ₃, 1+λ, 1+λ²} は**非独立**——隠れた関係
  **ζ₃ ≡ (1+λ)²(1+λ²) mod (L₂^×)³**（9/27 クラスに退化・付録 A COLLISION 出力）。
  「浅い方から順に 1+λ, 1+λ² を取る」自然な実装は**失敗する**。
- **地雷 2**: 1+λ⁴ は立方（{ζ₃,1+λ,1+λ⁴} も 9/27 に退化）。
- **立方全射深度: U^{(4)}_λ ⊆ (L₂^×)³・U^{(3)}_λ は非包含**（1+λ³ が非立方生成元・sharp）。
  B2 のノルム深度（U^{(3)}_λ=q9nfUfilt 9）と 1 違うので流用時に定数を写し間違えないこと。

**ゲート PASS**: K2 の LCFT 帳簿は数値レベルで完全に閉じ、生成元は
**{[λ], [ζ₃], [1+λ], [1+λ³]}** に確定。

### A6: K2 上界（立方 Hensel）に choice は要るか

**要らない**。x³=u の逐次近似塔は B2 T3-M3 が確立した**そのままのイディオム**
（`q9cl`: 塔 coherence・z3cLim 閉式極限・N 連続性・分離性——`IUT/Q3NormSurjCompleteLimit.lean`）で、
しかも**易しくなる**: 係数は O_{L₂}（z3 座標 **2 本**・q9cl は O_M の 6 本）、写像は
x↦x³（自己写像・σ 共役 3 本のノルムより単純・連続性は純環望遠鏡恒等式 1 本）。
更新則は Hensel: x_{n+1} = x_n + h、(x_n+h)³ − u ≡ 3x_n²h + (x_n³−u)、3 = −λ²
（`q3rq_three_eq_neg_lambda_sq`・厳密等式）で λ-深度が 1 段ずつ稼げる（p=3 の分岐 e=2 でも
深度 4 以深なら単調・数値ゲートの depth=4 と整合）。modulus 閉式・可算選択不要。

### 総合判定

候補 (a')（有限レベル H¹ 同定）と rank-4 完全化は**障害ゼロ・到達可能**。
候補 (b)(d) は**偽**（着手すれば水増しどころか誤り）。完全形 (a)・体版 (d)・本物 Tate 双対は
**research-blocked**（副有限 G_{L₂}・体 M^× のインフラ待ち・B6 単独では建てない）。

---

## 3. マイルストーン梯子（IF reachable → K1/K2 は YES）

### K1: 実 H¹ 同定 `IUT/Q3KummerH1Real.lean`（prefix **q9kh**・衝突なし・今すぐ）

分類ヘッダ: [実／(a) 昇格]（q9kd 正直限定 1 の「galH1 接続なし」を M326F に対して閉じる・
抽象 H¹ 機構の**初の実 instantiate**・toy 主語なし）。

| 段 | 内容 | 消費資産 |
|---|---|---|
| k1 | σ|μ₃ 閉性 + 実作用モジュール `q9khModule : galH1Module q9kdG`（M := q9kdMu3・act := q9kdAct 制限） | q3k_sigma_mul/q3k_sigma_one/q3k_sigma2_mul/q3k_sigma2_one・q9kd_act_mul |
| k2 | **作用自明性の計算** `q9kh_act_trivial : ∀ g m, …act g m = m`（仮定でない） | q9c_m_mu3_complete（枚挙）・q9kd_sigma_fixes_base・q3k_sigma2_comp |
| k3 | 自明性 3 補題の再証明（B¹=1・Z¹↔Hom 往復・htriv 形——§2 A1 の de-risk 経路） | galH1_trivial_coboundary_eq_one 等の証明体写経・galH1_proj_injective_of_trivial（一般形をそのまま消費） |
| k4 | **H¹ 完全枚挙**: `q9kh_H1_complete` — H¹(Gal(M/L₂),μ₃) の任意元は proj(χᵏ) のいずれか・pairwise 相異 ⟹ **ちょうど 3 元 ≅ ℤ/3** | k3 + quotientProjN_surjective + q9kd_hom_complete + q9kd_kummer_iso_inj |
| k5 | χ 冪乗法性 `q9kh_chipow_mul`（9 ケース）＋ Kummer コサイクル割当 κ : q9kdG → Z¹（k ↦ (g ↦ χᵏ(g))・**Hom として**）＋ `galH1KummerHom` 合成 δ | q9kdChiPow・galH1_cocycle_of_hom 相当（k3 版）・galH1KummerHom |
| k6 | **capstone**: δ : ⟨[ζ₃]⟩-index → H¹ **全単射** = 有限レベル Kummer 同型の Galois コホモロジー実現（kex の `hsurj` 型仮説がこの実例では**証明**になる旨をヘッダに）＋ q9cq 側クラス（`q9cq_zetaClass`）との突合 | k4+k5・q9kd_class_nontrivial・kex_trivial_ker_eq（参照のみ） |

- **新イディオム**: ほぼゼロ（k3 の写経と 9 ケース検査のみ）。**tier: M（opus）・1 ラウンド**。
  行数見積 300–400。
- ヘッダ必須の正直限定: 有限商 ⟨σ⟩ のみ（G_{L₂} なし）・H¹ は 3 元で L₂^×/(L₂^×)³ 全体
  （81 元）とは**同型でない**（inflation 像のみ）・M320F/M345F の体ベース機構への接続は
  依然未達・cup/Tate 双対は主張しない（§2 A3 の零性ゆえ）。

### K2: 立方剰余群の完全構造 (ℤ/3)⁴（q9cq named target の完済・2–3 ラウンド）

生成元確定: **{[λ], [ζ₃], [1+λ], [1+λ³]}**（§2 A5・{ζ₃,1+λ,1+λ²} は禁止）。

| 段 | 内容 | tier | 消費資産 |
|---|---|---|---|
| K2a `Q3CubeRankThree` | [1+λ] 非立方 + ζ₃ との 8 結合独立 ⟹ **rank≥3**。非立方性は gr 簿記: (1+λt)³ = 1 + λ³(…) mod（3=−λ² で 3λt 項が λ³ 深度・E 展開は q9ci 恒等式流用）⟹ 1+λ の λ-深度 1 剰余は立方像に現れない | M (opus) | q3rq_three_eq_neg_lambda_sq・q9ut の gr¹/gr² sweep イディオム・q9ci E0/E1/E2 |
| K2b `Q3CubeRankFour` | [1+λ³] 追加・単数側 26 非自明結合の全非立方（付値側 54 結合は q9cq_val_nontrivial 一般形で既済）⟹ **rank=4 下界** | M (opus) | K2a + q9cq_val_nontrivial・q9nf の λ-level sharp イディオム |
| K2c `Q3CubeHensel` | **上界/exhaustion**: 立方 Hensel（U^{(4)}_λ ⊆ (L₂^×)³・§2 A6 の 2 座標 z3cLim 塔）＋ tame 断面 27 類の被覆（q9ut a3–a5 の写経・N を立方に差替え）⟹ 任意の x ∈ L₂^× が λ^a ζ₃^b (1+λ)^c (1+λ³)^d mod 立方 ⟹ **L₂^×/(L₂^×)³ ≅ (ℤ/3)⁴ 完全**（81 類・商群対象は q9qc と同型に quotientGroupN で建てる） | M (opus)×1–2 | q9cl 塔イディオム・z3cLim・q9ut 帳簿・quotientGroupN |

- K2c 着地で q9cq named target（ヘッダの「2〜3 ラウンド案件」）が予定通り完済。
  K2 は K1 と**独立・並列可**（別ファイル・依存なし）。
- 将来接続（本梯子のスコープ外・順序メモ）: **K3** = B2 T3-M4-b（Gal ≅ 余核）着地後の
  ノルム剰余記号 (a,ζ₃)₃ = χ(rec a)（B6×B2 束ね・rec の逆向きデータ化は 𝔽₃ 三分法で
  choice-free 見込み・要別途詳細化）。**K4** = 周期性 Ĥ⁰≅H² 経由の実 H²（§2 A4 副産物・
  cupH2group の実 instantiate・tier-L 詳細化を先行させること）。

---

## 4. 保守的な正直予測と B6 の cap

| 段 | 内容 | tier | s_B6 予測（監査次第） |
|---|---|---|---|
| （現在） | q9kd 双対 + q9cq rank≥2 | — | **0.18** |
| K1 | 実 H¹ 同定・δ 全単射（**B6 の看板を「群論」から「Galois コホモロジー」へ**） | opus ×1 | → 0.21–0.23 |
| K2a–b | rank=4 下界 | opus ×2 | +0.02–0.04 |
| K2c | 完全構造 (ℤ/3)⁴（q9cq named target 完済） | opus ×1–2 | → **0.28–0.33** |

w_B6 = 10 なので完走で柱 B へ ≈ +1.0〜1.5pt 相当（B2 の大 mover ほどではないが、
0.18 は B 項目最下位圏であり成長余地・単価は良好）。監査前例に整合する保守性:
q9kd（完全双対の新建設）が 0.15、q9cq（軽量組立）が +0.03 だった——K1 は「抽象機構の
初 instantiate + 実計算」で q9kd と q9cq の中間の質量、K2 は数学量は多いが確立イディオムの
写経成分が大きい。

**K1/K2 完了後も残る正直な限定（§4 規約・消さない・弱めない・B6 の当面の天井）**:

1. **副有限 G_{L₂} 不在**: H¹(G_{L₂},μ₃) ≅ L₂^×/(L₂^×)³（完全形 (a)）は左辺が書けない。
   K2 完了で**右辺（K^× 側）は完全**になるが、コホモロジー側は有限商 1 個のまま。
   解消には Galois 群の逆極限インフラ（円分塔 CyclotomicResTower の Galois 版）が要る
   ——B6 単独でなく柱 A（A4/A6）との共同案件・別途 tier-L 詳細化必須。
2. **Tate 双対・cup**: 有限商上は恒等的零（§2 A3・偽）。副有限化まで封鎖。
3. **Hilbert 90**: 単数版は偽・体版は体化待ち（§2 A4）。
4. **M320F/M345F（IUTField ベースの抽象 Kummer）との接続**: q9kd 正直限定 1 の
   この部分は残存（M 体化後の後続のまま）。
5. n=3・拡大 M/L₂ 1 個・体 L₂ 1 個・O_M と単数のみ（恒久限定継承）。

これらが s_B6 の残り ≈ 0.67–0.72 の実体。**B6 は 0.35 前後で一旦プラトーに入る**見込みで、
その先は副有限インフラという柱横断投資が必要——「B6 だけを磨き続けない」判断材料として明記。

---

## 5. 推奨する次の一手

1. **第一スライス = K1（`IUT/Q3KummerH1Real.lean`・opus 1 本・今すぐ）**。実装順は
   k1 → k2 →（k3 が唯一の新規部品）→ k4/k5 → k6。K2a を同ラウンドの別枠に並列で
   差し込める（独立・別ファイル・5 並列の埋め草として適格・complete_pct を動かす枠）。
2. **de-risk 項目（k3 を最初に検証する理由）**: K1 で唯一滑り得るのは「実作用モジュールと
   galH1TrivialModule の同一視」。§2 A1 の通り**構造等式経路を取らず**、htriv
   （ポイントワイズ自明性）の下で 3 補題を再証明する経路を必ず取ること。万一 k3 が
   予想外に重い場合の fallback: `galH1TrivialModule q9kdG q9kdMu3 comm` を**そのまま**主語にし、
   k2 の `q9kh_act_trivial` を「この instantiate が実作用と一致することの定理」として
   併置する（H¹ 計算は自明モジュール側で行う・数学的内容は同値・正直限定に 1 行追記）。
3. **報告時の禁止事項**: (i)「Tate 双対」「Hilbert 90」の語を成果に使わない（§2 A3/A4）。
   (ii) K1 の H¹ は 3 元であり「L₂^×/(L₂^×)³ ≅ H¹」とは書かない（それは G_{L₂} 版・未達）。
   (iii) K2 実装者へ生成元 {λ, ζ₃, 1+λ, 1+λ³} の指定と地雷 2 件（§2 A5）を必ず伝達する。

---

## 付録 A: disproof-first 数値ゲート（本ラウンド実行・再現用・依存なし・厳密整数演算）

スクリプト: scratchpad `b6check.py`（Z[ω]/3⁴・ω=ζ₃・λ=1+2ω・λ²=−3・単数 4374 個全数）。

```
|U mod 81| = 4374・|U³ mod 81| = 162・index U/U³ = 27          → 81 = 3⁴ 確定 ✓
{ζ₃, 1+λ, 1+λ³} 独立（27/27）✓・{ζ₃, 1+λ², 1+λ³} 独立（27/27）✓
{ζ₃, 1+λ, 1+λ²} 非独立（9/27・ζ₃ ≡ (1+λ)²(1+λ²) mod 立方）    → 地雷 1
{ζ₃, 1+λ, 1+λ⁴} 非独立（1+λ⁴ ∈ 立方）                          → 地雷 2
U^{(1)}/U^{(2)}/U^{(3)}: 非立方元あり・U^{(4)}: 全立方（深度 4 sharp）✓
```

（cup 零性 §2 A3 と H¹(⟨σ⟩,U_M)≅ℤ/3 §2 A4 は数値でなく標準理論
（H*(C₃;𝔽₃)=Λ(x)⊗𝔽₃[y]・Herbrand h(U)=1 + B2 実測 Ĥ⁰=ℤ/3）による論証であり、
実装対象から**除外**するための根拠として記録する。）
