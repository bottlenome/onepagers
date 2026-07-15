# 柱B6 深掘りスコープ: 実局所体の立方剰余群 L₂^×/(L₂^×)³ 全体構造は今ラウンドで割れるか — 敵対的設計監査（2026-07-11）

**種別**: 詳細化ドキュメント（design-only・Lean 実装なし）
**対象**: 柱B B6「Kummer 理論（実）」（w10・現 status 0.15・q9kd の完全巡回3次 Kummer 双対に由来）
**前提**: 柱B 表示 26。厳密 Σ_B = 20·0.60(B1) + 20·0(B2) + 20·0.20(B3) + 15·0.10(B4) + 15·0.5(B5) + 10·0.15(B6) = 26.5 →（banker's）26。q9kd 正直限定 2 が明示した named gap =「**L₂^×/(L₂^×)³ の全体構造は未計算（⟨[ζ₃]⟩ 部分のみ）**」を割りにいく。
**姿勢**: 敵対的・正直。**デフォルト判定 =「全体構造（rank 4）は重い／q9kd が既に creditable な部分を押さえており、水増しの capstone 束ねを B6 status に化けさせてはならない」**。この推定を、実 def/theorem 本体（q9kd・q3rq・q9ci・prodGrp/intGrp）を読んで覆せるかどうかを検証した。

---

## TL;DR

- **全体構造 L₂^×/(L₂^×)³ ≅ (ℤ/3)⁴ の "完全計算" は今ラウンドでは割れない（重い・2〜3 ラウンド案件）**。数学的なランクは確定（下記 §1 で二重計上チェック済み: 分解 1+3=4 と局所体公式 [L₂^×:(L₂^×)³]=81=3⁴ が一致）だが、Lean-core で建つのは **rank ≥ 2 の下界**（部分群 ⟨[λ],[ζ₃]⟩ ≅ (ℤ/3)²）**のみ**。残る 2 次元（主単数 1+m ≅ ℤ₃² 部分）と、**上界＝exhaustion（"高々 rank 4"）は主単数フィルトレーション・v_M・graded 判別器を要し、B2 監査が flag した未建設機構と同じ**。
- **今ラウンドの genuine な真水は薄いが実在する**: (1) 一様化子クラス **[λ] の非立方性**（付値論法・3∤1 の 1 行）と、(2) **[λ] と [ζ₃] の 𝔽₃-独立性**（＝ q9kd の ⟨[ζ₃]⟩ rank≥1 を ⟨[λ],[ζ₃]⟩ rank≥2 へ拡張）。**新規部分は付値方向 [λ] と独立性の組み立てのみ**——非立方性の核（ζ₃・ζ₃² が O_{L₂} 内で非3乗）は **q9ci_no_cbrt_zeta / q9ci_no_cbrt_zetaSq を消費**（再証明せず）。
- **二重計上リスクは低い**。q9kd は ⟨[ζ₃]⟩ の 1 クラスのみ（`q9kd_class_nontrivial`）で [λ] も独立性も持たない。抽象 Kummer（`KummerTheory` M320F・`KummerExact` M345F）は**抽象体 K の K^×/(K^×)ⁿ（tateMultGroup・IUTField・Hilbert 90）**であって、**実局所体 L₂ = q3rqLx = ℤ×U₂ の具体立方剰余群を計算した初モジュール**。主語が別（抽象体 vs 実 ℤ₃[√−3]）。
- **推奨**: **rank ≥ 2 下界のみを honest に建て、full rank 4 を主張しない**。モジュール `Q3CubeQuotientReal.lean`（q9cq・tier M/opus・~200 行）。**予測 B6 0.15 → 0.20**（named gap を「rank≥1 → rank≥2」へ部分前進・full structure は据置）。**Σ_B 26 → 27（+1 表示前進）**。0.25（→28）は主単数 2 次元＋上界を要し、それは missing discriminator ＝ 過大主張なので**しない**。

---

## 1. 目標構造 L₂^×/(L₂^×)³ = q3rqLx/(q3rqLx)³ の正確化と二重計上（ランク）チェック

### 1.1 群提示と立方写像の成分分解

コードベースの実群提示は `q3rqLx := prodGrp intGrp q3rqU`（`Q3RamifiedQuadratic.lean` q3rq-4b）。すなわち **L₂^× = ℤ(v_λ) × U₂**、U₂ = O_{L₂}^× = `q3rqU`。`FundamentalGroup.lean` の実定義から:

- `intGrp`: 台 `Int`・`mul a b = a + b`・`one = 0`（＝加法群 (ℤ,+)）。
- `prodGrp G H`: `mul p q = (G.mul p.1 q.1, H.mul p.2 q.2)`（**成分ごと**）。

ゆえに任意 g = (n, u) ∈ ℤ×U₂ に対し、群冪 g³ = `q3rqLx.mul (q3rqLx.mul g g) g` は成分ごとに:

> **g³ = (n + n + n, u·u·u) = (3n, u³)**（第1成分は intGrp の加法で 3n、第2成分は U₂ の立方 u³）。

したがって **立方剰余群はテンソル的に分裂**する:

> **q3rqLx/(q3rqLx)³ ≅ (ℤ/3ℤ) × (U₂/(U₂)³)**（第1成分 ℤ/3 は [λ]、第2成分は単数部）。

これは Lean-core で（商群を建てずとも）「g³ の第1成分は 3 で割れる」という**無条件・1 行の付値補題**に落ちる（§2.1）。

### 1.2 単数部 U₂/(U₂)³ の 𝔽₃-次元（数学的評価）

局所体 U₂ = O_{L₂}^× の構造定理（残余体 𝔽₃・f=1・d=[L₂:ℚ₃]=2）:

- U₂ = μ_{q−1} × (1 + m) = **μ₂ × (1+m)**（q=3 ゆえ μ_{q−1}=μ₂={±1}）。
- 主単数 1+m は ℤ₃-加群として **1+m ≅ μ_{3^a} × ℤ₃^d = μ₃ × ℤ₃²**（ζ₃ ∈ L₂ だが ζ₉ ∉ L₂＝[ℚ₃(ζ₉):ℚ₃]=6>2 ゆえ a=1; ζ₃−1 ∈ m ＝ `q3rq` の m_{L₂}=(√−3)=(ζ₃−1) より ζ₃ は主単数）。

立方剰余（×3 の余核）を成分ごとに取る:

| 因子 | 元 | /(·)³ | 𝔽₃-次元 |
|---|---|---|---|
| μ₂ = {±1} | −1 = (−1)³ は立方 | 自明 | **0** |
| μ₃（主単数内） | ζ₃ | ℤ/3（×3 が μ₃ を潰す） | **1** |
| ℤ₃²（主単数 torsion-free） | 基本単数 2 個 | (ℤ/3)² | **2** |

⟹ **U₂/(U₂)³ ≅ (ℤ/3)³**（次元 0+1+2=3）。[λ] を足して **L₂^×/(L₂^×)³ ≅ (ℤ/3)⁴（rank 4）**。

### 1.3 二重計上（ランク）チェック — 分解 vs 局所体公式

独立2経路でランクを算出し一致を確認する:

**経路A（成分分解・§1.1–1.2）**: 1（[λ]）+ 0（μ₂）+ 1（μ₃）+ 2（主単数 ℤ₃²）= **4**。

**経路B（局所体の指数公式）**: 局所体 K・n に対し [K^×:(K^×)^n] = n·|μ_n(K)| / |n|_K（normalized）。K=L₂・n=3:
- |μ₃(L₂)| = 3（μ₃⊂L₂・`q3rq_zeta_cube`＋位数ちょうど3 `q3rq_zeta_sq_ne_one`）。
- |3|_{L₂} = |λ²·unit|_{L₂} = (3^{−1})² = 3^{−2} = 1/9（3 = −λ²・`q3rq_lambda_sq`・f=1 で π=λ は 3^{−1}）。
- [L₂^×:(L₂^×)³] = 3 · 3 / (1/9) = **81 = 3⁴** ⟹ rank = **4**。

**両経路一致（rank 4・|quotient|=81）。** さらに標準結果「μ_p ⊂ K ⟹ dim_{𝔽_p} K^×/(K^×)^p = [K:ℚ_p] + 2」でも 2+2 = 4。**プロンプトの r = 2 + d 公式を検算確認**。数学的なターゲットは (ℤ/3)⁴ で確定。

---

## 2. Lean-core で今ラウンド genuine に建つもの vs 重いもの（敵対的仕分け）

### 2.1 【建つ・EASY】一様化子クラス [λ] の非立方性（付値論法）

[λ] を群提示上で (1, e_{U₂}) ∈ ℤ×U₂ と実現（v_λ=1・単数部自明）。注意: `q3rqLambda = (0,1) ∈ q3rqCar` は**単数でない**（N(λ)=0+3·1²=3 は ℤ₃-単数でない）ので U₂ の元ではなく、L₂^× では付値 1 の元＝群提示第1成分 1 で表される。§1.1 より:

> **q9cq_lambda_nontrivial**: `¬ ∃ g : q3rqLx.carrier, g³ = ((1:Int), e_U)`。証明: g³ の第1成分 = 3·g.1 = 1 ⟹ 3∣1 ⟹ 矛盾（`omega`）。

**1 行・無条件・choice-free。genuine な新規（q9kd は付値方向を一切持たない）。** これが「別コースを走る」でなく「本コースを 1 次元進む」真水。

### 2.2 【建つ・独立性は q9ci 消費】[λ] と [ζ₃] の 𝔽₃-独立性（rank ≥ 2）

[ζ₃] = (0, ⟨q3rqZeta, q3rq_zeta_unit⟩)（q9kd と同一クラス）。⟨[λ],[ζ₃]⟩ が商内で (ℤ/3)² を張る ⟺ 各 (i,j) ∈ {0,1,2}²∖{(0,0)} で [λ]^i·[ζ₃]^j = (i, ζ₃^j) が非立方。場合分け:

- **i ≠ 0（i=1,2）**: 第1成分 i ∈{1,2}、3∤i ⟹ 非立方（**§2.1 の付値論法・EASY・新規**）。4 ケース（(1,0),(2,0),(1,1),(2,1),(1,2),(2,2)）を一括で処理。
- **i = 0, j = 1**: ζ₃ が U₂ 内で非立方。⟺ `q9kd_class_nontrivial`（=`q9ci_no_cbrt_zeta` 経由）**を消費**。再証明しない。
- **i = 0, j = 2**: ζ₃² が非立方。⟺ `q9ci_no_cbrt_zetaSq` **を消費**。

⟹ **q9cq_lambda_zeta_indep**: 8 個の非自明結合が全て非立方 ⟹ ⟨[λ],[ζ₃]⟩ ≅ (ℤ/3)²。**genuine な新規部分＝付値方向 [λ] ＋ 独立性の組み立てのみ**（非立方性の核は既存 q9ci を消費）。真水は薄いが実在し、named gap を「rank≥1 → rank≥2（4 のうち 2）」へ前進させる。

### 2.3 【重い・建たない】残り 2 次元（主単数 ℤ₃²）と上界 exhaustion

full rank 4 を主張するには **(a) rank ≥ 4（4 独立クラスの下界）** と **(b) rank ≤ 4（全元が 4 生成子×立方で尽くされる exhaustion）** の両方が要る。両方とも今ラウンドでは建たない:

- **(a) の残り 2 次元**: 主単数 1+m ≅ ℤ₃² の 2 個の基本単数クラスを判別するには、**単数を立方 mod で分離する判別器**が要る。B2 監査（`audit/pillar-B2-reciprocity-normgroup-scope-2026-07-11.md` §1.2）が確定した通り、**コードベース唯一の判別器 φ = q3rqNorm∘N は単数に盲目**（`q3rq_zeta_norm: N(ζ₃)=1`＝ζ₃ と 1 を分離不能）。今ある非立方判別器は q9ci の「**立方の第2座標 ≡ 0 mod 3**」（`q3mc_cube_snd`: cube の √−3 成分 = 3·(a²−b²)·b）のみで、これは **√−3 座標 mod 3 という 1 個の 𝔽₃-汎関数**＝[ζ₃] 方向 1 次元しか見えない。2 個目の主単数方向は mod λ²（graded piece U^(1)/U^(2)）を要し、未建設。
- **(b) の上界 exhaustion**: 主単数の ℤ₃-加群構造（1+m ≅ μ₃×ℤ₃²）＝ log/exp または U^(i) フィルトレーションを要する。q3rq 正直限定 4（「1+3ℤ₃ の pro-3 主単数部分は n≥2＝F-wild まで残存」）・B2 監査 §1.3（「有限 mod-m 計算では原理的に決着不能・v_M 不在」）が明示する**未建設機構そのもの**。**2〜3 ラウンド案件**。

**判定: full rank 4（＝named gap の完全 close）は今ラウンド不可。rank ≥ 2 下界のみ genuine。**

---

## 3. モジュール設計 `Q3CubeQuotientReal.lean`（q9cq）

**分類**: [実／(a) 昇格]（q9kd の ⟨[ζ₃]⟩ rank≥1 部分構造を、実群提示 ℤ×U₂ 上の ⟨[λ],[ζ₃]⟩ ≅ (ℤ/3)² 部分構造へ昇格）。**toy 主語なし**（主語は実 q3rqLx = ℤ×U₂）。
**tier**: **M（opus）**——確立イディオム（付値非立方 ＋ 既存 q9ci 非立方の消費 ＋ prodGrp 成分立方）の新インスタンス。新イディオムの発明なし（fable 不要）。
**消費（再主張しない）**: `q9kd_class_nontrivial`（q9kd）・`q9ci_no_cbrt_zeta` / `q9ci_no_cbrt_zetaSq`（q9ci）・`q3rqLx`/`q3rqZeta`/`q3rq_zeta_unit`（q3rq）・`prodGrp`/`intGrp`（FundamentalGroup）。
**行数見積**: ~180–260 行。

### 3.1 定理群（design）

| ID | 定理 | 内容 | 根拠／消費 | 難度 |
|---|---|---|---|---|
| q9cq-1 | `q9cq_cube_fst` | g³ の第1成分 = 3·g.1（∀ g:q3rqLx） | prodGrp/intGrp 成分立方・rfl | 自明 |
| q9cq-2 | `q9cq_lambdaClass` | [λ] := ((1:Int), e_U) の定義 | — | def |
| q9cq-3 | `q9cq_lambda_nontrivial` | ¬∃ g, g³ = [λ]（付値 3∤1） | q9cq-1 + omega | EASY・**新規** |
| q9cq-4 | `q9cq_zetaClass` | [ζ₃] := (0, ⟨q3rqZeta,·⟩)（q9kd と同一） | q3rq_zeta_unit | def |
| q9cq-5 | `q9cq_val_nontrivial` | i∈{1,2} で ¬∃ g, g³=(i, u)（任意 u） | q9cq-1 + omega | EASY・**新規** |
| q9cq-6 | `q9cq_zeta_noncube` | ¬∃ g, g³=(0,ζ₃) ∧ 同 ζ₃² | **q9ci 消費**（第2成分へ射影） | 消費 |
| q9cq-7 | `q9cq_lambda_zeta_indep` | 8 個の (i,ζ₃^j)≠(0,e) が全非立方 | q9cq-5,6 束ね | **新規（組立）** |
| q9cq-8 | `q9cq_rank_ge_two` | ⟨[λ],[ζ₃]⟩ ≅ (ℤ/3)²（honest 下界形） | q9cq-3,7 | **新規（capstone）** |
| q9cq-9 | `Q3CubeQuotientData` / `q9cq_data` / `q9cq_exists` | データ束ね | 上記 | capstone |

**注**: full structure (ℤ/3)⁴ は**定理化しない**。§1.3 の rank 4／|quotient|=81 は**コメント（named target）としてのみ**記録し、built content は rank ≥ 2 下界に限定する（過大主張禁止・§4 正直申告）。

### 3.2 正直な限定（ヘッダに記載・消さない・弱化しない）

1. **rank ≥ 2 下界のみ**。full rank 4（(ℤ/3)⁴）は未計算——主単数 1+m ≅ ℤ₃² の 2 次元と**上界 exhaustion（高々 rank 4）は未達**（v_M・主単数フィルトレーション U^(i)・graded 判別器を要す・B2 監査 §1.3／q3rq 限定 4 継承）。
2. **非立方性の核は消費**。ζ₃・ζ₃² の非3乗は q9ci を消費（本モジュール新規は付値方向 [λ] と独立性組立のみ）。
3. **商群オブジェクトは建てない**。「¬∃ g, g³=x」の非立方性述語形（q9kd_class_nontrivial 準拠）で下界を述べる。μ₂ 部分が自明（−1 は立方）である事実も定理化せず註記のみ。
4. q3rq/q9kd の恒久限定（O_L と L^× のみ・体化なし・Galois 作用 σ 超えゼロ・実テータ/π₁ ゼロ・tmzLimit 橋なし・兄弟担体）を継承。
5. 全て choice-free・sorry 皆無・#print axioms は [propext, Quot.sound] のみ・禁止タクティク不使用。

---

## 4. 二重計上チェック（genuinely new か）

- **vs q9kd（`Q3KummerDualityReal.lean`）**: q9kd は `q9kd_class_nontrivial` ＝ ⟨[ζ₃]⟩ の**単一クラス非3乗（rank≥1）のみ**。[λ] クラスも独立性も持たない。**新規 = [λ] 非立方（付値）＋ [λ],[ζ₃] 独立（rank≥2）**。非立方の核（q9ci）は q9kd も本モジュールも同じく消費するので、真水は「付値方向＋組立」に限られるが、それは q9kd に不在で genuine。⟨[ζ₃]⟩→⟨[λ],[ζ₃]⟩ の 1 次元前進。
- **vs 抽象 Kummer（`KummerTheory` M320F・`KummerExact` M345F）**: これらは**抽象体 K の K^×/(K^×)ⁿ**（`tateMultGroup`・`IUTField`・Hilbert 90 で H¹(G_K,μ_n) 同型）。**実局所体 L₂ = ℤ₃[√−3] = q3rqLx の具体立方剰余群を計算したものは無い**。本モジュールは実局所体の cube-quotient を計算する**初モジュール**。主語が別（抽象 vs 実 ℤ₃ 対環）＝二重計上なし。
- **vs q9ci（`Q3KummerCubeIdent.lean`）**: q9ci は非立方の**核**（ζ₃・ζ₃² が O_{L₂} 内非3乗・第2座標 mod 3 論法）。本モジュールはそれを**消費して商構造へ組み立てる**＋[λ] を追加。消費であって重複証明ではない。
- **vs q9cs/q9ps/q9wr**（DescentSpike・PiSplit・WildRamFiltration）: これらは M=q3k（level-9 ζ₉・π₉ wild）側の foundation。本モジュールは L₂=q3rq（base 局所体）側の立方剰余群。層が別。
- **grep 確認**: `L₂^×/(L₂^×)³` の全体構造・cube-quotient の rank を計算した既存モジュールは無し（rank 系ヒットは AlgebraTensor/HasseArfAbelian の別文脈）。**genuinely new を確認**。

---

## 5. 算術と予測（complete_pct 主指標）

現 Σ_B = 26.5 → 26（banker's・.5 境界を**下丸め**）。B6 weight=10・現 0.15。**現在が .5 の下丸め位置にあるため、小さな bump でも表示が動く**:

| B6 遷移 | ΔB6 raw | 新 Σ_B | banker's 表示 | 表示移動 | 判定 |
|---|---|---|---|---|---|
| 0.15 → 0.20 | +0.05·10 = +0.5 | 27.0 | **27** | 26 → 27（+1） | **本命・honest** |
| 0.15 → 0.22 | +0.07·10 = +0.7 | 27.2 | 27 | +1 | 可 |
| 0.15 → 0.25 | +0.10·10 = +1.0 | 27.5 | **28**（27.5→偶28） | +2 | **過大主張・不可** |
| 0.15 → 0.30 | +0.15·10 = +1.5 | 28.0 | 28 | +2 | 遠い（full rank 要） |

**honest forecast: B6 0.15 → 0.20（+0.05）**。理由:
- 上げ材料: named gap「全体構造未計算（⟨[ζ₃]⟩ のみ）」に対し、**rank≥1 → rank≥2 の部分前進**（4 のうち 2 次元を明示部分群として確定）＋付値方向 [λ] という初の第2成分外の real クラス。
- 抑え材料: **full rank 4 は未達**（主単数 2 次元＋上界 exhaustion なし）・**非立方の核は q9ci 消費**（真水＝付値＋組立のみ・薄い）・**商群オブジェクト未建設**（述語形下界）。0.25（→28）は主単数判別器＝missing machinery を要するので**しない**。
- **Σ_B 26 → 27（+1 表示前進・honest・cheap）**。q9cq は「本コースを 2/4 次元まで honest に進める」安価な B 前進。

---

## 6. 3 文結論

1. **今ラウンド深掘りできる real content は "rank ≥ 2 下界"（部分・full ではない）**——一様化子クラス [λ] の非立方性（付値 3∤1・新規）と [λ],[ζ₃] の 𝔽₃-独立性（⟨[ζ₃]⟩→⟨[λ],[ζ₃]⟩≅(ℤ/3)²）で、非立方の核は q9ci_no_cbrt_zeta/zetaSq を消費し、真水は付値方向＋独立性の組み立てに限られる。
2. **モジュール `Q3CubeQuotientReal.lean`（q9cq・tier M/opus・~200 行）・予測 B6 0.15→0.20・Σ_B 26→27（+1 表示前進）**——full rank 4（(ℤ/3)⁴）は定理化せず named target 註記に留め、rank≥2 下界のみ honest に建てる。
3. **最大リスクは主単数 2 次元の重さ**——残り 2 次元（1+m≅ℤ₃²）と上界 exhaustion は v_M・主単数フィルトレーション・graded 判別器（B2 監査 §1.3／q3rq 限定 4 が flag した未建設機構）を要する 2〜3 ラウンド案件で、0.25 への bump（full rank 主張）は過大主張ゆえ回避する（q9kd との二重計上リスクは低い＝q9kd に付値方向・独立性は不在）。

---

*読んだ .lean 本体*: `IUT/Q3KummerDualityReal.lean`（q9kd 全体・`q9kd_class_nontrivial` L340-350・`q9kd_kummer_iso` L551-556・正直限定 2 L39・capstone L560-591）、`IUT/Q3RamifiedQuadratic.lean`（q3rq 全体・`q3rqLx`=prodGrp intGrp q3rqU L505・`q3rqU` L488・`q3rqZeta`/`q3rq_zeta_unit` L534/607・`q3rq_zeta_cube` L614・`q3rq_zeta_sq_ne_one` L650・`q3rqLambda`/`q3rq_lambda_sq` L726/732・`q3rq_zeta_norm`=N(ζ₃)=1 L593・正直限定 4 L42-43）、`IUT/Q3KummerCubeIdent.lean`（`q9ci_no_cbrt_zeta` L628-658・`q9ci_no_cbrt_zetaSq` L661-688・第2座標 mod 3 論法・q3mc_cube_snd 消費）、`IUT/FundamentalGroup.lean`（`intGrp`=（ℤ,+）L283-290・`prodGrp` 成分演算 L444-457）、`IUT/Q3KummerCubic.lean`（q3k ヘッダ L1-53・O_M=L₂[Y]/(Y³−ζ₃)）、`IUT/Q3KummerDescentSpike.lean`／`IUT/Q3KummerPiSplit.lean`（ヘッダ・層の別確認）、`IUT/KummerExact.lean`／`IUT/KummerTheory.lean`（ヘッダ・抽象体 K^×/(K^×)ⁿ で主語別＝二重計上なし確認）。参照監査: `audit/pillar-B2-reciprocity-normgroup-scope-2026-07-11.md`（§1.2-1.3 単数判別器不在）、`audit/reaudit-q9kd-kummer-b6-2026-07-11.md`。graph-meta.json 柱B complete_note（Σ_B=26.5→26 の内訳）。
