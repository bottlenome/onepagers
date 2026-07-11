# A9「Belyi 化 / 遠アーベル幾何入力（実）」詳細化ラウンド（設計のみ・実装なし）2026-07-11

対象: `target_ledger.json` 柱A **A9「Belyi 化 / 遠アーベル幾何入力(実)」weight 10・status 0**（柱A 最後の status-0 項目）。
本ドキュメントは設計文書のみ（Lean 実装なし）。敵対的既定＝模型。判定は既存モジュールの def/theorem **本体**による。

**結論先出し**: A9 には **tractable な実の第一歩が存在する**——実 ℚ[X]（`polyCRing ratRing`）上の
**実 Belyi 多項式 f(X) = 3X² − 2X³** の分岐軌跡が **{0, 1, ∞} にちょうど一致**することの完全証明
（任意の零因子なし拡大環にわたる幾何的主張・choice-free）。必要部品（実 ℚ・実 ℚ[X]・形式微分・
一次因子ライプニッツ・重根判定・打ち切り評価準同型）は**全て既にリポジトリに実在**し、新イディオムの
発明は不要（tier M = opus 1 枠で実装可能）。ブロックではない。ただし §4 の正直な線引き
（Belyi の**定理**ではない・cuspidalization ではない・スキームでない）を厳守し、見込みは 0→**0.1** に留める。

---

## §1 A9 の定義と現状

### 1.1 実 Cor 3.12 における A9 の役割（望月の使い方）

A9 = 「Belyi 化 / 遠アーベル幾何入力」は IUT 本体への 2 系統の入力を指す:

1. **Belyi 化（[GenEll] §2・IUT IV Thm 1.10 周辺)**: 任意の代数曲線を tripod
   **P¹ ∖ {0,1,∞}** に有限被覆で結びつける Belyi 写像（とその **noncritical** 変種）。
   IUT IV での高さ計算・compactly bounded subset の制御、および一般 ABC/Vojta を
   初期 Θ-データの once-punctured 楕円曲線ケースへ還元する装置。
2. **遠アーベル幾何入力（[AbsTopII] §3 Belyi cuspidalization・[AbsTopIII])**:
   strictly Belyi type の双曲的（軌道）曲線に対し、π₁ から任意有限個の点を抜いた
   開部分曲線の π₁ を群論的に再構成する **Belyi cuspidalization**。これが
   mono-anabelian 数体復元（AbsTopIII）の要であり、初期 Θ-データの曲線
   （once-punctured 楕円曲線とその軌道曲線）が strictly Belyi type であることが
   IUT I §1 の前提に入る。

すなわち A9 の主語は「**分岐が {0,1,∞} に集中する実の有限写像とその周辺幾何**」であり、
tripod がその基底対象である。

### 1.2 現状（status 0 の確認）

- `grep -rniE "belyi|tripod|dessin|noncritical" IUT/*.lean` → **0 件**（実装ヒットなし）。
  P¹（射影直線）そのものも、3 点分岐構造も、リポジトリのどこにも存在しない。
- `target_ledger.json`: A9 weight 10・status 0。`graph-meta.json` 柱A complete_note でも
  A9 への言及は「A9=0」のみ（要求内容の追加規定なし）。
- 既存の遠アーベル系資産（§2(b) で詳述）は全て A6/A7/A3/A4 に計上済みで、
  Belyi/三点分岐の主語を持つものは皆無。

### 1.3 status 0→0.1 の「実の第一歩」が満たすべき条件（AUDIT_RUBRIC 適合）

1. **主対象が本物**: 実際の体（実 ℚ = `ratRing`）上の実際の多項式環の実元と、
   その写像としての分岐挙動。Nat/Bool/Fin/有限列挙の身代わりでないこと。
2. **A9 固有の主語**: 「分岐 ⊆ {0,1,∞} の有限写像」という Belyi 固有の内容。
   A4/A5/A6/A7 の再輸出・再ラベルでないこと（§4.2）。
3. **幾何的主張**: ℚ-有理点だけの偶然でなく、任意の（零因子なし）拡大環にわたる
   分岐軌跡の決定であること（分岐は幾何的概念）。
4. **正直な限定**: Belyi の定理（すべての曲線/ℚ̄ が Belyi 写像を持つ）・noncritical
   Belyi・cuspidalization は主張しない。

---

## §2 候補評価（4 候補・正直査定）

### 候補 (a) 実 Belyi 写像の具体第一例: f(X) = 3X² − 2X³ — **採用（tractable・実建設(b)型）**

**内容**: 次数 3 の実多項式 f(X) = 3X² − 2X³ ∈ ℚ[X] は、P¹ → P¹ の写像として
**ちょうど {0, 1, ∞} の 3 点で分岐**する古典的 Belyi 写像の最小非自明例
（dessin = 辺 2 本のパス）。数学的事実:

- f′(X) = 6X(1−X)、臨界点は X = 0, 1（と ∞）。臨界値 f(0)=0・f(1)=1・f(∞)=∞。
- ファイバー分解（実の二重根の顕示）:
  - y=0: f = X²·(3−2X) — 0 が二重根、
  - y=1: f − 1 = (X−1)²·(−2X−1) — 1 が二重根
    （検算: (X²−2X+1)(−2X−1) = −2X³+3X²−1 ✓）、
  - y=∞: 次数 3 の多項式ゆえ ∞ で全分岐 e_∞=3（チャート恒等式 f(1/u)·u³ = 3u−2、
    u=0 で右辺 −2 ≠ 0 = 3 位の零点の顕示）。
- **分岐軌跡の上界（幾何的主定理）**: 零因子なし・6·1≠0 の任意の可換環 E において、
  f − y が E 上の一次因子の二乗 (X−a)² を（多項式証人つきで）因子に持つなら
  y = 0 ∨ y = 1。証明は f−y = (X−a)²·g を一次因子ライプニッツで微分して
  Df(a) = 0、Df = 6X−6X² から 6a(1−a) = 0、零因子なしで a ∈ {0,1}、
  評価準同型で y = f(a) ∈ {0,1}。**choice-free・完全証明可能**。

**リポジトリの必要部品は全て実在**（本ラウンドで本体確認済み）:

| 部品 | 実在箇所 | 本体確認 |
|---|---|---|
| 実 ℚ (`ratRing`)・体データ | `IUT/Rationals.lean` (M115F) | Int 対の商・消去補題 |
| 実 ℚ[X] = `polyCRing ratRing`・`psSingle`/`psC`/`psAdd`/`psMul` | `IUT/SimpleExtension.lean`・`IUT/PowerSeries.lean`・`IUT/FrobeniusCharP.lean` | 係数列 PS・Cauchy 積 |
| 形式微分 `formalDeriv`＋線形性＋単項式則 | `IUT/SeparablePoly.lean` (M270F) 139–216 行 | 一般 CRing 上 |
| 一次因子ライプニッツ `formalDeriv_mul_linFactor` D(f·(X−a)) = Df·(X−a)+f | 同 327 行 | 完全証明済み |
| 重根判定 `sep_repeated_factor` (X−a)²∣f ⟹ (X−a)∣f ∧ (X−a)∣Df | 同 358 行 | 完全証明済み |
| 打ち切り評価準同型 `evalSum`/`evalHomId`/`evalHom_add`/`evalHom_id_mul`/`evalHom_stable` | `IUT/EvaluationHom.lean` (M274F) | 一般 CRing・上界つき積評価 |
| 有界性述語 `IsPolyBounded` | `IUT/PolyWeierstrass.lean` 46 行 | |
| ℚ の零因子なし `ratIUTField.eq_zero_of_mul_eq_zero_left` | `IUT/Field.lean` (M264F) 97/151 行 | 本物の IUTField ℚ |
| 自然数倍 `rnsmul`＋積法則 | `IUT/SeparablePoly.lean` 72–137 行 | 係数 3·1, 6·1 用 |
| 評価イディオムの先行実例 | `IUT/CbrtLinearFactor.lean`（evalSum で f=w·g を評価する同型パターン） | 写経元 |

**注意点（設計で回避済みの罠）**: `psDvd` は級数レベルの整除であり、a ≠ 0 のとき
X−a は R[[X]] の**単元**（−a(1−X/a)）なので psDvd 単独の重根仮定は空虚になり得る。
よって主定理の重根仮定は**有界（多項式）証人つき**の分解
`f − y = (X−a)²·g, IsPolyBounded g 2` で立てる。また `sep_repeated_factor` の出力
（psDvd の非有界証人）は評価に使えないため、証明は `formalDeriv_mul_linFactor` を
分解に直接 2 回当てて**有界因子の和・積**の形で Df を書き、`evalHom_id_mul`/`evalHom_add`
で評価する（CbrtLinearFactor の確立イディオム）。新規に要る補助補題は
「`formalDeriv` は有界性を保つ」「rnsmul の合成 m·(n·x)=(mn)·x」程度の小物のみ。

**判定: 実建設(b)型・tractable・新イディオム不要（tier M）**。Lean スケッチは §3。

### 候補 (a′) λ-line → j-line の次数 6 Belyi 写像（楕円曲線接続） — 実だが第一歩には重い

j(λ) = 256(λ²−λ+1)³ / (λ²(λ−1)²) は {0,1,∞}（正規化後）にのみ分岐する次数 6 の
Belyi 写像で、A8 の Tate 曲線（j(E_q) = 1/q + 744 + …）へ**本物の橋**を架け得る唯一の
候補。しかしリポジトリに**有理関数体 ℚ(X)（分数体）が無く**、分子分母の次数 6 の
resultant/判別式計算も (a) の 3 倍以上重い。**第一歩でなく A9 の名指し後続ターゲット**
として §3 の実装計画に「次段」として記載する。

### 候補 (b) 既存 A6/A7 復元の A9 再主語化 — **不採用（二重計上）**

A6 `CyclotomeRecoveryReal`（crr: mono-anabelian シクロトーム復元・0.55 計上済み）と
A7 `cra`（Gal ≅ Aut(μ_{3^ℓ})・0.4 計上済み）は確かに「遠アーベル入力」の語感を持つが、
これらを A9 の主語として再登録するのは AUDIT_RUBRIC「代理/橋 = 既存定理の再輸出…
算入しない」に正面から抵触する再ラベルであり、監査は却下する。A9 の固有主語は
Belyi/三点分岐/cuspidalization であって、円分剛性の再消費ではない。**却下**。

### 候補 (c) ℤ/n デッキ商上の dessin（置換対）構造 — **不採用（現状では模型判定）**

dessin d'enfant は置換対 (σ₀, σ₁)（推移的作用）という忠実な組合せ圏を持つため
本質的に toy ではないが、**実 Belyi 写像のモノドロミーとの対応を証明しない限り**、
単独の置換対モジュールは敵対的既定で「Fin 上の置換の身代わり＝模型」と判定される
（対応の証明には ℚ̄/ℂ 上の被覆理論＝Riemann existence が要り、core Lean では遠い）。
(a) 実装**後**に「(a) の実ファイバー（三次拡大体 ℚ[X]/(2X³−3X²+y) の実根）上の実
モノドロミー」として実化する道はあるが、第一歩ではない。**却下（後続候補として保留）**。

### 候補 (d) 実 π₁^ét (A4) から E_q の実不変量（v(q) 等）の復元 — **ブロック（前提部品が未建設）**

「π₁ ↦ 曲線の不変量」という復元方向は遠アーベル入力として本物だが、本体確認の結果
**現在の実 π₁ 対象からは v(q) が原理的に読めない**:

- A5b `Q3TemperedPi1.lean` の実 tempered π₁ は **分裂直積 q3tpGroup = tmzLimit × intGrp**
  （ヘッダ・本体とも確認）。拡大類が自明なので群構造は q に依存せず、全ての q で同型。
- A4 `Q3TatePi1Etale.lean` の実 π₁^ét は格子方向 pro-l 切片 ℤ_l のみ（正直な限定(3)で
  μ 方向・Weil ペアリングを意図的に不構成と明記）。v(q) は格子方向と μ 方向を結ぶ
  **テータ交換子ペアリング（拡大類）**に宿るため、切片単独からは復元不能。
- 実 Heisenberg 群は `TemperedThetaCommutator.lean` (M384F) に実在するが、それを
  **E_q の punctured 曲線の実 π₁^temp の拡大類として同定**する仕事（v(q) が交換子に
  現れる本物の非可換化）は A5 の非可換化＋柱E mono-theta の本丸であり未建設。

**必要な重前提を名指し**: 「ẑ(1)×ẑ 二成分実 π₁＋実 Weil/テータペアリング」（A5/柱E）。
それが立つまで (d) は着手不能。**ブロックと明記**（A9 でなく A5/E の後続でもある）。

### 候補まとめ

| 候補 | 型 | 判定 |
|---|---|---|
| (a) 実 Belyi 多項式 3X²−2X³ の分岐軌跡 = {0,1,∞} | 実建設(b) | **採用**（部品全て実在・tier M） |
| (a′) λ→j 次数 6・Tate 曲線接続 | 実建設(b) | 後続（分数体が未建設） |
| (b) A6/A7 の再主語化 | 再輸出 | 却下（二重計上） |
| (c) 置換対 dessin 単独 | 模型リスク | 却下（(a) 後の実モノドロミー化のみ可） |
| (d) π₁ ↦ v(q) 復元 | ブロック | 拡大類（A5 非可換化＋柱E）待ち |

---

## §3 結論: 採用する実の第一歩と Lean スケッチ

**採用**: 候補 (a)。**新規ファイル 1 個 `IUT/BelyiCubicReal.lean`・prefix `blc`・tier M (opus)**・
推定 500–700 行・choice-free（新規 Classical.choice なし・sorry なし・#print axioms は
propext/Quot.sound のみを目標）。

imports: `IUT.SeparablePoly`・`IUT.EvaluationHom`・`IUT.Field`・`IUT.PolyWeierstrass`
（＋推移で `IUT.Rationals`/`IUT.SimpleExtension`/`IUT.PowerSeries`）。

### blc-0 一般環上の整数係数と小補題
- `blcThree (E : CRing) := rnsmul E 3 E.one`、同様に `blcTwo`・`blcSix`。
- 新小補題: `blc_rnsmul_rnsmul : rnsmul E m (rnsmul E n x) = rnsmul E (m*n) x`、
  `blc_deriv_bounded : IsPolyBounded E f (N+1) → IsPolyBounded E (formalDeriv E f) N`。

### blc-1 実 Belyi 多項式（一般 CRing E 上・ℚ で具体化）
```
def blcF (E : CRing) : PS E :=
  psAdd E (psSingle E (blcThree E) 2) (psSingle E (E.neg (blcTwo E)) 3)
```
- 係数補題 `blcF_coeff0/1/2/3`（0,0,3·1,−2·1）・`blcF_bound : IsPolyBounded E (blcF E) 4`
  （CubicPolyQ の cbpF3 イディオムの写経）。

### blc-2 導関数の実因子分解（臨界点 = {0,1} の顕示）
```
theorem blc_deriv_eq (E) : formalDeriv E (blcF E)
  = psAdd E (psSingle E (blcSix E) 1) (psSingle E (E.neg (blcSix E)) 2)   -- 6X − 6X²
theorem blc_deriv_factor (E) : formalDeriv E (blcF E)
  = psMul E (psSingle E (blcSix E) 1) (psAdd E (psOne E) (psNeg E (psX E)))  -- 6X·(1−X)
```
係数 funext（formalDeriv_psSingle_succ ＋ Cauchy 積の有限計算）。

### blc-3 分岐ファイバーの実二重根（{0,1} が実際に分岐**する**こと・下界側）
```
theorem blc_fiber_zero (E) : blcF E
  = psMul E (psMul E (psX E) (psX E))
      (psAdd E (psC E (blcThree E)) (psSingle E (E.neg (blcTwo E)) 1))      -- X²(3−2X)
theorem blc_fiber_one (E) : psAdd E (blcF E) (psC E (E.neg E.one))
  = psMul E (psMul E (psLinFactor E E.one) (psLinFactor E E.one))
      (psNeg E (psAdd E (psSingle E (blcTwo E) 1) (psOne E)))               -- (X−1)²·(−(2X+1))
```
いずれも係数 funext の有限計算（検算済み: (X²−2X+1)(−2X−1) = −2X³+3X²−1）。

### blc-4 ★主定理: 分岐軌跡の上界（幾何的・任意の零因子なし拡大で）
```
theorem blc_branch_locus (E : CRing)
    (hdom : ∀ x y : E.carrier, E.mul x y = E.zero → x = E.zero ∨ y = E.zero)
    (h6 : blcSix E ≠ E.zero)
    (y a : E.carrier) (g : PS E) (hg : IsPolyBounded E g 2)
    (hfac : psAdd E (blcF E) (psC E (E.neg y))
              = psMul E (psMul E (psLinFactor E a) (psLinFactor E a)) g) :
    y = E.zero ∨ y = E.one
```
証明計画（全 choice-free・確立イディオムのみ）:
1. hfac を mul_comm/assoc で ((X−a)·g)·(X−a) 型に並べ替え、`formalDeriv_mul_linFactor`
   を 2 回当てて D(f−y) を**有界因子の psAdd/psMul 式**として陽に書く
   （psDvd の非有界証人は使わない——§2(a) の罠回避）。
2. `formalDeriv_add`/`formalDeriv_psC` で D(f−y) = Df。
3. 打ち切り評価: `evalSum (evalHomId E) a` を `evalHom_add`/`evalHom_id_mul`/`evalHom_stable`
   で分配（各因子の IsPolyBounded は hg・blc_deriv_bounded・psLinFactor の bound 2 から）。
   eval(X−a)(a) = 0 の小補題 `blc_eval_linFactor` を先に立てる。⟹ Df(a) = 0。
4. blc-2 の係数から Df(a) = (6·1)·a − (6·1)·a² = (6·1)·(a·(1−a))（rnsmul_mul_right・分配）。
   hdom＋h6 ⟹ a = 0 ∨ a = 1。
5. hfac 自体を a で評価（同じイディオム）: f(a) − y = 0·0·g(a) = 0 ⟹ y = f(a)。
   a=0 ⟹ y = 0、a=1 ⟹ y = 3·1 − 2·1 = 1（環演算の有限計算）。∎

### blc-5 実 ℚ での具体化＋ P¹ 点集合と ∞
```
theorem blc_branch_locus_rat :  -- E := ratRing、hdom := ratIUTField 経由、h6 := Int 代表 omega
    ∀ y a g, … → y = ratRing.zero ∨ y = ratRing.one
def blcP1 (E : CRing) : Type := Option E.carrier          -- P¹ の点集合（none = ∞）
def blcMap (E : CRing) : blcP1 E → blcP1 E               -- some x ↦ some f(x)・∞ ↦ ∞
theorem blc_map_infty_fiber : blcMap E x = none ↔ x = none  -- ∞ ファイバー = {∞}
theorem blc_eval_fun : evalSum (evalHomId E) x (blcF E) 4 = (3x²−2x³ の環式)  -- 多項式↔写像の橋
theorem blc_infty_chart :  -- 実 ℚ 上・ratIUTField の inv を使用: e_∞ = 3 の正直な顕示
    ∀ u ≠ 0, ratRing.mul (blcFun (ratField-inv u)) (u³) = 3u − 2
theorem blc_infty_unit : (3·0 − 2 : ratRing.carrier) ≠ ratRing.zero
```

### blc-6 見出し束ね
```
structure BelyiCubicData where  -- 実基底体・実多項式・分岐値 {0,1,∞}: 上界(blc-4)＋下界(blc-3)＋∞(blc-5)
def blcData : BelyiCubicData    -- E = ratRing の実証人
theorem blc_belyi_exists : Nonempty BelyiCubicData
```

**定理名の確定リスト**（監査向け load-bearing）: `blcF`・`blc_deriv_factor`・`blc_fiber_zero`・
`blc_fiber_one`・`blc_branch_locus`（★）・`blc_branch_locus_rat`・`blc_infty_chart`・`blcData`。

**なぜ次数 2 の 4X(1−X) でなく次数 3 か**: 4X(1−X) は分岐 {1,∞} の 2 点のみで tripod の
三点性を顕示しない。3X²−2X³ は {0,1,∞} **全部**で分岐する最小例であり、A9 の主語
「三点分岐」の忠実な最小部分ケース（CLAUDE.md §3「本コースを 3% 進む」）。

---

## §4 正直な線引き（過大主張の禁止・二重計上の排除）

### 4.1 本ステップが実にする**もの**
- 実 ℚ（と任意の零因子なし拡大環）上の、実多項式写像 1 本の**分岐軌跡の完全決定**
  （上界 blc-4＋下界 blc-3＋∞ blc-5）。リポジトリ初の Belyi 型対象。

### 4.2 実にしない**もの**（ヘッダに明記・消去/弱化禁止）
1. **Belyi の定理ではない**: 「ℚ̄ 上の全ての曲線が {0,1,∞} 分岐写像を持つ」は一切
   主張しない。1 本の具体例のみ。
2. **noncritical Belyi（[GenEll]・IUT IV）ではない**: 高さ・compactly bounded subset の
   制御は範囲外。
3. **Belyi cuspidalization（[AbsTopII]）ではない**: tripod の実 π₁・punctured 曲線の
   π₁ 再構成はゼロのまま（候補 (d) のブロックと同根）。
4. **スキームでない**: P¹ は点集合 Option K（リポジトリ恒久限定「K-点・スキーム/
   エタールサイト皆無」の継承・A8 の E_q(ℚ₃) と同じ流儀）。e_∞=3 はチャート恒等式
   での顕示であり局所環の付値ではない。
5. **重根仮定は多項式証人つき分解**（psDvd 級数整除は a≠0 で空虚になるため使わない
   ——これは弱化でなく、幾何的に正しい定式化の選択）。
6. **ℚ̄ 上の分岐点の存在列挙はしない**: blc-4 は「二重根があれば y∈{0,1}」の上界、
   blc-3 は「y=0,1 には実際に二重根がある」の下界で、対で「分岐値集合 = {0,1,∞}」を
   構成的に閉じるが、一般ファイバーの根の個数（分離閉包での 3 点）は数えない。
7. **A8 Tate 曲線との接続なし**: λ→j 次数 6 写像（候補 a′）は後続。E_q はここに登場しない。

### 4.3 二重計上リスクの明示（監査向け）
- **A1/A2 再消費でない**: ratRing・polyCRing は**消費**するだけで、本モジュールの主語は
  多項式環の一般論でなく「三点分岐写像」——A1 の主語（数体の構成）と交わらない。
- **M270F/M274F 再輸出でない**: sep-機構・評価機構は補題として使うが、blcF・分岐軌跡
  定理・チャート恒等式は全て新規の実内容。値一致の再確認だけの定理は置かない。
- **A4/A5/A6/A7 と主語素 disjoint**: π₁・デッキ群・円分体・Gal は本モジュールに一切
  登場しない（grep で Belyi 側 0 件・逆方向も 0 件を実装後に確認可能）。
- 逆に **A9 側も 0.1 のみ**を主張: 上記 4.2 の 1–4 が残る限り、A9 の IUT-facing 定理は
  未着手であり、0.1（主語クラスの実第一対象＋その完全分岐計算）を超えない。

---

## §5 status 見込み・柱A% 算術

`target_ledger.json` 現況（本ラウンドで再計算・検証済み）:

| 項目 | weight | status | 寄与 |
|---|---|---|---|
| A1 | 8 | 0.85 | 6.80 |
| A2 | 8 | 0.65 | 5.20 |
| A3 | 12 | 0.75 | 9.00 |
| A4 | 14 | 0.55 | 7.70 |
| A5 | 10 | 0.15 | 1.50 |
| A6 | 14 | 0.55 | 7.70 |
| A7 | 12 | 0.40 | 4.80 |
| A8 | 12 | 0.57 | 6.84 |
| A9 | 10 | **0** | 0 |
| **Σ_A** | 100 | | **49.54** → 表示 round(49.54) = **50** ✓（現表示と一致） |

**A9 0→0.1 のとき**: Σ_A = 49.54 + 10×0.1 = **50.54** → Python banker's round(50.54) = **51** ✓
（タイ 50.5 は round(50.5)=50 に落ちるが、50.54 はタイでなく余裕 +0.04。ただし監査が
0.05 に値切れば Σ_A = 50.04 → 表示 50 のまま——**表示が動くかは監査次第**であり、
0.1 は見込みに過ぎない。本ドキュメントは 0.1 を**主張**するが決めるのは独立監査と
ユーザーの baseline 署名である）。

0.1 の根拠（相場感）: A5 の 0.1（実デッキ作用の第一実例）・A8 の初期加点と同じ
「主語クラスの最初の非自明実対象＋その完全証明 1 本」の帯。0.15 以上を主張しない
（cuspidalization・noncritical・曲線接続が全て未達のため）。

---

## §6 実装計画（親向け）

- **tier/model**: **M = opus 1 枠**（確立イディオムの新インスタンス: CubicPolyQ の係数
  イディオム＋SeparablePoly のライプニッツ＋CbrtLinearFactor の evalSum イディオムの写経
  合成）。新イディオム発明なし・fable 不要。詰まったら親（fable）が blc-4 の評価分配
  だけスポット介入。
- **新規ファイル**: `IUT/BelyiCubicReal.lean` のみ（サブエージェントは共有ファイル不更新）。
- **推定規模**: 500–700 行（CubicPolyQ 221 行＋SeparablePoly 級の funext 計算×3 本＋評価 2 本）。
- **ヘッダ必須事項**: 分類 [実／本物の先行建設(b)]・complete_pct 影響（A9 0→0.1 見込み・
  独立監査確定が条件）・§4.2 の正直な限定 1–7 を全文掲載。
- **親の統合時共有ファイル更新**: `IUT.lean` import 追加・`tools/gen_graph.py` PILLAR に
  `BelyiCubicReal: "A"` 追記・`graph.json` 再生成・`dashboard.md`/`graph-meta.json`
  （complete_note 追記・pillars.A complete_pct は監査後）・`target_ledger.json` A9 status
  は**独立再監査（AUDIT_RUBRIC・敵対的）通過後のみ**更新。
- **独立再監査の依頼文に含めるべき点**: (i) 主語が Fin/Nat 身代わりでないこと（blcF は
  polyCRing ratRing の実元・blc-4 は任意零因子なし CRing にわたる幾何的主張）、
  (ii) A1/M270F/M274F の再輸出でないこと（§4.3）、(iii) psDvd 空虚性の罠を回避した
  定式化であること。
- **後続の名指しターゲット（A9 0.1→先）**: ①分数体 ℚ(X) の実建設 → λ→j 次数 6 Belyi
  写像（候補 a′・A8 E_q と接続）、②blc の実ファイバー体 ℚ[X]/(2X³−3X²+y) 上の実
  モノドロミー（候補 c の実化）、③（遠い）tripod の実 π₁ と cuspidalization（候補 d の
  前提でもある A5 非可換化＋柱E の後）。

## 主リスク

1. **監査の値切り**: blc-4 を「多項式の重根計算＝A1 圏」と分類し A9 0.05 に留める可能性
   （そのとき Σ_A = 50.04 → 表示 50 のまま）。反論材料: 主語は「{0,1,∞} 三点分岐の顕示」
   というリポジトリに存在しなかった A9 固有クラスであり、blc-3/blc-5 の下界・∞ 側と対で
   「分岐値集合の決定」という幾何の定理になっている点。
2. **blc-4 の評価分配の手間**: 有界因子 4 つの psAdd/psMul 混在式の evalSum 分配は
   行数が嵩む（CbrtLinearFactor 比 2–3 倍）。opus が詰まったら親がスポット。
3. **表示 51 はタイ余裕 +0.04 のみ**: A9=0.1 きっかりなら 51 だが、他項目の同時減点が
   1 件でもあれば 50 に戻る薄氷。報告では「表示は監査確定後」と明記する。
