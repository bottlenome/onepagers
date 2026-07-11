# A5 非可換 tempered π₁ 拡大類詳細化ラウンド — 実テータ群による代理昇格・v(q) 可視化（2026-07-11）

**種別**: 詳細化ラウンド（設計ドキュメントのみ・Lean 実装なし）
**対象**: 柱A A5「実 tempered π₁^temp」（w10・status **0.15**）
**土台**: 本日監査確定の実 Mumford テータ群 `IUT/Q3ThetaGroup.lean`（q3th・A8=0.65 計上済み）
**先行設計**: `audit/A5-real-tempered-pi1-detail-2026-07-10.md`（分裂直積ブロッカーの特定）・
`audit/theta-heisenberg-real-cover-detail-2026-07-11.md`（比較準同型を A5 後続として明示 defer）
**中心課題**: A5b の実 tempered π₁ は**分裂直積** `q3tpGroup = tmzLimit × intGrp` で、
q が群構造に不可視・v(q) 復元不能・拡大類自明。q3th が実 data として供給した
交換子＝実 Weil ペアリングを使い、**非可換 tempered 拡大類を A5 の主語で実現する**最小の
実ステップを、A8（テータ群本体）の二重計上を厳密に排除して切り出す。

---

## 0. 結論サマリ

| 項目 | 内容 |
|---|---|
| 判定 | **実ステップは tractable**。§2 候補 (b)（代理 tempered π₁ → 実テータ群への比較準同型）が本体。(a)（テータ群自身の拡大列の relabel）単独と (c)（g_τ 側からの v(q) 読み出し）単独は **A8 の再計上**であり不採用——(a)(c) は (b) を通した系としてのみ A5 の内容になる |
| 選定ステップ | **A5d**: 実比較準同型 **Φ : thetaGrp(ℤ³ Heisenberg・M384F/M11) → q3thM** と **Ψ : tpeGroup(=thetaGrp⋊ℤ・M424F) → q3thM**（像⊆q3thGrp）。抽象シンプレクティック形式 ω=ab′−a′b が**実 Weil ペアリング (−1)^ω ∈ 実 μ₂⊂ℤ₃^×**に等しくなり、deck 切断が実半周期 3ⁿ に乗り、**deck×テータ交換子が実 −1≠1**（分裂直積ブロッカーの discharge）、**v(q)=2 が tempered 側 data（deck 切断像の平方）から復元**される |
| 新規ファイル | `IUT/Q3TemperedThetaClass.lean`（prefix `q3nt`・1 本・約 550–700 行） |
| tier | **M（opus）**。HELP スポット 1 箇所（一般 braiding 補題 xᵃyᵇ=z^{ab}yᵇxᵃ の Int 二重帰納）のみ fable 候補 |
| 二重計上境界 | q3th の内部定理は**消費のみ**（再証明ゼロ・q3th ファイル不変更）。A5 に計上する新規内容は「代理 tempered π₁（A5/M384F/M424F 計上済みの骨格）の主張が実値になる」定理群——主語は Φ/Ψ と tempered 側対象であり、テータ群の交換子の relabel ではない（§2.4 で厳密化） |
| A5 status 見込み | 0.15 → **0.25**（設計見込み）・敵対的下限 **0.20**。表示: 0.25 なら柱A **52→53**・0.20 なら **52 据え置き**（§5） |
| 最大リスク | 監査が本モジュールを rubric「代理/橋（値一致確認）」に分類する可能性（§5.4）。対策: 実値等式（実 μ₂ 値・実半周期・v(q)=2）と正直核（ker Ψ の level-2 崩壊の定理化）を旗艦に置き、「比較」でなく「実現（実表現）」として構成する |

---

## 1. 現状実測 — A5 資産＋テータ資産の実／代理判定（本体精読）

### 1.1 資産表（def/theorem 本体で判定・敵対的既定=模型）

| モジュール | 帰属 | 本体実測 | 実／代理 |
|---|---|---|---|
| `Q3TateDeck.lean`（q3td・A5a） | A5 計上済 | 実周期準同型 t↦qᵗ（単射・像=ker(q3tProj)）・自由推移デッキ・M333F 外部仮説の実 discharge | **実**（アーベル・離散商のみ） |
| `Q3TemperedPi1.lean`（q3tp・A5b） | A5 計上済 | `q3tpGroup = prodGrp tmzLimit intGrp`。完全列 1→ℤ₃(1)→π₁^{(3)}→ℤ→1・実 Gal 作用（profinite 側 χ 冪・deck 固定）・無条件存在 | **実・しかし分裂直積**（§1.2） |
| `Q3TateCoverTower.lean`（q3tc・A5c） | A5 計上済 | 実中間被覆 E_{qⁿ}→E_q・有限デッキ ℤ/n・実被覆塔 | **実**（アーベル） |
| `Q3TatePi1Etale.lean`（q3pe・A4） | A4 計上済 | pro-l 逆極限の実塔作用・忠実性 | 実（A4 側・可換） |
| `EtaleTheta.lean`（M11）＋`TemperedThetaCommutator.lean`（M384F） | A5 骨格 | 離散 Heisenberg `thetaGrp`（台 ℤ³・積 (a,b,c)(a′,b′,c′)=(a+a′,b+b′,c+c′+ab′)）・`theta_comm`: [g,h]=(0,0,ab′−a′b)・¬tcmAbelian・μ_l 像（抽象 ζ パラメータ） | **代理**（主語 ℤ³・ヘッダ自認「tempered 被覆の商としての実現は外部」M384F:29-31） |
| `TemperedPi1Etale.lean`（M424F） | A5 骨格 | `tpeGroup = thetaGrp ⋊_α ℤ`（非可換分裂拡大・`tpe_deck_theta_commutator`: [s(n),ι(a,b,c)]=ι(0,0,n·b)・非 slim 定理化・α_n=内部 (n,0,0) 共役 `tpe_aut_conj_in_theta`） | **代理**（自認「Tate 曲線の実被覆空間としての実現…は外部/後続」:51-52） |
| `ArithTemperedPi1.lean`（M429F） | A5 骨格 | `atpGroup = tpeGroup ⋊_χ ℤ`・χ 捻り atpTw が真の自己同型 | **代理**（算術商 ℤ 模型を自認） |
| `Q3ThetaGroup.lean`（q3th・**A8 計上済 0.65**） | A8 | 実単項式束群 q3thM（台 (ℚ₃^××ℤ)×ℚ₃^×）・テータ群 q3thGrp=C_M(g_τ)（qᵃw²=1）・**交換子＝実 Weil ペアリング** `q3th_comm_eq_weil`（値 e([3],[−1])=(0,q3tNegOne)=実 −1∈μ₂⊂ℤ₃^×・`q3th_nonabelian`）・中心核 `q3th_ker_central`/スカラー q^{−n²} `q3th_ker_scalar`・**g_τⁿ=(q^{−n²},−2n,qⁿ)** `q3th_tau_pow` | **実**（A8 で計上済み。**ℤ³ 代理への比較準同型は意図的に未構築**——ヘッダ §4-6「A5/A7 後続の仕事として意図的に残す」・A8 再監査 D5 で「relabel なし」の根拠にもなった空白） |

### 1.2 A5b 分裂直積ブロッカーの精密化（本体からの実測）

`q3tpGroup` の定義は `prodGrp tmzLimit intGrp` ——**m（したがって q=3^m）を一切パラメータに
取らない定数**である。すなわち:

1. **q の群構造不可視**: q=3 の tempered π₁ と q=9 の tempered π₁ が**同一の群**。q は群の外の
   付属 field `deck_realize`（(z,n)↦qⁿ）としてのみ登場し、群論的 data から v(q) は復元不能。
2. **拡大類 ≡ 0**: 完全列 1→ℤ₃(1)→π₁^{(3)}→ℤ→1 は直積ゆえ分裂・中心的・可換。deck 切断は
   μ 部分と可換（one_mul/mul_one だけで証明できる程度に自明）。
3. **非可換性 0**: compact E_q の tempered π₁ は実際に可換（≅ ẑ(1)×ℤ）なので A5b 自体は正直。
   IUT が要る非可換性（[EtTh] のテータ交換子＝拡大類）は **punctured 曲線**の tempered π₁ に
   宿り、A5b 正直限定 (2) が「範囲外（tpeGroup/atpGroup の実化）」と明示 defer した。

q3th が新たに供給した実 data はまさにその欠落部品である: 実非可換交換子（実 μ₂ 値）・
実中心核（ℚ₃^××q^ℤ・q^{t²} スカラー）・実降下元 g_τⁿ=(q^{−n²},−2n,qⁿ)（v(q) 指数の実担体）。
**未接続なのは「代理 tempered π₁ ↔ 実テータ群」の準同型 1 本**——q3th 設計・A8 監査の双方が
名指しで A5 に残した空白そのものである。

---

## 2. 中心判定 — tempered π₁ を非可換にする／v(q) を復元する最小の実新規内容

### 2.1 候補 (a): テータ群自身の中心拡大 1→ℚ₃^××q^ℤ→q3thGrp→E₉[2]→1 を「mod-2 tempered π₁ 拡大類」と宣言する

**判定: 不採用（単独では A8 の再計上）**。

- q3thGrp は A8 で計上済みの対象。その拡大列の完全性（核の特徴付け {(c,−2t,qᵗ)} は q3th 本体に
  未証明で新規定理にはなる）を証明しても、**主語はテータ群**であり A8 の仕事。それを
  「tempered π₁ の mod-2 影」と**呼ぶ**だけでは、π₁ 側の対象が 1 つも登場しない——rubric の
  禁じる relabel そのもの。A8 再監査が q3th を「relabel でない」と判定した根拠が「ℤ³ 代理への
  比較準同型が皆無」だったことの裏返しとして、**比較なしにテータ群へ A5 status を付けることは
  同じ監査基準の下で自動的に二重計上**になる。
- (a) が A5 の内容になる唯一の形: 拡大類を **tempered π₁ 側の対象（tpeGroup またはその実現）**
  が受け取ること＝候補 (b)。

### 2.2 候補 (b): 実比較準同型 Φ/Ψ — 代理 tempered π₁ の実テータ群内実現（**採用**）

**判定: 実建設(b)＋昇格(a)・tractable・A5 の主語**。q3th 設計が「(i) A5: q3thGrp と tpeGroup の
比較準同型＝tempered π₁ の非可換拡大類の実現（v(q)=2 が拡大類に可視）」と明示 defer した仕事。

#### 2.2.1 数学的内容（本設計で手計算検証済み）

実テータ群内の 3 元（すべて q3th 既存・実 ℚ₃^× 成分）:

- X := `q3thG3` = ((1,−1),3)（Klein 点 [3] の lift・w=3=実半周期・v(3)=1=v(q)/2）
- Y := `q3thGm1` = ((1,0),−1)（Klein 点 [−1] の lift・w=−1∈ℤ₃^×）
- Z := `q3thScalar (0,q3tNegOne)`（実スカラー −1・中心的 `q3th_ker_central`・Z²=1 `q3tNegOne_sq`）

基本関係（既存定理から 1 行）: [X,Y]=Z（`q3th_comm_eq_weil`＋`q3th_weil_g3_gm1`）、すなわち
**X·Y = Z·(Y·X)**、Z 中心。このとき:

**Φ : thetaGrp → q3thM、Φ(a,b,c) := Yᵇ·Xᵃ·Zᶜ は本物の群準同型**（順序が本質: Xᵃ を先に
置く順序では準同型にならないことを検算済み）。証明は座標閉形式（スカラー成分に三角数
3^{−a(a−1)/2} が現れ Int 除算が要る）を**回避**し、braiding 補題

> 一般 Grp G で x·y = z·(y·x)・z 中心 ⟹ xᵃ·yᵇ = z^{a·b}·yᵇ·xᵃ（∀a,b:Int）

（tateZpow の Int 二重帰納・q3th_comm_zpow と同系の確立イディオム）から純群論的に出す:
Φ(v)Φ(w) = Yᵇ Xᵃ Zᶜ Yᵇ′ Xᵃ′ Zᶜ′ = Z^{ab′} Y^{b+b′} X^{a+a′} Z^{c+c′} = Φ(v·w)
（thetaGrp の積の第 3 成分 c+c′+ab′ と on the nose で一致）。

**Ψ : tpeGroup → q3thM、Ψ((a,b,c),n) := Yᵇ·X^{a+n}·Zᶜ は本物の群準同型**。検算:
Ψ(x)Ψ(y) の Z 指数 = c+c′+(a+n)b′ は tpeGroup の積の第 3 成分 c+(c′+n·b′)+a·b′ と一致。
Ψ∘tpeIncl = Φ・Ψ(tpeSection n) = Xⁿ。像は q3thGrp 内（X,Y,Z∈q3thGrp 既証明＋部分群の
zpow 閉性補題）。

#### 2.2.2 これが与える A5 の実定理（旗艦）

1. **代理シンプレクティック形式＝実 Weil ペアリング**:
   q3thWeil (Φv) (Φw) = (−1)^{ω(v,w)} ∈ 実 μ₂ ⊂ ℤ₃^×（ω = ab′−a′b・M384F `ttc_commutator_form`
   の抽象 ℤ 値が実 ℤ₃^× 単数として評価される）。抽象シクロトーム生成元 (0,0,1) ↦ 実 −1 ≠ 1。
   M384F 正直限定「μ_l 像は抽象 ζ パラメータ」「tempered 被覆の商としての実現は外部」の
   **level-2 部分の実 discharge**。
2. **deck×テータ交換子の実値化（分裂直積ブロッカーの discharge）**: M424F の
   [s(n), ι(a,b,c)] = ι(0,0,n·b) が Ψ で **[Xⁿ, Φ(a,b,c)] = 実 (−1)^{n·b}** になる。特に
   [Ψ(s 1), Ψ(ι(0,1,0))] = 実 −1 ≠ 1——**deck 切断がテータ部と可換でない実 tempered 対象**が
   初めて成立。対照定理: q3tpGroup では deck 切断 (1,n) が μ 部分 ι(z) と可換
   （one_mul/mul_one のみで証明——分裂直積の自明性を定理として可視化）。
3. **v(q) の tempered 側復元（候補 (c) の正当な形）**: deck 切断像の w 成分は実半周期
   (Ψ(s n)).w = 3ⁿ（付値 n）で、その**平方**が A5a の実周期準同型に着地する:
   ((Ψ(s n)).w)² = 9ⁿ = qⁿ = `(q3tdPeriodHom 2).map n`。よって
   **v(q) = 2 = 2·v((Ψ(s 1)).w)** が tempered π₁ 側の data（deck 切断の Ψ 像）から復元される。
   分裂直積では「q は群の外」だったが、テータ実現では q が deck 像の平方＝群論的 data として
   再出現する（q 不可視ブロッカーの level-2 discharge）。さらに X^{2n} = scalar(3ⁿ)·g_τⁿ
   （検算済み）により deck 像の平方が実降下元 g_τⁿ（スカラー q^{−n²}）に半周期スカラー込みで
   一致——拡大類と E2 二次指数の接続（系として任意・§3 の必須リストには入れない）。

#### 2.2.3 正直核（同時に定理化する・強化材料）

- **ker Ψ = {((−n, 2β, 2γ), n)}**（level-2 崩壊＋deck・テータ a 方向の融合）。witness 定理:
  Ψ(ι(0,0,2)) = 1（Z²=1）・Ψ(ι(−1,0,0)·s(1)) = 1。後者は M424F 自身の
  `tpe_aut_conj_in_theta`（s(n) と内部 (n,0,0) の共役作用一致）の忠実な帰結であり数学的に正直
  （[EtTh] のテータ商では deck と Heisenberg 第 1 座標は同一視される）。
- **χ 捻りは level 2 で不可視**: (a,b,c,n)↦(a,−b,−c,n) は tpeGroup の自己同型だが Ψ∘捻り = Ψ
  （(−1)^{−k}=(−1)^k）。M429F atpGroup の算術拡大は μ₂ 影では見えない——奇数レベル l≥3 が
  ζ_l∉ℚ₃ でブロックされる恒久限定（q3th 正直限定 5 と同根）を定理で固定。

### 2.3 候補 (c) 単独: g_τⁿ=(q^{−n²},−2n,qⁿ) から v(q)=2 を読む

**判定: 単独では不採用（A8 の再計上）・(b) 経由の系としてのみ採用**。
スカラー付値 P(n)=−2n² の二階差分 −2·v(q)/2 等、g_τ **のみ**を主語とする v(q) 読み出しは
`q3th_tau_pow`（A8 計上済み）の算術系にすぎない。v(q) 復元が A5 の内容になるのは、
**tempered π₁ 側の対象（Ψ の deck 切断像）**から読み出すとき（§2.2.2-3）に限る。

### 2.4 二重計上境界の厳密化（vs A8・監査向け明文）

| 項目 | A8 に既計上（触らない・消費のみ） | A5d の新規内容（今回計上を主張） |
|---|---|---|
| 対象 | q3thM・q3thGrp・q3thWeil・q3th_comm_eq_weil・q3th_nonabelian・q3th_ker_central・q3th_tau_pow・witness X,Y | 準同型 **Φ・Ψ そのもの**（map_mul・像の部分群所属）・braiding 補題（一般 Grp） |
| 交換子 | [X,Y]=−1 という**テータ群内の値**（A8 D3/D4 で計上済み） | **代理 tempered π₁ の交換子公式**（M384F ω・M424F deck×θ=n·b）**が Φ/Ψ を通して実値に等しい**という等式——左辺の主語は thetaGrp/tpeGroup（A5 骨格）であり、この等式は q3th 単独からも代理単独からも出ない |
| v(q) | g_τ の閉形式（q^{−n²}・qⁿ） | **tempered deck 切断像**の半周期 3ⁿ とその平方＝q3tdPeriodHom（A5a）への着地・v(q)=2 の tempered 側復元 |
| 判定基準 | — | 新定理の各主張から Φ/Ψ を消去すると命題が成立しなくなる（=relabel でない）ことを実装ヘッダに明記。q3th の定理の再証明・再輸出は 0 本 |

**厳密に言うべきこと**: もし本ラウンドが「[X,Y]=−1 を『tempered の交換子』と改名する」だけ
なら A8 の再計上である。そうならないための必須条件は (i) Φ/Ψ の map_mul が本物の証明を持つ
こと、(ii) 旗艦等式の左辺が M384F/M424F の**既存の代理対象**であること、(iii) v(q) 復元が
Ψ 像経由で A5a の実周期準同型に接続されること——の 3 点であり、§3 の必須定理リストは
この 3 点をすべて含む。

---

## 3. 結論 — 選定ステップ A5d: `IUT/Q3TemperedThetaClass.lean`（prefix `q3nt`・tier M）

**分類ヘッダ（実装時）**: [実／昇格(a)+本物建設(b)]。M384F/M424F の代理 tempered テータ骨格
（自認「実曲線未接続・実現は外部」）を、実 E₉(ℚ₃) 上の実テータ群 q3thGrp（A8）への本物の
準同型 Φ/Ψ で実現し、抽象シンプレクティック形式＝実 Weil ペアリング・deck×θ 交換子＝実 −1・
v(q)=2 の tempered 側復元を完全証明する。complete_pct 影響: **A5 0.15→0.25（見込み・
独立監査確定が条件）**。A8/A7/E は主張しない。

依存: `IUT.Q3ThetaGroup`・`IUT.TemperedPi1Etale`（→ thetaGrp/tpeGroup/M384F 系を連鎖 import）・
`IUT.Q3TateDeck`（q3tdPeriodHom）・`IUT.Q3TemperedPi1`（対照定理用）。既存ファイル不変更。
規模: 約 550–700 行・8 節。choice-free（新規 Classical.choice 禁止・#print axioms =
[propext, Quot.sound] を全公開対象で自己申告→独立監査再実行）。

### 3.1 必須定理リスト（正確な名前・全て choice-free 戦略込み）

```lean
-- §1 braiding（一般 Grp・唯一の新イディオム・fable HELP スポット候補）
theorem q3nt_braid (G : Grp) (x y z : G.carrier)
    (hz : ∀ g, G.mul z g = G.mul g z)
    (hrel : G.mul x y = G.mul z (G.mul y x)) (a b : Int) :
    G.mul (tateZpow G x a) (tateZpow G y b)
      = G.mul (tateZpow G z (a * b)) (G.mul (tateZpow G y b) (tateZpow G x a))
-- 証明: 先に b:Nat 帰納で xᵃy = zᵃ(yxᵃ) 型の一段補題（a の Int 場合分け）、
-- 次に b の Int 場合分け。q3th_comm_npow/zpow・tateZpow_add の写経圏内。

-- §2 生成元と関係式
def q3ntZ : q3thCar := q3thScalar ((0 : Int), q3tNegOne)
theorem q3nt_rel : q3thMul q3thG3 q3thGm1 = q3thMul q3ntZ (q3thMul q3thGm1 q3thG3)
  -- q3th_comm_eq_weil + q3th_weil_g3_gm1 から（または 1 回の成分計算）
theorem q3nt_Z_central : ∀ g, q3thMul q3ntZ g = q3thMul g q3ntZ   -- q3th_ker_central の系
theorem q3nt_Z_sq : q3thMul q3ntZ q3ntZ = q3thOne                 -- q3tNegOne_sq
theorem q3nt_Z_zpow (c : Int) :
    tateZpow q3thM q3ntZ c = q3thScalar (tateZpow q3tGrp ((0:Int), q3tNegOne) c)
theorem q3nt_mem_zpow (g : q3thCar) (hg : q3thMem g) (n : Int) :
    q3thMem (tateZpow q3thM g n)   -- 部分群 zpow 閉性（Nat 帰納 + inv）

-- §3 Φ: 代理 Heisenberg の実現
def q3ntPhi : Hom thetaGrp q3thM where
  map := fun v => q3thMul (tateZpow q3thM q3thGm1 v.2.1)
    (q3thMul (tateZpow q3thM q3thG3 v.1) (tateZpow q3thM q3ntZ v.2.2))
  map_mul := ...   -- q3nt_braid + 中心性で正規形へ（座標閉形式・三角数不使用）
theorem q3nt_phi_mem : ∀ v, q3thMem (q3ntPhi.map v)
theorem q3nt_cyclotome_real : q3ntPhi.map ((0,0,1) : Int×Int×Int) = q3ntZ
theorem q3nt_cyclotome_ne_one : q3ntPhi.map ((0,0,1) : Int×Int×Int) ≠ q3thOne

-- §4 旗艦 1: 代理 ω ＝ 実 Weil ペアリング
theorem q3nt_symplectic_real (v w : thetaGrp.carrier) :
    q3thComm (q3ntPhi.map v) (q3ntPhi.map w)
      = ((tateZpow q3tGrp ((0:Int), q3tNegOne) (v.1 * w.2.1 - w.1 * v.2.1), (0:Int)),
         q3tGrp.one)
  -- Hom.map_grp_comm + theta_comm + q3nt_Z_zpow
theorem q3nt_weil_eq_form (v w : thetaGrp.carrier) :
    q3thWeil (q3ntPhi.map v) (q3ntPhi.map w)
      = tateZpow q3tGrp ((0:Int), q3tNegOne) (v.1 * w.2.1 - w.1 * v.2.1)

-- §5 Ψ: 代理 tempered π₁（⋊ 込み）の実現
def q3ntPsi : Hom tpeGroup q3thM where
  map := fun x => q3thMul (tateZpow q3thM q3thGm1 x.1.2.1)
    (q3thMul (tateZpow q3thM q3thG3 (x.1.1 + x.2)) (tateZpow q3thM q3ntZ x.1.2.2))
  map_mul := ...   -- 同上（tpe 第 3 成分 c+c′+(a+n)b′ と Z 指数の一致・検算済み）
theorem q3nt_psi_incl : ∀ z, q3ntPsi.map (tpeIncl.map z) = q3ntPhi.map z
theorem q3nt_psi_deck (n : Int) :
    q3ntPsi.map (tpeSection.map n) = tateZpow q3thM q3thG3 n

-- §6 旗艦 2: deck×テータ交換子の実値（分裂直積ブロッカー discharge）
theorem q3nt_deck_theta_real (n a b c : Int) :
    q3thComm (q3ntPsi.map (tpeSection.map n))
        (q3ntPsi.map (tpeIncl.map ((a,b,c) : Int×Int×Int)))
      = ((tateZpow q3tGrp ((0:Int), q3tNegOne) (n * b), (0:Int)), q3tGrp.one)
theorem q3nt_deck_theta_ne_one :
    q3thComm (q3ntPsi.map (tpeSection.map 1))
        (q3ntPsi.map (tpeIncl.map ((0,1,0) : Int×Int×Int))) ≠ q3thOne
theorem q3nt_split_contrast (z : tmzLimit.carrier) (n : Int) :   -- 対照: A5b は可換
    q3tpGroup.mul (tmzLimit.one, n) (q3tpIncl.map z)
      = q3tpGroup.mul (q3tpIncl.map z) (tmzLimit.one, n)   -- one_mul/mul_one のみ

-- §7 旗艦 3: v(q)=2 の tempered 側復元
theorem q3nt_deck_halfperiod (n : Int) :
    (q3ntPsi.map (tpeSection.map n)).2
      = tateZpow q3tGrp ((1:Int), (zpUnits 3 isPrime_three).one) n   -- w 成分＝3ⁿ
  -- w 射影 Hom q3thM → q3tGrp（map=.2・map_mul rfl）＋ Hom-zpow 可換で閉形式不要
theorem q3nt_deck_sq_period (n : Int) :
    q3tGrp.mul (q3ntPsi.map (tpeSection.map n)).2 (q3ntPsi.map (tpeSection.map n)).2
      = (q3tdPeriodHom 2).map n     -- (3ⁿ)² = qⁿ（q3th_zpow_mul・3·3=q3tQ 2）
theorem q3nt_vq_recover (n : Int) :
    ((q3tdPeriodHom 2).map n).1 = 2 * ((q3ntPsi.map (tpeSection.map n)).2).1
theorem q3nt_vq_two : ((q3ntPsi.map (tpeSection.map 1)).2).1 = 1
  -- v(q) = 2·1 = 2: 分裂直積で不可視だった q が deck 像の平方として群論的に再出現

-- §8 正直核の定理化 + capstone
theorem q3nt_psi_level2_collapse :
    q3ntPsi.map (tpeIncl.map ((0,0,2) : Int×Int×Int)) = q3thOne
theorem q3nt_psi_deck_fusion :
    q3ntPsi.map (tpeGroup.mul (tpeIncl.map ((-1,0,0) : Int×Int×Int)) (tpeSection.map 1))
      = q3thOne
theorem q3nt_chi_invisible : ...   -- (a,b,c,n)↦(a,−b,−c,n) 捻りで Ψ 不変（任意・安価）
structure Q3TemperedThetaClassData ... / def q3ntData / theorem q3ntClass_exists
```

**任意（余力があれば・必須にしない）**: `q3nt_deck_sq_tau (n) : X^{2n} = scalar(3ⁿ)·g_τⁿ`
（deck 平方＝実降下元・E2 二次指数への接続。三角数簿記が要るため必須から外す）。

### 3.2 選定理由（候補比較）

| 候補 | 判定 |
|---|---|
| **(採用) (b) Φ/Ψ 実現＋(c) 系の v(q) 復元** | q3th 設計・A8 監査の双方が名指しで A5 に残した空白そのもの。全部品既存・新イディオムは braiding 1 本・A5 の主語（代理骨格の実値化・拡大類・v(q)）に正確に載る |
| (a) 単独（テータ群拡大列の relabel） | ❌ A8 再計上（§2.1） |
| (c) 単独（g_τ からの v(q)） | ❌ A8 再計上（§2.3） |
| tpeGroup の主語ごと置換（実被覆空間の tempered π₁） | ❌ 時期尚早——Berkovich/rigid 位相の形式化が前提（A5 恒久上限の壁・先行設計 §6） |
| 奇数レベル l≥3 の実テータ実現 | ❌ ζ_l ∉ ℚ₃（拡大体機構の後続・q3th 正直限定 5） |

---

## 4. 正直な線引き — 本ラウンドで実にならないもの・二重計上の明文

1. **実現は level 2（μ₂ 影）**: Ψ は単射でない（ker = {((−n,2β,2γ),n)}・§2.2.3 で定理化）。
   代理シクロトーム ℤ の実現は mod 2 のみ。ℤ 全体（μ_{l^∞}・ẑ(1)）の実現は奇レベル拡大体
   機構（後続）。χ 捻り（M429F）は level 2 で不可視（定理化）——算術拡大 atpGroup の実現は 0。
2. **tempered π₁ の「定義」は依然外部**: Berkovich/rigid 被覆理論・位相なし。Ψ は
   「実被覆空間の π₁ からの写像」ではなく「代理提示の実群内実現（mod-2 étale theta 商の
   群論的影）」。A5 の 1.0 どころか 0.5 にも位相なしでは届かない（先行設計 §6 の恒久線引きを
   継承——**A5 上限 0.35–0.4 の見積もりは不変**）。
3. **G_{ℚ₃}/実 Gal 作用 0**: q3thGrp・Ψ 像への実 Galois 作用（tmzActHom 接続）は A7 後続。
4. **実テータ関数 0・cuspidalization 本体 0**: q3th 正直限定 2・3 をそのまま継承（消さない・
   弱めない）。
5. **二重計上の排除（明文・実装ヘッダに転記）**:
   - **vs A8（q3th）**: q3th の定理は消費のみ（再証明・再輸出 0 本・ファイル不変更）。A5d の
     計上対象は Φ/Ψ・braiding・「代理の主張＝実値」等式・v(q) の tempered 側復元のみ。
     各旗艦は Φ/Ψ を消去すると成立しない主張であることをヘッダで自己点検（§2.4）。
     **A8 status は今回主張しない**。
   - **vs A5a/A5b/A5c**: q3tdPeriodHom は消費（v(q) 着地先）。q3tpGroup は対照定理の主語として
     登場するのみ（既存正直限定は不変更）。A5b の「punctured 非可換 θ は範囲外」正直限定 (2) は
     「level-2 実現は q3nt で成立・完全実現（忠実・全レベル・位相）は依然範囲外」へ**部分
     discharge として更新**（消去しない・新ファイル側に記載し既存ヘッダは触らない）。
   - **vs A4/A7/E**: 主張しない。E2 二次指数接続（任意定理）を入れても E status は動かさない。
   - 既存 M384F/M424F/M429F の正直限定・外部仮説は一切消さない（併設）。

---

## 5. status 見込み・柱A% 算術

### 5.1 現状の検算（target_ledger.json 実測・2026-07-11 A8=0.65 反映後）

Σ_A = 8·0.85 + 8·0.65 + 12·0.75 + 14·0.55 + **10·0.15** + 14·0.58 + 12·0.40 + 12·0.65 + 10·0.10
　　 = 6.8 + 5.2 + 9.0 + 7.7 + **1.5** + 8.12 + 4.8 + 7.8 + 1.0 = **51.92** → 表示 **52** ✓
（compute_complete_pct.py 出力 {"A": 52} と一致。非 A5 定数 = 51.92 − 1.5 = **50.42**、
Σ_A = 50.42 + 10·s_A5。）

### 5.2 s_A5 と表示の境界（Python banker's rounding）

round(52.5) = 52（偶数側）なので表示 53 には **Σ_A > 52.5 が厳密に必要** ⟺
50.42 + 10·s > 52.5 ⟺ **s_A5 ≥ 0.21**（ledger 粒度 0.01: s=0.209 は書けないので 0.21 が最小）。

| s_A5 | Σ_A | 表示 |
|---|---|---|
| 0.15（現状） | 51.92 | 52 |
| 0.20 | 52.42 | **52（据え置き）** |
| **0.21** | 52.52 | **53**（最小到達点） |
| 0.25（設計見込み） | 52.92 | 53 |

### 5.3 見込みと根拠

- **設計見込み 0.25（+0.10）**: A5 正直限定 (2) が「IUT 本丸・範囲外」と名指しした punctured
  非可換 θ 拡大の level-2 実現＋分裂直積ブロッカー（q 不可視・拡大類自明・非可換性 0）の
  3 点同時 discharge は、A5a（0→0.1）・A5c（+0.05）と比べ質的ジャンプ（A8 のテータ群 +0.05 と
  同格以上の、A5 側の対応部品）。
- **敵対的下限 0.20**: 監査が「level-2 影・非単射・位相なし」を強く割り引く場合。
  **このとき表示は 52 据え置き**（正直に横這い報告する）。表示 53 は監査が 0.21 以上
  （実質 0.25 裁定）を出した場合のみ。
- **最悪 0.15 据え置きのシナリオ**: §5.4 の「橋」分類リスク。

### 5.4 監査リスク（最大リスクの明示）

AUDIT_RUBRIC の「代理/橋（算入しない）: 既存定理の再輸出・値一致確認・束ね」に分類される
リスクが本ラウンド最大の下振れ要因。防御は設計に組み込み済み:
(i) Φ/Ψ は再輸出でなく**新規の実対象**（map_mul が braiding 経由の本物の証明・像は実 ℚ₃^×
成分の非可換部分群）、(ii) 旗艦は「値一致確認」でなく**代理側では未定義だった実値の生成**
（抽象 ω ∈ ℤ には実 μ₂ 値が存在しなかった）、(iii) v(q)=2 復元は A5 の名指しブロッカーの
discharge で q3th 単独からは出ない、(iv) 正直核（ker の定理化）で overclaim を先回り遮断。
それでも監査が橋と裁定すれば A5=0.15 据え置き・柱A 52 のまま——その場合も本ラウンドは
「A7 mono-theta（q3thGrp への実 Gal 作用）の前提整備」として無駄にはならないが、
complete_pct 0 前進と正直に報告する。

---

## 6. 実装計画（親向け）

- **1 ファイル・1 実装枠**: `IUT/Q3TemperedThetaClass.lean`（prefix `q3nt`・§3.1 の 8 節・
  550–700 行）。依存は既存のみで**他の柱の枠と並列可**。
- **tier/model**: **M（opus）1 枠**。本設計で Φ/Ψ の準同型性・Z 指数の一致・v(q) 着地を全て
  手計算検証済みのため新イディオム発明は braiding 補題 1 本のみ。**fable は HELP スポット限定**
  （詰まり候補: q3nt_braid の Int 二重帰納の負冪側・q3ntPsi.map_mul の正規形整理）。
- **choice-free 規約**: 全 witness 明示（X・Y・Z は q3th 既存）・∃ 除去は Prop ゴール内のみ・
  新規 Classical.choice 0・全公開対象の #print axioms = [propext, Quot.sound] を実装者が
  自己申告 → 独立監査が scratch import で再実行。
- **実装上の注意（先回り指示）**:
  (1) Φ の定義は必ず zpow 積形（Yᵇ·Xᵃ·Zᶜ）にする——座標閉形式は三角数 a(a−1)/2 の Int 除算
  簿記が発生するため禁止（braiding 経由なら不要）。
  (2) 順序は Y→X→Z（X を左に置く順序では準同型にならない・§2.2.1）。
  (3) `q3nt_split_contrast` は tmzLimit の可換性に依存させない（one_mul/mul_one で閉じる形に
  限定・tmz 内部に触らない）。
  (4) 監査観点: 各旗艦から Φ/Ψ を消去すると命題が成立しないこと・q3th/M384F/M424F の
  正直限定が不変更なこと・ker 定理（正直核）が消されていないこと。
- **共有ファイル**（IUT.lean・build.sh・graph-meta.json `pillars.A`・target_ledger.json A5・
  dashboard.md 二軸表・gen_graph.py PILLAR 辞書への q3nt 追記・graph.json 再生成）は
  親が統合時に一括更新。status 確定は独立敵対監査（AUDIT_RUBRIC・本体のみ判定）後。
- **後続ロードマップ（本ラウンド外）**: (i) A7: q3thGrp/Ψ 像への実 Gal(ℚ(ζ_{3^∞})/ℚ) 作用
  （tmzActHom 接続）→ mono-theta 剛性の実入口、(ii) A5 続き: 奇レベル l≥3 の実テータ実現
  （拡大体機構が前提）・忠実実現、(iii) A8: 交換子と π₁(E∖{O}) 惰性の同定（cuspidalization
  本体・最難）。

---

*設計: 詳細化ラウンド 2026-07-11。実装着手前にユーザー承認・実装後に独立敵対監査が status を
確定する。本書の全群論計算（q3nt_rel・Φ/Ψ の cocycle 一致・ker Ψ・半周期平方＝qⁿ・χ level-2
不可視）は設計時に手計算検証済み。*
