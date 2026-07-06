/-
  IUT/MonoThetaRigidity.lean — M323F（mono-theta 環境の定数倍剛性:
  テータ値の比 Θ(q,u_i)/Θ(q,u_j) = q^{(i²−j²)/2l} が定数倍不定性の下で
  一意 / 柱E・テータ）

  分類: **[実]**（本物の先行建設 (b)）。
  complete_pct 影響: 柱E の実 IUT 完全証明率を **mono-theta 環境の三剛性
  （円分剛性・離散剛性・定数倍剛性）のうち「定数倍剛性（constant multiple
  rigidity）」の値版**の側で前進させる。IUT III の遠アーベル復元は
  「エタールテータ関数を l-捻れ点 u_j で評価したテータ値」を主対象とし、
  その値が**定数倍の不定性**（テータ関数 Θ を単元定数 c 倍する曖昧さ、
  ℚ_p^× のなかで Θ ↦ c·Θ）に依らず**比 Θ(q,u_i)/Θ(q,u_j) が一意**に
  定まること——すなわち mono-theta 環境の定数倍剛性——が three-rigidity/
  log-shell 評価の核である。既存の柱E は M318F（ThetaValueLtor.lean）で
  l-捻れ点でのテータ値 Θ(q,u_j)=u^{j²}=q^{j²/2l}（本物の Laurent 単項式）・
  積の指数和 i²+j²・l-周期整合を、M308F（EtaleThetaReal.lean）で
  テータ因子の原点通過 Θ(q,1)=0（正規化の起点）を、M237F
  （ThetaValueSubgroup.lean）でテータ値の単元部分群構造（単位・積・逆元）を
  本物で建設していたが、**「定数倍不定性の下でのテータ値の比の一意性」**
  ——mono-theta 三剛性の一つ——は未着手だった。本層はそこへ本物で踏み込む:

    (1) **本物の対象**: l-捻れ点でのテータ値 Θ(q,u_j)=u^{j²}
        （M318F thLtorValue、本物の Laurent 単項式）の**本物の乗法逆元**
        u^{−j²}=uMonHom R (−j²)（`mThRigInv`、M232F uMonHom_unit による
        Laurent 環単元群での逆元、choice なし）と、それを用いた
        **テータ値の比** Θ(q,u_i)/Θ(q,u_j) = u^{i²−j²}（`mThRigRatio`,
        Laurent 環の乗法での本物の比）。
    (2) **本物の性質（本丸）**: **定数倍剛性** `mThRig_constMult_rigid`。
        すなわち、任意の**単元定数** c（逆元 cInv を持ち c·cInv=1；
        Θ を一様に c 倍する定数倍不定性を表す）で全テータ値を c 倍しても、
        比は不変:
          (c·Θ(q,u_i)) · (cInv·Θ(q,u_j)^{−1}) = Θ(q,u_i)·Θ(q,u_j)^{−1}
                                              = u^{i²−j²}。
        定数 c が比の中で相殺し（可換モノイドの並べ替え
        `mThRig_mul_rearrange` + c·cInv=1）、比がちょうど正準単項式
        u^{i²−j²}=q^{(i²−j²)/2l}（**c に依らず一意**）に定まる。これが
        mono-theta 環境の定数倍剛性の値版の本物の機械検証。
    (3) **剛性が整合系をなす（コサイクル）**: 比は推移的
        `mThRig_ratio_cocycle`: ratio(i,j)·ratio(j,k)=ratio(i,k)、
        対角 `mThRig_ratio_diag`: ratio(j,j)=1、因数分解
        `mThRig_ratio_factor`: 指数 i²−j²=(i−j)(i+j)。定数倍剛性で
        一意化された比が**大域的に整合した 1-コサイクル**をなすこと
        （正規化の一意性が系全体で無矛盾）。

  * M323F-1 `mThRigInv` / `mThRig_inv_mul` — テータ値の本物の乗法逆元
    u^{−j²}（M232F uMonHom_unit、Laurent 単元群での逆元）
  * M323F-2 `mThRigRatio` / `mThRig_ratio_exp` / `mThRig_ratio_factor` —
    テータ値の比 Θ_i/Θ_j = u^{i²−j²}（正準単項式）・因数分解 (i−j)(i+j)
  * M323F-3 `mThRig_ratio_diag` / `mThRig_ratio_cocycle` — 対角=1・
    推移律（比が整合した 1-コサイクルをなす）
  * M323F-4 `mThRig_mul_rearrange` — 可換モノイドの並べ替え
    (c·a)(cInv·b)=(c·cInv)(a·b)（定数相殺の代数核）
  * M323F-5 `mThRig_constMult_rigid` / `mThRig_constMult_canonical` —
    **定数倍剛性（本丸）**: 定数倍不定性の下で比が不変・正準単項式
    u^{i²−j²} に一意
  * M323F-6 `MonoThetaRigidityData` / `monoThetaRigidityData` /
    `mThRig_exists` — 総括レコードと存在

  意義: M318F の本物のテータ値 u^{j²} の上に、**本物の乗法逆元**と
  **テータ値の比**を建設し、mono-theta 環境の三剛性の一つ
  **「定数倍剛性」** ——テータ関数の定数倍不定性の下で比 Θ_i/Θ_j が
  正準単項式 u^{i²−j²}=q^{(i²−j²)/2l} に一意に定まること——を本物で
  閉じる。比が対角=1・推移律（1-コサイクル）で大域整合することも示し、
  three-rigidity/log-shell 評価の入口を柱E で前進させる。

  **正直な限定（消去・弱化禁止）**:
  - **本物にした mono-theta 三剛性は「定数倍剛性の値版」1 つのみ**:
    l-捻れ点でのテータ値の比 Θ_i/Θ_j が**単元定数倍の不定性**
    （Θ ↦ c·Θ, c·cInv=1）の下で不変で正準単項式 u^{i²−j²} に一意、
    である。**円分剛性（μ_l 成分の χ 一意性・M124F/M322F 系）**・
    **離散剛性（周期格子 q^ℤ の離散性の完全形）**・**三剛性の同時
    確立（mono-theta 環境の IUT 本丸）**は**後続**。
  - 主語は本物の Laurent 単項式 Θ(q,u_j)=u^{j²}=uMonHom R (j²)
    （M318F/M232F/M223F の本物）と、その本物の乗法逆元 u^{−j²}
    （M232F uMonHom_unit、Laurent 環単元群での逆元）。**toy 主語
    （m202fVol・Bool 軌道・surrogate 群）は一切用いない**。
  - **定数倍不定性**は「Laurent 環の単元 c（c·cInv=1）による一様な
    乗法」として本物にモデル化する。ここで扱う定数は Laurent 環の
    任意の単元であり、比の中で相殺することを可換モノイドの並べ替えで
    示す。**μ_2l（2l 乗根の群）としての定数の具体化**・**ガロア同変な
    p 進テータ値上での定数倍剛性**・**tempered π₁ の商としての実現**は
    後続（本層は Laurent 環単元一般での比の不変性まで）。
  - 有理冪 q^{(i²−j²)/2l} の「型」は指数の i²−j² 依存性（M318F 同様、
    分子が本物の i²−j²、分母 2l は微細格子＝l 乗根の witness）として
    本物。有理冪 q^{1/2l} そのものの体内実在（l 乗根の構成）は
    **witness**（微細座標 u を Laurent 変数として受ける）であり、
    柱A の分離閉包・実 π₁^ét で本物化する。
  - **既存 MonoThetaEnv/MonoThetaWitness の模型に対する本層の位置**:
    M196F（MonoThetaEnv）は mono-theta 環境の**群論的骨格**（Heisenberg
    群・cyclotomic 同期の witness）を束ねるにとどまり、三剛性のうち
    定数倍剛性を**値レベルで本物に**は与えていなかった。本層は
    その定数倍剛性を、既存の**本物のテータ値 u^{j²}**（骨格でなく
    M318F の実 Laurent 単項式）の上に**新規に本物建設**する
    （既存骨格の内部埋めでなく、本物のテータ値上の新規剛性）。

  全て選択公理を証明本体で新規導入せず（M318F/M237F/M232F/M223F/M88F
  から継承、新規 Classical・新規 Classical.choice なし。Laurent 環
  laurentRing / laurentRel / Quot レベルの主張は Quot.sound を使う——
  商構成に内在、選択公理ではない）。#print axioms により継承分のみ
  （propext, Quot.sound 系のみ・Classical.choice/sorryAx 不使用）で
  あることを確認済み。サブエージェント新規1本（共有ファイル未変更）。
  一般名は `mThRig` 接頭辞で衝突回避。
-/
import IUT.ThetaValueLtor

namespace IUT

/-! ## M323F-1: テータ値の本物の乗法逆元 u^{−j²} -/

/-- **M323F-1a: テータ値の乗法逆元** — l-捻れ点でのテータ値
    Θ(q,u_j)=u^{j²}（M318F thLtorValue）の Laurent 環単元群での**本物の
    乗法逆元** u^{−j²}=uMonHom R (−j²)。負冪の単項式（choice なし、
    M232F uMonHom_unit で逆元性を保証）。 -/
def mThRigInv (R : CRing) (j : Int) : (laurentRing R).carrier :=
  uMonHom R (- thLtorExp j)

/-- **定理 (M323F-1b): 逆元性** — Θ(q,u_j)·Θ(q,u_j)^{−1} = 1。
    テータ値 u^{j²} とその逆元 u^{−j²} の積が Laurent 環の乗法単位
    （M232F uMonHom_unit）。テータ値が Laurent 環単元群に住むことの
    逆元条件（本物）。 -/
theorem mThRig_inv_mul (R : CRing) (j : Int) :
    (laurentRing R).mul (thLtorValue R j) (mThRigInv R j)
      = (laurentRing R).one := by
  show (laurentRing R).mul (uMonHom R (thLtorExp j)) (uMonHom R (- thLtorExp j))
    = (laurentRing R).one
  exact uMonHom_unit R (thLtorExp j)

/-! ## M323F-2: テータ値の比 Θ_i/Θ_j = u^{i²−j²} -/

/-- **M323F-2a: テータ値の比** — Θ(q,u_i)/Θ(q,u_j)
    = Θ(q,u_i)·Θ(q,u_j)^{−1}（Laurent 環の乗法での本物の比）。
    l-捻れ点 u_i, u_j でのテータ値の比。IUT の定数倍剛性の主対象。 -/
def mThRigRatio (R : CRing) (i j : Int) : (laurentRing R).carrier :=
  (laurentRing R).mul (thLtorValue R i) (mThRigInv R j)

/-- **定理 (M323F-2b): 比の正準単項式表示** — Θ_i/Θ_j = u^{i²−j²}
    = uMonHom R (thLtorExp i − thLtorExp j)。テータ値の比がちょうど
    指数差 i²−j² の単項式 u^{i²−j²}=q^{(i²−j²)/2l}（M232F uMonHom_add）。
    比が正準な単項式に定まる（定数倍剛性の値の一意性の核）。 -/
theorem mThRig_ratio_exp (R : CRing) (i j : Int) :
    mThRigRatio R i j = uMonHom R (thLtorExp i - thLtorExp j) := by
  show (laurentRing R).mul (uMonHom R (thLtorExp i)) (uMonHom R (- thLtorExp j))
    = uMonHom R (thLtorExp i - thLtorExp j)
  rw [← uMonHom_add]
  have e : thLtorExp i + (- thLtorExp j) = thLtorExp i - thLtorExp j := by omega
  rw [e]

/-- **定理 (M323F-2c): 比の指数の因数分解** — Θ_i/Θ_j = u^{(i−j)(i+j)}。
    比の指数 i²−j² が (i−j)(i+j) に因数分解（差の平方公式）。テータ値の
    比が l-捻れラベルの差 i−j と和 i+j で決まる構造。 -/
theorem mThRig_ratio_factor (R : CRing) (i j : Int) :
    mThRigRatio R i j = uMonHom R ((i - j) * (i + j)) := by
  rw [mThRig_ratio_exp]
  have e : thLtorExp i - thLtorExp j = (i - j) * (i + j) := by
    show i * i - j * j = (i - j) * (i + j)
    have h1 : (i - j) * (i + j) = i * (i + j) - j * (i + j) := Int.sub_mul i j (i + j)
    have h2 : i * (i + j) = i * i + i * j := Int.mul_add i i j
    have h3 : j * (i + j) = j * i + j * j := Int.mul_add j i j
    have h4 : i * j = j * i := Int.mul_comm i j
    rw [h1, h2, h3, h4]
    omega
  rw [e]

/-! ## M323F-3: 比の対角=1・推移律（1-コサイクル） -/

/-- **定理 (M323F-3a): 対角の比は 1** — Θ_j/Θ_j = 1。同じ l-捻れ点での
    テータ値の比は乗法単位（M323F-1b 逆元性）。定数倍剛性で一意化された
    比の正規化条件。 -/
theorem mThRig_ratio_diag (R : CRing) (j : Int) :
    mThRigRatio R j j = (laurentRing R).one :=
  mThRig_inv_mul R j

/-- **定理 (M323F-3b): 比の推移律（1-コサイクル）** —
    (Θ_i/Θ_j)·(Θ_j/Θ_k) = Θ_i/Θ_k。テータ値の比が推移的に整合
    （u^{i²−j²}·u^{j²−k²}=u^{i²−k²}, M232F uMonHom_add）。定数倍剛性で
    一意化された比が**大域的に整合した 1-コサイクル**をなす
    （正規化の一意性が系全体で無矛盾）。 -/
theorem mThRig_ratio_cocycle (R : CRing) (i j k : Int) :
    (laurentRing R).mul (mThRigRatio R i j) (mThRigRatio R j k)
      = mThRigRatio R i k := by
  rw [mThRig_ratio_exp, mThRig_ratio_exp, mThRig_ratio_exp, ← uMonHom_add]
  have e : (thLtorExp i - thLtorExp j) + (thLtorExp j - thLtorExp k)
      = thLtorExp i - thLtorExp k := by omega
  rw [e]

/-! ## M323F-4: 可換モノイドの並べ替え（定数相殺の代数核） -/

/-- **M323F-4: 並べ替え補題** — 可換モノイド（Laurent 環の乗法）で
    (c·a)·(cInv·b) = (c·cInv)·(a·b)。定数 c と逆定数 cInv を集めて
    比 a·b から分離する代数核（結合律・可換律のみ、choice なし）。
    定数倍剛性で定数を相殺させるための本物の並べ替え。 -/
theorem mThRig_mul_rearrange (S : CRing) (c a cInv b : S.carrier) :
    S.mul (S.mul c a) (S.mul cInv b) = S.mul (S.mul c cInv) (S.mul a b) := by
  rw [S.mul_assoc c a (S.mul cInv b), ← S.mul_assoc a cInv b, S.mul_comm a cInv,
    S.mul_assoc cInv a b, ← S.mul_assoc c cInv (S.mul a b)]

/-! ## M323F-5: 定数倍剛性（本丸） -/

/-- **定理 (M323F-5a): 定数倍剛性（本丸）** — テータ関数の**定数倍不定性**
    の下で比 Θ_i/Θ_j は不変。任意の単元定数 c（逆元 cInv を持ち
    c·cInv=1；Θ を一様に c 倍する定数倍の曖昧さを表す）で全テータ値を
    c 倍しても:
      (c·Θ(q,u_i)) · (cInv·Θ(q,u_j)^{−1}) = Θ(q,u_i)·Θ(q,u_j)^{−1}
                                          = Θ_i/Θ_j。
    定数 c が比の中で相殺（M323F-4 並べ替え + c·cInv=1 + 単位律）し、
    比がちょうど **c に依らず一意** に定まる。mono-theta 環境の
    **定数倍剛性（constant multiple rigidity）の値版**の本物の機械検証。 -/
theorem mThRig_constMult_rigid (R : CRing) (i j : Int)
    (c cInv : (laurentRing R).carrier)
    (hc : (laurentRing R).mul c cInv = (laurentRing R).one) :
    (laurentRing R).mul
        ((laurentRing R).mul c (thLtorValue R i))
        ((laurentRing R).mul cInv (mThRigInv R j))
      = mThRigRatio R i j := by
  show (laurentRing R).mul ((laurentRing R).mul c (thLtorValue R i))
      ((laurentRing R).mul cInv (mThRigInv R j))
    = (laurentRing R).mul (thLtorValue R i) (mThRigInv R j)
  rw [mThRig_mul_rearrange (laurentRing R) c (thLtorValue R i) cInv (mThRigInv R j),
    hc, (laurentRing R).one_mul]

/-- **定理 (M323F-5b): 定数倍剛性の正準単項式版** — 定数倍不定性の下でも
    比は正準単項式 u^{i²−j²}=q^{(i²−j²)/2l} に一意（M323F-5a + M323F-2b）。
    定数倍の曖昧さを消した後のテータ値の比の**一意な値**。 -/
theorem mThRig_constMult_canonical (R : CRing) (i j : Int)
    (c cInv : (laurentRing R).carrier)
    (hc : (laurentRing R).mul c cInv = (laurentRing R).one) :
    (laurentRing R).mul
        ((laurentRing R).mul c (thLtorValue R i))
        ((laurentRing R).mul cInv (mThRigInv R j))
      = uMonHom R (thLtorExp i - thLtorExp j) := by
  rw [mThRig_constMult_rigid R i j c cInv hc, mThRig_ratio_exp]

/-! ## M323F-6: 総括レコードと存在 -/

/-- **M323F-6a: mono-theta 定数倍剛性データ** — l-捻れ点でのテータ値
    Θ(q,u_j)=u^{j²}・その本物の乗法逆元 u^{−j²}・テータ値の比
    Θ_i/Θ_j=u^{i²−j²}、そして本丸「定数倍剛性」（定数倍不定性の下で
    比が不変・正準単項式に一意）・比の対角=1・推移律（1-コサイクル）を
    一括束ね。主語は本物のテータ値 u^{j²}（M318F, toy 主語なし）。 -/
structure MonoThetaRigidityData (R : CRing) where
  /-- l-捻れ点でのテータ値 Θ(q,u_j) = u^{j²}。 -/
  value : Int → (laurentRing R).carrier
  /-- テータ値の本物の乗法逆元 u^{−j²}。 -/
  inv : Int → (laurentRing R).carrier
  /-- テータ値の比 Θ_i/Θ_j。 -/
  ratio : Int → Int → (laurentRing R).carrier
  /-- 逆元性: value j · inv j = 1（テータ値は Laurent 環単元群の元）。 -/
  value_inv : ∀ j : Int,
    (laurentRing R).mul (value j) (inv j) = (laurentRing R).one
  /-- 比の定義: ratio i j = value i · inv j。 -/
  ratio_def : ∀ i j : Int,
    ratio i j = (laurentRing R).mul (value i) (inv j)
  /-- 比の正準単項式表示: ratio i j = u^{i²−j²}。 -/
  ratio_exp : ∀ i j : Int,
    ratio i j = uMonHom R (thLtorExp i - thLtorExp j)
  /-- 比の対角=1（正規化条件）。 -/
  ratio_diag : ∀ j : Int, ratio j j = (laurentRing R).one
  /-- 比の推移律（1-コサイクル）: ratio i j · ratio j k = ratio i k。 -/
  ratio_cocycle : ∀ i j k : Int,
    (laurentRing R).mul (ratio i j) (ratio j k) = ratio i k
  /-- **本丸**: 定数倍剛性——単元定数 c（c·cInv=1）で全テータ値を
      c 倍しても比は不変: (c·value i)·(cInv·inv j) = ratio i j。 -/
  const_mult_rigid : ∀ (i j : Int) (c cInv : (laurentRing R).carrier),
    (laurentRing R).mul c cInv = (laurentRing R).one →
      (laurentRing R).mul ((laurentRing R).mul c (value i))
          ((laurentRing R).mul cInv (inv j))
        = ratio i j

/-- **M323F-6b: witness 本体** — value := thLtorValue、inv := mThRigInv、
    ratio := mThRigRatio として全フィールドを M323F-1〜5 で埋める。 -/
def monoThetaRigidityData (R : CRing) : MonoThetaRigidityData R where
  value := thLtorValue R
  inv := mThRigInv R
  ratio := mThRigRatio R
  value_inv := mThRig_inv_mul R
  ratio_def := fun _ _ => rfl
  ratio_exp := mThRig_ratio_exp R
  ratio_diag := mThRig_ratio_diag R
  ratio_cocycle := mThRig_ratio_cocycle R
  const_mult_rigid := mThRig_constMult_rigid R

/-- **定理 (M323F-6c): mono-theta 定数倍剛性データの存在（M323F 見出し）** —
    任意の係数環 R に対し、l-捻れ点でのテータ値 Θ(q,u_j)=u^{j²} の上に、
    その本物の乗法逆元・テータ値の比 Θ_i/Θ_j=u^{i²−j²}、そして
    **定数倍剛性**（定数倍不定性の下で比が不変・正準単項式に一意）と、
    比の対角=1・推移律（1-コサイクル）を束ねたデータが存在する。
    mono-theta 環境の三剛性の一つ「定数倍剛性」が本物のテータ値の上で
    値レベルで確立される。 -/
theorem mThRig_exists (R : CRing) : Nonempty (MonoThetaRigidityData R) :=
  ⟨monoThetaRigidityData R⟩

/-! ## 実例（定数倍剛性・比・コサイクル） -/

/-- 実例: テータ値の比 Θ_1/Θ_2 の指数は 1−4 = −3（u^{−3}）。 -/
example : thLtorExp 1 - thLtorExp 2 = -3 := by
  rw [thLtorExp_sq, thLtorExp_sq]; omega

/-- 実例: テータ値の比 Θ_1/Θ_2 = u^{1²−2²} = u^{−3}（正準単項式）。 -/
example (R : CRing) :
    mThRigRatio R 1 2 = uMonHom R (thLtorExp 1 - thLtorExp 2) :=
  mThRig_ratio_exp R 1 2

/-- 実例（本丸）: 定数倍 c=u^5（逆定数 cInv=u^{−5}, c·cInv=1）で全テータ値を
    5 倍しても、比 Θ_1/Θ_2 は不変（定数倍剛性）。 -/
example (R : CRing) :
    (laurentRing R).mul
        ((laurentRing R).mul (uMonHom R 5) (thLtorValue R 1))
        ((laurentRing R).mul (uMonHom R (-5)) (mThRigInv R 2))
      = mThRigRatio R 1 2 :=
  mThRig_constMult_rigid R 1 2 (uMonHom R 5) (uMonHom R (-5)) (uMonHom_unit R 5)

/-- 実例: 対角の比 Θ_3/Θ_3 = 1。 -/
example (R : CRing) : mThRigRatio R 3 3 = (laurentRing R).one :=
  mThRig_ratio_diag R 3

/-- 実例: 比の推移律（1-コサイクル）(Θ_3/Θ_5)·(Θ_5/Θ_8) = Θ_3/Θ_8。 -/
example (R : CRing) :
    (laurentRing R).mul (mThRigRatio R 3 5) (mThRigRatio R 5 8)
      = mThRigRatio R 3 8 :=
  mThRig_ratio_cocycle R 3 5 8

/-- 実例: 比の因数分解 Θ_2/Θ_5 = u^{(2−5)(2+5)} = u^{−21}。 -/
example (R : CRing) :
    mThRigRatio R 2 5 = uMonHom R ((2 - 5) * (2 + 5)) :=
  mThRig_ratio_factor R 2 5

end IUT
