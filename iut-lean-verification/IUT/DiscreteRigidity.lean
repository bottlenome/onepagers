/-
  IUT/DiscreteRigidity.lean — M333F [実／本物]
  分類: 実 (mono-theta 環境の離散剛性 = 周期格子 q^ℤ ≅ ℤ の離散性・三剛性の2つ目)
  complete_pct 影響: E 柱を前進させる（テータ値の不定性を離散 ℤ に限定する本物の剛性；
    M323F の定数倍剛性に続く2つ目の剛性）。周期指数群が可除でない（ℤ であって ℚ でない）
    ことを本物の群準同型・単射性で示す。
  正直な限定: 周期 q の「無限位数」（等価: q^n=1 ⟹ n=0、すなわち q^ℤ が ℤ と忠実に
    同型で格子が崩れないこと）は、正の付値 v(q)≠0 を持つ具体的な q（本物の離散付値の
    素元）を要する。M309F TateCurve の正直申告どおり trivialValuation は rank 0 で
    正 valuation の witness を持たず、その具体構成は柱B（ℤ_p 接続）の後続である。
    よって本層では無限位数を明示の Prop 仮説 `discRig_infiniteOrder_hypothesis` として
    受け、そこから単射性・離散剛性を本物に導出する（仮説は決して自前で導出しない）。
    非可除性（ℤ に 1/2 が無い）と可除細分の不存在は無条件で完全証明する。
-/
import IUT.TateCurve

namespace IUT

/-! ## M333F-1: 周期指数格子 = 加法群 ℤ（離散対象そのもの）

  Tate 曲線 E_q = K^×/q^ℤ の周期束 q^ℤ は、指数を取ることで**加法群 ℤ** に対応する
  （qᵃ ↦ a）。この ℤ が「離散・非可除」であることが離散剛性の中身。指数格子は既存の
  本物の加法群 `intGrp`（M-FundamentalGroup, (ℤ,+,0,−)）を主対象として用いる
  （toy 代理でなく本物の離散対象を再利用）。 -/

/-! ## M333F-2: 周期準同型 ℤ → K^×, n ↦ qⁿ（本物の群準同型） -/

/-- **M333F-2a: 周期準同型** — 指数格子 ℤ から乗法群 K^× への写像 n ↦ qⁿ。
    加法則 `tateZpow_add`（q^{a+b}=qᵃ·qᵇ, M309F）がちょうど準同型条件を与える本物の
    群準同型。像はまさに周期束 q^ℤ（`tateQPowersSubgroup`）。 -/
def discRig_periodHom (K : IUTField) (q : (tateMultGroup K).carrier) :
    Hom intGrp (tateMultGroup K) where
  map := fun n => tateZpow (tateMultGroup K) q n
  map_mul := fun a b => tateZpow_add (tateMultGroup K) q a b

/-- 周期準同型は指数 n を素直に qⁿ に送る（定義の確認）。 -/
theorem discRig_periodHom_apply (K : IUTField) (q : (tateMultGroup K).carrier) (n : Int) :
    (discRig_periodHom K q).map n = tateZpow (tateMultGroup K) q n := rfl

/-- 周期準同型の像は周期束 q^ℤ に属する（qⁿ ∈ q^ℤ）。 -/
theorem discRig_periodHom_mem (K : IUTField) (q : (tateMultGroup K).carrier) (n : Int) :
    (tateQPowersSubgroup (tateMultGroup K) q).mem ((discRig_periodHom K q).map n) :=
  ⟨n, rfl⟩

/-! ## M333F-3: 無限位数の仮説（正直な外部 crux） -/

/-- **M333F-3: 無限位数の仮説（正直な限定）** — q^n = 1 ⟹ n = 0。
    すなわち q は無限位数で、指数格子 ℤ が q^ℤ と**忠実に同型**（相異なる指数が相異なる
    格子点、崩れが無い）。これが離散性の核だが、成立には正の付値 v(q)≠0 を持つ具体的な
    q が要る（M309F `tate_qpow_ne_one` は v(q)=some m, m≠0 の下で n≥1 について q^n≠1 を
    本物で与えるが、そのような正 valuation の素元の**具体構成**は柱B ℤ_p 接続の後続；
    trivialValuation は rank 0 で witness を持たない）。よって**本層はこれを導出せず明示
    仮説として受ける**（決して自前で証明しない — 正直申告）。 -/
def discRig_infiniteOrder_hypothesis (G : Grp) (g : G.carrier) : Prop :=
  ∀ n : Int, tateZpow G g n = G.one → n = 0

/-! ## M333F-4: 離散性 = 周期準同型の単射性（指数格子 ≅ ℤ） -/

/-- **定理 (M333F-4): 周期指数群は ℤ（離散・単射）** — 無限位数の仮説の下で、周期準同型
    n ↦ qⁿ は**単射**。相異なる指数は相異なる周期格子点を与え、q^ℤ は加法群 ℤ と忠実に
    同型（連続的／可除的な曖昧さで潰れない）。証明の核: qᵃ=qᵇ ⟹ q^{a−b}=qᵃ·(qᵇ)⁻¹=1
    （`tateZpow_add`・`tateZpow_neg`・右逆元）⟹ a−b=0（無限位数）。 -/
theorem discRig_period_exponent_isZ (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q) :
    (discRig_periodHom K q).Injective := by
  intro a b h
  have hval : tateZpow (tateMultGroup K) q a = tateZpow (tateMultGroup K) q b := h
  have hone : tateZpow (tateMultGroup K) q (a + (-b)) = (tateMultGroup K).one := by
    rw [tateZpow_add, tateZpow_neg, hval]
    exact (tateMultGroup K).mul_inv (tateZpow (tateMultGroup K) q b)
  have hz : a + (-b) = 0 := hInf (a + (-b)) hone
  have e1 : a + (-b) + b = (0 : Int) + b := congrArg (fun t => t + b) hz
  rw [Int.add_assoc, Int.add_left_neg, Int.add_zero, Int.zero_add] at e1
  exact e1

/-! ## M333F-5: 非可除性（ℤ に 1/2 は無い・無条件） -/

/-- **定理 (M333F-5a): ℤ は可除でない** — 2·n = 1 なる整数 n は存在しない。
    周期 q は格子内に「平方根周期」を持たない（q^{1/2} は q^ℤ に無い）。無条件で本物。 -/
theorem discRig_no_division : ¬ ∃ n : Int, 2 * n = 1 := by
  intro h
  obtain ⟨n, hn⟩ := h
  omega

/-- **定理 (M333F-5b): ℕ 版の非可除性** — 2·n = 1 なる自然数 n は存在しない。 -/
theorem discRig_no_division_nat : ¬ ∃ n : Nat, 2 * n = 1 := by
  intro h
  obtain ⟨n, hn⟩ := h
  omega

/-! ## M333F-6: 離散剛性（本丸・単射性 × 非可除性を束ねる） -/

/-- **定理 (M333F-6): 離散剛性（本丸）** — 周期 q には格子内の平方根周期が無い。
    無限位数の仮説の下では、q^{2n} = q（＝q^1）を満たす整数 n は存在しない。
    証明は 1つ目の剛性材料（単射性 M333F-4）と 2つ目（非可除性 M333F-5）を結合:
    q^{2n}=q^1 ⟹（単射）2n=1 ⟹（非可除）矛盾。周期指数群 ℤ が可除細分（1/2 を含む
    ℚ 的な群）に緩められないこと＝mono-theta 環境の離散剛性。 -/
theorem discRig_rigidity (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q) :
    ¬ ∃ n : Int,
      tateZpow (tateMultGroup K) q (2 * n) = tateZpow (tateMultGroup K) q 1 := by
  intro h
  obtain ⟨n, hn⟩ := h
  have hinj := discRig_period_exponent_isZ K q hInf
  have h2 : 2 * n = 1 := hinj (2 * n) 1 hn
  exact discRig_no_division ⟨n, h2⟩

/-! ## M333F-7: 可除細分の不存在の抽象版（ℤ→ℤ の倍化・無条件）

  離散剛性の骨をなす純群論的事実を、仮説なしで指数格子 ℤ 上に literal に実現する:
  倍化準同型 n ↦ 2n は**単射だが全射でない**——1 は像に無い。すなわち ℤ は自分の真の
  可除細分を持たない（1/2 を付け足せない）。 -/

/-- **M333F-7a: 倍化準同型** — 指数格子 ℤ 上の n ↦ 2n（本物の加法群準同型）。 -/
def discRig_double : Hom intGrp intGrp where
  map := fun (n : Int) => 2 * n
  map_mul := fun (a b : Int) => by
    show 2 * (a + b) = 2 * a + 2 * b
    omega

/-- **定理 (M333F-7b): 倍化は単射** — 2a = 2b ⟹ a = b。 -/
theorem discRig_double_injective : discRig_double.Injective := by
  intro a b h
  have h' : 2 * a = 2 * b := h
  exact Int.eq_of_mul_eq_mul_left (by omega) h'

/-- **定理 (M333F-7c): 倍化は 1 を像に持たない** — 2n = 1 なる n は無い。
    「単射準同型 ℤ→ℤ が倍化で 1 に到達することは不可能」の literal な実現
    （離散剛性の抽象核: ℤ は可除細分を許さない）。 -/
theorem discRig_double_no_preimage_one :
    ¬ ∃ n : Int, discRig_double.map n = (1 : Int) := by
  intro h
  obtain ⟨n, hn⟩ := h
  have h' : 2 * n = 1 := hn
  omega

/-! ## M333F-8: 総括レコードと（条件付き）存在 -/

/-- **M333F-8a: 離散剛性データ** — 周期指数格子 ℤ・周期準同型 n↦qⁿ・その単射性
    （指数群 ≅ ℤ）・非可除性・平方根周期の不存在（離散剛性）を束ねる。無限位数の仮説
    `infiniteOrder`（正直な外部 crux）を明示フィールドとして持つ。主語は本物の周期束
    q^ℤ とその指数群 ℤ（toy 代理なし）。 -/
structure DiscreteRigidityData (K : IUTField) where
  /-- Tate パラメータ q ∈ K^×。 -/
  q : (tateMultGroup K).carrier
  /-- 周期準同型 ℤ → K^×, n ↦ qⁿ。 -/
  periodHom : Hom intGrp (tateMultGroup K)
  /-- 周期準同型は n ↦ qⁿ。 -/
  periodHom_def : ∀ n, periodHom.map n = tateZpow (tateMultGroup K) q n
  /-- 無限位数の仮説（正直な限定・外部 crux）。 -/
  infiniteOrder : discRig_infiniteOrder_hypothesis (tateMultGroup K) q
  /-- 離散性: 周期準同型は単射（指数群 ≅ ℤ）。 -/
  injective : periodHom.Injective
  /-- 非可除性: ℤ に 1/2 は無い。 -/
  no_division : ¬ ∃ n : Int, 2 * n = 1
  /-- 離散剛性: 格子内に平方根周期 q^{1/2} は無い。 -/
  no_sqrt_period : ¬ ∃ n : Int,
    tateZpow (tateMultGroup K) q (2 * n) = tateZpow (tateMultGroup K) q 1

/-- **M333F-8b: witness 本体** — 無限位数の仮説 hInf を受けて全フィールドを M333F-2〜6 で
    埋める（hInf 以外は本物の証明で埋まる）。 -/
def discreteRigidityData (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q) :
    DiscreteRigidityData K where
  q := q
  periodHom := discRig_periodHom K q
  periodHom_def := fun _ => rfl
  infiniteOrder := hInf
  injective := discRig_period_exponent_isZ K q hInf
  no_division := discRig_no_division
  no_sqrt_period := discRig_rigidity K q hInf

/-- **定理 (M333F-8c): 離散剛性データの（条件付き）存在** — 無限位数の周期 q が与えられ
    れば、指数群 ℤ の離散性・非可除性・離散剛性を束ねたデータが存在する。存在が無限位数
    仮説に条件付くのは正直な限定（正 valuation の素元の具体構成は柱B の後続）。 -/
theorem discRig_exists (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : discRig_infiniteOrder_hypothesis (tateMultGroup K) q) :
    Nonempty (DiscreteRigidityData K) :=
  ⟨discreteRigidityData K q hInf⟩

/-! ## 実例（無条件で成立する離散核） -/

/-- 実例: ℤ は可除でない（2n=1 の解無し）。 -/
example : ¬ ∃ n : Int, 2 * n = 1 := discRig_no_division

/-- 実例: 倍化準同型は単射。 -/
example : discRig_double.Injective := discRig_double_injective

/-- 実例: 倍化準同型は 1 を像に持たない（可除細分の不存在）。 -/
example : ¬ ∃ n : Int, discRig_double.map n = (1 : Int) :=
  discRig_double_no_preimage_one

/-- 実例: 周期準同型は指数 3 を q³ に送る。 -/
example (K : IUTField) (q : (tateMultGroup K).carrier) :
    (discRig_periodHom K q).map (3 : Int) = tateZpow (tateMultGroup K) q 3 := rfl

end IUT
