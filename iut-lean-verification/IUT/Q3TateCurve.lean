/-
  IUT/Q3TateCurve.lean — A8a（柱A A8: 実 Tate 曲線 E_q(ℚ₃) = (3^ℤ×ℤ₃^×)/q^ℤ）

  ── 主要成果の分類: **[実／昇格(a)]**。M309F `TateCurve.lean` の退化 witness
     `tateCurveDataOne`（q=1・自明周期）と、無限位数 `tate_qpow_ne_one` の「正 valuation
     v(q)=some m≠0 を外部仮定で受け取る」骨格を、**実 ℚ₃^×（q3u 群提示 3^ℤ×ℤ₃^×）上の
     実 Tate パラメータ q = 3^m（実付値 v(q)=m≥1・実無限位数）へ昇格**する。
     商機構 quotientGroupN・tateQPowersSubgroup・tateNpow/tateZpow は M267F/M309F が
     Grp 一般で既に本物なのでそのまま消費し、IUTField 特化だった付値・正規性を実 ℚ₃ の
     実算術で discharge する。toy 主語なし——主語は実 q3tGrp = QpUnits 3（= 実 ℚ₃^× の
     群提示）と実 q3fValRel（実 ℤ 値付値）。

  complete_pct 影響: **A8 A8a を前進**（設計見込み A8 0.5→0.55・A8b と合わせ 0.6・
  柱A 46→47・独立監査確定が条件）。内容:
  (i)  実 Tate 曲線 E_q(ℚ₃) = ℚ₃^×/q^ℤ（q3tCurve）を quotientGroupN で本物構成、
  (ii) 実付値 v(q)=m≥1（q3t_q_val: q3fValRel を主語）——M309F 退化 witness q=1 の解消、
  (iii)q の実無限位数（q3t_q_pow_ne_one: 第1成分 m·n≠0・**外部付値仮定なし**）——
       M309F honest note「正 valuation witness 未達」の実 discharge、
  (iv) 周期性 [u]=[qu]（q3t_period）とその実 ℚ₃ 内での読み（q3t_period_real: q3u_embed_hom）、
  (v)  実付値公式 v(qⁿ)=m·n（q3t_qpow_val: q3f_val_mul の帰納）、
  (vi) 曲線上の非自明点 [−1]（q3t_point_ne_one: 実 −1∈ℤ₃^× で退化 witness の質的超克）、
  (vii)束ね q3tData（q=3 見出し実例）。

  正直な限定（§3 準拠・消去/弱化しない・既存 surrogate は消さない）:
  1. E_q の担体は**群提示 3^ℤ×ℤ₃^×**（q3uEmbed で ℚ₃ 内の部分群と単射同定・像の全射性は
     q3u_image_char の ∃ 形まで）。「文字通りの {x:ℚ₃//x≠0} の商」は total inv 不能ゆえ
     choice-free 不能（A2 の ∃形体性と同一ラインの恒久限定）。
  2. **p = 3 固定**・q ∈ 3^ℤ（q = 3^m・単数部込みの一般 q=3^m·u₀ は後続）。
  3. Weierstrass 模型（M304F）との同型（a₄(q),a₆(q) q-級数）・rigid 幾何・位相は皆無。
  4. Θ の E_q 上の実現は柱E 後続（M309F-7 の骨組み申告を継承）。torsion は A8b（q3tt）。
  5. TateCover 系（代理 π₁）とは未接続（実 π₁^ét は A4/A5）。cuspidalization 皆無・T_l 皆無。
  6. 既存 `TateCurve.lean`/`tateCurveDataOne`/TateCover 系は消さず併設（§2(a) 昇格の規約）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ（Classical.choice 無し）。
-/
import IUT.Q3UnitsGroup
import IUT.TateCurve

namespace IUT

/-! ## q3t-0: 主語の固定 — 実 ℚ₃^× 群提示 -/

/-- **q3t-0（★）: 実 Tate 曲線の主語群** ℚ₃^× = 3^ℤ × ℤ₃^×（q3u の群提示）。
    FullReciprocity の抽象直積代理を A2c-2 で実 ℚ₃ 上へ昇格したもの（q3uEmbed 単射同定）。 -/
@[reducible] def q3tGrp : Grp := QpUnits 3 isPrime_three

/-! ## q3t-1: 可換性 -/

/-- **q3t-1: ℚ₃^× は可換**（第1成分 ℤ 加法可換 × 第2成分 ℤ₃^× 可換 zpUnits_comm）。 -/
theorem q3t_comm (x y : q3tGrp.carrier) : q3tGrp.mul x y = q3tGrp.mul y x := by
  show (intGrp.mul x.1 y.1, (zpUnits 3 isPrime_three).mul x.2 y.2)
     = (intGrp.mul y.1 x.1, (zpUnits 3 isPrime_three).mul y.2 x.2)
  have h1 : intGrp.mul x.1 y.1 = intGrp.mul y.1 x.1 := Int.add_comm x.1 y.1
  rw [h1, zpUnits_comm 3 isPrime_three x.2 y.2]

/-! ## q3t-2: 可換群では任意部分群が正規 -/

/-- **q3t-2: 可換群 ℚ₃^× では任意の部分群が正規**（M309F tateQPowers_isNormal の
    Grp 一般化・可換性のみ使用）。 -/
theorem q3t_normal (H : Subgroup q3tGrp) : IsNormalSubgroup q3tGrp H := by
  intro g n hn
  have hconj : q3tGrp.mul (q3tGrp.mul g n) (q3tGrp.inv g) = n := by
    rw [q3t_comm g n, q3tGrp.mul_assoc, q3tGrp.mul_inv, q3tGrp.mul_one]
  rw [hconj]
  exact hn

/-! ## q3t-3: 実 Tate パラメータ q = 3^m と実付値証明書 -/

/-- **q3t-3a: 実 Tate パラメータ q = 3^m**（m≥1）— 第1成分 m（付値 m）・第2成分 単位。
    q3uEmbed で実 ℚ₃ の元 3^m に写る。 -/
def q3tQ (m : Nat) : q3tGrp.carrier := ((m : Int), (zpUnits 3 isPrime_three).one)

/-- **q3t-3b（★）: 実付値 v(q)=m**（q3fValRel を主語）— M309F 退化 witness q=1 を、
    実 ℤ 値付値 v(3^m)=m で discharge する初の実例。numerator 3^m·1 の厳密付値 m・
    denominator 3^0 で κ = m − 0 = m。 -/
theorem q3t_q_val (m : Nat) : q3fValRel (q3uEmbed (q3tQ m)) (m : Int) := by
  refine ⟨z3.mul (ringLocPow z3 q3fThree (m : Int).toNat) (zpOne 3),
         (-(m : Int)).toNat, (m : Int).toNat, rfl, ?_, ?_⟩
  · exact z3v_exact_mul (q3_pow_exact (m : Int).toNat) (q3u_unit_exact0 (q3tQ m).2.property)
  · omega

/-! ## q3t-4: 実 Tate 曲線 E_q(ℚ₃) と射影 -/

/-- **q3t-4a: q^ℤ 部分群**（M309F tateQPowersSubgroup を実 q3tGrp・実 q=3^m で消費）。 -/
def q3tSubgroup (m : Nat) : Subgroup q3tGrp := tateQPowersSubgroup q3tGrp (q3tQ m)

/-- **q3t-4b（★）: 実 Tate 曲線 E_q(ℚ₃) = ℚ₃^×/q^ℤ**（M267F quotientGroupN）。
    IUT のエタールテータが乗る中心対象を、実 ℚ₃^×・実 q=3^m の上で本物の商群として構成。 -/
def q3tCurve (m : Nat) : Grp :=
  quotientGroupN q3tGrp (q3tSubgroup m) (q3t_normal (q3tSubgroup m))

/-- **q3t-4c: 射影 ℚ₃^× → E_q**（全射準同型 quotientProjN）。 -/
def q3tProj (m : Nat) : Hom q3tGrp (q3tCurve m) :=
  quotientProjN q3tGrp (q3tSubgroup m) (q3t_normal (q3tSubgroup m))

/-- **q3t-4d: 射影は全射**。 -/
theorem q3tProj_surjective (m : Nat) : ∀ x, ∃ a, (q3tProj m).map a = x :=
  quotientProjN_surjective q3tGrp (q3tSubgroup m) (q3t_normal (q3tSubgroup m))

/-- **q3t-4e: E_q はアーベル群**（可換群 ℚ₃^× の商）。 -/
theorem q3tCurve_abelian (m : Nat) :
    ∀ x y : (q3tCurve m).carrier, (q3tCurve m).mul x y = (q3tCurve m).mul y x := by
  intro x y
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  show Quot.mk _ (q3tGrp.mul a b) = Quot.mk _ (q3tGrp.mul b a)
  rw [q3t_comm a b]

/-! ## q3t-5: 周期性 [u]=[qu] と実 ℚ₃ 内での読み -/

/-- **q3t-5a（★）: 周期性 [u] = [qu]**（Tate 曲線の本質）— q^ℤ で割ることで u と qu が
    E_q(ℚ₃) 上で同一点になる。証明の核: u⁻¹·(q·u) = q ∈ q^ℤ（可換性で整理）。 -/
theorem q3t_period (m : Nat) (x : q3tGrp.carrier) :
    (q3tProj m).map x = (q3tProj m).map (q3tGrp.mul (q3tQ m) x) := by
  apply Quot.sound
  show (q3tSubgroup m).mem
      (q3tGrp.mul (q3tGrp.inv x) (q3tGrp.mul (q3tQ m) x))
  have heq : q3tGrp.mul (q3tGrp.inv x) (q3tGrp.mul (q3tQ m) x) = q3tQ m := by
    rw [q3t_comm (q3tQ m) x, ← q3tGrp.mul_assoc, q3tGrp.inv_mul, q3tGrp.one_mul]
  rw [heq]
  exact tate_gen_mem q3tGrp (q3tQ m)

/-- **q3t-5b（★）: 周期を実 ℚ₃ の中で読む証明書** — 商での同一視 [u]=[qu] は、
    実 ℚ₃ の元 u と 3^m·u の同一視である（q3u_embed_hom の実消費）。 -/
theorem q3t_period_real (m : Nat) (x : q3tGrp.carrier) :
    q3uEmbed (q3tGrp.mul (q3tQ m) x)
      = q3Ring.mul (q3uEmbed (q3tQ m)) (q3uEmbed x) :=
  q3u_embed_hom (q3tQ m) x

/-! ## q3t-6: q の実無限位数（外部付値仮定なし） -/

/-- q^n の第1成分（付値部）の成分計算: (qⁿ).1 = m·n（帰納・intGrp 加法）。 -/
theorem q3t_npow_fst (m : Nat) : ∀ n : Nat,
    (tateNpow q3tGrp (q3tQ m) n).1 = (m : Int) * (n : Int) := by
  intro n
  induction n with
  | zero =>
    show (0 : Int) = (m : Int) * ((0 : Nat) : Int)
    omega
  | succ k ih =>
    show (tateNpow q3tGrp (q3tQ m) k).1 + (m : Int) = (m : Int) * ((k + 1 : Nat) : Int)
    rw [ih]
    have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [hcast, Int.mul_add, Int.mul_one]

/-- **q3t-6a（★）: q の実無限位数** — q^n ≠ 1（m,n≥1）を、第1成分 m·n≠0 の
    実算術で閉じる。**外部付値仮定を一切使わない**——M309F `tate_qpow_ne_one`
    の「正 valuation の witness を外部入力」を実 ℚ₃^× の中で discharge する。 -/
theorem q3t_q_pow_ne_one (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    tateNpow q3tGrp (q3tQ m) n ≠ q3tGrp.one := by
  intro hc
  have h1 : (tateNpow q3tGrp (q3tQ m) n).1 = q3tGrp.one.1 := congrArg Prod.fst hc
  rw [q3t_npow_fst m n] at h1
  have h0 : q3tGrp.one.1 = (0 : Int) := rfl
  rw [h0] at h1
  have hm' : (m : Int) ≠ 0 := by omega
  have hn' : (n : Int) ≠ 0 := by omega
  exact (Int.mul_ne_zero hm' hn') h1

/-- **q3t-6b（★）: 実付値公式 v(qⁿ)=m·n**（M309F-6 tate_qpow_val の実 ℚ₃ 版）。
    q3f_val_mul と q3t_q_val の帰納。 -/
theorem q3t_qpow_val (m : Nat) : ∀ n : Nat,
    q3fValRel (q3uEmbed (tateNpow q3tGrp (q3tQ m) n)) ((m : Int) * (n : Int)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨z3.mul (ringLocPow z3 q3fThree 0) (zpOne 3), 0, 0, rfl, ?_, ?_⟩
    · exact z3v_exact_mul (q3_pow_exact 0) (q3u_unit_exact0 (q3tQ m).2.property)
    · omega
  | succ k ih =>
    show q3fValRel (q3uEmbed (q3tGrp.mul (tateNpow q3tGrp (q3tQ m) k) (q3tQ m)))
        ((m : Int) * ((k + 1 : Nat) : Int))
    rw [q3u_embed_hom (tateNpow q3tGrp (q3tQ m) k) (q3tQ m)]
    have hstep := q3f_val_mul ih (q3t_q_val m)
    have harith : (m : Int) * ((k + 1 : Nat) : Int)
        = (m : Int) * (k : Int) + (m : Int) := by
      have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hcast, Int.mul_add, Int.mul_one]
    rw [harith]
    exact hstep

/-! ## q3t-7: 実 −1 ∈ ℤ₃^×（非自明点の分離部品・A8b μ₂ と共用） -/

/-- 3 は −1 を割らない（Int・natAbs 経由）。 -/
theorem q3t_three_not_dvd_neg_one : ¬ ((3 : Nat) : Int) ∣ (-1 : Int) := by
  intro h
  have h1 : ((3 : Nat) : Int).natAbs ∣ ((-1 : Int)).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_natCast] at h1
  have h2 : (3 : Nat) ∣ ((-1 : Int)).natAbs := h1
  have h3 : ((-1 : Int)).natAbs = 1 := rfl
  rw [h3] at h2
  have := Nat.le_of_dvd (by omega) h2
  omega

/-- **q3t-7a: 実 −1 ∈ ℤ₃^×** — 対角埋め込み (toZp 3).map(−1)・レベル1 剰余 [−1]・
    ¬3∣(−1) で単数性。A8b の μ₂={±1} と共用の部品。 -/
def q3tNegOne : (zpUnits 3 isPrime_three).carrier :=
  ⟨(toZp 3).map (-1), ⟨-1, rfl, q3t_three_not_dvd_neg_one⟩⟩

/-- **q3t-7b: (−1)² = 1**（環準同型 toZpRing の乗法保存 + (−1)·(−1)=1）。 -/
theorem q3tNegOne_sq :
    (zpUnits 3 isPrime_three).mul q3tNegOne q3tNegOne
      = (zpUnits 3 isPrime_three).one := by
  apply Subtype.ext
  show zpMul 3 ((toZp 3).map (-1)) ((toZp 3).map (-1)) = zpOne 3
  have h := (toZpRing 3).map_mul (-1 : Int) (-1 : Int)
  have hone : intRing.mul (-1 : Int) (-1 : Int) = intRing.one := by
    show (-1 : Int) * (-1) = (1 : Int); omega
  rw [hone, (toZpRing 3).map_one] at h
  exact h.symm

/-- **q3t-7c: −1 ≠ 1 ∈ ℤ₃^×**（レベル1 で −1 ≢ 1 mod 3）。 -/
theorem q3t_negone_ne_one : q3tNegOne ≠ (zpUnits 3 isPrime_three).one := by
  intro h
  have hval : ((toZp 3).map (-1)) = zpOne 3 := congrArg Subtype.val h
  have hlev : ((toZp 3).map (-1)).val 1 = (zpOne 3).val 1 :=
    congrArg (fun z => z.val 1) hval
  have hq : Quot.mk (modCong (3 ^ 1)).rel (-1 : Int)
      = Quot.mk (modCong (3 ^ 1)).rel (1 : Int) := hlev
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (3 ^ 1)) hq
  rw [Nat.pow_one] at hk
  omega

/-! ## q3t-8: 曲線上の非自明点（退化 witness の質的超克） -/

/-- q^ℤ の元は第2成分（単数部）が常に 1（帰納・prodGrp 成分計算）。 -/
theorem q3t_npow_snd_of (g : q3tGrp.carrier)
    (hg : g.2 = (zpUnits 3 isPrime_three).one) : ∀ n : Nat,
    (tateNpow q3tGrp g n).2 = (zpUnits 3 isPrime_three).one := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show (zpUnits 3 isPrime_three).mul (tateNpow q3tGrp g k).2 g.2
        = (zpUnits 3 isPrime_three).one
    rw [ih, hg]
    exact (zpUnits 3 isPrime_three).one_mul (zpUnits 3 isPrime_three).one

/-- 単位元の逆元は単位元（ℤ₃^×）。 -/
theorem q3t_inv_one :
    (zpUnits 3 isPrime_three).inv (zpUnits 3 isPrime_three).one
      = (zpUnits 3 isPrime_three).one := by
  have h1 := (zpUnits 3 isPrime_three).inv_mul (zpUnits 3 isPrime_three).one
  rw [(zpUnits 3 isPrime_three).mul_one] at h1
  exact h1

/-- q^ℤ の整数冪も第2成分が常に 1（負冪は inv(q) の冪・inv one = one）。 -/
theorem q3t_zpow_snd (m : Nat) (t : Int) :
    (tateZpow q3tGrp (q3tQ m) t).2 = (zpUnits 3 isPrime_three).one := by
  cases t with
  | ofNat n => exact q3t_npow_snd_of (q3tQ m) rfl n
  | negSucc n =>
    show (tateNpow q3tGrp (q3tGrp.inv (q3tQ m)) (n + 1)).2
        = (zpUnits 3 isPrime_three).one
    exact q3t_npow_snd_of (q3tGrp.inv (q3tQ m)) q3t_inv_one (n + 1)

/-- **q3t-8（★）: 曲線上の非自明点 [(0,−1)] ≠ [1]** — E_q(ℚ₃) の点として
    実 −1∈ℤ₃^× が与える点が単位元と異なる。M309F 退化 witness（E=K^×/⟨1⟩ で
    周期自明）の**質的超克**: q^ℤ の元は第2成分 1 なのに (0,−1) は −1、
    q3t_negone_ne_one で矛盾。 -/
theorem q3t_point_ne_one (m : Nat) (hm : 1 ≤ m) :
    (q3tProj m).map ((0 : Int), q3tNegOne) ≠ (q3tCurve m).one := by
  intro h
  have hmem := (quotientProjN_ker q3tGrp (q3tSubgroup m)
    (q3t_normal (q3tSubgroup m)) ((0 : Int), q3tNegOne)).mp h
  obtain ⟨t, ht⟩ := hmem
  have hsnd : (tateZpow q3tGrp (q3tQ m) t).2 = ((0 : Int), q3tNegOne).2 :=
    congrArg Prod.snd ht
  rw [q3t_zpow_snd m t] at hsnd
  exact q3t_negone_ne_one hsnd.symm

/-! ## q3t-9: capstone -/

/-- **q3t-9a: 実 Tate 曲線データ** — 実 q=3^m（実付値 v(q)=m≥1・実無限位数）・
    実 E_q(ℚ₃)=ℚ₃^×/q^ℤ（アーベル・周期性）・非自明点を束ねる。 -/
structure Q3TateCurveData where
  /-- Tate パラメータの指数 m（q = 3^m）。 -/
  m : Nat
  /-- m ≥ 1（真の退化パラメータ）。 -/
  hm : 1 ≤ m
  /-- 実付値 v(q) = m ≥ 1（q3fValRel）。 -/
  q_val : q3fValRel (q3uEmbed (q3tQ m)) (m : Int)
  /-- E_q はアーベル群。 -/
  abelian : ∀ x y : (q3tCurve m).carrier,
    (q3tCurve m).mul x y = (q3tCurve m).mul y x
  /-- q の実無限位数（外部付値仮定なし）。 -/
  q_infinite : ∀ n, 1 ≤ n → tateNpow q3tGrp (q3tQ m) n ≠ q3tGrp.one
  /-- 周期性 [u]=[qu]。 -/
  period : ∀ x, (q3tProj m).map x = (q3tProj m).map (q3tGrp.mul (q3tQ m) x)
  /-- 曲線上の非自明点 [−1]。 -/
  point_nontrivial : (q3tProj m).map ((0 : Int), q3tNegOne) ≠ (q3tCurve m).one

/-- **q3t-9b: 見出し実例 q = 3**（m=1・v(q)=1）— 実 Tate 曲線 E₃(ℚ₃)=ℚ₃^×/3^ℤ。 -/
def q3tData : Q3TateCurveData where
  m := 1
  hm := Nat.le_refl 1
  q_val := q3t_q_val 1
  abelian := q3tCurve_abelian 1
  q_infinite := fun n hn => q3t_q_pow_ne_one 1 n (Nat.le_refl 1) hn
  period := q3t_period 1
  point_nontrivial := q3t_point_ne_one 1 (Nat.le_refl 1)

/-- **q3t-9c: 実 Tate 曲線の存在**（実 ℚ₃^×・実 q=3^m・m≥1）。 -/
theorem q3tCurve_exists : Nonempty Q3TateCurveData := ⟨q3tData⟩

end IUT
