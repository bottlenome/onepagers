/-
  IUT/Q3RatEmbed.lean — A2c-3（柱A2: 実 p 進局所体 — ℚ↪ℚ₃ 環準同型）

  ── 主要成果の分類: **[実／(a) 昇格]**。A2 設計文書 §5.2 が名指しした named 残欠
     A2c-3（ℚ↪ℚ₃ 環準同型）を本物 discharge する。既存の実 ℚ（ratRing = QRat・
     交差積 Quot 商）・実 ℚ₃（q3Ring = ℤ₃[1/3] = ringLocRf z3 q3fThree）・実 ℤ₃ 単数逆元
     zpUnitInv（choice-free）・実 ℤ 稠密 z3c_int_dense の上に、**実環準同型
     ratRing → q3Ring** をゼロから構成する。toy 主語なし。主語は実 ratRing・実 q3Ring。

  complete_pct 影響: **A2 の named 残欠 A2c-3 を discharge**（prior A2=0.65 は整数付値
  一致どまりで ℚ→ℚ₃ の埋め込みが皆無だった）。ここで初めて「K_v は K の完備化」の
  物語が実接続する。設計予測 A2 0.65→(監査確定・+0.02〜0.04)。表示 55 の閾値は
  A2（weight 8）で banker 丸め Σ_A=54.50→54 の罠があり +0.03 で越える（監査確定）。

  * q3reSplit           — 分母 n の 3 冪分解 n=3^w·d'（3∤d'・choice-free 強再帰・データ）
  * q3re_unit           — 3∤d' ⟹ zimg d' は ℤ₃-単数（IsZpUnit）
  * q3reQ               — ℤ→ℚ₃ 合成環準同型（a↦a/1・hom 補題）
  * q3reFracOf/q3reFrac/q3reMap — **★実環準同型 ratRing→q3Ring**（a/b ↦ a·d'⁻¹/3^w）
  * q3re_frac_spec      — 特徴付け方程式 image·q3reQ(den)=q3reQ(num)（well-def の要）
  * q3re_map_add/mul/one/zero — **環準同型性**（spec＋単数消去で降下）
  * q3re_map_inj        — 非零有理数 ↦ 非零（ℤ→ℤ₃ 分離 toZp_injective 消費）
  * q3re_val_compat     — **v₃(a/b)=v₃(a)−v₃(b)**（q3fValRel 形・z3c_val_compat 消費）
  * q3re_int_compat     — ℤ→ℚ→ℚ₃ = ℤ→ℤ₃→ℚ₃（三角可換）
  * q3re_dense          — ℚ（の整数像）は ℤ₃⊂ℚ₃ で稠密（z3c_int_dense 消費・modulus 形）
  * Q3RatEmbedData      — 総括レコード

  正直な限定（§3 準拠・消去/弱化しない）:
  - **ℚ₃ はなお total-inverse IUTField ではない**（A2 恒久限定を継承）: 本埋め込みは
    ∃-inverse を持つ CRing q3Ring への**環準同型**であって体射ではない。逆元の全域化は
    x≠0 の witness 抽出（Markov）を要し choice-free に不能。
  - **稠密性は modulus 形のみ**（z3c_int_dense の系）。ℚ₃ の位相・完備性そのものは範囲外。
    full ℚ-density（3 冪分母付き q3Ring 距離での）は主張せず、**ℤ₃⊂ℚ₃ での整数像稠密**
    （埋め込み経由で ℚ 像が稠密）に honest スコープする。
  - **p = 3 固定**・基礎体 ℚ のみ。ℚ₃ 上の位相・G_{ℚ₃}・分岐は範囲外（後続）。
  - 実 ratRing・実 q3Ring・zpUnitInv・z3c_int_dense は既存（新設せず消費）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。
-/
import IUT.Q3LocalField
import IUT.Rationals
import IUT.Zp3Complete
import IUT.ZpUnits

namespace IUT

/-! ## A2c-3-0: ℤ→ℤ₃ 像と ℤ→ℚ₃ 合成環準同型 -/

/-- ℤ の元 a の ℤ₃ 内像（対角埋め込み）。 -/
@[reducible] def zimg (a : Int) : z3.carrier := (toZpRing 3).map a

/-- ℤ→ℤ₃ 像の加法性。 -/
theorem zimg_add (a b : Int) : zimg (a + b) = z3.add (zimg a) (zimg b) :=
  (toZpRing 3).map_add a b

/-- ℤ→ℤ₃ 像の乗法性。 -/
theorem zimg_mul (a b : Int) : zimg (a * b) = z3.mul (zimg a) (zimg b) :=
  (toZpRing 3).map_mul a b

/-- ℤ→ℤ₃ 像は 1 を保存。 -/
theorem zimg_one : zimg 1 = z3.one := (toZpRing 3).map_one

/-- ℤ→ℚ₃ の合成像 a ↦ a/1（ringLocMap ∘ toZpRing）。 -/
@[reducible] def q3reQ (a : Int) : q3Ring.carrier :=
  (ringLocMap z3 q3S).map (zimg a)

/-- q3reQ は加法保存。 -/
theorem q3reQ_add (a b : Int) :
    q3reQ (a + b) = q3Ring.add (q3reQ a) (q3reQ b) := by
  show (ringLocMap z3 q3S).map (zimg (a + b))
    = q3Ring.add ((ringLocMap z3 q3S).map (zimg a)) ((ringLocMap z3 q3S).map (zimg b))
  rw [zimg_add]
  exact (ringLocMap z3 q3S).map_add (zimg a) (zimg b)

/-- q3reQ は乗法保存。 -/
theorem q3reQ_mul (a b : Int) :
    q3reQ (a * b) = q3Ring.mul (q3reQ a) (q3reQ b) := by
  show (ringLocMap z3 q3S).map (zimg (a * b))
    = q3Ring.mul ((ringLocMap z3 q3S).map (zimg a)) ((ringLocMap z3 q3S).map (zimg b))
  rw [zimg_mul]
  exact (ringLocMap z3 q3S).map_mul (zimg a) (zimg b)

/-- q3reQ は 1 を保存。 -/
theorem q3reQ_one : q3reQ 1 = q3Ring.one := by
  show (ringLocMap z3 q3S).map (zimg 1) = q3Ring.one
  rw [zimg_one]
  exact (ringLocMap z3 q3S).map_one

/-- ℤ₃ 内で 0 の像は 0。 -/
theorem zimg_zero : zimg 0 = z3.zero := by
  apply Subtype.ext
  funext n
  rfl

/-- q3reQ は 0 を保存。 -/
theorem q3reQ_zero : q3reQ 0 = q3Ring.zero := by
  show (ringLocMap z3 q3S).map (zimg 0) = q3Ring.zero
  rw [zimg_zero]
  rfl

/-! ## A2c-3-1: 分母の 3 冪分解 n = 3^w · d'（3∤d'・choice-free） -/

/-- **A2c-3-1a: 3 冪分解データ** n = 3^w·d'（3∤d'）。強再帰でデータとして構成する
    ため Exists でなく構造体で持つ（choice 回避）。 -/
structure Q3Split (n : Nat) where
  /-- 3 進付値 w = v₃(n)。 -/
  w : Nat
  /-- 3 と素な余因子 d'。 -/
  d : Nat
  /-- n = 3^w·d'。 -/
  eq : n = 3 ^ w * d
  /-- 3∤d'。 -/
  ndvd : ¬ (3 ∣ d)

/-- **A2c-3-1b（★）: 分母の 3 冪分解**（1≤n の強再帰・データ・choice-free）。
    prime_pow_extract と同じ再帰だが Exists でなく Q3Split を返す。 -/
noncomputable def q3reSplit : ∀ (n : Nat), 1 ≤ n → Q3Split n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    cases Nat.decidable_dvd 3 n with
    | isFalse hnd => exact ⟨0, n, (Nat.one_mul n).symm, hnd⟩
    | isTrue hd =>
      have hn1 : n = 3 * (n / 3) := (Nat.mul_div_cancel' hd).symm
      have hn1pos : 1 ≤ n / 3 := by
        cases Nat.eq_zero_or_pos (n / 3) with
        | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hn1; omega
        | inr hp => exact hp
      have hlt : n / 3 < n := by
        have hmm : 1 * (n / 3) < 3 * (n / 3) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        calc n / 3 = 1 * (n / 3) := (Nat.one_mul (n / 3)).symm
          _ < 3 * (n / 3) := hmm
          _ = n := hn1.symm
      have sub := ih (n / 3) hlt hn1pos
      refine ⟨sub.w + 1, sub.d, ?_, sub.ndvd⟩
      calc n = 3 * (n / 3) := hn1
        _ = 3 * (3 ^ sub.w * sub.d) := congrArg (fun z => 3 * z) sub.eq
        _ = 3 ^ (sub.w + 1) * sub.d := by
            rw [Nat.pow_succ, Nat.mul_comm (3 ^ sub.w) 3, Nat.mul_assoc]

/-- **A2c-3-1c: 3∤d' ⟹ ℤ₃-単数** — 余因子の像は ℤ₃ の単数。 -/
theorem q3re_unit (d : Nat) (hd : ¬ (3 ∣ d)) : IsZpUnit 3 (zimg (d : Int)) := by
  refine ⟨(d : Int), rfl, ?_⟩
  intro h
  exact hd (Int.ofNat_dvd.mp h)

/-! ## A2c-3-2: 分解の再合成と単数の付値 -/

/-- 3 の ℤ₃ 像は q3fThree。 -/
theorem zimg_three : (toZpRing 3).map ((3 : Nat) : Int) = q3fThree := rfl

/-- Nat 3 冪の像は ℤ₃ 内の 3 冪 ringLocPow。 -/
theorem zimg_natpow3 (w : Nat) :
    (toZpRing 3).map (((3 ^ w : Nat)) : Int) = ringLocPow z3 q3fThree w := by
  induction w with
  | zero =>
    have h0 : ((3 ^ 0 : Nat) : Int) = intRing.one := by rw [Nat.pow_zero]; rfl
    show (toZpRing 3).map (((3 ^ 0 : Nat)) : Int) = ringLocPow z3 q3fThree 0
    rw [h0]
    exact (toZpRing 3).map_one
  | succ w ih =>
    have hc : ((3 ^ (w + 1) : Nat) : Int)
        = intRing.mul ((3 ^ w : Nat) : Int) ((3 : Nat) : Int) := by
      rw [Nat.pow_succ, Int.natCast_mul]; rfl
    show (toZpRing 3).map (((3 ^ (w + 1) : Nat)) : Int) = ringLocPow z3 q3fThree (w + 1)
    rw [hc, (toZpRing 3).map_mul, ih, zimg_three]
    exact z3.mul_comm (ringLocPow z3 q3fThree w) q3fThree

/-- **A2c-3-2a: 分母の再合成** — n=3^w·d' なら zimg(n) = 3^w · zimg(d')。 -/
theorem q3re_den_recompose (n : Nat) (sp : Q3Split n) :
    zimg (n : Int) = z3.mul (ringLocPow z3 q3fThree sp.w) (zimg (sp.d : Int)) := by
  have hcast : (n : Int)
      = intRing.mul ((3 ^ sp.w : Nat) : Int) ((sp.d : Nat) : Int) := by
    have h1 : (n : Int) = ((3 ^ sp.w * sp.d : Nat) : Int) := by rw [← sp.eq]
    rw [h1, Int.natCast_mul]; rfl
  show (toZpRing 3).map (n : Int)
    = z3.mul (ringLocPow z3 q3fThree sp.w) (zimg (sp.d : Int))
  rw [hcast, (toZpRing 3).map_mul, zimg_natpow3]

/-- 単数は厳密付値 0（レベル 1 非零）。 -/
theorem z3v_unit_exact0 (x : z3.carrier) (hu : IsZpUnit 3 x) : z3vExact 3 x 0 := by
  refine ⟨z3vGe_zero 3 x, ?_⟩
  intro hge
  obtain ⟨a, hval, hnd⟩ := hu
  have h1 : Quot.mk (modCong (3 ^ 1)).rel a = Quot.mk (modCong (3 ^ 1)).rel 0 := by
    rw [← hval]; exact hge
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (3 ^ 1)) h1
  apply hnd
  rw [Nat.pow_one] at hk
  exact ⟨-k, by omega⟩

/-! ## A2c-3-3: 実環準同型 ratRing → q3Ring -/

/-- **A2c-3-3a: 分解付き表現子写像** a/n ↦ (a·d'⁻¹)/3^w（sp : n=3^w·d'・3∤d'）。
    d' の逆元は ℤ₃ 単数逆元 zpUnitInv（choice-free）。 -/
def q3reFracOf {n : Nat} (a : Int) (sp : Q3Split n) : q3Ring.carrier :=
  Quot.mk (ringLocRel q3S)
    ⟨z3.mul (zimg a)
        (zpUnitInv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd)),
      ringLocPow z3 q3fThree sp.w, ⟨sp.w, rfl⟩⟩

/-- **A2c-3-3b（★特徴付け方程式）: image·q3reQ(n) = q3reQ(a)**。well-def と環準同型性の要石。 -/
theorem q3re_fracOf_spec {n : Nat} (a : Int) (sp : Q3Split n) :
    q3Ring.mul (q3reFracOf a sp) (q3reQ (n : Int)) = q3reQ a := by
  have hrec : zimg (n : Int)
      = z3.mul (ringLocPow z3 q3fThree sp.w) (zimg (sp.d : Int)) :=
    q3re_den_recompose n sp
  have huinv : z3.mul
      (zpUnitInv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd))
      (zimg (sp.d : Int)) = z3.one :=
    zpUnitInv_mul 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd)
  show Quot.mk (ringLocRel q3S)
      (ringLocMul
        ⟨z3.mul (zimg a)
            (zpUnitInv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd)),
          ringLocPow z3 q3fThree sp.w, ⟨sp.w, rfl⟩⟩
        (ringLocOfElem (zimg (n : Int))))
    = Quot.mk (ringLocRel q3S) (ringLocOfElem (zimg a))
  apply Quot.sound
  refine ⟨z3.one, q3S.one_mem, ?_⟩
  show z3.mul z3.one
      (z3.mul (z3.mul (z3.mul (zimg a)
        (zpUnitInv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd)))
          (zimg (n : Int))) z3.one)
    = z3.mul z3.one (z3.mul (zimg a)
        (z3.mul (ringLocPow z3 q3fThree sp.w) z3.one))
  rw [z3.one_mul, z3.one_mul,
    cring_mul_one z3 (z3.mul (z3.mul (zimg a)
      (zpUnitInv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd)))
        (zimg (n : Int))),
    hrec,
    cring_mul_mul_swap' z3 (zimg a)
      (zpUnitInv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd))
      (ringLocPow z3 q3fThree sp.w) (zimg (sp.d : Int)),
    huinv, cring_mul_one z3 (z3.mul (zimg a) (ringLocPow z3 q3fThree sp.w)),
    cring_mul_one z3 (ringLocPow z3 q3fThree sp.w)]

/-- 正分母の natAbs は正。 -/
theorem q3reHden (x : PreRat) : 1 ≤ x.den.natAbs :=
  natAbs_pos_of_ne (by have := x.den_pos; omega)

/-- **A2c-3-3c: 表現子上の埋め込み**（分解を q3reSplit で供給）。 -/
noncomputable def q3reFrac (a : Int) (n : Nat) (hn : 1 ≤ n) : q3Ring.carrier :=
  q3reFracOf a (q3reSplit n hn)

/-- q3reFrac の特徴付け方程式。 -/
theorem q3re_frac_spec (a : Int) (n : Nat) (hn : 1 ≤ n) :
    q3Ring.mul (q3reFrac a n hn) (q3reQ (n : Int)) = q3reQ a :=
  q3re_fracOf_spec a (q3reSplit n hn)

/-! ## A2c-3-4: 単数消去と単位性 -/

/-- 単数右消去: c·inv=1, A·c=B·c ⟹ A=B。 -/
theorem q3_unit_cancel (c inv A B : q3Ring.carrier)
    (hc : q3Ring.mul c inv = q3Ring.one)
    (h : q3Ring.mul A c = q3Ring.mul B c) : A = B := by
  have hA : q3Ring.mul A (q3Ring.mul c inv) = A := by
    rw [hc, cring_mul_one]
  have hB : q3Ring.mul B (q3Ring.mul c inv) = B := by
    rw [hc, cring_mul_one]
  rw [← hA, ← hB, ← q3Ring.mul_assoc, ← q3Ring.mul_assoc, h]

/-- 正整数の像は q3Ring の単元（逆元 = 逆有理数の像）。 -/
theorem q3reQ_unit_pos (m : Int) (hm : 0 < m) :
    ∃ inv : q3Ring.carrier, q3Ring.mul (q3reQ m) inv = q3Ring.one := by
  have hmn : ((m.natAbs : Nat) : Int) = m := Int.natAbs_of_nonneg (Int.le_of_lt hm)
  refine ⟨q3reFrac 1 m.natAbs (natAbs_pos_of_ne (by omega)), ?_⟩
  have hspec := q3re_frac_spec 1 m.natAbs (natAbs_pos_of_ne (by omega))
  rw [hmn, q3reQ_one] at hspec
  rw [q3Ring.mul_comm (q3reQ m) (q3reFrac 1 m.natAbs (natAbs_pos_of_ne (by omega)))]
  exact hspec

/-! ## A2c-3-5: 実環準同型 ratRing → q3Ring -/

/-- **A2c-3-5（★）: 実環準同型 ratRing → q3Ring**（表現子写像の Quot.lift）。 -/
noncomputable def q3reMap : ratRing.carrier → q3Ring.carrier :=
  Quot.lift (fun x => q3reFrac x.num x.den.natAbs (q3reHden x))
    (fun x x' h => by
      have hdx : ((x.den.natAbs : Nat) : Int) = x.den :=
        Int.natAbs_of_nonneg (Int.le_of_lt x.den_pos)
      have hdx' : ((x'.den.natAbs : Nat) : Int) = x'.den :=
        Int.natAbs_of_nonneg (Int.le_of_lt x'.den_pos)
      have specA : q3Ring.mul (q3reFrac x.num x.den.natAbs (q3reHden x)) (q3reQ x.den)
          = q3reQ x.num := by
        have := q3re_frac_spec x.num x.den.natAbs (q3reHden x)
        rw [hdx] at this; exact this
      have specB : q3Ring.mul (q3reFrac x'.num x'.den.natAbs (q3reHden x')) (q3reQ x'.den)
          = q3reQ x'.num := by
        have := q3re_frac_spec x'.num x'.den.natAbs (q3reHden x')
        rw [hdx'] at this; exact this
      have hpos : (0 : Int) < x.den * x'.den := Int.mul_pos x.den_pos x'.den_pos
      obtain ⟨inv, hinv⟩ := q3reQ_unit_pos (x.den * x'.den) hpos
      have hrel : x.num * x'.den = x'.num * x.den := h
      have hAU : q3Ring.mul (q3reFrac x.num x.den.natAbs (q3reHden x))
          (q3reQ (x.den * x'.den)) = q3reQ (x.num * x'.den) := by
        rw [q3reQ_mul x.den x'.den, ← q3Ring.mul_assoc, specA, ← q3reQ_mul]
      have hBU : q3Ring.mul (q3reFrac x'.num x'.den.natAbs (q3reHden x'))
          (q3reQ (x.den * x'.den)) = q3reQ (x'.num * x.den) := by
        rw [show x.den * x'.den = x'.den * x.den from Int.mul_comm x.den x'.den,
          q3reQ_mul x'.den x.den, ← q3Ring.mul_assoc, specB, ← q3reQ_mul]
      exact q3_unit_cancel (q3reQ (x.den * x'.den)) inv
        (q3reFrac x.num x.den.natAbs (q3reHden x))
        (q3reFrac x'.num x'.den.natAbs (q3reHden x')) hinv
        (by rw [hAU, hBU, hrel]))

/-! ## A2c-3-6: PreRat 上の特徴付けと環準同型性 -/

/-- **A2c-3-6a: PreRat 上の特徴付け方程式**。 -/
theorem q3re_spec (x : PreRat) :
    q3Ring.mul (q3reMap (Quot.mk ratRel x)) (q3reQ x.den) = q3reQ x.num := by
  have hdx : ((x.den.natAbs : Nat) : Int) = x.den :=
    Int.natAbs_of_nonneg (Int.le_of_lt x.den_pos)
  show q3Ring.mul (q3reFrac x.num x.den.natAbs (q3reHden x)) (q3reQ x.den) = q3reQ x.num
  have := q3re_frac_spec x.num x.den.natAbs (q3reHden x)
  rw [hdx] at this
  exact this

/-- **A2c-3-6b: 乗法保存**。 -/
theorem q3re_map_mul (a b : ratRing.carrier) :
    q3reMap (ratRing.mul a b) = q3Ring.mul (q3reMap a) (q3reMap b) := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  have hpos : (0 : Int) < x.den * y.den := Int.mul_pos x.den_pos y.den_pos
  obtain ⟨inv, hinv⟩ := q3reQ_unit_pos (x.den * y.den) hpos
  have hA : q3Ring.mul
      (q3reMap (ratRing.mul (Quot.mk ratRel x) (Quot.mk ratRel y)))
      (q3reQ (x.den * y.den)) = q3reQ (x.num * y.num) := by
    show q3Ring.mul (q3reMap (Quot.mk ratRel (prMul x y))) (q3reQ (prMul x y).den)
      = q3reQ (prMul x y).num
    exact q3re_spec (prMul x y)
  have hB : q3Ring.mul
      (q3Ring.mul (q3reMap (Quot.mk ratRel x)) (q3reMap (Quot.mk ratRel y)))
      (q3reQ (x.den * y.den)) = q3reQ (x.num * y.num) := by
    rw [q3reQ_mul x.den y.den,
      cring_mul_mul_swap' q3Ring (q3reMap (Quot.mk ratRel x))
        (q3reMap (Quot.mk ratRel y)) (q3reQ x.den) (q3reQ y.den),
      q3re_spec x, q3re_spec y, ← q3reQ_mul]
  exact q3_unit_cancel (q3reQ (x.den * y.den)) inv
    (q3reMap (ratRing.mul (Quot.mk ratRel x) (Quot.mk ratRel y)))
    (q3Ring.mul (q3reMap (Quot.mk ratRel x)) (q3reMap (Quot.mk ratRel y)))
    hinv (by rw [hA, hB])

/-- **A2c-3-6c: 加法保存**。 -/
theorem q3re_map_add (a b : ratRing.carrier) :
    q3reMap (ratRing.add a b) = q3Ring.add (q3reMap a) (q3reMap b) := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  have hpos : (0 : Int) < x.den * y.den := Int.mul_pos x.den_pos y.den_pos
  obtain ⟨inv, hinv⟩ := q3reQ_unit_pos (x.den * y.den) hpos
  have hA : q3Ring.mul
      (q3reMap (ratRing.add (Quot.mk ratRel x) (Quot.mk ratRel y)))
      (q3reQ (x.den * y.den))
      = q3Ring.add (q3Ring.mul (q3reQ x.num) (q3reQ y.den))
          (q3Ring.mul (q3reQ y.num) (q3reQ x.den)) := by
    show q3Ring.mul (q3reMap (Quot.mk ratRel (prAdd x y))) (q3reQ (prAdd x y).den)
      = q3Ring.add (q3Ring.mul (q3reQ x.num) (q3reQ y.den))
          (q3Ring.mul (q3reQ y.num) (q3reQ x.den))
    rw [q3re_spec (prAdd x y)]
    show q3reQ (x.num * y.den + y.num * x.den)
      = q3Ring.add (q3Ring.mul (q3reQ x.num) (q3reQ y.den))
          (q3Ring.mul (q3reQ y.num) (q3reQ x.den))
    rw [q3reQ_add, q3reQ_mul x.num y.den, q3reQ_mul y.num x.den]
  have hB : q3Ring.mul
      (q3Ring.add (q3reMap (Quot.mk ratRel x)) (q3reMap (Quot.mk ratRel y)))
      (q3reQ (x.den * y.den))
      = q3Ring.add (q3Ring.mul (q3reQ x.num) (q3reQ y.den))
          (q3Ring.mul (q3reQ y.num) (q3reQ x.den)) := by
    rw [q3reQ_mul x.den y.den, q3Ring.right_distrib,
      ← q3Ring.mul_assoc (q3reMap (Quot.mk ratRel x)) (q3reQ x.den) (q3reQ y.den),
      q3re_spec x,
      q3Ring.mul_comm (q3reQ x.den) (q3reQ y.den),
      ← q3Ring.mul_assoc (q3reMap (Quot.mk ratRel y)) (q3reQ y.den) (q3reQ x.den),
      q3re_spec y]
  exact q3_unit_cancel (q3reQ (x.den * y.den)) inv
    (q3reMap (ratRing.add (Quot.mk ratRel x) (Quot.mk ratRel y)))
    (q3Ring.add (q3reMap (Quot.mk ratRel x)) (q3reMap (Quot.mk ratRel y)))
    hinv (by rw [hA, hB])

/-- **A2c-3-6d: 1 保存**。 -/
theorem q3re_map_one : q3reMap ratRing.one = q3Ring.one := by
  have hs := q3re_spec prOne
  show q3reMap (Quot.mk ratRel prOne) = q3Ring.one
  rw [show q3reQ prOne.den = q3Ring.one from q3reQ_one,
    show q3reQ prOne.num = q3Ring.one from q3reQ_one] at hs
  rw [cring_mul_one] at hs
  exact hs

/-- **A2c-3-6e: 0 保存**。 -/
theorem q3re_map_zero : q3reMap ratRing.zero = q3Ring.zero := by
  have hs := q3re_spec prZero
  show q3reMap (Quot.mk ratRel prZero) = q3Ring.zero
  rw [show q3reQ prZero.den = q3Ring.one from q3reQ_one,
    show q3reQ prZero.num = q3Ring.zero from q3reQ_zero] at hs
  rw [cring_mul_one] at hs
  exact hs

/-! ## A2c-3-7: 単射性 -/

/-- q3reQ は非零整数を非零へ（ℤ→ℤ₃ 分離 + 局所化非退化）。 -/
theorem q3reQ_ne_zero (a : Int) (ha : a ≠ 0) : q3reQ a ≠ q3Ring.zero := by
  intro h
  have h' : Quot.mk (ringLocRel q3S) (ringLocOfElem (zimg a))
      = Quot.mk (ringLocRel q3S) ringLocZero := h
  obtain ⟨t, ht, e⟩ := q3f_exact h'
  have e2 : z3.mul t (zimg a) = z3.zero := by
    have e' : z3.mul t (z3.mul (zimg a) z3.one) = z3.mul t (z3.mul z3.zero z3.one) := e
    rw [cring_mul_one z3 (zimg a), cring_zero_mul z3 z3.one, CRing.mul_zero z3 t] at e'
    exact e'
  have hz : zimg a = z3.zero := q3S_regular ht e2
  have hz0 : zimg a = zimg 0 := by rw [hz, zimg_zero]
  exact ha (toZp_injective 3 (by omega) a 0 hz0)

/-- **A2c-3-7（★）: 単射性（非零 witness 形）** — 非零有理数の像は非零。 -/
theorem q3re_map_inj (x : PreRat) (hx : x.num ≠ 0) :
    q3reMap (Quot.mk ratRel x) ≠ q3Ring.zero := by
  intro h
  have hs := q3re_spec x
  rw [h, cring_zero_mul] at hs
  exact q3reQ_ne_zero x.num hx hs.symm

/-! ## A2c-3-8: 付値両立 v₃(a/b)=v₃(a)−v₃(b) -/

/-- 分解付き表現子写像の付値。 -/
theorem q3re_fracOf_val {n : Nat} (a : Int) (ha : a ≠ 0) (sp : Q3Split n) :
    q3fValRel (q3reFracOf a sp) ((pvqNatVal 3 a.natAbs : Int) - (sp.w : Int)) := by
  have hza : z3vExact 3 (zimg a) (pvqNatVal 3 a.natAbs) := z3c_val_compat a ha
  have hunit : IsZpUnit 3
      (zpUnitInv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd)) :=
    isZpUnit_inv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd)
  have hinv0 : z3vExact 3
      (zpUnitInv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd)) 0 :=
    z3v_unit_exact0 _ hunit
  have hmul : z3vExact 3
      (z3.mul (zimg a)
        (zpUnitInv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd)))
      (pvqNatVal 3 a.natAbs + 0) := z3v_exact_mul hza hinv0
  refine ⟨z3.mul (zimg a)
      (zpUnitInv 3 isPrime_three (zimg (sp.d : Int)) (q3re_unit sp.d sp.ndvd)),
    sp.w, pvqNatVal 3 a.natAbs, rfl, ?_, rfl⟩
  have h0 : pvqNatVal 3 a.natAbs + 0 = pvqNatVal 3 a.natAbs := by omega
  rw [← h0]; exact hmul

/-- **A2c-3-8（★）: 付値両立** — 非零分子の有理数 a/b の ℚ₃ 内付値は v₃(a)−v₃(b)。 -/
theorem q3re_val_compat (x : PreRat) (hx : x.num ≠ 0) :
    q3fValRel (q3reMap (Quot.mk ratRel x))
      ((pvqNatVal 3 x.num.natAbs : Int) - (pvqNatVal 3 x.den.natAbs : Int)) := by
  have hmk : q3reMap (Quot.mk ratRel x)
      = q3reFracOf x.num (q3reSplit x.den.natAbs (q3reHden x)) := rfl
  have hdpos : 1 ≤ (q3reSplit x.den.natAbs (q3reHden x)).d := by
    cases Nat.eq_zero_or_pos (q3reSplit x.den.natAbs (q3reHden x)).d with
    | inl h0 =>
      exfalso
      have he := (q3reSplit x.den.natAbs (q3reHden x)).eq
      rw [h0, Nat.mul_zero] at he
      have := q3reHden x
      omega
    | inr hp => exact hp
  have hnat : pvqNatVal 3 x.den.natAbs = (q3reSplit x.den.natAbs (q3reHden x)).w := by
    have he := (q3reSplit x.den.natAbs (q3reHden x)).eq
    have hspec := pvqNatVal_spec 3 (by omega) (q3reSplit x.den.natAbs (q3reHden x)).w
      (q3reSplit x.den.natAbs (q3reHden x)).d (q3reSplit x.den.natAbs (q3reHden x)).ndvd hdpos
    rw [← he] at hspec
    exact hspec
  have hw : (pvqNatVal 3 x.den.natAbs : Int)
      = ((q3reSplit x.den.natAbs (q3reHden x)).w : Int) := by rw [hnat]
  rw [hmk, hw]
  exact q3re_fracOf_val x.num hx (q3reSplit x.den.natAbs (q3reHden x))

/-! ## A2c-3-9: ℤ→ℚ→ℚ₃ 三角可換と稠密性 -/

/-- **A2c-3-9a: 三角可換** — ℚ→ℚ₃ を ℤ に制限すると ℤ→ℤ₃→ℚ₃ に一致。 -/
theorem q3re_int_compat (a : Int) :
    q3reMap (ratOfInt.map a) = q3reQ a := by
  have hs := q3re_spec (intToPreRat a)
  show q3reMap (Quot.mk ratRel (intToPreRat a)) = q3reQ a
  rw [show q3reQ (intToPreRat a).den = q3Ring.one from q3reQ_one] at hs
  rw [cring_mul_one] at hs
  exact hs

/-- **A2c-3-9b: ℚ の稠密性（modulus 形・整数像）** — 任意の ℤ₃ 元と精度 n に対し、
    ℤ₃⊂ℚ₃ で q3reMap の像（有理数像）が n 精度で一致する整数が存在する
    （z3c_int_dense の埋め込み経由の系）。 -/
theorem q3re_dense (c : z3.carrier) (n : Nat) :
    ∃ a : Int, q3reMap (ratOfInt.map a) = q3reQ a ∧
      z3vGe 3 (z3.add c (z3.neg ((toZpRing 3).map a))) n := by
  obtain ⟨a, ha⟩ := z3c_int_dense c n
  exact ⟨a, q3re_int_compat a, ha⟩

/-! ## A2c-3-10: 総括レコード -/

/-- **A2c-3-10a: 総括** — ℚ↪ℚ₃ 環準同型（加法/乗法/1/0 保存・非零 witness 単射・
    付値両立・三角可換・整数像稠密）。 -/
structure Q3RatEmbedData where
  /-- 環準同型 ratRing → q3Ring。 -/
  map : ratRing.carrier → q3Ring.carrier
  /-- 加法保存。 -/
  map_add : ∀ a b, map (ratRing.add a b) = q3Ring.add (map a) (map b)
  /-- 乗法保存。 -/
  map_mul : ∀ a b, map (ratRing.mul a b) = q3Ring.mul (map a) (map b)
  /-- 1 保存。 -/
  map_one : map ratRing.one = q3Ring.one
  /-- 0 保存。 -/
  map_zero : map ratRing.zero = q3Ring.zero
  /-- 非零 witness 単射。 -/
  inj : ∀ x : PreRat, x.num ≠ 0 → map (Quot.mk ratRel x) ≠ q3Ring.zero
  /-- 付値両立 v₃(a/b)=v₃(a)−v₃(b)。 -/
  val_compat : ∀ x : PreRat, x.num ≠ 0 →
    q3fValRel (map (Quot.mk ratRel x))
      ((pvqNatVal 3 x.num.natAbs : Int) - (pvqNatVal 3 x.den.natAbs : Int))
  /-- ℤ→ℚ→ℚ₃ 三角可換。 -/
  int_compat : ∀ a : Int, map (ratOfInt.map a) = q3reQ a
  /-- ℚ の稠密性（modulus 形・整数像）。 -/
  dense : ∀ (c : z3.carrier) (n : Nat), ∃ a : Int,
    map (ratOfInt.map a) = q3reQ a ∧
      z3vGe 3 (z3.add c (z3.neg ((toZpRing 3).map a))) n

/-- **A2c-3-10b: witness**。 -/
noncomputable def q3re_data : Q3RatEmbedData where
  map := q3reMap
  map_add := q3re_map_add
  map_mul := q3re_map_mul
  map_one := q3re_map_one
  map_zero := q3re_map_zero
  inj := q3re_map_inj
  val_compat := q3re_val_compat
  int_compat := q3re_int_compat
  dense := q3re_dense

/-- **A2c-3-10c: 存在**。 -/
theorem q3re_exists : Nonempty Q3RatEmbedData := ⟨q3re_data⟩

end IUT
