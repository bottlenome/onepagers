/-
  IUT/FractionField.lean — M266F（柱 A/B/C 先行建設: 整域の本物の
  分数体 Frac(D) と局所体 ℚ_p = Frac(ℤ_p) の初構成）

  ── 分類 **[実]**（本物の数学的実体の新規建設）。

  **complete_pct 影響: 実 IUT の局所体 ℚ_p を本物の分数体として初構成
  （これまで 0 だった p 進体 ℚ_p を実構成）**。整域 D（可換環 + 1≠0 +
  零因子なし）に対し、ペア (num, den) with den≠0 の交差積 Quot 商として
  分数体 Frac(D) を建て、可換環公理・逆元（witness 形）・ℤ_p ↪ ℚ_p の
  単射環準同型・非自明性 1≠0 を**完全証明**（sorry 無し・新規 choice 無し）。
  ℚ_p := Frac(zpRing p) を実体化。

  * M266F-1 `Domain` — 抽象整域（CRing + `one_ne_zero` + 古典的
    零因子なし `no_zero_div`: ab=0 → a=0 ∨ b=0）。零因子なしから
    「den の積は非零」`domain_mul_ne_zero` と右消去
    `domain_mul_right_cancel` を導く（Or 場合分け・排中律不使用）
  * M266F-2 `cring_*` — 可換環の一般補題（neg_mul・add_neg・
    差ゼロ⇒相等・積の入れ替え群）。Int 版（M115F）の CRing 一般化
  * M266F-3 `PreFrac` / `fracRel` — 前分数（den≠0）と交差積関係
    a/b ~ c/d ⟺ ad = cb。推移律は中間分母 den の右消去（整域性）
  * M266F-4 `pfAdd`/`pfNeg`/`pfMul`/`pfZero`/`pfOne`/`pfScale` と
    片側 well-definedness（交差積恒等式）
  * M266F-5 `QFrac`/`qfAdd`/`qfNeg`/`qfMul`/`fracRing` — Quot 商と
    **Frac(D) は可換環**（分母一致法則は preFrac_ext + congrArg、
    neg_add / left_distrib は分母スケール経由の Quot.sound）
  * M266F-6 `pfInvOf`/`qfMul_inv` — 逆元（num≠0 ⟹ inv = den/num）と
    **体の乗法逆元公理（witness 形）** x·x⁻¹ = 1
  * M266F-7 `pfOfElem`/`fracOfRing`/`fracOfRing_inj`/`fracOne_ne_zero`
    — 埋め込み D ↪ Frac(D)（a ↦ a/1）が**単射環準同型**、非自明性 1≠0
  * M266F-8 `FracFieldData`/`fracFieldData`/`fracField_exists` — 総括
    レコードと存在定理（本物の分数体データ）
  * M266F-9 `zpOne_neZeroAt_one`/`zp_one_ne_zero`/`zpDomain`/`Qp`/
    `Qp_is_field` — **ℚ_p := Frac(ℤ_p) の実体化**。ℤ_p の 1≠0 は
    レベル 1 で構成的に証明、ℚ_p が本物の体であることを確定

  **正直な限定（必守申告）**:
  1. ℤ_p の**古典的零因子なし** `no_zero_div (zpRing p)`
     (ab=0 → a=0 ∨ b=0) はどちらの選言肢かの決定に排中律（Markov 原理）を
     要するため構成的に閉じられず、`zpDomain` の**仮説**として持ち回る
     （witness 形の零因子なしは M91F `ZpDomain` に既存。その古典的
     大域化のみが非構成的入力）。それ以外（1≠0・体公理・埋め込み・
     可換環法則）は全て完全証明。
  2. 逆元は Frac(D) 上で**代表 witness 形**（num≠0 を仮定に取る）。
     全域 qfInv は carrier の等号判定（DecidableEq）を要し、ℤ_p の等号は
     非可判定のため採らない（ℚ の M115F と同じ方針）。
  3. 付値・完備化・位相・絶対値・アルキメデス性は次段（本モジュールは
     体構造そのものに限定）。

  全て選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。
-/
import IUT.ZpDomain

namespace IUT

/-! ## M266F-1: 抽象整域 -/

/-- **M266F-1a: 整域** — 可換環 + 1≠0 + 古典的零因子なし
    （ab = 0 → a = 0 ∨ b = 0）。分数体の分母の非零性はこの
    零因子なしから供給される。 -/
structure Domain where
  /-- 台の可換環。 -/
  R : CRing
  /-- 非自明性（1 ≠ 0）。 -/
  one_ne_zero : R.one ≠ R.zero
  /-- 零因子なし（古典形）。 -/
  no_zero_div : ∀ a b : R.carrier, R.mul a b = R.zero → a = R.zero ∨ b = R.zero

/-! ## M266F-2: 可換環の一般補題（Int 版 M115F の CRing 一般化） -/

/-- a·1 = a（可換性 + one_mul）。 -/
theorem cring_mul_one (R : CRing) (a : R.carrier) : R.mul a R.one = a := by
  rw [R.mul_comm a R.one, R.one_mul]

/-- 0·a = 0（可換性 + mul_zero）。 -/
theorem cring_zero_mul (R : CRing) (a : R.carrier) : R.mul R.zero a = R.zero := by
  rw [R.mul_comm R.zero a]
  exact R.mul_zero a

/-- a + 0 = a（可換性 + zero_add）。 -/
theorem cring_add_zero (R : CRing) (a : R.carrier) : R.add a R.zero = a := by
  rw [R.add_comm a R.zero]
  exact R.zero_add a

/-- a + (−a) = 0（可換性 + neg_add）。 -/
theorem cring_add_neg (R : CRing) (a : R.carrier) : R.add a (R.neg a) = R.zero := by
  rw [R.add_comm a (R.neg a)]
  exact R.neg_add a

/-- (−a)·b = −(a·b)（分配 + 左簡約）。 -/
theorem cring_neg_mul (R : CRing) (a b : R.carrier) :
    R.mul (R.neg a) b = R.neg (R.mul a b) := by
  apply R.add_left_cancel (a := R.mul a b)
  rw [← R.right_distrib, cring_add_neg R a, cring_zero_mul R b,
    cring_add_neg R (R.mul a b)]

/-- 差がゼロなら相等: a + (−b) = 0 → a = b。 -/
theorem cring_eq_of_sub_zero (R : CRing) {a b : R.carrier}
    (h : R.add a (R.neg b) = R.zero) : a = b := by
  have h1 : R.add (R.add a (R.neg b)) b = b := by
    rw [h, R.zero_add]
  rw [R.add_assoc, R.neg_add, cring_add_zero R a] at h1
  exact h1

/-- 右 2 因子入れ替え: (a·b)·c = (a·c)·b。 -/
theorem cring_mul_right_swap (R : CRing) (a b c : R.carrier) :
    R.mul (R.mul a b) c = R.mul (R.mul a c) b := by
  rw [R.mul_assoc, R.mul_comm b c, ← R.mul_assoc]

/-- 対角入れ替え: (a·b)·(c·d) = (a·d)·(c·b)。 -/
theorem cring_mul_mul_swap (R : CRing) (a b c d : R.carrier) :
    R.mul (R.mul a b) (R.mul c d) = R.mul (R.mul a d) (R.mul c b) := by
  have h : R.mul b (R.mul c d) = R.mul d (R.mul c b) := by
    rw [← R.mul_assoc, ← R.mul_assoc, R.mul_comm b c, R.mul_comm d c,
      R.mul_assoc, R.mul_assoc, R.mul_comm b d]
  rw [R.mul_assoc, h, ← R.mul_assoc]

/-- 中間入れ替え: (a·b)·(c·d) = (a·c)·(b·d)。 -/
theorem cring_mul_mul_swap' (R : CRing) (a b c d : R.carrier) :
    R.mul (R.mul a b) (R.mul c d) = R.mul (R.mul a c) (R.mul b d) := by
  have h : R.mul b (R.mul c d) = R.mul c (R.mul b d) := by
    rw [← R.mul_assoc, ← R.mul_assoc, R.mul_comm b c]
  rw [R.mul_assoc, h, ← R.mul_assoc]

/-! ## M266F-1b: 整域からの非零性・消去 -/

/-- **非零の積は非零**（den の積 ≠ 0。零因子なしの対偶、Or 場合分け）。 -/
theorem domain_mul_ne_zero (D : Domain) {a b : D.R.carrier}
    (ha : a ≠ D.R.zero) (hb : b ≠ D.R.zero) : D.R.mul a b ≠ D.R.zero := by
  intro h
  cases D.no_zero_div a b h with
  | inl h1 => exact ha h1
  | inr h1 => exact hb h1

/-- **右消去**: c ≠ 0 かつ a·c = b·c なら a = b
    （(a−b)·c = 0 と零因子なしを Or 場合分けで消す。排中律不使用）。 -/
theorem domain_mul_right_cancel (D : Domain) {a b c : D.R.carrier}
    (hc : c ≠ D.R.zero) (h : D.R.mul a c = D.R.mul b c) : a = b := by
  have hz : D.R.mul (D.R.add a (D.R.neg b)) c = D.R.zero := by
    rw [D.R.right_distrib, cring_neg_mul, h, cring_add_neg]
  cases D.no_zero_div (D.R.add a (D.R.neg b)) c hz with
  | inl h1 => exact cring_eq_of_sub_zero D.R h1
  | inr h1 => exact absurd h1 hc

/-! ## M266F-3: 前分数と交差積関係 -/

/-- **M266F-3a: 前分数**（分子任意・分母 ≠ 0）。 -/
structure PreFrac (D : Domain) where
  /-- 分子。 -/
  num : D.R.carrier
  /-- 分母。 -/
  den : D.R.carrier
  /-- 分母は非零。 -/
  den_ne : den ≠ D.R.zero

/-- 前分数の外延性（den_ne は Prop なので proof irrelevance で消える）。 -/
theorem preFrac_ext {D : Domain} : ∀ {x y : PreFrac D},
    x.num = y.num → x.den = y.den → x = y
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

/-- **M266F-3b: 交差積関係** a/b ~ c/d ⟺ ad = cb。 -/
def fracRel (D : Domain) (x y : PreFrac D) : Prop :=
  D.R.mul x.num y.den = D.R.mul y.num x.den

/-- 反射律。 -/
theorem fracRel_refl {D : Domain} (x : PreFrac D) : fracRel D x x := rfl

/-- 対称律。 -/
theorem fracRel_symm {D : Domain} {x y : PreFrac D} (h : fracRel D x y) :
    fracRel D y x := by
  have h' : D.R.mul x.num y.den = D.R.mul y.num x.den := h
  show D.R.mul y.num x.den = D.R.mul x.num y.den
  exact h'.symm

/-- **M266F-3c: 推移律** — 中間分母 y.den を整域の右消去で割る。 -/
theorem fracRel_trans {D : Domain} {x y z : PreFrac D}
    (h1 : fracRel D x y) (h2 : fracRel D y z) : fracRel D x z := by
  have h1' : D.R.mul x.num y.den = D.R.mul y.num x.den := h1
  have h2' : D.R.mul y.num z.den = D.R.mul z.num y.den := h2
  show D.R.mul x.num z.den = D.R.mul z.num x.den
  apply domain_mul_right_cancel D y.den_ne
  rw [cring_mul_right_swap D.R x.num z.den y.den, h1',
    cring_mul_right_swap D.R z.num x.den y.den, ← h2',
    cring_mul_right_swap D.R y.num x.den z.den]

/-! ## M266F-4: 代表演算 -/

/-- **M266F-4a: 加法の代表** a/b + c/d = (ad + cb)/(bd)。 -/
def pfAdd {D : Domain} (x y : PreFrac D) : PreFrac D :=
  ⟨D.R.add (D.R.mul x.num y.den) (D.R.mul y.num x.den), D.R.mul x.den y.den,
    domain_mul_ne_zero D x.den_ne y.den_ne⟩

/-- **M266F-4b: 反元の代表**。 -/
def pfNeg {D : Domain} (x : PreFrac D) : PreFrac D :=
  ⟨D.R.neg x.num, x.den, x.den_ne⟩

/-- **M266F-4c: 乗法の代表**。 -/
def pfMul {D : Domain} (x y : PreFrac D) : PreFrac D :=
  ⟨D.R.mul x.num y.num, D.R.mul x.den y.den,
    domain_mul_ne_zero D x.den_ne y.den_ne⟩

/-- 0 の代表 0/1。 -/
def pfZero {D : Domain} : PreFrac D := ⟨D.R.zero, D.R.one, D.one_ne_zero⟩

/-- 1 の代表 1/1。 -/
def pfOne {D : Domain} : PreFrac D := ⟨D.R.one, D.R.one, D.one_ne_zero⟩

/-- 非零 c による分子分母の同時スケール（左分配の Quot.sound 用）。 -/
def pfScale {D : Domain} (c : D.R.carrier) (hc : c ≠ D.R.zero) (x : PreFrac D) :
    PreFrac D :=
  ⟨D.R.mul c x.num, D.R.mul c x.den, domain_mul_ne_zero D hc x.den_ne⟩

/-- スケールは関係を変えない（(c·n)·d = n·(c·d)）。 -/
theorem fracRel_scale {D : Domain} (c : D.R.carrier) (hc : c ≠ D.R.zero)
    (x : PreFrac D) : fracRel D (pfScale c hc x) x := by
  show D.R.mul (D.R.mul c x.num) x.den = D.R.mul x.num (D.R.mul c x.den)
  rw [D.R.mul_comm c x.num, D.R.mul_assoc]

/-! ## M266F-4d: 演算の well-definedness（片側ずつ） -/

/-- 加法は第 2 引数の関係を保つ。 -/
theorem fracRel_add_left {D : Domain} (x : PreFrac D) {y y' : PreFrac D}
    (h : fracRel D y y') : fracRel D (pfAdd x y) (pfAdd x y') := by
  have h' : D.R.mul y.num y'.den = D.R.mul y'.num y.den := h
  show D.R.mul (D.R.add (D.R.mul x.num y.den) (D.R.mul y.num x.den))
      (D.R.mul x.den y'.den)
    = D.R.mul (D.R.add (D.R.mul x.num y'.den) (D.R.mul y'.num x.den))
      (D.R.mul x.den y.den)
  rw [D.R.right_distrib, D.R.right_distrib,
    cring_mul_mul_swap D.R x.num y.den x.den y'.den,
    cring_mul_mul_swap D.R y.num x.den x.den y'.den, h',
    cring_mul_mul_swap D.R y'.num y.den x.den x.den]

/-- 加法は第 1 引数の関係を保つ。 -/
theorem fracRel_add_right {D : Domain} (y : PreFrac D) {x x' : PreFrac D}
    (h : fracRel D x x') : fracRel D (pfAdd x y) (pfAdd x' y) := by
  have h' : D.R.mul x.num x'.den = D.R.mul x'.num x.den := h
  show D.R.mul (D.R.add (D.R.mul x.num y.den) (D.R.mul y.num x.den))
      (D.R.mul x'.den y.den)
    = D.R.mul (D.R.add (D.R.mul x'.num y.den) (D.R.mul y.num x'.den))
      (D.R.mul x.den y.den)
  rw [D.R.right_distrib, D.R.right_distrib,
    cring_mul_mul_swap' D.R x.num y.den x'.den y.den, h',
    ← cring_mul_mul_swap' D.R x'.num y.den x.den y.den,
    cring_mul_mul_swap' D.R y.num x.den x'.den y.den]

/-- 反元は関係を保つ。 -/
theorem fracRel_neg {D : Domain} {x x' : PreFrac D} (h : fracRel D x x') :
    fracRel D (pfNeg x) (pfNeg x') := by
  have h' : D.R.mul x.num x'.den = D.R.mul x'.num x.den := h
  show D.R.mul (D.R.neg x.num) x'.den = D.R.mul (D.R.neg x'.num) x.den
  rw [cring_neg_mul, cring_neg_mul, h']

/-- 乗法は第 2 引数の関係を保つ。 -/
theorem fracRel_mul_left {D : Domain} (x : PreFrac D) {y y' : PreFrac D}
    (h : fracRel D y y') : fracRel D (pfMul x y) (pfMul x y') := by
  have h' : D.R.mul y.num y'.den = D.R.mul y'.num y.den := h
  show D.R.mul (D.R.mul x.num y.num) (D.R.mul x.den y'.den)
    = D.R.mul (D.R.mul x.num y'.num) (D.R.mul x.den y.den)
  rw [cring_mul_mul_swap' D.R x.num y.num x.den y'.den, h',
    cring_mul_mul_swap' D.R x.num y'.num x.den y.den]

/-- 乗法は第 1 引数の関係を保つ。 -/
theorem fracRel_mul_right {D : Domain} (y : PreFrac D) {x x' : PreFrac D}
    (h : fracRel D x x') : fracRel D (pfMul x y) (pfMul x' y) := by
  have h' : D.R.mul x.num x'.den = D.R.mul x'.num x.den := h
  show D.R.mul (D.R.mul x.num y.num) (D.R.mul x'.den y.den)
    = D.R.mul (D.R.mul x'.num y.num) (D.R.mul x.den y.den)
  rw [cring_mul_mul_swap' D.R x.num y.num x'.den y.den, h',
    cring_mul_mul_swap' D.R x'.num y.num x.den y.den]

/-! ## M266F-5: Quot 商 Frac(D) と可換環構造 -/

/-- **M266F-5a: Frac(D) の台** = PreFrac / 交差積関係。 -/
def QFrac (D : Domain) := Quot (fracRel D)

/-- **M266F-5b: 加法**（二重 Quot.lift）。 -/
def qfAdd {D : Domain} (a b : QFrac D) : QFrac D :=
  Quot.lift
    (fun x => Quot.lift
      (fun y => Quot.mk (fracRel D) (pfAdd x y))
      (fun _ _ hy => Quot.sound (fracRel_add_left x hy)) b)
    (fun _ _ hx => by
      induction b using Quot.ind
      rename_i y
      exact Quot.sound (fracRel_add_right y hx)) a

/-- **M266F-5c: 反元**。 -/
def qfNeg {D : Domain} (a : QFrac D) : QFrac D :=
  Quot.lift (fun x => Quot.mk (fracRel D) (pfNeg x))
    (fun _ _ hx => Quot.sound (fracRel_neg hx)) a

/-- **M266F-5d: 乗法**。 -/
def qfMul {D : Domain} (a b : QFrac D) : QFrac D :=
  Quot.lift
    (fun x => Quot.lift
      (fun y => Quot.mk (fracRel D) (pfMul x y))
      (fun _ _ hy => Quot.sound (fracRel_mul_left x hy)) b)
    (fun _ _ hx => by
      induction b using Quot.ind
      rename_i y
      exact Quot.sound (fracRel_mul_right y hx)) a

/-- 加法の結合律（分母は mul_assoc で一致 → preFrac_ext）。 -/
theorem pfAdd_assoc {D : Domain} (x y z : PreFrac D) :
    pfAdd (pfAdd x y) z = pfAdd x (pfAdd y z) := by
  apply preFrac_ext
  · show D.R.add (D.R.mul (D.R.add (D.R.mul x.num y.den) (D.R.mul y.num x.den))
        z.den) (D.R.mul z.num (D.R.mul x.den y.den))
      = D.R.add (D.R.mul x.num (D.R.mul y.den z.den))
        (D.R.mul (D.R.add (D.R.mul y.num z.den) (D.R.mul z.num y.den)) x.den)
    rw [D.R.right_distrib, D.R.right_distrib, D.R.add_assoc,
      D.R.mul_assoc x.num y.den z.den,
      cring_mul_right_swap D.R y.num x.den z.den,
      cring_mul_right_swap D.R z.num y.den x.den,
      D.R.mul_assoc z.num x.den y.den]
  · show D.R.mul (D.R.mul x.den y.den) z.den = D.R.mul x.den (D.R.mul y.den z.den)
    exact D.R.mul_assoc x.den y.den z.den

/-- 加法の可換律。 -/
theorem pfAdd_comm {D : Domain} (x y : PreFrac D) : pfAdd x y = pfAdd y x := by
  apply preFrac_ext
  · show D.R.add (D.R.mul x.num y.den) (D.R.mul y.num x.den)
      = D.R.add (D.R.mul y.num x.den) (D.R.mul x.num y.den)
    exact D.R.add_comm _ _
  · exact D.R.mul_comm x.den y.den

/-- 左零元。 -/
theorem pfZero_add {D : Domain} (x : PreFrac D) : pfAdd pfZero x = x := by
  apply preFrac_ext
  · show D.R.add (D.R.mul D.R.zero x.den) (D.R.mul x.num D.R.one) = x.num
    rw [cring_zero_mul, cring_mul_one, D.R.zero_add]
  · show D.R.mul D.R.one x.den = x.den
    exact D.R.one_mul x.den

/-- 左反元（分母 d² ≠ 1 のため Quot.sound 必須）。 -/
theorem pfNeg_add_rel {D : Domain} (x : PreFrac D) :
    fracRel D (pfAdd (pfNeg x) x) pfZero := by
  show D.R.mul (D.R.add (D.R.mul (D.R.neg x.num) x.den) (D.R.mul x.num x.den))
      D.R.one = D.R.mul D.R.zero (D.R.mul x.den x.den)
  rw [cring_mul_one, cring_zero_mul, cring_neg_mul, D.R.neg_add]

/-- 乗法の結合律。 -/
theorem pfMul_assoc {D : Domain} (x y z : PreFrac D) :
    pfMul (pfMul x y) z = pfMul x (pfMul y z) := by
  apply preFrac_ext
  · exact D.R.mul_assoc x.num y.num z.num
  · exact D.R.mul_assoc x.den y.den z.den

/-- 左単位元。 -/
theorem pfOne_mul {D : Domain} (x : PreFrac D) : pfMul pfOne x = x := by
  apply preFrac_ext
  · exact D.R.one_mul x.num
  · exact D.R.one_mul x.den

/-- 乗法の可換律。 -/
theorem pfMul_comm {D : Domain} (x y : PreFrac D) : pfMul x y = pfMul y x := by
  apply preFrac_ext
  · exact D.R.mul_comm x.num y.num
  · exact D.R.mul_comm x.den y.den

/-- 左分配は「x.den 倍スケール」との preFrac 等式に落ちる（分母が真に
    異なるため congrArg では閉じず、この等式 + fracRel_scale の
    Quot.sound 経由）。 -/
theorem pfLeftDistrib_scale {D : Domain} (x y z : PreFrac D) :
    pfAdd (pfMul x y) (pfMul x z)
      = pfScale x.den x.den_ne (pfMul x (pfAdd y z)) := by
  apply preFrac_ext
  · show D.R.add (D.R.mul (D.R.mul x.num y.num) (D.R.mul x.den z.den))
        (D.R.mul (D.R.mul x.num z.num) (D.R.mul x.den y.den))
      = D.R.mul x.den (D.R.mul x.num
        (D.R.add (D.R.mul y.num z.den) (D.R.mul z.num y.den)))
    rw [D.R.left_distrib x.num, D.R.left_distrib x.den,
      cring_mul_mul_swap' D.R x.num y.num x.den z.den,
      cring_mul_mul_swap' D.R x.num z.num x.den y.den,
      ← D.R.mul_assoc x.den x.num (D.R.mul y.num z.den),
      ← D.R.mul_assoc x.den x.num (D.R.mul z.num y.den),
      D.R.mul_comm x.den x.num]
  · show D.R.mul (D.R.mul x.den y.den) (D.R.mul x.den z.den)
      = D.R.mul x.den (D.R.mul x.den (D.R.mul y.den z.den))
    rw [cring_mul_mul_swap' D.R x.den y.den x.den z.den, D.R.mul_assoc]

/-- **定理 (M266F-5e): Frac(D) は可換環**。 -/
def fracRing (D : Domain) : CRing where
  carrier := QFrac D
  add := qfAdd
  zero := Quot.mk (fracRel D) pfZero
  neg := qfNeg
  mul := qfMul
  one := Quot.mk (fracRel D) pfOne
  add_assoc := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    exact congrArg (Quot.mk (fracRel D)) (pfAdd_assoc x y z)
  zero_add := by
    intro a
    induction a using Quot.ind; rename_i x
    exact congrArg (Quot.mk (fracRel D)) (pfZero_add x)
  neg_add := by
    intro a
    induction a using Quot.ind; rename_i x
    exact Quot.sound (pfNeg_add_rel x)
  add_comm := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    exact congrArg (Quot.mk (fracRel D)) (pfAdd_comm x y)
  mul_assoc := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    exact congrArg (Quot.mk (fracRel D)) (pfMul_assoc x y z)
  one_mul := by
    intro a
    induction a using Quot.ind; rename_i x
    exact congrArg (Quot.mk (fracRel D)) (pfOne_mul x)
  mul_comm := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    exact congrArg (Quot.mk (fracRel D)) (pfMul_comm x y)
  left_distrib := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    show Quot.mk (fracRel D) (pfMul x (pfAdd y z))
      = Quot.mk (fracRel D) (pfAdd (pfMul x y) (pfMul x z))
    rw [pfLeftDistrib_scale x y z]
    exact (Quot.sound (fracRel_scale x.den x.den_ne (pfMul x (pfAdd y z)))).symm

/-! ## M266F-6: 逆元（witness 形の体公理） -/

/-- **M266F-6a: 逆元の代表** — num ≠ 0 なら inv = den/num
    （num を分母に据える。仮説 num≠0 でそのまま非零分母を得る）。 -/
def pfInvOf {D : Domain} (x : PreFrac D) (hz : x.num ≠ D.R.zero) : PreFrac D :=
  ⟨x.den, x.num, hz⟩

/-- **定理 (M266F-6b): 体の乗法逆元公理（witness 形）** — num ≠ 0 なる
    代表 x に対し x · x⁻¹ = 1（分数体の本質。可換性のみで閉じる）。
    全域 qfInv は carrier の等号判定を要し ℤ_p では非可判定のため
    採らず、ℚ の M115F と同じく代表 witness 形で述べる（正直申告）。 -/
theorem qfMul_inv (D : Domain) (x : PreFrac D) (hz : x.num ≠ D.R.zero) :
    (fracRing D).mul (Quot.mk (fracRel D) x)
        (Quot.mk (fracRel D) (pfInvOf x hz))
      = (fracRing D).one := by
  show Quot.mk (fracRel D) (pfMul x (pfInvOf x hz))
    = Quot.mk (fracRel D) pfOne
  apply Quot.sound
  show D.R.mul (D.R.mul x.num x.den) D.R.one
    = D.R.mul D.R.one (D.R.mul x.den x.num)
  rw [cring_mul_one, D.R.one_mul, D.R.mul_comm x.num x.den]

/-! ## M266F-7: 埋め込み D ↪ Frac(D) -/

/-- 元 a の代表 a/1。 -/
def pfOfElem {D : Domain} (a : D.R.carrier) : PreFrac D :=
  ⟨a, D.R.one, D.one_ne_zero⟩

/-- **M266F-7a: 埋め込み D → Frac(D) は環準同型**（a ↦ a/1）。 -/
def fracOfRing (D : Domain) : RingHom D.R (fracRing D) where
  map := fun a => Quot.mk (fracRel D) (pfOfElem a)
  map_add := fun a b => by
    show Quot.mk (fracRel D) (pfOfElem (D.R.add a b))
      = Quot.mk (fracRel D) (pfAdd (pfOfElem a) (pfOfElem b))
    apply congrArg (Quot.mk (fracRel D))
    apply preFrac_ext
    · show D.R.add a b
        = D.R.add (D.R.mul a D.R.one) (D.R.mul b D.R.one)
      rw [cring_mul_one, cring_mul_one]
    · show D.R.one = D.R.mul D.R.one D.R.one
      rw [D.R.one_mul]
  map_mul := fun a b => by
    show Quot.mk (fracRel D) (pfOfElem (D.R.mul a b))
      = Quot.mk (fracRel D) (pfMul (pfOfElem a) (pfOfElem b))
    apply congrArg (Quot.mk (fracRel D))
    apply preFrac_ext
    · exact rfl
    · show D.R.one = D.R.mul D.R.one D.R.one
      rw [D.R.one_mul]
  map_one := rfl

/-- **定理 (M266F-7b): 分離性** — mk x = mk y なら fracRel x y
    （propext lift の標準トリック、Quot.exact 不使用）。 -/
theorem quot_exact_frac {D : Domain} {x y : PreFrac D}
    (h : Quot.mk (fracRel D) x = Quot.mk (fracRel D) y) : fracRel D x y := by
  have hf : Quot.lift (fracRel D x)
      (fun _ _ hxy => propext
        ⟨fun hfx => fracRel_trans hfx hxy,
         fun hfy => fracRel_trans hfy (fracRel_symm hxy)⟩)
      (Quot.mk (fracRel D) x) := fracRel_refl x
  rw [h] at hf
  exact hf

/-- **定理 (M266F-7c): 埋め込みは単射**（分離性で a·1 = b·1 に落とす）。 -/
theorem fracOfRing_inj (D : Domain) (a b : D.R.carrier)
    (h : (fracOfRing D).map a = (fracOfRing D).map b) : a = b := by
  have h1 : fracRel D (pfOfElem a) (pfOfElem b) := quot_exact_frac h
  have h2 : D.R.mul a D.R.one = D.R.mul b D.R.one := h1
  rw [cring_mul_one, cring_mul_one] at h2
  exact h2

/-- **定理 (M266F-7d): Frac(D) は非自明**（1 ≠ 0）。 -/
theorem fracOne_ne_zero (D : Domain) :
    (fracRing D).one ≠ (fracRing D).zero := by
  intro h
  have h1 : fracRel D pfOne pfZero := quot_exact_frac h
  have h2 : D.R.mul D.R.one D.R.one = D.R.mul D.R.zero D.R.one := h1
  rw [cring_mul_one, cring_zero_mul] at h2
  exact D.one_ne_zero h2

/-! ## M266F-8: 総括レコード（本物の分数体データ） -/

/-- **M266F-8a: 分数体データ** — Frac(D) の可換環性（fracRing）・
    非自明性・埋め込みの単射環準同型・逆元の体公理（witness 形）の束。 -/
structure FracFieldData (D : Domain) where
  /-- 非自明性 1 ≠ 0。 -/
  nontrivial : (fracRing D).one ≠ (fracRing D).zero
  /-- 埋め込み環準同型 D ↪ Frac(D)。 -/
  embed_hom : RingHom D.R (fracRing D)
  /-- 埋め込みの単射性。 -/
  embed_inj : ∀ a b : D.R.carrier, embed_hom.map a = embed_hom.map b → a = b
  /-- 体の乗法逆元公理（witness 形）。 -/
  mul_inv_witness : ∀ (x : PreFrac D) (hz : x.num ≠ D.R.zero),
    (fracRing D).mul (Quot.mk (fracRel D) x)
        (Quot.mk (fracRel D) (pfInvOf x hz))
      = (fracRing D).one

/-- **M266F-8b: witness**（全フィールドが本モジュールの完全証明）。 -/
def fracFieldData (D : Domain) : FracFieldData D where
  nontrivial := fracOne_ne_zero D
  embed_hom := fracOfRing D
  embed_inj := fracOfRing_inj D
  mul_inv_witness := qfMul_inv D

/-- **見出し定理 (M266F-8c)**: 任意の整域 D に対し分数体データが存在。 -/
theorem fracField_exists (D : Domain) : Nonempty (FracFieldData D) :=
  ⟨fracFieldData D⟩

/-! ## M266F-9: ℚ_p := Frac(ℤ_p) の実体化 -/

/-- **M266F-9a: ℤ_p の 1 はレベル 1 で非零**（p^1 ∣ 1 は p ≥ 2 に矛盾。
    構成的・レベル 1 の等号判定に帰着）。 -/
theorem zpOne_neZeroAt_one (p : Nat) (hp : 2 ≤ p) : NeZeroAt p (zpOne p) 1 := by
  intro h0
  have h : Quot.mk (modCong (p ^ 1)).rel (1 : Int)
      = Quot.mk (modCong (p ^ 1)).rel 0 := h0
  obtain ⟨t, ht⟩ := quot_exact intGrp (modCong (p ^ 1)) h
  rw [Nat.pow_one] at ht
  have hdvd : ((p : Nat) : Int) ∣ (1 : Int) := ⟨t, int_eq_of_sub_zero ht⟩
  have hle : ((p : Nat) : Int) ≤ 1 := Int.le_of_dvd (by omega) hdvd
  omega

/-- **M266F-9b: ℤ_p は非自明**（1 ≠ 0。レベル 1 の witness 非零から）。 -/
theorem frac_zp_one_ne_zero (p : Nat) (hp : IsPrime p) :
    (zpRing p).one ≠ (zpRing p).zero :=
  neZeroAt_ne_zero p (zpOne p) (zpOne_neZeroAt_one p hp.1)

/-- **M266F-9c: ℤ_p を整域として実体化** — 可換環 zpRing p、1≠0 は構成的、
    古典的零因子なしは**仮説** `hnzd`（witness 形は M91F 既存、その古典
    大域化のみが排中律を要する非構成的入力・正直申告）。 -/
def zpDomain (p : Nat) (hp : IsPrime p)
    (hnzd : ∀ a b : (zpRing p).carrier,
      (zpRing p).mul a b = (zpRing p).zero →
        a = (zpRing p).zero ∨ b = (zpRing p).zero) : Domain where
  R := zpRing p
  one_ne_zero := frac_zp_one_ne_zero p hp
  no_zero_div := hnzd

/-- **M266F-9d: ℚ_p := Frac(ℤ_p)**（本物の p 進体の可換環）。 -/
def Qp (p : Nat) (hp : IsPrime p)
    (hnzd : ∀ a b : (zpRing p).carrier,
      (zpRing p).mul a b = (zpRing p).zero →
        a = (zpRing p).zero ∨ b = (zpRing p).zero) : CRing :=
  fracRing (zpDomain p hp hnzd)

/-- **定理 (M266F-9e): ℚ_p は本物の体** — 分数体データ（非自明・逆元・
    埋め込み単射）が存在。ℤ_p ↪ ℚ_p も付随。 -/
theorem Qp_is_field (p : Nat) (hp : IsPrime p)
    (hnzd : ∀ a b : (zpRing p).carrier,
      (zpRing p).mul a b = (zpRing p).zero →
        a = (zpRing p).zero ∨ b = (zpRing p).zero) :
    Nonempty (FracFieldData (zpDomain p hp hnzd)) :=
  fracField_exists (zpDomain p hp hnzd)

end IUT
