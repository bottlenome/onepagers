/-
  IUT/PicardDivisor.lean — M307F（柱C 先行建設: 因子群 Div・単項因子・
                          Picard 群 Pic=Div/単項・次数写像 — 算術 Frobenioid の中核）

  ── 主要成果の分類: **[実]**（本物の先行建設 (b)）。整域／数体の**因子群**
     Div＝素点（素因子）の形式的有限 ℤ-線形和 Σ nᵢ[Pᵢ]（自由アーベル群 ⊕ℤ）、
     **単項因子** div(a)＝a の付値ベクトル（本物の群準同型 K^×→Div）、**Picard 群**
     Pic＝Div/（単項因子の像）（本物の商群＝cokernel＝直線束の同型類群）、**次数写像**
     deg:Div→ℤ（本物の群準同型）を core Lean のみで完全証明する。toy 主語なし——
     主語は「素点上の有限台 ℤ-値関数のなす自由アーベル群」という**本物の代数対象**で
     あり、群・準同型・商群は既存の本物の群機構（M16 `Grp`／M13 `quotGrp`／
     M267F `quotientGroupN`・`imSubgroup`）の上に載る。

  complete_pct 影響: **柱C（形式群/Frobenioid）の実 IUT 完全証明率を前進させる**。
  既存の柱C は Frobenioid の因子部分を **QDiv**（M51F `FrobenioidModel`: 素点ごとの
  重複度の有限台 **ℕ 値関数**＝有効因子の**可換モノイド**、逆元なし）で持っていた。
  これは「有効因子モノイド」までであり、**因子群**（＝有効因子モノイドの群化・
  Grothendieck 群）・**単項因子準同型**・**Picard 群**（因子群の単項による商）は
  柱C に 0 であった。本ファイルはそれを**本物**に建てる:
  (1) ℤ 値有限台関数の**自由アーベル群** picDivGrp（QDiv モノイドの群化。逆元 rawNeg・
      結合律・単位元・逆元律を Quot 商上で完全証明）、
  (2) 付値データからの**単項因子準同型** div:K^×→Div（div(ab)=div(a)+div(b) を付値の
      加法性から完全証明。本物の Hom）、
  (3) **Picard 群** Pic＝Div/im(div)（M267F `quotientGroupN` による本物の商群。
      アーベル性から像が正規部分群であることを完全証明）、
  (4) **次数準同型** deg:Div→ℤ（deg(x+y)=deg x+deg y を有限和の加法性・台安定性から
      完全証明。本物の Hom into `intGrp`）、
  (5) Frobenius 作用 [n]（因子の n 倍）が Div の自己準同型かつ deg([n]D)=n·deg D で
      あること（M51F `degZ_frob` の群版）＋有効因子（nᵢ≥0）が n 倍・和で閉じること
      （因子モノイド＋Frobenius＝Frobenioid の骨組み）。
  これにより柱C の因子部分は「有効因子モノイド QDiv」から「因子**群** Div・単項準同型・
  **Picard 群**・次数準同型」へと本物で前進する。

  ## 検証する中核（全て sorry なし・新規 Classical.choice なし）

  * M307F-0 `isum` / `isum_congr` / `isum_add` / `isum_ext_zero` / `isum_stable` /
    `isum_smul`               — ℤ 値有限和のインフラ（加法性・台安定性・斉次性）
  * M307F-1 `RawDiv` / `rawZero` / `rawAdd` / `rawNeg`
                              — 因子の代表（素点→ℤ の有限台関数、台上界 bound をデータに）
  * M307F-2 `rawEq`（係数等価）＋ 同値律 — bound 非依存の因子等価
  * M307F-3 `picDivGrp`         — **因子群 Div**＝Quot rawEq 上の本物のアーベル群
                                   （群公理を Quot.ind＋Quot.sound で完全証明）
  * M307F-4 `picDivGrp_comm` / `picDivAbelianNormal`
                              — Div のアーベル性 → 任意の部分群が正規
  * M307F-5 `picDivDegree`      — **次数準同型** Div→ℤ（Hom into intGrp、完全証明）
  * M307F-6 `PicDivValuation` / `picDivPrincipalRaw` / `picDivPrincipalHom`
                              — 付値データ・**単項因子準同型** div:K^×→Div（本物の Hom）
  * M307F-7 `picDivPrincipalSub` / `picDivPrincipalNormal` / `picDivPic`
                              — **Picard 群** Pic＝Div/im(div)（本物の商群）
  * M307F-8 `picDivFrobRaw` / `picDivFrob` / `picDiv_frob_degree`
                              — Frobenius 作用 [n] と次数の斉次性 deg([n]D)=n·deg D
  * M307F-9 `picDivEffectiveRaw` + `_zero`/`_add`/`_frob`
                              — 有効因子（nᵢ≥0）が 0・和・[n] で閉じる（因子モノイド）
  * M307F-10 `picDivTrivialVal` / `picDiv_field_trivial` / `picDiv_field_im_one` /
    `picDiv_pic_trivial_of_surjective`
                              — 実例: 体では div≡0（単項部分群は自明）・PID では
                                 単項が全射なら Pic=0
  * M307F-11 capstone `PicardDivisorData` / `picDivData` / `picDiv_exists` /
    `picDiv_principal_isHom` / `picDiv_degree_isHom` / `picDiv_pic_proj_surjective`

  ## 正直な限定（何が本物で何が後続か・消去/弱化禁止）

  - **本物（完全証明）**:
    ・因子群 Div が**アーベル群**であること（結合・単位・逆元・可換、Quot 商上で完全）。
    ・単項因子写像 div が**群準同型** div(ab)=div(a)+div(b)（付値の加法性 ord_mul から）。
    ・Picard 群 Pic＝Div/im(div) が**群**であること（M267F 商群＋像の正規性、完全）。
    ・次数写像 deg が**群準同型** deg(x+y)=deg x+deg y（有限和の加法性・台安定性、完全）。
    ・Frobenius [n] が Div の**自己準同型**かつ deg([n]D)=n·deg D（斉次性、完全）。
    ・有効因子が 0・和・[n] で閉じること（因子モノイドの本物）。
    ・体では div≡0・単項部分群が自明、単項全射なら Pic=0（実例、完全）。
  - **正直申告（未達・骨組み・後続。飾りでなく地図）**:
    ・**付値系は「付値データ」`PicDivValuation` をパラメータ**として受け取る（各素点の
      ord_k:K^×→ℤ が加法的準同型・有限台 witness をデータで持つ形）。これは div の
      **本物の普遍形**（普遍性: 任意の付値系に対し div は Hom）であり、特定の楕円曲線／
      局所体上の実付値（M301F 付値との連結）で `PicDivValuation` を**実体化**するのは
      後続。本ファイルは付値系上の Div・div・Pic・deg の代数的中核を本物で閉じる。
    ・素点（素因子）の添字は **ℕ 列挙**（k 番目の素点）とし、有限台は bound データで持つ。
      これは M289F `PrimeSpectrum` の点・M302F `FractionalIdeal` の単項因子と概念整合する
      簿記であり、素点集合そのものを Spec の点として実体化するのは後続。
    ・**Pic の有限性（類数 h<∞）は範囲外**（Div は自由アーベル群として無限位数）。
      次数 0 部分 Pic⁰（deg の核）の骨組みまで（deg が単項因子上 0 になる積公式は
      固有曲線／数体の大域理論を要すので後続——本ファイルは deg が Pic に降りることを
      主張しない）。
    ・**Frobenioid の完全な圏論的定義**（split Frobenioid・型 Frobenioid・base 圏）は
      M48F/M51F/M55F の圏構成と本モジュールの因子群を接続する後続で行う。本ファイルは
      「因子群＋Frobenius 自己準同型＋有効因子モノイド＝算術 Frobenioid の因子面の骨組み」
      を本物で与える（M51F QDiv モノイドの群化）。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無。
-/
import IUT.QuotientGroup

namespace IUT

/-! ## M307F-0: ℤ 値有限和のインフラ -/

/-- **M307F-0a: 有限和** Σ_{k<n} f k（ℤ 値、core のみ）。 -/
def isum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => isum f n + f n

/-- **M307F-0b: 合同性** — 各項が等しければ和も等しい。 -/
theorem isum_congr {f g : Nat → Int} (h : ∀ k, f k = g k) :
    ∀ n, isum f n = isum g n := by
  intro n
  induction n with
  | zero => rfl
  | succ p ih =>
    show isum f p + f p = isum g p + g p
    rw [ih, h p]

/-- **M307F-0c: 加法性** Σ(f+g) = Σf + Σg。 -/
theorem isum_add (f g : Nat → Int) :
    ∀ n, isum (fun k => f k + g k) n = isum f n + isum g n := by
  intro n
  induction n with
  | zero =>
    show (0 : Int) = 0 + 0
    omega
  | succ p ih =>
    show isum (fun k => f k + g k) p + (f p + g p)
        = (isum f p + f p) + (isum g p + g p)
    rw [ih]
    omega

/-- **M307F-0d: 台の外への延長** — m 以上で消える f は m+j まで和が m と同じ。 -/
theorem isum_ext_zero (f : Nat → Int) (m : Nat) (hf : ∀ k, m ≤ k → f k = 0) :
    ∀ j, isum f (m + j) = isum f m := by
  intro j
  induction j with
  | zero => rfl
  | succ p ih =>
    show isum f (m + p) + f (m + p) = isum f m
    rw [ih, hf (m + p) (Nat.le_add_right m p)]
    omega

/-- **M307F-0e: 台安定性** — m 以上で消える f は m ≤ n なら和が bound に依らない。 -/
theorem isum_stable (f : Nat → Int) (m n : Nat) (hf : ∀ k, m ≤ k → f k = 0)
    (hmn : m ≤ n) : isum f n = isum f m := by
  obtain ⟨j, hj⟩ := Nat.le.dest hmn
  rw [← hj]
  exact isum_ext_zero f m hf j

/-- **M307F-0f: 斉次性** Σ(c·f) = c·Σf。 -/
theorem isum_smul (c : Int) (f : Nat → Int) :
    ∀ n, isum (fun k => c * f k) n = c * isum f n := by
  intro n
  induction n with
  | zero =>
    show (0 : Int) = c * 0
    rw [Int.mul_zero]
  | succ p ih =>
    show isum (fun k => c * f k) p + c * f p = c * (isum f p + f p)
    rw [ih, Int.mul_add]

/-! ## M307F-1: 因子の代表 RawDiv（素点→ℤ の有限台関数） -/

/-- **M307F-1: 因子の代表** — 素点（k 番目の素因子）ごとの重複度 coeff:ℕ→ℤ と
    有限台の上界 bound（bound 以上の素点では 0）。Σ nₖ[Pₖ] の実体。 -/
structure RawDiv where
  coeff : Nat → Int
  bound : Nat
  vanish : ∀ k, bound ≤ k → coeff k = 0

/-- 零因子 0。 -/
def rawZero : RawDiv where
  coeff := fun _ => 0
  bound := 0
  vanish := fun _ _ => rfl

/-- 因子の和（点ごと加法、台は max）。 -/
def rawAdd (x y : RawDiv) : RawDiv where
  coeff := fun k => x.coeff k + y.coeff k
  bound := Nat.max x.bound y.bound
  vanish := fun k hk => by
    have hx := x.vanish k (Nat.le_trans (Nat.le_max_left x.bound y.bound) hk)
    have hy := y.vanish k (Nat.le_trans (Nat.le_max_right x.bound y.bound) hk)
    omega

/-- 因子の逆元（点ごと符号反転、台は不変）。 -/
def rawNeg (x : RawDiv) : RawDiv where
  coeff := fun k => -(x.coeff k)
  bound := x.bound
  vanish := fun k hk => by
    have hx := x.vanish k hk
    omega

/-! ## M307F-2: 係数等価（bound 非依存の因子等価） -/

/-- **M307F-2: 係数等価** — 二因子は各素点での重複度が等しければ等しい
    （bound の取り方に依らない自由アーベル群の等価）。 -/
def rawEq (x y : RawDiv) : Prop := ∀ k, x.coeff k = y.coeff k

theorem rawEq_refl (x : RawDiv) : rawEq x x := fun _ => rfl
theorem rawEq_symm {x y : RawDiv} (h : rawEq x y) : rawEq y x := fun k => (h k).symm
theorem rawEq_trans {x y z : RawDiv} (h1 : rawEq x y) (h2 : rawEq y z) :
    rawEq x z := fun k => (h1 k).trans (h2 k)

/-! ## M307F-3: 因子群 Div = Quot rawEq 上のアーベル群 -/

/-- 商上の積（因子の和、Quot.lift の二重適用）。 -/
def picDivMul (x y : Quot rawEq) : Quot rawEq :=
  Quot.lift
    (fun a => Quot.lift (fun b => Quot.mk rawEq (rawAdd a b))
      (fun _ _ hb => Quot.sound (fun k => by
        show a.coeff k + _ = a.coeff k + _
        rw [hb k])) y)
    (fun a a' ha => by
      induction y using Quot.ind
      rename_i b
      exact Quot.sound (fun k => by
        show a.coeff k + b.coeff k = a'.coeff k + b.coeff k
        rw [ha k])) x

/-- 商上の逆元（因子の符号反転）。 -/
def picDivInv (x : Quot rawEq) : Quot rawEq :=
  Quot.lift (fun a => Quot.mk rawEq (rawNeg a))
    (fun _ _ ha => Quot.sound (fun k => by
      show -_ = -_
      rw [ha k])) x

/-- **M307F-3: 因子群 Div** — 素点上の有限台 ℤ-値関数のなす自由アーベル群。
    群公理（結合・単位・逆元）を Quot.ind＋Quot.sound で完全証明。
    これは M51F QDiv（有効因子モノイド）の**群化**（逆元 rawNeg を持つ）。 -/
def picDivGrp : Grp where
  carrier := Quot rawEq
  mul := picDivMul
  one := Quot.mk rawEq rawZero
  inv := picDivInv
  mul_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    induction z using Quot.ind; rename_i c
    show Quot.mk rawEq (rawAdd (rawAdd a b) c)
        = Quot.mk rawEq (rawAdd a (rawAdd b c))
    exact Quot.sound (fun k => by
      show (a.coeff k + b.coeff k) + c.coeff k
          = a.coeff k + (b.coeff k + c.coeff k)
      omega)
  one_mul := by
    intro x
    induction x using Quot.ind; rename_i a
    show Quot.mk rawEq (rawAdd rawZero a) = Quot.mk rawEq a
    exact Quot.sound (fun k => by
      show (0 : Int) + a.coeff k = a.coeff k
      omega)
  inv_mul := by
    intro x
    induction x using Quot.ind; rename_i a
    show Quot.mk rawEq (rawAdd (rawNeg a) a) = Quot.mk rawEq rawZero
    exact Quot.sound (fun k => by
      show -(a.coeff k) + a.coeff k = (0 : Int)
      omega)

/-! ## M307F-4: Div のアーベル性 → 部分群は正規 -/

/-- **M307F-4a: 因子群は可換**。 -/
theorem picDivGrp_comm (x y : picDivGrp.carrier) :
    picDivGrp.mul x y = picDivGrp.mul y x := by
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  show Quot.mk rawEq (rawAdd a b) = Quot.mk rawEq (rawAdd b a)
  exact Quot.sound (fun k => by
    show a.coeff k + b.coeff k = b.coeff k + a.coeff k
    omega)

/-- **M307F-4b: アーベル群の任意の部分群は正規** — gng⁻¹ = n。 -/
theorem picDivAbelianNormal (N : Subgroup picDivGrp) :
    IsNormalSubgroup picDivGrp N := by
  intro g n hn
  have hcomm : picDivGrp.mul (picDivGrp.mul g n) (picDivGrp.inv g) = n := by
    rw [picDivGrp_comm g n, picDivGrp.mul_assoc, picDivGrp.mul_inv, picDivGrp.mul_one]
  rw [hcomm]
  exact hn

/-! ## M307F-5: 次数準同型 deg : Div → ℤ -/

/-- **M307F-5: 次数準同型** deg(Σ nₖ[Pₖ]) = Σ nₖ。有限和が well-defined
    （係数等価な代表は bound が違っても同じ和、`isum_stable` 経由）で、
    deg(x+y)=deg x+deg y（`isum_add`）。本物の Hom into `intGrp`。 -/
def picDivDegree : Hom picDivGrp intGrp where
  map := Quot.lift (fun a => isum a.coeff a.bound)
    (fun a a' ha => by
      show isum a.coeff a.bound = isum a'.coeff a'.bound
      have h1 : isum a.coeff a.bound
              = isum a.coeff (Nat.max a.bound a'.bound) :=
        (isum_stable a.coeff a.bound (Nat.max a.bound a'.bound) a.vanish
          (Nat.le_max_left a.bound a'.bound)).symm
      have h2 : isum a'.coeff a'.bound
              = isum a'.coeff (Nat.max a.bound a'.bound) :=
        (isum_stable a'.coeff a'.bound (Nat.max a.bound a'.bound) a'.vanish
          (Nat.le_max_right a.bound a'.bound)).symm
      have h3 : isum a.coeff (Nat.max a.bound a'.bound)
              = isum a'.coeff (Nat.max a.bound a'.bound) :=
        isum_congr ha (Nat.max a.bound a'.bound)
      rw [h1, h2, h3])
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show isum (fun k => a.coeff k + b.coeff k) (Nat.max a.bound b.bound)
        = isum a.coeff a.bound + isum b.coeff b.bound
    rw [isum_add,
      isum_stable a.coeff a.bound (Nat.max a.bound b.bound) a.vanish
        (Nat.le_max_left a.bound b.bound),
      isum_stable b.coeff b.bound (Nat.max a.bound b.bound) b.vanish
        (Nat.le_max_right a.bound b.bound)]

/-! ## M307F-6: 付値データと単項因子準同型 div : K^× → Div -/

/-- **M307F-6a: 付値データ** — 各素点 k の付値 ord_k:G→ℤ が加法的準同型
    （ord_k(ab)=ord_k a+ord_k b）で、各 a に対し有限個の素点でしか非零でない
    （fbound をデータで持つ）もの。K^× の実付値（M301F）で実体化する本物の普遍形。 -/
structure PicDivValuation (G : Grp) where
  ord : Nat → G.carrier → Int
  ord_mul : ∀ k a b, ord k (G.mul a b) = ord k a + ord k b
  fbound : G.carrier → Nat
  fbound_spec : ∀ a k, fbound a ≤ k → ord k a = 0

/-- **M307F-6b: 単項因子の代表** div(a) = Σ_k ord_k(a)[P_k]。 -/
def picDivPrincipalRaw {G : Grp} (v : PicDivValuation G) (a : G.carrier) : RawDiv where
  coeff := fun k => v.ord k a
  bound := v.fbound a
  vanish := fun k hk => v.fbound_spec a k hk

/-- **M307F-6c: 単項因子準同型** div : G(=K^×) → Div。
    div(ab)=div(a)+div(b)（付値の加法性 ord_mul）を本物で。 -/
def picDivPrincipalHom {G : Grp} (v : PicDivValuation G) : Hom G picDivGrp where
  map := fun a => Quot.mk rawEq (picDivPrincipalRaw v a)
  map_mul := fun a b => Quot.sound (fun k => by
    show v.ord k (G.mul a b) = v.ord k a + v.ord k b
    rw [v.ord_mul k a b])

/-! ## M307F-7: Picard 群 Pic = Div / im(div) -/

/-- **M307F-7a: 単項因子部分群** im(div) ⊆ Div（M267F `imSubgroup`）。 -/
def picDivPrincipalSub {G : Grp} (v : PicDivValuation G) : Subgroup picDivGrp :=
  imSubgroup (picDivPrincipalHom v)

/-- **M307F-7b: 単項因子部分群は正規**（Div はアーベル）。 -/
theorem picDivPrincipalNormal {G : Grp} (v : PicDivValuation G) :
    IsNormalSubgroup picDivGrp (picDivPrincipalSub v) :=
  picDivAbelianNormal (picDivPrincipalSub v)

/-- **M307F-7c: Picard 群** Pic = Div / im(div)（M267F `quotientGroupN`）。
    直線束の同型類群の代数的実体＝因子群を単項因子で割った cokernel。本物の群。 -/
def picDivPic {G : Grp} (v : PicDivValuation G) : Grp :=
  quotientGroupN picDivGrp (picDivPrincipalSub v) (picDivPrincipalNormal v)

/-- **M307F-7d: 射影 Div → Pic は全射準同型**（Pic が因子群の商であることの実体）。 -/
theorem picDiv_pic_proj_surjective {G : Grp} (v : PicDivValuation G) :
    ∀ x : (picDivPic v).carrier,
      ∃ D, (quotientProjN picDivGrp (picDivPrincipalSub v)
              (picDivPrincipalNormal v)).map D = x :=
  quotientProjN_surjective picDivGrp (picDivPrincipalSub v) (picDivPrincipalNormal v)

/-! ## M307F-8: Frobenius 作用 [n] と次数の斉次性 -/

/-- **M307F-8a: Frobenius 作用 [n] の代表** — 因子の n 倍（重複度を n 倍）。 -/
def picDivFrobRaw (n : Nat) (x : RawDiv) : RawDiv where
  coeff := fun k => (n : Int) * x.coeff k
  bound := x.bound
  vanish := fun k hk => by
    have h := x.vanish k hk
    rw [h, Int.mul_zero]

/-- **M307F-8b: Frobenius 自己準同型** [n] : Div → Div（[n](x+y)=[n]x+[n]y）。 -/
def picDivFrob (n : Nat) : Hom picDivGrp picDivGrp where
  map := Quot.lift (fun a => Quot.mk rawEq (picDivFrobRaw n a))
    (fun _ _ ha => Quot.sound (fun k => by
      show (n : Int) * _ = (n : Int) * _
      rw [ha k]))
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show Quot.mk rawEq (picDivFrobRaw n (rawAdd a b))
        = Quot.mk rawEq (rawAdd (picDivFrobRaw n a) (picDivFrobRaw n b))
    exact Quot.sound (fun k => by
      show (n : Int) * (a.coeff k + b.coeff k)
          = (n : Int) * a.coeff k + (n : Int) * b.coeff k
      rw [Int.mul_add])

/-- **M307F-8c: 次数の斉次性** deg([n]D) = n·deg D（M51F `degZ_frob` の群版）。 -/
theorem picDiv_frob_degree (n : Nat) (x : picDivGrp.carrier) :
    picDivDegree.map ((picDivFrob n).map x) = (n : Int) * picDivDegree.map x := by
  induction x using Quot.ind; rename_i a
  show isum (fun k => (n : Int) * a.coeff k) a.bound
      = (n : Int) * isum a.coeff a.bound
  rw [isum_smul]

/-! ## M307F-9: 有効因子モノイド（nₖ ≥ 0）— Frobenioid の因子面骨組み -/

/-- **M307F-9a: 有効因子** — 全素点で重複度が非負（Frobenioid の因子モノイド）。 -/
def picDivEffectiveRaw (x : RawDiv) : Prop := ∀ k, 0 ≤ x.coeff k

/-- **M307F-9b: 零因子は有効**。 -/
theorem picDivEffective_zero : picDivEffectiveRaw rawZero := by
  intro _
  show (0 : Int) ≤ 0
  omega

/-- **M307F-9c: 有効因子の和は有効**（因子モノイドが和で閉じる）。 -/
theorem picDivEffective_add {x y : RawDiv} (hx : picDivEffectiveRaw x)
    (hy : picDivEffectiveRaw y) : picDivEffectiveRaw (rawAdd x y) := by
  intro k
  have h1 := hx k
  have h2 := hy k
  show 0 ≤ x.coeff k + y.coeff k
  omega

/-- **M307F-9d: 有効因子の Frobenius 倍は有効**（[n] が因子モノイドを保つ）。 -/
theorem picDivEffective_frob {x : RawDiv} (n : Nat) (hx : picDivEffectiveRaw x) :
    picDivEffectiveRaw (picDivFrobRaw n x) := by
  intro k
  have h := hx k
  have hn : (0 : Int) ≤ (n : Int) := by omega
  show 0 ≤ (n : Int) * x.coeff k
  exact Int.mul_nonneg hn h

/-! ## M307F-10: 実例（体・PID） -/

/-- **M307F-10a: 自明付値** — 全付値 0（体は非零素イデアルを持たない ⇒ div≡0）。 -/
def picDivTrivialVal (G : Grp) : PicDivValuation G where
  ord := fun _ _ => 0
  ord_mul := fun _ _ _ => by show (0 : Int) = 0 + 0; omega
  fbound := fun _ => 0
  fbound_spec := fun _ _ _ => rfl

/-- **M307F-10b: 体では div(a) = 0**（全素点で重複度 0）。 -/
theorem picDiv_field_trivial (G : Grp) (a : G.carrier) (k : Nat) :
    (picDivPrincipalRaw (picDivTrivialVal G) a).coeff k = 0 := rfl

/-- **M307F-10c: 体では単項因子部分群の元は零因子**（im(div) = {0}）。 -/
theorem picDiv_field_im_one (G : Grp) (D : picDivGrp.carrier)
    (h : (picDivPrincipalSub (picDivTrivialVal G)).mem D) :
    D = picDivGrp.one := by
  obtain ⟨a, ha⟩ := h
  rw [← ha]
  exact Quot.sound (fun _ => rfl)

/-- **M307F-10d: PID では Pic = 0** — 単項因子が全射（全因子が単項）なら
    Picard 群は自明（全元が単位元）。イデアル類群 Cl=0 の骨組み。 -/
theorem picDiv_pic_trivial_of_surjective {G : Grp} (v : PicDivValuation G)
    (hsurj : ∀ D : picDivGrp.carrier, (picDivPrincipalSub v).mem D)
    (x : (picDivPic v).carrier) : x = (picDivPic v).one := by
  obtain ⟨D, hD⟩ := quotientProjN_surjective picDivGrp (picDivPrincipalSub v)
      (picDivPrincipalNormal v) x
  rw [← hD]
  exact (quotientProjN_ker picDivGrp (picDivPrincipalSub v)
      (picDivPrincipalNormal v) D).mpr (hsurj D)

/-! ## M307F-11: capstone -/

/-- **M307F-11a: Picard 因子データ** — 因子群・単項準同型・Picard 群・次数の束ね。 -/
structure PicardDivisorData {G : Grp} (v : PicDivValuation G) where
  div : Grp
  principal : Hom G div
  pic : Grp
  degree : Hom div intGrp

/-- **M307F-11b: 実データ** — 全フィールドを本物で充足。 -/
def picDivData {G : Grp} (v : PicDivValuation G) : PicardDivisorData v where
  div := picDivGrp
  principal := picDivPrincipalHom v
  pic := picDivPic v
  degree := picDivDegree

/-- **M307F-11c: 存在**（`Nonempty` でなく実データ）。 -/
theorem picDiv_exists {G : Grp} (v : PicDivValuation G) :
    Nonempty (PicardDivisorData v) := ⟨picDivData v⟩

/-- **M307F-11d: div は群準同型** div(ab)=div(a)+div(b)（付値の加法性）。 -/
theorem picDiv_principal_isHom {G : Grp} (v : PicDivValuation G) (a b : G.carrier) :
    (picDivPrincipalHom v).map (G.mul a b)
      = picDivGrp.mul ((picDivPrincipalHom v).map a) ((picDivPrincipalHom v).map b) :=
  (picDivPrincipalHom v).map_mul a b

/-- **M307F-11e: deg は群準同型** deg(x+y)=deg x+deg y。 -/
theorem picDiv_degree_isHom (x y : picDivGrp.carrier) :
    picDivDegree.map (picDivGrp.mul x y)
      = intGrp.mul (picDivDegree.map x) (picDivDegree.map y) :=
  picDivDegree.map_mul x y

end IUT
