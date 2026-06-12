/-
  IUT/PowerSeries3.lean — M63（三変数冪級数の基盤: 結合則キャンペーン第一層）

  形式群法則の**結合則** F(F(X,Y),Z) = F(X,F(Y,Z)) は三変数の議論を
  要する: 両辺とも三変数級数 G(X,Y,Z) として「G ≡ X+Y+Z mod 次数 2 と
  f∘G = G(f(X), f(Y), f(Z))」を満たすことを示し、**三変数の一意性**
  （M61 のスキーマの三変数版）で一致させるのが標準ルート。本層は
  その土台 — 三変数冪級数環と代入・方程式の定式化 — を建設する。

  方針は M50 の反復構成の再々適用: **PS3 R := PS(psRing(psRing R))**
  （R[[X]][[Y]][[Z]]、外から Z・Y・X）で環構造は無償。係数アクセスは
  G j k i = X^i Y^k Z^j の係数。新規の仕事は

  * M63-1 `RingHom.comp` — 環準同型の合成（注入の構成に使用）
  * M63-2 座標 X・Y・Z と線形部 X+Y+Z の係数
  * M63-3 `ps3Mul_coeff` — **三重 Cauchy 係数公式**（rsum_psRing_coeff
    の二段適用 + M57 の二変数公式）
  * M63-4 `ps3Pow_tcoeff_zero` — **総次数 truncation**: G₀₀₀ = 0 なら
    i+k+j < n で (G^n)_{j,k,i} = 0（M50 の証明の三変数版 — 四重和の
    各項を「総次数 < n の冪は帰納法・境界 (a,b,c) = (i,k,j) では
    G₀₀₀ = 0」で消す）。三変数代入の有限性の根拠
  * M63-5 `ps3Comp1` — 1 変数 → 3 変数代入 (f∘G)_{j,k,i}
    = Σ_{m ≤ i+k+j} f_m·(G^m)_{j,k,i}
  * M63-6 `in3X`/`in3Y`/`in3Z` — 1 変数級数の三方向注入
    （f(X)・f(Y)・f(Z)。psC/psMap/RingHom.comp の積み上げ）
  * M63-7 `ps3Comp3` — 3 変数 → 3 変数代入（三重矩形打ち切り）
  * M63-8 `IsLTFormalGroup3` — 三変数方程式の述語

  ロードマップ: 次層以降で三変数の係数合同（M57 版）・分解（M58/M59 版）
  ・一意性（M61 版）・両辺が方程式を満たすこと（合成の連鎖律）→ 結合則。
  全て選択公理不使用。
-/
import IUT.FormalGroupComm

namespace IUT

/-! ## 環準同型の合成 -/

/-- **M63-1: 環準同型の合成**。 -/
def RingHom.comp {A B C : CRing} (φ : RingHom A B) (ψ : RingHom B C) :
    RingHom A C where
  map := fun a => ψ.map (φ.map a)
  map_add := fun a b => by rw [φ.map_add, ψ.map_add]
  map_mul := fun a b => by rw [φ.map_mul, ψ.map_mul]
  map_one := by rw [φ.map_one, ψ.map_one]

/-! ## 三変数冪級数と座標 -/

/-- 三変数冪級数 R[[X]][[Y]][[Z]]（外から Z・Y・X）。
    係数アクセス: G j k i = X^i Y^k Z^j の係数。 -/
def PS3 (R : CRing) : Type := PS (psRing (psRing R))

/-- 座標 X（= (0,0,1) の単項式）。 -/
def ps3X (R : CRing) : PS3 R := psC (psRing (psRing R)) (ps2X R)

/-- 座標 Y（= (0,1,0) の単項式）。 -/
def ps3Y (R : CRing) : PS3 R := psC (psRing (psRing R)) (ps2Y R)

/-- 座標 Z（= (1,0,0) の単項式）。 -/
def ps3Z (R : CRing) : PS3 R := psX (psRing (psRing R))

/-- 線形部 X + Y + Z。 -/
def ps3Lin (R : CRing) : PS3 R :=
  psAdd (psRing (psRing R))
    (psAdd (psRing (psRing R)) (ps3X R) (ps3Y R)) (ps3Z R)

/-- 線形部の係数: 定数項 0。 -/
theorem ps3Lin_000 (R : CRing) : ps3Lin R 0 0 0 = R.zero := by
  show R.add (R.add R.zero R.zero) R.zero = R.zero
  rw [R.zero_add, R.zero_add]

/-- 線形部の係数: X の係数 1。 -/
theorem ps3Lin_001 (R : CRing) : ps3Lin R 0 0 1 = R.one := by
  show R.add (R.add R.one R.zero) R.zero = R.one
  rw [CRing.add_zero R _, CRing.add_zero R _]

/-- 線形部の係数: Y の係数 1。 -/
theorem ps3Lin_010 (R : CRing) : ps3Lin R 0 1 0 = R.one := by
  show R.add (R.add R.zero R.one) R.zero = R.one
  rw [R.zero_add, CRing.add_zero R _]

/-- 線形部の係数: Z の係数 1。 -/
theorem ps3Lin_100 (R : CRing) : ps3Lin R 1 0 0 = R.one := by
  show R.add (R.add R.zero R.zero) R.one = R.one
  rw [R.zero_add, R.zero_add]

/-! ## 三重 Cauchy 係数公式 -/

/-- **定理 (M63-3): 三重 Cauchy 係数公式** — (A·B)_{j,k,i}
    = Σ_{c≤j} Σ_{b≤k} Σ_{a≤i} A_{c,b,a}·B_{j−c,k−b,i−a}
    （外側二層を rsum_psRing_coeff で係数化し、各項に M57 の
    二変数公式を適用）。 -/
theorem ps3Mul_coeff (R : CRing) (A B : PS3 R) (j k i : Nat) :
    psMul (psRing (psRing R)) A B j k i
      = rsum R (fun c => rsum R (fun b => rsum R (fun a =>
          R.mul (A c b a) (B (j - c) (k - b) (i - a))) (i + 1)) (k + 1))
          (j + 1) := by
  have h1 : psMul (psRing (psRing R)) A B j k i
      = rsum (psRing R) (fun c =>
          (psRing (psRing R)).mul (A c) (B (j - c)) k) (j + 1) i :=
    congrFun (rsum_psRing_coeff (psRing R)
      (fun c => (psRing (psRing R)).mul (A c) (B (j - c))) k (j + 1)) i
  have h2 : rsum (psRing R) (fun c =>
        (psRing (psRing R)).mul (A c) (B (j - c)) k) (j + 1) i
      = rsum R (fun c =>
          (psRing (psRing R)).mul (A c) (B (j - c)) k i) (j + 1) :=
    rsum_psRing_coeff R
      (fun c => (psRing (psRing R)).mul (A c) (B (j - c)) k) i (j + 1)
  rw [h1, h2]
  exact rsum_congr R (j + 1) (fun c _ =>
    ps2Mul_coeff R (A c) (B (j - c)) k i)

/-! ## 総次数 truncation -/

/-- **定理 (M63-4): 総次数 truncation（三変数）** — G₀₀₀ = 0 なら
    i + k + j < n で (G^n)_{j,k,i} = 0。M50 の証明の三変数版:
    四重和の各項は「総次数 < n の冪は帰納法・境界 (a,b,c) = (i,k,j)
    では G₀₀₀ = 0」で消える。三変数代入の有限性の根拠。 -/
theorem ps3Pow_tcoeff_zero (R : CRing) (G : PS3 R)
    (hG : G 0 0 0 = R.zero) :
    ∀ n i k j, i + k + j < n →
      psPow (psRing (psRing R)) G n j k i = R.zero := by
  intro n
  induction n with
  | zero => intro i k j h; exact absurd h (by omega)
  | succ n ih =>
    intro i k j h
    show psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) G n) G j k i = R.zero
    rw [ps3Mul_coeff R (psPow (psRing (psRing R)) G n) G j k i]
    have hc : rsum R (fun c => rsum R (fun b => rsum R (fun a =>
          R.mul (psPow (psRing (psRing R)) G n c b a)
            (G (j - c) (k - b) (i - a))) (i + 1)) (k + 1)) (j + 1)
        = rsum R (fun _ => R.zero) (j + 1) :=
      rsum_congr R (j + 1) (fun c hc => by
        have hb : rsum R (fun b => rsum R (fun a =>
              R.mul (psPow (psRing (psRing R)) G n c b a)
                (G (j - c) (k - b) (i - a))) (i + 1)) (k + 1)
            = rsum R (fun _ => R.zero) (k + 1) :=
          rsum_congr R (k + 1) (fun b hb => by
            have ha : rsum R (fun a =>
                  R.mul (psPow (psRing (psRing R)) G n c b a)
                    (G (j - c) (k - b) (i - a))) (i + 1)
                = rsum R (fun _ => R.zero) (i + 1) :=
              rsum_congr R (i + 1) (fun a ha => by
                cases Nat.lt_or_ge (a + b + c) n with
                | inl hlt =>
                  rw [ih a b c hlt]
                  exact R.zero_mul _
                | inr hge =>
                  have hai : a = i := by omega
                  have hbk : b = k := by omega
                  have hcj : c = j := by omega
                  rw [hai, hbk, hcj, show j - j = 0 by omega,
                    show k - k = 0 by omega, show i - i = 0 by omega,
                    hG]
                  exact R.mul_zero _)
            rw [ha]
            exact rsum_const_zero R (i + 1))
        rw [hb]
        exact rsum_const_zero R (k + 1))
    rw [hc]
    exact rsum_const_zero R (j + 1)

/-! ## 代入と注入 -/

/-- **M63-5: 1 変数 → 3 変数代入** (f∘G)_{j,k,i}
    = Σ_{m ≤ i+k+j} f_m·(G^m)_{j,k,i}（G₀₀₀ = 0 のとき総次数
    truncation により真の代入と一致）。 -/
def ps3Comp1 (R : CRing) (f : PS R) (G : PS3 R) : PS3 R :=
  fun j k i =>
    rsum R (fun m => R.mul (f m)
      (psPow (psRing (psRing R)) G m j k i)) (i + k + j + 1)

/-- **M63-6a: X 方向注入** f(X)（j = k = 0 の層に f）。 -/
def in3X (R : CRing) (f : PS R) : PS3 R :=
  psC (psRing (psRing R)) (psC (psRing R) f)

/-- **M63-6b: Y 方向注入** f(Y)。 -/
def in3Y (R : CRing) (f : PS R) : PS3 R :=
  psC (psRing (psRing R)) (psMap (psConstHom R) f)

/-- **M63-6c: Z 方向注入** f(Z)（係数ごとの二重定数埋め込み）。 -/
def in3Z (R : CRing) (f : PS R) : PS3 R :=
  psMap (RingHom.comp (psConstHom R) (psConstHom (psRing R))) f

/-- 注入の定数項: in3X f の (0,0,0) 係数 = f₀。 -/
theorem in3X_000 (R : CRing) (f : PS R) : in3X R f 0 0 0 = f 0 := rfl

/-- 注入の定数項: in3Y f の (0,0,0) 係数 = f₀。 -/
theorem in3Y_000 (R : CRing) (f : PS R) : in3Y R f 0 0 0 = f 0 := rfl

/-- 注入の定数項: in3Z f の (0,0,0) 係数 = f₀。 -/
theorem in3Z_000 (R : CRing) (f : PS R) : in3Z R f 0 0 0 = f 0 := rfl

/-- **M63-7: 3 変数 → 3 変数代入** G(P,Q,W)_{j,k,i}
    = Σ_{c,b,a ≤ i+k+j} G_{c,b,a}·(P^a Q^b W^c)_{j,k,i}
    （三重矩形打ち切り。P₀₀₀ = Q₀₀₀ = W₀₀₀ = 0 のとき総次数
    truncation により真の代入と一致）。 -/
def ps3Comp3 (R : CRing) (G P Q W : PS3 R) : PS3 R :=
  fun j k i =>
    rsum R (fun c => rsum R (fun b => rsum R (fun a =>
      R.mul (G c b a)
        ((psMul (psRing (psRing R))
          (psMul (psRing (psRing R))
            (psPow (psRing (psRing R)) P a)
            (psPow (psRing (psRing R)) Q b))
          (psPow (psRing (psRing R)) W c)) j k i))
      (i + k + j + 1)) (i + k + j + 1)) (i + k + j + 1)

/-! ## 三変数方程式の述語 -/

/-- **M63-8: 三変数 LT 方程式の述語** — G ≡ X + Y + Z（mod 次数 2）かつ
    f∘G = G(f(X), f(Y), f(Z))（f = pX + X^p）。結合則の両辺
    F(F(X,Y),Z)・F(X,F(Y,Z)) がともにこれを満たすことを次層以降で示し、
    三変数一意性で結合則を得るのが標準ルート。 -/
def IsLTFormalGroup3 (p : Nat) (G : PS3 (zpRing p)) : Prop :=
  G 0 0 0 = (zpRing p).zero ∧
  G 0 0 1 = (zpRing p).one ∧
  G 0 1 0 = (zpRing p).one ∧
  G 1 0 0 = (zpRing p).one ∧
  ps3Comp1 (zpRing p) (ltPoly p) G
    = ps3Comp3 (zpRing p) G (in3X (zpRing p) (ltPoly p))
        (in3Y (zpRing p) (ltPoly p)) (in3Z (zpRing p) (ltPoly p))

/-- サニティアンカー: 線形部 X + Y + Z は一次条件を満たす。 -/
theorem ps3Lin_linear_conditions (p : Nat) :
    ps3Lin (zpRing p) 0 0 0 = (zpRing p).zero
    ∧ ps3Lin (zpRing p) 0 0 1 = (zpRing p).one
    ∧ ps3Lin (zpRing p) 0 1 0 = (zpRing p).one
    ∧ ps3Lin (zpRing p) 1 0 0 = (zpRing p).one :=
  ⟨ps3Lin_000 (zpRing p), ps3Lin_001 (zpRing p),
    ps3Lin_010 (zpRing p), ps3Lin_100 (zpRing p)⟩

end IUT
