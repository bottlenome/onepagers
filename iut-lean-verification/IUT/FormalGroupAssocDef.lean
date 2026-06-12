/-
  IUT/FormalGroupAssocDef.lean — M67（結合則の両辺の構成と一次条件:
  結合則キャンペーン第五層）

  結合則の両辺 F(F(X,Y), Z)・F(X, F(Y,Z)) を三変数級数として構成し、
  **一次条件**（≡ X + Y + Z mod 次数 2）を検証する。M66 の三変数一意性に
  かけるための「候補が IsLTFormalGroup3 の一次条件を満たす」部分で、
  残る方程式成分（合成の連鎖律）は次層。

  * M67-1 `ps23Comp` — **2 変数 → 3 変数代入** F(P, Q)_{j,k,i}
    = Σ_{b,a ≤ i+k+j} F_{b,a}·(P^a Q^b)_{j,k,i}
  * M67-2 `liftXY` / `liftYZ` — 2 変数級数の三変数化
    F(X,Y)（Z 定数方向の psC）・F(Y,Z)（X 定数方向の psMap、
    M53 の psRingHom を再利用）と係数読み出し
  * M67-3 `ps3Mul_deg1_zero` / `lin23_collapse` — 総次数 1 での
    積の消滅（定数項消滅から）と線形部の折りたたみ簿記
  * M67-4 `ps23Comp_000` / `ps23Comp_lin` — **代入の定数項と線形部**:
    F₀₀ = P₀₀₀ = Q₀₀₀ = 0 のとき、(F(P,Q))₀₀₀ = 0 かつ総次数 1 の
    係数 = F₀₁·P + F₁₀·Q（4 項展開の master 補題）
  * M67-5 `assocL` / `assocR` と**一次条件 8 本** — 両辺の構成と
    A₀₀₀ = 0・A₀₀₁ = A₀₁₀ = A₁₀₀ = 1（B も同様。F の一次条件
    F₀₁ = F₁₀ = 1 と座標・lift の係数から）

  全て選択公理不使用。
-/
import IUT.FormalGroup3Unique

namespace IUT

/-! ## 2 変数 → 3 変数代入と lift -/

/-- **M67-1: 2 変数 → 3 変数代入** F(P, Q)_{j,k,i}
    = Σ_{b,a ≤ i+k+j} F_{b,a}·(P^a Q^b)_{j,k,i}（P₀₀₀ = Q₀₀₀ = 0 の
    とき M63 の総次数 truncation により真の代入と一致）。 -/
def ps23Comp (R : CRing) (F : PS2 R) (P Q : PS3 R) : PS3 R :=
  fun j k i =>
    rsum R (fun b => rsum R (fun a =>
      R.mul (F b a)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i))
      (i + k + j + 1)) (i + k + j + 1)

/-- **M67-2a: F(X,Y) の三変数化**（Z 定数方向）。 -/
def liftXY (R : CRing) (F : PS2 R) : PS3 R :=
  psC (psRing (psRing R)) F

/-- **M67-2b: F(Y,Z) の三変数化**（X 定数方向、係数ごとの psMap）。 -/
def liftYZ (R : CRing) (F : PS2 R) : PS3 R :=
  psMap (psRingHom (psConstHom R)) F

/-- liftXY の係数（j = 0 層は F、j ≥ 1 は 0）。 -/
theorem liftXY_000 (R : CRing) (F : PS2 R) :
    liftXY R F 0 0 0 = F 0 0 := rfl

theorem liftXY_001 (R : CRing) (F : PS2 R) :
    liftXY R F 0 0 1 = F 0 1 := rfl

theorem liftXY_010 (R : CRing) (F : PS2 R) :
    liftXY R F 0 1 0 = F 1 0 := rfl

theorem liftXY_100 (R : CRing) (F : PS2 R) :
    liftXY R F 1 0 0 = R.zero := rfl

/-- liftYZ の係数（i = 0 層は F、i ≥ 1 は 0）。 -/
theorem liftYZ_000 (R : CRing) (F : PS2 R) :
    liftYZ R F 0 0 0 = F 0 0 := rfl

theorem liftYZ_001 (R : CRing) (F : PS2 R) :
    liftYZ R F 0 0 1 = R.zero := rfl

theorem liftYZ_010 (R : CRing) (F : PS2 R) :
    liftYZ R F 0 1 0 = F 0 1 := rfl

theorem liftYZ_100 (R : CRing) (F : PS2 R) :
    liftYZ R F 1 0 0 = F 1 0 := rfl

/-- 座標 X・Z の一次係数（rfl 読み出し）。 -/
theorem ps3X_000 (R : CRing) : ps3X R 0 0 0 = R.zero := rfl
theorem ps3X_001 (R : CRing) : ps3X R 0 0 1 = R.one := rfl
theorem ps3X_010 (R : CRing) : ps3X R 0 1 0 = R.zero := rfl
theorem ps3X_100 (R : CRing) : ps3X R 1 0 0 = R.zero := rfl
theorem ps3Z_000 (R : CRing) : ps3Z R 0 0 0 = R.zero := rfl
theorem ps3Z_001 (R : CRing) : ps3Z R 0 0 1 = R.zero := rfl
theorem ps3Z_010 (R : CRing) : ps3Z R 0 1 0 = R.zero := rfl
theorem ps3Z_100 (R : CRing) : ps3Z R 1 0 0 = R.one := rfl

/-! ## 総次数 1 の簿記 -/

/-- **M67-3a: 総次数 1 での積の消滅** — A₀₀₀ = B₀₀₀ = 0 なら
    (A·B) の総次数 1 の係数は 0（各項のどちらかの因子が定数項）。 -/
theorem ps3Mul_deg1_zero (R : CRing) (A B : PS3 R)
    (hA : A 0 0 0 = R.zero) (hB : B 0 0 0 = R.zero)
    (j k i : Nat) (hdeg : i + k + j = 1) :
    psMul (psRing (psRing R)) A B j k i = R.zero := by
  rw [ps3Mul_coeff R A B j k i]
  have hz : rsum R (fun c => rsum R (fun b => rsum R (fun a =>
        R.mul (A c b a) (B (j - c) (k - b) (i - a))) (i + 1)) (k + 1))
        (j + 1)
      = rsum R (fun _ => R.zero) (j + 1) :=
    rsum_congr R (j + 1) (fun c hc => by
      have hz2 : rsum R (fun b => rsum R (fun a =>
            R.mul (A c b a) (B (j - c) (k - b) (i - a))) (i + 1)) (k + 1)
          = rsum R (fun _ => R.zero) (k + 1) :=
        rsum_congr R (k + 1) (fun b hb => by
          have hz3 : rsum R (fun a =>
                R.mul (A c b a) (B (j - c) (k - b) (i - a))) (i + 1)
              = rsum R (fun _ => R.zero) (i + 1) :=
            rsum_congr R (i + 1) (fun a ha => by
              cases Nat.decEq (c + b + a) 0 with
              | isTrue h0 =>
                have hc0 : c = 0 := by omega
                have hb0 : b = 0 := by omega
                have ha0 : a = 0 := by omega
                subst hc0
                subst hb0
                subst ha0
                rw [hA]
                exact R.zero_mul _
              | isFalse h0 =>
                have hjc : j - c = 0 := by omega
                have hkb : k - b = 0 := by omega
                have hia : i - a = 0 := by omega
                rw [hjc, hkb, hia, hB]
                exact R.mul_zero _)
          rw [hz3]
          exact rsum_const_zero R (i + 1))
      rw [hz2]
      exact rsum_const_zero R (k + 1))
  rw [hz]
  exact rsum_const_zero R (j + 1)

/-- **M67-3b: 線形部の折りたたみ** —
    (0 + ((0+0) + x)) + ((0 + y) + 0) = x + y。 -/
theorem lin23_collapse (R : CRing) (x y : R.carrier) :
    R.add (R.add R.zero (R.add (R.add R.zero R.zero) x))
      (R.add (R.add R.zero y) R.zero) = R.add x y := by
  rw [R.zero_add R.zero, R.zero_add x, R.zero_add x, R.zero_add y,
    CRing.add_zero R y]

/-! ## 代入の定数項と線形部 -/

/-- **M67-4a: 代入の定数項** — F₀₀ = 0 なら (F(P,Q))₀₀₀ = 0。 -/
theorem ps23Comp_000 (R : CRing) (F : PS2 R) (P Q : PS3 R)
    (hF : F 0 0 = R.zero) :
    ps23Comp R F P Q 0 0 0 = R.zero := by
  show R.add R.zero (R.add R.zero
      (R.mul (F 0 0)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P 0)
          (psPow (psRing (psRing R)) Q 0)) 0 0 0))) = R.zero
  rw [hF, R.zero_mul, R.zero_add (R.add R.zero R.zero),
    R.zero_add R.zero]

/-- **定理 (M67-4b): 代入の線形部（master 補題）** —
    F₀₀ = P₀₀₀ = Q₀₀₀ = 0 のとき、総次数 1 の係数は
    F(P,Q)_{j,k,i} = F₀₁·P_{j,k,i} + F₁₀·Q_{j,k,i}
    （4 項展開: (0,0) 項は F₀₀ = 0、(1,1) 項は積の総次数 1 消滅）。 -/
theorem ps23Comp_lin (R : CRing) (F : PS2 R) (P Q : PS3 R)
    (hF : F 0 0 = R.zero) (hP : P 0 0 0 = R.zero)
    (hQ : Q 0 0 0 = R.zero) (j k i : Nat) (hdeg : i + k + j = 1) :
    ps23Comp R F P Q j k i
      = R.add (R.mul (F 0 1) (P j k i)) (R.mul (F 1 0) (Q j k i)) := by
  show rsum R (fun b => rsum R (fun a =>
      R.mul (F b a)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P a)
          (psPow (psRing (psRing R)) Q b)) j k i))
      (i + k + j + 1)) (i + k + j + 1) = _
  rw [show i + k + j + 1 = 2 from by omega]
  show R.add (R.add R.zero (R.add (R.add R.zero
      (R.mul (F 0 0)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P 0)
          (psPow (psRing (psRing R)) Q 0)) j k i)))
      (R.mul (F 0 1)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P 1)
          (psPow (psRing (psRing R)) Q 0)) j k i))))
    (R.add (R.add R.zero
      (R.mul (F 1 0)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P 0)
          (psPow (psRing (psRing R)) Q 1)) j k i)))
      (R.mul (F 1 1)
        ((psMul (psRing (psRing R))
          (psPow (psRing (psRing R)) P 1)
          (psPow (psRing (psRing R)) Q 1)) j k i)))
    = _
  rw [hF, R.zero_mul, ps3Pow_one R P, ps3Pow_one R Q,
    show psMul (psRing (psRing R)) P
        (psPow (psRing (psRing R)) Q 0) = P from
      CRing.mul_one (psRing (psRing (psRing R))) P,
    show psMul (psRing (psRing R))
        (psPow (psRing (psRing R)) P 0) Q = Q from
      (psRing (psRing (psRing R))).one_mul Q,
    ps3Mul_deg1_zero R P Q hP hQ j k i hdeg,
    R.mul_zero (F 1 1)]
  exact lin23_collapse R _ _

/-! ## 結合則の両辺と一次条件 -/

/-- **M67-5a: 結合則の左辺** A := F(F(X,Y), Z)。 -/
def assocL (p : Nat) (hp : IsPrime p) : PS3 (zpRing p) :=
  ps23Comp (zpRing p) (lt2Sol p hp)
    (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p))

/-- **M67-5b: 結合則の右辺** B := F(X, F(Y,Z))。 -/
def assocR (p : Nat) (hp : IsPrime p) : PS3 (zpRing p) :=
  ps23Comp (zpRing p) (lt2Sol p hp)
    (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp))

/-- 左辺の定数項 = 0。 -/
theorem assocL_000 (p : Nat) (hp : IsPrime p) :
    assocL p hp 0 0 0 = (zpRing p).zero :=
  ps23Comp_000 (zpRing p) (lt2Sol p hp)
    (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p)) rfl

/-- 右辺の定数項 = 0。 -/
theorem assocR_000 (p : Nat) (hp : IsPrime p) :
    assocR p hp 0 0 0 = (zpRing p).zero :=
  ps23Comp_000 (zpRing p) (lt2Sol p hp)
    (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp)) rfl

/-- 簿記: 1·1 + 1·0 = 1。 -/
theorem one_one_add_one_zero (R : CRing) :
    R.add (R.mul R.one R.one) (R.mul R.one R.zero) = R.one := by
  rw [CRing.mul_one R R.one, R.mul_zero R.one, CRing.add_zero R R.one]

/-- 簿記: 1·0 + 1·1 = 1。 -/
theorem one_zero_add_one_one (R : CRing) :
    R.add (R.mul R.one R.zero) (R.mul R.one R.one) = R.one := by
  rw [CRing.mul_one R R.one, R.mul_zero R.one, R.zero_add R.one]

/-- **定理 (M67-5c): 左辺の一次条件** — A ≡ X + Y + Z（mod 次数 2）。 -/
theorem assocL_linear (p : Nat) (hp : IsPrime p) :
    assocL p hp 0 0 1 = (zpRing p).one
    ∧ assocL p hp 0 1 0 = (zpRing p).one
    ∧ assocL p hp 1 0 0 = (zpRing p).one := by
  have hF := lt2Sol_is_formal_group p hp
  refine ⟨?_, ?_, ?_⟩
  · rw [show assocL p hp 0 0 1
        = (zpRing p).add
            ((zpRing p).mul (lt2Sol p hp 0 1)
              (liftXY (zpRing p) (lt2Sol p hp) 0 0 1))
            ((zpRing p).mul (lt2Sol p hp 1 0) (ps3Z (zpRing p) 0 0 1))
      from ps23Comp_lin (zpRing p) (lt2Sol p hp)
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p))
        hF.1 hF.1 rfl 0 0 1 (by omega),
      liftXY_001 (zpRing p) (lt2Sol p hp), hF.2.1, hF.2.2.1,
      ps3Z_001 (zpRing p)]
    exact one_one_add_one_zero (zpRing p)
  · rw [show assocL p hp 0 1 0
        = (zpRing p).add
            ((zpRing p).mul (lt2Sol p hp 0 1)
              (liftXY (zpRing p) (lt2Sol p hp) 0 1 0))
            ((zpRing p).mul (lt2Sol p hp 1 0) (ps3Z (zpRing p) 0 1 0))
      from ps23Comp_lin (zpRing p) (lt2Sol p hp)
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p))
        hF.1 hF.1 rfl 0 1 0 (by omega),
      liftXY_010 (zpRing p) (lt2Sol p hp), hF.2.1, hF.2.2.1,
      ps3Z_010 (zpRing p)]
    exact one_one_add_one_zero (zpRing p)
  · rw [show assocL p hp 1 0 0
        = (zpRing p).add
            ((zpRing p).mul (lt2Sol p hp 0 1)
              (liftXY (zpRing p) (lt2Sol p hp) 1 0 0))
            ((zpRing p).mul (lt2Sol p hp 1 0) (ps3Z (zpRing p) 1 0 0))
      from ps23Comp_lin (zpRing p) (lt2Sol p hp)
        (liftXY (zpRing p) (lt2Sol p hp)) (ps3Z (zpRing p))
        hF.1 hF.1 rfl 1 0 0 (by omega),
      liftXY_100 (zpRing p) (lt2Sol p hp), hF.2.1, hF.2.2.1,
      ps3Z_100 (zpRing p)]
    exact one_zero_add_one_one (zpRing p)

/-- **定理 (M67-5d): 右辺の一次条件** — B ≡ X + Y + Z（mod 次数 2）。 -/
theorem assocR_linear (p : Nat) (hp : IsPrime p) :
    assocR p hp 0 0 1 = (zpRing p).one
    ∧ assocR p hp 0 1 0 = (zpRing p).one
    ∧ assocR p hp 1 0 0 = (zpRing p).one := by
  have hF := lt2Sol_is_formal_group p hp
  refine ⟨?_, ?_, ?_⟩
  · rw [show assocR p hp 0 0 1
        = (zpRing p).add
            ((zpRing p).mul (lt2Sol p hp 0 1) (ps3X (zpRing p) 0 0 1))
            ((zpRing p).mul (lt2Sol p hp 1 0)
              (liftYZ (zpRing p) (lt2Sol p hp) 0 0 1))
      from ps23Comp_lin (zpRing p) (lt2Sol p hp)
        (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp))
        hF.1 rfl
        (show liftYZ (zpRing p) (lt2Sol p hp) 0 0 0 = (zpRing p).zero
          from hF.1) 0 0 1 (by omega),
      ps3X_001 (zpRing p), hF.2.1, hF.2.2.1,
      liftYZ_001 (zpRing p) (lt2Sol p hp)]
    exact one_one_add_one_zero (zpRing p)
  · rw [show assocR p hp 0 1 0
        = (zpRing p).add
            ((zpRing p).mul (lt2Sol p hp 0 1) (ps3X (zpRing p) 0 1 0))
            ((zpRing p).mul (lt2Sol p hp 1 0)
              (liftYZ (zpRing p) (lt2Sol p hp) 0 1 0))
      from ps23Comp_lin (zpRing p) (lt2Sol p hp)
        (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp))
        hF.1 rfl
        (show liftYZ (zpRing p) (lt2Sol p hp) 0 0 0 = (zpRing p).zero
          from hF.1) 0 1 0 (by omega),
      ps3X_010 (zpRing p), hF.2.1, hF.2.2.1,
      liftYZ_010 (zpRing p) (lt2Sol p hp)]
    exact one_zero_add_one_one (zpRing p)
  · rw [show assocR p hp 1 0 0
        = (zpRing p).add
            ((zpRing p).mul (lt2Sol p hp 0 1) (ps3X (zpRing p) 1 0 0))
            ((zpRing p).mul (lt2Sol p hp 1 0)
              (liftYZ (zpRing p) (lt2Sol p hp) 1 0 0))
      from ps23Comp_lin (zpRing p) (lt2Sol p hp)
        (ps3X (zpRing p)) (liftYZ (zpRing p) (lt2Sol p hp))
        hF.1 rfl
        (show liftYZ (zpRing p) (lt2Sol p hp) 0 0 0 = (zpRing p).zero
          from hF.1) 1 0 0 (by omega),
      ps3X_100 (zpRing p), hF.2.1, hF.2.2.1,
      liftYZ_100 (zpRing p) (lt2Sol p hp)]
    exact one_zero_add_one_one (zpRing p)

end IUT
