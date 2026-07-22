/-
  IUT/LambdaModule.lean — M105（柱B B-1 第一段: λ の [c]-倍作用と Λ₁ の位数 p）

  issue #36 B-1 の入口。M89F が正直申告していた「一般の [c]-倍作用
  （形式群加法経由）・Λₙ の位数」のうち、**Λ₁ の生成元 λ 上の
  ℤ_p-加群構造**を完全形式化する。鍵は二つ:

  (1) **評価 = 商写像**: O = ℤ_p[[X]]/(E) では「級数 S の λ での値」は
      S mod E そのもの（X ↦ λ）。収束や完備性は一切不要で、
      [c]λ := ([c] 級数) mod E が正直な定義になる。
  (2) **合成イデアル補題**: S(0) = 0・T(0) = 0・E ∣ T なら E ∣ S∘T。
      証明は係数計算ゼロ: S = X·(shift S)（M93F の頭出し分解）から
      S∘T = (X∘T)·(shift S ∘ T) = T·(…)（M72F 合成の乗法性）で
      T の因子 E がそのまま外に出る。

  これと **f = X·E という因数分解**（LT 多項式は Eisenstein 多項式の
  X 倍！）を合わせると、[πc] = [c]∘f ∈ (E) から「π の倍数は λ を
  殺す」、単数 c では [c⁻¹]∘[c] = X と λ ≠ 0 から「殺さない」が出て、

    **[c]λ = 0 ⟺ p ∣ c**（Λ₁ の巡回部分群 ⟨λ⟩ ≅ ℤ/p の位数言明）

  が機械検証される。

  * M105-1 `ltPoly_factor` — **f = X·E**（f(T) = πT + T^p は
    E = T^{p−1} + π の T 倍。分岐拡大の一意化元の等式の級数版）
  * M105-2 `psX_factor` / `eisRel_comp_ideal` — **合成イデアル補題**
    （S(0)=0 の頭出し S = X·shift S + 合成の乗法性・X∘T = T）
  * M105-3 `eisBr` — **[c]-倍作用の実構成**: [c]λ := ltSol(c) mod E、
    `eisBr_zero` / `eisBr_one`（[0]λ = 0・[1]λ = λ）
  * M105-4 `eisBr_add_series` / `eisBr_mul_series` — 加群法則の降下:
    [a+b]λ = F([a],[b]) mod E・[ab]λ = ([a]∘[b]) mod E（M76 の
    級数恒等式の商像、congrArg 一発）
  * M105-5 `ltSol_pi` / `eisBr_pi_mul` — **[π] = f と π 倍の消滅**:
    [πc]λ = 0（[πc] = [c]∘f = [c]∘(X·E) ∈ (E)）。系
    `eisBr_pi_pow` : [πⁿc]λ = 0（n ≥ 1）
  * M105-6 `eisBr_unit_ne_zero` — **単数は λ を殺さない**:
    IsZpUnit c なら [c]λ ≠ 0（[c] ∈ (E) なら X = [c⁻¹]∘[c] ∈ (E) で
    λ = 0、eis_lambda_ne_zero に矛盾）
  * M105-7 `eisBr_eq_zero_iff` — **位数**: [c]λ = 0 ⟺ ∃d, c = π·d
    （M91F の Bool 零判定で単数/π-倍数の二分、M43 の level-1 判定）
  * M105-8 `LambdaModuleData` / `lambdaModuleData` /
    `lambdaModule_exists` — 総括レコードと witness

  未形式化（正直申告）: [c]-作用の O 全体（一般の点）への拡張は
  合成の well-definedness に O の完備性（p 進級数和）を要し次層。
  Λₙ(n ≥ 2) の生成元 λₙ は次数 p^{n−1}(p−1) の拡大に住むため
  塔の環構成が先（B-1 残り）。λ ≠ 0 の依存で hodd : 3 ≤ p を仮定する
  定理がある（M83F と同じ正直申告）。
  全て選択公理不使用。
-/
import IUT.EisensteinTower
import IUT.FormalGroupOModule
import IUT.ZpDomain
import IUT.EisDomain

namespace IUT

/-! ## f = X·E -/

/-- **定理 (M105-1): LT 多項式の因数分解** f = X·E —
    πX + X^p = X·(X^{p−1} + π)。係数ごとの照合（X 倍 = 添字シフト）。 -/
theorem ltPoly_factor (p : Nat) (hp : 2 ≤ p) :
    ltPoly p = psMul (zpRing p) (psX (zpRing p)) (eisPoly p) := by
  funext n
  cases n with
  | zero =>
    rw [psMul_X_coeff_zero p (eisPoly p)]
    exact ltPoly_coeff_zero p hp
  | succ m =>
    rw [psMul_X_coeff p (eisPoly p) m]
    show (zpRing p).add
        (psSingle (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1 (m + 1))
        (psMono (zpRing p) p (m + 1))
      = (zpRing p).add (psMono (zpRing p) (p - 1) m)
        (psC (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
    cases m with
    | zero =>
      show (zpRing p).add
          (if 0 + 1 = 1 then (toZp p).map ((p : Nat) : Int) else (zpRing p).zero)
          (if 0 + 1 = p then (zpRing p).one else (zpRing p).zero)
        = (zpRing p).add
          (if 0 = p - 1 then (zpRing p).one else (zpRing p).zero)
          (if 0 = 0 then (toZp p).map ((p : Nat) : Int) else (zpRing p).zero)
      rw [if_pos rfl, if_neg (by omega : ¬ 0 + 1 = p),
        if_neg (by omega : ¬ 0 = p - 1), if_pos rfl,
        CRing.add_zero (zpRing p), (zpRing p).zero_add]
    | succ m' =>
      show (zpRing p).add
          (if m' + 1 + 1 = 1 then (toZp p).map ((p : Nat) : Int) else (zpRing p).zero)
          (if m' + 1 + 1 = p then (zpRing p).one else (zpRing p).zero)
        = (zpRing p).add
          (if m' + 1 = p - 1 then (zpRing p).one else (zpRing p).zero)
          (if m' + 1 = 0 then (toZp p).map ((p : Nat) : Int) else (zpRing p).zero)
      rw [if_neg (by omega : ¬ m' + 1 + 1 = 1),
        if_neg (by omega : ¬ m' + 1 = 0)]
      cases Nat.decEq (m' + 1 + 1) p with
      | isTrue h =>
        rw [if_pos h, if_pos (by omega : m' + 1 = p - 1),
          (zpRing p).zero_add, CRing.add_zero (zpRing p)]
      | isFalse h =>
        rw [if_neg h, if_neg (by omega : ¬ m' + 1 = p - 1)]

/-! ## 合成イデアル補題 -/

/-- **M105-2a: 頭出し因数分解** — S(0) = 0 なら S = X·shift(S)
    （M93F の分解の定数項消去形）。 -/
theorem psX_factor (p : Nat) {S : PS (zpRing p)}
    (hS : S 0 = (zpRing p).zero) :
    S = psMul (zpRing p) (psX (zpRing p)) (psShift (zpRing p) S) := by
  have hC0 : psC (zpRing p) ((zpRing p).zero) = psZero (zpRing p) :=
    (psConstHom (zpRing p)).map_zero
  have hz : psAdd (zpRing p)
      (psMul (zpRing p) (psX (zpRing p)) (psShift (zpRing p) S))
      (psZero (zpRing p))
      = psMul (zpRing p) (psX (zpRing p)) (psShift (zpRing p) S) :=
    CRing.add_zero (psRing (zpRing p)) _
  have hd := psX_shift_decomp p S
  rw [hS, hC0, hz] at hd
  exact hd

/-- **定理 (M105-2b): 合成イデアル補題** — S(0) = 0・T(0) = 0・
    T = w·E なら S∘T ≡ 0 (mod E)。係数計算ゼロ:
    S∘T = (X·shift S)∘T = T·(shift S ∘ T) = (w·(shift S ∘ T))·E。 -/
theorem eisRel_comp_ideal (p : Nat) (S T : PS (zpRing p))
    (hS : S 0 = (zpRing p).zero) (hT0 : T 0 = (zpRing p).zero)
    (w : PS (zpRing p)) (hT : T = psMul (zpRing p) w (eisPoly p)) :
    eisRel p (psComp (zpRing p) S T) (psZero (zpRing p)) := by
  -- S∘T = T·(shift S ∘ T)
  have h1 : psComp (zpRing p) S T
      = psComp (zpRing p)
        (psMul (zpRing p) (psX (zpRing p)) (psShift (zpRing p) S)) T :=
    congrArg (fun W => psComp (zpRing p) W T) (psX_factor p hS)
  have h2 := psComp_mul (zpRing p) (psX (zpRing p)) (psShift (zpRing p) S) T hT0
  have h3 : psComp (zpRing p) (psX (zpRing p)) T = T := psComp_X (zpRing p) T hT0
  have hstep : psComp (zpRing p) S T
      = psMul (zpRing p) T (psComp (zpRing p) (psShift (zpRing p) S) T) := by
    rw [h1, h2, h3]
  -- T = w·E を代入して E を外に出す
  have h4 : psMul (zpRing p) T (psComp (zpRing p) (psShift (zpRing p) S) T)
      = psMul (zpRing p) (psMul (zpRing p) w (eisPoly p))
        (psComp (zpRing p) (psShift (zpRing p) S) T) :=
    congrArg (fun W => psMul (zpRing p) W
      (psComp (zpRing p) (psShift (zpRing p) S) T)) hT
  have h5 : psMul (zpRing p) (psMul (zpRing p) w (eisPoly p))
        (psComp (zpRing p) (psShift (zpRing p) S) T)
      = psMul (zpRing p)
        (psMul (zpRing p) w (psComp (zpRing p) (psShift (zpRing p) S) T))
        (eisPoly p) := by
    show (psRing (zpRing p)).mul ((psRing (zpRing p)).mul w (eisPoly p))
        (psComp (zpRing p) (psShift (zpRing p) S) T)
      = (psRing (zpRing p)).mul
        ((psRing (zpRing p)).mul w (psComp (zpRing p) (psShift (zpRing p) S) T))
        (eisPoly p)
    rw [(psRing (zpRing p)).mul_assoc, (psRing (zpRing p)).mul_assoc,
      (psRing (zpRing p)).mul_comm (eisPoly p)
        (psComp (zpRing p) (psShift (zpRing p) S) T)]
  -- eisRel の証人
  refine ⟨psMul (zpRing p) w (psComp (zpRing p) (psShift (zpRing p) S) T), ?_⟩
  have hneg : psNeg (zpRing p) (psZero (zpRing p)) = psZero (zpRing p) :=
    CRing.neg_zero (psRing (zpRing p))
  have hadd : psAdd (zpRing p) (psComp (zpRing p) S T) (psZero (zpRing p))
      = psComp (zpRing p) S T :=
    CRing.add_zero (psRing (zpRing p)) _
  rw [hneg, hadd, hstep, h4, h5]

/-! ## [c]-倍作用の実構成 -/

/-- **M105-3a: [c]-倍作用** — [c]λ := ltSol(c) mod E（評価 = 商写像。
    λ = X mod E での [c] 級数の値そのもの）。 -/
def eisBr (p : Nat) (hp : IsPrime p) (c : (Zp p).carrier) :
    (eisRing p).carrier :=
  Quot.mk (eisRel p) (ltSol p hp c)

/-- **M105-3b**: [0]λ = 0。 -/
theorem eisBr_zero (p : Nat) (hp : IsPrime p) :
    eisBr p hp ((zpRing p).zero) = (eisRing p).zero :=
  congrArg (Quot.mk (eisRel p)) (ltSol_zero p hp)

/-- **M105-3c**: [1]λ = λ。 -/
theorem eisBr_one (p : Nat) (hp : IsPrime p) :
    eisBr p hp ((zpRing p).one) = eisLambda p :=
  congrArg (Quot.mk (eisRel p)) (ltSol_one p hp)

/-! ## 加群法則の降下 -/

/-- **M105-4a: 加法の降下** — [a+b]λ = F([a],[b]) mod E
    （M76 の F([a]X,[b]X) = [a+b]X の商像）。 -/
theorem eisBr_add_series (p : Nat) (hp : IsPrime p) (a b : (Zp p).carrier) :
    Quot.mk (eisRel p)
      (ps21Comp (zpRing p) (lt2Sol p hp) (ltSol p hp a) (ltSol p hp b))
      = eisBr p hp ((zpRing p).add a b) :=
  congrArg (Quot.mk (eisRel p)) (lt_module_add p hp a b)

/-- **M105-4b: 乗法の降下** — [ab]λ = ([a]∘[b]) mod E
    （M76 の [a]∘[b] = [ab] の商像）。 -/
theorem eisBr_mul_series (p : Nat) (hp : IsPrime p) (a b : (Zp p).carrier) :
    Quot.mk (eisRel p)
      (psComp (zpRing p) (ltSol p hp a) (ltSol p hp b))
      = eisBr p hp ((zpRing p).mul a b) :=
  congrArg (Quot.mk (eisRel p)) (lt_module_mul p hp a b)

/-! ## [π] = f と π 倍の消滅 -/

/-- **M105-5a: [π] = f** — ltIter の n = 1 同定（M72F）の読み替え。 -/
theorem ltSol_pi (p : Nat) (hp : IsPrime p) :
    ltSol p hp ((toZp p).map ((p : Nat) : Int)) = ltPoly p := by
  have h1 := ltIter_eq_ltSol p hp 1
  have h2 : rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) 1
      = (toZp p).map ((p : Nat) : Int) := by
    show (zpRing p).mul ((zpRing p).one) ((toZp p).map ((p : Nat) : Int))
      = (toZp p).map ((p : Nat) : Int)
    exact (zpRing p).one_mul _
  rw [h2] at h1
  have h3 : ltIter p 1 = ltPoly p := by
    show psComp (zpRing p) (psX (zpRing p)) (ltPoly p) = ltPoly p
    exact psComp_X (zpRing p) (ltPoly p) (ltPoly_coeff_zero p hp.1)
  rw [h3] at h1
  exact h1.symm

/-- **定理 (M105-5b): π 倍は λ を殺す** — [πc]λ = 0
    （[πc] = [c]∘[π] = [c]∘f = [c]∘(X·E) ∈ (E)、合成イデアル補題）。 -/
theorem eisBr_pi_mul (p : Nat) (hp : IsPrime p) (c : (Zp p).carrier) :
    eisBr p hp (zpMul p ((toZp p).map ((p : Nat) : Int)) c)
      = (eisRing p).zero := by
  have h0 : (zpRing p).mul c ((toZp p).map ((p : Nat) : Int))
      = zpMul p ((toZp p).map ((p : Nat) : Int)) c :=
    zpMul_comm p c ((toZp p).map ((p : Nat) : Int))
  have h1 : ltSol p hp (zpMul p ((toZp p).map ((p : Nat) : Int)) c)
      = psComp (zpRing p) (ltSol p hp c) (ltPoly p) := by
    rw [← h0, ← lt_module_mul p hp c ((toZp p).map ((p : Nat) : Int)),
      ltSol_pi p hp]
  show Quot.mk (eisRel p) (ltSol p hp (zpMul p ((toZp p).map ((p : Nat) : Int)) c))
    = Quot.mk (eisRel p) (psZero (zpRing p))
  rw [h1]
  exact Quot.sound (eisRel_comp_ideal p (ltSol p hp c) (ltPoly p) rfl
    (ltPoly_coeff_zero p hp.1) (psX (zpRing p)) (ltPoly_factor p hp.1))

/-- **系 (M105-5c): π 冪倍の消滅** — n ≥ 1 なら [πⁿ·c]λ = 0
    （π^{n} = π·π^{n−1} で M105-5b に帰着）。 -/
theorem eisBr_pi_pow (p : Nat) (hp : IsPrime p) (c : (Zp p).carrier)
    (n : Nat) (hn : 1 ≤ n) :
    eisBr p hp (zpMul p
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n) c)
      = (eisRing p).zero := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  -- π^{m+1}·c = π·(π^m·c)
  have h1 : zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 1)) c
      = zpMul p ((toZp p).map ((p : Nat) : Int))
        (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m) c) :=
    (congrArg (fun w => zpMul p w c)
        ((zpRing p).mul_comm
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
          ((toZp p).map ((p : Nat) : Int)))).trans
      (zpMul_assoc p ((toZp p).map ((p : Nat) : Int))
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m) c)
  rw [h1]
  exact eisBr_pi_mul p hp _

/-! ## 単数は λ を殺さない -/

/-- **定理 (M105-6): 単数の非消滅** — IsZpUnit c なら [c]λ ≠ 0。
    [c] ∈ (E) と仮定すると X = [1] = [c⁻¹]∘[c] ∈ (E)（合成イデアル
    補題）で λ = 0 となり eis_lambda_ne_zero（M83F）に矛盾。 -/
theorem eisBr_unit_ne_zero (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    {c : (Zp p).carrier} (hc : IsZpUnit p c) :
    eisBr p hp c ≠ (eisRing p).zero := by
  intro h
  have hrel : eisRel p (ltSol p hp c) (psZero (zpRing p)) := eis_exact p h
  obtain ⟨w, hw⟩ := hrel
  have hneg : psNeg (zpRing p) (psZero (zpRing p)) = psZero (zpRing p) :=
    CRing.neg_zero (psRing (zpRing p))
  have hadd : psAdd (zpRing p) (ltSol p hp c) (psZero (zpRing p))
      = ltSol p hp c :=
    CRing.add_zero (psRing (zpRing p)) _
  rw [hneg, hadd] at hw
  -- hw : [c] = w·E
  -- X = [c⁻¹·c] = [c⁻¹]∘[c]
  have hy : zpMul p (zpUnitInv p hp c hc) c = zpOne p :=
    zpUnitInv_mul p hp c hc
  have h1 : psComp (zpRing p) (ltSol p hp (zpUnitInv p hp c hc))
      (ltSol p hp c) = psX (zpRing p) := by
    rw [lt_module_mul p hp (zpUnitInv p hp c hc) c]
    have hyc : (zpRing p).mul (zpUnitInv p hp c hc) c = (zpRing p).one := hy
    rw [hyc]
    exact ltSol_one p hp
  have h2 := eisRel_comp_ideal p (ltSol p hp (zpUnitInv p hp c hc))
    (ltSol p hp c) rfl rfl w hw
  rw [h1] at h2
  have h3 : eisLambda p = (eisRing p).zero := Quot.sound h2
  exact eis_lambda_ne_zero p hodd h3

/-! ## 位数: [c]λ = 0 ⟺ p ∣ c -/

/-- **定理 (M105-7): ⟨λ⟩ の位数 = p** — [c]λ = 0 ⟺ c は π の倍数。
    M91F の Bool 零判定でレベル 1 剰余を二分し、零なら M43 の
    level-1 判定で π ∣ c、非零なら c は単数で M105-6。
    Λ₁ の巡回部分群 ⟨λ⟩ ≅ ℤ/p の位数言明（B-1 の「位数」部分）。 -/
theorem eisBr_eq_zero_iff (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    (c : (Zp p).carrier) :
    eisBr p hp c = (eisRing p).zero
      ↔ ∃ d, c = zpMul p ((toZp p).map ((p : Nat) : Int)) d := by
  constructor
  · intro h
    cases hz : zmodIsZero (p ^ 1) (c.val 1) with
    | true =>
      exact (zp_dvd_p_iff p hp.1 c).mpr (zmodIsZero_true (p ^ 1) _ hz)
    | false =>
      exfalso
      obtain ⟨a, ha⟩ := Quot.exists_rep (c.val 1)
      have hpa : ¬ ((p : Nat) : Int) ∣ a := by
        intro hd
        apply zmodIsZero_false (p ^ 1) _ hz
        rw [← ha]
        apply Quot.sound
        show ((p ^ 1 : Nat) : Int) ∣ a - 0
        rw [Nat.pow_one]
        obtain ⟨k, hk⟩ := hd
        refine ⟨k, ?_⟩
        rw [Int.sub_zero]
        exact hk
      exact eisBr_unit_ne_zero p hp hodd ⟨a, ha.symm, hpa⟩ h
  · intro hd
    obtain ⟨d, hdd⟩ := hd
    rw [hdd]
    exact eisBr_pi_mul p hp d

/-! ## 総括レコード -/

/-- **M105-8a: 総括** — λ 上の [c]-倍作用の加群構造と位数を束ねた
    純レコード。 -/
structure LambdaModuleData (p : Nat) (hp : IsPrime p) where
  /-- [c]-倍作用 ℤ_p → O。 -/
  bracket : (Zp p).carrier → (eisRing p).carrier
  /-- [0]λ = 0。 -/
  br_zero : bracket ((zpRing p).zero) = (eisRing p).zero
  /-- [1]λ = λ。 -/
  br_one : bracket ((zpRing p).one) = eisLambda p
  /-- π 倍は λ を殺す。 -/
  br_pi_mul : ∀ c, bracket (zpMul p ((toZp p).map ((p : Nat) : Int)) c)
    = (eisRing p).zero
  /-- 単数は λ を殺さない。 -/
  br_unit_ne_zero : ∀ c, IsZpUnit p c → bracket c ≠ (eisRing p).zero
  /-- 位数: [c]λ = 0 ⟺ π ∣ c。 -/
  br_zero_iff : ∀ c, bracket c = (eisRing p).zero
    ↔ ∃ d, c = zpMul p ((toZp p).map ((p : Nat) : Int)) d

/-- **M105-8b: witness**（全フィールド既証明の純レコード）。 -/
def lambdaModuleData (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    LambdaModuleData p hp where
  bracket := eisBr p hp
  br_zero := eisBr_zero p hp
  br_one := eisBr_one p hp
  br_pi_mul := eisBr_pi_mul p hp
  br_unit_ne_zero := fun _ hc => eisBr_unit_ne_zero p hp hodd hc
  br_zero_iff := fun c => eisBr_eq_zero_iff p hp hodd c

/-- **M105-8c: 存在**。 -/
theorem lambdaModule_exists (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    Nonempty (LambdaModuleData p hp) :=
  ⟨lambdaModuleData p hp hodd⟩

end IUT
