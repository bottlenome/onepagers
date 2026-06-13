/-
  IUT/RecGluing.lean — M94（K^× 貼り合わせのレベル 1 骨格: 柱B）

  柱B の残段「K^× 全体からの相互写像の貼り合わせ」の第一段。
  ℚ_p^× = p^ℤ × ℤ_p^×（M37 の QpUnits）に対し、**不分岐成分は
  Frobenius 側（toZhat、M37 の recQp の第 1 因子）へ、単数成分は
  Eisenstein 環 O の Galois 作用（M86F/M87F の eisGal）へ**送る
  「貼り合わされたレベル 1 相互作用」recLevelOne を構成する。

  設計の鍵: 単数 u ∈ ℤ_p^× のレベル 1 剰余の**標準 Int 代表 res1**
  を Quot.lift（c ↦ c % p）で choice なしに抽出する（IsZpUnit の
  ∃-witness を「データ」に使うと選択公理が要る——商の関数として
  持ち上げれば不要。well-definedness は Int.add_mul_emod_self_left）。
  σ_a が a mod p のみに依存する剰余依存性（M87F eisGal_residue）が
  この標準化と完全に整合し、レベル 1 乗法性（Int.mul_emod）+
  eisGal_mul で貼り合わせ写像の乗法性が閉じる。

  * M94-1 `zres` / `res1` / `res1_unit_not_dvd` / `res1_mul_congr` —
    レベル 1 剰余の標準代表と乗法合同
  * M94-2 `recInertia` と乗法性・U^(1) 自明性・λ-作用
  * M94-3 `recLevelOne` — **貼り合わせ（本丸）**: 不分岐 × 分岐の
    同時作用とその乗法性
  * M94-4 `recLevelOne_ker` — **レベル 1 の核 = {0} × U^(1)**
    （不分岐側は toZhat 単射性、分岐側は eisGal_faithful +
    emod 判定の構成的場合分け）
  * M94-5 `RecGluingData` / `recGluing` / `recGluing_exists` — 総括

  Λₙ（n ≥ 2）の高層・全射性・抽象 Galois 群（自己同型全体）との
  一致は次層。全て選択公理不使用。
-/
import IUT.FullReciprocity
import IUT.RecRamified

namespace IUT

/-! ## レベル 1 剰余の標準代表 -/

/-- 差の分離（omega をクリーン文脈で使うための補題）。 -/
theorem int_split (a b : Int) : a = b + (a - b) := by omega

/-- **M94-1a: ℤ/p の標準 Int 代表**（emod による Quot.lift、
    choice なし）。 -/
def zres (p : Nat) : (zmod (p ^ 1)).carrier → Int :=
  Quot.lift (fun c : Int => c % (((p ^ 1 : Nat)) : Int))
    (fun a b hab => by
      obtain ⟨k, hk⟩ := hab
      show a % ((p ^ 1 : Nat) : Int) = b % ((p ^ 1 : Nat) : Int)
      rw [int_split a b, hk, Int.add_mul_emod_self_left])

/-- **M94-1b: レベル 1 剰余の標準代表** res1(x) ∈ ℤ。 -/
def res1 (p : Nat) (x : (Zp p).carrier) : Int :=
  zres p (x.val 1)

/-- p^1 の cast 橋。 -/
theorem cast_pow_one (p : Nat) :
    ((p ^ 1 : Nat) : Int) = ((p : Nat) : Int) := by
  rw [Nat.pow_one]

/-- **M94-1c: 単数の標準代表は p と素**。 -/
theorem res1_unit_not_dvd (p : Nat) (x : (Zp p).carrier)
    (hx : IsZpUnit p x) : ¬ ((p : Nat) : Int) ∣ res1 p x := by
  obtain ⟨a, hval, ha⟩ := hx
  intro hd
  apply ha
  have hres : res1 p x = a % ((p ^ 1 : Nat) : Int) := by
    show zres p (x.val 1) = _
    rw [hval]
    rfl
  rw [cast_pow_one p] at hres
  rw [hres] at hd
  have hediv := Int.emod_add_mul_ediv a ((p : Nat) : Int)
  obtain ⟨k, hk⟩ := hd
  refine ⟨k + a / ((p : Nat) : Int), ?_⟩
  rw [Int.mul_add, ← hk]
  omega

/-- **M94-1d: レベル 1 乗法合同** — res1(x·y) ≡ res1(x)·res1(y)
    (mod p)（Int.mul_emod による）。 -/
theorem res1_mul_congr (p : Nat) (x y : (Zp p).carrier) :
    ((p : Nat) : Int) ∣ res1 p (zpMul p x y) - res1 p x * res1 p y := by
  have key : ∀ qa qb : (zmod (p ^ 1)).carrier,
      ((p : Nat) : Int) ∣
        zres p (zmodMul (p ^ 1) qa qb) - zres p qa * zres p qb := by
    intro qa qb
    induction qa using Quot.ind
    rename_i a
    induction qb using Quot.ind
    rename_i b
    show ((p : Nat) : Int) ∣
      (a * b) % ((p ^ 1 : Nat) : Int)
        - (a % ((p ^ 1 : Nat) : Int)) * (b % ((p ^ 1 : Nat) : Int))
    rw [cast_pow_one p]
    have h1 := Int.mul_emod a b ((p : Nat) : Int)
    have h2 := Int.emod_add_mul_ediv
      ((a % ((p : Nat) : Int)) * (b % ((p : Nat) : Int)))
      ((p : Nat) : Int)
    refine ⟨-(((a % ((p : Nat) : Int))
      * (b % ((p : Nat) : Int))) / ((p : Nat) : Int)), ?_⟩
    rw [h1, Int.mul_neg]
    omega
  exact key (x.val 1) (y.val 1)

/-! ## 分岐成分の作用（単数 → O の Galois 作用） -/

/-- **M94-2a: 慣性作用** — u ∈ ℤ_p^× を σ_{res1(u)} ∈ Aut(O) へ。 -/
def recInertia (p : Nat) (hp : IsPrime p)
    (u : (zpUnits p hp).carrier) : RingHom (eisRing p) (eisRing p) :=
  eisGal p hp (res1 p u.val) (res1_unit_not_dvd p u.val u.property)

/-- **定理 (M94-2b): 慣性作用の乗法性** — σ_{uv} = σ_u ∘ σ_v
    （レベル 1 乗法合同 + 剰余依存性 + eisGal_mul）。 -/
theorem recInertia_mul (p : Nat) (hp : IsPrime p)
    (u v : (zpUnits p hp).carrier) : ∀ t,
    (recInertia p hp ((zpUnits p hp).mul u v)).map t
      = (recInertia p hp u).map ((recInertia p hp v).map t) := by
  intro t
  have hu := res1_unit_not_dvd p u.val u.property
  have hv := res1_unit_not_dvd p v.val v.property
  have hab : ¬ ((p : Nat) : Int) ∣ (res1 p u.val * res1 p v.val) := by
    intro hd
    rw [Int.mul_comm] at hd
    exact hu (euclid_int p hp hd hv)
  have h1 := eisGal_residue p hp
    (res1_unit_not_dvd p ((zpUnits p hp).mul u v).val
      ((zpUnits p hp).mul u v).property) hab
    (res1_mul_congr p u.val v.val) t
  exact h1.trans (eisGal_mul p hp hu hv hab t).symm

/-- **定理 (M94-2c): U^(1) は自明に作用**（レベル 1 の核の片側）。 -/
theorem recInertia_principal (p : Nat) (hp : IsPrime p)
    (u : (zpUnits p hp).carrier)
    (h1 : ((p : Nat) : Int) ∣ res1 p u.val - 1) : ∀ t,
    (recInertia p hp u).map t = t :=
  eisGal_principal_trivial p hp (res1_unit_not_dvd p u.val u.property) h1

/-- **定理 (M94-2d): λ-作用の明示** — σ_u(λ) = ω(res1 u)·λ。 -/
theorem recInertia_lambda (p : Nat) (hp : IsPrime p)
    (u : (zpUnits p hp).carrier) :
    (recInertia p hp u).map (eisLambda p)
      = (eisRing p).mul
          ((eisOf p).map (teich p hp (res1 p u.val))) (eisLambda p) :=
  eisAut_lambda p (teich p hp (res1 p u.val))
    (teich_pow_rpow_one p hp (res1_unit_not_dvd p u.val u.property)) hp.1

/-! ## 貼り合わせ（本丸） -/

/-- **M94-3a: 貼り合わされたレベル 1 相互作用** —
    rec(k, u) = (Frobenius 側 toZhat(k), 慣性側 σ_{res1(u)})。 -/
def recLevelOne (p : Nat) (hp : IsPrime p)
    (x : (QpUnits p hp).carrier) :
    zhat.carrier × RingHom (eisRing p) (eisRing p) :=
  (toZhat.map x.1, recInertia p hp x.2)

/-- **定理 (M94-3b): 不分岐成分の乗法性**。 -/
theorem recLevelOne_mul_unram (p : Nat) (hp : IsPrime p)
    (x y : (QpUnits p hp).carrier) :
    (recLevelOne p hp ((QpUnits p hp).mul x y)).1
      = zhat.mul (recLevelOne p hp x).1 (recLevelOne p hp y).1 :=
  toZhat.map_mul x.1 y.1

/-- **定理 (M94-3c): 分岐成分の乗法性**。 -/
theorem recLevelOne_mul_ram (p : Nat) (hp : IsPrime p)
    (x y : (QpUnits p hp).carrier) : ∀ t,
    ((recLevelOne p hp ((QpUnits p hp).mul x y)).2).map t
      = ((recLevelOne p hp x).2).map (((recLevelOne p hp y).2).map t) :=
  recInertia_mul p hp x.2 y.2

/-! ## レベル 1 の核 = {0} × U^(1) -/

/-- **定理 (M94-4): 核の特徴付け（本丸）** — rec(k, u) が自明
    （Frobenius 成分 = 1 かつ λ を固定）なら k = 0 かつ u ∈ U^(1)。
    不分岐側は toZhat の単射性、分岐側は emod の構成的場合分け +
    eisGal_faithful（排中律不使用）。 -/
theorem recLevelOne_ker (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p)
    (x : (QpUnits p hp).carrier)
    (hfrob : (recLevelOne p hp x).1 = zhat.one)
    (hlam : ((recLevelOne p hp x).2).map (eisLambda p) = eisLambda p) :
    x.1 = 0 ∧ ((p : Nat) : Int) ∣ res1 p x.2.val - 1 := by
  constructor
  · -- 不分岐側: toZhat(k) = 1 = toZhat(0) → k = 0
    have h0 : toZhat.map (0 : Int) = zhat.one := toZhat.map_one
    exact toZhat_injective x.1 0 (hfrob.trans h0.symm)
  · -- 分岐側: emod 判定の構成的場合分け
    cases Int.decEq ((res1 p x.2.val - 1) % ((p : Nat) : Int)) 0 with
    | isTrue h => exact Int.dvd_of_emod_eq_zero h
    | isFalse h =>
      exfalso
      have hndvd : ¬ ((p : Nat) : Int) ∣ (res1 p x.2.val - 1) :=
        fun hd => h (Int.emod_eq_zero_of_dvd hd)
      have h1ndvd : ¬ ((p : Nat) : Int) ∣ (1 : Int) := not_dvd_one p hp.1
      have hsep := eisGal_faithful p hp hodd
        (res1_unit_not_dvd p x.2.val x.2.property) h1ndvd hndvd
      have htriv1 : (eisGal p hp 1 h1ndvd).map (eisLambda p)
          = eisLambda p :=
        eisGal_principal_trivial p hp h1ndvd ⟨0, by omega⟩ (eisLambda p)
      exact hsep (hlam.trans htriv1.symm)

/-! ## 総括 -/

/-- **M94-5a: K^× 貼り合わせレベル 1 の総括データ** — 作用・両成分の
    乗法性・U^(1) 自明性・核の特徴付け・λ-作用の明示。 -/
structure RecGluingData (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) where
  /-- 貼り合わせ作用 ℚ_p^× → ẑ × End(O)。 -/
  act : (QpUnits p hp).carrier →
    zhat.carrier × RingHom (eisRing p) (eisRing p)
  /-- 不分岐成分の乗法性。 -/
  mul_unram : ∀ x y, (act ((QpUnits p hp).mul x y)).1
    = zhat.mul (act x).1 (act y).1
  /-- 分岐成分の乗法性。 -/
  mul_ram : ∀ x y t, ((act ((QpUnits p hp).mul x y)).2).map t
    = ((act x).2).map (((act y).2).map t)
  /-- U^(1) は分岐成分に自明に作用。 -/
  u1_trivial : ∀ x, ((p : Nat) : Int) ∣ res1 p
      (x : (QpUnits p hp).carrier).2.val - 1 →
    ∀ t, ((act x).2).map t = t
  /-- λ-作用の明示: σ_u(λ) = ω(res1 u)·λ。 -/
  lambda_act : ∀ x, ((act x).2).map (eisLambda p)
    = (eisRing p).mul
        ((eisOf p).map (teich p hp (res1 p
          (x : (QpUnits p hp).carrier).2.val))) (eisLambda p)
  /-- 核の特徴付け: 自明に作用するのは {0} × U^(1) のみ。 -/
  ker : ∀ x, (act x).1 = zhat.one →
    ((act x).2).map (eisLambda p) = eisLambda p →
    x.1 = 0 ∧ ((p : Nat) : Int) ∣ res1 p x.2.val - 1

/-- **M94-5b: witness 本体**。 -/
def recGluing (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    RecGluingData p hp hodd where
  act := recLevelOne p hp
  mul_unram := recLevelOne_mul_unram p hp
  mul_ram := recLevelOne_mul_ram p hp
  u1_trivial := fun x h => recInertia_principal p hp x.2 h
  lambda_act := fun x => recInertia_lambda p hp x.2
  ker := recLevelOne_ker p hp hodd

/-- **定理 (M94-5c): 貼り合わせの存在（見出し）**。 -/
theorem recGluing_exists (p : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) :
    Nonempty (RecGluingData p hp hodd) :=
  ⟨recGluing p hp hodd⟩

end IUT
