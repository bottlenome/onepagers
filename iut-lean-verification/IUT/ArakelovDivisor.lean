/-
  IUT/ArakelovDivisor.lean — M356F [実／本物]
  分類: 実 (Arakelov 因子群 D̂=D_fin⊕D_∞・実次数 deg・主因子 deg=0)
  complete_pct 影響: 柱C を前進（M307F 有限因子群＋M346F アルキメデス重みを Arakelov 因子群
    D̂ へ束ね、実次数 deg:D̂→ℝ（加法準同型）・主 Arakelov 因子の deg=0（M351F 積公式）＝
    Arakelov Picard 群上で deg が well-defined、を本物で）。
  正直な限定: K=ℚ（模型）・一般数体/コンパクト性込みの完全 Arakelov Pic は後続。
-/
import IUT.ProductFormula

namespace IUT

/-! ## M356F-1: Arakelov 因子の代表 ardRaw = 有限部 ⊕ アルキメデス部

    K=ℚ の Arakelov 因子 D̂ を、有限部（M307F `RawDiv`＝素点上の有限台 ℤ-値関数
    Σ_p n_p[P_p]）とアルキメデス部（唯一のアルキメデス素点 ∞ の実重み arch∈ℝ、
    M346F/M317F の実測度的寄与）の対で模型化する。D̂ = D_fin ⊕ D_∞。 -/

/-- **M356F-1: Arakelov 因子の代表** — 有限部 fin（M307F RawDiv）と ∞ の実重み arch。 -/
structure ardRaw where
  /-- 有限部 Σ_p n_p[P_p]（M307F RawDiv）。 -/
  fin : RawDiv
  /-- アルキメデス部 ∞ の実重み（M346F/M317F 実測度的寄与）。 -/
  arch : RReal

/-- 零 Arakelov 因子 0̂。 -/
def ardZero : ardRaw where
  fin := rawZero
  arch := realZero

/-- Arakelov 因子の和（成分ごと: 有限部は rawAdd、∞ 部は realAdd）。 -/
def ardAdd (D E : ardRaw) : ardRaw where
  fin := rawAdd D.fin E.fin
  arch := realAdd D.arch E.arch

/-- Arakelov 因子の逆元（成分ごと符号反転）。 -/
def ardNeg (D : ardRaw) : ardRaw where
  fin := rawNeg D.fin
  arch := realNeg D.arch

/-! ## M356F-2: Arakelov 因子の等価 ardEq（成分等価）

    有限部は係数等価 rawEq（bound 非依存）、∞ 部は ℝ の setoid 等価 realEq。 -/

/-- **M356F-2: Arakelov 因子の等価** — 有限部が rawEq かつ ∞ 部が realEq。 -/
def ardEq (D E : ardRaw) : Prop := rawEq D.fin E.fin ∧ realEq D.arch E.arch

theorem ardEq_refl (D : ardRaw) : ardEq D D :=
  ⟨rawEq_refl D.fin, realEq_refl D.arch⟩

theorem ardEq_symm {D E : ardRaw} (h : ardEq D E) : ardEq E D :=
  ⟨rawEq_symm h.1, realEq_symm h.2⟩

theorem ardEq_trans {D E F : ardRaw} (h1 : ardEq D E) (h2 : ardEq E F) : ardEq D F :=
  ⟨rawEq_trans h1.1 h2.1, realEq_trans h1.2 h2.2⟩

/-! ## M356F-3: Arakelov 因子群 D̂ = Quot ardEq 上のアーベル群 -/

/-- 商上の積（成分ごとの和、Quot.lift の二重適用）。 -/
def ardMul (x y : Quot ardEq) : Quot ardEq :=
  Quot.lift
    (fun a => Quot.lift (fun b => Quot.mk ardEq (ardAdd a b))
      (fun _ _ hb => Quot.sound
        ⟨fun k => by
          show a.fin.coeff k + _ = a.fin.coeff k + _
          rw [hb.1 k],
         realAdd_congr_right a.arch hb.2⟩) y)
    (fun a a' ha => by
      induction y using Quot.ind
      rename_i b
      exact Quot.sound
        ⟨fun k => by
          show a.fin.coeff k + b.fin.coeff k = a'.fin.coeff k + b.fin.coeff k
          rw [ha.1 k],
         realAdd_congr_left b.arch ha.2⟩) x

/-- 商上の逆元（成分ごと符号反転）。 -/
def ardInv (x : Quot ardEq) : Quot ardEq :=
  Quot.lift (fun a => Quot.mk ardEq (ardNeg a))
    (fun _ _ ha => Quot.sound
      ⟨fun k => by
        show -_ = -_
        rw [ha.1 k],
       realNeg_congr ha.2⟩) x

/-- **M356F-3: Arakelov 因子群 D̂ = D_fin ⊕ D_∞** — 有限因子群（M307F）と ∞ の実重み
    を成分ごとの加法で束ねた本物のアーベル群。群公理（結合・単位・逆元）を Quot.ind＋
    Quot.sound で完全証明（有限部は omega、∞ 部は M117F realAdd の群法則）。 -/
def ardGroup : Grp where
  carrier := Quot ardEq
  mul := ardMul
  one := Quot.mk ardEq ardZero
  inv := ardInv
  mul_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    induction z using Quot.ind; rename_i c
    show Quot.mk ardEq (ardAdd (ardAdd a b) c)
        = Quot.mk ardEq (ardAdd a (ardAdd b c))
    exact Quot.sound
      ⟨fun k => by
        show (a.fin.coeff k + b.fin.coeff k) + c.fin.coeff k
            = a.fin.coeff k + (b.fin.coeff k + c.fin.coeff k)
        omega,
       realAdd_assoc a.arch b.arch c.arch⟩
  one_mul := by
    intro x
    induction x using Quot.ind; rename_i a
    show Quot.mk ardEq (ardAdd ardZero a) = Quot.mk ardEq a
    exact Quot.sound
      ⟨fun k => by
        show (0 : Int) + a.fin.coeff k = a.fin.coeff k
        omega,
       realEq_trans (realAdd_comm realZero a.arch) (realAdd_zero a.arch)⟩
  inv_mul := by
    intro x
    induction x using Quot.ind; rename_i a
    show Quot.mk ardEq (ardAdd (ardNeg a) a) = Quot.mk ardEq ardZero
    exact Quot.sound
      ⟨fun k => by
        show -(a.fin.coeff k) + a.fin.coeff k = (0 : Int)
        omega,
       realEq_trans (realAdd_comm (realNeg a.arch) a.arch) (realAdd_neg a.arch)⟩

/-! ## M356F-4: D̂ のアーベル性 → 部分群は正規 -/

/-- **M356F-4a: Arakelov 因子群は可換**（成分ごとの加法の可換性）。 -/
theorem ardGroup_comm (x y : ardGroup.carrier) :
    ardGroup.mul x y = ardGroup.mul y x := by
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  show Quot.mk ardEq (ardAdd a b) = Quot.mk ardEq (ardAdd b a)
  exact Quot.sound
    ⟨fun k => by
      show a.fin.coeff k + b.fin.coeff k = b.fin.coeff k + a.fin.coeff k
      omega,
     realAdd_comm a.arch b.arch⟩

/-- **M356F-4b: アーベル群 D̂ の任意の部分群は正規** — gng⁻¹ = n。 -/
theorem ardAbelianNormal (N : Subgroup ardGroup) :
    IsNormalSubgroup ardGroup N := by
  intro g n hn
  have hcomm : ardGroup.mul (ardGroup.mul g n) (ardGroup.inv g) = n := by
    rw [ardGroup_comm g n, ardGroup.mul_assoc, ardGroup.mul_inv, ardGroup.mul_one]
  rw [hcomm]
  exact hn

/-! ## M356F-5: Arakelov 次数 deg : D̂ → ℝ（加法準同型） -/

/-- **M356F-5a: Arakelov 次数** deg(D̂) = deg_fin(D_fin) + arch。有限部は M312F の
    実数値 Arakelov 次数 logVolGlobal（Σ_p n_p·log p）、∞ 部は実重み arch そのもの。
    ℝ は setoid ゆえ deg は Grp の `=` でなく realEq で well-defined（M312F 同様の正直形）。 -/
def ardDeg (logp : Nat → RReal) (D : ardRaw) : RReal :=
  realAdd (logVolGlobal logp D.fin) D.arch

/-- **M356F-5b: deg の well-defined 性** — 等価な代表は同じ次数（realEq、ℝ は setoid）。 -/
theorem ardDeg_wd (logp : Nat → RReal) {D E : ardRaw} (h : ardEq D E) :
    realEq (ardDeg logp D) (ardDeg logp E) :=
  realEq_trans (realAdd_congr_left D.arch (logVolGlobal_wd logp h.1))
    (realAdd_congr_right (logVolGlobal logp E.fin) h.2)

/-- **M356F-5c: deg の加法準同型（本丸）** deg(D̂+Ê) ≈ deg(D̂)+deg(Ê)。
    有限部は M312F 加法準同型 logVolGlobal_add、∞ 部は realAdd、4 項入替
    logVol_add4_swap で束ねる。D̂→ℝ の実加法 Hom。 -/
theorem ard_deg_hom (logp : Nat → RReal) (D E : ardRaw) :
    realEq (ardDeg logp (ardAdd D E))
      (realAdd (ardDeg logp D) (ardDeg logp E)) := by
  show realEq (realAdd (logVolGlobal logp (rawAdd D.fin E.fin)) (realAdd D.arch E.arch))
      (realAdd (realAdd (logVolGlobal logp D.fin) D.arch)
        (realAdd (logVolGlobal logp E.fin) E.arch))
  refine realEq_trans (realAdd_congr_left (realAdd D.arch E.arch)
    (logVolGlobal_add logp D.fin E.fin)) ?_
  exact logVol_add4_swap
    (logVolGlobal logp D.fin) (logVolGlobal logp E.fin) D.arch E.arch

/-! ## M356F-6: 主 Arakelov 因子 div̂(x) と次数 0 -/

/-- **M356F-6a: 主 Arakelov 因子** div̂(x) = div_fin(x) + div_∞(x)（x∈ℚ^×）。
    有限部＝付値ベクトル div(x)_fin = x.fin（Σ_p v_p(x)[P_p]）、∞ 部＝−log|x|_∞
    = logVolGlobal logp (rawNeg x.fin)（M351F pfFiniteDeg＝−Σ_p v_p(x)·log p）。 -/
def ardPrincipal (logp : Nat → RReal) (x : pfRational) : ardRaw where
  fin := x.fin
  arch := logVolGlobal logp (rawNeg x.fin)

/-- **M356F-6b: 主 Arakelov 因子の次数=0（well-defined 性）** deg(div̂(x)) = 0。
    deg(div̂(x)) = Σ_p v_p(x)·log p + (−log|x|_∞) = 大域 log-volume の積公式
    Σ_v log|x|_v = 0（M351F pf_product_formula）。これは deg が主因子で消える
    ＝Arakelov Picard 群上で deg が well-defined であることの核。 -/
theorem ard_principal_degree_zero (logp : Nat → RReal) (x : pfRational) :
    realEq (ardDeg logp (ardPrincipal logp x)) realZero := by
  show realEq (realAdd (logVolGlobal logp x.fin) (logVolGlobal logp (rawNeg x.fin)))
      realZero
  refine realEq_trans
    (realAdd_comm (logVolGlobal logp x.fin) (logVolGlobal logp (rawNeg x.fin))) ?_
  exact pf_product_formula logp x

/-! ## M356F-7: 主因子準同型 div̂ と Arakelov Picard 群 -/

/-- **M356F-7a: 主 Arakelov 因子の代表（有限因子から）** — 有限因子 f∈Div から
    ⟨f, −deg_fin(f)⟩＝ f の付値を実現する ℚ^× 元の主 Arakelov 因子（K=ℚ は類数 1
    ゆえ任意の有限因子 f が単項 div(x)、x=∏_p p^{f_p} で実現）。 -/
def ardPrincipalRaw (logp : Nat → RReal) (f : RawDiv) : ardRaw where
  fin := f
  arch := logVolGlobal logp (rawNeg f)

/-- **M356F-7b: 主因子準同型 div̂ : Div → D̂**（本物の Hom）。
    div̂(f+g)=div̂(f)+div̂(g): 有限部は成分和、∞ 部は M312F 加法準同型
    （logVolGlobal(rawNeg(f+g)) ≈ logVolGlobal(rawNeg f)+logVolGlobal(rawNeg g)）。 -/
def ardPrincipalHom (logp : Nat → RReal) : Hom picDivGrp ardGroup where
  map := Quot.lift (fun f => Quot.mk ardEq (ardPrincipalRaw logp f))
    (fun _ _ hf => Quot.sound
      ⟨fun k => hf k,
       logVolGlobal_wd logp (fun k => by
         show -(_) = -(_)
         rw [hf k])⟩)
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show Quot.mk ardEq (ardPrincipalRaw logp (rawAdd a b))
        = Quot.mk ardEq (ardAdd (ardPrincipalRaw logp a) (ardPrincipalRaw logp b))
    refine Quot.sound ⟨fun k => rfl, ?_⟩
    have hraw : rawEq (rawNeg (rawAdd a b)) (rawAdd (rawNeg a) (rawNeg b)) := by
      intro k
      show -(a.coeff k + b.coeff k) = -(a.coeff k) + -(b.coeff k)
      omega
    exact realEq_trans (logVolGlobal_wd logp hraw)
      (logVolGlobal_add logp (rawNeg a) (rawNeg b))

/-- **M356F-7c: 主 Arakelov 因子部分群** im(div̂) ⊆ D̂（M267F imSubgroup）。 -/
def ardPrincipalSub (logp : Nat → RReal) : Subgroup ardGroup :=
  imSubgroup (ardPrincipalHom logp)

/-- **M356F-7d: 主因子部分群は正規**（D̂ はアーベル）。 -/
theorem ardPrincipalNormal (logp : Nat → RReal) :
    IsNormalSubgroup ardGroup (ardPrincipalSub logp) :=
  ardAbelianNormal (ardPrincipalSub logp)

/-- **M356F-7e: Arakelov Picard 群** Pic^(D̂) = D̂ / im(div̂)（M267F quotientGroupN）。
    Arakelov 直線束の同型類群の代数的実体＝Arakelov 因子群を主因子で割った cokernel。 -/
def ardPicard (logp : Nat → RReal) : Grp :=
  quotientGroupN ardGroup (ardPrincipalSub logp) (ardPrincipalNormal logp)

/-- **M356F-7f: 射影 D̂ → Pic^(D̂) は全射準同型**。 -/
theorem ard_pic_proj_surjective (logp : Nat → RReal) :
    ∀ x : (ardPicard logp).carrier,
      ∃ D, (quotientProjN ardGroup (ardPrincipalSub logp)
              (ardPrincipalNormal logp)).map D = x :=
  quotientProjN_surjective ardGroup (ardPrincipalSub logp) (ardPrincipalNormal logp)

/-! ## M356F-8: deg が Arakelov Picard 群に降りる（主因子不変性） -/

/-- **M356F-8a: 主 Arakelov 因子（有限因子から）の次数=0** — deg(⟨f,−deg_fin(f)⟩)=0。
    deg = Σ_p f_p·log p + (−Σ_p f_p·log p) = logVolGlobal(f+(−f)) ≈ 0（零係数因子）。 -/
theorem ard_principalRaw_degree_zero (logp : Nat → RReal) (f : RawDiv) :
    realEq (ardDeg logp (ardPrincipalRaw logp f)) realZero := by
  show realEq (realAdd (logVolGlobal logp f) (logVolGlobal logp (rawNeg f))) realZero
  have hzero : realEq (logVolGlobal logp (rawAdd f (rawNeg f))) realZero :=
    logVolGlobal_zero_coeff logp (fun k => by
      show f.coeff k + -(f.coeff k) = 0
      omega)
  exact realEq_trans
    (realEq_symm (logVolGlobal_add logp f (rawNeg f))) hzero

/-- **M356F-8b: deg は主因子の加算で不変（Pic 上の well-defined 性）** —
    deg(D̂ + div̂(f)) ≈ deg(D̂)。deg の加法準同型＋主因子の次数0 から、次数は
    主因子で移動しても不変＝deg が Arakelov Picard 群 Pic^(D̂) の上に降りる。 -/
theorem ard_deg_descends (logp : Nat → RReal) (D : ardRaw) (f : RawDiv) :
    realEq (ardDeg logp (ardAdd D (ardPrincipalRaw logp f))) (ardDeg logp D) := by
  refine realEq_trans (ard_deg_hom logp D (ardPrincipalRaw logp f)) ?_
  refine realEq_trans
    (realAdd_congr_right (ardDeg logp D) (ard_principalRaw_degree_zero logp f)) ?_
  exact realAdd_zero (ardDeg logp D)

/-! ## M356F-9: capstone -/

/-- **M356F-9a: Arakelov 因子データ** — Arakelov 因子群 D̂・実次数 deg・主因子準同型
    div̂・Arakelov Picard 群 Pic^(D̂) の束ね。 -/
structure ArakelovDivisorData (logp : Nat → RReal) where
  /-- Arakelov 因子群 D̂ = D_fin ⊕ D_∞（本物のアーベル群）。 -/
  divhat : Grp
  /-- 実 Arakelov 次数 deg : D̂ → ℝ。 -/
  deg : ardRaw → RReal
  /-- 主因子準同型 div̂ : Div → D̂（本物の Hom）。 -/
  principal : Hom picDivGrp divhat
  /-- Arakelov Picard 群 Pic^(D̂)。 -/
  pic : Grp
  /-- deg の加法準同型 deg(D+E) ≈ deg D + deg E。 -/
  deg_hom : ∀ D E, realEq (deg (ardAdd D E)) (realAdd (deg D) (deg E))
  /-- 主因子準同型の次数は 0（Pic 上の well-defined 性）。 -/
  principal_deg_zero : ∀ f, realEq (deg (ardPrincipalRaw logp f)) realZero

/-- **M356F-9b: 実データ** — 全フィールドを本物で充足。 -/
def arakelovDivisorData (logp : Nat → RReal) : ArakelovDivisorData logp where
  divhat := ardGroup
  deg := ardDeg logp
  principal := ardPrincipalHom logp
  pic := ardPicard logp
  deg_hom := ard_deg_hom logp
  principal_deg_zero := ard_principalRaw_degree_zero logp

/-- **M356F-9c: 存在** — Arakelov 因子データは充足可能（K=ℚ）。 -/
theorem ard_exists (logp : Nat → RReal) : Nonempty (ArakelovDivisorData logp) :=
  ⟨arakelovDivisorData logp⟩

/-- **M356F-9d: div̂ は群準同型** div̂(f+g)=div̂(f)+div̂(g)（∞ 部は M312F 加法性）。 -/
theorem ard_principal_isHom (logp : Nat → RReal) (x y : picDivGrp.carrier) :
    (ardPrincipalHom logp).map (picDivGrp.mul x y)
      = ardGroup.mul ((ardPrincipalHom logp).map x) ((ardPrincipalHom logp).map y) :=
  (ardPrincipalHom logp).map_mul x y

/-! ## M356F-10: 実例（具体的な ℚ^× 元の主 Arakelov 因子） -/

/-- **M356F-10a: 実例 x=2 の主 Arakelov 因子は次数0** — div̂(2)=[P_2]+(−log2·∞)、
    deg = log2 + (−log2) = 0。 -/
theorem ard_example_two (logp : Nat → RReal) :
    realEq (ardDeg logp (ardPrincipal logp (pfSinglePrime 0 1))) realZero :=
  ard_principal_degree_zero logp (pfSinglePrime 0 1)

/-- **M356F-10b: 実例 x=6=2·3 の主 Arakelov 因子は次数0**（合成因子でも積公式）。 -/
theorem ard_example_six (logp : Nat → RReal) :
    realEq (ardDeg logp
      (ardPrincipal logp (pfRatMul (pfSinglePrime 0 1) (pfSinglePrime 1 1)))) realZero :=
  ard_principal_degree_zero logp (pfRatMul (pfSinglePrime 0 1) (pfSinglePrime 1 1))

/-- **M356F-10c: 実例（零 Arakelov 因子の次数0）** — deg(0̂)=0（零因子＋実重み0）。 -/
theorem ard_example_zero (logp : Nat → RReal) :
    realEq (ardDeg logp ardZero) realZero := by
  show realEq (realAdd (logVolGlobal logp rawZero) realZero) realZero
  refine realEq_trans (realAdd_zero (logVolGlobal logp rawZero)) ?_
  exact logVolGlobal_zero logp

/-- **M356F-10d: 実例（加法準同型）** deg(D̂+Ê)≈deg D̂+deg Ê の具体束ね。 -/
theorem ard_example_hom (logp : Nat → RReal) (D E : ardRaw) :
    realEq (ardDeg logp (ardAdd D E))
      (realAdd (ardDeg logp D) (ardDeg logp E)) :=
  ard_deg_hom logp D E

end IUT
