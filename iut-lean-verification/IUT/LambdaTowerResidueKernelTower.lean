/-
# M260F: 塔剰余射の核 = 極大イデアル(λₙ) を塔全体（全 n）へ持ち上げ
        ——剰余体環同型 Oₙ/(λₙ) ≅ ℤ/p の骨格を全レベルで
        （柱B B-1・ef=[L:K] 簿記の f 側 完全核構造）

M256F `IUT/LambdaTowerResidueKernelConverse.lean`（基底レベル n = 0 で
逆包含 ker ρ₀ ⊆ (λ₀)・核 = (λ₀) を無条件に閉じ、剰余体環同型
O₀/(λ₀) ≅ ℤ/p の第一同型定理骨格まで到達）、M251F
`IUT/LambdaTowerResidueKernel.lean`（下界 (λₙ) ⊆ ker ρₙ・全 n）、M246F
`IUT/LambdaTowerResidueSurj.lean`（全射 ρₙ・全 n・f = 1）の直上に立つ。

背景（M256F の正直な限定）:
  * M256F は逆包含 ker ρ ⊆ (λ) を**基底レベル n = 0 のみ**で閉じ、
    「上位レベル n ≥ 1 の逆包含は towerStep 上の一変数 λ 割り算補題を要し
    次層に残る」と明示申告していた。核 = (λₙ) の等式・Oₙ/(λₙ) ≅ ℤ/p も
    n ≥ 1 では未達だった。

本層はこの逆包含を**塔全体（全 n）へ持ち上げる**。鍵は次の二点:

  * **一段の λ' 割り算（本丸・generic）** `towerStep_ker_div`:
    一段昇り環 S = R[[Y]]/(π_R Y + Y^p − λ_R) の任意元 mk f について、
    定数係数 f₀ が (λ_R) に属する（f₀ = h·λ_R）なら mk f ∈ (λ')
    （λ' = Y mod (…)）。証明は級数の頭出し分解
    f = X·shift(f) + C(f₀)（`psX_shift_decomp_gen`、一般環版）と、
    塔の関係式 `towerStep_shape`（ι(λ_R) = π' λ' + λ'^p = λ'·(π' + λ'^{p−1})、
    ゆえに ι(λ_R) ∈ (λ')）を組み合わせ、
    mk f = λ'·mk(shift f) + ι(f₀) = λ'·mk(shift f) + ι(h)·ι(λ_R)
         = (mk(shift f) + ι(h)·(π' + λ'^{p−1}))·λ' を明示構成する。
  * **n 帰納持ち上げ** `tower_res_ker_sub_gen`: ρ_{n+1}(mk f) = ρ_n(f₀)
    （塔剰余射の定義計算）が 0 なら、帰納法の仮定（レベル n の逆包含）で
    f₀ ∈ (λₙ)、上の一段割り算で mk f ∈ (λ_{n+1})。基底は M256F。

内容:
  * M260F-1 `cr_add_mul` — 右分配律 (a+b)·c = a·c + b·c（一般環、
    左分配 + 交換から導出）。
  * M260F-2 `rpow_pred_mul` — a^k = a^{k−1}·a（k ≥ 1、一般環）。
  * M260F-3 `psMul_X_coeff_zero_gen` / `psMul_X_coeff_gen` /
    `psX_shift_decomp_gen` — 級数の頭出し分解の一般環版
    （M93F `psMul_X_coeff*`・`psX_shift_decomp` の zpRing 固定版を任意環へ）。
  * M260F-4 `towerStep_ker_div` — **一段の λ' 割り算（本丸・generic）**。
  * M260F-5 `tower_res_ker_sub_gen` — **逆包含の塔全体化（全 n）**:
    ρ_n(a) = 0 ⟹ a ∈ (λ_n)。基底 M256F を一段割り算で n 帰納持ち上げ。
  * M260F-6 `tower_res_ker_eq_gen` — **核 = (λ_n) の等式（全 n）**:
    ρ_n(a) = 0 ⟺ a ∈ (λ_n)。本層の逆包含 + M251F の下界。
  * M260F-7 `TowerResidueFieldIsoTower` / `towerResidueFieldIsoTower` /
    `towerResidueFieldIsoTower_exists` — **塔全体の剰余体環同型骨格**:
    全レベルで全射（M246F）+ 核 = (λ_n)（本層）。第一同型定理により
    Oₙ/(λₙ) ≅ ℤ/p を全 n で決定するデータ骨格。

意義: M256F が「基底のみ・n ≥ 1 は次層」と申告した逆包含・核等式・
剰余体環同型骨格を、towerStep 上の一段 λ' 割り算を無条件に確立する
ことで**塔全体（全 n）へ一気に持ち上げる**。ef=[L:K] 簿記の f 側
（剰余体拡大次数 f = 1）を、値域（M246F 全射）だけでなく**核の完全構造
（核 = (λ_n)・全 n）**まで全レベルで押さえた形。

正直な限定:
  * 本層が確定するのは核 = (λ_n) の等式・剰余体環同型 Oₙ/(λₙ) ≅ ℤ/p の
    **第一同型定理骨格（全射 + 核の完全同定）を全 n で**まで。商環
    Oₙ/(λₙ) の構成そのものと環同型写像の明示構成は骨格に留める
    （M256F 同様、供給するのはデータ骨格のみ）。
  * e 側の完全等式（v(π_{n+1}) = p·v(π_n)・ef = [Oₙ:O₀] の module 次数）
    は M235F/M246F/M251F/M256F の正直申告どおり依然未達。本層は f 側
    （核構造）を塔全体へ閉じるのみで、e·f を module 次数として確定する
    ものではない。

全て選択公理不使用（M256F/M251F/M246F/M109/LambdaValuation/LambdaTowerGen
から propext, Quot.sound を継承、新規 Classical.choice を証明本体で
導入しない）。サブエージェント並行部品（tier M）。
-/
import IUT.LambdaTowerResidueKernelConverse
import IUT.LambdaTowerResidueKernel
import IUT.LambdaTowerGen

namespace IUT

/-! ## M260F-1: 右分配律 (a+b)·c = a·c + b·c -/

/-- **定理 (M260F-1): 右分配律** — 一般可換環で (a+b)·c = a·c + b·c
    （左分配 `left_distrib` と交換 `mul_comm` から）。 -/
theorem cr_add_mul (R : CRing) (a b c : R.carrier) :
    R.mul (R.add a b) c = R.add (R.mul a c) (R.mul b c) := by
  rw [R.mul_comm (R.add a b) c, R.left_distrib c a b,
    R.mul_comm c a, R.mul_comm c b]

/-! ## M260F-2: 環冪の一段剥がし a^k = a^{k-1}·a -/

/-- **定理 (M260F-2): a^k = a^{k−1}·a**（k ≥ 1、一般環）。rpow の
    succ 展開を k = (k−1)+1 で畳む。λ'^p を λ'·λ'^{p−1} に分けて
    塔の関係式から λ' を括り出す糊。 -/
theorem rpow_pred_mul (R : CRing) (a : R.carrier) (k : Nat) (hk : 1 ≤ k) :
    rpow R a k = R.mul (rpow R a (k - 1)) a := by
  cases k with
  | zero => exact absurd hk (by omega)
  | succ m =>
    show R.mul (rpow R a m) a = R.mul (rpow R a (m + 1 - 1)) a
    rw [show m + 1 - 1 = m from by omega]

/-! ## M260F-3: 級数の頭出し分解（一般環版） -/

/-- **M260F-3a**: (X·g)₀ = 0（一般環、M93F `psMul_X_coeff_zero` の任意環版）。 -/
theorem psMul_X_coeff_zero_gen (R : CRing) (g : PS R) :
    psMul R (psX R) g 0 = R.zero := by
  show R.add R.zero (R.mul (psX R 0) (g (0 - 0))) = R.zero
  rw [R.zero_add, show psX R 0 = R.zero from if_neg (by omega)]
  exact CRing.zero_mul R (g (0 - 0))

/-- **M260F-3b**: (X·g)_{m+1} = g_m（一般環、M93F `psMul_X_coeff` の任意環版）。 -/
theorem psMul_X_coeff_gen (R : CRing) (g : PS R) (m : Nat) :
    psMul R (psX R) g (m + 1) = g m := by
  show rsum R (fun k => R.mul (psX R k) (g (m + 1 - k))) (m + 2) = g m
  have hs : rsum R (fun k => R.mul (psX R k) (g (m + 1 - k))) (m + 2)
      = R.mul (psX R 1) (g (m + 1 - 1)) := by
    refine rsum_single R _ 1 (m + 2) (by omega) (fun j _ hne => ?_)
    show R.mul (psX R j) (g (m + 1 - j)) = R.zero
    rw [show psX R j = R.zero from if_neg hne]
    exact CRing.zero_mul R (g (m + 1 - j))
  rw [hs, show psX R 1 = R.one from if_pos rfl, R.one_mul,
    show m + 1 - 1 = m from by omega]

/-- **M260F-3c: 頭出し分解（一般環版）** — f = X·shift(f) + C(f₀)
    （M93F `psX_shift_decomp` の任意環版）。 -/
theorem psX_shift_decomp_gen (R : CRing) (f : PS R) :
    f = psAdd R (psMul R (psX R) (psShift R f)) (psC R (f 0)) := by
  funext m
  cases m with
  | zero =>
    show f 0 = R.add (psMul R (psX R) (psShift R f) 0) (f 0)
    rw [psMul_X_coeff_zero_gen R (psShift R f), R.zero_add]
  | succ m =>
    show f (m + 1) = R.add (psMul R (psX R) (psShift R f) (m + 1)) R.zero
    rw [psMul_X_coeff_gen R (psShift R f) m, CRing.add_zero R (psShift R f m)]
    rfl

/-! ## M260F-4: 一段の λ' 割り算（本丸・generic） -/

/-- **定理 (M260F-4, 本丸): 一段昇りの λ' 割り算** —
    一段昇り環 S = R[[Y]]/(π_R Y + Y^p − λ_R) の元 mk f について、
    代表 f の定数係数 f₀ が (λ_R) に属する（f₀ = h·λ_R）なら
    mk f ∈ (λ')（λ' = Y mod (…)、付値 ≥ 1）。
    級数分解 `psX_shift_decomp_gen`（f = X·shift f + C(f₀)）で
    mk f = λ'·mk(shift f) + ι(f₀)、ι(f₀) = ι(h)·ι(λ_R)、
    塔の関係式 `towerStep_shape`（ι(λ_R) = λ'·(π' + λ'^{p−1})）で
    ι(f₀) = (ι(h)·(π' + λ'^{p−1}))·λ'。両項の λ' を右に括り出し
    mk f = (mk(shift f) + ι(h)·(π' + λ'^{p−1}))·λ'。 -/
theorem towerStep_ker_div (p : Nat) (hp1 : 1 ≤ p) (R : CRing)
    (piR lamR : R.carrier) (f : PS R) (h : R.carrier)
    (hh : f 0 = R.mul h lamR) :
    IsValAtLeast (towerStep p R piR lamR) (towerLam p R piR lamR)
      (Quot.mk (idealRel (psRing R) (towerStepPoly p R piR lamR)) f) 1 := by
  -- 塔の関係式: ι(λ_R) = π'·λ' + λ'^p
  have hshape : (towerStepOf p R piR lamR).map lamR
      = (towerStep p R piR lamR).add
          ((towerStep p R piR lamR).mul ((towerStepOf p R piR lamR).map piR)
            (towerLam p R piR lamR))
          (rpow (towerStep p R piR lamR) (towerLam p R piR lamR) p) :=
    (towerStep_shape p R piR lamR).symm
  -- λ'^p = λ'^{p-1}·λ'
  have hpm : rpow (towerStep p R piR lamR) (towerLam p R piR lamR) p
      = (towerStep p R piR lamR).mul
          (rpow (towerStep p R piR lamR) (towerLam p R piR lamR) (p - 1))
          (towerLam p R piR lamR) :=
    rpow_pred_mul (towerStep p R piR lamR) (towerLam p R piR lamR) p hp1
  -- ι(λ_R) = (π' + λ'^{p-1})·λ'
  have hiota : (towerStepOf p R piR lamR).map lamR
      = (towerStep p R piR lamR).mul
          ((towerStep p R piR lamR).add ((towerStepOf p R piR lamR).map piR)
            (rpow (towerStep p R piR lamR) (towerLam p R piR lamR) (p - 1)))
          (towerLam p R piR lamR) := by
    rw [hshape, hpm]
    exact (cr_add_mul (towerStep p R piR lamR) ((towerStepOf p R piR lamR).map piR)
      (rpow (towerStep p R piR lamR) (towerLam p R piR lamR) (p - 1))
      (towerLam p R piR lamR)).symm
  -- 頭出し分解: mk f = λ'·mk(shift f) + ι(f₀)
  have hdecomp :
      (quotOf (psRing R) (towerStepPoly p R piR lamR)).map f
        = (towerStep p R piR lamR).add
            ((towerStep p R piR lamR).mul (towerLam p R piR lamR)
              ((quotOf (psRing R) (towerStepPoly p R piR lamR)).map (psShift R f)))
            ((towerStepOf p R piR lamR).map (f 0)) :=
    (congrArg (quotOf (psRing R) (towerStepPoly p R piR lamR)).map
        (psX_shift_decomp_gen R f)).trans
      (((quotOf (psRing R) (towerStepPoly p R piR lamR)).map_add
          (psMul R (psX R) (psShift R f)) (psC R (f 0))).trans
        (congrArg
          (fun t => (towerStep p R piR lamR).add t
            ((towerStepOf p R piR lamR).map (f 0)))
          ((quotOf (psRing R) (towerStepPoly p R piR lamR)).map_mul
            (psX R) (psShift R f))))
  -- ι(f₀) = (ι(h)·(π' + λ'^{p-1}))·λ'
  have hc1 : (towerStepOf p R piR lamR).map (f 0)
      = (towerStep p R piR lamR).mul ((towerStepOf p R piR lamR).map h)
          ((towerStepOf p R piR lamR).map lamR) := by
    rw [hh]; exact (towerStepOf p R piR lamR).map_mul h lamR
  have hconst : (towerStepOf p R piR lamR).map (f 0)
      = (towerStep p R piR lamR).mul
          ((towerStep p R piR lamR).mul ((towerStepOf p R piR lamR).map h)
            ((towerStep p R piR lamR).add ((towerStepOf p R piR lamR).map piR)
              (rpow (towerStep p R piR lamR) (towerLam p R piR lamR) (p - 1))))
          (towerLam p R piR lamR) := by
    rw [hc1, hiota, (towerStep p R piR lamR).mul_assoc]
  -- 組み立て
  refine ⟨(towerStep p R piR lamR).add
      ((quotOf (psRing R) (towerStepPoly p R piR lamR)).map (psShift R f))
      ((towerStep p R piR lamR).mul ((towerStepOf p R piR lamR).map h)
        ((towerStep p R piR lamR).add ((towerStepOf p R piR lamR).map piR)
          (rpow (towerStep p R piR lamR) (towerLam p R piR lamR) (p - 1)))), ?_⟩
  rw [rpow_one]
  show (quotOf (psRing R) (towerStepPoly p R piR lamR)).map f
    = (towerStep p R piR lamR).mul
        ((towerStep p R piR lamR).add
          ((quotOf (psRing R) (towerStepPoly p R piR lamR)).map (psShift R f))
          ((towerStep p R piR lamR).mul ((towerStepOf p R piR lamR).map h)
            ((towerStep p R piR lamR).add ((towerStepOf p R piR lamR).map piR)
              (rpow (towerStep p R piR lamR) (towerLam p R piR lamR) (p - 1)))))
        (towerLam p R piR lamR)
  rw [hdecomp, hconst,
    (towerStep p R piR lamR).mul_comm (towerLam p R piR lamR)
      ((quotOf (psRing R) (towerStepPoly p R piR lamR)).map (psShift R f)),
    ← cr_add_mul]

/-! ## M260F-5: 逆包含の塔全体化（全 n） -/

/-- **定理 (M260F-5, 本丸): 逆包含の塔全体化** — ∀ n、レベル n の
    剰余射 ρ_n の核は極大イデアル (λ_n) に含まれる:
    ρ_n(a) = 0 ⟹ a ∈ (λ_n)（付値 ≥ 1）。基底 n = 0 は M256F
    `eisRes_ker_sub_lambda`、帰納段は一段割り算 `towerStep_ker_div`
    を f₀ ∈ (λ_n) に適用（f₀ の剰余は ρ_{n+1}(mk f) に等しく、
    帰納法の仮定でレベル n の逆包含が使える）。M256F が「n ≥ 1 は
    次層」と申告した逆包含を全 n で閉じる。 -/
theorem tower_res_ker_sub_gen (p : Nat) (hp : 2 ≤ p) :
    ∀ (n : Nat) (a : (towerLevel p n).ring.carrier),
      (towerRes p hp n).res.map a = (zmodRing (p ^ 1)).zero →
      IsValAtLeast (towerLevel p n).ring (towerGen p n) a 1 := by
  intro n
  induction n with
  | zero =>
    intro a ha
    exact eisRes_ker_sub_lambda p hp a ha
  | succ n ih =>
    intro a
    induction a using Quot.ind
    rename_i f
    intro ha
    have hf0 : (towerRes p hp n).res.map (f 0) = (zmodRing (p ^ 1)).zero := ha
    obtain ⟨h, hh⟩ := ih (f 0) hf0
    rw [rpow_one] at hh
    exact towerStep_ker_div p (Nat.le_of_succ_le hp) (towerLevel p n).ring
      (towerLevel p n).pi (towerLevel p n).lam f h hh

/-! ## M260F-6: 核 = (λ_n) の等式（全 n） -/

/-- **定理 (M260F-6): 核 = (λ_n) の等式（全 n）** —
    ρ_n(a) = 0 ⟺ a ∈ (λ_n)（付値 ≥ 1）。本層の逆包含 M260F-5 と
    M251F の下界 `tower_res_kills_val_ge_one` の合流。塔剰余射の核が
    極大イデアル (λ_n) と**正確に一致**する（核の完全同定・全 n）。 -/
theorem tower_res_ker_eq_gen (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (a : (towerLevel p n).ring.carrier) :
    (towerRes p hp n).res.map a = (zmodRing (p ^ 1)).zero
      ↔ IsValAtLeast (towerLevel p n).ring (towerGen p n) a 1 :=
  ⟨tower_res_ker_sub_gen p hp n a,
   fun ha => tower_res_kills_val_ge_one p hp n ha⟩

/-! ## M260F-7: 塔全体の剰余体環同型骨格 -/

/-- **M260F-7a: 総括** — 塔全体の剰余体環同型 Oₙ/(λₙ) ≅ ℤ/p の
    第一同型定理骨格データ（全 n）: 全射性（M246F, 値域 = ℤ/p・f = 1）と
    核 = (λₙ) の完全同定（本層）。この二つが第一同型定理により
    Oₙ/(λₙ) ≅ ℤ/p を全レベルで決定する。 -/
structure TowerResidueFieldIsoTower (p : Nat) (hp : 2 ≤ p) where
  /-- f 側（M246F）: ∀ n、ρ_n : Oₙ → ℤ/p は全射（値域 = ℤ/p・f = 1）。 -/
  surjective : ∀ (n : Nat) (c : (zmodRing (p ^ 1)).carrier),
    ∃ x : (towerLevel p n).ring.carrier,
      (towerRes p hp n).res.map x = c
  /-- 本層: ∀ n、核 = (λₙ) の完全同定 — ρ_n(a) = 0 ⟺ a ∈ (λₙ)。 -/
  ker_eq_gen : ∀ (n : Nat) (a : (towerLevel p n).ring.carrier),
    (towerRes p hp n).res.map a = (zmodRing (p ^ 1)).zero
      ↔ IsValAtLeast (towerLevel p n).ring (towerGen p n) a 1

/-- **M260F-7b: witness** — M246F `tower_res_surjective`（全射・全 n）と
    本層 `tower_res_ker_eq_gen`（核 = (λₙ)・全 n）で純レコードを充填
    （選択公理不使用）。 -/
def towerResidueFieldIsoTower (p : Nat) (hp : 2 ≤ p) :
    TowerResidueFieldIsoTower p hp where
  surjective := tower_res_surjective p hp
  ker_eq_gen := tower_res_ker_eq_gen p hp

/-- **M260F-7c: 存在定理（ヘッドライン）** — 塔の各レベルの剰余射
    ρ_n : Oₙ → ℤ/p は全射であり（M246F, f = 1）、その核は極大イデアル
    (λₙ) と正確に一致する（本層, ker ρ_n = (λₙ)・**全 n**）。この二つは
    第一同型定理により剰余体環同型 Oₙ/(λₙ) ≅ ℤ/p を全レベルで決定する
    骨格データである。M256F が「n ≥ 1 は次層」と申告した逆包含・核等式・
    剰余体環同型骨格を塔全体へ持ち上げた——柱B B-1（λ-塔の剰余・分岐
    構造）の一段。 -/
theorem towerResidueFieldIsoTower_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (TowerResidueFieldIsoTower p hp) :=
  ⟨towerResidueFieldIsoTower p hp⟩

end IUT
