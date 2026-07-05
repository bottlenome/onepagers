/-
# M256F: 塔剰余射の核の逆包含 — 基底レベルで ker ρ₀ ⊆ (λ₀)、核 = (λ₀) の等式
        （柱B B-1・剰余体環同型 O₀/(λ₀) ≅ ℤ/p の第一同型定理骨格）

M251F `IUT/LambdaTowerResidueKernel.lean`（下界 (λₙ) ⊆ ker ρₙ・
付値 ≥ 1 ⟹ ρₙ(a) = 0、`tower_res_kills_val_ge_one`）と
M246F `IUT/LambdaTowerResidueSurj.lean`（f 側: ρₙ の全射性
`eisRes_surjective` / `tower_res_surjective`）の直上に立つ。

背景（M251F/M246F の正直な限定）:
  * M251F は核の**下界** (λₙ) ⊆ ker ρₙ（付値 ≥ 1 ⟹ 剰余 0）を全レベルで
    無条件に閉じたが、**逆包含** ker ρₙ ⊆ (λₙ)（剰余 0 ⟹ 付値 ≥ 1、
    すなわち核 = (λₙ) の等式・剰余体環同型 Oₙ/(λₙ) ≅ ℤ/p）は
    「次層に残る」と明示申告していた（M251F 正直な限定第 1 段:
    「逆包含には各レベルの整域性・付値の完全性を要し次層に残る」）。
  * M246F は f 側を ρₙ の**全射性**（値域 = ℤ/p 全体・f = 1）として
    閉じたが、核の構造（核 = (λₙ)）は「別枝」として残していた。

本層はこの逆包含を**基底レベル n = 0（O₀ = ℤ_p[[X]]/(E)）で無条件に
架ける**。鍵は M43（`IUT/PadicDivision.lean`）の p-可除性の level-1 判定
`zp_dvd_p_iff`（x のレベル 1 射影 = 0 ⟺ ∃e, x = p·e）と、M93F
（`IUT/EisDomain.lean`）の witness 付き λ 割り算
`eis_lambda_division_exists`（代表 f の定数項 f₀ が π で割れるなら
mk f = λ·x′ を明示構成）である:

  * **逆包含 ker ρ₀ ⊆ (λ₀)（本丸）**: ρ₀(mk f) = 0 は定義計算で
    「定数項 f₀ のレベル 1 射影 = 0」、すなわち f₀ ≡ 0 (mod p)。
    `zp_dvd_p_iff` で f₀ = π·e（witness e）を取り、`eis_lambda_division_exists`
    に食わせると mk f = λ·x′。ゆえに mk f ∈ (λ₀)（付値 ≥ 1、
    `IsValAtLeast (eisRing p) (eisLambda p) (mk f) 1`、witness は x′）。
  * **核 = (λ₀) の等式**: 逆包含（本丸）と M251F の下界（基底 instance、
    ここでは eisRes 上に再証明）を合わせ、
    ρ₀(a) = 0 ⟺ a ∈ (λ₀) の双条件を閉じる。
  * **剰余体環同型 O₀/(λ₀) ≅ ℤ/p の第一同型定理骨格**: M246F の
    全射性（値域 = ℤ/p）+ 本層の核 = (λ₀)（核の完全同定）は、第一
    同型定理により O₀/(λ₀) ≅ ℤ/p を決定する**データ骨格**である。

内容:
  * M256F-1 `eisRes_ker_sub_lambda` — **逆包含（本丸）**: ρ₀(a) = 0 なら
    a ∈ (λ₀)（付値 ≥ 1）。`zp_dvd_p_iff` + `eis_lambda_division_exists`。
  * M256F-2 `eisRes_lambda_sub_ker` — **下界（基底 instance）**:
    a ∈ (λ₀) なら ρ₀(a) = 0（a = h·λ を `map_mul` + `eisRes_lambda` で
    吸収、M251F `tower_res_kills_val_ge_one` の n = 0 版を eisRes 上で
    直接再証明）。
  * M256F-3 `eisRes_ker_eq_lambda` — **核 = (λ₀) の等式（双条件）**:
    ρ₀(a) = 0 ⟺ a ∈ (λ₀)。
  * M256F-4 `tower_res_ker_eq_gen_base` — 塔記法での言い換え
    （towerLevel p 0 = O₀・towerGen p 0 = λ₀・towerRes p hp 0 = ρ₀ の
    defeq）: ρ₀(a) = 0 ⟺ IsValAtLeast … (towerGen p 0) a 1。
  * M256F-5 `EisResidueFieldIsoSkeleton` / `eisResidueFieldIsoSkeleton` /
    `eisResidueFieldIso_exists` — **剰余体環同型の第一同型定理骨格**:
    全射性（M246F）+ 核 = (λ₀)（本層）のレコードと witness・存在。

意義: M251F が「別枝」「次層」と申告した逆包含を、基底レベルで
無条件に閉じ、核 = (λ₀) の**完全等式**を確立する。M246F の全射性と
合わせ、剰余体環同型 O₀/(λ₀) ≅ ℤ/p の第一同型定理骨格
（全射 + 核の完全同定）まで到達する。ef = [L:K] 簿記の f 側
（剰余体拡大次数 f = 1）を、値域だけでなく**核の完全構造**まで
押さえた形。

正直な限定:
  * 本層が確定するのは**基底レベル n = 0** の逆包含 ker ρ₀ ⊆ (λ₀)・
    核 = (λ₀) の等式・剰余体環同型骨格のみである。**上位レベル
    n ≥ 1 の逆包含**（ρ_{n+1}(a) = 0 ⟹ a ∈ (λ_{n+1})）は、towerStep
    R[[Y]]/(π_R Y + Y^p − λ_R) 上の一変数 λ 割り算補題（`eis_lambda_division`
    の一段昇り版・生成元 Y = λ' による割り算）を要し**本層では未達・
    次層に残る**。したがって核 = (λₙ) の等式・Oₙ/(λₙ) ≅ ℤ/p も
    n ≥ 1 では依然未達。
  * 剰余体環同型 O₀/(λ₀) ≅ ℤ/p は**第一同型定理の骨格データ**
    （全射性 + 核の完全同定）として供給するのみで、商環 O₀/(λ₀) の
    構成そのものと環同型写像の明示構成は本層では扱わない（骨格に留める）。
  * e 側の完全等式（v(π_{n+1}) = p·v(π_n)・ef = [Oₙ:O₀] の module
    次数）は M235F/M246F/M251F の正直申告どおり依然未達。

全て選択公理不使用（M251F/M246F/M93F/M43/LambdaValuation/LambdaTowerGen
から propext, Quot.sound を継承、新規 Classical.choice を証明本体で
導入しない）。サブエージェント並行部品（tier M）。
-/
import IUT.LambdaTowerResidueKernel
import IUT.EisDomain
import IUT.PadicDivision

namespace IUT

/-! ## M256F-1: 逆包含（本丸）— ρ₀(a) = 0 ⟹ a ∈ (λ₀) -/

/-- **定理 (M256F-1, 本丸): 剰余核の逆包含（基底レベル）** —
    基底剰余射 ρ₀ = `eisRes p hp` : O₀ = ℤ_p[[X]]/(E) → ℤ/p の核は
    極大イデアル (λ₀) に含まれる: ρ₀(a) = 0 なら a ∈ (λ₀)
    （`IsValAtLeast (eisRing p) (eisLambda p) a 1`）。
    代表 f を取ると ρ₀(mk f) = 0 は定義計算で定数項 f₀ のレベル 1
    射影が 0、すなわち f₀ ≡ 0 (mod p)。M43-5 `zp_dvd_p_iff` で
    f₀ = π·e（witness e）を取り、M93F-3 `eis_lambda_division_exists`
    で mk f = λ·x′。mul_comm で mk f = x′·λ = x′·λ^1 とし付値 ≥ 1 の
    witness x′ を供給する。 -/
theorem eisRes_ker_sub_lambda (p : Nat) (hp : 2 ≤ p)
    (a : (eisRing p).carrier)
    (ha : (eisRes p hp).map a = (zmodRing (p ^ 1)).zero) :
    IsValAtLeast (eisRing p) (eisLambda p) a 1 := by
  induction a using Quot.ind
  rename_i f
  have hval : (f 0).val 1 = Quot.mk (modCong (p ^ 1)).rel 0 := ha
  obtain ⟨e, he⟩ := (zp_dvd_p_iff p hp (f 0)).mpr hval
  obtain ⟨x', hx'⟩ := eis_lambda_division_exists p hp f e he
  refine ⟨x', ?_⟩
  rw [rpow_one (eisRing p) (eisLambda p), hx']
  exact (eisRing p).mul_comm (eisLambda p) x'

/-! ## M256F-2: 下界（基底 instance）— a ∈ (λ₀) ⟹ ρ₀(a) = 0 -/

/-- **定理 (M256F-2): 剰余核の下界（基底レベル）** — a ∈ (λ₀)
    （付値 ≥ 1）なら ρ₀(a) = 0。a = h·λ^1 の witness を `rpow_one` で
    h·λ に開き、`map_mul` で ρ₀(h)·ρ₀(λ) に落とし、M111 `eisRes_lambda`
    （ρ₀(λ) = 0）を掛け算で吸収（`CRing.mul_zero`）。M251F
    `tower_res_kills_val_ge_one` の n = 0 版を eisRes 上で直接再証明
    （双条件を閉じるための下界側）。 -/
theorem eisRes_lambda_sub_ker (p : Nat) (hp : 2 ≤ p)
    (a : (eisRing p).carrier)
    (ha : IsValAtLeast (eisRing p) (eisLambda p) a 1) :
    (eisRes p hp).map a = (zmodRing (p ^ 1)).zero := by
  obtain ⟨h, hx⟩ := ha
  rw [hx, rpow_one (eisRing p) (eisLambda p), (eisRes p hp).map_mul,
    eisRes_lambda p hp]
  exact CRing.mul_zero (zmodRing (p ^ 1)) ((eisRes p hp).map h)

/-! ## M256F-3: 核 = (λ₀) の等式（双条件） -/

/-- **定理 (M256F-3): 核 = (λ₀) の等式（基底レベル）** —
    ρ₀(a) = 0 ⟺ a ∈ (λ₀)（付値 ≥ 1）。逆包含 M256F-1 と下界 M256F-2 の
    合流。基底剰余射の核が極大イデアル (λ₀) と**正確に一致**する
    （核の完全同定）。M251F が「次層」と申告した逆包含の基底解消。 -/
theorem eisRes_ker_eq_lambda (p : Nat) (hp : 2 ≤ p)
    (a : (eisRing p).carrier) :
    (eisRes p hp).map a = (zmodRing (p ^ 1)).zero
      ↔ IsValAtLeast (eisRing p) (eisLambda p) a 1 :=
  ⟨eisRes_ker_sub_lambda p hp a, eisRes_lambda_sub_ker p hp a⟩

/-! ## M256F-4: 塔記法での言い換え -/

/-- **定理 (M256F-4): 塔記法での核 = (λ₀)（基底レベル）** —
    towerLevel p 0 = O₀・towerGen p 0 = λ₀・towerRes p hp 0 = ρ₀ の
    defeq を通じて M256F-3 を塔の生成元 `towerGen` と剰余射 `towerRes`
    の言葉で述べる: ρ₀(a) = 0 ⟺ IsValAtLeast … (towerGen p 0) a 1。
    M251F `tower_res_kills_val_ge_one` の n = 0 の逆包含を塔記法で
    閉じたもの。 -/
theorem tower_res_ker_eq_gen_base (p : Nat) (hp : 2 ≤ p)
    (a : (towerLevel p 0).ring.carrier) :
    (towerRes p hp 0).res.map a = (zmodRing (p ^ 1)).zero
      ↔ IsValAtLeast (towerLevel p 0).ring (towerGen p 0) a 1 :=
  eisRes_ker_eq_lambda p hp a

/-! ## M256F-5: 剰余体環同型の第一同型定理骨格 -/

/-- **M256F-5a: 総括** — 剰余体環同型 O₀/(λ₀) ≅ ℤ/p の第一同型定理
    骨格データ: 全射性（M246F, 値域 = ℤ/p・f = 1）と核 = (λ₀) の完全
    同定（本層）。この二つが第一同型定理により O₀/(λ₀) ≅ ℤ/p を
    決定する（商環と同型写像の明示構成は骨格に留める）。 -/
structure EisResidueFieldIsoSkeleton (p : Nat) (hp : 2 ≤ p) where
  /-- f 側（M246F）: ρ₀ : O₀ → ℤ/p は全射（値域 = ℤ/p 全体・f = 1）。 -/
  surjective : ∀ c : (zmodRing (p ^ 1)).carrier,
    ∃ x : (eisRing p).carrier, (eisRes p hp).map x = c
  /-- 本層: 核 = (λ₀) の完全同定 — ρ₀(a) = 0 ⟺ a ∈ (λ₀)。 -/
  ker_eq_lambda : ∀ a : (eisRing p).carrier,
    (eisRes p hp).map a = (zmodRing (p ^ 1)).zero
      ↔ IsValAtLeast (eisRing p) (eisLambda p) a 1

/-- **M256F-5b: witness** — M246F `eisRes_surjective`（全射）と本層
    `eisRes_ker_eq_lambda`（核 = (λ₀)）で純レコードを充填
    （選択公理不使用）。 -/
def eisResidueFieldIsoSkeleton (p : Nat) (hp : 2 ≤ p) :
    EisResidueFieldIsoSkeleton p hp where
  surjective := eisRes_surjective p hp
  ker_eq_lambda := eisRes_ker_eq_lambda p hp

/-- **M256F-5c: 存在定理（ヘッドライン）** — 基底 O₀ = ℤ_p[[X]]/(E) の
    剰余射 ρ₀ : O₀ → ℤ/p は全射であり（M246F, f = 1）、その核は極大
    イデアル (λ₀) と正確に一致する（本層, ker ρ₀ = (λ₀)）。この二つは
    第一同型定理により剰余体環同型 O₀/(λ₀) ≅ ℤ/p を決定する骨格
    データである。M251F が「次層」と申告した逆包含 ker ρ ⊆ (λ) の
    基底解消——柱B B-1（λ-塔の剰余・分岐構造）の一段。 -/
theorem eisResidueFieldIso_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (EisResidueFieldIsoSkeleton p hp) :=
  ⟨eisResidueFieldIsoSkeleton p hp⟩

end IUT
