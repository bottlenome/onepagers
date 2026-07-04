/-
# M226F: 塔遷移像 ι(λₙ) の exact 付値（柱B B-1・下界を超える上界／等号）

M222F `IUT/LambdaTowerRamif.lean`（塔の分岐の**下界**を無条件 discharge:
π_n ∈ (λ_n)・遷移像 ι(λₙ) ∈ (λ_{n+1}²)・基点の exact v(π₀)=p−1）と
M211F `IUT/LambdaTowerExactVal.lean`（遷移像の二項還元・冪項の厳密付値
v(λ_{n+1}^p)=p）の直上に立つ。

M222F は遷移像 ι(λₙ) = f_π(λ_{n+1}) = π_{n+1}λ_{n+1} + λ_{n+1}^p の付値を
**≥ 2 の下界**までしか押し上げられなかった。本層はこれを、明示した
分岐入力 **v(π_{n+1}) ≥ p** の下で **exact 付値 v(ι(λₙ)) = p の等号**へ
引き上げる。鍵は「支配項の分離」:

  * 冪項 λ_{n+1}^p は exact 付値 p（M151F-5 `lam_pow_strict`: λ 正則・
    非単元なら λ^p ∉ (λ^{p+1})）。
  * 線形項 π_{n+1}λ_{n+1} は v(π_{n+1}) ≥ p の下で付値 ≥ p+1（M161-2
    `isValAtLeast_mul`）、すなわち冪項より**真に深い**。
  * ゆえに和 ι(λₙ) = 線形項 + 冪項 は冪項に**支配され**、
    ι(λₙ) ∉ (λ^{p+1})（**上界 v(ι(λₙ)) ≤ p**、M222F の下界を厳密に超える
    新規成果）かつ ι(λₙ) ∈ (λ^k) ⇔ k ≤ p（**exact 等号 v(ι(λₙ)) = p**）。

上界（∉ (λ^{p+1})）の論法: もし ι(λₙ) ∈ (λ^{p+1}) なら、
λ_{n+1}^p = ι(λₙ) − π_{n+1}λ_{n+1} は膜の加法/反元閉性（M164）で
(λ^{p+1}) に属し、`lam_pow_strict`（λ^p ∉ (λ^{p+1})）に矛盾。

内容:
  * M226F-1 `ringF_not_valAtLeast_p_succ` — **一般環の上界（本丸）**:
    λ 正則・非単元、線形項 π·λ ∈ (λ^{p+1}) なら ringF p R π λ ∉ (λ^{p+1})。
    支配項分離による**上界の核**。M222F の下界（≥）を超える片翼。
  * M226F-2 `ringF_exact_val_of_lin_deep` — **一般環の exact 付値**:
    同仮定で ringF p R π λ ∈ (λ^k) ⇔ k ≤ p（**等号 v = p**）。
  * M226F-3 `lin_term_deep_of_pi_val` — 仮定の橋渡し: v(π) ≥ p なら
    線形項 π·λ ∈ (λ^{p+1})（M161-2）。
  * M226F-4 `ringF_exact_val_of_pi_val` — **一般環の exact 付値（π 版）**:
    v(π) ≥ p なら ringF p R π λ の付値ちょうど p。
  * M226F-5 `towerGen_transition_not_val_p_succ_of_pi` — **塔の上界**:
    v(π_{n+1}) ≥ p なら ι(λₙ) ∉ (λ_{n+1}^{p+1})（M222F の下界 ≥ 2 を
    厳密に超える上界）。
  * M226F-6 `towerGen_transition_val_exact_of_pi` — **塔の exact 付値
    （ヘッドライン）**: v(π_{n+1}) ≥ p なら ι(λₙ) ∈ (λ_{n+1}^k) ⇔ k ≤ p、
    すなわち **v(ι(λₙ)) = p の完全等号**（分岐指数 e=p の実現の一片）。
  * M226F-7 `LambdaTowerExactRamifData` / `lambdaTowerExactRamifData` /
    `lambdaTowerExactRamif_exists` — 総括レコードと witness・存在。

意義: M222F/M211F が遺した「上位 exact 値 v(ι(λₙ)) の完全等号」を、
唯一の未形式入力 v(π_{n+1}) ≥ p を**明示仮定**として切り出したうえで
**等号として閉じる**。M222F の下界（付値 ≥ 2）を厳密に超え、上界
（∉ (λ^{p+1})）と exact 等号（付値ちょうど p）を初めて供給する。

正直な限定:
  * 本層の exact 等号 v(ι(λₙ)) = p は **v(π_{n+1}) ≥ p を明示仮定**した
    条件付き定理である。この仮定の無条件確立（分岐帰納
    v(π_{n+1}) = p·v(π_n) の完全等式・分岐指数 e=p のちょうどの実現）は、
    塔版 Eisenstein 関係式 λ_{n+1}^{p−1} = −π_{n+1} が本塔で成立せず
    （M222F の正直申告参照）、剰余体拡大次数 f と分岐指数 e の塔での
    ef=[L:K] 簿記を要するため、本層では閉じない（次層に残る）。
  * M222F が無条件に確立したのは v(π_{n+1}) ≥ 1（π_{n+1} ∈ (λ_{n+1})）の
    みで、本層が要する v(π_{n+1}) ≥ p（p ≥ 2）とは gap がある。すなわち
    「上界・等号の**構造**（支配項分離）」は本層が無条件に供給するが、
    それを発火させる分岐入力 v(π_{n+1}) ≥ p は依然仮定である。
  * 基点 n=0 では M222F が v(π₀)=p−1 を無条件確定するが、これは
    分岐指数 e=p−1 であり、本層の一般構造（e=p の分離）とは別枝。

全て選択公理不使用（M222F/M211F/M164/M161/M151F/M193F から
propext, Quot.sound を継承、新規 Classical.choice なし）。
サブエージェント並行部品（tier M）。
-/
import IUT.LambdaTowerRamif
import IUT.LambdaTowerGen

namespace IUT

/-! ## M226F-1: 一般環の上界（本丸）— 支配項分離で ringF ∉ (λ^{p+1}) -/

/-- **定理 (M226F-1, 本丸): 一般環の上界** — λ が正則かつ非単元で、
    線形項 π·λ が (λ^{p+1}) に属する（冪項 λ^p より真に深い）なら、
    ringF p R π λ = π·λ + λ^p は (λ^{p+1}) に属さない。すなわち
    **上界 v(ringF) ≤ p**。もし ringF ∈ (λ^{p+1}) なら
    λ^p = ringF − π·λ が M164 の加法/反元閉性で (λ^{p+1}) に属し、
    M151F-5 `lam_pow_strict`（λ^p ∉ (λ^{p+1})）に矛盾する。
    **M222F の付値 ≥ 2 の下界（≥）を厳密に超える上界（≤）**。 -/
theorem ringF_not_valAtLeast_p_succ (p : Nat) (R : CRing) {lam : R.carrier}
    (hreg : IsRegularElem R lam) (hnu : ∀ v, R.mul lam v ≠ R.one)
    (pi : R.carrier)
    (hlin : IsValAtLeast R lam (R.mul pi lam) (p + 1)) :
    ¬ IsValAtLeast R lam (ringF p R pi lam) (p + 1) := by
  intro h
  -- λ^p = ringF + (−(π·λ)) を膜の加法/反元閉性で (λ^{p+1}) に運ぶ
  have e : R.add (ringF p R pi lam) (R.neg (R.mul pi lam))
      = rpow R lam p := by
    show R.add (R.add (R.mul pi lam) (rpow R lam p)) (R.neg (R.mul pi lam))
        = rpow R lam p
    rw [R.add_comm (R.mul pi lam) (rpow R lam p),
      R.add_assoc (rpow R lam p) (R.mul pi lam) (R.neg (R.mul pi lam)),
      CRing.add_neg R (R.mul pi lam),
      CRing.add_zero R (rpow R lam p)]
  have hpow : IsValAtLeast R lam (rpow R lam p) (p + 1) := by
    have hsum := isValAtLeast_add h (isValAtLeast_neg hlin)
    rw [e] at hsum
    exact hsum
  exact lam_pow_strict R hreg hnu p hpow

/-! ## M226F-2: 一般環の exact 付値 — v(ringF) = p の等号 -/

/-- **定理 (M226F-2): 一般環の exact 付値** — λ 正則・非単元、線形項
    π·λ ∈ (λ^{p+1})、2 ≤ p のとき ringF p R π λ ∈ (λ^k) ⇔ k ≤ p、
    すなわち **v(ringF) = p の完全等号**。
    ⇐（k ≤ p）: 線形項 ∈ (λ^{p+1}) ⊆ (λ^k)（M151F-3b 単調降下）・
    冪項 λ^p ∈ (λ^k)（M151F-4b、k ≤ p）を M164 の加法閉性で和へ。
    ⇒（ringF ∈ (λ^k) → k ≤ p）: k > p なら M151F-3b で (λ^{p+1}) へ
    降下でき M226F-1 の上界に矛盾するので k ≤ p。 -/
theorem ringF_exact_val_of_lin_deep (p : Nat) (hp : 2 ≤ p) (R : CRing)
    {lam : R.carrier} (hreg : IsRegularElem R lam)
    (hnu : ∀ v, R.mul lam v ≠ R.one) (pi : R.carrier)
    (hlin : IsValAtLeast R lam (R.mul pi lam) (p + 1)) (k : Nat) :
    IsValAtLeast R lam (ringF p R pi lam) k ↔ k ≤ p := by
  constructor
  · intro hv
    cases Nat.lt_or_ge p k with
    | inl hlt =>
      -- p < k すなわち p+1 ≤ k: (λ^k) から (λ^{p+1}) へ降下し M226F-1 に矛盾
      exact absurd
        (isValAtLeast_mono R lam (ringF p R pi lam) k (p + 1) hlt hv)
        (ringF_not_valAtLeast_p_succ p R hreg hnu pi hlin)
    | inr hge => exact hge
  · intro hk
    -- 線形項 ∈ (λ^{p+1}) ⊆ (λ^k)、冪項 λ^p ∈ (λ^k)（k ≤ p）を和で
    have hlin' : IsValAtLeast R lam (R.mul pi lam) k :=
      isValAtLeast_mono R lam (R.mul pi lam) (p + 1) k (by omega) hlin
    have hpow' : IsValAtLeast R lam (rpow R lam p) k :=
      lam_pow_val_le p k hk
    show IsValAtLeast R lam (R.add (R.mul pi lam) (rpow R lam p)) k
    exact isValAtLeast_add hlin' hpow'

/-! ## M226F-3: 仮定の橋渡し — v(π) ≥ p なら線形項 π·λ ∈ (λ^{p+1}) -/

/-- **定理 (M226F-3): 線形項の深さ** — v(π) ≥ p（π ∈ (λ^p)）なら
    線形項 π·λ ∈ (λ^{p+1})。π ∈ (λ^p)・λ ∈ (λ^1)（M151F-4a・rpow_one）
    を M161-2 `isValAtLeast_mul` に食わせ π·λ ∈ (λ^{p+1})。 -/
theorem lin_term_deep_of_pi_val (p : Nat) (R : CRing) {lam pi : R.carrier}
    (hpi : IsValAtLeast R lam pi p) :
    IsValAtLeast R lam (R.mul pi lam) (p + 1) := by
  have hlam : IsValAtLeast R lam lam 1 := by
    have h := lam_pow_self_val R lam 1
    rw [rpow_one] at h
    exact h
  exact isValAtLeast_mul hpi hlam

/-! ## M226F-4: 一般環の exact 付値（π 版） -/

/-- **定理 (M226F-4): 一般環の exact 付値（π 版）** — λ 正則・非単元、
    **v(π) ≥ p**、2 ≤ p のとき ringF p R π λ ∈ (λ^k) ⇔ k ≤ p
    （**v(ringF) = p**）。M226F-3 で v(π) ≥ p を線形項の深さへ、
    M226F-2 に食わせる。 -/
theorem ringF_exact_val_of_pi_val (p : Nat) (hp : 2 ≤ p) (R : CRing)
    {lam : R.carrier} (hreg : IsRegularElem R lam)
    (hnu : ∀ v, R.mul lam v ≠ R.one) {pi : R.carrier}
    (hpi : IsValAtLeast R lam pi p) (k : Nat) :
    IsValAtLeast R lam (ringF p R pi lam) k ↔ k ≤ p :=
  ringF_exact_val_of_lin_deep p hp R hreg hnu pi
    (lin_term_deep_of_pi_val p R hpi) k

/-! ## M226F-5: 塔の上界 — ι(λₙ) ∉ (λ_{n+1}^{p+1}) -/

/-- **定理 (M226F-5): 塔遷移像の上界** — 上位レベルで v(π_{n+1}) ≥ p の
    分岐入力の下、遷移像 ι(λₙ) = (towerHom p n)(λₙ) は (λ_{n+1}^{p+1}) に
    属さない（**上界 v(ι(λₙ)) ≤ p**）。M203F towerGen_transition で
    遷移像を ringF に開き、M226F-1（支配項分離）の塔インスタンス。
    towerGen の正則性（M193F-3a）・非単元性（M193F-3b）を供給。
    **M222F の無条件下界 ≥ 2 を厳密に超える上界**。 -/
theorem towerGen_transition_not_val_p_succ_of_pi (p : Nat) (hp : 2 ≤ p)
    (n : Nat)
    (hpi : IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerLevel p (n + 1)).ring.mul (towerLevel p (n + 1)).pi
        (towerGen p (n + 1))) (p + 1)) :
    ¬ IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerHom p n).map (towerGen p n)) (p + 1) := by
  rw [towerGen_transition p n]
  exact ringF_not_valAtLeast_p_succ p (towerLevel p (n + 1)).ring
    (towerGen_regular p hp (n + 1)) (towerGen_not_unit p hp (n + 1))
    (towerLevel p (n + 1)).pi hpi

/-! ## M226F-6: 塔の exact 付値（ヘッドライン）— v(ι(λₙ)) = p -/

/-- **定理 (M226F-6, ヘッドライン): 塔遷移像の exact 付値** — 上位レベルで
    **v(π_{n+1}) ≥ p** の分岐入力の下、遷移像 ι(λₙ) = (towerHom p n)(λₙ)
    は ι(λₙ) ∈ (λ_{n+1}^k) ⇔ k ≤ p、すなわち **v(ι(λₙ)) = p の完全等号**。
    M203F towerGen_transition で遷移像を ringF に開き、M226F-4
    （支配項分離による exact 付値）の塔インスタンス。
    towerGen の正則性・非単元性を供給。**M222F の下界 ≥ 2 を、明示仮定
    v(π_{n+1}) ≥ p の下で exact 等号 v=p へ引き上げる**。 -/
theorem towerGen_transition_val_exact_of_pi (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (hpi : IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      (towerLevel p (n + 1)).pi p) (k : Nat) :
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
        ((towerHom p n).map (towerGen p n)) k
      ↔ k ≤ p := by
  rw [towerGen_transition p n]
  exact ringF_exact_val_of_pi_val p hp (towerLevel p (n + 1)).ring
    (towerGen_regular p hp (n + 1)) (towerGen_not_unit p hp (n + 1)) hpi k

/-! ## M226F-7: 総括 -/

/-- **M226F-7a: 総括** — 塔遷移像の exact 付値データ（すべて分岐入力
    v(π_{n+1}) ≥ p を明示仮定した条件付き）:
    一般環の上界・一般環の exact 付値・塔の上界・塔の exact 付値。 -/
structure LambdaTowerExactRamifData (p : Nat) (hp : 2 ≤ p) where
  /-- 塔の生成元 λₙ := (towerLevel p n).lam。 -/
  gen : ∀ n, (towerLevel p n).ring.carrier
  /-- 一般環の上界（支配項分離）: 線形項 π·λ ∈ (λ^{p+1}) なら
      ringF p R π λ ∉ (λ^{p+1})。 -/
  ringF_upper : ∀ (R : CRing) (lam : R.carrier),
    IsRegularElem R lam → (∀ v, R.mul lam v ≠ R.one) →
    ∀ (pi : R.carrier),
      IsValAtLeast R lam (R.mul pi lam) (p + 1) →
      ¬ IsValAtLeast R lam (ringF p R pi lam) (p + 1)
  /-- 一般環の exact 付値（π 版）: v(π) ≥ p なら
      ringF p R π λ ∈ (λ^k) ⇔ k ≤ p。 -/
  ringF_exact : ∀ (R : CRing) (lam : R.carrier),
    IsRegularElem R lam → (∀ v, R.mul lam v ≠ R.one) →
    ∀ (pi : R.carrier), IsValAtLeast R lam pi p → ∀ k,
      (IsValAtLeast R lam (ringF p R pi lam) k ↔ k ≤ p)
  /-- 塔の exact 付値（ヘッドライン）: v(π_{n+1}) ≥ p なら
      ι(λₙ) ∈ (λ_{n+1}^k) ⇔ k ≤ p（v(ι(λₙ)) = p の等号）。 -/
  transition_val_exact : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      (towerLevel p (n + 1)).pi p → ∀ k,
      (IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
          ((towerHom p n).map (gen n)) k ↔ k ≤ p)

/-- **M226F-7b: witness** — towerGen が exact 付値データを成す
    （純レコード、選択公理不使用）。 -/
def lambdaTowerExactRamifData (p : Nat) (hp : 2 ≤ p) :
    LambdaTowerExactRamifData p hp where
  gen := towerGen p
  ringF_upper := fun R lam hreg hnu pi hlin =>
    ringF_not_valAtLeast_p_succ p R hreg hnu pi hlin
  ringF_exact := fun R lam hreg hnu pi hpi k =>
    ringF_exact_val_of_pi_val p hp R hreg hnu hpi k
  transition_val_exact := fun n hpi k =>
    towerGen_transition_val_exact_of_pi p hp n hpi k

/-- **M226F-7c: 存在定理（ヘッドライン）** — Λₙ 塔の遷移像 ι(λₙ) は、
    上位レベルの分岐入力 v(π_{n+1}) ≥ p の下で **exact 付値 v(ι(λₙ)) = p**
    を持つ（支配項分離: 冪項 λ_{n+1}^p が付値 p で支配、線形項が真に深い）。
    M222F の無条件下界 ≥ 2 を、明示仮定の下で **上界（∉ (λ^{p+1})）と
    exact 等号（付値ちょうど p）**へ引き上げる。柱B B-1（塔の分岐指数
    e=p の実現）の一段。 -/
theorem lambdaTowerExactRamif_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaTowerExactRamifData p hp) :=
  ⟨lambdaTowerExactRamifData p hp⟩

end IUT
