/-
# M211F: 塔遷移 ι(λ_n) の厳密付値（柱B B-1・並行部品）

M203F（塔遷移 towerHom による生成元 λₙ の遷移像 ι(λₙ) = f_π(λ_{n+1})
= π_{n+1}λ_{n+1} + λ_{n+1}^p が上位レベルの極大イデアル (λ_{n+1}) に
属する・付値 ≥ 1）と M193F（各レベルの生成元 λₙ の付値正確に 1・
一意化元性）・M151F（λ-adic 値 v(λ^j)=j の井戸定義性）・M161/M164
（付値の加法性の下界・イデアル膜の加法/反元閉性）の直上に立ち、
M203F の付値 ≥ 1 を**厳密付値 v(ι(λₙ)) = p へ向けて構造的に鋭化**する。

issue #36（B-1 残件）の「遷移像の厳密付値」の斜片を、**遷移像の
二項分解 f_π(λ_{n+1}) = 線形項 π_{n+1}λ_{n+1} + 冪項 λ_{n+1}^p の
各項の付値を切り出し、厳密付値問題を線形項（＝ π_{n+1} の付値）へ
一意に還元する**形で解消する（分岐指数 e=p の実現に必要な
唯一の入力を明示的に隔離）。

  * M211F-1 `ringF_pow_term_deep` — 一般環の補題: f_π(λ) の冪項
    λ^p は (λ²) に属する（付値 ≥ 2、2 ≤ p、M151F-4b lam_pow_val_le）
  * M211F-2 `ringF_lin_term_val` — 一般環の補題: 線形項 π·λ は
    (λ) に属する（付値 ≥ 1、M161-2 isValAtLeast_mul: π ∈ (λ^0)・
    λ ∈ (λ^1)）
  * M211F-3 **`ringF_val_ge_two_iff_lin`（還元・本丸）** — f_π(λ) ∈ (λ²)
    ⇔ 線形項 π·λ ∈ (λ²)。冪項 λ^p が (λ²) に属す（M211F-1）ので、
    和の (λ²)-所属は線形項の (λ²)-所属と同値（M164 の加法/反元閉性で
    差 λ^p を打ち消す）。**厳密付値の第 2 段は線形項へ一意に還元**
  * M211F-4 `ringF_val_ge_two_of_pi` — 条件付き鋭化: π ∈ (λ) なら
    f_π(λ) ∈ (λ²)（付値 ≥ 2）。M211F-3 の ⇐ 側に π·λ ∈ (λ²)
    （isValAtLeast_mul）を食わせる。**分岐入力 π ∈ (λ) を仮定すれば
    M203F の付値 ≥ 1 が付値 ≥ 2 に上がる**
  * M211F-5 `towerGen_transition_pow_term_val_exact` — 塔遷移像の
    冪項の**厳密付値**: v(λ_{n+1}^p) = p（λ_{n+1}^p ∈ (λ_{n+1}^k) ⇔
    k ≤ p、M151F-7b tower_lam_val_exact の j=p 版）。**遷移像の
    支配項の付値をちょうど p に確定**
  * M211F-6 `towerGen_transition_val_ge_two_iff` /
    `towerGen_transition_val_ge_two_of_pi` — 塔遷移への持ち上げ:
    ι(λₙ) ∈ (λ_{n+1}²) ⇔ π_{n+1}λ_{n+1} ∈ (λ_{n+1}²)、および
    π_{n+1} ∈ (λ_{n+1}) からの条件付き付値 ≥ 2
  * M211F-7 `LambdaTowerExactValData` / `lambdaTowerExactValData` /
    `lambdaTowerExactVal_exists` — 総括レコードと witness・存在

意義: M203F は遷移像 ι(λₙ) が上位の極大イデアルに属する（付値 ≥ 1）
ことを与えたが、厳密付値（付値 = 何段か）は開いていた。本層は遷移像を
支配する**冪項 λ_{n+1}^p の付値をちょうど p に確定**し、和の (λ²)-所属を
**線形項 π_{n+1}λ_{n+1} の (λ²)-所属へ一意に還元**する。数論的には
分岐指数 e=p の全対称拡大では λ_{n+1}^p の付値 p が支配し、
線形項 π_{n+1}λ_{n+1} は付値 v(π_{n+1})+1 で（v(π_{n+1}) ≥ p−1 ゆえ）
真に深いので v(ι(λₙ)) = p となる。本層はこの厳密付値の**構造**
（冪項が支配・厳密還元）を choice なしで切り出す。

正直な限定: 本層 Slice B が閉じるのは **遷移像の二項分解の各項付値
（冪項の厳密付値 = p・線形項の付値 ≥ 1）と、付値 ≥ 2 の線形項への
一意還元、および π ∈ (λ) を仮定した条件付き付値 ≥ 2** の斜片のみ。
厳密付値 v(ι(λₙ)) = p の無条件確定には上位レベルの π_{n+1} の付値
（v(π_{n+1}) = p·v(π_n) ≥ p−1 の分岐帰納 = 分岐指数 e=p の実現）
という**塔の分岐理論**が要り、これが本層の還元で隔離した唯一の
未形式入力（π_{n+1} ∈ (λ_{n+1})）である。上位レベルの塔版
λ^{p−1} = −π 型関係式（基底 M82F-5c eis_lambda_pow の O_n 版）と
一般 [c]-倍作用・剰余体拡大の完全構造は次層（issue #36 の残余）。
全て選択公理不使用（M203F/M161/M164 から propext, Quot.sound を継承、
新規 Classical.choice なし）。サブエージェント並行部品。
-/
import IUT.LambdaTowerTrans
import IUT.LambdaValuationMul
import IUT.LambdaIdeal

namespace IUT

/-! ## M211F-1: 冪項は (λ²) に属する（一般環、2 ≤ p） -/

/-- **定理 (M211F-1): f_π(λ) の冪項 λ^p ∈ (λ²)**（付値 ≥ 2、2 ≤ p）。
    λ^p = λ^{p−2}·λ²（M151F-4b lam_pow_val_le の k=2）。遷移像の
    支配項が極大イデアルの 2 乗に沈むことを与える糊。 -/
theorem ringF_pow_term_deep (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (lam : R.carrier) :
    IsValAtLeast R lam (rpow R lam p) 2 :=
  lam_pow_val_le p 2 hp

/-! ## M211F-2: 線形項は (λ) に属する（一般環） -/

/-- **定理 (M211F-2): f_π(λ) の線形項 π·λ ∈ (λ)**（付値 ≥ 1）。
    π ∈ (λ^0) = R（M151F-2）・λ ∈ (λ^1)（M151F-4a）を M161-2
    isValAtLeast_mul に食わせ π·λ ∈ (λ^{0+1}) = (λ)。 -/
theorem ringF_lin_term_val (R : CRing) (pi lam : R.carrier) :
    IsValAtLeast R lam (R.mul pi lam) 1 := by
  have hpi : IsValAtLeast R lam pi 0 := isValAtLeast_zero R lam pi
  have hlam : IsValAtLeast R lam lam 1 := by
    have h := lam_pow_self_val R lam 1
    rw [rpow_one] at h
    exact h
  exact isValAtLeast_mul hpi hlam

/-! ## M211F-3: 還元（本丸）— f_π(λ) ∈ (λ²) ⇔ 線形項 ∈ (λ²) -/

/-- **定理 (M211F-3, 本丸): 厳密付値の線形項への還元** —
    f_π(λ) = π·λ + λ^p が (λ²) に属する ⇔ 線形項 π·λ が (λ²) に属する。
    冪項 λ^p は無条件で (λ²) に属す（M211F-1）ので、和の (λ²)-所属は
    線形項の (λ²)-所属で完全に決まる（→ は差 (f_π(λ)) − λ^p = π·λ を
    M164 の加法/反元閉性で、← は M164 の加法閉性で）。
    **v(ι(λₙ)) ≥ 2 か否かは線形項 π·λ の付値、すなわち π の付値に
    一意に還元される**。 -/
theorem ringF_val_ge_two_iff_lin (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (pi lam : R.carrier) :
    IsValAtLeast R lam (ringF p R pi lam) 2
      ↔ IsValAtLeast R lam (R.mul pi lam) 2 := by
  have hB : IsValAtLeast R lam (rpow R lam p) 2 := ringF_pow_term_deep p hp R lam
  constructor
  · intro h
    -- f_π(λ) は defeq で π·λ + λ^p、差 (…) + (−λ^p) = π·λ
    have h0 : IsValAtLeast R lam
        (R.add (R.mul pi lam) (rpow R lam p)) 2 := h
    have h' : IsValAtLeast R lam
        (R.add (R.add (R.mul pi lam) (rpow R lam p)) (R.neg (rpow R lam p))) 2 :=
      isValAtLeast_add h0 (isValAtLeast_neg hB)
    have e : R.add (R.add (R.mul pi lam) (rpow R lam p)) (R.neg (rpow R lam p))
        = R.mul pi lam := by
      rw [R.add_assoc (R.mul pi lam) (rpow R lam p) (R.neg (rpow R lam p)),
        CRing.add_neg R (rpow R lam p), CRing.add_zero R (R.mul pi lam)]
    rw [e] at h'
    exact h'
  · intro h
    exact isValAtLeast_add h hB

/-! ## M211F-4: 条件付き鋭化 — π ∈ (λ) ⟹ f_π(λ) ∈ (λ²) -/

/-- **定理 (M211F-4): 条件付き付値 ≥ 2** — π が (λ) に属する
    （＝ π ∈ 極大イデアル）なら f_π(λ) ∈ (λ²)。M211F-3 の ⇐ 側に
    π·λ ∈ (λ^{1+1}) = (λ²)（π ∈ (λ^1)・λ ∈ (λ^1) の M161-2）を
    食わせる。**分岐入力 π ∈ (λ) を仮定すれば M203F の付値 ≥ 1 が
    付値 ≥ 2 へ上がる**（厳密付値問題の唯一の未形式入力を隔離）。 -/
theorem ringF_val_ge_two_of_pi (p : Nat) (hp : 2 ≤ p) (R : CRing)
    (pi lam : R.carrier) (hpi : IsValAtLeast R lam pi 1) :
    IsValAtLeast R lam (ringF p R pi lam) 2 := by
  have hlam : IsValAtLeast R lam lam 1 := by
    have h := lam_pow_self_val R lam 1
    rw [rpow_one] at h
    exact h
  have hmul : IsValAtLeast R lam (R.mul pi lam) 2 := isValAtLeast_mul hpi hlam
  exact (ringF_val_ge_two_iff_lin p hp R pi lam).mpr hmul

/-! ## M211F-5: 塔遷移像の冪項の厳密付値 v(λ_{n+1}^p) = p -/

/-- **定理 (M211F-5): 遷移像の冪項の厳密付値** — 遷移像
    ι(λₙ) = π_{n+1}λ_{n+1} + λ_{n+1}^p の冪項 λ_{n+1}^p は
    λ_{n+1}^p ∈ (λ_{n+1}^k) ⇔ k ≤ p、すなわち **v(λ_{n+1}^p) = p が
    井戸定義**（M151F-7b tower_lam_val_exact の j=p 版）。遷移像を
    支配する冪項の付値をちょうど p に確定する。 -/
theorem towerGen_transition_pow_term_val_exact (p : Nat) (hp : 2 ≤ p)
    (n k : Nat) :
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      (rpow (towerLevel p (n + 1)).ring (towerGen p (n + 1)) p) k
      ↔ k ≤ p :=
  tower_lam_val_exact p hp (n + 1) p k

/-! ## M211F-6: 塔遷移への持ち上げ -/

/-- **定理 (M211F-6a): 塔遷移像の (λ²)-所属の線形項への還元** —
    ι(λₙ) = (towerHom p n)(λₙ) ∈ (λ_{n+1}²) ⇔ 線形項
    π_{n+1}λ_{n+1} ∈ (λ_{n+1}²)。M203F-2 towerGen_transition で遷移像を
    f_π(λ_{n+1}) に開き、M211F-3 の塔インスタンス。 -/
theorem towerGen_transition_val_ge_two_iff (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
        ((towerHom p n).map (towerGen p n)) 2
      ↔ IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
        ((towerLevel p (n + 1)).ring.mul (towerLevel p (n + 1)).pi
          (towerGen p (n + 1))) 2 := by
  rw [towerGen_transition p n]
  exact ringF_val_ge_two_iff_lin p hp (towerLevel p (n + 1)).ring
    (towerLevel p (n + 1)).pi (towerGen p (n + 1))

/-- **定理 (M211F-6b): 塔遷移像の条件付き付値 ≥ 2** —
    π_{n+1} ∈ (λ_{n+1})（上位レベルの π が極大イデアルに属する・
    分岐入力）なら遷移像 ι(λₙ) ∈ (λ_{n+1}²)。M203F の付値 ≥ 1 の
    塔版鋭化（M211F-4 の塔インスタンス）。 -/
theorem towerGen_transition_val_ge_two_of_pi (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (hpi : IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      (towerLevel p (n + 1)).pi 1) :
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerHom p n).map (towerGen p n)) 2 := by
  rw [towerGen_transition p n]
  exact ringF_val_ge_two_of_pi p hp (towerLevel p (n + 1)).ring
    (towerLevel p (n + 1)).pi (towerGen p (n + 1)) hpi

/-! ## M211F-7: 総括 -/

/-- **M211F-7a: 総括** — 塔遷移 ι(λₙ) の厳密付値へ向けた構造データ:
    冪項の厳密付値（v(λ_{n+1}^p) = p）・冪項の深さ（∈ (λ²)）・
    線形項の付値（∈ (λ)）・(λ²)-所属の線形項への還元・π ∈ (λ) からの
    条件付き付値 ≥ 2。 -/
structure LambdaTowerExactValData (p : Nat) (hp : 2 ≤ p) where
  /-- 塔の生成元 λₙ := (towerLevel p n).lam。 -/
  gen : ∀ n, (towerLevel p n).ring.carrier
  /-- 遷移像の冪項の厳密付値: λ_{n+1}^p ∈ (λ_{n+1}^k) ⇔ k ≤ p。 -/
  pow_term_val_exact : ∀ n k,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      (rpow (towerLevel p (n + 1)).ring (gen (n + 1)) p) k ↔ k ≤ p
  /-- 遷移像の冪項の深さ: λ_{n+1}^p ∈ (λ_{n+1}²)。 -/
  pow_term_deep : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      (rpow (towerLevel p (n + 1)).ring (gen (n + 1)) p) 2
  /-- 遷移像の線形項の付値: π_{n+1}λ_{n+1} ∈ (λ_{n+1})。 -/
  lin_term_val : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      ((towerLevel p (n + 1)).ring.mul (towerLevel p (n + 1)).pi
        (gen (n + 1))) 1
  /-- (λ²)-所属の還元: ι(λₙ) ∈ (λ_{n+1}²) ⇔ 線形項 ∈ (λ_{n+1}²)。 -/
  val_ge_two_iff : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
        ((towerHom p n).map (gen n)) 2
      ↔ IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
        ((towerLevel p (n + 1)).ring.mul (towerLevel p (n + 1)).pi
          (gen (n + 1))) 2
  /-- 条件付き付値 ≥ 2: π_{n+1} ∈ (λ_{n+1}) なら ι(λₙ) ∈ (λ_{n+1}²)。 -/
  val_ge_two_of_pi : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
        (towerLevel p (n + 1)).pi 1 →
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      ((towerHom p n).map (gen n)) 2

/-- **M211F-7b: witness** — towerGen が厳密付値データを成す
    （純レコード、選択公理不使用）。 -/
def lambdaTowerExactValData (p : Nat) (hp : 2 ≤ p) :
    LambdaTowerExactValData p hp where
  gen := towerGen p
  pow_term_val_exact := towerGen_transition_pow_term_val_exact p hp
  pow_term_deep := fun n => ringF_pow_term_deep p hp
    (towerLevel p (n + 1)).ring (towerGen p (n + 1))
  lin_term_val := fun n => ringF_lin_term_val
    (towerLevel p (n + 1)).ring (towerLevel p (n + 1)).pi (towerGen p (n + 1))
  val_ge_two_iff := towerGen_transition_val_ge_two_iff p hp
  val_ge_two_of_pi := towerGen_transition_val_ge_two_of_pi p hp

/-- **M211F-7c: 存在定理（ヘッドライン）** — Λₙ 塔の遷移像 ι(λₙ) の
    厳密付値は、支配する冪項 λ_{n+1}^p の付値ちょうど p と、線形項
    π_{n+1}λ_{n+1} への一意還元で構造的に決まる（無条件付値 ≥ 1 の
    鋭化・厳密付値の未形式入力 π ∈ (λ) の隔離）。柱B B-1 の一歩。 -/
theorem lambdaTowerExactVal_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaTowerExactValData p hp) :=
  ⟨lambdaTowerExactValData p hp⟩

end IUT
