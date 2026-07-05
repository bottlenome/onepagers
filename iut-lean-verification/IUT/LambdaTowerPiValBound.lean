/-
# M235F: 塔の π の付値下界の無条件化と ι(λₙ) の exact 付値の無条件化
        （柱B B-1・M226F 仮定の discharge）

M222F `IUT/LambdaTowerRamif.lean` と M226F `IUT/LambdaTowerExactRamif.lean`
の直上に立つ。

背景（M226F の正直な限定）:
  * M226F は遷移像 ι(λₙ) = (towerHom p n)(λₙ) の **exact 付値 v(ι(λₙ)) = p**
    を確立したが、それは分岐入力 **v(π_{n+1}) ≥ p を明示仮定**した
    条件付き定理だった（M226F-6 `towerGen_transition_val_exact_of_pi`）。
  * M222F が無条件に確立していたのは v(π_n) ≥ 1（π_n ∈ (λ_n)、M222F-1）と、
    遷移像の付値 ≥ 2（ι(λₙ) ∈ (λ_{n+1}²)、M222F-3
    `towerGen_transition_val_ge_two`）まで。両者の間には gap があった。

本層はこの gap を、**遷移射 towerHom の付値倍化**という構造だけから
**無条件に**埋める。鍵は M222F-3 が無条件に与える
「ι(λ_n) ∈ (λ_{n+1}²)（付値 ≥ 2）」である。すなわち:

  * **付値倍化（本丸）**: レベル n の元 a が付値 ≥ k（a ∈ (λ_n^k)）なら、
    その遷移像 ι(a) は付値 ≥ 2k（ι(a) ∈ (λ_{n+1}^{2k})）。
    証明: a = w·λ_n^k を ι で運び ι(a) = ι(w)·ι(λ_n)^k、そして
    ι(λ_n) ∈ (λ_{n+1}²)（M222F-3）を M164-4 `isValAtLeast_pow` で
    k 乗し ι(λ_n)^k ∈ (λ_{n+1}^{k·2})、ι(w) ∈ (λ_{n+1}^0) と
    M161-2 `isValAtLeast_mul` で積へ。

  * **π の付値下界の無条件化**: π_{n+1} = ι(π_n) なので、付値倍化を
    基点 v(π_0) ≥ p−1（M222F-2 の基底 Eisenstein 分岐）から回すと
    v(π_1) ≥ 2(p−1) ≥ p、以降 v(π_{n+1}) ≥ 2·v(π_n) ≥ p（n の帰納）。
    すなわち **∀ n, v(π_{n+1}) ≥ p を無条件に**確立する（p ≥ 2 で
    2(p−1) ≥ p が効く）。

  * **ι(λₙ) の exact 付値の無条件化（ヘッドライン）**: 上の無条件下界を
    M226F-6 `towerGen_transition_val_exact_of_pi` の分岐入力へ食わせ、
    **v(ι(λₙ)) = p の完全等号を仮定なしで**得る。M226F が明示仮定として
    切り出していた v(π_{n+1}) ≥ p が本層で discharge され、**分岐指数
    e = p の実現（遷移像 ι(λₙ) がちょうど p 段目に沈む）が全レベル・
    全 p で無条件に閉じる**。

内容:
  * M235F-1 `tower_pi_doubling` — **付値倍化（本丸）**: a ∈ (λ_n^k) なら
    ι(a) ∈ (λ_{n+1}^{k·2})。遷移射が付値を倍化する（ι(λ_n) ∈ (λ_{n+1}²)
    に由来）。
  * M235F-2 `tower_pi_val_ge_p` — **π の付値下界の無条件化**:
    ∀ n, v(π_{n+1}) ≥ p（π_{n+1} ∈ (λ_{n+1}^p)）を仮定なしで。
  * M235F-3 `towerGen_transition_val_exact_uncond` — **ι(λₙ) の exact 付値
    の無条件化（ヘッドライン）**: ∀ n k, ι(λₙ) ∈ (λ_{n+1}^k) ⇔ k ≤ p、
    すなわち **v(ι(λₙ)) = p を仮定なしで**（M226F-6 の仮定 discharge）。
  * M235F-4 `LambdaTowerPiValBoundData` / `lambdaTowerPiValBoundData` /
    `lambdaTowerPiValBound_exists` — 総括レコードと witness・存在。

意義: M226F は ι(λₙ) の exact 付値を「v(π_{n+1}) ≥ p」という未形式の
分岐入力に依存させていたが、本層はその入力を **遷移射 towerHom の
付値倍化（M222F-3 の無条件な ι(λ_n) ∈ (λ_{n+1}²) に由来）** から
基点 v(π_0) ≥ p−1 を回すだけで無条件に供給する。これにより M226F-6 の
条件が discharge され、**遷移像 ι(λₙ) の exact 付値 = p（分岐指数
e = p の実現の一片）が全レベル・全 p で仮定なしに成り立つ**。

正直な限定:
  * 本層が無条件に閉じるのは **π_{n+1} の付値の下界 v(π_{n+1}) ≥ p**
    と、それが discharge する **遷移像 ι(λₙ) の exact 付値 = p** まで。
    ι(λₙ) の exact 付値の等号は付値の**下界** v(π_{n+1}) ≥ p のみで
    発火する（支配項分離: 線形項 π·λ は v ≥ p+1 で冪項 λ^p（v = p）より
    真に深い、M226F の論法）ため、下界の無条件供給で十分である。
  * 依然として未達なのは π_{n+1} の付値の**正確な値**（分岐帰納
    v(π_{n+1}) = p·v(π_n) の完全な等式・π の付値そのものの exact 値）。
    本層の倍化は v(π_{n+1}) ≥ 2·v(π_n) の**下界**（実際は
    v(π_{n+1}) ≥ 2^{n+1}(p−1)）であり、上界（等号）は与えない。塔版
    Eisenstein 関係式が本塔で成立しないため、π の付値の exact 値は
    剰余体拡大次数 f と分岐指数 e の ef=[L:K] 簿記を要し次層に残る
    （M222F/M226F の正直申告と整合）。
  * 基点 n=0 の v(π_0) = p−1（分岐指数 e = p−1）は M222F-2 が正確に
    確定する別枝であり、本層の一般構造（上位レベルの e = p の遷移像）
    とは指数が異なる。

全て選択公理不使用（M226F/M222F/M164/M161/PSFunctor から propext,
Quot.sound を継承、新規 Classical.choice なし）。サブエージェント並行
部品（tier M）。
-/
import IUT.LambdaTowerExactRamif
import IUT.LambdaIdeal
import IUT.PSFunctor

namespace IUT

/-! ## M235F-1: 付値倍化（本丸）— 遷移射は付値を倍化する -/

/-- **定理 (M235F-1, 本丸): 遷移射の付値倍化** — レベル n の元 a が
    付値 ≥ k（a ∈ (λ_n^k)）なら、遷移像 ι(a) = (towerHom p n)(a) は
    付値 ≥ 2k（ι(a) ∈ (λ_{n+1}^{k·2})）。
    a = w·λ_n^k を ι で運び ι(a) = ι(w)·ι(λ_n)^k（`ringHom_rpow`）、
    ι(λ_n) ∈ (λ_{n+1}²)（M222F-3 `towerGen_transition_val_ge_two`）を
    M164-4 `isValAtLeast_pow` で k 乗して ι(λ_n)^k ∈ (λ_{n+1}^{k·2})、
    ι(w) ∈ (λ_{n+1}^0)（M151F-2）と M161-2 `isValAtLeast_mul` で積へ。
    遷移射が付値を **2 倍する**構造（ι(λ_n) ∈ (λ_{n+1}²) に由来）。 -/
theorem tower_pi_doubling (p : Nat) (hp : 2 ≤ p) (n : Nat)
    {a : (towerLevel p n).ring.carrier} {k : Nat}
    (ha : IsValAtLeast (towerLevel p n).ring (towerGen p n) a k) :
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerHom p n).map a) (k * 2) := by
  obtain ⟨w, hw⟩ := ha
  -- ι(a) = ι(w)·ι(λ_n)^k
  have hmap : (towerHom p n).map a
      = (towerLevel p (n + 1)).ring.mul ((towerHom p n).map w)
          (rpow (towerLevel p (n + 1)).ring
            ((towerHom p n).map (towerGen p n)) k) := by
    rw [hw, (towerHom p n).map_mul,
      ringHom_rpow (towerHom p n) (towerGen p n) k]
  rw [hmap]
  -- ι(λ_n)^k ∈ (λ_{n+1}^{k·2})（M222F-3 を M164-4 で k 乗）
  have hpow : IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      (rpow (towerLevel p (n + 1)).ring
        ((towerHom p n).map (towerGen p n)) k) (k * 2) :=
    isValAtLeast_pow (towerGen_transition_val_ge_two p hp n) k
  -- ι(w) ∈ (λ_{n+1}^0)
  have hz : IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerHom p n).map w) 0 :=
    isValAtLeast_zero (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerHom p n).map w)
  -- 積: 0 + k·2 = k·2
  have hmul := isValAtLeast_mul hz hpow
  rw [Nat.zero_add] at hmul
  exact hmul

/-! ## M235F-2: π の付値下界の無条件化 — v(π_{n+1}) ≥ p -/

/-- **定理 (M235F-2): π の付値下界の無条件化** — ∀ n, 上位レベルの π、
    すなわち π_{n+1} = (towerLevel p (n+1)).pi は付値 ≥ p
    （π_{n+1} ∈ (λ_{n+1}^p)）、**仮定なしで**。
    π_{n+1} = ι(π_n) と付値倍化（M235F-1）を基点 v(π_0) ≥ p−1
    （M222F-2 の基底 Eisenstein 分岐）から回す:
    基底 v(π_1) ≥ 2(p−1) ≥ p（p ≥ 2）、帰納段 v(π_{n+2}) ≥ 2·p ≥ p。
    M226F が明示仮定として切り出していた分岐入力 v(π_{n+1}) ≥ p の
    無条件確立。 -/
theorem tower_pi_val_ge_p (p : Nat) (hp : 2 ≤ p) : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      (towerLevel p (n + 1)).pi p := by
  intro n
  induction n with
  | zero =>
    -- v(π_0) ≥ p−1、倍化で v(π_1) ≥ (p−1)·2 ≥ p
    have h0 : IsValAtLeast (towerLevel p 0).ring (towerGen p 0)
        (towerLevel p 0).pi (p - 1) := by
      show IsValAtLeast (eisRing p) (eisLambda p)
        ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) (p - 1)
      exact (base_pi_val_exact p hp (p - 1)).mpr (Nat.le_refl (p - 1))
    have hd := tower_pi_doubling p hp 0 h0
    exact isValAtLeast_mono (towerLevel p 1).ring (towerGen p 1)
      (towerLevel p 1).pi ((p - 1) * 2) p (by omega) hd
  | succ n ih =>
    -- v(π_{n+1}) ≥ p、倍化で v(π_{n+2}) ≥ p·2 ≥ p
    have hd := tower_pi_doubling p hp (n + 1) ih
    exact isValAtLeast_mono (towerLevel p (n + 2)).ring (towerGen p (n + 2))
      (towerLevel p (n + 2)).pi (p * 2) p (by omega) hd

/-! ## M235F-3: ι(λₙ) の exact 付値の無条件化（ヘッドライン） -/

/-- **定理 (M235F-3, ヘッドライン): 遷移像の exact 付値の無条件化** —
    ∀ n k, 遷移像 ι(λₙ) = (towerHom p n)(λₙ) は
    ι(λₙ) ∈ (λ_{n+1}^k) ⇔ k ≤ p、すなわち **v(ι(λₙ)) = p を仮定なしで**。
    M226F-6 `towerGen_transition_val_exact_of_pi`（条件付き）の分岐入力
    v(π_{n+1}) ≥ p を M235F-2 `tower_pi_val_ge_p`（無条件）で discharge。
    **M226F が明示仮定として残していた分岐入力を除去し、分岐指数
    e = p の実現（遷移像がちょうど p 段目に沈む）を全レベル・全 p で
    無条件に閉じる**。 -/
theorem towerGen_transition_val_exact_uncond (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (k : Nat) :
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
        ((towerHom p n).map (towerGen p n)) k
      ↔ k ≤ p :=
  towerGen_transition_val_exact_of_pi p hp n (tower_pi_val_ge_p p hp n) k

/-! ## M235F-4: 総括 -/

/-- **M235F-4a: 総括** — 塔の π の付値下界の無条件化データ:
    遷移射の付値倍化・π の付値下界の無条件化・ι(λₙ) の exact 付値の
    無条件化。 -/
structure LambdaTowerPiValBoundData (p : Nat) (hp : 2 ≤ p) where
  /-- 塔の生成元 λₙ := (towerLevel p n).lam。 -/
  gen : ∀ n, (towerLevel p n).ring.carrier
  /-- 遷移射の付値倍化: a ∈ (λ_n^k) なら ι(a) ∈ (λ_{n+1}^{k·2})。 -/
  doubling : ∀ (n : Nat) (a : (towerLevel p n).ring.carrier) (k : Nat),
    IsValAtLeast (towerLevel p n).ring (gen n) a k →
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      ((towerHom p n).map a) (k * 2)
  /-- π の付値下界の無条件化: v(π_{n+1}) ≥ p（全 n・仮定なし）。 -/
  pi_val_ge_p : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      (towerLevel p (n + 1)).pi p
  /-- ι(λₙ) の exact 付値の無条件化: ι(λₙ) ∈ (λ_{n+1}^k) ⇔ k ≤ p
      （v(ι(λₙ)) = p・仮定なし）。 -/
  transition_val_exact : ∀ n k,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
        ((towerHom p n).map (gen n)) k
      ↔ k ≤ p

/-- **M235F-4b: witness** — towerGen が無条件下界データを成す
    （純レコード、選択公理不使用）。 -/
def lambdaTowerPiValBoundData (p : Nat) (hp : 2 ≤ p) :
    LambdaTowerPiValBoundData p hp where
  gen := towerGen p
  doubling := fun n _ _ ha => tower_pi_doubling p hp n ha
  pi_val_ge_p := tower_pi_val_ge_p p hp
  transition_val_exact := fun n k =>
    towerGen_transition_val_exact_uncond p hp n k

/-- **M235F-4c: 存在定理（ヘッドライン）** — Λₙ 塔の遷移像 ι(λₙ) は、
    **仮定なしで** exact 付値 v(ι(λₙ)) = p を持つ。遷移射 towerHom の
    付値倍化（ι(λ_n) ∈ (λ_{n+1}²) に由来）を基点 v(π_0) ≥ p−1 から
    回すことで分岐入力 v(π_{n+1}) ≥ p を無条件に供給し、M226F-6 の
    仮定を discharge する。柱B B-1（塔の分岐指数 e = p の実現）の一段。 -/
theorem lambdaTowerPiValBound_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaTowerPiValBoundData p hp) :=
  ⟨lambdaTowerPiValBoundData p hp⟩

end IUT
