/-
# M182: 幾何級数の収束 — (1⊖r)·s_k → 1 の明示速度（柱C・収束の本丸）

第101弾の幾何級数プログラムの到達点。M177（逆元近似の誤差
(1⊖r)·s_k ⊖ 1 ≈ ⊖r^k、|誤差| = |r|^k）と M181（|r|^k の減衰 |r|^k → 0
の明示モジュラス）を合流させ、**公比の絶対値が 1 未満（|r| ≤ N/(N+1)）
なら幾何部分和 s_k は 1⊖r の逆元に収束する**——正確には残差
(1⊖r)·s_k ⊖ 1 の絶対値が k ≥ N·m で 1/(m+1) 以下に落ちる——ことを
choice なしで閉じる。

  * M182-1 **`geom_inverse_converges`（収束の本丸）** —
    |r| ≤ N/(N+1) ∧ 1 ≤ N ∧ N·m ≤ k ⟹
    |(1⊖r)·s_k ⊖ 1| ≤ 1/(m+1)
  * M182-2 `GeomConvergeData` — 総括

意義: これが幾何級数収束論の**到達点**。M162（逆元の一意性）と併せると、
s_k は「1⊖r の唯一の逆元 (1⊖r)⁻¹」に、残差 |(1⊖r)·s_k − 1| ≤ 1/(m+1)
（k ≥ N·m）という明示速度で収束する。証明は M177 の誤差の閉形式
（|残差| ≈ |r|^k）と M181 の減衰（|r|^k ≤ 1/(m+1)）を rLe で連鎖する
だけ——本丸の 2 段は M180（乗法単調性）・M179（Bernoulli）という
tier L の rate-bound 部品（Fable スポット）で支えられている。

構成: 環側（M176: 誤差 ∈ (λ^{km})）と実数側（本モジュール: |誤差| ≤
1/(m+1)）で、幾何級数による 1−r の逆元近似が**両面から定量的に**
閉じた。M31（局所類体論の単数 filtration）から実数解析（M165〜M181）
までの一連の橋が、この収束定理で束ねられる。

正直な限定: 本定理は「残差 → 0（明示速度）」= 構成的・実効的な収束の
表明である。極限 L 自体を対角極限 rlim（M128 完備性）で構成し
realEq (rmul (realAdd 1 (realNeg r)) L) 1 を閉じる**位相的完備化版**は、
s_k の IsCauchyReals 性（テール評価）を要し次層。実効版（残差評価）が
収束の数学的内容の核であり、極限対象の構成はその上の層。

全て選択公理不使用。
-/
import IUT.RealGeomInv
import IUT.RealGeomDecay

namespace IUT

/-! ## M182-1: 収束の本丸 -/

/-- **定理 (M182-1, 収束の本丸): 幾何級数の逆元収束** —
    |r| ≤ N/(N+1)（1 ≤ N）で N·m ≤ k なら、残差 (1⊖r)·s_k ⊖ 1 の
    絶対値は 1/(m+1) 以下。すなわち **(1⊖r)·s_k → 1**（= s_k → (1⊖r)⁻¹）
    が明示速度で成立。M177 誤差の閉形式 |(1⊖r)·s_k ⊖ 1| ≈ |r|^k と
    M181 減衰 |r|^k ≤ 1/(m+1) を rLe で連鎖。 -/
theorem geom_inverse_converges (r : RReal) (N m k : Nat)
    (hb : rLe (rabs r) (qToReal (qFrac N N))) (hN : 1 ≤ N) (hk : N * m ≤ k) :
    rLe (rabs (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realNeg (qToReal ratRing.one))))
      (qToReal (qFrac 1 m)) :=
  rLe_trans (rLe_of_realEq (rabs_geom_inv_error r k))
    (realPow_rabs_decay r N m k hb hN hk)

/-! ## M182-2: 総括 -/

/-- **M182-2a: 総括** — 幾何級数の収束データ。 -/
structure GeomConvergeData where
  /-- 逆元収束: 残差 |(1⊖r)·s_k ⊖ 1| ≤ 1/(m+1)（k ≥ N·m, |r| ≤ N/(N+1)）。 -/
  converges : ∀ (r : RReal) (N m k : Nat),
    rLe (rabs r) (qToReal (qFrac N N)) → 1 ≤ N → N * m ≤ k →
    rLe (rabs (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realNeg (qToReal ratRing.one))))
      (qToReal (qFrac 1 m))

/-- **M182-2b: witness**。 -/
def geomConvergeData : GeomConvergeData where
  converges := fun r N m k hb hN hk => geom_inverse_converges r N m k hb hN hk

/-- **M182-2c: 存在** — 幾何級数収束の certification。 -/
theorem geomConverge_exists : Nonempty GeomConvergeData := ⟨geomConvergeData⟩

end IUT
