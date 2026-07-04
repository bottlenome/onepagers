/-
# M199F: 柱C 幾何級数収束プログラムの総括 capstone — 残差収束・極限対象・
自己完結・rlim 完備化 + 除算代数（柱C・並行部品）

M178（`GeometricSeriesProgramData`）が束ねた M163〜M177（幾何級数の
代数：閉形式・漸化式・冪法則・絶対値・逆元近似）の**続き**として、
M182〜M185F の収束層（残差収束 → 極限対象 → 自己完結 → rlim 位相的
完備化）と、M162 の除算代数（逆元の一意性・congruence・積の逆元）を
**単一のレコード `ConvergenceProgramData` に束ねて一括 certification**
する。witness は全て既存定理名のみ——**新規証明ゼロ**（§7.5 の
capstone 束ね）。`#print axioms convergenceProgram_exists` が全鎖の
choice-free 性を一度に確認する。

収録する 8 の柱石:

  1. `geom_inverse_converges`（M182） — 残差収束:
     |r| ≤ N/(N+1) ∧ 1 ≤ N ∧ N·m ≤ k ⟹ |(1⊖r)·s_k ⊖ 1| ≤ 1/(m+1)
  2. `geom_sub_limit`（M183-1） — 極限対象との差の閉形式:
     (1⊖r)·L ≈ 1 ⟹ s_k ⊖ L ≈ ⊖(L·r^k)
  3. `rabs_geom_sub_limit`（M183-2） — 差の絶対値:
     |s_k ⊖ L| ≈ |L|·|r|^k
  4. `geom_converges_to_limit`（M183-4） — 極限対象への収束（B は
     |L| の有理上界を仮説として要求）:
     (1⊖r)·L ≈ 1 ∧ |r| ≤ N/(N+1) ∧ |L| ≤ B ∧ N·(B(m+1)+m) ≤ k ⟹
     |s_k ⊖ L| ≤ 1/(m+1)
  5. `geom_limit_object`（M183-5） — 極限対象の存在:
     IsPos |1⊖r| ⟹ ∃ L, (1⊖r)·L ≈ 1 ∧ ∀k, s_k ⊖ L ≈ ⊖(L·r^k)
  6. `geom_converges_self_contained`（M184-4） — 自己完結な収束
     （離隔性・|L| の上界の二仮説を |r| ≤ N/(N+1) から自前で導出）:
     |r| ≤ N/(N+1) ∧ 1 ≤ N ⟹
     ∃ L, (1⊖r)·L ≈ 1 ∧ ∀ m k, N·((N+1)(m+1)+m) ≤ k ⟹ |s_k ⊖ L| ≤ 1/(m+1)
  7. `geom_rlim_complete`（M185F-5） — rlim 位相的完備化:
     |r| ≤ N/(N+1) ∧ 1 ≤ N ⟹
     ∃ L, (1⊖r)·L ≈ 1 ∧ rlim (geomRlimSeq r N) ≈ L
  8. 除算代数（M162） `rinv_unique` / `rinv_congr` / `rmul_inv_mul` —
     逆元の一意性・congruence・積の逆元

意義: M178 が閉じた幾何級数の**代数**（有限 k での恒等式・不等式）に
対し、本 capstone は M182〜M185F が積み上げた**収束**の全層
（実効的残差収束 → 極限対象の言葉での収束 → 二仮説を自前で消した
自己完結版 → 対角極限 rlim との位相的一致）と、M162 の**除算代数**
（逆元の一意性・congruence・積の逆元）を一つのレコードに束ねる。
これにより「第101弾 幾何級数収束プログラム（残差→極限対象→自己完結
→rlim 完備化）+ 除算代数」が単一の certification として choice-free に
確定する。M178 の後継（continuation）であり、M178 の内容自体は
再収録しない。

正直な限定: 本 capstone は M182・M183-1/2/4/5・M184-4・M185F-5・M162
の 8 定理をそのまま束ねたものであり、新規の合成・弱化は行っていない
（`geom_converges_to_limit` は |L| の有理上界 B と離隔性を仮説として
要求する版のまま収録し、その二仮説の解消は `self_contained` フィールド
（M184-4）に別途収録した）。除算代数は逆元「関係」（x·y ≈ 1）の代数則
であり、全域的な逆元関数の構成は対象外（M162 の限定を継承）。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.GeomRlimComplete
import IUT.RealDivision
import IUT.GeometricSeriesProgram

namespace IUT

/-! ## M199F-1: プログラム総括レコード -/

/-- **M199F-1: 幾何級数収束プログラム + 除算代数の総括** —
    M182（残差収束）・M183（極限対象）・M184（自己完結）・M185F（rlim
    完備化）・M162（除算代数）の 8 柱石を束ねる。M178 の続き。 -/
structure ConvergenceProgramData where
  /-- 残差収束（M182）: |r| ≤ N/(N+1) ∧ 1 ≤ N ∧ N·m ≤ k ⟹
      |(1⊖r)·s_k ⊖ 1| ≤ 1/(m+1)。 -/
  residual_converges : ∀ (r : RReal) (N m k : Nat),
    rLe (rabs r) (qToReal (qFrac N N)) → 1 ≤ N → N * m ≤ k →
    rLe (rabs (realAdd (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realGeomSum r k)) (realNeg (qToReal ratRing.one))))
      (qToReal (qFrac 1 m))
  /-- 極限対象との差の閉形式（M183-1）: (1⊖r)·L ≈ 1 ⟹
      s_k ⊖ L ≈ ⊖(L·r^k)。 -/
  limit_sub_closed : ∀ (r L : RReal) (k : Nat),
    realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one) →
    realEq (realAdd (realGeomSum r k) (realNeg L))
      (realNeg (rmul L (realPow r k)))
  /-- 差の絶対値（M183-2）: |s_k ⊖ L| ≈ |L|·|r|^k。 -/
  limit_sub_abs : ∀ (r L : RReal) (k : Nat),
    realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one) →
    realEq (rabs (realAdd (realGeomSum r k) (realNeg L)))
      (rmul (rabs L) (realPow (rabs r) k))
  /-- 極限対象への収束（M183-4）: (1⊖r)·L ≈ 1 ∧ |r| ≤ N/(N+1) ∧
      |L| ≤ B ∧ N·(B(m+1)+m) ≤ k ⟹ |s_k ⊖ L| ≤ 1/(m+1)。 -/
  converges_to_limit : ∀ (r L : RReal) (N B m k : Nat),
    realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one) →
    rLe (rabs r) (qToReal (qFrac N N)) → 1 ≤ N →
    rLe (rabs L) (qToReal (qFrac B 0)) →
    N * (B * (m + 1) + m) ≤ k →
    rLe (rabs (realAdd (realGeomSum r k) (realNeg L)))
      (qToReal (qFrac 1 m))
  /-- 極限対象の存在（M183-5）: IsPos |1⊖r| ⟹
      ∃ L, (1⊖r)·L ≈ 1 ∧ ∀k, s_k ⊖ L ≈ ⊖(L·r^k)。 -/
  limit_object : ∀ r : RReal,
    IsPos (rabs (realAdd (qToReal ratRing.one) (realNeg r))) →
    ∃ L : RReal,
      realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
        (qToReal ratRing.one) ∧
      ∀ k : Nat, realEq (realAdd (realGeomSum r k) (realNeg L))
        (realNeg (rmul L (realPow r k)))
  /-- 自己完結な収束（M184-4）: |r| ≤ N/(N+1) ∧ 1 ≤ N のみから
      ∃ L, (1⊖r)·L ≈ 1 ∧ 明示モジュラス付き収束。 -/
  self_contained : ∀ (r : RReal) (N : Nat),
    rLe (rabs r) (qToReal (qFrac N N)) → 1 ≤ N →
    ∃ L : RReal,
      realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
        (qToReal ratRing.one) ∧
      ∀ m k : Nat, N * ((N + 1) * (m + 1) + m) ≤ k →
        rLe (rabs (realAdd (realGeomSum r k) (realNeg L)))
          (qToReal (qFrac 1 m))
  /-- rlim 位相的完備化（M185F-5）: |r| ≤ N/(N+1) ∧ 1 ≤ N のみから、
      極限対象 L が存在して対角極限 rlim (geomRlimSeq r N) が L に
      realEq で一致する。 -/
  rlim_complete : ∀ (r : RReal) (N : Nat)
    (hb : rLe (rabs r) (qToReal (qFrac N N))) (hN : 1 ≤ N),
    ∃ L : RReal,
      realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
        (qToReal ratRing.one) ∧
      realEq (rlim (geomRlimSeq r N) (geom_seq_isCauchy r N hb hN)) L
  /-- 除算代数（M162-1）: 逆元の一意性。 -/
  inv_unique : ∀ {x y y' : RReal},
    realEq (rmul x y) (qToReal ratRing.one) →
    realEq (rmul x y') (qToReal ratRing.one) → realEq y y'
  /-- 除算代数（M162-2）: 逆元の congruence。 -/
  inv_congr : ∀ {x x' y : RReal}, realEq x x' →
    realEq (rmul x y) (qToReal ratRing.one) →
    realEq (rmul x' y) (qToReal ratRing.one)
  /-- 除算代数（M162-4）: 積の逆元。 -/
  inv_mul : ∀ {x y a b : RReal},
    realEq (rmul x a) (qToReal ratRing.one) →
    realEq (rmul y b) (qToReal ratRing.one) →
    realEq (rmul (rmul x y) (rmul a b)) (qToReal ratRing.one)

/-- **M199F-2: witness** — 全て既存定理名（新規証明ゼロ）。 -/
def convergenceProgramData : ConvergenceProgramData where
  residual_converges := geom_inverse_converges
  limit_sub_closed := geom_sub_limit
  limit_sub_abs := rabs_geom_sub_limit
  converges_to_limit := geom_converges_to_limit
  limit_object := geom_limit_object
  self_contained := geom_converges_self_contained
  rlim_complete := geom_rlim_complete
  inv_unique := fun h1 h2 => rinv_unique h1 h2
  inv_congr := fun hx h => rinv_congr hx h
  inv_mul := fun ha hb => rmul_inv_mul ha hb

/-- **M199F-3: 存在** — 幾何級数収束プログラム + 除算代数の
    一括 certification。 -/
theorem convergenceProgram_exists : Nonempty ConvergenceProgramData :=
  ⟨convergenceProgramData⟩

end IUT
