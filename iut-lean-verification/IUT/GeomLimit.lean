/-
# M183: 幾何級数の極限対象 — s_k → (1⊖r)⁻¹ の構成的収束（柱C）

第101弾の幾何級数プログラムの完結編（極限対象の構成）。M182 は
残差 (1⊖r)·s_k ⊖ 1 → 0 という「実効版収束」を閉じたが、本モジュールは
**極限対象 L そのもの**（1⊖r の逆元、M153F apart_inv_exists で存在）に対し
s_k ⊖ L の閉形式と絶対値評価、そして明示モジュラス付きの収束
|s_k ⊖ L| ≤ 1/(m+1) を choice なしで閉じる。

  * M183-1 **`geom_sub_limit`（差の閉形式）** —
    (1⊖r)·L ≈ 1 なら s_k ⊖ L ≈ ⊖(L·r^k)
  * M183-2 **`rabs_geom_sub_limit`（差の絶対値）** —
    |s_k ⊖ L| ≈ |L|·|r|^k
  * M183-3 `qFrac_mul_le` — 有理係数の折込 B·(1/(P+1)) ≤ 1/(m+1)
  * M183-4 **`geom_converges_to_limit`（収束の完結）** —
    |r| ≤ N/(N+1) ∧ 1 ≤ N ∧ |L| ≤ B ∧ N·(B·(m+1)+m) ≤ k ⟹
    |s_k ⊖ L| ≤ 1/(m+1)
  * M183-5 `geom_limit_object` — 極限対象の存在（M153F と合成）:
    IsPos |1⊖r| なら ∃ L, (1⊖r)·L ≈ 1 ∧ ∀ k, s_k ⊖ L ≈ ⊖(L·r^k)
  * M183-6 `GeomLimitData` — 総括

意義: M182 の「(1⊖r)·s_k → 1」を極限対象の言葉に持ち上げ、
**s_k は L = (1⊖r)⁻¹ に明示速度 |s_k − L| = |L|·|r|^k ≤ 1/(m+1)
（k ≥ N·(B(m+1)+m)）で収束する**という、幾何級数収束論の最終形を得た。
差の閉形式（M183-1）は M177 の誤差 (1⊖r)·s_k ⊖ 1 ≈ ⊖r^k に L を掛けて
1 を消す純代数（M150 環法則 + M153F 負号引き出し）、収束（M183-4）は
M181 の減衰 |r|^k ≤ 1/(m'+1) と |L| の有理上界 B の折込で閉じる。

正直な限定: L は仮説として与える（(1⊖r)·L ≈ 1）。その存在は
IsPos |1⊖r|（|r| < 1 のとき成立）の下で M153F `apart_inv_exists` が
∃ 形で保証し、M183-5 で合成済み。∃ からの witness 抽出（choice）を
避けるため、定量的定理（M183-1/2/4）は L を明示引数に取る形とした。
また |L| の有理上界 B も仮説である（|r| ≤ N/(N+1) から B = N+1 級の
上界を導く定量化は逆元構成 M145 の witness 評価を要し次層）。
rlim（M128 完備性）による位相的構成（Path A）は s_k の
IsCauchyReals 性のテール評価を要し、本モジュールの範囲外。

全て選択公理不使用。
-/
import IUT.GeomConverge
import IUT.ApartInv
import IUT.RealRingLaws

namespace IUT

/-! ## M183-1: 差の閉形式 s_k ⊖ L ≈ ⊖(L·r^k) -/

/-- **定理 (M183-1, 本丸1): 差の閉形式** — (1⊖r)·L ≈ 1 なら
    s_k ⊖ L ≈ ⊖(L·r^k)。二段構え:
    (i) (1⊖r)·(s_k ⊖ L) ≈ (1⊖r)·s_k ⊕ (⊖((1⊖r)·L)) ≈ (1⊖r)·s_k ⊖ 1
        ≈ ⊖r^k（M150 分配 + M153F 負号 + hL + M177 誤差）。
    (ii) s_k ⊖ L ≈ 1·(s_k ⊖ L) ≈ (L·(1⊖r))·(s_k ⊖ L)
        ≈ L·((1⊖r)·(s_k ⊖ L)) ≈ L·(⊖r^k) ≈ ⊖(L·r^k)
        （単位元・可換・結合 + (i) + 負号引き出し）。 -/
theorem geom_sub_limit (r L : RReal) (k : Nat)
    (hL : realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one)) :
    realEq (realAdd (realGeomSum r k) (realNeg L))
      (realNeg (rmul L (realPow r k))) := by
  -- (i): E·D ≈ ⊖r^k（E := 1⊖r, D := s_k ⊖ L）
  have hED : realEq
      (rmul (realAdd (qToReal ratRing.one) (realNeg r))
        (realAdd (realGeomSum r k) (realNeg L)))
      (realNeg (realPow r k)) :=
    realEq_trans (rmul_add_left (realGeomSum r k) (realNeg L)
        (realAdd (qToReal ratRing.one) (realNeg r)))
      (realEq_trans (realAdd_congr_right
          (rmul (realAdd (qToReal ratRing.one) (realNeg r)) (realGeomSum r k))
          (rmul_neg_right (realAdd (qToReal ratRing.one) (realNeg r)) L))
        (realEq_trans (realAdd_congr_right
            (rmul (realAdd (qToReal ratRing.one) (realNeg r))
              (realGeomSum r k))
            (realNeg_congr hL))
          (real_geom_inv_error r k)))
  -- L·E ≈ 1（可換 + hL）
  have hLE : realEq
      (rmul L (realAdd (qToReal ratRing.one) (realNeg r)))
      (qToReal ratRing.one) :=
    realEq_trans (rmul_comm L (realAdd (qToReal ratRing.one) (realNeg r))) hL
  -- 1·D ≈ D（可換 + 右単位元）
  have hOneD : realEq
      (rmul (qToReal ratRing.one) (realAdd (realGeomSum r k) (realNeg L)))
      (realAdd (realGeomSum r k) (realNeg L)) :=
    realEq_trans (rmul_comm (qToReal ratRing.one)
        (realAdd (realGeomSum r k) (realNeg L)))
      (rmul_one (realAdd (realGeomSum r k) (realNeg L)))
  -- (ii): D ≈ 1·D ≈ (L·E)·D ≈ L·(E·D) ≈ L·(⊖r^k) ≈ ⊖(L·r^k)
  exact realEq_trans (realEq_symm hOneD)
    (realEq_trans (rmul_congr_left (realAdd (realGeomSum r k) (realNeg L))
        (realEq_symm hLE))
      (realEq_trans (rmul_assoc_real L
          (realAdd (qToReal ratRing.one) (realNeg r))
          (realAdd (realGeomSum r k) (realNeg L)))
        (realEq_trans (rmul_congr_right L hED)
          (rmul_neg_right L (realPow r k)))))

/-! ## M183-2: 差の絶対値 |s_k ⊖ L| ≈ |L|·|r|^k -/

/-- **定理 (M183-2, 本丸2): 差の絶対値** — (1⊖r)·L ≈ 1 なら
    |s_k ⊖ L| ≈ |L|·|r|^k。M183-1 の閉形式に
    |⊖x| ≈ |x|（M127F）・|xy| ≈ |x||y|（M127F）・|r^k| ≈ |r|^k（M169）
    を連鎖。|r|^k → 0（M181）ゆえ、これが **s_k → L** の内容。 -/
theorem rabs_geom_sub_limit (r L : RReal) (k : Nat)
    (hL : realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one)) :
    realEq (rabs (realAdd (realGeomSum r k) (realNeg L)))
      (rmul (rabs L) (realPow (rabs r) k)) :=
  realEq_trans (rabs_congr (geom_sub_limit r L k hL))
    (realEq_trans (rabs_neg (rmul L (realPow r k)))
      (realEq_trans (rabs_mul L (realPow r k))
        (rmul_congr_right (rabs L) (rabs_pow r k))))

/-! ## M183-3: 有理係数の折込 -/

/-- **補題 (M183-3): 有理係数の折込** — B·(m+1) ≤ P+1 なら
    (B/1)·(1/(P+1)) ≤ 1/(m+1)。M129F qFrac_mul で積を単一分数に畳み、
    M117F qFrac_le の線形判定（Int 昇格は M181-3 と同型の
    natCast 展開）で閉じる。 -/
theorem qFrac_mul_le (B m P : Nat) (hP : B * (m + 1) ≤ P + 1) :
    qLe (qMul (qFrac B 0) (qFrac 1 P)) (qFrac 1 m) := by
  rw [qFrac_mul]
  have e1 : B * 1 = B := by omega
  have e2 : (0 + 1) * (P + 1) - 1 = P := by omega
  rw [e1, e2]
  apply qFrac_le
  have h2 : ((B * (m + 1) : Nat) : Int) ≤ ((P + 1 : Nat) : Int) :=
    Int.ofNat_le.mpr hP
  rw [Int.natCast_mul, Int.natCast_add, Int.natCast_add,
    Int.natCast_one] at h2
  rw [Int.natCast_one, Int.one_mul]
  exact h2

/-! ## M183-4: 収束の完結 |s_k ⊖ L| ≤ 1/(m+1) -/

/-- **定理 (M183-4, 収束の完結): 極限対象への収束** —
    (1⊖r)·L ≈ 1、|r| ≤ N/(N+1)（1 ≤ N）、|L| ≤ B、
    k ≥ N·(B·(m+1)+m) なら |s_k ⊖ L| ≤ 1/(m+1)。
    鎖: |s_k ⊖ L| ≈ |L|·|r|^k（M183-2）≤ B·|r|^k（M180 右単調）
    ≤ B·(1/(m'+1))（M181 減衰 + M180 左単調、m' := B(m+1)+m）
    ≈ (B·(1/(m'+1)))↑（M123F 埋め込み乗法）≤ (1/(m+1))↑
    （M183-3 折込: B(m+1) ≤ m'+1）。すなわち **s_k → L**
    （明示モジュラス k ≥ N·(B(m+1)+m)）。 -/
theorem geom_converges_to_limit (r L : RReal) (N B m k : Nat)
    (hL : realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one))
    (hb : rLe (rabs r) (qToReal (qFrac N N))) (hN : 1 ≤ N)
    (hLb : rLe (rabs L) (qToReal (qFrac B 0)))
    (hk : N * (B * (m + 1) + m) ≤ k) :
    rLe (rabs (realAdd (realGeomSum r k) (realNeg L)))
      (qToReal (qFrac 1 m)) := by
  -- |L|·|r|^k ≤ B·|r|^k（右因子固定の単調性、0 ≤ |r|^k）
  have t1 : rLe (rmul (rabs L) (realPow (rabs r) k))
      (rmul (qToReal (qFrac B 0)) (realPow (rabs r) k)) :=
    rmul_le_mul_right hLb (realPow_nonneg (rabs_nonneg r) k)
  -- B·|r|^k ≤ B·(1/(m'+1))（左因子固定の単調性 + M181 減衰）
  have hB0 : rLe realZero (qToReal (qFrac B 0)) :=
    rLe_qToReal (qFrac_nonneg B 0)
  have t2 : rLe (rmul (qToReal (qFrac B 0)) (realPow (rabs r) k))
      (rmul (qToReal (qFrac B 0)) (qToReal (qFrac 1 (B * (m + 1) + m)))) :=
    rmul_le_mul_left (qToReal (qFrac B 0))
      (realPow_rabs_decay r N (B * (m + 1) + m) k hb hN hk) hB0
  -- B·(1/(m'+1)) ≈ (B·(1/(m'+1)))↑ ≤ (1/(m+1))↑（埋め込み + 折込）
  have hP : B * (m + 1) ≤ (B * (m + 1) + m) + 1 := by
    generalize B * (m + 1) = Q
    omega
  have t3 : rLe (rmul (qToReal (qFrac B 0))
        (qToReal (qFrac 1 (B * (m + 1) + m))))
      (qToReal (qFrac 1 m)) :=
    rLe_trans (rLe_of_realEq
        (qToReal_mul (qFrac B 0) (qFrac 1 (B * (m + 1) + m))))
      (rLe_qToReal (qFrac_mul_le B m (B * (m + 1) + m) hP))
  exact rLe_trans (rLe_of_realEq (rabs_geom_sub_limit r L k hL))
    (rLe_trans t1 (rLe_trans t2 t3))

/-! ## M183-5: 極限対象の存在（M153F との合成） -/

/-- **定理 (M183-5): 極限対象の存在** — IsPos |1⊖r|（|r| < 1 のとき
    成立）なら、極限対象 L（1⊖r の逆元）が存在し、全ての k で差の
    閉形式 s_k ⊖ L ≈ ⊖(L·r^k) が成り立つ。M153F apart_inv_exists の
    ∃ を ∃ へ写すだけなので witness 抽出（choice）は不要。 -/
theorem geom_limit_object (r : RReal)
    (h : IsPos (rabs (realAdd (qToReal ratRing.one) (realNeg r)))) :
    ∃ L : RReal,
      realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
        (qToReal ratRing.one) ∧
      ∀ k : Nat, realEq (realAdd (realGeomSum r k) (realNeg L))
        (realNeg (rmul L (realPow r k))) := by
  obtain ⟨L, hL⟩ :=
    apart_inv_exists (realAdd (qToReal ratRing.one) (realNeg r)) h
  exact ⟨L, hL, fun k => geom_sub_limit r L k hL⟩

/-! ## M183-6: 総括 -/

/-- **M183-6a: 総括** — 幾何級数の極限対象データ。 -/
structure GeomLimitData where
  /-- 差の閉形式: (1⊖r)·L ≈ 1 ⟹ s_k ⊖ L ≈ ⊖(L·r^k)。 -/
  sub_limit : ∀ (r L : RReal) (k : Nat),
    realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one) →
    realEq (realAdd (realGeomSum r k) (realNeg L))
      (realNeg (rmul L (realPow r k)))
  /-- 差の絶対値: |s_k ⊖ L| ≈ |L|·|r|^k。 -/
  abs_sub_limit : ∀ (r L : RReal) (k : Nat),
    realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one) →
    realEq (rabs (realAdd (realGeomSum r k) (realNeg L)))
      (rmul (rabs L) (realPow (rabs r) k))
  /-- 収束: |r| ≤ N/(N+1)・|L| ≤ B・k ≥ N·(B(m+1)+m) ⟹
      |s_k ⊖ L| ≤ 1/(m+1)。 -/
  converges : ∀ (r L : RReal) (N B m k : Nat),
    realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one) →
    rLe (rabs r) (qToReal (qFrac N N)) → 1 ≤ N →
    rLe (rabs L) (qToReal (qFrac B 0)) →
    N * (B * (m + 1) + m) ≤ k →
    rLe (rabs (realAdd (realGeomSum r k) (realNeg L)))
      (qToReal (qFrac 1 m))
  /-- 極限対象の存在: IsPos |1⊖r| ⟹ ∃ L, 逆元かつ差の閉形式。 -/
  limit_object : ∀ r : RReal,
    IsPos (rabs (realAdd (qToReal ratRing.one) (realNeg r))) →
    ∃ L : RReal,
      realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
        (qToReal ratRing.one) ∧
      ∀ k : Nat, realEq (realAdd (realGeomSum r k) (realNeg L))
        (realNeg (rmul L (realPow r k)))

/-- **M183-6b: witness**。 -/
def geomLimitData : GeomLimitData where
  sub_limit := geom_sub_limit
  abs_sub_limit := rabs_geom_sub_limit
  converges := geom_converges_to_limit
  limit_object := geom_limit_object

/-- **M183-6c: 存在** — 幾何級数の極限対象の certification。 -/
theorem geomLimit_exists : Nonempty GeomLimitData := ⟨geomLimitData⟩

end IUT
