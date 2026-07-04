/-
# M181: 実数幾何級数の減衰 — |r|^k → 0 の明示モジュラス（柱C）

M179 の算術核（Nat 上の減衰モジュラス N^k·(m+1) ≤ (N+1)^k）と
M180 の実数冪単調性（0 ≤ a ≤ b ⟹ a^k ≤ b^k）を接続し、
**実数の幾何減衰** |r| ≤ N/(N+1) ⟹ |r|^k ≤ 1/(m+1)（k ≥ N·m）を
choice なしで閉じる。幾何級数収束 4 段組（M179 の注記 (a)–(d)）の
段 (c) に当たる。

  * M181-1 `int_add_one_pow_pos` — 分母正値 0 < ((N:Int)+1)^k
  * M181-2 `qpow`・**`qpow_frac_repr`** — 有理数の冪と代表元計算:
    (N/(N+1))^k = N^k/(N+1)^k（Quot 上で厳密等式）
  * M181-3 **`qpow_frac_le`** — 有理冪の減衰:
    N·m ≤ k ⟹ (N/(N+1))^k ≤ 1/(m+1)（M179 の Int 昇格）
  * M181-4 **`realPow_qToReal`** — 埋め込みと冪の可換:
    (q↑)^k ≈ (q^k)↑（qToReal_mul の帰納反復）
  * M181-5 **`realPow_rabs_decay`** — 本丸: |r| ≤ (N/(N+1))↑ なら
    k ≥ N·m で |r|^k ≤ (1/(m+1))↑
  * M181-6 `RealGeomDecayData` — 総括

意義: 公比の絶対値に有理上界 N/(N+1) < 1 があれば、その冪は明示
モジュラス k ≥ N·m で単位分数 1/(m+1) 以下に落ちる。M175（部分和の
絶対上界）・M177（誤差 = |r|^k）と併せ、幾何級数の誤差が実際に
0 へ潰れることの定量的内容であり、収束証明の解析的心臓部。

正直な限定: 本モジュールは |r|^k の減衰（各 m に対する明示添字）まで。
収束の最終組み上げ — IsPos(1 ⊖ |r|) からの有理上界抽出 (a)、部分和の
IsCauchyReals 性と rlim（M128 完備性）による極限構成 (d) — は次層。

全て選択公理不使用。
-/
import IUT.RealMulOrder
import IUT.RealAbsTriangle
import IUT.GeomDecayNat
import IUT.RealPow

namespace IUT

/-! ## M181-1: 分母の正値性 -/

/-- **補題 (M181-1): 分母正値** — 0 < ((N:Int)+1)^k。k の帰納:
    0 段は 0 < 1、succ 段は正×正（Int.mul_pos）。 -/
theorem int_add_one_pow_pos (N k : Nat) : 0 < ((N : Int) + 1) ^ k := by
  induction k with
  | zero =>
    rw [Int.pow_zero]
    omega
  | succ k ih =>
    rw [Int.pow_succ]
    exact Int.mul_pos ih (by omega)

/-! ## M181-2: 有理数の冪と代表元 -/

/-- **M181-2a: 有理数の冪** — q^0 = 1、q^{k+1} = q^k · q。 -/
def qpow (q : QRat) : Nat → QRat
  | 0 => ratRing.one
  | k + 1 => qMul (qpow q k) q

/-- **定理 (M181-2b): 代表元計算** — (N/(N+1))^k は代表
    N^k/(N+1)^k を持つ（Quot 上の厳密等式）。k の帰納で prMul の
    分子分母がそれぞれ Int.pow_succ に畳まれる（preRat_ext）。 -/
theorem qpow_frac_repr (N k : Nat) :
    qpow (qFrac N N) k
      = Quot.mk ratRel
          ⟨(N : Int) ^ k, ((N : Int) + 1) ^ k, int_add_one_pow_pos N k⟩ := by
  induction k with
  | zero =>
    show Quot.mk ratRel prOne = _
    exact congrArg (Quot.mk ratRel)
      (preRat_ext (Int.pow_zero (N : Int)).symm
        (Int.pow_zero ((N : Int) + 1)).symm)
  | succ k ih =>
    show qMul (qpow (qFrac N N) k) (qFrac N N) = _
    rw [ih]
    show Quot.mk ratRel
        (prMul ⟨(N : Int) ^ k, ((N : Int) + 1) ^ k, int_add_one_pow_pos N k⟩
          ⟨(N : Int), (N : Int) + 1, by omega⟩) = _
    exact congrArg (Quot.mk ratRel)
      (preRat_ext (Int.pow_succ (N : Int) k).symm
        (Int.pow_succ ((N : Int) + 1) k).symm)

/-! ## M181-3: 有理冪の減衰 -/

/-- **定理 (M181-3, 本丸): 有理冪の減衰** — N ≥ 1・N·m ≤ k なら
    (N/(N+1))^k ≤ 1/(m+1)。代表元計算（M181-2b）で prLe に落とし、
    M179 の Nat 不等式 N^k·(m+1) ≤ (N+1)^k を Int へ昇格。 -/
theorem qpow_frac_le (N m k : Nat) (hN : 1 ≤ N) (hk : N * m ≤ k) :
    qLe (qpow (qFrac N N) k) (qFrac 1 m) := by
  rw [qpow_frac_repr]
  show (N : Int) ^ k * ((m : Int) + 1) ≤ (1 : Int) * (((N : Int) + 1) ^ k)
  have h1 : N ^ k * (m + 1) ≤ (N + 1) ^ k :=
    nat_geom_decay_modulus N m k hN hk
  have h2 : ((N ^ k * (m + 1) : Nat) : Int) ≤ (((N + 1) ^ k : Nat) : Int) :=
    Int.ofNat_le.mpr h1
  rw [Int.natCast_mul, Int.natCast_pow, Int.natCast_pow, Int.natCast_add,
    Int.natCast_add, Int.natCast_one] at h2
  rw [Int.one_mul]
  exact h2

/-! ## M181-4: 埋め込みと冪の可換 -/

/-- **定理 (M181-4): 埋め込みと冪の可換** — (q↑)^k ≈ (q^k)↑。
    k の帰納: 0 段は両辺 1↑（refl）、succ 段は左 congruence（IH）の後
    qToReal_mul（M123F-7d）で rmul を qMul に畳む。 -/
theorem realPow_qToReal (q : QRat) :
    ∀ k, realEq (realPow (qToReal q) k) (qToReal (qpow q k)) := by
  intro k
  induction k with
  | zero => exact realEq_refl (qToReal ratRing.one)
  | succ k ih =>
    show realEq (rmul (realPow (qToReal q) k) (qToReal q))
      (qToReal (qMul (qpow q k) q))
    exact realEq_trans (rmul_congr_left (qToReal q) ih)
      (qToReal_mul (qpow q k) q)

/-! ## M181-5: 実数幾何減衰 -/

/-- **定理 (M181-5, 本丸): 実数幾何減衰** — |r| ≤ (N/(N+1))↑（N ≥ 1）
    なら k ≥ N·m で |r|^k ≤ (1/(m+1))↑。鎖:
    |r|^k ≤ ((N/(N+1))↑)^k（M180 冪単調 + M173 |r| ≥ 0）
    ≈ ((N/(N+1))^k)↑（M181-4）≤ (1/(m+1))↑（M181-3 + M174 埋め込み
    単調）。各 m に対し添字 N·m から先で成立 = 明示モジュラス。 -/
theorem realPow_rabs_decay (r : RReal) (N m k : Nat)
    (hb : rLe (rabs r) (qToReal (qFrac N N)))
    (hN : 1 ≤ N) (hk : N * m ≤ k) :
    rLe (realPow (rabs r) k) (qToReal (qFrac 1 m)) := by
  have h1 : rLe (realPow (rabs r) k) (realPow (qToReal (qFrac N N)) k) :=
    realPow_le (rabs_nonneg r) hb k
  have h2 : rLe (realPow (qToReal (qFrac N N)) k)
      (qToReal (qpow (qFrac N N) k)) :=
    rLe_of_realEq (realPow_qToReal (qFrac N N) k)
  have h3 : rLe (qToReal (qpow (qFrac N N) k)) (qToReal (qFrac 1 m)) :=
    rLe_qToReal (qpow_frac_le N m k hN hk)
  exact rLe_trans h1 (rLe_trans h2 h3)

/-! ## M181-6: 総括 -/

/-- **M181-6a: 総括** — 実数幾何減衰データ。 -/
structure RealGeomDecayData where
  /-- 有理冪の減衰 (N/(N+1))^k ≤ 1/(m+1)（k ≥ N·m）。 -/
  frac_le : ∀ (N m k : Nat), 1 ≤ N → N * m ≤ k →
    qLe (qpow (qFrac N N) k) (qFrac 1 m)
  /-- 埋め込みと冪の可換 (q↑)^k ≈ (q^k)↑。 -/
  pow_embed : ∀ (q : QRat) (k : Nat),
    realEq (realPow (qToReal q) k) (qToReal (qpow q k))
  /-- 実数幾何減衰 |r| ≤ (N/(N+1))↑ ⟹ |r|^k ≤ (1/(m+1))↑（k ≥ N·m）。 -/
  decay : ∀ (r : RReal) (N m k : Nat),
    rLe (rabs r) (qToReal (qFrac N N)) → 1 ≤ N → N * m ≤ k →
    rLe (realPow (rabs r) k) (qToReal (qFrac 1 m))

/-- **M181-6b: witness**。 -/
def realGeomDecayData : RealGeomDecayData where
  frac_le := qpow_frac_le
  pow_embed := realPow_qToReal
  decay := realPow_rabs_decay

/-- **M181-6c: 存在**。 -/
theorem realGeomDecay_exists : Nonempty RealGeomDecayData :=
  ⟨realGeomDecayData⟩

end IUT
