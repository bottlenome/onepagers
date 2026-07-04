/-
# M184: 自己完結な幾何級数収束 — |r|≤N/(N+1) のみからの収束（柱C）

M183 `geom_converges_to_limit` は極限対象への収束を閉じたが、
(i) 極限対象の存在に必要な離隔性 IsPos |1⊖r| と
(ii) |L| の有理上界 B の二つを**仮説**として要求していた。
本モジュールはこの両者を有理上界 |r| ≤ N/(N+1) のみから**導出**し、
幾何級数の収束定理を仮説 hb（と 1 ≤ N）だけの自己完結形で閉じる。

  * M184-1 **`oneMinus_lower`（下界）** —
    |r| ≤ N/(N+1) ⟹ 1/(N+1) ≤ 1⊖r（rLe）。
    点ごとの証明: r_s ≤ |r_s| ≤ N/(N+1) + 2u_s（hb の witness）を
    1/(N+1) + r_s ≤ 1 + 2u_n へ折り込み（2u_{2n+1} ≤ u_n ≤ 2u_n）、
    M130 の移項補題 qLe_sub_move で 1⊖r 側へ移す。
  * M184-2 **`oneMinus_isPos`（離隔性）** —
    |r| ≤ N/(N+1) ⟹ IsPos |1⊖r|。M184-1 の下界を witness 添字
    n₀ = 4N+3 で読む: 2/(n₀+1) + 2u_{n₀} = 4/(4N+4) = 1/(N+1) が
    ちょうど相殺し、qLe_cancel_right で 2/(n₀+1) ≤ (1⊖r)_{n₀}。
  * M184-3 **`Lbound`（|L| の定量上界）** —
    (1⊖r)·L ≈ 1 ∧ |r| ≤ N/(N+1) ⟹ |L| ≤ N+1。
    鎖: |1⊖r|·|L| ≈ |(1⊖r)·L| ≈ |1| ≈ 1（M127F）と
    1/(N+1) ≤ |1⊖r|（M184-1 + M173）から
    (1/(N+1))·|L| ≤ 1（M180 右単調）、両辺を定数 N+1 倍
    （M159F `rLe_mul_natConst_left`）して (N+1)·(1/(N+1)) ≈ 1
    （M129F qFrac_mul + Quot.sound）で |L| ≤ N+1。
  * M184-4 **`geom_converges_self_contained`（本丸）** —
    |r| ≤ N/(N+1) ∧ 1 ≤ N のみから
    ∃ L, (1⊖r)·L ≈ 1 ∧ ∀ m k, N·((N+1)(m+1)+m) ≤ k ⟹
    |s_k ⊖ L| ≤ 1/(m+1)。M184-2 → M183-5（存在）→ M184-3（上界）→
    M183-4（収束）の純合成。witness L は M183-5 の ∃ から obtain で
    受け直して明示に渡す（choice 不使用）。
  * M184-5 `GeomConvergeSCData` — 総括

意義: M183 の「正直な限定」に残っていた二仮説（離隔性・|L| の上界）を
解消し、**幾何級数 s_k は仮説 |r| ≤ N/(N+1)（1 ≤ N）のみで極限対象
L = (1⊖r)⁻¹ に明示モジュラス付きで収束する**という完全自己完結の
収束定理を得た。B = N+1 という上界の定量化は「|1⊖r| ≥ 1/(N+1) の
逆数評価」であり、逆元 witness の評価（M145 の次層とされていた課題）を
順序算術のみで迂回した点が要点。

正直な限定: 収束モジュラス k ≥ N·((N+1)(m+1)+m) は B = N+1 を M183-4 に
代入した形で、最適定数ではない。また L の一意性（realEq を除く）は
M162 系の逆元一意性の範囲であり本層では扱わない。

全て選択公理不使用。
-/
import IUT.GeomLimit
import IUT.RealObstruction
import IUT.RealAbsLe

namespace IUT

/-! ## M184-1: 下界 1/(N+1) ≤ 1⊖r -/

/-- **定理 (M184-1): 1⊖r の下界** — |r| ≤ N/(N+1) なら
    1/(N+1) ≤ 1⊖r（rLe）。点ごと: 添字 n で r_s（s = 2n+1）は
    r_s ≤ |r_s| ≤ N/(N+1) + 2u_s。1/(N+1) + N/(N+1) = 1 と
    2u_s ≤ u_n ≤ 2u_n の折込で 1/(N+1) + r_s ≤ 1 + 2u_n、
    qNeg_neg + qLe_sub_move（M130）で移項して着地。 -/
theorem oneMinus_lower (r : RReal) (N : Nat)
    (hb : rLe (rabs r) (qToReal (qFrac N N))) :
    rLe (qToReal (qFrac 1 N))
      (realAdd (qToReal ratRing.one) (realNeg r)) := by
  intro n
  show qLe (qFrac 1 N)
    (qAdd (qAdd ratRing.one (qNeg (r.seq (2 * n + 1))))
      (qAdd (qUnitFrac n) (qUnitFrac n)))
  -- r_s ≤ |r_s| ≤ N/(N+1) + 2u_s
  have h1 : qLe (r.seq (2 * n + 1))
      (qAdd (qFrac N N)
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1)))) :=
    qLe_trans _ _ _ (qLe_self_abs (r.seq (2 * n + 1))) (hb (2 * n + 1))
  -- 1/(N+1) + r_s ≤ 1/(N+1) + (N/(N+1) + 2u_s)
  have h3 : qLe (qAdd (qFrac 1 N) (r.seq (2 * n + 1)))
      (qAdd (qFrac 1 N)
        (qAdd (qFrac N N)
          (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1))))) :=
    qLe_add_two (qLe_refl (qFrac 1 N)) h1
  -- 結合の付け替え
  have h4 : qAdd (qFrac 1 N)
      (qAdd (qFrac N N)
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1))))
      = qAdd (qAdd (qFrac 1 N) (qFrac N N))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1))) :=
    (qAdd_assoc _ _ _).symm
  -- 1/(N+1) + N/(N+1) ≤ 1（代表計算: (1+N)·1 ≤ 1·(N+1)）
  have q2 : qLe (qFrac (1 + N) N) ratRing.one := by
    show ((1 + N : Nat) : Int) * 1 ≤ 1 * ((N : Int) + 1)
    omega
  have q12 : qLe (qAdd (qFrac 1 N) (qFrac N N)) ratRing.one :=
    qLe_trans _ _ _ (qFrac_add 1 N N) q2
  -- 2u_{2n+1} ≤ 2u_n
  have hus : qLe (qUnitFrac (2 * n + 1)) (qUnitFrac n) :=
    qFrac_le (by omega)
  have q3 : qLe (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1)))
      (qAdd (qUnitFrac n) (qUnitFrac n)) :=
    qLe_add_two hus hus
  have h5 : qLe (qAdd (qAdd (qFrac 1 N) (qFrac N N))
        (qAdd (qUnitFrac (2 * n + 1)) (qUnitFrac (2 * n + 1))))
      (qAdd ratRing.one (qAdd (qUnitFrac n) (qUnitFrac n))) :=
    qLe_add_two q12 q3
  -- 総和: 1/(N+1) + r_s ≤ 1 + 2u_n
  have hsum : qLe (qAdd (qFrac 1 N) (r.seq (2 * n + 1)))
      (qAdd ratRing.one (qAdd (qUnitFrac n) (qUnitFrac n))) :=
    qLe_trans _ _ _ h3 (qLe_trans _ _ _ (qLe_of_eq h4) h5)
  -- r_s = −(−r_s) にして移項（qLe_sub_move）
  have hsum' : qLe (qAdd (qFrac 1 N) (qNeg (qNeg (r.seq (2 * n + 1)))))
      (qAdd ratRing.one (qAdd (qUnitFrac n) (qUnitFrac n))) := by
    rw [qNeg_neg (r.seq (2 * n + 1))]
    exact hsum
  have hfin : qLe (qFrac 1 N)
      (qAdd (qAdd ratRing.one (qAdd (qUnitFrac n) (qUnitFrac n)))
        (qNeg (r.seq (2 * n + 1)))) :=
    qLe_sub_move hsum'
  -- 目標の並べ替え: (1 + (−r_s)) + 2u_n = (1 + 2u_n) + (−r_s)
  have e : qAdd (qAdd ratRing.one (qNeg (r.seq (2 * n + 1))))
      (qAdd (qUnitFrac n) (qUnitFrac n))
      = qAdd (qAdd ratRing.one (qAdd (qUnitFrac n) (qUnitFrac n)))
        (qNeg (r.seq (2 * n + 1))) := by
    rw [qAdd_assoc ratRing.one (qNeg (r.seq (2 * n + 1)))
        (qAdd (qUnitFrac n) (qUnitFrac n)),
      qAdd_comm (qNeg (r.seq (2 * n + 1)))
        (qAdd (qUnitFrac n) (qUnitFrac n)),
      ← qAdd_assoc ratRing.one (qAdd (qUnitFrac n) (qUnitFrac n))
        (qNeg (r.seq (2 * n + 1)))]
  rw [e]
  exact hfin

/-! ## M184-2: 離隔性 IsPos |1⊖r| -/

/-- **定理 (M184-2): 1⊖r の離隔性** — |r| ≤ N/(N+1) なら
    IsPos |1⊖r|。M184-1 の下界を witness 添字 n₀ = 4N+3 で読む:
    2/(n₀+1) + 2u_{n₀} = 4/(4N+4) = 1/(N+1) ≤ (1⊖r)_{n₀} + 2u_{n₀}、
    右消去（qLe_cancel_right）で 2/(n₀+1) ≤ (1⊖r)_{n₀} ≤ |(1⊖r)_{n₀}|。
    これが M153F `apart_inv_exists`（→ M183-5）の要求する離隔性。 -/
theorem oneMinus_isPos (r : RReal) (N : Nat)
    (hb : rLe (rabs r) (qToReal (qFrac N N))) :
    IsPos (rabs (realAdd (qToReal ratRing.one) (realNeg r))) := by
  have hge := oneMinus_lower r N hb
  refine ⟨4 * N + 3, ?_⟩
  show qLe (qFrac 2 (4 * N + 3))
    (qAbs ((realAdd (qToReal ratRing.one) (realNeg r)).seq (4 * N + 3)))
  have hg := hge (4 * N + 3)
  -- 2/(4N+4) + 2u_{4N+3} ≤ 4/(4N+4) = 1/(N+1)
  have hstep : qLe (qAdd (qFrac 2 (4 * N + 3))
        (qAdd (qUnitFrac (4 * N + 3)) (qUnitFrac (4 * N + 3))))
      (qFrac 1 N) :=
    qLe_trans _ _ _
      (qLe_add_two (qLe_refl (qFrac 2 (4 * N + 3)))
        (qFrac_add 1 1 (4 * N + 3)))
      (qLe_trans _ _ _ (qFrac_add 2 2 (4 * N + 3)) (qFrac_le (by omega)))
  have h5 : qLe (qAdd (qFrac 2 (4 * N + 3))
        (qAdd (qUnitFrac (4 * N + 3)) (qUnitFrac (4 * N + 3))))
      (qAdd ((realAdd (qToReal ratRing.one) (realNeg r)).seq (4 * N + 3))
        (qAdd (qUnitFrac (4 * N + 3)) (qUnitFrac (4 * N + 3)))) :=
    qLe_trans _ _ _ hstep hg
  have hwit : qLe (qFrac 2 (4 * N + 3))
      ((realAdd (qToReal ratRing.one) (realNeg r)).seq (4 * N + 3)) :=
    qLe_cancel_right h5
  exact qLe_trans _ _ _ hwit (qLe_self_abs _)

/-! ## M184-3: |L| の定量上界 -/

/-- ℤ 定数 N+1 の実数化は分数 (N+1)/1 の実数化と一致（代表計算）。 -/
theorem intToReal_qFrac (N : Nat) :
    realEq (intToReal ((N + 1 : Nat) : Int)) (qToReal (qFrac (N + 1) 0)) :=
  realEq_of_seq_eq (fun _ =>
    Quot.sound (show ((N + 1 : Nat) : Int) * (((0 : Nat) : Int) + 1)
      = ((N + 1 : Nat) : Int) * 1 by omega))

/-- (N+1)/1 · 1/(N+1) = 1（M129F qFrac_mul + Quot.sound）。 -/
theorem qFrac_succ_inv (N : Nat) :
    qMul (qFrac (N + 1) 0) (qFrac 1 N) = ratRing.one := by
  rw [qFrac_mul (N + 1) 0 1 N]
  refine Quot.sound ?_
  show (((N + 1) * 1 : Nat) : Int) * 1
    = 1 * ((((0 + 1) * (N + 1) - 1 : Nat) : Int) + 1)
  omega

/-- **定理 (M184-3): |L| の定量上界** — (1⊖r)·L ≈ 1 かつ
    |r| ≤ N/(N+1) なら |L| ≤ N+1。鎖:
    |1⊖r|·|L| ≈ |(1⊖r)·L| ≈ |1| ≈ 1、1/(N+1) ≤ 1⊖r ≤ |1⊖r|
    （M184-1 + M173）、M180 右単調で (1/(N+1))·|L| ≤ 1、
    定数 N+1 倍（M159F）と (N+1)·(1/(N+1)) ≈ 1 で |L| ≤ N+1。 -/
theorem Lbound (r L : RReal) (N : Nat)
    (hb : rLe (rabs r) (qToReal (qFrac N N)))
    (hL : realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one)) :
    rLe (rabs L) (qToReal (qFrac (N + 1) 0)) := by
  -- |1⊖r|·|L| ≈ 1
  have h1 : realEq
      (rmul (rabs (realAdd (qToReal ratRing.one) (realNeg r))) (rabs L))
      (qToReal ratRing.one) :=
    realEq_trans
      (realEq_symm (rabs_mul (realAdd (qToReal ratRing.one) (realNeg r)) L))
      (realEq_trans (rabs_congr hL) rabs_one)
  -- 1/(N+1) ≤ |1⊖r|
  have hlow : rLe (qToReal (qFrac 1 N))
      (rabs (realAdd (qToReal ratRing.one) (realNeg r))) :=
    rLe_trans (oneMinus_lower r N hb)
      (rLe_self_rabs (realAdd (qToReal ratRing.one) (realNeg r)))
  -- (1/(N+1))·|L| ≤ |1⊖r|·|L| ≈ 1
  have h2 : rLe (rmul (qToReal (qFrac 1 N)) (rabs L))
      (rmul (rabs (realAdd (qToReal ratRing.one) (realNeg r))) (rabs L)) :=
    rmul_le_mul_right hlow (rabs_nonneg L)
  have h3 : rLe (rmul (qToReal (qFrac 1 N)) (rabs L))
      (qToReal ratRing.one) :=
    rLe_trans h2 (rLe_of_realEq h1)
  -- 定数 N+1 倍
  have h4 := rLe_mul_natConst_left (N + 1) h3
  -- 左辺 ≈ |L|: (N+1)·((1/(N+1))·|L|) ≈ ((N+1)·(1/(N+1)))·|L| ≈ 1·|L| ≈ |L|
  have eL : realEq
      (rmul (intToReal ((N + 1 : Nat) : Int))
        (rmul (qToReal (qFrac 1 N)) (rabs L)))
      (rabs L) := by
    refine realEq_trans (rmul_congr_left
      (rmul (qToReal (qFrac 1 N)) (rabs L)) (intToReal_qFrac N)) ?_
    refine realEq_trans (realEq_symm (rmul_assoc_real
      (qToReal (qFrac (N + 1) 0)) (qToReal (qFrac 1 N)) (rabs L))) ?_
    refine realEq_trans (rmul_congr_left (rabs L)
      (qToReal_mul (qFrac (N + 1) 0) (qFrac 1 N))) ?_
    rw [qFrac_succ_inv N]
    exact realEq_trans (rmul_comm (qToReal ratRing.one) (rabs L))
      (rmul_one (rabs L))
  -- 右辺 ≈ N+1
  have eR : realEq
      (rmul (intToReal ((N + 1 : Nat) : Int)) (qToReal ratRing.one))
      (qToReal (qFrac (N + 1) 0)) :=
    realEq_trans (rmul_one (intToReal ((N + 1 : Nat) : Int)))
      (intToReal_qFrac N)
  exact rLe_congr eL eR h4

/-! ## M184-4: 本丸 — 自己完結な収束定理 -/

/-- **定理 (M184-4, 本丸): 自己完結な幾何級数収束** —
    |r| ≤ N/(N+1)（1 ≤ N）**のみ**から、極限対象 L（1⊖r の逆元）が
    存在して s_k は L に明示モジュラス k ≥ N·((N+1)(m+1)+m) 付きで
    収束する。M184-2（離隔性）→ M183-5（∃L）→ M184-3（|L| ≤ N+1）→
    M183-4（B = N+1 で収束）の合成。∃ の witness は obtain で受け直して
    明示に渡す（choice 不使用）。 -/
theorem geom_converges_self_contained (r : RReal) (N : Nat)
    (hb : rLe (rabs r) (qToReal (qFrac N N))) (hN : 1 ≤ N) :
    ∃ L : RReal,
      realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
        (qToReal ratRing.one) ∧
      ∀ m k : Nat, N * ((N + 1) * (m + 1) + m) ≤ k →
        rLe (rabs (realAdd (realGeomSum r k) (realNeg L)))
          (qToReal (qFrac 1 m)) := by
  obtain ⟨L, hL, _⟩ := geom_limit_object r (oneMinus_isPos r N hb)
  refine ⟨L, hL, ?_⟩
  intro m k hk
  exact geom_converges_to_limit r L N (N + 1) m k hL hb hN
    (Lbound r L N hb hL) hk

/-! ## M184-5: 総括 -/

/-- **M184-5a: 総括** — 自己完結な幾何級数収束データ。 -/
structure GeomConvergeSCData where
  /-- 下界: |r| ≤ N/(N+1) ⟹ 1/(N+1) ≤ 1⊖r。 -/
  lower : ∀ (r : RReal) (N : Nat),
    rLe (rabs r) (qToReal (qFrac N N)) →
    rLe (qToReal (qFrac 1 N))
      (realAdd (qToReal ratRing.one) (realNeg r))
  /-- 離隔性: |r| ≤ N/(N+1) ⟹ IsPos |1⊖r|。 -/
  isPos : ∀ (r : RReal) (N : Nat),
    rLe (rabs r) (qToReal (qFrac N N)) →
    IsPos (rabs (realAdd (qToReal ratRing.one) (realNeg r)))
  /-- 上界: (1⊖r)·L ≈ 1 ∧ |r| ≤ N/(N+1) ⟹ |L| ≤ N+1。 -/
  lbound : ∀ (r L : RReal) (N : Nat),
    rLe (rabs r) (qToReal (qFrac N N)) →
    realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
      (qToReal ratRing.one) →
    rLe (rabs L) (qToReal (qFrac (N + 1) 0))
  /-- 自己完結な収束: |r| ≤ N/(N+1) ∧ 1 ≤ N ⟹
      ∃ L, (1⊖r)·L ≈ 1 ∧ 明示モジュラス付き収束。 -/
  converges : ∀ (r : RReal) (N : Nat),
    rLe (rabs r) (qToReal (qFrac N N)) → 1 ≤ N →
    ∃ L : RReal,
      realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
        (qToReal ratRing.one) ∧
      ∀ m k : Nat, N * ((N + 1) * (m + 1) + m) ≤ k →
        rLe (rabs (realAdd (realGeomSum r k) (realNeg L)))
          (qToReal (qFrac 1 m))

/-- **M184-5b: witness**。 -/
def geomConvergeSCData : GeomConvergeSCData where
  lower := oneMinus_lower
  isPos := oneMinus_isPos
  lbound := Lbound
  converges := geom_converges_self_contained

/-- **M184-5c: 存在** — 自己完結な幾何級数収束の certification。 -/
theorem geomConvergeSC_exists : Nonempty GeomConvergeSCData :=
  ⟨geomConvergeSCData⟩

end IUT

