/-
# M185F: 幾何級数の rlim 完備化 — 対角極限 = (1⊖r)⁻¹（柱C）

幾何級数収束プログラムの最後の「正直な限定」の解消: M183/M184 が
残していた **rlim（M128 完備性）による位相的構成（Path A）** を閉じる。
加速部分列 Y_m := s_{a(m)}（a(m) = N·((N+1)(m+1)+m)、M184 の明示
モジュラス）が IsCauchyReals（M128 の witness 形正則性）を満たすことを
示し、その対角極限 rlim Y が代数的逆元 L = (1⊖r)⁻¹ に realEq で
一致することを rlim_unique で確定する。

  * M185F-1 実数レベルの補助 — `realSub_split`（望遠鏡）・
    `rLe_add_pair`（両側加法単調）・`rabs_sub_comm_real`（|x⊖y| ≈ |y⊖x|）
  * M185F-2 **`rabs_sub_pointwise`（点ごと展開の核）** —
    rLe |X ⊖ L| ≤ B↑ ⟹ ∀j, |X_j − L_j| ≤ B + 2u_j
    （添字 2t+1 の読み替えを ε-消去 c = 3 で吸収。2u_j 予算を
    一度しか消費しない点が本モジュール全体の勘所）
  * M185F-3 `geomRlimSeq`・`geom_rlim_converges_witness` — 加速部分列と
    rlim_unique 形の収束 witness ∀m j, |L_j − Y_{m,j}| ≤ u_m + 2u_j
  * M185F-4 **`geom_seq_diff_bound`・`geom_seq_isCauchy`（本丸）** —
    三角不等式を rLe レベルで先に閉じ（|Y_m ⊖ Y_n| ≤ 1/(m+1) + 1/(n+1)、
    余剰は rLe_trans 内部の ε-消去が吸収）、M185F-2 を一度だけ適用して
    u_m + u_n + 2u_j 予算に正確に着地
  * M185F-5 **`geom_rlim_complete`（主定理）** — |r| ≤ N/(N+1)（1 ≤ N）
    のみから ∃ L, (1⊖r)·L ≈ 1 ∧ rlim (geomRlimSeq r N) ≈ L
  * M185F-6 `GeomRlimData` — 総括

意義: M183 の正直な限定に「rlim による位相的構成は s_k の
IsCauchyReals 性のテール評価を要し範囲外」とあった最後の欠落を埋め、
**代数的に構成した逆元 (1⊖r)⁻¹ が、幾何級数部分和の構成的対角極限
（Bishop 流完備性 M128）と同一の実数である**ことを確定した。これで
柱Cの幾何級数収束プログラムは「代数（逆元）・定量（明示モジュラス）・
位相（rlim）」の三面が全て一致する完結形に到達。IsCauchyReals の
2u_j 予算（素朴な点ごと三角分割では u_m + u_n + 4u_j に溢れる）は、
三角不等式を rLe レベルで先に済ませてから点ごと展開を一度だけ行う
二段構えで回避した。

正直な限定: 完備化の対象は生の部分和列 s_k ではなく明示モジュラスで
加速した部分列 geomRlimSeq r N（s_k 自身は 1/(m+1) 速の正則性を持たない
ため IsCauchyReals の modulus 固定形に乗らない — 添字付け替えは
Bishop 流の標準操作）。また geomRlimSeq は上界パラメータ N に依存する
（N を変えた加速列の極限が互いに realEq であることは rlim_unique から
従うが、本層では個別 N ごとの一致まで）。L は ∃ 形で受け渡し、
witness 抽出（choice）は不使用。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealComplete
import IUT.GeomConvergeSC

namespace IUT

/-! ## M185F-1: 実数レベルの補助 -/

/-- 望遠鏡分解（実数版）: x ⊖ z ≈ (x ⊖ y) ⊕ (y ⊖ z)。
    加法群法則（M117F）の合成のみ。 -/
theorem realSub_split (x y z : RReal) :
    realEq (realAdd x (realNeg z))
      (realAdd (realAdd x (realNeg y)) (realAdd y (realNeg z))) := by
  -- 内側: ⊖y ⊕ (y ⊕ ⊖z) ≈ ⊖z
  have a1 : realEq (realAdd (realAdd (realNeg y) y) (realNeg z))
      (realAdd (realNeg y) (realAdd y (realNeg z))) :=
    realAdd_assoc (realNeg y) y (realNeg z)
  have a2 : realEq (realAdd (realNeg y) y) realZero :=
    realEq_trans (realAdd_comm (realNeg y) y) (realAdd_neg y)
  have a3 : realEq (realAdd (realAdd (realNeg y) y) (realNeg z))
      (realAdd realZero (realNeg z)) :=
    realAdd_congr_left (realNeg z) a2
  have a4 : realEq (realAdd realZero (realNeg z)) (realNeg z) :=
    realEq_trans (realAdd_comm realZero (realNeg z))
      (realAdd_zero (realNeg z))
  have hyz : realEq (realAdd (realNeg y) (realAdd y (realNeg z)))
      (realNeg z) :=
    realEq_trans (realEq_symm a1) (realEq_trans a3 a4)
  -- 全体: (x ⊖ y) ⊕ (y ⊖ z) ≈ x ⊕ ⊖z
  have hfull : realEq
      (realAdd (realAdd x (realNeg y)) (realAdd y (realNeg z)))
      (realAdd x (realNeg z)) :=
    realEq_trans (realAdd_assoc x (realNeg y) (realAdd y (realNeg z)))
      (realAdd_congr_right x hyz)
  exact realEq_symm hfull

/-- 両側加法単調: x ≤ x' ∧ y ≤ y' ⟹ x ⊕ y ≤ x' ⊕ y'
    （rLe_add（M130）+ 可換 congruence の合成）。 -/
theorem rLe_add_pair {x y x' y' : RReal} (h1 : rLe x x') (h2 : rLe y y') :
    rLe (realAdd x y) (realAdd x' y') := by
  have s1 : rLe (realAdd x y) (realAdd x' y) := rLe_add y h1
  have s2 : rLe (realAdd y x') (realAdd y' x') := rLe_add x' h2
  have s3 : rLe (realAdd x' y) (realAdd x' y') :=
    rLe_congr (realAdd_comm y x') (realAdd_comm y' x') s2
  exact rLe_trans s1 s3

/-- 差の絶対値の対称性（実数版）: |x ⊖ y| ≈ |y ⊖ x|
    （列レベルで qAbs_sub_comm（M128-1）が点ごとに一致）。 -/
theorem rabs_sub_comm_real (x y : RReal) :
    realEq (rabs (realAdd x (realNeg y))) (rabs (realAdd y (realNeg x))) :=
  realEq_of_seq_eq (fun n =>
    qAbs_sub_comm (x.seq (2 * n + 1)) (y.seq (2 * n + 1)))

/-! ## M185F-2: 点ごと展開の核 -/

/-- **定理 (M185F-2, 核): rLe から witness 形への点ごと展開** —
    rLe |X ⊖ L| ≤ B↑ なら ∀j, |X_j − L_j| ≤ B + 2u_j。
    rLe の各項評価は添字 2t+1 のもの（realAdd の倍速化）なので、
    3 点分割 |X_j − L_j| ≤ |X_j − X_s| + |X_s − L_s| + |L_s − L_j|
    （s = 2t+1）で正則性 2 本 + 仮定を合成し、余剰
    2u_s + 2u_t ≤ 3/(t+1) を ε-消去（c = 3）で潰す。
    **2u_j 予算を一度しか消費しない**のが IsCauchyReals 着地の鍵。 -/
theorem rabs_sub_pointwise (X L : RReal) (B : QRat)
    (h : rLe (rabs (realAdd X (realNeg L))) (qToReal B)) (j : Nat) :
    qLe (qAbs (qAdd (X.seq j) (qNeg (L.seq j))))
      (qAdd B (qAdd (qUnitFrac j) (qUnitFrac j))) := by
  apply qLe_of_forall_add_frac 3
  intro t
  -- 仮定の添字 t 読み（defeq: (rabs (X ⊖ L)).seq t = |X_s − L_s|, s = 2t+1）
  have b2 : qLe (qAbs (qAdd (X.seq (2 * t + 1)) (qNeg (L.seq (2 * t + 1)))))
      (qAdd B (qAdd (qUnitFrac t) (qUnitFrac t))) := h t
  -- 3 点分割と正則性
  have t1 := qAbs_sub_split (X.seq j) (X.seq (2 * t + 1)) (L.seq j)
  have t2 := qAbs_sub_split (X.seq (2 * t + 1)) (L.seq (2 * t + 1))
    (L.seq j)
  have b1 := X.reg j (2 * t + 1)
  have b3 := L.reg (2 * t + 1) j
  have total := qLe_trans _ _ _ t1
    (qLe_add_two b1 (qLe_trans _ _ _ t2 (qLe_add_two b2 b3)))
  apply qLe_trans _ _ _ total
  -- 並べ替え: (u_j+u_s) + ((B+2u_t)+(u_s+u_j)) = (B+2u_j) + (2u_t+2u_s)
  have e1 : qAdd (qAdd (qUnitFrac j) (qUnitFrac (2 * t + 1)))
      (qAdd (qAdd B (qAdd (qUnitFrac t) (qUnitFrac t)))
        (qAdd (qUnitFrac (2 * t + 1)) (qUnitFrac j)))
      = qAdd (qAdd B (qAdd (qUnitFrac j) (qUnitFrac j)))
        (qAdd (qAdd (qUnitFrac t) (qUnitFrac t))
          (qAdd (qUnitFrac (2 * t + 1)) (qUnitFrac (2 * t + 1)))) := by
    rw [← qAdd_assoc (qAdd (qUnitFrac j) (qUnitFrac (2 * t + 1)))
        (qAdd B (qAdd (qUnitFrac t) (qUnitFrac t)))
        (qAdd (qUnitFrac (2 * t + 1)) (qUnitFrac j)),
      qAdd_comm (qAdd (qUnitFrac j) (qUnitFrac (2 * t + 1)))
        (qAdd B (qAdd (qUnitFrac t) (qUnitFrac t))),
      qAdd_assoc (qAdd B (qAdd (qUnitFrac t) (qUnitFrac t)))
        (qAdd (qUnitFrac j) (qUnitFrac (2 * t + 1)))
        (qAdd (qUnitFrac (2 * t + 1)) (qUnitFrac j)),
      qAdd_comm (qUnitFrac (2 * t + 1)) (qUnitFrac j),
      qAdd_swap_mid (qUnitFrac j) (qUnitFrac (2 * t + 1))
        (qUnitFrac j) (qUnitFrac (2 * t + 1)),
      qAdd_swap_mid B (qAdd (qUnitFrac t) (qUnitFrac t))
        (qAdd (qUnitFrac j) (qUnitFrac j))
        (qAdd (qUnitFrac (2 * t + 1)) (qUnitFrac (2 * t + 1)))]
  apply qLe_trans _ _ _ (qLe_of_eq e1)
  refine qLe_add_two (qLe_refl _) ?_
  -- 余剰: 2u_t + 2u_s ≤ F2t + u_t ≤ F3t（2u_{2t+1} = u_t）
  have hs2 : qLe (qAdd (qUnitFrac (2 * t + 1)) (qUnitFrac (2 * t + 1)))
      (qFrac 1 t) :=
    qLe_trans _ _ _ (qFrac_add 1 1 (2 * t + 1)) (qFrac_le (by omega))
  exact qLe_trans _ _ _ (qLe_add_two (qFrac_add 1 1 t) hs2)
    (qFrac_add 2 1 t)

/-! ## M185F-3: 加速部分列と収束 witness -/

/-- **M185F-3a: 加速部分列** — Y_m := s_{a(m)}、
    a(m) = N·((N+1)(m+1)+m)（M184 の明示モジュラス、
    |Y_m ⊖ L| ≤ 1/(m+1) が成り立つ最小保証添字）。 -/
def geomRlimSeq (r : RReal) (N : Nat) (m : Nat) : RReal :=
  realGeomSum r (N * ((N + 1) * (m + 1) + m))

/-- **定理 (M185F-3b): rlim_unique 形の収束 witness** —
    M184 の収束（k = a(m) で |Y_m ⊖ L| ≤ 1/(m+1)）を M185F-2 で
    点ごと展開し、qAbs_sub_comm で L 側へ反転:
    ∀m j, |L_j − Y_{m,j}| ≤ u_m + 2u_j。 -/
theorem geom_rlim_converges_witness (r L : RReal) (N : Nat)
    (hconv : ∀ m k : Nat, N * ((N + 1) * (m + 1) + m) ≤ k →
      rLe (rabs (realAdd (realGeomSum r k) (realNeg L)))
        (qToReal (qFrac 1 m)))
    (m j : Nat) :
    qLe (qAbs (qAdd (L.seq j) (qNeg ((geomRlimSeq r N m).seq j))))
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac j) (qUnitFrac j))) := by
  have hm : rLe (rabs (realAdd (geomRlimSeq r N m) (realNeg L)))
      (qToReal (qFrac 1 m)) :=
    hconv m (N * ((N + 1) * (m + 1) + m)) (Nat.le_refl _)
  rw [qAbs_sub_comm (L.seq j) ((geomRlimSeq r N m).seq j)]
  exact rabs_sub_pointwise (geomRlimSeq r N m) L (qFrac 1 m) hm j

/-! ## M185F-4: IsCauchyReals（本丸） -/

/-- **定理 (M185F-4a): 差の一括評価** —
    |Y_m ⊖ Y_n| ≤ (1/(m+1) + 1/(n+1))↑（rLe）。
    望遠鏡 Y_m ⊖ Y_n ≈ (Y_m ⊖ L) ⊕ (L ⊖ Y_n) と rLe レベルの
    三角不等式（M174）で先に単一の rLe に畳む — 点ごと三角分割だと
    2u_j が二重に発生して IsCauchyReals の予算に溢れるが、rLe_trans の
    内部 ε-消去が余剰を吸収するためここでは無償。 -/
theorem geom_seq_diff_bound (r L : RReal) (N : Nat)
    (hconv : ∀ m k : Nat, N * ((N + 1) * (m + 1) + m) ≤ k →
      rLe (rabs (realAdd (realGeomSum r k) (realNeg L)))
        (qToReal (qFrac 1 m)))
    (m n : Nat) :
    rLe (rabs (realAdd (geomRlimSeq r N m) (realNeg (geomRlimSeq r N n))))
      (qToReal (qAdd (qUnitFrac m) (qUnitFrac n))) := by
  -- 収束評価（k = 各モジュラス）
  have hm : rLe (rabs (realAdd (geomRlimSeq r N m) (realNeg L)))
      (qToReal (qFrac 1 m)) :=
    hconv m (N * ((N + 1) * (m + 1) + m)) (Nat.le_refl _)
  have hn : rLe (rabs (realAdd (geomRlimSeq r N n) (realNeg L)))
      (qToReal (qFrac 1 n)) :=
    hconv n (N * ((N + 1) * (n + 1) + n)) (Nat.le_refl _)
  -- 反転: |L ⊖ Y_n| ≈ |Y_n ⊖ L| ≤ 1/(n+1)
  have hn' : rLe (rabs (realAdd L (realNeg (geomRlimSeq r N n))))
      (qToReal (qFrac 1 n)) :=
    rLe_congr (rabs_sub_comm_real (geomRlimSeq r N n) L)
      (realEq_refl (qToReal (qFrac 1 n))) hn
  -- 望遠鏡 + 三角不等式（rLe レベル）
  have hsplit : realEq
      (realAdd (geomRlimSeq r N m) (realNeg (geomRlimSeq r N n)))
      (realAdd (realAdd (geomRlimSeq r N m) (realNeg L))
        (realAdd L (realNeg (geomRlimSeq r N n)))) :=
    realSub_split (geomRlimSeq r N m) L (geomRlimSeq r N n)
  have h1 : rLe (rabs (realAdd (geomRlimSeq r N m) (realNeg (geomRlimSeq r N n))))
      (realAdd (rabs (realAdd (geomRlimSeq r N m) (realNeg L)))
        (rabs (realAdd L (realNeg (geomRlimSeq r N n))))) :=
    rLe_trans (rLe_of_realEq (rabs_congr hsplit))
      (rabs_triangle (realAdd (geomRlimSeq r N m) (realNeg L))
        (realAdd L (realNeg (geomRlimSeq r N n))))
  -- 右辺の合成と埋め込みの加法性
  have h2 : rLe (realAdd (rabs (realAdd (geomRlimSeq r N m) (realNeg L)))
        (rabs (realAdd L (realNeg (geomRlimSeq r N n)))))
      (realAdd (qToReal (qFrac 1 m)) (qToReal (qFrac 1 n))) :=
    rLe_add_pair hm hn'
  have h3 : rLe (realAdd (qToReal (qFrac 1 m)) (qToReal (qFrac 1 n)))
      (qToReal (qAdd (qFrac 1 m) (qFrac 1 n))) :=
    rLe_of_realEq (qToReal_add (qFrac 1 m) (qFrac 1 n))
  exact rLe_trans h1 (rLe_trans h2 h3)

/-- **定理 (M185F-4b, 本丸): 加速部分列の正則性** —
    IsCauchyReals (geomRlimSeq r N)。M185F-4a の単一 rLe を M185F-2 で
    一度だけ点ごと展開し、u_m + u_n + 2u_j 予算に正確に着地。
    極限対象 L は ∃（M184-4）から obtain で受ける（Prop ゴールなので
    choice 不要）。 -/
theorem geom_seq_isCauchy (r : RReal) (N : Nat)
    (hb : rLe (rabs r) (qToReal (qFrac N N))) (hN : 1 ≤ N) :
    IsCauchyReals (geomRlimSeq r N) := by
  obtain ⟨L, _, hconv⟩ := geom_converges_self_contained r N hb hN
  intro m n j
  exact rabs_sub_pointwise (geomRlimSeq r N m) (geomRlimSeq r N n)
    (qAdd (qUnitFrac m) (qUnitFrac n))
    (geom_seq_diff_bound r L N hconv m n) j

/-! ## M185F-5: 主定理 -/

/-- **定理 (M185F-5, 主定理): rlim 完備化** — |r| ≤ N/(N+1)（1 ≤ N）
    のみから、極限対象 L（(1⊖r)⁻¹）が存在して、加速部分和列の
    構成的対角極限（M128 rlim）が L に realEq で一致する:
    rlim (geomRlimSeq r N) ≈ L。証明は rlim_unique（M128-5）に
    M185F-3b の収束 witness を渡すだけ。代数（逆元）と位相（完備化）の
    同一性の確定。 -/
theorem geom_rlim_complete (r : RReal) (N : Nat)
    (hb : rLe (rabs r) (qToReal (qFrac N N))) (hN : 1 ≤ N) :
    ∃ L : RReal,
      realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
        (qToReal ratRing.one) ∧
      realEq (rlim (geomRlimSeq r N) (geom_seq_isCauchy r N hb hN)) L := by
  obtain ⟨L, hL, hconv⟩ := geom_converges_self_contained r N hb hN
  refine ⟨L, hL, ?_⟩
  exact rlim_unique (geomRlimSeq r N) (geom_seq_isCauchy r N hb hN) L
    (geom_rlim_converges_witness r L N hconv)

/-! ## M185F-6: 総括 -/

/-- **M185F-6a: 総括** — 幾何級数の rlim 完備化データ。 -/
structure GeomRlimData where
  /-- 点ごと展開の核: rLe |X ⊖ L| ≤ B↑ ⟹ ∀j, |X_j − L_j| ≤ B + 2u_j。 -/
  pointwise : ∀ (X L : RReal) (B : QRat),
    rLe (rabs (realAdd X (realNeg L))) (qToReal B) →
    ∀ j, qLe (qAbs (qAdd (X.seq j) (qNeg (L.seq j))))
      (qAdd B (qAdd (qUnitFrac j) (qUnitFrac j)))
  /-- 加速部分列の正則性: IsCauchyReals (geomRlimSeq r N)。 -/
  cauchy : ∀ (r : RReal) (N : Nat),
    rLe (rabs r) (qToReal (qFrac N N)) → 1 ≤ N →
    IsCauchyReals (geomRlimSeq r N)
  /-- 完備化の一致: 対角極限 rlim (geomRlimSeq r N) は代数的逆元
      L = (1⊖r)⁻¹ に realEq で一致する。 -/
  complete : ∀ (r : RReal) (N : Nat)
    (hb : rLe (rabs r) (qToReal (qFrac N N))) (hN : 1 ≤ N),
    ∃ L : RReal,
      realEq (rmul (realAdd (qToReal ratRing.one) (realNeg r)) L)
        (qToReal ratRing.one) ∧
      realEq (rlim (geomRlimSeq r N) (geom_seq_isCauchy r N hb hN)) L

/-- **M185F-6b: witness**。 -/
def geomRlimData : GeomRlimData where
  pointwise := rabs_sub_pointwise
  cauchy := geom_seq_isCauchy
  complete := geom_rlim_complete

/-- **M185F-6c: 存在** — 幾何級数 rlim 完備化の certification。 -/
theorem geomRlim_exists : Nonempty GeomRlimData := ⟨geomRlimData⟩

end IUT
