/-
  IUT/PolyFieldDivision.lean — M268F（体上の多項式: 本物の除法定理・
  剰余の一意性・体の整域性）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明）。

  **complete_pct 影響**: 柱A「実 Galois 理論」の本物の先行建設。
  体係数の除法定理は最小多項式・分離性・PID/ユークリッド整域の前提で、
  **先頭係数の逆元**（一般の可換環では存在しない）を本質的に使う点が
  体固有である。既存 `FactorTheorem`（M96）は一般可換環 + 零因子なしの
  下で**一次因数 (X−r) による除算**と根の個数 ≤ 次数を扱うが、
  本層は**任意の非零多項式 g（先頭係数 g_m ≠ 0、モニックとは限らない）**
  による除法を扱い、これは体でしか成立しない（既存 `PolyDivision`(M152F)
  は g がモニック = g_p = 1 の場合の一般環除法で、体構造を使わない）。

  * M268F-1 `Field268` — 体（inv を持ち a≠0 で a·a⁻¹=1 を満たす可換環）
  * M268F-2 `mul_eq_zero_left268` — **体は整域**: a·b=0, b≠0 ⇒ a=0
    （b⁻¹ を掛けて消す。零因子なしの本物・体固有）
  * M268F-3 `psMul_single_coeff268` — 単項式 × g の係数公式（一般 g）
  * M268F-4 `sub_top_bounded268` — **頂点消去（体固有）**: 先頭係数の
    逆元 (w_{N+m}·g_m⁻¹)·Y^N·g を引くと上界が一段下がる。
    j=N+m での打ち消しに **g_m⁻¹·g_m = 1**（mul_inv_cancel）を使う
  * M268F-5 `field_division_exists` — **除法定理（本丸・体固有）**:
    任意 w（N+m 有界）と g（m+1 有界・g_m≠0）に対し
    ∃ q(N+1 有界) r(m 有界), w = q·g + r（deg r < deg g）。次数超過分 N
    の帰納で明示構成（選択公理不要・witness は各段で構成）
  * M268F-6 `psMul_g_top_coeff268` / `poly_mul_g_bounded_zero268` —
    正則性の一般化（g_m≠0 + 整域性で w=0）
  * M268F-7 `field_division_unique` — **剰余の一意性（体固有）**: 商・
    剰余は一意（整域性が本質。一般環では成立しない）
  * M268F-8 `field_division_exists_unique` — 存在 + 一意性の完結
  * M268F-9 `PolyDivFieldData` / `polyDivFieldWitness` /
    `polyDivField_exists` — capstone

  意義: K[X] がユークリッド整域（除法定理）かつ剰余が一意という
  両輪は、最小多項式の存在・分離性・Galois 理論の代数的基盤。

  正直な限定:
   - 多項式は有限台の係数列（PS = ℕ→K）として扱い、次数は明示上界
     パラメータとして受け取る（有限台性からの次数抽出は行わない）。
   - **根の重複度**（(X−a)^m ∣ f の最大 m）と **gcd/ユークリッド互除法**
     は本層に含めない（除法定理を土台に次層）。既存 M96 の一次因数分解
     （pEval 表現）との橋渡し（剰余 = 評価値）も別表現のため未実施。
   - 体 K は仮説パラメータ（`Field268`）として受け取る。具体体
     （ℤ/p 等）が体である証明は別途。

  全て選択公理不使用（Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyDivision
import IUT.Binomial2
import IUT.LubinTateZp

namespace IUT

/-! ## M268F-1: 体 -/

/-- **M268F-1: 体** — 逆元函数 `invf` を持ち、非零元 a で a·a⁻¹ = 1 を
    満たす可換環。M264F 等と衝突しない自前定義（親が統合時に統一）。 -/
structure Field268 where
  ring : CRing
  invf : ring.carrier → ring.carrier
  mul_inv_cancel : ∀ a, a ≠ ring.zero → ring.mul a (invf a) = ring.one

/-! ## M268F-2: 体は整域（本物・体固有） -/

/-- **定理 (M268F-2): 体は零因子を持たない** — a·b = 0 かつ b ≠ 0 なら
    a = 0。b⁻¹ を右から掛けて a = (a·b)·b⁻¹ = 0·b⁻¹ = 0。
    **先頭係数の逆元による消去**の原型で、一般の可換環では成立しない。 -/
theorem mul_eq_zero_left268 (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    {a b : R.carrier} (hb : b ≠ R.zero) (hab : R.mul a b = R.zero) :
    a = R.zero := by
  have hbi : R.mul b (invf b) = R.one := hinv b hb
  have hstep : a = R.mul (R.mul a b) (invf b) := by
    rw [R.mul_assoc, hbi, CRing.mul_one R a]
  rw [hstep, hab]
  exact CRing.zero_mul R (invf b)

/-! ## M268F-3: 単項式 × g の係数公式（一般 g） -/

/-- **M268F-3: 単項式 × g の係数** — (c·Y^k · g)_j は k ≤ j なら
    c·g_{j−k}、k > j なら 0。Cauchy 和のうち i = k の項だけが
    psSingle の台で残る（rsum_single_middle）。 -/
theorem psMul_single_coeff268 (R : CRing) (c : R.carrier) (k : Nat)
    (g : PS R) :
    ∀ j, psMul R (psSingle R c k) g j
      = if k ≤ j then R.mul c (g (j - k)) else R.zero := by
  intro j
  show rsum R (fun i => R.mul (psSingle R c k i) (g (j - i))) (j + 1)
    = if k ≤ j then R.mul c (g (j - k)) else R.zero
  cases Nat.lt_or_ge j k with
  | inl hlt =>
    rw [if_neg (by omega)]
    have hz : rsum R (fun i => R.mul (psSingle R c k i) (g (j - i))) (j + 1)
        = rsum R (fun _ => R.zero) (j + 1) :=
      rsum_congr R (j + 1) (fun i hi => by
        show R.mul (psSingle R c k i) (g (j - i)) = R.zero
        rw [show psSingle R c k i = R.zero from if_neg (by omega)]
        exact CRing.zero_mul R _)
    rw [hz]
    exact rsum_const_zero R (j + 1)
  | inr hge =>
    rw [if_pos hge]
    have hmid : rsum R
        (fun i => R.mul (psSingle R c k i) (g (j - i))) (j + 1)
        = R.mul (psSingle R c k k) (g (j - k)) :=
      rsum_single_middle R
        (fun i => R.mul (psSingle R c k i) (g (j - i))) k (j + 1)
        (fun i _ hik => by
          show R.mul (psSingle R c k i) (g (j - i)) = R.zero
          rw [show psSingle R c k i = R.zero from if_neg hik]
          exact CRing.zero_mul R _)
        (by omega)
    rw [hmid, show psSingle R c k k = c from if_pos rfl]

/-! ## M268F-4: 頂点消去（体固有） -/

/-- **M268F-4: 頂点消去（先頭係数の逆元）** — w が N+m+1 で有界なら、
    先頭項 (w_{N+m}·g_m⁻¹)·Y^N·g を引いた差は N+m で有界。
    j = N+m では **g_m⁻¹·g_m = 1**（mul_inv_cancel、体固有）で
    w_{N+m} が打ち消し、j > N+m では w も単項式積も台の外で消える。
    一般環では g_m の逆元が無いためこの一手が打てない。 -/
theorem sub_top_bounded268 (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    (g : PS R) (m : Nat) (hg : IsPolyBounded R g (m + 1))
    (hlead : g m ≠ R.zero) (w : PS R) (N : Nat)
    (hw : IsPolyBounded R w (N + m + 1)) :
    IsPolyBounded R
      (psAdd R w (psNeg R (psMul R
        (psSingle R (R.mul (w (N + m)) (invf (g m))) N) g))) (N + m) := by
  intro j hj
  show R.add (w j) (R.neg (psMul R
      (psSingle R (R.mul (w (N + m)) (invf (g m))) N) g j)) = R.zero
  rw [psMul_single_coeff268 R (R.mul (w (N + m)) (invf (g m))) N g j]
  cases Nat.lt_or_ge j (N + m + 1) with
  | inl hlt =>
    have hje : j = N + m := by omega
    subst hje
    rw [if_pos (Nat.le_add_right N m), show N + m - N = m from by omega]
    have hcancel : R.mul (invf (g m)) (g m) = R.one := by
      rw [R.mul_comm]
      exact hinv (g m) hlead
    have hcg : R.mul (R.mul (w (N + m)) (invf (g m))) (g m) = w (N + m) := by
      rw [R.mul_assoc, hcancel]
      exact CRing.mul_one R (w (N + m))
    rw [hcg]
    exact CRing.add_neg R (w (N + m))
  | inr hge =>
    rw [hw j hge, if_pos (show N ≤ j from by omega),
      hg (j - N) (by omega),
      CRing.mul_zero R (R.mul (w (N + m)) (invf (g m))),
      CRing.neg_zero R, R.zero_add]

/-! ## M268F-5: 除法定理（本丸・体固有） -/

/-- **定理 (M268F-5): 体上の多項式除法（存在）** — 任意の w（N+m 有界）
    と g（m+1 有界・先頭係数 g_m ≠ 0）に対し、q（N+1 有界）と r（m 有界、
    すなわち deg r < deg g）が存在して **w = q·g + r**。次数超過分 N の
    帰納: N=0 は q=0・r=w、N+1 は頂点消去（M268F-4）で上界を下げ、
    商を q = q' + (w_{N+m}·g_m⁻¹)·Y^N と積み上げる。witness は各段で
    明示構成（選択公理不要）。**g がモニックでない一般の非零多項式でも
    割れる**のが体固有（先頭係数の逆元を使う）。 -/
theorem field_division_exists (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    (g : PS R) (m : Nat) (hg : IsPolyBounded R g (m + 1))
    (hlead : g m ≠ R.zero) :
    ∀ (N : Nat) (w : PS R), IsPolyBounded R w (N + m) →
    ∃ (q r : PS R), IsPolyBounded R q (N + 1) ∧ IsPolyBounded R r m ∧
      ∀ j, w j = psAdd R (psMul R q g) r j := by
  intro N
  induction N with
  | zero =>
    intro w hw
    refine ⟨psZero R, w, ?_, ?_, ?_⟩
    · intro i _
      rfl
    · intro i hi
      exact hw i (by omega)
    · intro j
      show w j = R.add (psMul R (psZero R) g j) (w j)
      have hz : psMul R (psZero R) g j = R.zero := by
        show rsum R (fun i => R.mul (psZero R i) (g (j - i))) (j + 1) = R.zero
        have hc : rsum R (fun i => R.mul (psZero R i) (g (j - i))) (j + 1)
            = rsum R (fun _ => R.zero) (j + 1) :=
          rsum_congr R (j + 1) (fun i _ => CRing.zero_mul R _)
        rw [hc]
        exact rsum_const_zero R (j + 1)
      rw [hz, R.zero_add]
  | succ N ih =>
    intro w hw
    have hw' : IsPolyBounded R w (N + m + 1) := by
      intro i hi
      exact hw i (by omega)
    have hsub := sub_top_bounded268 R invf hinv g m hg hlead w N hw'
    obtain ⟨q', r', hq', hr', heq'⟩ := ih _ hsub
    refine ⟨psAdd R q' (psSingle R (R.mul (w (N + m)) (invf (g m))) N),
      r', ?_, hr', ?_⟩
    · intro i hi
      show R.add (q' i)
        (psSingle R (R.mul (w (N + m)) (invf (g m))) N i) = R.zero
      rw [hq' i (by omega),
        show psSingle R (R.mul (w (N + m)) (invf (g m))) N i = R.zero
          from if_neg (by omega),
        R.zero_add]
    · intro j
      show w j = R.add
        (psMul R (psAdd R q'
          (psSingle R (R.mul (w (N + m)) (invf (g m))) N)) g j) (r' j)
      have h1 : R.add (w j)
          (R.neg (psMul R
            (psSingle R (R.mul (w (N + m)) (invf (g m))) N) g j))
          = R.add (psMul R q' g j) (r' j) := heq' j
      have hdist : psMul R (psAdd R q'
          (psSingle R (R.mul (w (N + m)) (invf (g m))) N)) g j
          = R.add (psMul R q' g j)
            (psMul R (psSingle R (R.mul (w (N + m)) (invf (g m))) N) g j) := by
        show rsum R (fun i => R.mul
            (R.add (q' i) (psSingle R (R.mul (w (N + m)) (invf (g m))) N i))
            (g (j - i))) (j + 1)
          = R.add
            (rsum R (fun i => R.mul (q' i) (g (j - i))) (j + 1))
            (rsum R (fun i => R.mul
              (psSingle R (R.mul (w (N + m)) (invf (g m))) N i)
              (g (j - i))) (j + 1))
        rw [← rsum_add R _ _ (j + 1)]
        exact rsum_congr R (j + 1) (fun i _ =>
          CRing.right_distrib R (q' i)
            (psSingle R (R.mul (w (N + m)) (invf (g m))) N i) (g (j - i)))
      calc w j
          = R.add (R.add (w j)
              (R.neg (psMul R
                (psSingle R (R.mul (w (N + m)) (invf (g m))) N) g j)))
              (psMul R (psSingle R (R.mul (w (N + m)) (invf (g m))) N) g j) := by
            rw [R.add_assoc, R.neg_add, CRing.add_zero R]
        _ = R.add (R.add (psMul R q' g j) (r' j))
              (psMul R (psSingle R (R.mul (w (N + m)) (invf (g m))) N) g j) := by
            rw [h1]
        _ = R.add (R.add (psMul R q' g j)
              (psMul R (psSingle R (R.mul (w (N + m)) (invf (g m))) N) g j))
              (r' j) := by
            rw [R.add_assoc, R.add_comm (r' j)
              (psMul R (psSingle R (R.mul (w (N + m)) (invf (g m))) N) g j),
              ← R.add_assoc]
        _ = R.add (psMul R (psAdd R q'
              (psSingle R (R.mul (w (N + m)) (invf (g m))) N)) g j) (r' j) := by
            rw [hdist]

/-! ## M268F-6: 積の正則性（g_m ≠ 0 + 整域性） -/

/-- **M268F-6a: 積の頂点係数** — w が M+1 で有界なら (w·g)_{M+m} = w_M·g_m。
    Cauchy 和のうち i>M は w の有界性、i<M は g の添字が m+1 以上で
    台の外、i=M の中央項だけ残る。 -/
theorem psMul_g_top_coeff268 (R : CRing) (g : PS R) (m : Nat)
    (hg : IsPolyBounded R g (m + 1)) (w : PS R) (M : Nat)
    (hw : ∀ i, M + 1 ≤ i → w i = R.zero) :
    psMul R w g (M + m) = R.mul (w M) (g m) := by
  show rsum R (fun i => R.mul (w i) (g (M + m - i))) (M + m + 1)
    = R.mul (w M) (g m)
  have hmid : rsum R (fun i => R.mul (w i) (g (M + m - i))) (M + m + 1)
      = R.mul (w M) (g (M + m - M)) :=
    rsum_single_middle R (fun i => R.mul (w i) (g (M + m - i))) M (M + m + 1)
      (fun i _ hiM => by
        cases Nat.lt_or_ge i M with
        | inl hlt =>
          show R.mul (w i) (g (M + m - i)) = R.zero
          rw [hg (M + m - i) (by omega), CRing.mul_zero R (w i)]
        | inr hge =>
          show R.mul (w i) (g (M + m - i)) = R.zero
          rw [hw i (by omega), CRing.zero_mul R (g (M + m - i))])
      (by omega)
  rw [hmid, show M + m - M = m from by omega]

/-- **定理 (M268F-6b): 積の正則性** — w が有界で、積 w·g の次数 ≥ m 部分が
    全部 0 なら w = 0。上界の下向き帰納: 頂点係数 w_M·g_m = (w·g)_{M+m} = 0
    に **整域性**（M268F-2、g_m ≠ 0）を当てて w_M = 0、上界を一段下げる。 -/
theorem poly_mul_g_bounded_zero268 (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    (g : PS R) (m : Nat) (hg : IsPolyBounded R g (m + 1))
    (hlead : g m ≠ R.zero) (w : PS R) (N : Nat)
    (hw : IsPolyBounded R w N)
    (hlow : ∀ j, m ≤ j → psMul R w g j = R.zero) :
    ∀ i, w i = R.zero := by
  revert hw
  induction N with
  | zero =>
    intro hw i
    exact hw i (Nat.zero_le i)
  | succ M ih =>
    intro hw
    have hM : w M = R.zero := by
      have h1 : psMul R w g (M + m) = R.mul (w M) (g m) :=
        psMul_g_top_coeff268 R g m hg w M (fun i hi => hw i hi)
      have h2 : R.mul (w M) (g m) = R.zero := by
        rw [← h1]
        exact hlow (M + m) (by omega)
      exact mul_eq_zero_left268 R invf hinv hlead h2
    apply ih
    intro i hi
    cases Nat.lt_or_ge i (M + 1) with
    | inl hlt =>
      rw [show i = M from by omega]
      exact hM
    | inr hge => exact hw i hge

/-! ## M268F-7: 剰余の一意性（体固有） -/

/-- **定理 (M268F-7): 剰余の一意性** — q·g + r = q'·g + r'（q,q' 有界、
    r,r' は deg < m）なら q = q' かつ r = r'。差 w = q − q' に正則性
    （M268F-6b）を適用: (w·g)_j (j ≥ m) は r'−r の係数で、deg < m により 0。
    **整域性が本質**で、一般環では一意性は崩れる（体固有）。 -/
theorem field_division_unique (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    (g : PS R) (m : Nat) (hg : IsPolyBounded R g (m + 1))
    (hlead : g m ≠ R.zero)
    (q q' r r' : PS R) (Nq Nq' : Nat)
    (hq : IsPolyBounded R q Nq) (hq' : IsPolyBounded R q' Nq')
    (hr : IsPolyBounded R r m) (hr' : IsPolyBounded R r' m)
    (heq : ∀ j, psAdd R (psMul R q g) r j = psAdd R (psMul R q' g) r' j) :
    (∀ i, q i = q' i) ∧ (∀ i, r i = r' i) := by
  have hwb : IsPolyBounded R (psAdd R q (psNeg R q')) (Nq + Nq') := by
    intro i hi
    show R.add (q i) (R.neg (q' i)) = R.zero
    rw [hq i (by omega), hq' i (by omega), CRing.neg_zero R, R.zero_add]
  have hsum : ∀ j,
      R.add (psMul R (psAdd R q (psNeg R q')) g j) (psMul R q' g j)
      = psMul R q g j := by
    intro j
    show R.add
        (rsum R (fun k => R.mul (psAdd R q (psNeg R q') k) (g (j - k))) (j + 1))
        (rsum R (fun k => R.mul (q' k) (g (j - k))) (j + 1))
      = rsum R (fun k => R.mul (q k) (g (j - k))) (j + 1)
    rw [← rsum_add R _ _ (j + 1)]
    exact rsum_congr R (j + 1) (fun k _ => by
      show R.add
          (R.mul (psAdd R q (psNeg R q') k) (g (j - k)))
          (R.mul (q' k) (g (j - k)))
        = R.mul (q k) (g (j - k))
      rw [← CRing.right_distrib R]
      have hkey : R.add (psAdd R q (psNeg R q') k) (q' k) = q k := by
        show R.add (R.add (q k) (R.neg (q' k))) (q' k) = q k
        rw [R.add_assoc, R.neg_add, CRing.add_zero R]
      rw [hkey])
  have hwlow : ∀ j, m ≤ j →
      psMul R (psAdd R q (psNeg R q')) g j = R.zero := by
    intro j hj
    have hqg : psMul R q g j = psMul R q' g j := by
      have h2 : R.add (psMul R q g j) (r j)
          = R.add (psMul R q' g j) (r' j) := heq j
      rw [hr j hj, hr' j hj, CRing.add_zero R, CRing.add_zero R] at h2
      exact h2
    have h3 : R.add (psMul R q' g j)
        (psMul R (psAdd R q (psNeg R q')) g j)
        = R.add (psMul R q' g j) R.zero := by
      rw [CRing.add_zero R,
        R.add_comm (psMul R q' g j)
          (psMul R (psAdd R q (psNeg R q')) g j),
        hsum j]
      exact hqg
    exact CRing.add_left_cancel R h3
  have hw0 : ∀ i, psAdd R q (psNeg R q') i = R.zero :=
    poly_mul_g_bounded_zero268 R invf hinv g m hg hlead
      (psAdd R q (psNeg R q')) (Nq + Nq') hwb hwlow
  have hqq : ∀ i, q i = q' i := by
    intro i
    have h' : R.add (q i) (R.neg (q' i)) = R.zero := hw0 i
    exact CRing.eq_of_sub_eq_zero R h'
  have hmul : ∀ j, psMul R q g j = psMul R q' g j := by
    intro j
    show rsum R (fun k => R.mul (q k) (g (j - k))) (j + 1)
      = rsum R (fun k => R.mul (q' k) (g (j - k))) (j + 1)
    exact rsum_congr R (j + 1) (fun k _ => by rw [hqq k])
  refine ⟨hqq, ?_⟩
  intro j
  have h2 : R.add (psMul R q g j) (r j)
      = R.add (psMul R q' g j) (r' j) := heq j
  rw [hmul j] at h2
  exact CRing.add_left_cancel R h2

/-! ## M268F-8: 存在 + 一意性の完結 -/

/-- **定理 (M268F-8): 体上多項式除法の完結（存在 + 一意）** — 存在
    （M268F-5）と剰余の一意性（M268F-7）を一本化。K[X] が deg r < deg g
    の剰余表現を存在・一意に持つ（ユークリッド整域の除法）。 -/
theorem field_division_exists_unique (K : Field268)
    (g : PS K.ring) (m : Nat) (hg : IsPolyBounded K.ring g (m + 1))
    (hlead : g m ≠ K.ring.zero) (N : Nat) (w : PS K.ring)
    (hw : IsPolyBounded K.ring w (N + m)) :
    ∃ (q r : PS K.ring), IsPolyBounded K.ring q (N + 1) ∧
      IsPolyBounded K.ring r m ∧
      (∀ j, w j = psAdd K.ring (psMul K.ring q g) r j) ∧
      (∀ (q₂ r₂ : PS K.ring) (Nq₂ : Nat), IsPolyBounded K.ring q₂ Nq₂ →
        IsPolyBounded K.ring r₂ m →
        (∀ j, w j = psAdd K.ring (psMul K.ring q₂ g) r₂ j) →
        (∀ i, q i = q₂ i) ∧ (∀ i, r i = r₂ i)) := by
  obtain ⟨q, r, hq, hr, heq⟩ :=
    field_division_exists K.ring K.invf K.mul_inv_cancel g m hg hlead N w hw
  refine ⟨q, r, hq, hr, heq, ?_⟩
  intro q₂ r₂ Nq₂ hq₂ hr₂ heq₂
  exact field_division_unique K.ring K.invf K.mul_inv_cancel g m hg hlead
    q q₂ r r₂ (N + 1) Nq₂ hq hq₂ hr hr₂
    (fun j => (heq j).symm.trans (heq₂ j))

/-! ## M268F-9: capstone -/

/-- **M268F-9: 体上多項式除法データ** — 任意の体 K・非零多項式 g に対する
    除法（存在）を束ねる。 -/
structure PolyDivFieldData where
  divmod : ∀ (K : Field268) (g : PS K.ring) (m : Nat),
    IsPolyBounded K.ring g (m + 1) → g m ≠ K.ring.zero →
    ∀ (N : Nat) (w : PS K.ring), IsPolyBounded K.ring w (N + m) →
    ∃ (q r : PS K.ring), IsPolyBounded K.ring q (N + 1) ∧
      IsPolyBounded K.ring r m ∧
      ∀ j, w j = psAdd K.ring (psMul K.ring q g) r j

/-- 証人: M268F-5 をそのまま束ねる。 -/
def polyDivFieldWitness : PolyDivFieldData where
  divmod := fun K g m hg hlead N w hw =>
    field_division_exists K.ring K.invf K.mul_inv_cancel g m hg hlead N w hw

/-- **見出し (M268F): 体上多項式除法データの存在**。 -/
theorem polyDivField_exists : Nonempty PolyDivFieldData :=
  ⟨polyDivFieldWitness⟩

end IUT
