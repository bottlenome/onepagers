/-
  IUT/FormalGroupPoints.lean — M77（冪級数の点での評価:
  点の群キャンペーン第一層）

  形式群の「点の群」F(pℤ_p) の実体化に向けた第一歩として、
  **冪級数 F ∈ ℤ_p[[X]] の点 x ∈ pℤ_p での値 F(x) ∈ ℤ_p** を
  choice なしで構成する。鍵: x = p·e のとき x^k ≡ 0 (mod p^k) なので
  **レベル m の成分は部分和 Σ_{k<m} F_k x^k だけで決まる**（無限和・
  完備性の一般論を持ち出さず逆極限の成分ごとに定義できる）。

  * M77-1 `rsum_split` — 有限和の分割 Σ_{<i+d} = Σ_{<i} + Σ_{i≤·<i+d}
    （新しい和の道具）
  * M77-2 `int_rpow_p_dvd` / `proj_rpow_p_zero` — p^i ∣ p^i（環冪の
    Int 表示）とレベル i での p^i の消滅
  * M77-3 `zpEvalSeg` — 部分和 Σ_{k<N} F_k x^k ∈ ℤ_p（rsum を
    係数環 zpRing 自身で使う）
  * M77-4 `zpEvalSeg_stable` — **安定性**: i ≤ j ⟹ レベル i では
    Σ_{<j} = Σ_{<i}（尻尾 = p^i·(何か) をレベル i が殺す）
  * M77-5 `zpEval` — **評価の本体** F(x) ∈ ℤ_p（成分 n = 部分和
    Σ_{<n} のレベル n 射影、整合性は安定性から）
  * M77-6 `zpEval_zero` / `zpEval_const` / `zpEval_X` / `zpEval_add` —
    0(x) = 0・c(x) = c・X(x) = x・(F+G)(x) = F(x)+G(x)

  乗法 (F·G)(x) = F(x)·G(x)・合成との両立 (F∘G)(x) = F(G(x))・
  点の群 F(pℤ_p) の群法則・[πⁿ]-捻れは次層以降。
  全て選択公理不使用。
-/
import IUT.FormalGroupOModule

namespace IUT

/-! ## 有限和の分割 -/

/-- **M77-1: 有限和の分割** — Σ_{<i+d} g = Σ_{<i} g + Σ_{k<d} g(i+k)。 -/
theorem rsum_split (R : CRing) (g : Nat → R.carrier) (i : Nat) :
    ∀ d, rsum R g (i + d)
      = R.add (rsum R g i) (rsum R (fun k => g (i + k)) d) := by
  intro d
  induction d with
  | zero => exact (CRing.add_zero R _).symm
  | succ d ih =>
    show R.add (rsum R g (i + d)) (g (i + d))
      = R.add (rsum R g i)
          (R.add (rsum R (fun k => g (i + k)) d) (g (i + d)))
    rw [ih, R.add_assoc]

/-! ## p^i のレベル i 消滅 -/

/-- **M77-2a: Int 冪の p^i 因子**（M29 の ipow、構成的 witness）。 -/
theorem int_ipow_p_dvd (p : Nat) : ∀ i, ∃ c : Int,
    ipow ((p : Nat) : Int) i = ((p ^ i : Nat) : Int) * c := by
  intro i
  induction i with
  | zero =>
    refine ⟨1, ?_⟩
    show (1 : Int) = ((1 : Nat) : Int) * 1
    omega
  | succ i ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c, ?_⟩
    show ipow ((p : Nat) : Int) i * ((p : Nat) : Int)
      = ((p ^ (i + 1) : Nat) : Int) * c
    rw [hc, Nat.pow_succ, Int.natCast_mul, Int.mul_assoc,
      Int.mul_comm c ((p : Nat) : Int), ← Int.mul_assoc]

/-- ℤ/m の環冪は代表元の ipow（Quot.mk と rpow の交換）。 -/
theorem zmod_rpow_quot (m : Nat) (z : Int) : ∀ k,
    rpow (zmodRing m) (Quot.mk (modCong m).rel z) k
      = Quot.mk (modCong m).rel (ipow z k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (zmodRing m).mul
        (rpow (zmodRing m) (Quot.mk (modCong m).rel z) k)
        (Quot.mk (modCong m).rel z)
      = Quot.mk (modCong m).rel (ipow z k * z)
    rw [ih]
    rfl

/-- **M77-2b: レベル i での p^i の消滅** —
    proj_i((p)^i) = 0 in ℤ/p^i。 -/
theorem proj_rpow_p_zero (p i : Nat) :
    (projRing p i).map
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) i)
      = (zmodRing (p ^ i)).zero := by
  rw [ringHom_rpow (projRing p i) ((toZp p).map ((p : Nat) : Int)) i]
  show rpow (zmodRing (p ^ i))
      (Quot.mk (modCong (p ^ i)).rel ((p : Nat) : Int)) i
    = (zmodRing (p ^ i)).zero
  rw [zmod_rpow_quot (p ^ i) ((p : Nat) : Int) i]
  show Quot.mk (modCong (p ^ i)).rel (ipow ((p : Nat) : Int) i)
    = Quot.mk (modCong (p ^ i)).rel 0
  apply Quot.sound
  obtain ⟨c, hc⟩ := int_ipow_p_dvd p i
  show ((p ^ i : Nat) : Int) ∣ ipow ((p : Nat) : Int) i - 0
  refine ⟨c, ?_⟩
  generalize hW : ((p ^ i : Nat) : Int) * c = W
  rw [hW] at hc
  omega

/-! ## 部分和と安定性 -/

/-- **M77-3: 部分和** Σ_{k<N} F_k·x^k ∈ ℤ_p。 -/
def zpEvalSeg (p : Nat) (F : PS (zpRing p)) (x : (Zp p).carrier)
    (N : Nat) : (Zp p).carrier :=
  rsum (zpRing p) (fun k => (zpRing p).mul (F k) (rpow (zpRing p) x k)) N

/-- 積の左因子の引き出し a·((b·c)·d) = b·(a·(c·d))（簿記）。 -/
theorem CRing.mul_pull_left (R : CRing) (a b c d : R.carrier) :
    R.mul a (R.mul (R.mul b c) d) = R.mul b (R.mul a (R.mul c d)) := by
  rw [R.mul_assoc b c d, ← R.mul_assoc a b (R.mul c d), R.mul_comm a b,
    R.mul_assoc b a (R.mul c d)]

/-- **定理 (M77-4): 部分和の安定性** — x = p·e、i ≤ j のとき
    レベル i では Σ_{<j} = Σ_{<i}（尻尾の各項 F_{i+k}·x^{i+k} は
    p^i·(何か) で、レベル i 射影が殺す）。 -/
theorem zpEvalSeg_stable (p : Nat) (F : PS (zpRing p))
    (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e)
    {i j : Nat} (h : i ≤ j) :
    (zpEvalSeg p F x j).val i = (zpEvalSeg p F x i).val i := by
  obtain ⟨d, hd⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  subst hd
  -- 尻尾の各項から p^i を括り出す
  have hterm : ∀ k, k < d →
      (zpRing p).mul (F (i + k)) (rpow (zpRing p) x (i + k))
      = (zpRing p).mul
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) i)
          ((zpRing p).mul (F (i + k))
            ((zpRing p).mul
              (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k)
              (rpow (zpRing p) e (i + k)))) := by
    intro k _
    rw [hx, rpow_mul_dist (zpRing p) ((toZp p).map ((p : Nat) : Int))
        e (i + k),
      rpow_add (zpRing p) ((toZp p).map ((p : Nat) : Int)) i k]
    exact CRing.mul_pull_left (zpRing p) (F (i + k))
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) i)
      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k)
      (rpow (zpRing p) e (i + k))
  have htail : rsum (zpRing p) (fun k =>
        (zpRing p).mul (F (i + k)) (rpow (zpRing p) x (i + k))) d
      = (zpRing p).mul
          (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) i)
          (rsum (zpRing p) (fun k =>
            (zpRing p).mul (F (i + k))
              ((zpRing p).mul
                (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k)
                (rpow (zpRing p) e (i + k)))) d) :=
    (rsum_congr (zpRing p) d hterm).trans
      ((rsum_mul_left (zpRing p) (fun k =>
          (zpRing p).mul (F (i + k))
            ((zpRing p).mul
              (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) k)
              (rpow (zpRing p) e (i + k))))
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) i) d).symm)
  -- レベル i で射影: p^i 因子が消える
  have hsplit : zpEvalSeg p F x (i + d)
      = (zpRing p).add (zpEvalSeg p F x i)
          (rsum (zpRing p) (fun k =>
            (zpRing p).mul (F (i + k)) (rpow (zpRing p) x (i + k))) d) :=
    rsum_split (zpRing p) _ i d
  show (projRing p i).map (zpEvalSeg p F x (i + d))
    = (projRing p i).map (zpEvalSeg p F x i)
  rw [hsplit, htail, (projRing p i).map_add, (projRing p i).map_mul,
    proj_rpow_p_zero p i, CRing.zero_mul (zmodRing (p ^ i)),
    CRing.add_zero (zmodRing (p ^ i))]

/-! ## 評価の本体 -/

/-- **M77-5: 評価** F(x) ∈ ℤ_p（x = p·e は witness e と等式で受ける
    = choice 不要のデータ渡し。成分 n = Σ_{k<n} F_k x^k のレベル n
    射影、整合性は安定性 M77-4）。 -/
def zpEval (p : Nat) (F : PS (zpRing p)) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    (Zp p).carrier :=
  ⟨fun n => (zpEvalSeg p F x n).val n, by
    intro i j h
    have h1 : (zmodTrans (pow_dvd_mono p h)).map
        ((zpEvalSeg p F x j).val j) = (zpEvalSeg p F x j).val i :=
      (zpEvalSeg p F x j).property h
    show (zmodTrans (pow_dvd_mono p h)).map ((zpEvalSeg p F x j).val j)
      = (zpEvalSeg p F x i).val i
    rw [h1]
    exact zpEvalSeg_stable p F x e hx h⟩

/-! ## 基本値 -/

/-- ℤ/p^0 = ℤ/1 は自明（レベル 0 の値はなんでも一致）。 -/
theorem zmod_pow_zero_eq (p : Nat) (z w : (zmod (p ^ 0)).carrier) :
    z = w := by
  obtain ⟨a, ha⟩ := Quot.exists_rep z
  obtain ⟨b, hb⟩ := Quot.exists_rep w
  rw [← ha, ← hb]
  apply Quot.sound
  show ((p ^ 0 : Nat) : Int) ∣ a - b
  refine ⟨a - b, ?_⟩
  rw [show ((p ^ 0 : Nat) : Int) = (1 : Int) from rfl, Int.one_mul]

/-- **M77-6a: 0 級数の値** 0(x) = 0。 -/
theorem zpEval_zero (p : Nat) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (psZero (zpRing p)) x e hx = (zpRing p).zero := by
  apply Subtype.ext
  funext n
  show (zpEvalSeg p (psZero (zpRing p)) x n).val n
    = ((zpRing p).zero).val n
  have hseg : zpEvalSeg p (psZero (zpRing p)) x n = (zpRing p).zero := by
    show rsum (zpRing p) (fun k =>
        (zpRing p).mul (psZero (zpRing p) k) (rpow (zpRing p) x k)) n
      = (zpRing p).zero
    have hz : rsum (zpRing p) (fun k =>
          (zpRing p).mul (psZero (zpRing p) k) (rpow (zpRing p) x k)) n
        = rsum (zpRing p) (fun _ => (zpRing p).zero) n :=
      rsum_congr (zpRing p) n (fun k _ =>
        (zpRing p).zero_mul (rpow (zpRing p) x k))
    rw [hz]
    exact rsum_const_zero (zpRing p) n
  rw [hseg]

/-- **M77-6b: 定数級数の値** c(x) = c。 -/
theorem zpEval_const (p : Nat) (c x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (psC (zpRing p) c) x e hx = c := by
  apply Subtype.ext
  funext n
  show (zpEvalSeg p (psC (zpRing p) c) x n).val n = c.val n
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ m =>
    have hseg : zpEvalSeg p (psC (zpRing p) c) x (m + 1) = c := by
      have hs : rsum (zpRing p) (fun k =>
            (zpRing p).mul (psC (zpRing p) c k) (rpow (zpRing p) x k))
            (m + 1)
          = (zpRing p).mul (psC (zpRing p) c 0) (rpow (zpRing p) x 0) :=
        rsum_single (zpRing p) (fun k =>
            (zpRing p).mul (psC (zpRing p) c k) (rpow (zpRing p) x k))
          0 (m + 1) (by omega)
          (fun k _ hk => by
            show (zpRing p).mul (psC (zpRing p) c k) (rpow (zpRing p) x k)
              = (zpRing p).zero
            rw [show psC (zpRing p) c k = (zpRing p).zero from if_neg hk]
            exact (zpRing p).zero_mul _)
      show rsum (zpRing p) (fun k =>
          (zpRing p).mul (psC (zpRing p) c k) (rpow (zpRing p) x k))
          (m + 1) = c
      rw [hs, show rpow (zpRing p) x 0 = (zpRing p).one from rfl,
        (zpRing p).mul_comm, (zpRing p).one_mul]
      rfl
    rw [hseg]

/-- **M77-6c: 恒等級数の値** X(x) = x（x ∈ pℤ_p が効く: レベル 1 でも
    部分和 0 と x の成分 0 が一致）。 -/
theorem zpEval_X (p : Nat) (hp : 2 ≤ p) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (psX (zpRing p)) x e hx = x := by
  apply Subtype.ext
  funext n
  show (zpEvalSeg p (psX (zpRing p)) x n).val n = x.val n
  cases n with
  | zero => exact zmod_pow_zero_eq p _ _
  | succ m =>
    cases m with
    | zero =>
      have h1 : zpEvalSeg p (psX (zpRing p)) x 1 = (zpRing p).zero := by
        show (zpRing p).add (zpRing p).zero
            ((zpRing p).mul (psX (zpRing p) 0) (rpow (zpRing p) x 0))
          = (zpRing p).zero
        rw [show psX (zpRing p) 0 = (zpRing p).zero from rfl,
          (zpRing p).zero_mul, (zpRing p).zero_add]
      have hx1 : x.val 1 = Quot.mk (modCong (p ^ 1)).rel 0 :=
        (zp_dvd_p_iff p hp x).mp ⟨e, hx⟩
      rw [h1, hx1]
      rfl
    | succ m' =>
      have hseg : zpEvalSeg p (psX (zpRing p)) x (m' + 2) = x := by
        have hs : rsum (zpRing p) (fun k =>
              (zpRing p).mul (psX (zpRing p) k) (rpow (zpRing p) x k))
              (m' + 2)
            = (zpRing p).mul (psX (zpRing p) 1) (rpow (zpRing p) x 1) :=
          rsum_single (zpRing p) (fun k =>
              (zpRing p).mul (psX (zpRing p) k) (rpow (zpRing p) x k))
            1 (m' + 2) (by omega)
            (fun k _ hk => by
              show (zpRing p).mul (psX (zpRing p) k) (rpow (zpRing p) x k)
                = (zpRing p).zero
              rw [show psX (zpRing p) k = (zpRing p).zero from if_neg hk]
              exact (zpRing p).zero_mul _)
        show rsum (zpRing p) (fun k =>
            (zpRing p).mul (psX (zpRing p) k) (rpow (zpRing p) x k))
            (m' + 2) = x
        rw [hs, show psX (zpRing p) 1 = (zpRing p).one from rfl,
          (zpRing p).one_mul]
        show (zpRing p).mul (rpow (zpRing p) x 0) x = x
        rw [show rpow (zpRing p) x 0 = (zpRing p).one from rfl,
          (zpRing p).one_mul]
      rw [hseg]

/-- **M77-6d: 加法性** (F + G)(x) = F(x) + G(x)（部分和レベルの
    分配 + 射影の加法性）。 -/
theorem zpEval_add (p : Nat) (F G : PS (zpRing p)) (x e : (Zp p).carrier)
    (hx : x = (zpRing p).mul ((toZp p).map ((p : Nat) : Int)) e) :
    zpEval p (psAdd (zpRing p) F G) x e hx
      = (zpRing p).add (zpEval p F x e hx) (zpEval p G x e hx) := by
  apply Subtype.ext
  funext n
  have hseg : zpEvalSeg p (psAdd (zpRing p) F G) x n
      = (zpRing p).add (zpEvalSeg p F x n) (zpEvalSeg p G x n) := by
    show rsum (zpRing p) (fun k =>
        (zpRing p).mul ((zpRing p).add (F k) (G k)) (rpow (zpRing p) x k))
        n = _
    have hc : rsum (zpRing p) (fun k =>
          (zpRing p).mul ((zpRing p).add (F k) (G k))
            (rpow (zpRing p) x k)) n
        = rsum (zpRing p) (fun k =>
            (zpRing p).add
              ((zpRing p).mul (F k) (rpow (zpRing p) x k))
              ((zpRing p).mul (G k) (rpow (zpRing p) x k))) n :=
      rsum_congr (zpRing p) n (fun k _ =>
        (zpRing p).right_distrib (F k) (G k) (rpow (zpRing p) x k))
    rw [hc]
    exact rsum_add (zpRing p) _ _ n
  show (projRing p n).map (zpEvalSeg p (psAdd (zpRing p) F G) x n)
    = (zmodRing (p ^ n)).add
        ((projRing p n).map (zpEvalSeg p F x n))
        ((projRing p n).map (zpEvalSeg p G x n))
  rw [hseg]
  exact (projRing p n).map_add _ _

end IUT
