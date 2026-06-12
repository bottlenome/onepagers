/-
  IUT/FormalGroup3Unique.lean — M66（三変数の対角分離と一意性: 結合則キャンペーン第四層）

  M59（対角分離）+ M61（一意性）の三変数版。

  * M66-1 `lt3_rhs_split` — **対角分離**: G と G' が総次数 < i+k+j で
    一致するとき RHS(G)_{j,k,i} = RHS(G')_{j,k,i}
    + (G_{j,k,i}·C − G'_{j,k,i}·C)、C = (f^i)_i·(f^k)_k·(f^j)_j。
    三重一点差分（rsum_single_diff ×3 + add_add_neg_cancel ×2）。
    残余項は「< n は合同・≥ n は三因子のどれかが対角下消滅」の四分
  * M66-2 `lt3_unique` — **三変数一意性**: IsLTFormalGroup3 p G ∧
    IsLTFormalGroup3 p G' ⟹ G = G'（総次数強帰納法 + M42 の
    zp_lt_cancel — M61 のスキーマがそのまま一添字増えて通る）

  結合則 F(F(X,Y),Z) = F(X,F(Y,Z)) は、両辺がともに
  IsLTFormalGroup3 を満たすこと（次層・合成の連鎖律）と本層の一意性で
  従う。全て選択公理不使用。
-/
import IUT.FormalGroup3Decomp

namespace IUT

/-! ## 対角分離 -/

/-- **定理 (M66-1): 右辺の対角分離（三変数）** — G と G' が総次数
    < i+k+j で一致するとき、
    RHS(G) = RHS(G') + (G_{j,k,i}·C − G'_{j,k,i}·C)、
    C = ((f^i)_i·(f^k)_k)·(f^j)_j。 -/
theorem lt3_rhs_split (p : Nat) (hp : 2 ≤ p) (G G' : PS3 (zpRing p))
    (j k i : Nat)
    (h : ∀ c b a, a + b + c < i + k + j → G c b a = G' c b a) :
    ps3Comp3 (zpRing p) G (in3X (zpRing p) (ltPoly p))
        (in3Y (zpRing p) (ltPoly p)) (in3Z (zpRing p) (ltPoly p)) j k i
      = (zpRing p).add
          (ps3Comp3 (zpRing p) G' (in3X (zpRing p) (ltPoly p))
            (in3Y (zpRing p) (ltPoly p)) (in3Z (zpRing p) (ltPoly p))
            j k i)
          ((zpRing p).add
            ((zpRing p).mul (G j k i)
              ((zpRing p).mul
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                  (psPow (zpRing p) (ltPoly p) k k))
                (psPow (zpRing p) (ltPoly p) j j)))
            ((zpRing p).neg ((zpRing p).mul (G' j k i)
              ((zpRing p).mul
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                  (psPow (zpRing p) (ltPoly p) k k))
                (psPow (zpRing p) (ltPoly p) j j))))) := by
  have hterm : ∀ c b a, ¬ (c = j ∧ b = k ∧ a = i) →
      (zpRing p).mul (G c b a)
        ((zpRing p).mul
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) b k))
          (psPow (zpRing p) (ltPoly p) c j))
      = (zpRing p).mul (G' c b a)
          ((zpRing p).mul
            ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
              (psPow (zpRing p) (ltPoly p) b k))
            (psPow (zpRing p) (ltPoly p) c j)) := by
    intro c b a hne
    cases Nat.lt_or_ge (a + b + c) (i + k + j) with
    | inl hlt => rw [h c b a hlt]
    | inr hge =>
      cases Nat.lt_or_ge i a with
      | inl hia =>
        rw [ltPow_low p hp a i hia,
          CRing.zero_mul (zpRing p) (psPow (zpRing p) (ltPoly p) b k),
          CRing.zero_mul (zpRing p) (psPow (zpRing p) (ltPoly p) c j),
          CRing.mul_zero (zpRing p) (G c b a),
          CRing.mul_zero (zpRing p) (G' c b a)]
      | inr hai =>
        cases Nat.lt_or_ge k b with
        | inl hkb =>
          rw [ltPow_low p hp b k hkb,
            CRing.mul_zero (zpRing p) (psPow (zpRing p) (ltPoly p) a i),
            CRing.zero_mul (zpRing p) (psPow (zpRing p) (ltPoly p) c j),
            CRing.mul_zero (zpRing p) (G c b a),
            CRing.mul_zero (zpRing p) (G' c b a)]
        | inr hbk =>
          cases Nat.lt_or_ge j c with
          | inl hjc =>
            rw [ltPow_low p hp c j hjc,
              CRing.mul_zero (zpRing p)
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                  (psPow (zpRing p) (ltPoly p) b k)),
              CRing.mul_zero (zpRing p) (G c b a),
              CRing.mul_zero (zpRing p) (G' c b a)]
          | inr hcj =>
            have hc : c = j := by omega
            have hb : b = k := by omega
            have ha : a = i := by omega
            exact absurd ⟨hc, hb, ha⟩ hne
  rw [lt3_rhs_coeff (zpRing p) (ltPoly p) G j k i,
    lt3_rhs_coeff (zpRing p) (ltPoly p) G' j k i]
  have houter : rsum (zpRing p) (fun c => rsum (zpRing p) (fun b =>
        rsum (zpRing p) (fun a => (zpRing p).mul (G c b a)
          ((zpRing p).mul
            ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
              (psPow (zpRing p) (ltPoly p) b k))
            (psPow (zpRing p) (ltPoly p) c j))) (i + k + j + 1))
        (i + k + j + 1)) (i + k + j + 1)
      = (zpRing p).add
          (rsum (zpRing p) (fun c => rsum (zpRing p) (fun b =>
            rsum (zpRing p) (fun a => (zpRing p).mul (G' c b a)
              ((zpRing p).mul
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                  (psPow (zpRing p) (ltPoly p) b k))
                (psPow (zpRing p) (ltPoly p) c j))) (i + k + j + 1))
            (i + k + j + 1)) (i + k + j + 1))
          ((zpRing p).add
            (rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
              (zpRing p).mul (G j b a)
                ((zpRing p).mul
                  ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                    (psPow (zpRing p) (ltPoly p) b k))
                  (psPow (zpRing p) (ltPoly p) j j))) (i + k + j + 1))
              (i + k + j + 1))
            ((zpRing p).neg
              (rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
                (zpRing p).mul (G' j b a)
                  ((zpRing p).mul
                    ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                      (psPow (zpRing p) (ltPoly p) b k))
                    (psPow (zpRing p) (ltPoly p) j j))) (i + k + j + 1))
                (i + k + j + 1)))) :=
    rsum_single_diff (zpRing p)
      (fun c => rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (G c b a)
          ((zpRing p).mul
            ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
              (psPow (zpRing p) (ltPoly p) b k))
            (psPow (zpRing p) (ltPoly p) c j))) (i + k + j + 1))
        (i + k + j + 1))
      (fun c => rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (G' c b a)
          ((zpRing p).mul
            ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
              (psPow (zpRing p) (ltPoly p) b k))
            (psPow (zpRing p) (ltPoly p) c j))) (i + k + j + 1))
        (i + k + j + 1))
      j (i + k + j + 1) (by omega)
      (fun c _ hcne => rsum_congr (zpRing p) (i + k + j + 1)
        (fun b _ => rsum_congr (zpRing p) (i + k + j + 1)
          (fun a _ => hterm c b a (fun hh => hcne hh.1))))
  have hmid : rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (G j b a)
          ((zpRing p).mul
            ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
              (psPow (zpRing p) (ltPoly p) b k))
            (psPow (zpRing p) (ltPoly p) j j))) (i + k + j + 1))
        (i + k + j + 1)
      = (zpRing p).add
          (rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
            (zpRing p).mul (G' j b a)
              ((zpRing p).mul
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                  (psPow (zpRing p) (ltPoly p) b k))
                (psPow (zpRing p) (ltPoly p) j j))) (i + k + j + 1))
            (i + k + j + 1))
          ((zpRing p).add
            (rsum (zpRing p) (fun a => (zpRing p).mul (G j k a)
              ((zpRing p).mul
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                  (psPow (zpRing p) (ltPoly p) k k))
                (psPow (zpRing p) (ltPoly p) j j))) (i + k + j + 1))
            ((zpRing p).neg
              (rsum (zpRing p) (fun a => (zpRing p).mul (G' j k a)
                ((zpRing p).mul
                  ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                    (psPow (zpRing p) (ltPoly p) k k))
                  (psPow (zpRing p) (ltPoly p) j j))) (i + k + j + 1)))) :=
    rsum_single_diff (zpRing p)
      (fun b => rsum (zpRing p) (fun a => (zpRing p).mul (G j b a)
        ((zpRing p).mul
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) b k))
          (psPow (zpRing p) (ltPoly p) j j))) (i + k + j + 1))
      (fun b => rsum (zpRing p) (fun a => (zpRing p).mul (G' j b a)
        ((zpRing p).mul
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) b k))
          (psPow (zpRing p) (ltPoly p) j j))) (i + k + j + 1))
      k (i + k + j + 1) (by omega)
      (fun b _ hbne => rsum_congr (zpRing p) (i + k + j + 1)
        (fun a _ => hterm j b a (fun hh => hbne hh.2.1)))
  have hinner : rsum (zpRing p) (fun a => (zpRing p).mul (G j k a)
        ((zpRing p).mul
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) k k))
          (psPow (zpRing p) (ltPoly p) j j))) (i + k + j + 1)
      = (zpRing p).add
          (rsum (zpRing p) (fun a => (zpRing p).mul (G' j k a)
            ((zpRing p).mul
              ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                (psPow (zpRing p) (ltPoly p) k k))
              (psPow (zpRing p) (ltPoly p) j j))) (i + k + j + 1))
          ((zpRing p).add
            ((zpRing p).mul (G j k i)
              ((zpRing p).mul
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                  (psPow (zpRing p) (ltPoly p) k k))
                (psPow (zpRing p) (ltPoly p) j j)))
            ((zpRing p).neg ((zpRing p).mul (G' j k i)
              ((zpRing p).mul
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                  (psPow (zpRing p) (ltPoly p) k k))
                (psPow (zpRing p) (ltPoly p) j j))))) :=
    rsum_single_diff (zpRing p)
      (fun a => (zpRing p).mul (G j k a)
        ((zpRing p).mul
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) k k))
          (psPow (zpRing p) (ltPoly p) j j)))
      (fun a => (zpRing p).mul (G' j k a)
        ((zpRing p).mul
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) k k))
          (psPow (zpRing p) (ltPoly p) j j)))
      i (i + k + j + 1) (by omega)
      (fun a _ hane => hterm j k a (fun hh => hane hh.2.2))
  rw [houter, hmid, CRing.add_add_neg_cancel (zpRing p) _ _,
    hinner, CRing.add_add_neg_cancel (zpRing p) _ _]

/-! ## 三変数一意性 -/

/-- **定理 (M66-2): 三変数一意性** — IsLTFormalGroup3 p G ∧
    IsLTFormalGroup3 p G' ⟹ G = G'（M61 のスキーマの三変数版）。 -/
theorem lt3_unique (p : Nat) (hp : IsPrime p) (G G' : PS3 (zpRing p))
    (hG : IsLTFormalGroup3 p G) (hG' : IsLTFormalGroup3 p G') :
    G = G' := by
  have key : ∀ n, ∀ j k i, i + k + j < n → G j k i = G' j k i := by
    intro n
    induction n with
    | zero => intro j k i h; exact absurd h (by omega)
    | succ n ih =>
      intro j k i hlt
      cases Nat.lt_or_ge (i + k + j) n with
      | inl h => exact ih j k i h
      | inr hge =>
        have hn : i + k + j = n := by omega
        cases n with
        | zero =>
          have hi : i = 0 := by omega
          have hk : k = 0 := by omega
          have hj : j = 0 := by omega
          subst hi
          subst hk
          subst hj
          rw [hG.1, hG'.1]
        | succ n' =>
          cases n' with
          | zero =>
            cases Nat.decEq i 1 with
            | isTrue hi =>
              have hk : k = 0 := by omega
              have hj : j = 0 := by omega
              subst hi
              subst hk
              subst hj
              exact hG.2.1.trans hG'.2.1.symm
            | isFalse hi =>
              cases Nat.decEq k 1 with
              | isTrue hk =>
                have hi0 : i = 0 := by omega
                have hj : j = 0 := by omega
                subst hk
                subst hi0
                subst hj
                exact hG.2.2.1.trans hG'.2.2.1.symm
              | isFalse hk =>
                have hj : j = 1 := by omega
                have hi0 : i = 0 := by omega
                have hk0 : k = 0 := by omega
                subst hj
                subst hi0
                subst hk0
                exact hG.2.2.2.1.trans hG'.2.2.2.1.symm
          | succ m =>
            have hagree : ∀ c b a, a + b + c < i + k + j →
                G c b a = G' c b a :=
              fun c b a hab => ih c b a (by omega)
            have hpow : psPow (psRing (psRing (zpRing p))) G p j k i
                = psPow (psRing (psRing (zpRing p))) G' p j k i :=
              ps3Pow_coeff_congr' (zpRing p) (i + k + j) hG.1 hG'.1
                (fun c b a hab => hagree c b a hab) p hp.1 j k i
                (Nat.le_refl (i + k + j))
            have hGeq : ps3Comp1 (zpRing p) (ltPoly p) G j k i
                = ps3Comp3 (zpRing p) G (in3X (zpRing p) (ltPoly p))
                    (in3Y (zpRing p) (ltPoly p))
                    (in3Z (zpRing p) (ltPoly p)) j k i :=
              congrFun (congrFun (congrFun hG.2.2.2.2 j) k) i
            have hGeq' : ps3Comp1 (zpRing p) (ltPoly p) G' j k i
                = ps3Comp3 (zpRing p) G' (in3X (zpRing p) (ltPoly p))
                    (in3Y (zpRing p) (ltPoly p))
                    (in3Z (zpRing p) (ltPoly p)) j k i :=
              congrFun (congrFun (congrFun hG'.2.2.2.2 j) k) i
            have hCpow : (zpRing p).mul
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                  (psPow (zpRing p) (ltPoly p) k k))
                (psPow (zpRing p) (ltPoly p) j j)
                = rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))
                    (m + 2) := by
              rw [ltPow_diag p hp.1 i, ltPow_diag p hp.1 k,
                ltPow_diag p hp.1 j,
                ← rpow_add (zpRing p) ((toZp p).map ((p : Nat) : Int))
                  i k,
                ← rpow_add (zpRing p) ((toZp p).map ((p : Nat) : Int))
                  (i + k) j]
              exact congrArg
                (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))) hn
            have hbig : (zpRing p).add
                ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
                  (G j k i))
                (psPow (psRing (psRing (zpRing p))) G p j k i)
                = (zpRing p).add
                    ((zpRing p).add
                      ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
                        (G' j k i))
                      (psPow (psRing (psRing (zpRing p))) G' p j k i))
                    ((zpRing p).add
                      ((zpRing p).mul (G j k i)
                        ((zpRing p).mul
                          ((zpRing p).mul
                            (psPow (zpRing p) (ltPoly p) i i)
                            (psPow (zpRing p) (ltPoly p) k k))
                          (psPow (zpRing p) (ltPoly p) j j)))
                      ((zpRing p).neg ((zpRing p).mul (G' j k i)
                        ((zpRing p).mul
                          ((zpRing p).mul
                            (psPow (zpRing p) (ltPoly p) i i)
                            (psPow (zpRing p) (ltPoly p) k k))
                          (psPow (zpRing p) (ltPoly p) j j))))) := by
              rw [← lt3_lhs_decomp p G hG.1 j k i, hGeq,
                lt3_rhs_split p hp.1 G G' j k i hagree,
                show ps3Comp3 (zpRing p) G' (in3X (zpRing p) (ltPoly p))
                    (in3Y (zpRing p) (ltPoly p))
                    (in3Z (zpRing p) (ltPoly p)) j k i
                  = (zpRing p).add
                      ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
                        (G' j k i))
                      (psPow (psRing (psRing (zpRing p))) G' p j k i)
                  from hGeq'.symm.trans (lt3_lhs_decomp p G' hG'.1 j k i)]
            rw [hpow] at hbig
            have hquad := CRing.cancel_quad (zpRing p) hbig
            rw [hCpow] at hquad
            have hfinal : (zpRing p).add
                ((zpRing p).mul (G j k i)
                  (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))
                    (m + 2)))
                ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
                  (G' j k i))
                = (zpRing p).add
                    ((zpRing p).mul (G' j k i)
                      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))
                        (m + 2)))
                    ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
                      (G j k i)) := by
              rw [(zpRing p).add_comm
                ((zpRing p).mul (G j k i)
                  (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))
                    (m + 2)))
                ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
                  (G' j k i))]
              exact hquad.symm
            exact zp_lt_cancel p hp (m + 2) (G j k i) (G' j k i)
              (by omega) hfinal
  funext j k i
  exact key (i + k + j + 1) j k i (by omega)

end IUT
