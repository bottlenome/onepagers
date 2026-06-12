/-
  IUT/FormalGroupUnique.lean — M61（LT 形式群法則の一意性）

  **一意性定理**: IsLTFormalGroup p F かつ IsLTFormalGroup p G なら
  F = G。M60 の存在と合わせて Lubin–Tate 形式群法則の**存在と一意性**が
  完結する（一変数版 M42/M49 の lubin_tate に対応する二変数版）。

  証明は総次数の強帰納法。総次数 0・1 は一次条件が直接固定し、
  総次数 n = m+2 では両者の方程式を M58（左辺分解）・M59（対角分離）で
  開いて差をとると

    F_{j,i}·πⁿ + π·G_{j,i} = G_{j,i}·πⁿ + π·F_{j,i}

  に落ち、M42 の消去補題 `zp_lt_cancel`（πⁿ − π = π·(π^{n−1} − 1) の
  正則性 — p 正則 + 単数正則）で F_{j,i} = G_{j,i} が出る。
  低次依存（F^p の係数・対角以外の右辺）は M57 の係数合同が処理する。

  * M61-1 `CRing.cancel_quad` — 簿記: X + T = (Y + T) + (A − B) ⟹
    B + X = Y + A（左消去 + 結合・可換の往復）
  * M61-2 `lt_formal_group_unique` — **一意性定理**（総次数強帰納法）
  * M61-3 `lt_formal_group_exists_unique` — **存在と一意性のパッケージ**
    （M60 と結合: lt2Sol が唯一の LT 形式群法則）

  全て選択公理不使用。
-/
import IUT.FormalGroupExists

namespace IUT

/-! ## 簿記 -/

/-- **M61-1**: X + T = (Y + T) + (A − B) ⟹ B + X = Y + A。 -/
theorem CRing.cancel_quad (R : CRing) {X Y A B T : R.carrier}
    (h : R.add X T = R.add (R.add Y T) (R.add A (R.neg B))) :
    R.add B X = R.add Y A := by
  have h3 : R.add T X
      = R.add T (R.add Y (R.add A (R.neg B))) := by
    rw [R.add_comm T X, h,
      R.add_assoc Y T (R.add A (R.neg B)),
      CRing.add_left_comm R Y T (R.add A (R.neg B))]
  have hX : X = R.add Y (R.add A (R.neg B)) :=
    add_left_cancel R h3
  rw [hX, CRing.add_left_comm R B Y (R.add A (R.neg B)),
    CRing.add_left_comm R B A (R.neg B),
    CRing.add_neg R B]
  rw [CRing.add_zero R A]

/-! ## 一意性 -/

/-- **定理 (M61-2): LT 形式群法則の一意性** — IsLTFormalGroup p F かつ
    IsLTFormalGroup p G なら F = G（総次数の強帰納法 + M42 の消去）。 -/
theorem lt_formal_group_unique (p : Nat) (hp : IsPrime p)
    (F G : PS2 (zpRing p))
    (hF : IsLTFormalGroup p F) (hG : IsLTFormalGroup p G) : F = G := by
  have key : ∀ n, ∀ j i, i + j < n → F j i = G j i := by
    intro n
    induction n with
    | zero => intro j i h; exact absurd h (by omega)
    | succ n ih =>
      intro j i hlt
      cases Nat.lt_or_ge (i + j) n with
      | inl h => exact ih j i h
      | inr hge =>
        have hn : i + j = n := by omega
        cases n with
        | zero =>
          have hi : i = 0 := by omega
          have hj : j = 0 := by omega
          subst hi
          subst hj
          rw [hF.1, hG.1]
        | succ n' =>
          cases n' with
          | zero =>
            cases Nat.decEq i 0 with
            | isTrue hi =>
              have hj : j = 1 := by omega
              subst hi
              subst hj
              exact hF.2.2.1.trans hG.2.2.1.symm
            | isFalse hi =>
              have hi1 : i = 1 := by omega
              have hj : j = 0 := by omega
              subst hi1
              subst hj
              exact hF.2.1.trans hG.2.1.symm
          | succ m =>
            -- 総次数 m + 2: 両者の方程式の差を消去補題へ
            have hagree : ∀ b a, a + b < i + j → F b a = G b a :=
              fun b a hab => ih b a (by omega)
            have hpow : psPow (psRing (zpRing p)) F p j i
                = psPow (psRing (zpRing p)) G p j i :=
              ps2Pow_coeff_congr' (zpRing p) (i + j) hF.1 hG.1 hagree
                p hp.1 j i (Nat.le_refl (i + j))
            have hFeq : ps2Comp1 (zpRing p) (ltPoly p) F j i
                = ps2Comp2 (zpRing p) F
                    (psC (psRing (zpRing p)) (ltPoly p))
                    (psMap (psConstHom (zpRing p)) (ltPoly p)) j i :=
              congrFun (congrFun hF.2.2.2 j) i
            have hGeq : ps2Comp1 (zpRing p) (ltPoly p) G j i
                = ps2Comp2 (zpRing p) G
                    (psC (psRing (zpRing p)) (ltPoly p))
                    (psMap (psConstHom (zpRing p)) (ltPoly p)) j i :=
              congrFun (congrFun hG.2.2.2 j) i
            -- C = (f^i)_i·(f^j)_j = π^{m+2}
            have hCpow : (zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                (psPow (zpRing p) (ltPoly p) j j)
                = rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))
                    (m + 2) := by
              rw [ltPow_diag p hp.1 i, ltPow_diag p hp.1 j,
                ← rpow_add (zpRing p) ((toZp p).map ((p : Nat) : Int)) i j]
              exact congrArg
                (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))) hn
            -- 主等式: π·F + (F^p) = (π·G + (G^p)) + (F·C − G·C)
            have hbig : (zpRing p).add
                ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) (F j i))
                (psPow (psRing (zpRing p)) F p j i)
                = (zpRing p).add
                    ((zpRing p).add
                      ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
                        (G j i))
                      (psPow (psRing (zpRing p)) G p j i))
                    ((zpRing p).add
                      ((zpRing p).mul (F j i)
                        ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                          (psPow (zpRing p) (ltPoly p) j j)))
                      ((zpRing p).neg ((zpRing p).mul (G j i)
                        ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                          (psPow (zpRing p) (ltPoly p) j j))))) := by
              rw [← lt2_lhs_decomp p F hF.1 j i, hFeq,
                lt2_rhs_split p hp.1 F G j i hagree,
                show ps2Comp2 (zpRing p) G
                    (psC (psRing (zpRing p)) (ltPoly p))
                    (psMap (psConstHom (zpRing p)) (ltPoly p)) j i
                  = (zpRing p).add
                      ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
                        (G j i))
                      (psPow (psRing (zpRing p)) G p j i) from
                  hGeq.symm.trans (lt2_lhs_decomp p G hG.1 j i)]
            rw [hpow] at hbig
            -- 消去補題の形へ
            have hquad : (zpRing p).add
                ((zpRing p).mul (G j i)
                  ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                    (psPow (zpRing p) (ltPoly p) j j)))
                ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) (F j i))
                = (zpRing p).add
                    ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
                      (G j i))
                    ((zpRing p).mul (F j i)
                      ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                        (psPow (zpRing p) (ltPoly p) j j))) :=
              CRing.cancel_quad (zpRing p) hbig
            rw [hCpow] at hquad
            -- zp_lt_cancel: F·πⁿ + π·G = G·πⁿ + π·F → F = G
            have hfinal : (zpRing p).add
                ((zpRing p).mul (F j i)
                  (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))
                    (m + 2)))
                ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) (G j i))
                = (zpRing p).add
                    ((zpRing p).mul (G j i)
                      (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))
                        (m + 2)))
                    ((zpRing p).mul ((toZp p).map ((p : Nat) : Int))
                      (F j i)) := by
              rw [(zpRing p).add_comm
                ((zpRing p).mul (F j i)
                  (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int))
                    (m + 2)))
                ((zpRing p).mul ((toZp p).map ((p : Nat) : Int)) (G j i))]
              exact hquad.symm
            exact zp_lt_cancel p hp (m + 2) (F j i) (G j i)
              (by omega) hfinal
  funext j i
  exact key (i + j + 1) j i (by omega)

/-! ## 存在と一意性のパッケージ -/

/-- **定理 (M61-3): LT 形式群法則の存在と一意性** — lt2Sol が
    IsLTFormalGroup p の**唯一の** witness（M60 と結合）。
    形式群キャンペーン M50–M61 の総括定理。 -/
theorem lt_formal_group_exists_unique (p : Nat) (hp : IsPrime p) :
    IsLTFormalGroup p (lt2Sol p hp)
      ∧ ∀ G : PS2 (zpRing p), IsLTFormalGroup p G → G = lt2Sol p hp :=
  ⟨lt2Sol_is_formal_group p hp,
    fun G hG => lt_formal_group_unique p hp G (lt2Sol p hp) hG
      (lt2Sol_is_formal_group p hp)⟩

end IUT
