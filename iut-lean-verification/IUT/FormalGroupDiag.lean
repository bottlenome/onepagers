/-
  IUT/FormalGroupDiag.lean — M59（右辺の対角分離: 形式群第九層）

  存在再帰の最後の構造補題: 方程式右辺 F(f(X), f(Y))_{j,i} から
  **対角項 (a,b) = (i,j)（係数 π^{i+j}）を分離**する。

    RHS(F)_{j,i} = RHS(G)_{j,i} + (F_{j,i}·C − G_{j,i}·C)、C = (f^i)_i·(f^j)_j

  （F と G が総次数 < i+j で一致するとき）。これと M57（F^p の低次依存）
  ・M58（左辺分解）を合わせると、方程式の総次数 n 部分が
  π·(π^{n−1} − 1)·F_{j,i} = E(G)_{j,i} の形に落ち、係数再帰が回る。

  * M59-1 `rsum_single_diff` / `CRing.add_add_neg_cancel` —
    **一点差分抽出**: f と g が k₀ 以外で一致するなら
    Σf = Σg + (f(k₀) − g(k₀))（新しい和の道具）
  * M59-2 `ltPow_low` / `ltPow_diag` — **f = pX + X^p の冪の係数**:
    対角下 (f^a)_i = 0 (i < a)・対角 (f^a)_a = π^a
    （M40/M41 の一変数機構の ltPoly への instantiation）
  * M59-3 `lt2_rhs_split` — **対角分離**(本層の主定理):
    外側 b = j・内側 a = i の二重一点差分。残余項の termwise 一致は
    「総次数 < n では合同仮定・総次数 ≥ n では (f^a)_i か (f^b)_j の
    対角下消滅」の三分

  ロードマップ: 次層で係数の再帰構成 lt2Seg/lt2Sol と存在定理。
  全て選択公理不使用。
-/
import IUT.FormalGroupDecomp

namespace IUT

/-! ## 一点差分抽出 -/

/-- 簿記: (y + d) + (−y) = d。 -/
theorem CRing.add_add_neg_cancel (R : CRing) (y d : R.carrier) :
    R.add (R.add y d) (R.neg y) = d := by
  rw [R.add_comm y d, R.add_assoc, CRing.add_neg R y]
  exact CRing.add_zero R d

/-- **定理 (M59-1): 一点差分抽出** — f と g が k₀ 以外（範囲内）で
    一致するなら Σ_{k<m} f = Σ_{k<m} g + (f(k₀) − g(k₀))。 -/
theorem rsum_single_diff (R : CRing) (f g : Nat → R.carrier) (k0 : Nat) :
    ∀ m, k0 < m → (∀ k, k < m → k ≠ k0 → f k = g k) →
    rsum R f m
      = R.add (rsum R g m) (R.add (f k0) (R.neg (g k0))) := by
  intro m
  induction m with
  | zero => intro h _; exact absurd h (by omega)
  | succ m' ih =>
    intro hk0 h
    cases Nat.decEq k0 m' with
    | isTrue he =>
      subst he
      show R.add (rsum R f k0) (f k0)
          = R.add (R.add (rsum R g k0) (g k0))
              (R.add (f k0) (R.neg (g k0)))
      rw [rsum_congr R k0 (fun k hk => h k (by omega) (by omega)),
        R.add_assoc (rsum R g k0) (g k0) (R.add (f k0) (R.neg (g k0))),
        show R.add (g k0) (R.add (f k0) (R.neg (g k0))) = f k0 from by
          rw [R.add_comm (f k0) (R.neg (g k0)),
            ← R.add_assoc (g k0) (R.neg (g k0)) (f k0),
            CRing.add_neg R (g k0), R.zero_add]]
    | isFalse he =>
      have hk0' : k0 < m' := by omega
      show R.add (rsum R f m') (f m')
          = R.add (R.add (rsum R g m') (g m'))
              (R.add (f k0) (R.neg (g k0)))
      rw [ih hk0' (fun k hk hne => h k (by omega) hne),
        h m' (by omega) (fun hh => he hh.symm),
        R.add_assoc (rsum R g m') (R.add (f k0) (R.neg (g k0))) (g m'),
        R.add_comm (R.add (f k0) (R.neg (g k0))) (g m'),
        ← R.add_assoc (rsum R g m') (g m') (R.add (f k0) (R.neg (g k0)))]

/-! ## f = pX + X^p の冪の係数 -/

/-- **M59-2a: 対角下消滅** — i < a なら (f^a)_i = 0
    （f₀ = 0、M40 の psPow_coeff_zero）。 -/
theorem ltPow_low (p : Nat) (hp : 2 ≤ p) (a i : Nat) (h : i < a) :
    psPow (zpRing p) (ltPoly p) a i = (zpRing p).zero :=
  psPow_coeff_zero (zpRing p) (ltPoly p) (ltPoly_coeff_zero p hp) a i h

/-- **M59-2b: 対角係数** — (f^a)_a = π^a（f₁ = π、M41 の
    psPow_coeff_diag）。 -/
theorem ltPow_diag (p : Nat) (hp : 2 ≤ p) (a : Nat) :
    psPow (zpRing p) (ltPoly p) a a
      = rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) a := by
  rw [psPow_coeff_diag (zpRing p) (ltPoly p) (ltPoly_coeff_zero p hp) a,
    ltPoly_coeff_one p hp]

/-! ## 対角分離 -/

/-- **定理 (M59-3): 右辺の対角分離** — F と G が総次数 < i+j で
    一致するとき、
    RHS(F)_{j,i} = RHS(G)_{j,i} + (F_{j,i}·C − G_{j,i}·C)、
    C = (f^i)_i·(f^j)_j（= π^{i+j}）。総次数 ≥ i+j の非対角項は
    (f^a)_i か (f^b)_j の対角下消滅で両辺とも消える。 -/
theorem lt2_rhs_split (p : Nat) (hp : 2 ≤ p) (F G : PS2 (zpRing p))
    (j i : Nat) (h : ∀ b a, a + b < i + j → F b a = G b a) :
    ps2Comp2 (zpRing p) F (psC (psRing (zpRing p)) (ltPoly p))
        (psMap (psConstHom (zpRing p)) (ltPoly p)) j i
      = (zpRing p).add
          (ps2Comp2 (zpRing p) G (psC (psRing (zpRing p)) (ltPoly p))
            (psMap (psConstHom (zpRing p)) (ltPoly p)) j i)
          ((zpRing p).add
            ((zpRing p).mul (F j i)
              ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                (psPow (zpRing p) (ltPoly p) j j)))
            ((zpRing p).neg ((zpRing p).mul (G j i)
              ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                (psPow (zpRing p) (ltPoly p) j j))))) := by
  have hterm : ∀ b a, ¬ (b = j ∧ a = i) →
      (zpRing p).mul (F b a)
        ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
          (psPow (zpRing p) (ltPoly p) b j))
      = (zpRing p).mul (G b a)
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) b j)) := by
    intro b a hne
    cases Nat.lt_or_ge (a + b) (i + j) with
    | inl hlt => rw [h b a hlt]
    | inr hge =>
      cases Nat.lt_or_ge i a with
      | inl hia =>
        rw [ltPow_low p hp a i hia,
          CRing.zero_mul (zpRing p) (psPow (zpRing p) (ltPoly p) b j),
          CRing.mul_zero (zpRing p) (F b a),
          CRing.mul_zero (zpRing p) (G b a)]
      | inr hai =>
        cases Nat.lt_or_ge j b with
        | inl hjb =>
          rw [ltPow_low p hp b j hjb,
            CRing.mul_zero (zpRing p) (psPow (zpRing p) (ltPoly p) a i),
            CRing.mul_zero (zpRing p) (F b a),
            CRing.mul_zero (zpRing p) (G b a)]
        | inr hbj =>
          have hb : b = j := by omega
          have ha : a = i := by omega
          exact absurd ⟨hb, ha⟩ hne
  rw [lt2_rhs_coeff (zpRing p) (ltPoly p) F j i,
    lt2_rhs_coeff (zpRing p) (ltPoly p) G j i]
  have houter : rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (F b a)
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) b j))) (i + j + 1)) (i + j + 1)
      = (zpRing p).add
          (rsum (zpRing p) (fun b => rsum (zpRing p) (fun a =>
            (zpRing p).mul (G b a)
              ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                (psPow (zpRing p) (ltPoly p) b j))) (i + j + 1)) (i + j + 1))
          ((zpRing p).add
            (rsum (zpRing p) (fun a =>
              (zpRing p).mul (F j a)
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                  (psPow (zpRing p) (ltPoly p) j j))) (i + j + 1))
            ((zpRing p).neg (rsum (zpRing p) (fun a =>
              (zpRing p).mul (G j a)
                ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                  (psPow (zpRing p) (ltPoly p) j j))) (i + j + 1)))) :=
    rsum_single_diff (zpRing p)
      (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (F b a)
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) b j))) (i + j + 1))
      (fun b => rsum (zpRing p) (fun a =>
        (zpRing p).mul (G b a)
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) b j))) (i + j + 1))
      j (i + j + 1) (by omega)
      (fun b _ hbne => rsum_congr (zpRing p) (i + j + 1)
        (fun a _ => hterm b a (fun hh => hbne hh.1)))
  have hinner : rsum (zpRing p) (fun a =>
        (zpRing p).mul (F j a)
          ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
            (psPow (zpRing p) (ltPoly p) j j))) (i + j + 1)
      = (zpRing p).add
          (rsum (zpRing p) (fun a =>
            (zpRing p).mul (G j a)
              ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
                (psPow (zpRing p) (ltPoly p) j j))) (i + j + 1))
          ((zpRing p).add
            ((zpRing p).mul (F j i)
              ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                (psPow (zpRing p) (ltPoly p) j j)))
            ((zpRing p).neg ((zpRing p).mul (G j i)
              ((zpRing p).mul (psPow (zpRing p) (ltPoly p) i i)
                (psPow (zpRing p) (ltPoly p) j j))))) :=
    rsum_single_diff (zpRing p)
      (fun a => (zpRing p).mul (F j a)
        ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
          (psPow (zpRing p) (ltPoly p) j j)))
      (fun a => (zpRing p).mul (G j a)
        ((zpRing p).mul (psPow (zpRing p) (ltPoly p) a i)
          (psPow (zpRing p) (ltPoly p) j j)))
      i (i + j + 1) (by omega)
      (fun a _ hane => hterm j a (fun hh => hane hh.2))
  rw [houter, hinner,
    CRing.add_add_neg_cancel (zpRing p) _ _]

end IUT
