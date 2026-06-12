/-
  IUT/FormalGroupMap.lean — M53（二変数係数持ち上げと方程式の mod-p 還元: 形式群第四層）

  形式群法則の存在証明（M49 のスキーマの二変数版）に向けた最初の柱:
  環準同型 φ : R → S の **二変数冪級数への持ち上げ** ps2Map を構成し、
  形式群方程式 f∘F = F(f(X), f(Y)) が ps2Map で保たれることを完全証明する。

  方針: PS2 R = PS(psRing R)（M50 の反復構成）なので、φ をまず
  psRingHom φ : R[[X]] → S[[X]]（M46 の psMap が環準同型であること）に
  持ち上げ、もう一度 psMap を適用するだけで二変数の持ち上げが
  **一変数の理論から無償で**得られる。係数ごとには (ps2Map φ F)_{j,i}
  = φ(F_{j,i})。

  * M53-1 `psRingHom` — **psMap の環準同型化** R[[X]] → S[[X]]
    （M46-3 の add/mul 保存 + one 保存を RingHom に束ねる）
  * M53-2 `ps2Map` / 座標保存 — 二変数持ち上げ、X ↦ X・Y ↦ Y
  * M53-3 `ps2Map_comp1` / `ps2Map_comp2` — **代入との交換**
    φ(f∘F) = φf∘φF・φ(F(P,Q)) = (φF)(φP, φQ)（M46 の psMap_pow を
    psRing レベルで再利用 + ringHom_rsum）
  * M53-4 `ps2Map_psC` / `ps2Map_inY` — **二方向注入との交換**
    （M52 の inX・inY が係数持ち上げと可換）
  * M53-5 `ps2Map_equation` — **方程式の移送**: F が f の形式群方程式を
    満たすなら φF は φf の方程式を満たす（M53-3〜4 の合流・一撃）
  * M53-6 `ltFormalGroup_reduction` — **LT 形式群の mod-p 還元**:
    IsLTFormalGroup p F なら還元 F̄ = ps2Map(projRing p 1) F は
    **X^p の方程式** X^p∘F̄ = F̄(X^p, Y^p) を満たす（M48 の
    ltPoly_reduction f̄ = X^p と結合）。一次条件 F̄₀₀ = 0・
    F̄₁₀ = F̄₀₁ = 1 も還元される

  ロードマップ: 次層で標数 p の二変数 Frobenius G(X,Y)^p = G(X^p, Y^p)
  （M47 の二変数版）→ 誤差項の p-整除性 → 総次数帰納による存在。
  全て選択公理不使用。
-/
import IUT.FormalGroupEq

namespace IUT

/-! ## psMap の環準同型化 -/

/-- **M53-1: psMap は環準同型** R[[X]] → S[[X]]（M46-3 の束ね上げ）。 -/
def psRingHom {R S : CRing} (φ : RingHom R S) : RingHom (psRing R) (psRing S) where
  map := psMap φ
  map_add := psMap_add φ
  map_mul := psMap_mul φ
  map_one := by
    funext n
    cases n with
    | zero => exact φ.map_one
    | succ m => exact φ.map_zero

/-! ## 二変数持ち上げ -/

/-- **M53-2a: 二変数係数持ち上げ** PS2 R → PS2 S
    （psMap の反復適用。係数ごとには φ(F_{j,i})）。 -/
def ps2Map {R S : CRing} (φ : RingHom R S) (F : PS2 R) : PS2 S :=
  psMap (psRingHom φ) F

/-- 係数ごとの記述（定義の透過性）。 -/
theorem ps2Map_coeff {R S : CRing} (φ : RingHom R S) (F : PS2 R)
    (j i : Nat) : ps2Map φ F j i = φ.map (F j i) := rfl

/-- **M53-2b: 持ち上げは X 座標を保つ**。 -/
theorem ps2Map_X {R S : CRing} (φ : RingHom R S) :
    ps2Map φ (ps2X R) = ps2X S := by
  funext j i
  show φ.map ((if j = 0 then psX R else (psRing R).zero) i)
      = (if j = 0 then psX S else (psRing S).zero) i
  cases Nat.decEq j 0 with
  | isTrue hj =>
    rw [if_pos hj, if_pos hj]
    show φ.map (if i = 1 then R.one else R.zero)
        = (if i = 1 then S.one else S.zero)
    cases Nat.decEq i 1 with
    | isTrue hi =>
      rw [if_pos hi, if_pos hi]
      exact φ.map_one
    | isFalse hi =>
      rw [if_neg hi, if_neg hi]
      exact φ.map_zero
  | isFalse hj =>
    rw [if_neg hj, if_neg hj]
    exact φ.map_zero

/-- **M53-2c: 持ち上げは Y 座標を保つ**。 -/
theorem ps2Map_Y {R S : CRing} (φ : RingHom R S) :
    ps2Map φ (ps2Y R) = ps2Y S := by
  funext j i
  show φ.map ((if j = 1 then (psRing R).one else (psRing R).zero) i)
      = (if j = 1 then (psRing S).one else (psRing S).zero) i
  cases Nat.decEq j 1 with
  | isTrue hj =>
    rw [if_pos hj, if_pos hj]
    cases i with
    | zero => exact φ.map_one
    | succ m => exact φ.map_zero
  | isFalse hj =>
    rw [if_neg hj, if_neg hj]
    exact φ.map_zero

/-! ## 代入との交換 -/

/-- **定理 (M53-3a): 持ち上げは 1→2 変数代入と交換** φ(f∘F) = φf∘φF。 -/
theorem ps2Map_comp1 {R S : CRing} (φ : RingHom R S) (f : PS R) (F : PS2 R) :
    ps2Map φ (ps2Comp1 R f F) = ps2Comp1 S (psMap φ f) (ps2Map φ F) := by
  funext j i
  show φ.map (rsum R (fun k => R.mul (f k) (psPow (psRing R) F k j i))
        (i + j + 1))
      = rsum S (fun k => S.mul (psMap φ f k)
          (psPow (psRing S) (ps2Map φ F) k j i)) (i + j + 1)
  rw [ringHom_rsum φ _ (i + j + 1)]
  exact rsum_congr S (i + j + 1) (fun k _ => by
    have hpow : φ.map (psPow (psRing R) F k j i)
        = psPow (psRing S) (ps2Map φ F) k j i :=
      congrFun (congrFun (psMap_pow (psRingHom φ) F k) j) i
    rw [φ.map_mul (f k) (psPow (psRing R) F k j i), hpow]
    rfl)

/-- **定理 (M53-3b): 持ち上げは 2→2 変数代入と交換**
    φ(F(P,Q)) = (φF)(φP, φQ)（二重和の各項で psMap_mul + psMap_pow）。 -/
theorem ps2Map_comp2 {R S : CRing} (φ : RingHom R S) (F P Q : PS2 R) :
    ps2Map φ (ps2Comp2 R F P Q)
      = ps2Comp2 S (ps2Map φ F) (ps2Map φ P) (ps2Map φ Q) := by
  funext j i
  show φ.map (rsum R (fun b => rsum R (fun a => R.mul (F b a)
        ((psMul (psRing R) (psPow (psRing R) P a)
          (psPow (psRing R) Q b)) j i)) (i + j + 1)) (i + j + 1))
      = rsum S (fun b => rsum S (fun a => S.mul (ps2Map φ F b a)
          ((psMul (psRing S) (psPow (psRing S) (ps2Map φ P) a)
            (psPow (psRing S) (ps2Map φ Q) b)) j i)) (i + j + 1)) (i + j + 1)
  rw [ringHom_rsum φ _ (i + j + 1)]
  exact rsum_congr S (i + j + 1) (fun b _ => by
    rw [ringHom_rsum φ _ (i + j + 1)]
    exact rsum_congr S (i + j + 1) (fun a _ => by
      have hmul : psMap (psRingHom φ)
            (psMul (psRing R) (psPow (psRing R) P a) (psPow (psRing R) Q b))
          = psMul (psRing S) (psMap (psRingHom φ) (psPow (psRing R) P a))
              (psMap (psRingHom φ) (psPow (psRing R) Q b)) :=
        psMap_mul (psRingHom φ) _ _
      rw [psMap_pow (psRingHom φ) P a, psMap_pow (psRingHom φ) Q b] at hmul
      have hfac : φ.map ((psMul (psRing R) (psPow (psRing R) P a)
            (psPow (psRing R) Q b)) j i)
          = (psMul (psRing S) (psPow (psRing S) (ps2Map φ P) a)
              (psPow (psRing S) (ps2Map φ Q) b)) j i :=
        congrFun (congrFun hmul j) i
      rw [φ.map_mul (F b a) _, hfac]
      rfl))

/-! ## 二方向注入との交換 -/

/-- **定理 (M53-4a): 持ち上げは X 方向注入と交換**
    φ(inX f) = inX (φf)。 -/
theorem ps2Map_psC {R S : CRing} (φ : RingHom R S) (f : PS R) :
    ps2Map φ (psC (psRing R) f) = psC (psRing S) (psMap φ f) := by
  funext j i
  show φ.map ((if j = 0 then f else (psRing R).zero) i)
      = (if j = 0 then psMap φ f else (psRing S).zero) i
  cases Nat.decEq j 0 with
  | isTrue hj =>
    rw [if_pos hj, if_pos hj]
    rfl
  | isFalse hj =>
    rw [if_neg hj, if_neg hj]
    exact φ.map_zero

/-- **定理 (M53-4b): 持ち上げは Y 方向注入と交換**
    φ(inY f) = inY (φf)。 -/
theorem ps2Map_inY {R S : CRing} (φ : RingHom R S) (f : PS R) :
    ps2Map φ (psMap (psConstHom R) f) = psMap (psConstHom S) (psMap φ f) := by
  funext j i
  show φ.map (if i = 0 then f j else R.zero)
      = (if i = 0 then φ.map (f j) else S.zero)
  cases Nat.decEq i 0 with
  | isTrue hi =>
    rw [if_pos hi, if_pos hi]
  | isFalse hi =>
    rw [if_neg hi, if_neg hi]
    exact φ.map_zero

/-! ## 方程式の移送と mod-p 還元 -/

/-- **定理 (M53-5): 形式群方程式の移送** — F が f の方程式
    f∘F = F(f(X), f(Y)) を満たすなら、持ち上げ φF は φf の方程式を
    満たす（M53-3〜4 の合流）。 -/
theorem ps2Map_equation {R S : CRing} (φ : RingHom R S) (f : PS R)
    (F : PS2 R)
    (h : ps2Comp1 R f F
      = ps2Comp2 R F (psC (psRing R) f) (psMap (psConstHom R) f)) :
    ps2Comp1 S (psMap φ f) (ps2Map φ F)
      = ps2Comp2 S (ps2Map φ F) (psC (psRing S) (psMap φ f))
          (psMap (psConstHom S) (psMap φ f)) := by
  rw [← ps2Map_comp1 φ f F, h, ps2Map_comp2 φ F _ _, ps2Map_psC φ f,
    ps2Map_inY φ f]

/-- **定理 (M53-6a): LT 形式群の mod-p 還元は X^p の方程式を満たす** —
    IsLTFormalGroup p F なら F̄ = ps2Map(projRing p 1) F は
    X^p∘F̄ = F̄(X^p, Y^p) を満たす（ltPoly_reduction f̄ = X^p と M53-5）。
    標数 p の Frobenius（次層）と合流して誤差項の p-整除性を生む核。 -/
theorem ltFormalGroup_reduction (p : Nat) (F : PS2 (zpRing p))
    (h : IsLTFormalGroup p F) :
    ps2Comp1 (zmodRing (p ^ 1)) (psMono (zmodRing (p ^ 1)) p)
        (ps2Map (projRing p 1) F)
      = ps2Comp2 (zmodRing (p ^ 1)) (ps2Map (projRing p 1) F)
          (psC (psRing (zmodRing (p ^ 1))) (psMono (zmodRing (p ^ 1)) p))
          (psMap (psConstHom (zmodRing (p ^ 1)))
            (psMono (zmodRing (p ^ 1)) p)) := by
  have h4 := ps2Map_equation (projRing p 1) (ltPoly p) F h.2.2.2
  rw [ltPoly_reduction p] at h4
  exact h4

/-- **定理 (M53-6b): 一次条件の還元** — F̄₀₀ = 0・F̄₀₁ = F̄₁₀ = 1。 -/
theorem ltFormalGroup_reduction_linear (p : Nat) (F : PS2 (zpRing p))
    (h : IsLTFormalGroup p F) :
    ps2Map (projRing p 1) F 0 0 = (zmodRing (p ^ 1)).zero
    ∧ ps2Map (projRing p 1) F 0 1 = (zmodRing (p ^ 1)).one
    ∧ ps2Map (projRing p 1) F 1 0 = (zmodRing (p ^ 1)).one := by
  refine ⟨?_, ?_, ?_⟩
  · show (projRing p 1).map (F 0 0) = (zmodRing (p ^ 1)).zero
    rw [h.1]
    exact RingHom.map_zero (projRing p 1)
  · show (projRing p 1).map (F 0 1) = (zmodRing (p ^ 1)).one
    rw [h.2.1]
    exact (projRing p 1).map_one
  · show (projRing p 1).map (F 1 0) = (zmodRing (p ^ 1)).one
    rw [h.2.2.1]
    exact (projRing p 1).map_one

end IUT
