/-
  IUT/WeilKummerDuality.lean — M354F [実／本物]
  分類: 実 (Weil ペアリングの完全双対 E_q[n]≅Hom(E_q[n],μ_n))
  complete_pct 影響: 柱A を前進（M339F Weil ペアリングの非退化から双対写像 P↦e_n(P,·)∈
    Hom(E_q[n],μ_n) を構成し単射（非退化から）・完全双対 E_q[n]≅Hom(E_q[n],μ_n)・
    M344F ガロア同変性との両立を本物で＝捻れの自己双対性）。
  正直な限定: 全射性/位数勘定・幾何的 Cartier 双対は外部仮説/後続等。

  * M354F-1 `wkdTorInv`/`wkdTorGrp` — E_q[n]=ℤ/n×ℤ/n を本物の可換群 Grp に（座標ごとの
    ℤ/n 加法・零点・逆元、結合律/単位律/逆元律を M339F の座標群から完全証明）。
  * M354F-2 `wkdDualMap` — 双対写像 P↦(Q↦e_n(P,Q))∈Hom(E_q[n],μ_n)（M339F 第二引数
    双線形性 weil_bilinear_right が Hom.map_mul を与える）・`wkd_dual_hom`。
  * M354F-3 `wkd_zero_pairing`/`wkd_dual_inv` — 零点・逆元でのペアリング（e(0,Q)=1・
    e(−P,Q)=e(P,Q)⁻¹、双線形性 + 群公理から本物）。
  * M354F-4 `wkd_dual_injective`（本丸1）— P↦wkdDualMap P は単射（M339F 点版非退化
    weil_pt_nondegenerate: e_n(P,·)=e_n(P',·) ⟹ P=P'）。
  * M354F-5 `wkd_surj_hypothesis`/`WeilKummerDuality`/`wkd_duality`（本丸2）— 完全双対
    E_q[n]≅Hom(E_q[n],μ_n)（単射は本物・全射は同位数群間の完全ペアリングの帰結として
    外部仮説 wkd_surj_hypothesis で受ける）。
  * M354F-6 `wkd_kummer_compat`/`wkd_self_dual` — M344F ガロア同変性 e_n(σP,σQ)=χ(σ)e_n(P,Q)
    との両立（双対が χ で捻れて同変）・M339F 反対称性による E_q[n] の自己双対性。
  * M354F-7 capstone `wkdDualityData`/`wkd_exists` + 実例（n=3）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用。共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
  一般名は `wkd` 接頭辞で衝突回避。
-/
import IUT.WeilGaloisEquiv

namespace IUT

/-! ## M354F-1: E_q[n]=ℤ/n×ℤ/n を本物の可換群 Grp に -/

/-- **M354F-1a: E_q[n] の逆元**（座標ごとの ℤ/n 逆元）−P = (−P.zExp, −P.qExp)。 -/
def wkdTorInv (n : Nat) (P : WeilTorsion n) : WeilTorsion n :=
  ⟨(zmod n).inv P.zExp, (zmod n).inv P.qExp⟩

/-- **M354F-1b: 捻れ群 E_q[n]=ℤ/n×ℤ/n の群構造**（本物の可換群 Grp）。加法は
    座標ごとの ℤ/n 加法 `weilTorAdd`、零点 `weilTorZero`、逆元 `wkdTorInv`。結合律・
    単位律・逆元律は M339F の座標群 `zmod n` の群公理から完全証明。Hom(E_q[n],μ_n)
    の始域となる本物の捻れ群。 -/
def wkdTorGrp (n : Nat) : Grp where
  carrier := WeilTorsion n
  mul := weilTorAdd n
  one := weilTorZero n
  inv := wkdTorInv n
  mul_assoc := fun P Q R => by
    show WeilTorsion.mk ((zmod n).mul ((zmod n).mul P.zExp Q.zExp) R.zExp)
        ((zmod n).mul ((zmod n).mul P.qExp Q.qExp) R.qExp)
      = WeilTorsion.mk ((zmod n).mul P.zExp ((zmod n).mul Q.zExp R.zExp))
        ((zmod n).mul P.qExp ((zmod n).mul Q.qExp R.qExp))
    rw [(zmod n).mul_assoc, (zmod n).mul_assoc]
  one_mul := fun P => by
    cases P with
    | mk z q =>
      show WeilTorsion.mk ((zmod n).mul (zmod n).one z) ((zmod n).mul (zmod n).one q)
        = WeilTorsion.mk z q
      rw [(zmod n).one_mul, (zmod n).one_mul]
  inv_mul := fun P => by
    cases P with
    | mk z q =>
      show WeilTorsion.mk ((zmod n).mul ((zmod n).inv z) z) ((zmod n).mul ((zmod n).inv q) q)
        = WeilTorsion.mk (zmod n).one (zmod n).one
      rw [(zmod n).inv_mul, (zmod n).inv_mul]

/-! ## M354F-2: 双対写像 P ↦ (Q ↦ e_n(P,Q)) ∈ Hom(E_q[n], μ_n) -/

/-- **M354F-2a: 双対写像** wkdDualMap P : Q ↦ e_n(P,Q) — 各 P∈E_q[n] に対し
    Q↦e_n(P,Q) は群準同型 E_q[n]→μ_n（Hom(E_q[n],μ_n) の元）。準同型性
    e_n(P,Q+Q')=e_n(P,Q)·e_n(P,Q') は M339F 第二引数双線形性 `weil_bilinear_right`。
    Weil/Cartier 双対の双対写像本体。 -/
def wkdDualMap (n : Nat) (P : WeilTorsion n) : Hom (wkdTorGrp n) (zmod n) where
  map := fun Q => weilPairingPt n P Q
  map_mul := fun Q Q' =>
    weil_bilinear_right n P.zExp P.qExp Q.zExp Q'.zExp Q.qExp Q'.qExp

/-- **M354F-2b: 双対写像は準同型** e_n(P,Q+Q')=e_n(P,Q)·e_n(P,Q')。 -/
theorem wkd_dual_hom (n : Nat) (P Q Q' : WeilTorsion n) :
    weilPairingPt n P (weilTorAdd n Q Q')
      = (zmod n).mul (weilPairingPt n P Q) (weilPairingPt n P Q') :=
  (wkdDualMap n P).map_mul Q Q'

/-! ## M354F-3: 零点・逆元でのペアリング -/

/-- **M354F-3a: 零点でのペアリング** e_n(0,Q)=1（零点はどの点ともペアリング自明）。 -/
theorem wkd_zero_pairing (n : Nat) (Q : WeilTorsion n) :
    weilPairingPt n (weilTorZero n) Q = (zmod n).one := by
  cases Q with
  | mk qz qq =>
    induction qz using Quot.ind; rename_i c
    induction qq using Quot.ind; rename_i d
    show weilPairing n (Quot.mk (modCong n).rel 0) (Quot.mk (modCong n).rel 0)
        (Quot.mk (modCong n).rel c) (Quot.mk (modCong n).rel d) = Quot.mk (modCong n).rel 0
    rw [weilPairing_mk]
    show Quot.mk (modCong n).rel (0 * d + -(0 * c)) = Quot.mk (modCong n).rel 0
    have hh : (0 : Int) * d + -(0 * c) = 0 := by omega
    rw [hh]

/-- **M354F-3b: 逆元でのペアリング** e_n(−P,Q)=e_n(P,Q)⁻¹（双線形性 + 群逆元律）。 -/
theorem wkd_dual_inv (n : Nat) (P Q : WeilTorsion n) :
    weilPairingPt n (wkdTorInv n P) Q = (zmod n).inv (weilPairingPt n P Q) := by
  apply Grp.inv_eq_of_mul_eq_one (zmod n)
  have hb := weil_pt_bilinear_left n P (wkdTorInv n P) Q
  have hz : weilTorAdd n P (wkdTorInv n P) = weilTorZero n := by
    cases P with
    | mk z q =>
      show WeilTorsion.mk ((zmod n).mul z ((zmod n).inv z))
          ((zmod n).mul q ((zmod n).inv q)) = WeilTorsion.mk (zmod n).one (zmod n).one
      rw [(zmod n).mul_inv, (zmod n).mul_inv]
  rw [hz, wkd_zero_pairing] at hb
  exact hb.symm

/-! ## M354F-4: 双対写像の単射性（本丸1・非退化から） -/

/-- **M354F-4: 双対写像は単射（本丸1）** — P↦wkdDualMap P は単射。すなわち
    ∀Q, e_n(P,Q)=e_n(P',Q) ⟹ P=P'。M339F 点版非退化性 `weil_pt_nondegenerate` を、
    差 P−P' に適用（e_n(P−P',Q)=e_n(P,Q)·e_n(P',Q)⁻¹=1 ⟹ P−P'=0）。Weil ペアリングが
    完全（perfect）であること＝双対写像 E_q[n]↪Hom(E_q[n],μ_n) の単射性の本物の核。 -/
theorem wkd_dual_injective (n : Nat) (P P' : WeilTorsion n)
    (h : ∀ Q, weilPairingPt n P Q = weilPairingPt n P' Q) :
    P = P' := by
  have hR : ∀ Q, weilPairingPt n (weilTorAdd n P (wkdTorInv n P')) Q = (zmod n).one := by
    intro Q
    rw [weil_pt_bilinear_left n P (wkdTorInv n P') Q, wkd_dual_inv n P' Q, h Q]
    exact Grp.mul_inv (zmod n) (weilPairingPt n P' Q)
  have hzero : (wkdTorGrp n).mul P ((wkdTorGrp n).inv P') = (wkdTorGrp n).one :=
    weil_pt_nondegenerate n (weilTorAdd n P (wkdTorInv n P')) hR
  -- 群 wkdTorGrp で mul P (inv P') = one から P = P'（右簡約）。
  have h2 : (wkdTorGrp n).mul ((wkdTorGrp n).mul P ((wkdTorGrp n).inv P')) P'
      = (wkdTorGrp n).mul (wkdTorGrp n).one P' := by
    rw [hzero]
  rw [(wkdTorGrp n).mul_assoc, (wkdTorGrp n).inv_mul, (wkdTorGrp n).mul_one,
    (wkdTorGrp n).one_mul] at h2
  exact h2

/-! ## M354F-5: 完全双対 E_q[n] ≅ Hom(E_q[n], μ_n)（本丸2） -/

/-- **M354F-5a: 全射性の外部仮説** — 双対写像 P↦(Q↦e_n(P,Q)) の**全射性**（任意の
    φ∈Hom(E_q[n],μ_n) がある P の双対写像 e_n(P,·) に一致）。有限群 ℤ/n×ℤ/n 上で単射
    かつ同位数群間ゆえ全単射という位数勘定の帰結だが、位数勘定は重いので完全ペアリングの
    帰結として明示の Prop 仮説で受け、決して導出しない（幾何的 Cartier 双対も後続）。 -/
def wkd_surj_hypothesis (n : Nat) : Prop :=
  ∀ φ : Hom (wkdTorGrp n) (zmod n), ∃ P, ∀ Q, φ.map Q = weilPairingPt n P Q

/-- **M354F-5b: 完全双対データ** — E_q[n]≅Hom(E_q[n],μ_n)。双対写像 `dual`・その値の
    明示・**単射性（本物）**・**全射性（仮説）**を束ねる。Weil/Cartier n-捻れ双対の総括。 -/
structure WeilKummerDuality (n : Nat) where
  /-- 双対写像 P↦e_n(P,·)∈Hom(E_q[n],μ_n)。 -/
  dual : WeilTorsion n → Hom (wkdTorGrp n) (zmod n)
  /-- dual P の値は e_n(P,Q)。 -/
  dual_eq : ∀ P Q, (dual P).map Q = weilPairingPt n P Q
  /-- 単射性（本物・非退化から）。 -/
  injective : ∀ P P', (∀ Q, (dual P).map Q = (dual P').map Q) → P = P'
  /-- 全射性（仮説・位数勘定/完全ペアリングの帰結）。 -/
  surjective : ∀ φ : Hom (wkdTorGrp n) (zmod n), ∃ P, ∀ Q, φ.map Q = (dual P).map Q

/-- **M354F-5c: 完全双対（本丸2）** — 全射仮説の下で、双対写像は単射（本物）かつ全射
    ＝完全双対 E_q[n]≅Hom(E_q[n],μ_n)。単射は M339F 非退化からの本物、全射は仮説。 -/
theorem wkd_duality (n : Nat) (hsurj : wkd_surj_hypothesis n) :
    (∀ P P', (∀ Q, weilPairingPt n P Q = weilPairingPt n P' Q) → P = P')
    ∧ (∀ φ : Hom (wkdTorGrp n) (zmod n), ∃ P, ∀ Q, φ.map Q = weilPairingPt n P Q) :=
  ⟨wkd_dual_injective n, hsurj⟩

/-! ## M354F-6: M344F ガロア同変性との両立・自己双対性 -/

/-- **M354F-6a: 双対とガロア作用の両立（Kummer 互換）** — 双対写像は G_K の上三角作用の
    下で円分指標 χ で捻れて同変: e_n(σ_g·P, σ_g·Q)=χ(g)·e_n(P,Q)。M344F `wge_equivariant`
    を双対写像の言葉に据える（双対 E_q[n]≅Hom(E_q[n],μ_n) が χ 捻りで G_K-同変）。 -/
theorem wkd_kummer_compat (GK : Grp) (n : Nat) (ρ : WeilGKAction GK n) (g : GK.carrier)
    (P Q : WeilTorsion n) :
    (wkdDualMap n (wgeTorAct GK n ρ g P)).map (wgeTorAct GK n ρ g Q)
      = zmodMul n (ρ.chi g) ((wkdDualMap n P).map Q) :=
  wge_equivariant GK n ρ g P Q

/-- **M354F-6b: E_q[n] の自己双対性** — 双対写像の両側は反対称性で結ばれる:
    e_n(P,Q)=e_n(Q,P)⁻¹。始域 E_q[n] と双対 Hom(E_q[n],μ_n) が交代双線形形式を介して
    同じ群である＝n-捻れの自己双対性（M339F `weil_pt_antisymmetric`）。 -/
theorem wkd_self_dual (n : Nat) (P Q : WeilTorsion n) :
    (wkdDualMap n P).map Q = (zmod n).inv ((wkdDualMap n Q).map P) :=
  weil_pt_antisymmetric n P Q

/-! ## M354F-7: capstone と実例 -/

/-- **M354F-7a: 証人** — 全射仮説から完全双対データを本物で組む（単射は本物・全射は仮説）。 -/
def wkdDualityData (n : Nat) (hsurj : wkd_surj_hypothesis n) : WeilKummerDuality n where
  dual := wkdDualMap n
  dual_eq := fun _ _ => rfl
  injective := wkd_dual_injective n
  surjective := fun φ => hsurj φ

/-- **M354F-7b: capstone — 完全双対の存在**（全射仮説の下で E_q[n]≅Hom(E_q[n],μ_n)）。 -/
theorem wkd_exists (n : Nat) (hsurj : wkd_surj_hypothesis n) :
    Nonempty (WeilKummerDuality n) :=
  ⟨wkdDualityData n hsurj⟩

/-- **M354F-7c: 実例 n=3** — 双対写像 wkdDualMap((1,0)) を (0,1) に評価すると μ_3 の生成元
    ζ=class 1。ζ=(1,0)（円分方向）の双対が Q=q^{1/3}=(0,1) を ζ に送る（M339F の e_3 実例）。 -/
theorem wkd_example_n3 :
    (wkdDualMap 3 ⟨Quot.mk (modCong 3).rel 1, Quot.mk (modCong 3).rel 0⟩).map
        ⟨Quot.mk (modCong 3).rel 0, Quot.mk (modCong 3).rel 1⟩
      = Quot.mk (modCong 3).rel 1 :=
  weil_example_n3

/-- **M354F-7d: 実例 n=3（自己双対性）** — 双対写像の自己双対関係
    e_3(P,Q)=e_3(Q,P)⁻¹（任意の P,Q）。 -/
theorem wkd_example_n3_self (P Q : WeilTorsion 3) :
    (wkdDualMap 3 P).map Q = (zmod 3).inv ((wkdDualMap 3 Q).map P) :=
  wkd_self_dual 3 P Q

end IUT
