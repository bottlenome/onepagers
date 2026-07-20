/-
  IUT/Q3TemperedThetaClassL9.lean — A5 N2 [実／(b) 本物の先行建設]

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（骨格・模型・代理でなく、q9mt で建てた
     実 level-9 μ₉ 値テータ群 q9mtM = C_{M₉}(g_τ)（M=ℚ₃(ζ₉)・q=3⁹・wild e=6）の中へ、
     M424F の代理 tempered π₁ 骨格 tpeGroup = thetaGrp ⋊ ℤ を**本物の準同型 Φ₉/Ψ₉ で実現**
     する。q3nt（A5d・level 2・μ₂ 影・ℚ₃ 上）の忠実な **wild level-9 昇格**であり、q3nt の
     正直限定 1「奇レベル実現は ζ_l∉ℚ₃ で恒久ブロック」の前提が L₂/M 生態系
     （q3rq→q3tl→q9tl→q9mt）で 3-冪レベルについて失効したことを実コードで確定する。
     主語は実 q9mtM／実 q9tlMx=ℤ(v_π)×U₃／実 ζ₉=q3kZeta9（位数ちょうど 9）。toy 主語なし。）

  complete_pct 影響: **A5 N2（s_A5 0.23 → 予測 0.26–0.28・独立敵対監査確定が条件）**。
     q3nt の 2 つの新規: (i) **シクロトーム実現の深化 mod-2 → mod-9**——代理シクロトーム ℤ の
     生成元 (0,0,1) の実現 Z₉ が**位数ちょうど 9**（wild 円分値 ζ₉⁻¹ の実担体・q3nt の Z=−1 は
     位数 2 だった）。(ii) **χ 捻りの可視化**——q3nt_chi_invisible（level 2 で捻り不変）の
     **正反対** Ψ₉∘tw ≠ Ψ₉（witness ι(0,0,1)・Z₉≠Z₉⁻¹⟸ζ₉²≠1）を証明。M429F atpChi が主張する
     「算術捻りが tempered テータに非自明に効く」が実値で初めて見える。**A7/A8 status は主張しない**
     （q9mt/q3nt の定理は消費のみ・再証明ゼロ・q9mt は foundation の 0 計上ゆえ二重計上でない）。

  正直な限定（§4 準拠・消去/弱化しない・q3nt/q9mt/q3rq 継承）:
  1. **q=3⁹ の wild 忠実部分ケース**: 実現は M=ℚ₃(ζ₉) 上の level 9（μ₉）と q3nt の level 2
     （μ₂・ℚ₃ 上）で成立。**full ẑ(1)・全素数 l は依然未達**。Ψ₉ も非単射（mod-9 崩壊
     q9nt_psi_level9_collapse: Ψ₉(ι(0,0,9))=1）。旧 q3nt 限定は消さず本ファイルに深化形を並置。
  2. **tempered π₁ の「定義」は依然外部**: Berkovich/rigid 解析被覆・位相 π₁ を建てない。
     Φ₉/Ψ₉ は「実被覆空間の π₁ からの写像」でなく「代理 étale-theta 商の群論的影の実 μ₉ 群内
     実現」。**A5 恒久上限 0.35–0.4 は不変**。
  3. **χ 可視化は「捻りに対する Ψ₉ の非不変性」**であり、**atpGroup 半直積まるごとの実現ではない**
     （実 Gal(M/ℚ₃)≅(ℤ/9)^× 自己同型 ζ₉↦ζ₉^k の建設は named future target・A7 と主語が絡む）。
  4. **実 Gal 作用 0・実テータ関数 0・cuspidalization 本体 0・π₁ 同定は class を超えない・σ-only
     Galois**（q3nt/q9mt/q3k/q9tl の正直限定を継承）。pro-3 恒久限定・K-point の影（群提示担体）も継承。
  5. **二重計上の firewall**: q9mt（μ₉ テータ群・foundation 0 計上）・q3nt（braiding 一般補題）・
     tpeGroup/thetaGrp（代理骨格）は**消費のみ**（再証明 0 本・共有ファイル不変更）。各旗艦
     （symplectic_real・chi_visible・deck_theta）は Φ₉/Ψ₉ を主語に持ち、Φ₉/Ψ₉ を消去すると命題が消滅する。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3Mu9ThetaGroup
import IUT.Q3TemperedThetaClass
import IUT.TemperedPi1Etale
import IUT.ArithTemperedPi1
import IUT.Q3KummerYPow

namespace IUT

/-! ## q9nt-helpers: 単位元の冪（q9mtM のスカラー中心性・Z₉⁹ 用） -/

/-- 一般 Grp: 単位元の Nat 冪は単位元。 -/
theorem q9nt_one_npow (G : Grp) (k : Nat) : tateNpow G G.one k = G.one := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show G.mul (tateNpow G G.one k) G.one = G.one
    rw [ih, G.mul_one]

/-- 一般 Grp: 単位元の整数冪は単位元。 -/
theorem q9nt_one_zpow (G : Grp) (n : Int) : tateZpow G G.one n = G.one := by
  cases n with
  | ofNat k => exact q9nt_one_npow G k
  | negSucc k =>
    show tateNpow G (G.inv G.one) (k + 1) = G.one
    have hinv : G.inv G.one = G.one := (G.inv_eq_of_mul_eq_one (G.one_mul G.one)).symm
    rw [hinv]
    exact q9nt_one_npow G (k + 1)

/-! ## q9nt-0: Z₉ = scalar(ζ₉⁻¹)・中心性・位数ちょうど 9（mod-2→mod-9 の核） -/

/-- ζ₉⁻¹ の実担体 (0, ζ₉U⁻¹) ∈ M^× = q9tlMx（付値 0・単数 ζ₉⁻¹）。 -/
def q9ntZw : q9tlMx.carrier := ((0 : Int), q3kU.inv q9tlZeta9U)

/-- 純スカラー準同型 M^× → M₉（c ↦ ((c,0),1)）。 -/
def q9ntScalar (c : q9tlMx.carrier) : q9mtCar := ((c, (0 : Int)), q9tlMx.one)

/-- **q9nt-0a: Z₉ := scalar(ζ₉⁻¹)** — 代理シクロトーム生成元の wild level-9 実担体
    （q3nt の Z=−1（位数 2）を μ₉⊂U₃ の原始 9 乗根の逆へ昇格）。 -/
def q9ntZ9 : q9mtCar := q9ntScalar q9ntZw

/-- 純スカラー準同型 q9tlMx → q9mtM。 -/
def q9ntScalarHom : Hom q9tlMx q9mtM where
  map := q9ntScalar
  map_mul := by
    intro c c'
    show ((q9tlMx.mul c c', (0 : Int)), q9tlMx.one)
       = ((q9tlMx.mul (q9tlMx.mul c c') (tateZpow q9tlMx q9tlMx.one 0), (0 : Int) + 0),
          q9tlMx.mul q9tlMx.one q9tlMx.one)
    have h00 : (0 : Int) + 0 = 0 := by omega
    rw [tateZpow_zero, q9tlMx.mul_one, q9tlMx.one_mul, h00]

/-- **q9nt-0b: Z₉ の中心性**（純スカラー・cocycle 成分 1 行・M^× 可換 q9tlComm）。 -/
theorem q9nt_Z_central (g : q9mtCar) : q9mtM.mul q9ntZ9 g = q9mtM.mul g q9ntZ9 := by
  obtain ⟨⟨c, a⟩, w⟩ := g
  show ((q9tlMx.mul (q9tlMx.mul q9ntZw c) (tateZpow q9tlMx w 0), (0 : Int) + a),
          q9tlMx.mul q9tlMx.one w)
     = ((q9tlMx.mul (q9tlMx.mul c q9ntZw) (tateZpow q9tlMx q9tlMx.one a), a + (0 : Int)),
          q9tlMx.mul w q9tlMx.one)
  have hA : (0 : Int) + a = a + (0 : Int) := by omega
  have hW : q9tlMx.mul q9tlMx.one w = q9tlMx.mul w q9tlMx.one := by
    rw [q9tlMx.one_mul, q9tlMx.mul_one]
  have hC : q9tlMx.mul (q9tlMx.mul q9ntZw c) (tateZpow q9tlMx w 0)
      = q9tlMx.mul (q9tlMx.mul c q9ntZw) (tateZpow q9tlMx q9tlMx.one a) := by
    rw [tateZpow_zero, q9nt_one_zpow, q9tlMx.mul_one, q9tlMx.mul_one, q9tlComm q9ntZw c]
  rw [hA, hW, hC]

/-- **q9nt-0c: Z₉⁹ = 1**（位数は 9 を割る・q9tl_zpow9 の subtype 化＋スカラー準同型）。 -/
theorem q9nt_Z9_pow9 : tateNpow q9mtM q9ntZ9 9 = q9mtM.one := by
  have hh : tateNpow q9mtM q9ntZ9 9 = q9ntScalarHom.map (tateNpow q9tlMx q9ntZw 9) :=
    (hom_map_tnpow q9ntScalarHom q9ntZw 9).symm
  rw [hh]
  have hz : tateNpow q9tlMx q9ntZw 9 = q9tlMx.one := by
    apply Prod.ext
    · show (tateNpow q9tlMx q9ntZw 9).1 = (0 : Int)
      rw [q9tl_npow_fst q9ntZw 9, tateNpow_intGrp]
      show (9 : Int) * (0 : Int) = 0
      omega
    · show (tateNpow q9tlMx q9ntZw 9).2 = q3kU.one
      rw [q9tl_npow_snd q9ntZw 9]
      show tateNpow q3kU (q3kU.inv q9tlZeta9U) 9 = q3kU.one
      have e1 : tateNpow q3kU (q3kU.inv q9tlZeta9U) 9
          = q3kU.inv (tateNpow q3kU q9tlZeta9U 9) := by
        have a1 : tateZpow q3kU (q3kU.inv q9tlZeta9U) (Int.ofNat 9)
            = tateZpow q3kU q9tlZeta9U (-(Int.ofNat 9)) :=
          grp_zpow_inv_base q3kU q9tlZeta9U (Int.ofNat 9)
        have a2 : tateZpow q3kU q9tlZeta9U (-(Int.ofNat 9))
            = q3kU.inv (tateZpow q3kU q9tlZeta9U (Int.ofNat 9)) :=
          tateZpow_neg q3kU q9tlZeta9U (Int.ofNat 9)
        exact a1.trans a2
      have e3 : tateNpow q3kU q9tlZeta9U 9 = q3kU.one := Subtype.ext q9tl_zpow9
      rw [e1, e3, Grp.inv_one]
  rw [hz]
  exact q9ntScalarHom.map_one

/-- **q9nt-0d: Z₉ ≠ 1**（ζ₉⁻¹≠1・q3k_zeta9_ne_one）。 -/
theorem q9nt_Z9_ne_one : q9ntZ9 ≠ q9mtM.one := by
  intro h
  have h2 : q3kU.inv q9tlZeta9U = q3kU.one := congrArg (fun t => t.1.1.2) h
  have hz : q9tlZeta9U = q3kU.one := by
    have hh := congrArg q3kU.inv h2
    rw [Grp.inv_inv, Grp.inv_one] at hh
    exact hh
  exact q3k_zeta9_ne_one (congrArg Subtype.val hz)

/-- **q9nt-0e: Z₉ᵏ ≠ 1 (0<k<9)** — 位数ちょうど 9（q9tl_zeta9U_pow_ne の逆冪化・
    mod-2→mod-9 昇格の headline の核）。 -/
theorem q9nt_Z9_npow_ne (k : Nat) (h0 : 0 < k) (h9 : k < 9) :
    tateNpow q9mtM q9ntZ9 k ≠ q9mtM.one := by
  intro h
  have hs : tateNpow q9mtM q9ntZ9 k = q9ntScalarHom.map (tateNpow q9tlMx q9ntZw k) :=
    (hom_map_tnpow q9ntScalarHom q9ntZw k).symm
  rw [hs] at h
  have hc : tateNpow q9tlMx q9ntZw k = q9tlMx.one := congrArg (fun t => t.1.1) h
  have h2 : tateNpow q3kU (q3kU.inv q9tlZeta9U) k = q3kU.one := by
    have hh := congrArg Prod.snd hc
    rw [q9tl_npow_snd q9ntZw k] at hh
    exact hh
  have h3 : tateNpow q3kU q9tlZeta9U k = q3kU.one := by
    have e1 : tateNpow q3kU (q3kU.inv q9tlZeta9U) k
        = q3kU.inv (tateNpow q3kU q9tlZeta9U k) := by
      have a1 : tateZpow q3kU (q3kU.inv q9tlZeta9U) (Int.ofNat k)
          = tateZpow q3kU q9tlZeta9U (-(Int.ofNat k)) :=
        grp_zpow_inv_base q3kU q9tlZeta9U (Int.ofNat k)
      have a2 : tateZpow q3kU q9tlZeta9U (-(Int.ofNat k))
          = q3kU.inv (tateZpow q3kU q9tlZeta9U (Int.ofNat k)) :=
        tateZpow_neg q3kU q9tlZeta9U (Int.ofNat k)
      exact a1.trans a2
    rw [e1] at h2
    have hh := congrArg q3kU.inv h2
    rw [Grp.inv_inv, Grp.inv_one] at hh
    exact hh
  exact q9tl_zeta9U_pow_ne k h0 h9 h3

/-! ## q9nt-1: 基本関係 X·Y = Z₉·(Y·X)（q9mt 交換子＋grp_comm_rel）・zpow 中心冪 -/

/-- **q9nt-1a: 基本関係式** X·Y = Z₉·(Y·X)（X=q9mtG3・Y=q9mtGZeta・
    [X,Y]=(ζ₉⁻¹,0,1)=Z₉・q9mt_comm_eq_weil + q9mt_weil_g3_gz + 一般 grp_comm_rel）。 -/
theorem q9nt_rel : q9mtMul q9mtG3 q9mtGZeta = q9mtMul q9ntZ9 (q9mtMul q9mtGZeta q9mtG3) := by
  have hZ : q9mtComm q9mtG3 q9mtGZeta = q9ntZ9 := by
    rw [q9mt_comm_eq_weil, q9mt_weil_g3_gz]
    rfl
  show q9mtM.mul q9mtG3 q9mtGZeta = q9mtM.mul q9ntZ9 (q9mtM.mul q9mtGZeta q9mtG3)
  rw [← hZ]
  exact (grp_comm_rel q9mtM q9mtG3 q9mtGZeta).symm

/-- **q9nt-0f: Z₉ の整数冪＝スカラー(ζ₉⁻¹)^c**（スカラー準同型の zpow 保存・μ₉ 値露出）。 -/
theorem q9nt_Z9_zpow (c : Int) :
    tateZpow q9mtM q9ntZ9 c = q9ntScalarHom.map (tateZpow q9tlMx q9ntZw c) :=
  (hom_map_zpow q9ntScalarHom q9ntZw c).symm

/-! ## q9nt-2: 一般 y-first 積規則（q3nt_braid 消費・新イディオム 0）と Φ₉ -/

/-- **q9nt-2a: 一般 Grp の y-first 積規則**（q3nt_phi_prod の一般化・braiding と中心性のみ）:
    (Yᵇ Xᵃ Zᶜ)(Yᵇ' Xᵃ' Zᶜ') = Yᵇ⁺ᵇ' Xᵃ⁺ᵃ' Z^{c+c'+ab'}（z 中心・X·Y=Z·(Y·X)）。
    新規イディオム 0——braiding は q3nt_braid（一般 Grp 既証明）をそのまま消費。 -/
theorem grp_yfirst_prod (G : Grp) (x y z : G.carrier)
    (hz : ∀ g, G.mul z g = G.mul g z) (hrel : G.mul x y = G.mul z (G.mul y x))
    (a b c a' b' c' : Int) :
    G.mul (G.mul (tateZpow G y b) (G.mul (tateZpow G x a) (tateZpow G z c)))
        (G.mul (tateZpow G y b') (G.mul (tateZpow G x a') (tateZpow G z c')))
      = G.mul (tateZpow G y (b + b'))
          (G.mul (tateZpow G x (a + a')) (tateZpow G z (c + c' + a * b'))) := by
  have hzc := grp_zpow_central G z hz
  have hbr := q3nt_braid G x y z hz hrel
  rw [G.mul_assoc (tateZpow G y b)
        (G.mul (tateZpow G x a) (tateZpow G z c))
        (G.mul (tateZpow G y b')
          (G.mul (tateZpow G x a') (tateZpow G z c'))),
      G.mul_assoc (tateZpow G x a) (tateZpow G z c)
        (G.mul (tateZpow G y b')
          (G.mul (tateZpow G x a') (tateZpow G z c'))),
      ← G.mul_assoc (tateZpow G z c) (tateZpow G y b')
        (G.mul (tateZpow G x a') (tateZpow G z c')),
      hzc c (tateZpow G y b'),
      G.mul_assoc (tateZpow G y b') (tateZpow G z c)
        (G.mul (tateZpow G x a') (tateZpow G z c')),
      ← G.mul_assoc (tateZpow G z c) (tateZpow G x a')
        (tateZpow G z c'),
      hzc c (tateZpow G x a'),
      G.mul_assoc (tateZpow G x a') (tateZpow G z c)
        (tateZpow G z c'),
      ← G.mul_assoc (tateZpow G x a) (tateZpow G y b')
        (G.mul (tateZpow G x a')
          (G.mul (tateZpow G z c) (tateZpow G z c'))),
      hbr a b',
      G.mul_assoc (tateZpow G z (a * b'))
        (G.mul (tateZpow G y b') (tateZpow G x a))
        (G.mul (tateZpow G x a')
          (G.mul (tateZpow G z c) (tateZpow G z c'))),
      G.mul_assoc (tateZpow G y b') (tateZpow G x a)
        (G.mul (tateZpow G x a')
          (G.mul (tateZpow G z c) (tateZpow G z c'))),
      ← G.mul_assoc (tateZpow G y b) (tateZpow G z (a * b'))
        (G.mul (tateZpow G y b')
          (G.mul (tateZpow G x a)
            (G.mul (tateZpow G x a')
              (G.mul (tateZpow G z c) (tateZpow G z c'))))),
      ← hzc (a * b') (tateZpow G y b),
      G.mul_assoc (tateZpow G z (a * b')) (tateZpow G y b)
        (G.mul (tateZpow G y b')
          (G.mul (tateZpow G x a)
            (G.mul (tateZpow G x a')
              (G.mul (tateZpow G z c) (tateZpow G z c'))))),
      ← tateZpow_add G z c c',
      ← G.mul_assoc (tateZpow G x a) (tateZpow G x a')
        (tateZpow G z (c + c')),
      ← tateZpow_add G x a a',
      ← G.mul_assoc (tateZpow G y b) (tateZpow G y b')
        (G.mul (tateZpow G x (a + a')) (tateZpow G z (c + c'))),
      ← tateZpow_add G y b b',
      ← G.mul_assoc (tateZpow G z (a * b')) (tateZpow G y (b + b'))
        (G.mul (tateZpow G x (a + a')) (tateZpow G z (c + c'))),
      hzc (a * b') (tateZpow G y (b + b')),
      G.mul_assoc (tateZpow G y (b + b')) (tateZpow G z (a * b'))
        (G.mul (tateZpow G x (a + a')) (tateZpow G z (c + c'))),
      ← G.mul_assoc (tateZpow G z (a * b')) (tateZpow G x (a + a'))
        (tateZpow G z (c + c')),
      hzc (a * b') (tateZpow G x (a + a')),
      G.mul_assoc (tateZpow G x (a + a')) (tateZpow G z (a * b'))
        (tateZpow G z (c + c')),
      ← tateZpow_add G z (a * b') (c + c'),
      Int.add_comm (a * b') (c + c')]

/-- **q9nt-2b（★）: Φ₉ : thetaGrp → q9mtM**（v=(a,b,c) ↦ Yᵇ·Xᵃ·Z₉ᶜ・本物の準同型）。 -/
def q9ntPhi : Hom thetaGrp q9mtM where
  map := fun v => q9mtM.mul (tateZpow q9mtM q9mtGZeta v.2.1)
    (q9mtM.mul (tateZpow q9mtM q9mtG3 v.1) (tateZpow q9mtM q9ntZ9 v.2.2))
  map_mul := by
    intro v w
    obtain ⟨a, b, c⟩ := v
    obtain ⟨a', b', c'⟩ := w
    exact (grp_yfirst_prod q9mtM q9mtG3 q9mtGZeta q9ntZ9 q9nt_Z_central q9nt_rel
      a b c a' b' c').symm

/-- **q9nt-2c: 中心の実現** Φ₉(0,0,k) = Z₉ᵏ（幾何座標消滅・純スカラーのみ）。 -/
theorem q9nt_phi_center (k : Int) :
    q9ntPhi.map ((0, 0, k) : Int × Int × Int) = tateZpow q9mtM q9ntZ9 k := by
  show q9mtM.mul (tateZpow q9mtM q9mtGZeta 0)
      (q9mtM.mul (tateZpow q9mtM q9mtG3 0) (tateZpow q9mtM q9ntZ9 k)) = tateZpow q9mtM q9ntZ9 k
  rw [tateZpow_zero, tateZpow_zero, q9mtM.one_mul, q9mtM.one_mul]

/-- **q9nt-2d（★ headline）: 実シクロトーム生成元** Φ₉(0,0,1) = Z₉。 -/
theorem q9nt_cyclotome_real : q9ntPhi.map ((0, 0, 1) : Int × Int × Int) = q9ntZ9 := by
  rw [q9nt_phi_center, tateZpow_one]

/-- **q9nt-2e（★）: シクロトーム生成元は非自明** Φ₉(0,0,1) = Z₉ ≠ 1。 -/
theorem q9nt_cyclotome_ne_one : q9ntPhi.map ((0, 0, 1) : Int × Int × Int) ≠ q9mtM.one := by
  rw [q9nt_cyclotome_real]; exact q9nt_Z9_ne_one

/-- **q9nt-2f（★★ mod-2→mod-9）: シクロトーム生成元の位数はちょうど 9** —
    Φ₉(0,0,1)⁹ = 1 かつ 0<k<9 で Φ₉(0,0,1)ᵏ ≠ 1。代理シクロトーム ℤ の実現が初めて
    2-冪でない wild 円分値（原始 9 乗根）に届く（q3nt の位数 2 からの質的昇格）。 -/
theorem q9nt_cyclotome_pow9 : tateNpow q9mtM (q9ntPhi.map ((0, 0, 1) : Int × Int × Int)) 9
    = q9mtM.one := by
  rw [q9nt_cyclotome_real]; exact q9nt_Z9_pow9

theorem q9nt_cyclotome_order9 (k : Nat) (h0 : 0 < k) (h9 : k < 9) :
    tateNpow q9mtM (q9ntPhi.map ((0, 0, 1) : Int × Int × Int)) k ≠ q9mtM.one := by
  rw [q9nt_cyclotome_real]; exact q9nt_Z9_npow_ne k h0 h9

/-! ## q9nt-3: 部分群所属（Φ₉ の像はテータ群 q9mtGrp 内） -/

/-- テータ群条件は Nat 冪で閉じる。 -/
theorem q9nt_mem_npow (g : q9mtCar) (hg : q9mtMem g) (k : Nat) :
    q9mtMem (tateNpow q9mtM g k) := by
  induction k with
  | zero => exact q9mt_mem_one
  | succ k ih =>
    show q9mtMem (q9mtMul (tateNpow q9mtM g k) g)
    exact q9mt_mem_mul _ _ ih hg

/-- **q9nt-3a: 部分群 zpow 閉性** — テータ群 q9mtGrp は整数冪で閉じる。 -/
theorem q9nt_mem_zpow (g : q9mtCar) (hg : q9mtMem g) (n : Int) :
    q9mtMem (tateZpow q9mtM g n) := by
  cases n with
  | ofNat k => exact q9nt_mem_npow g hg k
  | negSucc k =>
    show q9mtMem (tateNpow q9mtM (q9mtInv g) (k + 1))
    exact q9nt_mem_npow (q9mtInv g) (q9mt_mem_inv g hg) (k + 1)

/-- Z₉ ∈ テータ群（純スカラー・qᵃw⁹ = 1·q⁰=1 と 1⁹=1）。 -/
theorem q9nt_Z9_mem : q9mtMem q9ntZ9 := by
  show q9tlMx.mul (tateZpow q9tlMx q9tlQ 0) (tateZpow q9tlMx q9tlMx.one 9) = q9tlMx.one
  rw [tateZpow_zero, q9nt_one_zpow, q9tlMx.one_mul]

/-- **q9nt-3b: Φ₉ の像はテータ群 q9mtGrp 内**（X,Y,Z₉∈q9mtGrp・部分群閉性）。 -/
theorem q9nt_phi_mem (v : thetaGrp.carrier) : q9mtMem (q9ntPhi.map v) := by
  obtain ⟨a, b, c⟩ := v
  show q9mtMem (q9mtM.mul (tateZpow q9mtM q9mtGZeta b)
    (q9mtM.mul (tateZpow q9mtM q9mtG3 a) (tateZpow q9mtM q9ntZ9 c)))
  exact q9mt_mem_mul _ _ (q9nt_mem_zpow q9mtGZeta q9mt_gz_mem b)
    (q9mt_mem_mul _ _ (q9nt_mem_zpow q9mtG3 q9mt_g3_mem a) (q9nt_mem_zpow q9ntZ9 q9nt_Z9_mem c))

/-! ## q9nt-4: Ψ₉ — 代理 tempered π₁（thetaGrp ⋊ ℤ）の実現 -/

/-- **q9nt-4a（★）: Ψ₉ : tpeGroup → q9mtM**（((a,b,c),n) ↦ Yᵇ·X^{a+n}·Z₉ᶜ・本物の準同型）。 -/
def q9ntPsi : Hom tpeGroup q9mtM where
  map := fun p => q9mtM.mul (tateZpow q9mtM q9mtGZeta p.1.2.1)
    (q9mtM.mul (tateZpow q9mtM q9mtG3 (p.1.1 + p.2)) (tateZpow q9mtM q9ntZ9 p.1.2.2))
  map_mul := by
    intro p pp
    obtain ⟨⟨a, b, c⟩, n⟩ := p
    obtain ⟨⟨a', b', c'⟩, n'⟩ := pp
    show q9mtM.mul (tateZpow q9mtM q9mtGZeta (b + b'))
         (q9mtM.mul (tateZpow q9mtM q9mtG3 ((a + a') + (n + n')))
           (tateZpow q9mtM q9ntZ9 (c + (c' + n * b') + a * b')))
       = q9mtM.mul (q9mtM.mul (tateZpow q9mtM q9mtGZeta b)
             (q9mtM.mul (tateZpow q9mtM q9mtG3 (a + n)) (tateZpow q9mtM q9ntZ9 c)))
           (q9mtM.mul (tateZpow q9mtM q9mtGZeta b')
             (q9mtM.mul (tateZpow q9mtM q9mtG3 (a' + n')) (tateZpow q9mtM q9ntZ9 c')))
    rw [grp_yfirst_prod q9mtM q9mtG3 q9mtGZeta q9ntZ9 q9nt_Z_central q9nt_rel
         (a + n) b c (a' + n') b' c']
    have hX : (a + a') + (n + n') = (a + n) + (a' + n') := by omega
    have hZ : c + (c' + n * b') + a * b' = c + c' + (a + n) * b' := by
      rw [Int.add_mul]
      generalize a * b' = P
      generalize n * b' = Q
      omega
    rw [hX, hZ]

/-- **q9nt-4b: Ψ₉∘ι = Φ₉**（テータ部への制限が Φ₉ に一致）。 -/
theorem q9nt_psi_incl (z : thetaGrp.carrier) : q9ntPsi.map (tpeIncl.map z) = q9ntPhi.map z := by
  obtain ⟨a, b, c⟩ := z
  show q9mtM.mul (tateZpow q9mtM q9mtGZeta b)
      (q9mtM.mul (tateZpow q9mtM q9mtG3 (a + 0)) (tateZpow q9mtM q9ntZ9 c))
    = q9mtM.mul (tateZpow q9mtM q9mtGZeta b)
      (q9mtM.mul (tateZpow q9mtM q9mtG3 a) (tateZpow q9mtM q9ntZ9 c))
  have ha : a + 0 = a := by omega
  rw [ha]

/-- **q9nt-4c: deck 切断の実現** Ψ₉(s(n)) = Xⁿ（deck 切断が実半周期 [3] の冪へ乗る）。 -/
theorem q9nt_psi_deck (n : Int) : q9ntPsi.map (tpeSection.map n) = tateZpow q9mtM q9mtG3 n := by
  show q9mtM.mul (tateZpow q9mtM q9mtGZeta 0)
      (q9mtM.mul (tateZpow q9mtM q9mtG3 (0 + n)) (tateZpow q9mtM q9ntZ9 0))
    = tateZpow q9mtM q9mtG3 n
  have hn : (0 : Int) + n = n := by omega
  rw [hn, tateZpow_zero, tateZpow_zero, q9mtM.mul_one, q9mtM.one_mul]

/-! ## q9nt-5: 旗艦 1 — 代理シンプレクティック形式 ＝ 実 μ₉ Weil ペアリング -/

/-- q9mtComm（テータ群交換子）と q9mtM.comm（Grp.comm）の一致（結合律のみ）。 -/
theorem q9nt_comm_eq (g g' : q9mtCar) : q9mtComm g g' = q9mtM.comm g g' := by
  show q9mtM.mul (q9mtM.mul (q9mtM.mul g g') (q9mtM.inv g)) (q9mtM.inv g')
     = q9mtM.mul (q9mtM.mul g g') (q9mtM.mul (q9mtM.inv g) (q9mtM.inv g'))
  rw [q9mtM.mul_assoc (q9mtM.mul g g') (q9mtM.inv g) (q9mtM.inv g')]

/-- **q9nt-5a（★ 旗艦 1）: 代理シンプレクティック形式 ＝ Z₉ の μ₉ 冪** —
    [Φ₉v, Φ₉w] = Z₉^{ω(v,w)}（ω = v₁w₂−w₁v₂・q3nt の μ₂ 影が wild μ₉ へ深化）。
    Φ₉ を消去すると成立しない（左辺の主語は thetaGrp の代理交換子）。 -/
theorem q9nt_symplectic_real (v w : thetaGrp.carrier) :
    q9mtComm (q9ntPhi.map v) (q9ntPhi.map w)
      = tateZpow q9mtM q9ntZ9 (v.1 * w.2.1 - w.1 * v.2.1) := by
  obtain ⟨a, b, c⟩ := v
  obtain ⟨a', b', c'⟩ := w
  rw [q9nt_comm_eq, ← q9ntPhi.map_grp_comm, theta_comm, q9nt_phi_center]

/-- **q9nt-5b（★）: μ₉ 値 Weil ペアリングの露出** —
    e₉(Φ₉v,Φ₉w) = (ζ₉⁻¹)^{ω(v,w)}（q9mt_comm_eq_weil でスカラー成分を取り、実 μ₉ 値へ）。 -/
theorem q9nt_weil_eq_form (v w : thetaGrp.carrier) :
    q9mtWeil (q9ntPhi.map v) (q9ntPhi.map w)
      = tateZpow q9tlMx q9ntZw (v.1 * w.2.1 - w.1 * v.2.1) := by
  have h := q9nt_symplectic_real v w
  rw [q9mt_comm_eq_weil, q9nt_Z9_zpow] at h
  exact congrArg (fun t => t.1.1) h

/-! ## q9nt-6: 旗艦 2 — deck×テータ交換子 ＝ 実 ζ₉^{−nb}（wild 分裂直積ブロッカー discharge） -/

/-- **q9nt-6a（★ 旗艦 2）: deck×テータ交換子の実値化** —
    [Ψ₉(s n), Ψ₉(ι(a,b,c))] = Z₉^{n·b}（M424F の [s(n),ι]=ι(0,0,nb) が実 μ₉ 値へ）。 -/
theorem q9nt_deck_theta_real (n a b c : Int) :
    q9mtComm (q9ntPsi.map (tpeSection.map n))
        (q9ntPsi.map (tpeIncl.map ((a, b, c) : Int × Int × Int)))
      = tateZpow q9mtM q9ntZ9 (n * b) := by
  rw [q9nt_comm_eq, ← q9ntPsi.map_grp_comm, tpe_deck_theta_commutator, q9nt_psi_incl,
      q9nt_phi_center]

/-- **q9nt-6b（★）: deck 切断はテータ部と非可換（wild）** —
    [Ψ₉(s 1), Ψ₉(ι(0,1,0))] = Z₉ ≠ 1。分裂直積ブロッカーの level-9 discharge。 -/
theorem q9nt_deck_theta_ne_one :
    q9mtComm (q9ntPsi.map (tpeSection.map 1))
        (q9ntPsi.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int))) ≠ q9mtM.one := by
  rw [q9nt_deck_theta_real]
  have h11 : (1 : Int) * 1 = 1 := by omega
  rw [h11, tateZpow_one]
  exact q9nt_Z9_ne_one

/-! ## q9nt-7（★★ 旗艦 3・q3nt に無い）: χ 捻りの可視化 Ψ₉∘tw ≠ Ψ₉ -/

/-- **q9nt-7a（★★★）: χ 捻りは level 9 で可視** — 捻り tw:(a,b,c,n)↦(a,−b,−c,n)
    （M429F atpChi 系）に対し **Ψ₉∘tw ≠ Ψ₉**（witness ι(0,0,1)）。
    q3nt_chi_invisible（level 2 で捻り不変）の**正反対**が wild レベルで成立する:
    Ψ₉(ι(0,0,−1)) = Z₉⁻¹ ≠ Z₉ = Ψ₉(ι(0,0,1))（⟸ Z₉² ≠ 1・原始 9 乗根）。
    算術捻りが実テータ交換子に非自明に効くことが実値で初めて見える。 -/
theorem q9nt_chi_visible :
    q9ntPsi.map (((0, 0, -1) : Int × Int × Int), (0 : Int))
      ≠ q9ntPsi.map (((0, 0, 1) : Int × Int × Int), (0 : Int)) := by
  intro h
  have hL : q9ntPsi.map (((0, 0, -1) : Int × Int × Int), (0 : Int)) = q9mtM.inv q9ntZ9 := by
    show q9mtM.mul (tateZpow q9mtM q9mtGZeta 0)
        (q9mtM.mul (tateZpow q9mtM q9mtG3 (0 + 0)) (tateZpow q9mtM q9ntZ9 (-1)))
      = q9mtM.inv q9ntZ9
    have h00 : (0 : Int) + 0 = 0 := by omega
    rw [h00, tateZpow_zero, tateZpow_zero, q9mtM.one_mul, q9mtM.one_mul, tateZpow_neg,
        tateZpow_one]
  have hR : q9ntPsi.map (((0, 0, 1) : Int × Int × Int), (0 : Int)) = q9ntZ9 := by
    show q9mtM.mul (tateZpow q9mtM q9mtGZeta 0)
        (q9mtM.mul (tateZpow q9mtM q9mtG3 (0 + 0)) (tateZpow q9mtM q9ntZ9 1))
      = q9ntZ9
    have h00 : (0 : Int) + 0 = 0 := by omega
    rw [h00, tateZpow_zero, tateZpow_zero, q9mtM.one_mul, q9mtM.one_mul, tateZpow_one]
  rw [hL, hR] at h
  -- inv Z₉ = Z₉ ⟹ Z₉·Z₉ = 1 ⟹ tateNpow Z₉ 2 = 1 ⟹ 位数 9 に矛盾
  have hsq : q9mtM.mul q9ntZ9 q9ntZ9 = q9mtM.one :=
    (congrArg (q9mtM.mul q9ntZ9) h).symm.trans (q9mtM.mul_inv q9ntZ9)
  have hn2 : tateNpow q9mtM q9ntZ9 2 = q9mtM.mul q9ntZ9 q9ntZ9 := by
    show q9mtM.mul (q9mtM.mul q9mtM.one q9ntZ9) q9ntZ9 = q9mtM.mul q9ntZ9 q9ntZ9
    rw [q9mtM.one_mul]
  exact q9nt_Z9_npow_ne 2 (by omega) (by omega) (hn2.trans hsq)

/-! ## q9nt-8: wild v(q) 復元（e=6・v(q)=54=9·6） -/

/-- q9mtM の w 成分（平行移動）射影 q9mtM → q9tlMx（本物の準同型）。 -/
def q9ntW : Hom q9mtM q9tlMx where
  map := fun g => g.2
  map_mul := fun _ _ => rfl

/-- **q9nt-8a（★）: deck 切断像の半周期** (Ψ₉(s n)).w = [3]ⁿ = tateZpow q9tl3 n。 -/
theorem q9nt_deck_halfperiod (n : Int) :
    (q9ntPsi.map (tpeSection.map n)).2 = tateZpow q9tlMx q9tl3 n := by
  rw [q9nt_psi_deck]
  exact hom_map_zpow q9ntW q9mtG3 n

/-- **q9nt-8b（★）: 半周期の付値は 6n**（wild 分岐 e=6・M=ℚ₃(ζ₉) 上の v_π）。 -/
theorem q9nt_deck_val (n : Int) :
    ((q9ntPsi.map (tpeSection.map n)).2).1 = n * 6 := by
  have h6 : q9tl3.1 = (6 : Int) := rfl
  rw [q9nt_deck_halfperiod, q9tl_zpow_fst q9tl3 n, tateZpow_intGrp, h6]

/-- **q9nt-8c（★★ wild 復元）: v(q) の tempered 側 wild 復元** —
    9·v((Ψ₉(s n)).w) = v_π(qⁿ) = 54n。半周期付値 6（e=6・wild）の 9 倍が q の付値 54=9·6。
    q3nt の v(q)=2（e=1・tame）の wild 昇格。 -/
theorem q9nt_vq_wild (n : Int) :
    9 * ((q9ntPsi.map (tpeSection.map n)).2).1 = (tateZpow q9tlMx q9tlQ n).1 := by
  rw [q9nt_deck_val, q9tl_pow_fst n]
  show (9 : Int) * (n * 6) = n * 54
  omega

/-! ## q9nt-9: 正直核（level-9 崩壊）＋ capstone -/

/-- **q9nt-9a（正直核）: level-9 崩壊** — Ψ₉(ι(0,0,9)) = 1（Z₉⁹=1・シクロトーム ℤ の実現は
    mod 9 まで・Ψ₉ は単射でない）。full ẑ(1)・全素数 l は依然未達（正直限定 1）。 -/
theorem q9nt_psi_level9_collapse :
    q9ntPsi.map (tpeIncl.map ((0, 0, 9) : Int × Int × Int)) = q9mtM.one := by
  rw [q9nt_psi_incl, q9nt_phi_center]
  show tateZpow q9mtM q9ntZ9 9 = q9mtM.one
  exact q9nt_Z9_pow9

/-- **q9nt-9b: A5 N2 capstone データ** — Φ₉/Ψ₉・旗艦（μ₉ シンプレクティック・
    deck×θ=Z₉・χ 可視）・正直核（level-9 崩壊）を束ねる。主語はすべて Φ₉/Ψ₉ と
    代理対象（thetaGrp/tpeGroup）。 -/
structure Q3TemperedThetaL9Data where
  /-- Φ₉ : thetaGrp → q9mtM（代理 Heisenberg の μ₉ 群内実現）。 -/
  phi : Hom thetaGrp q9mtM
  /-- Ψ₉ : tpeGroup → q9mtM（代理 tempered π₁ の実現）。 -/
  psi : Hom tpeGroup q9mtM
  /-- Ψ₉∘ι = Φ₉。 -/
  psi_incl : ∀ z, psi.map (tpeIncl.map z) = phi.map z
  /-- 旗艦 1: 代理 ω ＝ Z₉ の μ₉ 冪。 -/
  symplectic_real : ∀ v w, q9mtComm (phi.map v) (phi.map w)
    = tateZpow q9mtM q9ntZ9 (v.1 * w.2.1 - w.1 * v.2.1)
  /-- 旗艦 2: deck×テータ交換子 ＝ Z₉^{nb}。 -/
  deck_theta_real : ∀ n a b c,
    q9mtComm (psi.map (tpeSection.map n)) (psi.map (tpeIncl.map ((a, b, c) : Int × Int × Int)))
    = tateZpow q9mtM q9ntZ9 (n * b)
  /-- deck 切断はテータ部と非可換（Z₉ ≠ 1）。 -/
  deck_theta_ne_one : q9mtComm (psi.map (tpeSection.map 1))
    (psi.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int))) ≠ q9mtM.one
  /-- headline: シクロトーム生成元の位数はちょうど 9（mod-2→mod-9）。 -/
  cyclotome_pow9 : tateNpow q9mtM (phi.map ((0, 0, 1) : Int × Int × Int)) 9 = q9mtM.one
  cyclotome_order9 : ∀ k : Nat, 0 < k → k < 9 →
    tateNpow q9mtM (phi.map ((0, 0, 1) : Int × Int × Int)) k ≠ q9mtM.one
  /-- 旗艦 3（q3nt に無い）: χ 捻り可視 Ψ₉∘tw ≠ Ψ₉（witness ι(0,0,1)）。 -/
  chi_visible : psi.map (((0, 0, -1) : Int × Int × Int), (0 : Int))
    ≠ psi.map (((0, 0, 1) : Int × Int × Int), (0 : Int))
  /-- 正直核: level-9 崩壊 Ψ₉(ι(0,0,9))=1（Ψ₉ 非単射・実現は mod 9 まで）。 -/
  level9_collapse : psi.map (tpeIncl.map ((0, 0, 9) : Int × Int × Int)) = q9mtM.one

/-- **q9nt-9c: 見出し実例** — 実 M=ℚ₃(ζ₉) 上の μ₉ テータ群 q9mtM 内での代理 tempered
    テータ骨格の wild level-9 実現。 -/
def q9ntData : Q3TemperedThetaL9Data where
  phi := q9ntPhi
  psi := q9ntPsi
  psi_incl := q9nt_psi_incl
  symplectic_real := q9nt_symplectic_real
  deck_theta_real := q9nt_deck_theta_real
  deck_theta_ne_one := q9nt_deck_theta_ne_one
  cyclotome_pow9 := q9nt_cyclotome_pow9
  cyclotome_order9 := q9nt_cyclotome_order9
  chi_visible := q9nt_chi_visible
  level9_collapse := q9nt_psi_level9_collapse

/-- **q9nt-9d（★ capstone）: 代理 tempered テータ骨格の wild level-9（μ₉）実現の存在**
    （実 M=ℚ₃(ζ₉)・q=3⁹・level 9・μ₉・χ 可視・v(q)=54=9·6 wild 復元込み）。 -/
theorem q9ntL9_exists : Nonempty Q3TemperedThetaL9Data := ⟨q9ntData⟩

end IUT
