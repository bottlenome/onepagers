/-
  IUT/Q3Mu3Rigidity.lean — R4（level-3 実 mono-theta 円分剛性・μ₃ 値・初の非自明 3-冪 kill）

  ── 主要成果の分類: **[実／昇格(a)+本物建設(b)]**。
     昇格(a): q3mr（IUT.Q3MonoThetaRigidity・level-2/μ₂）が正直限定 1 で「ℤ₃^×→Aut(μ₂)
     が算術的自明ゆえ IUT 荷重の kill は 0」とした所を、R3 の実 μ₃ 値テータ群 q3m3
     （IUT.Q3Mu3ThetaGroup）の上で level-3 に昇格させる。level 3 では ℤ₃^×→Aut(μ₃)=(ℤ/3)^×
     が非自明（位数 2）——テータ剛性が内部 μ₃ の円分捻りを {id} に固定することは、
     **初めて本物の非自明自己同型（反転 ζ₃↦ζ₃²）を排除する**（＝tmi ℤ₃^× 不定性の
     mod-3 成分の kill）。
     本物建設(b): E₂₇[3] 決定性（μ₃ 値 Weil ペアリングが E₂₇[3] 像のみに依る・立方 w³
     membership 消費）・テータ両立自己準同型の全交換子保存・内部 cyclotome 生成元
     q3m3rZeta の恒等固定を、実 L₂^×=q3rqLx 成分計算で完全証明する。

  complete_pct 影響: **R4（level-3 mono-theta 剛性）＝キャンペーンの display-moving 成果**。
  監査 audit/frontier-z3x-kill-mu3n-theta-detail-2026-07-11.md §2(c)/§3/§4/§5 の R4
  マイルストーン: A7 目標 0.46–0.50。q3mr の μ₂ 自明 kill と対照的に、これは **初の genuine
  3-冪 ℤ₃^× kill（mod-3 成分 ℤ₃^×→(ℤ/3)^×=Aut(μ₃) が NON-trivial）**。最終値は独立監査が確定。
  A8/A5 は本ラウンドでは主張しない（二重計上境界）。

  主要内容（q3mr=level-2 テンプレートの立方版・prefix q3m3r）:
  (h)  q3m3r_zpow_npow / q3m3r_zpow_zpow: L₂^× 上の冪の冪 (gᵐ)ⁿ=g^{mn}（choice-free）。
  (1)  q3m3r_proj_eq_shift: E₂₇ 上 proj x=proj y ⟹ ∃k, y=x·qᵏ（q3tl の商核消費）。
  (2)  q3m3r_weil_e3_left (★): 鍵補題。μ₃ 値 Weil の E₂₇[3] 決定性（左）。差分因子が
       **g' の立方 membership w'³=q^{−a'}（μ₃ の cube）を消費**して 1 に閉じる。
  (3)  q3m3r_weil_e3_right (★): 第 2 引数版（g の立方 membership を消費）。
  (4)  q3m3r_hom_one / q3m3r_hom_inv: 所属限定 hom の単位・逆元保存（消去律）。
  (5)  q3m3r_rigidity (★★): 主定理 —— **自己準同型** φ が所属限定 hom・所属保存・E₂₇[3]
       上恒等なら全交換子を保存する。単射仮定なし（endo）。
  (6)  q3m3rZeta / q3m3r_zeta_eq_comm / q3m3r_zeta_mem: 内部 cyclotome 生成元
       =comm(g₃,g_ζ)（値 ζ₃⁻¹∈μ₃）。
  (7)  q3m3r_cyclotome_fixed (★★★): φ(q3m3rZeta)=q3m3rZeta —— 内部 μ₃ への捻りゼロ。
  (8)  q3m3r_mu3_killed (★★): 内部 μ₃={1,ζ₃⁻¹,(ζ₃⁻¹)²} 上の誘導作用は endo クラス全体で恒等。
  (9)  q3m3r_aut_mu3_nontrivial (★ 質的に新しい payoff): Aut(μ₃)≅ℤ/2 は非自明——反転
       ζ₃↦ζ₃²=ζ₃⁻¹（実共役 q3rqConj）は非恒等自己同型。よって剛性の {id} 固定は
       **本物の非自明自己同型を排除**（q3mr の μ₂ 自明ケースと対照）。
  (10) q3m3r_weil_fails_on_M (★): M 上反例（membership が load-bearing）。
  (11) Q3Mu3RigidityData / q3m3rData / q3m3r_exists: capstone。

  正直な限定（監査 §4 準拠・消去/弱化しない・追記のみ）:
  1. **殺すのは mod-3 成分（Aut(μ₃)≅ℤ/2）のみ**。ℤ₃^× の 1+3ℤ₃ 部分（pro-3 主単数側）は
     n≥2＝F-wild まで**まるごと残存（SURVIVES）**。full ℤ₃^× kill には実 wild 円分塔
     ℚ₃(ζ_{3ⁿ})（n≥2 暴分岐 e=2·3^{n−1}）が要る（named future target）。tmi の残存宣言は不変更。
  2. **q=27 は忠実部分ケース**（監査 §2(b)）。q^{1/3}=3∈ℚ₃ の立方トリックであって [EtTh] の
     q 固定 q^{1/l} 添加そのものではない。6 次暴分岐体経路は full-faithful 版の named target。
  3. **L₂/level-3/μ₃ 単一スライス**。endo 定式化（全単射でない）。E₂₇[3]-降下は関係式であって
     函数ではない（∃k は Prop ゴール内破壊のみ・choice 回避）。
  4. **実テータ関数ゼロ・π₁ 同定ゼロ・Galois 作用ゼロ**（q3mr/q3th/R1 の正直限定を継承）。
  5. **二重計上の firewall**: q3m3(R3)・q3mr(level-2 テンプレート)・R1(q3rq)・R2b(q3tl) は
     **消費のみ・再証明ゼロ**。tmi は import しない（主語は level-3 テータ剛性であって
     A8 の交換子・A7 の ℤ₃^× 特徴付けとは別物）。tmzLimit への比較橋は含めない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3MonoThetaRigidity
import IUT.Q3Mu3ThetaGroup
import IUT.Q3RamifiedQuadratic

namespace IUT

/-! ## q3m3r-helpers: 実 L₂^×（可換群 q3rqLx）上の冪の冪（choice-free） -/

/-- **q3m3r-h1: 冪の冪（自然数側）** (gᵐ)^j = g^{m·j}（j:Nat・L₂^×）。 -/
theorem q3m3r_zpow_npow (g : q3rqLx.carrier) (m : Int) : ∀ j : Nat,
    tateNpow q3rqLx (tateZpow q3rqLx g m) j = tateZpow q3rqLx g (m * (j : Int)) := by
  intro j
  induction j with
  | zero =>
    have h0 : m * ((0 : Nat) : Int) = 0 := by omega
    calc tateNpow q3rqLx (tateZpow q3rqLx g m) 0
        = q3rqLx.one := rfl
      _ = tateZpow q3rqLx g 0 := rfl
      _ = tateZpow q3rqLx g (m * ((0 : Nat) : Int)) := by rw [h0]
  | succ j ih =>
    show q3rqLx.mul (tateNpow q3rqLx (tateZpow q3rqLx g m) j) (tateZpow q3rqLx g m)
        = tateZpow q3rqLx g (m * ((j + 1 : Nat) : Int))
    rw [ih, ← tateZpow_add]
    have hexp : m * ((j : Nat) : Int) + m = m * ((j + 1 : Nat) : Int) := by
      have hc : ((j + 1 : Nat) : Int) = ((j : Nat) : Int) + 1 := by omega
      rw [hc, Int.mul_add, Int.mul_one]
    rw [hexp]

/-- **q3m3r-h2: 冪の冪（全整数）** (gᵐ)ⁿ = g^{m·n}（全 m,n:ℤ・L₂^×）。 -/
theorem q3m3r_zpow_zpow (g : q3rqLx.carrier) (m n : Int) :
    tateZpow q3rqLx (tateZpow q3rqLx g m) n = tateZpow q3rqLx g (m * n) := by
  cases n with
  | ofNat j =>
    show tateNpow q3rqLx (tateZpow q3rqLx g m) j = tateZpow q3rqLx g (m * (j : Int))
    exact q3m3r_zpow_npow g m j
  | negSucc k =>
    show tateNpow q3rqLx (q3rqLx.inv (tateZpow q3rqLx g m)) (k + 1)
        = tateZpow q3rqLx g (m * (Int.negSucc k))
    have hinv : q3rqLx.inv (tateZpow q3rqLx g m) = tateZpow q3rqLx g (-m) :=
      (tateZpow_neg q3rqLx g m).symm
    rw [hinv, q3m3r_zpow_npow g (-m) (k + 1)]
    have hexp : (-m) * ((k + 1 : Nat) : Int) = m * (Int.negSucc k) := by
      have hns : (Int.negSucc k) = -((k + 1 : Nat) : Int) := by omega
      rw [hns, Int.mul_neg, Int.neg_mul]
    rw [hexp]

/-! ## q3m3r-1: proj 相等 ⟹ q^ℤ-shift（E₂₇ 上の関係式・∃ は Prop 内破壊のみ） -/

/-- **q3m3r-1（★）: proj x=proj y ⟹ ∃k, y=x·qᵏ**（q3tl の商核 quotientProjN_ker 消費）。
    ∃k は Prop ゴール内で破壊するのみ・witness 関数化しない（choice 回避）。 -/
theorem q3m3r_proj_eq_shift (x y : q3rqLx.carrier)
    (h : q3tlProj.map x = q3tlProj.map y) :
    ∃ k : Int, y = q3rqLx.mul x (tateZpow q3rqLx q3tlQ k) := by
  have hker : q3tlProj.map (q3rqLx.mul (q3rqLx.inv x) y) = q3tlCurve.one := by
    rw [q3tlProj.map_mul, q3tlProj.map_inv, h, q3tlCurve.inv_mul]
  have hmem := (quotientProjN_ker q3rqLx q3tlSubgroup (q3tlNormal q3tlSubgroup)
      (q3rqLx.mul (q3rqLx.inv x) y)).mp hker
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  rw [hk, ← q3rqLx.mul_assoc, q3rqLx.mul_inv, q3rqLx.one_mul]

/-! ## q3m3r-2: ★ 鍵補題 E₂₇[3] 決定性（左引数）—— 立方 membership の実消費 -/

/-- **q3m3r-h3: 指数消去（純 Int）** — 付値方程式 2a+v=0（×2）と付値シフト v₂=v₁+6k から
    a₂=a₁−3k。intGrp.carrier の付値射影を genuine Int 引数に落として omega に渡す
    （q3m3_val_fwd と同型の型変換イディオム・choice-free）。 -/
theorem q3m3r_aexp (a1 a2 v1 v2 k : Int)
    (h1 : 2 * a1 + v1 = 0) (h2 : 2 * a2 + v2 = 0) (hv : v2 = v1 + k * 6) :
    a2 = a1 + (-(3 * k)) := by omega

/-- 立方 membership: g∈テータ群 ⟹ w³ = q^{−a}（μ₃ の cube・R3 q3m3Mem の整理）。 -/
theorem q3m3r_cube_of_mem (g : q3m3Car) (hg : q3m3Mem g) :
    tateZpow q3rqLx g.2 3 = tateZpow q3rqLx q3tlQ (-(g.1.2)) := by
  have hc3 : q3rqLx.mul (q3rqLx.mul g.2 g.2) g.2 = tateZpow q3rqLx g.2 3 :=
    (q3m3_cube_gen g.2).symm
  have hm : q3rqLx.mul (tateZpow q3rqLx q3tlQ g.1.2) (tateZpow q3rqLx g.2 3) = q3rqLx.one := by
    rw [← hc3]; exact hg
  rw [Grp.inv_eq_of_mul_eq_one q3rqLx hm, tateZpow_neg]

/-- **q3m3r-2（★）: E₂₇[3] 決定性・左** — g₁,g₂,g'∈q3m3Grp かつ proj(g₁.2)=proj(g₂.2)
    （同 E₂₇[3] 像）ならば e₃(g₁,g')=e₃(g₂,g')。差分因子 w'^{−3k}·(qᵏ)^{−a'} が
    **g' の立方 membership w'³=q^{−a'}（μ₃ の cube・w³）を消費**して 1 に閉じる。
    q3mr_weil_klein_left の平方 w² を立方 w³ に置換した level-3 版。 -/
theorem q3m3r_weil_e3_left (g1 g2 g' : q3m3Car)
    (h1 : q3m3Mem g1) (h2 : q3m3Mem g2) (hg' : q3m3Mem g')
    (hproj : q3tlProj.map g1.2 = q3tlProj.map g2.2) :
    q3m3Weil g1 g' = q3m3Weil g2 g' := by
  obtain ⟨k, hk⟩ := q3m3r_proj_eq_shift g1.2 g2.2 hproj
  have ha1 : 2 * g1.1.2 + g1.2.1 = 0 := ((q3m3_mem_iff g1).mp h1).1
  have ha2 : 2 * g2.1.2 + g2.2.1 = 0 := ((q3m3_mem_iff g2).mp h2).1
  -- 立方 membership（g' の w'³=q^{−a'}）
  have hcube : tateZpow q3rqLx g'.2 3 = tateZpow q3rqLx q3tlQ (-(g'.1.2)) :=
    q3m3r_cube_of_mem g' hg'
  -- 付値: g2.2.1 = g1.2.1 + k·6（v_λ(27)=6）
  have hval : g2.2.1 = g1.2.1 + k * 6 := by
    rw [hk]
    show g1.2.1 + (tateZpow q3rqLx q3tlQ k).1 = g1.2.1 + k * 6
    rw [q3tl_pow_fst k]
  -- 指数: a₂ = a₁ + (−3k)（付値方程式 2a+v=0 の消費）
  have haexp : g2.1.2 = g1.1.2 + (-(3 * k)) :=
    q3m3r_aexp g1.1.2 g2.1.2 g1.2.1 g2.2.1 k ha1 ha2 hval
  -- 補正因子 B·D = 1（立方 membership の実消費点）
  have hBD : q3rqLx.mul (tateZpow q3rqLx g'.2 (-(3 * k)))
      (tateZpow q3rqLx (tateZpow q3rqLx q3tlQ k) (-(g'.1.2))) = q3rqLx.one := by
    have hB : tateZpow q3rqLx g'.2 (-(3 * k))
        = tateZpow q3rqLx q3tlQ ((-(g'.1.2)) * (-k)) := by
      have hneg : (-(3 * k) : Int) = 3 * (-k) := by omega
      rw [hneg, ← q3m3r_zpow_zpow g'.2 3 (-k), hcube, q3m3r_zpow_zpow]
    have hD : tateZpow q3rqLx (tateZpow q3rqLx q3tlQ k) (-(g'.1.2))
        = tateZpow q3rqLx q3tlQ (k * (-(g'.1.2))) := q3m3r_zpow_zpow q3tlQ k (-(g'.1.2))
    rw [hB, hD, ← tateZpow_add]
    have hexp0 : (-(g'.1.2)) * (-k) + k * (-(g'.1.2)) = 0 := by
      rw [Int.neg_mul_neg, Int.mul_neg, Int.mul_comm k (g'.1.2)]; omega
    rw [hexp0]
    exact tateZpow_zero q3rqLx q3tlQ
  -- 本計算
  show q3rqLx.mul (tateZpow q3rqLx g'.2 g1.1.2) (tateZpow q3rqLx g1.2 (-(g'.1.2)))
     = q3rqLx.mul (tateZpow q3rqLx g'.2 g2.1.2) (tateZpow q3rqLx g2.2 (-(g'.1.2)))
  rw [haexp, hk, tateZpow_add, q3m3_zpow_mul, q3rqLx.mul_assoc,
      q3m3_lc (tateZpow q3rqLx g'.2 (-(3 * k)))
        (tateZpow q3rqLx g1.2 (-(g'.1.2)))
        (tateZpow q3rqLx (tateZpow q3rqLx q3tlQ k) (-(g'.1.2))),
      hBD, q3rqLx.mul_one]

/-! ## q3m3r-3: ★ 鍵補題 E₂₇[3] 決定性（右引数） -/

/-- **q3m3r-3（★）: E₂₇[3] 決定性・右** — g,g'₁,g'₂∈q3m3Grp かつ proj(g'₁.2)=proj(g'₂.2)
    ならば e₃(g,g'₁)=e₃(g,g'₂)。ここは **g の立方 membership w³=q^{−a} を消費**する。 -/
theorem q3m3r_weil_e3_right (g g'1 g'2 : q3m3Car)
    (hg : q3m3Mem g) (h1 : q3m3Mem g'1) (h2 : q3m3Mem g'2)
    (hproj : q3tlProj.map g'1.2 = q3tlProj.map g'2.2) :
    q3m3Weil g g'1 = q3m3Weil g g'2 := by
  obtain ⟨k, hk⟩ := q3m3r_proj_eq_shift g'1.2 g'2.2 hproj
  have ha1 : 2 * g'1.1.2 + g'1.2.1 = 0 := ((q3m3_mem_iff g'1).mp h1).1
  have ha2 : 2 * g'2.1.2 + g'2.2.1 = 0 := ((q3m3_mem_iff g'2).mp h2).1
  have hcube_g : tateZpow q3rqLx g.2 3 = tateZpow q3rqLx q3tlQ (-(g.1.2)) :=
    q3m3r_cube_of_mem g hg
  have hval : g'2.2.1 = g'1.2.1 + k * 6 := by
    rw [hk]
    show g'1.2.1 + (tateZpow q3rqLx q3tlQ k).1 = g'1.2.1 + k * 6
    rw [q3tl_pow_fst k]
  have haexp : g'2.1.2 = g'1.1.2 + (-(3 * k)) :=
    q3m3r_aexp g'1.1.2 g'2.1.2 g'1.2.1 g'2.2.1 k ha1 ha2 hval
  have hng : -(g'1.1.2 + (-(3 * k))) = -(g'1.1.2) + 3 * k := by omega
  -- 補正因子 E·F = 1（g の立方 membership を消費）
  have hEF : q3rqLx.mul (tateZpow q3rqLx (tateZpow q3rqLx q3tlQ k) g.1.2)
      (tateZpow q3rqLx g.2 (3 * k)) = q3rqLx.one := by
    have hE : tateZpow q3rqLx (tateZpow q3rqLx q3tlQ k) g.1.2
        = tateZpow q3rqLx q3tlQ (k * g.1.2) := q3m3r_zpow_zpow q3tlQ k g.1.2
    have hF : tateZpow q3rqLx g.2 (3 * k)
        = tateZpow q3rqLx q3tlQ ((-(g.1.2)) * k) := by
      rw [← q3m3r_zpow_zpow g.2 3 k, hcube_g, q3m3r_zpow_zpow]
    rw [hE, hF, ← tateZpow_add]
    have hexp0 : k * g.1.2 + (-(g.1.2)) * k = 0 := by
      rw [Int.neg_mul, Int.mul_comm k (g.1.2)]; omega
    rw [hexp0]
    exact tateZpow_zero q3rqLx q3tlQ
  show q3rqLx.mul (tateZpow q3rqLx g'1.2 g.1.2) (tateZpow q3rqLx g.2 (-(g'1.1.2)))
     = q3rqLx.mul (tateZpow q3rqLx g'2.2 g.1.2) (tateZpow q3rqLx g.2 (-(g'2.1.2)))
  rw [hk, haexp, q3m3_zpow_mul, hng, tateZpow_add, q3rqLx.mul_assoc,
      q3m3_lc (tateZpow q3rqLx (tateZpow q3rqLx q3tlQ k) g.1.2)
        (tateZpow q3rqLx g.2 (-(g'1.1.2)))
        (tateZpow q3rqLx g.2 (3 * k)),
      hEF, q3rqLx.mul_one]

/-! ## q3m3r-4: 所属限定 hom の単位・逆元保存（消去律） -/

/-- **q3m3r-4a: hom は単位を保つ** φ(1)=1（消去律）。 -/
theorem q3m3r_hom_one (φ : q3m3Car → q3m3Car)
    (hHom : ∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Mul g g') = q3m3Mul (φ g) (φ g')) :
    φ q3m3One = q3m3One := by
  have h := hHom q3m3One q3m3One q3m3_mem_one q3m3_mem_one
  rw [q3m3One_mul] at h
  have hone : q3m3M.mul (φ q3m3One) q3m3One = φ q3m3One := q3m3M.mul_one (φ q3m3One)
  have h2 : q3m3M.mul (φ q3m3One) q3m3One = q3m3M.mul (φ q3m3One) (φ q3m3One) := by
    rw [hone]; exact h
  exact (q3m3M.mul_left_cancel h2).symm

/-- **q3m3r-4b: hom は逆元を保つ** φ(g⁻¹)=φ(g)⁻¹（所属閉性消費）。 -/
theorem q3m3r_hom_inv (φ : q3m3Car → q3m3Car)
    (hHom : ∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Mul g g') = q3m3Mul (φ g) (φ g'))
    (g : q3m3Car) (hg : q3m3Mem g) :
    φ (q3m3Inv g) = q3m3Inv (φ g) := by
  have h := hHom (q3m3Inv g) g (q3m3_mem_inv g hg) hg
  rw [q3m3Inv_mul] at h
  rw [q3m3r_hom_one φ hHom] at h
  have hb : φ g = q3m3M.inv (φ (q3m3Inv g)) := Grp.inv_eq_of_mul_eq_one q3m3M h.symm
  show φ (q3m3Inv g) = q3m3M.inv (φ g)
  rw [hb, Grp.inv_inv]

/-! ## q3m3r-5: ★★ 主定理 mono-theta 剛性（endo・全交換子保存） -/

/-- **q3m3r-5（★★）: level-3 mono-theta 剛性** — φ が (i) 所属限定準同型 hHom・
    (ii) 所属保存 hMem・(iii) E₂₇[3] 上恒等 hE3 を満たす**自己準同型**なら、任意の所属元
    g,g' に対して φ(comm g g') = comm g g'（全交換子保存）。単射仮定なし（endo）が
    cyclotome 潰し map を排除する非自明点。q3mr_rigidity の level-3 版。 -/
theorem q3m3r_rigidity (φ : q3m3Car → q3m3Car)
    (hHom : ∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Mul g g') = q3m3Mul (φ g) (φ g'))
    (hMem : ∀ g, q3m3Mem g → q3m3Mem (φ g))
    (hE3 : ∀ g, q3m3Mem g → q3tlProj.map (φ g).2 = q3tlProj.map g.2)
    (g g' : q3m3Car) (hg : q3m3Mem g) (hg' : q3m3Mem g') :
    φ (q3m3Comm g g') = q3m3Comm g g' := by
  have hφg : q3m3Mem (φ g) := hMem g hg
  have hφg' : q3m3Mem (φ g') := hMem g' hg'
  have hmm : q3m3Mem (q3m3Mul g g') := q3m3_mem_mul g g' hg hg'
  have hig : q3m3Mem (q3m3Inv g) := q3m3_mem_inv g hg
  have hig' : q3m3Mem (q3m3Inv g') := q3m3_mem_inv g' hg'
  have hmmig : q3m3Mem (q3m3Mul (q3m3Mul g g') (q3m3Inv g)) :=
    q3m3_mem_mul _ _ hmm hig
  -- Step 1: φ が交換子語を貫通 → comm(φg,φg')
  have hcomm : φ (q3m3Comm g g') = q3m3Comm (φ g) (φ g') := by
    show φ (q3m3Mul (q3m3Mul (q3m3Mul g g') (q3m3Inv g)) (q3m3Inv g'))
       = q3m3Mul (q3m3Mul (q3m3Mul (φ g) (φ g')) (q3m3Inv (φ g))) (q3m3Inv (φ g'))
    rw [hHom _ _ hmmig hig', hHom _ _ hmm hig, hHom _ _ hg hg',
        q3m3r_hom_inv φ hHom g hg, q3m3r_hom_inv φ hHom g' hg']
  rw [hcomm, q3m3_comm_eq_weil (φ g) (φ g'), q3m3_comm_eq_weil g g']
  -- Step 2: Weil 値が E₂₇[3] 決定性で不変
  have hw : q3m3Weil (φ g) (φ g') = q3m3Weil g g' := by
    have hL := q3m3r_weil_e3_left (φ g) g (φ g') hφg hg hφg' (hE3 g hg)
    have hR := q3m3r_weil_e3_right g (φ g') g' hg hφg' hg' (hE3 g' hg')
    rw [hL, hR]
  rw [hw]

/-! ## q3m3r-6: ★★★ 内部 cyclotome 生成元 q3m3rZeta の恒等固定 -/

/-- **q3m3r-6a: 内部 cyclotome 生成元** q3m3rZeta = comm(g₃,g_ζ) の値
    = ((0, ζ₃⁻¹), 0, 1) ∈ q3m3Grp（μ₃ 値・q3m3_weil_g3_gz の担体）。 -/
def q3m3rZeta : q3m3Car :=
  ((((0 : Int), q3rqU.inv q3tlZeta3U), (0 : Int)), q3rqLx.one)

/-- **q3m3r-6b: q3m3rZeta = comm(g₃,g_ζ)**（q3m3_weil_g3_gz 消費・非退化 μ₃ 値 ζ₃⁻¹ の交換子）。 -/
theorem q3m3r_zeta_eq_comm : q3m3Comm q3m3G3 q3m3Gz = q3m3rZeta := by
  show q3m3Comm q3m3G3 q3m3Gz
      = ((((0 : Int), q3rqU.inv q3tlZeta3U), (0 : Int)), q3rqLx.one)
  rw [q3m3_comm_eq_weil, q3m3_weil_g3_gz]
  rfl

/-- **q3m3r-6c: q3m3rZeta ∈ q3m3Grp**（交換子ゆえ所属閉性から）。 -/
theorem q3m3r_zeta_mem : q3m3Mem q3m3rZeta := by
  rw [← q3m3r_zeta_eq_comm]
  show q3m3Mem (q3m3Mul (q3m3Mul (q3m3Mul q3m3G3 q3m3Gz) (q3m3Inv q3m3G3)) (q3m3Inv q3m3Gz))
  exact q3m3_mem_mul _ _
    (q3m3_mem_mul _ _
      (q3m3_mem_mul _ _ q3m3_g3_mem q3m3_gz_mem)
      (q3m3_mem_inv _ q3m3_g3_mem))
    (q3m3_mem_inv _ q3m3_gz_mem)

/-- **q3m3r-6d（★★★）: 内部 cyclotome の恒等固定** φ(q3m3rZeta)=q3m3rZeta —— テータ両立
    自己準同型は内部 μ₃ cyclotome を捻れない（level-3 mono-theta 剛性の実現形）。 -/
theorem q3m3r_cyclotome_fixed (φ : q3m3Car → q3m3Car)
    (hHom : ∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Mul g g') = q3m3Mul (φ g) (φ g'))
    (hMem : ∀ g, q3m3Mem g → q3m3Mem (φ g))
    (hE3 : ∀ g, q3m3Mem g → q3tlProj.map (φ g).2 = q3tlProj.map g.2) :
    φ q3m3rZeta = q3m3rZeta := by
  have hc := q3m3r_rigidity φ hHom hMem hE3 q3m3G3 q3m3Gz q3m3_g3_mem q3m3_gz_mem
  rw [q3m3r_zeta_eq_comm] at hc
  exact hc

/-- **q3m3r-7（★★）: 内部 μ₃={1,q3m3rZeta,q3m3rZeta²} は endo クラス全体で恒等固定**
    （level-3「kill」の言明形）。q3mr_mu2_killed の μ₃ 版：q3mr の μ₂（3 と素）と違い、
    この μ₃ 上で ℤ₃^×→Aut(μ₃) は非自明（q3m3r_aut_mu3_nontrivial）——初の genuine 3-冪 kill。 -/
theorem q3m3r_mu3_killed (φ : q3m3Car → q3m3Car)
    (hHom : ∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Mul g g') = q3m3Mul (φ g) (φ g'))
    (hMem : ∀ g, q3m3Mem g → q3m3Mem (φ g))
    (hE3 : ∀ g, q3m3Mem g → q3tlProj.map (φ g).2 = q3tlProj.map g.2) :
    ∀ x, (x = q3m3One ∨ x = q3m3rZeta ∨ x = q3m3Mul q3m3rZeta q3m3rZeta) → φ x = x := by
  intro x hx
  obtain h | h | h := hx
  · rw [h]; exact q3m3r_hom_one φ hHom
  · rw [h]; exact q3m3r_cyclotome_fixed φ hHom hMem hE3
  · rw [h, hHom q3m3rZeta q3m3rZeta q3m3r_zeta_mem q3m3r_zeta_mem,
        q3m3r_cyclotome_fixed φ hHom hMem hE3]

/-! ## q3m3r-8: ★ 質的に新しい payoff — Aut(μ₃)≅ℤ/2 は非自明（反転 ζ₃↦ζ₃²） -/

/-- **q3m3r-8（★ campaign の display-moving 核心）: Aut(μ₃) の非自明性** —
    実共役 q3rqConj（複素共役 √−3↦−√−3）は μ₃ 上で**反転 ζ₃↦ζ₃²=ζ₃⁻¹** として作用する
    乗法的写像であり、1 を固定し μ₃ を保つが **恒等ではない**（ζ₃≠ζ₃²）。すなわち
    Aut(μ₃)≅ℤ/2 は非自明で、テータ剛性が内部 μ₃ の cyclotome-twist を {id} に固定することは
    **本物の非自明自己同型を排除する**。q3mr の μ₂（反転 −1↦−1 が算術的自明）と対照的な
    初の genuine 3-冪 kill。 -/
theorem q3m3r_aut_mu3_nontrivial :
    (∀ x y : q3rqCar, q3rqConj (q3rqMul x y) = q3rqMul (q3rqConj x) (q3rqConj y))
    ∧ q3rqConj q3rqOne = q3rqOne
    ∧ q3rqConj q3rqZeta = q3rqZetaSq
    ∧ q3rqConj q3rqZetaSq = q3rqZeta
    ∧ q3rqConj q3rqZeta ≠ q3rqZeta := by
  refine ⟨q3rq_conj_mul, ?_, ?_, ?_, ?_⟩
  · -- conj 1 = 1
    show q3rqConj q3rqOne = q3rqOne
    apply q3rq_ext
    · rfl
    · exact z3.neg_zero
  · -- conj ζ₃ = ζ₃² （反転）
    show ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar) = q3rqZetaSq
    exact q3rq_zeta_sq_eq.symm
  · -- conj ζ₃² = ζ₃
    have hsq : q3rqZetaSq = ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar) := q3rq_zeta_sq_eq
    rw [hsq]
    show q3rqConj ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar) = q3rqZeta
    apply q3rq_ext
    · rfl
    · exact z3.neg_neg q3rqHalf
  · -- 非恒等: ζ₃ ≠ ζ₃²（第 2 成分 h ≠ −h ⟸ 2h=1≠0）
    intro h
    have h2 : z3.neg q3rqHalf = q3rqHalf := congrArg (fun p : q3rqCar => p.2) h
    have h3 : z3.add q3rqHalf (z3.neg q3rqHalf) = z3.add q3rqHalf q3rqHalf :=
      congrArg (z3.add q3rqHalf) h2
    rw [z3.add_neg q3rqHalf, q3rq_half_add_half] at h3
    exact q3rq_z3_one_ne_zero h3.symm

/-! ## q3m3r-9: ★ M 上反例（membership が load-bearing・鍵補題は q3m3_comm_eq_weil の系でない） -/

/-- 反例 witness 1: g₁=((1,0),1) ∈ q3m3Grp（=q3m3One・a=0）。 -/
def q3m3rWit1 : q3m3Car := ((q3rqLx.one, (0 : Int)), q3rqLx.one)

/-- 反例 witness 2: g₂=((1,1),1) ∉ q3m3Grp（a=1・付値方程式 2·1+0≠0）。同 E₂₇[3] 像（w=1）。 -/
def q3m3rWit2 : q3m3Car := ((q3rqLx.one, (1 : Int)), q3rqLx.one)

/-- **q3m3r-9（★）: M 上反例** — g₁∈q3m3Grp・g₂∉q3m3Grp が同 E₂₇[3] 像（proj w 一致）を
    持つのに e₃(g₁,g_ζ)=1 ≠ ζ₃=e₃(g₂,g_ζ)。すなわち q3m3r_weil_e3_left の membership 仮定は
    load-bearing で、鍵補題は q3m3_comm_eq_weil（値の式）の系ではない。 -/
theorem q3m3r_weil_fails_on_M :
    q3m3Mem q3m3rWit1 ∧ ¬ q3m3Mem q3m3rWit2
    ∧ q3tlProj.map q3m3rWit1.2 = q3tlProj.map q3m3rWit2.2
    ∧ q3m3Weil q3m3rWit1 q3m3Gz ≠ q3m3Weil q3m3rWit2 q3m3Gz := by
  refine ⟨q3m3_mem_one, ?_, rfl, ?_⟩
  · intro hmem
    have hval : (2 : Int) * 1 + (0 : Int) = 0 := ((q3m3_mem_iff q3m3rWit2).mp hmem).1
    omega
  · have hw1 : q3m3Weil q3m3rWit1 q3m3Gz = q3rqLx.one := by
      show q3rqLx.mul (tateZpow q3rqLx q3tlZeta3Elt (0 : Int))
          (tateZpow q3rqLx q3rqLx.one (-(0 : Int))) = q3rqLx.one
      rw [tateZpow_zero, q3rqLx.one_mul, q3m3_zpow_one_id]
    have hw2 : q3m3Weil q3m3rWit2 q3m3Gz = (((0 : Int), q3tlZeta3U)) := by
      show q3rqLx.mul (tateZpow q3rqLx q3tlZeta3Elt (1 : Int))
          (tateZpow q3rqLx q3rqLx.one (-(0 : Int))) = (((0 : Int), q3tlZeta3U))
      rw [tateZpow_one, q3m3_zpow_one_id, q3rqLx.mul_one]
      rfl
    rw [hw1, hw2]
    intro h
    have hu : q3rqU.one = q3tlZeta3U := congrArg Prod.snd h
    have hval : q3rqOne = q3rqZeta := congrArg Subtype.val hu
    exact q3rq_zeta_ne_one hval.symm

/-! ## q3m3r-10: capstone -/

/-- **q3m3r-10a: level-3 実 mono-theta 剛性データ** — μ₃ 値 Weil の E₂₇[3] 決定性・endo
    剛性・内部 μ₃ cyclotome 恒等固定・そして質的に新しい **Aut(μ₃) 非自明性**（初の
    genuine 3-冪 kill・q3mr の μ₂ 自明ケースと対照）を束ねる。 -/
structure Q3Mu3RigidityData where
  /-- μ₃ 値 Weil の E₂₇[3] 決定性（左）。 -/
  weilE3Left : ∀ g1 g2 g' : q3m3Car, q3m3Mem g1 → q3m3Mem g2 → q3m3Mem g' →
    q3tlProj.map g1.2 = q3tlProj.map g2.2 → q3m3Weil g1 g' = q3m3Weil g2 g'
  /-- μ₃ 値 Weil の E₂₇[3] 決定性（右）。 -/
  weilE3Right : ∀ g g'1 g'2 : q3m3Car, q3m3Mem g → q3m3Mem g'1 → q3m3Mem g'2 →
    q3tlProj.map g'1.2 = q3tlProj.map g'2.2 → q3m3Weil g g'1 = q3m3Weil g g'2
  /-- endo 剛性（全交換子保存）。 -/
  rigidity : ∀ φ : q3m3Car → q3m3Car,
    (∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Mul g g') = q3m3Mul (φ g) (φ g')) →
    (∀ g, q3m3Mem g → q3m3Mem (φ g)) →
    (∀ g, q3m3Mem g → q3tlProj.map (φ g).2 = q3tlProj.map g.2) →
    ∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Comm g g') = q3m3Comm g g'
  /-- 内部 μ₃ cyclotome の恒等固定（endo クラス全体）。 -/
  cyclotomeFixed : ∀ φ : q3m3Car → q3m3Car,
    (∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Mul g g') = q3m3Mul (φ g) (φ g')) →
    (∀ g, q3m3Mem g → q3m3Mem (φ g)) →
    (∀ g, q3m3Mem g → q3tlProj.map (φ g).2 = q3tlProj.map g.2) →
    φ q3m3rZeta = q3m3rZeta
  /-- 内部 cyclotome 生成元 = comm(g₃,g_ζ)。 -/
  zetaEqComm : q3m3Comm q3m3G3 q3m3Gz = q3m3rZeta
  /-- 生成元はテータ群の元。 -/
  zetaMem : q3m3Mem q3m3rZeta
  /-- ★ Aut(μ₃) の非自明性: 反転 ζ₃↦ζ₃²（実共役）。 -/
  autConj : q3rqConj q3rqZeta = q3rqZetaSq
  /-- ★ 反転は恒等でない（ζ₃≠ζ₃²）——q3mr の μ₂ 自明ケースと対照する genuine 3-冪 kill。 -/
  autNontrivial : q3rqConj q3rqZeta ≠ q3rqZeta

/-- **q3m3r-10b: 見出し実例** — L₂=ℚ₃(ζ₃)・q=27 上の level-3 実 mono-theta 剛性
    （μ₃ 値・初の genuine 3-冪 ℤ₃^× kill＝mod-3 成分 Aut(μ₃)）。 -/
def q3m3rData : Q3Mu3RigidityData where
  weilE3Left := q3m3r_weil_e3_left
  weilE3Right := q3m3r_weil_e3_right
  rigidity := q3m3r_rigidity
  cyclotomeFixed := q3m3r_cyclotome_fixed
  zetaEqComm := q3m3r_zeta_eq_comm
  zetaMem := q3m3r_zeta_mem
  autConj := (q3m3r_aut_mu3_nontrivial.2.2.1)
  autNontrivial := (q3m3r_aut_mu3_nontrivial.2.2.2.2)

/-- **q3m3r-10c: level-3 実 mono-theta 剛性の存在**
    （実 L₂=ℚ₃(ζ₃)・q=27・μ₃・初の genuine 3-冪 kill）。 -/
theorem q3m3r_exists : Nonempty Q3Mu3RigidityData := ⟨q3m3rData⟩

end IUT
