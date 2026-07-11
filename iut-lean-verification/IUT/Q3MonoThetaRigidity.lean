/-
  IUT/Q3MonoThetaRigidity.lean — A7d（柱A A7: 実 mono-theta 円分剛性・level-2/μ₂ 忠実インスタンス）

  ── 主要成果の分類: **[実／昇格(a)+本物建設(b)]**。
     昇格(a): A7 監査 audit/A7-mono-theta-rigidity-detail-2026-07-11.md §2 が named blocker と
     した「mono-theta 円分剛性（テータ環境の自己準同型は内部 cyclotome に恒等作用する）」を、
     実テータ群 q3thGrp（IUT.Q3ThetaGroup）の上でゼロから実定理化し、A7「実円分剛性」の
     characterize-not-kill 状態に **endo 水準の非自明な KILL** を差し込む。
     本物建設(b): Klein 決定性（q^ℤ-lift をまたぐ Weil ペアリング降下・所属条件 2 本の実消費）・
     テータ両立自己準同型の全交換子保存・内部 cyclotome 生成元 q3mrZeta の恒等固定を、
     実 q3tGrp=ℚ₃^× 成分計算（tateZpow 簿記）で完全証明する。

  complete_pct 影響: **A7 のみ前進見込み**（監査 §5: A7 0.40 → 見込み 0.43・敵対的下限 0.41・
  最終値は独立監査が確定）。realizes the [EtTh] mono-theta rigidity MECHANISM at level 2 ——
  すなわち prior A7 監査群（tme/tmi/cra/cgar/crl）が一様に「不定性を CHARACTERIZE するのみで
  KILL しない」とした所を、テータ環境の cyclotomic rigidity 機構の忠実 level-2 インスタンスで
  非零化する。A8/A6/A5 の status は今回**主張しない**（§2.4 二重計上境界）。

  主要内容（監査 §3 の定理列 1–10）:
  (1)  q3mr_proj_eq_shift: proj x=proj y ⟹ ∃k, y=x·qᵏ（quotientProjN_ker + inv 簿記）。
  (2)  q3mr_weil_klein_left (★): 鍵補題。Klein 決定性（左引数）—— 差分因子
       (−2k(j'+a'), (u₀'²)^{−k}) = 1 が **所属 a'=−j' と u₀'²=1 の両方を実消費**して閉じる。
  (3)  q3mr_weil_klein_right (★): 第 2 引数版（g の所属 w²=q^{−a} を消費）。
  (4)  q3mr_hom_one / q3mr_hom_inv: 所属限定 hom の単位・逆元保存（消去律）。
  (5)  q3mr_rigidity (★★): 主定理 —— **自己準同型** φ が所属限定 hom・所属保存・Klein 上恒等
       なら全交換子を保存する（φ(comm g g')=comm g g'）。単射仮定なし（endo）が非自明の核。
  (6)  q3mrZeta := q3thScalar((0,q3tNegOne))・q3mr_zeta_eq_comm（=comm(g₃,g₋₁)）・q3mr_zeta_mem。
  (7)  q3mr_cyclotome_fixed (★★★): φ(q3mrZeta)=q3mrZeta —— 内部 cyclotome への捻りゼロ。
  (8)  q3mr_mu2_killed (★★): 内部 μ₂={1,q3mrZeta} 上の誘導作用は endo クラス全体で恒等。
  (9)  q3mr_klein_fails_on_M (★): M 上反例。所属仮定が load-bearing であることの機械可検証な証拠
       （鍵補題は q3th_comm_eq_weil の系ではない）。
  (10) q3mr_inner_example: 内部自己同型 conj_h が仮定クラスに入る（非空性 witness）。

  正直な限定（監査 §4 準拠・消去/弱化しない・既存 surrogate/正直申告は消さない）:
  1. **殺した群は「テータ両立 endo の内部 μ₂ への作用」であり Aut(ℤ₃(1))=ℤ₃^× ではない**。
     rigidify された cyclotome は μ₂（3 と素）であって ℤ₃(1) ではない。tmi の ℤ₃^× 不定性
     （3-冪円分塔上・TateModuleIndeterminacy）は本定理の後も**まるごと残存（SURVIVES）**する。
     ℤ₃^×→Aut(μ₂) が算術的に自明（u 奇数ゆえ (−1)ᵘ=−1）である事実は隠さない。本ステップは
     MECHANISM + endo 水準の KILL であって **full ℤ₃^× KILL ではない**（それには μ_{3ⁿ} 水準の
     テータ環境＝実 ℚ₃(ζ₃)（分岐 2 次拡大）が要る・named future target）。
  2. 全単射 φ に限れば系 7 は安く出る（唯一の位数 2 元）。非安価な内容は **endo 版**＋Klein 決定性
     ＋全交換子保存（機構）。q3mr_rigidity は bijective に弱めていない。
  3. **level 2/p=3/q=9/μ₂ 単一切片**。μ_{3ⁿ} 水準は後続。
  4. **Galois 作用ゼロ**（監査 §2.1: tmzActHom は 3-冪円分塔 cmrGrp に作用し、ℚ₃^×-built な
     テータ台と交わらない・μ₂⊂ℚ₃ は Galois 固定で自由）。空虚な同変仮定は足さない。
  5. **Klein 降下ペアリングの関数化はしない**（∃k は Prop ゴール内で破壊するのみ・関係式形に
     留める・choice 回避）。実テータ関数・π₁-同定は依然 0（q3th の正直限定を不変更で保持）。
  6. **二重計上境界（監査 §2.4）**: q3th 定理は**消費のみ・再証明ゼロ**。tmi/q3nt/crl は
     import しない。比較準同型は作らない。q3mrZeta は定義 1 行の重複（q3ntZ と同一元だが
     q3nt を import しない）。crl/crc の「復元は ℤ₃^× torsor」・tmi の「同変性は空」は消さない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。
-/
import IUT.Q3ThetaGroup

namespace IUT

/-! ## q3mr-helpers: 整数冪の合成則（q3tGrp 上・choice-free） -/

/-- **q3mr-h1: 冪の冪（自然数側）** (gᵐ)^j = g^{m·j}（j:Nat）。 -/
theorem q3mr_zpow_npow (g : q3tGrp.carrier) (m : Int) : ∀ j : Nat,
    tateNpow q3tGrp (tateZpow q3tGrp g m) j = tateZpow q3tGrp g (m * (j : Int)) := by
  intro j
  induction j with
  | zero =>
    have h0 : m * ((0 : Nat) : Int) = 0 := by omega
    calc tateNpow q3tGrp (tateZpow q3tGrp g m) 0
        = q3tGrp.one := rfl
      _ = tateZpow q3tGrp g 0 := rfl
      _ = tateZpow q3tGrp g (m * ((0 : Nat) : Int)) := by rw [h0]
  | succ j ih =>
    show q3tGrp.mul (tateNpow q3tGrp (tateZpow q3tGrp g m) j) (tateZpow q3tGrp g m)
        = tateZpow q3tGrp g (m * ((j + 1 : Nat) : Int))
    rw [ih, ← tateZpow_add]
    have hexp : m * ((j : Nat) : Int) + m = m * ((j + 1 : Nat) : Int) := by
      have hc : ((j + 1 : Nat) : Int) = ((j : Nat) : Int) + 1 := by omega
      rw [hc, Int.mul_add, Int.mul_one]
    rw [hexp]

/-- **q3mr-h2: 冪の冪（全整数）** (gᵐ)ⁿ = g^{m·n}（全 m,n:ℤ）。負冪側は逆底へ帰着。 -/
theorem q3mr_zpow_zpow (g : q3tGrp.carrier) (m n : Int) :
    tateZpow q3tGrp (tateZpow q3tGrp g m) n = tateZpow q3tGrp g (m * n) := by
  cases n with
  | ofNat j =>
    show tateNpow q3tGrp (tateZpow q3tGrp g m) j = tateZpow q3tGrp g (m * (j : Int))
    exact q3mr_zpow_npow g m j
  | negSucc k =>
    show tateNpow q3tGrp (q3tGrp.inv (tateZpow q3tGrp g m)) (k + 1)
        = tateZpow q3tGrp g (m * (Int.negSucc k))
    have hinv : q3tGrp.inv (tateZpow q3tGrp g m) = tateZpow q3tGrp g (-m) :=
      (tateZpow_neg q3tGrp g m).symm
    rw [hinv, q3mr_zpow_npow g (-m) (k + 1)]
    have hexp : (-m) * ((k + 1 : Nat) : Int) = m * (Int.negSucc k) := by
      have hns : (Int.negSucc k) = -((k + 1 : Nat) : Int) := by omega
      rw [hns, Int.mul_neg, Int.neg_mul]
    rw [hexp]

/-- **q3mr-h3: 偶冪はスカラー二乗の冪** g^{2n} = (g·g)ⁿ（可換・q3th_zpow_mul 消費）。 -/
theorem q3mr_zpow_two (g : q3tGrp.carrier) (n : Int) :
    tateZpow q3tGrp g (2 * n) = tateZpow q3tGrp (q3tGrp.mul g g) n := by
  have h : (2 * n : Int) = n + n := by omega
  rw [h, tateZpow_add, q3th_zpow_mul]

/-! ## q3mr-1: proj 相等 ⟹ q^ℤ-shift（Klein 降下の関係式・∃ は Prop 内破壊のみ） -/

/-- **q3mr-1（★）: proj x=proj y ⟹ ∃k, y=x·qᵏ**（quotientProjN_ker + inv 簿記）。
    ∃k は Prop ゴール内で破壊するのみ・witness 関数化しない（choice 回避・§4-5）。 -/
theorem q3mr_proj_eq_shift (x y : q3tGrp.carrier)
    (h : (q3tProj 2).map x = (q3tProj 2).map y) :
    ∃ k : Int, y = q3tGrp.mul x (tateZpow q3tGrp (q3tQ 2) k) := by
  have hker : (q3tProj 2).map (q3tGrp.mul (q3tGrp.inv x) y) = (q3tCurve 2).one := by
    rw [(q3tProj 2).map_mul, (q3tProj 2).map_inv, h, (q3tCurve 2).inv_mul]
  have hmem := (quotientProjN_ker q3tGrp (q3tSubgroup 2) (q3t_normal (q3tSubgroup 2))
      (q3tGrp.mul (q3tGrp.inv x) y)).mp hker
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  rw [hk, ← q3tGrp.mul_assoc, q3tGrp.mul_inv, q3tGrp.one_mul]

/-! ## q3mr-2: ★ 鍵補題 Klein 決定性（左引数）—— 所属 2 条件の実消費 -/

/-- **q3mr-2（★）: Klein 決定性・左** — g₁,g₂,g'∈q3thGrp かつ proj(g₁.2)=proj(g₂.2)（同 Klein 像）
    ならば e(g₁,g')=e(g₂,g')。差分因子 (−2k(j'+a'), (u₀'²)^{−k}) が **g' の所属 a'=−j' と
    u₀'²=1 を両方消費**して 1 に閉じる（監査 §2.2 の実計算）。一般 M 元では偽（q3mr_klein_fails_on_M）。 -/
theorem q3mr_weil_klein_left (g1 g2 g' : q3thCar)
    (h1 : q3thMem g1) (h2 : q3thMem g2) (hg' : q3thMem g')
    (hproj : (q3tProj 2).map g1.2 = (q3tProj 2).map g2.2) :
    q3thWeil g1 g' = q3thWeil g2 g' := by
  obtain ⟨k, hk⟩ := q3mr_proj_eq_shift g1.2 g2.2 hproj
  have ha1 : g1.1.2 = -(g1.2.1) := ((q3th_mem_iff g1).mp h1).1
  have ha2 : g2.1.2 = -(g2.2.1) := ((q3th_mem_iff g2).mp h2).1
  -- 所属より w'² = q^{−a'}
  have hsq : q3tGrp.mul g'.2 g'.2 = tateZpow q3tGrp (q3tQ 2) (-(g'.1.2)) := by
    rw [Grp.inv_eq_of_mul_eq_one q3tGrp hg', tateZpow_neg]
  -- 付値: g2.2.1 = g1.2.1 + 2k
  have hval : g2.2.1 = g1.2.1 + 2 * k := by
    rw [hk]
    show g1.2.1 + (tateZpow q3tGrp (q3tQ 2) k).1 = g1.2.1 + 2 * k
    rw [q3th_q_zpow_fst k]
  -- 指数: a₂ = a₁ + (−2k)
  have haexp : g2.1.2 = g1.1.2 + (-(2 * k)) := by
    rw [ha2, hval, ha1]; omega
  -- 補正因子 B·D = 1（所属 2 条件の実消費点）
  have hBD : q3tGrp.mul (tateZpow q3tGrp g'.2 (-(2 * k)))
      (tateZpow q3tGrp (tateZpow q3tGrp (q3tQ 2) k) (-(g'.1.2))) = q3tGrp.one := by
    have hB : tateZpow q3tGrp g'.2 (-(2 * k))
        = tateZpow q3tGrp (q3tQ 2) ((-(g'.1.2)) * (-k)) := by
      have hneg : (-(2 * k) : Int) = 2 * (-k) := by omega
      rw [hneg, q3mr_zpow_two g'.2 (-k), hsq, q3mr_zpow_zpow]
    have hD : tateZpow q3tGrp (tateZpow q3tGrp (q3tQ 2) k) (-(g'.1.2))
        = tateZpow q3tGrp (q3tQ 2) (k * (-(g'.1.2))) := q3mr_zpow_zpow (q3tQ 2) k (-(g'.1.2))
    rw [hB, hD, ← tateZpow_add]
    have hexp0 : (-(g'.1.2)) * (-k) + k * (-(g'.1.2)) = 0 := by
      rw [Int.neg_mul_neg, Int.mul_neg, Int.mul_comm k (g'.1.2)]; omega
    rw [hexp0]
    exact tateZpow_zero q3tGrp (q3tQ 2)
  -- 本計算
  show q3tGrp.mul (tateZpow q3tGrp g'.2 g1.1.2) (tateZpow q3tGrp g1.2 (-(g'.1.2)))
     = q3tGrp.mul (tateZpow q3tGrp g'.2 g2.1.2) (tateZpow q3tGrp g2.2 (-(g'.1.2)))
  rw [haexp, hk, tateZpow_add, q3th_zpow_mul, q3tGrp.mul_assoc,
      q3th_lc (tateZpow q3tGrp g'.2 (-(2 * k)))
        (tateZpow q3tGrp g1.2 (-(g'.1.2)))
        (tateZpow q3tGrp (tateZpow q3tGrp (q3tQ 2) k) (-(g'.1.2))),
      hBD, q3tGrp.mul_one]

/-! ## q3mr-3: ★ 鍵補題 Klein 決定性（右引数） -/

/-- **q3mr-3（★）: Klein 決定性・右** — g,g'₁,g'₂∈q3thGrp かつ proj(g'₁.2)=proj(g'₂.2)
    ならば e(g,g'₁)=e(g,g'₂)。ここは **g の所属 w²=q^{−a} を消費**する。 -/
theorem q3mr_weil_klein_right (g g'1 g'2 : q3thCar)
    (hg : q3thMem g) (h1 : q3thMem g'1) (h2 : q3thMem g'2)
    (hproj : (q3tProj 2).map g'1.2 = (q3tProj 2).map g'2.2) :
    q3thWeil g g'1 = q3thWeil g g'2 := by
  obtain ⟨k, hk⟩ := q3mr_proj_eq_shift g'1.2 g'2.2 hproj
  have ha1 : g'1.1.2 = -(g'1.2.1) := ((q3th_mem_iff g'1).mp h1).1
  have ha2 : g'2.1.2 = -(g'2.2.1) := ((q3th_mem_iff g'2).mp h2).1
  have hsq_g : q3tGrp.mul g.2 g.2 = tateZpow q3tGrp (q3tQ 2) (-(g.1.2)) := by
    rw [Grp.inv_eq_of_mul_eq_one q3tGrp hg, tateZpow_neg]
  have hval : g'2.2.1 = g'1.2.1 + 2 * k := by
    rw [hk]
    show g'1.2.1 + (tateZpow q3tGrp (q3tQ 2) k).1 = g'1.2.1 + 2 * k
    rw [q3th_q_zpow_fst k]
  have haexp : g'2.1.2 = g'1.1.2 + (-(2 * k)) := by
    rw [ha2, hval, ha1]; omega
  have hng : -(g'1.1.2 + (-(2 * k))) = -(g'1.1.2) + 2 * k := by omega
  -- 補正因子 E·F = 1（g の所属を消費）
  have hEF : q3tGrp.mul (tateZpow q3tGrp (tateZpow q3tGrp (q3tQ 2) k) g.1.2)
      (tateZpow q3tGrp g.2 (2 * k)) = q3tGrp.one := by
    have hE : tateZpow q3tGrp (tateZpow q3tGrp (q3tQ 2) k) g.1.2
        = tateZpow q3tGrp (q3tQ 2) (k * g.1.2) := q3mr_zpow_zpow (q3tQ 2) k g.1.2
    have hF : tateZpow q3tGrp g.2 (2 * k)
        = tateZpow q3tGrp (q3tQ 2) ((-(g.1.2)) * k) := by
      rw [q3mr_zpow_two g.2 k, hsq_g, q3mr_zpow_zpow]
    rw [hE, hF, ← tateZpow_add]
    have hexp0 : k * g.1.2 + (-(g.1.2)) * k = 0 := by
      rw [Int.neg_mul, Int.mul_comm k (g.1.2)]; omega
    rw [hexp0]
    exact tateZpow_zero q3tGrp (q3tQ 2)
  show q3tGrp.mul (tateZpow q3tGrp g'1.2 g.1.2) (tateZpow q3tGrp g.2 (-(g'1.1.2)))
     = q3tGrp.mul (tateZpow q3tGrp g'2.2 g.1.2) (tateZpow q3tGrp g.2 (-(g'2.1.2)))
  rw [hk, haexp, q3th_zpow_mul, hng, tateZpow_add, q3tGrp.mul_assoc,
      q3th_lc (tateZpow q3tGrp (tateZpow q3tGrp (q3tQ 2) k) g.1.2)
        (tateZpow q3tGrp g.2 (-(g'1.1.2)))
        (tateZpow q3tGrp g.2 (2 * k)),
      hEF, q3tGrp.mul_one]

/-! ## q3mr-4: 所属限定 hom の単位・逆元保存（消去律） -/

/-- **q3mr-4a: hom は単位を保つ** φ(1)=1（消去律・φ が所属限定準同型のとき）。 -/
theorem q3mr_hom_one (φ : q3thCar → q3thCar)
    (hHom : ∀ g g', q3thMem g → q3thMem g' → φ (q3thMul g g') = q3thMul (φ g) (φ g')) :
    φ q3thOne = q3thOne := by
  have h := hHom q3thOne q3thOne q3th_mem_one q3th_mem_one
  rw [q3thOne_mul] at h
  have hone : q3thMul (φ q3thOne) q3thOne = φ q3thOne := q3thM.mul_one (φ q3thOne)
  have h2 : q3thMul (φ q3thOne) q3thOne = q3thMul (φ q3thOne) (φ q3thOne) := by
    rw [hone]; exact h
  exact (q3thM.mul_left_cancel h2).symm

/-- **q3mr-4b: hom は逆元を保つ** φ(g⁻¹)=φ(g)⁻¹（所属限定・所属閉性消費）。 -/
theorem q3mr_hom_inv (φ : q3thCar → q3thCar)
    (hHom : ∀ g g', q3thMem g → q3thMem g' → φ (q3thMul g g') = q3thMul (φ g) (φ g'))
    (g : q3thCar) (hg : q3thMem g) :
    φ (q3thInv g) = q3thInv (φ g) := by
  have h := hHom (q3thInv g) g (q3th_mem_inv g hg) hg
  rw [q3thInv_mul] at h
  rw [q3mr_hom_one φ hHom] at h
  have hb : φ g = q3thM.inv (φ (q3thInv g)) := Grp.inv_eq_of_mul_eq_one q3thM h.symm
  show φ (q3thInv g) = q3thM.inv (φ g)
  rw [hb, Grp.inv_inv]

/-! ## q3mr-5: ★★ 主定理 mono-theta 剛性（endo・全交換子保存） -/

/-- **q3mr-5（★★）: mono-theta 剛性** — φ が (i) 所属限定準同型 hHom・(ii) 所属保存 hMem・
    (iii) Klein 上恒等 hKlein を満たす**自己準同型**なら、任意の所属元 g,g' に対して
    φ(comm g g') = comm g g'（全交換子保存）。単射仮定なし（endo）が cyclotome 潰し map を
    排除する非自明点（監査 §2.3 攻撃 1）。証明: φ(comm)=comm(φg,φg')（hHom+4a/4b）＝
    ((e(φg,φg'),0),1)（q3th_comm_eq_weil）＝((e(g,g'),0),1)（鍵補題 2/3・hMem/hKlein）＝comm。 -/
theorem q3mr_rigidity (φ : q3thCar → q3thCar)
    (hHom : ∀ g g', q3thMem g → q3thMem g' → φ (q3thMul g g') = q3thMul (φ g) (φ g'))
    (hMem : ∀ g, q3thMem g → q3thMem (φ g))
    (hKlein : ∀ g, q3thMem g → (q3tProj 2).map (φ g).2 = (q3tProj 2).map g.2)
    (g g' : q3thCar) (hg : q3thMem g) (hg' : q3thMem g') :
    φ (q3thComm g g') = q3thComm g g' := by
  have hφg : q3thMem (φ g) := hMem g hg
  have hφg' : q3thMem (φ g') := hMem g' hg'
  have hmm : q3thMem (q3thMul g g') := q3th_mem_mul g g' hg hg'
  have hig : q3thMem (q3thInv g) := q3th_mem_inv g hg
  have hig' : q3thMem (q3thInv g') := q3th_mem_inv g' hg'
  have hmmig : q3thMem (q3thMul (q3thMul g g') (q3thInv g)) :=
    q3th_mem_mul _ _ hmm hig
  -- Step 1: φ が交換子語を貫通 → comm(φg,φg')
  have hcomm : φ (q3thComm g g') = q3thComm (φ g) (φ g') := by
    show φ (q3thMul (q3thMul (q3thMul g g') (q3thInv g)) (q3thInv g'))
       = q3thMul (q3thMul (q3thMul (φ g) (φ g')) (q3thInv (φ g))) (q3thInv (φ g'))
    rw [hHom _ _ hmmig hig', hHom _ _ hmm hig, hHom _ _ hg hg',
        q3mr_hom_inv φ hHom g hg, q3mr_hom_inv φ hHom g' hg']
  rw [hcomm, q3th_comm_eq_weil (φ g) (φ g'), q3th_comm_eq_weil g g']
  -- Step 2: Weil 値が Klein 決定性で不変
  have hw : q3thWeil (φ g) (φ g') = q3thWeil g g' := by
    have hL := q3mr_weil_klein_left (φ g) g (φ g') hφg hg hφg' (hKlein g hg)
    have hR := q3mr_weil_klein_right g (φ g') g' hg hφg' hg' (hKlein g' hg')
    rw [hL, hR]
  rw [hw]

/-! ## q3mr-6: ★★★ 内部 cyclotome 生成元 q3mrZeta の恒等固定 -/

/-- **q3mr-6a: 内部 cyclotome 生成元** q3mrZeta = s(−1) = (( (0,−1) ),0,1)（q3ntZ と同一元だが
    q3nt を import しない・§4-6 の正直重複）。 -/
def q3mrZeta : q3thCar := q3thScalar ((0 : Int), q3tNegOne)

/-- **q3mr-6b: q3mrZeta = comm(g₃,g₋₁)**（q3th_weil_g3_gm1 消費・非退化値 −1 の交換子担体）。 -/
theorem q3mr_zeta_eq_comm : q3thComm q3thG3 q3thGm1 = q3mrZeta := by
  rw [q3th_comm_eq_weil, q3th_weil_g3_gm1]
  rfl

/-- **q3mr-6c: q3mrZeta ∈ q3thGrp**（中心スカラー・a=0・u₀=+1 分岐）。 -/
theorem q3mr_zeta_mem : q3thMem q3mrZeta :=
  (q3th_mem_iff q3mrZeta).mpr ⟨rfl, Or.inl rfl⟩

/-- **q3mr-6d（★★★）: 内部 cyclotome の恒等固定** φ(q3mrZeta)=q3mrZeta —— テータ両立自己準同型は
    内部 cyclotome を捻れない（mono-theta 剛性 MECHANISM の実現形・監査 §2.2 系）。 -/
theorem q3mr_cyclotome_fixed (φ : q3thCar → q3thCar)
    (hHom : ∀ g g', q3thMem g → q3thMem g' → φ (q3thMul g g') = q3thMul (φ g) (φ g'))
    (hMem : ∀ g, q3thMem g → q3thMem (φ g))
    (hKlein : ∀ g, q3thMem g → (q3tProj 2).map (φ g).2 = (q3tProj 2).map g.2) :
    φ q3mrZeta = q3mrZeta := by
  have hc := q3mr_rigidity φ hHom hMem hKlein q3thG3 q3thGm1 q3th_g3_mem q3th_gm1_mem
  rw [q3mr_zeta_eq_comm] at hc
  exact hc

/-- **q3mr-7（★★）: 内部 μ₂={1,q3mrZeta} は endo クラス全体で恒等固定**（「kill」の言明形）。
    正直限定: この μ₂ は 3 と素で、tmi の ℤ₃^× 不定性はこの後も残存（§4-1）。 -/
theorem q3mr_mu2_killed (φ : q3thCar → q3thCar)
    (hHom : ∀ g g', q3thMem g → q3thMem g' → φ (q3thMul g g') = q3thMul (φ g) (φ g'))
    (hMem : ∀ g, q3thMem g → q3thMem (φ g))
    (hKlein : ∀ g, q3thMem g → (q3tProj 2).map (φ g).2 = (q3tProj 2).map g.2) :
    ∀ x, (x = q3thOne ∨ x = q3mrZeta) → φ x = x := by
  intro x hx
  cases hx with
  | inl h => rw [h]; exact q3mr_hom_one φ hHom
  | inr h => rw [h]; exact q3mr_cyclotome_fixed φ hHom hMem hKlein

/-! ## q3mr-8: ★ M 上反例（所属仮定の load-bearing 証明・鍵補題は q3th_comm_eq_weil の系でない） -/

/-- 反例 witness 1: g₁=((1,0),1) ∈ q3thGrp（a=0=−0・u₀=+1）。 -/
def q3mrWit1 : q3thCar := ((q3tGrp.one, (0 : Int)), q3tGrp.one)

/-- 反例 witness 2: g₂=((1,1),1) ∉ q3thGrp（a=1≠−0）。Klein 像は witness 1 と同一（w=1）。 -/
def q3mrWit2 : q3thCar := ((q3tGrp.one, (1 : Int)), q3tGrp.one)

/-- **q3mr-8（★）: M 上反例** — g₁∈q3thGrp・g₂∉q3thGrp が同 Klein 像（proj w 一致）を持つのに
    e(g₁,g₋₁)=1 ≠ (0,−1)=e(g₂,g₋₁)。すなわち q3mr_weil_klein_left の所属仮定は load-bearing で、
    鍵補題は q3th_comm_eq_weil（値の式）の系ではない（監査 §2.3 攻撃 1・§2.4 の機械可検証証拠）。 -/
theorem q3mr_klein_fails_on_M :
    q3thMem q3mrWit1 ∧ ¬ q3thMem q3mrWit2
    ∧ (q3tProj 2).map q3mrWit1.2 = (q3tProj 2).map q3mrWit2.2
    ∧ q3thWeil q3mrWit1 q3thGm1 ≠ q3thWeil q3mrWit2 q3thGm1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (q3th_mem_iff q3mrWit1).mpr ⟨rfl, Or.inl rfl⟩
  · intro hmem
    have h : (1 : Int) = -(0 : Int) := ((q3th_mem_iff q3mrWit2).mp hmem).1
    omega
  · rfl
  · have hw1 : q3thWeil q3mrWit1 q3thGm1 = q3tGrp.one := by
      show q3tGrp.mul (tateZpow q3tGrp q3thGm1.2 (0 : Int))
          (tateZpow q3tGrp q3tGrp.one (-(0 : Int))) = q3tGrp.one
      rw [tateZpow_zero, q3tGrp.one_mul]
      exact q3th_zpow_one_id (-(0 : Int))
    have hw2 : q3thWeil q3mrWit2 q3thGm1 = ((0 : Int), q3tNegOne) := by
      show q3tGrp.mul (tateZpow q3tGrp q3thGm1.2 (1 : Int))
          (tateZpow q3tGrp q3tGrp.one (-(0 : Int))) = ((0 : Int), q3tNegOne)
      rw [tateZpow_one, q3th_zpow_one_id (-(0 : Int)), q3tGrp.mul_one]
      rfl
    rw [hw1, hw2]
    intro h
    exact q3t_negone_ne_one (congrArg Prod.snd h).symm

/-! ## q3mr-9: 内部自己同型が仮定クラスに入る（非空性 witness） -/

/-- 内部自己同型 conj_h(x) = h·x·h⁻¹。 -/
def q3thConj (h x : q3thCar) : q3thCar := q3thMul (q3thMul h x) (q3thInv h)

/-- **q3mr-9a: conj は準同型**（一般群事実 h(gg')h⁻¹=(hgh⁻¹)(hg'h⁻¹)・所属不要）。 -/
theorem q3thConj_mul (h g g' : q3thCar) :
    q3thConj h (q3thMul g g') = q3thMul (q3thConj h g) (q3thConj h g') := by
  have hL : q3thConj h (q3thMul g g')
      = q3thM.mul (q3thM.mul (q3thM.mul h g) g') (q3thM.inv h) := by
    show q3thM.mul (q3thM.mul h (q3thM.mul g g')) (q3thM.inv h)
       = q3thM.mul (q3thM.mul (q3thM.mul h g) g') (q3thM.inv h)
    rw [← q3thM.mul_assoc h g g']
  have hR : q3thM.mul (q3thConj h g) (q3thConj h g')
      = q3thM.mul (q3thM.mul (q3thM.mul h g) g') (q3thM.inv h) := by
    show q3thM.mul (q3thM.mul (q3thM.mul h g) (q3thM.inv h))
            (q3thM.mul (q3thM.mul h g') (q3thM.inv h))
       = q3thM.mul (q3thM.mul (q3thM.mul h g) g') (q3thM.inv h)
    have key : q3thM.mul (q3thM.inv h) (q3thM.mul (q3thM.mul h g') (q3thM.inv h))
        = q3thM.mul g' (q3thM.inv h) := by
      rw [← q3thM.mul_assoc (q3thM.inv h) (q3thM.mul h g') (q3thM.inv h),
          ← q3thM.mul_assoc (q3thM.inv h) h g', q3thM.inv_mul, q3thM.one_mul]
    rw [q3thM.mul_assoc (q3thM.mul h g) (q3thM.inv h)
          (q3thM.mul (q3thM.mul h g') (q3thM.inv h)), key,
        ← q3thM.mul_assoc (q3thM.mul h g) g' (q3thM.inv h)]
  rw [hL]; exact hR.symm

/-- **q3mr-9b: conj は所属を保つ**（h,g∈q3thGrp → conj_h g∈q3thGrp・部分群閉性消費）。 -/
theorem q3thConj_mem (h g : q3thCar) (hh : q3thMem h) (hg : q3thMem g) :
    q3thMem (q3thConj h g) :=
  q3th_mem_mul _ _ (q3th_mem_mul h g hh hg) (q3th_mem_inv h hh)

/-- **q3mr-9c: conj は平行移動成分を保つ**（可換 ℚ₃^× ゆえ (conj_h g).2 = g.2）。
    ⟹ Klein 上恒等（proj 不変）。 -/
theorem q3thConj_w (h g : q3thCar) : (q3thConj h g).2 = g.2 := by
  show q3tGrp.mul (q3tGrp.mul h.2 g.2) (q3tGrp.inv h.2) = g.2
  rw [q3th_rc h.2 g.2 (q3tGrp.inv h.2), q3tGrp.mul_inv, q3tGrp.one_mul]

/-- **q3mr-9（★）: 内部自己同型は q3mr_rigidity の仮定クラスに入る**（非空性 witness）。
    conj_h は所属限定準同型・所属保存・Klein 上恒等（w 不変）を全て満たす。 -/
theorem q3mr_inner_example (h : q3thCar) (hh : q3thMem h) :
    (∀ g g', q3thMem g → q3thMem g' →
        q3thConj h (q3thMul g g') = q3thMul (q3thConj h g) (q3thConj h g'))
    ∧ (∀ g, q3thMem g → q3thMem (q3thConj h g))
    ∧ (∀ g, q3thMem g → (q3tProj 2).map (q3thConj h g).2 = (q3tProj 2).map g.2) :=
  ⟨fun g g' _ _ => q3thConj_mul h g g',
   fun g hg => q3thConj_mem h g hh hg,
   fun g _ => by rw [q3thConj_w]⟩

end IUT
