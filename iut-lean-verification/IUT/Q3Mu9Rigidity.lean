/-
  IUT/Q3Mu9Rigidity.lean — level-9 実 mono-theta 円分剛性（μ₉ 値・原始 9 乗根 ζ₉⁻¹ の恒等固定・
    新層 ker(Aut(μ₉)→Aut(μ₃)) = (1+3ℤ₃)/(1+9ℤ₃) の kill 機構）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**。q3m3r（IUT.Q3Mu3Rigidity・level-3/μ₃）の
     mono-theta 剛性機構を level 9（実 μ₉ 値テータ群 q9mt=IUT.Q3Mu9ThetaGroup・q=3⁹・実 U₃）へ
     写経し（E[9] 決定性・endo 剛性・cyclotome 固定＝機械的なテンプレ再インスタンス）、
     その上に **質的に新しい 2 点**を積む:
     (i) 内部 cyclotome 固定の対象が**原始 9 乗根** ζ₉⁻¹ である（テータ交換子から初の wild
         円分値の恒等固定）。level-3 の固定対象 ζ₃⁻¹ は {4,7} 型捻り（μ₃ 上恒等）に不変で
         剛性は {4,7} を排除できなかった。ζ₉⁻¹ の固定が初めてそれを排除する。
     (ii) payoff `q9mr_aut_mu9_new_layer`: σ=q3kSigma（Y↦ζ₃Y）は実 O_M の実環自己同型で
         (乗法的・σ(1)=1・μ₃ 対角を各点固定・σ(ζ₉)=ζ₉⁴≠ζ₉)。すなわち level-3 の kill 対象
         Aut(μ₃) 上では**恒等に見えるのに μ₉ 上非恒等**な本物の自己同型が実在し、level-9 剛性の
         {id} 固定はそれを排除する。q3m3r_aut_mu3_nontrivial（反転・位数 2）と対照する新層
         = ker(Aut(μ₉)→Aut(μ₃)) = {1,4,7}∖{1} ≅ (1+3ℤ₃)/(1+9ℤ₃) の非自明元を機械可読にする。

  complete_pct 影響: **0 前進**。本モジュールは新層を殺す剛性を**機構レベル**で建てる
  （level-3 で kill R4 が機構を持ち、橋 q3mb が display を動かしたのと同じ）。display を
  動かすには kill を tmi の実 ℤ₃^× に接続する橋 q9mb が要る——本ファイルはその前段。
  「complete_pct 0 前進（骨格でなく本物基盤の先行建設・新層 kill 機構の設置）」と正直申告する。

  内容（audit/level9-theta-kill-detail-2026-07-11.md §3・prefix q9mr）:
   ◇ クローン部（§3.1・テンプレ再インスタンス・新規数学ゼロ）:
     * q9mr_zpow_npow / q9mr_zpow_zpow — M^× 上の冪の冪（choice-free）
     * q9mr_proj_eq_shift — E_{3⁹} 上 proj x=proj y ⟹ ∃k, y=x·qᵏ
     * q9mr_ninth_of_mem — 9 乗 membership w⁹=q^{−a}（μ₉ の 9 乗・q3m3r_cube_of_mem の 9 乗版）
     * q9mr_aexp — 指数消去（6a+v=0・シフト 54k・a₂=a₁−9k・純 Int omega）
     * q9mr_weil_e9_left / q9mr_weil_e9_right (★) — E[9] 決定性（9 乗 membership 消費）
     * q9mr_hom_one / q9mr_hom_inv — 所属限定 hom の単位・逆元保存
     * q9mr_rigidity (★★) — endo 剛性（全交換子保存）
     * q9mr_zeta9 / q9mr_zeta_eq_comm / q9mr_zeta_mem / q9mr_cyclotome_fixed — 内部 cyclotome
       ζ₉⁻¹ = comm(g₃,g_ζ) の恒等固定
     * q9mr_weil_fails_on_M (★) — M 上反例（membership load-bearing）
   ◇ ★ 質的新規（§3.2・complete_pct を動かす実体）:
     * q9mr_zeta9_fixed (★) — 固定対象が**原始 9 乗根**（非自明・{4,7} 捻り σ が ζ₉ を動かす）
     * q9mr_aut_mu9_new_layer (★★ payoff) — σ=q3kSigma が μ₃ 対角固定・μ₉ 非恒等の実自己同型
   ◇ Q3Mu9RigidityData / q9mr_data / q9mr_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・追記のみ）:
  1. **位数 2 側の M 上共役 τ（ζ₉↦ζ₉⁻¹）は建てない**——level-3 kill 内容の再ラベルに過ぎず
     complete_pct を動かさない（named non-goal・§3.2）。
  2. **機構レベル**の kill（display を動かす橋は q9mb・後続）。本ファイル単体は tmi の実 ℤ₃^×
     不定性を殺さない（tmzLimit への比較橋を含めない）。
  3. **殺す新スライスは核 {1,4,7}∖{1}（位数 3・(1+3ℤ₃)/(1+9ℤ₃)）のみ**。1+9ℤ₃（n≥3 の全層）
     は pro-3 bulk の残り全部として**まるごと残存（SURVIVES）**。full ℤ₃^× kill には実 wild
     円分塔（named future target）が要る。
  4. **q=3⁹ は忠実部分ケースの 2 乗**（q^{1/9}=3∈ℚ₃ の 9 乗トリック・[EtTh] の q^{1/l} 添加
     そのものではない）。full-faithful 版は named target。
  5. **U₃/level-9/μ₉ 単一スライス**。endo 定式化（全単射でない）。E[9]-降下は関係式であって
     函数ではない（∃k は Prop ゴール内破壊のみ・choice 回避）。
  6. **実テータ関数ゼロ・π₁ 同定ゼロ・Galois 作用ゼロ**（q3m3r/q9mt/q9tl/q3k の正直限定を継承）。
  7. **二重計上の firewall**: q9mt（level-9 テータ群）・q9yp（Y-冪）・q3k・q3rq は**消費のみ・
     再証明ゼロ**。tmi は import しない（主語は level-9 テータ剛性）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3Mu9ThetaGroup
import IUT.Q3KummerYPow

namespace IUT

/-! ## q9mr-helpers: 実 M^×（可換群 q9tlMx）上の冪の冪（choice-free・q3m3r の写経） -/

/-- **q9mr-h1: 冪の冪（自然数側）** (gᵐ)^j = g^{m·j}（j:Nat・M^×）。 -/
theorem q9mr_zpow_npow (g : q9tlMx.carrier) (m : Int) : ∀ j : Nat,
    tateNpow q9tlMx (tateZpow q9tlMx g m) j = tateZpow q9tlMx g (m * (j : Int)) := by
  intro j
  induction j with
  | zero =>
    have h0 : m * ((0 : Nat) : Int) = 0 := by omega
    calc tateNpow q9tlMx (tateZpow q9tlMx g m) 0
        = q9tlMx.one := rfl
      _ = tateZpow q9tlMx g 0 := rfl
      _ = tateZpow q9tlMx g (m * ((0 : Nat) : Int)) := by rw [h0]
  | succ j ih =>
    show q9tlMx.mul (tateNpow q9tlMx (tateZpow q9tlMx g m) j) (tateZpow q9tlMx g m)
        = tateZpow q9tlMx g (m * ((j + 1 : Nat) : Int))
    rw [ih, ← tateZpow_add]
    have hexp : m * ((j : Nat) : Int) + m = m * ((j + 1 : Nat) : Int) := by
      have hc : ((j + 1 : Nat) : Int) = ((j : Nat) : Int) + 1 := by omega
      rw [hc, Int.mul_add, Int.mul_one]
    rw [hexp]

/-- **q9mr-h2: 冪の冪（全整数）** (gᵐ)ⁿ = g^{m·n}（全 m,n:ℤ・M^×）。 -/
theorem q9mr_zpow_zpow (g : q9tlMx.carrier) (m n : Int) :
    tateZpow q9tlMx (tateZpow q9tlMx g m) n = tateZpow q9tlMx g (m * n) := by
  cases n with
  | ofNat j =>
    show tateNpow q9tlMx (tateZpow q9tlMx g m) j = tateZpow q9tlMx g (m * (j : Int))
    exact q9mr_zpow_npow g m j
  | negSucc k =>
    show tateNpow q9tlMx (q9tlMx.inv (tateZpow q9tlMx g m)) (k + 1)
        = tateZpow q9tlMx g (m * (Int.negSucc k))
    have hinv : q9tlMx.inv (tateZpow q9tlMx g m) = tateZpow q9tlMx g (-m) :=
      (tateZpow_neg q9tlMx g m).symm
    rw [hinv, q9mr_zpow_npow g (-m) (k + 1)]
    have hexp : (-m) * ((k + 1 : Nat) : Int) = m * (Int.negSucc k) := by
      have hns : (Int.negSucc k) = -((k + 1 : Nat) : Int) := by omega
      rw [hns, Int.mul_neg, Int.neg_mul]
    rw [hexp]

/-! ## q9mr-1: proj 相等 ⟹ q^ℤ-shift（E_{3⁹} 上の関係式・∃ は Prop 内破壊のみ） -/

/-- **q9mr-1（★）: proj x=proj y ⟹ ∃k, y=x·qᵏ**（q9tl の商核 quotientProjN_ker 消費・q=3⁹）。
    ∃k は Prop ゴール内で破壊するのみ・witness 関数化しない（choice 回避）。 -/
theorem q9mr_proj_eq_shift (x y : q9tlMx.carrier)
    (h : q9tlProj.map x = q9tlProj.map y) :
    ∃ k : Int, y = q9tlMx.mul x (tateZpow q9tlMx q9tlQ k) := by
  have hker : q9tlProj.map (q9tlMx.mul (q9tlMx.inv x) y) = q9tlCurve.one := by
    rw [q9tlProj.map_mul, q9tlProj.map_inv, h, q9tlCurve.inv_mul]
  have hmem := (quotientProjN_ker q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup)
      (q9tlMx.mul (q9tlMx.inv x) y)).mp hker
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  rw [hk, ← q9tlMx.mul_assoc, q9tlMx.mul_inv, q9tlMx.one_mul]

/-! ## q9mr-2: ★ 鍵補題 E[9] 決定性（左引数）—— 9 乗 membership の実消費 -/

/-- **q9mr-h3: 指数消去（純 Int）** — 付値方程式 6a+v=0（×2）と付値シフト v₂=v₁+54k から
    a₂=a₁−9k。q3m3r_aexp（2a+v=0・6k・3k）の level-9 定数替え（choice-free・omega）。 -/
theorem q9mr_aexp (a1 a2 v1 v2 k : Int)
    (h1 : 6 * a1 + v1 = 0) (h2 : 6 * a2 + v2 = 0) (hv : v2 = v1 + k * 54) :
    a2 = a1 + (-(9 * k)) := by omega

/-- **q9mr-2a: 9 乗 membership** g∈テータ群 ⟹ w⁹ = q^{−a}（μ₉ の 9 乗・q9mtMem の整理）。
    q3m3r_cube_of_mem の 9 乗版だが q9mtMem が直接 tateZpow w 9 を持つため展開不要。 -/
theorem q9mr_ninth_of_mem (g : q9mtCar) (hg : q9mtMem g) :
    tateZpow q9tlMx g.2 9 = tateZpow q9tlMx q9tlQ (-(g.1.2)) := by
  have hm : q9tlMx.mul (tateZpow q9tlMx q9tlQ g.1.2) (tateZpow q9tlMx g.2 9) = q9tlMx.one := hg
  rw [Grp.inv_eq_of_mul_eq_one q9tlMx hm, tateZpow_neg]

/-- **q9mr-2（★）: E[9] 決定性・左** — g₁,g₂,g'∈q9mtGrp かつ proj(g₁.2)=proj(g₂.2)
    （同 E_{3⁹}[9] 像）ならば e₉(g₁,g')=e₉(g₂,g')。差分因子 w'^{−9k}·(qᵏ)^{−a'} が
    **g' の 9 乗 membership w'⁹=q^{−a'}（μ₉ の 9 乗・w⁹）を消費**して 1 に閉じる。
    q3m3r_weil_e3_left の立方 w³ を 9 乗 w⁹・シフト 6k を 54k に置換した level-9 版。 -/
theorem q9mr_weil_e9_left (g1 g2 g' : q9mtCar)
    (h1 : q9mtMem g1) (h2 : q9mtMem g2) (hg' : q9mtMem g')
    (hproj : q9tlProj.map g1.2 = q9tlProj.map g2.2) :
    q9mtWeil g1 g' = q9mtWeil g2 g' := by
  obtain ⟨k, hk⟩ := q9mr_proj_eq_shift g1.2 g2.2 hproj
  have ha1 : 6 * g1.1.2 + g1.2.1 = 0 := ((q9mt_mem_iff g1).mp h1).1
  have ha2 : 6 * g2.1.2 + g2.2.1 = 0 := ((q9mt_mem_iff g2).mp h2).1
  -- 9 乗 membership（g' の w'⁹=q^{−a'}）
  have hninth : tateZpow q9tlMx g'.2 9 = tateZpow q9tlMx q9tlQ (-(g'.1.2)) :=
    q9mr_ninth_of_mem g' hg'
  -- 付値: g2.2.1 = g1.2.1 + k·54（v_π(q)=54）
  have hval : g2.2.1 = g1.2.1 + k * 54 := by
    rw [hk]
    show g1.2.1 + (tateZpow q9tlMx q9tlQ k).1 = g1.2.1 + k * 54
    rw [q9tl_pow_fst k]
  -- 指数: a₂ = a₁ + (−9k)（付値方程式 6a+v=0 の消費）
  have haexp : g2.1.2 = g1.1.2 + (-(9 * k)) :=
    q9mr_aexp g1.1.2 g2.1.2 g1.2.1 g2.2.1 k ha1 ha2 hval
  -- 補正因子 B·D = 1（9 乗 membership の実消費点）
  have hBD : q9tlMx.mul (tateZpow q9tlMx g'.2 (-(9 * k)))
      (tateZpow q9tlMx (tateZpow q9tlMx q9tlQ k) (-(g'.1.2))) = q9tlMx.one := by
    have hB : tateZpow q9tlMx g'.2 (-(9 * k))
        = tateZpow q9tlMx q9tlQ ((-(g'.1.2)) * (-k)) := by
      have hneg : (-(9 * k) : Int) = 9 * (-k) := by omega
      rw [hneg, ← q9mr_zpow_zpow g'.2 9 (-k), hninth, q9mr_zpow_zpow]
    have hD : tateZpow q9tlMx (tateZpow q9tlMx q9tlQ k) (-(g'.1.2))
        = tateZpow q9tlMx q9tlQ (k * (-(g'.1.2))) := q9mr_zpow_zpow q9tlQ k (-(g'.1.2))
    rw [hB, hD, ← tateZpow_add]
    have hexp0 : (-(g'.1.2)) * (-k) + k * (-(g'.1.2)) = 0 := by
      rw [Int.neg_mul_neg, Int.mul_neg, Int.mul_comm k (g'.1.2)]; omega
    rw [hexp0]
    exact tateZpow_zero q9tlMx q9tlQ
  -- 本計算
  show q9tlMx.mul (tateZpow q9tlMx g'.2 g1.1.2) (tateZpow q9tlMx g1.2 (-(g'.1.2)))
     = q9tlMx.mul (tateZpow q9tlMx g'.2 g2.1.2) (tateZpow q9tlMx g2.2 (-(g'.1.2)))
  rw [haexp, hk, tateZpow_add, q9mt_zpow_mul, q9tlMx.mul_assoc,
      q9mt_lc (tateZpow q9tlMx g'.2 (-(9 * k)))
        (tateZpow q9tlMx g1.2 (-(g'.1.2)))
        (tateZpow q9tlMx (tateZpow q9tlMx q9tlQ k) (-(g'.1.2))),
      hBD, q9tlMx.mul_one]

/-! ## q9mr-3: ★ 鍵補題 E[9] 決定性（右引数） -/

/-- **q9mr-3（★）: E[9] 決定性・右** — g,g'₁,g'₂∈q9mtGrp かつ proj(g'₁.2)=proj(g'₂.2)
    ならば e₉(g,g'₁)=e₉(g,g'₂)。ここは **g の 9 乗 membership w⁹=q^{−a} を消費**する。 -/
theorem q9mr_weil_e9_right (g g'1 g'2 : q9mtCar)
    (hg : q9mtMem g) (h1 : q9mtMem g'1) (h2 : q9mtMem g'2)
    (hproj : q9tlProj.map g'1.2 = q9tlProj.map g'2.2) :
    q9mtWeil g g'1 = q9mtWeil g g'2 := by
  obtain ⟨k, hk⟩ := q9mr_proj_eq_shift g'1.2 g'2.2 hproj
  have ha1 : 6 * g'1.1.2 + g'1.2.1 = 0 := ((q9mt_mem_iff g'1).mp h1).1
  have ha2 : 6 * g'2.1.2 + g'2.2.1 = 0 := ((q9mt_mem_iff g'2).mp h2).1
  have hninth_g : tateZpow q9tlMx g.2 9 = tateZpow q9tlMx q9tlQ (-(g.1.2)) :=
    q9mr_ninth_of_mem g hg
  have hval : g'2.2.1 = g'1.2.1 + k * 54 := by
    rw [hk]
    show g'1.2.1 + (tateZpow q9tlMx q9tlQ k).1 = g'1.2.1 + k * 54
    rw [q9tl_pow_fst k]
  have haexp : g'2.1.2 = g'1.1.2 + (-(9 * k)) :=
    q9mr_aexp g'1.1.2 g'2.1.2 g'1.2.1 g'2.2.1 k ha1 ha2 hval
  have hng : -(g'1.1.2 + (-(9 * k))) = -(g'1.1.2) + 9 * k := by omega
  -- 補正因子 E·F = 1（g の 9 乗 membership を消費）
  have hEF : q9tlMx.mul (tateZpow q9tlMx (tateZpow q9tlMx q9tlQ k) g.1.2)
      (tateZpow q9tlMx g.2 (9 * k)) = q9tlMx.one := by
    have hE : tateZpow q9tlMx (tateZpow q9tlMx q9tlQ k) g.1.2
        = tateZpow q9tlMx q9tlQ (k * g.1.2) := q9mr_zpow_zpow q9tlQ k g.1.2
    have hF : tateZpow q9tlMx g.2 (9 * k)
        = tateZpow q9tlMx q9tlQ ((-(g.1.2)) * k) := by
      rw [← q9mr_zpow_zpow g.2 9 k, hninth_g, q9mr_zpow_zpow]
    rw [hE, hF, ← tateZpow_add]
    have hexp0 : k * g.1.2 + (-(g.1.2)) * k = 0 := by
      rw [Int.neg_mul, Int.mul_comm k (g.1.2)]; omega
    rw [hexp0]
    exact tateZpow_zero q9tlMx q9tlQ
  show q9tlMx.mul (tateZpow q9tlMx g'1.2 g.1.2) (tateZpow q9tlMx g.2 (-(g'1.1.2)))
     = q9tlMx.mul (tateZpow q9tlMx g'2.2 g.1.2) (tateZpow q9tlMx g.2 (-(g'2.1.2)))
  rw [hk, haexp, q9mt_zpow_mul, hng, tateZpow_add, q9tlMx.mul_assoc,
      q9mt_lc (tateZpow q9tlMx (tateZpow q9tlMx q9tlQ k) g.1.2)
        (tateZpow q9tlMx g.2 (-(g'1.1.2)))
        (tateZpow q9tlMx g.2 (9 * k)),
      hEF, q9tlMx.mul_one]

/-! ## q9mr-4: 所属限定 hom の単位・逆元保存（消去律） -/

/-- **q9mr-4a: hom は単位を保つ** φ(1)=1（消去律）。 -/
theorem q9mr_hom_one (φ : q9mtCar → q9mtCar)
    (hHom : ∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g')) :
    φ q9mtOne = q9mtOne := by
  have h := hHom q9mtOne q9mtOne q9mt_mem_one q9mt_mem_one
  rw [q9mtOne_mul] at h
  have hone : q9mtM.mul (φ q9mtOne) q9mtOne = φ q9mtOne := q9mtM.mul_one (φ q9mtOne)
  have h2 : q9mtM.mul (φ q9mtOne) q9mtOne = q9mtM.mul (φ q9mtOne) (φ q9mtOne) := by
    rw [hone]; exact h
  exact (q9mtM.mul_left_cancel h2).symm

/-- **q9mr-4b: hom は逆元を保つ** φ(g⁻¹)=φ(g)⁻¹（所属閉性消費）。 -/
theorem q9mr_hom_inv (φ : q9mtCar → q9mtCar)
    (hHom : ∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g'))
    (g : q9mtCar) (hg : q9mtMem g) :
    φ (q9mtInv g) = q9mtInv (φ g) := by
  have h := hHom (q9mtInv g) g (q9mt_mem_inv g hg) hg
  rw [q9mtInv_mul] at h
  rw [q9mr_hom_one φ hHom] at h
  have hb : φ g = q9mtM.inv (φ (q9mtInv g)) := Grp.inv_eq_of_mul_eq_one q9mtM h.symm
  show φ (q9mtInv g) = q9mtM.inv (φ g)
  rw [hb, Grp.inv_inv]

/-! ## q9mr-5: ★★ 主定理 level-9 mono-theta 剛性（endo・全交換子保存） -/

/-- **q9mr-5（★★）: level-9 mono-theta 剛性** — φ が (i) 所属限定準同型 hHom・
    (ii) 所属保存 hMem・(iii) E_{3⁹}[9] 上恒等 hE9 を満たす**自己準同型**なら、任意の所属元
    g,g' に対して φ(comm g g') = comm g g'（全交換子保存）。単射仮定なし（endo）。
    q3m3r_rigidity の level-9 版（語彙置換のみ・機構は同一）。 -/
theorem q9mr_rigidity (φ : q9mtCar → q9mtCar)
    (hHom : ∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g'))
    (hMem : ∀ g, q9mtMem g → q9mtMem (φ g))
    (hE9 : ∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2)
    (g g' : q9mtCar) (hg : q9mtMem g) (hg' : q9mtMem g') :
    φ (q9mtComm g g') = q9mtComm g g' := by
  have hφg : q9mtMem (φ g) := hMem g hg
  have hφg' : q9mtMem (φ g') := hMem g' hg'
  have hmm : q9mtMem (q9mtMul g g') := q9mt_mem_mul g g' hg hg'
  have hig : q9mtMem (q9mtInv g) := q9mt_mem_inv g hg
  have hig' : q9mtMem (q9mtInv g') := q9mt_mem_inv g' hg'
  have hmmig : q9mtMem (q9mtMul (q9mtMul g g') (q9mtInv g)) :=
    q9mt_mem_mul _ _ hmm hig
  -- Step 1: φ が交換子語を貫通 → comm(φg,φg')
  have hcomm : φ (q9mtComm g g') = q9mtComm (φ g) (φ g') := by
    show φ (q9mtMul (q9mtMul (q9mtMul g g') (q9mtInv g)) (q9mtInv g'))
       = q9mtMul (q9mtMul (q9mtMul (φ g) (φ g')) (q9mtInv (φ g))) (q9mtInv (φ g'))
    rw [hHom _ _ hmmig hig', hHom _ _ hmm hig, hHom _ _ hg hg',
        q9mr_hom_inv φ hHom g hg, q9mr_hom_inv φ hHom g' hg']
  rw [hcomm, q9mt_comm_eq_weil (φ g) (φ g'), q9mt_comm_eq_weil g g']
  -- Step 2: Weil 値が E[9] 決定性で不変
  have hw : q9mtWeil (φ g) (φ g') = q9mtWeil g g' := by
    have hL := q9mr_weil_e9_left (φ g) g (φ g') hφg hg hφg' (hE9 g hg)
    have hR := q9mr_weil_e9_right g (φ g') g' hg hφg' hg' (hE9 g' hg')
    rw [hL, hR]
  rw [hw]

/-! ## q9mr-6: ★★★ 内部 cyclotome 生成元 q9mr_zeta9（原始 9 乗根 ζ₉⁻¹）の恒等固定 -/

/-- **q9mr-6a: 内部 cyclotome 生成元** q9mr_zeta9 = comm(g₃,g_ζ) の値
    = ((0, ζ₉⁻¹), 0, 1) ∈ q9mtGrp（**原始 9 乗根** μ₉ 値・q9mt_weil_g3_gz の担体）。 -/
def q9mr_zeta9 : q9mtCar :=
  ((((0 : Int), q3kU.inv q9tlZeta9U), (0 : Int)), q9tlMx.one)

/-- **q9mr-6b: q9mr_zeta9 = comm(g₃,g_ζ)**（q9mt_weil_g3_gz 消費・非退化 μ₉ 値 ζ₉⁻¹ の交換子）。 -/
theorem q9mr_zeta_eq_comm : q9mtComm q9mtG3 q9mtGZeta = q9mr_zeta9 := by
  show q9mtComm q9mtG3 q9mtGZeta
      = ((((0 : Int), q3kU.inv q9tlZeta9U), (0 : Int)), q9tlMx.one)
  rw [q9mt_comm_eq_weil, q9mt_weil_g3_gz]
  rfl

/-- **q9mr-6c: q9mr_zeta9 ∈ q9mtGrp**（交換子ゆえ所属閉性から）。 -/
theorem q9mr_zeta_mem : q9mtMem q9mr_zeta9 := by
  rw [← q9mr_zeta_eq_comm]
  show q9mtMem (q9mtMul (q9mtMul (q9mtMul q9mtG3 q9mtGZeta) (q9mtInv q9mtG3)) (q9mtInv q9mtGZeta))
  exact q9mt_mem_mul _ _
    (q9mt_mem_mul _ _
      (q9mt_mem_mul _ _ q9mt_g3_mem q9mt_gz_mem)
      (q9mt_mem_inv _ q9mt_g3_mem))
    (q9mt_mem_inv _ q9mt_gz_mem)

/-- **q9mr-6d（★★★）: 内部 cyclotome の恒等固定** φ(q9mr_zeta9)=q9mr_zeta9 —— テータ両立
    自己準同型は内部 μ₉ cyclotome（原始 9 乗根 ζ₉⁻¹）を捻れない（level-9 mono-theta 剛性の
    実現形）。q3m3r_cyclotome_fixed の固定対象 ζ₃⁻¹ を原始 9 乗根 ζ₉⁻¹ に置換した版。 -/
theorem q9mr_cyclotome_fixed (φ : q9mtCar → q9mtCar)
    (hHom : ∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g'))
    (hMem : ∀ g, q9mtMem g → q9mtMem (φ g))
    (hE9 : ∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2) :
    φ q9mr_zeta9 = q9mr_zeta9 := by
  have hc := q9mr_rigidity φ hHom hMem hE9 q9mtG3 q9mtGZeta q9mt_g3_mem q9mt_gz_mem
  rw [q9mr_zeta_eq_comm] at hc
  exact hc

/-! ## q9mr-7: ★ 質的新規(1) — 固定対象が原始 9 乗根（{4,7} 捻り σ が ζ₉ を動かす） -/

/-- **q9mr-7a: σ は μ₃ 対角（定数部）を各点固定** σ(ζ₃ⁱ,0,0)=(ζ₃ⁱ,0,0)。
    q3kSigma が定数成分に恒等・Y/Y² 成分は 0 のまま（ζ₃·0=0・ζ₃²·0=0）。 -/
theorem q9mr_sigma_fixes_mu3 (n : q3rqCar) : q3kSigma (q3kEmbed n) = q3kEmbed n := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta q3rqZero = q3rqZero
    exact q3rqRing.mul_zero q3rqZeta
  · show q3rqMul q3rqZetaSq q3rqZero = q3rqZero
    exact q3rqRing.mul_zero q3rqZetaSq

/-- **q9mr-7b: σ(ζ₉)=ζ₉⁴** σ(Y)=ζ₃Y=Y⁴（q9yp_y4 消費・第 2 成分 ζ₃·1=ζ₃）。 -/
theorem q9mr_sigma_zeta9 : q3kSigma q3kZeta9 = q9ypY4 := by
  rw [q9yp_y4]
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta q3rqOne = q3rqZeta
    exact q3rqRing.mul_one q3rqZeta
  · show q3rqMul q3rqZetaSq q3rqZero = q3rqZero
    exact q3rqRing.mul_zero q3rqZetaSq

/-- **q9mr-7c: σ(ζ₉)≠ζ₉** ζ₉⁴≠ζ₉（第 2 成分 ζ₃≠1・q3rq_zeta_ne_one）。
    {4,7} 捻りは μ₉ を実際に動かす（level-3 では μ₃ 上恒等ゆえ不可視だった層）。 -/
theorem q9mr_sigma_zeta9_ne : q3kSigma q3kZeta9 ≠ q3kZeta9 := by
  rw [q9mr_sigma_zeta9, q9yp_y4]
  intro h
  have h1 : q3rqZeta = q3rqOne := congrArg (fun z : q3kCar => z.2.1) h
  exact q3rq_zeta_ne_one h1

/-- **q9mr-7（★）: 固定対象は原始 9 乗根（level-3 では固定できなかった {4,7} 層を排除）** —
    テータ剛性が固定する内部 cyclotome q9mr_zeta9 (=ζ₉⁻¹) は (i) φ で恒等固定・(ii) 非自明
    （≠1）・(iii) その原始 9 乗根性を実現する {4,7} 捻り σ が ζ₉ を実際に動かす（σ(ζ₉)=ζ₉⁴≠ζ₉）。
    q3m3r の ζ₃⁻¹ 固定は {4,7} を排除できなかった（μ₃ 上恒等）が、ζ₉⁻¹ の固定は初めて排除する。 -/
theorem q9mr_zeta9_fixed (φ : q9mtCar → q9mtCar)
    (hHom : ∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g'))
    (hMem : ∀ g, q9mtMem g → q9mtMem (φ g))
    (hE9 : ∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2) :
    φ q9mr_zeta9 = q9mr_zeta9
    ∧ q9mr_zeta9 ≠ q9mtOne
    ∧ q3kSigma q3kZeta9 = q9ypY4
    ∧ q3kSigma q3kZeta9 ≠ q3kZeta9 := by
  refine ⟨q9mr_cyclotome_fixed φ hHom hMem hE9, ?_, q9mr_sigma_zeta9, q9mr_sigma_zeta9_ne⟩
  rw [← q9mr_zeta_eq_comm]
  exact q9mt_nonabelian

/-! ## q9mr-8: ★★ payoff — 新層 ker(Aut(μ₉)→Aut(μ₃)) の実自己同型 σ の排除 -/

/-- **q9mr-8（★★ campaign の core payoff）: σ=q3kSigma は新層 ker(Aut(μ₉)→Aut(μ₃)) の
    非自明元を実現する実自己同型** — σ は (i) 乗法的（q3k_sigma_mul）・(ii) σ(1)=1
    （q3k_sigma_one）・(iii) **μ₃ 対角を各点固定**（Aut(μ₃) 上恒等・level-3 kill 対象では不可視）・
    (iv) **σ(ζ₉)=ζ₉⁴≠ζ₉**（μ₉ 上非恒等）。すなわち σ ∈ ker(Aut(μ₉)→Aut(μ₃))∖{id}
    = {1,4,7}∖{1} ≅ (1+3ℤ₃)/(1+9ℤ₃) の非自明元であり、level-9 剛性の内部 cyclotome
    {id} 固定（q9mr_cyclotome_fixed）はこの σ を排除する。q3m3r_aut_mu3_nontrivial（反転
    ζ₃↦ζ₃²・位数 2・μ₃ 上非恒等）と対照的に、σ は μ₃ 上恒等ゆえ level-3 剛性には見えなかった
    ——これが「pro-3 bulk 1+3ℤ₃ への初の一咬み」の実担体。 -/
theorem q9mr_aut_mu9_new_layer :
    (∀ x y : q3kCar, q3kSigma (q3kMul x y) = q3kMul (q3kSigma x) (q3kSigma y))
    ∧ q3kSigma q3kOne = q3kOne
    ∧ (∀ n : q3rqCar, q3kSigma (q3kEmbed n) = q3kEmbed n)
    ∧ q3kSigma q3kZeta9 = q9ypY4
    ∧ q3kSigma q3kZeta9 ≠ q3kZeta9 :=
  ⟨q3k_sigma_mul, q3k_sigma_one, q9mr_sigma_fixes_mu3, q9mr_sigma_zeta9, q9mr_sigma_zeta9_ne⟩

/-! ## q9mr-9: ★ M 上反例（membership が load-bearing・鍵補題は q9mt_comm_eq_weil の系でない） -/

/-- 反例 witness 1: g₁=((1,0),1) ∈ q9mtGrp（=q9mtOne・a=0）。 -/
def q9mrWit1 : q9mtCar := ((q9tlMx.one, (0 : Int)), q9tlMx.one)

/-- 反例 witness 2: g₂=((1,1),1) ∉ q9mtGrp（a=1・付値方程式 6·1+0≠0）。同 E_{3⁹}[9] 像（w=1）。 -/
def q9mrWit2 : q9mtCar := ((q9tlMx.one, (1 : Int)), q9tlMx.one)

/-- **q9mr-9（★）: M 上反例** — g₁∈q9mtGrp・g₂∉q9mtGrp が同 E_{3⁹}[9] 像（proj w 一致）を
    持つのに e₉(g₁,g_ζ)=1 ≠ ζ₉=e₉(g₂,g_ζ)。すなわち q9mr_weil_e9_left の membership 仮定は
    load-bearing で、鍵補題は q9mt_comm_eq_weil（値の式）の系ではない。q3m3r_weil_fails_on_M
    の 9 乗版（監査前例が要求・安価なクローンで収録）。 -/
theorem q9mr_weil_fails_on_M :
    q9mtMem q9mrWit1 ∧ ¬ q9mtMem q9mrWit2
    ∧ q9tlProj.map q9mrWit1.2 = q9tlProj.map q9mrWit2.2
    ∧ q9mtWeil q9mrWit1 q9mtGZeta ≠ q9mtWeil q9mrWit2 q9mtGZeta := by
  refine ⟨q9mt_mem_one, ?_, rfl, ?_⟩
  · intro hmem
    have hval : (6 : Int) * 1 + (0 : Int) = 0 := ((q9mt_mem_iff q9mrWit2).mp hmem).1
    omega
  · have hw1 : q9mtWeil q9mrWit1 q9mtGZeta = q9tlMx.one := by
      show q9tlMx.mul (tateZpow q9tlMx q9tlZeta9Elt (0 : Int))
          (tateZpow q9tlMx q9tlMx.one (-(0 : Int))) = q9tlMx.one
      rw [tateZpow_zero, q9tlMx.one_mul]
      have h00 : (-(0 : Int)) = 0 := by omega
      rw [h00, tateZpow_zero]
    have hw2 : q9mtWeil q9mrWit2 q9mtGZeta = (((0 : Int), q9tlZeta9U)) := by
      show q9tlMx.mul (tateZpow q9tlMx q9tlZeta9Elt (1 : Int))
          (tateZpow q9tlMx q9tlMx.one (-(0 : Int))) = (((0 : Int), q9tlZeta9U))
      rw [tateZpow_one]
      have h00 : (-(0 : Int)) = 0 := by omega
      rw [h00, tateZpow_zero, q9tlMx.mul_one]
      rfl
    rw [hw1, hw2]
    intro h
    have hu : q3kU.one = q9tlZeta9U := congrArg Prod.snd h
    have hval : q3kOne = q3kZeta9 := congrArg Subtype.val hu
    exact q3k_zeta9_ne_one hval.symm

/-! ## q9mr-10: capstone -/

/-- **q9mr-10a: level-9 実 mono-theta 剛性データ** — μ₉ 値 Weil の E[9] 決定性・endo 剛性・
    内部 μ₉ cyclotome（原始 9 乗根 ζ₉⁻¹）恒等固定・そして質的に新しい **新層 payoff**（σ=q3kSigma
    が μ₃ 対角固定・μ₉ 非恒等の実自己同型＝ker(Aut(μ₉)→Aut(μ₃)) の非自明元）を束ねる。 -/
structure Q3Mu9RigidityData where
  /-- μ₉ 値 Weil の E[9] 決定性（左）。 -/
  weilE9Left : ∀ g1 g2 g' : q9mtCar, q9mtMem g1 → q9mtMem g2 → q9mtMem g' →
    q9tlProj.map g1.2 = q9tlProj.map g2.2 → q9mtWeil g1 g' = q9mtWeil g2 g'
  /-- μ₉ 値 Weil の E[9] 決定性（右）。 -/
  weilE9Right : ∀ g g'1 g'2 : q9mtCar, q9mtMem g → q9mtMem g'1 → q9mtMem g'2 →
    q9tlProj.map g'1.2 = q9tlProj.map g'2.2 → q9mtWeil g g'1 = q9mtWeil g g'2
  /-- endo 剛性（全交換子保存）。 -/
  rigidity : ∀ φ : q9mtCar → q9mtCar,
    (∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g')) →
    (∀ g, q9mtMem g → q9mtMem (φ g)) →
    (∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2) →
    ∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtComm g g') = q9mtComm g g'
  /-- 内部 μ₉ cyclotome（原始 9 乗根）の恒等固定（endo クラス全体）。 -/
  cyclotomeFixed : ∀ φ : q9mtCar → q9mtCar,
    (∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g')) →
    (∀ g, q9mtMem g → q9mtMem (φ g)) →
    (∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2) →
    φ q9mr_zeta9 = q9mr_zeta9
  /-- 内部 cyclotome 生成元 = comm(g₃,g_ζ)。 -/
  zetaEqComm : q9mtComm q9mtG3 q9mtGZeta = q9mr_zeta9
  /-- 生成元はテータ群の元。 -/
  zetaMem : q9mtMem q9mr_zeta9
  /-- 固定対象は非自明（原始 9 乗根 ≠1）。 -/
  zetaNontrivial : q9mr_zeta9 ≠ q9mtOne
  /-- ★ 新層 payoff-i: σ は乗法的。 -/
  sigmaMul : ∀ x y : q3kCar, q3kSigma (q3kMul x y) = q3kMul (q3kSigma x) (q3kSigma y)
  /-- ★ 新層 payoff-iii: σ は μ₃ 対角を各点固定（Aut(μ₃) 上恒等）。 -/
  sigmaFixesMu3 : ∀ n : q3rqCar, q3kSigma (q3kEmbed n) = q3kEmbed n
  /-- ★ 新層 payoff-iv: σ(ζ₉)=ζ₉⁴≠ζ₉（μ₉ 上非恒等）——ker(Aut(μ₉)→Aut(μ₃)) の非自明元。 -/
  sigmaMovesZeta9 : q3kSigma q3kZeta9 ≠ q3kZeta9

/-- **q9mr-10b: 見出し実例** — M = O_M 上・q=3⁹ の level-9 実 mono-theta 剛性
    （μ₉ 値・原始 9 乗根 ζ₉⁻¹ 固定・新層 (1+3ℤ₃)/(1+9ℤ₃) の kill 機構）。 -/
def q9mr_data : Q3Mu9RigidityData where
  weilE9Left := q9mr_weil_e9_left
  weilE9Right := q9mr_weil_e9_right
  rigidity := q9mr_rigidity
  cyclotomeFixed := q9mr_cyclotome_fixed
  zetaEqComm := q9mr_zeta_eq_comm
  zetaMem := q9mr_zeta_mem
  zetaNontrivial := by rw [← q9mr_zeta_eq_comm]; exact q9mt_nonabelian
  sigmaMul := q3k_sigma_mul
  sigmaFixesMu3 := q9mr_sigma_fixes_mu3
  sigmaMovesZeta9 := q9mr_sigma_zeta9_ne

/-- **q9mr-10c: level-9 実 mono-theta 剛性の存在**
    （実 M=O_M・q=3⁹・μ₉・原始 9 乗根 ζ₉⁻¹ 固定・新層 kill 機構）。 -/
theorem q9mr_exists : Nonempty Q3Mu9RigidityData := ⟨q9mr_data⟩

end IUT
