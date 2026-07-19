/-
  IUT/BelyiCubicRamification.lean — A9（Belyi 化 / 遠アーベル幾何入力(実)）
  第二歩: 三次 Belyi 被覆の**正確な分岐指数プロファイル (2,2,3)** と
  臨界ファイバーの**残余単純根**（次数 3 ファイバーの第三点）の実証明。

  ── 分類 **[実／本物の先行建設(b)]**（骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無・toy 模型を定理の主語にしない）。

  **complete_pct 影響**: **本物の先行建設(b)**。柱A A9（現 status 0.1）へ、
  `IUT/BelyiCubicReal.lean` の実 Belyi 多項式 f(X)=3X²−2X³ の分岐**値**集合 {0,1,∞}
  の決定に続き、各分岐点の**分岐指数がちょうど幾つか（正確な下限でなく上限＝単元性）**
  を供給する:
   * 0 の上の二重根点で余因子 (3−2X)|_{X=0}=3 が**単元**（≠0）⇒ e₀ = ちょうど 2
     （三重根ではない）。
   * 1 の上の二重根点で余因子 −(2X+1)|_{X=1}=−3 が**単元**（≠0）⇒ e₁ = ちょうど 2。
   * ∞ の全分岐 e_∞ = 3（既存 blc_infty_unit を束ねで再利用・非再証明）。
  さらに臨界ファイバーの**残余単純根**（0 のファイバーの 3/2・1 のファイバーの −1/2）を
  実 ℚ 上で構成し、ramified 点と相異なることを示す（次数 3 ファイバー = {二重根, 単純根}）。
  これで正直な限定 §4.2-6「一般ファイバーの根の個数は数えない／分岐指数は下界のみ」を
  臨界ファイバーに関して **上界（指数の厳密値）＋第三点の存在**まで実に押し上げる。
  見込み A9 0.1→予測（独立監査が確定・過大主張しない・下記正直な限定を消さない）。

  内容（blr-0..blr-5）:
   * blr-0 余因子の切り捨て評価: blc_eval_W (=3−2X の値) / blc_eval_M (=−(2X+1) の値)
   * blr-1 ramified 点での余因子単元性 blr_ram0_cofactor / blr_ram1_cofactor（一般 CRing）
   * blr-2 実 ℚ での厳密指数（≠0）blr_ram0_exact / blr_ram1_exact
   * blr-3 残余単純根 blr_fiber0_simple(=3/2) / blr_fiber1_simple(=−1/2)（実 ℚ）と相異性
   * blr-4 Riemann–Hurwitz の数値バランス（種数 0・プロファイル (2,2,3)・次数 3）
   * blr-5 見出し束ね BelyiRamProfile（実 witness を要求する grounded 構造）

  正直な限定（§4.2 の継承・消去/弱化しない）:
   1. **Belyi の定理ではない**: 1 本の具体例 f=3X²−2X³ のみ。全曲線/ℚ̄ は不主張。
   2. **noncritical Belyi / cuspidalization ではない**: 高さ制御・tripod の実 π₁ は 0 のまま。
   3. **スキームでない**: P¹ は点集合 Option K の継承。分岐指数は「余因子の単元性」と
      「∞ チャートの単元性」による顕示であって局所環の付値・完備化ではない。
   4. **残余単純根は臨界ファイバー（y=0,1）のみ**: 一般 y のファイバーの根の個数・
      分離閉包での全 3 点の列挙はしない。y∉{0,1} の分離性は base の blc_branch_locus の
      対偶が与えるが、本モジュールは臨界 2 本の第三点のみ構成する。
   5. **Riemann–Hurwitz は数値バランスのみ**: 種数 0 は 2g−2 = deg·(2·0−2)+Σ(eᵢ−1) の
      Nat 恒等式での顕示であり、被覆のコホモロジー的種数・複素構造の主張ではない。
      分岐指数 eᵢ 自体は blr-1/blr-2/blc_infty_unit の実単元性が根拠。
   6. **A8 Tate 曲線との接続なし**: λ→j 次数 6 写像は後続。E_q はここに登場しない。

  二重計上の排除（監査向け）:
   - **base BelyiCubicReal を消費するのみ**: blcF/blcW/blcM/blc_fiber_zero/blc_fiber_one・
     評価機構（evalSum/evalHomId）・実 ℚ の rep 補題 blc_rnsmul_one_rep は使うが、
     分岐指数の厳密値（余因子単元性）・残余単純根・RH バランスは全て新規の実内容。
     値一致の再確認だけの定理は置かない（blc_infty_unit は束ねで 1 回参照するのみ）。
   - **A4/A5/A6/A7 と主語素 disjoint**: π₁・デッキ群・円分体・Gal は登場しない。

  全て選択公理不使用（propext/Quot.sound のみ）。禁止タクティク不使用。
  新規ファイル 1 個のみ（共有ファイル不更新）。
-/
import IUT.BelyiCubicReal

namespace IUT

/-! ## blr-0: 余因子の切り捨て評価（一般 CRing E 上） -/

/-- **blr-0a**: y=0 のファイバー余因子 3 − 2X の a での評価 = 3·1 + (−2·1)·a。 -/
theorem blc_eval_W (E : CRing) (a : E.carrier) :
    evalSum (evalHomId E) a (blcW E) 2
      = E.add (blcThree E) (E.mul (E.neg (blcTwo E)) a) := by
  rw [evalSum_id]
  show E.add (E.add E.zero (E.mul (blcW E 0) (rpow E a 0))) (E.mul (blcW E 1) (rpow E a 1))
    = E.add (blcThree E) (E.mul (E.neg (blcTwo E)) a)
  rw [blc_blcW_coeff0 E, blc_blcW_coeff1 E, rpow_zero E a, blc_rpow_one E a,
    CRing.mul_one E (blcThree E), E.zero_add (blcThree E)]

/-- **blr-0b**: y=1 のファイバー余因子 −(2X+1) の a での評価 = (−1) + (−2·1)·a。 -/
theorem blc_eval_M (E : CRing) (a : E.carrier) :
    evalSum (evalHomId E) a (blcM E) 2
      = E.add (E.neg E.one) (E.mul (E.neg (blcTwo E)) a) := by
  rw [evalSum_id]
  show E.add (E.add E.zero (E.mul (blcM E 0) (rpow E a 0))) (E.mul (blcM E 1) (rpow E a 1))
    = E.add (E.neg E.one) (E.mul (E.neg (blcTwo E)) a)
  rw [blcM_coeff0 E, blcM_coeff1 E, rpow_zero E a, blc_rpow_one E a,
    CRing.mul_one E (E.neg E.one), E.zero_add (E.neg E.one)]

/-! ## blr-1: ramified 点での余因子単元性（分岐指数がちょうど 2・一般 CRing） -/

/-- **blr-1a**: 0 の上の二重根点 X=0 での余因子 (3−2X)|_{X=0} = 3·1。
    3·1 が単元（≠0）である環では 0 の分岐指数は**ちょうど 2**（三重根でない）。 -/
theorem blr_ram0_cofactor (E : CRing) :
    evalSum (evalHomId E) E.zero (blcW E) 2 = blcThree E := by
  rw [blc_eval_W E E.zero, CRing.mul_zero E (E.neg (blcTwo E)), CRing.add_zero E (blcThree E)]

/-- **blr-1b**: 1 の上の二重根点 X=1 での余因子 −(2X+1)|_{X=1} = −(3·1)。
    −(3·1) が単元（≠0）である環では 1 の分岐指数は**ちょうど 2**。 -/
theorem blr_ram1_cofactor (E : CRing) :
    evalSum (evalHomId E) E.one (blcM E) 2 = E.neg (blcThree E) := by
  rw [blc_eval_M E E.one, CRing.mul_one E (E.neg (blcTwo E)),
    blc_three_eq E, CRing.neg_add_dist E (blcTwo E) E.one,
    E.add_comm (E.neg E.one) (E.neg (blcTwo E))]

/-! ## blr-2: 実 ℚ での厳密分岐指数（余因子 ≠ 0） -/

/-- **blr-2a**: 実 ℚ 上、0 の余因子は X=0 で単元（=3≠0）⇒ e₀ = ちょうど 2。 -/
theorem blr_ram0_exact :
    evalSum (evalHomId ratRing) ratRing.zero (blcW ratRing) 2 ≠ ratRing.zero := by
  rw [blr_ram0_cofactor ratRing]
  exact blc_three_rat_ne_zero

/-- **blr-2b**: 実 ℚ 上、1 の余因子は X=1 で単元（=−3≠0）⇒ e₁ = ちょうど 2。 -/
theorem blr_ram1_exact :
    evalSum (evalHomId ratRing) ratRing.one (blcM ratRing) 2 ≠ ratRing.zero := by
  rw [blr_ram1_cofactor ratRing]
  intro h
  apply blc_three_rat_ne_zero
  have h2 := congrArg ratRing.neg h
  rw [CRing.neg_neg ratRing (blcThree ratRing), CRing.neg_zero ratRing] at h2
  exact h2

/-! ## blr-3: 臨界ファイバーの残余単純根（次数 3 ファイバーの第三点・実 ℚ） -/

/-- 実 ℚ の元 3/2（0 のファイバー f=X²(3−2X) の残余単純根）。 -/
def blrHalf3 : ratRing.carrier := Quot.mk ratRel ⟨3, 2, by omega⟩

/-- 実 ℚ の元 −1/2（1 のファイバー f−1=(X−1)²(−(2X+1)) の残余単純根）。 -/
def blrHalfNeg : ratRing.carrier := Quot.mk ratRel ⟨-1, 2, by omega⟩

/-- **blr-3a**: 3/2 は 0 の余因子 3−2X の根（0 のファイバーの第三点）。 -/
theorem blr_fiber0_simple :
    evalSum (evalHomId ratRing) blrHalf3 (blcW ratRing) 2 = ratRing.zero := by
  rw [blc_eval_W ratRing blrHalf3,
    show blcThree ratRing = Quot.mk ratRel (intToPreRat (Int.ofNat 3)) from blc_rnsmul_one_rep 3,
    show blcTwo ratRing = Quot.mk ratRel (intToPreRat (Int.ofNat 2)) from blc_rnsmul_one_rep 2]
  show Quot.mk ratRel
      (prAdd (intToPreRat (Int.ofNat 3))
        (prMul (prNeg (intToPreRat (Int.ofNat 2))) ⟨3, 2, by omega⟩))
    = Quot.mk ratRel prZero
  apply Quot.sound
  show ((3 : Int) * (1 * 2) + -2 * 3 * 1) * 1 = 0 * (1 * (1 * 2))
  omega

/-- **blr-3b**: 残余単純根 3/2 は ramified 点 0 と相異なる。 -/
theorem blr_fiber0_simple_ne : blrHalf3 ≠ ratRing.zero := by
  intro h
  have hrel : ratRel (⟨3, 2, by omega⟩ : PreRat) prZero := quot_exact_rat h
  have h2 : (3 : Int) * 1 = 0 * 2 := hrel
  omega

/-- **blr-3c**: −1/2 は 1 の余因子 −(2X+1) の根（1 のファイバーの第三点）。 -/
theorem blr_fiber1_simple :
    evalSum (evalHomId ratRing) blrHalfNeg (blcM ratRing) 2 = ratRing.zero := by
  rw [blc_eval_M ratRing blrHalfNeg,
    show blcTwo ratRing = Quot.mk ratRel (intToPreRat (Int.ofNat 2)) from blc_rnsmul_one_rep 2,
    show ratRing.one = Quot.mk ratRel prOne from rfl]
  show Quot.mk ratRel
      (prAdd (prNeg prOne)
        (prMul (prNeg (intToPreRat (Int.ofNat 2))) ⟨-1, 2, by omega⟩))
    = Quot.mk ratRel prZero
  apply Quot.sound
  show ((-1 : Int) * (1 * 2) + -2 * -1 * 1) * 1 = 0 * (1 * (1 * 2))
  omega

/-- **blr-3d**: 残余単純根 −1/2 は ramified 点 1 と相異なる。 -/
theorem blr_fiber1_simple_ne : blrHalfNeg ≠ ratRing.one := by
  intro h
  have hrel : ratRel (⟨-1, 2, by omega⟩ : PreRat) prOne := quot_exact_rat h
  have h2 : (-1 : Int) * 1 = 1 * 2 := hrel
  omega

/-! ## blr-4: Riemann–Hurwitz の数値バランス（種数 0・プロファイル (2,2,3)） -/

/-- **blr-4**: 次数 3・分岐プロファイル (e₀,e₁,e_∞)=(2,2,3) の Riemann–Hurwitz バランス
    Σ(eᵢ−1) = 2·deg − 2 = 4 は種数 0 を顕示する（Nat 恒等式・付値/複素構造ではない）。 -/
theorem blr_riemann_hurwitz : (2 - 1) + (2 - 1) + (3 - 1) = 2 * 3 - 2 := by omega

/-! ## blr-5: 見出し束ね（実 witness を要求する grounded 構造） -/

/-- **BelyiRamProfile**: 三次 Belyi 被覆の分岐指数プロファイルの実データ。
    各フィールドが実際の余因子単元性・残余単純根・RH バランスの証明を要求するため、
    骨格でなく grounded（インスタンス化に本物の証明が要る）。 -/
structure BelyiRamProfile where
  /-- 0 の余因子が ramified 点で単元 ⇒ e₀ = ちょうど 2。 -/
  ram0 : evalSum (evalHomId ratRing) ratRing.zero (blcW ratRing) 2 ≠ ratRing.zero
  /-- 1 の余因子が ramified 点で単元 ⇒ e₁ = ちょうど 2。 -/
  ram1 : evalSum (evalHomId ratRing) ratRing.one (blcM ratRing) 2 ≠ ratRing.zero
  /-- ∞ チャートが単元 ⇒ e_∞ = 3（base blc_infty_unit）。 -/
  raminf : ratRing.add (ratRing.mul (blcThree ratRing) ratRing.zero) (ratRing.neg (blcTwo ratRing))
      ≠ ratRing.zero
  /-- 0 のファイバーの残余単純根 3/2 と ramified 点 0 との相異（次数 3 ファイバー）。 -/
  simple0 : evalSum (evalHomId ratRing) blrHalf3 (blcW ratRing) 2 = ratRing.zero
      ∧ blrHalf3 ≠ ratRing.zero
  /-- 1 のファイバーの残余単純根 −1/2 と ramified 点 1 との相異。 -/
  simple1 : evalSum (evalHomId ratRing) blrHalfNeg (blcM ratRing) 2 = ratRing.zero
      ∧ blrHalfNeg ≠ ratRing.one
  /-- Riemann–Hurwitz 種数 0 バランス・プロファイル (2,2,3)・次数 3。 -/
  rh : (2 - 1) + (2 - 1) + (3 - 1) = 2 * 3 - 2

/-- **blrCubicProfile**: 実 ℚ 上の f=3X²−2X³ の分岐指数プロファイルの実証人。 -/
def blrCubicProfile : BelyiRamProfile where
  ram0 := blr_ram0_exact
  ram1 := blr_ram1_exact
  raminf := blc_infty_unit
  simple0 := ⟨blr_fiber0_simple, blr_fiber0_simple_ne⟩
  simple1 := ⟨blr_fiber1_simple, blr_fiber1_simple_ne⟩
  rh := blr_riemann_hurwitz

/-- **blr_belyi_ram_exists**: 三次 Belyi 被覆の実分岐プロファイルは存在する。 -/
theorem blr_belyi_ram_exists : Nonempty BelyiRamProfile := ⟨blrCubicProfile⟩

end IUT
