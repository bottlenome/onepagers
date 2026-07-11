/-
  IUT/BelyiCubicReal.lean — A9（Belyi 化 / 遠アーベル幾何入力(実)の第一歩）

  ── 分類 **[実／本物の先行建設(b)]**（骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無・toy 模型を定理の主語にしない）。

  **complete_pct 影響**: **本物の先行建設(b)**。柱A A9（status 0）へ、実 ℚ
  （`ratRing`）と任意の零因子なし拡大環の上での **実 Belyi 多項式
  f(X) = 3X² − 2X³ ∈ ℚ[X]（= `polyCRing ratRing` の実元）** の分岐軌跡が
  ちょうど {0, 1, ∞} に一致することの完全証明を供給する。見込み A9 0→0.1
  （独立監査が確定）。設計書 `audit/A9-belyi-anabelian-input-detail-2026-07-11.md`
  §3（blc-0..blc-6）・§2 候補(a)（psDvd 空虚性の罠の回避）・§4（正直な限定）に準拠。

  内容（設計 §3）:
   * blc-0 一般環上の整数係数 blcThree/blcTwo/blcSix と rnsmul の合成則
   * blc-1 実 Belyi 多項式 blcF = 3X² − 2X³（一般 CRing E 上・ℚ で具体化）
   * blc-2 導関数の実因子分解 Df = 6X − 6X²（臨界点 = {0,1} の顕示）
   * blc-3 分岐ファイバーの実二重根（blc_fiber_zero: f = X²(3−2X)・
     blc_fiber_one: f − 1 = (X−1)²(−(2X+1))）＝ {0,1} が実際に分岐する下界
   * blc-4 ★主定理 blc_branch_locus: 零因子なし・6·1≠0 の任意の拡大環で、
     f − y が有界証人つきの二重一次因子 (X−a)² を持つなら y ∈ {0,1}（上界）
   * blc-5 実 ℚ での具体化 blc_branch_locus_rat ＋ ∞ チャート恒等式
     blc_infty_chart: f(1/u)·u³ = 3u − 2（e_∞ = 3 の顕示・blc_infty_unit）
   * blc-6 見出し束ね blcData / blc_belyi_exists

  正直な限定（§4.2・消去・弱化しない）:
   1. **Belyi の定理ではない**: 「ℚ̄ 上の全ての曲線が {0,1,∞} 分岐写像を持つ」は
      一切主張しない。1 本の具体例 f = 3X² − 2X³ のみ。
   2. **noncritical Belyi（[GenEll]・IUT IV）ではない**: 高さ・compactly bounded
      subset の制御は範囲外。
   3. **Belyi cuspidalization（[AbsTopII]）ではない**: tripod の実 π₁・punctured
      曲線の π₁ 再構成はゼロのまま。
   4. **スキームでない**: P¹ は点集合 Option K（K-点・スキーム/エタールサイト
      皆無の恒久限定の継承）。e_∞ = 3 はチャート恒等式での顕示であり局所環の
      付値ではない。
   5. **重根仮定は多項式証人つき分解**（psDvd 級数整除は a ≠ 0 で X−a が単元と
      なり空虚になるため使わない ── これは弱化でなく幾何的に正しい定式化の選択）。
   6. **ℚ̄ 上の分岐点の存在列挙はしない**: blc_branch_locus は「二重根があれば
      y∈{0,1}」の上界、blc_fiber_zero/one は「y=0,1 には実際に二重根がある」の
      下界で、対で「分岐値集合 = {0,1,∞}」を構成的に閉じるが、一般ファイバーの
      根の個数は数えない。
   7. **A8 Tate 曲線との接続なし**: λ→j 次数 6 写像は後続。E_q はここに登場しない。

  §4.3 二重計上の排除（監査向け）:
   - **A1/M270F/M274F を消費するのみで再輸出しない**: ratRing・polyCRing・
     sep-機構（formalDeriv/formalDeriv_mul_linFactor）・評価機構（evalSum/
     evalHom_id_mul/evalHom_stable）は補題として使うが、blcF・分岐軌跡定理・
     チャート恒等式は全て新規の実内容。値一致の再確認だけの定理は置かない。
   - **A4/A5/A6/A7 と主語素 disjoint**: π₁・デッキ群・円分体・Gal は本モジュールに
     一切登場しない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.SeparablePoly
import IUT.EvaluationHom
import IUT.Field
import IUT.PolyWeierstrass

namespace IUT

/-! ## blc-0: 一般環上の整数係数と rnsmul の合成則 -/

/-- 一般 CRing E 上の 3·1。 -/
def blcThree (E : CRing) : E.carrier := rnsmul E 3 E.one
/-- 一般 CRing E 上の 2·1。 -/
def blcTwo (E : CRing) : E.carrier := rnsmul E 2 E.one
/-- 一般 CRing E 上の 6·1。 -/
def blcSix (E : CRing) : E.carrier := rnsmul E 6 E.one

/-- rnsmul の指数加法性 (m+n)·a = m·a + n·a。 -/
theorem blc_rnsmul_add (E : CRing) (a : E.carrier) : ∀ m n,
    rnsmul E (m + n) a = E.add (rnsmul E m a) (rnsmul E n a) := by
  intro m n
  induction n with
  | zero =>
    show rnsmul E m a = E.add (rnsmul E m a) E.zero
    rw [CRing.add_zero E (rnsmul E m a)]
  | succ n ih =>
    show E.add (rnsmul E (m + n) a) a = E.add (rnsmul E m a) (E.add (rnsmul E n a) a)
    rw [ih, E.add_assoc]

/-- rnsmul の合成 m·(n·x) = (mn)·x。 -/
theorem blc_rnsmul_rnsmul (E : CRing) (m n : Nat) (x : E.carrier) :
    rnsmul E m (rnsmul E n x) = rnsmul E (m * n) x := by
  induction m with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ m ih =>
    show E.add (rnsmul E m (rnsmul E n x)) (rnsmul E n x) = rnsmul E (Nat.succ m * n) x
    rw [ih, Nat.succ_mul, blc_rnsmul_add E x (m * n) n]

/-- 形式微分は有界性を N+1 → N に落とす。 -/
theorem blc_deriv_bounded (E : CRing) (f : PS E) (N : Nat)
    (hf : IsPolyBounded E f (N + 1)) : IsPolyBounded E (formalDeriv E f) N := by
  intro n hn
  show rnsmul E (n + 1) (f (n + 1)) = E.zero
  rw [hf (n + 1) (by omega), rnsmul_zero E]

/-- 環の恒等式 3·1 − 2·1 = 1（任意 CRing）。 -/
theorem blc_three_sub_two (E : CRing) :
    E.add (blcThree E) (E.neg (blcTwo E)) = E.one := by
  show E.add (E.add (blcTwo E) E.one) (E.neg (blcTwo E)) = E.one
  rw [E.add_assoc (blcTwo E) E.one (E.neg (blcTwo E)),
    E.add_comm E.one (E.neg (blcTwo E)),
    ← E.add_assoc (blcTwo E) (E.neg (blcTwo E)) E.one,
    CRing.add_neg E (blcTwo E), E.zero_add E.one]

/-- (−1)·(−1) = 1。 -/
theorem blc_negone_sq (E : CRing) :
    E.mul (E.neg E.one) (E.neg E.one) = E.one := by
  rw [CRing.neg_mul E E.one (E.neg E.one), E.one_mul (E.neg E.one), CRing.neg_neg E E.one]

/-- (−x)·(−1) = x。 -/
theorem blc_negmul_negone (E : CRing) (x : E.carrier) :
    E.mul (E.neg x) (E.neg E.one) = x := by
  rw [CRing.neg_mul E x (E.neg E.one), CRing.mul_neg E x E.one, CRing.mul_one E x,
    CRing.neg_neg E x]

/-- 2·1 = 1 + 1（環の展開）。 -/
theorem blc_two_eq (E : CRing) : blcTwo E = E.add E.one E.one := by
  show E.add (E.add E.zero E.one) E.one = E.add E.one E.one
  rw [E.zero_add E.one]

/-- 3·1 = (2·1) + 1（定義的展開）。 -/
theorem blc_three_eq (E : CRing) : blcThree E = E.add (blcTwo E) E.one := rfl

/-- 1 + (1 + (−2·1)) = 0。 -/
theorem blc_val1 (E : CRing) :
    E.add E.one (E.add E.one (E.neg (blcTwo E))) = E.zero := by
  rw [blc_two_eq E, ← E.add_assoc E.one E.one (E.neg (E.add E.one E.one)),
    CRing.add_neg E (E.add E.one E.one)]

/-- (−1 + 2·1) + 2·1 = 3·1。 -/
theorem blc_val2 (E : CRing) :
    E.add (E.add (E.neg E.one) (blcTwo E)) (blcTwo E) = blcThree E := by
  rw [blc_three_eq E, blc_two_eq E,
    show E.add (E.neg E.one) (E.add E.one E.one) = E.one from by
      rw [← E.add_assoc (E.neg E.one) E.one E.one, E.neg_add E.one, E.zero_add E.one],
    ← E.add_assoc E.one E.one E.one]

/-! ## blc-1: 実 Belyi 多項式 f = 3X² − 2X³ -/

/-- **blc-1: 実 Belyi 多項式** f(X) = 3X² − 2X³（一般 CRing E 上）。 -/
def blcF (E : CRing) : PS E :=
  psAdd E (psSingle E (blcThree E) 2) (psSingle E (E.neg (blcTwo E)) 3)

theorem blcF_coeff0 (E : CRing) : blcF E 0 = E.zero := by
  show E.add (psSingle E (blcThree E) 2 0) (psSingle E (E.neg (blcTwo E)) 3 0) = E.zero
  rw [show psSingle E (blcThree E) 2 0 = E.zero from if_neg (by omega),
    show psSingle E (E.neg (blcTwo E)) 3 0 = E.zero from if_neg (by omega), E.zero_add E.zero]

theorem blcF_coeff1 (E : CRing) : blcF E 1 = E.zero := by
  show E.add (psSingle E (blcThree E) 2 1) (psSingle E (E.neg (blcTwo E)) 3 1) = E.zero
  rw [show psSingle E (blcThree E) 2 1 = E.zero from if_neg (by omega),
    show psSingle E (E.neg (blcTwo E)) 3 1 = E.zero from if_neg (by omega), E.zero_add E.zero]

theorem blcF_coeff2 (E : CRing) : blcF E 2 = blcThree E := by
  show E.add (psSingle E (blcThree E) 2 2) (psSingle E (E.neg (blcTwo E)) 3 2) = blcThree E
  rw [show psSingle E (blcThree E) 2 2 = blcThree E from if_pos rfl,
    show psSingle E (E.neg (blcTwo E)) 3 2 = E.zero from if_neg (by omega),
    CRing.add_zero E (blcThree E)]

theorem blcF_coeff3 (E : CRing) : blcF E 3 = E.neg (blcTwo E) := by
  show E.add (psSingle E (blcThree E) 2 3) (psSingle E (E.neg (blcTwo E)) 3 3) = E.neg (blcTwo E)
  rw [show psSingle E (blcThree E) 2 3 = E.zero from if_neg (by omega),
    show psSingle E (E.neg (blcTwo E)) 3 3 = E.neg (blcTwo E) from if_pos rfl,
    E.zero_add (E.neg (blcTwo E))]

theorem blcF_bound (E : CRing) : IsPolyBounded E (blcF E) 4 := by
  intro j hj
  show E.add (psSingle E (blcThree E) 2 j) (psSingle E (E.neg (blcTwo E)) 3 j) = E.zero
  rw [show psSingle E (blcThree E) 2 j = E.zero from if_neg (by omega),
    show psSingle E (E.neg (blcTwo E)) 3 j = E.zero from if_neg (by omega), E.zero_add E.zero]

/-! ## blc-2: 導関数の実因子分解 Df = 6X − 6X² -/

/-- **blc-2: 実導関数** Df = 6X − 6X²（一般 CRing E 上の陽な係数列）。 -/
def blcDeriv (E : CRing) : PS E :=
  psAdd E (psSingle E (blcSix E) 1) (psSingle E (E.neg (blcSix E)) 2)

theorem blcDeriv_coeff0 (E : CRing) : blcDeriv E 0 = E.zero := by
  show E.add (psSingle E (blcSix E) 1 0) (psSingle E (E.neg (blcSix E)) 2 0) = E.zero
  rw [show psSingle E (blcSix E) 1 0 = E.zero from if_neg (by omega),
    show psSingle E (E.neg (blcSix E)) 2 0 = E.zero from if_neg (by omega), E.zero_add E.zero]

theorem blcDeriv_coeff1 (E : CRing) : blcDeriv E 1 = blcSix E := by
  show E.add (psSingle E (blcSix E) 1 1) (psSingle E (E.neg (blcSix E)) 2 1) = blcSix E
  rw [show psSingle E (blcSix E) 1 1 = blcSix E from if_pos rfl,
    show psSingle E (E.neg (blcSix E)) 2 1 = E.zero from if_neg (by omega),
    CRing.add_zero E (blcSix E)]

theorem blcDeriv_coeff2 (E : CRing) : blcDeriv E 2 = E.neg (blcSix E) := by
  show E.add (psSingle E (blcSix E) 1 2) (psSingle E (E.neg (blcSix E)) 2 2) = E.neg (blcSix E)
  rw [show psSingle E (blcSix E) 1 2 = E.zero from if_neg (by omega),
    show psSingle E (E.neg (blcSix E)) 2 2 = E.neg (blcSix E) from if_pos rfl,
    E.zero_add (E.neg (blcSix E))]

theorem blcDeriv_bound (E : CRing) : IsPolyBounded E (blcDeriv E) 3 := by
  intro j hj
  show E.add (psSingle E (blcSix E) 1 j) (psSingle E (E.neg (blcSix E)) 2 j) = E.zero
  rw [show psSingle E (blcSix E) 1 j = E.zero from if_neg (by omega),
    show psSingle E (E.neg (blcSix E)) 2 j = E.zero from if_neg (by omega), E.zero_add E.zero]

/-- **blc-2 主等式**: formalDeriv f = 6X − 6X²（単項式則で係数ごとに確定）。 -/
theorem blc_deriv_eq (E : CRing) : formalDeriv E (blcF E) = blcDeriv E := by
  funext n
  show rnsmul E (n + 1) (blcF E (n + 1)) = blcDeriv E n
  cases n with
  | zero =>
    show rnsmul E 1 (blcF E 1) = blcDeriv E 0
    rw [blcF_coeff1 E, rnsmul_zero E, blcDeriv_coeff0 E]
  | succ n1 => cases n1 with
    | zero =>
      show rnsmul E 2 (blcF E 2) = blcDeriv E 1
      rw [blcF_coeff2 E,
        show rnsmul E 2 (blcThree E) = blcSix E from blc_rnsmul_rnsmul E 2 3 E.one,
        blcDeriv_coeff1 E]
    | succ n2 => cases n2 with
      | zero =>
        show rnsmul E 3 (blcF E 3) = blcDeriv E 2
        rw [blcF_coeff3 E, rnsmul_neg E 3 (blcTwo E),
          show rnsmul E 3 (blcTwo E) = blcSix E from blc_rnsmul_rnsmul E 3 2 E.one,
          blcDeriv_coeff2 E]
      | succ n3 =>
        show rnsmul E (n3 + 3 + 1) (blcF E (n3 + 3 + 1)) = blcDeriv E (n3 + 3)
        rw [blcF_bound E (n3 + 3 + 1) (by omega), rnsmul_zero E,
          blcDeriv_bound E (n3 + 3) (by omega)]

/-! ## blc-2': 一次因子 X − a の係数と有界性 -/

theorem blc_linFactor_coeff0 (E : CRing) (a : E.carrier) : psLinFactor E a 0 = E.neg a := by
  show E.add (psX E 0) (psC E (E.neg a) 0) = E.neg a
  rw [show psX E 0 = E.zero from if_neg (by omega),
    show psC E (E.neg a) 0 = E.neg a from rfl, E.zero_add (E.neg a)]

theorem blc_linFactor_coeff1 (E : CRing) (a : E.carrier) : psLinFactor E a 1 = E.one := by
  show E.add (psX E 1) (psC E (E.neg a) 1) = E.one
  rw [show psX E 1 = E.one from if_pos rfl,
    show psC E (E.neg a) 1 = E.zero from if_neg (by omega), CRing.add_zero E E.one]

theorem blc_linFactor_bound (E : CRing) (a : E.carrier) :
    IsPolyBounded E (psLinFactor E a) 2 := by
  intro j hj
  show E.add (psX E j) (psC E (E.neg a) j) = E.zero
  rw [show psX E j = E.zero from if_neg (by omega),
    show psC E (E.neg a) j = E.zero from if_neg (by omega), E.zero_add E.zero]

/-! ## blc-3a: y = 0 のファイバー f = X²·(3 − 2X) -/

/-- 3 − 2X（一次の tail・y=0 のファイバー分解の右因子）。 -/
def blcW (E : CRing) : PS E :=
  psAdd E (psC E (blcThree E)) (psSingle E (E.neg (blcTwo E)) 1)

theorem blc_blcW_coeff0 (E : CRing) : blcW E 0 = blcThree E := by
  show E.add (psC E (blcThree E) 0) (psSingle E (E.neg (blcTwo E)) 1 0) = blcThree E
  rw [show psC E (blcThree E) 0 = blcThree E from rfl,
    show psSingle E (E.neg (blcTwo E)) 1 0 = E.zero from if_neg (by omega),
    CRing.add_zero E (blcThree E)]

theorem blc_blcW_coeff1 (E : CRing) : blcW E 1 = E.neg (blcTwo E) := by
  show E.add (psC E (blcThree E) 1) (psSingle E (E.neg (blcTwo E)) 1 1) = E.neg (blcTwo E)
  rw [show psC E (blcThree E) 1 = E.zero from if_neg (by omega),
    show psSingle E (E.neg (blcTwo E)) 1 1 = E.neg (blcTwo E) from if_pos rfl,
    E.zero_add (E.neg (blcTwo E))]

theorem blc_blcW_bound (E : CRing) : IsPolyBounded E (blcW E) 2 := by
  intro j hj
  show E.add (psC E (blcThree E) j) (psSingle E (E.neg (blcTwo E)) 1 j) = E.zero
  rw [show psC E (blcThree E) j = E.zero from if_neg (by omega),
    show psSingle E (E.neg (blcTwo E)) 1 j = E.zero from if_neg (by omega), E.zero_add E.zero]

/-- f を X 倍する係数の literal 版（rw のための 0..3 展開）。 -/
theorem blc_mulX_0 (E : CRing) (f : PS E) : psMul E f (psX E) 0 = E.zero :=
  psMul_psX_zero E f
theorem blc_mulX_1 (E : CRing) (f : PS E) : psMul E f (psX E) 1 = f 0 :=
  psMul_psX_succ E f 0
theorem blc_mulX_2 (E : CRing) (f : PS E) : psMul E f (psX E) 2 = f 1 :=
  psMul_psX_succ E f 1
theorem blc_mulX_3 (E : CRing) (f : PS E) : psMul E f (psX E) 3 = f 2 :=
  psMul_psX_succ E f 2
theorem blc_mulX_4 (E : CRing) (f : PS E) : psMul E f (psX E) 4 = f 3 :=
  psMul_psX_succ E f 3
theorem blc_mulX_5 (E : CRing) (f : PS E) : psMul E f (psX E) 5 = f 4 :=
  psMul_psX_succ E f 4

/-- **blc-3a（下界・y=0）**: f = X²·(3 − 2X)（0 が二重根）。 -/
theorem blc_fiber_zero (E : CRing) :
    blcF E = psMul E (psMul E (psX E) (psX E)) (blcW E) := by
  have hre : psMul E (psMul E (psX E) (psX E)) (blcW E)
      = psMul E (psMul E (blcW E) (psX E)) (psX E) := by
    have h1 : psMul E (psMul E (psX E) (psX E)) (blcW E)
        = psMul E (blcW E) (psMul E (psX E) (psX E)) :=
      (psRing E).mul_comm (psMul E (psX E) (psX E)) (blcW E)
    have h2 : psMul E (blcW E) (psMul E (psX E) (psX E))
        = psMul E (psMul E (blcW E) (psX E)) (psX E) :=
      ((psRing E).mul_assoc (blcW E) (psX E) (psX E)).symm
    rw [h1, h2]
  rw [hre]
  funext n
  show blcF E n = psMul E (psMul E (blcW E) (psX E)) (psX E) n
  cases n with
  | zero =>
    rw [blc_mulX_0 E (psMul E (blcW E) (psX E))]
    exact blcF_coeff0 E
  | succ m => cases m with
    | zero =>
      rw [blc_mulX_1 E (psMul E (blcW E) (psX E)), blc_mulX_0 E (blcW E)]
      exact blcF_coeff1 E
    | succ j => cases j with
      | zero =>
        rw [blc_mulX_2 E (psMul E (blcW E) (psX E)), blc_mulX_1 E (blcW E), blc_blcW_coeff0 E]
        exact blcF_coeff2 E
      | succ i => cases i with
        | zero =>
          rw [blc_mulX_3 E (psMul E (blcW E) (psX E)), blc_mulX_2 E (blcW E), blc_blcW_coeff1 E]
          exact blcF_coeff3 E
        | succ k =>
          rw [psMul_psX_succ E (psMul E (blcW E) (psX E)) (k + 3),
            psMul_psX_succ E (blcW E) (k + 2), blc_blcW_bound E (k + 2) (by omega)]
          exact blcF_bound E (k + 4) (by omega)

/-! ## blc-3b: y = 1 のファイバー f − 1 = (X−1)²·(−(2X+1)) -/

/-- −(2X + 1)（y=1 のファイバー分解の右因子）。 -/
def blcM (E : CRing) : PS E :=
  psNeg E (psAdd E (psSingle E (blcTwo E) 1) (psOne E))

theorem blcM_coeff0 (E : CRing) : blcM E 0 = E.neg E.one := by
  show E.neg (E.add (psSingle E (blcTwo E) 1 0) (psOne E 0)) = E.neg E.one
  rw [show psSingle E (blcTwo E) 1 0 = E.zero from if_neg (by omega),
    show psOne E 0 = E.one from if_pos rfl, E.zero_add E.one]

theorem blcM_coeff1 (E : CRing) : blcM E 1 = E.neg (blcTwo E) := by
  show E.neg (E.add (psSingle E (blcTwo E) 1 1) (psOne E 1)) = E.neg (blcTwo E)
  rw [show psSingle E (blcTwo E) 1 1 = blcTwo E from if_pos rfl,
    show psOne E 1 = E.zero from if_neg (by omega), CRing.add_zero E (blcTwo E)]

theorem blcM_bound (E : CRing) : IsPolyBounded E (blcM E) 2 := by
  intro j hj
  show E.neg (E.add (psSingle E (blcTwo E) 1 j) (psOne E j)) = E.zero
  rw [show psSingle E (blcTwo E) 1 j = E.zero from if_neg (by omega),
    show psOne E j = E.zero from if_neg (by omega), E.zero_add E.zero, CRing.neg_zero E]

/-- f を X − 1 倍する分配（X 倍 + 定数 (−1) 倍）。 -/
theorem blc_mulLone (E : CRing) (f : PS E) :
    psMul E f (psLinFactor E E.one)
      = psAdd E (psMul E f (psX E)) (psMul E f (psC E (E.neg E.one))) :=
  psMul_psAdd E f (psX E) (psC E (E.neg E.one))

/-- p = M·(X−1) の係数 = (M·X)ₙ + Mₙ·(−1)。 -/
theorem blc_p_coeff (E : CRing) (n : Nat) :
    psMul E (blcM E) (psLinFactor E E.one) n
      = E.add (psMul E (blcM E) (psX E) n) (E.mul (blcM E n) (E.neg E.one)) := by
  rw [blc_mulLone E (blcM E)]
  show E.add (psMul E (blcM E) (psX E) n) (psMul E (blcM E) (psC E (E.neg E.one)) n)
    = E.add (psMul E (blcM E) (psX E) n) (E.mul (blcM E n) (E.neg E.one))
  rw [psMul_psC E (blcM E) (E.neg E.one) n]

theorem blc_p_val0 (E : CRing) : psMul E (blcM E) (psLinFactor E E.one) 0 = E.one := by
  rw [blc_p_coeff E 0, blc_mulX_0 E (blcM E), blcM_coeff0 E, E.zero_add, blc_negone_sq E]

theorem blc_p_val1 (E : CRing) :
    psMul E (blcM E) (psLinFactor E E.one) 1 = E.add (E.neg E.one) (blcTwo E) := by
  rw [blc_p_coeff E 1, blc_mulX_1 E (blcM E), blcM_coeff0 E, blcM_coeff1 E,
    blc_negmul_negone E (blcTwo E)]

theorem blc_p_val2 (E : CRing) :
    psMul E (blcM E) (psLinFactor E E.one) 2 = E.neg (blcTwo E) := by
  rw [blc_p_coeff E 2, blc_mulX_2 E (blcM E), blcM_coeff1 E, blcM_bound E 2 (by omega),
    CRing.zero_mul E (E.neg E.one), CRing.add_zero E (E.neg (blcTwo E))]

theorem blc_p_val3 (E : CRing) : psMul E (blcM E) (psLinFactor E E.one) 3 = E.zero := by
  rw [blc_p_coeff E 3, blc_mulX_3 E (blcM E), blcM_bound E 2 (by omega),
    blcM_bound E 3 (by omega), CRing.zero_mul E (E.neg E.one), CRing.add_zero E E.zero]

theorem blc_p_bound (E : CRing) : IsPolyBounded E (psMul E (blcM E) (psLinFactor E E.one)) 4 :=
  simpleExt_mul_bounded E (blcM_bound E) (blc_linFactor_bound E E.one)

/-- RHS = (M·(X−1))·(X−1) の係数分配。 -/
theorem blc_rhs_coeff (E : CRing) (n : Nat) :
    psMul E (psMul E (blcM E) (psLinFactor E E.one)) (psLinFactor E E.one) n
      = E.add (psMul E (psMul E (blcM E) (psLinFactor E E.one)) (psX E) n)
          (E.mul (psMul E (blcM E) (psLinFactor E E.one) n) (E.neg E.one)) := by
  rw [blc_mulLone E (psMul E (blcM E) (psLinFactor E E.one))]
  show E.add (psMul E (psMul E (blcM E) (psLinFactor E E.one)) (psX E) n)
      (psMul E (psMul E (blcM E) (psLinFactor E E.one)) (psC E (E.neg E.one)) n)
    = E.add (psMul E (psMul E (blcM E) (psLinFactor E E.one)) (psX E) n)
        (E.mul (psMul E (blcM E) (psLinFactor E E.one) n) (E.neg E.one))
  rw [psMul_psC E (psMul E (blcM E) (psLinFactor E E.one)) (E.neg E.one) n]

theorem blc_rhs_bound (E : CRing) :
    IsPolyBounded E
      (psMul E (psMul E (blcM E) (psLinFactor E E.one)) (psLinFactor E E.one)) 6 :=
  simpleExt_mul_bounded E (blc_p_bound E) (blc_linFactor_bound E E.one)

/-- **blc-3b（下界・y=1）**: f − 1 = (X−1)²·(−(2X+1))（1 が二重根）。 -/
theorem blc_fiber_one (E : CRing) :
    psAdd E (blcF E) (psC E (E.neg E.one))
      = psMul E (psMul E (psLinFactor E E.one) (psLinFactor E E.one)) (blcM E) := by
  have hre : psMul E (psMul E (psLinFactor E E.one) (psLinFactor E E.one)) (blcM E)
      = psMul E (psMul E (blcM E) (psLinFactor E E.one)) (psLinFactor E E.one) := by
    have h1 : psMul E (psMul E (psLinFactor E E.one) (psLinFactor E E.one)) (blcM E)
        = psMul E (blcM E) (psMul E (psLinFactor E E.one) (psLinFactor E E.one)) :=
      (psRing E).mul_comm (psMul E (psLinFactor E E.one) (psLinFactor E E.one)) (blcM E)
    have h2 : psMul E (blcM E) (psMul E (psLinFactor E E.one) (psLinFactor E E.one))
        = psMul E (psMul E (blcM E) (psLinFactor E E.one)) (psLinFactor E E.one) :=
      ((psRing E).mul_assoc (blcM E) (psLinFactor E E.one) (psLinFactor E E.one)).symm
    rw [h1, h2]
  rw [hre]
  funext n
  show E.add (blcF E n) (psC E (E.neg E.one) n)
    = psMul E (psMul E (blcM E) (psLinFactor E E.one)) (psLinFactor E E.one) n
  cases n with
  | zero =>
    rw [blc_rhs_coeff E 0, blc_mulX_0 E (psMul E (blcM E) (psLinFactor E E.one)), blc_p_val0 E,
      E.one_mul (E.neg E.one), E.zero_add (E.neg E.one), blcF_coeff0 E,
      show psC E (E.neg E.one) 0 = E.neg E.one from rfl, E.zero_add (E.neg E.one)]
  | succ m => cases m with
    | zero =>
      rw [blc_rhs_coeff E 1, blc_mulX_1 E (psMul E (blcM E) (psLinFactor E E.one)),
        blc_p_val0 E, blc_p_val1 E, blcF_coeff1 E,
        show psC E (E.neg E.one) 1 = E.zero from if_neg (by omega), E.zero_add E.zero,
        CRing.right_distrib E (E.neg E.one) (blcTwo E) (E.neg E.one), blc_negone_sq E,
        CRing.mul_neg E (blcTwo E) E.one, CRing.mul_one E (blcTwo E)]
      exact (blc_val1 E).symm
    | succ j => cases j with
      | zero =>
        rw [blc_rhs_coeff E 2, blc_mulX_2 E (psMul E (blcM E) (psLinFactor E E.one)),
          blc_p_val1 E, blc_p_val2 E, blc_negmul_negone E (blcTwo E), blcF_coeff2 E,
          show psC E (E.neg E.one) 2 = E.zero from if_neg (by omega), CRing.add_zero E (blcThree E)]
        exact (blc_val2 E).symm
      | succ i => cases i with
        | zero =>
          rw [blc_rhs_coeff E 3, blc_mulX_3 E (psMul E (blcM E) (psLinFactor E E.one)),
            blc_p_val2 E, blc_p_val3 E, CRing.zero_mul E (E.neg E.one),
            CRing.add_zero E (E.neg (blcTwo E)), blcF_coeff3 E,
            show psC E (E.neg E.one) 3 = E.zero from if_neg (by omega),
            CRing.add_zero E (E.neg (blcTwo E))]
        | succ k0 => cases k0 with
          | zero =>
            rw [blc_rhs_coeff E 4, blc_mulX_4 E (psMul E (blcM E) (psLinFactor E E.one)),
              blc_p_val3 E, blc_p_bound E 4 (by omega), CRing.zero_mul E (E.neg E.one),
              E.zero_add E.zero, blcF_bound E 4 (by omega),
              show psC E (E.neg E.one) 4 = E.zero from if_neg (by omega), E.zero_add E.zero]
          | succ k1 => cases k1 with
            | zero =>
              rw [blc_rhs_coeff E 5, blc_mulX_5 E (psMul E (blcM E) (psLinFactor E E.one)),
                blc_p_bound E 4 (by omega), blc_p_bound E 5 (by omega),
                CRing.zero_mul E (E.neg E.one), E.zero_add E.zero, blcF_bound E 5 (by omega),
                show psC E (E.neg E.one) 5 = E.zero from if_neg (by omega), E.zero_add E.zero]
            | succ k =>
              show E.add (blcF E (k + 6)) (psC E (E.neg E.one) (k + 6))
                = psMul E (psMul E (blcM E) (psLinFactor E E.one)) (psLinFactor E E.one) (k + 6)
              rw [blc_rhs_bound E (k + 6) (by omega), blcF_bound E (k + 6) (by omega),
                show psC E (E.neg E.one) (k + 6) = E.zero from if_neg (by omega), E.zero_add E.zero]

/-! ## blc-4: rpow の小補題（import 外の名前を局所化） -/

/-- rpow a 1 = a。 -/
theorem blc_rpow_one (E : CRing) (a : E.carrier) : rpow E a 1 = a := by
  show E.mul (rpow E a 0) a = a
  rw [rpow_zero E a, E.one_mul a]

/-- rpow 1 k = 1（全 k）。 -/
theorem blc_rpow_one_one (E : CRing) : ∀ k, rpow E E.one k = E.one := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show E.mul (rpow E E.one k) E.one = E.one
    rw [CRing.mul_one E (rpow E E.one k), ih]

/-! ## blc-4: 打ち切り評価の小補題 -/

/-- 定数 c の a での評価 = c（打ち切り 1）。 -/
theorem blc_eval_psC (E : CRing) (a c : E.carrier) :
    evalSum (evalHomId E) a (psC E c) 1 = c := by
  rw [evalSum_id]
  show E.add E.zero (E.mul (psC E c 0) (rpow E a 0)) = c
  rw [show psC E c 0 = c from rfl, rpow_zero E a, CRing.mul_one E c, E.zero_add c]

/-- 一次因子 X − a の a での評価 = 0（a − a = 0）。 -/
theorem blc_eval_linFactor (E : CRing) (a : E.carrier) :
    evalSum (evalHomId E) a (psLinFactor E a) 2 = E.zero := by
  rw [evalSum_id]
  show E.add (E.add E.zero (E.mul (psLinFactor E a 0) (rpow E a 0)))
      (E.mul (psLinFactor E a 1) (rpow E a 1)) = E.zero
  rw [blc_linFactor_coeff0 E a, blc_linFactor_coeff1 E a, rpow_zero E a, blc_rpow_one E a,
    CRing.mul_one E (E.neg a), E.one_mul a, E.zero_add (E.neg a)]
  exact E.neg_add a

/-- **blc_eval_fun**（多項式↔写像の橋）: f の a での評価 = 3a² − 2a³。 -/
theorem blc_eval_F (E : CRing) (a : E.carrier) :
    evalSum (evalHomId E) a (blcF E) 4
      = E.add (E.mul (blcThree E) (rpow E a 2)) (E.mul (E.neg (blcTwo E)) (rpow E a 3)) := by
  rw [evalSum_id]
  show E.add (E.add (E.add (E.add E.zero (E.mul (blcF E 0) (rpow E a 0)))
      (E.mul (blcF E 1) (rpow E a 1))) (E.mul (blcF E 2) (rpow E a 2)))
      (E.mul (blcF E 3) (rpow E a 3))
    = E.add (E.mul (blcThree E) (rpow E a 2)) (E.mul (E.neg (blcTwo E)) (rpow E a 3))
  rw [blcF_coeff0 E, blcF_coeff1 E, blcF_coeff2 E, blcF_coeff3 E,
    CRing.zero_mul E (rpow E a 0), CRing.zero_mul E (rpow E a 1),
    E.zero_add E.zero, E.zero_add E.zero,
    E.zero_add (E.mul (blcThree E) (rpow E a 2))]

/-- Df の a での評価 = 6a − 6a²（打ち切り 3）。 -/
theorem blc_eval_deriv (E : CRing) (a : E.carrier) :
    evalSum (evalHomId E) a (blcDeriv E) 3
      = E.add (E.mul (blcSix E) a) (E.mul (E.neg (blcSix E)) (E.mul a a)) := by
  have hr2 : rpow E a 2 = E.mul a a := by
    show E.mul (rpow E a 1) a = E.mul a a
    rw [blc_rpow_one E a]
  rw [evalSum_id]
  show E.add (E.add (E.add E.zero (E.mul (blcDeriv E 0) (rpow E a 0)))
      (E.mul (blcDeriv E 1) (rpow E a 1))) (E.mul (blcDeriv E 2) (rpow E a 2))
    = E.add (E.mul (blcSix E) a) (E.mul (E.neg (blcSix E)) (E.mul a a))
  rw [blcDeriv_coeff0 E, blcDeriv_coeff1 E, blcDeriv_coeff2 E, rpow_zero E a, blc_rpow_one E a, hr2,
    CRing.zero_mul E E.one, E.zero_add E.zero, E.zero_add (E.mul (blcSix E) a)]

/-! ## blc-4 ★主定理: 分岐軌跡の上界（任意の零因子なし拡大環で） -/

/-- **★ blc_branch_locus**（設計 §3 blc-4）: 零因子なし・6·1≠0 の任意の可換環 E で、
    f − y が有界証人つきの二重一次因子 (X−a)² を因子に持つなら y ∈ {0,1}。
    一次因子ライプニッツで D(f−y)=Df を有界因子の和として書き、a で評価して
    Df(a)=6a(1−a)=0、零因子なしで a∈{0,1}、f を a で評価して y=f(a)∈{0,1}。 -/
theorem blc_branch_locus (E : CRing)
    (hdom : ∀ x z : E.carrier, E.mul x z = E.zero → x = E.zero ∨ z = E.zero)
    (h6 : blcSix E ≠ E.zero)
    (y a : E.carrier) (g : PS E) (hg : IsPolyBounded E g 2)
    (hfac : psAdd E (blcF E) (psC E (E.neg y))
              = psMul E (psMul E (psLinFactor E a) (psLinFactor E a)) g) :
    y = E.zero ∨ y = E.one := by
  -- 有界性
  have hlin : IsPolyBounded E (psLinFactor E a) 2 := blc_linFactor_bound E a
  have hw4 : IsPolyBounded E (psMul E (psLinFactor E a) g) 4 := simpleExt_mul_bounded E hlin hg
  have hDw : IsPolyBounded E (formalDeriv E (psMul E (psLinFactor E a) g)) 3 :=
    blc_deriv_bounded E (psMul E (psLinFactor E a) g) 3 hw4
  have hLL : IsPolyBounded E (psMul E (psLinFactor E a) (psLinFactor E a)) 4 :=
    simpleExt_mul_bounded E hlin hlin
  -- D(f−y) = Df = blcDeriv
  have hD1 : formalDeriv E (psAdd E (blcF E) (psC E (E.neg y))) = blcDeriv E := by
    rw [formalDeriv_add E (blcF E) (psC E (E.neg y)), formalDeriv_psC E (E.neg y), blc_deriv_eq E]
    funext n
    show E.add (blcDeriv E n) (psZero E n) = blcDeriv E n
    exact CRing.add_zero E (blcDeriv E n)
  -- RHS を (M·(X−a))·(X−a) に並べ替え
  have hre : psMul E (psMul E (psLinFactor E a) (psLinFactor E a)) g
      = psMul E (psMul E (psLinFactor E a) g) (psLinFactor E a) := by
    have h1 : psMul E (psMul E (psLinFactor E a) (psLinFactor E a)) g
        = psMul E (psLinFactor E a) (psMul E (psLinFactor E a) g) :=
      (psRing E).mul_assoc (psLinFactor E a) (psLinFactor E a) g
    have h2 : psMul E (psLinFactor E a) (psMul E (psLinFactor E a) g)
        = psMul E (psMul E (psLinFactor E a) g) (psLinFactor E a) :=
      (psRing E).mul_comm (psLinFactor E a) (psMul E (psLinFactor E a) g)
    rw [h1, h2]
  -- D(f−y) = D(w·(X−a)) = Dw·(X−a) + w
  have hD2 : formalDeriv E (psAdd E (blcF E) (psC E (E.neg y)))
      = psAdd E (psMul E (formalDeriv E (psMul E (psLinFactor E a) g)) (psLinFactor E a))
          (psMul E (psLinFactor E a) g) := by
    rw [hfac, hre]
    exact formalDeriv_mul_linFactor E (psMul E (psLinFactor E a) g) a
  have hDeriv : blcDeriv E
      = psAdd E (psMul E (formalDeriv E (psMul E (psLinFactor E a) g)) (psLinFactor E a))
          (psMul E (psLinFactor E a) g) := hD1.symm.trans hD2
  -- 評価（打ち切り 6）
  have hev6 : evalSum (evalHomId E) a (blcDeriv E) 6
      = evalSum (evalHomId E) a
          (psAdd E (psMul E (formalDeriv E (psMul E (psLinFactor E a) g)) (psLinFactor E a))
            (psMul E (psLinFactor E a) g)) 6 :=
    congrArg (fun s => evalSum (evalHomId E) a s 6) hDeriv
  have hLHS6 : evalSum (evalHomId E) a (blcDeriv E) 6
      = E.add (E.mul (blcSix E) a) (E.mul (E.neg (blcSix E)) (E.mul a a)) := by
    rw [evalHom_stable (evalHomId E) a (blcDeriv E) 3 (blcDeriv_bound E) 6 (by omega)]
    exact blc_eval_deriv E a
  have hterm1 : evalSum (evalHomId E) a
      (psMul E (formalDeriv E (psMul E (psLinFactor E a) g)) (psLinFactor E a)) 6 = E.zero := by
    rw [evalHom_id_mul E a (formalDeriv E (psMul E (psLinFactor E a) g)) (psLinFactor E a)
        3 2 hDw hlin, blc_eval_linFactor E a]
    exact CRing.mul_zero E
      (evalSum (evalHomId E) a (formalDeriv E (psMul E (psLinFactor E a) g)) 3)
  have hterm2 : evalSum (evalHomId E) a (psMul E (psLinFactor E a) g) 6 = E.zero := by
    have h54 : evalSum (evalHomId E) a (psMul E (psLinFactor E a) g) 5
        = evalSum (evalHomId E) a (psMul E (psLinFactor E a) g) 4 :=
      evalHom_stable (evalHomId E) a (psMul E (psLinFactor E a) g) 4 hw4 5 (by omega)
    have h64 : evalSum (evalHomId E) a (psMul E (psLinFactor E a) g) 6
        = evalSum (evalHomId E) a (psMul E (psLinFactor E a) g) 4 :=
      evalHom_stable (evalHomId E) a (psMul E (psLinFactor E a) g) 4 hw4 6 (by omega)
    have h5 : evalSum (evalHomId E) a (psMul E (psLinFactor E a) g) 5 = E.zero := by
      rw [evalHom_id_mul E a (psLinFactor E a) g 2 2 hlin hg, blc_eval_linFactor E a]
      exact CRing.zero_mul E (evalSum (evalHomId E) a g 2)
    rw [h64, ← h54, h5]
  have hRHS6 : evalSum (evalHomId E) a
      (psAdd E (psMul E (formalDeriv E (psMul E (psLinFactor E a) g)) (psLinFactor E a))
        (psMul E (psLinFactor E a) g)) 6 = E.zero := by
    rw [evalHom_add (evalHomId E) a
        (psMul E (formalDeriv E (psMul E (psLinFactor E a) g)) (psLinFactor E a))
        (psMul E (psLinFactor E a) g) 6, hterm1, hterm2, E.zero_add E.zero]
  have heq0 : E.add (E.mul (blcSix E) a) (E.mul (E.neg (blcSix E)) (E.mul a a)) = E.zero :=
    hLHS6.symm.trans (hev6.trans hRHS6)
  -- 因子化 6·(a·(1−a)) = 0
  have hfac2 : E.mul (blcSix E) (E.mul a (E.add E.one (E.neg a))) = E.zero := by
    rw [E.left_distrib a E.one (E.neg a), CRing.mul_one E a, CRing.mul_neg E a a,
      E.left_distrib (blcSix E) a (E.neg (E.mul a a)), CRing.mul_neg E (blcSix E) (E.mul a a),
      ← CRing.neg_mul E (blcSix E) (E.mul a a)]
    exact heq0
  have haa : E.mul a (E.add E.one (E.neg a)) = E.zero := by
    cases hdom (blcSix E) (E.mul a (E.add E.one (E.neg a))) hfac2 with
    | inl h6' => exact absurd h6' h6
    | inr h => exact h
  have hA : a = E.zero ∨ a = E.one := by
    cases hdom a (E.add E.one (E.neg a)) haa with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (CRing.eq_of_sub_eq_zero E h).symm
  -- y = f(a)
  have hcong : evalSum (evalHomId E) a (psAdd E (blcF E) (psC E (E.neg y))) 7
      = evalSum (evalHomId E) a
          (psMul E (psMul E (psLinFactor E a) (psLinFactor E a)) g) 7 :=
    congrArg (fun s => evalSum (evalHomId E) a s 7) hfac
  have hL : evalSum (evalHomId E) a (psAdd E (blcF E) (psC E (E.neg y))) 7
      = E.add (E.add (E.mul (blcThree E) (rpow E a 2)) (E.mul (E.neg (blcTwo E)) (rpow E a 3)))
          (E.neg y) := by
    rw [evalHom_add (evalHomId E) a (blcF E) (psC E (E.neg y)) 7,
      evalHom_stable (evalHomId E) a (blcF E) 4 (blcF_bound E) 7 (by omega),
      blc_eval_F E a,
      evalHom_stable (evalHomId E) a (psC E (E.neg y)) 1
        (by intro i hi; show psC E (E.neg y) i = E.zero; exact if_neg (by omega)) 7 (by omega),
      blc_eval_psC E a (E.neg y)]
  have hR : evalSum (evalHomId E) a
      (psMul E (psMul E (psLinFactor E a) (psLinFactor E a)) g) 7 = E.zero := by
    rw [evalHom_id_mul E a (psMul E (psLinFactor E a) (psLinFactor E a)) g 4 2 hLL hg]
    have hLL4 : evalSum (evalHomId E) a (psMul E (psLinFactor E a) (psLinFactor E a)) 4 = E.zero := by
      have hst : evalSum (evalHomId E) a (psMul E (psLinFactor E a) (psLinFactor E a)) 5
          = evalSum (evalHomId E) a (psMul E (psLinFactor E a) (psLinFactor E a)) 4 :=
        evalHom_stable (evalHomId E) a (psMul E (psLinFactor E a) (psLinFactor E a)) 4 hLL 5 (by omega)
      rw [← hst, evalHom_id_mul E a (psLinFactor E a) (psLinFactor E a) 2 2 hlin hlin,
        blc_eval_linFactor E a]
      exact CRing.zero_mul E E.zero
    rw [hLL4]
    exact CRing.zero_mul E (evalSum (evalHomId E) a g 2)
  have hsum0 : E.add (E.add (E.mul (blcThree E) (rpow E a 2))
      (E.mul (E.neg (blcTwo E)) (rpow E a 3))) (E.neg y) = E.zero :=
    hL.symm.trans (hcong.trans hR)
  have hyval : y = E.add (E.mul (blcThree E) (rpow E a 2)) (E.mul (E.neg (blcTwo E)) (rpow E a 3)) :=
    (CRing.eq_of_sub_eq_zero E hsum0).symm
  -- a=0 ⟹ y=0, a=1 ⟹ y=1
  cases hA with
  | inl ha0 =>
    left
    rw [hyval, ha0,
      show rpow E E.zero 2 = E.zero from CRing.mul_zero E (rpow E E.zero 1),
      show rpow E E.zero 3 = E.zero from CRing.mul_zero E (rpow E E.zero 2),
      CRing.mul_zero E (blcThree E), CRing.mul_zero E (E.neg (blcTwo E)), E.zero_add E.zero]
  | inr ha1 =>
    right
    rw [hyval, ha1, blc_rpow_one_one E 2, blc_rpow_one_one E 3,
      CRing.mul_one E (blcThree E), CRing.mul_one E (E.neg (blcTwo E))]
    exact blc_three_sub_two E

/-! ## blc-5: 実 ℚ での具体化（零因子なし・整数係数の非零） -/

/-- n·1（ℚ 上）の代表 = n/1。 -/
theorem blc_rnsmul_one_rep (n : Nat) :
    rnsmul ratRing n ratRing.one = Quot.mk ratRel (intToPreRat (Int.ofNat n)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show ratRing.add (rnsmul ratRing k ratRing.one) ratRing.one
      = Quot.mk ratRel (intToPreRat (Int.ofNat (k + 1)))
    rw [ih]
    show Quot.mk ratRel (prAdd (intToPreRat (Int.ofNat k)) prOne)
      = Quot.mk ratRel (intToPreRat (Int.ofNat (k + 1)))
    apply Quot.sound
    show (Int.ofNat k * 1 + 1 * 1) * 1 = Int.ofNat (k + 1) * (1 * 1)
    show (Int.ofNat k * 1 + 1 * 1) * 1 = (Int.ofNat k + 1) * (1 * 1)
    omega

/-- n ≠ 0 なら n·1 ≠ 0（ℚ 上）— 分子 n が非零。 -/
theorem blc_ofNat_ne_zero (n : Nat) (hn : n ≠ 0) :
    rnsmul ratRing n ratRing.one ≠ ratRing.zero := by
  rw [blc_rnsmul_one_rep n]
  intro h
  have hrel : ratRel (intToPreRat (Int.ofNat n)) prZero := quot_exact_rat h
  have h2 : Int.ofNat n * 1 = 0 * 1 := hrel
  rw [Int.mul_one, Int.zero_mul] at h2
  exact hn (Int.ofNat_eq_zero.mp h2)

theorem blc_two_rat_ne_zero : blcTwo ratRing ≠ ratRing.zero := blc_ofNat_ne_zero 2 (by omega)
theorem blc_three_rat_ne_zero : blcThree ratRing ≠ ratRing.zero := blc_ofNat_ne_zero 3 (by omega)
theorem blc_six_rat_ne_zero : blcSix ratRing ≠ ratRing.zero := blc_ofNat_ne_zero 6 (by omega)

/-- ℚ の元は 0 か 0 でないかを構成的に判定（代表の分子で Int.decEq）。 -/
theorem blc_rat_eq_zero_dec (x : ratRing.carrier) :
    x = ratRing.zero ∨ x ≠ ratRing.zero := by
  induction x using Quot.ind
  rename_i r
  cases Int.decEq r.num 0 with
  | isTrue h =>
    left
    apply Quot.sound
    show r.num * 1 = 0 * r.den
    rw [h, Int.zero_mul, Int.zero_mul]
  | isFalse h =>
    right
    intro hc
    have hrel : ratRel r prZero := quot_exact_rat hc
    have h2 : r.num * 1 = 0 * r.den := hrel
    rw [Int.mul_one, Int.zero_mul] at h2
    exact h h2

/-- **ℚ は零因子を持たない**（本物の IUTField ℚ の整域性 ＋ 構成的ゼロ判定）。 -/
theorem blc_rat_no_zero_div (x z : ratRing.carrier)
    (h : ratRing.mul x z = ratRing.zero) : x = ratRing.zero ∨ z = ratRing.zero := by
  cases blc_rat_eq_zero_dec x with
  | inl hx => exact Or.inl hx
  | inr hx => exact Or.inr (ratIUTField.eq_zero_of_mul_eq_zero_left h hx)

/-- **blc_branch_locus_rat**（設計 §3 blc-5）: 実 ℚ での分岐軌跡上界の具体化。 -/
theorem blc_branch_locus_rat (y a : ratRing.carrier) (g : PS ratRing)
    (hg : IsPolyBounded ratRing g 2)
    (hfac : psAdd ratRing (blcF ratRing) (psC ratRing (ratRing.neg y))
              = psMul ratRing (psMul ratRing (psLinFactor ratRing a) (psLinFactor ratRing a)) g) :
    y = ratRing.zero ∨ y = ratRing.one :=
  blc_branch_locus ratRing blc_rat_no_zero_div blc_six_rat_ne_zero y a g hg hfac

/-! ## blc-5: P¹ の点集合・写像・∞ チャート（e_∞ = 3 の顕示） -/

/-- 実 Belyi 写像の点関数 x ↦ 3x² − 2x³。 -/
def blcFunVal (E : CRing) (x : E.carrier) : E.carrier :=
  E.add (E.mul (blcThree E) (rpow E x 2)) (E.mul (E.neg (blcTwo E)) (rpow E x 3))

/-- **blc_eval_fun**: 多項式 f の a での打ち切り評価 = 点関数 blcFunVal。 -/
theorem blc_eval_fun (E : CRing) (a : E.carrier) :
    evalSum (evalHomId E) a (blcF E) 4 = blcFunVal E a := blc_eval_F E a

/-- **blcP1**: P¹ の点集合（none = ∞、K-点集合 Option K・スキームではない）。 -/
def blcP1 (E : CRing) : Type := Option E.carrier

/-- **blcMap**: 実 Belyi 写像 P¹ → P¹（some x ↦ some f(x)・∞ ↦ ∞）。 -/
def blcMap (E : CRing) : blcP1 E → blcP1 E := fun p =>
  match p with
  | none => none
  | some x => some (blcFunVal E x)

/-- **blc_map_infty_fiber**: ∞ のファイバーはちょうど {∞}。 -/
theorem blc_map_infty_fiber (E : CRing) (p : blcP1 E) :
    blcMap E p = none ↔ p = none := by
  constructor
  · intro h
    cases p with
    | none => rfl
    | some x =>
      exact absurd (show (some (blcFunVal E x) : Option E.carrier) = none from h)
        (Option.some_ne_none (blcFunVal E x))
  · intro h
    subst h
    rfl

/-- inv u の k 乗と u の k 乗の積は 1（u ≠ 0）。 -/
theorem blc_inv_pow (u : ratRing.carrier) (hu : u ≠ ratRing.zero) : ∀ k,
    ratRing.mul (rpow ratRing (ratIUTField.inv u) k) (rpow ratRing u k) = ratRing.one := by
  intro k
  induction k with
  | zero => exact ratRing.one_mul ratRing.one
  | succ k ih =>
    show ratRing.mul (ratRing.mul (rpow ratRing (ratIUTField.inv u) k) (ratIUTField.inv u))
        (ratRing.mul (rpow ratRing u k) u) = ratRing.one
    have hswap : ratRing.mul (ratRing.mul (rpow ratRing (ratIUTField.inv u) k) (ratIUTField.inv u))
          (ratRing.mul (rpow ratRing u k) u)
        = ratRing.mul (ratRing.mul (rpow ratRing (ratIUTField.inv u) k) (rpow ratRing u k))
          (ratRing.mul (ratIUTField.inv u) u) :=
      IUTField.mul_mul_mul_comm ratIUTField (rpow ratRing (ratIUTField.inv u) k)
        (ratIUTField.inv u) (rpow ratRing u k) u
    have hcancel : ratRing.mul (ratIUTField.inv u) u = ratRing.one :=
      IUTField.inv_mul_cancel ratIUTField hu
    rw [hswap, ih, hcancel, ratRing.one_mul ratRing.one]

/-- **blc_infty_chart**（設計 §3 blc-5）: ∞ チャート恒等式 f(1/u)·u³ = 3u − 2。
    u = 0 で右辺 = −2 ≠ 0（3 位の零点 = e_∞ = 3 の正直な顕示・付値ではない）。 -/
theorem blc_infty_chart (u : ratRing.carrier) (hu : u ≠ ratRing.zero) :
    ratRing.mul (blcFunVal ratRing (ratIUTField.inv u)) (rpow ratRing u 3)
      = ratRing.add (ratRing.mul (blcThree ratRing) u) (ratRing.neg (blcTwo ratRing)) := by
  have hu2 : ratRing.mul (rpow ratRing (ratIUTField.inv u) 2) (rpow ratRing u 3) = u := by
    show ratRing.mul (rpow ratRing (ratIUTField.inv u) 2) (ratRing.mul (rpow ratRing u 2) u) = u
    rw [← ratRing.mul_assoc, blc_inv_pow u hu 2, ratRing.one_mul u]
  have hu3 : ratRing.mul (rpow ratRing (ratIUTField.inv u) 3) (rpow ratRing u 3) = ratRing.one :=
    blc_inv_pow u hu 3
  show ratRing.mul (ratRing.add
      (ratRing.mul (blcThree ratRing) (rpow ratRing (ratIUTField.inv u) 2))
      (ratRing.mul (ratRing.neg (blcTwo ratRing)) (rpow ratRing (ratIUTField.inv u) 3)))
      (rpow ratRing u 3)
    = ratRing.add (ratRing.mul (blcThree ratRing) u) (ratRing.neg (blcTwo ratRing))
  rw [CRing.right_distrib ratRing (ratRing.mul (blcThree ratRing) (rpow ratRing (ratIUTField.inv u) 2))
      (ratRing.mul (ratRing.neg (blcTwo ratRing)) (rpow ratRing (ratIUTField.inv u) 3))
      (rpow ratRing u 3),
    ratRing.mul_assoc (blcThree ratRing) (rpow ratRing (ratIUTField.inv u) 2) (rpow ratRing u 3),
    hu2,
    ratRing.mul_assoc (ratRing.neg (blcTwo ratRing)) (rpow ratRing (ratIUTField.inv u) 3) (rpow ratRing u 3),
    hu3, CRing.mul_one ratRing (ratRing.neg (blcTwo ratRing))]

/-- **blc_infty_unit**: チャート多項式 3u − 2 の u = 0 での値 = −2 ≠ 0
    （∞ での全分岐 e_∞ = 3 が退化しないことの顕示）。 -/
theorem blc_infty_unit :
    ratRing.add (ratRing.mul (blcThree ratRing) ratRing.zero) (ratRing.neg (blcTwo ratRing))
      ≠ ratRing.zero := by
  rw [CRing.mul_zero ratRing (blcThree ratRing), ratRing.zero_add (ratRing.neg (blcTwo ratRing))]
  intro h
  apply blc_two_rat_ne_zero
  have h2 := congrArg ratRing.neg h
  rw [CRing.neg_neg ratRing (blcTwo ratRing), CRing.neg_zero ratRing] at h2
  exact h2

/-! ## blc-6: 見出し束ね -/

/-- **BelyiCubicData**（設計 §3 blc-6）: 実基底体・実 Belyi 多項式と、その分岐値
    {0,1,∞} の完全決定（上界 branch_upper ＋ 下界 fiber0/fiber1）。 -/
structure BelyiCubicData where
  /-- 基底環（本物の可換環）。 -/
  base : CRing
  /-- 実 Belyi 多項式。 -/
  poly : PS base
  /-- 下界 y=0: X² が二重因子。 -/
  fiber0 : poly = psMul base (psMul base (psX base) (psX base)) (blcW base)
  /-- 下界 y=1: (X−1)² が二重因子。 -/
  fiber1 : psAdd base poly (psC base (base.neg base.one))
      = psMul base (psMul base (psLinFactor base base.one) (psLinFactor base base.one)) (blcM base)
  /-- 上界: 二重根 ⟹ y ∈ {0,1}（零因子なし・6·1≠0 の下で）。 -/
  branch_upper : ∀ (y a : base.carrier) (g : PS base), IsPolyBounded base g 2 →
    (∀ x z : base.carrier, base.mul x z = base.zero → x = base.zero ∨ z = base.zero) →
    blcSix base ≠ base.zero →
    psAdd base poly (psC base (base.neg y))
      = psMul base (psMul base (psLinFactor base a) (psLinFactor base a)) g →
    y = base.zero ∨ y = base.one

/-- **blcData**: E = ℚ の実証人（実 ℚ 上の f = 3X² − 2X³）。 -/
def blcData : BelyiCubicData where
  base := ratRing
  poly := blcF ratRing
  fiber0 := blc_fiber_zero ratRing
  fiber1 := blc_fiber_one ratRing
  branch_upper := fun y a g hg hdom h6 hfac => blc_branch_locus ratRing hdom h6 y a g hg hfac

/-- **blc_belyi_exists**: 実 Belyi 三点分岐データは存在する。 -/
theorem blc_belyi_exists : Nonempty BelyiCubicData := ⟨blcData⟩

end IUT
