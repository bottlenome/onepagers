/-
  IUT/ArakelovMetrizedLineQ.lean — M474F [実／(a) 昇格]

  分類: **[実]** — 実 ℚ（QRat = Quot ratRel・ratRing）上の**実計量付き直線束**
    L̄ = (q·ℤ ⊂ ℚ, ‖·‖ = λ·|·|_∞) と**実算術次数（乗法形）**。アルキメデス計量は
    実アルキメデス絶対値 arpAbs（=qAbs, M115F）の正スケール λ 倍、有限部の寄与は
    実 p 進絶対値 pavAbs（p^{-v_p}）、切断非依存性は実 B5 積公式
    b5_product_formula（∏_v|x|_v = 1 over ℚˣ, B5ProductFormulaQ）から証明する。

  complete_pct 影響: **あり（C3 の 0→ 前進を意図・判定は独立監査）**。
    C3=0 の診断: 既存 M356F 系（ArakelovDivisor / ArakelovClassDegree /
    ArakelovArithDegree 等）は (i) 主語が pfRational（sign×RawDiv という ℚˣ の
    因子模型）で実 ℚ でない、(ii) 「log p」が自由パラメタ logp : Nat → RReal で
    実対数でない、(iii) |x|_∞ が「積公式が成り立つように」付値データから circular
    に定義されており（実計量なし）、(iv) 計量付き直線束という対象そのものが不在
    （因子群のみ）。本モジュールは主語を実 ℚ に置換し、(iv) を初めて本物にする:
    直線束 = 実 ℚ の真の ℤ-部分加群 q·ℤ（amlMem・加法閉・ℤ 作用閉を証明）、
    計量 = 実 |·|_∞ の正スケール（斉次性・非負性・正定値性を証明）、算術次数 =
    乗法形 deg×(L̄) := 1/(λ·|q|_∞)（deg = −log(λ|q|_∞) の指数形）で、
    任意の非零有理切断 s = q·x に対する次数公式
      deg×(L̄) · (‖s‖ · ∏_p |s/q|_p) = 1
    と切断非依存性を**実 B5 積公式から**証明（模型積公式 M351F の消費を実 B5 に
    置換＝§2(a) 昇格）。テンソル積の次数乗法性（log 形の加法性）・主イソメトリ
    捻りの次数不変性（「主 Arakelov 因子の次数 0」の計量版）も実対象上で証明。

  正直な限定（消去・弱化禁止）:
  1. **K = ℚ のみ**（Spec ℤ・実素点 1 個・複素素点なし）。一般数体の Arakelov は未達。
  2. 直線束は**生成元表示** q·ℤ（K=ℚ は類数 1 ゆえ忠実だが、「ℚ 内の任意の階数 1
     ℤ-部分加群が主である」ことは未証明。生成元 q の取り替えは amlTwist の
     イソメトリで扱う）。
  3. 次数は**乗法形**（古典的 deg の指数 exp(deg) に相当・値は実 ℚ>0）。実 log が
     未構成のため加法形 deg = Σ n_p log p − log‖s‖（実 ℝ 値）へは未接続
     （B5ProductFormulaQ の正直な限定 5 を継承）。
  4. 有限部の寄与 ∏_p |s/q|_p は実 p 進絶対値の有限台積であり、整切断（s/q = m∈ℤ）
     では一般化指数 [L : ℤs] に等しいはずだが、「指数 = 商加群の濃度」という
     数え上げ命題は未証明（絶対値経由でのみ扱う）。
  5. 非零性は代表 witness 形（x : PreRat・x.num ≠ 0）。商上のゼロ判定選言は排中律を
     要するため対象外（qInv・qMul_inv・b5 の既存の正直申告を継承）。
  6. 正定値性は qLt 不在のため「qLe 0 ‖s‖ かつ ¬ qLe ‖s‖ 0」の対で述べる。
  7. 曲面上の Arakelov 交点理論・アルキメデス Green 関数の実積分は対象外。既存
     M356F 系模型モジュールは置換対象として残置する（§4・消さない）。

  全て Lean 4.30.0 core のみ（mathlib 不使用）・sorry なし・新規 Classical.choice
  なし。全公開定理の #print axioms は [propext, Quot.sound]。
-/
import IUT.B5ProductFormulaQ

namespace IUT

/-! ## M474F-1: 実計量付き直線束 L̄ = (q·ℤ ⊂ ℚ, ‖·‖ = λ·|·|_∞)

    有限部: 生成元 q ∈ ℚˣ（PreRat 代表・num ≠ 0）の定める実 ℚ の ℤ-部分加群 q·ℤ。
    アルキメデス部: 正スケール λ ∈ ℚ>0（PreRat 代表・num > 0）による実計量
    ‖x‖ := λ·|x|_∞（|·|_∞ = arpAbs は M115F の実絶対値）。 -/

/-- **M474F-1a: 実計量付き直線束** — 生成元 q（非零）と計量スケール λ（正）。 -/
structure amlBundle where
  /-- 生成元 q の代表（直線束の有限部 L = q·ℤ ⊂ ℚ）。 -/
  gen : PreRat
  /-- 生成元は非零（witness 形）。 -/
  gen_ne : gen.num ≠ 0
  /-- アルキメデス計量スケール λ の代表（‖x‖ = λ·|x|_∞）。 -/
  met : PreRat
  /-- スケールは正（分子正・分母は den_pos で常に正）。 -/
  met_pos : 0 < met.num

/-- 生成元の実 ℚ 値。 -/
abbrev amlGen (L : amlBundle) : QRat := Quot.mk ratRel L.gen

/-- 計量スケールの実 ℚ 値。 -/
abbrev amlMet (L : amlBundle) : QRat := Quot.mk ratRel L.met

/-- **M474F-1b: 直線束の切断の全体** — 実 ℚ の部分集合としての L = q·ℤ
    （s ∈ L ⟺ ∃ m ∈ ℤ, s = q·m）。 -/
def amlMem (L : amlBundle) (s : QRat) : Prop :=
  ∃ m : Int, s = ratRing.mul (amlGen L) (ratOfInt.map m)

/-- **M474F-1c: アルキメデス計量** ‖s‖ := λ·|s|_∞（実 arpAbs の正スケール）。 -/
def amlNorm (L : amlBundle) (s : QRat) : QRat :=
  ratRing.mul (amlMet L) (arpAbs s)

/-! ## M474F-2: 直線束は実 ℚ の真の ℤ-部分加群（有限部が本物） -/

/-- **M474F-2a: 生成元は切断**（q = q·1 ∈ L）。 -/
theorem aml_gen_mem (L : amlBundle) : amlMem L (amlGen L) :=
  ⟨1, (fsp_rat_mul_one (amlGen L)).symm⟩

/-- **M474F-2b: ℤ 作用で閉じる** — q·m ∈ L（∀ m ∈ ℤ）。 -/
theorem aml_mem_smul (L : amlBundle) (m : Int) :
    amlMem L (ratRing.mul (amlGen L) (ratOfInt.map m)) := ⟨m, rfl⟩

/-- **M474F-2c: 加法で閉じる** — s, t ∈ L ⟹ s + t ∈ L（ℤ-部分加群性の核。
    実環準同型 ratOfInt.map_add と ratRing の左分配律で本物証明）。 -/
theorem aml_mem_add (L : amlBundle) {s t : QRat}
    (hs : amlMem L s) (ht : amlMem L t) : amlMem L (ratRing.add s t) := by
  apply Exists.elim hs
  intro m hm
  apply Exists.elim ht
  intro n hn
  refine ⟨m + n, ?_⟩
  have hadd : ratOfInt.map (m + n)
      = ratRing.add (ratOfInt.map m) (ratOfInt.map n) := ratOfInt.map_add m n
  rw [hm, hn, hadd, ratRing.left_distrib]

/-! ## M474F-3: 計量の実性 — 斉次性・非負性・正定値性 -/

/-- 実アルキメデス絶対値の乗法性（qAbs_mul の ratRing 表示）。 -/
theorem aml_abs_mul (a b : QRat) :
    arpAbs (ratRing.mul a b) = ratRing.mul (arpAbs a) (arpAbs b) :=
  qAbs_mul a b

/-- **M474F-3a: 計量の |·|_∞-斉次性** ‖x·s‖ = |x|_∞·‖s‖（1 次元 ℚ-ベクトル空間の
    本物の計量の公理）。 -/
theorem aml_norm_smul (L : amlBundle) (x s : QRat) :
    amlNorm L (ratRing.mul x s) = ratRing.mul (arpAbs x) (amlNorm L s) := by
  show ratRing.mul (amlMet L) (arpAbs (ratRing.mul x s))
      = ratRing.mul (arpAbs x) (ratRing.mul (amlMet L) (arpAbs s))
  rw [aml_abs_mul x s, ← ratRing.mul_assoc (amlMet L) (arpAbs x) (arpAbs s),
    ratRing.mul_comm (amlMet L) (arpAbs x),
    ratRing.mul_assoc (arpAbs x) (amlMet L) (arpAbs s)]

/-- **M474F-3b: 計量の非負性** 0 ≤ ‖s‖（実順序 qLe）。 -/
theorem aml_norm_nonneg (L : amlBundle) (s : QRat) :
    qLe ratRing.zero (amlNorm L s) := by
  induction s using Quot.ind
  rename_i x
  show (0 : Int) * (L.met.den * x.den) ≤ L.met.num * intAbs x.num * 1
  have h1 : 0 ≤ L.met.num * intAbs x.num :=
    Int.mul_nonneg (Int.le_of_lt L.met_pos) (intAbs_nonneg x.num)
  rw [Int.zero_mul, Int.mul_one]
  exact h1

/-- **M474F-3c: 計量の正定値性** — 非零切断（代表 witness 形）の計量は ¬(‖s‖ ≤ 0)
    （非負性 3b と合わせ狭義正。qLt 不在のための対表示・正直な限定 6）。 -/
theorem aml_norm_pos (L : amlBundle) (x : PreRat) (hx : x.num ≠ 0) :
    ¬ qLe (amlNorm L (Quot.mk ratRel x)) ratRing.zero := by
  intro h
  have h' : L.met.num * intAbs x.num * 1 ≤ 0 * (L.met.den * x.den) := h
  have hpos : 0 < L.met.num * intAbs x.num :=
    Int.mul_pos L.met_pos (avi_intAbs_pos hx)
  rw [Int.mul_one, Int.zero_mul] at h'
  omega

/-! ## M474F-4: 実算術次数（乗法形）

    余次数 codeg×(L̄) := λ·|q|_∞ = ‖q‖（生成元切断の計量）、次数
    deg×(L̄) := 1/codeg×(L̄)。古典的には deg(L̄) = −log‖q‖ であり、deg× は
    その指数形 exp(deg) = 1/‖q‖（実 log 未構成のための乗法形・正直な限定 3）。 -/

/-- 余次数の代表 λ·|q|（PreRat）。 -/
def amlCodegRep (L : amlBundle) : PreRat := prMul L.met (prAbs L.gen)

/-- 余次数 codeg×(L̄) = λ·|q|_∞ ∈ ℚ>0。 -/
def amlCodeg (L : amlBundle) : QRat := Quot.mk ratRel (amlCodegRep L)

/-- **M474F-4a: 余次数の計量表示** codeg×(L̄) = λ·|q|_∞。 -/
theorem aml_codeg_eq (L : amlBundle) :
    amlCodeg L = ratRing.mul (amlMet L) (arpAbs (amlGen L)) := rfl

/-- **M474F-4b: 余次数 = 生成元切断の計量** codeg×(L̄) = ‖q‖（古典公式
    deg(L̄) = −log‖s‖ + log[L:ℤs] の s = q・指数 1 の場合の乗法形）。 -/
theorem aml_codeg_norm_gen (L : amlBundle) :
    amlCodeg L = amlNorm L (amlGen L) := rfl

/-- 余次数の分子は正。 -/
theorem aml_codegRep_num_pos (L : amlBundle) : 0 < (amlCodegRep L).num := by
  show 0 < L.met.num * intAbs L.gen.num
  exact Int.mul_pos L.met_pos (avi_intAbs_pos L.gen_ne)

/-- 余次数は非零（witness 形）。 -/
theorem aml_codegRep_ne (L : amlBundle) : (amlCodegRep L).num ≠ 0 := by
  have h := aml_codegRep_num_pos L
  omega

/-- **M474F-4c: 余次数の正値性** ¬(codeg×(L̄) ≤ 0)。 -/
theorem aml_codeg_pos (L : amlBundle) : ¬ qLe (amlCodeg L) ratRing.zero :=
  aml_norm_pos L L.gen L.gen_ne

/-- 実算術次数（乗法形）deg×(L̄) := 1/(λ·|q|_∞)。 -/
def amlDeg (L : amlBundle) : QRat := qInv (amlCodeg L)

/-- **M474F-4d: 次数×余次数 = 1**（qMul_inv の本物 witness・codeg の分子正から）。 -/
theorem aml_codeg_mul_deg (L : amlBundle) :
    ratRing.mul (amlCodeg L) (amlDeg L) = ratRing.one :=
  qMul_inv (amlCodegRep L) (aml_codegRep_ne L)

/-- 4d の可換形。 -/
theorem aml_deg_mul_codeg (L : amlBundle) :
    ratRing.mul (amlDeg L) (amlCodeg L) = ratRing.one := by
  rw [ratRing.mul_comm (amlDeg L) (amlCodeg L)]
  exact aml_codeg_mul_deg L

/-! ## M474F-5: 次数公式と切断非依存性（実 B5 積公式の消費・本丸）

    任意の非零有理倍率 x（有理切断 s = q·x、x ∈ ℤ なら整切断 s ∈ L）に対し
      ‖s‖ · ∏_{p∈Supp(x)} |x|_p = codeg×(L̄)   （5a）
    したがって deg×(L̄)·(‖s‖·∏_p|s/q|_p) = 1（5c）で、左辺の切断データは s に
    非依存（5b）。これは古典的な「deg(L̄) = Σ_p v_p(s/q)log p − log‖s‖ が切断の
    取り方に依らない」ことの乗法形であり、証明は**実 B5 積公式**
    b5_product_formula（|x|_∞·∏_p|x|_p = 1・実 ℚ・実絶対値）を消費する。 -/

/-- **M474F-5a（核・実 B5 消費）**: ‖q·x‖ · ∏_{p∈Supp(x)} |x|_p = codeg×(L̄)。 -/
theorem aml_norm_prod_section (L : amlBundle) (x : PreRat) (hx : x.num ≠ 0) :
    ratRing.mul (amlNorm L (ratRing.mul (amlGen L) (Quot.mk ratRel x)))
      (fspProd (fun p => pavAbs p x) (b5Support x))
    = amlCodeg L := by
  show ratRing.mul
      (ratRing.mul (amlMet L) (arpAbs (ratRing.mul (amlGen L) (Quot.mk ratRel x))))
      (fspProd (fun p => pavAbs p x) (b5Support x))
    = amlCodeg L
  rw [aml_abs_mul (amlGen L) (Quot.mk ratRel x),
    ← ratRing.mul_assoc (amlMet L) (arpAbs (amlGen L)) (arpAbs (Quot.mk ratRel x)),
    ratRing.mul_assoc (ratRing.mul (amlMet L) (arpAbs (amlGen L)))
      (arpAbs (Quot.mk ratRel x)) (fspProd (fun p => pavAbs p x) (b5Support x)),
    b5_product_formula x hx, fsp_rat_mul_one, aml_codeg_eq L]

/-- **M474F-5b: 切断非依存性** — 次数データ ‖s‖·∏_p|s/q|_p は切断の取り方に
    依らない（Arakelov 次数の well-definedness の実形）。 -/
theorem aml_deg_section_indep (L : amlBundle) (x y : PreRat)
    (hx : x.num ≠ 0) (hy : y.num ≠ 0) :
    ratRing.mul (amlNorm L (ratRing.mul (amlGen L) (Quot.mk ratRel x)))
      (fspProd (fun p => pavAbs p x) (b5Support x))
    = ratRing.mul (amlNorm L (ratRing.mul (amlGen L) (Quot.mk ratRel y)))
        (fspProd (fun p => pavAbs p y) (b5Support y)) := by
  rw [aml_norm_prod_section L x hx, aml_norm_prod_section L y hy]

/-- **M474F-5c: 算術次数公式** deg×(L̄) · (‖q·x‖ · ∏_p|x|_p) = 1
    （deg = Σ_p v_p(s/q)·log p − log‖s‖ の乗法 cleared 形）。 -/
theorem aml_deg_section_formula (L : amlBundle) (x : PreRat) (hx : x.num ≠ 0) :
    ratRing.mul (amlDeg L)
      (ratRing.mul (amlNorm L (ratRing.mul (amlGen L) (Quot.mk ratRel x)))
        (fspProd (fun p => pavAbs p x) (b5Support x)))
    = ratRing.one := by
  rw [aml_norm_prod_section L x hx]
  exact aml_deg_mul_codeg L

/-- **M474F-5d: 整切断版** — s = q·m（m ∈ ℤ 非零・aml_mem_smul により s ∈ L）に
    対する次数公式。5c の x = m/1 の忠実な特殊化。 -/
theorem aml_deg_integral_section (L : amlBundle) (m : Int) (hm : m ≠ 0) :
    ratRing.mul (amlDeg L)
      (ratRing.mul (amlNorm L (ratRing.mul (amlGen L) (ratOfInt.map m)))
        (fspProd (fun p => pavAbs p (intToPreRat m)) (b5Support (intToPreRat m))))
    = ratRing.one :=
  aml_deg_section_formula L (intToPreRat m) hm

/-! ## M474F-6: テンソル積と次数の乗法性（log 形の加法性） -/

/-- **M474F-6a: 計量付き直線束のテンソル積** L̄⊗M̄ = (q_L·q_M, λ_L·λ_M)
    （生成元・計量スケールとも積）。 -/
def amlTensor (L M : amlBundle) : amlBundle where
  gen := prMul L.gen M.gen
  gen_ne := Int.mul_ne_zero L.gen_ne M.gen_ne
  met := prMul L.met M.met
  met_pos := Int.mul_pos L.met_pos M.met_pos

/-- 逆元の一意性（可換モノイド・deg の等式導出用）。 -/
theorem aml_inv_unique {a b c : QRat} (hb : ratRing.mul a b = ratRing.one)
    (hc : ratRing.mul a c = ratRing.one) : b = c := by
  have h1 : ratRing.mul b (ratRing.mul a c) = b := by
    rw [hc, fsp_rat_mul_one]
  rw [← ratRing.mul_assoc b a c, ratRing.mul_comm b a, hb, ratRing.one_mul] at h1
  exact h1.symm

/-- **M474F-6b: 余次数の乗法性** codeg×(L̄⊗M̄) = codeg×(L̄)·codeg×(M̄)
    （実 |·|_∞ の乗法性 qAbs_mul を消費）。 -/
theorem aml_codeg_tensor (L M : amlBundle) :
    amlCodeg (amlTensor L M) = ratRing.mul (amlCodeg L) (amlCodeg M) := by
  rw [aml_codeg_eq (amlTensor L M), aml_codeg_eq L, aml_codeg_eq M]
  show ratRing.mul (ratRing.mul (amlMet L) (amlMet M))
        (arpAbs (ratRing.mul (amlGen L) (amlGen M)))
      = ratRing.mul (ratRing.mul (amlMet L) (arpAbs (amlGen L)))
          (ratRing.mul (amlMet M) (arpAbs (amlGen M)))
  rw [aml_abs_mul (amlGen L) (amlGen M)]
  exact fsp_rat_mul_mul_mul_comm (amlMet L) (amlMet M)
    (arpAbs (amlGen L)) (arpAbs (amlGen M))

/-- **M474F-6c: 次数の乗法性** deg×(L̄⊗M̄) = deg×(L̄)·deg×(M̄)
    （log 形では deg(L̄⊗M̄) = deg(L̄)+deg(M̄)、Arakelov 次数の加法性）。 -/
theorem aml_deg_tensor (L M : amlBundle) :
    amlDeg (amlTensor L M) = ratRing.mul (amlDeg L) (amlDeg M) := by
  apply aml_inv_unique (aml_codeg_mul_deg (amlTensor L M))
  rw [aml_codeg_tensor L M,
    fsp_rat_mul_mul_mul_comm (amlCodeg L) (amlCodeg M) (amlDeg L) (amlDeg M),
    aml_codeg_mul_deg L, aml_codeg_mul_deg M, ratRing.one_mul]

/-! ## M474F-7: 主イソメトリ捻りと次数不変性（「主因子の次数 0」の計量版）

    u ∈ ℚˣ による捻り L̄ ↦ u·L̄ = (u·q, λ/|u|_∞) は乗算 s ↦ u·s を通じて
    イソメトリ（‖u·s‖' = ‖s‖・7b）。その次数は不変（7c/7d）＝主 Arakelov 因子
    div̂(u) の次数 0 の計量付き直線束版。 -/

/-- 捻りの計量スケール λ' = λ·den(u)/|num(u)|（= λ/|u|_∞ の代表・choice なし）。 -/
def amlTwistMet (lam u : PreRat) (hu : u.num ≠ 0) : PreRat :=
  ⟨lam.num * u.den, lam.den * intAbs u.num,
    Int.mul_pos lam.den_pos (avi_intAbs_pos hu)⟩

/-- **M474F-7a: 捻り** u·L̄ = (u·q, λ/|u|_∞)。 -/
def amlTwist (L : amlBundle) (u : PreRat) (hu : u.num ≠ 0) : amlBundle where
  gen := prMul u L.gen
  gen_ne := Int.mul_ne_zero hu L.gen_ne
  met := amlTwistMet L.met u hu
  met_pos := Int.mul_pos L.met_pos u.den_pos

/-- 捻り計量の補償等式 λ'·|u|_∞ = λ（実 ℚ の Quot.sound 交差積で本物証明）。 -/
theorem aml_twist_met_compat (lam u : PreRat) (hu : u.num ≠ 0) :
    ratRing.mul (Quot.mk ratRel (amlTwistMet lam u hu))
      (arpAbs (Quot.mk ratRel u)) = Quot.mk ratRel lam := by
  apply Quot.sound
  show (lam.num * u.den) * intAbs u.num * lam.den
      = lam.num * ((lam.den * intAbs u.num) * u.den)
  rw [Int.mul_assoc (lam.num * u.den) (intAbs u.num) lam.den,
    Int.mul_assoc lam.num u.den (intAbs u.num * lam.den),
    Int.mul_comm (lam.den * intAbs u.num) u.den,
    Int.mul_comm lam.den (intAbs u.num)]

/-- **M474F-7b: 捻りはイソメトリ** ‖u·s‖_{u·L̄} = ‖s‖_{L̄}（∀ s ∈ ℚ）。 -/
theorem aml_twist_isometry (L : amlBundle) (u : PreRat) (hu : u.num ≠ 0)
    (s : QRat) :
    amlNorm (amlTwist L u hu) (ratRing.mul (Quot.mk ratRel u) s)
      = amlNorm L s := by
  show ratRing.mul (Quot.mk ratRel (amlTwistMet L.met u hu))
        (arpAbs (ratRing.mul (Quot.mk ratRel u) s))
      = ratRing.mul (amlMet L) (arpAbs s)
  rw [aml_abs_mul (Quot.mk ratRel u) s,
    ← ratRing.mul_assoc (Quot.mk ratRel (amlTwistMet L.met u hu))
      (arpAbs (Quot.mk ratRel u)) (arpAbs s),
    aml_twist_met_compat L.met u hu]

/-- **M474F-7b': 捻りは加群の対応も保つ** — s ∈ L ⟹ u·s ∈ u·L。 -/
theorem aml_twist_mem (L : amlBundle) (u : PreRat) (hu : u.num ≠ 0) {s : QRat}
    (hs : amlMem L s) :
    amlMem (amlTwist L u hu) (ratRing.mul (Quot.mk ratRel u) s) := by
  apply Exists.elim hs
  intro m hm
  refine ⟨m, ?_⟩
  rw [hm, ← ratRing.mul_assoc (Quot.mk ratRel u) (amlGen L) (ratOfInt.map m)]
  rfl

/-- **M474F-7c: 捻りの余次数不変性** codeg×(u·L̄) = codeg×(L̄)。 -/
theorem aml_codeg_twist (L : amlBundle) (u : PreRat) (hu : u.num ≠ 0) :
    amlCodeg (amlTwist L u hu) = amlCodeg L := by
  rw [aml_codeg_eq (amlTwist L u hu)]
  show ratRing.mul (Quot.mk ratRel (amlTwistMet L.met u hu))
        (arpAbs (ratRing.mul (Quot.mk ratRel u) (amlGen L)))
      = amlCodeg L
  rw [aml_abs_mul (Quot.mk ratRel u) (amlGen L),
    ← ratRing.mul_assoc (Quot.mk ratRel (amlTwistMet L.met u hu))
      (arpAbs (Quot.mk ratRel u)) (arpAbs (amlGen L)),
    aml_twist_met_compat L.met u hu, aml_codeg_eq L]

/-- **M474F-7d: 捻りの次数不変性** deg×(u·L̄) = deg×(L̄)（主 Arakelov 因子の
    次数 0 の計量付き直線束版・実対象上）。 -/
theorem aml_deg_twist (L : amlBundle) (u : PreRat) (hu : u.num ≠ 0) :
    amlDeg (amlTwist L u hu) = amlDeg L := by
  apply aml_inv_unique (aml_codeg_mul_deg (amlTwist L u hu))
  rw [aml_codeg_twist L u hu]
  exact aml_codeg_mul_deg L

/-! ## M474F-8: 自明束と非空虚性の具体例 -/

/-- **M474F-8a: 自明束** O̅ = (ℤ ⊂ ℚ, |·|_∞)。 -/
def amlTrivial : amlBundle where
  gen := prOne
  gen_ne := by show (1 : Int) ≠ 0; omega
  met := prOne
  met_pos := by show (0 : Int) < 1; omega

/-- **M474F-8b: 自明束の余次数 = 1**。 -/
theorem aml_codeg_trivial : amlCodeg amlTrivial = ratRing.one := by
  apply Quot.sound
  show (1 * intAbs 1) * 1 = 1 * (1 * 1)
  have h1 : intAbs (1 : Int) = 1 := intAbs_of_nonneg (by omega)
  rw [h1]
  omega

/-- **M474F-8c: 自明束の次数 = 1**（log 形では deg(O̅) = 0）。 -/
theorem aml_deg_trivial : amlDeg amlTrivial = ratRing.one := by
  apply aml_inv_unique (aml_codeg_mul_deg amlTrivial)
  rw [aml_codeg_trivial, ratRing.one_mul]

/-- **M474F-8d: 非空虚性の具体例** L̄ = (2·ℤ, (3/2)·|·|_∞)。 -/
def amlExample : amlBundle where
  gen := ⟨2, 1, by omega⟩
  gen_ne := by show (2 : Int) ≠ 0; omega
  met := ⟨3, 2, by omega⟩
  met_pos := by show (0 : Int) < 3; omega

/-- **M474F-8e: 具体例の余次数 = 3**（codeg = (3/2)·|2|_∞ = 3・自明束と異なる値
    ＝ deg は定数関数でない）。 -/
theorem aml_example_codeg : amlCodeg amlExample = ratOfInt.map (3 : Int) := by
  apply Quot.sound
  show (3 * intAbs 2) * 1 = 3 * (2 * 1)
  have h2 : intAbs (2 : Int) = 2 := intAbs_of_nonneg (by omega)
  rw [h2]
  omega

/-- **M474F-8f: 具体例の次数** deg×·3 = 1（deg× = 1/3・log 形では −log 3 < 0）。 -/
theorem aml_example_deg :
    ratRing.mul (amlDeg amlExample) (ratOfInt.map (3 : Int)) = ratRing.one := by
  rw [← aml_example_codeg]
  exact aml_deg_mul_codeg amlExample

end IUT

-- 公理検査（全て [propext, Quot.sound] であること）
#print axioms IUT.aml_gen_mem
#print axioms IUT.aml_mem_add
#print axioms IUT.aml_norm_smul
#print axioms IUT.aml_norm_nonneg
#print axioms IUT.aml_norm_pos
#print axioms IUT.aml_codeg_mul_deg
#print axioms IUT.aml_norm_prod_section
#print axioms IUT.aml_deg_section_indep
#print axioms IUT.aml_deg_section_formula
#print axioms IUT.aml_deg_integral_section
#print axioms IUT.aml_codeg_tensor
#print axioms IUT.aml_deg_tensor
#print axioms IUT.aml_twist_isometry
#print axioms IUT.aml_codeg_twist
#print axioms IUT.aml_deg_twist
#print axioms IUT.aml_deg_trivial
#print axioms IUT.aml_example_deg
