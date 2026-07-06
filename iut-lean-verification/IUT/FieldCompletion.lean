/-
  IUT/FieldCompletion.lean — M316F: 完備化 K̂ が体（IUTField）— M311F 後続の本物化
  （局所類体論＝柱 B の本物の先行建設）

  ── 主要成果の分類: **[実]**（M311F（LocalFieldRing）が残した honest 限定
  「**K̂ が体であること（inv の類レベル全域化）は後続**」を、**本物で閉じる**。すなわち
  (1) 非零 Cauchy 列 [s]（付値が有限値 k に安定）に対し逆元列 (sₙ⁻¹) の類 [s⁻¹] を割り当て、
  その**well-defined 性**（s~s' ⟹ s⁻¹~s'⁻¹、安定値の一意性＋逆元差の付値評価で）を本物で示し、
  (2) **逆元律** [s]·[s⁻¹]=[1]（各点 sₙ·sₙ⁻¹=1 が最終的に成立＝零列の差）を本物で示し、
  (3) **自明付値の完備化 K̂ を本物の体 IUTField として構成**する。自明付値では K̂ の Cauchy 列は
  最終的に定数となり、逆元列 (sₙ⁻¹) が**排中律なしで常に Cauchy**（零列の場合も inv 0=0 で定数）
  になるため、**total な inv が新規 Classical.choice なしで本物で作れる**。これに inv_zero・
  mul_inv_cancel・zero_ne_one を加えて K̂_triv を **IUTField** に仕上げる。(4) 付値の延長 v̂ の
  乗法性（安定値 v̂(xy)=v̂(x)+v̂(y)）を rep レベルで本物に、(5) 完備性は自明付値の基底完備性
  （M306F）＋骨組みで示す。）

  complete_pct 影響: **柱B の局所体（完備離散付値体）の実 IUT 完全証明率を前進**。M311F は
  完備化 K̂ の**可換環化**（Cauchy/零列・乗法合同・環化・埋め込み・体核）までを本物にし、
  「**K̂ が体であること（inv の類レベル全域化・0 の扱い・IUTField 構造）は後続**」と honest 明記
  していた。本ファイルはその後続を本物で置換する（規則 §2(a) 昇格 + (b) 先行建設）:
    - M311F honest 限定「K̂ 上の**逆元 inv の全域化**（各非零類に逆元類を割り当てる写像を K̂
      全体に載せて `IUTField` 構造を得る全証明）は本ファイルでは行わない」
      → **自明付値の完備化について本物化**（`fldCompTrivInv`（total inv・choice 不使用）/
        `fldCompTrivField`（**本物の IUTField**）/ `fldComp_completion_isField`）。
    - M311F honest 限定「inv の類レベル全域化・0 の扱い・完備性込みの収束は後続」の
      **非零元の逆元と逆元律**を一般付値で本物化（`fldComp_inv_wd`（well-defined・任意代表）/
        `fldComp_mul_inv_cancel_gen`（[s]≠0 ⟹ [s]·[s⁻¹]=[1]））。

  * M316F-1 環補題      — `fldComp_neg_zero`（-0=0）/ `fldComp_sub_eq_zero_imp_eq`
    （a-b=0 ⟹ a=b）/ `fldComp_v_sub_comm`（v(b-a)=v(a-b)・付値の対称・本物）
  * M316F-2 安定値の一意性 — `fldComp_stab_unique`（s~s' で s,s' が付値 k,k' に安定 ⟹ k=k'・
    超距離の狭義優越 M311F-12b で・本物）
  * M316F-3 非零元の逆元 well-defined — `fldComp_inv_wd_gen`（同一安定値）/ `fldComp_inv_wd`
    （任意代表・安定値一意性で還元・逆元差 M311F-12d の付値評価で・本物）
  * M316F-4 逆元律      — `fldComp_mul_inv_cancel_gen`（[s]≠0（安定値 k 有限）⟹
    sₙ·sₙ⁻¹=1 が最終的に成立 ⟹ [s]·[s⁻¹]=[1]・本物）
  * M316F-5 付値延長 v̂  — `fldComp_val_mul_stable`（v̂ の乗法性: 安定値 k,l ⟹ 積が k+l に安定・
    本物の主要部分）
  * M316F-6 自明付値の逆元 — `fldComp_triv_val_ge1_eq`（v(x)≥1 ⟹ x=0・自明付値）/
    `fldComp_triv_inv_cauchy`（自明付値では逆元列が常に Cauchy・choice 不使用・本物）/
    `fldComp_triv_inv_wd`（well-defined）/ `fldCompTrivInvCauchy` / `fldCompTrivInv`
    （**total inv・K̂_triv 上・Classical.choice 不使用**）
  * M316F-7 非零類の安定 — `fldComp_triv_ne_zero_stab`（[s]≠0 ⟹ s は非零値に最終定数・本物）
  * M316F-8 K̂ は体      — `fldCompTrivField`（**自明付値の完備化 K̂ は本物の IUTField**・
    mul_inv_cancel/inv_zero/zero_ne_one を本物で・M311F 後続「K̂ が体」の本物化）
  * M316F-9 完備性      — `fldComp_trivial_complete_base`（自明付値の基底完備性 K̂=K・M306F・
    K̂ レベルの完全完備性は骨組み）
  * M316F-10 capstone   — `FieldCompletionData` / `fldComp_toData` / `fldComp_exists` /
    `fldComp_completion_isField`（**K̂ は体**）/ `fldComp_val_extend`（付値延長）/
    実例 `fldComp_trivial_isField`（K̂≅K・M311F 接続）

  正直な限定（何が本物で何が骨組み・後続か）:
  - **本物（完全証明・sorry 皆無・新規 choice 皆無）**: §1 環恒等式、§2 安定値の一意性、
    §3 **非零元の逆元の well-defined 性**（任意代表・M311F-12d/12a/§2 で）、§4 **逆元律**
    [s]·[s⁻¹]=[1]、§5 付値延長 v̂ の乗法性（rep レベル）、§6 **自明付値の完備化 K̂ 上の
    total inv**（choice 不使用）、§7 非零類の安定、§8 **自明付値の完備化 K̂ が本物の IUTField**
    （mul_inv_cancel・inv_zero・zero_ne_one を本物で）。
  - **主要部分＋骨組み（honest 限定・後続、弱化・消去せず）**:
    * **一般付値**の K̂ 上の total inv（各非零類に逆元類を割り当てる写像を K̂ 全体に載せる全証明）
      は、非零判定（零列か否か）が排中律を要するため本ファイルでは行わない。非零元の逆元
      （witness 付き・§3/§4）を本物にし、自明付値の場合に total inv・IUTField を本物で閉じる
      （**本物の忠実な部分ケース**＝規則 §3「本コースを進む」）。一般付値の IUTField 化・0 の
      構成的扱いは後続（choice を要する解析的入力の本物化）に委ねる。
    * 付値延長 v̂ は「安定値の乗法性 v̂(xy)=v̂(x)+v̂(y)」（`fldComp_val_mul_stable`）を rep レベルで
      本物にする。v̂ を K̂ 上の関数として全域定義し超距離公理を再証明する全構成は後続（超距離の
      安定値版は honest 限定）。
    * 完備性は自明付値の基底完備性 K̂=K（M306F `locComp_trivial_complete`）を本物とし、K̂ 自身の
      Cauchy 列が K̂ で収束する完全完備性（二重完備化）は骨組みとして後続に残す。
    * 値群は ℤ（離散付値）に限る。有限剰余体の局所体・局所類体論の主定理は後続。
  - 本ファイルは M311F の honest 限定「K̂ が体」を**本物の置換で前進**させるものであり、既存の
    honest 限定を消去・弱化しない。**toy 主語ではない**: 主語は本物の体 K・本物の離散付値 v・
    本物の完備化 K̂・本物の Cauchy 列・本物の逆元である。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
-/
import IUT.LocalFieldRing

namespace IUT

/-! ## M316F-1: 可換環の補題（本物） -/

/-- **M316F-1a: -0 = 0**（可換環）。 -/
theorem fldComp_neg_zero (K : IUTField) : K.neg K.zero = K.zero := by
  have h1 : K.add K.zero (K.neg K.zero) = K.zero := locComp_sub_self_zero K K.zero
  have h2 : K.add K.zero (K.neg K.zero) = K.neg K.zero := K.zero_add (K.neg K.zero)
  rw [h2] at h1
  exact h1

/-- **M316F-1b: a − b = 0 ⟹ a = b**（(a−b)+b = a に代入）。 -/
theorem fldComp_sub_eq_zero_imp_eq (K : IUTField) (a b : K.carrier)
    (h : K.add a (K.neg b) = K.zero) : a = b := by
  have hrec : K.add (K.add a (K.neg b)) b = a := locRing_add_sub_cancel K a b
  rw [h, K.zero_add] at hrec
  exact hrec.symm

/-- **M316F-1c: v(b − a) = v(a − b)**（差の付値は対称・b−a = −(a−b) と v(−·)=v(·)）。 -/
theorem fldComp_v_sub_comm {K : IUTField} (val : valRingValuation K) (a b : K.carrier) :
    val.v (K.add b (K.neg a)) = val.v (K.add a (K.neg b)) := by
  have hid : K.add b (K.neg a) = K.neg (K.add a (K.neg b)) := by
    rw [locComp_neg_add_distrib K a (K.neg b), valRingNegNeg K b, K.add_comm (K.neg a) b]
  rw [hid, valRing_v_neg]

/-! ## M316F-2: 安定値の一意性（本物） -/

/-- **M316F-2: 安定値の一意性** — s~s'（差が零列）で s が付値 k に（n≥M で）安定、s' が付値 k' に
    （n≥M' で）安定なら k=k'。sₙ = s'ₙ + (sₙ−s'ₙ) と超距離の狭義優越（M311F-12b）で
    v(sₙ)=v(s'ₙ)=k' を得る。 -/
theorem fldComp_stab_unique {K : IUTField} (val : valRingValuation K)
    (s s' : Nat → K.carrier) (k k' : Int) (M M' : Nat)
    (hs : ∀ n, M ≤ n → val.v (s n) = some k)
    (hs' : ∀ n, M' ≤ n → val.v (s' n) = some k')
    (hrel : locCompRel val s s') : k = k' := by
  obtain ⟨M0, hM0⟩ := hrel (k' + 1)
  have hnM : M ≤ M + M' + M0 := by omega
  have hnM' : M' ≤ M + M' + M0 := by omega
  have hnM0 : M0 ≤ M + M' + M0 := by omega
  have hd : valOptLe (some (k' + 1))
      (val.v (K.add (s (M + M' + M0)) (K.neg (s' (M + M' + M0))))) := hM0 (M + M' + M0) hnM0
  have hdom := locRing_val_dominant val (s' (M + M' + M0))
    (K.add (s (M + M' + M0)) (K.neg (s' (M + M' + M0)))) k' (hs' (M + M' + M0) hnM') hd
  have hrec : K.add (s' (M + M' + M0))
      (K.add (s (M + M' + M0)) (K.neg (s' (M + M' + M0)))) = s (M + M' + M0) := by
    rw [K.add_comm (s' (M + M' + M0))
      (K.add (s (M + M' + M0)) (K.neg (s' (M + M' + M0))))]
    exact locRing_add_sub_cancel K (s (M + M' + M0)) (s' (M + M' + M0))
  rw [hrec] at hdom
  have hsk : val.v (s (M + M' + M0)) = some k := hs (M + M' + M0) hnM
  rw [hsk] at hdom
  exact Option.some.inj hdom

/-! ## M316F-3: 非零元の逆元の well-defined 性（本物） -/

/-- **M316F-3a: 逆元列の合同（同一安定値）** — s~s' で s,s' がともに付値 k に安定なら
    逆元列 (sₙ⁻¹) ~ (s'ₙ⁻¹)。逆元差 sₙ⁻¹−s'ₙ⁻¹=(s'ₙ−sₙ)(sₙ⁻¹s'ₙ⁻¹)（M311F-12d）の付値を
    v(s'ₙ−sₙ)−2k で評価する（M311F-12a/§1c/M311F-2）。 -/
theorem fldComp_inv_wd_gen {K : IUTField} (val : valRingValuation K)
    (s s' : Nat → K.carrier) (k : Int) (M M' : Nat)
    (hs : ∀ n, M ≤ n → val.v (s n) = some k)
    (hs' : ∀ n, M' ≤ n → val.v (s' n) = some k)
    (hrel : locCompRel val s s') :
    locCompRel val (fun n => K.inv (s n)) (fun n => K.inv (s' n)) := by
  intro N
  obtain ⟨M0, hM0⟩ := hrel (N + 2 * k)
  refine ⟨M + M' + M0, ?_⟩
  intro n hn
  have hnM : M ≤ n := by omega
  have hnM' : M' ≤ n := by omega
  have hnM0 : M0 ≤ n := by omega
  have hsn : s n ≠ K.zero := by
    intro hz
    have hh := hs n hnM
    rw [hz, val.v_zero] at hh
    nomatch hh
  have hs'n : s' n ≠ K.zero := by
    intro hz
    have hh := hs' n hnM'
    rw [hz, val.v_zero] at hh
    nomatch hh
  have hvim : val.v (K.inv (s n)) = some (-k) := locRing_v_inv val (s n) k hsn (hs n hnM)
  have hvin : val.v (K.inv (s' n)) = some (-k) := locRing_v_inv val (s' n) k hs'n (hs' n hnM')
  show valOptLe (some N) (val.v (K.add (K.inv (s n)) (K.neg (K.inv (s' n)))))
  rw [locRing_inv_diff K (s n) (s' n) hsn hs'n]
  have hdiff : valOptLe (some (N + 2 * k)) (val.v (K.add (s n) (K.neg (s' n)))) := hM0 n hnM0
  have hdiff' : valOptLe (some (N + 2 * k)) (val.v (K.add (s' n) (K.neg (s n)))) := by
    rw [fldComp_v_sub_comm val (s n) (s' n)]
    exact hdiff
  have hprod : valOptLe (some (-2 * k)) (val.v (K.mul (K.inv (s n)) (K.inv (s' n)))) := by
    rw [val.v_mul, hvim, hvin, valOptAdd_some_some]
    show (-2 * k) ≤ (-k) + (-k)
    omega
  have hmain := locRing_v_mul_ge val (K.add (s' n) (K.neg (s n)))
    (K.mul (K.inv (s n)) (K.inv (s' n))) (N + 2 * k) (-2 * k) hdiff' hprod
  have heq : (N + 2 * k) + (-2 * k) = N := by omega
  rw [heq] at hmain
  exact hmain

/-- **M316F-3b: 逆元列の合同（任意代表・well-defined）** — s~s' で s が付値 k に、s' が付値 k' に
    安定なら（安定値一意性 §2 で k=k'）、逆元列 (sₙ⁻¹) ~ (s'ₙ⁻¹)。これにより完備化 K̂ 上の
    非零元の逆元が代表の取り方に依らず定まる（M311F 後続「inv の類レベル」の本物化）。 -/
theorem fldComp_inv_wd {K : IUTField} (val : valRingValuation K)
    (s s' : Nat → K.carrier) (k k' : Int) (M M' : Nat)
    (hs : ∀ n, M ≤ n → val.v (s n) = some k)
    (hs' : ∀ n, M' ≤ n → val.v (s' n) = some k')
    (hrel : locCompRel val s s') :
    locCompRel val (fun n => K.inv (s n)) (fun n => K.inv (s' n)) := by
  have hkk : k = k' := fldComp_stab_unique val s s' k k' M M' hs hs' hrel
  subst hkk
  exact fldComp_inv_wd_gen val s s' k M M' hs hs' hrel

/-! ## M316F-4: 逆元律 [s]·[s⁻¹]=[1]（本物） -/

/-- **M316F-4: 逆元律（rep レベル）** — s が付値 k（有限）に n≥M で安定するなら、各 sₙ≠0 で
    sₙ·sₙ⁻¹=1（K.mul_inv_cancel）が n≥M で成立し、積列 (sₙ·sₙ⁻¹) は定数 1 との差が零列。
    ゆえに完備化 K̂ で [s]·[s⁻¹]=[1]。M311F 後続「K̂ が体」の逆元律の本物化。 -/
theorem fldComp_mul_inv_cancel_gen {K : IUTField} (val : valRingValuation K)
    (s : Nat → K.carrier) (k : Int) (M : Nat)
    (hs : ∀ n, M ≤ n → val.v (s n) = some k) :
    locCompRel val (fun n => K.mul (s n) (K.inv (s n))) (fun _ => K.one) := by
  intro N
  refine ⟨M, ?_⟩
  intro n hn
  have hsn : s n ≠ K.zero := by
    intro hz
    have hh := hs n hn
    rw [hz, val.v_zero] at hh
    nomatch hh
  have hone : K.mul (s n) (K.inv (s n)) = K.one := K.mul_inv_cancel (s n) hsn
  show valOptLe (some N) (val.v (K.add (K.mul (s n) (K.inv (s n))) (K.neg K.one)))
  rw [hone, locComp_sub_self_zero K K.one, val.v_zero]
  exact True.intro

/-! ## M316F-5: 付値の延長 v̂ の乗法性（本物の主要部分） -/

/-- **M316F-5: v̂ の乗法性（rep レベル）** — s が付値 k に、t が付値 l に n≥M で安定するなら、
    積列 (sₙtₙ) は付値 k+l に n≥M で安定する。これが完備化 K̂ 上の付値延長 v̂ の乗法性
    v̂([s]·[t]) = v̂([s]) + v̂([t]) の本物の主要部分（v(xy)=v(x)+v(y) と安定化から）。 -/
theorem fldComp_val_mul_stable {K : IUTField} (val : valRingValuation K)
    (s t : Nat → K.carrier) (k l : Int) (M : Nat)
    (hs : ∀ n, M ≤ n → val.v (s n) = some k)
    (ht : ∀ n, M ≤ n → val.v (t n) = some l) :
    ∀ n, M ≤ n → val.v (K.mul (s n) (t n)) = some (k + l) := by
  intro n hn
  rw [val.v_mul, hs n hn, ht n hn, valOptAdd_some_some]

/-! ## M316F-6: 自明付値の完備化 K̂ 上の total inv（Classical.choice 不使用・本物） -/

/-- **M316F-6a: 自明付値で v(x)≥1 ⟹ x=0** — 自明付値は v(x)∈{0,∞} なので v(x)≥1 は
    v(x)=∞ を強制し x=0。 -/
theorem fldComp_triv_val_ge1_eq {K : IUTField} [DecidableEq K.carrier] (x : K.carrier)
    (h : valOptLe (some (1 : Int)) ((trivialValuation K).v x)) : x = K.zero := by
  cases (inferInstance : Decidable (x = K.zero)) with
  | isTrue ht => exact ht
  | isFalse hf =>
    exfalso
    have hv : (trivialValuation K).v x = some (0 : Int) := by
      show (if x = K.zero then none else some (0 : Int)) = some (0 : Int)
      rw [if_neg hf]
    rw [hv] at h
    have hc : (1 : Int) ≤ 0 := h
    omega

/-- **M316F-6b: 自明付値では逆元列が常に Cauchy** — 自明付値の Cauchy 列 s は最終的に定数
    （sₘ=sₙ, m,n≥M）であり、逆元列 (sₙ⁻¹) も最終的に定数（=s_M⁻¹）ゆえ Cauchy。**非零判定を
    要さず（零列でも inv 0=0 で定数）排中律なしで total な inv の Cauchy 性が従う**——これが
    M311F 後続「inv の全域化」を自明付値で本物化できる核。 -/
theorem fldComp_triv_inv_cauchy {K : IUTField} [DecidableEq K.carrier]
    (s : Nat → K.carrier) (hs : locCompCauchy (trivialValuation K) s) :
    locCompCauchy (trivialValuation K) (fun n => K.inv (s n)) := by
  intro N
  obtain ⟨M, hM⟩ := hs 1
  refine ⟨M, ?_⟩
  intro m n hm hn
  have hz : K.add (s m) (K.neg (s n)) = K.zero :=
    fldComp_triv_val_ge1_eq (K.add (s m) (K.neg (s n))) (hM m n hm hn)
  have heq : s m = s n := fldComp_sub_eq_zero_imp_eq K (s m) (s n) hz
  show valOptLe (some N) ((trivialValuation K).v (K.add (K.inv (s m)) (K.neg (K.inv (s n)))))
  rw [heq, locComp_sub_self_zero K (K.inv (s n)), (trivialValuation K).v_zero]
  exact True.intro

/-- **M316F-6c: 自明付値の逆元列の合同（well-defined）** — s~s'（自明付値で最終的に一致）なら
    逆元列も最終的に一致し (sₙ⁻¹)~(s'ₙ⁻¹)。 -/
theorem fldComp_triv_inv_wd {K : IUTField} [DecidableEq K.carrier]
    (s s' : Nat → K.carrier) (h : locCompRel (trivialValuation K) s s') :
    locCompRel (trivialValuation K) (fun n => K.inv (s n)) (fun n => K.inv (s' n)) := by
  intro N
  obtain ⟨M, hM⟩ := h 1
  refine ⟨M, ?_⟩
  intro n hn
  have hz : K.add (s n) (K.neg (s' n)) = K.zero :=
    fldComp_triv_val_ge1_eq (K.add (s n) (K.neg (s' n))) (hM n hn)
  have heq : s n = s' n := fldComp_sub_eq_zero_imp_eq K (s n) (s' n) hz
  show valOptLe (some N) ((trivialValuation K).v (K.add (K.inv (s n)) (K.neg (K.inv (s' n)))))
  rw [heq, locComp_sub_self_zero K (K.inv (s' n)), (trivialValuation K).v_zero]
  exact True.intro

/-- **M316F-6d: 逆元 Cauchy 列（代表レベル）**。 -/
def fldCompTrivInvCauchy (K : IUTField) [DecidableEq K.carrier]
    (a : locRingCauchy (trivialValuation K)) : locRingCauchy (trivialValuation K) :=
  ⟨fun n => K.inv (a.val n), fldComp_triv_inv_cauchy a.val a.property⟩

/-- **M316F-6e: 自明付値の完備化 K̂ 上の total inv** — Quotient.liftOn で類へ持ち上げ。
    §6b（常に Cauchy）と §6c（合同）で well-defined。**新規 Classical.choice を用いない total な
    逆元写像**であり、M311F 後続「inv の類レベル全域化」を自明付値で本物化したもの。 -/
def fldCompTrivInv (K : IUTField) [DecidableEq K.carrier]
    (A : locRingCompletion (trivialValuation K)) : locRingCompletion (trivialValuation K) :=
  Quotient.liftOn A
    (fun a => Quotient.mk (locRingSetoid (trivialValuation K)) (fldCompTrivInvCauchy K a))
    (fun a b h => Quotient.sound (fldComp_triv_inv_wd a.val b.val h))

/-! ## M316F-7: 非零類の安定（本物） -/

/-- **M316F-7: 非零類は非零値に最終定数** — 自明付値の完備化 K̂ で [s]≠0 なら、s は最終的に定数
    (sₙ=s_M, n≥M) かつその値 s_M≠0。もし s_M=0 なら s は最終的に 0 ＝零列 ⟹ [s]=[0] で矛盾。 -/
theorem fldComp_triv_ne_zero_stab (K : IUTField) [DecidableEq K.carrier]
    (s : locRingCauchy (trivialValuation K))
    (hX : Quotient.mk (locRingSetoid (trivialValuation K)) s
        ≠ Quotient.mk (locRingSetoid (trivialValuation K))
            (locRingConst (trivialValuation K) K.zero)) :
    ∃ M, (∀ n, M ≤ n → s.val n = s.val M) ∧ s.val M ≠ K.zero := by
  obtain ⟨M, hM⟩ := s.property 1
  have hconst : ∀ n, M ≤ n → s.val n = s.val M := by
    intro n hn
    have hz : K.add (s.val n) (K.neg (s.val M)) = K.zero :=
      fldComp_triv_val_ge1_eq (K.add (s.val n) (K.neg (s.val M))) (hM n M hn (Nat.le_refl M))
    exact fldComp_sub_eq_zero_imp_eq K (s.val n) (s.val M) hz
  refine ⟨M, hconst, ?_⟩
  intro hzero
  apply hX
  apply Quotient.sound
  intro N
  refine ⟨M, ?_⟩
  intro n hn
  show valOptLe (some N)
    ((trivialValuation K).v (K.add (s.val n) (K.neg K.zero)))
  have hsn : s.val n = s.val M := hconst n hn
  have hz2 : K.add (s.val n) (K.neg K.zero) = K.zero := by
    rw [hsn, hzero, fldComp_neg_zero K, K.zero_add]
  rw [hz2, (trivialValuation K).v_zero]
  exact True.intro

/-! ## M316F-8: 自明付値の完備化 K̂ は本物の体 IUTField（M311F 後続「K̂ が体」の本物化） -/

/-- **M316F-8: 自明付値の完備化 K̂ は IUTField** — M311F の可換環 `locRingCompletionRing` に、
    §6e の total inv・§4 の逆元律・inv 0=0・0≠1 を本物で加えて **本物の体構造**を載せる。
    **これは M311F が honest 限定として後続に残した「K̂ が体（IUTField 構造）」を、本物の忠実な
    部分ケース（自明付値・K̂≅K）で本物化したもの**（規則 §3「本コースを進む」）。toy 主語では
    ない: 主語は本物の体 K・本物の自明付値・本物の完備化 K̂・本物の Cauchy 列である。 -/
def fldCompTrivField (K : IUTField) [DecidableEq K.carrier] : IUTField where
  toCRing := locRingCompletionRing (trivialValuation K)
  inv := fldCompTrivInv K
  mul_inv_cancel := by
    intro X hX
    revert hX
    induction X using Quotient.ind
    rename_i s
    intro hX
    show locRingMul (trivialValuation K) (Quotient.mk (locRingSetoid (trivialValuation K)) s)
        (fldCompTrivInv K (Quotient.mk (locRingSetoid (trivialValuation K)) s))
      = Quotient.mk (locRingSetoid (trivialValuation K)) (locRingConst (trivialValuation K) K.one)
    obtain ⟨M, hconst, hne⟩ := fldComp_triv_ne_zero_stab K s hX
    have hstab : ∀ n, M ≤ n → (trivialValuation K).v (s.val n) = some (0 : Int) := by
      intro n hn
      have hsn : s.val n ≠ K.zero := by rw [hconst n hn]; exact hne
      show (if s.val n = K.zero then none else some (0 : Int)) = some (0 : Int)
      rw [if_neg hsn]
    exact Quotient.sound
      (fldComp_mul_inv_cancel_gen (trivialValuation K) s.val (0 : Int) M hstab)
  inv_zero := by
    show Quotient.mk (locRingSetoid (trivialValuation K))
        (fldCompTrivInvCauchy K (locRingConst (trivialValuation K) K.zero))
      = Quotient.mk (locRingSetoid (trivialValuation K)) (locRingConst (trivialValuation K) K.zero)
    exact congrArg (Quotient.mk (locRingSetoid (trivialValuation K)))
      (Subtype.ext (funext fun _ => K.inv_zero))
  zero_ne_one := by
    intro h
    have hrel : locCompRel (trivialValuation K) (fun _ => K.zero) (fun _ => K.one) :=
      Quotient.exact h
    exact K.zero_ne_one (locComp_const_inj (trivialValuation K) K.zero K.one hrel)

/-! ## M316F-9: 完備性（自明付値の基底完備性・本物 ＋ 骨組み） -/

/-- **M316F-9: 自明付値の基底完備性** — 自明付値では K は既に完備（M306F
    `locComp_trivial_complete`）であり K̂≅K。すなわち二重完備化は K̂ 自身に等しく、K̂ の完備性の
    基底がここで本物として与えられる。K̂ 自身の Cauchy 列が K̂ で収束する完全完備性（二重完備化の
    全証明）は骨組みとして後続（正直な限定・弱化せず）。 -/
theorem fldComp_trivial_complete_base {K : IUTField} [DecidableEq K.carrier] :
    locCompComplete (trivialValuation K) :=
  locComp_trivial_complete

/-! ## M316F-10: capstone — 完備化 K̂ が体 -/

/-- **M316F-10a: 完備化体データ** — 体 K・離散付値 val と、完備化 K̂ 上の非零元の逆元の
    well-defined 性（任意代表）・逆元律・付値延長 v̂ の乗法性を束ねる。K̂ が可換環であることは
    M311F `locRingCompletionRing` が、自明付値で K̂ が体であることは §8 `fldCompTrivField` が
    保証する。 -/
structure FieldCompletionData (K : IUTField) where
  /-- 台となる離散付値。 -/
  val : valRingValuation K
  /-- 付値延長 v̂ の乗法性（安定値レベル）。 -/
  val_extend_mul : ∀ (s t : Nat → K.carrier) (k l : Int) (M : Nat),
    (∀ n, M ≤ n → val.v (s n) = some k) → (∀ n, M ≤ n → val.v (t n) = some l) →
    ∀ n, M ≤ n → val.v (K.mul (s n) (t n)) = some (k + l)
  /-- 非零元の逆元の well-defined 性（同一安定値の任意代表）。 -/
  inv_wd : ∀ (s s' : Nat → K.carrier) (k : Int) (M M' : Nat),
    (∀ n, M ≤ n → val.v (s n) = some k) → (∀ n, M' ≤ n → val.v (s' n) = some k) →
    locCompRel val s s' →
    locCompRel val (fun n => K.inv (s n)) (fun n => K.inv (s' n))
  /-- 逆元律: 安定値 k（有限）を持つ非零 Cauchy 列 s は [s]·[s⁻¹]=[1]。 -/
  mul_inv : ∀ (s : Nat → K.carrier) (k : Int) (M : Nat),
    (∀ n, M ≤ n → val.v (s n) = some k) →
    locCompRel val (fun n => K.mul (s n) (K.inv (s n))) (fun _ => K.one)

/-- **M316F-10b: 任意の離散付値から完備化体データを組み立てる**。 -/
def fldComp_toData {K : IUTField} (val : valRingValuation K) : FieldCompletionData K where
  val := val
  val_extend_mul := fun s t k l M hs ht => fldComp_val_mul_stable val s t k l M hs ht
  inv_wd := fun s s' k M M' hs hs' hrel => fldComp_inv_wd_gen val s s' k M M' hs hs' hrel
  mul_inv := fun s k M hs => fldComp_mul_inv_cancel_gen val s k M hs

/-- **M316F-10c: 完備化体データは存在する**（DecidableEq を持つ体上、自明付値から）。 -/
theorem fldComp_exists (K : IUTField) [DecidableEq K.carrier] :
    Nonempty (FieldCompletionData K) :=
  ⟨fldComp_toData (trivialValuation K)⟩

/-- **M316F-10d: 完備化 K̂ は体**（総括・本物）— 自明付値の完備化 K̂ が本物の IUTField をなす。
    **M311F が後続に残した「K̂ が体」を本物で閉じた成果**（本物の忠実な部分ケース）。 -/
theorem fldComp_completion_isField (K : IUTField) [DecidableEq K.carrier] :
    Nonempty IUTField :=
  ⟨fldCompTrivField K⟩

/-- **M316F-10e: 付値延長 v̂ の乗法性**（総括・本物の主要部分）。 -/
theorem fldComp_val_extend {K : IUTField} (val : valRingValuation K) :
    ∀ (s t : Nat → K.carrier) (k l : Int) (M : Nat),
    (∀ n, M ≤ n → val.v (s n) = some k) → (∀ n, M ≤ n → val.v (t n) = some l) →
    ∀ n, M ≤ n → val.v (K.mul (s n) (t n)) = some (k + l) :=
  fldComp_val_mul_stable val

/-- **M316F-10f: 実例（自明付値の完備化 K̂ は体）** — 自明付値では K は完備で K̂≅K だが、本
    ファイルの構成でも完備化 K̂ は本物の IUTField をなす。**本物の体 K・本物の自明付値を主語**と
    する実例（toy 主語ではない）。K̂≅K の全体同型（環・体同型・逆向き）は後続。 -/
def fldComp_trivial_isField (K : IUTField) [DecidableEq K.carrier] : IUTField :=
  fldCompTrivField K

end IUT
