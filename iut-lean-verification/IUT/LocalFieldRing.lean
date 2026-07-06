/-
  IUT/LocalFieldRing.lean — M311F: 完備化 K̂ の環化・体核（局所類体論＝柱 B の本物の先行建設）

  ── 主要成果の分類: **[実]**（M306F（LocalFieldCompletion）が残した honest 限定
  「**乗法の合同は Cauchy 列の付値有界性を要し…環化は後続。K̂ が体であることの全証明も
  後続**」を、**本物で閉じる**。すなわち (1) Cauchy 列の**付値有界性**（下に有界）を本物で
  示し、(2) それを土台に**乗法の Cauchy 閉性**と**乗法の合同（well-defined）**を本物で建設、
  (3) M306F の setoid（Cauchy 列 / 零列）を実際の `Quotient` に束ね、加法（M306F）＋
  **乗法**を入れて **K̂ を本物の可換環 `CRing` として構成**する。(4) 定数列による埋め込み
  K↪K̂ が**環準同型**（加法・乗法・1 保存）かつ**単射**（M306F `locComp_const_inj` を
  `Quotient.exact` 経由で接続）であることを本物で示す。(5) 体核として、非零 Cauchy 列の
  **付値が最終的に一定**（安定化・付値の延長 v̂ の核）と、**その逆元列が Cauchy**（K̂ が体で
  ある核）を本物で証明する。）

  complete_pct 影響: **柱B の局所体（完備離散付値体）の実 IUT 完全証明率を前進**。
  M306F は完備化の**加法群構造**（Cauchy/零列・setoid・加法合同・埋め込み単射）までを
  本物にし、**乗法合同・環化・体核は「後続」と honest 明記**していた。本ファイルはその
  後続を本物で置換する（規則 §2(a) 昇格 + (b) 先行建設）:
    - M306F honest 限定「乗法の合同は Cauchy 列の付値有界性を要し…環化は後続」
      → **本物化**（`locRing_cauchy_bddBelow` / `locRing_cauchy_mul` / `locRing_cong_mul`
        / `locRingCompletionRing`（実 CRing））。
    - M306F honest 限定「K̂ が体であることの全証明も後続」
      → 体核を**本物化**（`locRing_cauchy_stable`（付値の延長 v̂ の核）/
        `locRing_inv_cauchy`（逆元列の Cauchy 性））。K̂ の inv 全域化・完備性込みの
        収束は主要部分＋骨組みとして後続に残す（下記 正直な限定を参照・弱化せず）。

  * M311F-1 環補題      — `locRing_mul_neg` / `locRing_neg_mul` / `locRing_add_sub_cancel`
    （可換環の恒等式・本物）
  * M311F-2 付値の積下界 — `locRing_v_mul_ge`（v(a)≥p, v(b)≥q ⟹ v(ab)≥p+q・本物）/
    `locRing_le_of_none_le`
  * M311F-3 付値有界性  — `locRing_cauchy_bddBelow`（Cauchy 列は付値が下に有界・本物・
    M306F 後続の核）
  * M311F-4 乗法テレスコープ — `locRing_mul_telescope`
    （sₘtₘ−sₙtₙ = sₘ(tₘ−tₙ)+(sₘ−sₙ)tₙ・可換環恒等式・本物）
  * M311F-5 乗法 Cauchy 閉性 — `locRing_cauchy_mul`（Cauchy×Cauchy＝Cauchy・本物）
  * M311F-6 乗法零吸収  — `locRing_mulL_null` / `locRing_mulR_null`
    （有界×零＝零・付値有界性を使う本物）
  * M311F-7 乗法合同    — `locRing_cong_mul`（s~s', t~t' ⟹ st~s't'・**M306F の後続を
    本物で閉じた核**）
  * M311F-8 完備化の型  — `locRingCauchy`（Cauchy 列の subtype）/ `locRingRel` /
    `locRingSetoid`（M306F の同値律を Setoid に束ねる）/ `locRingCompletion`（Quotient）
  * M311F-9 環演算      — `locRingCauchyAdd/Neg/Mul` / `locRingConst` /
    `locRingAdd/Neg/Mul`（Quotient.liftOn₂ で well-defined・合同は §6/§7 と M306F）
  * M311F-10 K̂ は可換環 — `locRingCompletionRing`（**本物の CRing**）/ `locRing_isCRing`
  * M311F-11 環準同型埋め込み — `locRingEmbed` / `locRing_embed_add/mul/one`
    （K↪K̂ 環準同型・本物）/ `locRing_embed_inj`（単射・`Quotient.exact` + M306F）
  * M311F-12 体核（付値延長・逆元）— `locRing_v_inv`（v(x⁻¹)=−v(x)）/
    `locRing_val_dominant`（超距離の狭義優越）/ `locRing_cauchy_stable`（付値の安定化＝
    延長 v̂ の核）/ `locRing_inv_diff`（x⁻¹−y⁻¹=(y−x)x⁻¹y⁻¹）/ `locRing_inv_cauchy`
    （逆元列の Cauchy 性）
  * M311F-13 capstone   — `LocalFieldRingData` / `locRing_toData` / `locRing_exists` /
    `locRing_completion_isCRing` / `locRing_embed_isHom` / 実例 `locRing_trivial_completion`

  正直な限定（何が本物で何が骨組み・後続か）:
  - **本物（完全証明・sorry 皆無・新規 choice 皆無）**: §1 環恒等式、§2 付値の積下界、
    §3 **Cauchy 列の付値有界性**（M306F 後続の核）、§4 乗法テレスコープ、§5 **乗法の
    Cauchy 閉性**、§6 有界×零＝零、§7 **乗法の合同**（M306F の gap を閉じた本物）、
    §8/§9 完備化 Quotient と環演算の well-defined、§10 **K̂ が本物の可換環 CRing**、
    §11 埋め込み K↪K̂ が**環準同型かつ単射**、§12 体核（付値の安定化＝延長 v̂ の核・
    逆元列の Cauchy 性）。
  - **主要部分＋骨組み（honest 限定・後続、弱化・消去せず）**:
    * K̂ 上の**逆元 inv の全域化**（各非零類に逆元類を割り当てる写像を K̂ 全体に載せて
      `IUTField` 構造を得る全証明）は本ファイルでは行わない。核（非零 Cauchy 列の逆元列が
      Cauchy であること・付値が安定すること）を本物にし、inv の類レベル全域化・0 の扱い・
      完備性込みの収束（K̂ が完備）は後続に委ねる。ゆえに本ファイルは「K̂ は**可換環**」
      までを本物とし、「K̂ は**体**」は体核（逆元 Cauchy・付値安定）の本物 + 全域化の骨組み。
    * 付値の延長 v̂ は「非零 Cauchy 列の付値が或る有限値 v₀ に安定する」（`locRing_cauchy_stable`）
      を本物にする。v̂ を K̂ 上の関数として全域定義し付値公理を再証明する全構成は後続。
    * 値群は ℤ（離散付値）に限る。有限剰余体の局所体・局所類体論の主定理は後続。
  - 本ファイルは M306F の honest 限定を**本物の置換で前進**させるものであり、既存の honest
    限定を消去・弱化しない。**toy 主語ではない**: 主語は本物の体 K・本物の離散付値 v・
    本物の完備化 K̂・本物の Cauchy 列である。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
-/
import IUT.LocalFieldCompletion

namespace IUT

/-! ## M311F-1: 可換環の恒等式（本物） -/

/-- **M311F-1a: a·(−b) = −(a·b)**（可換環）。 -/
theorem locRing_mul_neg (K : IUTField) (a b : K.carrier) :
    K.mul a (K.neg b) = K.neg (K.mul a b) := by
  have hz : K.add (K.mul a b) (K.mul a (K.neg b)) = K.zero := by
    rw [← K.left_distrib, locComp_sub_self_zero K b, K.toCRing.mul_zero]
  have hz2 : K.add (K.mul a b) (K.neg (K.mul a b)) = K.zero :=
    locComp_sub_self_zero K (K.mul a b)
  have e : K.add (K.mul a b) (K.mul a (K.neg b)) = K.add (K.mul a b) (K.neg (K.mul a b)) := by
    rw [hz, hz2]
  exact K.toCRing.add_left_cancel e

/-- **M311F-1b: (−a)·b = −(a·b)**（可換環）。 -/
theorem locRing_neg_mul (K : IUTField) (a b : K.carrier) :
    K.mul (K.neg a) b = K.neg (K.mul a b) := by
  have hz : K.add (K.mul a b) (K.mul (K.neg a) b) = K.zero := by
    rw [← K.toCRing.right_distrib, locComp_sub_self_zero K a,
      K.mul_comm K.zero b, K.toCRing.mul_zero]
  have hz2 : K.add (K.mul a b) (K.neg (K.mul a b)) = K.zero :=
    locComp_sub_self_zero K (K.mul a b)
  have e : K.add (K.mul a b) (K.mul (K.neg a) b) = K.add (K.mul a b) (K.neg (K.mul a b)) := by
    rw [hz, hz2]
  exact K.toCRing.add_left_cancel e

/-- **M311F-1c: (x−y)+y = x**（可換環）。 -/
theorem locRing_add_sub_cancel (K : IUTField) (x y : K.carrier) :
    K.add (K.add x (K.neg y)) y = x := by
  rw [K.add_assoc x (K.neg y) y, K.neg_add y, K.add_comm x K.zero, K.zero_add]

/-- **M311F-1d: (x+y)−y = x**（可換環）。 -/
theorem locRing_add_neg_cancel (K : IUTField) (x y : K.carrier) :
    K.add (K.add x y) (K.neg y) = x := by
  rw [K.add_assoc x y (K.neg y), locComp_sub_self_zero K y, K.add_comm x K.zero, K.zero_add]

/-! ## M311F-2: 付値の積下界（本物） -/

/-- **M311F-2a: none 下界からの持ち上げ** — v(x)≥∞ なら v(x)≥p（p 任意）。 -/
theorem locRing_le_of_none_le (p : Int) (x : Option Int) (h : valOptLe none x) :
    valOptLe (some p) x := by
  cases x with
  | none => exact True.intro
  | some k => exact h.elim

/-- **M311F-2b: 積の付値下界** — v(a)≥p かつ v(b)≥q なら v(ab)=v(a)+v(b)≥p+q。 -/
theorem locRing_v_mul_ge {K : IUTField} (val : valRingValuation K) (a b : K.carrier)
    (p q : Int) (ha : valOptLe (some p) (val.v a)) (hb : valOptLe (some q) (val.v b)) :
    valOptLe (some (p + q)) (val.v (K.mul a b)) := by
  rw [val.v_mul]
  cases hva : val.v a with
  | none => rw [valOptAdd_none_left]; exact True.intro
  | some x =>
    cases hvb : val.v b with
    | none => rw [valOptAdd_some_none]; exact True.intro
    | some y =>
      rw [valOptAdd_some_some]
      show p + q ≤ x + y
      rw [hva] at ha
      rw [hvb] at hb
      have hpx : p ≤ x := ha
      have hqy : q ≤ y := hb
      omega

/-! ## M311F-3: Cauchy 列の付値有界性（本物・M306F 後続の核） -/

/-- **M311F-3: Cauchy 列は付値が下に有界** — 任意の Cauchy 列 s に対し、ある有限下界
    B:ℤ とある閾値 M があり、n≥M で v(sₙ)≥B。sₙ=(sₙ−s_M)+s_M と超距離不等式から。
    これは M306F が「乗法合同に必要」と honest 明記した**付値有界性 witness** の本物。 -/
theorem locRing_cauchy_bddBelow {K : IUTField} (val : valRingValuation K)
    (s : Nat → K.carrier) (hs : locCompCauchy val s) :
    ∃ (B : Int) (M : Nat), ∀ n, M ≤ n → valOptLe (some B) (val.v (s n)) := by
  obtain ⟨M, hM⟩ := hs 0
  cases hvM : val.v (s M) with
  | none =>
    refine ⟨0, M, ?_⟩
    intro n hn
    have hdiff : valOptLe (some 0) (val.v (K.add (s n) (K.neg (s M)))) := hM n M hn (Nat.le_refl M)
    have hrec : K.add (K.add (s n) (K.neg (s M))) (s M) = s n :=
      locRing_add_sub_cancel K (s n) (s M)
    cases val.v_add_ge (K.add (s n) (K.neg (s M))) (s M) with
    | inl hd =>
      have hd' : valOptLe (val.v (K.add (s n) (K.neg (s M)))) (val.v (s n)) := by
        rw [hrec] at hd; exact hd
      exact valOptLe_trans hdiff hd'
    | inr hd =>
      have hd' : valOptLe (val.v (s M)) (val.v (s n)) := by
        rw [hrec] at hd; exact hd
      rw [hvM] at hd'
      exact locRing_le_of_none_le 0 (val.v (s n)) hd'
  | some k =>
    cases Int.le_total 0 k with
    | inl hk =>
      refine ⟨0, M, ?_⟩
      intro n hn
      have hdiff : valOptLe (some 0) (val.v (K.add (s n) (K.neg (s M)))) := hM n M hn (Nat.le_refl M)
      have hrec : K.add (K.add (s n) (K.neg (s M))) (s M) = s n :=
        locRing_add_sub_cancel K (s n) (s M)
      cases val.v_add_ge (K.add (s n) (K.neg (s M))) (s M) with
      | inl hd =>
        have hd' : valOptLe (val.v (K.add (s n) (K.neg (s M)))) (val.v (s n)) := by
          rw [hrec] at hd; exact hd
        exact valOptLe_trans hdiff hd'
      | inr hd =>
        have hd' : valOptLe (val.v (s M)) (val.v (s n)) := by
          rw [hrec] at hd; exact hd
        rw [hvM] at hd'
        have hk' : valOptLe (some (0 : Int)) (some k) := hk
        exact valOptLe_trans hk' hd'
    | inr hk =>
      refine ⟨k, M, ?_⟩
      intro n hn
      have hdiff : valOptLe (some 0) (val.v (K.add (s n) (K.neg (s M)))) := hM n M hn (Nat.le_refl M)
      have hrec : K.add (K.add (s n) (K.neg (s M))) (s M) = s n :=
        locRing_add_sub_cancel K (s n) (s M)
      cases val.v_add_ge (K.add (s n) (K.neg (s M))) (s M) with
      | inl hd =>
        have hd' : valOptLe (val.v (K.add (s n) (K.neg (s M)))) (val.v (s n)) := by
          rw [hrec] at hd; exact hd
        have hk' : valOptLe (some k) (some (0 : Int)) := hk
        exact valOptLe_trans hk' (valOptLe_trans hdiff hd')
      | inr hd =>
        have hd' : valOptLe (val.v (s M)) (val.v (s n)) := by
          rw [hrec] at hd; exact hd
        rw [hvM] at hd'
        exact hd'

/-! ## M311F-4: 乗法テレスコープ恒等式（本物） -/

/-- **M311F-4: 乗法テレスコープ** — sₘtₘ − sₙtₙ = sₘ(tₘ−tₙ) + (sₘ−sₙ)tₙ（可換環）。
    乗法の Cauchy 閉性・合同の代数核。 -/
theorem locRing_mul_telescope (K : IUTField) (sm sn tm tn : K.carrier) :
    K.add (K.mul sm (K.add tm (K.neg tn))) (K.mul (K.add sm (K.neg sn)) tn)
      = K.add (K.mul sm tm) (K.neg (K.mul sn tn)) := by
  rw [K.left_distrib sm tm (K.neg tn), locRing_mul_neg K sm tn,
    K.toCRing.right_distrib sm (K.neg sn) tn, locRing_neg_mul K sn tn]
  exact (locComp_sub_telescope K (K.mul sm tm) (K.mul sm tn) (K.mul sn tn)).symm

/-! ## M311F-5: 乗法の Cauchy 閉性（本物） -/

/-- **M311F-5: Cauchy 列は乗法で閉じる** — 付値有界性（§3）+ 乗法テレスコープ（§4）+
    付値の積下界（§2）で v(sₘtₘ−sₙtₙ)≥N を得る。M306F が後続とした乗法閉性の本物。 -/
theorem locRing_cauchy_mul {K : IUTField} (val : valRingValuation K)
    (s t : Nat → K.carrier) (hs : locCompCauchy val s) (ht : locCompCauchy val t) :
    locCompCauchy val (fun n => K.mul (s n) (t n)) := by
  intro N
  obtain ⟨Bs, Ms, hBs⟩ := locRing_cauchy_bddBelow val s hs
  obtain ⟨Bt, Mt, hBt⟩ := locRing_cauchy_bddBelow val t ht
  obtain ⟨M1, hM1⟩ := ht (N - Bs)
  obtain ⟨M2, hM2⟩ := hs (N - Bt)
  refine ⟨Ms + Mt + M1 + M2, ?_⟩
  intro m n hm hn
  have hmMs : Ms ≤ m := by omega
  have hnMt : Mt ≤ n := by omega
  have hmM1 : M1 ≤ m := by omega
  have hnM1 : M1 ≤ n := by omega
  have hmM2 : M2 ≤ m := by omega
  have hnM2 : M2 ≤ n := by omega
  -- term1 = sₘ·(tₘ−tₙ): v ≥ Bs + (N−Bs) = N
  have hv1 : valOptLe (some N) (val.v (K.mul (s m) (K.add (t m) (K.neg (t n))))) := by
    have h := locRing_v_mul_ge val (s m) (K.add (t m) (K.neg (t n))) Bs (N - Bs)
      (hBs m hmMs) (hM1 m n hmM1 hnM1)
    have heq : Bs + (N - Bs) = N := by omega
    rw [heq] at h
    exact h
  -- term2 = (sₘ−sₙ)·tₙ: v ≥ (N−Bt) + Bt = N
  have hv2 : valOptLe (some N) (val.v (K.mul (K.add (s m) (K.neg (s n))) (t n))) := by
    have h := locRing_v_mul_ge val (K.add (s m) (K.neg (s n))) (t n) (N - Bt) Bt
      (hM2 m n hmM2 hnM2) (hBt n hnMt)
    have heq : (N - Bt) + Bt = N := by omega
    rw [heq] at h
    exact h
  show valOptLe (some N) (val.v (K.add (K.mul (s m) (t m)) (K.neg (K.mul (s n) (t n)))))
  rw [← locRing_mul_telescope K (s m) (s n) (t m) (t n)]
  exact locComp_add_both_ge val N _ _ hv1 hv2

/-! ## M311F-6: 有界×零＝零（付値有界性を使う本物） -/

/-- **M311F-6a: 有界列×零列＝零列** — a が下に有界（∃B M, n≥M で v(aₙ)≥B）で b が零列
    なら a·b は零列（v(aₙbₙ)=v(aₙ)+v(bₙ)≥B+(N−B)=N）。 -/
theorem locRing_mulL_null {K : IUTField} (val : valRingValuation K) (a b : Nat → K.carrier)
    (ha : ∃ (B : Int) (M : Nat), ∀ n, M ≤ n → valOptLe (some B) (val.v (a n)))
    (hb : locCompNull val b) : locCompNull val (fun n => K.mul (a n) (b n)) := by
  obtain ⟨B, Ma, hMa⟩ := ha
  intro N
  obtain ⟨Mb, hMb⟩ := hb (N - B)
  refine ⟨Ma + Mb, ?_⟩
  intro n hn
  have hnMa : Ma ≤ n := by omega
  have hnMb : Mb ≤ n := by omega
  have h := locRing_v_mul_ge val (a n) (b n) B (N - B) (hMa n hnMa) (hMb n hnMb)
  have heq : B + (N - B) = N := by omega
  rw [heq] at h
  exact h

/-- **M311F-6b: 零列×有界列＝零列**（可換性で §6a に帰着）。 -/
theorem locRing_mulR_null {K : IUTField} (val : valRingValuation K) (a b : Nat → K.carrier)
    (ha : locCompNull val a)
    (hb : ∃ (B : Int) (M : Nat), ∀ n, M ≤ n → valOptLe (some B) (val.v (b n))) :
    locCompNull val (fun n => K.mul (a n) (b n)) := by
  have h := locRing_mulL_null val b a hb ha
  have e : (fun n => K.mul (b n) (a n)) = (fun n => K.mul (a n) (b n)) :=
    funext fun n => K.mul_comm (b n) (a n)
  rw [e] at h
  exact h

/-! ## M311F-7: 乗法の合同（M306F の後続を本物で閉じた核） -/

/-- **M311F-7: 乗法の合同（well-defined）** — s Cauchy, t' Cauchy で s~s'（差が零列）,
    t~t'（差が零列）なら s·t ~ s'·t'。M306F が「Cauchy 列の付値有界性を要す」として後続と
    した**乗法の合同**を、§3 の付値有界性を土台に本物で閉じる。これにより完備化 K̂ の乗法が
    setoid で well-defined になる。 -/
theorem locRing_cong_mul {K : IUTField} (val : valRingValuation K)
    (s s' t t' : Nat → K.carrier)
    (hsC : locCompCauchy val s) (ht'C : locCompCauchy val t')
    (hss' : locCompRel val s s') (htt' : locCompRel val t t') :
    locCompRel val (fun n => K.mul (s n) (t n)) (fun n => K.mul (s' n) (t' n)) := by
  -- term1 = s·(t−t'): 有界 s × 零列 (t−t')
  have hnull1 : locCompNull val (fun n => K.mul (s n) (K.add (t n) (K.neg (t' n)))) :=
    locRing_mulL_null val s (fun n => K.add (t n) (K.neg (t' n)))
      (locRing_cauchy_bddBelow val s hsC) htt'
  -- term2 = (s−s')·t': 零列 (s−s') × 有界 t'
  have hnull2 : locCompNull val (fun n => K.mul (K.add (s n) (K.neg (s' n))) (t' n)) :=
    locRing_mulR_null val (fun n => K.add (s n) (K.neg (s' n))) t'
      hss' (locRing_cauchy_bddBelow val t' ht'C)
  have hsum := locComp_null_add val
    (fun n => K.mul (s n) (K.add (t n) (K.neg (t' n))))
    (fun n => K.mul (K.add (s n) (K.neg (s' n))) (t' n)) hnull1 hnull2
  -- sum = s·t − s'·t' by 乗法テレスコープ
  have e : (fun n => K.add (K.mul (s n) (K.add (t n) (K.neg (t' n))))
        (K.mul (K.add (s n) (K.neg (s' n))) (t' n)))
      = (fun n => K.add (K.mul (s n) (t n)) (K.neg (K.mul (s' n) (t' n)))) :=
    funext fun n => locRing_mul_telescope K (s n) (s' n) (t n) (t' n)
  rw [e] at hsum
  exact hsum

/-! ## M311F-8: 完備化の型（Cauchy 列の Quotient・M306F setoid を束ねる） -/

/-- **M311F-8a: Cauchy 列の subtype**（完備化 K̂ の台の代表）。 -/
def locRingCauchy {K : IUTField} (val : valRingValuation K) : Type :=
  { s : Nat → K.carrier // locCompCauchy val s }

/-- **M311F-8b: 完備化の同値関係**（M306F `locCompRel` を subtype に持ち上げ）。 -/
def locRingRel {K : IUTField} (val : valRingValuation K)
    (a b : locRingCauchy val) : Prop :=
  locCompRel val a.val b.val

/-- **M311F-8c: 完備化の Setoid**（M306F の反射・対称・推移律を束ねる・本物）。 -/
instance locRingSetoid {K : IUTField} (val : valRingValuation K) :
    Setoid (locRingCauchy val) where
  r := locRingRel val
  iseqv := ⟨fun a => locCompRel_refl val a.val,
    fun {a b} h => locCompRel_symm val a.val b.val h,
    fun {a b c} h1 h2 => locCompRel_trans val a.val b.val c.val h1 h2⟩

/-- **M311F-8d: 完備化 K̂ の台**（Cauchy 列を零列で割る Quotient）。 -/
def locRingCompletion {K : IUTField} (val : valRingValuation K) : Type :=
  Quotient (locRingSetoid val)

/-! ## M311F-9: 環演算（Quotient.liftOn₂ で well-defined） -/

/-- 定数列（Cauchy）。 -/
def locRingConst {K : IUTField} (val : valRingValuation K) (a : K.carrier) :
    locRingCauchy val :=
  ⟨fun _ => a, locComp_const_cauchy val a⟩

/-- 代表レベルの加法（Cauchy 閉性は M306F）。 -/
def locRingCauchyAdd {K : IUTField} (val : valRingValuation K)
    (a b : locRingCauchy val) : locRingCauchy val :=
  ⟨fun n => K.add (a.val n) (b.val n), locComp_cauchy_add val a.val b.val a.property b.property⟩

/-- 代表レベルの反元（Cauchy 閉性は M306F）。 -/
def locRingCauchyNeg {K : IUTField} (val : valRingValuation K)
    (a : locRingCauchy val) : locRingCauchy val :=
  ⟨fun n => K.neg (a.val n), locComp_cauchy_neg val a.val a.property⟩

/-- 代表レベルの乗法（Cauchy 閉性は §5）。 -/
def locRingCauchyMul {K : IUTField} (val : valRingValuation K)
    (a b : locRingCauchy val) : locRingCauchy val :=
  ⟨fun n => K.mul (a.val n) (b.val n), locRing_cauchy_mul val a.val b.val a.property b.property⟩

/-- **M311F-9a: K̂ の加法**（M306F の加法合同 `locCompRel_add` で well-defined）。 -/
def locRingAdd {K : IUTField} (val : valRingValuation K)
    (A B : locRingCompletion val) : locRingCompletion val :=
  Quotient.liftOn₂ A B (fun a b => Quotient.mk (locRingSetoid val) (locRingCauchyAdd val a b))
    (fun a₁ a₂ b₁ b₂ h1 h2 =>
      Quotient.sound (locCompRel_add val a₁.val b₁.val a₂.val b₂.val h1 h2))

/-- **M311F-9b: K̂ の反元**（M306F の反元合同 `locCompRel_neg` で well-defined）。 -/
def locRingNeg {K : IUTField} (val : valRingValuation K)
    (A : locRingCompletion val) : locRingCompletion val :=
  Quotient.liftOn A (fun a => Quotient.mk (locRingSetoid val) (locRingCauchyNeg val a))
    (fun a b h => Quotient.sound (locCompRel_neg val a.val b.val h))

/-- **M311F-9c: K̂ の乗法**（§7 の乗法合同 `locRing_cong_mul` で well-defined・本物）。 -/
def locRingMul {K : IUTField} (val : valRingValuation K)
    (A B : locRingCompletion val) : locRingCompletion val :=
  Quotient.liftOn₂ A B (fun a b => Quotient.mk (locRingSetoid val) (locRingCauchyMul val a b))
    (fun a₁ a₂ b₁ b₂ h1 h2 =>
      Quotient.sound (locRing_cong_mul val a₁.val b₁.val a₂.val b₂.val
        a₁.property b₂.property h1 h2))

/-! ## M311F-10: K̂ は本物の可換環（環化・M306F の gap を閉じる本丸） -/

/-- **M311F-10: 完備化 K̂ は可換環** — M306F の setoid（Cauchy 列 / 零列）を Quotient に
    束ね、加法（M306F）・反元・**乗法（§7 で本物化）**を入れた**本物の CRing**。環法則は
    代表列の各点環法則（Subtype.ext + funext）で閉じる（零列を割っても各点法則は不変）。 -/
def locRingCompletionRing {K : IUTField} (val : valRingValuation K) : CRing where
  carrier := locRingCompletion val
  add := locRingAdd val
  zero := Quotient.mk (locRingSetoid val) (locRingConst val K.zero)
  neg := locRingNeg val
  mul := locRingMul val
  one := Quotient.mk (locRingSetoid val) (locRingConst val K.one)
  add_assoc := by
    intro A B C
    induction A using Quotient.ind; rename_i a
    induction B using Quotient.ind; rename_i b
    induction C using Quotient.ind; rename_i c
    show Quotient.mk (locRingSetoid val) (locRingCauchyAdd val (locRingCauchyAdd val a b) c)
      = Quotient.mk (locRingSetoid val) (locRingCauchyAdd val a (locRingCauchyAdd val b c))
    exact congrArg (Quotient.mk (locRingSetoid val))
      (Subtype.ext (funext fun n => K.add_assoc (a.val n) (b.val n) (c.val n)))
  zero_add := by
    intro A
    induction A using Quotient.ind; rename_i a
    show Quotient.mk (locRingSetoid val) (locRingCauchyAdd val (locRingConst val K.zero) a)
      = Quotient.mk (locRingSetoid val) a
    exact congrArg (Quotient.mk (locRingSetoid val))
      (Subtype.ext (funext fun n => K.zero_add (a.val n)))
  neg_add := by
    intro A
    induction A using Quotient.ind; rename_i a
    show Quotient.mk (locRingSetoid val) (locRingCauchyAdd val (locRingCauchyNeg val a) a)
      = Quotient.mk (locRingSetoid val) (locRingConst val K.zero)
    exact congrArg (Quotient.mk (locRingSetoid val))
      (Subtype.ext (funext fun n => K.neg_add (a.val n)))
  add_comm := by
    intro A B
    induction A using Quotient.ind; rename_i a
    induction B using Quotient.ind; rename_i b
    show Quotient.mk (locRingSetoid val) (locRingCauchyAdd val a b)
      = Quotient.mk (locRingSetoid val) (locRingCauchyAdd val b a)
    exact congrArg (Quotient.mk (locRingSetoid val))
      (Subtype.ext (funext fun n => K.add_comm (a.val n) (b.val n)))
  mul_assoc := by
    intro A B C
    induction A using Quotient.ind; rename_i a
    induction B using Quotient.ind; rename_i b
    induction C using Quotient.ind; rename_i c
    show Quotient.mk (locRingSetoid val) (locRingCauchyMul val (locRingCauchyMul val a b) c)
      = Quotient.mk (locRingSetoid val) (locRingCauchyMul val a (locRingCauchyMul val b c))
    exact congrArg (Quotient.mk (locRingSetoid val))
      (Subtype.ext (funext fun n => K.mul_assoc (a.val n) (b.val n) (c.val n)))
  one_mul := by
    intro A
    induction A using Quotient.ind; rename_i a
    show Quotient.mk (locRingSetoid val) (locRingCauchyMul val (locRingConst val K.one) a)
      = Quotient.mk (locRingSetoid val) a
    exact congrArg (Quotient.mk (locRingSetoid val))
      (Subtype.ext (funext fun n => K.one_mul (a.val n)))
  mul_comm := by
    intro A B
    induction A using Quotient.ind; rename_i a
    induction B using Quotient.ind; rename_i b
    show Quotient.mk (locRingSetoid val) (locRingCauchyMul val a b)
      = Quotient.mk (locRingSetoid val) (locRingCauchyMul val b a)
    exact congrArg (Quotient.mk (locRingSetoid val))
      (Subtype.ext (funext fun n => K.mul_comm (a.val n) (b.val n)))
  left_distrib := by
    intro A B C
    induction A using Quotient.ind; rename_i a
    induction B using Quotient.ind; rename_i b
    induction C using Quotient.ind; rename_i c
    show Quotient.mk (locRingSetoid val) (locRingCauchyMul val a (locRingCauchyAdd val b c))
      = Quotient.mk (locRingSetoid val)
          (locRingCauchyAdd val (locRingCauchyMul val a b) (locRingCauchyMul val a c))
    exact congrArg (Quotient.mk (locRingSetoid val))
      (Subtype.ext (funext fun n => K.left_distrib (a.val n) (b.val n) (c.val n)))

/-- **M311F-10b: K̂ は可換環（存在）**。 -/
theorem locRing_isCRing {K : IUTField} (val : valRingValuation K) :
    Nonempty CRing :=
  ⟨locRingCompletionRing val⟩

/-! ## M311F-11: 環準同型埋め込み K ↪ K̂（本物） -/

/-- **M311F-11a: 埋め込み** — 定数列で K → K̂。 -/
def locRingEmbed {K : IUTField} (val : valRingValuation K) (a : K.carrier) :
    locRingCompletion val :=
  Quotient.mk (locRingSetoid val) (locRingConst val a)

/-- **M311F-11b: 加法を保存** — φ(a+b) = φ(a) + φ(b)。 -/
theorem locRing_embed_add {K : IUTField} (val : valRingValuation K) (a b : K.carrier) :
    locRingEmbed val (K.add a b) = locRingAdd val (locRingEmbed val a) (locRingEmbed val b) :=
  congrArg (Quotient.mk (locRingSetoid val)) (Subtype.ext rfl)

/-- **M311F-11c: 乗法を保存** — φ(ab) = φ(a)·φ(b)。 -/
theorem locRing_embed_mul {K : IUTField} (val : valRingValuation K) (a b : K.carrier) :
    locRingEmbed val (K.mul a b) = locRingMul val (locRingEmbed val a) (locRingEmbed val b) :=
  congrArg (Quotient.mk (locRingSetoid val)) (Subtype.ext rfl)

/-- **M311F-11d: 1 を保存** — φ(1) = 1。 -/
theorem locRing_embed_one {K : IUTField} (val : valRingValuation K) :
    locRingEmbed val K.one = (locRingCompletionRing val).one :=
  rfl

/-- **M311F-11e: 埋め込みは単射** — φ(a)=φ(b) ⟹ a=b（`Quotient.exact` で類の同値へ、
    M306F `locComp_const_inj` で代表の等式へ）。 -/
theorem locRing_embed_inj {K : IUTField} (val : valRingValuation K) (a b : K.carrier)
    (h : locRingEmbed val a = locRingEmbed val b) : a = b := by
  have hrel : locRingRel val (locRingConst val a) (locRingConst val b) := Quotient.exact h
  exact locComp_const_inj val a b hrel

/-! ## M311F-12: 体核（付値の延長・逆元列の Cauchy 性・本物） -/

/-- **M311F-12a: 逆元の付値** — v(x)=k（有限, x≠0）なら v(x⁻¹)=−k。 -/
theorem locRing_v_inv {K : IUTField} (val : valRingValuation K) (x : K.carrier)
    (k : Int) (hx : x ≠ K.zero) (hvx : val.v x = some k) :
    val.v (K.inv x) = some (-k) := by
  have hv1 : val.v (K.mul x (K.inv x)) = valOptAdd (val.v x) (val.v (K.inv x)) :=
    val.v_mul x (K.inv x)
  rw [K.mul_inv_cancel x hx, val.v_one, hvx] at hv1
  cases hvi : val.v (K.inv x) with
  | none => rw [hvi, valOptAdd_some_none] at hv1; nomatch hv1
  | some c =>
    rw [hvi, valOptAdd_some_some] at hv1
    have hcc : (0 : Int) = k + c := Option.some.inj hv1
    have hc : c = -k := by omega
    rw [hc]

/-- **M311F-12b: 超距離の狭義優越** — v(a)=ka（有限）かつ v(b)≥ka+1 なら v(a+b)=v(a)。
    付値の安定化（延長 v̂）の核。 -/
theorem locRing_val_dominant {K : IUTField} (val : valRingValuation K) (a b : K.carrier)
    (ka : Int) (hva : val.v a = some ka) (hvb : valOptLe (some (ka + 1)) (val.v b)) :
    val.v (K.add a b) = some ka := by
  have hge : valOptLe (some ka) (val.v (K.add a b)) := by
    cases val.v_add_ge a b with
    | inl h => rw [hva] at h; exact h
    | inr h =>
      have hstep : valOptLe (some ka) (val.v b) :=
        valOptLe_trans (show valOptLe (some ka) (some (ka + 1)) from by
          show ka ≤ ka + 1; omega) hvb
      exact valOptLe_trans hstep h
  have hrec : K.add (K.add a b) (K.neg b) = a := locRing_add_neg_cancel K a b
  have hle : valOptLe (val.v (K.add a b)) (some ka) := by
    cases val.v_add_ge (K.add a b) (K.neg b) with
    | inl h => rw [hrec, hva] at h; exact h
    | inr h =>
      rw [hrec, hva, valRing_v_neg] at h
      exfalso
      cases hvbc : val.v b with
      | none => rw [hvbc] at h; exact h.elim
      | some mb =>
        rw [hvbc] at h
        rw [hvbc] at hvb
        have h1 : mb ≤ ka := h
        have h2 : ka + 1 ≤ mb := hvb
        omega
  cases hvab : val.v (K.add a b) with
  | none => rw [hvab] at hle; exact hle.elim
  | some j =>
    rw [hvab] at hge hle
    have hj1 : ka ≤ j := hge
    have hj2 : j ≤ ka := hle
    have hje : j = ka := by omega
    rw [hje]

/-- **M311F-12c: Cauchy 列の付値の安定化（付値の延長 v̂ の核）** — s が Cauchy で、その
    N=k+1 での Cauchy 閾値 M において v(s_M)=k（有限）なら、n≥M で v(sₙ)=k で一定。
    すなわち非零 Cauchy 列の付値は最終的に一定値 v₀=k に安定し、これが完備化 K̂ 上の付値
    v̂（Cauchy 列の安定値）の本物の核である。 -/
theorem locRing_cauchy_stable {K : IUTField} (val : valRingValuation K)
    (s : Nat → K.carrier) (k : Int) (M : Nat)
    (hmod : ∀ m n, M ≤ m → M ≤ n →
      valOptLe (some (k + 1)) (val.v (K.add (s m) (K.neg (s n)))))
    (hbase : val.v (s M) = some k) :
    ∀ n, M ≤ n → val.v (s n) = some k := by
  intro n hn
  have hb : valOptLe (some (k + 1)) (val.v (K.add (s n) (K.neg (s M)))) :=
    hmod n M hn (Nat.le_refl M)
  have hdom := locRing_val_dominant val (s M) (K.add (s n) (K.neg (s M))) k hbase hb
  have hrec : K.add (s M) (K.add (s n) (K.neg (s M))) = s n := by
    rw [K.add_comm (s M) (K.add (s n) (K.neg (s M)))]
    exact locRing_add_sub_cancel K (s n) (s M)
  rw [hrec] at hdom
  exact hdom

/-- **M311F-12d: 逆元の差** — x⁻¹ − y⁻¹ = (y − x)·(x⁻¹·y⁻¹)（x,y≠0・体の恒等式）。 -/
theorem locRing_inv_diff (K : IUTField) (x y : K.carrier)
    (hx : x ≠ K.zero) (hy : y ≠ K.zero) :
    K.add (K.inv x) (K.neg (K.inv y))
      = K.mul (K.add y (K.neg x)) (K.mul (K.inv x) (K.inv y)) := by
  have e1 : K.mul y (K.mul (K.inv x) (K.inv y)) = K.inv x := by
    rw [← K.mul_assoc y (K.inv x) (K.inv y), K.mul_comm y (K.inv x),
      K.mul_assoc (K.inv x) y (K.inv y), K.mul_inv_cancel y hy, valRingMulOne K (K.inv x)]
  have e2 : K.mul x (K.mul (K.inv x) (K.inv y)) = K.inv y := by
    rw [← K.mul_assoc x (K.inv x) (K.inv y), K.mul_inv_cancel x hx, K.one_mul]
  rw [K.toCRing.right_distrib y (K.neg x) (K.mul (K.inv x) (K.inv y)), e1,
    locRing_neg_mul K x (K.mul (K.inv x) (K.inv y)), e2]

/-- **M311F-12e: 逆元列の Cauchy 性（K̂ が体である核）** — s が Cauchy で、その付値が
    n≥M で有限値 k に安定する（各 sₙ≠0）なら、逆元列 (sₙ⁻¹) も Cauchy。
    v(sₘ⁻¹−sₙ⁻¹)=v(sₙ−sₘ)−2k を §12d/§12a/§2 で評価する。非零元の可逆性（K̂ が体）の
    本物の核であり、inv の類レベル全域化は後続（正直な限定）。 -/
theorem locRing_inv_cauchy {K : IUTField} (val : valRingValuation K)
    (s : Nat → K.carrier) (k : Int) (M : Nat) (hs : locCompCauchy val s)
    (hstab : ∀ n, M ≤ n → val.v (s n) = some k) :
    locCompCauchy val (fun n => K.inv (s n)) := by
  intro N
  obtain ⟨M0, hM0⟩ := hs (N + 2 * k)
  refine ⟨M + M0, ?_⟩
  intro m n hm hn
  have hmM : M ≤ m := by omega
  have hnM : M ≤ n := by omega
  have hmM0 : M0 ≤ m := by omega
  have hnM0 : M0 ≤ n := by omega
  have hsm : s m ≠ K.zero := by
    intro h
    have hh := hstab m hmM
    rw [h, val.v_zero] at hh
    nomatch hh
  have hsn : s n ≠ K.zero := by
    intro h
    have hh := hstab n hnM
    rw [h, val.v_zero] at hh
    nomatch hh
  have hvim : val.v (K.inv (s m)) = some (-k) := locRing_v_inv val (s m) k hsm (hstab m hmM)
  have hvin : val.v (K.inv (s n)) = some (-k) := locRing_v_inv val (s n) k hsn (hstab n hnM)
  show valOptLe (some N) (val.v (K.add (K.inv (s m)) (K.neg (K.inv (s n)))))
  rw [locRing_inv_diff K (s m) (s n) hsm hsn]
  have hdiff : valOptLe (some (N + 2 * k)) (val.v (K.add (s n) (K.neg (s m)))) :=
    hM0 n m hnM0 hmM0
  have hprod : valOptLe (some (-2 * k)) (val.v (K.mul (K.inv (s m)) (K.inv (s n)))) := by
    rw [val.v_mul, hvim, hvin, valOptAdd_some_some]
    show (-2 * k) ≤ (-k) + (-k)
    omega
  have hmain := locRing_v_mul_ge val (K.add (s n) (K.neg (s m)))
    (K.mul (K.inv (s m)) (K.inv (s n))) (N + 2 * k) (-2 * k) hdiff hprod
  have heq : (N + 2 * k) + (-2 * k) = N := by omega
  rw [heq] at hmain
  exact hmain

/-! ## M311F-13: capstone — 完備局所環データ -/

/-- **M311F-13a: 完備局所環データ** — 体 K・離散付値 val と、完備化 K̂ の**環準同型埋め込み**
    K↪K̂（加法・乗法・1 保存・単射）を束ねる。K̂ が可換環であることは `locRingCompletionRing`
    が保証する。 -/
structure LocalFieldRingData (K : IUTField) where
  /-- 台となる離散付値。 -/
  val : valRingValuation K
  /-- 埋め込みが加法を保存。 -/
  embed_add : ∀ a b, locRingEmbed val (K.add a b)
    = locRingAdd val (locRingEmbed val a) (locRingEmbed val b)
  /-- 埋め込みが乗法を保存。 -/
  embed_mul : ∀ a b, locRingEmbed val (K.mul a b)
    = locRingMul val (locRingEmbed val a) (locRingEmbed val b)
  /-- 埋め込みが 1 を保存。 -/
  embed_one : locRingEmbed val K.one = (locRingCompletionRing val).one
  /-- 埋め込みが単射。 -/
  embed_inj : ∀ a b, locRingEmbed val a = locRingEmbed val b → a = b

/-- **M311F-13b: 任意の離散付値から完備局所環データを組み立てる**。 -/
def locRing_toData {K : IUTField} (val : valRingValuation K) : LocalFieldRingData K where
  val := val
  embed_add := locRing_embed_add val
  embed_mul := locRing_embed_mul val
  embed_one := locRing_embed_one val
  embed_inj := locRing_embed_inj val

/-- **M311F-13c: 完備局所環データは存在する**（DecidableEq を持つ体上、自明付値から）。 -/
theorem locRing_exists (K : IUTField) [DecidableEq K.carrier] :
    Nonempty (LocalFieldRingData K) :=
  ⟨locRing_toData (trivialValuation K)⟩

/-- **M311F-13d: 完備化 K̂ は可換環**（総括・本物）。 -/
theorem locRing_completion_isCRing {K : IUTField} (val : valRingValuation K) :
    Nonempty CRing :=
  ⟨locRingCompletionRing val⟩

/-- **M311F-13e: 埋め込みは環準同型**（加法・乗法・1 保存を束ねた総括）。 -/
theorem locRing_embed_isHom {K : IUTField} (val : valRingValuation K) :
    (∀ a b, locRingEmbed val (K.add a b)
      = locRingAdd val (locRingEmbed val a) (locRingEmbed val b))
    ∧ (∀ a b, locRingEmbed val (K.mul a b)
      = locRingMul val (locRingEmbed val a) (locRingEmbed val b))
    ∧ locRingEmbed val K.one = (locRingCompletionRing val).one :=
  ⟨locRing_embed_add val, locRing_embed_mul val, locRing_embed_one val⟩

/-- **M311F-13f: 実例（自明付値の完備化 K̂）** — 自明付値では K は既に完備（M306F
    `locComp_trivial_complete`）であり K̂≅K だが、本ファイルの構成でも完備化 K̂ は本物の
    可換環をなす。**本物の体 K・本物の自明付値を主語**とする実例（toy 主語ではない）。
    K̂≅K の全同型（環同型・逆向き）は後続。 -/
def locRing_trivial_completion (K : IUTField) [DecidableEq K.carrier] : CRing :=
  locRingCompletionRing (trivialValuation K)

end IUT
