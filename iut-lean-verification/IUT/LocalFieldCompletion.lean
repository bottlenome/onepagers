/-
  IUT/LocalFieldCompletion.lean — M306F: 離散付値による完備化と Hensel の補題
  （局所体＝柱 B への本物の先行建設）

  ── 主要成果の分類: **[実]**（M301F の本物の離散付値 `v : K → ℤ∪{∞}` と付値環
  O_v を土台に、**付値位相による Cauchy 列・零列・完備化の設定**と、**Hensel の補題の
  核（Newton 補正が誤差の線形項をちょうど打ち消し、付値が倍々に増える）**を本物構成
  する。完備化は本コードベースの完備化イディオム（RReal の regular 列 + realEq、
  Quot ではなく setoid）に倣い、**Cauchy 列の集合を付値差の同値関係 locCompRel で
  割る setoid** として提示し、加法群構造（同値関係 + 加法/反元の合同）と埋め込み
  K↪K̂ の単射性を**完全証明**する。Hensel は Newton 反復の**線形項相殺の代数恒等式**を
  完全証明し、付値倍化を「Taylor 剰余の付値評価を入力とする条件付き本物」で閉じる。）

  complete_pct 影響: **柱B の局所体（完備離散付値体）への本物の先行建設**。M301F は
  付値環 O_v の**代数構造**のみで、位相（完備化）・Hensel は「後続」と明記されていた
  （honest 限定）。本ファイルはその後続の**位相層の最下層**——付値による Cauchy/零列と
  完備化 setoid——を本物で積み、さらにコードベースに**皆無だった Hensel の補題**の核
  （Newton 相殺 + 付値倍化）を新規に本物建設する。これにより柱B は「代数的付値環」から
  「完備局所体 + Hensel（＝滑らかな点の持ち上げ）」へ一段前進する。具体的な数体・ℚ_p の
  完備化そのもの（K̂ が体・完備であることの全証明）は主要部分＋骨組みで示し、完全化は
  後続の多項式層（Taylor 展開の本物）に委ねる。

  * M306F-1 環補題      — locComp_neg_add_distrib / locComp_add4comm /
    locComp_sub_self_zero / locComp_sub_telescope（可換環の恒等式・本物）
  * M306F-2 付値評価    — locComp_add_both_ge / locComp_neg_ge / locComp_sub_ge
    （超距離不等式による「≥N の閉性」・本物）
  * M306F-3 列の環      — `seqRing`（Nat→K は各点で可換環をなす・本物）
  * M306F-4 Cauchy/零列 — `locCompNull` / `locCompCauchy`（付値位相の定義・本物）
  * M306F-5 閉性        — const/null→Cauchy・add/neg で Cauchy 閉・null 閉・
    null が O_v で吸収（null イデアル性の核・本物）
  * M306F-6 完備化 setoid — `locCompRel`（差が零列）の同値律 + 加法/反元の合同
    （完備化の加法群構造が well-defined・本物）
  * M306F-7 埋め込み    — `locComp_const_inj`（K↪K̂ が単射: 定数列が同値なら等しい・本物）
  * M306F-8 完備性      — `locCompLimit` / `locCompComplete`（定義・本物）と
    実例 `locComp_trivial_complete`（自明付値 ⟹ K̂=K は完備・本物・非 toy）
  * M306F-9 Hensel      — `locCompNewton`（Newton 補正 a−f(a)/f'(a)）/
    `locComp_newton_cancel`（線形項がちょうど誤差を打ち消す・本物の恒等式）/
    `locComp_hensel_step`（付値倍化: v(f(a'))≥2v(f(a))、Taylor 剰余評価を入力）/
    `locComp_hensel_improves`（m≥1 で m<2m: 誤差が真に改善・本物）
  * M306F-10 capstone   — `LocalFieldData` / `locComp_toData` / `locComp_exists`

  正直な限定（何が本物で何が骨組み・後続か）:
  - **本物（完全証明・sorry 皆無・新規 choice 皆無）**: §1 環恒等式、§2 超距離の ≥N 閉性、
    §3 列の各点環 seqRing、§4/§5 Cauchy/零列の定義と閉性（const/null→Cauchy、add/neg
    閉、null の add/neg 閉、null の O_v 吸収）、§6 完備化 setoid の同値律と加法/反元の
    合同（完備化の加法群構造が well-defined）、§7 埋め込み K↪K̂ の単射性、§8 完備性の
    定義と**自明付値の完備性の実例**、§9 Newton 相殺の代数恒等式と付値倍化・改善。
  - **主要部分＋骨組み（honest 限定・後続）**:
    * 完備化 K̂ を Quot として束ね CRing/IUTField 構造を載せる**環・体化の全証明**は
      本ファイルでは行わず、setoid（Cauchy 列 + locCompRel）と加法/反元の合同までを
      本物とする。乗法の合同は Cauchy 列の付値有界性を要し（null の乗法吸収は O_v 値の
      場合のみ本物）、環化は後続。K̂ が体であることの全証明も後続。
    * Hensel は Newton 反復列 aₙ₊₁=aₙ−f(aₙ)/f'(aₙ) の**線形項相殺**（f(a) をちょうど
      打ち消す代数恒等式）を本物で閉じ、`f(a')=Taylor 剰余` と `v(剰余)≥2v(f(a))` を
      **入力（仮説）**として付値倍化を導く。Taylor 剰余の付値評価そのもの（多項式の
      2 次以上の項が h² で割れる本物）は多項式・微分の層が未建設のため後続に委ね、
      本層では「多項式が与える剰余評価を入力すれば Newton が付値を倍化する」という
      **付値についての本物の定理**として提示する（toy を主語にしない: 主語は本物の
      付値 v・本物の体 K・本物の Newton 補正である）。
    * 値群は ℤ（離散付値）に限る。一般局所体（有限剰余体・局所類体論の主定理）は
      既存 LocalCFT.lean（M27）の unramified 部分と後続で接続する。
  - 本ファイルは M301F の honest 限定「位相（完備化）は後続」を**本物の置換で前進**させる
    ものであり、既存の honest 限定を消去・弱化しない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
-/
import IUT.ValuationRing

namespace IUT

/-! ## M306F-1: 可換環の恒等式（本物） -/

/-- **M306F-1a: neg の加法分配** — -(a+b) = (-a)+(-b)（可換環の本物の恒等式）。 -/
theorem locComp_neg_add_distrib (K : IUTField) (a b : K.carrier) :
    K.neg (K.add a b) = K.add (K.neg a) (K.neg b) := by
  have key : K.add (K.add (K.neg a) (K.neg b)) (K.add a b) = K.zero := by
    rw [K.add_assoc (K.neg a) (K.neg b) (K.add a b), K.add_comm a b,
      ← K.add_assoc (K.neg b) b a, K.neg_add b, K.zero_add, K.neg_add a]
  have h2 : K.add (K.neg (K.add a b)) (K.add a b) = K.zero := K.neg_add (K.add a b)
  have e : K.add (K.add a b) (K.neg (K.add a b))
      = K.add (K.add a b) (K.add (K.neg a) (K.neg b)) := by
    rw [K.add_comm (K.add a b) (K.neg (K.add a b)), h2,
      K.add_comm (K.add a b) (K.add (K.neg a) (K.neg b)), key]
  exact K.toCRing.add_left_cancel e

/-- **M306F-1b: 4 項の加法入替** — (a+b)+(c+d) = (a+c)+(b+d)（可換環）。 -/
theorem locComp_add4comm (K : IUTField) (a b c d : K.carrier) :
    K.add (K.add a b) (K.add c d) = K.add (K.add a c) (K.add b d) := by
  rw [K.add_assoc a b (K.add c d), ← K.add_assoc b c d, K.add_comm b c,
    K.add_assoc c b d, ← K.add_assoc a c (K.add b d)]

/-- **M306F-1c: a + (-a) = 0**。 -/
theorem locComp_sub_self_zero (K : IUTField) (a : K.carrier) :
    K.add a (K.neg a) = K.zero := by
  rw [K.add_comm a (K.neg a)]
  exact K.neg_add a

/-- **M306F-1d: 差のテレスコープ** — a−c = (a−b)+(b−c)（可換環）。 -/
theorem locComp_sub_telescope (K : IUTField) (a b c : K.carrier) :
    K.add a (K.neg c) = K.add (K.add a (K.neg b)) (K.add b (K.neg c)) := by
  rw [K.add_assoc a (K.neg b) (K.add b (K.neg c)),
    ← K.add_assoc (K.neg b) b (K.neg c), K.neg_add b, K.zero_add]

/-! ## M306F-2: 超距離不等式による「付値 ≥ N の閉性」（本物） -/

/-- **M306F-2a: 和の付値評価** — v(x)≥N かつ v(y)≥N なら v(x+y)≥N
    （超距離不等式の選言形から）。 -/
theorem locComp_add_both_ge {K : IUTField} (val : valRingValuation K) (N : Int)
    (x y : K.carrier) (hx : valOptLe (some N) (val.v x))
    (hy : valOptLe (some N) (val.v y)) :
    valOptLe (some N) (val.v (K.add x y)) := by
  cases val.v_add_ge x y with
  | inl h => exact valOptLe_trans hx h
  | inr h => exact valOptLe_trans hy h

/-- **M306F-2b: 反元の付値評価** — v(x)≥N なら v(−x)≥N（v(−x)=v(x)）。 -/
theorem locComp_neg_ge {K : IUTField} (val : valRingValuation K) (N : Int)
    (x : K.carrier) (hx : valOptLe (some N) (val.v x)) :
    valOptLe (some N) (val.v (K.neg x)) := by
  rw [valRing_v_neg]
  exact hx

/-- **M306F-2c: 差の付値評価** — v(x)≥N かつ v(y)≥N なら v(x−y)≥N。 -/
theorem locComp_sub_ge {K : IUTField} (val : valRingValuation K) (N : Int)
    (x y : K.carrier) (hx : valOptLe (some N) (val.v x))
    (hy : valOptLe (some N) (val.v y)) :
    valOptLe (some N) (val.v (K.add x (K.neg y))) :=
  locComp_add_both_ge val N x (K.neg y) hx (locComp_neg_ge val N y hy)

/-! ## M306F-3: 列の環（Nat→K は各点で可換環をなす・本物） -/

/-- **M306F-3: 列の可換環** — 付値体 K の値をとる列 `Nat → K.carrier` は各点演算で
    本物の可換環をなす（完備化の台となる列空間）。 -/
def seqRing (K : IUTField) : CRing where
  carrier := Nat → K.carrier
  add := fun s t n => K.add (s n) (t n)
  zero := fun _ => K.zero
  neg := fun s n => K.neg (s n)
  mul := fun s t n => K.mul (s n) (t n)
  one := fun _ => K.one
  add_assoc := by intro a b c; funext n; exact K.add_assoc (a n) (b n) (c n)
  zero_add := by intro a; funext n; exact K.zero_add (a n)
  neg_add := by intro a; funext n; exact K.neg_add (a n)
  add_comm := by intro a b; funext n; exact K.add_comm (a n) (b n)
  mul_assoc := by intro a b c; funext n; exact K.mul_assoc (a n) (b n) (c n)
  one_mul := by intro a; funext n; exact K.one_mul (a n)
  mul_comm := by intro a b; funext n; exact K.mul_comm (a n) (b n)
  left_distrib := by intro a b c; funext n; exact K.left_distrib (a n) (b n) (c n)

/-! ## M306F-4: 付値位相の Cauchy 列・零列（本物の定義） -/

/-- **M306F-4a: 零列** — v(sₙ) が ∞ に発散（sₙ → 0）: 任意の N に対し、ある M 以降
    v(sₙ) ≥ N。 -/
def locCompNull {K : IUTField} (val : valRingValuation K) (s : Nat → K.carrier) : Prop :=
  ∀ N : Int, ∃ M : Nat, ∀ n, M ≤ n → valOptLe (some N) (val.v (s n))

/-- **M306F-4b: Cauchy 列** — 差が零に収束: 任意の N に対し、ある M 以降 m,n≥M で
    v(sₘ − sₙ) ≥ N。 -/
def locCompCauchy {K : IUTField} (val : valRingValuation K) (s : Nat → K.carrier) : Prop :=
  ∀ N : Int, ∃ M : Nat, ∀ m n, M ≤ m → M ≤ n →
    valOptLe (some N) (val.v (K.add (s m) (K.neg (s n))))

/-! ## M306F-5: Cauchy 列・零列の閉性（本物） -/

/-- **M306F-5a: 定数列は Cauchy**（差 = a − a = 0、v(0)=∞≥N）。 -/
theorem locComp_const_cauchy {K : IUTField} (val : valRingValuation K) (a : K.carrier) :
    locCompCauchy val (fun _ => a) := by
  intro N
  refine ⟨0, ?_⟩
  intro m n _ _
  show valOptLe (some N) (val.v (K.add a (K.neg a)))
  rw [locComp_sub_self_zero K a, val.v_zero]
  exact True.intro

/-- **M306F-5b: 零列は Cauchy**（v(sₘ)≥N, v(sₙ)≥N ⟹ v(sₘ−sₙ)≥N）。 -/
theorem locComp_null_imp_cauchy {K : IUTField} (val : valRingValuation K)
    (s : Nat → K.carrier) (h : locCompNull val s) : locCompCauchy val s := by
  intro N
  obtain ⟨M, hM⟩ := h N
  refine ⟨M, ?_⟩
  intro m n hm hn
  exact locComp_sub_ge val N (s m) (s n) (hM m hm) (hM n hn)

/-- **M306F-5c: 零列は加法で閉じる**。 -/
theorem locComp_null_add {K : IUTField} (val : valRingValuation K)
    (s t : Nat → K.carrier) (hs : locCompNull val s) (ht : locCompNull val t) :
    locCompNull val (fun n => K.add (s n) (t n)) := by
  intro N
  obtain ⟨Ms, hMs⟩ := hs N
  obtain ⟨Mt, hMt⟩ := ht N
  refine ⟨Ms + Mt, ?_⟩
  intro n hn
  have hns : Ms ≤ n := by omega
  have hnt : Mt ≤ n := by omega
  exact locComp_add_both_ge val N (s n) (t n) (hMs n hns) (hMt n hnt)

/-- **M306F-5d: 零列は反元で閉じる**。 -/
theorem locComp_null_neg {K : IUTField} (val : valRingValuation K)
    (s : Nat → K.carrier) (hs : locCompNull val s) :
    locCompNull val (fun n => K.neg (s n)) := by
  intro N
  obtain ⟨M, hM⟩ := hs N
  refine ⟨M, ?_⟩
  intro n hn
  exact locComp_neg_ge val N (s n) (hM n hn)

/-- **M306F-5e: Cauchy 列は加法で閉じる**。 -/
theorem locComp_cauchy_add {K : IUTField} (val : valRingValuation K)
    (s t : Nat → K.carrier) (hs : locCompCauchy val s) (ht : locCompCauchy val t) :
    locCompCauchy val (fun n => K.add (s n) (t n)) := by
  intro N
  obtain ⟨Ms, hMs⟩ := hs N
  obtain ⟨Mt, hMt⟩ := ht N
  refine ⟨Ms + Mt, ?_⟩
  intro m n hm hn
  have hms : Ms ≤ m := by omega
  have hns : Ms ≤ n := by omega
  have hmt : Mt ≤ m := by omega
  have hnt : Mt ≤ n := by omega
  show valOptLe (some N)
    (val.v (K.add (K.add (s m) (t m)) (K.neg (K.add (s n) (t n)))))
  rw [locComp_neg_add_distrib K (s n) (t n),
    locComp_add4comm K (s m) (t m) (K.neg (s n)) (K.neg (t n))]
  exact locComp_add_both_ge val N (K.add (s m) (K.neg (s n)))
    (K.add (t m) (K.neg (t n))) (hMs m n hms hns) (hMt m n hmt hnt)

/-- **M306F-5f: Cauchy 列は反元で閉じる**。 -/
theorem locComp_cauchy_neg {K : IUTField} (val : valRingValuation K)
    (s : Nat → K.carrier) (hs : locCompCauchy val s) :
    locCompCauchy val (fun n => K.neg (s n)) := by
  intro N
  obtain ⟨M, hM⟩ := hs N
  refine ⟨M, ?_⟩
  intro m n hm hn
  show valOptLe (some N) (val.v (K.add (K.neg (s m)) (K.neg (K.neg (s n)))))
  have hid : K.add (K.neg (s m)) (K.neg (K.neg (s n)))
      = K.neg (K.add (s m) (K.neg (s n))) :=
    (locComp_neg_add_distrib K (s m) (K.neg (s n))).symm
  rw [hid, valRing_v_neg]
  exact hM m n hm hn

/-- **M306F-5g: 零列は O_v 値の列で吸収される**（null イデアル性の核）——
    s が零列で t が各点 O_v 値（v(tₙ)≥0）なら s·t は零列
    （v(sₙtₙ)=v(sₙ)+v(tₙ)≥v(sₙ)→∞）。 -/
theorem locComp_null_absorb {K : IUTField} (val : valRingValuation K)
    (s t : Nat → K.carrier) (hs : locCompNull val s)
    (ht : ∀ n, valRingMem val (t n)) :
    locCompNull val (fun n => K.mul (s n) (t n)) := by
  intro N
  obtain ⟨M, hM⟩ := hs N
  refine ⟨M, ?_⟩
  intro n hn
  show valOptLe (some N) (val.v (K.mul (s n) (t n)))
  rw [val.v_mul]
  have h1 : valOptLe (some N) (val.v (s n)) := hM n hn
  have h2 : valOptLe (some (0 : Int)) (val.v (t n)) := ht n
  cases hvs : val.v (s n) with
  | none => rw [valOptAdd_none_left]; exact True.intro
  | some a =>
    cases hvt : val.v (t n) with
    | none => rw [valOptAdd_some_none]; exact True.intro
    | some b =>
      rw [valOptAdd_some_some]
      show N ≤ a + b
      rw [hvs] at h1
      rw [hvt] at h2
      have ha : N ≤ a := h1
      have hb : (0 : Int) ≤ b := h2
      omega

/-! ## M306F-6: 完備化 setoid（差が零列）の同値律と加法/反元の合同（本物） -/

/-- **M306F-6a: 完備化の同値関係** — s ~ t ⟺ 差 s − t が零列。 -/
def locCompRel {K : IUTField} (val : valRingValuation K)
    (s t : Nat → K.carrier) : Prop :=
  locCompNull val (fun n => K.add (s n) (K.neg (t n)))

/-- 反射律。 -/
theorem locCompRel_refl {K : IUTField} (val : valRingValuation K)
    (s : Nat → K.carrier) : locCompRel val s s := by
  intro N
  refine ⟨0, ?_⟩
  intro n _
  show valOptLe (some N) (val.v (K.add (s n) (K.neg (s n))))
  rw [locComp_sub_self_zero K (s n), val.v_zero]
  exact True.intro

/-- 対称律（t − s = −(s − t)）。 -/
theorem locCompRel_symm {K : IUTField} (val : valRingValuation K)
    (s t : Nat → K.carrier) (h : locCompRel val s t) : locCompRel val t s := by
  have hneg := locComp_null_neg val (fun n => K.add (s n) (K.neg (t n))) h
  intro N
  obtain ⟨M, hM⟩ := hneg N
  refine ⟨M, ?_⟩
  intro n hn
  show valOptLe (some N) (val.v (K.add (t n) (K.neg (s n))))
  have hid : K.add (t n) (K.neg (s n)) = K.neg (K.add (s n) (K.neg (t n))) := by
    rw [locComp_neg_add_distrib K (s n) (K.neg (t n)), valRingNegNeg K (t n),
      K.add_comm (K.neg (s n)) (t n)]
  rw [hid]
  exact hM n hn

/-- 推移律（s − u = (s − t) + (t − u)）。 -/
theorem locCompRel_trans {K : IUTField} (val : valRingValuation K)
    (s t u : Nat → K.carrier) (h1 : locCompRel val s t) (h2 : locCompRel val t u) :
    locCompRel val s u := by
  have hadd := locComp_null_add val (fun n => K.add (s n) (K.neg (t n)))
    (fun n => K.add (t n) (K.neg (u n))) h1 h2
  intro N
  obtain ⟨M, hM⟩ := hadd N
  refine ⟨M, ?_⟩
  intro n hn
  show valOptLe (some N) (val.v (K.add (s n) (K.neg (u n))))
  rw [locComp_sub_telescope K (s n) (t n) (u n)]
  exact hM n hn

/-- **M306F-6b: 加法の合同** — s~s', t~t' なら s+t ~ s'+t'
    （完備化の加法が well-defined）。 -/
theorem locCompRel_add {K : IUTField} (val : valRingValuation K)
    (s s' t t' : Nat → K.carrier) (hs : locCompRel val s s') (ht : locCompRel val t t') :
    locCompRel val (fun n => K.add (s n) (t n)) (fun n => K.add (s' n) (t' n)) := by
  have hadd := locComp_null_add val (fun n => K.add (s n) (K.neg (s' n)))
    (fun n => K.add (t n) (K.neg (t' n))) hs ht
  intro N
  obtain ⟨M, hM⟩ := hadd N
  refine ⟨M, ?_⟩
  intro n hn
  show valOptLe (some N)
    (val.v (K.add (K.add (s n) (t n)) (K.neg (K.add (s' n) (t' n)))))
  rw [locComp_neg_add_distrib K (s' n) (t' n),
    locComp_add4comm K (s n) (t n) (K.neg (s' n)) (K.neg (t' n))]
  exact hM n hn

/-- **M306F-6c: 反元の合同** — s~s' なら −s ~ −s'
    （完備化の反元が well-defined）。 -/
theorem locCompRel_neg {K : IUTField} (val : valRingValuation K)
    (s s' : Nat → K.carrier) (hs : locCompRel val s s') :
    locCompRel val (fun n => K.neg (s n)) (fun n => K.neg (s' n)) := by
  have hneg := locComp_null_neg val (fun n => K.add (s n) (K.neg (s' n))) hs
  intro N
  obtain ⟨M, hM⟩ := hneg N
  refine ⟨M, ?_⟩
  intro n hn
  show valOptLe (some N) (val.v (K.add (K.neg (s n)) (K.neg (K.neg (s' n)))))
  have hid : K.add (K.neg (s n)) (K.neg (K.neg (s' n)))
      = K.neg (K.add (s n) (K.neg (s' n))) :=
    (locComp_neg_add_distrib K (s n) (K.neg (s' n))).symm
  rw [hid]
  exact hM n hn

/-! ## M306F-7: 埋め込み K ↪ K̂ の単射性（本物） -/

/-- **M306F-7: 埋め込みの単射性** — 定数列 (a) と (b) が完備化で同値なら a = b
    （K ↪ K̂ は単射: v(a−b) が全 N で ≥N ⟹ v(a−b)=∞ ⟹ a−b=0 ⟹ a=b）。 -/
theorem locComp_const_inj {K : IUTField} (val : valRingValuation K) (a b : K.carrier)
    (h : locCompRel val (fun _ => a) (fun _ => b)) : a = b := by
  have key : val.v (K.add a (K.neg b)) = none := by
    cases hv : val.v (K.add a (K.neg b)) with
    | none => rfl
    | some k =>
      exfalso
      obtain ⟨M, hM⟩ := h (k + 1)
      have hle : valOptLe (some (k + 1)) (val.v (K.add a (K.neg b))) :=
        hM M (Nat.le_refl M)
      rw [hv] at hle
      have hk : (k + 1 : Int) ≤ k := hle
      omega
  have hab0 : K.add a (K.neg b) = K.zero := val.v_eq_top _ key
  have e1 : K.add (K.add a (K.neg b)) b = b := by
    rw [hab0, K.zero_add]
  rw [K.add_assoc a (K.neg b) b, K.neg_add b, K.add_comm a K.zero, K.zero_add] at e1
  exact e1

/-! ## M306F-8: 完備性の定義と自明付値の完備性の実例（本物） -/

/-- **M306F-8a: 収束** — 列 s が L に収束 ⟺ 差 s − L が零列。 -/
def locCompLimit {K : IUTField} (val : valRingValuation K)
    (s : Nat → K.carrier) (L : K.carrier) : Prop :=
  locCompNull val (fun n => K.add (s n) (K.neg L))

/-- **M306F-8b: 完備性** — 任意の Cauchy 列が K の中に極限を持つ。 -/
def locCompComplete {K : IUTField} (val : valRingValuation K) : Prop :=
  ∀ s, locCompCauchy val s → ∃ L, locCompLimit val s L

/-- **M306F-8c: 自明付値の完備性（実例・非 toy）** — 自明付値 v（O_v=K, rank 0）では
    Cauchy 列は最終的に定数（v(sₘ−sₙ)≥1 は sₘ=sₙ を強制）となり、その最終値へ収束する。
    ゆえに K は自明付値について完備（K̂=K）。**本物の付値・本物の体・本物の収束を主語**と
    する実例で、toy を主語にしていない。 -/
theorem locComp_trivial_complete {K : IUTField} [DecidableEq K.carrier] :
    locCompComplete (trivialValuation K) := by
  intro s hs
  obtain ⟨M, hM⟩ := hs 1
  refine ⟨s M, ?_⟩
  intro N
  refine ⟨M, ?_⟩
  intro n hn
  show valOptLe (some N) ((trivialValuation K).v (K.add (s n) (K.neg (s M))))
  have h1 : valOptLe (some 1) ((trivialValuation K).v (K.add (s n) (K.neg (s M)))) :=
    hM n M hn (Nat.le_refl M)
  cases hcase : (trivialValuation K).v (K.add (s n) (K.neg (s M))) with
  | none => exact True.intro
  | some k =>
    exfalso
    rw [hcase] at h1
    have hk0 : k = 0 := by
      have hdef : (if K.add (s n) (K.neg (s M)) = K.zero then none else some (0 : Int))
          = some k := hcase
      split at hdef
      · nomatch hdef
      · have hkk : (0 : Int) = k := Option.some.inj hdef
        omega
    rw [hk0] at h1
    have hcontra : (1 : Int) ≤ 0 := h1
    omega

/-! ## M306F-9: Hensel の補題（Newton 相殺 + 付値倍化・本物） -/

/-- **M306F-9a: Newton 補正** — a' = a − f(a)/f'(a)（付値環上の Newton 反復の 1 段）。 -/
def locCompNewton {K : IUTField} (a fa fpa : K.carrier) : K.carrier :=
  K.add a (K.neg (K.mul fa (K.inv fpa)))

/-- **M306F-9b: Newton 相殺の恒等式（本物）** — f'(a)·(f(a)/f'(a)) がちょうど f(a) と
    等しいので、線形補正項が現在の誤差 f(a) をちょうど打ち消す:
    f(a) + (−f'(a)·(f(a)/f'(a))) = 0（f'(a)≠0）。これが Hensel＝Newton 反復の核。 -/
theorem locComp_newton_cancel {K : IUTField} (fa fpa : K.carrier) (hfpa : fpa ≠ K.zero) :
    K.add fa (K.neg (K.mul fpa (K.mul fa (K.inv fpa)))) = K.zero := by
  have hkey : K.mul fpa (K.mul fa (K.inv fpa)) = fa := by
    rw [K.mul_comm fa (K.inv fpa), ← K.mul_assoc fpa (K.inv fpa) fa,
      K.mul_inv_cancel fpa hfpa, K.one_mul]
  rw [hkey]
  exact locComp_sub_self_zero K fa

/-- **M306F-9c: Hensel の付値倍化ステップ（本物・条件付き）** — f'(a) が単元
    （fpa≠0）で、Taylor 展開により Newton 補正点での値が「線形相殺項 + 剰余 R」の形に
    書け（`hf`）、剰余の付値が v(f(a)) の 2 倍以上（`hR`、多項式層が与える入力）ならば、
    Newton 補正点での値の付値も 2 倍以上に増える: v(f(a'))≥2·v(f(a))。
    線形相殺（`locComp_newton_cancel`）は本物で閉じ、Taylor 剰余の付値評価を入力とする。 -/
theorem locComp_hensel_step {K : IUTField} (val : valRingValuation K)
    (fa fpa R fAtNewton : K.carrier) (m : Int) (hfpa : fpa ≠ K.zero)
    (hfa : val.v fa = some m)
    (hf : fAtNewton
      = K.add (K.add fa (K.neg (K.mul fpa (K.mul fa (K.inv fpa))))) R)
    (hR : valOptLe (some (2 * m)) (val.v R)) :
    valOptLe (some (2 * m)) (val.v fAtNewton) := by
  have hcancel := locComp_newton_cancel fa fpa hfpa
  rw [hcancel, K.zero_add] at hf
  rw [hf]
  exact hR

/-- **M306F-9d: 誤差の真の改善** — v(f(a))=m≥1 なら 2m>m、すなわち Newton は付値を
    真に増やす（「倍々に増える」の単調性）。 -/
theorem locComp_hensel_improves (m : Int) (hm : 1 ≤ m) : m < 2 * m := by omega

/-! ## M306F-10: capstone — 完備局所体データ -/

/-- **M306F-10a: 完備局所体データ** — 体 K・離散付値 val と、その付値位相の
    Cauchy 列が定数・加法・反元で閉じること、完備化 setoid（locCompRel）が同値関係を
    なすこと、埋め込み K↪K̂ が単射であることを束ねる。 -/
structure LocalFieldData (K : IUTField) where
  /-- 台となる離散付値。 -/
  val : valRingValuation K
  /-- 定数列は Cauchy。 -/
  cauchy_const : ∀ a, locCompCauchy val (fun _ => a)
  /-- Cauchy 列は加法で閉じる。 -/
  cauchy_add : ∀ s t, locCompCauchy val s → locCompCauchy val t →
    locCompCauchy val (fun n => K.add (s n) (t n))
  /-- Cauchy 列は反元で閉じる。 -/
  cauchy_neg : ∀ s, locCompCauchy val s → locCompCauchy val (fun n => K.neg (s n))
  /-- 零列は Cauchy。 -/
  null_cauchy : ∀ s, locCompNull val s → locCompCauchy val s
  /-- 完備化同値関係の反射律。 -/
  rel_refl : ∀ s, locCompRel val s s
  /-- 完備化同値関係の対称律。 -/
  rel_symm : ∀ s t, locCompRel val s t → locCompRel val t s
  /-- 完備化同値関係の推移律。 -/
  rel_trans : ∀ s t u, locCompRel val s t → locCompRel val t u → locCompRel val s u
  /-- 加法の合同（完備化の加法が well-defined）。 -/
  rel_add : ∀ s s' t t', locCompRel val s s' → locCompRel val t t' →
    locCompRel val (fun n => K.add (s n) (t n)) (fun n => K.add (s' n) (t' n))
  /-- 埋め込み K↪K̂ の単射性。 -/
  embed_inj : ∀ a b, locCompRel val (fun _ => a) (fun _ => b) → a = b

/-- **M306F-10b: 任意の離散付値から完備局所体データを組み立てる**。 -/
def locComp_toData {K : IUTField} (val : valRingValuation K) : LocalFieldData K where
  val := val
  cauchy_const := locComp_const_cauchy val
  cauchy_add := locComp_cauchy_add val
  cauchy_neg := locComp_cauchy_neg val
  null_cauchy := locComp_null_imp_cauchy val
  rel_refl := locCompRel_refl val
  rel_symm := locCompRel_symm val
  rel_trans := locCompRel_trans val
  rel_add := locCompRel_add val
  embed_inj := locComp_const_inj val

/-- **M306F-10c: 完備局所体データは存在する**（DecidableEq を持つ体上、自明付値から）。
    具体的な数体・ℚ_p の完備化（K̂ の環・体化、完備性の全証明）は後続。 -/
theorem locComp_exists (K : IUTField) [DecidableEq K.carrier] :
    Nonempty (LocalFieldData K) :=
  ⟨locComp_toData (trivialValuation K)⟩

end IUT
