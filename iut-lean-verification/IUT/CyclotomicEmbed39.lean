/-
  IUT/CyclotomicEmbed39.lean — A3/W-C（CE39: 円分体の埋め込み
  ι: ℚ(ζ₃) ↪ ℚ(ζ₉)、x̄₃ ↦ x̄₉³）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・
     実円分体 ℚ(ζ₃)=ℚ[x]/(Φ₃) と ℚ(ζ₉)=ℚ[x]/(Φ₉) の上での本物の体埋め込み
     ι を、担体写像 (a+bx̄₃) ↦ (a+bx̄₉³) として構成し、環準同型性
     （加法・乗法・1 保存）を剰余簡約越しに完全証明する。乗法性は Φ₃ 簡約の
     余因子が**定数** q=u₁v₁（deg uv ≤ 2 = deg Φ₃）であることに帰着させ、
     一般 stretch 補題を回避して具体 3 係数計算で閉じる）。

  complete_pct 影響: A3（円分塔 res₁）への承認済み足場——K₁⊂K₂
  （ℚ(ζ₃)⊂ℚ(ζ₉)）の実体埋め込みで、res の意味論（ι∘res(σ)=σ∘ι）の左辺を
  供給する。本ファイル単体では complete_pct 未設定（W-C 完了＝CR39 で res を
  構成し独立監査で反映する）。

  内容（設計 audit/A3-cyclotomic-tower-detail-2026-07-09.md §2.2 CE39）:
   * `ce39Map` — 担体写像 (a+bx̄₃) ↦ (a+bx̄₉³)（明示係数・deg 1 ↦ deg 3 < 6）。
   * `ce39_map_add` / `ce39_map_mul` / `ce39_map_one` — 環準同型性
     （★乗法性は剰余簡約越し・余因子定数 q=psC(u₁v₁)）。
   * `ce39Iota` — RingHom cnfPhi3Field.toCRing p9iPhi9Field.toCRing。
   * `ce39_phi9_eq_phi3_cubed` — Φ₃(x³) = Φ_9 の係数照合。
   * `ce39_incl_compat` — ι ∘ incl₃ = incl₉（定数は不動）。
   * `ce39Ext` — FieldExtension（base=cnfPhi3Field, top=p9iPhi9Field, incl=ι）。

  正直な限定（§4 規約により消さない・追記のみ）:
   (i)   p = 3・ℚ 上・2 段（ℚ(ζ₃)⊂ℚ(ζ₉)）のみの忠実な部分ケース。
   (ii)  制限準同型 res の本体は CR39（`CyclotomicRes39.lean`）で構成する。
         本ファイルは埋め込み ι（K₁⊂K₂）と Φ₃(x³)=Φ_9・incl 適合まで。
   (iii) 「余因子が定数」という短絡は nf=2（deg Φ₃=2）に依存し、一般 n 段
         （M2）では一般 stretch 補題が改めて必要になる（手抜きでなく順序）。
   (iv)  ι の全射性・分離性・正規性の一般論は未形式化。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイルのみ（共有ファイル不更新・親が統合）。
-/
import IUT.CyclotomicField3
import IUT.Phi9Irreducible

namespace IUT

/-! ## CE39-0: 定数余因子 q = u₁v₁ と純代数補題 -/

/-- **CE39-0a: 余因子定数 q = u₁·v₁**（Φ₃ 簡約の商・deg uv ≤ 2 = deg Φ₃）。 -/
@[reducible] def ce39q (u v : GefNF cq0PS 2) : QRat := ratRing.mul (u.val 1) (v.val 1)

/-- **CE39-0b: 純代数補題** — a + (−(a + (−q))) = q（超距離でなく単なる群算術）。
    剰余簡約の各点照合で「w 側 − 余因子 = q」に効く。 -/
theorem ce39_alg (a q : QRat) :
    ratRing.add a (ratRing.neg (ratRing.add a (ratRing.neg q))) = q := by
  rw [CRing.neg_add_dist ratRing a (ratRing.neg q), CRing.neg_neg ratRing q,
    ← ratRing.add_assoc a (ratRing.neg a) q, CRing.add_neg ratRing a, ratRing.zero_add]

/-! ## CE39-1: 二単項式積の一般補題（gefSMS の分配展開） -/

/-- **CE39-1: 二単項式積** — (a₀ + a₁x^s)(b₀ + b₁x^t) の Cauchy 積は
    a₀b₀ + a₀b₁x^t + a₁b₀x^s + a₁b₁x^{s+t}（分配律 + `gefSMS`）。
    P = u·v（s=t=1）と w = ι(u)·ι(v)（s=t=3）の両方に使う。 -/
theorem two_single_mul (a0 a1 b0 b1 : QRat) (s t : Nat) :
    psMul ratRing
      (psAdd ratRing (psSingle ratRing a0 0) (psSingle ratRing a1 s))
      (psAdd ratRing (psSingle ratRing b0 0) (psSingle ratRing b1 t))
    = psAdd ratRing
        (psAdd ratRing (psSingle ratRing (ratRing.mul a0 b0) 0)
          (psSingle ratRing (ratRing.mul a0 b1) t))
        (psAdd ratRing (psSingle ratRing (ratRing.mul a1 b0) s)
          (psSingle ratRing (ratRing.mul a1 b1) (s + t))) := by
  rw [show psMul ratRing
        (psAdd ratRing (psSingle ratRing a0 0) (psSingle ratRing a1 s))
        (psAdd ratRing (psSingle ratRing b0 0) (psSingle ratRing b1 t))
      = psAdd ratRing
          (psMul ratRing (psSingle ratRing a0 0)
            (psAdd ratRing (psSingle ratRing b0 0) (psSingle ratRing b1 t)))
          (psMul ratRing (psSingle ratRing a1 s)
            (psAdd ratRing (psSingle ratRing b0 0) (psSingle ratRing b1 t)))
      from (psRing ratRing).right_distrib _ _ _,
    show psMul ratRing (psSingle ratRing a0 0)
          (psAdd ratRing (psSingle ratRing b0 0) (psSingle ratRing b1 t))
      = psAdd ratRing (psMul ratRing (psSingle ratRing a0 0) (psSingle ratRing b0 0))
          (psMul ratRing (psSingle ratRing a0 0) (psSingle ratRing b1 t))
      from (psRing ratRing).left_distrib _ _ _,
    show psMul ratRing (psSingle ratRing a1 s)
          (psAdd ratRing (psSingle ratRing b0 0) (psSingle ratRing b1 t))
      = psAdd ratRing (psMul ratRing (psSingle ratRing a1 s) (psSingle ratRing b0 0))
          (psMul ratRing (psSingle ratRing a1 s) (psSingle ratRing b1 t))
      from (psRing ratRing).left_distrib _ _ _]
  funext j
  show ratRing.add
      (ratRing.add (psMul ratRing (psSingle ratRing a0 0) (psSingle ratRing b0 0) j)
        (psMul ratRing (psSingle ratRing a0 0) (psSingle ratRing b1 t) j))
      (ratRing.add (psMul ratRing (psSingle ratRing a1 s) (psSingle ratRing b0 0) j)
        (psMul ratRing (psSingle ratRing a1 s) (psSingle ratRing b1 t) j))
    = ratRing.add
        (ratRing.add (psSingle ratRing (ratRing.mul a0 b0) 0 j)
          (psSingle ratRing (ratRing.mul a0 b1) t j))
        (ratRing.add (psSingle ratRing (ratRing.mul a1 b0) s j)
          (psSingle ratRing (ratRing.mul a1 b1) (s + t) j))
  rw [gefSMS a0 b0 0 0 j, gefSMS a0 b1 0 t j, gefSMS a1 b0 s 0 j, gefSMS a1 b1 s t j,
    Nat.zero_add t, Nat.add_zero s, Nat.add_zero 0]

/-! ## CE39-2: 担体写像 (a+bx̄₃) ↦ (a+bx̄₉³) と有界性・単項式分解 -/

/-- **CE39-2a: 担体写像の係数** — (a+bx̄₃)=(u₀,u₁) を (u₀,0,0,u₁,0,…) へ
    （0 次 ↦ 0 次・1 次 ↦ 3 次、deg 1 ↦ deg 3 < 6 で NF 簡約不要）。 -/
def ce39MapVal (u : GefNF cq0PS 2) : PS ratRing :=
  fun j => if j = 0 then u.val 0 else if j = 3 then u.val 1 else ratRing.zero

/-- **CE39-2b: 有界性** — ce39MapVal u は 6 有界（deg ≤ 3 < 6・台 ⊆ {0,3}）。 -/
theorem ce39MapVal_bnd (u : GefNF cq0PS 2) : IsPolyBounded ratRing (ce39MapVal u) 6 := by
  intro j hj
  show (if j = 0 then u.val 0 else if j = 3 then u.val 1 else ratRing.zero) = ratRing.zero
  rw [if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 3 by omega)]

/-- **CE39-2c: 担体元** — ce39Map u : GefNF cpdPhi9 6（= p9iPhi9Field.carrier）。 -/
def ce39Map (u : GefNF cq0PS 2) : GefNF cpdPhi9 6 :=
  ⟨ce39MapVal u, ce39MapVal_bnd u⟩

/-- **CE39-2d: 二単項式分解** — ce39MapVal u = (u₀·x⁰) + (u₁·x³)。 -/
theorem ce39MapVal_eq (u : GefNF cq0PS 2) :
    ce39MapVal u
      = psAdd ratRing (psSingle ratRing (u.val 0) 0) (psSingle ratRing (u.val 1) 3) := by
  funext j
  show (if j = 0 then u.val 0 else if j = 3 then u.val 1 else ratRing.zero)
    = ratRing.add (psSingle ratRing (u.val 0) 0 j) (psSingle ratRing (u.val 1) 3 j)
  cases Nat.decEq j 0 with
  | isTrue h =>
    rw [if_pos h, show psSingle ratRing (u.val 0) 0 j = u.val 0 from if_pos h,
      show psSingle ratRing (u.val 1) 3 j = ratRing.zero from if_neg (by omega),
      CRing.add_zero ratRing (u.val 0)]
  | isFalse h0 =>
    rw [if_neg h0, show psSingle ratRing (u.val 0) 0 j = ratRing.zero from if_neg h0]
    cases Nat.decEq j 3 with
    | isTrue h3 =>
      rw [if_pos h3, show psSingle ratRing (u.val 1) 3 j = u.val 1 from if_pos h3,
        ratRing.zero_add (u.val 1)]
    | isFalse h3 =>
      rw [if_neg h3, show psSingle ratRing (u.val 1) 3 j = ratRing.zero from if_neg h3,
        ratRing.zero_add ratRing.zero]

/-- **CE39-2e: NF 担体の二単項式分解** — u.val = (u₀·x⁰) + (u₁·x¹)（u は 2 有界）。 -/
theorem cnf_val_eq (u : GefNF cq0PS 2) :
    u.val = psAdd ratRing (psSingle ratRing (u.val 0) 0) (psSingle ratRing (u.val 1) 1) := by
  funext j
  show u.val j = ratRing.add (psSingle ratRing (u.val 0) 0 j) (psSingle ratRing (u.val 1) 1 j)
  cases Nat.decEq j 0 with
  | isTrue h =>
    rw [show psSingle ratRing (u.val 0) 0 j = u.val 0 from if_pos h,
      show psSingle ratRing (u.val 1) 1 j = ratRing.zero from if_neg (by omega),
      CRing.add_zero ratRing (u.val 0), h]
  | isFalse h0 =>
    rw [show psSingle ratRing (u.val 0) 0 j = ratRing.zero from if_neg h0]
    cases Nat.decEq j 1 with
    | isTrue h1 =>
      rw [show psSingle ratRing (u.val 1) 1 j = u.val 1 from if_pos h1,
        ratRing.zero_add (u.val 1), h1]
    | isFalse h1 =>
      rw [show psSingle ratRing (u.val 1) 1 j = ratRing.zero from if_neg h1,
        ratRing.zero_add ratRing.zero]
      exact u.property j (by omega)

/-! ## CE39-3: ℚ(ζ₉) 側の積 w = ι(u)·ι(v) の係数（台 ⊆ {0,3,6}） -/

/-- **CE39-3a: w の一般係数** — 二単項式分解 + `two_single_mul`（s=t=3）。 -/
theorem ce39_w_at (u v : GefNF cq0PS 2) (j : Nat) :
    psMul ratRing (ce39MapVal u) (ce39MapVal v) j
    = ratRing.add
        (ratRing.add (psSingle ratRing (ratRing.mul (u.val 0) (v.val 0)) 0 j)
          (psSingle ratRing (ratRing.mul (u.val 0) (v.val 1)) 3 j))
        (ratRing.add (psSingle ratRing (ratRing.mul (u.val 1) (v.val 0)) 3 j)
          (psSingle ratRing (ratRing.mul (u.val 1) (v.val 1)) 6 j)) := by
  rw [ce39MapVal_eq u, ce39MapVal_eq v,
    two_single_mul (u.val 0) (u.val 1) (v.val 0) (v.val 1) 3 3]
  rfl

/-- **CE39-3b: w 0 = u₀v₀**。 -/
theorem ce39_w0 (u v : GefNF cq0PS 2) :
    psMul ratRing (ce39MapVal u) (ce39MapVal v) 0 = ratRing.mul (u.val 0) (v.val 0) := by
  rw [ce39_w_at u v 0,
    show psSingle ratRing (ratRing.mul (u.val 0) (v.val 0)) 0 0 = ratRing.mul (u.val 0) (v.val 0)
      from if_pos rfl,
    show psSingle ratRing (ratRing.mul (u.val 0) (v.val 1)) 3 0 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing (ratRing.mul (u.val 1) (v.val 0)) 3 0 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing (ratRing.mul (u.val 1) (v.val 1)) 6 0 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add ratRing.zero,
    CRing.add_zero ratRing (ratRing.add (ratRing.mul (u.val 0) (v.val 0)) ratRing.zero),
    CRing.add_zero ratRing (ratRing.mul (u.val 0) (v.val 0))]

/-- **CE39-3c: w 3 = u₀v₁ + u₁v₀**。 -/
theorem ce39_w3 (u v : GefNF cq0PS 2) :
    psMul ratRing (ce39MapVal u) (ce39MapVal v) 3
      = ratRing.add (ratRing.mul (u.val 0) (v.val 1)) (ratRing.mul (u.val 1) (v.val 0)) := by
  rw [ce39_w_at u v 3,
    show psSingle ratRing (ratRing.mul (u.val 0) (v.val 0)) 0 3 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing (ratRing.mul (u.val 0) (v.val 1)) 3 3 = ratRing.mul (u.val 0) (v.val 1)
      from if_pos rfl,
    show psSingle ratRing (ratRing.mul (u.val 1) (v.val 0)) 3 3 = ratRing.mul (u.val 1) (v.val 0)
      from if_pos rfl,
    show psSingle ratRing (ratRing.mul (u.val 1) (v.val 1)) 6 3 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add (ratRing.mul (u.val 0) (v.val 1)),
    CRing.add_zero ratRing (ratRing.mul (u.val 1) (v.val 0))]

/-- **CE39-3d: w 6 = u₁v₁**（= 余因子 q）。 -/
theorem ce39_w6 (u v : GefNF cq0PS 2) :
    psMul ratRing (ce39MapVal u) (ce39MapVal v) 6 = ratRing.mul (u.val 1) (v.val 1) := by
  rw [ce39_w_at u v 6,
    show psSingle ratRing (ratRing.mul (u.val 0) (v.val 0)) 0 6 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing (ratRing.mul (u.val 0) (v.val 1)) 3 6 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing (ratRing.mul (u.val 1) (v.val 0)) 3 6 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing (ratRing.mul (u.val 1) (v.val 1)) 6 6 = ratRing.mul (u.val 1) (v.val 1)
      from if_pos rfl,
    ratRing.zero_add ratRing.zero,
    ratRing.zero_add (ratRing.mul (u.val 1) (v.val 1)),
    ratRing.zero_add (ratRing.mul (u.val 1) (v.val 1))]

/-- **CE39-3e: w j = 0（j ∉ {0,3,6}）**。 -/
theorem ce39_w_other (u v : GefNF cq0PS 2) (j : Nat)
    (h0 : j ≠ 0) (h3 : j ≠ 3) (h6 : j ≠ 6) :
    psMul ratRing (ce39MapVal u) (ce39MapVal v) j = ratRing.zero := by
  rw [ce39_w_at u v j,
    show psSingle ratRing (ratRing.mul (u.val 0) (v.val 0)) 0 j = ratRing.zero from if_neg (by omega),
    show psSingle ratRing (ratRing.mul (u.val 0) (v.val 1)) 3 j = ratRing.zero from if_neg h3,
    show psSingle ratRing (ratRing.mul (u.val 1) (v.val 0)) 3 j = ratRing.zero from if_neg h3,
    show psSingle ratRing (ratRing.mul (u.val 1) (v.val 1)) 6 j = ratRing.zero from if_neg h6,
    ratRing.zero_add ratRing.zero, ratRing.zero_add ratRing.zero]

/-! ## CE39-4: ℚ(ζ₃) 側の積 P = u·v の係数（直接 Cauchy 和・台 ⊆ {0,1,2}） -/

/-- **CE39-4a: P 0 = u₀v₀**。 -/
theorem cnf_P0 (u v : GefNF cq0PS 2) :
    psMul ratRing u.val v.val 0 = ratRing.mul (u.val 0) (v.val 0) := by
  show rsum ratRing (fun k => ratRing.mul (u.val k) (v.val (0 - k))) 1 = ratRing.mul (u.val 0) (v.val 0)
  rw [show rsum ratRing (fun k => ratRing.mul (u.val k) (v.val (0 - k))) 1
        = ratRing.add ratRing.zero (ratRing.mul (u.val 0) (v.val 0)) from rfl,
    ratRing.zero_add (ratRing.mul (u.val 0) (v.val 0))]

/-- **CE39-4b: P 1 = u₀v₁ + u₁v₀**。 -/
theorem cnf_P1 (u v : GefNF cq0PS 2) :
    psMul ratRing u.val v.val 1
      = ratRing.add (ratRing.mul (u.val 0) (v.val 1)) (ratRing.mul (u.val 1) (v.val 0)) := by
  show rsum ratRing (fun k => ratRing.mul (u.val k) (v.val (1 - k))) 2
    = ratRing.add (ratRing.mul (u.val 0) (v.val 1)) (ratRing.mul (u.val 1) (v.val 0))
  rw [show rsum ratRing (fun k => ratRing.mul (u.val k) (v.val (1 - k))) 2
        = ratRing.add (ratRing.add ratRing.zero (ratRing.mul (u.val 0) (v.val 1)))
            (ratRing.mul (u.val 1) (v.val 0)) from rfl,
    ratRing.zero_add (ratRing.mul (u.val 0) (v.val 1))]

/-- **CE39-4c: P 2 = u₁v₁**（= q）。u₂=v₂=0 で外側 2 項が消える。 -/
theorem cnf_P2 (u v : GefNF cq0PS 2) :
    psMul ratRing u.val v.val 2 = ratRing.mul (u.val 1) (v.val 1) := by
  show rsum ratRing (fun k => ratRing.mul (u.val k) (v.val (2 - k))) 3 = ratRing.mul (u.val 1) (v.val 1)
  rw [show rsum ratRing (fun k => ratRing.mul (u.val k) (v.val (2 - k))) 3
        = ratRing.add (ratRing.add (ratRing.add ratRing.zero (ratRing.mul (u.val 0) (v.val 2)))
            (ratRing.mul (u.val 1) (v.val 1))) (ratRing.mul (u.val 2) (v.val 0)) from rfl,
    show v.val 2 = ratRing.zero from v.property 2 (by omega),
    show u.val 2 = ratRing.zero from u.property 2 (by omega),
    CRing.mul_zero ratRing (u.val 0), CRing.zero_mul ratRing (v.val 0),
    ratRing.zero_add ratRing.zero, ratRing.zero_add (ratRing.mul (u.val 1) (v.val 1)),
    CRing.add_zero ratRing (ratRing.mul (u.val 1) (v.val 1))]

/-- **CE39-4d: P j = 0（j ≥ 3）** — 各 Cauchy 項が消える（k≥2 で u₀、k<2 で v₀）。 -/
theorem cnf_P_ge3 (u v : GefNF cq0PS 2) (j : Nat) (hj : 3 ≤ j) :
    psMul ratRing u.val v.val j = ratRing.zero := by
  show rsum ratRing (fun k => ratRing.mul (u.val k) (v.val (j - k))) (j + 1) = ratRing.zero
  have hz : rsum ratRing (fun k => ratRing.mul (u.val k) (v.val (j - k))) (j + 1)
      = rsum ratRing (fun _ => ratRing.zero) (j + 1) :=
    rsum_congr ratRing (j + 1) (fun k _ => by
      cases Nat.lt_or_ge k 2 with
      | inl hk =>
        rw [v.property (j - k) (by omega)]
        exact CRing.mul_zero ratRing (u.val k)
      | inr hk =>
        rw [u.property k hk]
        exact CRing.zero_mul ratRing (v.val (j - k)))
  rw [hz]
  exact rsum_const_zero ratRing (j + 1)

/-! ## CE39-5: 法多項式 Φ_9 = x⁶+x³+1 の係数（台 = {0,3,6}） -/

/-- **CE39-5a: Φ_9 0 = 1**。 -/
theorem cpdPhi9_0 : cpdPhi9 0 = ratRing.one := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 0) (psSingle ratRing ratRing.one 3 0))
      (psC ratRing ratRing.one 0) = ratRing.one
  rw [show psSingle ratRing ratRing.one 6 0 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 3 0 = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one 0 = ratRing.one from if_pos rfl,
    ratRing.zero_add ratRing.zero, ratRing.zero_add ratRing.one]

/-- **CE39-5b: Φ_9 3 = 1**。 -/
theorem cpdPhi9_3 : cpdPhi9 3 = ratRing.one := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 3) (psSingle ratRing ratRing.one 3 3))
      (psC ratRing ratRing.one 3) = ratRing.one
  rw [show psSingle ratRing ratRing.one 6 3 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 3 3 = ratRing.one from if_pos rfl,
    show psC ratRing ratRing.one 3 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add ratRing.one, CRing.add_zero ratRing ratRing.one]

/-- **CE39-5c: Φ_9 6 = 1**。 -/
theorem cpdPhi9_6 : cpdPhi9 6 = ratRing.one := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 6) (psSingle ratRing ratRing.one 3 6))
      (psC ratRing ratRing.one 6) = ratRing.one
  rw [show psSingle ratRing ratRing.one 6 6 = ratRing.one from if_pos rfl,
    show psSingle ratRing ratRing.one 3 6 = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one 6 = ratRing.zero from if_neg (by omega),
    CRing.add_zero ratRing ratRing.one, CRing.add_zero ratRing ratRing.one]

/-- **CE39-5d: Φ_9 j = 0（j ∉ {0,3,6}）**。 -/
theorem cpdPhi9_other (j : Nat) (h0 : j ≠ 0) (h3 : j ≠ 3) (h6 : j ≠ 6) :
    cpdPhi9 j = ratRing.zero := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 j) (psSingle ratRing ratRing.one 3 j))
      (psC ratRing ratRing.one j) = ratRing.zero
  rw [show psSingle ratRing ratRing.one 6 j = ratRing.zero from if_neg h6,
    show psSingle ratRing ratRing.one 3 j = ratRing.zero from if_neg h3,
    show psC ratRing ratRing.one j = ratRing.zero from if_neg h0,
    ratRing.zero_add ratRing.zero, ratRing.zero_add ratRing.zero]

/-! ## CE39-6: ℚ(ζ₃) 側の NF 剰余 r₃ = pfdRed_{Φ₃}(u·v) の明示形 -/

/-- **CE39-6a: NF 剰余 r₃** — (u·v) の Φ₃ 簡約結果の明示係数
    r₃ = (u₀v₀ − q) + (u₀v₁ + u₁v₀ − q)·x（q = u₁v₁、deg ≤ 1）。 -/
def ce39r3 (u v : GefNF cq0PS 2) : PS ratRing :=
  fun j => if j = 0 then ratRing.add (ratRing.mul (u.val 0) (v.val 0)) (ratRing.neg (ce39q u v))
           else if j = 1 then
             ratRing.add (ratRing.add (ratRing.mul (u.val 0) (v.val 1)) (ratRing.mul (u.val 1) (v.val 0)))
               (ratRing.neg (ce39q u v))
           else ratRing.zero

/-- **CE39-6b: r₃ 0**。 -/
theorem ce39r3_0 (u v : GefNF cq0PS 2) :
    ce39r3 u v 0 = ratRing.add (ratRing.mul (u.val 0) (v.val 0)) (ratRing.neg (ce39q u v)) :=
  if_pos rfl

/-- **CE39-6c: r₃ 1**。 -/
theorem ce39r3_1 (u v : GefNF cq0PS 2) :
    ce39r3 u v 1
      = ratRing.add (ratRing.add (ratRing.mul (u.val 0) (v.val 1)) (ratRing.mul (u.val 1) (v.val 0)))
          (ratRing.neg (ce39q u v)) :=
  (if_neg (show (1 : Nat) ≠ 0 by omega)).trans (if_pos rfl)

/-- **CE39-6d: r₃ j = 0（j ≥ 2）**（有界性の担体）。 -/
theorem ce39r3_ge2 (u v : GefNF cq0PS 2) (j : Nat) (hj : 2 ≤ j) : ce39r3 u v j = ratRing.zero :=
  (if_neg (show j ≠ 0 by omega)).trans (if_neg (show j ≠ 1 by omega))

/-- **CE39-6e: r₃ は 2 有界**（deg ≤ 1）。 -/
theorem ce39r3_bnd (u v : GefNF cq0PS 2) : IsPolyBounded ratRing (ce39r3 u v) 2 :=
  fun j hj => ce39r3_ge2 u v j hj

/-- **CE39-6f: psC c は 1 有界**（定数余因子）。 -/
theorem ce39_psC_bnd1 (c : QRat) : IsPolyBounded ratRing (psC ratRing c) 1 :=
  fun j hj => if_neg (by omega)

/-- **CE39-6g: NF 剰余の合同**（Φ₃ 側 pfdRed_char の入力）— 各点 j で
    (u·v − r₃)_j = (q·Φ₃)_j。余因子は**定数** q = u₁v₁（deg uv ≤ 2 = deg Φ₃）。 -/
theorem cnf_r3_cong (u v : GefNF cq0PS 2) : ∀ j,
    psAdd ratRing (psMul ratRing u.val v.val) (psNeg ratRing (ce39r3 u v)) j
      = psMul ratRing (psC ratRing (ce39q u v)) cq0PS j := by
  intro j
  show ratRing.add (psMul ratRing u.val v.val j) (ratRing.neg (ce39r3 u v j))
    = psMul ratRing (psC ratRing (ce39q u v)) cq0PS j
  rw [gefSmulCoeff (ce39q u v) cq0PS j]
  cases Nat.decEq j 0 with
  | isTrue h0 =>
    subst h0
    rw [cnf_P0 u v, ce39r3_0 u v, cq0PS_coeff0, CRing.mul_one ratRing (ce39q u v)]
    exact ce39_alg (ratRing.mul (u.val 0) (v.val 0)) (ce39q u v)
  | isFalse h0 =>
    cases Nat.decEq j 1 with
    | isTrue h1 =>
      subst h1
      rw [cnf_P1 u v, ce39r3_1 u v, cq0PS_coeff1, CRing.mul_one ratRing (ce39q u v)]
      exact ce39_alg (ratRing.add (ratRing.mul (u.val 0) (v.val 1)) (ratRing.mul (u.val 1) (v.val 0)))
        (ce39q u v)
    | isFalse h1 =>
      cases Nat.decEq j 2 with
      | isTrue h2 =>
        subst h2
        rw [cnf_P2 u v, ce39r3_ge2 u v 2 (by omega), cq0PS_coeff2,
          CRing.mul_one ratRing (ce39q u v), CRing.neg_zero ratRing,
          CRing.add_zero ratRing (ratRing.mul (u.val 1) (v.val 1))]
      | isFalse h2 =>
        rw [cnf_P_ge3 u v j (by omega), ce39r3_ge2 u v j (by omega),
          cq0_bound j (by omega), CRing.mul_zero ratRing (ce39q u v),
          CRing.neg_zero ratRing, CRing.add_zero ratRing ratRing.zero]

/-- **CE39-6h: ℚ(ζ₃) 側の NF 積の明示形** — (u·v).val = r₃（pfdRed_char）。 -/
theorem cnf_mul_char (u v : GefNF cq0PS 2) :
    ∀ j, (cnfPhi3Field.mul u v).val j = ce39r3 u v j :=
  pfdRed_char cq0PS 2 cq0_bound cq0_lead 2 (psMul ratRing u.val v.val) (ce39r3 u v)
    (simpleExt_mul_bounded ratRing u.property v.property) (ce39r3_bnd u v)
    ⟨psC ratRing (ce39q u v), 1, ce39_psC_bnd1 (ce39q u v), cnf_r3_cong u v⟩

/-! ## CE39-7: ι(u·v) の係数 V = ce39MapVal(u·v)（台 ⊆ {0,3}） -/

/-- **CE39-7a: V 0 = u₀v₀ − q**。 -/
theorem ce39_V0 (u v : GefNF cq0PS 2) :
    ce39MapVal (cnfPhi3Field.mul u v) 0
      = ratRing.add (ratRing.mul (u.val 0) (v.val 0)) (ratRing.neg (ce39q u v)) :=
  (show ce39MapVal (cnfPhi3Field.mul u v) 0 = (cnfPhi3Field.mul u v).val 0 from if_pos rfl).trans
    ((cnf_mul_char u v 0).trans (ce39r3_0 u v))

/-- **CE39-7b: V 3 = u₀v₁ + u₁v₀ − q**。 -/
theorem ce39_V3 (u v : GefNF cq0PS 2) :
    ce39MapVal (cnfPhi3Field.mul u v) 3
      = ratRing.add (ratRing.add (ratRing.mul (u.val 0) (v.val 1)) (ratRing.mul (u.val 1) (v.val 0)))
          (ratRing.neg (ce39q u v)) :=
  (show ce39MapVal (cnfPhi3Field.mul u v) 3 = (cnfPhi3Field.mul u v).val 1
      from (if_neg (show (3 : Nat) ≠ 0 by omega)).trans (if_pos rfl)).trans
    ((cnf_mul_char u v 1).trans (ce39r3_1 u v))

/-- **CE39-7c: V j = 0（j ∉ {0,3}）**。 -/
theorem ce39_V_other (u v : GefNF cq0PS 2) (j : Nat) (h0 : j ≠ 0) (h3 : j ≠ 3) :
    ce39MapVal (cnfPhi3Field.mul u v) j = ratRing.zero :=
  (if_neg h0).trans (if_neg h3)

/-! ## CE39-8: 乗法性の合同（★山場）— w − V = q·Φ_9 -/

/-- **CE39-8: 乗法性の合同** — 各点 j で (ι(u)·ι(v) − ι(u·v))_j = (q·Φ_9)_j。
    余因子は**定数** q = u₁v₁。台照合 4 分岐（j = 0,3,6 と他）で、Φ₃(x³)=Φ_9
    （x⁶+x³+1 の係数 1,1,1 が 0,3,6 に立つ）を使って純代数補題 `ce39_alg` で閉じる。 -/
theorem ce39_mul_cong (u v : GefNF cq0PS 2) : ∀ j,
    psAdd ratRing (psMul ratRing (ce39MapVal u) (ce39MapVal v))
        (psNeg ratRing (ce39MapVal (cnfPhi3Field.mul u v))) j
      = psMul ratRing (psC ratRing (ce39q u v)) cpdPhi9 j := by
  intro j
  show ratRing.add (psMul ratRing (ce39MapVal u) (ce39MapVal v) j)
      (ratRing.neg (ce39MapVal (cnfPhi3Field.mul u v) j))
    = psMul ratRing (psC ratRing (ce39q u v)) cpdPhi9 j
  rw [gefSmulCoeff (ce39q u v) cpdPhi9 j]
  cases Nat.decEq j 0 with
  | isTrue h0 =>
    subst h0
    rw [ce39_w0 u v, ce39_V0 u v, cpdPhi9_0, CRing.mul_one ratRing (ce39q u v)]
    exact ce39_alg (ratRing.mul (u.val 0) (v.val 0)) (ce39q u v)
  | isFalse h0 =>
    cases Nat.decEq j 3 with
    | isTrue h3 =>
      subst h3
      rw [ce39_w3 u v, ce39_V3 u v, cpdPhi9_3, CRing.mul_one ratRing (ce39q u v)]
      exact ce39_alg (ratRing.add (ratRing.mul (u.val 0) (v.val 1)) (ratRing.mul (u.val 1) (v.val 0)))
        (ce39q u v)
    | isFalse h3 =>
      cases Nat.decEq j 6 with
      | isTrue h6 =>
        subst h6
        rw [ce39_w6 u v, ce39_V_other u v 6 (by omega) (by omega), cpdPhi9_6,
          CRing.mul_one ratRing (ce39q u v), CRing.neg_zero ratRing,
          CRing.add_zero ratRing (ratRing.mul (u.val 1) (v.val 1))]
      | isFalse h6 =>
        rw [ce39_w_other u v j h0 h3 h6, ce39_V_other u v j h0 h3,
          cpdPhi9_other j h0 h3 h6, CRing.mul_zero ratRing (ce39q u v),
          CRing.neg_zero ratRing, CRing.add_zero ratRing ratRing.zero]

/-! ## CE39-9: 環準同型性（加法・乗法・1 保存）と ι の束ね -/

/-- **CE39-9a: 加法保存** — ι(u+v) = ι(u)+ι(v)（成分ごと・線形・簡約不要）。 -/
theorem ce39_map_add (u v : GefNF cq0PS 2) :
    ce39Map (cnfPhi3Field.add u v) = p9iPhi9Field.add (ce39Map u) (ce39Map v) := by
  apply Subtype.ext
  funext j
  show (if j = 0 then ratRing.add (u.val 0) (v.val 0)
         else if j = 3 then ratRing.add (u.val 1) (v.val 1) else ratRing.zero)
    = ratRing.add
        (if j = 0 then u.val 0 else if j = 3 then u.val 1 else ratRing.zero)
        (if j = 0 then v.val 0 else if j = 3 then v.val 1 else ratRing.zero)
  cases Nat.decEq j 0 with
  | isTrue h => rw [if_pos h, if_pos h, if_pos h]
  | isFalse h0 =>
    rw [if_neg h0, if_neg h0, if_neg h0]
    cases Nat.decEq j 3 with
    | isTrue h => rw [if_pos h, if_pos h, if_pos h]
    | isFalse h3 => rw [if_neg h3, if_neg h3, if_neg h3, ratRing.zero_add ratRing.zero]

/-- **CE39-9b: 乗法保存（★山場）** — ι(u·v) = ι(u)·ι(v)。ℚ(ζ₉) 側の NF 積
    pfdRed_{Φ_9}(ι(u)·ι(v)) が ι(pfdRed_{Φ₃}(u·v)) に一致することを、`pfdRed_char`
    と乗法性合同 `ce39_mul_cong`（余因子定数 q・Φ₃(x³)=Φ_9）で閉じる。 -/
theorem ce39_map_mul (u v : GefNF cq0PS 2) :
    ce39Map (cnfPhi3Field.mul u v) = p9iPhi9Field.mul (ce39Map u) (ce39Map v) := by
  apply Subtype.ext
  show ce39MapVal (cnfPhi3Field.mul u v)
    = pfdRed cpdPhi9 6 6 (psMul ratRing (ce39MapVal u) (ce39MapVal v))
  funext j
  exact (pfdRed_char cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead 6
    (psMul ratRing (ce39MapVal u) (ce39MapVal v))
    (ce39MapVal (cnfPhi3Field.mul u v))
    (simpleExt_mul_bounded ratRing (ce39MapVal_bnd u) (ce39MapVal_bnd v))
    (ce39MapVal_bnd (cnfPhi3Field.mul u v))
    ⟨psC ratRing (ce39q u v), 1, ce39_psC_bnd1 (ce39q u v), ce39_mul_cong u v⟩ j).symm

/-- **CE39-9c: 1 保存** — ι(1) = 1（定数 1 は不動・3 次係数は 0）。 -/
theorem ce39_map_one : ce39Map cnfPhi3Field.one = p9iPhi9Field.one := by
  apply Subtype.ext
  funext j
  show (if j = 0 then ratRing.one else if j = 3 then ratRing.zero else ratRing.zero)
    = (if j = 0 then ratRing.one else ratRing.zero)
  cases Nat.decEq j 0 with
  | isTrue h => rw [if_pos h, if_pos h]
  | isFalse h0 =>
    rw [if_neg h0, if_neg h0]
    cases Nat.decEq j 3 with
    | isTrue h => rw [if_pos h]
    | isFalse h => rw [if_neg h]

/-- **CE39-9d: 埋め込み ι : ℚ(ζ₃) ↪ ℚ(ζ₉)** — RingHom（x̄₃ ↦ x̄₉³）。 -/
def ce39Iota : RingHom cnfPhi3Field.toCRing p9iPhi9Field.toCRing where
  map := ce39Map
  map_add := ce39_map_add
  map_mul := ce39_map_mul
  map_one := ce39_map_one

/-! ## CE39-10: Φ₃(x³) = Φ_9・incl 適合・体拡大 K₁⊂K₂ -/

/-- **CE39-10a: Φ₃(x³) = Φ_9** — 係数照合（Φ_9 = x⁶+x³+1 の係数 1,1,1 が
    0,3,6 に立ち、Φ₃ = x²+x+1 の係数 1,1,1 が 0,1,2 に立つ・x↦x³ の対応）。 -/
theorem ce39_phi9_eq_phi3_cubed :
    cpdPhi9 0 = cq0PS 0 ∧ cpdPhi9 3 = cq0PS 1 ∧ cpdPhi9 6 = cq0PS 2 :=
  ⟨by rw [cpdPhi9_0, cq0PS_coeff0], by rw [cpdPhi9_3, cq0PS_coeff1],
    by rw [cpdPhi9_6, cq0PS_coeff2]⟩

/-- **CE39-10b: incl 適合** — ι ∘ incl₃ = incl₉（基礎体 ℚ の定数は不動）。 -/
theorem ce39_incl_compat (a : QRat) :
    ce39Map (cnfExt3.incl a) = p9iExt9.incl a := by
  apply Subtype.ext
  funext j
  show (if j = 0 then a else if j = 3 then ratRing.zero else ratRing.zero)
    = (if j = 0 then a else ratRing.zero)
  cases Nat.decEq j 0 with
  | isTrue h => rw [if_pos h, if_pos h]
  | isFalse h0 =>
    rw [if_neg h0, if_neg h0]
    cases Nat.decEq j 3 with
    | isTrue h => rw [if_pos h]
    | isFalse h => rw [if_neg h]

/-- **CE39-10c: 体拡大 K₁ ⊂ K₂ = ℚ(ζ₃) ⊂ ℚ(ζ₉)** — base=cnfPhi3Field,
    top=p9iPhi9Field, incl=ι（RingHom の担体写像）。res₁（CR39）の意味論
    ι∘res(σ)=σ∘ι の左辺を供給する実体埋め込み。 -/
def ce39Ext : FieldExtension where
  base := cnfPhi3Field
  top := p9iPhi9Field
  incl := ce39Map
  incl_add := ce39_map_add
  incl_mul := ce39_map_mul
  incl_one := ce39_map_one

end IUT
