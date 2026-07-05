/-
  IUT/EvaluationHom.lean — M274F（評価準同型 ev_α : K[X] → E:
  柱A 実代数拡大の本物の先行建設）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無）。

  **complete_pct 影響**: **昇格(a)**。M273F `MinimalPolynomial` は「多項式
  評価 ev が環準同型である」ことを honest 仮説 `PolyEval`（ev_add/ev_mul/
  ev_zero を公理として受け取る structure）として持ち回っていた。本層は
  その ev を、環準同型 ι:K→E と元 α∈E から **本物の評価写像**
  ev_α(Σ aᵢXⁱ) = Σ ι(aᵢ)·αⁱ として実構成し、加法・零・定数・単位・
  **乗法（Cauchy 畳み込みの評価＝評価の積）保存**を本物に証明する。
  すなわち PolyEval の defining property（ev が環準同型）を仮説から
  **構成された本物の定理へ昇格**させる。

  * M274F-1 `evalSum` — 評価の有限和 ev_α(f)|_n = Σ_{i<n} ι(fᵢ)·αⁱ
  * M274F-2 `evalHom_rsum_stable_ge` / `evalHom_rsum_eq_of_bound` —
    有限台上界での和の安定性（上界を超えても値不変）
  * M274F-3 `evalHom_stable` — **evalSum の打ち切り安定性**（f が N で
    有界なら M ≥ N で ev_α(f)|_M = ev_α(f)|_N。台の外は 0）
  * M274F-4 `evalHom_add` — **加法保存** ev_α(f+g) = ev_α(f)+ev_α(g)
  * M274F-5 `evalHom_zero` / `evalHom_C` / `evalHom_one` — **零・定数・
    単位** ev_α(0)=0・ev_α(polyC c)=ι(c)・ev_α(1)=1
  * M274F-6 `evalHom_cauchy_mul` — 有限台の Cauchy 畳み込みの評価公式の
    核（三角和 rsum_triangle + 有界性で矩形和に還元）
  * M274F-7 `evalHom_term_mul` — 項ごとの Cauchy 同定
    ι((fg)ⱼ)·αʲ = Σ_{k≤j} (ι(fₖ)αᵏ)(ι(g_{j−k})α^{j−k})（rpow_add + interchange）
  * M274F-8 `evalHom_mul` — **乗法保存（本丸）** f が Nf・g が Ng で有界なら
    ev_α(f·g)|_{Nf+Ng+1} = ev_α(f)|_{Nf}·ev_α(g)|_{Ng}
  * M274F-9 `evalHomId` / `evalSum_id` / `evalHom_id_mul` — 実例:
    ι=恒等（K=E）での通常の多項式評価が乗法を保つ
  * M274F-10 capstone `EvalHomData` / `EvalHomProps` / `evalHom_isRingHom` /
    `evalHom_exists` — ι・α・評価法則の束（= M273F PolyEval を満たす本物の
    witness データ）と存在

  正直な限定（何が本物で何が未達か・§4 準拠、消去・弱化しない）:
   - **本物**: 評価写像 evalSum そのもの、加法・零・定数・単位・**乗法
     （Cauchy 畳み込みの評価が評価の積に一致すること）**の保存は完全証明
     （sorry 皆無・新規 Classical.choice 皆無）。乗法保存は有限台の
     三角和交換（rsum_triangle）と項ごとの αⁱαʲ=α^{i+j}（rpow_add）で
     本当に閉じている。
   - **honest 限定（bound を data として持つ）**: 評価は係数列 `PS K` 上で
     **有限台上界 N を明示引数**として扱う。多項式部分環 `polyCRing K`
     （M269F の有限台部分環、台上界は `∃ N` の Prop）上の**全域 RingHom
     オブジェクト** `RingHom (polyCRing K) E` は、Prop の存在から次数上界を
     抽出する必要があり **Classical.choice を要する**（本規約が証明本体で
     禁ずる）ため本層では構成しない。乗法保存は打ち切り点 Nf+Ng+1 を
     明示して述べる（toy 化・弱化ではなく、有限台の忠実な扱い）。
   - **未達（正直申告）**: 有界でない冪級数 `PS K` 全域を α で評価する
     全域 ev（M273F `PolyEval.ev` の域）は、一般の α では R[[X]]→E の
     収束が代数的に定まらず本物には存在しない。本層の `EvalHomProps` は
     多項式（有限台）に限った ev の環準同型性という **PolyEval の
     defining property の本物の内容**を捉える（choice 依存の全域函数化・
     不定和の評価は deferred）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.SimpleExtension
import IUT.PSFunctor
import IUT.FormalGroupExists

namespace IUT

/-! ## M274F-1: 評価の有限和 -/

/-- **M274F-1: 評価写像の有限和** — 環準同型 ι:K→E と α∈E に対し、
    係数列 f の n 次までの評価 Σ_{i<n} ι(fᵢ)·αⁱ。 -/
def evalSum {K E : CRing} (ι : RingHom K E) (α : E.carrier) (f : PS K) (n : Nat) :
    E.carrier :=
  rsum E (fun i => E.mul (ι.map (f i)) (rpow E α i)) n

/-! ## M274F-2: 有限台上界での和の安定性 -/

/-- **M274F-2a: 上界を超えても不変** — f が A 以上で消えるなら
    Σ_{k<A+d} f = Σ_{k<A} f（尾部が全て 0）。 -/
theorem evalHom_rsum_stable_ge (E : CRing) (f : Nat → E.carrier) (A : Nat)
    (hf : ∀ k, A ≤ k → f k = E.zero) :
    ∀ d, rsum E f (A + d) = rsum E f A := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    show E.add (rsum E f (A + d)) (f (A + d)) = rsum E f A
    rw [hf (A + d) (by omega), CRing.add_zero E (rsum E f (A + d))]
    exact ih

/-- **M274F-2b: 上界の付け替え** — A ≤ N かつ f が A 以上で消えるなら
    Σ_{k<N} f = Σ_{k<A} f。 -/
theorem evalHom_rsum_eq_of_bound (E : CRing) (f : Nat → E.carrier) (A N : Nat)
    (hle : A ≤ N) (hf : ∀ k, A ≤ k → f k = E.zero) :
    rsum E f N = rsum E f A := by
  rw [show N = A + (N - A) from by omega]
  exact evalHom_rsum_stable_ge E f A hf (N - A)

/-! ## M274F-3: evalSum の打ち切り安定性 -/

/-- **M274F-3: 打ち切り安定性** — f が N で有界（多項式）なら、上界 M ≥ N を
    どこまで伸ばしても評価値は不変（台の外の項 ι(0)·αⁱ = 0）。 -/
theorem evalHom_stable {K E : CRing} (ι : RingHom K E) (α : E.carrier) (f : PS K)
    (N : Nat) (hf : IsPolyBounded K f N) :
    ∀ M, N ≤ M → evalSum ι α f M = evalSum ι α f N := by
  intro M hM
  exact evalHom_rsum_eq_of_bound E (fun i => E.mul (ι.map (f i)) (rpow E α i)) N M hM
    (fun k hk => by
      show E.mul (ι.map (f k)) (rpow E α k) = E.zero
      rw [hf k hk, RingHom.map_zero ι, CRing.zero_mul E (rpow E α k)])

/-! ## M274F-4: 加法保存 -/

/-- **M274F-4: 加法保存** — ev_α(f+g) = ev_α(f) + ev_α(g)（項ごとの
    ι の加法性 + 右分配、そして rsum_add）。 -/
theorem evalHom_add {K E : CRing} (ι : RingHom K E) (α : E.carrier)
    (f g : PS K) (n : Nat) :
    evalSum ι α (psAdd K f g) n
      = E.add (evalSum ι α f n) (evalSum ι α g n) := by
  show rsum E (fun i => E.mul (ι.map (psAdd K f g i)) (rpow E α i)) n
    = E.add (rsum E (fun i => E.mul (ι.map (f i)) (rpow E α i)) n)
        (rsum E (fun i => E.mul (ι.map (g i)) (rpow E α i)) n)
  have hc : rsum E (fun i => E.mul (ι.map (psAdd K f g i)) (rpow E α i)) n
      = rsum E (fun i => E.add (E.mul (ι.map (f i)) (rpow E α i))
          (E.mul (ι.map (g i)) (rpow E α i))) n :=
    rsum_congr E n (fun i _ => by
      show E.mul (ι.map (K.add (f i) (g i))) (rpow E α i)
        = E.add (E.mul (ι.map (f i)) (rpow E α i)) (E.mul (ι.map (g i)) (rpow E α i))
      rw [ι.map_add (f i) (g i),
        CRing.right_distrib E (ι.map (f i)) (ι.map (g i)) (rpow E α i)])
  rw [hc]
  exact rsum_add E _ _ n

/-! ## M274F-5: 零・定数・単位 -/

/-- **M274F-5a: 零** — ev_α(0) = 0。 -/
theorem evalHom_zero {K E : CRing} (ι : RingHom K E) (α : E.carrier) (n : Nat) :
    evalSum ι α (psZero K) n = E.zero := by
  show rsum E (fun i => E.mul (ι.map (psZero K i)) (rpow E α i)) n = E.zero
  have hc : rsum E (fun i => E.mul (ι.map (psZero K i)) (rpow E α i)) n
      = rsum E (fun _ => E.zero) n :=
    rsum_congr E n (fun i _ => by
      show E.mul (ι.map K.zero) (rpow E α i) = E.zero
      rw [RingHom.map_zero ι, CRing.zero_mul E (rpow E α i)])
  rw [hc]
  exact rsum_const_zero E n

/-- **M274F-5b: 定数** — ev_α(polyC c) = ι(c)（定数項だけが残り、α⁰=1）。 -/
theorem evalHom_C {K E : CRing} (ι : RingHom K E) (α : E.carrier) (c : K.carrier) :
    evalSum ι α (psC K c) 1 = ι.map c := by
  show E.add (rsum E (fun i => E.mul (ι.map (psC K c i)) (rpow E α i)) 0)
      (E.mul (ι.map (psC K c 0)) (rpow E α 0)) = ι.map c
  show E.add E.zero (E.mul (ι.map (psC K c 0)) (rpow E α 0)) = ι.map c
  rw [E.zero_add]
  show E.mul (ι.map (psC K c 0)) (rpow E α 0) = ι.map c
  rw [show psC K c 0 = c from rfl, show rpow E α 0 = E.one from rfl]
  exact CRing.mul_one E (ι.map c)

/-- **M274F-5c: 単位** — ev_α(1) = 1（psOne = psC 1、ι.map_one）。 -/
theorem evalHom_one {K E : CRing} (ι : RingHom K E) (α : E.carrier) :
    evalSum ι α (psOne K) 1 = E.one := by
  have h := evalHom_C ι α K.one
  rw [ι.map_one] at h
  exact h

/-! ## M274F-6: Cauchy 畳み込みの評価（純有限和の核） -/

/-- **M274F-6: 有限台 Cauchy 和の矩形化** — E 内の列 a・b が A・B 以上で
    消えるなら、それらの Cauchy 畳み込みを Nf+Ng+1 まで足したものは、
    各々の部分和の積に一致する。三角和交換 rsum_triangle で三角に直し、
    有界性で矩形（k<A, l<B）に還元する。 -/
theorem evalHom_cauchy_mul (E : CRing) (a b : Nat → E.carrier) (A B : Nat)
    (ha : ∀ k, A ≤ k → a k = E.zero) (hb : ∀ l, B ≤ l → b l = E.zero) :
    rsum E (fun j => rsum E (fun k => E.mul (a k) (b (j - k))) (j + 1)) (A + B + 1)
      = E.mul (rsum E a A) (rsum E b B) := by
  have htri := rsum_triangle E (fun k l => E.mul (a k) (b l)) (A + B)
  rw [htri]
  rw [evalHom_rsum_eq_of_bound E
      (fun k => rsum E (fun l => E.mul (a k) (b l)) (A + B + 1 - k)) A (A + B + 1)
      (by omega)
      (fun k hk => by
        show rsum E (fun l => E.mul (a k) (b l)) (A + B + 1 - k) = E.zero
        have hz : rsum E (fun l => E.mul (a k) (b l)) (A + B + 1 - k)
            = rsum E (fun _ => E.zero) (A + B + 1 - k) :=
          rsum_congr E (A + B + 1 - k) (fun l _ => by
            show E.mul (a k) (b l) = E.zero
            rw [ha k hk, CRing.zero_mul E (b l)])
        rw [hz]
        exact rsum_const_zero E (A + B + 1 - k))]
  rw [rsum_mul_right E a (rsum E b B) A]
  exact rsum_congr E A (fun k hk => by
    rw [evalHom_rsum_eq_of_bound E (fun l => E.mul (a k) (b l)) B (A + B + 1 - k)
        (by omega)
        (fun l hl => by
          show E.mul (a k) (b l) = E.zero
          rw [hb l hl, CRing.mul_zero E (a k)])]
    exact (rsum_mul_left E b (a k) B).symm)

/-! ## M274F-7: 項ごとの Cauchy 同定 -/

/-- **M274F-7: 積係数の評価 = 項の Cauchy 畳み込み** —
    ι((fg)ⱼ)·αʲ = Σ_{k≤j} (ι(fₖ)·αᵏ)·(ι(g_{j−k})·α^{j−k})。
    ι の有限和保存・乗法保存、αʲ = αᵏ·α^{j−k}（rpow_add）、interchange。 -/
theorem evalHom_term_mul {K E : CRing} (ι : RingHom K E) (α : E.carrier)
    (f g : PS K) (j : Nat) :
    E.mul (ι.map (psMul K f g j)) (rpow E α j)
      = rsum E (fun k => E.mul (E.mul (ι.map (f k)) (rpow E α k))
          (E.mul (ι.map (g (j - k))) (rpow E α (j - k)))) (j + 1) := by
  show E.mul (ι.map (rsum K (fun k => K.mul (f k) (g (j - k))) (j + 1))) (rpow E α j)
    = rsum E (fun k => E.mul (E.mul (ι.map (f k)) (rpow E α k))
        (E.mul (ι.map (g (j - k))) (rpow E α (j - k)))) (j + 1)
  rw [ringHom_rsum ι (fun k => K.mul (f k) (g (j - k))) (j + 1)]
  rw [rsum_mul_right E (fun k => ι.map (K.mul (f k) (g (j - k)))) (rpow E α j) (j + 1)]
  exact rsum_congr E (j + 1) (fun k hk => by
    rw [ι.map_mul (f k) (g (j - k))]
    have hj : k + (j - k) = j := by omega
    have hpow : rpow E α (k + (j - k)) = E.mul (rpow E α k) (rpow E α (j - k)) :=
      rpow_add E α k (j - k)
    rw [hj] at hpow
    rw [hpow]
    exact CRing.mul_mul_comm E (ι.map (f k)) (ι.map (g (j - k)))
      (rpow E α k) (rpow E α (j - k)))

/-! ## M274F-8: 乗法保存（本丸） -/

/-- **M274F-8: 乗法保存** — f が Nf・g が Ng で有界（多項式）なら、
    ev_α(f·g) を Nf+Ng+1 まで評価したものは ev_α(f)|_{Nf}·ev_α(g)|_{Ng}
    に一致する。項ごとの Cauchy 同定（M274F-7）で E 内の Cauchy 畳み込み
    に直し、有限台の矩形化（M274F-6）で積に還元する。 -/
theorem evalHom_mul {K E : CRing} (ι : RingHom K E) (α : E.carrier)
    (f g : PS K) (Nf Ng : Nat)
    (hf : IsPolyBounded K f Nf) (hg : IsPolyBounded K g Ng) :
    evalSum ι α (psMul K f g) (Nf + Ng + 1)
      = E.mul (evalSum ι α f Nf) (evalSum ι α g Ng) := by
  show rsum E (fun j => E.mul (ι.map (psMul K f g j)) (rpow E α j)) (Nf + Ng + 1)
    = E.mul (rsum E (fun i => E.mul (ι.map (f i)) (rpow E α i)) Nf)
        (rsum E (fun i => E.mul (ι.map (g i)) (rpow E α i)) Ng)
  have hstep : rsum E (fun j => E.mul (ι.map (psMul K f g j)) (rpow E α j))
        (Nf + Ng + 1)
      = rsum E (fun j => rsum E (fun k =>
          E.mul (E.mul (ι.map (f k)) (rpow E α k))
            (E.mul (ι.map (g (j - k))) (rpow E α (j - k)))) (j + 1)) (Nf + Ng + 1) :=
    rsum_congr E (Nf + Ng + 1) (fun j _ => evalHom_term_mul ι α f g j)
  rw [hstep]
  exact evalHom_cauchy_mul E
    (fun i => E.mul (ι.map (f i)) (rpow E α i))
    (fun i => E.mul (ι.map (g i)) (rpow E α i))
    Nf Ng
    (fun k hk => by
      show E.mul (ι.map (f k)) (rpow E α k) = E.zero
      rw [hf k hk, RingHom.map_zero ι, CRing.zero_mul E (rpow E α k)])
    (fun l hl => by
      show E.mul (ι.map (g l)) (rpow E α l) = E.zero
      rw [hg l hl, RingHom.map_zero ι, CRing.zero_mul E (rpow E α l)])

/-! ## M274F-9: 実例 — 恒等 ι での通常の多項式評価 -/

/-- **M274F-9a: 恒等環準同型** R → R。 -/
def evalHomId (R : CRing) : RingHom R R where
  map := fun x => x
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- **M274F-9b: 恒等での評価 = 通常の多項式評価** ev_α(f)|_n = Σ_{i<n} fᵢ·αⁱ。 -/
theorem evalSum_id (R : CRing) (α : R.carrier) (f : PS R) (n : Nat) :
    evalSum (evalHomId R) α f n = rsum R (fun i => R.mul (f i) (rpow R α i)) n :=
  rfl

/-- **M274F-9c: 通常の多項式評価は乗法を保つ**（M274F-8 の ι=恒等の実例）。 -/
theorem evalHom_id_mul (R : CRing) (α : R.carrier) (f g : PS R) (Nf Ng : Nat)
    (hf : IsPolyBounded R f Nf) (hg : IsPolyBounded R g Ng) :
    evalSum (evalHomId R) α (psMul R f g) (Nf + Ng + 1)
      = R.mul (evalSum (evalHomId R) α f Nf) (evalSum (evalHomId R) α g Ng) :=
  evalHom_mul (evalHomId R) α f g Nf Ng hf hg

/-! ## M274F-10: capstone -/

/-- **M274F-10a: 評価準同型の入力データ** — 環準同型 ι:K→E と評価点 α∈E。 -/
structure EvalHomData where
  /-- 係数環 K。 -/
  K : CRing
  /-- 値の住む環 E。 -/
  E : CRing
  /-- 係数埋め込み ι:K→E（本物の評価の入力、toy 主語ではない）。 -/
  iota : RingHom K E
  /-- 評価点 α∈E。 -/
  alpha : E.carrier

/-- **M274F-10b: 評価法則の束**（= M273F PolyEval の defining property を
    多項式・有限台の本物の内容として捉える）。 -/
structure EvalHomProps (D : EvalHomData) : Prop where
  /-- 零の保存。 -/
  ev_zero : ∀ n, evalSum D.iota D.alpha (psZero D.K) n = D.E.zero
  /-- 単位の保存 ev(1)=1。 -/
  ev_one : evalSum D.iota D.alpha (psOne D.K) 1 = D.E.one
  /-- 定数の評価 ev(polyC c)=ι(c)。 -/
  ev_C : ∀ c, evalSum D.iota D.alpha (psC D.K c) 1 = D.iota.map c
  /-- 加法の保存。 -/
  ev_add : ∀ f g n, evalSum D.iota D.alpha (psAdd D.K f g) n
      = D.E.add (evalSum D.iota D.alpha f n) (evalSum D.iota D.alpha g n)
  /-- 乗法の保存（有限台の打ち切り点 Nf+Ng+1）。 -/
  ev_mul : ∀ f g Nf Ng, IsPolyBounded D.K f Nf → IsPolyBounded D.K g Ng →
      evalSum D.iota D.alpha (psMul D.K f g) (Nf + Ng + 1)
        = D.E.mul (evalSum D.iota D.alpha f Nf) (evalSum D.iota D.alpha g Ng)
  /-- 打ち切り安定性。 -/
  ev_stable : ∀ f N, IsPolyBounded D.K f N → ∀ M, N ≤ M →
      evalSum D.iota D.alpha f M = evalSum D.iota D.alpha f N

/-- **M274F-10c: 評価準同型は本物の環準同型（witness）** — 任意の入力
    データ D に対し、評価法則の束が成り立つ。M273F `PolyEval` が仮説として
    要求していた ev の環準同型性を、本層で構成した ev から本物に供給する。 -/
theorem evalHom_isRingHom (D : EvalHomData) : EvalHomProps D where
  ev_zero := fun n => evalHom_zero D.iota D.alpha n
  ev_one := evalHom_one D.iota D.alpha
  ev_C := fun c => evalHom_C D.iota D.alpha c
  ev_add := fun f g n => evalHom_add D.iota D.alpha f g n
  ev_mul := fun f g Nf Ng hf hg => evalHom_mul D.iota D.alpha f g Nf Ng hf hg
  ev_stable := fun f N hN M hM => evalHom_stable D.iota D.alpha f N hN M hM

/-- **M274F-10d: 実例の入力データ** — K=E=ℤ・ι=恒等・α=0。 -/
def evalHomData_int : EvalHomData where
  K := intRing
  E := intRing
  iota := evalHomId intRing
  alpha := intRing.zero

/-- **M274F-10e: 評価準同型データは存在する**（実例 ℤ での通常評価）。 -/
theorem evalHom_exists : Nonempty EvalHomData := ⟨evalHomData_int⟩

end IUT
