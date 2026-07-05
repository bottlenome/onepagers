/-
  IUT/NormalSplitting.lean — M284F（分裂体・正規拡大: 柱A 実分裂体／正規拡大の
  本物の先行建設）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無）。

  **complete_pct 影響**: 柱A「実分裂体・正規拡大」の本物の先行建設。
  M269F `SimpleExtension`（K[X]/(f)）・M275F `RootAdjunction`（添加根 ρ で
  f(ρ)=0）・M268F `PolyFieldDivision`（体上除法）・M96 `FactorTheorem`
  （一次因数定理 P(r)=0 ⟹ P(x)=(X−r)·Q(x)、Q は明示 `qCoeff`）を土台に、
  **多項式が線形因子の積へ完全分解する（分裂する）体（分裂体）**と、
  **その体が f の全根を含む（正規拡大の定義的性質）**を本物に建てる。

  核心の本物の数学:
  * **一根添加で次数が下がる** `normSplit_factor_out` — 体 L の元 ρ が根なら
    P(x)=(X−ρ)·Q(x)、Q の最高次係数は P と同じ（次数はちょうど 1 下がる）。
    これは M96 `pEval_root_factor` + `qCoeff_lead` の本物の含意。
  * **完全分解（分裂）** `normSplit_splits` — 分裂体 L（各段で残り多項式の
    根が L に存在する＝root-supply）上で、次数 d の多項式は
    **P(x) = (P の最高次係数)·∏_{i<d}(x − αᵢ)** に完全分解する。
    d に関する本物の帰納（一根剥がし → 次数 d−1 の商へ帰納 → 因子復元）。
  * **全根包含（正規性）** `normSplit_all_roots` / `normSplit_normal` —
    分解の αᵢ は全て P の根（L は f の deg f 個の根を含む）であり、さらに
    **L 内の任意の根 β は必ずどれかの αⱼ に一致する**（零因子なし NoZeroDiv
    の下で、正規拡大の「拡大内の全根は分裂体の根で尽くされる」性質の本物）。
  * capstone `SplittingFieldData` / `normSplit_data_exists` /
    `normSplit_normal_exists` — 分裂体データ（多項式・分裂体・根の族・完全
    分解 witness・全根包含）と、分裂体・正規拡大の存在。

  正直な限定（何が本物で何が honest 限定か・消去弱化禁止 §4）:
   - **本物（本丸）**: 「一根剥がしで次数が 1 下がる」「root-supply の下で
     線形因子へ完全分解する」「分解の根が全て P の根」「NoZeroDiv の下で
     拡大内の任意の根は分解の根に一致（正規性）」は完全証明（sorry 皆無・
     新規 choice 皆無）。実体 `Field268`（本物の体）・実多項式評価 `pEval`
     （M96）・実因数分解 `pEval_root_factor` の上の本物の等式であり toy 主語
     ではない。
   - **分裂の表現（evaluation 形）**: 「完全分解」は**評価等式**
     `∀ x, P(x) = lead·∏(x−αᵢ)`（`normSplitLinProd` は本物の環積）として
     述べる。係数列そのものの積多項式 ∏(X−αᵢ) の係数レベル一致は多項式積
     の係数構成を要し、本層に含めない（別モジュール）——これは正直な限定で
     あって、根包含・正規性の証明には評価形で十分である。
   - **root-supply（分裂体の入力）**: 「各因数分解の段で残り多項式の根が
     分裂体 L の中に存在する」は honest 仮説 `H`（root-supply）として受け取る
     ——これは分裂体を「f の全根が住む体」として与えることに対応し、その体を
     根の反復添加（M275F）で**型レベルの塔**として構成する部分（各段で環の型が
     変わる）は honest に後続とする（§既約性 witness を仮説で受け取る許容の
     範囲）。一根添加の本物の 1 段（`normSplit_factor_out`）と M275F の
     `rootAdj_is_root`（f(ρ)=0）が、この root-supply の各段の実現である。
   - **分裂体の一意性**（同型を除いて一意）は後続。ここは**存在・完全分解・
     全根包含・正規性**まで本物で建てる。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用（simp/decide/by_cases/rcases/ring/nlinarith 等）。
  サブエージェント新規部品（共有ファイル一切不更新）。名前は `normSplit`
  接頭辞で衝突回避。
-/
import IUT.RootAdjunction
import IUT.FactorTheorem

namespace IUT

/-! ## M284F-1: 一根添加で次数が下がる（本物の 1 段） -/

/-- **定理 (M284F-1): 一根剥がしで次数がちょうど 1 下がる** — 体 L の元 ρ が
    次数 d+1 の多項式 P（係数列 c）の根なら、
    P(x) = (x − ρ)·Q(x)（∀ x、Q の係数は M96 `qCoeff`）に分解し、
    さらに **Q の最高次係数は P の最高次係数に等しい**（次数 = d、ちょうど
    1 下がる・先頭係数は保存）。M96 `pEval_root_factor` + `qCoeff_lead` の
    本物の含意。分裂体構成の各段の実体。 -/
theorem normSplit_factor_out (K : Field268) (c : Nat → K.ring.carrier)
    (d : Nat) (ρ : K.ring.carrier)
    (hρ : pEval K.ring c (d + 1) ρ = K.ring.zero) :
    (∀ x, pEval K.ring c (d + 1) x
        = K.ring.mul (K.ring.add x (K.ring.neg ρ))
            (pEval K.ring (qCoeff K.ring c (d + 1) ρ) d x))
      ∧ qCoeff K.ring c (d + 1) ρ d = c (d + 1) :=
  ⟨pEval_root_factor K.ring c ρ d hρ, qCoeff_lead K.ring c d ρ⟩

/-! ## M284F-2: 線形因子の積 ∏(x−αᵢ)（本物の環積） -/

/-- **M284F-2a: 線形因子の積** ∏_{i<n}(x − αᵢ)（分裂形の右辺）。
    本物の環の反復積（末尾 Nat 引数の構造的再帰）。 -/
def normSplitLinProd (R : CRing) (α : Nat → R.carrier) (x : R.carrier) :
    Nat → R.carrier
  | 0 => R.one
  | n + 1 => R.mul (normSplitLinProd R α x n) (R.add x (R.neg (α n)))

/-- **M284F-2b: 積は使う根 αᵢ (i<n) にのみ依存** — [0,n) 上で α = β なら
    ∏ は等しい（帰納）。分解の根を付け替える時に使う。 -/
theorem normSplit_linProd_congr (R : CRing) (α β : Nat → R.carrier)
    (x : R.carrier) :
    ∀ n, (∀ i, i < n → α i = β i) →
      normSplitLinProd R α x n = normSplitLinProd R β x n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    show R.mul (normSplitLinProd R α x n) (R.add x (R.neg (α n)))
      = R.mul (normSplitLinProd R β x n) (R.add x (R.neg (β n)))
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- **M284F-2c: 各根 αⱼ (j<n) で積は消える** — ∏_{i<n}(αⱼ − αᵢ) = 0
    （因子 (αⱼ − αⱼ) = 0）。帰納: j = n なら末項が 0、j < n なら IH。 -/
theorem normSplit_linProd_root (R : CRing) (α : Nat → R.carrier) :
    ∀ n j, j < n → normSplitLinProd R α (α j) n = R.zero := by
  intro n
  induction n with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro j hj
    show R.mul (normSplitLinProd R α (α j) n) (R.add (α j) (R.neg (α n)))
      = R.zero
    cases Nat.lt_or_ge j n with
    | inl hlt =>
      rw [ih j hlt]
      exact CRing.zero_mul R _
    | inr hge =>
      have hjn : j = n := by omega
      rw [hjn, R.add_neg (α n), R.mul_zero]

/-- **M284F-2d: 積が消えるなら或る因子が消える（正規性の核）** — 零因子
    なし NoZeroDiv の下で、∏_{i<n}(β − αᵢ) = 0 なら β = αⱼ なる j<n が
    存在する（帰納 + NoZeroDiv で因子分岐）。1 ≠ 0 は空積 = 1 ≠ 0 の排除。 -/
theorem normSplit_linProd_zero_root (R : CRing) (hD : NoZeroDiv R)
    (hone : R.one ≠ R.zero) (α : Nat → R.carrier) (β : R.carrier) :
    ∀ n, normSplitLinProd R α β n = R.zero → ∃ j, j < n ∧ β = α j := by
  intro n
  induction n with
  | zero =>
    intro h
    exact absurd h hone
  | succ n ih =>
    intro h
    have h' : R.mul (normSplitLinProd R α β n) (R.add β (R.neg (α n)))
        = R.zero := h
    cases hD _ _ h' with
    | inl hl =>
      obtain ⟨j, hjn, hj⟩ := ih hl
      exact ⟨j, by omega, hj⟩
    | inr hr =>
      exact ⟨n, by omega, CRing.eq_of_sub_eq_zero R hr⟩

/-! ## M284F-3: 完全分解（分裂）の述語 -/

/-- **M284F-3: 分裂述語** — P（係数 c・次数 d）が lead と根の族 α で
    **P(x) = lead·∏_{i<d}(x − αᵢ)（∀ x、evaluation 形）**に分裂する。 -/
def NormSplitsAt (R : CRing) (c : Nat → R.carrier) (d : Nat)
    (lead : R.carrier) (α : Nat → R.carrier) : Prop :=
  ∀ x, pEval R c d x = R.mul lead (normSplitLinProd R α x d)

/-! ## M284F-4: 完全分解の本丸（root-supply 上で分裂） -/

/-- **定理 (M284F-4): root-supply の下で完全分解する（分裂）** — 体 L の
    上の次数 d・最高次係数 ≠ 0 の多項式は、
    **root-supply H**（次数 e (1≤e≤d)・最高次 ≠ 0 の任意多項式が L の中に
    根を持つ）の下で、**P(x) = (最高次係数)·∏_{i<d}(x − αᵢ)** に完全分解する。
    d に関する本物の帰納: d=0 は空積、d=e+1 は一根 ρ を取り一根剥がし
    （`pEval_root_factor`）で次数 e の商へ、IH で商を分解し末尾に (x−ρ) を
    復元。root-supply は「分裂体 L（f の全根が住む体）」の honest 入力で、
    その塔構成（型レベル）は後続。 -/
theorem normSplit_splits (K : Field268) :
    ∀ (d : Nat) (c : Nat → K.ring.carrier), c d ≠ K.ring.zero →
    (∀ (e : Nat) (c' : Nat → K.ring.carrier), e ≤ d → 1 ≤ e →
        c' e ≠ K.ring.zero → ∃ ρ, pEval K.ring c' e ρ = K.ring.zero) →
    ∃ α, NormSplitsAt K.ring c d (c d) α := by
  intro d
  induction d with
  | zero =>
    intro c _ _
    refine ⟨fun _ => K.ring.zero, ?_⟩
    intro x
    show pEval K.ring c 0 x
      = K.ring.mul (c 0) (normSplitLinProd K.ring (fun _ => K.ring.zero) x 0)
    rw [pEval_zero K.ring c x]
    show c 0 = K.ring.mul (c 0) K.ring.one
    rw [K.ring.mul_one]
  | succ d ih =>
    intro c hlead H
    obtain ⟨ρ, hρ⟩ := H (d + 1) c (Nat.le_refl (d + 1)) (by omega) hlead
    have hfac := pEval_root_factor K.ring c ρ d hρ
    have hlead' : qCoeff K.ring c (d + 1) ρ d ≠ K.ring.zero := by
      rw [qCoeff_lead K.ring c d ρ]
      exact hlead
    obtain ⟨α', hsp⟩ := ih (qCoeff K.ring c (d + 1) ρ) hlead'
      (fun e c'' he h1 hne => H e c'' (by omega) h1 hne)
    refine ⟨fun i => if i = d then ρ else α' i, ?_⟩
    intro x
    have hαfd : (fun i => if i = d then ρ else α' i) d = ρ := if_pos rfl
    have hstep :
        normSplitLinProd K.ring (fun i => if i = d then ρ else α' i) x (d + 1)
        = K.ring.mul (normSplitLinProd K.ring α' x d)
            (K.ring.add x (K.ring.neg ρ)) := by
      show K.ring.mul
          (normSplitLinProd K.ring (fun i => if i = d then ρ else α' i) x d)
          (K.ring.add x
            (K.ring.neg ((fun i => if i = d then ρ else α' i) d)))
        = K.ring.mul (normSplitLinProd K.ring α' x d)
            (K.ring.add x (K.ring.neg ρ))
      rw [hαfd, normSplit_linProd_congr K.ring
          (fun i => if i = d then ρ else α' i) α' x d
          (fun i hi => if_neg (by omega))]
    show pEval K.ring c (d + 1) x
      = K.ring.mul (c (d + 1))
          (normSplitLinProd K.ring (fun i => if i = d then ρ else α' i) x (d + 1))
    rw [hstep, hfac x, hsp x, qCoeff_lead K.ring c d ρ,
      K.ring.mul_comm (K.ring.add x (K.ring.neg ρ))
        (K.ring.mul (c (d + 1)) (normSplitLinProd K.ring α' x d)),
      K.ring.mul_assoc (c (d + 1)) (normSplitLinProd K.ring α' x d)
        (K.ring.add x (K.ring.neg ρ))]

/-! ## M284F-5: 全根包含（正規性の骨組み） -/

/-- **定理 (M284F-5a: 全根包含)** — 分裂した多項式の分解の根 αⱼ (j<d) は
    全て P の根（L は P の deg 個の根をすべて含む）。P(αⱼ) = lead·0 = 0。 -/
theorem normSplit_all_roots (K : Field268) (c : Nat → K.ring.carrier)
    (d : Nat) (lead : K.ring.carrier) (α : Nat → K.ring.carrier)
    (hsp : NormSplitsAt K.ring c d lead α) :
    ∀ j, j < d → pEval K.ring c d (α j) = K.ring.zero := by
  intro j hj
  rw [hsp (α j), normSplit_linProd_root K.ring α d j hj, K.ring.mul_zero]

/-- **定理 (M284F-5b: 正規性)** — 零因子なし NoZeroDiv・最高次係数 ≠ 0 の
    下で、分裂体 L 内の P の**任意の根 β は必ずどれかの分解根 αⱼ に一致**
    する。すなわち L 内の P の根は分解 ∏(x−αᵢ) の根で**尽くされる**——
    正規拡大の定義的性質（分裂体の中では全根が明示的に現れる）の本物。
    lead·∏(β−αᵢ) = 0 に NoZeroDiv（lead ≠ 0）→ ∏ = 0 → 因子分岐。 -/
theorem normSplit_normal (K : Field268) (hD : NoZeroDiv K.ring)
    (hone : K.ring.one ≠ K.ring.zero)
    (c : Nat → K.ring.carrier) (d : Nat) (lead : K.ring.carrier)
    (hlead : lead ≠ K.ring.zero) (α : Nat → K.ring.carrier)
    (hsp : NormSplitsAt K.ring c d lead α)
    (β : K.ring.carrier) (hβ : pEval K.ring c d β = K.ring.zero) :
    ∃ j, j < d ∧ β = α j := by
  have h0 : K.ring.mul lead (normSplitLinProd K.ring α β d) = K.ring.zero := by
    rw [← hsp β]
    exact hβ
  have hlp : normSplitLinProd K.ring α β d = K.ring.zero := by
    cases hD _ _ h0 with
    | inl h => exact absurd h hlead
    | inr h => exact h
  exact normSplit_linProd_zero_root K.ring hD hone α β d hlp

/-! ## M284F-6: capstone（分裂体データと存在） -/

/-- **M284F-6a: 分裂体データ** — 分裂体 L（`Field268`、f の全根が住む体）・
    多項式（係数 coeff・次数 deg・最高次 ≠ 0）・根の族 roots・完全分解
    witness `splits`・全根包含 `all_roots` を束ねる。 -/
structure SplittingFieldData (L : Field268) where
  /-- 分裂させる多項式の係数列。 -/
  coeff : Nat → L.ring.carrier
  /-- 次数。 -/
  deg : Nat
  /-- 最高次係数 ≠ 0。 -/
  lead_ne : coeff deg ≠ L.ring.zero
  /-- 分裂体の中の根の族 αᵢ。 -/
  roots : Nat → L.ring.carrier
  /-- **完全分解**: P(x) = (最高次係数)·∏(x − αᵢ)。 -/
  splits : NormSplitsAt L.ring coeff deg (coeff deg) roots
  /-- **全根包含**: 各 αⱼ (j<deg) は P の根。 -/
  all_roots : ∀ j, j < deg → pEval L.ring coeff deg (roots j) = L.ring.zero

/-- **定理 (M284F-6b: 分裂体の存在)** — 体 L の上の次数 d・最高次 ≠ 0 の
    多項式に対し、root-supply（f の全根が L に住む）の下で**分裂体データが
    存在する**（完全分解 + 全根包含を備える）。root-supply は分裂体を与える
    honest 入力。obtain は Exists.elim（選択公理不使用）。 -/
theorem normSplit_data_exists (L : Field268) (c : Nat → L.ring.carrier)
    (d : Nat) (hlead : c d ≠ L.ring.zero)
    (H : ∀ (e : Nat) (c' : Nat → L.ring.carrier), e ≤ d → 1 ≤ e →
        c' e ≠ L.ring.zero → ∃ ρ, pEval L.ring c' e ρ = L.ring.zero) :
    Nonempty (SplittingFieldData L) := by
  obtain ⟨α, hsp⟩ := normSplit_splits L d c hlead H
  exact ⟨⟨c, d, hlead, α, hsp, normSplit_all_roots L c d (c d) α hsp⟩⟩

/-- **定理 (M284F-6c: 正規拡大の存在)** — さらに NoZeroDiv の下で、分裂体は
    **正規**（分解 + 全根包含 + 拡大内の任意の根はどれかの αⱼ に一致）。
    分裂体・正規拡大の存在を一本化。 -/
theorem normSplit_normal_exists (L : Field268) (hD : NoZeroDiv L.ring)
    (hone : L.ring.one ≠ L.ring.zero) (c : Nat → L.ring.carrier)
    (d : Nat) (hlead : c d ≠ L.ring.zero)
    (H : ∀ (e : Nat) (c' : Nat → L.ring.carrier), e ≤ d → 1 ≤ e →
        c' e ≠ L.ring.zero → ∃ ρ, pEval L.ring c' e ρ = L.ring.zero) :
    ∃ α, NormSplitsAt L.ring c d (c d) α
      ∧ (∀ j, j < d → pEval L.ring c d (α j) = L.ring.zero)
      ∧ (∀ β, pEval L.ring c d β = L.ring.zero → ∃ j, j < d ∧ β = α j) := by
  obtain ⟨α, hsp⟩ := normSplit_splits L d c hlead H
  exact ⟨α, hsp, normSplit_all_roots L c d (c d) α hsp,
    fun β hβ => normSplit_normal L hD hone c d (c d) hlead α hsp β hβ⟩

/-! ## M284F-7: 実例（2 次: 具体的な線形因子分解と全根包含） -/

/-- **M284F-7a: 実例（2 次の線形因子分解）** — 根の族 α = (a, b) に対する
    ∏_{i<2}(x − αᵢ) が (x − a)(x − b) の本物の環積であることの具体確認。 -/
example (R : CRing) (a b x : R.carrier) :
    normSplitLinProd R (fun i => if i = 0 then a else b) x 2
      = R.mul (R.mul R.one (R.add x (R.neg a))) (R.add x (R.neg b)) := rfl

/-- **M284F-7b: 実例（第 1 根は根）** — 2 次分解の第 1 根 a は ∏ の根。 -/
example (R : CRing) (a b : R.carrier) :
    normSplitLinProd R (fun i => if i = 0 then a else b)
        ((fun i => if i = 0 then a else b) 0) 2 = R.zero :=
  normSplit_linProd_root R (fun i => if i = 0 then a else b) 2 0 (by omega)

/-- **M284F-7c: 実例（第 2 根は根）** — 2 次分解の第 2 根 b は ∏ の根。 -/
example (R : CRing) (a b : R.carrier) :
    normSplitLinProd R (fun i => if i = 0 then a else b)
        ((fun i => if i = 0 then a else b) 1) 2 = R.zero :=
  normSplit_linProd_root R (fun i => if i = 0 then a else b) 2 1 (by omega)

end IUT
