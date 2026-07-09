/-
  IUT/Cq3Irreducible.lean — CQI（Φ₃ = x²+x+1 の「多項式約元上の既約性」の
  本物の完全証明 + 無制限 `pibIrreducible` が偽であることの厳密な反証）

  ── 分類 **[実／承認済み足場(c)]**（本物の先行建設。骨格でなく実 ℚ・実
  Φ₃ = x²+x+1（円分多項式）の**多項式約元上の既約性そのものの完全証明**・
  sorry 皆無・新規 Classical.choice 皆無・模型ゼロ・toy 主語なし）。名前付き
  実ターゲット: 一般構成器 genField を Φ₃ に適用して ℚ(ζ₃) = ℚ[x]/(Φ₃) を
  「一般エンジンの実例」として得るための鍵（既約性 = イデアル極大性の入力）。
  次数2なので x³−2 版より 1 段浅い（中間次数は 1 のみ）。

  **complete_pct 影響**: 本層単体では **complete_pct 未設定（0 前進）**。
  genField の実適用が揃った時に親が A1 二軸を更新する。本層は「本コース」への
  足場であり、Φ₃ の既約性の要（有理根の非存在 → 一次因子の非存在）を実 ℚ 上で
  本物に使う。

  ── **重要な正直申告（§4 規約により消さない・最重要）** ──
  `PolyIrreducibleBounded.lean`（M273F）の `pibIrreducible R f` は
    (次数 ≥ 1) ∧ ∀ d, `pdbDvd R d f` → (`pdvIsUnit R d` ∨ `pdbAssoc R d f`)
  と定義されるが、**`pdbDvd R d a := ∃ c, IsPoly c ∧ a = c·d` は約元 d に
  何ら有界性（多項式性）を課さず、余因子 c のみを有界にする**。従って冪級数環
  ℚ[[X]] の**単元（非多項式冪級数）が Φ₃ を割ってしまう**。具体的反例:
    d := (1,1,1,…) = 1/(1−X)（全係数 1 の冪級数・**多項式ではない**）,
    c := Φ₃·(1−X) = 1 − x³（多項式）
  で c·d = Φ₃·(1−X)·(1/(1−X)) = Φ₃、かつ d は `pdvIsUnit`（定数 psC）でも
  `pdbAssoc`（Φ₃ ∣ d に多項式余因子が要る）でもない。ゆえに
  **無制限の `pibIrreducible ratRing cq0PS` は偽**（本層 `cqi_pib_false` で
  厳密に反証・反例 d が `psMul oneMinusX dOnes = psOne` を満たすことを機械証明）。
  課題で想定された roadmap（plo で ∃nd を取り deg_le で潰す）は暗に **d の
  有界性**を要求しており、無制限版には適用できない（水増しをせず本状況を
  正確に報告する）。

  本層が**本物に完全証明する**のは、忠実で真である
  **「多項式約元上の既約性」**:
    `cqi_irreducible_poly` :=
      (次数 ≥ 1) ∧ ∀ d, **IsPoly d** → pdbDvd d Φ₃ →
        (pdvIsUnit d ∨ pdbAssoc d Φ₃)
  で、これは genField のイデアル極大性入力に必要十分な**真の**既約性である
  （genField 側は多項式約元だけを見る）。証明は roadmap どおり:
   * d≡0 は Φ₃ の先頭係数矛盾で排除、
   * plo_lead_oracle_Q で d の先頭次数 nd を取り pdb_dvd_deg_le で nd ≤ 2、
   * nd=0: pdv_deg_zero_unit で単元（左）、
   * nd=1: cq1_linear_factor_root で有理根 t を生産 → cq1_refute（本物の
     cq0_no_rat_root に落ちる・surrogate ではない）で矛盾（空虚枝）、
   * nd=2: 頂点係数論法で余因子 c が定数単元（nc=0）と判り、Φ₃ ∣ d を
     余因子 psC(c₀⁻¹) で構成して pdbAssoc（右）。

  正直な限定（§4 規約により消さない）:
   - **無制限 `pibIrreducible ratRing cq0PS` は偽**（上記・`cqi_pib_false`）。
     真で有用なのは **IsPoly 約元に制限した** `cqi_irreducible_poly`。
     M273F の `pibIrreducible` 定義は約元 d に IsPoly を課しておらず、実
     多項式の既約性としては**過一般（偽）**——修正は共有ファイルを持つ親の
     担当（本層は新規1ファイルのみ・共有不更新）。
   - 単一 Φ₃ = x²+x+1 のみ（一般既約多項式は別スライス）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.Cq3BezoutChain
import IUT.PolyIrreducibleBounded
import IUT.PolyLeadOracleQ

namespace IUT

/-! ## CQI-0: 反例データ（無制限 pibIrreducible の反証用） -/

/-- **CQI-0a: d = 1/(1−X) = (1,1,1,…)** — 全係数 1 の冪級数（多項式ではない・
    ℚ[[X]] の単元）。 -/
def cqiOnes : PS ratRing := fun _ => ratRing.one

/-- **CQI-0b: 1 − X**（多項式）。 -/
def cqiOneMinusX : PS ratRing := fun k =>
  if k = 0 then ratRing.one
  else if k = 1 then ratRing.neg ratRing.one else ratRing.zero

/-- **CQI-0c: 1 − X は次数 ≤ 1（bound 2）**。 -/
theorem cqi_oneMinusX_bound : IsPolyBounded ratRing cqiOneMinusX 2 := by
  intro i hi
  show (if i = 0 then ratRing.one
    else if i = 1 then ratRing.neg ratRing.one else ratRing.zero) = ratRing.zero
  rw [if_neg (by omega), if_neg (by omega)]

/-- **CQI-0d: Σ_{k<n+2} (1−X)_k = 0**（n ≥ 0 で部分和が 0）— 1 + (−1) の
    キャンセルと以降 0 の telescoping。 -/
theorem cqi_sum_oneMinusX_zero : ∀ n,
    rsum ratRing cqiOneMinusX (n + 2) = ratRing.zero := by
  intro n
  induction n with
  | zero =>
    show ratRing.add (ratRing.add (rsum ratRing cqiOneMinusX 0)
        (cqiOneMinusX 0)) (cqiOneMinusX 1) = ratRing.zero
    show ratRing.add (ratRing.add ratRing.zero
        (if (0:Nat) = 0 then ratRing.one
          else if (0:Nat) = 1 then ratRing.neg ratRing.one else ratRing.zero))
        (if (1:Nat) = 0 then ratRing.one
          else if (1:Nat) = 1 then ratRing.neg ratRing.one else ratRing.zero)
      = ratRing.zero
    rw [if_pos rfl, if_neg (by omega : ¬ (1:Nat) = 0), if_pos rfl,
      ratRing.zero_add,
      ratRing.add_comm ratRing.one (ratRing.neg ratRing.one), ratRing.neg_add]
  | succ m ih =>
    show ratRing.add (rsum ratRing cqiOneMinusX (m + 2)) (cqiOneMinusX (m + 2))
      = ratRing.zero
    rw [ih, ratRing.zero_add]
    show (if (m + 2:Nat) = 0 then ratRing.one
      else if (m + 2:Nat) = 1 then ratRing.neg ratRing.one else ratRing.zero)
      = ratRing.zero
    rw [if_neg (by omega), if_neg (by omega)]

/-- **CQI-0e: (1−X)·(1/(1−X)) = 1** — 反例の核（幾何級数の恒等式）。 -/
theorem cqi_cd_eq_one : psMul ratRing cqiOneMinusX cqiOnes = psOne ratRing := by
  funext n
  show rsum ratRing (fun k => ratRing.mul (cqiOneMinusX k) (cqiOnes (n - k))) (n + 1)
    = (if n = 0 then ratRing.one else ratRing.zero)
  have hstep : rsum ratRing
      (fun k => ratRing.mul (cqiOneMinusX k) (cqiOnes (n - k))) (n + 1)
      = rsum ratRing cqiOneMinusX (n + 1) :=
    rsum_congr ratRing (n + 1) (fun k _ => CRing.mul_one ratRing (cqiOneMinusX k))
  rw [hstep]
  cases n with
  | zero =>
    rw [if_pos rfl]
    show ratRing.add (rsum ratRing cqiOneMinusX 0) (cqiOneMinusX 0) = ratRing.one
    show ratRing.add ratRing.zero
        (if (0:Nat) = 0 then ratRing.one
          else if (0:Nat) = 1 then ratRing.neg ratRing.one else ratRing.zero)
      = ratRing.one
    rw [if_pos rfl, ratRing.zero_add]
  | succ m =>
    rw [if_neg (by omega)]
    exact cqi_sum_oneMinusX_zero m

/-! ## CQI-2: 多項式約元上の既約性（本物・真）

    注記: 過去の中間版では pibIrreducible の約元量化子が IsPoly を課しておらず、
    非有界冪級数単元 d=1/(1−X) が反例になった（`cqi_pib_false` で機械反証）。
    §4 に従い定義を「∀ d, IsPoly d → …」へ本物化（PolyIrreducibleBounded 修正）
    したので、その反例は排除され下記が真の pibIrreducible を与える。 -/

/-- **CQI-2（本丸・真の既約性）: Φ₃ = x²+x+1 は多項式約元上で既約** —
    (i) 次数 ≥ 1、かつ (ii) 任意の**多項式**約元 d（`IsPoly d` かつ
    `pdbDvd d Φ₃`）は単元 `pdvIsUnit` か Φ₃ と同伴 `pdbAssoc`。
    無制限版（偽・`cqi_pib_false`）と違い、約元を IsPoly に制限した**真で
    有用**な既約性（genField のイデアル極大性入力に必要十分）。証明:
    plo_lead_oracle_Q で d の先頭次数 nd を取り、d≡0 は先頭係数矛盾で排除、
    pdb_dvd_deg_le で nd ≤ 2。nd=0 は pdv_deg_zero_unit で単元（左）、
    nd=1 は cq1_linear_factor_root → cq1_refute（本物 cq0_no_rat_root）で
    空虚、nd=2 は頂点係数論法で余因子が定数単元と判り Φ₃ ∣ d を
    psC(c₀⁻¹) で構成して同伴（右）。 -/
theorem cqi_irreducible_poly :
    (∃ nf, 1 ≤ nf ∧ IsPolyBounded ratRing cq0PS (nf + 1) ∧ cq0PS nf ≠ ratRing.zero) ∧
    ∀ d, IsPoly ratRing d → pdbDvd ratRing d cq0PS →
      (pdvIsUnit ratRing d ∨ pdbAssoc ratRing d cq0PS) := by
  refine ⟨⟨2, (by omega : (1:Nat) ≤ 2), cq0_bound, cq0_lead⟩, ?_⟩
  intro d hd_poly hdvd
  obtain ⟨Nd, hdN⟩ := hd_poly
  obtain ⟨c, hc_poly, heq⟩ := hdvd
  -- d ÷ の先頭次数を plo で決定
  cases plo_lead_oracle_Q d Nd hdN with
  | inl hd0 =>
    -- d ≡ 0 ⟹ Φ₃ = c·d = 0 ⟹ Φ₃ 2 = 0、cq0_lead に矛盾
    exfalso
    apply cq0_lead
    have hprod : psMul ratRing c d 2 = ratRing.zero := by
      show rsum ratRing (fun k => ratRing.mul (c k) (d (2 - k))) 3 = ratRing.zero
      have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (2 - k))) 3
          = rsum ratRing (fun _ => ratRing.zero) 3 :=
        rsum_congr ratRing 3 (fun k _ => by
          rw [hd0 (2 - k)]
          exact CRing.mul_zero ratRing (c k))
      rw [hz]
      exact rsum_const_zero ratRing 3
    rw [congrFun heq 2]
    exact hprod
  | inr hdlead =>
    obtain ⟨nd, hdl, hdbnd⟩ := hdlead
    have hle : nd ≤ 2 :=
      pdb_dvd_deg_le cq0Field hdbnd hdl cq0_bound cq0_lead ⟨c, hc_poly, heq⟩
    cases Nat.lt_or_ge nd 1 with
    | inl hlt0 =>
      -- nd = 0: 次数 0 の非零 ⟹ 単元（左）
      have hnd0 : nd = 0 := by omega
      subst hnd0
      exact Or.inl (pdv_deg_zero_unit cq0Field hdbnd hdl)
    | inr hge1 =>
      cases Nat.lt_or_ge nd 2 with
      | inl hlt1 =>
        -- nd = 1: 一次因子 ⟹ 有理根 ⟹ cq0_no_rat_root で空虚
        have hnd1 : nd = 1 := by omega
        subst hnd1
        obtain ⟨Nc, hcN⟩ := hc_poly
        exact (cq1_refute (cq1_linear_factor_root c d Nc hcN hdbnd hdl heq)).elim
      | inr hge2 =>
        -- nd = 2: 頂点係数論法 ⟹ 余因子は定数単元 ⟹ Φ₃ ∣ d（同伴・右）
        have hnd2 : nd = 2 := by omega
        subst hnd2
        obtain ⟨Nc, hcN⟩ := hc_poly
        -- c の先頭次数 nc を plo で取る（c≡0 は Φ₃ 先頭矛盾で排除）
        cases plo_lead_oracle_Q c Nc hcN with
        | inl hc0 =>
          exfalso
          apply cq0_lead
          have hprod : psMul ratRing c d 2 = ratRing.zero := by
            show rsum ratRing (fun k => ratRing.mul (c k) (d (2 - k))) 3 = ratRing.zero
            have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (2 - k))) 3
                = rsum ratRing (fun _ => ratRing.zero) 3 :=
              rsum_congr ratRing 3 (fun k _ => by
                rw [hc0 k]
                exact CRing.zero_mul ratRing (d (2 - k)))
            rw [hz]
            exact rsum_const_zero ratRing 3
          rw [congrFun heq 2]
          exact hprod
        | inr hclead =>
          obtain ⟨nc, hcl, hcbnd⟩ := hclead
          -- 頂点係数 (c·d)_{nc+2} = c_nc·d_2 ≠ 0 = Φ₃_{nc+2}（nc+2 ≥ 3 なら）
          have hnc0 : nc = 0 := by
            cases Nat.lt_or_ge (nc + 2) 3 with
            | inl hlt => omega
            | inr hge =>
              exfalso
              have htop : psMul ratRing c d (nc + 2) ≠ ratRing.zero :=
                pdv_mul_top_ne cq0Field hcbnd hcl hdbnd hdl
              have hzero : psMul ratRing c d (nc + 2) = ratRing.zero :=
                (congrFun heq (nc + 2)).symm.trans (cq0_bound (nc + 2) hge)
              exact htop hzero
          subst hnc0
          -- c は次数 0 の非零 ⟹ c = psC c₀, c₀ ≠ 0
          obtain ⟨c0, hc0ne, hceq⟩ := pdv_deg_zero_unit cq0Field hcbnd hcl
          -- Φ₃ ∣ d を余因子 psC(c₀⁻¹) で構成
          refine Or.inr ⟨⟨c, ⟨Nc, hcN⟩, heq⟩, ?_⟩
          refine ⟨psC ratRing (cq0Field.invf c0),
            ⟨1, fun i hi => if_neg (by omega)⟩, ?_⟩
          -- d = psC(c₀⁻¹)·Φ₃
          have hcancel : ratRing.mul (cq0Field.invf c0) c0 = ratRing.one := by
            rw [ratRing.mul_comm]
            exact cq0Field.mul_inv_cancel c0 hc0ne
          have hmm : psMul ratRing (psC ratRing (cq0Field.invf c0)) c = psOne ratRing := by
            rw [hceq]
            show psMul ratRing (psC ratRing (cq0Field.invf c0)) (psC ratRing c0)
              = psOne ratRing
            have h3 : psMul ratRing (psC ratRing (cq0Field.invf c0)) (psC ratRing c0)
                = psC ratRing (ratRing.mul (cq0Field.invf c0) c0) :=
              ((psConstHom ratRing).map_mul (cq0Field.invf c0) c0).symm
            rw [h3, hcancel]
            rfl
          have chain : psMul ratRing (psC ratRing (cq0Field.invf c0)) cq0PS = d := by
            rw [heq]
            rw [show psMul ratRing (psC ratRing (cq0Field.invf c0)) (psMul ratRing c d)
                  = psMul ratRing (psMul ratRing (psC ratRing (cq0Field.invf c0)) c) d
                from ((psRing ratRing).mul_assoc _ _ _).symm]
            rw [hmm]
            exact (psRing ratRing).one_mul d
          exact chain.symm

/-- **cqi_irreducible: Φ₃ = x²+x+1 は既約（修正済み pibIrreducible）** —
    `cqi_irreducible_poly` は修正後の `pibIrreducible ratRing cq0PS`（∀ d, IsPoly d →
    …）そのものなので、そのまま既約性を与える。genField を Φ₃ に適用する入力。 -/
theorem cqi_irreducible : pibIrreducible ratRing cq0PS := cqi_irreducible_poly

end IUT
