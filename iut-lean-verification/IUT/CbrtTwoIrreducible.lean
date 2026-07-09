/-
  IUT/CbrtTwoIrreducible.lean — CTI（A1 実数体 ℚ(∛2) = ℚ[x]/(x³−2) の
  「多項式約元上の既約性」の本物の完全証明。修正済み `pibIrreducible`
  （約元 d に IsPoly を課す版）の下で x³−2 が既約であることを機械証明する。）

  ── 分類 **[実／承認済み足場(c)]**（本物の先行建設。骨格でなく実 ℚ・実
  f = x³−2 の**多項式約元上の既約性そのものの完全証明**・sorry 皆無・
  新規 Classical.choice 皆無・模型ゼロ・toy 主語なし）。名前付き実ターゲット:
  一般構成器 genField を x³−2 に適用して ℚ(∛2) = ℚ[x]/(x³−2) を得るための
  鍵（既約性 = イデアル極大性の入力）。Φ₃ 次数2版（`Cq3Irreducible`）を
  次数3へ写した層。中間次数が 1 と 2 の二段あるぶん Φ₃ 版より 1 段深い。

  **complete_pct 影響**: 本層単体では **complete_pct 未設定（0 前進）**。
  genField の実適用が揃った時に親が A1 二軸を更新する。本層は「本コース」への
  足場であり、x³−2 の既約性の要（有理立方根の非存在 ∛2 ∉ ℚ → 一次因子・
  二次因子の非存在）を実 ℚ 上で本物に使う。

  ── **重要な設計上の注記（§4 規約により消さない）** ──
  `PolyIrreducibleBounded.lean`（M273F）の `pibIrreducible R f` は
    (次数 ≥ 1) ∧ ∀ d, **IsPoly R d →** pdbDvd R d f → (pdvIsUnit R d ∨ pdbAssoc R d f)
  と、**約元 d に IsPoly（有界＝真の多項式）を課す**形へ本物化されている。
  旧版の本ファイルは d に IsPoly を課さない過一般 `pibIrreducible` を反証
  （`cti_pib_false`）していたが、定義修正でその反例（非有界冪級数単元
  d = 1+X+X²+…）は排除され、下記が真の `pibIrreducible ratRing ct0PS` を
  与える。証明は Φ₃ 版 roadmap の次数3版:
   * d≡0 は ct0PS の先頭係数矛盾で排除、
   * plo_lead_oracle_Q で d の先頭次数 nd を取り pdb_dvd_deg_le で nd ≤ 3、
   * nd=0: pdv_deg_zero_unit で単元（左）、
   * nd=1: d が一次因子 ⟹ clf_linear_factor_root で ∃t, t³=2 ⟹ crt_no_rat_cube
     （∀t, t³≠2）で矛盾（空虚枝）、
   * nd=2: d が二次因子 ⟹ 余因子 c は頂点係数論法で一次（nc=1）と判り、
     c が一次因子 ⟹ clf_linear_factor_root で ∃t, t³=2 ⟹ 矛盾（空虚枝）、
   * nd=3: d と ct0PS 同次数 ⟹ 頂点係数論法で余因子 c は定数単元（nc=0）と
     判り、ct0PS ∣ d を余因子 psC(c₀⁻¹) で構成して pdbAssoc（右）。

  正直な限定（§4 規約により消さない）:
   - 有理立方根なし（x³−2 の一次因子・二次因子なし）は本物の
     `crt_no_rat_cube`（∛2 ∉ ℚ）に本当に落ちる（surrogate ではない）。
   - 単一 f = x³−2 のみ（一般既約多項式は別スライス）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.CbrtLinearFactor
import IUT.CubeRootTwoIrrational
import IUT.PolyIrreducibleBounded
import IUT.PolyLeadOracleQ

namespace IUT

/-! ## CTI-0: refutation アダプタ（一次因子 ⟹ 有理立方根 ⟹ 矛盾） -/

/-- **CTI-0a: ct0Two = ratOfTwo**（実 ℚ の 2 の二表示の一致・proof irrelevance）。 -/
theorem cti_two_eq : ct0Two = ratOfTwo := rfl

/-- **CTI-0b: refutation アダプタ** — `clf_linear_factor_root` の生産物
    `∃ t, t·(t·t) = ct0Two`（= t³ = 2）を `crt_no_rat_cube`（`∀ r, r³ ≠ 2`）で
    反駁して False を得る（本物の ∛2 ∉ ℚ に落ちる・surrogate ではない）。
    `Cq3Irreducible` の `cq1_refute` の次数3版（有理根 → 有理立方根）。 -/
theorem cti_refute
    (h : ∃ t : QRat, ratRing.mul t (ratRing.mul t t) = ct0Two) : False := by
  obtain ⟨t, ht⟩ := h
  apply crt_no_rat_cube t
  have hcomm : ratRing.mul (ratRing.mul t t) t = ratRing.mul t (ratRing.mul t t) :=
    (ratRing.mul_comm t (ratRing.mul t t)).symm
  rw [hcomm, ht]
  exact cti_two_eq

/-! ## CTI-1: 多項式約元上の既約性（本物・真）

    修正済み `pibIrreducible`（約元 d に IsPoly を課す版）の下で x³−2 が
    既約であることの完全証明。`Cq3Irreducible.cqi_irreducible_poly` の
    次数3版（中間次数 1・2 の二段 + 同伴の nd=3 枝）。 -/

/-- **CTI-1（本丸・真の既約性）: x³−2 は多項式約元上で既約** —
    (i) 次数 ≥ 1、かつ (ii) 任意の**多項式**約元 d（`IsPoly d` かつ
    `pdbDvd d ct0PS`）は単元 `pdvIsUnit` か x³−2 と同伴 `pdbAssoc`。証明:
    plo_lead_oracle_Q で d の先頭次数 nd を取り、d≡0 は先頭係数矛盾で排除、
    pdb_dvd_deg_le で nd ≤ 3。nd=0 は pdv_deg_zero_unit で単元（左）、
    nd=1 は clf_linear_factor_root → cti_refute（本物 crt_no_rat_cube）で
    空虚、nd=2 は頂点係数論法で余因子が一次（nc=1）と判り
    clf_linear_factor_root → cti_refute で空虚、nd=3 は頂点係数論法で余因子が
    定数単元と判り x³−2 ∣ d を psC(c₀⁻¹) で構成して同伴（右）。 -/
theorem cti_irreducible_poly :
    (∃ nf, 1 ≤ nf ∧ IsPolyBounded ratRing ct0PS (nf + 1) ∧ ct0PS nf ≠ ratRing.zero) ∧
    ∀ d, IsPoly ratRing d → pdbDvd ratRing d ct0PS →
      (pdvIsUnit ratRing d ∨ pdbAssoc ratRing d ct0PS) := by
  refine ⟨⟨3, (by omega : (1:Nat) ≤ 3), ct0_bound, ct0_lead⟩, ?_⟩
  intro d hd_poly hdvd
  obtain ⟨Nd, hdN⟩ := hd_poly
  obtain ⟨c, hc_poly, heq⟩ := hdvd
  -- d の先頭次数を plo で決定
  cases plo_lead_oracle_Q d Nd hdN with
  | inl hd0 =>
    -- d ≡ 0 ⟹ x³−2 = c·d = 0 ⟹ (x³−2) 3 = 0、ct0_lead に矛盾
    exfalso
    apply ct0_lead
    have hprod : psMul ratRing c d 3 = ratRing.zero := by
      show rsum ratRing (fun k => ratRing.mul (c k) (d (3 - k))) 4 = ratRing.zero
      have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (3 - k))) 4
          = rsum ratRing (fun _ => ratRing.zero) 4 :=
        rsum_congr ratRing 4 (fun k _ => by
          rw [hd0 (3 - k)]
          exact CRing.mul_zero ratRing (c k))
      rw [hz]
      exact rsum_const_zero ratRing 4
    rw [congrFun heq 3]
    exact hprod
  | inr hdlead =>
    obtain ⟨nd, hdl, hdbnd⟩ := hdlead
    have hle : nd ≤ 3 :=
      pdb_dvd_deg_le ct0Field hdbnd hdl ct0_bound ct0_lead ⟨c, hc_poly, heq⟩
    cases Nat.lt_or_ge nd 1 with
    | inl hlt0 =>
      -- nd = 0: 次数 0 の非零 ⟹ 単元（左）
      have hnd0 : nd = 0 := by omega
      subst hnd0
      exact Or.inl (pdv_deg_zero_unit ct0Field hdbnd hdl)
    | inr hge1 =>
      cases Nat.lt_or_ge nd 2 with
      | inl hlt1 =>
        -- nd = 1: 一次因子 ⟹ 有理立方根 ⟹ crt_no_rat_cube で空虚
        have hnd1 : nd = 1 := by omega
        subst hnd1
        obtain ⟨Nc, hcN⟩ := hc_poly
        exact (cti_refute (clf_linear_factor_root c d Nc hcN hdbnd hdl heq)).elim
      | inr hge2 =>
        cases Nat.lt_or_ge nd 3 with
        | inl hlt2 =>
          -- nd = 2: 二次因子 ⟹ 余因子 c は一次（nc=1）⟹ clf → cti_refute で空虚
          have hnd2 : nd = 2 := by omega
          subst hnd2
          obtain ⟨Nc, hcN⟩ := hc_poly
          -- c の先頭次数 nc を plo で取る（c≡0 は ct0PS 先頭矛盾で排除）
          cases plo_lead_oracle_Q c Nc hcN with
          | inl hc0 =>
            exfalso
            apply ct0_lead
            have hprod : psMul ratRing c d 3 = ratRing.zero := by
              show rsum ratRing (fun k => ratRing.mul (c k) (d (3 - k))) 4 = ratRing.zero
              have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (3 - k))) 4
                  = rsum ratRing (fun _ => ratRing.zero) 4 :=
                rsum_congr ratRing 4 (fun k _ => by
                  rw [hc0 k]
                  exact CRing.zero_mul ratRing (d (3 - k)))
              rw [hz]
              exact rsum_const_zero ratRing 4
            rw [congrFun heq 3]
            exact hprod
          | inr hclead =>
            obtain ⟨nc, hcl, hcbnd⟩ := hclead
            -- 頂点係数 (c·d)_{nc+2} = c_nc·d_2 ≠ 0 = (x³−2)_{nc+2}（nc≠1 なら）で nc=1 を pin
            have htop : psMul ratRing c d (nc + 2) ≠ ratRing.zero :=
              pdv_mul_top_ne ct0Field hcbnd hcl hdbnd hdl
            have htop' : ct0PS (nc + 2) ≠ ratRing.zero := by
              rw [heq]; exact htop
            have hnc1 : nc = 1 := by
              cases Nat.lt_or_ge nc 1 with
              | inl h0 =>
                exfalso
                have hnc0 : nc = 0 := by omega
                subst hnc0
                exact absurd ct0PS_coeff2 htop'
              | inr hge1' =>
                cases Nat.lt_or_ge nc 2 with
                | inl h1 => omega
                | inr hge2' =>
                  exfalso
                  exact htop' (ct0_bound (nc + 2) (by omega))
            subst hnc1
            -- c は一次因子（bound 2・c 1 ≠ 0）。heq を並べ替えて clf → cti_refute
            have heq' : ct0PS = psMul ratRing d c :=
              heq.trans ((psRing ratRing).mul_comm c d)
            exact (cti_refute
              (clf_linear_factor_root d c 3 hdbnd hcbnd hcl heq')).elim
        | inr hge3 =>
          -- nd = 3: 頂点係数論法 ⟹ 余因子は定数単元 ⟹ x³−2 ∣ d（同伴・右）
          have hnd3 : nd = 3 := by omega
          subst hnd3
          obtain ⟨Nc, hcN⟩ := hc_poly
          -- c の先頭次数 nc を plo で取る（c≡0 は ct0PS 先頭矛盾で排除）
          cases plo_lead_oracle_Q c Nc hcN with
          | inl hc0 =>
            exfalso
            apply ct0_lead
            have hprod : psMul ratRing c d 3 = ratRing.zero := by
              show rsum ratRing (fun k => ratRing.mul (c k) (d (3 - k))) 4 = ratRing.zero
              have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (3 - k))) 4
                  = rsum ratRing (fun _ => ratRing.zero) 4 :=
                rsum_congr ratRing 4 (fun k _ => by
                  rw [hc0 k]
                  exact CRing.zero_mul ratRing (d (3 - k)))
              rw [hz]
              exact rsum_const_zero ratRing 4
            rw [congrFun heq 3]
            exact hprod
          | inr hclead =>
            obtain ⟨nc, hcl, hcbnd⟩ := hclead
            -- 頂点係数 (c·d)_{nc+3} = c_nc·d_3 ≠ 0 = (x³−2)_{nc+3}（nc+3 ≥ 4 なら）
            have hnc0 : nc = 0 := by
              cases Nat.lt_or_ge (nc + 3) 4 with
              | inl hlt => omega
              | inr hge =>
                exfalso
                have htop : psMul ratRing c d (nc + 3) ≠ ratRing.zero :=
                  pdv_mul_top_ne ct0Field hcbnd hcl hdbnd hdl
                have hzero : psMul ratRing c d (nc + 3) = ratRing.zero :=
                  (congrFun heq (nc + 3)).symm.trans (ct0_bound (nc + 3) hge)
                exact htop hzero
            subst hnc0
            -- c は次数 0 の非零 ⟹ c = psC c₀, c₀ ≠ 0
            obtain ⟨c0, hc0ne, hceq⟩ := pdv_deg_zero_unit ct0Field hcbnd hcl
            -- x³−2 ∣ d を余因子 psC(c₀⁻¹) で構成
            refine Or.inr ⟨⟨c, ⟨Nc, hcN⟩, heq⟩, ?_⟩
            refine ⟨psC ratRing (ct0Field.invf c0),
              ⟨1, fun i hi => if_neg (by omega)⟩, ?_⟩
            -- d = psC(c₀⁻¹)·(x³−2)
            have hcancel : ratRing.mul (ct0Field.invf c0) c0 = ratRing.one := by
              rw [ratRing.mul_comm]
              exact ct0Field.mul_inv_cancel c0 hc0ne
            have hmm : psMul ratRing (psC ratRing (ct0Field.invf c0)) c = psOne ratRing := by
              rw [hceq]
              show psMul ratRing (psC ratRing (ct0Field.invf c0)) (psC ratRing c0)
                = psOne ratRing
              have h3 : psMul ratRing (psC ratRing (ct0Field.invf c0)) (psC ratRing c0)
                  = psC ratRing (ratRing.mul (ct0Field.invf c0) c0) :=
                ((psConstHom ratRing).map_mul (ct0Field.invf c0) c0).symm
              rw [h3, hcancel]
              rfl
            have chain : psMul ratRing (psC ratRing (ct0Field.invf c0)) ct0PS = d := by
              rw [heq]
              rw [show psMul ratRing (psC ratRing (ct0Field.invf c0)) (psMul ratRing c d)
                    = psMul ratRing (psMul ratRing (psC ratRing (ct0Field.invf c0)) c) d
                  from ((psRing ratRing).mul_assoc _ _ _).symm]
              rw [hmm]
              exact (psRing ratRing).one_mul d
            exact chain.symm

/-- **cti_irreducible: x³−2 は既約（修正済み pibIrreducible）** —
    `cti_irreducible_poly` は修正後の `pibIrreducible ratRing ct0PS`（∀ d, IsPoly d →
    …）そのものなので、そのまま既約性を与える。genField を x³−2 に適用する入力。 -/
theorem cti_irreducible : pibIrreducible ratRing ct0PS := cti_irreducible_poly

end IUT

#print axioms IUT.cti_irreducible
