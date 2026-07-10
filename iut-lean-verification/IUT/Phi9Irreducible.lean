/-
  IUT/Phi9Irreducible.lean — E4′ 後半（Φ_9 の既約性証明と ℚ(ζ_9) 体構成）

  A3 円分塔 ℚ ⊂ ℚ(ζ_9) の法多項式 Φ_9 = x⁶+x³+1 の既約性を、Eisenstein 判定器
  E3（`eis_irreducible`）とシフト像 E4′前半（`Phi9Shift`）を接続して本物に閉じる。
  設計 audit/A3-cyclotomic-tower-detail-2026-07-09.md §1.2 E4′ ステップ 4・5 の実装:
   * ステップ4: Φ_9(x+1) = x⁶+6x⁵+15x⁴+21x³+18x²+9x+3 の係数 (3,9,18,21,15,6,1)
     について p = 3 の Eisenstein 入力（v₃(3)=1・中間 v₃≥1・先頭 v₃=0）を
     `pvqNatVal_spec` の具体代入（9=3²·1, 18=3²·2, 21=3·7, 15=3·5, 6=3·2）で本物に検証し、
     `eis_irreducible` へ投入して `p9i_shifted_irreducible : pibIrreducible ratRing p9eShifted`。
   * ステップ5（逆シフト不要の片道輸送）: Φ_9 = c·d（有界余因子整除 pdbDvd）とすると、
     評価準同型 `evalHom_mul`（シフトの乗法性）と打切安定 `evalHom_stable`・シフト像照合
     `p9e_shift_eq` で p9eShifted = (p9eShift c)·(p9eShift d)。シフトは次数保存
     （`p9i_shift_deg`）なので、p9eShifted の既約性から d の像 p9eShift d は単元
     （⟹ d 次数 0 ⟹ d 単元）か同伴（⟹ d 次数 6 ⟹ 余因子 c 定数単元 ⟹ pdbAssoc）。
     逆方向シフト・合成恒等式は一切不要。⟹ `p9i_irreducible : pibIrreducible ratRing cpdPhi9`。
   * 仕上げ: `p9iPhi9Field : IUTField`（ℚ[x]/(Φ_9) = ℚ(ζ_9)）と
     `p9iExt9 : FieldExtension`（ℚ↪ℚ(ζ_9) の次数 6 拡大）を 1 行ずつ。

  ── 分類 **[実／本物建設(b)]**（本物の先行建設。実 Φ_9 = x⁶+x³+1 の
  多項式約元上の既約性の完全証明そのもの。骨格・模型・代理・toy 主語なし。
  sorry 皆無・新規 Classical.choice 皆無・禁止タクティク不使用）。

  **complete_pct 影響**: A3——Φ_9 既約性の完成で ℚ(ζ_9) = ℚ[x]/(Φ_9)（次数 6 拡大）を
  実 IUTField（`gefNFIUTField`）として構成し、円分塔 2 段目の体が本物に立つ
  （res₁ = W-C の直接の前提）。本ファイル単体では complete_pct 未設定
  （W-C 到達＝res 構成で A3 を動かす・独立監査確定）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   - **本物**: Φ_9 の既約性 `p9i_irreducible : pibIrreducible ratRing cpdPhi9` は
     E3（有理係数 Eisenstein 判定器）とシフト同型（実 evalSum）越しの完全証明。
     模型・代理なし。ℚ(ζ_9) 体 `p9iPhi9Field` と拡大 `p9iExt9` は実 IUTField。
   - **部分ケースであること（消さない）**: p = 3・円分塔 2 段目（ℚ(ζ_9)）の体の
     構成のみ。制限準同型 res・塔・逆極限は W-C 以降（本ファイルの射程外）。
   - **E3 の正規化形の継承**: `eis_irreducible` は「先頭 v = 0・定数 v = 1」の
     正規化形での判定器であり、本ファイルは Φ_9 のシフト像の具体係数でこれを満たす。
   - シフトの乗法性 `evalHom_mul` は有限台の打切点で述べる（EvaluationHom の
     honest 限定を継承・打切安定 `evalHom_stable` で照合）。

  全て選択公理不使用（propext/Quot.sound のみ）。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.EisensteinCriterionQ
import IUT.Phi9Shift
import IUT.GenExtTower

namespace IUT

/-! ## P9I-0: 数値素性補題（3 が特定の小数を割らない） -/

/-- ¬ 3 ∣ 1。 -/
theorem p9i_not3dvd1 : ¬ (3 : Nat) ∣ 1 := by
  intro h; have := Nat.le_of_dvd (by omega) h; omega

/-- ¬ 3 ∣ 2。 -/
theorem p9i_not3dvd2 : ¬ (3 : Nat) ∣ 2 := by
  intro h; obtain ⟨k, hk⟩ := h; omega

/-- ¬ 3 ∣ 5。 -/
theorem p9i_not3dvd5 : ¬ (3 : Nat) ∣ 5 := by
  intro h; obtain ⟨k, hk⟩ := h; omega

/-- ¬ 3 ∣ 7。 -/
theorem p9i_not3dvd7 : ¬ (3 : Nat) ∣ 7 := by
  intro h; obtain ⟨k, hk⟩ := h; omega

/-! ## P9I-1: 自然数の環像 ℚ への持ち上げと p 進付値の計算 -/

/-- **P9I-1a: rofNat と代表の橋** — 自然数 n の環像 `rofNat ratRing n`（1 の n 回和）は
    代表 n/1 のクラス `Quot.mk ratRel (intToPreRat n)` に一致する。n の帰納で、
    段は qAdd の Quot.lift 計算 + prAdd の交差積を `preRat_ext` + omega で照合。 -/
theorem p9i_rofNat_mk (n : Nat) :
    rofNat ratRing n = Quot.mk ratRel (intToPreRat ((n : Nat) : Int)) := by
  induction n with
  | zero =>
    show Quot.mk ratRel prZero = Quot.mk ratRel (intToPreRat (((0 : Nat)) : Int))
    apply congrArg (Quot.mk ratRel)
    apply preRat_ext
    · show (0 : Int) = (((0 : Nat)) : Int)
      omega
    · show (1 : Int) = 1
      rfl
  | succ n ih =>
    show ratRing.add (rofNat ratRing n) ratRing.one
      = Quot.mk ratRel (intToPreRat (((n + 1 : Nat)) : Int))
    rw [ih]
    show Quot.mk ratRel (prAdd (intToPreRat ((n : Nat) : Int)) prOne)
      = Quot.mk ratRel (intToPreRat (((n + 1 : Nat)) : Int))
    apply congrArg (Quot.mk ratRel)
    apply preRat_ext
    · show ((n : Nat) : Int) * 1 + 1 * 1 = (((n + 1 : Nat)) : Int)
      omega
    · show (1 : Int) * 1 = 1
      omega

/-- **P9I-1b: rofNat n ≠ 0（n ≥ 1）** — 橋 + `rzd_eq_zero_iff`（零 ⟺ 代表 num = 0）。 -/
theorem p9i_rofNat_ne (n : Nat) (hn : 1 ≤ n) : rofNat ratRing n ≠ ratRing.zero := by
  rw [p9i_rofNat_mk n]
  intro h
  have hz : ((n : Nat) : Int) = 0 :=
    (rzd_eq_zero_iff (intToPreRat ((n : Nat) : Int))).mp h
  omega

/-- **P9I-1c: v₃(rofNat n) = v₃(n)（n ≥ 1）** — 商付値 `egvValQ` を rofNat n に適用すると
    `pvqNatVal 3 n`（自然数 p 進付値）に一致する。橋 + `egvValQ_mk_ne`（非零類）+
    pvqVal の分子/分母展開（num = n・den = 1・v₃(1) = 0）。 -/
theorem p9i_val_rofNat (n : Nat) (hn : 1 ≤ n) :
    egvValQ 3 isPrime_three (rofNat ratRing n) = (pvqNatVal 3 n : Int) := by
  rw [p9i_rofNat_mk n]
  have hnum : (intToPreRat ((n : Nat) : Int)).num ≠ 0 := by
    show ((n : Nat) : Int) ≠ 0
    omega
  rw [egvValQ_mk_ne 3 isPrime_three (intToPreRat ((n : Nat) : Int)) hnum]
  show (pvqNatVal 3 (intToPreRat ((n : Nat) : Int)).num.natAbs : Int)
      - (pvqNatVal 3 (intToPreRat ((n : Nat) : Int)).den.natAbs : Int)
    = (pvqNatVal 3 n : Int)
  rw [show (intToPreRat ((n : Nat) : Int)).num.natAbs = n from Int.natAbs_natCast n,
    show (intToPreRat ((n : Nat) : Int)).den.natAbs = 1 from rfl,
    show pvqNatVal 3 1 = 0 from pvqNatVal_spec 3 (by omega) 0 1 p9i_not3dvd1 (by omega)]
  omega

/-! ## P9I-2: シフト像 p9eShifted の先頭係数と有界性 -/

/-- **P9I-2a: p9eShifted は 7 有界（deg 6）**。 -/
theorem p9eShifted_bnd : IsPolyBounded ratRing p9eShifted 7 :=
  fun j hj => p9eShifted_ge7 j hj

/-- **P9I-2b: p9eShifted は (6+1) 有界**（`pdv_mul_top_ne` の次数推論用の明示形）。 -/
theorem p9eShifted_bnd6 : IsPolyBounded ratRing p9eShifted (6 + 1) :=
  fun j hj => p9eShifted_ge7 j hj

/-- **P9I-2c: p9eShifted の先頭係数 = 1**（rofNat 1）。 -/
theorem p9eShifted_6 : p9eShifted 6 = ratRing.one := by
  show rofNat ratRing 1 = ratRing.one
  exact rofNat_one ratRing

/-- **P9I-2d: p9eShifted の先頭係数 ≠ 0**。 -/
theorem p9eShifted_lead : p9eShifted 6 ≠ ratRing.zero := by
  rw [p9eShifted_6]
  exact cbp_one_ne_zero

/-! ## P9I-3: シフトの有界性保存と次数保存 -/

/-- **P9I-3a: シフトの有界性保存** — f が B 有界なら p9eShift f M も B 有界（任意打切 M）。
    p9e_shift_coeff の各項 f_i·C(i,j)（j ≥ B）は i ≥ B（f_i = 0）か i < B ≤ j（C(i,j) = 0）で消える。 -/
theorem p9i_shift_bounded (f : PS ratRing) (B M : Nat)
    (hb : IsPolyBounded ratRing f B) :
    IsPolyBounded ratRing (p9eShift f M) B := by
  intro j hj
  rw [p9e_shift_coeff f M j]
  have hz : rsum ratRing (fun i => ratRing.mul (f i) (rofNat ratRing (chs i j))) M
      = rsum ratRing (fun _ => ratRing.zero) M :=
    rsum_congr ratRing M (fun i _ => by
      cases Nat.lt_or_ge i B with
      | inr hge =>
        rw [hb i hge]
        exact ratRing.zero_mul (rofNat ratRing (chs i j))
      | inl hlt =>
        rw [chs_gt i j (by omega)]
        exact ratRing.mul_zero (f i))
  rw [hz]
  exact rsum_const_zero ratRing M

/-- **P9I-3b: シフトの次数・先頭係数保存** — f が (nf+1) 有界なら、任意の打切 M ≥ nf+1 で
    p9eShift f M の nf 次係数は f_nf を保存し、(nf+1) 有界を保つ。三角性 C(i,nf)=0 (i<nf)、
    C(nf,nf)=1、f_i=0 (i>nf) を p9e_shift_coeff + rsum_single で閉じる。 -/
theorem p9i_shift_deg (f : PS ratRing) (nf M : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hM : nf + 1 ≤ M) :
    p9eShift f M nf = f nf ∧ IsPolyBounded ratRing (p9eShift f M) (nf + 1) := by
  refine ⟨?_, ?_⟩
  · rw [p9e_shift_coeff f M nf,
      rsum_single ratRing (fun i => ratRing.mul (f i) (rofNat ratRing (chs i nf))) nf M hM
        (fun q hq hqnf => by
          show ratRing.mul (f q) (rofNat ratRing (chs q nf)) = ratRing.zero
          cases Nat.lt_or_ge q nf with
          | inl hlt =>
            rw [chs_gt q nf hlt]
            exact ratRing.mul_zero (f q)
          | inr hge =>
            rw [hb q (by omega)]
            exact ratRing.zero_mul (rofNat ratRing (chs q nf)))]
    show ratRing.mul (f nf) (rofNat ratRing (chs nf nf)) = f nf
    rw [chs_self nf, rofNat_one ratRing, CRing.mul_one ratRing]
  · exact p9i_shift_bounded f (nf + 1) M hb

/-! ## P9I-4: Eisenstein 入力（ステップ4）と p9eShifted の既約性 -/

/-- **P9I-4（ステップ4 + 2）: シフト像 Φ_9(x+1) の既約性** — p = 3 の Eisenstein 判定を
    `eis_irreducible` へ投入して `pibIrreducible ratRing p9eShifted`。数値 v₃ は
    `pvqNatVal_spec` の具体代入（9=3²·1, 18=3²·2, 21=3·7, 15=3·5, 6=3·2, 定数 3=3·1, 先頭 1=3⁰）。 -/
theorem p9i_shifted_irreducible : pibIrreducible ratRing p9eShifted := by
  have hbnd : IsPolyBounded ratRing p9eShifted (6 + 1) := p9eShifted_bnd6
  have hlead : egvValQ 3 isPrime_three (p9eShifted 6) = 0 := by
    have hv : pvqNatVal 3 1 = 0 :=
      pvqNatVal_spec 3 (by omega) 0 1 p9i_not3dvd1 (by omega)
    show egvValQ 3 isPrime_three (rofNat ratRing 1) = 0
    rw [p9i_val_rofNat 1 (by omega)]
    omega
  have hln : p9eShifted 6 ≠ ratRing.zero := p9eShifted_lead
  have hconst : egvValQ 3 isPrime_three (p9eShifted 0) = 1 := by
    have hv : pvqNatVal 3 3 = 1 :=
      pvqNatVal_spec 3 (by omega) 1 1 p9i_not3dvd1 (by omega)
    show egvValQ 3 isPrime_three (rofNat ratRing 3) = 1
    rw [p9i_val_rofNat 3 (by omega)]
    omega
  have hc0 : p9eShifted 0 ≠ ratRing.zero := by
    show rofNat ratRing 3 ≠ ratRing.zero
    exact p9i_rofNat_ne 3 (by omega)
  have hmid : ∀ i, i < 6 → p9eShifted i ≠ ratRing.zero →
      1 ≤ egvValQ 3 isPrime_three (p9eShifted i) := by
    intro i hi _
    cases i with
    | zero =>
      have hv : pvqNatVal 3 3 = 1 :=
        pvqNatVal_spec 3 (by omega) 1 1 p9i_not3dvd1 (by omega)
      show 1 ≤ egvValQ 3 isPrime_three (rofNat ratRing 3)
      rw [p9i_val_rofNat 3 (by omega)]
      omega
    | succ i => cases i with
      | zero =>
        have hv : pvqNatVal 3 9 = 2 :=
          pvqNatVal_spec 3 (by omega) 2 1 p9i_not3dvd1 (by omega)
        show 1 ≤ egvValQ 3 isPrime_three (rofNat ratRing 9)
        rw [p9i_val_rofNat 9 (by omega)]
        omega
      | succ i => cases i with
        | zero =>
          have hv : pvqNatVal 3 18 = 2 :=
            pvqNatVal_spec 3 (by omega) 2 2 p9i_not3dvd2 (by omega)
          show 1 ≤ egvValQ 3 isPrime_three (rofNat ratRing 18)
          rw [p9i_val_rofNat 18 (by omega)]
          omega
        | succ i => cases i with
          | zero =>
            have hv : pvqNatVal 3 21 = 1 :=
              pvqNatVal_spec 3 (by omega) 1 7 p9i_not3dvd7 (by omega)
            show 1 ≤ egvValQ 3 isPrime_three (rofNat ratRing 21)
            rw [p9i_val_rofNat 21 (by omega)]
            omega
          | succ i => cases i with
            | zero =>
              have hv : pvqNatVal 3 15 = 1 :=
                pvqNatVal_spec 3 (by omega) 1 5 p9i_not3dvd5 (by omega)
              show 1 ≤ egvValQ 3 isPrime_three (rofNat ratRing 15)
              rw [p9i_val_rofNat 15 (by omega)]
              omega
            | succ i => cases i with
              | zero =>
                have hv : pvqNatVal 3 6 = 1 :=
                  pvqNatVal_spec 3 (by omega) 1 2 p9i_not3dvd2 (by omega)
                show 1 ≤ egvValQ 3 isPrime_three (rofNat ratRing 6)
                rw [p9i_val_rofNat 6 (by omega)]
                omega
              | succ i =>
                exact absurd hi (by omega)
  exact eis_irreducible p9eShifted 6 3 isPrime_three hbnd (by omega) hlead hln hmid hconst hc0

/-! ## P9I-5: シフト因数分解（ステップ5 の乗法性 + 打切安定 + 照合） -/

/-- **P9I-5: シフト因数分解** — Φ_9 = c·d（c, d 有界・打切点が 7 以上）ならば、
    シフト像 p9eShifted は (p9eShift c)·(p9eShift d) に一致する。評価準同型の乗法性
    `evalHom_mul`（打切 Bc+Bd+1）+ 打切安定 `evalHom_stable`（Φ_9 は 7 有界）+ 照合
    `p9e_shift_eq` で本物に閉じる（逆シフト・合成恒等式不要）。 -/
theorem p9i_shift_factor (c d : PS ratRing) (Bc Bd : Nat)
    (hc : IsPolyBounded ratRing c Bc) (hd : IsPolyBounded ratRing d Bd)
    (hB : 7 ≤ Bc + Bd + 1) (heq : cpdPhi9 = psMul ratRing c d) :
    p9eShifted = psMul ratRing (p9eShift c Bc) (p9eShift d Bd) := by
  have hmul := evalHom_mul (psConstHom ratRing) p9eXp1 c d Bc Bd hc hd
  have hstab := evalHom_stable (psConstHom ratRing) p9eXp1 cpdPhi9 7 cpdPhi9_bound
    (Bc + Bd + 1) hB
  funext j
  have e1 : p9eShifted j = p9eShift cpdPhi9 7 j := (p9e_shift_eq j).symm
  have e2 : p9eShift cpdPhi9 7 j = p9eShift cpdPhi9 (Bc + Bd + 1) j :=
    (congrFun hstab j).symm
  have e3 : p9eShift cpdPhi9 (Bc + Bd + 1) j
      = p9eShift (psMul ratRing c d) (Bc + Bd + 1) j := by rw [heq]
  have e4 : p9eShift (psMul ratRing c d) (Bc + Bd + 1) j
      = psMul ratRing (p9eShift c Bc) (p9eShift d Bd) j := congrFun hmul j
  rw [e1, e2, e3, e4]

/-! ## P9I-6: Φ_9 の既約性（本丸・ステップ5 輸送） -/

/-- **P9I-6（本丸）: Φ_9 = x⁶+x³+1 は多項式約元上で既約** — `pibIrreducible ratRing cpdPhi9`。
    任意の有界余因子約元 d（Φ_9 = c·d）に対し、シフト像へ移して
    p9eShifted = (p9eShift c)·(p9eShift d)（`p9i_shift_factor`）を得、p9eShifted の既約性
    （`p9i_shifted_irreducible`）で d の像を単元 or 同伴に分類。シフトは次数保存
    （`p9i_shift_deg`）なので、単元 ⟹ d 次数 0 ⟹ d 単元、同伴 ⟹ d 次数 6 ⟹ 余因子 c
    定数単元 ⟹ Φ_9 ∣ d（pdbAssoc）。逆シフト・合成恒等式は不要。 -/
theorem p9i_irreducible : pibIrreducible ratRing cpdPhi9 := by
  refine ⟨⟨6, by omega, cpdPhi9_bound, p9e_phi9_lead⟩, ?_⟩
  intro d hd_poly hdvd
  obtain ⟨Nd, hdN⟩ := hd_poly
  obtain ⟨c, hc_poly, heq⟩ := hdvd
  obtain ⟨Nc, hcN⟩ := hc_poly
  -- 打切点を 7 以上にするための有界性拡大
  have hcB : IsPolyBounded ratRing c (Nc + 7) := fun i hi => hcN i (by omega)
  have hdB : IsPolyBounded ratRing d (Nd + 7) := fun i hi => hdN i (by omega)
  -- シフト因数分解
  have hCD : p9eShifted
      = psMul ratRing (p9eShift c (Nc + 7)) (p9eShift d (Nd + 7)) :=
    p9i_shift_factor c d (Nc + 7) (Nd + 7) hcB hdB (by omega) heq
  have hCpoly : IsPoly ratRing (p9eShift c (Nc + 7)) :=
    ⟨Nc, p9i_shift_bounded c Nc (Nc + 7) hcN⟩
  have hDpoly : IsPoly ratRing (p9eShift d (Nd + 7)) :=
    ⟨Nd, p9i_shift_bounded d Nd (Nd + 7) hdN⟩
  have hdvdD : pdbDvd ratRing (p9eShift d (Nd + 7)) p9eShifted :=
    ⟨p9eShift c (Nc + 7), hCpoly, hCD⟩
  -- d の先頭次数を決定
  cases plo_lead_oracle_Q d Nd hdN with
  | inl hd0 =>
    -- d ≡ 0 ⟹ Φ_9 6 = (c·d) 6 = 0、先頭係数矛盾
    exfalso
    apply p9e_phi9_lead
    have hprod : psMul ratRing c d 6 = ratRing.zero := by
      show rsum ratRing (fun k => ratRing.mul (c k) (d (6 - k))) (6 + 1) = ratRing.zero
      have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (6 - k))) (6 + 1)
          = rsum ratRing (fun _ => ratRing.zero) (6 + 1) :=
        rsum_congr ratRing (6 + 1) (fun k _ => by
          rw [hd0 (6 - k)]
          exact ratRing.mul_zero (c k))
      rw [hz]
      exact rsum_const_zero ratRing (6 + 1)
    rw [congrFun heq 6]
    exact hprod
  | inr hdlead =>
    obtain ⟨nd, hdl, hdbnd⟩ := hdlead
    have hle : nd ≤ 6 :=
      pdb_dvd_deg_le pbzRatField hdbnd hdl cpdPhi9_bound p9e_phi9_lead
        ⟨c, ⟨Nc, hcN⟩, heq⟩
    have hndlt : nd + 1 ≤ Nd + 7 := by omega
    have hDdeg := p9i_shift_deg d nd (Nd + 7) hdbnd hndlt
    cases p9i_shifted_irreducible.2 (p9eShift d (Nd + 7)) hDpoly hdvdD with
    | inl hDunit =>
      -- 像が単元 ⟹ nd = 0 ⟹ d 単元
      obtain ⟨e, hene, hDe⟩ := hDunit
      have hnd0 : nd = 0 := by
        cases Nat.eq_zero_or_pos nd with
        | inl h0 => exact h0
        | inr hpos =>
          exfalso
          apply hdl
          rw [← hDdeg.1, hDe]
          show (if nd = 0 then e else ratRing.zero) = ratRing.zero
          exact if_neg (by omega)
      subst hnd0
      exact Or.inl (pdv_deg_zero_unit pbzRatField hdbnd hdl)
    | inr hDassoc =>
      -- 像が同伴 ⟹ nd = 6 ⟹ 余因子 c 定数単元 ⟹ pdbAssoc
      obtain ⟨E, hEpoly, hDeq⟩ := hDassoc.2
      obtain ⟨Ne, hEN⟩ := hEpoly
      have hnd6 : nd = 6 := by
        cases plo_lead_oracle_Q E Ne hEN with
        | inl hE0 =>
          -- E ≡ 0 ⟹ 像 ≡ 0 ⟹ 像 nd = 0、d nd ≠ 0 に矛盾
          exfalso
          apply hdl
          rw [← hDdeg.1, hDeq]
          show rsum ratRing (fun k => ratRing.mul (E k) (p9eShifted (nd - k))) (nd + 1)
            = ratRing.zero
          have hzz : rsum ratRing
              (fun k => ratRing.mul (E k) (p9eShifted (nd - k))) (nd + 1)
              = rsum ratRing (fun _ => ratRing.zero) (nd + 1) :=
            rsum_congr ratRing (nd + 1) (fun k _ => by
              rw [hE0 k]
              exact CRing.zero_mul ratRing (p9eShifted (nd - k)))
          rw [hzz]
          exact rsum_const_zero ratRing (nd + 1)
        | inr hElead =>
          obtain ⟨ne, hEl, hEbnd⟩ := hElead
          -- 像 = E·p9eShifted の頂点 (ne+6) が非零 ⟹ (nd+1) 有界より ne+6 ≤ nd ⟹ nd ≥ 6
          have htop : psMul ratRing E p9eShifted (ne + 6) ≠ ratRing.zero :=
            pdv_mul_top_ne pbzRatField hEbnd hEl p9eShifted_bnd6 p9eShifted_lead
          have hge : ne + 6 ≤ nd := by
            cases Nat.lt_or_ge (ne + 6) (nd + 1) with
            | inl h => omega
            | inr h =>
              exfalso
              apply htop
              have hval : psMul ratRing E p9eShifted (ne + 6)
                  = p9eShift d (Nd + 7) (ne + 6) := (congrFun hDeq (ne + 6)).symm
              rw [hval]
              exact hDdeg.2 (ne + 6) h
          omega
      subst hnd6
      -- 余因子 c の先頭次数 nc を決定 ⟹ nc = 0 ⟹ c 定数単元 ⟹ Φ_9 ∣ d
      cases plo_lead_oracle_Q c Nc hcN with
      | inl hc0 =>
        exfalso
        apply p9e_phi9_lead
        have hprod : psMul ratRing c d 6 = ratRing.zero := by
          show rsum ratRing (fun k => ratRing.mul (c k) (d (6 - k))) (6 + 1)
            = ratRing.zero
          have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (6 - k))) (6 + 1)
              = rsum ratRing (fun _ => ratRing.zero) (6 + 1) :=
            rsum_congr ratRing (6 + 1) (fun k _ => by
              rw [hc0 k]
              exact CRing.zero_mul ratRing (d (6 - k)))
          rw [hz]
          exact rsum_const_zero ratRing (6 + 1)
        rw [congrFun heq 6]
        exact hprod
      | inr hclead =>
        obtain ⟨nc, hcl, hcbnd⟩ := hclead
        have hnc0 : nc = 0 := by
          cases Nat.lt_or_ge (nc + 6) 7 with
          | inl hlt => omega
          | inr hge =>
            exfalso
            have htop2 : psMul ratRing c d (nc + 6) ≠ ratRing.zero :=
              pdv_mul_top_ne pbzRatField hcbnd hcl hdbnd hdl
            have hzero : psMul ratRing c d (nc + 6) = ratRing.zero :=
              (congrFun heq (nc + 6)).symm.trans (cpdPhi9_bound (nc + 6) hge)
            exact htop2 hzero
        subst hnc0
        obtain ⟨c0, hc0ne, hceq⟩ := pdv_deg_zero_unit pbzRatField hcbnd hcl
        refine Or.inr ⟨⟨c, ⟨Nc, hcN⟩, heq⟩, ?_⟩
        refine ⟨psC ratRing (pbzRatField.invf c0),
          ⟨1, fun i hi => if_neg (by omega)⟩, ?_⟩
        have hcancel : ratRing.mul (pbzRatField.invf c0) c0 = ratRing.one := by
          rw [ratRing.mul_comm]
          exact pbzRatField.mul_inv_cancel c0 hc0ne
        have hmm : psMul ratRing (psC ratRing (pbzRatField.invf c0)) c = psOne ratRing := by
          rw [hceq]
          show psMul ratRing (psC ratRing (pbzRatField.invf c0)) (psC ratRing c0)
            = psOne ratRing
          have h3 : psMul ratRing (psC ratRing (pbzRatField.invf c0)) (psC ratRing c0)
              = psC ratRing (ratRing.mul (pbzRatField.invf c0) c0) :=
            ((psConstHom ratRing).map_mul (pbzRatField.invf c0) c0).symm
          rw [h3, hcancel]
          rfl
        have chain : psMul ratRing (psC ratRing (pbzRatField.invf c0)) cpdPhi9 = d := by
          rw [heq]
          rw [show psMul ratRing (psC ratRing (pbzRatField.invf c0)) (psMul ratRing c d)
                = psMul ratRing (psMul ratRing (psC ratRing (pbzRatField.invf c0)) c) d
              from ((psRing ratRing).mul_assoc _ _ _).symm]
          rw [hmm]
          exact (psRing ratRing).one_mul d
        exact chain.symm

/-! ## P9I-7: ℚ(ζ_9) = ℚ[x]/(Φ_9) の体構成と拡大（仕上げ） -/

/-- **P9I-7a: ℚ(ζ_9) = ℚ[x]/(Φ_9)** — Φ_9 の既約性から全域 inv 付き実体 `IUTField`。
    円分塔 2 段目の体が本物に立つ（正直な限定: p=3・2 段目の体のみ）。 -/
def p9iPhi9Field : IUTField :=
  gefNFIUTField cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead (by omega) p9i_irreducible

/-- **P9I-7b: 体拡大 ℚ ↪ ℚ(ζ_9)** — 定数埋め込みによる次数 6 の体拡大
    `FieldExtension`（F7 `gefFieldExtension` の Φ_9 実例化）。 -/
def p9iExt9 : FieldExtension :=
  gefFieldExtension cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead (by omega) p9i_irreducible

end IUT
