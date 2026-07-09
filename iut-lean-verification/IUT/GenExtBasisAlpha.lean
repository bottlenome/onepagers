/-
  IUT/GenExtBasisAlpha.lean — Wave3/F9（A1 0.80→0.85 設計 §2 F9）:
  α = [x] の冪基底 {1, α, …, α^{n−1}}・拡大次数 [K:ℚ] = n = deg f・
  TowerLawBasis への接続

  ── 主要成果の分類: **[実／承認済み足場(c)]**（本物の先行建設。実 ℚ[x]/(f)
     の第二表示＝正規形担体 `GefNF`（F5）上で、生成元 α = [x] の冪
     {1, α, …, α^{n−1}} が **本物の ℚ-基底**（span＋一次独立）であり、
     拡大次数 = 基底要素数 = nf = deg f であることを core Lean のみで
     choice-free に完全証明する）。

  **complete_pct 影響**: A1（実 ℚ[x]/(f)・{1,α,…,α^{n−1}} 基底・次数論）への
  承認済み足場。前回 A1 監査（`audit/reaudit-A-genf-2026-07-09.md`）が 0.85 の
  残欠として名指しした (iii)「{1,α,…,α^{n−1}} 基底・次数 = [K:ℚ] 理論」を、
  一般既約 f・実 ℚ 上・NF 担体で本物に建てる（設計 `audit/A1-to-085-plan.md`
  §2/F9）。本層は次を本物に閉じる:
   * `gefAlpha_pow_eq_mon`: **α^i = 単項式 X^i**（i < nf・剰余簡約不要を
     `pfdRed_of_bounded` で確定・i 帰納）。
   * `gefPow_indep`: **一次独立** {1,α,…,α^{n−1}} の ℚ-線形結合 = 0 ⟹ 全係数 0
     （`pmbLinComb_zero_iff`＋α^i=X^i 経由の座標読み出し）。
   * `gefPow_spans`: **span** 任意の NF 担体元 = 冪の ℚ-線形結合（NF 担体は
     deg < nf なので座標そのもの・`pmbLinComb_coeff`）。
   * `gefPowBasis : TowerLawBasis ratIUTField (gefNFModule …)`: 監査文言どおりの
     主語 {1, α, …, α^{n−1}}（TowerLawBasis の全フィールドを充填）。
   * `gef_degree_eq`: **[K:ℚ] = nf = deg f**（`towerLawDegree` の定義展開）。
  complete_pct は本ファイル単体では未前進（A1 は基底・次数・全域 inv 揃った
  後の独立再監査で確定）。complete_pct 未設定。

  本物性: α = [x] は `pfdRed f nf 1 X`（X = X^1）で NF 化した本物の生成元。
  α^i = X^i は剰余簡約関数 `pfdRed`（F3・`field_division_exists` の witness を
  関数化したもの）と単項式の積公式（`psMul_single_coeff268`）で本物に閉じる。
  ℚ-加群構造 `gefNFModule` の smul c x = psC c · x は定数倍（`psConstHom` 環
  準同型）であり模型・代理でない。一次独立・span は F8 相当の座標読み出し
  `pmbLinComb_coeff`/零判定 `pmbLinComb_zero_iff` を NF 担体へ特殊化して閉じる
  （仮定・sorry での誤魔化しなし）。

  正直な限定:
   - 対象体は実 ℚ（ratRing）に固定。基礎体は ℚ 固定（塔の反復は後段）。
   - **F6（`GenExtFieldInv`・全域 inv 付き `gefNFIUTField`）が未 compile** の
     ため、設計 §2 F9 末尾の `gefFieldExtension`（ℚ↪gefNFIUTField）・
     `gefBasisLK`（TowerData の basisLK スロット・A3 塔用）は本ファイルでは
     **保留**（IUTField インスタンスを要するため）。基底・次数（(B) の核）は
     `gefNFRing` の CRing レベル（＝ ℚ-加群 `gefNFModule`）で本物に閉じており、
     TowerLaw 塔への流し込み（basisLK）は F6 完成後に親が接続する。
   - `towerLawDegree` は基底 witness 依存（M281F の honest 仮説 1 と同精神・
     次元 well-defined 性は未証明）。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.GenExtFieldNF
import IUT.PolyMonomialBasis
import IUT.TowerLaw

namespace IUT

/-! ## F9-0: 環非依存の補助（単項式の積・定数倍係数・係数拡張・再構成） -/

/-- 単項式の積（一点集中 Cauchy 和・`psMul_single_coeff268` から）:
    (a·X^p)·(b·X^q) の j 次係数 = (ab·X^{p+q}) の j 次係数。 -/
theorem gefSMS (a b : QRat) (p q j : Nat) :
    psMul ratRing (psSingle ratRing a p) (psSingle ratRing b q) j
      = psSingle ratRing (ratRing.mul a b) (p + q) j := by
  rw [psMul_single_coeff268 ratRing a p (psSingle ratRing b q) j]
  cases Nat.decEq j (p + q) with
  | isTrue hj =>
    rw [if_pos (show p ≤ j by omega),
      show psSingle ratRing b q (j - p) = b from if_pos (by omega),
      show psSingle ratRing (ratRing.mul a b) (p + q) j = ratRing.mul a b from if_pos hj]
  | isFalse hj =>
    rw [show psSingle ratRing (ratRing.mul a b) (p + q) j = ratRing.zero from if_neg hj]
    cases Nat.lt_or_ge j p with
    | inl hlt => rw [if_neg (show ¬ p ≤ j by omega)]
    | inr hge =>
      rw [if_pos hge,
        show psSingle ratRing b q (j - p) = ratRing.zero from if_neg (by omega),
        CRing.mul_zero ratRing a]

/-- 定数倍の係数: (psC c · g)_j = c · g_j（psC = psSingle _ 0・k = 0 で 0 ≤ j）。 -/
theorem gefSmulCoeff (c : QRat) (g : PS ratRing) (j : Nat) :
    psMul ratRing (psC ratRing c) g j = ratRing.mul c (g j) := by
  have h := psMul_single_coeff268 ratRing c 0 g j
  rw [if_pos (Nat.zero_le j)] at h
  exact h

/-- 係数列 `Fin n → QRat` を `Nat → QRat` へ拡張（範囲外は 0）。一次独立で使用。 -/
def gefExtCoef (n : Nat) (c : Fin n → QRat) : Nat → QRat :=
  fun k => if hk : k < n then c ⟨k, hk⟩ else ratRing.zero

/-- 拡張係数の範囲内一致 gefExtCoef n c i.val = c i。 -/
theorem gefExtCoef_val (n : Nat) (c : Fin n → QRat) (i : Fin n) :
    gefExtCoef n c i.val = c i := by
  show (if hk : i.val < n then c ⟨i.val, hk⟩ else ratRing.zero) = c i
  rw [dif_pos i.isLt]

/-- 有界多項式は自身の係数の単項式線形結合に等しい（span の核）。 -/
theorem gefBoundedRecon (v : PS ratRing) (n : Nat) (hv : IsPolyBounded ratRing v n) :
    v = pmbLinComb ratRing v n := by
  funext j
  cases Nat.lt_or_ge j n with
  | inl hlt => exact (pmbLinComb_coeff ratRing v n j hlt).symm
  | inr hge =>
    rw [pmbLinComb_bound ratRing v n j hge]
    exact hv j hge

/-! ## F9-1: NF 担体の ℚ-加群構造（smul = psC 定数倍） -/

/-- **F9-1: NF 担体の ℚ-加群** — `GefNF f nf` を ℚ-ベクトル空間として見る。
    加法・零・反元は `gefNFRing`（F5）のアーベル群、**スカラー倍は定数倍**
    smul c x = psC c · x（`psConstHom` 環準同型・簡約不要で nf 有界保存）。 -/
def gefNFModule (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) : TowerLawModule ratIUTField where
  carrier := GefNF f nf
  add := (gefNFRing f nf hb hl hn).add
  zero := (gefNFRing f nf hb hl hn).zero
  neg := (gefNFRing f nf hb hl hn).neg
  smul := fun c x => ⟨psMul ratRing (psC ratRing c) x.val, fun j hj => by
    show psMul ratRing (psC ratRing c) x.val j = ratRing.zero
    rw [gefSmulCoeff c x.val j, x.property j hj]
    exact CRing.mul_zero ratRing c⟩
  add_assoc := (gefNFRing f nf hb hl hn).add_assoc
  zero_add := (gefNFRing f nf hb hl hn).zero_add
  neg_add := (gefNFRing f nf hb hl hn).neg_add
  add_comm := (gefNFRing f nf hb hl hn).add_comm
  smul_add := fun a x y =>
    Subtype.ext ((psRing ratRing).left_distrib (psC ratRing a) x.val y.val)
  add_smul := fun a b x => by
    apply Subtype.ext
    show psMul ratRing (psC ratRing (ratRing.add a b)) x.val
      = psAdd ratRing (psMul ratRing (psC ratRing a) x.val)
          (psMul ratRing (psC ratRing b) x.val)
    rw [show psC ratRing (ratRing.add a b)
          = psAdd ratRing (psC ratRing a) (psC ratRing b)
        from (psConstHom ratRing).map_add a b]
    exact CRing.right_distrib (psRing ratRing) (psC ratRing a) (psC ratRing b) x.val
  mul_smul := fun a b x => by
    apply Subtype.ext
    show psMul ratRing (psC ratRing (ratRing.mul a b)) x.val
      = psMul ratRing (psC ratRing a) (psMul ratRing (psC ratRing b) x.val)
    rw [show psC ratRing (ratRing.mul a b)
          = psMul ratRing (psC ratRing a) (psC ratRing b)
        from (psConstHom ratRing).map_mul a b]
    exact (psRing ratRing).mul_assoc (psC ratRing a) (psC ratRing b) x.val
  one_smul := fun x => by
    apply Subtype.ext
    show psMul ratRing (psC ratRing ratRing.one) x.val = x.val
    exact (psRing ratRing).one_mul x.val
  zero_smul := fun x => by
    apply Subtype.ext
    show psMul ratRing (psC ratRing ratRing.zero) x.val = psZero ratRing
    have hz : psC ratRing ratRing.zero = psZero ratRing := by
      funext n
      cases n with
      | zero => rfl
      | succ k => rfl
    rw [hz]
    exact CRing.zero_mul (psRing ratRing) x.val

/-! ## F9-2: 生成元 α = [x]・単項式・冪 -/

/-- **F9-2a: 生成元 α = [x]** — 変数 X = X^1 を NF 化（剰余簡約）した担体元。 -/
def gefAlpha (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) : GefNF f nf :=
  ⟨pfdRed f nf 1 (psSingle ratRing ratRing.one 1),
   pfdRed_bound f nf hb hl 1 (psSingle ratRing ratRing.one 1)
     (fun j hj => by
       show psSingle ratRing ratRing.one 1 j = ratRing.zero
       exact if_neg (by omega))⟩

/-- **F9-2b: 単項式担体元 X^i**（i < nf・簡約不要）。 -/
def gefNFMon (f : PS ratRing) (nf : Nat) (i : Nat) (hi : i < nf) : GefNF f nf :=
  ⟨psSingle ratRing ratRing.one i,
   fun j hj => by
     show psSingle ratRing ratRing.one i j = ratRing.zero
     exact if_neg (by omega)⟩

/-- **F9-2c: 担体元の冪** x^0 = 1、x^{k+1} = (x^k)·x（`gefNFRing` の乗法）。 -/
def gefNFPow (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (x : GefNF f nf) : Nat → GefNF f nf
  | 0 => (gefNFRing f nf hb hl hn).one
  | k + 1 => (gefNFRing f nf hb hl hn).mul (gefNFPow f nf hb hl hn x k) x

/-! ## F9-3: α^i = X^i（本設計の核・i 帰納） -/

/-- **F9-3a: α^i の係数 = 単項式 X^i の係数**（i < nf）。i 帰納:
    i = 0 は 1 = X^0、i+1 では α = X（nf ≥ 2 で簡約不要）・単項式の積
    X^i·X = X^{i+1}・i+1 < nf で簡約不要（`pfdRed_of_bounded`）。 -/
theorem gefAlphaPowVal (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) :
    ∀ i, i < nf →
      (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i).val
        = psSingle ratRing ratRing.one i := by
  intro i
  induction i with
  | zero =>
    intro _
    funext j
    show psOne ratRing j = psSingle ratRing ratRing.one 0 j
    rfl
  | succ k ih =>
    intro hk
    have hk' : k < nf := by omega
    have hnf2 : 2 ≤ nf := by omega
    have hXnf : IsPolyBounded ratRing (psSingle ratRing ratRing.one 1) nf := by
      intro j hj
      show psSingle ratRing ratRing.one 1 j = ratRing.zero
      exact if_neg (by omega)
    have hAlphaX : (gefAlpha f nf hb hl hn).val = psSingle ratRing ratRing.one 1 := by
      funext j
      show pfdRed f nf 1 (psSingle ratRing ratRing.one 1) j
        = psSingle ratRing ratRing.one 1 j
      exact pfdRed_of_bounded f nf hb hl 1 (psSingle ratRing ratRing.one 1) hXnf j
    have hProd : psMul ratRing (psSingle ratRing ratRing.one k)
          (psSingle ratRing ratRing.one 1)
        = psSingle ratRing ratRing.one (k + 1) := by
      funext j
      rw [gefSMS ratRing.one ratRing.one k 1 j, ratRing.one_mul ratRing.one]
    show pfdRed f nf nf
        (psMul ratRing (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) k).val
          (gefAlpha f nf hb hl hn).val)
      = psSingle ratRing ratRing.one (k + 1)
    rw [ih hk', hAlphaX, hProd]
    funext j
    exact pfdRed_of_bounded f nf hb hl nf (psSingle ratRing ratRing.one (k + 1))
      (fun j2 hj2 => by
        show psSingle ratRing ratRing.one (k + 1) j2 = ratRing.zero
        exact if_neg (by omega)) j

/-- **F9-3b: α^i = X^i**（担体元レベル・監査文言の主語同定）。 -/
theorem gefAlpha_pow_eq_mon (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (i : Nat) (hi : i < nf) :
    gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i = gefNFMon f nf i hi :=
  Subtype.ext (gefAlphaPowVal f nf hb hl hn i hi)

/-! ## F9-4: smul(α^m) の係数と有限和の係数（座標読み出しへの橋） -/

/-- **F9-4a: c·α^m の係数 = psSingle c m**（α^m = X^m・定数倍）。 -/
theorem gefSmulMonVal (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (c : QRat) (m : Nat) (hm : m < nf) :
    ((gefNFModule f nf hb hl hn).smul c
        (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) m)).val
      = psSingle ratRing c m := by
  show psMul ratRing (psC ratRing c)
      (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) m).val
    = psSingle ratRing c m
  rw [gefAlphaPowVal f nf hb hl hn m hm]
  funext j
  rw [show psC ratRing c = psSingle ratRing c 0 from rfl,
    gefSMS c ratRing.one 0 m j, ratRing.mul_comm c ratRing.one,
    ratRing.one_mul c, Nat.zero_add]

/-- **F9-4b: 冪基底の有限和の係数 = 単項式線形結合**（n ≤ nf・n 帰納）。
    towerLawSum の各段（smul c α^i）の係数が psSingle c i に一致し、
    和の係数列が `pmbLinComb`（F8 の座標読み出し・零判定の主語）に落ちる。 -/
theorem gefSumVal (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (coef : Nat → QRat) :
    ∀ n, n ≤ nf →
      (towerLawSum (gefNFModule f nf hb hl hn) n
        (fun i : Fin n =>
          (gefNFModule f nf hb hl hn).smul (coef i.val)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))).val
        = pmbLinComb ratRing coef n := by
  intro n
  induction n with
  | zero =>
    intro _
    rfl
  | succ m ih =>
    intro hm
    have hmnf : m ≤ nf := by omega
    have hmlt : m < nf := by omega
    show psAdd ratRing
        (towerLawSum (gefNFModule f nf hb hl hn) m
          (fun i : Fin m =>
            (gefNFModule f nf hb hl hn).smul (coef i.val)
              (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))).val
        ((gefNFModule f nf hb hl hn).smul (coef m)
          (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) m)).val
      = psAdd ratRing (pmbLinComb ratRing coef m) (psSingle ratRing (coef m) m)
    rw [ih hmnf, gefSmulMonVal f nf hb hl hn (coef m) m hmlt]

/-! ## F9-5: 冪基底の span・一次独立 -/

/-- **F9-5a: span** — 任意の NF 担体元は冪 {1,α,…,α^{n−1}} の ℚ-線形結合。
    座標は担体元の係数そのもの（NF 担体は deg < nf）。 -/
theorem gefPow_spans (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (v : GefNF f nf) :
    v = towerLawSum (gefNFModule f nf hb hl hn) nf
      (fun i : Fin nf =>
        (gefNFModule f nf hb hl hn).smul (v.val i.val)
          (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val)) := by
  apply Subtype.ext
  exact (gefBoundedRecon v.val nf v.property).trans
    (gefSumVal f nf hb hl hn (fun k => v.val k) nf (Nat.le_refl nf)).symm

/-- **F9-5b: 一次独立** — 冪 {1,α,…,α^{n−1}} の ℚ-線形結合 = 0 ⟹ 全係数 0。
    α^i = X^i（`gefAlpha_pow_eq_mon`）で単項式線形結合に落とし、
    `pmbLinComb_zero_iff`（F8 の一次独立の核）で全係数消滅を得る。 -/
theorem gefPow_indep (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (c : Fin nf → QRat)
    (h : towerLawSum (gefNFModule f nf hb hl hn) nf
        (fun i : Fin nf =>
          (gefNFModule f nf hb hl hn).smul (c i)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))
        = (gefNFModule f nf hb hl hn).zero) :
    ∀ i, c i = ratRing.zero := by
  intro i
  have hcong : (fun i : Fin nf =>
        (gefNFModule f nf hb hl hn).smul (c i)
          (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))
      = (fun i : Fin nf =>
        (gefNFModule f nf hb hl hn).smul (gefExtCoef nf c i.val)
          (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val)) := by
    funext j
    rw [gefExtCoef_val nf c j]
  rw [hcong] at h
  have hval : (towerLawSum (gefNFModule f nf hb hl hn) nf
      (fun i : Fin nf =>
        (gefNFModule f nf hb hl hn).smul (gefExtCoef nf c i.val)
          (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))).val
      = psZero ratRing :=
    congrArg (fun z : GefNF f nf => z.val) h
  rw [gefSumVal f nf hb hl hn (gefExtCoef nf c) nf (Nat.le_refl nf)] at hval
  have hz := (pmbLinComb_zero_iff ratRing (gefExtCoef nf c) nf).mp hval i.val i.isLt
  rw [← gefExtCoef_val nf c i]
  exact hz

/-! ## F9-6: 冪基底と拡大次数 [K:ℚ] = n = deg f -/

/-- **F9-6a: 冪基底** {1, α, …, α^{n−1}} — 監査文言どおりの主語で
    `TowerLawBasis ratIUTField (gefNFModule …)` の全フィールドを充填。
    dim = nf、vec = α の冪、repr = 担体元の係数（NF 設計の配当・リフト不要）。 -/
def gefPowBasis (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) : TowerLawBasis ratIUTField (gefNFModule f nf hb hl hn) where
  dim := nf
  vec := fun i => gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val
  repr := fun x i => x.val i.val
  spans := gefPow_spans f nf hb hl hn
  indep := gefPow_indep f nf hb hl hn

/-- **F9-6b: 拡大次数 [K:ℚ] = nf = deg f**（基底要素数の定義展開）。 -/
theorem gef_degree_eq (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) :
    towerLawDegree (gefPowBasis f nf hb hl hn) = nf := rfl

/-
  F9-7（保留・F6 待ち）: `gefFieldExtension`（ℚ↪gefNFIUTField・incl = psC 定数
  埋め込み）と `gefBasisLK`（TowerData の basisLK スロット・A3 円分塔用）は
  `gefNFIUTField : IUTField`（F6 = `GenExtFieldInv`）を要するため本ファイルでは
  未実装。F6 完成後に親が本ファイルの `gefPowBasis`/`gefAlpha_pow_eq_mon` を
  移送して接続する（設計 `audit/A1-to-085-plan.md` §2/F9 末尾）。基底・次数
  （A1→0.85 の (B) の核）は上記で本物に閉じている。
-/

end IUT
