/-
  IUT/Phi9Shift.lean — Φ_9 のシフト像（Eisenstein 判定 E4′ の前半）:
  A3 円分塔 ℚ ⊂ ℚ(ζ_9) の法多項式 Φ_9 = x⁶+x³+1 に対し、シフト演算子
  f ↦ f(x+1) を評価準同型 `evalSum` で本物に構成し、Pascal 行係数
  ((x+1)^k の j 次係数 = C(k,j)) と Φ_9 のシフト像
  Φ_9(x+1) = x⁶+6x⁵+15x⁴+21x³+18x²+9x+3 の明示係数照合までを閉じる。

  ── 分類 **[実／本物建設(b)]**（本物の先行建設。実 ℚ[X] = `PS ratRing`
  上のシフト同型・Pascal 係数・シフト像の全係数一致。骨格・模型・代理なし。
  sorry 皆無・新規 Classical.choice 皆無。禁止タクティク不使用）。

  **complete_pct 影響**: A3（Φ_9 Eisenstein → ℚ(ζ_9)）への**承認済み足場(c)**。
  シフト同型 p9eShift・Pascal 行係数 p9e_pow_coeff・シフト像照合 p9e_shift_eq・
  先頭係数 p9e_phi9_lead を本物で供給する。既約性本体（Φ_9 の既約性）は
  Eisenstein 判定器 E3 の完成後に E4′ 後半（ステップ 4・5）で接続する。
  本ファイル単体では complete_pct は動かさない（未設定・0 前進）。

  内容（設計 audit/A3-cyclotomic-tower-detail-2026-07-09.md §1.2 E4′ ステップ
  1・2・3・6前半）:
   * `p9eXp1`            — x+1（`psAdd (psSingle 1 1) (psC 1)`）。
   * `p9eShift f N`      — f(x+1) の N 打切り（`evalSum (psConstHom) p9eXp1 f N`）。
   * `p9e_mul_xp1_{zero,succ}` — ·(x+1) の係数 Pascal 段（P·(x+1))_{n+1}=P_n+P_{n+1}。
   * **`p9e_pow_coeff`** — **Pascal 行**: ((x+1)^k)_j = C(k,j) = rofNat(chs k j)。
   * `p9e_pow0_coeff … p9e_pow6_coeff` — k=0..6 の 7 本の Pascal 行小補題。
   * `p9eShifted`        — 係数 (3,9,18,21,15,6,1) の明示多項式。
   * **`p9e_shift_eq`**  — **シフト像照合**: ∀ j, p9eShift Φ_9 7 j = p9eShifted j。
   * `p9e_phi9_lead`     — 先頭係数 Φ_9(6) = 1 ≠ 0。
   * `p9e_pow_{bounded,lead}` — (x+1)^i は (i+1)有界・先頭係数 1。
   * `p9e_shift_coeff`  — シフト像の一般係数公式 (p9eShift f M)_j = Σ f_i·C(i,j)。
   * **`p9e_shift_lead`** — **シフトの次数保存**: N 次係数保存 + (N+1)有界
     （E4′ ステップ5 の E3非依存な前提部品・既約性輸送本体は E3 待ちで保留）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   - **本物**: p9eShift は実 evalSum によるシフト、Pascal 係数と Φ_9 の
     シフト像は実 ℚ[X] の全係数一致で完全証明（模型・代理なし）。
   - **含めない（E3 待ちで保留）**: E4′ ステップ 4（数値 v₃ 検証: v₃(3)=1,
     v₃(9)=2,… の Eisenstein 入力）とステップ 5（既約性輸送
     pibIrreducible Φ_9）は Eisenstein 判定器 E3 に依存するため本ファイルでは
     **保留**する。既約性本体はここに存在しない（骨格で埋めない）。
   - complete_pct は E3 完成 → E4′ 後半接続 → 円分塔の体化が揃った段で動かす。

  全て選択公理不使用（新規 Classical.choice なし・propext/Quot.sound のみ）。
-/
import IUT.CyclotomicPolyData
import IUT.EvaluationHom
import IUT.Fermat
import IUT.PolyFieldDivision
import IUT.CubicPolyQ

namespace IUT

/-! ## P9-1: シフト演算子 x+1 と f ↦ f(x+1)（設計 E4′ ステップ 1） -/

/-- **P9-1a: x+1** — 単項式 X（`psSingle 1 1`）と定数 1（`psC 1`）の和。
    シフト f(x) ↦ f(x+1) の評価点。 -/
def p9eXp1 : PS ratRing :=
  psAdd ratRing (psSingle ratRing ratRing.one 1) (psC ratRing ratRing.one)

/-- **P9-1b: シフト f ↦ f(x+1)（N 打切り）** — 評価準同型 `evalSum` を
    E := `psRing ratRing`・α := x+1 で使う（新規演算子ゼロ）。乗法性・加法性は
    `evalHom_mul`/`evalHom_add` がそのまま供給する。 -/
def p9eShift (f : PS ratRing) (N : Nat) : PS ratRing :=
  evalSum (psConstHom ratRing) p9eXp1 f N

/-! ## P9-2: ·(x+1) の係数 Pascal 段（設計 E4′ ステップ 2 の核） -/

/-- **P9-2a: (P·(x+1))_0 = P_0** — 可換化 + 右分配で
    P·(x+1) = (x+1)·P = X·P + 1·P、0 次では X·P が消え 1·P が残る。 -/
theorem p9e_mul_xp1_zero (P : PS ratRing) :
    psMul ratRing P p9eXp1 0 = P 0 := by
  have h1 : psMul ratRing P p9eXp1 0 = psMul ratRing p9eXp1 P 0 :=
    congrFun ((psRing ratRing).mul_comm P p9eXp1) 0
  have h2 : psMul ratRing p9eXp1 P 0
      = ratRing.add (psMul ratRing (psSingle ratRing ratRing.one 1) P 0)
          (psMul ratRing (psC ratRing ratRing.one) P 0) :=
    congrFun (CRing.right_distrib (psRing ratRing)
      (psSingle ratRing ratRing.one 1) (psC ratRing ratRing.one) P) 0
  rw [h1, h2, psMul_single_coeff268 ratRing ratRing.one 1 P 0,
    if_neg (show ¬ (1 ≤ 0) by omega),
    psC_mul_coeff ratRing ratRing.one P 0, ratRing.one_mul, ratRing.zero_add]

/-- **P9-2b: (P·(x+1))_{n+1} = P_n + P_{n+1}** — Pascal 段。X·P が P_n を、
    1·P が P_{n+1} を供給する（`psMul_single_coeff268` と `psC_mul_coeff`）。 -/
theorem p9e_mul_xp1_succ (P : PS ratRing) (n : Nat) :
    psMul ratRing P p9eXp1 (n + 1) = ratRing.add (P n) (P (n + 1)) := by
  have h1 : psMul ratRing P p9eXp1 (n + 1) = psMul ratRing p9eXp1 P (n + 1) :=
    congrFun ((psRing ratRing).mul_comm P p9eXp1) (n + 1)
  have h2 : psMul ratRing p9eXp1 P (n + 1)
      = ratRing.add (psMul ratRing (psSingle ratRing ratRing.one 1) P (n + 1))
          (psMul ratRing (psC ratRing ratRing.one) P (n + 1)) :=
    congrFun (CRing.right_distrib (psRing ratRing)
      (psSingle ratRing ratRing.one 1) (psC ratRing ratRing.one) P) (n + 1)
  rw [h1, h2, psMul_single_coeff268 ratRing ratRing.one 1 P (n + 1),
    if_pos (show 1 ≤ n + 1 by omega), show n + 1 - 1 = n from by omega,
    psC_mul_coeff ratRing ratRing.one P (n + 1), ratRing.one_mul, ratRing.one_mul]

/-! ## P9-3: Pascal 行 ((x+1)^k)_j = C(k,j)（設計 E4′ ステップ 2） -/

/-- **P9-3 (本丸・Pascal 行): ((x+1)^k)_j = C(k,j)** — 冪級数環での (x+1)^k の
    j 次係数は二項係数 chs k j の環像（`rofNat`）に一致する。k についての帰納：
    段は ·(x+1) の Pascal 段（P9-2b）+ chs の Pascal 漸化式 + `rofNat_add`。 -/
theorem p9e_pow_coeff : ∀ (k j : Nat),
    rpow (psRing ratRing) p9eXp1 k j = rofNat ratRing (chs k j) := by
  intro k
  induction k with
  | zero =>
    intro j
    cases j with
    | zero => exact (rofNat_one ratRing).symm
    | succ n => rfl
  | succ k ih =>
    intro j
    show psMul ratRing (rpow (psRing ratRing) p9eXp1 k) p9eXp1 j
      = rofNat ratRing (chs (k + 1) j)
    cases j with
    | zero =>
      rw [p9e_mul_xp1_zero, ih 0, chs_zero k, chs_zero (k + 1)]
    | succ n =>
      rw [p9e_mul_xp1_succ, ih n, ih (n + 1),
        show chs (k + 1) (n + 1) = chs k n + chs k (n + 1) from rfl, rofNat_add]

/-- **P9-3a..g: k = 0..6 の Pascal 行小補題**（設計 E4′ ステップ 2 の 7 本）。
    ((x+1)^k)_j = C(k,j)。数値行は k を代入して chs で確定
    (k=6 なら 1,6,15,20,15,6,1 等)。 -/
theorem p9e_pow0_coeff (j : Nat) :
    rpow (psRing ratRing) p9eXp1 0 j = rofNat ratRing (chs 0 j) := p9e_pow_coeff 0 j
theorem p9e_pow1_coeff (j : Nat) :
    rpow (psRing ratRing) p9eXp1 1 j = rofNat ratRing (chs 1 j) := p9e_pow_coeff 1 j
theorem p9e_pow2_coeff (j : Nat) :
    rpow (psRing ratRing) p9eXp1 2 j = rofNat ratRing (chs 2 j) := p9e_pow_coeff 2 j
theorem p9e_pow3_coeff (j : Nat) :
    rpow (psRing ratRing) p9eXp1 3 j = rofNat ratRing (chs 3 j) := p9e_pow_coeff 3 j
theorem p9e_pow4_coeff (j : Nat) :
    rpow (psRing ratRing) p9eXp1 4 j = rofNat ratRing (chs 4 j) := p9e_pow_coeff 4 j
theorem p9e_pow5_coeff (j : Nat) :
    rpow (psRing ratRing) p9eXp1 5 j = rofNat ratRing (chs 5 j) := p9e_pow_coeff 5 j
theorem p9e_pow6_coeff (j : Nat) :
    rpow (psRing ratRing) p9eXp1 6 j = rofNat ratRing (chs 6 j) := p9e_pow_coeff 6 j

/-- **P9-3h: (x+1)^i は (i+1) 有界**（deg = i）— j ≥ i+1 では i < j より
    C(i,j) = 0（`chs_gt`）。設計 E4′ ステップ5 の三角性の入力。 -/
theorem p9e_pow_bounded (i : Nat) :
    IsPolyBounded ratRing (rpow (psRing ratRing) p9eXp1 i) (i + 1) := by
  intro j hj
  rw [p9e_pow_coeff i j, chs_gt i j (by omega)]
  rfl

/-- **P9-3i: (x+1)^i の先頭係数 = 1** — C(i,i) = 1（`chs_self`）。
    設計 E4′ ステップ5 の次数保存の入力。 -/
theorem p9e_pow_lead (i : Nat) :
    rpow (psRing ratRing) p9eXp1 i i = ratRing.one := by
  rw [p9e_pow_coeff i i, chs_self i]
  exact rofNat_one ratRing

/-! ## P9-4: Φ_9 の各係数値 -/

/-- Φ_9(0) = 1（定数項）。 -/
theorem p9e_phi9_0 : cpdPhi9 0 = ratRing.one := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 0)
      (psSingle ratRing ratRing.one 3 0)) (psC ratRing ratRing.one 0) = ratRing.one
  rw [show psSingle ratRing ratRing.one 6 0 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 3 0 = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one 0 = ratRing.one from if_pos rfl,
    ratRing.zero_add, ratRing.zero_add]

/-- Φ_9(1) = 0。 -/
theorem p9e_phi9_1 : cpdPhi9 1 = ratRing.zero := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 1)
      (psSingle ratRing ratRing.one 3 1)) (psC ratRing ratRing.one 1) = ratRing.zero
  rw [show psSingle ratRing ratRing.one 6 1 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 3 1 = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one 1 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add, ratRing.zero_add]

/-- Φ_9(2) = 0。 -/
theorem p9e_phi9_2 : cpdPhi9 2 = ratRing.zero := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 2)
      (psSingle ratRing ratRing.one 3 2)) (psC ratRing ratRing.one 2) = ratRing.zero
  rw [show psSingle ratRing ratRing.one 6 2 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 3 2 = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one 2 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add, ratRing.zero_add]

/-- Φ_9(3) = 1。 -/
theorem p9e_phi9_3 : cpdPhi9 3 = ratRing.one := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 3)
      (psSingle ratRing ratRing.one 3 3)) (psC ratRing ratRing.one 3) = ratRing.one
  rw [show psSingle ratRing ratRing.one 6 3 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 3 3 = ratRing.one from if_pos rfl,
    show psC ratRing ratRing.one 3 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add, CRing.add_zero ratRing]

/-- Φ_9(4) = 0。 -/
theorem p9e_phi9_4 : cpdPhi9 4 = ratRing.zero := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 4)
      (psSingle ratRing ratRing.one 3 4)) (psC ratRing ratRing.one 4) = ratRing.zero
  rw [show psSingle ratRing ratRing.one 6 4 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 3 4 = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one 4 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add, ratRing.zero_add]

/-- Φ_9(5) = 0。 -/
theorem p9e_phi9_5 : cpdPhi9 5 = ratRing.zero := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 5)
      (psSingle ratRing ratRing.one 3 5)) (psC ratRing ratRing.one 5) = ratRing.zero
  rw [show psSingle ratRing ratRing.one 6 5 = ratRing.zero from if_neg (by omega),
    show psSingle ratRing ratRing.one 3 5 = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one 5 = ratRing.zero from if_neg (by omega),
    ratRing.zero_add, ratRing.zero_add]

/-- **Φ_9(6) = 1**（先頭係数）。 -/
theorem p9e_phi9_6 : cpdPhi9 6 = ratRing.one := by
  show ratRing.add (ratRing.add (psSingle ratRing ratRing.one 6 6)
      (psSingle ratRing ratRing.one 3 6)) (psC ratRing ratRing.one 6) = ratRing.one
  rw [show psSingle ratRing ratRing.one 6 6 = ratRing.one from if_pos rfl,
    show psSingle ratRing ratRing.one 3 6 = ratRing.zero from if_neg (by omega),
    show psC ratRing ratRing.one 6 = ratRing.zero from if_neg (by omega),
    CRing.add_zero ratRing, CRing.add_zero ratRing]

/-! ## P9-5: シフト像の明示多項式と係数照合（設計 E4′ ステップ 3） -/

/-- **P9-5a: Φ_9(x+1) の明示多項式** — Φ_9(x+1) = x⁶+6x⁵+15x⁴+21x³+18x²+9x+3。
    係数 (3,9,18,21,15,6,1)。設計の手計算 (x+1)⁶+(x+1)³+1 の検算値。 -/
def p9eShifted : PS ratRing := fun j =>
  if j = 0 then rofNat ratRing 3
  else if j = 1 then rofNat ratRing 9
  else if j = 2 then rofNat ratRing 18
  else if j = 3 then rofNat ratRing 21
  else if j = 4 then rofNat ratRing 15
  else if j = 5 then rofNat ratRing 6
  else if j = 6 then rofNat ratRing 1
  else ratRing.zero

/-- **P9-5b: p9eShifted は 7 次以上で 0**（deg = 6）。 -/
theorem p9eShifted_ge7 (j : Nat) (h : 7 ≤ j) : p9eShifted j = ratRing.zero := by
  show (if j = 0 then rofNat ratRing 3
    else if j = 1 then rofNat ratRing 9
    else if j = 2 then rofNat ratRing 18
    else if j = 3 then rofNat ratRing 21
    else if j = 4 then rofNat ratRing 15
    else if j = 5 then rofNat ratRing 6
    else if j = 6 then rofNat ratRing 1
    else ratRing.zero) = ratRing.zero
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **P9-5c: 冪級数和の点評価** — E = psRing 上の有限和を j 次で読むと、
    各項を j 次で読んだ ratRing の有限和になる（psAdd/psZero の点ごと性）。 -/
theorem p9e_rsum_apply (f : Nat → PS ratRing) (n j : Nat) :
    rsum (psRing ratRing) f n j = rsum ratRing (fun i => f i j) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ratRing.add (rsum (psRing ratRing) f n j) (f n j)
      = ratRing.add (rsum ratRing (fun i => f i j) n) (f n j)
    rw [ih]

/-- **P9-5c′: シフト像の一般係数公式** — 任意の f・打切 M・次数 j で
    p9eShift f M の j 次係数 = Σ_{i<M} f_i·C(i,j)。点評価 (P9-5c) + 各項の
    `psC_mul_coeff` + Pascal 行 (P9-3) で本物に閉じる。 -/
theorem p9e_shift_coeff (f : PS ratRing) (M j : Nat) :
    p9eShift f M j
      = rsum ratRing (fun i => ratRing.mul (f i) (rofNat ratRing (chs i j))) M := by
  show rsum (psRing ratRing)
      (fun i => psMul ratRing (psC ratRing (f i)) (rpow (psRing ratRing) p9eXp1 i)) M j
    = rsum ratRing (fun i => ratRing.mul (f i) (rofNat ratRing (chs i j))) M
  rw [p9e_rsum_apply]
  exact rsum_congr ratRing M (fun i _ => by
    show psMul ratRing (psC ratRing (f i)) (rpow (psRing ratRing) p9eXp1 i) j
      = ratRing.mul (f i) (rofNat ratRing (chs i j))
    rw [psC_mul_coeff ratRing (f i) (rpow (psRing ratRing) p9eXp1 i) j, p9e_pow_coeff i j])

/-- **P9-5d: Φ_9 の重み付き Pascal 和の収束** — Σ_{i<7} Φ_9(i)·C(i,j) は
    Φ_9 の非零係数 i ∈ {0,3,6} のみが生き、C(0,j)+C(3,j)+C(6,j) に収束する。 -/
theorem p9e_rsum_collapse (j : Nat) :
    rsum ratRing (fun i => ratRing.mul (cpdPhi9 i) (rofNat ratRing (chs i j))) 7
      = ratRing.add (ratRing.add (rofNat ratRing (chs 0 j)) (rofNat ratRing (chs 3 j)))
          (rofNat ratRing (chs 6 j)) := by
  show ratRing.add (ratRing.add (ratRing.add (ratRing.add (ratRing.add (ratRing.add
      (ratRing.add ratRing.zero
        (ratRing.mul (cpdPhi9 0) (rofNat ratRing (chs 0 j))))
      (ratRing.mul (cpdPhi9 1) (rofNat ratRing (chs 1 j))))
      (ratRing.mul (cpdPhi9 2) (rofNat ratRing (chs 2 j))))
      (ratRing.mul (cpdPhi9 3) (rofNat ratRing (chs 3 j))))
      (ratRing.mul (cpdPhi9 4) (rofNat ratRing (chs 4 j))))
      (ratRing.mul (cpdPhi9 5) (rofNat ratRing (chs 5 j))))
      (ratRing.mul (cpdPhi9 6) (rofNat ratRing (chs 6 j)))
    = ratRing.add (ratRing.add (rofNat ratRing (chs 0 j)) (rofNat ratRing (chs 3 j)))
        (rofNat ratRing (chs 6 j))
  rw [p9e_phi9_0, p9e_phi9_1, p9e_phi9_2, p9e_phi9_3, p9e_phi9_4, p9e_phi9_5, p9e_phi9_6,
    ratRing.one_mul, ratRing.one_mul, ratRing.one_mul,
    CRing.zero_mul ratRing (rofNat ratRing (chs 1 j)),
    CRing.zero_mul ratRing (rofNat ratRing (chs 2 j)),
    CRing.zero_mul ratRing (rofNat ratRing (chs 4 j)),
    CRing.zero_mul ratRing (rofNat ratRing (chs 5 j)),
    ratRing.zero_add, CRing.add_zero ratRing, CRing.add_zero ratRing,
    CRing.add_zero ratRing, CRing.add_zero ratRing]

/-- **P9-5e: 3 項 rofNat 和の合体** — rofNat の加法保存を 2 回。 -/
theorem p9e_rofNat_collapse (a b c : Nat) :
    ratRing.add (ratRing.add (rofNat ratRing a) (rofNat ratRing b)) (rofNat ratRing c)
      = rofNat ratRing (a + b + c) := by
  rw [rofNat_add ratRing (a + b) c, rofNat_add ratRing a b]

/-- **定理 (P9-5, 本丸): シフト像の係数照合** — Φ_9 の x↦x+1 シフト像は
    明示多項式 x⁶+6x⁵+15x⁴+21x³+18x²+9x+3 に全係数一致する:
    ∀ j, p9eShift Φ_9 7 j = p9eShifted j。
    証明: p9eShift を評価準同型で展開 → 各項を `psC_mul_coeff` と Pascal 行
    `p9e_pow_coeff` で Φ_9(i)·C(i,j) に → Φ_9 の非零 3 係数へ収束
    (P9-5d) → C(0,j)+C(3,j)+C(6,j) を rofNat 合体 → 各 j で chs 値を確定。 -/
theorem p9e_shift_eq : ∀ j, p9eShift cpdPhi9 7 j = p9eShifted j := by
  intro j
  rw [p9e_shift_coeff cpdPhi9 7 j, p9e_rsum_collapse j, p9e_rofNat_collapse]
  cases j with
  | zero => rfl
  | succ j => cases j with
    | zero => rfl
    | succ j => cases j with
      | zero => rfl
      | succ j => cases j with
        | zero => rfl
        | succ j => cases j with
          | zero => rfl
          | succ j => cases j with
            | zero => rfl
            | succ j => cases j with
              | zero => rfl
              | succ n =>
                rw [chs_gt 3 (n + 7) (by omega), chs_gt 6 (n + 7) (by omega),
                  show chs 0 (n + 7) = 0 from rfl, p9eShifted_ge7 (n + 7) (by omega)]
                show rofNat ratRing 0 = ratRing.zero
                rfl

/-! ## P9-6: 先頭係数（設計 E4′ ステップ 6 前半） -/

/-- **定理 (P9-6): Φ_9 の先頭係数 ≠ 0** — Φ_9(6) = 1 ≠ 0（ℚ の非自明性）。
    Eisenstein 判定 E4′ の次数保存・輸送（後半・E3 待ち）の入力。 -/
theorem p9e_phi9_lead : cpdPhi9 6 ≠ ratRing.zero := by
  rw [p9e_phi9_6]
  exact cbp_one_ne_zero

/-! ## P9-7: シフトの次数保存（設計 E4′ ステップ5 の E3非依存な前提部品） -/

/-- **定理 (P9-7): シフトの次数・先頭係数保存** — シフト f ↦ f(x+1)（N+1 打切）は
    N 次係数を保存し（(p9eShift f (N+1))_N = f_N）、deg ≤ N を保つ
    （(N+1) 有界）。三角性: N 次に効くのは i = N の項のみ（C(i,N)=0 for i<N,
    C(N,N)=1）、j ≥ N+1 では全項 C(i,j)=0（i ≤ N < j）。**hf 不要**の強形。
    設計 E4′ ステップ5 の次数保存 deg(p9eShift d)=deg d の核（既約性輸送
    本体は Eisenstein 判定器 E3 完成後に E4′ 後半で接続・本ファイルでは保留）。 -/
theorem p9e_shift_lead (f : PS ratRing) (N : Nat) :
    p9eShift f (N + 1) N = f N
      ∧ IsPolyBounded ratRing (p9eShift f (N + 1)) (N + 1) := by
  refine ⟨?_, ?_⟩
  · rw [p9e_shift_coeff f (N + 1) N,
      rsum_single ratRing (fun i => ratRing.mul (f i) (rofNat ratRing (chs i N))) N (N + 1)
        (by omega)
        (fun q hq hqN => by
          show ratRing.mul (f q) (rofNat ratRing (chs q N)) = ratRing.zero
          rw [chs_gt q N (by omega)]
          exact ratRing.mul_zero (f q))]
    show ratRing.mul (f N) (rofNat ratRing (chs N N)) = f N
    rw [chs_self N, rofNat_one ratRing, CRing.mul_one ratRing]
  · intro j hj
    rw [p9e_shift_coeff f (N + 1) j]
    have hz : rsum ratRing (fun i => ratRing.mul (f i) (rofNat ratRing (chs i j))) (N + 1)
        = rsum ratRing (fun _ => ratRing.zero) (N + 1) :=
      rsum_congr ratRing (N + 1) (fun i hi => by
        show ratRing.mul (f i) (rofNat ratRing (chs i j)) = ratRing.zero
        rw [chs_gt i j (by omega)]
        exact ratRing.mul_zero (f i))
    rw [hz]
    exact rsum_const_zero ratRing (N + 1)

end IUT
