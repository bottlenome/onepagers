/-
  IUT/FrobenioidRealification.lean — M411F（柱C 昇格: Frobenioid の realification を
                          **M312F の本物の実数値 Arakelov 次数 deg_ℝ** で完成する）

  -- M411F FrobenioidRealification [実・本物・柱C]
  -- complete_pct 影響: 柱C で Frobenioid の realification ＝ M312F の実数値 Arakelov 次数
  --   deg_ℝ による実数値次数関手（[FrdI] の次数変換則 deg(φ(x))=n·deg(x)+deg(Div φ) を
  --   本物の ℝ 上で成立させる）へ、M331F の骨組み frobCRealDegree を昇格する。
  -- 正直な限定: 完全な FrdI/FrdII・型付き Frobenioid・ファイバー化・base category の
  --   全公理・Frobenioid 間の theta-link/log-link 連結は柱D/E 後続。

  ── 主要成果の分類: **[実]**（既存骨組みの昇格 (a)）。
     M331F `FrobenioidCategory` は算術 Frobenioid を M307F の本物の因子群
     `picDivGrp` 上の圏として構成し、次数の乗法性 `frobC_degree_mult` を本物で証明した
     が、その **realification は `frobCRealDegree`（＝M312F `logVolGlobal` を RawDiv 代表に
     載せただけの骨組み）** に留まり、Frobenioid の**射の次数変換則**を実数値で結んで
     いなかった。本モジュールはそれを次の形で**本物へ昇格**する:
     (1) **realified 次数関手** `frRealDeg`（＝M312F の Arakelov 次数 deg_ℝ＝`logVolGlobal`）を
         Frobenioid の対象（因子＝RawDiv 代表）上の実数値次数として据える。
     (2) **射の realified 次数変換則** `frRealDeg_hom`:
         Frobenioid の射 f : D→E（Frobenius 次数 n・零因子 Div(φ)=eff）に対し
         **deg_ℝ(E) ≈ n·deg_ℝ(D) + deg_ℝ(eff)**（[FrdI] の次数変換則の実数値化）を
         M312F `logVolGlobal_add`・`logVolGlobal_frob` から本物で証明する。
     (3) **合成での準同型性** `frMorDeg_comp`: 射の零因子部の realified 次数が合成で
         deg_ℝ(Div(g∘f)) ≈ deg(g)·deg_ℝ(Div f) + deg_ℝ(Div g)（捻れ半直積の実数値版）を
         満たす＝realified 次数関手が準同型であること。Frobenius 次数側の乗法性は M331F
         `frobC_degree_mult`（本モジュールでは `frRawComp` の deg が rfl で n·m）。
     (4) **整数次数ブリッジ** `frRealDeg_int_bridge`: unit 重みで deg_ℝ が M307F の commit 済み
         整数次数 `picDivDegree` の ℝ 像に一致（M312F `logVolGlobal_unweighted_degree`）。
     (5) **Frobenius 斉次性** `frRealDeg_frob`: deg_ℝ([n]·D) ≈ n·deg_ℝ(D)（M312F `logVolGlobal_frob`）。
     toy 主語なし——主語は M307F の本物の因子代表 `RawDiv`・M312F の本物の ℝ 値次数
     `logVolGlobal`・M331F の本物の Frobenioid 射（Frobenius 次数付き）である。

  ## 検証する中核（全て sorry なし・新規 Classical.choice なし）

  * M411F-1 `frRealDeg` / `frRealDeg_wd` / `frRealDeg_add` / `frRealDeg_frob` /
    `frRealDeg_int_bridge`
                              — realified 次数関手 deg_ℝ（M312F への昇格）＋ well-defined・
                                加法性・Frobenius 斉次・整数次数ブリッジ（M312F から本物で継承）
  * M411F-2 `frRawHom` / `frRawToHom` / `frRawToHom_deg`
                              — 代表レベルの Frobenioid 射（rawEq 線形条件）と M331F
                                `frobCHom` への本物のブリッジ（choice 不使用）
  * M411F-3 `frRealDeg_hom`     — **射の realified 次数変換則** deg_ℝ(E)≈n·deg_ℝ(D)+deg_ℝ(eff)
                                （[FrdI] deg(φ(x))=n·deg(x)+deg(Div φ) の実数値化・本丸）
  * M411F-4 `frRawComp` / `frMorDeg` / `frMorDeg_comp` / `frRawComp_deg`
                              — 代表射の合成・射の零因子 realified 次数と合成準同型性
                                （捻れ半直積の実数値化・deg 乗法性は rfl）
  * M411F-5 capstone `FrobenioidRealificationData` / `frData` / `fr_exists` /
    `fr_realification_isHom` / `fr_degree_transform` ＋ 実例
    `frFrobRawMor`（Frobenius [n] 射）/ `frFrobRawMor_deg` / `frFrobRawMor_eff_deg` /
    `frFrob_comp_deg`

  ## 正直な限定（何が本物で何が後続か・消去/弱化禁止）

  - **本物（完全証明）**:
    ・realified 次数関手 `frRealDeg`＝M312F の Arakelov 次数 deg_ℝ が Frobenioid の対象
      （因子）上の**実数値次数**であること（加法性・well-defined・Frobenius 斉次・
      整数次数ブリッジを M312F から realEq で継承、完全）。
    ・**射の次数変換則** deg_ℝ(E)≈n·deg_ℝ(D)+deg_ℝ(eff)（[FrdI] の実数値化、M312F
      `logVolGlobal_add`+`logVolGlobal_frob` から本物で、完全）。
    ・**合成準同型性** deg_ℝ(Div(g∘f))≈deg(g)·deg_ℝ(Div f)+deg_ℝ(Div g)（捻れ半直積の
      実数値化、完全）＋ Frobenius 次数の乗法性（`frRawComp` deg = n·m、rfl）。
    ・代表射 `frRawHom` から M331F `frobCHom` への本物のブリッジ `frRawToHom`（choice 不使用）。
  - **正直申告（未達・骨組み・後続。飾りでなく地図）**:
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ realified 次数は RawDiv 代表上で
      **realEq による準同型性**として言明する（因子群 Div=Quot rawEq への厳密 Quot.lift は
      不可、M312F/M331F と同じ正直な扱い）。Grp 圏の ℝ 係数対象化は後続。
    ・**射の realified 次数は代表レベル `frRawHom`（rawEq 線形条件）で定義**する。M331F
      `frobCHom`（Quot レベル）の任意射の realified 次数を choice なしで一意に取り出すには
      因子群の代表選択を要すので、**代表を持つ射 `frRawHom`** で本物に閉じ、`frRawToHom` で
      Quot レベル `frobCHom` へ橋渡しする（choice 不使用の忠実な部分ケース、§3）。
    ・**実重み logq:ℕ→ℝ はパラメータ**（M312F と同じ）。log q_v の超越性・具体値構成、
      アルキメデス素点の log|·|、完全積公式は M312F と同じく後続。
    ・完全な [FrdI/II]（型付き Frobenioid・ファイバー化・base category 全公理）・
      **Frobenioid 間の theta-link/log-link**（Frobenioid の連結）は柱D/E 後続。
      本ファイルは単一 Frobenioid の realified 次数関手と射の次数変換則まで。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無。
-/
import IUT.LogVolume
import IUT.FrobenioidCategory

namespace IUT

/-! ## M411F-1: realified 次数関手 deg_ℝ（M312F Arakelov 次数への昇格） -/

/-- **M411F-1a: realified Frobenioid 次数（実数値 Arakelov 次数 deg_ℝ）** — Frobenioid の
    対象（因子＝M307F `RawDiv` 代表）に M312F の本物の実数値 Arakelov 次数
    `logVolGlobal` を対応させる realified 次数関手。M331F の骨組み `frobCRealDegree` を
    「realification 次数関手そのもの」へ昇格した本体（値は M312F deg_ℝ）。 -/
def frRealDeg (logq : Nat → RReal) (x : RawDiv) : RReal :=
  logVolGlobal logq x

/-- **M411F-1b: well-definedness** — 係数等価な因子代表は同じ realified 次数（≈、
    ℝ は setoid）。因子群 Div=Quot rawEq の上に realEq で well-defined。 -/
theorem frRealDeg_wd (logq : Nat → RReal) {x y : RawDiv} (h : rawEq x y) :
    realEq (frRealDeg logq x) (frRealDeg logq y) :=
  logVolGlobal_wd logq h

/-- **M411F-1c: 加法性** deg_ℝ(D+E) ≈ deg_ℝ(D)+deg_ℝ(E)（M312F `logVolGlobal_add`）。 -/
theorem frRealDeg_add (logq : Nat → RReal) (x y : RawDiv) :
    realEq (frRealDeg logq (rawAdd x y))
      (realAdd (frRealDeg logq x) (frRealDeg logq y)) :=
  logVolGlobal_add logq x y

/-- **M411F-1d: Frobenius 斉次性** deg_ℝ([n]·D) ≈ n·deg_ℝ(D)（M312F `logVolGlobal_frob`）。 -/
theorem frRealDeg_frob (logq : Nat → RReal) (n : Nat) (x : RawDiv) :
    realEq (frRealDeg logq (picDivFrobRaw n x))
      (rmul (intToReal (n : Int)) (frRealDeg logq x)) :=
  logVolGlobal_frob logq n x

/-- **M411F-1e: 整数次数ブリッジ** — unit 重みでの realified 次数は M307F の commit 済み
    整数次数 `picDivDegree`（Div→ℤ）の ℝ 像に一致（M312F `logVolGlobal_unweighted_degree`）。
    realification が M331F の離散次数を忠実に拡張していることの本物の接続。 -/
theorem frRealDeg_int_bridge (x : RawDiv) :
    realEq (frRealDeg logVolUnit x)
      (intToReal (picDivDegree.map (Quot.mk rawEq x))) :=
  logVolGlobal_unweighted_degree x

/-- **M411F-1f: 零因子の realified 次数は 0**。 -/
theorem frRealDeg_zero (logq : Nat → RReal) :
    realEq (frRealDeg logq rawZero) realZero :=
  logVolGlobal_zero logq

/-! ## M411F-2: 代表レベルの Frobenioid 射と M331F frobCHom へのブリッジ -/

/-- **M411F-2a: 代表レベルの Frobenioid 射** D → E — Frobenius 次数 `deg`≥1・
    有効零因子 `eff`（Div(φ)≥0）・線形条件 E ≈ [deg]·D + eff（rawEq）。
    M331F `frobCHom`（Quot レベル）の代表版で、realified 次数を choice なしで扱うための
    忠実な部分ケース。 -/
structure frRawHom (D E : RawDiv) where
  deg : Nat
  deg_pos : 1 ≤ deg
  eff : RawDiv
  eff_eff : picDivEffectiveRaw eff
  linear : rawEq E (rawAdd (picDivFrobRaw deg D) eff)

/-- **M411F-2b: M331F frobCHom へのブリッジ** — 代表射 `frRawHom` は Quot レベルの
    本物の Frobenioid 射 `frobCHom` を誘導する（新規 Classical.choice 不使用、
    因子群の演算・Frobenius 自己準同型の Quot.lift 計算則で線形条件を継承）。 -/
def frRawToHom {D E : RawDiv} (f : frRawHom D E) :
    frobCHom (Quot.mk rawEq D) (Quot.mk rawEq E) where
  deg := f.deg
  deg_pos := f.deg_pos
  eff := Quot.mk rawEq f.eff
  eff_effective := ⟨f.eff, f.eff_eff, rfl⟩
  linear := Quot.sound f.linear

/-- **M411F-2c: ブリッジは次数を保つ** — `frRawToHom` の Frobenius 次数は元の deg。 -/
theorem frRawToHom_deg {D E : RawDiv} (f : frRawHom D E) :
    (frRawToHom f).deg = f.deg := rfl

/-! ## M411F-3: 射の realified 次数変換則（[FrdI] の実数値化・本丸） -/

/-- **M411F-3: 射の realified 次数変換則** — Frobenioid の射 f : D→E（Frobenius 次数 n・
    有効零因子 eff）に対し **deg_ℝ(E) ≈ n·deg_ℝ(D) + deg_ℝ(eff)**。
    [FrdI] の次数変換則 deg(φ(x)) = n·deg(x) + deg(Div φ) の**実数値化**であり、
    M312F の well-definedness（`logVolGlobal_wd`）・加法性（`logVolGlobal_add`）・
    Frobenius 斉次性（`logVolGlobal_frob`）から本物で証明する。realification の中核成果。 -/
theorem frRealDeg_hom (logq : Nat → RReal) {D E : RawDiv} (f : frRawHom D E) :
    realEq (frRealDeg logq E)
      (realAdd (rmul (intToReal (f.deg : Int)) (frRealDeg logq D))
        (frRealDeg logq f.eff)) := by
  refine realEq_trans (logVolGlobal_wd logq f.linear) ?_
  refine realEq_trans (logVolGlobal_add logq (picDivFrobRaw f.deg D) f.eff) ?_
  exact realAdd_congr_left (frRealDeg logq f.eff) (logVolGlobal_frob logq f.deg D)

/-! ## M411F-4: 代表射の合成と射の零因子 realified 次数の準同型性 -/

/-- **M411F-4a: 代表射の合成** (D→E)∘(E→F) = (D→F) — 次数は積 nf·ng、
    有効零因子は捻れ半直積 [ng]·ef + eg（M331F `frobCComp` の代表版）。 -/
def frRawComp {D E F : RawDiv} (f : frRawHom D E) (g : frRawHom E F) :
    frRawHom D F where
  deg := f.deg * g.deg
  deg_pos := by
    have h := Nat.mul_le_mul f.deg_pos g.deg_pos
    omega
  eff := rawAdd (picDivFrobRaw g.deg f.eff) g.eff
  eff_eff := picDivEffective_add (picDivEffective_frob g.deg f.eff_eff) g.eff_eff
  linear := by
    intro k
    have hfk : E.coeff k = (f.deg : Int) * D.coeff k + f.eff.coeff k := f.linear k
    have hgk : F.coeff k = (g.deg : Int) * E.coeff k + g.eff.coeff k := g.linear k
    show F.coeff k = ((f.deg * g.deg : Nat) : Int) * D.coeff k
        + ((g.deg : Int) * f.eff.coeff k + g.eff.coeff k)
    rw [hgk, hfk, Int.natCast_mul, Int.mul_add, ← Int.mul_assoc,
      Int.mul_comm (g.deg : Int) (f.deg : Int), Int.add_assoc]

/-- **M411F-4b: 合成の次数は積**（M331F `frobC_degree_mult` の代表版、rfl）。 -/
theorem frRawComp_deg {D E F : RawDiv} (f : frRawHom D E) (g : frRawHom E F) :
    (frRawComp f g).deg = f.deg * g.deg := rfl

/-- **M411F-4c: 射の零因子 Div(φ) の realified 次数** — 射 f の有効零因子部の
    Arakelov 次数 deg_ℝ(Div φ)。次数変換則の "deg(Div φ)" 項。 -/
def frMorDeg (logq : Nat → RReal) {D E : RawDiv} (f : frRawHom D E) : RReal :=
  frRealDeg logq f.eff

/-- **M411F-4d: 合成での準同型性** — 合成射の零因子 realified 次数は
    deg_ℝ(Div(g∘f)) ≈ deg(g)·deg_ℝ(Div f) + deg_ℝ(Div g)（捻れ半直積 [ng]ef+eg の
    実数値化）。M312F `logVolGlobal_add`+`logVolGlobal_frob` から本物で。realified 次数
    関手が準同型（cocycle）であることの中核。 -/
theorem frMorDeg_comp (logq : Nat → RReal) {D E F : RawDiv}
    (f : frRawHom D E) (g : frRawHom E F) :
    realEq (frMorDeg logq (frRawComp f g))
      (realAdd (rmul (intToReal (g.deg : Int)) (frMorDeg logq f))
        (frMorDeg logq g)) := by
  refine realEq_trans (logVolGlobal_add logq (picDivFrobRaw g.deg f.eff) g.eff) ?_
  exact realAdd_congr_left (frRealDeg logq g.eff)
    (logVolGlobal_frob logq g.deg f.eff)

/-! ## M411F-5: capstone と実例 -/

/-- **M411F-5a: Frobenioid realification データ** — realified 次数関手（deg_ℝ）と
    その加法性・well-defined・Frobenius 斉次性・**射の次数変換則**の束ね。 -/
structure FrobenioidRealificationData (logq : Nat → RReal) where
  /-- realified 次数関手 deg_ℝ:RawDiv→ℝ。 -/
  rdeg : RawDiv → RReal
  /-- 加法性 deg_ℝ(D+E)≈deg_ℝ(D)+deg_ℝ(E)。 -/
  rdeg_add : ∀ x y, realEq (rdeg (rawAdd x y)) (realAdd (rdeg x) (rdeg y))
  /-- rawEq 不変（因子群 Div の上に well-defined）。 -/
  rdeg_wd : ∀ {x y}, rawEq x y → realEq (rdeg x) (rdeg y)
  /-- Frobenius 斉次 deg_ℝ([n]D)≈n·deg_ℝ(D)。 -/
  rdeg_frob : ∀ (n : Nat) (x : RawDiv),
    realEq (rdeg (picDivFrobRaw n x)) (rmul (intToReal (n : Int)) (rdeg x))
  /-- **射の次数変換則** deg_ℝ(E)≈n·deg_ℝ(D)+deg_ℝ(eff)（[FrdI] の実数値化）。 -/
  rdeg_hom : ∀ {D E} (f : frRawHom D E),
    realEq (rdeg E)
      (realAdd (rmul (intToReal (f.deg : Int)) (rdeg D)) (rdeg f.eff))

/-- **M411F-5b: 実データ** — 全フィールドを M312F の本物の deg_ℝ で充足。 -/
def frData (logq : Nat → RReal) : FrobenioidRealificationData logq where
  rdeg := frRealDeg logq
  rdeg_add := frRealDeg_add logq
  rdeg_wd := frRealDeg_wd logq
  rdeg_frob := frRealDeg_frob logq
  rdeg_hom := frRealDeg_hom logq

/-- **M411F-5c: 存在**（`Nonempty` でなく実データ）。 -/
theorem fr_exists (logq : Nat → RReal) :
    Nonempty (FrobenioidRealificationData logq) :=
  ⟨frData logq⟩

/-- **M411F-5d: realification は加法準同型**（capstone 再掲）。 -/
theorem fr_realification_isHom (logq : Nat → RReal) (x y : RawDiv) :
    realEq (frRealDeg logq (rawAdd x y))
      (realAdd (frRealDeg logq x) (frRealDeg logq y)) :=
  frRealDeg_add logq x y

/-- **M411F-5e: realified 次数変換則**（capstone 再掲）— deg_ℝ(E)≈n·deg_ℝ(D)+deg_ℝ(Div φ)。 -/
theorem fr_degree_transform (logq : Nat → RReal) {D E : RawDiv} (f : frRawHom D E) :
    realEq (frRealDeg logq E)
      (realAdd (rmul (intToReal (f.deg : Int)) (frRealDeg logq D))
        (frRealDeg logq f.eff)) :=
  frRealDeg_hom logq f

/-- **M411F-5f: 実例（Frobenius [n] 射）** — 因子 D から [n]·D への代表 Frobenius 射
    （次数 n・零因子 0）。IUT の Frobenius 自己射の realification 版。 -/
def frFrobRawMor (n : Nat) (hn : 1 ≤ n) (D : RawDiv) : frRawHom D (picDivFrobRaw n D) where
  deg := n
  deg_pos := hn
  eff := rawZero
  eff_eff := picDivEffective_zero
  linear := by
    intro k
    show (n : Int) * D.coeff k = (n : Int) * D.coeff k + (0 : Int)
    omega

/-- **M411F-5g: Frobenius [n] 射の realified 次数**（実例、完全）— deg_ℝ([n]D)≈n·deg_ℝ(D)。 -/
theorem frFrobRawMor_deg (logq : Nat → RReal) (n : Nat) (hn : 1 ≤ n) (D : RawDiv) :
    realEq (frRealDeg logq (picDivFrobRaw n D))
      (rmul (intToReal (n : Int)) (frRealDeg logq D)) :=
  frRealDeg_frob logq n D

/-- **M411F-5h: Frobenius [n] 射の零因子 realified 次数は 0**（実例、完全）— Div(φ)=0。 -/
theorem frFrobRawMor_eff_deg (logq : Nat → RReal) (n : Nat) (hn : 1 ≤ n) (D : RawDiv) :
    realEq (frMorDeg logq (frFrobRawMor n hn D)) realZero :=
  logVolGlobal_zero logq

/-- **M411F-5i: Frobenius 射の合成の次数は積**（次数乗法性の実例、rfl）。 -/
theorem frFrob_comp_deg (n m : Nat) (hn : 1 ≤ n) (hm : 1 ≤ m) (D : RawDiv) :
    (frRawComp (frFrobRawMor n hn D)
      (frFrobRawMor m hm (picDivFrobRaw n D))).deg = n * m := rfl

end IUT
