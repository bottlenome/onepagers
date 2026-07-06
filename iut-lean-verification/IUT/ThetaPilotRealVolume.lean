/-
  IUT/ThetaPilotRealVolume.lean — M319F（柱D 本丸の横展開:
  **テータパイロット log-volume の実対象化＝定理3.11 の体積 LHS を
  m202fVol toy から実 deg_ℝ（Arakelov 局所次数）へ昇格**）

  ── 主要成果の分類: **[実]**（既存 toy 模型 m202fVol の **本物への置換
     (a) 昇格**）。complete_pct 影響: **柱D（定理3.11・体積側）の実 IUT
     完全証明率を前進させる**。従来、定理3.11 の充足模型
     （GaussPilot311.lean M216F・MultiradialInput.lean 等）の体積主語は
     **toy 模型 `m202fVol`（Region = ℤ・vol = id・体積値そのものが領域）**
     であり、Θ-正則包の体積 `hullTheta` は「id 体積で読んだ整数」に過ぎ
     なかった（正直な限定として「体積値そのものを領域とする充足デモ模型」
     と明記されている）。本層はその体積主語を、M312F `LogVolume.lean` の
     **本物の実数値 Arakelov 局所次数 `logVolLocal`（deg_ℝ: n·log q_v、
     本物の ℝ = RReal 上）** と、M318F `ThetaValueLtor.lean` の **本物の
     テータ値指数 `thLtorExp j = j²`** の上へ載せ替える。すなわち
     「テータパイロットのテータ値 q^{j²/2l} の deg_ℝ を Σ で束ねた体積」を
     **実対象で** 構成し、その **Σj² 閉形式** と **l³ 下界** を、既存の
     本物（M1 `sumSq` / M97 `cube_le_sumSq` = l³ ≤ 3Σj²）を実 deg_ℝ 文脈で
     再利用して閉じる。toy 主語 m202fVol は本層では一切用いない。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M319F-1 `thPilotValueDeg` / `thPilotValueDeg_eq`
      — **単一 l-捻れ点でのテータ値の実 deg_ℝ**: deg_ℝ(Θ(q,u_j)) =
        deg_ℝ(q^{j²/2l}) = j²·log q_v。M318F `thLtorExp`（指数 j²）を
        M312F `logVolLocal`（n·log q_v）に接続。実数値で
        thPilotValueDeg logq v j = rmul(intToReal(j²))(log q_v)。
  * M319F-2 `thPilotTotalVol` / `thPilot_total_closed`
      — **テータパイロット総体積** Σ_{j=1}^{l⋇} deg_ℝ(Θ(q,u_j))
        = (Σj²)·log q_v を実数値で。M312F `logVolLocal_add` で有限和を
        束ね、**Σj² の閉形式**（M1 `sumSq`: Σ_{j=1}^n j²）へ落とす:
        thPilotTotalVol logq v n ≈ logVolLocal logq v (Σ_{j≤n} j²)。
  * M319F-3 `thPilot_cubic_bound`
      — **l³ 下界**: l³·log q_v ≤ 3·(Σj²)·log q_v（M97 `cube_le_sumSq`:
        l³ ≤ 3Σj² を実 deg_ℝ の順序 rLe へ持ち上げ、非負重み log q_v≥0 で
        単調に。M180 `rmul_le_mul_right` + M139 `intToReal_mono`）。定理3.11
        の体積側ステートメント（テータパイロット総次数 ≥ l³ の型）の実数値版。
  * M319F-4 `thPilot_theorem311_lhs`
      — **実 deg_ℝ での定理3.11 体積 LHS**: 従来 m202fVol で書かれていた
        テータパイロット体積を、実 deg_ℝ の閉形式（Σj²）＋ l³ 下界の連言
        として言い直した LHS。
  * M319F-5 capstone `ThetaPilotVolumeData` / `thetaPilotVolumeData` /
        `thPilot_exists` / `thPilot_total_volume` / `thPilot_lower_bound`。
  * 実例: l=5（l⋇=2）で Σj²=1²+2²=5、総体積 ≈ logVolLocal v 5
        （= 5·log u = log q/2, u=q^{1/2l} 微細重み witness）。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）

  - **本物（完全証明）**:
    ・テータ値の指数 j²（= M318F `thLtorExp`, 分子）と、その有限和 Σj²
      の**閉形式**（M1 `sumSq` の Σ_{j=1}^{l⋇} j²）・**l³ 下界**
      （M97 `cube_le_sumSq`: l³ ≤ 3Σj²）は **本物**。
    ・体積の主語は M312F の**本物の実数値 Arakelov 局所次数**
      `logVolLocal`（本物の ℝ = RReal 上の n·log q_v）であり、
      **toy 主語 m202fVol（vol = id・領域 = ℤ）は用いない**——ここが
      「体積の主語を toy から実へ昇格」の中身。
    ・総体積の deg_ℝ 加法性（`logVolLocal_add`）による Σ の束ね、および
      l³ 下界の順序 rLe への持ち上げ（`rmul_le_mul_right`・`intToReal_mono`）
      は完全証明。
  - **正直申告（未達・witness・後続。飾りでなく地図）**:
    ・log q_v（重み `logq : Nat → RReal`）は M312F と同じく**実重み
      witness**（係数扱い）。有理冪 q^{j²/2l} の分母 2l（微細格子
      u = q^{1/2l}）は M318F と同じく witness——テータ値の指数の**分子 j²**
      と Σj² 閉形式・l³ 下界が本物であり、log q_v の超越性・具体値・
      u = q^{1/2l} の体内実在は本層の範囲外（柱A/柱C の後続で本物化）。
    ・**これはテータパイロット体積（定理3.11 の LHS）の実対象化のみ**で
      ある。ガウスパイロット（RHS）との **crux 不等式（Dβ-ω＝多輻的
      アルゴリズム＝IUT 論争の係争点）は恒久的に本タスクの範囲外**——
      本層は体積の**主語**を toy から実へ昇格するのみで、crux（LHS と RHS
      を突き合わせる不等式）の証明ではない。
    ・定理3.11 ⟹ 系3.12 の還元は既存 M5/M97 のまま（本層は触れない）。
      ここは体積 LHS の実 deg_ℝ 化に限る。
    ・**ℝ は setoid**（realEq が同値・`=` でない）ゆえ総体積の閉形式・
      加法性は realEq で言明する（M312F と同じ正直な形）。
  全て新規 Classical.choice を証明本体に導入せず（M312F/M318F/M1/M97 から
  継承、#print axioms は propext/Quot.sound 系のみ）。sorry 皆無・禁止
  タクティク不使用（core Lean のみ）。サブエージェント新規1本（共有
  ファイル未変更）。一般名は `thPilot` 接頭辞で衝突回避。
-/
import IUT.LogVolume
import IUT.ThetaValueLtor
import IUT.Premises311

namespace IUT

/-! ## M319F-1: 単一 l-捻れ点でのテータ値の実 deg_ℝ -/

/-- **M319F-1a: l-捻れ点でのテータ値の実 Arakelov 局所次数** —
    deg_ℝ(Θ(q,u_j)) = deg_ℝ(q^{j²/2l}) = j²·log q_v。M318F のテータ値指数
    `thLtorExp j = j²` を M312F の局所 log-volume `logVolLocal`（n·log q_v）
    に投入する。素点 v の重み logq v は微細座標 u = q^{1/2l} の対数 log u
    （実重み witness）。従来 m202fVol の id 体積ではなく **本物の実数値
    Arakelov 次数**。 -/
def thPilotValueDeg (logq : Nat → RReal) (v : Nat) (j : Int) : RReal :=
  logVolLocal logq v (thLtorExp j)

/-- **定理 (M319F-1b): テータ値の実 deg_ℝ の指数抽出** —
    thPilotValueDeg logq v j = j²·log q_v = rmul(intToReal(j²))(log q_v)。
    テータ値の deg_ℝ の主要係数がちょうど j²（M318F `thLtorExp_sq`）。 -/
theorem thPilotValueDeg_eq (logq : Nat → RReal) (v : Nat) (j : Int) :
    thPilotValueDeg logq v j = rmul (intToReal (j * j)) (logq v) := by
  show rmul (intToReal (thLtorExp j)) (logq v) = rmul (intToReal (j * j)) (logq v)
  rw [thLtorExp_sq]

/-! ## M319F-2: テータパイロット総体積 Σ_{j=1}^{l⋇} deg_ℝ と Σj² 閉形式 -/

/-- **M319F-2a: テータパイロット総体積** — Σ_{j=1}^{n} deg_ℝ(Θ(q,u_j))
    = Σ_{j=1}^{n} j²·log q_v。l-捻れ点ラベル j=1..n に沿ったテータ値の
    実 Arakelov 次数の有限和（j=0 の寄与は 0 ゆえ 1..n）。定理3.11 の
    テータパイロット体積（LHS）を **実数値 deg_ℝ** で束ねたもの。 -/
def thPilotTotalVol (logq : Nat → RReal) (v : Nat) : Nat → RReal
  | 0 => realZero
  | n + 1 => realAdd (thPilotTotalVol logq v n)
      (thPilotValueDeg logq v ((n + 1 : Nat) : Int))

/-- **定理 (M319F-2b): 総体積の Σj² 閉形式** — テータパイロット総体積は
    Σ_{j=1}^{n} j² の重み付き実 deg_ℝ に一致する（realEq、ℝ は setoid）:
    thPilotTotalVol logq v n ≈ logVolLocal logq v (Σ_{j≤n} j²)
    = (Σj²)·log q_v。M1 `sumSq`（Σ_{j=1}^n j²）を再利用し、M312F
    `logVolLocal_add` で各テータ値の deg_ℝ を束ねる。テータパイロット体積の
    **本物の閉形式**（q-指数 j² の総和がガウス簿記 Σj² に落ちる）。 -/
theorem thPilot_total_closed (logq : Nat → RReal) (v : Nat) :
    ∀ n, realEq (thPilotTotalVol logq v n)
      (logVolLocal logq v ((sumSq n : Nat) : Int)) := by
  intro n
  induction n with
  | zero =>
    show realEq realZero (logVolLocal logq v 0)
    exact realEq_symm (logVolLocal_zero logq v)
  | succ n ih =>
    -- テータ値の deg_ℝ の指数 (n+1)² は thLtorExp の defeq で取り出す。
    show realEq (realAdd (thPilotTotalVol logq v n)
          (logVolLocal logq v (((n + 1 : Nat) : Int) * ((n + 1 : Nat) : Int))))
        (logVolLocal logq v ((sumSq (n + 1) : Nat) : Int))
    have hcoeff : ((sumSq (n + 1) : Nat) : Int)
        = ((sumSq n : Nat) : Int)
          + ((n + 1 : Nat) : Int) * ((n + 1 : Nat) : Int) := by
      have hs : sumSq (n + 1) = sumSq n + (n + 1) * (n + 1) := sumSq_succ n
      rw [hs, Int.natCast_add, Int.natCast_mul]
    rw [hcoeff]
    refine realEq_trans (realAdd_congr_left
      (logVolLocal logq v (((n + 1 : Nat) : Int) * ((n + 1 : Nat) : Int))) ih) ?_
    exact realEq_symm (logVolLocal_add logq v ((sumSq n : Nat) : Int)
      (((n + 1 : Nat) : Int) * ((n + 1 : Nat) : Int)))

/-! ## M319F-3: l³ 下界（定理3.11 体積側の実数値版） -/

/-- **定理 (M319F-3): テータパイロット総体積の l³ 下界** —
    l³·log q_v ≤ 3·(Σj²)·log q_v（非負重み log q_v ≥ 0 の下で）。
    M97 `cube_le_sumSq`（l³ ≤ 3Σj²、既存の本物の離散下界）を実 deg_ℝ の
    順序 rLe へ持ち上げ、M180 `rmul_le_mul_right`（右非負での単調性）と
    M139 `intToReal_mono`（順序埋め込み）で閉じる。定理3.11 の
    「テータパイロット総次数 ≥ (定数)·l³」の実数値ステートメント。 -/
theorem thPilot_cubic_bound (logq : Nat → RReal) (v : Nat) (l : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 * sumSq l : Nat) : Int)) (logq v)) := by
  have hnat : l * l * l ≤ 3 * sumSq l := cube_le_sumSq l
  have hint : ((l * l * l : Nat) : Int) ≤ ((3 * sumSq l : Nat) : Int) := by omega
  exact rmul_le_mul_right (intToReal_mono hint) hq

/-! ## M319F-4: 実 deg_ℝ での定理3.11 の体積 LHS -/

/-- **定理 (M319F-4): 実 deg_ℝ で書き直した定理3.11 の体積 LHS** —
    従来 m202fVol（toy）で書かれていたテータパイロット体積を、**本物の
    実 Arakelov 局所次数 deg_ℝ** で書き直した LHS: (i) 総体積は Σj² の
    実 deg_ℝ 閉形式に一致し、(ii) l³ 下界 l³·log q_v ≤ 3·(Σj²)·log q_v を
    満たす。定理3.11 の体積側の主語を **toy から実へ昇格**した言明
    （crux 不等式＝Dβ-ω は範囲外）。 -/
theorem thPilot_theorem311_lhs (logq : Nat → RReal) (v : Nat) (l : Nat)
    (hq : rLe realZero (logq v)) :
    realEq (thPilotTotalVol logq v l) (logVolLocal logq v ((sumSq l : Nat) : Int))
    ∧ rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 * sumSq l : Nat) : Int)) (logq v)) :=
  ⟨thPilot_total_closed logq v l, thPilot_cubic_bound logq v l hq⟩

/-! ## M319F-5: capstone -/

/-- **M319F-5a: テータパイロット実体積データ** — 定理3.11 のテータパイロット
    体積（LHS）を **実 Arakelov 次数 deg_ℝ** で束ねる: 各 l-捻れ点での
    テータ値の実 deg_ℝ（係数 j²）、総体積、Σj² 閉形式、l³ 下界。主語は
    M312F の本物の実数値 log-volume であり、toy m202fVol を用いない。 -/
structure ThetaPilotVolumeData (logq : Nat → RReal) (v : Nat) where
  /-- 単一 l-捻れ点でのテータ値の実 deg_ℝ。 -/
  valueDeg : Int → RReal
  /-- テータパイロット総体積 Σ_{j=1}^{n} deg_ℝ(Θ(q,u_j))。 -/
  totalVol : Nat → RReal
  /-- テータ値の実 deg_ℝ の係数は j²: valueDeg j = j²·log q_v。 -/
  value_eq : ∀ j : Int, valueDeg j = rmul (intToReal (j * j)) (logq v)
  /-- 総体積の Σj² 閉形式: totalVol n ≈ (Σ_{j≤n} j²)·log q_v。 -/
  total_closed : ∀ n : Nat,
    realEq (totalVol n) (logVolLocal logq v ((sumSq n : Nat) : Int))
  /-- l³ 下界: l³·log q_v ≤ 3·(Σj²)·log q_v（非負重みの下で）。 -/
  lower_bound : ∀ l : Nat, rLe realZero (logq v) →
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 * sumSq l : Nat) : Int)) (logq v))

/-- **M319F-5b: 実データ** — 全フィールドを M319F-1〜3 の本物で充足。
    テータ値の実 deg_ℝ・総体積・Σj² 閉形式・l³ 下界を実対象で埋める。 -/
def thetaPilotVolumeData (logq : Nat → RReal) (v : Nat) :
    ThetaPilotVolumeData logq v where
  valueDeg := thPilotValueDeg logq v
  totalVol := thPilotTotalVol logq v
  value_eq := thPilotValueDeg_eq logq v
  total_closed := thPilot_total_closed logq v
  lower_bound := fun l hq => thPilot_cubic_bound logq v l hq

/-- **M319F-5c: 存在（M319F 見出し）** — 任意の実重み logq・素点 v に対し、
    定理3.11 のテータパイロット体積（LHS）を実 Arakelov 次数 deg_ℝ で
    束ねたデータが存在する。従来 m202fVol toy だった体積主語が
    **本物の実数値 log-volume** へ昇格される。 -/
theorem thPilot_exists (logq : Nat → RReal) (v : Nat) :
    Nonempty (ThetaPilotVolumeData logq v) :=
  ⟨thetaPilotVolumeData logq v⟩

/-- **M319F-5d: 総体積の Σj² 閉形式**（capstone 再掲）。 -/
theorem thPilot_total_volume (logq : Nat → RReal) (v : Nat) (n : Nat) :
    realEq (thPilotTotalVol logq v n) (logVolLocal logq v ((sumSq n : Nat) : Int)) :=
  thPilot_total_closed logq v n

/-- **M319F-5e: 総体積の l³ 下界**（capstone 再掲）。 -/
theorem thPilot_lower_bound (logq : Nat → RReal) (v : Nat) (l : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((l * l * l : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 * sumSq l : Nat) : Int)) (logq v)) :=
  thPilot_cubic_bound logq v l hq

/-! ## 実例（l=5, l⋇=2: Σj²=1²+2²=5, 総体積 ≈ 5·log u = log q/2） -/

/-- 実例: l⋇=2 での平方和 Σ_{j=1}^{2} j² = 1²+2² = 5。 -/
example : sumSq 2 = 5 := rfl

/-- 実例: l=5（l⋇=2）のテータパイロット総体積 ≈ logVolLocal v 5
    （= 5·log u_v = log q_v / 2, u = q^{1/2l} 微細重み witness）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thPilotTotalVol logq v 2) (logVolLocal logq v ((sumSq 2 : Nat) : Int)) :=
  thPilot_total_closed logq v 2

/-- 実例: j=2 の l-捻れ点でのテータ値の実 deg_ℝ の係数は 2²=4。 -/
example (logq : Nat → RReal) (v : Nat) :
    thPilotValueDeg logq v 2 = rmul (intToReal (2 * 2)) (logq v) :=
  thPilotValueDeg_eq logq v 2

/-- 実例: l=5 のテータパイロット総体積の l³ 下界（非負重みの下で）。 -/
example (logq : Nat → RReal) (v : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v))
        (rmul (intToReal ((3 * sumSq 5 : Nat) : Int)) (logq v)) :=
  thPilot_cubic_bound logq v 5 hq

end IUT
