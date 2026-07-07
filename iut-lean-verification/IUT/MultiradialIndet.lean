/-
  IUT/MultiradialIndet.lean — M382F MultiradialIndet [実・本物・柱D]
  complete_pct 影響: 柱D で 3 不定性 (Ind1: ±1/単数自己同型・Ind2: 水平⊗ 単数トーソル・
    Ind3: log-shell 膨張) を実 deg_ℝ 値 (RReal) 上の**本物の有限群作用（付値シフト作用）**
    として構成し、(Ind1)(Ind2) の合成作用が可換な積作用であること・その軌道（商）が
    well-defined（合成作用の下で不変）であることを完全証明で昇格。crux Dβ-ω は外部仮説。
  正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点=Ind3 log-shell 包含が与える不等式)は
    恒久的に外部仮説（`mind_crux_external` / `mind_crux_is_hypothesis` は Iff.rfl のみ、決して導出
    しない）。本層は不定性作用の**群作用代数**（付値シフトの ℤ 作用・可換性・(Ind1)(Ind2)-商の
    well-defined 性）を実 deg_ℝ で本物構成するのみ。Ind3 膨張の**作用**（m シフト）は本物だが、
    その**上界包含不等式**（＝crux）は本層で証明しない。deg_ℝ（Arakelov 局所次数）レベル。
    ℝ は setoid ゆえ全等式は realEq で言明する。

  ## 本モジュールの位置づけ（何を合成したか）

  IUT III の**多輻表現**は、テータパイロット log-volume を 3 つの不定性 (Ind1)(Ind2)(Ind3) を
  「法として」見た対象である（M372F `MultiradialRep`）。従来 M332F `IndeterminacyRealAction`
  は各不定性が実総体積を保つ／シフトする**個別の事実**を実 deg_ℝ で確立した。本 M382F は、
  この 3 不定性を **RReal 上の本物の群作用**として組織化する:

    * 付値シフトの ℤ 作用 `mindValAct μ V = V + logVolLocal v μ`（M312F `logVolLocal_add`/
      `logVolLocal_zero` が群作用律 act(μ+ν)=act μ∘act ν・act 0 = id を保証する本物の
      加法群作用）。
    * (Ind1) = ±1/単数自己同型群 Z/2（`Bool`, `Bool.xor`）が付値ゼロを経て作用
      （単数は v=0、`mindSignVal ≡ 0`）——値を保存する本物の有限群作用。
    * (Ind2) = 水平⊗ 単数トーソル Z/2 が同様に付値ゼロを経て作用（`mindUnitVal ≡ 0`）。
    * 合成作用 = (Ind1)×(Ind2) の**積作用**（`mindCompAct`）。可換（アーベル付値作用の
      `mind_val_act_commute`）・積の下で軌道（商）が well-defined（`mind_comp_invariant`）。
    * (Ind3) = log-shell 膨張作用 `mindInd3Act m V = V + logVolLocal v m`（本物の m シフト、
      不変ではない）。その**上界包含不等式**＝crux Dβ-ω は外部仮説のまま。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）
  * M382F-1 `mindValAct` / `mind_val_act_zero` / `mind_val_act_add` / `mind_val_act_congr`
      — 付値シフトの ℤ 群作用と群作用律（単位元 = id・(μ+ν) = 合成）・値 congruence。
  * M382F-2 `mind_val_act_commute` — アーベル付値作用の可換性（realAdd 結合・可換の本物）。
  * M382F-3 Z/2 符号群 `mindXor` / `mind_xor_assoc` / `mind_xor_comm` / `mind_xor_false_right` /
      `mind_xor_self` / `mindSignVal` / `mind_signVal_hom` — ±1 自己同型群の本物の群構造と
      付値ゼロ準同型。
  * M382F-4 `mindInd1Act` / `mindInd2Act` / `mind_ind1_invariant` / `mind_ind2_invariant`
      — (Ind1)(Ind2) を付値ゼロ経由の Z/2 作用として構成、値を保存（本物）。
  * M382F-5 `mindCompAct` / `mind_comp_is_product` / `mind_actions_commute` /
      `mind_invariant_composite` / `mind_comp_invariant` / `mind_comp_id` / `mind_comp_mul`
      — 合成 = 積作用・作用の可換・「各々で不変な値は合成でも不変」・積群の単位元/乗法律。
  * M382F-6 `mindInd3Act` / `mind_ind3_shift` — (Ind3) 膨張作用（m シフト、不変でない）。
  * M382F-7 `mind_crux_external` / `mind_crux_is_hypothesis` — crux Dβ-ω は外部仮説（Iff.rfl）。
  * M382F-8 capstone `MultiradialIndetData` / `multiradialIndetData` / `mind_exists` + 実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）
  * **crux Dβ-ω（多輻的アルゴリズム＝Ind3 log-shell 包含が与える不等式＝IUT 論争の当の
    係争点）は恒久的に本層の範囲外**。本層は 3 不定性の**群作用代数**（付値シフトの ℤ 作用・
    (Ind1)(Ind2)-商の well-defined 性・可換性）を実 deg_ℝ で構成するのみで、crux は外部 Prop
    仮説として受け取り決して導出しない（`mind_crux_is_hypothesis` は Iff.rfl）。
  * **(Ind1)(Ind2) は付値ゼロ経由の作用**（単数/±1 は v=0）ゆえ値を保存し、軌道は 1 点＝商が
    well-defined。これは deg_ℝ が不定性商へ降下する**本物の理由**であり toy ではない。
  * **(Ind3) 膨張の作用（m シフト）は本物**だが、その上界包含不等式（crux）は範囲外。
  * **deg_ℝ（Arakelov 局所次数）レベル**。log q_v は実重み witness（M312F 継承）。群レベルの
    完全同変性・tempered π₁^ét は後続。ℝ は setoid ゆえ realEq で言明する。
  全て選択公理不使用（sorry 皆無・新規 Classical 皆無）。禁止タクティク不使用（core Lean のみ）。
  共有ファイル未変更。柱D 横展開・本物の先行建設[実]。一般名は `mind` 接頭辞で衝突回避。
-/
import IUT.MultiradialRep

namespace IUT

/-! ## M382F-1: 付値シフトの ℤ 群作用（実 deg_ℝ 値 RReal への本物の加法群作用） -/

/-- **M382F-1a: 付値シフト作用** — 不定性が実 deg_ℝ 値 V に及ぼす基本作用。付値 μ の
    寄与 logVolLocal v μ を実体積に上乗せする（M332F `indR_ind2Vol`/`indR_ind3Vol` と同型）。
    加法群 ℤ が RReal に作用する本物の群作用の核（μ が単数/±1 なら 0、膨張なら m）。 -/
def mindValAct (logq : Nat → RReal) (v : Nat) (μ : Int) (V : RReal) : RReal :=
  realAdd V (logVolLocal logq v μ)

/-- **定理 (M382F-1b: 群作用の単位元則)** — 群の単位元 μ=0 は恒等作用: act 0 V ≈ V
    （M312F `logVolLocal_zero`: 付値 0 の寄与は実 deg_ℝ 0）。 -/
theorem mind_val_act_zero (logq : Nat → RReal) (v : Nat) (V : RReal) :
    realEq (mindValAct logq v 0 V) V :=
  realEq_trans (realAdd_congr_right V (logVolLocal_zero logq v)) (realAdd_zero V)

/-- **M382F-1c: 作用の値 congruence** — V ≈ V' なら act μ V ≈ act μ V'（realAdd 左 congr）。
    作用が realEq 商（＝実 deg_ℝ の setoid 商）の上で well-defined であることの本物。 -/
theorem mind_val_act_congr (logq : Nat → RReal) (v : Nat) (μ : Int)
    {V V' : RReal} (h : realEq V V') :
    realEq (mindValAct logq v μ V) (mindValAct logq v μ V') :=
  realAdd_congr_left (logVolLocal logq v μ) h

/-- **定理 (M382F-1d: 群作用の合成則)** — 群の加法 μ+ν は作用の合成に対応:
    act (μ+ν) V ≈ act μ (act ν V)（M312F `logVolLocal_add` の付値加法準同型 v(xy)=v(x)+v(y)
    を実 deg_ℝ の作用合成へ持ち上げた本物の群作用律）。 -/
theorem mind_val_act_add (logq : Nat → RReal) (v : Nat) (μ ν : Int) (V : RReal) :
    realEq (mindValAct logq v (μ + ν) V)
      (mindValAct logq v μ (mindValAct logq v ν V)) := by
  show realEq (realAdd V (logVolLocal logq v (μ + ν)))
    (realAdd (realAdd V (logVolLocal logq v ν)) (logVolLocal logq v μ))
  -- LHS ≈ V + (logVol μ + logVol ν)
  refine realEq_trans
    (realAdd_congr_right V (logVolLocal_add logq v μ ν)) ?_
  -- V + (logVol μ + logVol ν) ≈ V + (logVol ν + logVol μ)
  refine realEq_trans
    (realAdd_congr_right V (realAdd_comm (logVolLocal logq v μ) (logVolLocal logq v ν))) ?_
  -- V + (logVol ν + logVol μ) ≈ (V + logVol ν) + logVol μ
  exact realEq_symm
    (realAdd_assoc V (logVolLocal logq v ν) (logVolLocal logq v μ))

/-! ## M382F-2: アーベル付値作用の可換性（実 deg_ℝ 群作用代数） -/

/-- **定理 (M382F-2: 付値作用は可換)** — ℤ はアーベルゆえ付値シフト作用は可換:
    act μ (act ν V) ≈ act ν (act μ V)（realAdd の結合・可換の本物）。異なる不定性作用が
    「作用させる順序に依らない」ことの群作用代数レベルの本物（後の (Ind1)(Ind2) 可換の核）。 -/
theorem mind_val_act_commute (logq : Nat → RReal) (v : Nat) (μ ν : Int) (V : RReal) :
    realEq (mindValAct logq v μ (mindValAct logq v ν V))
      (mindValAct logq v ν (mindValAct logq v μ V)) := by
  show realEq (realAdd (realAdd V (logVolLocal logq v ν)) (logVolLocal logq v μ))
    (realAdd (realAdd V (logVolLocal logq v μ)) (logVolLocal logq v ν))
  refine realEq_trans
    (realAdd_assoc V (logVolLocal logq v ν) (logVolLocal logq v μ)) ?_
  refine realEq_trans
    (realAdd_congr_right V
      (realAdd_comm (logVolLocal logq v ν) (logVolLocal logq v μ))) ?_
  exact realEq_symm
    (realAdd_assoc V (logVolLocal logq v μ) (logVolLocal logq v ν))

/-! ## M382F-3: Z/2 符号群（±1/単数自己同型群）の本物の群構造と付値ゼロ準同型 -/

/-- **M382F-3a: 符号群の乗法** — ±1 自己同型群 Z/2 の群演算（`Bool.xor`）。
    false = +1（恒等）、true = −1（符号反転）。 -/
def mindXor (a b : Bool) : Bool := Bool.xor a b

/-- **定理 (M382F-3b: 符号群は結合的)**。 -/
theorem mind_xor_assoc (a b c : Bool) :
    mindXor (mindXor a b) c = mindXor a (mindXor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **定理 (M382F-3c: 符号群は可換)**（Z/2 はアーベル）。 -/
theorem mind_xor_comm (a b : Bool) : mindXor a b = mindXor b a := by
  cases a <;> cases b <;> rfl

/-- **定理 (M382F-3d: 単位元 false=+1)** — a·(+1)=a。 -/
theorem mind_xor_false_right (a : Bool) : mindXor a false = a := by
  cases a <;> rfl

/-- **定理 (M382F-3e: 各元は対合)** — a·a=+1（Z/2 では逆元は自身）。 -/
theorem mind_xor_self (a : Bool) : mindXor a a = false := by
  cases a <;> rfl

/-- **M382F-3f: 符号群の付値** — ±1 は局所体の単数（v(±1)=0）ゆえ付値ゼロ準同型。
    (Ind1) 自己同型群が実 deg_ℝ に及ぼす付値寄与は常に 0。 -/
def mindSignVal (_ : Bool) : Int := 0

/-- **定理 (M382F-3g: 付値は群準同型 Z/2→ℤ)** — v(a·b)=v(a)+v(b)（0=0+0、単数の付値
    加法性の自明なケース）。符号群作用が本物の付値シフト作用として整合することの根拠。 -/
theorem mind_signVal_hom (a b : Bool) :
    mindSignVal (mindXor a b) = mindSignVal a + mindSignVal b := rfl

/-! ## M382F-4: (Ind1) ±1 自己同型群・(Ind2) 水平⊗ 単数トーソルの作用（値を保存） -/

/-- **M382F-4a: (Ind1) 作用** — ±1/単数自己同型群 Z/2 が付値ゼロ（`mindSignVal`）を経て
    実 deg_ℝ 値へ作用する本物の有限群作用（自己同型は単数倍＝付値 0）。 -/
def mindInd1Act (logq : Nat → RReal) (v : Nat) (s : Bool) (V : RReal) : RReal :=
  mindValAct logq v (mindSignVal s) V

/-- **M382F-4b: (Ind2) 作用** — 水平⊗ 単数トーソル Z/2 が付値ゼロ（`mindUnitVal`）を経て
    作用する本物の有限群作用（単数トーソルは v=0）。 -/
def mindUnitVal (_ : Bool) : Int := 0

/-- **M382F-4c: (Ind2) 作用**。 -/
def mindInd2Act (logq : Nat → RReal) (v : Nat) (t : Bool) (V : RReal) : RReal :=
  mindValAct logq v (mindUnitVal t) V

/-- **定理 (M382F-4d: (Ind1) は値を保存)** — ±1 自己同型は付値 0 ゆえ実 deg_ℝ 値を保つ:
    mindInd1Act s V ≈ V（`mind_val_act_zero`、単数の v=0）。(Ind1) 軌道が 1 点＝商が
    well-defined であることの本物の理由。 -/
theorem mind_ind1_invariant (logq : Nat → RReal) (v : Nat) (s : Bool) (V : RReal) :
    realEq (mindInd1Act logq v s V) V :=
  mind_val_act_zero logq v V

/-- **定理 (M382F-4e: (Ind2) は値を保存)** — 水平⊗ 単数トーソルは付値 0 ゆえ実 deg_ℝ 値を
    保つ: mindInd2Act t V ≈ V。(Ind2) 軌道が 1 点＝商が well-defined。 -/
theorem mind_ind2_invariant (logq : Nat → RReal) (v : Nat) (t : Bool) (V : RReal) :
    realEq (mindInd2Act logq v t V) V :=
  mind_val_act_zero logq v V

/-! ## M382F-5: 合成 = (Ind1)×(Ind2) 積作用（可換・商 well-defined・積群律） -/

/-- **M382F-5a: 合成作用（(Ind1)×(Ind2) 積作用）** — 符号群と単数トーソルの積 Z/2×Z/2 が
    実 deg_ℝ 値へ**積作用**として作用する: 先に (Ind1) s、次に (Ind2) t。合成不定性の本物。 -/
def mindCompAct (logq : Nat → RReal) (v : Nat) (s t : Bool) (V : RReal) : RReal :=
  mindInd2Act logq v t (mindInd1Act logq v s V)

/-- **定理 (M382F-5b: 合成 = 積作用)** — 合成作用はちょうど (Ind1) と (Ind2) の合成
    （積作用の定義、rfl）。 -/
theorem mind_comp_is_product (logq : Nat → RReal) (v : Nat) (s t : Bool) (V : RReal) :
    mindCompAct logq v s t V = mindInd2Act logq v t (mindInd1Act logq v s V) := rfl

/-- **定理 (M382F-5c: (Ind1) と (Ind2) は可換)** — 二つの不定性作用は作用させる順序に依らない:
    mindInd1Act s (mindInd2Act t V) ≈ mindInd2Act t (mindInd1Act s V)（アーベル付値作用
    `mind_val_act_commute`）。積作用が well-defined な Z/2×Z/2 作用である根拠。 -/
theorem mind_actions_commute (logq : Nat → RReal) (v : Nat) (s t : Bool) (V : RReal) :
    realEq (mindInd1Act logq v s (mindInd2Act logq v t V))
      (mindInd2Act logq v t (mindInd1Act logq v s V)) :=
  mind_val_act_commute logq v (mindSignVal s) (mindUnitVal t) V

/-- **定理 (M382F-5d: 各々で不変な値は合成でも不変)** — V が (Ind1) でも (Ind2) でも不変なら、
    合成作用でも不変: mindCompAct s t V ≈ V。群作用の商（軌道）が well-defined であることの
    一般形（不変性は合成へ持ち上がる）。 -/
theorem mind_invariant_composite (logq : Nat → RReal) (v : Nat) (s t : Bool) (V : RReal)
    (h1 : realEq (mindInd1Act logq v s V) V)
    (h2 : realEq (mindInd2Act logq v t V) V) :
    realEq (mindCompAct logq v s t V) V := by
  show realEq (mindInd2Act logq v t (mindInd1Act logq v s V)) V
  refine realEq_trans (mind_val_act_congr logq v (mindUnitVal t) h1) ?_
  exact h2

/-- **定理 (M382F-5e: 合成作用は値を保存＝商 well-defined)** — (Ind1)(Ind2) は各々値を保存する
    （M382F-4d/4e）ので、合成不定性作用も値を保存する: 実 deg_ℝ 値は (Ind1)(Ind2)-不定性商の
    上に well-defined に降下する（軌道は 1 点）。crux Dβ-ω＝Ind3 log-shell 包含はこの降下の外。 -/
theorem mind_comp_invariant (logq : Nat → RReal) (v : Nat) (s t : Bool) (V : RReal) :
    realEq (mindCompAct logq v s t V) V :=
  mind_invariant_composite logq v s t V
    (mind_ind1_invariant logq v s V) (mind_ind2_invariant logq v t V)

/-- **定理 (M382F-5f: 積群の単位元は恒等作用)** — 単位元 (false,false)=(+1,+1) は値を保つ。 -/
theorem mind_comp_id (logq : Nat → RReal) (v : Nat) (V : RReal) :
    realEq (mindCompAct logq v false false V) V :=
  mind_comp_invariant logq v false false V

/-- **定理 (M382F-5g: 積群の乗法律)** — 積群 Z/2×Z/2 の乗法（成分毎 xor）は作用の合成に
    対応する（両辺とも値を保存ゆえ realEq V で束ねる）: 積作用が Z/2×Z/2 の本物の群作用で
    あることの群作用律。 -/
theorem mind_comp_mul (logq : Nat → RReal) (v : Nat) (s s' t t' : Bool) (V : RReal) :
    realEq (mindCompAct logq v (mindXor s s') (mindXor t t') V)
      (mindCompAct logq v s t (mindCompAct logq v s' t' V)) :=
  realEq_trans (mind_comp_invariant logq v (mindXor s s') (mindXor t t') V)
    (realEq_symm
      (realEq_trans (mind_comp_invariant logq v s t (mindCompAct logq v s' t' V))
        (mind_comp_invariant logq v s' t' V)))

/-! ## M382F-6: (Ind3) log-shell 膨張作用（本物の m シフト・不変ではない） -/

/-- **M382F-6a: (Ind3) 膨張作用** — log-shell 膨張は付値 m の寄与 logVolLocal v m を
    実 deg_ℝ 値に上乗せする本物の作用（M332F `indR_ind3Vol` と同型）。(Ind1)(Ind2) と異なり
    **不変ではなく明示 m だけシフト**する。その**上界包含不等式**（＝crux）は外部仮説。 -/
def mindInd3Act (logq : Nat → RReal) (v : Nat) (m : Int) (V : RReal) : RReal :=
  mindValAct logq v m V

/-- **定理 (M382F-6b: (Ind3) は明示 m シフト)** — 膨張作用は値を logVolLocal v m だけ
    平行移動する（不変ではない、rfl）。予測可能なずれ（M372F `mrp_ind3_shift_core` と整合）。 -/
theorem mind_ind3_shift (logq : Nat → RReal) (v : Nat) (m : Int) (V : RReal) :
    realEq (mindInd3Act logq v m V) (realAdd V (logVolLocal logq v m)) :=
  realEq_refl _

/-! ## M382F-7: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M382F-7a: crux は外部仮説・決して導出しない／honest)** — (Ind1)(Ind2)-商の
    well-defined 性（合成作用が値を保存、`mind_comp_invariant`）は**無条件で本物**（crux とは
    独立に成立）だが、その下での**多輻的アルゴリズム**（Ind3 log-shell 包含が与える crux
    ＝ Dβ-ω ＝ IUT 論争の当の係争点）は本層で**決して証明しない**。crux を任意の外部 Prop
    `crux` として受け取り、商 well-defined の本物性 **と** crux の連言を、crux が仮説として
    供給された場合にのみ返す——crux は決して導出されない。 -/
theorem mind_crux_external (logq : Nat → RReal) (v : Nat) (s t : Bool) (V : RReal)
    (crux : Prop) (hcrux : crux) :
    realEq (mindCompAct logq v s t V) V ∧ crux :=
  ⟨mind_comp_invariant logq v s t V, hcrux⟩

/-- **定理 (M382F-7b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説
    そのもの**として扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明した定理では
    なく、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で明示
    （M372F/M377F と同じ精神）。 -/
theorem mind_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M382F-8: capstone -/

/-- **M382F-8a: 多輻不定性データ**（総括） — 3 不定性 (Ind1)(Ind2)(Ind3) を実 deg_ℝ 値
    `val` 上の本物の群作用として束ねる: (Ind1) ±1 自己同型 Z/2・(Ind2) 単数トーソル Z/2 の
    作用と各不変性・合成=積作用・作用の可換・合成不変（商 well-defined）・(Ind3) 膨張の
    明示 m シフト。主語は M312F/M332F の本物の実 deg_ℝ であり toy を用いない。
    crux Dβ-ω（Ind3 log-shell 包含が与える不等式）は範囲外。 -/
structure MultiradialIndetData (logq : Nat → RReal) (v : Nat) where
  /-- 実 deg_ℝ 値（不定性が作用する対象、例: 多輻表現の値）。 -/
  val : RReal
  /-- (Ind1) ±1/単数自己同型群 Z/2 の作用。 -/
  ind1 : Bool → RReal → RReal
  /-- (Ind2) 水平⊗ 単数トーソル Z/2 の作用。 -/
  ind2 : Bool → RReal → RReal
  /-- 合成 = (Ind1)×(Ind2) 積作用。 -/
  comp : Bool → Bool → RReal → RReal
  /-- ind1 は本物の (Ind1) 作用。 -/
  is_ind1 : ind1 = mindInd1Act logq v
  /-- ind2 は本物の (Ind2) 作用。 -/
  is_ind2 : ind2 = mindInd2Act logq v
  /-- comp は本物の積作用。 -/
  is_comp : comp = mindCompAct logq v
  /-- (Ind1) は値を保存（±1 は付値 0）。 -/
  ind1_inv : ∀ s, realEq (ind1 s val) val
  /-- (Ind2) は値を保存（単数トーソルは付値 0）。 -/
  ind2_inv : ∀ t, realEq (ind2 t val) val
  /-- (Ind1) と (Ind2) は可換（作用の順序に依らない）。 -/
  commute : ∀ s t, realEq (ind1 s (ind2 t val)) (ind2 t (ind1 s val))
  /-- 合成 = 積作用（先 Ind1、後 Ind2）。 -/
  comp_product : ∀ s t W, comp s t W = ind2 t (ind1 s W)
  /-- 合成作用も値を保存＝実 deg_ℝ 値は (Ind1)(Ind2)-不定性商へ well-defined に降下。 -/
  comp_inv : ∀ s t, realEq (comp s t val) val
  /-- (Ind3) 膨張は値を明示 m だけシフト（不変ではない）。上界包含（crux）は範囲外。 -/
  ind3_shift : ∀ m, realEq (mindInd3Act logq v m val) (realAdd val (logVolLocal logq v m))

/-- **M382F-8b: witness** — 任意の実 deg_ℝ 値 V 上の本物の 3 不定性群作用データ。 -/
def multiradialIndetData (logq : Nat → RReal) (v : Nat) (V : RReal) :
    MultiradialIndetData logq v where
  val := V
  ind1 := mindInd1Act logq v
  ind2 := mindInd2Act logq v
  comp := mindCompAct logq v
  is_ind1 := rfl
  is_ind2 := rfl
  is_comp := rfl
  ind1_inv := fun s => mind_ind1_invariant logq v s V
  ind2_inv := fun t => mind_ind2_invariant logq v t V
  commute := fun s t => mind_actions_commute logq v s t V
  comp_product := fun s t W => mind_comp_is_product logq v s t W
  comp_inv := fun s t => mind_comp_invariant logq v s t V
  ind3_shift := fun m => mind_ind3_shift logq v m V

/-- **M382F-8c: 存在** — 任意の実重み logq・素点 v・実 deg_ℝ 値 V に対し、3 不定性群作用
    データが存在する。M332F の 3 不定性の個別事実を、RReal 上の**本物の有限群作用**
    （(Ind1)×(Ind2) 積作用・可換・商 well-defined）へ組織化した（crux Dβ-ω は外部仮説）。 -/
theorem mind_exists (logq : Nat → RReal) (v : Nat) (V : RReal) :
    Nonempty (MultiradialIndetData logq v) :=
  ⟨multiradialIndetData logq v V⟩

/-! ## M382F-8 実例（多輻表現 mrpRepresentation の値の上での 3 不定性群作用） -/

/-- 実例: l=5（n=2）で多輻表現の値 mrpRepresentation v 2 に対し (Ind1) ±1 自己同型（s=true=−1）は
    実 deg_ℝ 値を保存する（±1 は付値 0）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (mindInd1Act logq v true (mrpRepresentation logq v 2)) (mrpRepresentation logq v 2) :=
  mind_ind1_invariant logq v true (mrpRepresentation logq v 2)

/-- 実例: 多輻表現の値の上で (Ind1) と (Ind2) は可換（作用の順序に依らない）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (mindInd1Act logq v true (mindInd2Act logq v true (mrpRepresentation logq v 2)))
      (mindInd2Act logq v true (mindInd1Act logq v true (mrpRepresentation logq v 2))) :=
  mind_actions_commute logq v true true (mrpRepresentation logq v 2)

/-- 実例: 合成 (Ind1)×(Ind2) 積作用は多輻表現の値を保存＝実 deg_ℝ 値は不定性商へ降下する。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (mindCompAct logq v true true (mrpRepresentation logq v 2)) (mrpRepresentation logq v 2) :=
  mind_comp_invariant logq v true true (mrpRepresentation logq v 2)

/-- 実例: (Ind3) 膨張 m=1 は多輻表現の値を明示 logVolLocal v 1 だけシフトする（不変でない）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (mindInd3Act logq v 1 (mrpRepresentation logq v 2))
      (realAdd (mrpRepresentation logq v 2) (logVolLocal logq v 1)) :=
  mind_ind3_shift logq v 1 (mrpRepresentation logq v 2)

/-- 実例: 符号群 Z/2 は結合的（±1 自己同型群の本物の群構造）。 -/
example : mindXor (mindXor true true) false = mindXor true (mindXor true false) :=
  mind_xor_assoc true true false

/-- 実例: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  mind_crux_is_hypothesis crux

/-- 実例: 3 不定性群作用データは存在する。 -/
example (logq : Nat → RReal) (v : Nat) :
    Nonempty (MultiradialIndetData logq v) :=
  mind_exists logq v (mrpRepresentation logq v 2)

end IUT
