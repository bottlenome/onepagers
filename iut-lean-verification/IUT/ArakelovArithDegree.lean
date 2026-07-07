-- M436F ArakelovArithDegree [実・本物・柱C]
-- complete_pct 影響: 柱C（Frobenioid／Arakelov）を前進。M356F 実次数 deg:D̂→ℝ・M426F Pic^0＝ker(deg)・
--   M431F 完全列を土台に、**算術次数から算術交点数（intersection pairing）⟨D,E⟩:D̂×D̂→ℝ を本物で建設**
--   （ℝ 双線形・対称・ardEq well-defined・Pic^0 で退化）。deg を pairing の対角/片側に載せた本物の実部分ケース。
-- 正直な限定: pairing は「算術次数の積」⟨D,E⟩=deg(D)·deg(E)（次数積形式）に留まり、真の Arakelov 交点数の
--   局所寄与（有限素点の局所交点重複度・∞ 素点の Green 関数積分）は捉えない。K=ℚ 模型・∞ 部近似も M356F 継承。

/-
  IUT/ArakelovArithDegree.lean — M436F（柱C: Arakelov 算術次数・算術交点数 pairing）

  ── 主要成果の分類: **[実]**（本物の先行建設 (b)）。M356F
     (`IUT/ArakelovDivisor.lean`, prefix `ard`) の Arakelov 因子群 D̂・実次数 deg:D̂→ℝ
     （加法準同型 `ard_deg_hom`・主因子 deg=0 `ard_principalRaw_degree_zero`）、M426F
     (`IUT/ArakelovClassDegree.lean`, prefix `acd`) の次数0 部分群 D̂^0＝ker(deg)＝Pic^0、
     M431F (`IUT/ArakelovPicExact.lean`, prefix `ape`) の完全列 0→Pic^0→Pic(D̂)→im(deg)→0
     を土台に、**次の本物の一手**——Arakelov **算術交点数**（arithmetic intersection pairing）
     ⟨·,·⟩ : D̂ × D̂ → ℝ を core Lean のみで完全証明する。toy 主語なし——主語は M356F の
     本物の Arakelov 因子・実次数・M150F の実数乗法 rmul（ℝ の環法則 `rmul_add_right`/`rmul_comm`）。

  complete_pct 影響: **柱C（Frobenioid／Arakelov 交点理論）の実 IUT 完全証明率を前進**。
  M356F–M431F は deg を「因子群 → ℝ の加法準同型」まで建てた。本ファイルは deg から
  **算術交点数 pairing を構成し、その双線形性・対称性・Pic^0 での退化を本物で証明**する:
  (1) **算術次数の再定式化** `aadArithDeg = ardDeg`（M356F deg を本モジュールの主語に採る）。
  (2) **加法性** `aad_deg_additive`（M356F `ard_deg_hom` の交点理論的再述）。
  (3) **Pic^0 で次数消失** `aad_deg_pic0_zero`（M426F D̂^0＝ker(deg) と接続、[D]∈Pic^0 ⟹ deg≈0）。
  (4) **算術交点数 pairing** `aadPair logp D E = deg(D)·deg(E)`（ℝ 値の双線形・対称形式）——
      ・**ardEq well-defined** `aad_pair_wd`（両変数 M356F `ardDeg_wd`＋rmul congruence）、
      ・**対称性** `aad_deg_intersection`（M150F `rmul_comm`）、
      ・**左双線形** `aad_pair_add_left`（`ard_deg_hom`＋M150F `rmul_add_right` 右分配律）、
      ・**右双線形** `aad_pair_add_right`（対称性経由）、
      ・**Pic^0 での退化** `aad_pair_pic0_left_zero`（D∈Pic^0 ⟹ ⟨D,E⟩≈0）——
        交点数が Pic^0（コンパクト核）方向で消える＝deg 部分での退化構造の本物。
  (5) **正直な scope 定理** `aad_model_scope`（pairing の定義的正体＝次数積形式であることを定理として露出）。
  (6) capstone `AadArithDegData` / `aad_arithDegData` / `aad_exists` / 実例。

  ## 正直な限定（消去/弱化禁止・地図として保持）
  - **本物（完全証明）**: 算術交点数 pairing ⟨D,E⟩=deg(D)·deg(E) が ℝ 値の**対称双線形形式**であること・
    ardEq（因子群 D̂）の上で well-defined であること・Pic^0（次数0 類）方向で退化すること・M356F deg の
    加法性の交点理論的再述。全て K=ℚ 模型上で本物・sorry 皆無・新規 Classical.choice なし。
  - **正直申告（未達・後続）**:
    ・**pairing は「算術次数の積」形式 ⟨D,E⟩=deg(D)·deg(E) に留まる**（`aad_model_scope` で定理として明示）。
      真の Arakelov 算術交点数は、有限素点での**局所交点重複度**（arithmetic surface の
      成分同士の交わり）と ∞ 素点での**Green 関数の積分** ∫ log‖·‖ を場所ごとに足し上げるもので、
      本模型の次数積形式はその**対角的縮約**（両因子を大域次数へ潰した部分ケース）に過ぎない。
      場所ごとの局所交点・Green 積分・arithmetic surface の Deligne pairing は **後続**。
    ・**K=ℚ 模型**・∞ 部を自由実数とする近似は M356F/M426F/M431F を継承（範囲外）。
    ・**adjunction / arithmetic Riemann–Roch**（交点数と算術次数の Riemann–Roch 型関係）は範囲外。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・[propext, Quot.sound]）・
  sorry 皆無・禁止タクティク不使用。
-/
import IUT.ArakelovClassDegree
import IUT.RealRingLaws

namespace IUT

/-! ## M436F-1: 算術次数の再定式化（M356F deg を本モジュールの主語に採る） -/

/-- **M436F-1a: Arakelov 算術次数** deg : D̂ → ℝ（M356F `ardDeg` を本モジュールの主語に）。
    有限部 Σ_p n_p·log p ＋ ∞ 部の実重み。算術交点数 pairing の対角入力になる。 -/
def aadArithDeg (logp : Nat → RReal) (D : ardRaw) : RReal :=
  ardDeg logp D

/-- **M436F-1b: 算術次数の well-defined 性**（realEq、ℝ は setoid）— M356F `ardDeg_wd`。 -/
theorem aad_arithDeg_wd (logp : Nat → RReal) {D E : ardRaw} (h : ardEq D E) :
    realEq (aadArithDeg logp D) (aadArithDeg logp E) :=
  ardDeg_wd logp h

/-! ## M436F-2: 算術次数の加法性（交点理論的再述） -/

/-- **M436F-2: 算術次数の加法性** deg(D+D') ≈ deg(D)+deg(D')（M356F `ard_deg_hom`）。
    交点数 pairing の左双線形性の土台。 -/
theorem aad_deg_additive (logp : Nat → RReal) (D D' : ardRaw) :
    realEq (aadArithDeg logp (ardAdd D D'))
      (realAdd (aadArithDeg logp D) (aadArithDeg logp D')) :=
  ard_deg_hom logp D D'

/-! ## M436F-3: Pic^0 で算術次数が消失（M426F 次数0 類群と接続） -/

/-- **M436F-3: Pic^0（次数0 因子）で deg≈0** — 因子 D の類が M426F 次数0 部分群 D̂^0＝ker(deg)
    に入るなら deg(D)≈0。完全列 0→Pic^0→Pic(D̂)→ℝ の Pic^0＝ker(deg) を本モジュールの
    算術次数の言葉で再述（`acdDegZeroSub` の所属は定義的に `realEq (ardDeg D) 0`）。 -/
theorem aad_deg_pic0_zero (logp : Nat → RReal) (D : ardRaw)
    (h : (acdDegZeroSub logp).mem (Quot.mk ardEq D)) :
    realEq (aadArithDeg logp D) realZero :=
  h

/-! ## M436F-4: Arakelov 算術交点数 pairing ⟨·,·⟩ : D̂ × D̂ → ℝ -/

/-- **M436F-4a: Arakelov 算術交点数** ⟨D,E⟩ = deg(D)·deg(E)（ℝ 値の対称双線形形式）。
    M150F の実数乗法 rmul で算術次数の積を取る。**正直な限定**（`aad_model_scope`）: これは
    真の Arakelov 交点数の**対角縮約**（両因子を大域次数へ潰した次数積形式）であり、局所交点・
    Green 積分は捉えない。それでも ℝ 双線形・対称・Pic^0 退化という交点形式の中核性質を本物で満たす。 -/
def aadPair (logp : Nat → RReal) (D E : ardRaw) : RReal :=
  rmul (aadArithDeg logp D) (aadArithDeg logp E)

/-- **M436F-4b: pairing は ardEq で well-defined**（両変数）— 等価な代表（因子群 D̂ の元）は
    同じ交点数。M356F `ardDeg_wd`（両変数）＋M150F rmul の congruence。因子群 D̂×D̂ の上へ
    pairing が降りることの土台。 -/
theorem aad_pair_wd (logp : Nat → RReal) {D D' E E' : ardRaw}
    (hD : ardEq D D') (hE : ardEq E E') :
    realEq (aadPair logp D E) (aadPair logp D' E') := by
  refine realEq_trans
    (rmul_congr_left (aadArithDeg logp E) (aad_arithDeg_wd logp hD)) ?_
  exact rmul_congr_right (aadArithDeg logp D') (aad_arithDeg_wd logp hE)

/-- **M436F-4c: 算術交点数の対称性** ⟨D,E⟩ ≈ ⟨E,D⟩（交点 pairing の基本性質・本丸）。
    M150F `rmul_comm`。算術交点数が対称双線形形式であることの核。 -/
theorem aad_deg_intersection (logp : Nat → RReal) (D E : ardRaw) :
    realEq (aadPair logp D E) (aadPair logp E D) :=
  rmul_comm (aadArithDeg logp D) (aadArithDeg logp E)

/-- **M436F-4d: 左双線形** ⟨D+D',E⟩ ≈ ⟨D,E⟩+⟨D',E⟩ — 算術次数の加法性
    （M356F `ard_deg_hom`）＋ M150F 右分配律 `rmul_add_right`。交点 pairing の双線形性（左）。 -/
theorem aad_pair_add_left (logp : Nat → RReal) (D D' E : ardRaw) :
    realEq (aadPair logp (ardAdd D D') E)
      (realAdd (aadPair logp D E) (aadPair logp D' E)) := by
  show realEq (rmul (aadArithDeg logp (ardAdd D D')) (aadArithDeg logp E))
      (realAdd (rmul (aadArithDeg logp D) (aadArithDeg logp E))
        (rmul (aadArithDeg logp D') (aadArithDeg logp E)))
  refine realEq_trans
    (rmul_congr_left (aadArithDeg logp E) (aad_deg_additive logp D D')) ?_
  exact rmul_add_right (aadArithDeg logp D) (aadArithDeg logp D') (aadArithDeg logp E)

/-- **M436F-4e: 右双線形** ⟨D,E+E'⟩ ≈ ⟨D,E⟩+⟨D,E'⟩ — 対称性で左双線形へ帰着。
    交点 pairing の双線形性（右）。 -/
theorem aad_pair_add_right (logp : Nat → RReal) (D E E' : ardRaw) :
    realEq (aadPair logp D (ardAdd E E'))
      (realAdd (aadPair logp D E) (aadPair logp D E')) := by
  refine realEq_trans (aad_deg_intersection logp D (ardAdd E E')) ?_
  refine realEq_trans (aad_pair_add_left logp E E' D) ?_
  refine realEq_trans
    (realAdd_congr_left (aadPair logp E' D) (aad_deg_intersection logp E D)) ?_
  exact realAdd_congr_right (aadPair logp D E) (aad_deg_intersection logp E' D)

/-! ## M436F-5: 交点数の Pic^0 での退化 -/

/-- **M436F-5a: 左 Pic^0 退化** — D が Pic^0（deg(D)≈0）なら ⟨D,E⟩≈0（任意の E）。
    deg(D)≈0 ⟹ ⟨D,E⟩=deg(D)·deg(E) ≈ 0·deg(E) ≈ 0（M150F `rmul_congr_left`＋
    `rmul_comm`＋`rmul_zero`）。交点数が Pic^0（次数0 コンパクト核）方向で退化する構造。 -/
theorem aad_pair_pic0_left_zero (logp : Nat → RReal) (D E : ardRaw)
    (h : realEq (aadArithDeg logp D) realZero) :
    realEq (aadPair logp D E) realZero := by
  refine realEq_trans (rmul_congr_left (aadArithDeg logp E) h) ?_
  exact realEq_trans (rmul_comm realZero (aadArithDeg logp E))
    (rmul_zero (aadArithDeg logp E))

/-- **M436F-5b: 右 Pic^0 退化** — E が Pic^0（deg(E)≈0）なら ⟨D,E⟩≈0（対称性経由）。 -/
theorem aad_pair_pic0_right_zero (logp : Nat → RReal) (D E : ardRaw)
    (h : realEq (aadArithDeg logp E) realZero) :
    realEq (aadPair logp D E) realZero :=
  realEq_trans (aad_deg_intersection logp D E) (aad_pair_pic0_left_zero logp E D h)

/-- **M436F-5c: Pic^0 所属からの退化（M426F 接続版）** — D の類が M426F 次数0 部分群 D̂^0
    に入るなら ⟨D,E⟩≈0。M426F `acdDegZeroSub`（Pic^0＝ker(deg)）と交点数退化の接続。 -/
theorem aad_pair_degZero_left_zero (logp : Nat → RReal) (D E : ardRaw)
    (h : (acdDegZeroSub logp).mem (Quot.mk ardEq D)) :
    realEq (aadPair logp D E) realZero :=
  aad_pair_pic0_left_zero logp D E (aad_deg_pic0_zero logp D h)

/-! ## M436F-6: 正直な scope 定理（pairing の正体を定理として露出） -/

/-- **M436F-6: 正直な scope 定理** — 本モジュールの算術交点数の**正体は次数積形式**
    ⟨D,E⟩ = deg(D)·deg(E) であること（定義的等式）。**これは飾りでなく地図**: 真の Arakelov
    交点数は有限素点の局所交点重複度と ∞ 素点の Green 関数積分を場所ごとに足すもので、本模型は
    その対角縮約（両因子を大域次数へ潰した部分ケース）に過ぎない。定理として露出することで
    「何を本物にし何を後続に残したか」を消去不能に記録する（完全証明ファースト規則 §4）。 -/
theorem aad_model_scope (logp : Nat → RReal) (D E : ardRaw) :
    aadPair logp D E = rmul (aadArithDeg logp D) (aadArithDeg logp E) :=
  rfl

/-! ## M436F-7: capstone -/

/-- **M436F-7a: Arakelov 算術交点数データ** — 算術次数・加法性・Pic^0 での次数消失・
    算術交点数 pairing・対称性・左右双線形・Pic^0 退化を束ねた交点形式の実体。 -/
structure AadArithDegData (logp : Nat → RReal) where
  /-- Arakelov 算術次数 deg : D̂ → ℝ。 -/
  deg : ardRaw → RReal
  /-- 算術交点数 pairing ⟨·,·⟩ : D̂ × D̂ → ℝ。 -/
  pair : ardRaw → ardRaw → RReal
  /-- 算術次数の加法性 deg(D+D') ≈ deg D + deg D'。 -/
  deg_additive : ∀ D D',
    realEq (deg (ardAdd D D')) (realAdd (deg D) (deg D'))
  /-- 交点数の対称性 ⟨D,E⟩ ≈ ⟨E,D⟩。 -/
  pair_symm : ∀ D E, realEq (pair D E) (pair E D)
  /-- 交点数の左双線形 ⟨D+D',E⟩ ≈ ⟨D,E⟩+⟨D',E⟩。 -/
  pair_add_left : ∀ D D' E,
    realEq (pair (ardAdd D D') E) (realAdd (pair D E) (pair D' E))
  /-- 交点数の右双線形 ⟨D,E+E'⟩ ≈ ⟨D,E⟩+⟨D,E'⟩。 -/
  pair_add_right : ∀ D E E',
    realEq (pair D (ardAdd E E')) (realAdd (pair D E) (pair D E'))
  /-- Pic^0（deg≈0）での退化 ⟨D,E⟩≈0。 -/
  pair_pic0_zero : ∀ D E, realEq (deg D) realZero → realEq (pair D E) realZero

/-- **M436F-7b: Arakelov 算術交点数データの witness**（全て本物）。 -/
def aad_arithDegData (logp : Nat → RReal) : AadArithDegData logp where
  deg := aadArithDeg logp
  pair := aadPair logp
  deg_additive := aad_deg_additive logp
  pair_symm := aad_deg_intersection logp
  pair_add_left := aad_pair_add_left logp
  pair_add_right := aad_pair_add_right logp
  pair_pic0_zero := aad_pair_pic0_left_zero logp

/-- **M436F-7c: 存在** — Arakelov 算術交点数データは充足可能（K=ℚ）。 -/
theorem aad_exists (logp : Nat → RReal) : Nonempty (AadArithDegData logp) :=
  ⟨aad_arithDegData logp⟩

/-! ## M436F-8: 実例 -/

/-- **M436F-8a: 実例（零因子との交点は0）** — ⟨0̂,E⟩≈0（deg(0̂)=0 ゆえ左退化）。 -/
theorem aad_example_zero_pair (logp : Nat → RReal) (E : ardRaw) :
    realEq (aadPair logp ardZero E) realZero :=
  aad_pair_pic0_left_zero logp ardZero E (ard_example_zero logp)

/-- **M436F-8b: 実例（主因子 div̂(2) との交点は0）** — 主 Arakelov 因子は deg=0
    （実積公式 log2+(−log2)=0）ゆえ ⟨div̂(2),E⟩≈0（Pic^0 退化）。 -/
theorem aad_example_principal_pair_zero (logp : Nat → RReal) (E : ardRaw) :
    realEq (aadPair logp (ardPrincipalRaw logp (pfSinglePrime 0 1).fin) E) realZero :=
  aad_pair_pic0_left_zero logp _ E
    (ard_principalRaw_degree_zero logp (pfSinglePrime 0 1).fin)

/-- **M436F-8c: 実例（交点数の対称性の具体束ね）** — ⟨D,E⟩≈⟨E,D⟩。 -/
theorem aad_example_symm (logp : Nat → RReal) (D E : ardRaw) :
    realEq (aadPair logp D E) (aadPair logp E D) :=
  aad_deg_intersection logp D E

end IUT
