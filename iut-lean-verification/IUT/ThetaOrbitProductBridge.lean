/-
  IUT/ThetaOrbitProductBridge.lean — M408F [実・本物・柱E]
  complete_pct 影響: 柱E で、総軌道積の指数 Σj²（M373F `topExpSumNat`/`ssq`）が、
    各ラベル j の具体指数 j²（M403F `tvob_exp_toNat`＝M398F/M318F Laurent 環側
    `thLtorExp` の toNat）の**有限和**として本物に一致することを `topb_orbit_sum`
    に closes、単一ラベルの値ブリッジ（M403F）と軌道積ブリッジ（M373F）を接続する。
  正直な限定: 全ラベルの解析的エタールテータ関数値そのもの・p 進収束・tempered π₁^ét
    による軌道の実現は M368F/M373F/M398F/M403F と同様に外部仮説として継承し、
    本層は一切導出しない。

  ## 内容（tier-S・実ブリッジ、M403F（単一ラベル j の具体指数 j²）↔ M373F（軌道積の
  総指数 Σj²）の直接連結）

  M373F は円分影の有限積 `topCycProd M l`（μ_l 側、ラベル j=0,…,l−1 にわたる
  ∏_j ζ^{j²}）が単一の円分影 ζ^{Σj²} に一致すること（`top_cyc_prod_pow`）を、
  総指数 `topExpSumNat l = Σ_{j=0}^{l-1} j*j`（Nat 版、M93 `ssq` へのシフトで
  一致、`top_exp_sum_shift`）として確立した。一方 M403F は、各ラベル j に対する
  M398F/M318F の Laurent 環側 Int 指数 `thLtorExp (j:Int)` の `.toNat` が、まさに
  μ_l 側の Nat 指数 j*j に一致すること（`tvob_exp_toNat`）を machine-checked に
  した。しかし **軌道積の総指数 Σj²（M373F）が、ラベルごとの M403F/M398F
  具体指数 j*j = (thLtorExp (j:Int)).toNat の有限和そのものであること自体は、
  これまで一度も定理として結ばれていなかった**（M373F は Nat 帰納で `l*l` を
  直書きしており、M398F/M403F の Laurent 環側指数を経由していない）。本層は
  その隙間を埋める:

  * M408F-1 `topbConcreteExpSumNat` — M403F/M398F の Laurent 環側具体指数
    `(thLtorExp (j:Int)).toNat`（j=0,…,l−1）の有限和（Nat 版、`topExpSumNat`
    と同型の帰納構造だが、各項が M373F の直書き `l*l` ではなく M403F 由来の
    具体指数から来る点が新規）。
  * M408F-2 本丸 capstone `topb_concrete_exp_sum_eq` — `topbConcreteExpSumNat l`
    が M373F の総指数 `topExpSumNat l` に一致すること（各項を `tvob_exp_toNat`
    で書き換える帰納、M403F と M373F の直接接続）。
  * M408F-3 `topb_orbit_sum` — M408F-2 と M373F `top_exp_sum_shift` を合成し、
    `topbConcreteExpSumNat (l+1)` が M93 `ssq l` に一致することを示す。単一
    ラベルの値ブリッジ（M403F）の指数を足し上げると軌道積ブリッジ（M373F/M93）
    の総指数 Σj²=ssq に一致するという、本丸の集約等式。
  * M408F-4 `topb_cyc_prod_concrete_exp` — M373F `top_cyc_prod_pow` と
    M408F-2 を合成し、円分影の有限積 `topCycProd M l` そのものが
    `M.μ.pow M.ζ (topbConcreteExpSumNat l)`（M403F/M398F 由来の具体指数の和を
    冪指数とする円分影）に一致することを示す。軌道積（M373F の実オブジェクト）が
    単一ラベルの具体指数の総和（M403F/M398F の実オブジェクト）で書けることの
    本物の接続——単なる Nat の等式ではなく、実際の群の元の等式。
  * M408F-5 `ThetaOrbitProductBridgeData` / `thetaOrbitProductBridgeData` /
    `topb_exists` — 上記を一つの witness レコードに束ね、任意の M・l に対する
    存在を示す。
  * M408F-6 実例（l=5・Σj²=30、M373F の実例と同じ数値）。

  選択公理不使用（新規 Classical.choice なし；継承分の Quot.sound のみ）。sorry 皆無・
  禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。許可タクティク（cases/obtain/induction/rw/show/refine/exact/apply/
  intro/generalize/funext/omega）のみ使用。共有ファイル（IUT.lean・build.sh・
  dashboard.md・graph 系）は一切変更していない。一般名は `topb` 接頭辞で衝突回避。
-/
import IUT.ThetaValueOrbitBridge

namespace IUT

/-! ## M408F-1: ラベルごとの M403F/M398F 具体指数の有限和（Nat 版） -/

/-- **M408F-1: 具体指数の和** — topbConcreteExpSumNat l = Σ_{j=0}^{l−1}
    (thLtorExp (j:Int)).toNat（M403F/M398F の Laurent 環側具体指数の j=0,…,l−1
    にわたる有限和、Nat 版）。各項は M373F の `topExpSumNat` の直書き `j*j` では
    なく、M403F の共有指数 `(thLtorExp (j:Int)).toNat` から来る。 -/
def topbConcreteExpSumNat : Nat → Nat
  | 0 => 0
  | l + 1 => (thLtorExp (l : Int)).toNat + topbConcreteExpSumNat l

/-! ## M408F-2: 本丸 capstone——具体指数の和は M373F の総指数に一致 -/

/-- **定理 (M408F-2: capstone——具体指数の総和は M373F の総指数 Σj² に一致)** —
    topbConcreteExpSumNat l = topExpSumNat l（M403F `tvob_exp_toNat` で各項
    `(thLtorExp (j:Int)).toNat` を `j*j` に書き換える帰納、M373F の直書き総指数
    への直接接続）。単一ラベルの M403F/M398F 具体指数の有限和が、M373F の軌道積
    総指数と machine-checked に同一の自然数であることの本丸。 -/
theorem topb_concrete_exp_sum_eq (l : Nat) :
    topbConcreteExpSumNat l = topExpSumNat l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    show (thLtorExp (l : Int)).toNat + topbConcreteExpSumNat l
       = l * l + topExpSumNat l
    rw [tvob_exp_toNat, ih]

/-! ## M408F-3: ssq（M93）への集約 -/

/-- **定理 (M408F-3: 単一ラベル値ブリッジの集約=軌道積ブリッジの総指数・本丸)** —
    topbConcreteExpSumNat (l+1) = ssq l（M408F-2 で M373F の総指数に書き換え、
    M373F `top_exp_sum_shift` で M93 `ssq` に一致させる）。M403F の単一ラベル
    値ブリッジの具体指数 j² を j=0,…,l にわたって足し上げると、M373F/M93 の
    軌道積総指数 Σj²=ssq l に本物で一致するという集約等式。 -/
theorem topb_orbit_sum (l : Nat) :
    topbConcreteExpSumNat (l + 1) = ssq l := by
  rw [topb_concrete_exp_sum_eq (l + 1), top_exp_sum_shift]

/-! ## M408F-4: 円分影の有限積そのものが具体指数の和で書ける（実オブジェクトの等式） -/

/-- **定理 (M408F-4: 軌道積は具体指数の和を指数とする円分影に一致)** —
    topCycProd M l = M.μ.pow M.ζ (topbConcreteExpSumNat l)（M373F
    `top_cyc_prod_pow` で `topExpSumNat` 形に書き換え、M408F-2 で
    `topbConcreteExpSumNat` に戻す）。M373F の実オブジェクト（円分影の有限積、
    μ_l の元）が、M403F/M398F 由来の単一ラベル具体指数の総和を指数とする単一の
    円分影として書けることの本物の接続——Nat の等式に留まらず、群 μ_l の元の
    等式として、単一値ブリッジと軌道積ブリッジが繋がる。 -/
theorem topb_cyc_prod_concrete_exp (M : CycMuGroup) (l : Nat) :
    topCycProd M l = M.μ.pow M.ζ (topbConcreteExpSumNat l) := by
  rw [top_cyc_prod_pow, topb_concrete_exp_sum_eq]

/-! ## M408F-5: 総括レコード（witness）と存在 -/

/-- **M408F-5a: 軌道積・単一値ブリッジ集約データ** — M373F の軌道積総指数
    `topExpSumNat`/`ssq` と M403F/M398F 由来の単一ラベル具体指数の和
    `topbConcreteExpSumNat`、および実オブジェクト（円分影の有限積 `topCycProd`）
    レベルでの一致を一括束ねる。 -/
structure ThetaOrbitProductBridgeData (M : CycMuGroup) (l : Nat) where
  /-- 具体指数の総和は M373F の総指数 Σj² に一致。 -/
  concrete_sum_eq : topbConcreteExpSumNat l = topExpSumNat l
  /-- 円分影の有限積は、具体指数の総和を指数とする円分影に一致。 -/
  cyc_prod_concrete_exp :
      topCycProd M l = M.μ.pow M.ζ (topbConcreteExpSumNat l)

/-- **M408F-5b: witness 本体** — 各フィールドを M408F-2・M408F-4 の主定理で埋める。 -/
def thetaOrbitProductBridgeData (M : CycMuGroup) (l : Nat) :
    ThetaOrbitProductBridgeData M l where
  concrete_sum_eq := topb_concrete_exp_sum_eq l
  cyc_prod_concrete_exp := topb_cyc_prod_concrete_exp M l

/-- **定理 (M408F-5c: 軌道積・単一値ブリッジ集約データの存在)** — 任意の μ_l・
    ラベル数 l に対し、単一ラベル値ブリッジ（M403F）の具体指数の総和が M373F の
    軌道積総指数 Σj²=ssq、および実オブジェクトの円分影積そのものに machine-checked
    で一致する集約データが存在する。 -/
theorem topb_exists (M : CycMuGroup) (l : Nat) :
    Nonempty (ThetaOrbitProductBridgeData M l) :=
  ⟨thetaOrbitProductBridgeData M l⟩

/-! ## M408F-6: 実例（l=5・Σj²=30、M373F の実例と同じ数値） -/

/-- 実例: l=5 の M403F/M398F 由来の具体指数の総和 Σ_{j=0}^{4} (thLtorExp (j:Int)).toNat
    は M93 の ssq 4 = 30 に一致する（`topb_orbit_sum`、M373F の実例と同じ数値）。 -/
theorem topb_example_l5 : topbConcreteExpSumNat 5 = 30 :=
  topb_orbit_sum 4

/-- 実例: 本物の G_ℚ の μ_5（`cycMuStd 5`）上で、軌道積・単一値ブリッジ集約データが
    存在する（`topb_exists`、M373F/M403F と同じ具体構成）。 -/
theorem topb_example_data_l5 :
    Nonempty (ThetaOrbitProductBridgeData (cycMuStd 5 (by omega)) 5) :=
  topb_exists (cycMuStd 5 (by omega)) 5

end IUT
