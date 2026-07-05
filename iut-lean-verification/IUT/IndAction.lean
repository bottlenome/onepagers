/-
  IUT/IndAction.lean — M241F（Dβ-5: 不定性の作用 IndAction）

  D-β 詳細化ラウンド（軸1 = 模型忠実化）の第三資産。M238F
  `IUT/ArithPilot.lean` の前表現 `arithPreRep` は、像・q-領域を実 Frobenioid
  因子（`gaussDiv`・`qPilotDiv`・`degZ`）で据えたが、**不定性は最小限**
  （`Ind = Unit`・`image` は定数 `gaussDiv l`）に留まっていた——不定性が
  領域 `QDiv` に**実際には作用していない**。本モジュールはこの `Ind = Unit`
  を、不定性が QDiv 領域へ**実際に作用**して `image` に**非定数の軌道**を
  与える構造 `IndAction` に格上げする。

  ## 核心（何を honest に実装したか）

  * `IndAction w l`（構造）: 不定性の作用データ。軌道 index `Ix`・基点
    `base`・**非定数になり得る** `image : Ix → QDiv`・軌道の上界包 `hull`
    と、作用が**次数 degZ を保つ**ことの証明 `deg_image`/`deg_hull` を持つ。
  * `unitIndAction`（(Ind2) の実装）: M55F `unitEndo`（split Frobenioid の
    単数自己射＝次数不変の U-トーソル、`IUT/SplitFrobenioid.lean`）の作用を
    QDiv 上に実現する。単数不定性は「エタール方向（重み 0 の座標 k₀）」の
    重複度を動かす——これは degZ に**寄与しない**方向なので、像は動く
    （軌道は非定数）が**大域次数は不変**である。M55F の
    「因子部分は剛的・単数成分だけがトーソル」＝「単数は degZ を保つ」の
    算術模型上の実体化。
  * `unitIndAction_orbit`: `image` が**定数でない**初の表現
    （`image true ≠ image false`）。多輻性＝軌道共変性の芽。
  * `unit_indeterminacy_acts`: (Ind2) 単数トーソルの非自明性（M55F の
    `unitIso` が生む非自明な同型対）と、その作用のもとで Θ-像の軌道が
    非定数かつ**次数不変**であることを一つに束ねた capstone。
  * `arithPreRepInd`: `arithPreRep`（M238F）の `Ind = Unit` を `IndAction`
    に差し替えた**一般化前表現**。任意の作用データ `A : IndAction` を受け取り、
    `q_realized` だけを外部仮説 hq に外部化した
    `MultiradialRep (arithVol w B) (arithSkeleton w n l B …)` を構成する。
    `image` は `A.image`（非定数可）、`hullTheta` は `A.hull`（次数 = wssq）。
  * `arith_rep_of_unit_orbit` / `arith_transport_of_unit_orbit`:
    unit 軌道を差し込んだ具体前表現と、crux ⟹ Cor312。

  ## 正直な限定（どこまで作用させたか・D-β 本丸ではない）

  * **作用させたのは (Ind2)（単数 = `unitEndo`）のみ**。(Ind1)
    `deloopInd`（procession のラベル置換＝因子 mult の置換）と (Ind3)
    `UpperCompat`（上方包含による領域膨張）を QDiv に**同時作用**させる
    完全版は**次段**である。本モジュールの `IndAction` は一般の作用データを
    受け取れる器であり、Ind1/Ind3 を後から差し込める設計だが、居住する
    具体 witness は Ind2 のみ。
  * **単数作用の非定数性は「重み 0 のエタール座標 k₀」に宿らせた**。
    実 log-重み（正の素点重み）を持つ座標では、単数作用が degZ を保つには
    等重み座標の置換（Ind1 = ラベル置換）が要る——それは次段。ここでの
    k₀（`hw0 : w k₀ = 0`）は「単数方向は大域次数に効かない」という M55F の
    圏論的事実の**算術的影**であり、原論文の log-shell 上の単数積分
    （Ism のコピーの解析的作用）の内容は写像しない。
  * **crux `q_realized` は依然として外部仮説 hq**（M238F と同じ）。crux の
    単一 Prop 化 `ThetaLinkTransport`（Dβ-6）・鏡像定理
    `transport_iff_cor312`（Dβ-7）・実データでの証明（Dβ-ω）は本モジュール
    では**一切構成しない**。ここで示したのは「不定性が像を動かす軌道を
    実際に持ち、その軌道が次数不変である」ことまでである。
  * 軌道は**二点**（基点 + 単数 1 個ぶんのずらし）に留める。`IndAction.hull`
    の次数を wssq に固定するため、軌道の膨張を有界に保つ設計判断であり、
    無限トーソル全体の像を同時に据えることは（hull の次数有界性のため）
    行わない。
-/
import IUT.ArithPilot
import IUT.Indeterminacies

namespace IUT

/-! ## Part 1: 単一素点因子の ℤ 次数（Dβ-4 の degN_single の ℤ 化） -/

/-- 単一素点因子の ℤ 次数 = 重み × 重複度（`degN_single` の ℤ 化）。
    「単数方向 k₀（重み 0）は次数に寄与しない」を式で効かせる供給源。 -/
theorem degZ_single (w : Nat → Nat) (k m : Nat) :
    degZ w (singleDiv k m) = ((w k * m : Nat) : Int) := by
  show ((degN w (singleDiv k m) : Nat) : Int) = ((w k * m : Nat) : Int)
  rw [degN_single]

/-! ## Part 2: 不定性の作用 IndAction -/

/-- **不定性の作用データ（Dβ-5 の本構造）**: 不定性が Θ-像の領域 `QDiv`
    へ実際に作用して像に**軌道**を与える構造。

    * `Ix` — 作用の軌道 index（(Ind2) では単数トーソル由来の 2 点集合）。
    * `base` — 基点（恒等作用 = 「不定性を選ばない」選択肢）。
    * `image` — 不定性 i の作用のもとでの Θ-像。**定数でなくてよい**
      （`unitIndAction_orbit` で真に非定数な witness を与える）。
    * `hull` — 軌道全体の上界包（系3.12 で −|log Θ| を測る対象）。
    * `image_le_hull` — 各像は hull に点毎包含される。
    * `deg_image` — **作用は大域次数 degZ を保つ**（(Ind2) の次数不変性）。
      像は動くが `degZ` は基点像 `gaussDiv l` と等しい。
    * `deg_hull` — hull も次数 = `degZ (gaussDiv l)`（膨張が次数を増やさない
      = 軌道が等次数葉上に載る）。 -/
structure IndAction (w : Nat → Nat) (l : Nat) where
  /-- 作用の軌道 index。 -/
  Ix : Type
  /-- 基点（恒等作用）。 -/
  base : Ix
  /-- 不定性 i のもとでの Θ-像（非定数可）。 -/
  image : Ix → QDiv
  /-- 軌道の上界包。 -/
  hull : QDiv
  /-- 各像は hull に点毎包含。 -/
  image_le_hull : ∀ i, ∀ k, (image i).mult k ≤ hull.mult k
  /-- 作用は大域次数を保つ（(Ind2) 次数不変）。 -/
  deg_image : ∀ i, degZ w (image i) = degZ w (gaussDiv l)
  /-- 上界包も等次数（膨張は次数を増やさない）。 -/
  deg_hull : degZ w hull = degZ w (gaussDiv l)

/-! ## Part 3: (Ind2) 単数作用の QDiv 上の実装 -/

/-- 単数軌道の Θ-像: 基点は素の `gaussDiv l`、単数 1 個ぶんずらすと
    「エタール方向 k₀」の重複度を +1 する。k₀ が重み 0 なら degZ は不変。 -/
def unitOrbitImg (l k₀ : Nat) : Bool → QDiv
  | false => gaussDiv l
  | true  => qadd (gaussDiv l) (singleDiv k₀ 1)

/-- 単数軌道の上界包（+1 ずらした側 = 二点の点毎 max）。 -/
def unitOrbitHull (l k₀ : Nat) : QDiv := qadd (gaussDiv l) (singleDiv k₀ 1)

/-- 重み 0 のエタール座標 k₀ を +1 しても大域次数は不変
    （`degZ_add` + `degZ_single` + `hw0`）。 -/
theorem unitOrbit_deg (w : Nat → Nat) (l k₀ : Nat) (hw0 : w k₀ = 0) :
    degZ w (qadd (gaussDiv l) (singleDiv k₀ 1)) = degZ w (gaussDiv l) := by
  rw [degZ_add, degZ_single, hw0]
  show degZ w (gaussDiv l) + ((0 * 1 : Nat) : Int) = degZ w (gaussDiv l)
  omega

/-- **(Ind2) の作用実装**: split Frobenioid の単数自己射（`unitEndo`、
    M55F）の作用を QDiv 上に実現した `IndAction`。単数不定性は重み 0 の
    エタール座標 k₀ の重複度を動かす——像は非定数だが degZ は不変。
    M55F の「単数成分だけがトーソル・因子次数は剛的」の算術模型化。 -/
def unitIndAction (w : Nat → Nat) (l k₀ : Nat) (hw0 : w k₀ = 0) :
    IndAction w l where
  Ix := Bool
  base := false
  image := unitOrbitImg l k₀
  hull := unitOrbitHull l k₀
  image_le_hull := fun b k => by
    cases b with
    | false =>
      show (gaussDiv l).mult k ≤ (gaussDiv l).mult k + (singleDiv k₀ 1).mult k
      exact Nat.le_add_right _ _
    | true => exact Nat.le_refl _
  deg_image := fun b => by
    cases b with
    | false => rfl
    | true => exact unitOrbit_deg w l k₀ hw0
  deg_hull := unitOrbit_deg w l k₀ hw0

/-- **像は定数でない（軌道共変性の芽）**: 単数作用の二像は k₀ の重複度で
    真に食い違う。`arithPreRep`（M238F）の定数像 `fun _ => gaussDiv l` を
    脱し、不定性が像を実際に動かす初の表現。 -/
theorem unitIndAction_orbit (w : Nat → Nat) (l k₀ : Nat) (hw0 : w k₀ = 0) :
    (unitIndAction w l k₀ hw0).image true
      ≠ (unitIndAction w l k₀ hw0).image false := by
  intro h
  have hk : (gaussDiv l).mult k₀ + (singleDiv k₀ 1).mult k₀ = (gaussDiv l).mult k₀ :=
    congrArg (fun d => d.mult k₀) h
  have h1 : (singleDiv k₀ 1).mult k₀ = 1 := by
    show (if k₀ = k₀ then 1 else 0) = 1
    rw [if_pos rfl]
  rw [h1] at hk
  omega

/-! ## Part 4: (Ind2) トーソルとの接続と capstone -/

/-- **capstone (M241F-a): 単数不定性が QDiv に作用する** —
    (1) (Ind2) 単数トーソル（M55F `unitIso`）は非自明: 単数 1 と単数 0 の
        自己同型は相異なる、
    (2) その作用のもとで Θ-像の軌道は**非定数**（`image true ≠ image false`）、
    (3) しかし作用は**大域次数を保つ**（degZ が両像で一致）。
    「不定性 (Ind2) が像を動かす軌道を実際に持ち、その軌道が次数不変で
    ある」ことの機械検証。M238F の `Ind = Unit`・定数像からの格上げ。 -/
theorem unit_indeterminacy_acts (w : Nat → Nat) (l k₀ : Nat) (hw0 : w k₀ = 0) :
    (unitIso intGrp intComm qzero (1 : Int)
        ≠ unitIso intGrp intComm qzero intGrp.one)
      ∧ ((unitIndAction w l k₀ hw0).image true
          ≠ (unitIndAction w l k₀ hw0).image false)
      ∧ (degZ w ((unitIndAction w l k₀ hw0).image true)
          = degZ w ((unitIndAction w l k₀ hw0).image false)) := by
  refine ⟨?_, unitIndAction_orbit w l k₀ hw0, ?_⟩
  · intro heq
    have h1 : (1 : Int) = intGrp.one :=
      congrArg (fun i => splitIsoToUnit intGrp intComm i) heq
    have h2 : (1 : Int) = 0 := h1
    omega
  · exact ((unitIndAction w l k₀ hw0).deg_image true).trans
      ((unitIndAction w l k₀ hw0).deg_image false).symm

/-! ## Part 5: IndAction を受け取る一般化前表現 -/

/-- **一般化前表現 (M241F-b)**: `arithPreRep`（M238F、`Ind = Unit`・定数像）を、
    任意の不定性作用データ `A : IndAction` を受け取る形に一般化した前表現。
    `Ind` は軌道 `A.Ix`（非定数可）、`image` は `A.image`、`hullTheta`/`shell`
    は軌道の上界包 `A.hull`（次数 = wssq を `A.deg_hull` が保証）。
    `q_realized` だけを外部仮説 hq に外部化する。 -/
def arithPreRepInd (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (A : IndAction w l)
    (hq : ∃ i, (frobVol w).le (qPilotDiv n) (A.image i)) :
    MultiradialRep (arithVol w B) (arithSkeleton w n l B hl hB) where
  Ind := A.Ix
  ind0 := A.base
  shell := A.hull
  image := A.image
  image_in_shell := fun i => A.image_le_hull i
  hullTheta := A.hull
  image_in_hull := fun i => A.image_le_hull i
  qRegion := qPilotDiv n
  q_realized := hq
  vol_hull := by
    show degZ w A.hull - (B : Int) = -((B : Int) - degZ w (gaussDiv l))
    rw [A.deg_hull]
    omega
  vol_q := by
    show degZ w (qPilotDiv n) - (B : Int) = -((B : Int) - degZ w (qPilotDiv n))
    omega

/-- **crux ⟹ Cor312（一般化版）**: 任意の作用データ上でも、外部化した
    輸送仮説から系3.12 が従う。 -/
theorem arith_transport_ind (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (A : IndAction w l)
    (hq : ∃ i, (frobVol w).le (qPilotDiv n) (A.image i)) :
    Cor312 (arithSkeleton w n l B hl hB) :=
  cor312_of_multiradial (arithPreRepInd w n l B hl hB A hq)

/-! ## Part 6: 単数軌道を差し込んだ具体前表現 -/

/-- **単数軌道を据えた前表現**: `arithPreRepInd` に (Ind2) 作用 `unitIndAction`
    を差し込む。crux は基点像 `gaussDiv l`（= `image false`）への包含
    `qPilotDiv n ⊆ gaussDiv l` で供給する。像は非定数（`unitIndAction_orbit`）
    でありながら q_realized が基点で成立する初の算術前表現。 -/
def arithPreRepUnit (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0)
    (hq : (frobVol w).le (qPilotDiv n) (gaussDiv l)) :
    MultiradialRep (arithVol w B) (arithSkeleton w n l B hl hB) :=
  arithPreRepInd w n l B hl hB (unitIndAction w l k₀ hw0)
    ⟨false, hq⟩

/-- **crux ⟹ Cor312（単数軌道版）**: 非定数軌道を持つ表現を経由しても
    系3.12 が従う。 -/
theorem arith_transport_of_unit_orbit (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0)
    (hq : (frobVol w).le (qPilotDiv n) (gaussDiv l)) :
    Cor312 (arithSkeleton w n l B hl hB) :=
  cor312_of_multiradial (arithPreRepUnit w n l B k₀ hl hB hw0 hq)

/-- **crux ⟹ 表現の存在（単数軌道版）**: 忠実算術模型上の、**非定数**な
    Θ-像軌道を持つ `MultiradialRep` の居住が輸送仮説へ局在した。 -/
theorem arith_rep_of_unit_orbit (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0)
    (hq : (frobVol w).le (qPilotDiv n) (gaussDiv l)) :
    Nonempty (MultiradialRep (arithVol w B) (arithSkeleton w n l B hl hB)) :=
  ⟨arithPreRepUnit w n l B k₀ hl hB hw0 hq⟩

/-! ## Part 7: capstone（総括） -/

/-- **capstone (M241F): 不定性の作用 IndAction の総括** —
    (a) 単数不定性 (Ind2) が Θ-像に作用し軌道が**非定数**、
    (b) その作用は**大域次数 degZ を保つ**（軌道は等次数葉上）、
    (c) 一般化前表現 `arithPreRepInd` は任意の作用データを受け取り、
        `q_realized` だけを外部化した `MultiradialRep` を居住させ、
    (d) 単数軌道の前表現から crux ⟹ Cor312 が従う。
    M238F の `Ind = Unit`・定数像から、不定性が領域 QDiv に実際に作用する
    構造への格上げが機械検証された（Ind1/Ind3 同時作用・crux 単一 Prop 化・
    鏡像定理は次段）。 -/
theorem indAction_wellDefined (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0) :
    ((unitIndAction w l k₀ hw0).image true
        ≠ (unitIndAction w l k₀ hw0).image false)
      ∧ (∀ i, degZ w ((unitIndAction w l k₀ hw0).image i)
          = degZ w (gaussDiv l))
      ∧ ((frobVol w).le (qPilotDiv n) (gaussDiv l)
          → Cor312 (arithSkeleton w n l B hl hB)) :=
  ⟨unitIndAction_orbit w l k₀ hw0,
   (unitIndAction w l k₀ hw0).deg_image,
   fun hq => arith_transport_of_unit_orbit w n l B k₀ hl hB hw0 hq⟩

end IUT
