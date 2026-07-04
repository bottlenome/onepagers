/-
  IUT/Indeterminacies.lean — M202F（(Ind1)(Ind2)(Ind3) の構造化・
  柱D D-α-3・並行部品）

  # M202F: (Ind1)(Ind2)(Ind3) の構造化（柱D D-α-3・並行部品）

  IUT III 定理3.11 (i)(ii) の三つの不定性を、既に建設済みの部品から
  「型レベルで」束ね直す並行部品。M5（IUT/Multiradial.lean）の
  `MultiradialRep` は不定性を平坦な単一フィールド `Ind : Type`
  （基点 `ind0`）として公理化している。本モジュールはこの平坦な
  `Ind` を三つの由来に分解する:

  * M202F-1 `Ind1` / `ind1_0` — (Ind1)「procession の自己同型による
    不定性」。M53F-9 `deloopInd`（IUT/PolyIsomorphism.lean）の
    再輸出。BG の poly-isomorphism（G-トーソル）を選択肢の型とする。
  * M202F-2 `Ind2` / `ind2_0` — (Ind2)「各直和因子への Ism のコピーの
    作用による不定性」。M55F `splitInd`/`unitEndo`
    （IUT/SplitFrobenioid.lean）の再輸出。split Frobenioid の
    単数成分トーソルを選択肢の型とする。
  * M202F-3 `UpperCompat` / `upperCompat_refl` — (Ind3)「上半両立性」
    の **新規** 定義。log-Kummer 対応で m を動かすとき (a) 対数殻は
    包含 ⊆（一方向）でしか両立しない、という一方向スラックを
    `V.le lo hi` を担うだけの最小構造として捉える（project-first）。
  * M202F-4 `upper_compat_not_symm` — 上半両立が真に一方向である
    こと（⊆ は成り立つが逆 ⊇ は成り立たない witness）。これは
    M5 の `strict_evaluation_obstruction`（両側厳密評価は破綻）／
    `padding_necessary`（片側の膨張が必然）が捉える「厳密＝両側は
    不可能・Ind3＝⊆ のみのスラック」の型レベルの影である。
  * M202F-5 `ind311` / `ind311_0` — 積不定性 (Ind1)×(Ind2)×(Ind3)。
  * M202F-6 `ind311_forget` — 構造化不定性が平坦な `MultiradialRep.Ind`
    を細分することを、同一視 `h : M.Ind = ind311 …` に沿った輸送
    （忘却）として表す。
  * M202F-7 `ind311_refines` — 平坦な `Ind` フィールドが実際に積
    不定性 `ind311` を担い得ること（実現可能性・realizability）。
    Int モデル上の具体的 `MultiradialRep` を建てて示す。
  * M202F-8 capstone: `IndeterminaciesData` / `indeterminaciesData` /
    `indeterminacies_exists`。

  **意義**（Dα-3）: (Ind1)=`deloopInd`・(Ind2)=`splitInd`/`unitEndo`
  を再輸出し、(Ind3)=新規の一方向上半両立 `UpperCompat` を加え、
  三者の積 `ind311` が平坦な `MultiradialRep.Ind` を細分する（忘却
  `ind311_forget`）ことを機械検証する。これは Dα-5 の `ind_eq`
  フィールド（`M.Ind = ind311 …` の同一視）へ供給される部品である。

  **正直な限定**:
  * `Ind3`（上半両立）は `V.le lo hi` を担うだけの **最小の
    le-関係** に留める。log-Kummer 対応・Θ×μ_LGP-link 両立性との
    完全な連結（Kummer 同型の構成）は Dα-4 の課題である。
  * `ind311_forget` は同一視 `h` を仮定した上での輸送であり、
    実際の定理3.11 の構成で `M.Ind` が本当にこの積型に一致すること
    （`ind_eq`）は Dα-5 が確立する。ここでは `ind311_refines` で
    「平坦フィールドがこの積型を担い得る」ことまでを示す。
  * `MultiradialRep` の解析的構成そのもの（遠アーベル復元・エタール
    テータ剛性・mono-theta 環境）は D-β の課題であり、本モジュールは
    型レベルの束ね直しに徹する。

  D-α の三不定性を一つの積 `ind311` へ束ね、平坦 `Ind` への忘却まで
  を core Lean だけで（sorry なし・新規 Classical.choice なし）閉じる。
-/
import IUT.Multiradial
import IUT.SplitFrobenioid
import IUT.PolyIsomorphism

namespace IUT

/-! ## M202F-1: (Ind1) — procession の自己同型（`deloopInd` 再輸出）

    IUT III 定理3.11 (i) の (Ind1)「procession の自己同型による
    不定性」。M53F-9 `deloopInd`（BG の poly-isomorphism = G-トーソル）
    をそのまま (Ind1) の選択肢の型として採用する。 -/

/-- (Ind1) の選択肢の型: BG の一点上の poly-isomorphism（M53F-7 により
    G-トーソル）。`MultiradialRep.Ind` へ供給できる形。 -/
abbrev Ind1 (G : Grp) : Type := deloopInd G

/-- (Ind1) の基点（恒等同型 = 「不定性を選ばない」選択肢）。 -/
def ind1_0 (G : Grp) : Ind1 G := deloopInd0 G

/-- (Ind1) の非自明性の再輸出（M53F-9）。 -/
theorem ind1_nontrivial (G : Grp) (h : ∃ g, g ≠ G.one) :
    ∃ i : Ind1 G, i ≠ ind1_0 G :=
  deloopInd_nontrivial G h

/-! ## M202F-2: (Ind2) — 単数成分の作用（`splitInd`/`unitEndo` 再輸出）

    IUT III 定理3.11 (i) の (Ind2)「各直和因子への Ism のコピーの
    作用による不定性」。M55F `splitInd`（split Frobenioid の自明因子上
    の自己同型 = 単数成分 U-トーソル、`unitEndo` の族）を (Ind2) の
    選択肢の型として採用する。 -/

/-- (Ind2) の選択肢の型: split Frobenioid の自明因子上の
    poly-isomorphism（M55F-6 により U-トーソル）。 -/
abbrev Ind2 (U : Grp) (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) :
    Type := splitInd U hU

/-- (Ind2) の基点（単数 1 の同型 = 恒等同型）。 -/
def ind2_0 (U : Grp) (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) :
    Ind2 U hU := splitInd0 U hU

/-- (Ind2) の非自明性の再輸出（M55F-8）。 -/
theorem ind2_nontrivial (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (h : ∃ u : U.carrier, u ≠ U.one) :
    ∃ i : Ind2 U hU, i ≠ ind2_0 U hU :=
  splitInd_nontrivial U hU h

/-! ## M202F-3: (Ind3) — 上半両立性（一方向スラック・新規）

    IUT III 定理3.11 (ii) の (Ind3)「上半両立性」: log-Kummer 対応で
    m を動かすとき、(b)(c)-MOD は厳密に両立するが (a) 対数殻は包含
    ⊆（inclusions）／全射 ↠（surjections）**のみ** で両立する。
    その一方向性を `VolumeTheory.le`（= ⊆）を一つ担うだけの最小構造
    として捉える。等号（両側両立）を要求しないのが本質である。 -/

/-- **(Ind3) 上半両立の選択肢の型（新規）**: 領域の一方向包含
    `lo ⊆ hi`（`V.le lo hi`）を担うデータ。等号 `lo = hi`
    （両側両立）ではなく **⊆ のみ**（片側スラック）を要求する点が
    (Ind3) の核心。 -/
structure UpperCompat (V : VolumeTheory) where
  /-- 下側の領域（例: log-Kummer 後の対数殻像）。 -/
  lo : V.Region
  /-- 上側の領域（例: 正則包側の容器）。 -/
  hi : V.Region
  /-- 上半両立: `lo ⊆ hi`（一方向のみ）。 -/
  compat : V.le lo hi

/-- (Ind3) の基点: 反射的な上半両立 `r ⊆ r`（「スラックを選ばない」
    自明な選択肢）。 -/
def upperCompat_refl (V : VolumeTheory) (r : V.Region) : UpperCompat V :=
  ⟨r, r, V.le_refl r⟩

/-! ## M202F-4: 一方向性の witness（障害理論との橋渡し）

    上半両立が真に一方向であること — ⊆ は成り立つが逆 ⊇ は成り立た
    ない具体例 — を Int モデルで示す。これは M5 の
    `strict_evaluation_obstruction`（両側＝厳密テータ評価は充足不能）
    と `padding_necessary`（片側の体積膨張が必然）が捉える
    「両側は破綻・Ind3 は ⊆ のみのスラック」の型レベルの影である。 -/

/-- Int モデルの `VolumeTheory`（領域 = ℤ、包含 = ≤、正則包 = max、
    体積 = 恒等）。M5 `multiradial_consistent` と同じ充足モデル。 -/
@[reducible] def m202fVol : VolumeTheory where
  Region := Int
  le := (· ≤ ·)
  le_refl := Int.le_refl
  le_trans := fun h1 h2 => Int.le_trans h1 h2
  hull := fun a b => max a b
  le_hull_left := fun a b => by omega
  le_hull_right := fun a b => by omega
  hull_least := fun h1 h2 => by omega
  vol := id
  vol_mono := fun h => h

/-- **(Ind3) は真に一方向**: `lo ⊆ hi` を満たす上半両立であって
    逆 `hi ⊆ lo` は成り立たないものが存在する。等号への強化
    （両側両立）が不可能な地点にこそ (Ind3) の膨張スラックが宿る。 -/
theorem upper_compat_not_symm :
    ∃ (V : VolumeTheory) (c : UpperCompat V), ¬ V.le c.hi c.lo :=
  ⟨m202fVol, ⟨0, 1, by show (0 : Int) ≤ 1; omega⟩, by
    show ¬ (1 : Int) ≤ 0
    omega⟩

/-! ## M202F-5: 積不定性 ind311 = (Ind1)×(Ind2)×(Ind3) -/

/-- **積不定性** (Ind1)×(Ind2)×(Ind3)。三つの由来の選択肢を一つの
    型に束ねる（[IUTchIII] 定理3.11 の不定性 (Ind1–3) 全体）。 -/
def ind311 (G U : Grp) (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (V : VolumeTheory) : Type :=
  Ind1 G × Ind2 U hU × UpperCompat V

/-- 積不定性の基点（各成分の基点の組 = 「どの不定性も選ばない」
    選択肢）。上半両立成分は反射的容器 `r ⊆ r` を使う。 -/
def ind311_0 (G U : Grp) (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (V : VolumeTheory) (r : V.Region) : ind311 G U hU V :=
  (ind1_0 G, ind2_0 U hU, upperCompat_refl V r)

/-! ## M202F-6: 平坦 Ind への忘却（構造化不定性の細分性） -/

/-- **忘却 / 細分**: 同一視 `h : M.Ind = ind311 …` が与えられれば、
    構造化された積不定性 `ind311` を平坦な `MultiradialRep.Ind` へ
    輸送できる。構造化不定性が平坦フィールドを細分する（refine）
    ことの型レベルの内容。同一視 `h`（`ind_eq`）の供給は Dα-5。 -/
def ind311_forget {V : VolumeTheory} {s : Skeleton} (M : MultiradialRep V s)
    {G U : Grp} {hU : ∀ a b : U.carrier, U.mul a b = U.mul b a}
    (h : M.Ind = ind311 G U hU V) :
    ind311 G U hU V → M.Ind :=
  fun x => cast h.symm x

/-! ## M202F-7: 実現可能性（平坦フィールドが積不定性を担い得る） -/

/-- ℤ の加法群の可換性（`intGrp` を (Ind2) パラメータ U に使うため）。 -/
def intComm : ∀ a b : intGrp.carrier, intGrp.mul a b = intGrp.mul b a :=
  fun a b => Int.add_comm a b

/-- **定理 (M202F-7): 実現可能性** — 平坦な `MultiradialRep.Ind`
    フィールドが実際に積不定性 `ind311` を担い得る。M5
    `multiradial_consistent` と同じ Int モデル上に、`Ind` 成分を
    `ind311 intGrp intGrp intComm` に据えた具体的 `MultiradialRep`
    を建てて示す。これにより `ind311_forget` の同一視 `h` が
    空回りでないことが保証される。 -/
theorem ind311_refines :
    ∃ (V : VolumeTheory) (s : Skeleton) (M : MultiradialRep V s),
      M.Ind = ind311 intGrp intGrp intComm V :=
  ⟨m202fVol,
   { lstar := 2, hl := by omega, logq := 1, hq := by omega, logTheta := 1 },
   { Ind := ind311 intGrp intGrp intComm m202fVol,
     ind0 := ind311_0 intGrp intGrp intComm m202fVol 0,
     shell := 0,
     image := fun _ => -1,
     image_in_shell := fun _ => by show (-1 : Int) ≤ 0; omega,
     hullTheta := -1,
     image_in_hull := fun _ => by show (-1 : Int) ≤ -1; omega,
     qRegion := -1,
     q_realized := ⟨ind311_0 intGrp intGrp intComm m202fVol 0,
                    by show (-1 : Int) ≤ -1; omega⟩,
     vol_hull := rfl,
     vol_q := rfl },
   rfl⟩

/-! ## M202F-8: capstone — IndeterminaciesData / def / exists -/

/-- **(Ind1)(Ind2)(Ind3) の構造化データ**（Dα-3 の成果物）:
    三つの不定性の由来（群 G・可換群 U・体積理論 V）と、各々からの
    一つの不定性選択（i1/i2/i3）を束ねる。平坦 `MultiradialRep.Ind`
    の三由来分解の具体化。 -/
structure IndeterminaciesData where
  /-- (Ind1) の由来: procession の自己同型群。 -/
  G : Grp
  /-- (Ind2) の由来: 単数群（可換）。 -/
  U : Grp
  /-- U の可換性（split Frobenioid の合成則に必要）。 -/
  hU : ∀ a b : U.carrier, U.mul a b = U.mul b a
  /-- (Ind3) の舞台: 体積理論。 -/
  V : VolumeTheory
  /-- (Ind1) の一選択。 -/
  i1 : Ind1 G
  /-- (Ind2) の一選択。 -/
  i2 : Ind2 U hU
  /-- (Ind3) の一選択（一方向上半両立）。 -/
  i3 : UpperCompat V

/-- 基点からなる標準的な構造化不定性データ（各成分の基点を選ぶ）。 -/
def indeterminaciesData : IndeterminaciesData where
  G := intGrp
  U := intGrp
  hU := intComm
  V := m202fVol
  i1 := ind1_0 intGrp
  i2 := ind2_0 intGrp intComm
  i3 := upperCompat_refl m202fVol 0

/-- **定理 (M202F-8): 構造化不定性データの存在** — (Ind1)(Ind2)(Ind3)
    を束ねた `IndeterminaciesData` は充足可能。Dα-3 の並行部品が
    空回りでないことの capstone。 -/
theorem indeterminacies_exists : Nonempty IndeterminaciesData :=
  ⟨indeterminaciesData⟩

end IUT
