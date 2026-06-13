/-
  IUT/VolumeModel.lean — M99F（具体的 VolumeTheory モデルの構成）

  **形式化の範囲（正直な申告）**:
  * M99F-1  具体的 `VolumeTheory` インスタンス `intVolumeTheory` の構成
             （Region = Int, le = ≤, hull = max, vol = id）
  * M99F-2  `intVolumeTheory_consistent : Nonempty VolumeTheory`
  * M99F-3  M97 の `sumSq_closed`・`cube_le_sumSq` から導く整数算術橋
             （Nat 等式を Nat→Int キャストで持ち上げ）
  * M99F-4  具体的 `Skeleton` 値 `demoSkeleton`（lstar=2, logq=1, logTheta=0）
             と `Cor312 demoSkeleton`（充足可能性のサニティチェック）
  * M99F-5  `VolumeModelData` — 上記を束ねた総括構造体・witness・
             `Nonempty VolumeModelData`

  **本モジュールが提供しないもの（未形式化）**:
  - `MultiradialRep` の充足（= 定理3.11 の構成そのもの）は **提供しない**。
    それは柱D の本丸であり、本モジュールの範囲外である。
  - 定理3.11 / 系3.12 の証明は **提供しない**。
    `cor312_of_multiradial`（M5）は `MultiradialRep` を仮定として要求する。
  - 本モジュールは IUT の数学的主張を証明するものではなく、
    `VolumeTheory` インターフェースが非空（無矛盾）であることの実証、
    および体積側の初等算術の接続の確認のみを行う。

  全て選択公理不使用。
-/
import IUT.Premises311

namespace IUT

/-! ## M99F-1: 具体的 VolumeTheory インスタンス -/

/-- **M99F-1 `intVolumeTheory`** — 具体的 VolumeTheory モデル。
    - `Region := Int`（各領域をその log-volume 整数値で表現）
    - `le a b := a ≤ b`（包含 = 整数順序）
    - `hull a b := max a b`（正則包 = 上限）
    - `vol r := r`（log-volume = 恒等写像）

    全 9 フィールドを sorry なしで証明する。
    これにより `VolumeTheory` インターフェースが非空であることが確認される。

    **注意**: これは `MultiradialRep` の構成ではない。IUT 定理3.11 の
    証明でも系3.12 の証明でもない。インターフェースの inhabitation（非空性）
    を示す最小のモデルである。 -/
def intVolumeTheory : VolumeTheory where
  Region     := Int
  le         := (· ≤ ·)
  le_refl    := Int.le_refl
  le_trans   := fun h1 h2 => Int.le_trans h1 h2
  hull       := fun a b => max a b
  le_hull_left  := fun a b => Int.le_max_left a b
  le_hull_right := fun a b => Int.le_max_right a b
  hull_least := fun h1 h2 => by rw [Int.max_le]; exact ⟨h1, h2⟩
  vol        := id
  vol_mono   := fun h => h

/-! ## M99F-2: VolumeTheory の非空性 -/

/-- **M99F-2 `intVolumeTheory_consistent`** — `VolumeTheory` は非空。
    `intVolumeTheory` が witness となる。 -/
theorem intVolumeTheory_consistent : Nonempty VolumeTheory :=
  ⟨intVolumeTheory⟩

/-! ## M99F-3: 体積側の整数算術橋 -/

/-- **M99F-3a `theta_volume_cube_bound`** — テータパイロット総次数の
    体積下界の整数版。M97 の `cube_le_sumSq`（Nat 等式）を
    `exact_mod_cast` で Int に持ち上げる。

    この不等式は、テータパイロットの q-冪 {q^{j²}} _{j=1,…,l}
    の総 log-volume が少なくとも l³/3 以上であることを整数算術で
    表現したものである（IUT III Prop 3.9 の文脈）。

    **注**: 本定理は VolumeTheory や Skeleton を仮定せず、
    純粋に Nat→Int キャストの演習として成立する。 -/
theorem theta_volume_cube_bound (l : Nat) :
    (l * l * l : Int) ≤ 3 * (sumSq l : Int) := by
  have h := cube_le_sumSq l
  exact_mod_cast h

/-- **M99F-3b `sumSq_closed_int`** — 平方和の閉形式（Int 版）。
    M97 の `sumSq_closed`（Nat 等式 6·Σj² = l(l+1)(2l+1)）を
    `exact_mod_cast` で Int に持ち上げる。

    これは M5-2（厳密評価の障害定理）で使われる Σj² 係数の
    閉形式であり、体積側の計算の明示的な根拠となる。 -/
theorem sumSq_closed_int (l : Nat) :
    6 * (sumSq l : Int) = (l : Int) * ((l : Int) + 1) * (2 * (l : Int) + 1) := by
  have h := sumSq_closed l
  exact_mod_cast h

/-! ## M99F-4: 具体的 Skeleton と Cor312 の充足可能性 -/

/-- **M99F-4a `demoSkeleton`** — 具体的な `Skeleton` 値。
    - `lstar := 2`（l⋇ ≥ 2 を満たす最小値）
    - `logq  := 1`（|log q| = 1 > 0）
    - `logTheta := 0`（|log Θ| = 0 ≤ 1 = |log q|）

    `Cor312 demoSkeleton` = (-0 ≥ -1) = (0 ≥ -1) が成立する。

    **注意**: これは「Cor312 の仮定を満たす Skeleton が存在する」という
    サニティチェックである。IUT のいかなる定理の証明でもない。 -/
def demoSkeleton : Skeleton where
  lstar    := 2
  hl       := by omega
  logq     := 1
  hq       := by omega
  logTheta := 0

/-- **M99F-4b `demoSkeleton_cor312`** — `demoSkeleton` に対して `Cor312` が
    成立することの直接検証。`Cor312 s` の定義は `-s.logTheta ≥ -s.logq`。
    `-0 ≥ -1` は `omega` で閉じる。

    これは「Cor312 の結論が充足可能（satisfiable）」であることを示すに留まる。
    実際の IUT III 系3.12 の証明（任意の楕円曲線について Cor312 が成立すること）
    は `MultiradialRep` の充足を要し、本モジュールの範囲外である。 -/
theorem demoSkeleton_cor312 : Cor312 demoSkeleton := by
  unfold Cor312 demoSkeleton
  simp only []
  omega

/-! ## M99F-5: VolumeModelData 総括構造体 -/

/-- **M99F-5a `VolumeModelData`** — 本モジュールの成果を束ねる総括構造体。

    正直な説明:
    - `volume_theory` フィールドは `VolumeTheory` の inhabitant（非空の証拠）
    - `theta_cube_bound` / `sumSq_formula` は体積側の整数算術の接続
    - `demo_skel` / `demo_cor312` は Cor312 の充足可能性のサニティチェック
    - `no_multiradial_rep` は**明示的な非達成マーカー**: MultiradialRep は
      構成していない（定理3.11 は証明していない）ことを型として記録する。

    **MultiradialRep の充足（= 定理3.11 の構成そのもの）は
    本モジュールでは提供されない。それは柱D の本丸であり未形式化である。** -/
structure VolumeModelData where
  /-- `VolumeTheory` の具体的な inhabitant。 -/
  volume_theory    : VolumeTheory
  /-- l³ ≤ 3·Σj² の整数版（テータパイロット体積下界）。 -/
  theta_cube_bound : ∀ l : Nat, (l * l * l : Int) ≤ 3 * (sumSq l : Int)
  /-- 6·Σj² = l(l+1)(2l+1) の整数版（閉形式）。 -/
  sumSq_formula    : ∀ l : Nat,
    6 * (sumSq l : Int) = (l : Int) * ((l : Int) + 1) * (2 * (l : Int) + 1)
  /-- Cor312 を満たす具体的 Skeleton（充足可能性のサニティチェック）。 -/
  demo_skel        : Skeleton
  /-- demo_skel に対して Cor312 が直接成立する。 -/
  demo_cor312      : Cor312 demo_skel
  /-- **明示的な非達成マーカー**: MultiradialRep は構成していない。
      定理3.11 / 系3.12 はここでは証明されていない。
      このフィールドは「本モジュールの範囲外」を型レベルで明記する。 -/
  no_multiradial_rep : True

/-- **M99F-5b `volumeModelData`** — VolumeModelData の具体的 witness。 -/
def volumeModelData : VolumeModelData where
  volume_theory    := intVolumeTheory
  theta_cube_bound := theta_volume_cube_bound
  sumSq_formula    := sumSq_closed_int
  demo_skel        := demoSkeleton
  demo_cor312      := demoSkeleton_cor312
  no_multiradial_rep := trivial

/-- **定理 (M99F-5c): VolumeModelData の存在（見出し）** —
    具体的な体積モデルデータが inhabit される。 -/
theorem volumeModelData_exists : Nonempty VolumeModelData :=
  ⟨volumeModelData⟩

end IUT
