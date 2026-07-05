/-
  IUT/FrobenioidVolume.lean — M230F（Dβ-3: 算術体積理論 frobVol）の形式化

  D-β 詳細化ラウンド（軸1 = 模型忠実化）の第一資産。これまでの
  `MultiradialRep`/`MultiradialInput` の全充足模型（M5-4・M210F・M216F）は
  Region = ℤ・vol = id の「体積値そのものが領域」デモ模型 `m202fVol`
  （IUT/Indeterminacies.lean:142）上にあった。領域が算術的対象でなく、
  不定性が実際に作用していない——これが現行 witness の正直な弱点である。

  本モジュールは領域を**実際の Frobenioid 有効因子** `QDiv`
  （IUT/FrobenioidModel.lean:196、素点ごとの重複度の有限サポート関数・
  bound をデータに持ち選択公理不要）に据え、体積を**重み付き大域次数**
  `degZ w`（同 :314、加法性・斉次性・非負性が既証明）とする
  `VolumeTheory`（IUT/Multiradial.lean:55）インスタンス `frobVol w` を
  構成する。IUT-III 定理3.11 (i)(a)(c) のデータ実体化（対数殻＝因子領域・
  大域 Frobenioid の次数＝degZ）に対応する。

  ## 新規に閉じる中核（全て sorry なし・新規 Classical.choice なし）

  * `qdivSup` — QDiv の正則包（holomorphic hull）の組合せ代理:
    各座標 max・bound は max。格子法則 `qdivSup_comm`/`qdivSup_self`。
  * `nsum_mono` — 有限和 `nsum`（FrobenioidModel:113）の単調性:
    各項 f k ≤ g k なら Σf ≤ Σg。degZ 単調性の算術核。
  * `degZ_mono` — **本タスクの主定理**: 各座標 ≤（le）から次数 ≤。
    両因子を共通上界 max bound へ `degN_stable` で持ち上げ、`nsum_mono`
    と `Nat.mul_le_mul` で閉じる（重み w は非負性を要さない ℕ 値）。
  * `frobVol` — VolumeTheory の全 9 フィールド（le_refl/le_trans/hull の
    三格子法則/vol_mono）を実データで充足する `VolumeTheory` インスタンス。
  * well-defined 補題群（`frobVol_le_iff`/`frobVol_vol_eq`/`frobVol_hull_eq`
    ・順序とモノイド和の両立 `frobVol_le_qadd_left`/`frobVol_vol_qadd`・
    膨張単調性 `frobVol_expansion_monotone`）と capstone `frobVol_wellDefined`。

  ## 正直な限定（この上に載るべき次段 = まだ D-β 本丸ではない）

  * `frobVol` は算術体積理論の**土台**にすぎない。この上に像・q-領域を
    実データ化した前表現 `arithPreRep`（Dβ-4）、不定性の作用 `IndAction`
    （Dβ-5）、crux の単一 Prop 化 `ThetaLinkTransport`（Dβ-6/7）を載せる
    のは次段であり、本モジュールはそれらを一切構成しない。
  * degZ は ℕ 値（非負）なので、frobVol 上では `vol` が常に ≥ 0 である。
    デモ模型の `vol_q = -s.logq < 0`（負の体積）は frobVol の効果的因子には
    そのままでは載らない——符号規約の整合（logq := deg qPilot 等）は Dβ-4 の
    `arithSkeleton` 設計に委ねる。ゆえに本ファイルでは frobVol 上の
    `MultiradialRep` は構成しない（それは Dβ-4 以降）。
  * `hull`（各座標 max）は正則包の**組合せ代理**であり、原論文の
    holomorphic hull の複素幾何的内容は写像しない。重み w は ℕ 値
    （log p の整数化）。実数値体積版 `frobVolReal`（vol := rlogVol）は
    VolumeTheory.vol : Region → Int に型が合わない別構造 RealVolumeTheory を
    要するため本ファイル範囲外（Dβ-2/実数トラックで別途）。
-/
import IUT.Multiradial
import IUT.FrobenioidModel

namespace IUT

/-! ## Part 1: QDiv の正則包 qdivSup（各座標 max） -/

/-- **QDiv の正則包（holomorphic hull の組合せ代理）**: 各座標で重複度の
    max を取り、サポート上界は bound の max。効果的因子の格子構造の join。
    bound をデータに持つので選択公理不要（qadd と同流）。 -/
def qdivSup (x y : QDiv) : QDiv where
  mult := fun k => max (x.mult k) (y.mult k)
  bound := max x.bound y.bound
  vanish := fun k hk => by
    have h1 := x.vanish k (Nat.le_trans (Nat.le_max_left _ _) hk)
    have h2 := y.vanish k (Nat.le_trans (Nat.le_max_right _ _) hk)
    omega

/-- 正則包の可換律（格子法則 join の可換性）。 -/
theorem qdivSup_comm (x y : QDiv) : qdivSup x y = qdivSup y x :=
  QDiv.ext (funext fun k => nat_max_comm (x.mult k) (y.mult k))
    (nat_max_comm x.bound y.bound)

/-- 正則包の冪等律 x ⊔ x = x（格子法則）。 -/
theorem qdivSup_self (x : QDiv) : qdivSup x x = x :=
  QDiv.ext (funext fun k => by
      show max (x.mult k) (x.mult k) = x.mult k
      omega)
    (by show max x.bound x.bound = x.bound; omega)

/-! ## Part 2: 有限和 nsum の単調性と degZ の単調性 -/

/-- **有限和の単調性**: 各項で f k ≤ g k なら Σ_{k<n} f k ≤ Σ_{k<n} g k。
    degZ の単調性の算術核（各座標の重複度の ≤ を次数の ≤ に持ち上げる）。 -/
theorem frobNsum_mono (f g : Nat → Nat) (n : Nat) (h : ∀ k, f k ≤ g k) :
    nsum f n ≤ nsum g n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    show nsum f m + f m ≤ nsum g m + g m
    have hm := h m
    omega

/-- **定理 (M230F-1): 重み付き大域次数の単調性** — 各座標 ≤
    （x.mult k ≤ y.mult k, ∀k）なら degZ w x ≤ degZ w y。

    証明: 両因子の次数を共通上界 max(x.bound, y.bound) までの和に
    `degN_stable` で書き換え、各項 w k · x.mult k ≤ w k · y.mult k
    （`Nat.mul_le_mul`）に `nsum_mono` を適用。最後に ℕ→ℤ の cast
    単調性（omega が cast を解する）で degZ へ。重み w は非負性を
    要さない ℕ 値で閉じる。frobVol の `vol_mono` フィールドの供給源。 -/
theorem degZ_mono (w : Nat → Nat) {x y : QDiv}
    (h : ∀ k, x.mult k ≤ y.mult k) : degZ w x ≤ degZ w y := by
  have hmono : degN w x ≤ degN w y := by
    have hx : degN w x
        = nsum (fun k => w k * x.mult k) (max x.bound y.bound) :=
      (degN_stable w x (max x.bound y.bound) (Nat.le_max_left _ _)).symm
    have hy : degN w y
        = nsum (fun k => w k * y.mult k) (max x.bound y.bound) :=
      (degN_stable w y (max x.bound y.bound) (Nat.le_max_right _ _)).symm
    rw [hx, hy]
    exact frobNsum_mono _ _ _ (fun k => Nat.mul_le_mul (Nat.le_refl (w k)) (h k))
  show (degN w x : Int) ≤ (degN w y : Int)
  omega

/-! ## Part 3: 算術体積理論 frobVol の構成 -/

/-- **定理 (M230F-2): 算術 Frobenioid 体積理論** —
    Region = 有効因子 `QDiv`・包含 le = 各座標 ≤・正則包 hull = `qdivSup`
    （各座標 max）・体積 vol = 重み付き大域次数 `degZ w` とする
    `VolumeTheory` インスタンス。VolumeTheory の全公理:
    * 順序律 (le_refl/le_trans) — 各座標の ℕ の反射・推移
    * 格子律 (le_hull_left/right/hull_least) — 各座標 max の join 普遍性
    * 体積単調性 (vol_mono) — `degZ_mono`（M230F-1）
    を実データの定理で満たす。デモ模型 `m202fVol`（vol = id・領域 = ℤ）を
    実 Frobenioid 因子上の算術模型へ置き換えた、忠実模型化の土台。 -/
@[reducible] def frobVol (w : Nat → Nat) : VolumeTheory where
  Region := QDiv
  le := fun x y => ∀ k, x.mult k ≤ y.mult k
  le_refl := fun r k => Nat.le_refl (r.mult k)
  le_trans := fun h1 h2 k => Nat.le_trans (h1 k) (h2 k)
  hull := qdivSup
  le_hull_left := fun a b k => Nat.le_max_left (a.mult k) (b.mult k)
  le_hull_right := fun a b k => Nat.le_max_right (a.mult k) (b.mult k)
  hull_least := fun {a b _c} h1 h2 k => by
    have p := h1 k
    have q := h2 k
    show max (a.mult k) (b.mult k) ≤ _c.mult k
    omega
  vol := degZ w
  vol_mono := fun h => degZ_mono w h

/-! ## Part 4: well-defined 性の補題群と capstone -/

/-- 包含順序の展開（各座標 ≤）。 -/
theorem frobVol_le_iff (w : Nat → Nat) (x y : QDiv) :
    (frobVol w).le x y ↔ ∀ k, x.mult k ≤ y.mult k := Iff.rfl

/-- 体積の展開（degZ w）。 -/
theorem frobVol_vol_eq (w : Nat → Nat) (x : QDiv) :
    (frobVol w).vol x = degZ w x := rfl

/-- 正則包の展開（qdivSup）。 -/
theorem frobVol_hull_eq (w : Nat → Nat) (x y : QDiv) :
    (frobVol w).hull x y = qdivSup x y := rfl

/-- **順序とモノイド和の両立（左）**: x ⊆ x + y。有効因子の加法は
    領域を太らせる方向のみ（Ind3 の上方包含の因子代数的裏付け）。 -/
theorem frobVol_le_qadd_left (w : Nat → Nat) (x y : QDiv) :
    (frobVol w).le x (qadd x y) :=
  fun k => Nat.le_add_right (x.mult k) (y.mult k)

/-- **体積の加法性の frobVol 上の発動**: vol(x + y) = vol x + vol y
    （degZ の加法性 M51F-2 が frobVol の vol として作用する）。 -/
theorem frobVol_vol_qadd (w : Nat → Nat) (x y : QDiv) :
    (frobVol w).vol (qadd x y) = (frobVol w).vol x + (frobVol w).vol y :=
  degZ_add w x y

/-- **膨張単調性**: 領域を正則包で太らせると体積は増加のみ
    （x ⊆ x⊔y かつ vol x ≤ vol(x⊔y)）。Ind3（上半両立性による膨張は
    体積を増やすだけ）が frobVol 上で成立することの土台。 -/
theorem frobVol_expansion_monotone (w : Nat → Nat) (x y : QDiv) :
    (frobVol w).le x ((frobVol w).hull x y)
      ∧ (frobVol w).vol x ≤ (frobVol w).vol ((frobVol w).hull x y) :=
  ⟨(frobVol w).le_hull_left x y,
   (frobVol w).vol_mono ((frobVol w).le_hull_left x y)⟩

/-- **capstone (M230F-3): frobVol の well-defined 性** —
    構成した算術体積理論が (a) 領域は有効因子 QDiv、(b) 包含は各座標 ≤、
    (c) 体積は重み付き大域次数 degZ w、(d) 正則包は各座標 max の qdivSup、
    という設計どおりのデータで矛盾なく居住することの機械検証。
    忠実模型化トラック（軸1）の第一資産が確定したことを表す。 -/
theorem frobVol_wellDefined (w : Nat → Nat) :
    (frobVol w).Region = QDiv
      ∧ (∀ x y : QDiv, (frobVol w).le x y ↔ ∀ k, x.mult k ≤ y.mult k)
      ∧ (∀ x : QDiv, (frobVol w).vol x = degZ w x)
      ∧ (∀ x y : QDiv, (frobVol w).hull x y = qdivSup x y) :=
  ⟨rfl, fun _ _ => Iff.rfl, fun _ => rfl, fun _ _ => rfl⟩

end IUT
