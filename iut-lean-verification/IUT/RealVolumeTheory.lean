/-
# M139: 実数値体積理論 — 柱D 入口: 定理3.11 インターフェースの ℝ 化

柱D（定理3.11 = 多輻的表現）の入口。M5 の `VolumeTheory` は
log-volume を **Int 値**で公理化していた（M99F の具体モデルも
Region = Int）。本モジュールはこの器を第87〜95弾で建設した
**本物の構成的実数 ℝ**（Bishop 流正則列）に持ち上げる:

  * M139-1 `qMax` — ℚ の max（PreRat の決定的交差比較の Quot.lift、
    井戸定義性 = prLe の関係両立の再利用）と order 法則
  * M139-2 `rmax` — **ℝ の max（正則包の実体）**: 点ごと max が
    正則性を保つ（4 分岐とも共通上界 u_m + u_n で押さえる）
  * M139-3 `RealVolumeTheory` — vol : Region → ℝ の M5 鏡映
    インターフェースと、Region = ℝ・le = rLe・hull = rmax・
    vol = id の具体モデル `realVolumeTheory`
  * M139-4 `intToReal` の順序埋め込み（単調 + **反映**: ε-消去
    c = 2 で実数の不等式から整数の不等式へ降下）と
    `RealVolumeTheory.ofInt` — 任意の Int 値体積理論の実数化
  * M139-5 `RealMultiradialRep` — 定理3.11 出力仕様の実数値版。
    **系3.12 の導出が実数経由でも降りる**（`cor312_of_realMultiradial`:
    実数値の体積比較 → intToReal 反映 → 整数 Cor312）。
    Int 値表現の持ち上げ `RealMultiradialRep.ofInt` と
    Szpiro 型不等式への full pipeline も実数経由で再現
  * M139-6 充足可能性（無矛盾性）: ℝ モデル上で実数値
    インターフェースは充足できる
  * M139-7 `RealVolumeTheoryData` — 総括

正直な限定: `MultiradialRep` の充足本体（遠アーベル復元・
エタールテータ剛性による構成そのもの = 柱D 本丸）は依然
未形式化であり、本モジュールは「体積理論の器と系3.12 導出が
実数の土俵でも成立する」ことの機械検証である（M5-4・M99F の
正直申告を引き継ぐ）。rmax の realEq 両立（congruence）は
本インターフェースの法則には不要のため次層に委ねる。

全て選択公理不使用。
-/
import IUT.VolumeModel
import IUT.Premises311Real

namespace IUT

/-! ## M139-1: ℚ の max -/

/-- 代表レベルの max（分子交差比較の決定的 if）。 -/
def prMax (x y : PreRat) : PreRat :=
  if x.num * y.den ≤ y.num * x.den then y else x

/-- 左引数の関係両立（cross case は prLe の両立で条件が同値になる）。 -/
theorem prMax_rel_left {x x' : PreRat} (hx : ratRel x x') (y : PreRat) :
    ratRel (prMax x y) (prMax x' y) := by
  unfold prMax
  cases Int.lt_or_le (y.num * x.den) (x.num * y.den) with
  | inr hle =>
    have hle' : x'.num * y.den ≤ y.num * x'.den := prLe_of_rel_left hx y hle
    rw [if_pos hle, if_pos hle']
    show y.num * y.den = y.num * y.den
    rfl
  | inl hlt =>
    have hcond : ¬ x.num * y.den ≤ y.num * x.den := by omega
    have hcond' : ¬ x'.num * y.den ≤ y.num * x'.den := by
      intro hle'
      have hback : x.num * y.den ≤ y.num * x.den :=
        prLe_of_rel_left (ratRel_symm hx) y hle'
      omega
    rw [if_neg hcond, if_neg hcond']
    exact hx

/-- 右引数の関係両立。 -/
theorem prMax_rel_right (x : PreRat) {y y' : PreRat} (hy : ratRel y y') :
    ratRel (prMax x y) (prMax x y') := by
  unfold prMax
  cases Int.lt_or_le (y.num * x.den) (x.num * y.den) with
  | inr hle =>
    have hle' : x.num * y'.den ≤ y'.num * x.den := prLe_of_rel_right x hy hle
    rw [if_pos hle, if_pos hle']
    exact hy
  | inl hlt =>
    have hcond : ¬ x.num * y.den ≤ y.num * x.den := by omega
    have hcond' : ¬ x.num * y'.den ≤ y'.num * x.den := by
      intro hle'
      have hback : x.num * y.den ≤ y.num * x.den :=
        prLe_of_rel_right x (ratRel_symm hy) hle'
      omega
    rw [if_neg hcond, if_neg hcond']
    show x.num * x.den = x.num * x.den
    rfl

/-- **M139-1a: ℚ の max**（二重 Quot.lift）。 -/
def qMax (a b : QRat) : QRat :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk ratRel (prMax x y))
      (fun _ _ hy => Quot.sound (prMax_rel_right x hy)) b)
    (fun _ _ hx => by
      induction b using Quot.ind
      rename_i y
      exact Quot.sound (prMax_rel_left hx y)) a

/-- **定理 (M139-1b): max の場合分け** — qMax は一方の腕に一致し、
    他方はそれ以下（以降の全法則の唯一の源）。 -/
theorem qMax_cases (a b : QRat) :
    (qMax a b = b ∧ qLe a b) ∨ (qMax a b = a ∧ qLe b a) := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  cases Int.lt_or_le (y.num * x.den) (x.num * y.den) with
  | inr hle =>
    apply Or.inl
    constructor
    · show Quot.mk ratRel (prMax x y) = Quot.mk ratRel y
      unfold prMax
      rw [if_pos hle]
    · show x.num * y.den ≤ y.num * x.den
      exact hle
  | inl hlt =>
    apply Or.inr
    constructor
    · show Quot.mk ratRel (prMax x y) = Quot.mk ratRel x
      unfold prMax
      rw [if_neg (by omega : ¬ x.num * y.den ≤ y.num * x.den)]
    · show y.num * x.den ≤ x.num * y.den
      omega

/-- **M139-1c: 左上界**。 -/
theorem qLe_max_left (a b : QRat) : qLe a (qMax a b) := by
  cases qMax_cases a b with
  | inl h => rw [h.1]; exact h.2
  | inr h => rw [h.1]; exact qLe_refl a

/-- **M139-1d: 右上界**。 -/
theorem qLe_max_right (a b : QRat) : qLe b (qMax a b) := by
  cases qMax_cases a b with
  | inl h => rw [h.1]; exact qLe_refl b
  | inr h => rw [h.1]; exact h.2

/-- **M139-1e: 最小上界性**。 -/
theorem qMax_le {a b c : QRat} (h1 : qLe a c) (h2 : qLe b c) :
    qLe (qMax a b) c := by
  cases qMax_cases a b with
  | inl h => rw [h.1]; exact h2
  | inr h => rw [h.1]; exact h1

/-- padding: a ≤ b なら a ≤ b + 2/(n+1)。 -/
theorem qLe_pad {a b : QRat} (n : Nat) (h : qLe a b) :
    qLe a (qAdd b (qAdd (qUnitFrac n) (qUnitFrac n))) := by
  have h2 : qLe (qAdd b ratRing.zero)
      (qAdd b (qAdd (qUnitFrac n) (qUnitFrac n))) :=
    qLe_add_two (qLe_refl b) (qFrac_add_nonneg 1 n 1 n)
  rw [qAdd_zero] at h2
  exact qLe_trans _ _ _ h h2

/-! ## M139-2: ℝ の max（正則包の実体） -/

/-- **M139-2a: ℝ の max** — 点ごと max。正則性は 4 分岐とも
    共通上界 u_m + u_n（cross case は片腕優越の連鎖
    y_m − x_n ≤ y_m − y_n ≤ |y_m − y_n|）で閉じる。 -/
def rmax (x y : RReal) : RReal where
  seq := fun n => qMax (x.seq n) (y.seq n)
  reg := by
    intro m n
    show qLe (qAbs (qAdd (qMax (x.seq m) (y.seq m))
        (qNeg (qMax (x.seq n) (y.seq n)))))
      (qAdd (qUnitFrac m) (qUnitFrac n))
    cases qMax_cases (x.seq m) (y.seq m) with
    | inl hm =>
      cases qMax_cases (x.seq n) (y.seq n) with
      | inl hn =>
        rw [hm.1, hn.1]
        exact y.reg m n
      | inr hn =>
        rw [hm.1, hn.1]
        apply qAbs_le_both
        · exact qLe_trans _ _ _
            (qLe_add_two (qLe_refl (y.seq m)) (qLe_neg_flip hn.2))
            (reg_sub_le y m n)
        · rw [qNeg_sub]
          exact qLe_trans _ _ _
            (qLe_add_two (qLe_refl (x.seq n)) (qLe_neg_flip hm.2))
            (qLe_trans _ _ _ (reg_sub_le x n m)
              (qLe_of_eq (qAdd_comm (qUnitFrac n) (qUnitFrac m))))
    | inr hm =>
      cases qMax_cases (x.seq n) (y.seq n) with
      | inl hn =>
        rw [hm.1, hn.1]
        apply qAbs_le_both
        · exact qLe_trans _ _ _
            (qLe_add_two (qLe_refl (x.seq m)) (qLe_neg_flip hn.2))
            (reg_sub_le x m n)
        · rw [qNeg_sub]
          exact qLe_trans _ _ _
            (qLe_add_two (qLe_refl (y.seq n)) (qLe_neg_flip hm.2))
            (qLe_trans _ _ _ (reg_sub_le y n m)
              (qLe_of_eq (qAdd_comm (qUnitFrac n) (qUnitFrac m))))
      | inr hn =>
        rw [hm.1, hn.1]
        exact x.reg m n

/-- **M139-2b: 左上界（rLe）**。 -/
theorem rLe_max_left (x y : RReal) : rLe x (rmax x y) := by
  intro n
  show qLe (x.seq n) (qAdd (qMax (x.seq n) (y.seq n))
    (qAdd (qUnitFrac n) (qUnitFrac n)))
  exact qLe_pad n (qLe_max_left (x.seq n) (y.seq n))

/-- **M139-2c: 右上界（rLe）**。 -/
theorem rLe_max_right (x y : RReal) : rLe y (rmax x y) := by
  intro n
  show qLe (y.seq n) (qAdd (qMax (x.seq n) (y.seq n))
    (qAdd (qUnitFrac n) (qUnitFrac n)))
  exact qLe_pad n (qLe_max_right (x.seq n) (y.seq n))

/-- **M139-2d: 最小上界性（rLe）** — 点ごとに qMax_le。 -/
theorem rmax_least {x y z : RReal} (h1 : rLe x z) (h2 : rLe y z) :
    rLe (rmax x y) z := by
  intro n
  show qLe (qMax (x.seq n) (y.seq n))
    (qAdd (z.seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))
  exact qMax_le (h1 n) (h2 n)

/-! ## M139-3: 実数値体積理論 -/

/-- **M139-3a: 実数値体積理論** — M5 `VolumeTheory` の鏡映で、
    log-volume が Int でなく構成的 ℝ に値を取る。 -/
structure RealVolumeTheory where
  Region : Type
  /-- 包含 ⊆。 -/
  le : Region → Region → Prop
  le_refl : ∀ r, le r r
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  /-- 正則包（holomorphic hull / join）。 -/
  hull : Region → Region → Region
  le_hull_left : ∀ a b, le a (hull a b)
  le_hull_right : ∀ a b, le b (hull a b)
  hull_least : ∀ {a b c}, le a c → le b c → le (hull a b) c
  /-- procession 正規化 log-volume（実数値）。 -/
  vol : Region → RReal
  /-- 体積の単調性（rLe）。 -/
  vol_mono : ∀ {a b}, le a b → rLe (vol a) (vol b)

/-- **M139-3b: ℝ モデル** — Region = ℝ・包含 = rLe・正則包 = rmax・
    vol = id。体積値そのものを領域とする M5-4 のモデルの実数版。 -/
def realVolumeTheory : RealVolumeTheory where
  Region := RReal
  le := rLe
  le_refl := rLe_refl
  le_trans := fun h1 h2 => rLe_trans h1 h2
  hull := rmax
  le_hull_left := rLe_max_left
  le_hull_right := rLe_max_right
  hull_least := fun h1 h2 => rmax_least h1 h2
  vol := id
  vol_mono := fun h => h

/-- **M139-3c: 非空性**。 -/
theorem realVolumeTheory_consistent : Nonempty RealVolumeTheory :=
  ⟨realVolumeTheory⟩

/-! ## M139-4: 整数橋 -/

/-- **M139-4a: 埋め込み** ℤ → ℝ（定数列）。 -/
def intToReal (z : Int) : RReal :=
  qToReal (ratOfInt.map z)

/-- **M139-4b: 単調性**。 -/
theorem intToReal_mono {a b : Int} (h : a ≤ b) :
    rLe (intToReal a) (intToReal b) :=
  qToReal_mono (ratOfInt_le h)

/-- **定理 (M139-4c): 順序の反映（忠実性）** — 実数の不等式から
    整数の不等式へ降下（ε-消去 c = 2 + 代表計算）。 -/
theorem intToReal_reflect {a b : Int}
    (h : rLe (intToReal a) (intToReal b)) : a ≤ b := by
  have hq : qLe (ratOfInt.map a) (ratOfInt.map b) := by
    apply qLe_of_forall_add_frac 2
    intro m
    exact qLe_trans _ _ _ (h m)
      (qLe_add_two (qLe_refl (ratOfInt.map b)) (qFrac_add 1 1 m))
  have hab : a * 1 ≤ b * 1 := hq
  omega

/-- **M139-4d: Int 値体積理論の実数化** — vol を intToReal と合成。 -/
def RealVolumeTheory.ofInt (V : VolumeTheory) : RealVolumeTheory where
  Region := V.Region
  le := V.le
  le_refl := V.le_refl
  le_trans := V.le_trans
  hull := V.hull
  le_hull_left := V.le_hull_left
  le_hull_right := V.le_hull_right
  hull_least := V.hull_least
  vol := fun r => intToReal (V.vol r)
  vol_mono := fun h => intToReal_mono (V.vol_mono h)

/-! ## M139-5: 実数値多輻的表現と系3.12 の実数経由導出 -/

/-- **M139-5a: 定理3.11 出力仕様の実数値版** — M5 `MultiradialRep` の
    鏡映。体積側の言明（vol_hull・vol_q）が realEq になる。 -/
structure RealMultiradialRep (V : RealVolumeTheory) (s : Skeleton) where
  Ind : Type
  ind0 : Ind
  shell : V.Region
  image : Ind → V.Region
  image_in_shell : ∀ i, V.le (image i) shell
  hullTheta : V.Region
  image_in_hull : ∀ i, V.le (image i) hullTheta
  qRegion : V.Region
  q_realized : ∃ i, V.le qRegion (image i)
  vol_hull : realEq (V.vol hullTheta) (intToReal (-s.logTheta))
  vol_q : realEq (V.vol qRegion) (intToReal (-s.logq))

/-- 体積比較の核（M5-1 の実数版）: vol(q像) ≤ vol(Θ正則包)。 -/
theorem real_cor312_vol {V : RealVolumeTheory} {s : Skeleton}
    (M : RealMultiradialRep V s) :
    rLe (V.vol M.qRegion) (V.vol M.hullTheta) := by
  obtain ⟨i, hi⟩ := M.q_realized
  exact V.vol_mono (V.le_trans hi (M.image_in_hull i))

/-- **定理 (M139-5b): 系3.12 の実数経由導出（本丸）** —
    実数値の体積比較を realEq で −|log q| ≤ −|log Θ| の実数形に
    書き換え、intToReal の順序反映で整数の Cor312 に降下する。
    定理3.11 → 系3.12 の導出が実数の土俵を経由しても成立。 -/
theorem cor312_of_realMultiradial {V : RealVolumeTheory} {s : Skeleton}
    (M : RealMultiradialRep V s) : Cor312 s := by
  have h2 : rLe (intToReal (-s.logq)) (intToReal (-s.logTheta)) :=
    rLe_congr M.vol_q M.vol_hull (real_cor312_vol M)
  have h3 : -s.logq ≤ -s.logTheta := intToReal_reflect h2
  unfold Cor312
  omega

/-- **M139-5c: Int 値表現の持ち上げ** — M5 の `MultiradialRep` は
    実数化した体積理論の `RealMultiradialRep` にそのまま持ち上がる。 -/
def RealMultiradialRep.ofInt {V : VolumeTheory} {s : Skeleton}
    (M : MultiradialRep V s) :
    RealMultiradialRep (RealVolumeTheory.ofInt V) s where
  Ind := M.Ind
  ind0 := M.ind0
  shell := M.shell
  image := M.image
  image_in_shell := M.image_in_shell
  hullTheta := M.hullTheta
  image_in_hull := M.image_in_hull
  qRegion := M.qRegion
  q_realized := M.q_realized
  vol_hull := by
    show realEq (intToReal (V.vol M.hullTheta)) (intToReal (-s.logTheta))
    rw [M.vol_hull]
    exact realEq_refl _
  vol_q := by
    show realEq (intToReal (V.vol M.qRegion)) (intToReal (-s.logq))
    rw [M.vol_q]
    exact realEq_refl _

/-- **定理 (M139-5d): 完全パイプラインの実数版** — 実数値表現
    ＋ IUT IV の体積計算 ⟹ Szpiro 型不等式（M5-5 の実数経由再現）。 -/
theorem szpiro_of_realMultiradial {V : RealVolumeTheory} {s : Skeleton}
    (M : RealMultiradialRep V s) (comp : LogVolumeComputation s) :
    (comp.a - 1) * s.logq ≤ comp.err :=
  szpiro_of_cor312_precise s (cor312_of_realMultiradial M) comp

/-! ## M139-6: 充足可能性 -/

/-- **定理 (M139-6): 実数値インターフェースの充足可能性** —
    ℝ モデル上で `RealMultiradialRep` は充足できる（M5-4 の実数版。
    定理3.11 の実数値出力仕様そのものに形式的矛盾はない）。 -/
theorem realMultiradial_consistent :
    ∃ (V : RealVolumeTheory) (s : Skeleton),
      Nonempty (RealMultiradialRep V s) := by
  refine ⟨realVolumeTheory,
    { lstar := 2, hl := by omega, logq := 1, hq := by omega,
      logTheta := 1 }, ⟨?_⟩⟩
  exact
    { Ind := Unit, ind0 := (),
      shell := intToReal 0,
      image := fun _ => intToReal (-1),
      image_in_shell := fun _ => intToReal_mono (by omega),
      hullTheta := intToReal (-1),
      image_in_hull := fun _ => rLe_refl _,
      qRegion := intToReal (-1),
      q_realized := ⟨(), rLe_refl _⟩,
      vol_hull := realEq_refl _,
      vol_q := realEq_refl _ }

/-! ## M139-7: 総括 -/

/-- **M139-7a: 総括** — 実数値体積理論のデータ。 -/
structure RealVolumeTheoryData where
  /-- ℚ の max の法則。 -/
  qmax_left : ∀ a b, qLe a (qMax a b)
  qmax_right : ∀ a b, qLe b (qMax a b)
  qmax_le : ∀ {a b c}, qLe a c → qLe b c → qLe (qMax a b) c
  /-- ℝ の max（正則包）の法則。 -/
  rmax_left : ∀ x y, rLe x (rmax x y)
  rmax_right : ∀ x y, rLe y (rmax x y)
  rmax_le : ∀ {x y z}, rLe x z → rLe y z → rLe (rmax x y) z
  /-- 実数値体積理論の非空性。 -/
  real_theory : Nonempty RealVolumeTheory
  /-- Int 値体積理論の実数化。 -/
  of_int : VolumeTheory → RealVolumeTheory
  /-- 系3.12 の実数経由導出。 -/
  descent : ∀ {V : RealVolumeTheory} {s : Skeleton},
    RealMultiradialRep V s → Cor312 s
  /-- Int 値表現の持ち上げ。 -/
  lift : ∀ {V : VolumeTheory} {s : Skeleton}, MultiradialRep V s →
    Nonempty (RealMultiradialRep (RealVolumeTheory.ofInt V) s)
  /-- 充足可能性。 -/
  consistent : ∃ (V : RealVolumeTheory) (s : Skeleton),
    Nonempty (RealMultiradialRep V s)

/-- **M139-7b: witness**。 -/
def realVolumeTheoryData : RealVolumeTheoryData where
  qmax_left := qLe_max_left
  qmax_right := qLe_max_right
  qmax_le := qMax_le
  rmax_left := rLe_max_left
  rmax_right := rLe_max_right
  rmax_le := rmax_least
  real_theory := realVolumeTheory_consistent
  of_int := RealVolumeTheory.ofInt
  descent := cor312_of_realMultiradial
  lift := fun M => ⟨RealMultiradialRep.ofInt M⟩
  consistent := realMultiradial_consistent

/-- **M139-7c: 存在**。 -/
theorem realVolumeTheoryData_exists : Nonempty RealVolumeTheoryData :=
  ⟨realVolumeTheoryData⟩

end IUT
