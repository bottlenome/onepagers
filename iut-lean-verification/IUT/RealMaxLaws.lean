/-
# M140F: 実数 max の代数法則 — 正則包 rmax の可換・冪等・結合・congruence

M139 で構成した qMax（ℚ の max）と rmax（ℝ の max = 正則包）の
代数法則を検証する。M139 は rmax の realEq 両立（congruence）を
次層に委ねると正直申告していた — 本モジュールがその負債を返済する:

  * M140F-1 `qMax_comm`・`qMax_idem`・`qMax_assoc` — ℚ の max の
    可換・冪等・結合（いずれも qLe_antisym + 上界・最小上界性のみ、
    qMax_cases の場合分けすら不要な純 order-theoretic 証明）
  * M140F-2 `rmax_comm`・`rmax_idem`・`rmax_assoc` — ℝ の max の
    可換・冪等・結合（realEq の意味で。点ごとに M140F-1 を
    `realEq_of_seq_eq` で持ち上げる — rmax は点ごと max なので
    列レベルでは**厳密等式**が成り立つ）
  * M140F-3 **本丸 `rmax_congr`** — rmax の realEq 両立:
    x ≈ x'・y ≈ y' ⟹ rmax x y ≈ rmax x' y'。M139 の rmax の
    正則性証明と同型の 4 分岐（qMax_cases × 2）。対角 2 分岐は
    仮定そのまま、cross 分岐は片腕優越の連鎖
    y_n − x'_n ≤ y_n − y'_n ≤ |y_n − y'_n| ≤ 2u_n で閉じる
  * M140F-4 `RealMaxLawsData` — 総括

意義: M139 の正則包 rmax が realEq 商の上で well-defined な
join 半束（可換・冪等・結合な二項演算）をなすことの検証。
柱D の実数値体積理論の hull 演算の代数的健全性がこれで担保される。

正直な限定: rmax と rLe の完全な半束順序同値
rLe x y ↔ realEq (rmax x y) y は rLe の反対称律（ε-消去）経由の
議論を要するため次層に委ねる。また本モジュールの結合律・可換律は
列レベルの厳密等式からの持ち上げであり、realEq 商上の抽象半束
構造（商型の構成）自体はここでは作らない。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealVolumeTheory

namespace IUT

/-! ## M140F-1: ℚ の max の代数法則 -/

/-- **M140F-1a: 可換律** — 両向きとも最小上界性 + 上界性。 -/
theorem qMax_comm (a b : QRat) : qMax a b = qMax b a :=
  qLe_antisym (qMax a b) (qMax b a)
    (qMax_le (qLe_max_right b a) (qLe_max_left b a))
    (qMax_le (qLe_max_right a b) (qLe_max_left a b))

/-- **M140F-1b: 冪等律**。 -/
theorem qMax_idem (a : QRat) : qMax a a = a :=
  qLe_antisym (qMax a a) a
    (qMax_le (qLe_refl a) (qLe_refl a))
    (qLe_max_left a a)

/-- **M140F-1c: 結合律** — 入れ子の qMax_le と qLe_trans の張り合わせ。 -/
theorem qMax_assoc (a b c : QRat) :
    qMax (qMax a b) c = qMax a (qMax b c) :=
  qLe_antisym (qMax (qMax a b) c) (qMax a (qMax b c))
    (qMax_le
      (qMax_le (qLe_max_left a (qMax b c))
        (qLe_trans b (qMax b c) (qMax a (qMax b c))
          (qLe_max_left b c) (qLe_max_right a (qMax b c))))
      (qLe_trans c (qMax b c) (qMax a (qMax b c))
        (qLe_max_right b c) (qLe_max_right a (qMax b c))))
    (qMax_le
      (qLe_trans a (qMax a b) (qMax (qMax a b) c)
        (qLe_max_left a b) (qLe_max_left (qMax a b) c))
      (qMax_le
        (qLe_trans b (qMax a b) (qMax (qMax a b) c)
          (qLe_max_right a b) (qLe_max_left (qMax a b) c))
        (qLe_max_right (qMax a b) c)))

/-! ## M140F-2: ℝ の max の代数法則（realEq） -/

/-- **M140F-2a: 可換律** — 点ごとに qMax_comm（列レベルの厳密等式）。 -/
theorem rmax_comm (x y : RReal) : realEq (rmax x y) (rmax y x) :=
  realEq_of_seq_eq (fun n => qMax_comm (x.seq n) (y.seq n))

/-- **M140F-2b: 冪等律**。 -/
theorem rmax_idem (x : RReal) : realEq (rmax x x) x :=
  realEq_of_seq_eq (fun n => qMax_idem (x.seq n))

/-- **M140F-2c: 結合律**。 -/
theorem rmax_assoc (x y z : RReal) :
    realEq (rmax (rmax x y) z) (rmax x (rmax y z)) :=
  realEq_of_seq_eq (fun n => qMax_assoc (x.seq n) (y.seq n) (z.seq n))

/-! ## M140F-3: 本丸 — rmax の realEq 両立（congruence） -/

/-- **M140F-3: congruence** — x ≈ x'・y ≈ y' なら
    rmax x y ≈ rmax x' y'。M139 の rmax の正則性証明と同型の
    4 分岐: 対角は仮定そのまま、cross は片腕優越の連鎖
    y_n − x'_n ≤ y_n − y'_n ≤ |y_n − y'_n| ≤ 2u_n（逆側は
    qNeg_sub で腕を張り替えて qAbs_sub_comm 経由）。 -/
theorem rmax_congr {x x' y y' : RReal}
    (hx : realEq x x') (hy : realEq y y') :
    realEq (rmax x y) (rmax x' y') := by
  intro n
  show qLe (qAbs (qAdd (qMax (x.seq n) (y.seq n))
      (qNeg (qMax (x'.seq n) (y'.seq n)))))
    (qAdd (qUnitFrac n) (qUnitFrac n))
  cases qMax_cases (x.seq n) (y.seq n) with
  | inl hm =>
    cases qMax_cases (x'.seq n) (y'.seq n) with
    | inl hn =>
      rw [hm.1, hn.1]
      exact hy n
    | inr hn =>
      -- 左 = y_n・右 = x'_n（y'_n ≤ x'_n・x_n ≤ y_n）
      rw [hm.1, hn.1]
      apply qAbs_le_both
      · -- y_n − x'_n ≤ y_n − y'_n ≤ |y_n − y'_n| ≤ 2u_n
        exact qLe_trans _ _ _
          (qLe_add_two (qLe_refl (y.seq n)) (qLe_neg_flip hn.2))
          (qLe_trans _ _ _ (qLe_self_abs _) (hy n))
      · -- x'_n − y_n ≤ x'_n − x_n ≤ |x'_n − x_n| = |x_n − x'_n| ≤ 2u_n
        rw [qNeg_sub]
        exact qLe_trans _ _ _
          (qLe_add_two (qLe_refl (x'.seq n)) (qLe_neg_flip hm.2))
          (qLe_trans _ _ _ (qLe_self_abs _)
            (qLe_trans _ _ _
              (qLe_of_eq (qAbs_sub_comm (x'.seq n) (x.seq n)))
              (hx n)))
  | inr hm =>
    cases qMax_cases (x'.seq n) (y'.seq n) with
    | inl hn =>
      -- 左 = x_n・右 = y'_n（x'_n ≤ y'_n・y_n ≤ x_n）
      rw [hm.1, hn.1]
      apply qAbs_le_both
      · -- x_n − y'_n ≤ x_n − x'_n ≤ |x_n − x'_n| ≤ 2u_n
        exact qLe_trans _ _ _
          (qLe_add_two (qLe_refl (x.seq n)) (qLe_neg_flip hn.2))
          (qLe_trans _ _ _ (qLe_self_abs _) (hx n))
      · -- y'_n − x_n ≤ y'_n − y_n ≤ |y'_n − y_n| = |y_n − y'_n| ≤ 2u_n
        rw [qNeg_sub]
        exact qLe_trans _ _ _
          (qLe_add_two (qLe_refl (y'.seq n)) (qLe_neg_flip hm.2))
          (qLe_trans _ _ _ (qLe_self_abs _)
            (qLe_trans _ _ _
              (qLe_of_eq (qAbs_sub_comm (y'.seq n) (y.seq n)))
              (hy n)))
    | inr hn =>
      rw [hm.1, hn.1]
      exact hx n

/-! ## M140F-4: 総括 -/

/-- **M140F-4a: 総括** — qMax/rmax の代数法則パッケージ。 -/
structure RealMaxLawsData where
  /-- ℚ: 可換。 -/
  qmax_comm : ∀ a b, qMax a b = qMax b a
  /-- ℚ: 冪等。 -/
  qmax_idem : ∀ a, qMax a a = a
  /-- ℚ: 結合。 -/
  qmax_assoc : ∀ a b c, qMax (qMax a b) c = qMax a (qMax b c)
  /-- ℝ: 可換（realEq）。 -/
  rmax_comm : ∀ x y, realEq (rmax x y) (rmax y x)
  /-- ℝ: 冪等（realEq）。 -/
  rmax_idem : ∀ x, realEq (rmax x x) x
  /-- ℝ: 結合（realEq）。 -/
  rmax_assoc : ∀ x y z,
    realEq (rmax (rmax x y) z) (rmax x (rmax y z))
  /-- ℝ: congruence — rmax は realEq 商上 well-defined。 -/
  rmax_congr : ∀ {x x' y y' : RReal},
    realEq x x' → realEq y y' → realEq (rmax x y) (rmax x' y')

/-- **M140F-4b: witness**。 -/
def realMaxLawsData : RealMaxLawsData where
  qmax_comm := qMax_comm
  qmax_idem := qMax_idem
  qmax_assoc := qMax_assoc
  rmax_comm := rmax_comm
  rmax_idem := rmax_idem
  rmax_assoc := rmax_assoc
  rmax_congr := rmax_congr

/-- **M140F-4c: 存在**。 -/
theorem realMaxLaws_exists : Nonempty RealMaxLawsData :=
  ⟨realMaxLawsData⟩

end IUT
