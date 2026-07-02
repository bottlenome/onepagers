/-
# M128: 実数の完備性 — 対角極限

柱C（issue #37）ℝ 構成の最終解析部品。**実数の正則列**
（|X_m − X_n| ≤ 1/(m+1) + 1/(n+1)、witness 形 = 各成分に固有の
揺らぎ 2/(j+1) を許した一様評価）は極限を持つ:

  Y_n := (X_{4n+3}).seq (4n+3)  （対角、4 倍加速で正則性が閉じる）

  * M128-1 `qAbs_sub_comm` — |a−b| = |b−a|
  * M128-2 `IsCauchyReals` — 実数列の正則性（witness 形）
  * M128-3 `rlim` — 対角極限の構成（正則性: 4u_{4m+3} + 2u_{4n+3}
    ≤ u_m + u_n）
  * M128-4 `rlim_close` — **収束（本丸1）**: |Y − X_m| ≤ 1/(m+1)
    （witness 形: ∀j, |Y_j − (X_m)_j| ≤ u_m + 2u_j）
  * M128-5 `rlim_unique` — **極限の一意性（本丸2)**: 同じ収束評価を
    満たす Z は Y に ≈（k = m の 3 点分割 + ε-消去 c = 8）
  * M128-6 `RealCompleteData` — 総括

これで ℝ は ℚ 体（M115F）→ 加法群（M117F）→ 床・上界（M120F）→
乗法（M123F）→ 順序・共推移性（M125）→ 絶対値（M127F）→
**完備性（本層）** まで到達 — C-1（実数値 log-volume）の解析基盤が
揃った。

正直な限定: 「任意のコーシー列」でなく正則列（modulus 固定形）に
対する完備性 — Bishop 流ではこれが標準（一般 modulus からの正則化
は添字の付け替えで、次層の整備課題）。

全て選択公理不使用。
-/
import IUT.RealOrder

namespace IUT

/-! ## M128-1: 補助 -/

/-- |a − b| = |b − a|。 -/
theorem qAbs_sub_comm (a b : QRat) :
    qAbs (qAdd a (qNeg b)) = qAbs (qAdd b (qNeg a)) := by
  rw [← qNeg_sub a b, qAbs_neg]

/-! ## M128-2: 実数の正則列 -/

/-- **M128-2: 実数列の正則性（witness 形）** —
    ∀j, |（X_m)_j − (X_n)_j| ≤ (1/(m+1) + 1/(n+1)) + 2/(j+1)
    （末項は各実数の固有の揺らぎ）。 -/
def IsCauchyReals (X : Nat → RReal) : Prop :=
  ∀ m n j, qLe (qAbs (qAdd ((X m).seq j) (qNeg ((X n).seq j))))
    (qAdd (qAdd (qUnitFrac m) (qUnitFrac n))
      (qAdd (qUnitFrac j) (qUnitFrac j)))

/-! ## M128-3: 対角極限 -/

/-- **M128-3: 対角極限** Y_n = (X_{4n+3})_{4n+3}
    （4 倍加速: 4u_{4m+3} + 2u_{4n+3} = u_m + u_n/2 ≤ u_m + u_n）。 -/
def rlim (X : Nat → RReal) (hX : IsCauchyReals X) : RReal where
  seq := fun n => (X (4 * n + 3)).seq (4 * n + 3)
  reg := by
    intro m n
    -- 分割: |Y_m − Y_n| ≤ |(X sm)_sm − (X sn)_sm| + |(X sn)_sm − (X sn)_sn|
    have t1 := qAbs_sub_split ((X (4 * m + 3)).seq (4 * m + 3))
      ((X (4 * n + 3)).seq (4 * m + 3))
      ((X (4 * n + 3)).seq (4 * n + 3))
    have b1 := hX (4 * m + 3) (4 * n + 3) (4 * m + 3)
    have b2 := (X (4 * n + 3)).reg (4 * m + 3) (4 * n + 3)
    have total := qLe_trans _ _ _ t1 (qLe_add_two b1 b2)
    apply qLe_trans _ _ _ total
    -- S = [(a+b)+(a+a)] + (a+b)、a := u_{sm}、b := u_{sn}
    -- → ((a+a)+a) + ((b+a)+b) → (F3sm + …) 折り畳み
    have e1 : qAdd (qAdd (qAdd (qUnitFrac (4 * m + 3)) (qUnitFrac (4 * n + 3)))
          (qAdd (qUnitFrac (4 * m + 3)) (qUnitFrac (4 * m + 3))))
        (qAdd (qUnitFrac (4 * m + 3)) (qUnitFrac (4 * n + 3)))
        = qAdd (qAdd (qAdd (qUnitFrac (4 * m + 3)) (qUnitFrac (4 * m + 3)))
            (qUnitFrac (4 * m + 3)))
          (qAdd (qAdd (qUnitFrac (4 * n + 3)) (qUnitFrac (4 * m + 3)))
            (qUnitFrac (4 * n + 3))) := by
      rw [qAdd_swap_mid (qUnitFrac (4 * m + 3)) (qUnitFrac (4 * n + 3))
          (qUnitFrac (4 * m + 3)) (qUnitFrac (4 * m + 3)),
        qAdd_swap_mid (qAdd (qUnitFrac (4 * m + 3)) (qUnitFrac (4 * m + 3)))
          (qAdd (qUnitFrac (4 * n + 3)) (qUnitFrac (4 * m + 3)))
          (qUnitFrac (4 * m + 3)) (qUnitFrac (4 * n + 3))]
    apply qLe_trans _ _ _ (qLe_of_eq e1)
    -- 左: 3u_{sm} ≤ F3sm、右: (u_{sn}+u_{sm})+u_{sn} → F2sn + u_{sm}
    have hL : qLe (qAdd (qAdd (qUnitFrac (4 * m + 3)) (qUnitFrac (4 * m + 3)))
        (qUnitFrac (4 * m + 3))) (qFrac 3 (4 * m + 3)) :=
      qLe_trans _ _ _
        (qLe_add_two (qFrac_add 1 1 (4 * m + 3)) (qLe_refl _))
        (qFrac_add 2 1 (4 * m + 3))
    have eR : qAdd (qAdd (qUnitFrac (4 * n + 3)) (qUnitFrac (4 * m + 3)))
        (qUnitFrac (4 * n + 3))
        = qAdd (qAdd (qUnitFrac (4 * n + 3)) (qUnitFrac (4 * n + 3)))
          (qUnitFrac (4 * m + 3)) := by
      rw [qAdd_assoc (qUnitFrac (4 * n + 3)) (qUnitFrac (4 * m + 3))
          (qUnitFrac (4 * n + 3)),
        qAdd_comm (qUnitFrac (4 * m + 3)) (qUnitFrac (4 * n + 3)),
        ← qAdd_assoc (qUnitFrac (4 * n + 3)) (qUnitFrac (4 * n + 3))
          (qUnitFrac (4 * m + 3))]
    have hR : qLe (qAdd (qAdd (qUnitFrac (4 * n + 3)) (qUnitFrac (4 * m + 3)))
        (qUnitFrac (4 * n + 3)))
        (qAdd (qFrac 2 (4 * n + 3)) (qUnitFrac (4 * m + 3))) :=
      qLe_trans _ _ _ (qLe_of_eq eR)
        (qLe_add_two (qFrac_add 1 1 (4 * n + 3)) (qLe_refl _))
    apply qLe_trans _ _ _ (qLe_add_two hL hR)
    -- F3sm + (F2sn + u_{sm}) = (F3sm + u_{sm}) + F2sn ≤ F4sm + F2sn ≤ u_m + u_n
    have e2 : qAdd (qFrac 3 (4 * m + 3))
        (qAdd (qFrac 2 (4 * n + 3)) (qUnitFrac (4 * m + 3)))
        = qAdd (qAdd (qFrac 3 (4 * m + 3)) (qUnitFrac (4 * m + 3)))
          (qFrac 2 (4 * n + 3)) := by
      rw [qAdd_comm (qFrac 2 (4 * n + 3)) (qUnitFrac (4 * m + 3)),
        ← qAdd_assoc (qFrac 3 (4 * m + 3)) (qUnitFrac (4 * m + 3))
          (qFrac 2 (4 * n + 3))]
    apply qLe_trans _ _ _ (qLe_of_eq e2)
    exact qLe_add_two
      (qLe_trans _ _ _ (qFrac_add 3 1 (4 * m + 3)) (qFrac_le (by omega)))
      (qFrac_le (by omega))

/-! ## M128-4: 収束 -/

/-- **定理 (M128-4): 収束（本丸1）** — 極限は各 X_m に 1/(m+1) 以内
    （witness 形: ∀j, |Y_j − (X_m)_j| ≤ u_m + 2u_j）。 -/
theorem rlim_close (X : Nat → RReal) (hX : IsCauchyReals X)
    (m j : Nat) :
    qLe (qAbs (qAdd ((rlim X hX).seq j) (qNeg ((X m).seq j))))
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac j) (qUnitFrac j))) := by
  -- 分割: |Y_j − (X m)_j| ≤ |(X sj)_sj − (X m)_sj| + |(X m)_sj − (X m)_j|
  have t1 := qAbs_sub_split ((X (4 * j + 3)).seq (4 * j + 3))
    ((X m).seq (4 * j + 3)) ((X m).seq j)
  have b1 := hX (4 * j + 3) m (4 * j + 3)
  have b2 := (X m).reg (4 * j + 3) j
  have total := qLe_trans _ _ _ t1 (qLe_add_two b1 b2)
  apply qLe_trans _ _ _ total
  -- S = [(a+u_m)+(a+a)] + (a+u_j)、a := u_{sj}
  -- → ((a+a)+a) + ((u_m+a)+u_j) → F3sj + (u_m + (a+u_j))
  have e1 : qAdd (qAdd (qAdd (qUnitFrac (4 * j + 3)) (qUnitFrac m))
        (qAdd (qUnitFrac (4 * j + 3)) (qUnitFrac (4 * j + 3))))
      (qAdd (qUnitFrac (4 * j + 3)) (qUnitFrac j))
      = qAdd (qAdd (qAdd (qUnitFrac (4 * j + 3)) (qUnitFrac (4 * j + 3)))
          (qUnitFrac (4 * j + 3)))
        (qAdd (qAdd (qUnitFrac m) (qUnitFrac (4 * j + 3)))
          (qUnitFrac j)) := by
    rw [qAdd_swap_mid (qUnitFrac (4 * j + 3)) (qUnitFrac m)
        (qUnitFrac (4 * j + 3)) (qUnitFrac (4 * j + 3)),
      qAdd_swap_mid (qAdd (qUnitFrac (4 * j + 3)) (qUnitFrac (4 * j + 3)))
        (qAdd (qUnitFrac m) (qUnitFrac (4 * j + 3)))
        (qUnitFrac (4 * j + 3)) (qUnitFrac j)]
  apply qLe_trans _ _ _ (qLe_of_eq e1)
  have hL : qLe (qAdd (qAdd (qUnitFrac (4 * j + 3)) (qUnitFrac (4 * j + 3)))
      (qUnitFrac (4 * j + 3))) (qFrac 3 (4 * j + 3)) :=
    qLe_trans _ _ _
      (qLe_add_two (qFrac_add 1 1 (4 * j + 3)) (qLe_refl _))
      (qFrac_add 2 1 (4 * j + 3))
  have eR : qAdd (qAdd (qUnitFrac m) (qUnitFrac (4 * j + 3))) (qUnitFrac j)
      = qAdd (qUnitFrac m) (qAdd (qUnitFrac (4 * j + 3)) (qUnitFrac j)) :=
    qAdd_assoc _ _ _
  apply qLe_trans _ _ _
    (qLe_add_two hL (qLe_of_eq eR))
  -- F3sj + (u_m + (u_sj + u_j)) = u_m + ((F3sj + u_sj) + u_j)
  have e2 : qAdd (qFrac 3 (4 * j + 3))
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac (4 * j + 3)) (qUnitFrac j)))
      = qAdd (qUnitFrac m)
        (qAdd (qAdd (qFrac 3 (4 * j + 3)) (qUnitFrac (4 * j + 3)))
          (qUnitFrac j)) := by
    rw [← qAdd_assoc (qFrac 3 (4 * j + 3)) (qUnitFrac m)
        (qAdd (qUnitFrac (4 * j + 3)) (qUnitFrac j)),
      qAdd_comm (qFrac 3 (4 * j + 3)) (qUnitFrac m),
      qAdd_assoc (qUnitFrac m) (qFrac 3 (4 * j + 3))
        (qAdd (qUnitFrac (4 * j + 3)) (qUnitFrac j)),
      ← qAdd_assoc (qFrac 3 (4 * j + 3)) (qUnitFrac (4 * j + 3))
        (qUnitFrac j)]
  apply qLe_trans _ _ _ (qLe_of_eq e2)
  exact qLe_add_two (qLe_refl (qUnitFrac m))
    (qLe_add_two
      (qLe_trans _ _ _ (qFrac_add 3 1 (4 * j + 3)) (qFrac_le (by omega)))
      (qLe_refl (qUnitFrac j)))

/-! ## M128-5: 一意性 -/

/-- **定理 (M128-5): 極限の一意性（本丸2）** — 同じ収束評価を満たす
    Z は対角極限に ≈（3 点分割 k = m + ε-消去 c = 8）。 -/
theorem rlim_unique (X : Nat → RReal) (hX : IsCauchyReals X)
    (Z : RReal)
    (hZ : ∀ m j, qLe (qAbs (qAdd (Z.seq j) (qNeg ((X m).seq j))))
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac j) (qUnitFrac j)))) :
    realEq (rlim X hX) Z := by
  intro n
  apply qLe_of_forall_add_frac 8
  intro m
  -- |Y_n − Z_n| ≤ |Y_n − Y_m| + |Y_m − Z_m| + |Z_m − Z_n|
  have t1 := qAbs_sub_split ((rlim X hX).seq n) ((rlim X hX).seq m)
    (Z.seq n)
  have t2 := qAbs_sub_split ((rlim X hX).seq m) (Z.seq m) (Z.seq n)
  -- |Y_m − Z_m| ≤ |Y_m − (X m)_m| + |(X m)_m − Z_m| ≤ 3u_m + 3u_m
  have c1 := rlim_close X hX m m
  have c2 : qLe (qAbs (qAdd ((X m).seq m) (qNeg (Z.seq m))))
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac m) (qUnitFrac m))) := by
    rw [qAbs_sub_comm]
    exact hZ m m
  have t3 := qLe_trans _ _ _
    (qAbs_sub_split ((rlim X hX).seq m) ((X m).seq m) (Z.seq m))
    (qLe_add_two c1 c2)
  -- 各項: |Y_n − Y_m| ≤ u_n + u_m、|Z_m − Z_n| ≤ u_m + u_n
  have r1 := (rlim X hX).reg n m
  have r2 := Z.reg m n
  -- 合成: D ≤ (u_n+u_m) + ([(u_m+2u_m)+(u_m+2u_m)] + (u_m+u_n))
  have total := qLe_trans _ _ _ t1
    (qLe_add_two r1 (qLe_trans _ _ _ t2 (qLe_add_two t3 r2)))
  apply qLe_trans _ _ _ total
  -- 濃縮: 全体 ≤ (u_n + u_n) + F8m
  -- 内側 [(u_m+(u_m+u_m))+(u_m+(u_m+u_m))] ≤ F3m+F3m ≤ F6m
  have hmid : qLe (qAdd
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac m) (qUnitFrac m)))
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac m) (qUnitFrac m))))
      (qFrac 6 m) := by
    have h3 : qLe (qAdd (qUnitFrac m) (qAdd (qUnitFrac m) (qUnitFrac m)))
        (qFrac 3 m) :=
      qLe_trans _ _ _
        (qLe_add_two (qLe_refl _) (qFrac_add 1 1 m))
        (qFrac_add 1 2 m)
    exact qLe_trans _ _ _ (qLe_add_two h3 h3) (qFrac_add 3 3 m)
  -- (u_n+u_m) + (F6m + (u_m+u_n)) → (u_n+u_n) + (u_m + (F6m + u_m))
  have step1 : qLe (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
      (qAdd (qAdd
        (qAdd (qUnitFrac m) (qAdd (qUnitFrac m) (qUnitFrac m)))
        (qAdd (qUnitFrac m) (qAdd (qUnitFrac m) (qUnitFrac m))))
        (qAdd (qUnitFrac m) (qUnitFrac n))))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
        (qAdd (qFrac 6 m) (qAdd (qUnitFrac m) (qUnitFrac n)))) :=
    qLe_add_two (qLe_refl _) (qLe_add_two hmid (qLe_refl _))
  apply qLe_trans _ _ _ step1
  -- 並べ替え: (u_n+u_m)+(F6m+(u_m+u_n)) = (u_n+u_n)+((u_m+F6m)+u_m)
  have e3 : qAdd (qAdd (qUnitFrac n) (qUnitFrac m))
      (qAdd (qFrac 6 m) (qAdd (qUnitFrac m) (qUnitFrac n)))
      = qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
        (qAdd (qUnitFrac m) (qAdd (qFrac 6 m) (qUnitFrac m))) := by
    rw [qAdd_comm (qUnitFrac m) (qUnitFrac n),
      ← qAdd_assoc (qFrac 6 m) (qUnitFrac n) (qUnitFrac m),
      qAdd_comm (qFrac 6 m) (qUnitFrac n),
      qAdd_assoc (qUnitFrac n) (qFrac 6 m) (qUnitFrac m),
      qAdd_swap_mid (qUnitFrac n) (qUnitFrac m)
        (qUnitFrac n) (qAdd (qFrac 6 m) (qUnitFrac m))]
  apply qLe_trans _ _ _ (qLe_of_eq e3)
  -- u_m + (F6m + u_m) ≤ F8m
  refine qLe_add_two (qLe_refl _) ?_
  exact qLe_trans _ _ _
    (qLe_add_two (qLe_refl (qUnitFrac m)) (qFrac_add 6 1 m))
    (qFrac_add 1 7 m)

/-! ## M128-6: 総括 -/

/-- **M128-6a: 総括** — 完備性データ。 -/
structure RealCompleteData where
  /-- 対角極限の存在（構成そのもの）。 -/
  lim : (X : Nat → RReal) → IsCauchyReals X → RReal
  /-- 収束: |lim − X_m| ≤ 1/(m+1)（witness 形）。 -/
  close : ∀ (X : Nat → RReal) (hX : IsCauchyReals X) (m j : Nat),
    qLe (qAbs (qAdd ((lim X hX).seq j) (qNeg ((X m).seq j))))
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac j) (qUnitFrac j)))
  /-- 一意性。 -/
  unique : ∀ (X : Nat → RReal) (hX : IsCauchyReals X) (Z : RReal),
    (∀ m j, qLe (qAbs (qAdd (Z.seq j) (qNeg ((X m).seq j))))
      (qAdd (qUnitFrac m) (qAdd (qUnitFrac j) (qUnitFrac j)))) →
    realEq (lim X hX) Z

/-- **M128-6b: witness**。 -/
def realCompleteData : RealCompleteData where
  lim := rlim
  close := rlim_close
  unique := rlim_unique

/-- **M128-6c: 存在**。 -/
theorem realComplete_exists : Nonempty RealCompleteData :=
  ⟨realCompleteData⟩

end IUT
