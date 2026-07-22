/-
# M136F: 順序の完全整合 — ¬rLt → rLe の δ-論法

柱C（issue #37）。M130 の正直申告解消。rLe ⟺ ¬rLt の双方向で
Bishop 順序の標準的整合が完結。比較 margin 3/(N+1)・
witness m = 4N+3 の粒度設計:

各添字 n のゴール x_n ≤ y_n + 2u_n を ∀N の ε-形（+5/(N+1)）で
示し、qLe_total による高精度比較 x_N vs y_N + 3/(N+1) で分岐:

  * 上側: 望遠鏡分解 x_n − y_n = (x_n − x_N) + ((x_N − y_N) +
    (y_N − y_n)) と定数濃縮（2u_N + F3N ≤ F5N）、ε-消去 c = 5
  * 下側: gap 3u_N から witness m = 4N+3 で rLt y x を構成して
    仮定 ¬rLt y x と矛盾。IsPos の要求 2/(4N+4) = u_N/2 に対し
    伝播下界は 3u_N − 2u_N − 2u_{8N+7} = 3u_N/4 — 分母 8N+8 の
    族（F4 + F9 + F9 = F22 ≤ F3N ⟺ 22(N+1) ≤ 24(N+1)）で線形化

  * M136F-1 **本丸 `not_lt_le`** — ¬rLt y x → rLe x y
  * M136F-2 `le_iff_not_lt` — rLe x y ↔ ¬rLt y x（→ は M130 の
    rLt_not_le、← は M136F-1）
  * M136F-3 `lt_iff_not_le` — rLt y x → ¬rLe x y（M130 再輸出）
  * M136F-4 `RealOrderCompleteData` — 総括

正直な限定: 逆向き ¬rLe x y → rLt y x は ¬¬rLt からの復元
（二重否定除去相当）を要するため排中律なしでは対象外。
le_iff_not_lt の iff が構成的に取れる全内容。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealLe

namespace IUT

/-! ## M136F-1: 本丸 — ¬rLt → rLe -/

/-- **定理 (M136F-1): 順序の完全整合（δ-論法）** — ¬(y < x) なら
    x ≤ y。各添字 n で ε-形（qLe_of_forall_add_frac c = 5）にし、
    比較点 N で x_N vs y_N + 3/(N+1) を qLe_total 分岐。下側は
    witness m = 4N+3 で rLt y x を構成して仮定と矛盾。 -/
theorem not_lt_le {x y : RReal} (h : ¬ rLt y x) : rLe x y := by
  intro n
  apply qLe_of_forall_add_frac 5
  intro N
  cases qLe_total (x.seq N) (qAdd (y.seq N) (qFrac 3 N)) with
  | inl hA =>
    -- 上側: 望遠鏡 x_n − y_n = (x_n − x_N) + ((x_N − y_N) + (y_N − y_n))
    have t1 := reg_sub_le x n N
    have t2 : qLe (qAdd (x.seq N) (qNeg (y.seq N))) (qFrac 3 N) :=
      qSub_le_of_le hA
    have t3 := reg_sub_le y N n
    have esplit : qAdd (x.seq n) (qNeg (y.seq n))
        = qAdd (qAdd (x.seq n) (qNeg (x.seq N)))
          (qAdd (qAdd (x.seq N) (qNeg (y.seq N)))
            (qAdd (y.seq N) (qNeg (y.seq n)))) := by
      rw [← qSub_split (x.seq N) (y.seq N) (y.seq n),
        ← qSub_split (x.seq n) (x.seq N) (y.seq n)]
    have total : qLe (qAdd (x.seq n) (qNeg (y.seq n)))
        (qAdd (qAdd (qUnitFrac n) (qUnitFrac N))
          (qAdd (qFrac 3 N) (qAdd (qUnitFrac N) (qUnitFrac n)))) :=
      qLe_trans _ _ _ (qLe_of_eq esplit)
        (qLe_add_two t1 (qLe_add_two t2 t3))
    -- 定数側の並べ替え: (u_n+u_N) + (F3N + (u_N+u_n))
    --   = (u_n+u_n) + ((u_N+u_N) + F3N)
    have e1 : qAdd (qAdd (qUnitFrac n) (qUnitFrac N))
        (qAdd (qFrac 3 N) (qAdd (qUnitFrac N) (qUnitFrac n)))
        = qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
          (qAdd (qAdd (qUnitFrac N) (qUnitFrac N)) (qFrac 3 N)) := by
      rw [qAdd_comm (qFrac 3 N) (qAdd (qUnitFrac N) (qUnitFrac n)),
        qAdd_comm (qUnitFrac N) (qUnitFrac n),
        ← qAdd_assoc (qAdd (qUnitFrac n) (qUnitFrac N))
          (qAdd (qUnitFrac n) (qUnitFrac N)) (qFrac 3 N),
        qAdd_swap_mid (qUnitFrac n) (qUnitFrac N)
          (qUnitFrac n) (qUnitFrac N),
        qAdd_assoc (qAdd (qUnitFrac n) (qUnitFrac n))
          (qAdd (qUnitFrac N) (qUnitFrac N)) (qFrac 3 N)]
    -- 濃縮: (u_N+u_N) + F3N ≤ F2N + F3N ≤ F5N
    have i1 : qLe (qAdd (qAdd (qUnitFrac N) (qUnitFrac N)) (qFrac 3 N))
        (qFrac 5 N) :=
      qLe_trans _ _ _ (qLe_add_two (qFrac_add 1 1 N) (qLe_refl _))
        (qFrac_add 2 3 N)
    have hfold : qLe (qAdd (qAdd (qUnitFrac n) (qUnitFrac N))
        (qAdd (qFrac 3 N) (qAdd (qUnitFrac N) (qUnitFrac n))))
        (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 5 N)) :=
      qLe_trans _ _ _ (qLe_of_eq e1) (qLe_add_two (qLe_refl _) i1)
    -- 移項して着地
    have hD := qLe_trans _ _ _ total hfold
    have hx := qLe_sub_move hD
    have e5 : qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 5 N))
        (y.seq n)
        = qAdd (qAdd (y.seq n) (qAdd (qUnitFrac n) (qUnitFrac n)))
          (qFrac 5 N) := by
      rw [qAdd_comm (qAdd (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac 5 N))
          (y.seq n),
        ← qAdd_assoc (y.seq n) (qAdd (qUnitFrac n) (qUnitFrac n))
          (qFrac 5 N)]
    exact qLe_trans _ _ _ hx (qLe_of_eq e5)
  | inr hB =>
    -- 下側: gap 3u_N から witness m = 4N+3 で rLt y x を構成
    have hlt : rLt y x := by
      refine ⟨4 * N + 3, ?_⟩
      show qLe (qFrac 2 (4 * N + 3))
        (qAdd (x.seq (2 * (4 * N + 3) + 1))
          (qNeg (y.seq (2 * (4 * N + 3) + 1))))
      apply qLe_move_right
      -- ゴール: F2m + y_s ≤ x_s（s = 8N+7）、cancel F3N 方式
      apply qLe_cancel_right (c := qFrac 3 N)
      -- 伝播部品: y_s ≤ (u_s + u_N) + y_N、x_N ≤ (u_N + u_s) + x_s
      have hys : qLe (y.seq (2 * (4 * N + 3) + 1))
          (qAdd (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N))
            (y.seq N)) :=
        qLe_abs_move (y.reg (2 * (4 * N + 3) + 1) N)
      have hxs : qLe (x.seq N)
          (qAdd (qAdd (qUnitFrac N) (qUnitFrac (2 * (4 * N + 3) + 1)))
            (x.seq (2 * (4 * N + 3) + 1))) :=
        qLe_abs_move (x.reg N (2 * (4 * N + 3) + 1))
      -- 濃縮: F2m + (u_s + u_N) + (u_N + u_s) ≤ F3N（分母 8N+8 の族:
      --   F4 + (F1+F8) + (F8+F1) = F22 ≤ F3N ⟺ 22(N+1) ≤ 24(N+1)）
      have hcon : qLe (qAdd (qAdd (qFrac 2 (4 * N + 3))
          (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
          (qAdd (qUnitFrac N) (qUnitFrac (2 * (4 * N + 3) + 1))))
          (qFrac 3 N) := by
        have f1 : qLe (qFrac 2 (4 * N + 3))
            (qFrac 4 (2 * (4 * N + 3) + 1)) := qFrac_le (by omega)
        have f2 : qLe (qUnitFrac N) (qFrac 8 (2 * (4 * N + 3) + 1)) :=
          qFrac_le (by omega)
        have h9a : qLe (qAdd (qUnitFrac (2 * (4 * N + 3) + 1))
            (qUnitFrac N)) (qFrac 9 (2 * (4 * N + 3) + 1)) :=
          qLe_trans _ _ _ (qLe_add_two (qLe_refl _) f2)
            (qFrac_add 1 8 (2 * (4 * N + 3) + 1))
        have h9b : qLe (qAdd (qUnitFrac N)
            (qUnitFrac (2 * (4 * N + 3) + 1)))
            (qFrac 9 (2 * (4 * N + 3) + 1)) :=
          qLe_trans _ _ _ (qLe_add_two f2 (qLe_refl _))
            (qFrac_add 8 1 (2 * (4 * N + 3) + 1))
        have h13 : qLe (qAdd (qFrac 2 (4 * N + 3))
            (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
            (qFrac 13 (2 * (4 * N + 3) + 1)) :=
          qLe_trans _ _ _ (qLe_add_two f1 h9a)
            (qFrac_add 4 9 (2 * (4 * N + 3) + 1))
        have h22 : qLe (qAdd (qAdd (qFrac 2 (4 * N + 3))
            (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
            (qAdd (qUnitFrac N) (qUnitFrac (2 * (4 * N + 3) + 1))))
            (qFrac 22 (2 * (4 * N + 3) + 1)) :=
          qLe_trans _ _ _ (qLe_add_two h13 h9b)
            (qFrac_add 13 9 (2 * (4 * N + 3) + 1))
        exact qLe_trans _ _ _ h22 (qFrac_le (by omega))
      -- 鎖: (F2m + y_s) + F3N ≤ … ≤ x_s + F3N
      have g1 : qLe (qAdd (qAdd (qFrac 2 (4 * N + 3))
          (y.seq (2 * (4 * N + 3) + 1))) (qFrac 3 N))
          (qAdd (qAdd (qFrac 2 (4 * N + 3))
            (qAdd (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N))
              (y.seq N))) (qFrac 3 N)) :=
        qLe_add_two (qLe_add_two (qLe_refl _) hys) (qLe_refl _)
      have e1 : qAdd (qAdd (qFrac 2 (4 * N + 3))
          (qAdd (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N))
            (y.seq N))) (qFrac 3 N)
          = qAdd (qAdd (qFrac 2 (4 * N + 3))
              (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
            (qAdd (y.seq N) (qFrac 3 N)) := by
        rw [← qAdd_assoc (qFrac 2 (4 * N + 3))
            (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N))
            (y.seq N),
          qAdd_assoc (qAdd (qFrac 2 (4 * N + 3))
              (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
            (y.seq N) (qFrac 3 N)]
      have g2 : qLe (qAdd (qAdd (qFrac 2 (4 * N + 3))
          (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
          (qAdd (y.seq N) (qFrac 3 N)))
          (qAdd (qAdd (qFrac 2 (4 * N + 3))
            (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
            (x.seq N)) :=
        qLe_add_two (qLe_refl _) hB
      have g3 : qLe (qAdd (qAdd (qFrac 2 (4 * N + 3))
          (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
          (x.seq N))
          (qAdd (qAdd (qFrac 2 (4 * N + 3))
            (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
            (qAdd (qAdd (qUnitFrac N) (qUnitFrac (2 * (4 * N + 3) + 1)))
              (x.seq (2 * (4 * N + 3) + 1)))) :=
        qLe_add_two (qLe_refl _) hxs
      have e2 : qAdd (qAdd (qFrac 2 (4 * N + 3))
          (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
          (qAdd (qAdd (qUnitFrac N) (qUnitFrac (2 * (4 * N + 3) + 1)))
            (x.seq (2 * (4 * N + 3) + 1)))
          = qAdd (qAdd (qAdd (qFrac 2 (4 * N + 3))
              (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
              (qAdd (qUnitFrac N) (qUnitFrac (2 * (4 * N + 3) + 1))))
            (x.seq (2 * (4 * N + 3) + 1)) :=
        (qAdd_assoc _ _ _).symm
      have g4 : qLe (qAdd (qAdd (qAdd (qFrac 2 (4 * N + 3))
          (qAdd (qUnitFrac (2 * (4 * N + 3) + 1)) (qUnitFrac N)))
          (qAdd (qUnitFrac N) (qUnitFrac (2 * (4 * N + 3) + 1))))
          (x.seq (2 * (4 * N + 3) + 1)))
          (qAdd (qFrac 3 N) (x.seq (2 * (4 * N + 3) + 1))) :=
        qLe_add_two hcon (qLe_refl _)
      exact qLe_trans _ _ _ g1 (qLe_trans _ _ _ (qLe_of_eq e1)
        (qLe_trans _ _ _ g2 (qLe_trans _ _ _ g3
          (qLe_trans _ _ _ (qLe_of_eq e2) (qLe_trans _ _ _ g4
            (qLe_of_eq (qAdd_comm _ _)))))))
    exact absurd hlt h

/-! ## M136F-2: 双方向の整合 -/

/-- **定理 (M136F-2): rLe ⟺ ¬rLt** — → は M130 の強排反
    rLt_not_le、← は M136F-1 の δ-論法。 -/
theorem le_iff_not_lt (x y : RReal) : rLe x y ↔ ¬ rLt y x :=
  Iff.intro (fun hle hlt => rLt_not_le hlt hle) not_lt_le

/-! ## M136F-3: 強排反の再輸出 -/

/-- **M136F-3: 強排反**（M130 の rLt_not_le の再輸出）。逆向き
    ¬rLe x y → rLt y x は二重否定除去相当のため対象外（正直申告）。 -/
theorem lt_iff_not_le (x y : RReal) : rLt y x → ¬ rLe x y :=
  rLt_not_le

/-! ## M136F-4: 総括 -/

/-- **M136F-4a: 総括** — 順序の完全整合データ。 -/
structure RealOrderCompleteData where
  /-- δ-論法: ¬rLt → rLe。 -/
  not_lt_le : ∀ {x y : RReal}, ¬ rLt y x → rLe x y
  /-- 双方向: rLe ⟺ ¬rLt。 -/
  le_iff_not_lt : ∀ x y : RReal, rLe x y ↔ ¬ rLt y x
  /-- 強排反: rLt → ¬rLe。 -/
  lt_iff_not_le : ∀ x y : RReal, rLt y x → ¬ rLe x y

/-- **M136F-4b: witness**。 -/
def realOrderCompleteData : RealOrderCompleteData where
  not_lt_le := not_lt_le
  le_iff_not_lt := le_iff_not_lt
  lt_iff_not_le := lt_iff_not_le

/-- **M136F-4c: 存在**。 -/
theorem realOrderComplete_exists : Nonempty RealOrderCompleteData :=
  ⟨realOrderCompleteData⟩

end IUT
