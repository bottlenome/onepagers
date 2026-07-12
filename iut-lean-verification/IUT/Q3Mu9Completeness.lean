/-
  IUT/Q3Mu9Completeness.lean — F-wild level-9 μ₉-completeness campaign / Module B
    （実 O_M = O_{L₂}[Y]/(Y³−ζ₃) = q3kRing 内の μ₃ 完全性核＋塔分解 μ₉ 完全性）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**（骨格・模型・代理でなく、R1/R2a で
     建てた**実** O_{L₂}=q3rqRing・実 O_M=q3kRing の上に、level-9 μ₉ 完全性の真の新規核
     ——O_M 内 μ₃ 完全性「x³=1 ⟹ x∈μ₃(L₂)⊂O_M」（B7）と、塔分解による μ₉ 完全性
     「u⁹=1 ⟹ u∈μ₉」（B8）——をゼロから本物に積む。主語は実 q3k/q3rq の元
     （m202fVol 型・Bool 軌道・surrogate 群を一切使わない）。消費するのは実 Module A
     （q9ci：ねじれ 3 次冪の成分恒等式 E0/E1/E2・正則性パック・no-cbrt・ノルム整合）・
     実降下スパイク（q9cs：交互パリティ同時降下）・実 level-3 μ₃ 完全性（q3mc）のみ。）

  complete_pct 影響: **F-wild (ii)（μ₉ 完全性 / level-9 kill）の急所 discharge・foundation**。
  μ₉ 完全性それ自体は後続の level-9 テータ kill（display-mover）に**消費される本物入力**で
  あり、本モジュール単体は何も kill しない（テータ群・Weil pairing・剛性は本ファイルに無い）。
  よって**単体では complete_pct 丸め値 0 前進（本物基盤・level-9 kill は後続）**と正直申告する。

  内容（§6.1 Module B = B1–B9）:
   * B1 q9c_norm_one       — x³=1 ⟹ N(x)=1（q3mc 消費 1・mod-9 剛性 N=1−9ζ₃abc）
   * B2 q9c_abc_zero       — 9ζ₃abc=0 ⟹ abc=0（9 正則＋ζ₃ 単数正則）
   * B3 q9c_F1/_F2/_F3/_F3'— G=a²+ζ₃bc の成分恒等式群（環計算・abc=0 の下 E′·b=b²G 等）
   * B4 q9c_not_b_unit/_c_unit — 2 単数枝の完全反証（Decidable-cases×2・no-cbrt）
   * B5 q9c_a_unit         — 生存枝（両非単数）で 3∤a₁（a は O_{L₂} 単数）
   * B6 q9c_bc_zero        — 交互パリティ同時降下（q9cs 消費）で b=c=0
   * B7 q9c_m_mu3_complete — ★★ O_M 内 μ₃ 完全性（B1–B6 束ね＋q3mc 消費 2）
   * B8 q3kMu9 / q9c_mu9_complete — ★★★ 塔分解 u⁹=(u³)³ で μ₉ 完全性（9 乗展開なし）
   * B9 Q3Mu9CompletenessData / q9c_data / q9c_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・q3k/q3rq/q3mc/q9ci/q9cs 継承の上に追記）:
  1. **μ₉ 完全性は carrier レベルの言明**（q3kCar 上・単数性を仮定に取らない・§6.2 消費者互換）。
  2. **本モジュールは何も kill しない**（テータ群・Weil pairing・剛性ゼロ——それは後続 kill モジュール）。
  3. **奇 a 枝（u⁹=−1 ⟹ μ₁₈）は収録しない**（q3mc 正直限定 4 の前例どおり named next）。
  4. q3k/q3rq/q3mc/q9ci/q9cs の正直限定を全て継承（O_M と M^× のみ・体化なし・σ を超える
     Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・tmzLimit 比較橋なし・兄弟担体・
     正則性は零因子でない代数的言明のみ）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用（Or 破壊は obtain、
  3∣n 分岐は Decidable インスタンスの cases、omega は純線形 Int/Nat ゴールのみ）。
-/
import IUT.Q3KummerCubeIdent
import IUT.Q3KummerDescentSpike
import IUT.Q3Mu3Completeness

namespace IUT

/-! ## q9c-0raw: 純 CRing 恒等式（G=a²+ζ₃bc の成分方程式・9-fold 折り畳みの骨） -/

/-- mul の左交換（構造公理のみ・import 閉包に CRing.mul_left_comm が無いため自前）。 -/
private theorem q9c_mlc (R : CRing) (a b c : R.carrier) :
    R.mul a (R.mul b c) = R.mul b (R.mul a c) := by
  rw [← R.mul_assoc, R.mul_comm a b, R.mul_assoc]

/-- **F1**: E1' = b·G + d·a·c²（G = a² + d·bc）。 -/
theorem q9c_rawF1 (R : CRing) (a b c d : R.carrier) :
    R.add (R.add (R.mul (R.mul a a) b) (R.mul d (R.mul a (R.mul c c))))
          (R.mul d (R.mul (R.mul b b) c))
    = R.add (R.mul b (R.add (R.mul a a) (R.mul d (R.mul b c))))
            (R.mul d (R.mul a (R.mul c c))) := by
  rw [R.left_distrib b (R.mul a a) (R.mul d (R.mul b c)),
      R.mul_comm (R.mul a a) b,
      R.mul_assoc b b c,
      q9c_mlc R d b (R.mul b c),
      R.add_assoc (R.mul b (R.mul a a)) (R.mul d (R.mul a (R.mul c c)))
        (R.mul b (R.mul d (R.mul b c))),
      R.add_comm (R.mul d (R.mul a (R.mul c c))) (R.mul b (R.mul d (R.mul b c))),
      ← R.add_assoc (R.mul b (R.mul a a)) (R.mul b (R.mul d (R.mul b c)))
        (R.mul d (R.mul a (R.mul c c)))]

/-- **F2**: E2' = c·G + a·b²。 -/
theorem q9c_rawF2 (R : CRing) (a b c d : R.carrier) :
    R.add (R.add (R.mul (R.mul a a) c) (R.mul a (R.mul b b)))
          (R.mul d (R.mul b (R.mul c c)))
    = R.add (R.mul c (R.add (R.mul a a) (R.mul d (R.mul b c))))
            (R.mul a (R.mul b b)) := by
  rw [R.left_distrib c (R.mul a a) (R.mul d (R.mul b c)),
      R.mul_comm (R.mul a a) c,
      q9c_mlc R b c c,
      q9c_mlc R d c (R.mul b c),
      R.add_assoc (R.mul c (R.mul a a)) (R.mul a (R.mul b b))
        (R.mul c (R.mul d (R.mul b c))),
      R.add_comm (R.mul a (R.mul b b)) (R.mul c (R.mul d (R.mul b c))),
      ← R.add_assoc (R.mul c (R.mul a a)) (R.mul c (R.mul d (R.mul b c)))
        (R.mul a (R.mul b b))]

/-- **F3**: E1'·b = b²·G + d·(a·b·c)·c。 -/
theorem q9c_rawF3 (R : CRing) (a b c d : R.carrier) :
    R.mul (R.add (R.add (R.mul (R.mul a a) b) (R.mul d (R.mul a (R.mul c c))))
                 (R.mul d (R.mul (R.mul b b) c))) b
    = R.add (R.mul (R.mul b b) (R.add (R.mul a a) (R.mul d (R.mul b c))))
            (R.mul d (R.mul (R.mul a (R.mul b c)) c)) := by
  have hm1 : R.mul (R.mul (R.mul a a) b) b = R.mul (R.mul b b) (R.mul a a) := by
    rw [R.mul_assoc (R.mul a a) b b, R.mul_comm (R.mul a a) (R.mul b b)]
  have hm2 : R.mul (R.mul d (R.mul a (R.mul c c))) b
      = R.mul d (R.mul (R.mul a (R.mul b c)) c) := by
    rw [R.mul_assoc d (R.mul a (R.mul c c)) b,
        R.mul_assoc a (R.mul c c) b,
        R.mul_comm (R.mul c c) b,
        R.mul_assoc a (R.mul b c) c,
        R.mul_assoc b c c]
  have hm3 : R.mul (R.mul d (R.mul (R.mul b b) c)) b
      = R.mul (R.mul b b) (R.mul d (R.mul b c)) := by
    rw [R.mul_assoc d (R.mul (R.mul b b) c) b,
        R.mul_assoc (R.mul b b) c b,
        q9c_mlc R d (R.mul b b) (R.mul c b),
        R.mul_comm c b]
  rw [R.right_distrib (R.add (R.mul (R.mul a a) b) (R.mul d (R.mul a (R.mul c c))))
        (R.mul d (R.mul (R.mul b b) c)) b,
      R.right_distrib (R.mul (R.mul a a) b) (R.mul d (R.mul a (R.mul c c))) b,
      R.left_distrib (R.mul b b) (R.mul a a) (R.mul d (R.mul b c)),
      hm1, hm2, hm3,
      R.add_assoc (R.mul (R.mul b b) (R.mul a a))
        (R.mul d (R.mul (R.mul a (R.mul b c)) c))
        (R.mul (R.mul b b) (R.mul d (R.mul b c))),
      R.add_comm (R.mul d (R.mul (R.mul a (R.mul b c)) c))
        (R.mul (R.mul b b) (R.mul d (R.mul b c))),
      ← R.add_assoc (R.mul (R.mul b b) (R.mul a a))
        (R.mul (R.mul b b) (R.mul d (R.mul b c)))
        (R.mul d (R.mul (R.mul a (R.mul b c)) c))]

/-- **F3'**: E2'·c = c²·G + (a·b·c)·b。 -/
theorem q9c_rawF3' (R : CRing) (a b c d : R.carrier) :
    R.mul (R.add (R.add (R.mul (R.mul a a) c) (R.mul a (R.mul b b)))
                 (R.mul d (R.mul b (R.mul c c)))) c
    = R.add (R.mul (R.mul c c) (R.add (R.mul a a) (R.mul d (R.mul b c))))
            (R.mul (R.mul a (R.mul b c)) b) := by
  have hn1 : R.mul (R.mul (R.mul a a) c) c = R.mul (R.mul c c) (R.mul a a) := by
    rw [R.mul_assoc (R.mul a a) c c, R.mul_comm (R.mul a a) (R.mul c c)]
  have hn2 : R.mul (R.mul a (R.mul b b)) c = R.mul (R.mul a (R.mul b c)) b := by
    rw [R.mul_assoc a (R.mul b b) c,
        R.mul_assoc b b c,
        R.mul_assoc a (R.mul b c) b,
        R.mul_assoc b c b,
        R.mul_comm c b]
  have hn3 : R.mul (R.mul d (R.mul b (R.mul c c))) c
      = R.mul (R.mul c c) (R.mul d (R.mul b c)) := by
    rw [R.mul_assoc d (R.mul b (R.mul c c)) c,
        R.mul_assoc b (R.mul c c) c,
        R.mul_assoc c c c,
        R.mul_comm (R.mul c c) (R.mul d (R.mul b c)),
        R.mul_assoc d (R.mul b c) (R.mul c c),
        R.mul_assoc b c (R.mul c c)]
  rw [R.right_distrib (R.add (R.mul (R.mul a a) c) (R.mul a (R.mul b b)))
        (R.mul d (R.mul b (R.mul c c))) c,
      R.right_distrib (R.mul (R.mul a a) c) (R.mul a (R.mul b b)) c,
      R.left_distrib (R.mul c c) (R.mul a a) (R.mul d (R.mul b c)),
      hn1, hn2, hn3,
      R.add_assoc (R.mul (R.mul c c) (R.mul a a))
        (R.mul (R.mul a (R.mul b c)) b)
        (R.mul (R.mul c c) (R.mul d (R.mul b c))),
      R.add_comm (R.mul (R.mul a (R.mul b c)) b)
        (R.mul (R.mul c c) (R.mul d (R.mul b c))),
      ← R.add_assoc (R.mul (R.mul c c) (R.mul a a))
        (R.mul (R.mul c c) (R.mul d (R.mul b c)))
        (R.mul (R.mul a (R.mul b c)) b)]

/-- **9-fold の骨**: BIG = S+(S+S)（S = Z+(Z+Z)・9 個の Z の再結合）。 -/
theorem q9c_rawNine (R : CRing) (Z : R.carrier) :
    R.add (R.add (R.add (R.add (R.add (R.add Z Z) Z) Z) Z) Z)
          (R.add Z (R.add Z Z))
    = R.add (R.add Z (R.add Z Z))
            (R.add (R.add Z (R.add Z Z)) (R.add Z (R.add Z Z))) := by
  have hL :
      R.add (R.add (R.add (R.add (R.add (R.add Z Z) Z) Z) Z) Z)
            (R.add Z (R.add Z Z))
      = R.add Z (R.add Z (R.add Z (R.add Z (R.add Z (R.add Z (R.add Z (R.add Z Z))))))) := by
    rw [R.add_assoc (R.add (R.add (R.add (R.add Z Z) Z) Z) Z) Z (R.add Z (R.add Z Z)),
        R.add_assoc (R.add (R.add (R.add Z Z) Z) Z) Z (R.add Z (R.add Z (R.add Z Z))),
        R.add_assoc (R.add (R.add Z Z) Z) Z (R.add Z (R.add Z (R.add Z (R.add Z Z)))),
        R.add_assoc (R.add Z Z) Z (R.add Z (R.add Z (R.add Z (R.add Z (R.add Z Z))))),
        R.add_assoc Z Z (R.add Z (R.add Z (R.add Z (R.add Z (R.add Z (R.add Z Z))))))]
  have hR :
      R.add (R.add Z (R.add Z Z))
            (R.add (R.add Z (R.add Z Z)) (R.add Z (R.add Z Z)))
      = R.add Z (R.add Z (R.add Z (R.add Z (R.add Z (R.add Z (R.add Z (R.add Z Z))))))) := by
    rw [R.add_assoc Z (R.add Z Z)
          (R.add (R.add Z (R.add Z Z)) (R.add Z (R.add Z Z))),
        R.add_assoc Z Z (R.add (R.add Z (R.add Z Z)) (R.add Z (R.add Z Z))),
        R.add_assoc Z (R.add Z Z) (R.add Z (R.add Z Z)),
        R.add_assoc Z Z (R.add Z (R.add Z Z))]
  exact hL.trans hR.symm

/-! ## q9c-0: スカラー橋（3・9 の乗法と 9-fold 折り畳み） -/

/-- 3·w = w+(w+w)（z3 内・右分配）。 -/
theorem q9c_three_z3 (w : z3.carrier) :
    z3.mul q3rqThree w = z3.add w (z3.add w w) := by
  show z3.mul (z3.add (z3.add z3.one z3.one) z3.one) w = z3.add w (z3.add w w)
  rw [z3.right_distrib (z3.add z3.one z3.one) z3.one w,
      z3.right_distrib z3.one z3.one w, z3.one_mul w, z3.add_assoc w w w]

/-- 3·z = z+(z+z)（q3rqCar 内・環元 (3,0) の乗法）。 -/
theorem q9c_three_mul_elt (z : q3rqCar) :
    q3rqMul q3rqThreeElt z = q3rqAdd z (q3rqAdd z z) := by
  apply q3rq_ext
  · show z3.add (z3.mul q3rqThree z.1) (z3.mul q3rqD (z3.mul z3.zero z.2))
        = z3.add z.1 (z3.add z.1 z.1)
    rw [z3.zero_mul z.2, z3.mul_zero q3rqD, z3.add_zero, q9c_three_z3 z.1]
  · show z3.add (z3.mul q3rqThree z.2) (z3.mul z3.zero z.1)
        = z3.add z.2 (z3.add z.2 z.2)
    rw [z3.zero_mul z.1, z3.add_zero, q9c_three_z3 z.2]

/-- 9-fold の折り畳み: BIG(Z) = 9·Z = q3rqMul q9ciNine Z。 -/
theorem q9c_big_eq (Z : q3rqCar) :
    q3rqAdd
      (q3rqAdd
        (q3rqAdd (q3rqAdd (q3rqAdd (q3rqAdd Z Z) Z) Z) Z) Z)
      (q3rqAdd Z (q3rqAdd Z Z))
    = q3rqMul q9ciNine Z := by
  have h1 :
      q3rqAdd
        (q3rqAdd (q3rqAdd (q3rqAdd (q3rqAdd (q3rqAdd Z Z) Z) Z) Z) Z)
        (q3rqAdd Z (q3rqAdd Z Z))
      = q3rqAdd (q3rqAdd Z (q3rqAdd Z Z))
          (q3rqAdd (q3rqAdd Z (q3rqAdd Z Z)) (q3rqAdd Z (q3rqAdd Z Z))) :=
    q9c_rawNine q3rqRing Z
  have h2 : q3rqMul q9ciNine Z
      = q3rqAdd (q3rqAdd Z (q3rqAdd Z Z))
          (q3rqAdd (q3rqAdd Z (q3rqAdd Z Z)) (q3rqAdd Z (q3rqAdd Z Z))) := by
    show q3rqMul (q3rqMul q3rqThreeElt q3rqThreeElt) Z = _
    rw [q3k_M_eq, q3rqRing.mul_assoc q3rqThreeElt q3rqThreeElt Z, ← q3k_M_eq,
        q9c_three_mul_elt Z, q9c_three_mul_elt (q3rqAdd Z (q3rqAdd Z Z))]
  rw [h1, h2]

/-! ## q9c-0b: ζ₃ の単数性と q9ciNine の座標 -/

/-- ζ₃ は O_{L₂} の単数（N(ζ₃)=1）。 -/
theorem q9c_zeta_unit : q3rqUnitMem q3rqZeta := by
  show IsZpUnit 3 (q3rqNorm q3rqZeta)
  rw [q3rq_zeta_norm]
  have h := q3rq_unit_one
  show IsZpUnit 3 z3.one
  have he : q3rqNorm q3rqOne = z3.one := q3rq_norm_one
  have h' : IsZpUnit 3 (q3rqNorm q3rqOne) := h
  rw [he] at h'
  exact h'

/-- q9ciNine の第 1 座標 = 3·3。 -/
theorem q9c_nine_fst : q9ciNine.1 = z3.mul q3rqThree q3rqThree := by
  show z3.add (z3.mul q3rqThree q3rqThree) (z3.mul q3rqD (z3.mul z3.zero z3.zero))
      = z3.mul q3rqThree q3rqThree
  rw [z3.mul_zero z3.zero, z3.mul_zero q3rqD, z3.add_zero]

/-- q9ciNine の第 2 座標 = 0。 -/
theorem q9c_nine_snd : q9ciNine.2 = z3.zero := by
  show z3.add (z3.mul q3rqThree z3.zero) (z3.mul z3.zero q3rqThree) = z3.zero
  rw [z3.mul_zero q3rqThree, z3.zero_mul q3rqThree, z3.add_zero]

/-- (9·Z) の第 2 座標のレベル 1 値 = [0]（9 ≡ 0 mod 3）。 -/
theorem q9c_nineZ_snd_val1 (Z : q3rqCar) :
    (q3rqMul q9ciNine Z).2.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := by
  obtain ⟨zr, hzr⟩ := Quot.exists_rep (Z.2.val 1)
  show (z3.add (z3.mul q9ciNine.1 Z.2) (z3.mul q9ciNine.2 Z.1)).val 1 = _
  rw [q9c_nine_fst, q9c_nine_snd, z3.zero_mul Z.1, z3.add_zero]
  have h99 : (z3.mul q3rqThree q3rqThree).val 1
      = Quot.mk (modCong (3 ^ 1)).rel (3 * 3) :=
    q3mc_mul_val1 q3rqThree q3rqThree 3 3 (q3rq_three_val 1) (q3rq_three_val 1)
  rw [q3mc_mul_val1 (z3.mul q3rqThree q3rqThree) Z.2 (3 * 3) zr h99 hzr.symm]
  apply Quot.sound
  show ((3 ^ 1 : Nat) : Int) ∣ ((3 * 3) * zr - 0)
  exact ⟨3 * zr, by rw [Nat.pow_one]; omega⟩

/-! ## q9c-1（B1）: x³=1 ⟹ N(x)=1（★q3mc 消費 1・mod-9 剛性） -/

/-- q3rqTwoZ のレベル 1 値 = [2]。 -/
theorem q9c_two_val1 : q3rqTwoZ.val 1 = Quot.mk (modCong (3 ^ 1)).rel 2 := by
  show (z3.add z3.one z3.one).val 1 = Quot.mk (modCong (3 ^ 1)).rel 2
  show (zmod (3 ^ 1)).mul ((zpOne 3).val 1) ((zpOne 3).val 1)
    = Quot.mk (modCong (3 ^ 1)).rel 2
  show Quot.mk (modCong (3 ^ 1)).rel (1 + 1) = Quot.mk (modCong (3 ^ 1)).rel 2
  rfl

/-- **B1（★）: x³=1 ⟹ N(x)=1**。N(x)³=1（q3mc 消費）で N∈{1,ζ₃,ζ₃²}、
    N=1−9ζ₃abc の第 2 座標 level-1 = [0] で ζ₃/ζ₃² を排除。 -/
theorem q9c_norm_one (x : q3kCar)
    (hu : q3kMul (q3kMul x x) x = q3kOne) : q3kNormBase x = q3rqOne := by
  -- N(x)³ = 1
  have hcube1 : q3rqMul (q3rqMul (q3kNormBase x) (q3kNormBase x)) (q3kNormBase x)
      = q3rqOne := by
    have h1 : q3kNormBase (q3kMul (q3kMul x x) x)
        = q3rqMul (q3rqMul (q3kNormBase x) (q3kNormBase x)) (q3kNormBase x) := by
      rw [q3k_normBase_mul (q3kMul x x) x, q3k_normBase_mul x x]
    rw [← h1, hu, q3k_normBase_one]
  have hmu3 : q3rqMu3 (q3kNormBase x) := q3mc_mu3_complete (q3kNormBase x) hcube1
  -- N(x).2.val 1 = [0]
  have hval : (q3kNormBase x).2.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := by
    rw [q9ci_norm_sub x, hu,
        q9c_big_eq (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))]
    show (z3.add q3rqOne.2
          (z3.neg (q3rqMul q9ciNine
            (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))).2)).val 1 = _
    rw [show q3rqOne.2 = z3.zero from rfl, z3.zero_add,
        q3mc_neg_val1 _ 0
          (q9c_nineZ_snd_val1 (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))]
    apply Quot.sound
    show ((3 ^ 1 : Nat) : Int) ∣ (-0 - 0)
    exact ⟨0, by rw [Nat.pow_one]; omega⟩
  -- 枝処理
  obtain h1 | hz | hzsq := hmu3
  · exact h1
  · exfalso
    have h2eq : (q3kNormBase x).2 = q3rqHalf := congrArg Prod.snd hz
    have heq : q3rqHalf.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := by rw [← h2eq]; exact hval
    have h2h : (z3.mul q3rqTwoZ q3rqHalf).val 1 = Quot.mk (modCong (3 ^ 1)).rel 1 := by
      rw [q3rq_two_half]; rfl
    rw [q3mc_mul_val1 q3rqTwoZ q3rqHalf 2 0 q9c_two_val1 heq] at h2h
    have hd := quot_exact intGrp (modCong (3 ^ 1)) h2h
    rw [Nat.pow_one] at hd
    obtain ⟨c, hc⟩ := hd; omega
  · exfalso
    have hsnd : (q3kNormBase x).2 = q3rqZetaSq.2 := congrArg Prod.snd hzsq
    have hzs2 : q3rqZetaSq.2 = z3.neg q3rqHalf := congrArg Prod.snd q3rq_zeta_sq_eq
    have heq : (z3.neg q3rqHalf).val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := by
      rw [← hzs2, ← hsnd]; exact hval
    have h2h : (z3.mul q3rqTwoZ (z3.neg q3rqHalf)).val 1
        = Quot.mk (modCong (3 ^ 1)).rel (-1) := by
      rw [z3.mul_neg q3rqTwoZ q3rqHalf, q3rq_two_half]
      exact q3mc_neg_val1 z3.one 1 rfl
    rw [q3mc_mul_val1 q3rqTwoZ (z3.neg q3rqHalf) 2 0 q9c_two_val1 heq] at h2h
    have hd := quot_exact intGrp (modCong (3 ^ 1)) h2h
    rw [Nat.pow_one] at hd
    obtain ⟨c, hc⟩ := hd; omega

/-! ## q9c-2（B2）: 9ζ₃abc=0 ⟹ abc=0 -/

/-- **B2: abc=0**（N(x)=1 で 9ζ₃abc=0、9 正則＋ζ₃ 単数正則で剥がす）。 -/
theorem q9c_abc_zero (x : q3kCar)
    (hu : q3kMul (q3kMul x x) x = q3kOne) :
    q3rqMul x.1 (q3rqMul x.2.1 x.2.2) = q3rqZero := by
  have hN : q3kNormBase x = q3rqOne := q9c_norm_one x hu
  have hns := q9ci_norm_sub x
  rw [hu, q9c_big_eq (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))] at hns
  rw [hN] at hns
  have hcancel :
      q3rqRing.add q3rqOne
        (q3rqRing.neg (q3rqMul q9ciNine
          (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))))
      = q3rqRing.add q3rqOne q3rqRing.zero := by
    rw [q3rqRing.add_zero q3rqOne]
    exact hns.symm
  have hnegz := q3rqRing.add_left_cancel hcancel
  have hbig : q3rqMul q9ciNine (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))
      = q3rqZero := by
    have h := congrArg q3rqRing.neg hnegz
    rw [q3rqRing.neg_neg, q3rqRing.neg_zero] at h
    exact h
  have hZc := q9ci_nine_reg _ hbig
  exact q9ci_unit_reg_L2 q3rqZeta _ q9c_zeta_unit hZc

/-! ## q9c-3（E1'/E2' 消去）: x³=1 の Y/Y² 成分から E1'=E2'=0（3 正則） -/

/-- E1' = a²b + ζ₃ac² + ζ₃b²c = 0（(x³).2.1 = 3·E1' と 3 正則）。 -/
theorem q9c_E1_zero (x : q3kCar) (hu : q3kMul (q3kMul x x) x = q3kOne) :
    q3rqAdd
      (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.1)
        (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.2 x.2.2))))
      (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.2)) = q3rqZero := by
  have h : (q3kMul (q3kMul x x) x).2.1 = q3rqZero :=
    congrArg (fun z : q3kCar => z.2.1) hu
  rw [q9ci_cube_1 x, ← q9c_three_mul_elt _] at h
  exact q9ci_three_reg_L2 _ h

/-- E2' = a²c + ab² + ζ₃bc² = 0（(x³).2.2 = 3·E2' と 3 正則）。 -/
theorem q9c_E2_zero (x : q3kCar) (hu : q3kMul (q3kMul x x) x = q3kOne) :
    q3rqAdd
      (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.2)
        (q3rqMul x.1 (q3rqMul x.2.1 x.2.1)))
      (q3rqMul q3rqZeta (q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2))) = q3rqZero := by
  have h : (q3kMul (q3kMul x x) x).2.2 = q3rqZero :=
    congrArg (fun z : q3kCar => z.2.2) hu
  rw [q9ci_cube_2 x, ← q9c_three_mul_elt _] at h
  exact q9ci_three_reg_L2 _ h

/-! ## q9c-4: 射影整合（レベル間の rep 伝播）と単数判定 -/

/-- **射影整合**: w.val n = [j] ⟹ w.val s = [j]（s ≤ n・逆極限の compat）。 -/
theorem q9c_val_proj_gen (w : z3.carrier) (s n : Nat) (j : Int) (hsn : s ≤ n)
    (h : w.val n = Quot.mk (modCong (3 ^ n)).rel j) :
    w.val s = Quot.mk (modCong (3 ^ s)).rel j := by
  have hc := w.property (i := s) (j := n) hsn
  rw [h] at hc
  exact hc.symm

/-- **単数判定**: 第 1 座標 level-1 rep が 3∤ ⟹ O_{L₂} 単数（N=p²+3q²≡p²≢0）。 -/
theorem q9c_unit_of_fst_nondvd (u : q3rqCar) (u1 u2 : Int)
    (h1 : u.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel u1)
    (h2 : u.2.val 1 = Quot.mk (modCong (3 ^ 1)).rel u2)
    (hnd : ¬ ((3 : Nat) : Int) ∣ u1) : q3rqUnitMem u := by
  show IsZpUnit 3 (q3rqNorm u)
  apply z3v_unit_of_lev1 3 (q3rqNorm u)
  intro hge
  have hn1 : (q3rqNorm u).val 1
      = Quot.mk (modCong (3 ^ 1)).rel (u1 * u1 + (-((-3) * (u2 * u2)))) :=
    q3mc_norm_lev1 u.1 u.2 u1 u2 h1 h2
  have heq : Quot.mk (modCong (3 ^ 1)).rel (u1 * u1 + (-((-3) * (u2 * u2))))
      = Quot.mk (modCong (3 ^ 1)).rel 0 := hn1.symm.trans hge
  have hdvd := quot_exact intGrp (modCong (3 ^ 1)) heq
  rw [Nat.pow_one] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have h3u1sq : ((3 : Nat) : Int) ∣ (u1 * u1) := ⟨k - u2 * u2, by omega⟩
  exact hnd (euclid_int 3 isPrime_three h3u1sq hnd)

/-! ## q9c-5（B4 骨）: 零消去補助（q3rqMul/q3rqAdd 形の 0 法則） -/

/-- q3rqMul q3rqZero y = q3rqZero。 -/
theorem q9c_zm (y : q3rqCar) : q3rqMul q3rqZero y = q3rqZero := q3rqRing.zero_mul y
/-- q3rqMul y q3rqZero = q3rqZero。 -/
theorem q9c_mz (y : q3rqCar) : q3rqMul y q3rqZero = q3rqZero := q3rqRing.mul_zero y
/-- q3rqAdd q3rqZero y = y。 -/
theorem q9c_za (y : q3rqCar) : q3rqAdd q3rqZero y = y := q3rqRing.zero_add y
/-- q3rqAdd y q3rqZero = y。 -/
theorem q9c_az (y : q3rqCar) : q3rqAdd y q3rqZero = y := q3rqRing.add_zero y
/-- q3rqNeg q3rqZero = q3rqZero。 -/
theorem q9c_nz : q3rqNeg q3rqZero = q3rqZero := q3rqRing.neg_zero

/-- N((0,b,0)) = ζ₃·b³。 -/
theorem q9c_norm_a0c0 (x : q3kCar) (ha : x.1 = q3rqZero) (hc : x.2.2 = q3rqZero) :
    q3kNormBase x = q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1) := by
  show q3rqAdd (q3rqAdd (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.1)
      (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)))
      (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)))
    (q3rqNeg (q3rqMul q3kThree (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.1 x.2.1) x.2.2)))) = _
  rw [ha, hc, q9c_zm q3rqZero, q9c_zm q3rqZero, q9c_mz q3rqZetaSq, q9c_zm x.2.1,
      q9c_mz q3rqZero, q9c_mz q3rqZeta, q9c_mz q3kThree, q9c_nz, q9c_za, q9c_az, q9c_az]

/-- N((0,0,c)) = ζ₃²·c³。 -/
theorem q9c_norm_a0b0 (x : q3kCar) (ha : x.1 = q3rqZero) (hb : x.2.1 = q3rqZero) :
    q3kNormBase x = q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2) := by
  show q3rqAdd (q3rqAdd (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.1)
      (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)))
      (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)))
    (q3rqNeg (q3rqMul q3kThree (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.1 x.2.1) x.2.2)))) = _
  rw [ha, hb, q9c_zm q3rqZero, q9c_zm q3rqZero, q9c_zm x.2.2, q9c_mz q3rqZeta,
      q9c_mz q3kThree, q9c_nz, q9c_za, q9c_za, q9c_az]

/-- E1'=0 かつ a=0 ⟹ ζ₃·b²·c = 0。 -/
theorem q9c_E1_a0 (x : q3kCar) (ha : x.1 = q3rqZero)
    (hE1 : q3rqAdd
      (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.1)
        (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.2 x.2.2))))
      (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.2)) = q3rqZero) :
    q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.2) = q3rqZero := by
  rw [ha, q9c_zm q3rqZero, q9c_zm x.2.1, q9c_zm (q3rqMul x.2.2 x.2.2), q9c_mz q3rqZeta,
      q9c_za, q9c_za] at hE1
  exact hE1

/-- E2'=0 かつ a=0 ⟹ ζ₃·b·c² = 0。 -/
theorem q9c_E2_a0 (x : q3kCar) (ha : x.1 = q3rqZero)
    (hE2 : q3rqAdd
      (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.2)
        (q3rqMul x.1 (q3rqMul x.2.1 x.2.1)))
      (q3rqMul q3rqZeta (q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2))) = q3rqZero) :
    q3rqMul q3rqZeta (q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2)) = q3rqZero := by
  rw [ha, q9c_zm q3rqZero, q9c_zm x.2.2, q9c_zm (q3rqMul x.2.1 x.2.1), q9c_za, q9c_za] at hE2
  exact hE2

/-! ## q9c-5（B4）: 2 単数枝の完全反証 -/

/-- **B4a: b 単数枝の反証**（G=0⟹a=0⟹c=0⟹b³=ζ₃²・no_cbrt_zetaSq）。 -/
theorem q9c_not_b_unit (x : q3kCar) (hu : q3kMul (q3kMul x x) x = q3kOne)
    (hbu : q3rqUnitMem x.2.1) : False := by
  have habc : q3rqMul x.1 (q3rqMul x.2.1 x.2.2) = q3rqZero := q9c_abc_zero x hu
  have hE1 := q9c_E1_zero x hu
  have hE2 := q9c_E2_zero x hu
  have hb2u : q3rqUnitMem (q3rqMul x.2.1 x.2.1) := q3rq_unit_mul hbu hbu
  -- G = 0（F3・b² 単数正則）
  have hbG0 : q3rqMul (q3rqMul x.2.1 x.2.1)
      (q3rqAdd (q3rqMul x.1 x.1) (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2))) = q3rqZero := by
    have hF3' : q3rqMul
        (q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.1)
            (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.2 x.2.2))))
          (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.2))) x.2.1
        = q3rqAdd (q3rqMul (q3rqMul x.2.1 x.2.1)
            (q3rqAdd (q3rqMul x.1 x.1) (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2))))
            (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)) x.2.2)) :=
      q9c_rawF3 q3rqRing x.1 x.2.1 x.2.2 q3rqZeta
    have key : q3rqAdd (q3rqMul (q3rqMul x.2.1 x.2.1)
        (q3rqAdd (q3rqMul x.1 x.1) (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2))))
        (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)) x.2.2)) = q3rqZero := by
      rw [← hF3', hE1]; exact q9c_zm x.2.1
    rw [habc, q9c_zm x.2.2, q9c_mz q3rqZeta, q9c_az] at key
    exact key
  have hG : q3rqAdd (q3rqMul x.1 x.1) (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2)) = q3rqZero :=
    q9ci_unit_reg_L2 (q3rqMul x.2.1 x.2.1) _ hb2u hbG0
  -- a = 0（F2・G=0・b² 単数正則）
  have hab2 : q3rqMul x.1 (q3rqMul x.2.1 x.2.1) = q3rqZero := by
    have hF2' : q3rqAdd
        (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.2)
          (q3rqMul x.1 (q3rqMul x.2.1 x.2.1)))
        (q3rqMul q3rqZeta (q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2)))
        = q3rqAdd (q3rqMul x.2.2
            (q3rqAdd (q3rqMul x.1 x.1) (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2))))
            (q3rqMul x.1 (q3rqMul x.2.1 x.2.1)) :=
      q9c_rawF2 q3rqRing x.1 x.2.1 x.2.2 q3rqZeta
    have h := hF2'.symm.trans hE2
    rw [hG, q9c_mz x.2.2, q9c_za] at h
    exact h
  have ha0 : x.1 = q3rqZero := by
    apply q9ci_unit_reg_L2 (q3rqMul x.2.1 x.2.1) x.1 hb2u
    have hcomm : q3rqMul (q3rqMul x.2.1 x.2.1) x.1 = q3rqMul x.1 (q3rqMul x.2.1 x.2.1) :=
      q3rqRing.mul_comm (q3rqMul x.2.1 x.2.1) x.1
    rw [hcomm]; exact hab2
  -- c = 0（E1'|a=0・ζ₃/b² 単数正則）
  have hzb2c : q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.2) = q3rqZero :=
    q9c_E1_a0 x ha0 hE1
  have hb2c : q3rqMul (q3rqMul x.2.1 x.2.1) x.2.2 = q3rqZero :=
    q9ci_unit_reg_L2 q3rqZeta _ q9c_zeta_unit hzb2c
  have hc0 : x.2.2 = q3rqZero :=
    q9ci_unit_reg_L2 (q3rqMul x.2.1 x.2.1) x.2.2 hb2u hb2c
  -- b³ = ζ₃²（no_cbrt_zetaSq 反証）
  have hzb3 : q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1) = q3rqOne := by
    rw [← q9c_norm_a0c0 x ha0 hc0]; exact q9c_norm_one x hu
  have hb3 : q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1 = q3rqZetaSq := by
    have h : q3rqMul q3rqZetaSq (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1))
        = q3rqMul q3rqZetaSq q3rqOne := congrArg (q3rqMul q3rqZetaSq) hzb3
    have hassoc : q3rqMul q3rqZetaSq (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1))
        = q3rqMul (q3rqMul q3rqZetaSq q3rqZeta) (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1) :=
      (q3rqRing.mul_assoc q3rqZetaSq q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)).symm
    have hzz : q3rqMul q3rqZetaSq q3rqZeta = q3rqOne := q3k_zsq_zR1
    rw [hassoc, hzz, q3rq_one_mul, q3rq_mul_one] at h
    exact h
  exact q9ci_no_cbrt_zetaSq x.2.1 hb3

/-- **B4b: c 単数枝の反証**（G=0⟹a=0⟹b=0⟹c³=ζ₃・no_cbrt_zeta）。 -/
theorem q9c_not_c_unit (x : q3kCar) (hu : q3kMul (q3kMul x x) x = q3kOne)
    (hcu : q3rqUnitMem x.2.2) : False := by
  have habc : q3rqMul x.1 (q3rqMul x.2.1 x.2.2) = q3rqZero := q9c_abc_zero x hu
  have hE1 := q9c_E1_zero x hu
  have hE2 := q9c_E2_zero x hu
  have hc2u : q3rqUnitMem (q3rqMul x.2.2 x.2.2) := q3rq_unit_mul hcu hcu
  -- G = 0（F3'・c² 単数正則）
  have hcG0 : q3rqMul (q3rqMul x.2.2 x.2.2)
      (q3rqAdd (q3rqMul x.1 x.1) (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2))) = q3rqZero := by
    have hF3'' : q3rqMul
        (q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.2)
            (q3rqMul x.1 (q3rqMul x.2.1 x.2.1)))
          (q3rqMul q3rqZeta (q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2)))) x.2.2
        = q3rqAdd (q3rqMul (q3rqMul x.2.2 x.2.2)
            (q3rqAdd (q3rqMul x.1 x.1) (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2))))
            (q3rqMul (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)) x.2.1) :=
      q9c_rawF3' q3rqRing x.1 x.2.1 x.2.2 q3rqZeta
    have key : q3rqAdd (q3rqMul (q3rqMul x.2.2 x.2.2)
        (q3rqAdd (q3rqMul x.1 x.1) (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2))))
        (q3rqMul (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)) x.2.1) = q3rqZero := by
      rw [← hF3'', hE2]; exact q9c_zm x.2.2
    rw [habc, q9c_zm x.2.1, q9c_az] at key
    exact key
  have hG : q3rqAdd (q3rqMul x.1 x.1) (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2)) = q3rqZero :=
    q9ci_unit_reg_L2 (q3rqMul x.2.2 x.2.2) _ hc2u hcG0
  -- a = 0（F1・G=0・ζ₃/c² 単数正則）
  have hac2 : q3rqMul x.1 (q3rqMul x.2.2 x.2.2) = q3rqZero := by
    have hF1' :
        q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.1)
            (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.2 x.2.2))))
          (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.2))
        = q3rqAdd (q3rqMul x.2.1
            (q3rqAdd (q3rqMul x.1 x.1) (q3rqMul q3rqZeta (q3rqMul x.2.1 x.2.2))))
            (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.2 x.2.2))) :=
      q9c_rawF1 q3rqRing x.1 x.2.1 x.2.2 q3rqZeta
    have h := hF1'.symm.trans hE1
    rw [hG, q9c_mz x.2.1, q9c_za] at h
    have hz : q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.2 x.2.2)) = q3rqZero := h
    exact q9ci_unit_reg_L2 q3rqZeta _ q9c_zeta_unit hz
  have ha0 : x.1 = q3rqZero := by
    apply q9ci_unit_reg_L2 (q3rqMul x.2.2 x.2.2) x.1 hc2u
    have hcomm : q3rqMul (q3rqMul x.2.2 x.2.2) x.1 = q3rqMul x.1 (q3rqMul x.2.2 x.2.2) :=
      q3rqRing.mul_comm (q3rqMul x.2.2 x.2.2) x.1
    rw [hcomm]; exact hac2
  -- b = 0（E2'|a=0・ζ₃/c² 単数正則）
  have hzbc2 : q3rqMul q3rqZeta (q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2)) = q3rqZero :=
    q9c_E2_a0 x ha0 hE2
  have hbc2 : q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2) = q3rqZero :=
    q9ci_unit_reg_L2 q3rqZeta _ q9c_zeta_unit hzbc2
  have hb0 : x.2.1 = q3rqZero := by
    apply q9ci_unit_reg_L2 (q3rqMul x.2.2 x.2.2) x.2.1 hc2u
    have hcomm : q3rqMul (q3rqMul x.2.2 x.2.2) x.2.1 = q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2) :=
      q3rqRing.mul_comm (q3rqMul x.2.2 x.2.2) x.2.1
    rw [hcomm]; exact hbc2
  -- c³ = ζ₃（no_cbrt_zeta 反証）
  have hzc3 : q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2) = q3rqOne := by
    rw [← q9c_norm_a0b0 x ha0 hb0]; exact q9c_norm_one x hu
  have hc3 : q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2 = q3rqZeta := by
    have h : q3rqMul q3rqZeta (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2))
        = q3rqMul q3rqZeta q3rqOne := congrArg (q3rqMul q3rqZeta) hzc3
    have hassoc : q3rqMul q3rqZeta (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2))
        = q3rqMul (q3rqMul q3rqZeta q3rqZetaSq) (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2) :=
      (q3rqRing.mul_assoc q3rqZeta q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)).symm
    have hzz : q3rqMul q3rqZeta q3rqZetaSq = q3rqOne := q3k_z_zsqR1
    rw [hassoc, hzz, q3rq_one_mul, q3rq_mul_one] at h
    exact h
  exact q9ci_no_cbrt_zeta x.2.2 hc3

/-! ## q9c-6: E1′/E2′ 座標多項式の忠実性（level-n Int rep = q9csE?fst/snd・q9cs 橋の合成） -/

/-- E1′ 第 1 座標の忠実性。 -/
theorem q9c_e1fst_valn (n : Nat) (a b c w : q3rqCar)
    (a1 a2 b1 b2 c1 c2 d1 d2 : Int)
    (ha1 : a.1.val n = Quot.mk (modCong (3 ^ n)).rel a1)
    (ha2 : a.2.val n = Quot.mk (modCong (3 ^ n)).rel a2)
    (hb1 : b.1.val n = Quot.mk (modCong (3 ^ n)).rel b1)
    (hb2 : b.2.val n = Quot.mk (modCong (3 ^ n)).rel b2)
    (hc1 : c.1.val n = Quot.mk (modCong (3 ^ n)).rel c1)
    (hc2 : c.2.val n = Quot.mk (modCong (3 ^ n)).rel c2)
    (hd1 : w.1.val n = Quot.mk (modCong (3 ^ n)).rel d1)
    (hd2 : w.2.val n = Quot.mk (modCong (3 ^ n)).rel d2) :
    (q3rqAdd (q3rqAdd (q3rqMul (q3rqMul a a) b) (q3rqMul w (q3rqMul a (q3rqMul c c))))
        (q3rqMul w (q3rqMul (q3rqMul b b) c))).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csE1fst a1 a2 b1 b2 c1 c2 d1 d2) := by
  have haa1 : (q3rqMul a a).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst a1 a2 a1 a2) :=
    q9cs_rq_mul_fst_valn n a a a1 a2 a1 a2 ha1 ha2 ha1 ha2
  have haa2 : (q3rqMul a a).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd a1 a2 a1 a2) :=
    q9cs_rq_mul_snd_valn n a a a1 a2 a1 a2 ha1 ha2 ha1 ha2
  have hA1 : (q3rqMul (q3rqMul a a) b).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) b1 b2) :=
    q9cs_rq_mul_fst_valn n (q3rqMul a a) b
      (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) b1 b2 haa1 haa2 hb1 hb2
  have hcc1 : (q3rqMul c c).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst c1 c2 c1 c2) :=
    q9cs_rq_mul_fst_valn n c c c1 c2 c1 c2 hc1 hc2 hc1 hc2
  have hcc2 : (q3rqMul c c).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd c1 c2 c1 c2) :=
    q9cs_rq_mul_snd_valn n c c c1 c2 c1 c2 hc1 hc2 hc1 hc2
  have hacc1 : (q3rqMul a (q3rqMul c c)).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2)) :=
    q9cs_rq_mul_fst_valn n a (q3rqMul c c) a1 a2
      (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) ha1 ha2 hcc1 hcc2
  have hacc2 : (q3rqMul a (q3rqMul c c)).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2)) :=
    q9cs_rq_mul_snd_valn n a (q3rqMul c c) a1 a2
      (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) ha1 ha2 hcc1 hcc2
  have hB1 : (q3rqMul w (q3rqMul a (q3rqMul c c))).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst d1 d2
            (q9csMulFst a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
            (q9csMulSnd a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))) :=
    q9cs_rq_mul_fst_valn n w (q3rqMul a (q3rqMul c c)) d1 d2
      (q9csMulFst a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
      (q9csMulSnd a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
      hd1 hd2 hacc1 hacc2
  have hbb1 : (q3rqMul b b).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst b1 b2 b1 b2) :=
    q9cs_rq_mul_fst_valn n b b b1 b2 b1 b2 hb1 hb2 hb1 hb2
  have hbb2 : (q3rqMul b b).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd b1 b2 b1 b2) :=
    q9cs_rq_mul_snd_valn n b b b1 b2 b1 b2 hb1 hb2 hb1 hb2
  have hbbc1 : (q3rqMul (q3rqMul b b) c).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2) :=
    q9cs_rq_mul_fst_valn n (q3rqMul b b) c
      (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2 hbb1 hbb2 hc1 hc2
  have hbbc2 : (q3rqMul (q3rqMul b b) c).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2) :=
    q9cs_rq_mul_snd_valn n (q3rqMul b b) c
      (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2 hbb1 hbb2 hc1 hc2
  have hC1 : (q3rqMul w (q3rqMul (q3rqMul b b) c)).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst d1 d2
            (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)
            (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)) :=
    q9cs_rq_mul_fst_valn n w (q3rqMul (q3rqMul b b) c) d1 d2
      (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)
      (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)
      hd1 hd2 hbbc1 hbbc2
  have hAB := q9cs_add_valn n (q3rqMul (q3rqMul a a) b).1
      (q3rqMul w (q3rqMul a (q3rqMul c c))).1 _ _ hA1 hB1
  have hABC := q9cs_add_valn n
      (z3.add (q3rqMul (q3rqMul a a) b).1 (q3rqMul w (q3rqMul a (q3rqMul c c))).1)
      (q3rqMul w (q3rqMul (q3rqMul b b) c)).1 _ _ hAB hC1
  exact hABC

/-- E1′ 第 2 座標の忠実性。 -/
theorem q9c_e1snd_valn (n : Nat) (a b c w : q3rqCar)
    (a1 a2 b1 b2 c1 c2 d1 d2 : Int)
    (ha1 : a.1.val n = Quot.mk (modCong (3 ^ n)).rel a1)
    (ha2 : a.2.val n = Quot.mk (modCong (3 ^ n)).rel a2)
    (hb1 : b.1.val n = Quot.mk (modCong (3 ^ n)).rel b1)
    (hb2 : b.2.val n = Quot.mk (modCong (3 ^ n)).rel b2)
    (hc1 : c.1.val n = Quot.mk (modCong (3 ^ n)).rel c1)
    (hc2 : c.2.val n = Quot.mk (modCong (3 ^ n)).rel c2)
    (hd1 : w.1.val n = Quot.mk (modCong (3 ^ n)).rel d1)
    (hd2 : w.2.val n = Quot.mk (modCong (3 ^ n)).rel d2) :
    (q3rqAdd (q3rqAdd (q3rqMul (q3rqMul a a) b) (q3rqMul w (q3rqMul a (q3rqMul c c))))
        (q3rqMul w (q3rqMul (q3rqMul b b) c))).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csE1snd a1 a2 b1 b2 c1 c2 d1 d2) := by
  have haa1 : (q3rqMul a a).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst a1 a2 a1 a2) :=
    q9cs_rq_mul_fst_valn n a a a1 a2 a1 a2 ha1 ha2 ha1 ha2
  have haa2 : (q3rqMul a a).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd a1 a2 a1 a2) :=
    q9cs_rq_mul_snd_valn n a a a1 a2 a1 a2 ha1 ha2 ha1 ha2
  have hA2 : (q3rqMul (q3rqMul a a) b).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) b1 b2) :=
    q9cs_rq_mul_snd_valn n (q3rqMul a a) b
      (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) b1 b2 haa1 haa2 hb1 hb2
  have hcc1 : (q3rqMul c c).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst c1 c2 c1 c2) :=
    q9cs_rq_mul_fst_valn n c c c1 c2 c1 c2 hc1 hc2 hc1 hc2
  have hcc2 : (q3rqMul c c).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd c1 c2 c1 c2) :=
    q9cs_rq_mul_snd_valn n c c c1 c2 c1 c2 hc1 hc2 hc1 hc2
  have hacc1 : (q3rqMul a (q3rqMul c c)).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2)) :=
    q9cs_rq_mul_fst_valn n a (q3rqMul c c) a1 a2
      (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) ha1 ha2 hcc1 hcc2
  have hacc2 : (q3rqMul a (q3rqMul c c)).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2)) :=
    q9cs_rq_mul_snd_valn n a (q3rqMul c c) a1 a2
      (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) ha1 ha2 hcc1 hcc2
  have hB2 : (q3rqMul w (q3rqMul a (q3rqMul c c))).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd d1 d2
            (q9csMulFst a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
            (q9csMulSnd a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))) :=
    q9cs_rq_mul_snd_valn n w (q3rqMul a (q3rqMul c c)) d1 d2
      (q9csMulFst a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
      (q9csMulSnd a1 a2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
      hd1 hd2 hacc1 hacc2
  have hbb1 : (q3rqMul b b).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst b1 b2 b1 b2) :=
    q9cs_rq_mul_fst_valn n b b b1 b2 b1 b2 hb1 hb2 hb1 hb2
  have hbb2 : (q3rqMul b b).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd b1 b2 b1 b2) :=
    q9cs_rq_mul_snd_valn n b b b1 b2 b1 b2 hb1 hb2 hb1 hb2
  have hbbc1 : (q3rqMul (q3rqMul b b) c).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2) :=
    q9cs_rq_mul_fst_valn n (q3rqMul b b) c
      (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2 hbb1 hbb2 hc1 hc2
  have hbbc2 : (q3rqMul (q3rqMul b b) c).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2) :=
    q9cs_rq_mul_snd_valn n (q3rqMul b b) c
      (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2 hbb1 hbb2 hc1 hc2
  have hC2 : (q3rqMul w (q3rqMul (q3rqMul b b) c)).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd d1 d2
            (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)
            (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)) :=
    q9cs_rq_mul_snd_valn n w (q3rqMul (q3rqMul b b) c) d1 d2
      (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)
      (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) c1 c2)
      hd1 hd2 hbbc1 hbbc2
  have hAB := q9cs_add_valn n (q3rqMul (q3rqMul a a) b).2
      (q3rqMul w (q3rqMul a (q3rqMul c c))).2 _ _ hA2 hB2
  have hABC := q9cs_add_valn n
      (z3.add (q3rqMul (q3rqMul a a) b).2 (q3rqMul w (q3rqMul a (q3rqMul c c))).2)
      (q3rqMul w (q3rqMul (q3rqMul b b) c)).2 _ _ hAB hC2
  exact hABC

/-- E2′ 第 1 座標の忠実性。 -/
theorem q9c_e2fst_valn (n : Nat) (a b c w : q3rqCar)
    (a1 a2 b1 b2 c1 c2 d1 d2 : Int)
    (ha1 : a.1.val n = Quot.mk (modCong (3 ^ n)).rel a1)
    (ha2 : a.2.val n = Quot.mk (modCong (3 ^ n)).rel a2)
    (hb1 : b.1.val n = Quot.mk (modCong (3 ^ n)).rel b1)
    (hb2 : b.2.val n = Quot.mk (modCong (3 ^ n)).rel b2)
    (hc1 : c.1.val n = Quot.mk (modCong (3 ^ n)).rel c1)
    (hc2 : c.2.val n = Quot.mk (modCong (3 ^ n)).rel c2)
    (hd1 : w.1.val n = Quot.mk (modCong (3 ^ n)).rel d1)
    (hd2 : w.2.val n = Quot.mk (modCong (3 ^ n)).rel d2) :
    (q3rqAdd (q3rqAdd (q3rqMul (q3rqMul a a) c) (q3rqMul a (q3rqMul b b)))
        (q3rqMul w (q3rqMul b (q3rqMul c c)))).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csE2fst a1 a2 b1 b2 c1 c2 d1 d2) := by
  have haa1 : (q3rqMul a a).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst a1 a2 a1 a2) :=
    q9cs_rq_mul_fst_valn n a a a1 a2 a1 a2 ha1 ha2 ha1 ha2
  have haa2 : (q3rqMul a a).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd a1 a2 a1 a2) :=
    q9cs_rq_mul_snd_valn n a a a1 a2 a1 a2 ha1 ha2 ha1 ha2
  have hP1 : (q3rqMul (q3rqMul a a) c).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) c1 c2) :=
    q9cs_rq_mul_fst_valn n (q3rqMul a a) c
      (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) c1 c2 haa1 haa2 hc1 hc2
  have hbb1 : (q3rqMul b b).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst b1 b2 b1 b2) :=
    q9cs_rq_mul_fst_valn n b b b1 b2 b1 b2 hb1 hb2 hb1 hb2
  have hbb2 : (q3rqMul b b).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd b1 b2 b1 b2) :=
    q9cs_rq_mul_snd_valn n b b b1 b2 b1 b2 hb1 hb2 hb1 hb2
  have hQ1 : (q3rqMul a (q3rqMul b b)).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst a1 a2 (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2)) :=
    q9cs_rq_mul_fst_valn n a (q3rqMul b b) a1 a2
      (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) ha1 ha2 hbb1 hbb2
  have hcc1 : (q3rqMul c c).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst c1 c2 c1 c2) :=
    q9cs_rq_mul_fst_valn n c c c1 c2 c1 c2 hc1 hc2 hc1 hc2
  have hcc2 : (q3rqMul c c).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd c1 c2 c1 c2) :=
    q9cs_rq_mul_snd_valn n c c c1 c2 c1 c2 hc1 hc2 hc1 hc2
  have hbcc1 : (q3rqMul b (q3rqMul c c)).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2)) :=
    q9cs_rq_mul_fst_valn n b (q3rqMul c c) b1 b2
      (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) hb1 hb2 hcc1 hcc2
  have hbcc2 : (q3rqMul b (q3rqMul c c)).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2)) :=
    q9cs_rq_mul_snd_valn n b (q3rqMul c c) b1 b2
      (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) hb1 hb2 hcc1 hcc2
  have hR1 : (q3rqMul w (q3rqMul b (q3rqMul c c))).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst d1 d2
            (q9csMulFst b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
            (q9csMulSnd b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))) :=
    q9cs_rq_mul_fst_valn n w (q3rqMul b (q3rqMul c c)) d1 d2
      (q9csMulFst b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
      (q9csMulSnd b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
      hd1 hd2 hbcc1 hbcc2
  have hPQ := q9cs_add_valn n (q3rqMul (q3rqMul a a) c).1
      (q3rqMul a (q3rqMul b b)).1 _ _ hP1 hQ1
  have hPQR := q9cs_add_valn n
      (z3.add (q3rqMul (q3rqMul a a) c).1 (q3rqMul a (q3rqMul b b)).1)
      (q3rqMul w (q3rqMul b (q3rqMul c c))).1 _ _ hPQ hR1
  exact hPQR

/-- E2′ 第 2 座標の忠実性。 -/
theorem q9c_e2snd_valn (n : Nat) (a b c w : q3rqCar)
    (a1 a2 b1 b2 c1 c2 d1 d2 : Int)
    (ha1 : a.1.val n = Quot.mk (modCong (3 ^ n)).rel a1)
    (ha2 : a.2.val n = Quot.mk (modCong (3 ^ n)).rel a2)
    (hb1 : b.1.val n = Quot.mk (modCong (3 ^ n)).rel b1)
    (hb2 : b.2.val n = Quot.mk (modCong (3 ^ n)).rel b2)
    (hc1 : c.1.val n = Quot.mk (modCong (3 ^ n)).rel c1)
    (hc2 : c.2.val n = Quot.mk (modCong (3 ^ n)).rel c2)
    (hd1 : w.1.val n = Quot.mk (modCong (3 ^ n)).rel d1)
    (hd2 : w.2.val n = Quot.mk (modCong (3 ^ n)).rel d2) :
    (q3rqAdd (q3rqAdd (q3rqMul (q3rqMul a a) c) (q3rqMul a (q3rqMul b b)))
        (q3rqMul w (q3rqMul b (q3rqMul c c)))).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csE2snd a1 a2 b1 b2 c1 c2 d1 d2) := by
  have haa1 : (q3rqMul a a).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst a1 a2 a1 a2) :=
    q9cs_rq_mul_fst_valn n a a a1 a2 a1 a2 ha1 ha2 ha1 ha2
  have haa2 : (q3rqMul a a).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd a1 a2 a1 a2) :=
    q9cs_rq_mul_snd_valn n a a a1 a2 a1 a2 ha1 ha2 ha1 ha2
  have hP2 : (q3rqMul (q3rqMul a a) c).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) c1 c2) :=
    q9cs_rq_mul_snd_valn n (q3rqMul a a) c
      (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) c1 c2 haa1 haa2 hc1 hc2
  have hbb1 : (q3rqMul b b).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst b1 b2 b1 b2) :=
    q9cs_rq_mul_fst_valn n b b b1 b2 b1 b2 hb1 hb2 hb1 hb2
  have hbb2 : (q3rqMul b b).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd b1 b2 b1 b2) :=
    q9cs_rq_mul_snd_valn n b b b1 b2 b1 b2 hb1 hb2 hb1 hb2
  have hQ2 : (q3rqMul a (q3rqMul b b)).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd a1 a2 (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2)) :=
    q9cs_rq_mul_snd_valn n a (q3rqMul b b) a1 a2
      (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) ha1 ha2 hbb1 hbb2
  have hcc1 : (q3rqMul c c).1.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulFst c1 c2 c1 c2) :=
    q9cs_rq_mul_fst_valn n c c c1 c2 c1 c2 hc1 hc2 hc1 hc2
  have hcc2 : (q3rqMul c c).2.val n
      = Quot.mk (modCong (3 ^ n)).rel (q9csMulSnd c1 c2 c1 c2) :=
    q9cs_rq_mul_snd_valn n c c c1 c2 c1 c2 hc1 hc2 hc1 hc2
  have hbcc1 : (q3rqMul b (q3rqMul c c)).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2)) :=
    q9cs_rq_mul_fst_valn n b (q3rqMul c c) b1 b2
      (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) hb1 hb2 hcc1 hcc2
  have hbcc2 : (q3rqMul b (q3rqMul c c)).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2)) :=
    q9cs_rq_mul_snd_valn n b (q3rqMul c c) b1 b2
      (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) hb1 hb2 hcc1 hcc2
  have hR2 : (q3rqMul w (q3rqMul b (q3rqMul c c))).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd d1 d2
            (q9csMulFst b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
            (q9csMulSnd b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))) :=
    q9cs_rq_mul_snd_valn n w (q3rqMul b (q3rqMul c c)) d1 d2
      (q9csMulFst b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
      (q9csMulSnd b1 b2 (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2))
      hd1 hd2 hbcc1 hbcc2
  have hPQ := q9cs_add_valn n (q3rqMul (q3rqMul a a) c).2
      (q3rqMul a (q3rqMul b b)).2 _ _ hP2 hQ2
  have hPQR := q9cs_add_valn n
      (z3.add (q3rqMul (q3rqMul a a) c).2 (q3rqMul a (q3rqMul b b)).2)
      (q3rqMul w (q3rqMul b (q3rqMul c c))).2 _ _ hPQ hR2
  exact hPQR

/-! ## q9c-7（B5）: 生存枝で a は O_{L₂} 単数（3∤a₁） -/

/-- **B5: 生存枝の a 単数性** — b,c 非単数（3∣b₁,3∣c₁）ならば N(x)=1 の
    第 1 座標 level-1 が a₁³≡1 mod 3 を強制し 3∤a₁（x.1.1.val 1 ≠ [0]）。 -/
theorem q9c_a_unit (x : q3kCar) (hu : q3kMul (q3kMul x x) x = q3kOne)
    (hbge : x.2.1.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0)
    (hcge : x.2.2.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0) :
    x.1.1.val 1 ≠ Quot.mk (modCong (3 ^ 1)).rel 0 := by
  intro hz
  -- N = a³ + ζ₃b³ + ζ₃²c³（abc=0 で −3ζ₃abc を消去）
  have habc' : q3rqMul (q3rqMul x.1 x.2.1) x.2.2 = q3rqZero := by
    have hassoc : q3rqMul (q3rqMul x.1 x.2.1) x.2.2
        = q3rqMul x.1 (q3rqMul x.2.1 x.2.2) := q3rqRing.mul_assoc x.1 x.2.1 x.2.2
    rw [hassoc]; exact q9c_abc_zero x hu
  have hNred : q3kNormBase x
      = q3rqAdd (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.1)
          (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)))
          (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)) := by
    show q3rqAdd (q3rqAdd (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.1)
        (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)))
        (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)))
      (q3rqNeg (q3rqMul q3kThree (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.1 x.2.1) x.2.2)))) = _
    rw [habc', q9c_mz q3rqZeta, q9c_mz q3kThree, q9c_nz, q9c_az]
  -- reps
  obtain ⟨a1, ha1⟩ := Quot.exists_rep (x.1.1.val 1)
  obtain ⟨a2, ha2⟩ := Quot.exists_rep (x.1.2.val 1)
  obtain ⟨b1, hb1⟩ := Quot.exists_rep (x.2.1.1.val 1)
  obtain ⟨b2, hb2⟩ := Quot.exists_rep (x.2.1.2.val 1)
  obtain ⟨c1, hc1⟩ := Quot.exists_rep (x.2.2.1.val 1)
  obtain ⟨c2, hc2⟩ := Quot.exists_rep (x.2.2.2.val 1)
  obtain ⟨d1, hd1⟩ := Quot.exists_rep (q3rqZeta.1.val 1)
  obtain ⟨d2, hd2⟩ := Quot.exists_rep (q3rqZeta.2.val 1)
  obtain ⟨e1, he1⟩ := Quot.exists_rep (q3rqZetaSq.1.val 1)
  obtain ⟨e2, he2⟩ := Quot.exists_rep (q3rqZetaSq.2.val 1)
  -- a³ 第 1 座標
  have haa1 := q9cs_rq_mul_fst_valn 1 x.1 x.1 a1 a2 a1 a2 ha1.symm ha2.symm ha1.symm ha2.symm
  have haa2 := q9cs_rq_mul_snd_valn 1 x.1 x.1 a1 a2 a1 a2 ha1.symm ha2.symm ha1.symm ha2.symm
  have hA1 := q9cs_rq_mul_fst_valn 1 (q3rqMul x.1 x.1) x.1
    (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) a1 a2 haa1 haa2 ha1.symm ha2.symm
  -- b³ 両座標 → ζ₃b³ 第 1 座標
  have hbb1 := q9cs_rq_mul_fst_valn 1 x.2.1 x.2.1 b1 b2 b1 b2 hb1.symm hb2.symm hb1.symm hb2.symm
  have hbb2 := q9cs_rq_mul_snd_valn 1 x.2.1 x.2.1 b1 b2 b1 b2 hb1.symm hb2.symm hb1.symm hb2.symm
  have hb3f := q9cs_rq_mul_fst_valn 1 (q3rqMul x.2.1 x.2.1) x.2.1
    (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2 hbb1 hbb2 hb1.symm hb2.symm
  have hb3s := q9cs_rq_mul_snd_valn 1 (q3rqMul x.2.1 x.2.1) x.2.1
    (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2 hbb1 hbb2 hb1.symm hb2.symm
  have hZb := q9cs_rq_mul_fst_valn 1 q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)
    d1 d2 (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2)
    (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2)
    hd1.symm hd2.symm hb3f hb3s
  -- c³ 両座標 → ζ₃²c³ 第 1 座標
  have hcc1 := q9cs_rq_mul_fst_valn 1 x.2.2 x.2.2 c1 c2 c1 c2 hc1.symm hc2.symm hc1.symm hc2.symm
  have hcc2 := q9cs_rq_mul_snd_valn 1 x.2.2 x.2.2 c1 c2 c1 c2 hc1.symm hc2.symm hc1.symm hc2.symm
  have hc3f := q9cs_rq_mul_fst_valn 1 (q3rqMul x.2.2 x.2.2) x.2.2
    (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2 hcc1 hcc2 hc1.symm hc2.symm
  have hc3s := q9cs_rq_mul_snd_valn 1 (q3rqMul x.2.2 x.2.2) x.2.2
    (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2 hcc1 hcc2 hc1.symm hc2.symm
  have hZc := q9cs_rq_mul_fst_valn 1 q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)
    e1 e2 (q9csMulFst (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2)
    (q9csMulSnd (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2)
    he1.symm he2.symm hc3f hc3s
  -- 合算: N.1.val 1 = [(A + Bt) + Ct]
  have hAB := q9cs_add_valn 1 (q3rqMul (q3rqMul x.1 x.1) x.1).1
    (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)).1 _ _ hA1 hZb
  have hABC := q9cs_add_valn 1
    (z3.add (q3rqMul (q3rqMul x.1 x.1) x.1).1
      (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)).1)
    (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)).1 _ _ hAB hZc
  have hN1 : (q3kNormBase x).1.val 1
      = Quot.mk (modCong (3 ^ 1)).rel
        (((q9csMulFst (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) a1 a2)
          + (q9csMulFst d1 d2
              (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2)
              (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2)))
          + (q9csMulFst e1 e2
              (q9csMulFst (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2)
              (q9csMulSnd (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2))) := by
    rw [hNred]; exact hABC
  have hNone : (q3kNormBase x).1.val 1 = Quot.mk (modCong (3 ^ 1)).rel 1 := by
    rw [q9c_norm_one x hu]
    show (zpOne 3).val 1 = Quot.mk (modCong (3 ^ 1)).rel 1
    rfl
  have heq := hN1.symm.trans hNone
  have hdvd := quot_exact intGrp (modCong (3 ^ 1)) heq
  rw [Nat.pow_one] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  -- 3∣a1, 3∣b1, 3∣c1
  have h3a : ((3 : Nat) : Int) ∣ a1 := by
    have h := ha1.trans hz
    have hd := quot_exact intGrp (modCong (3 ^ 1)) h
    rw [Nat.pow_one] at hd
    obtain ⟨t, ht⟩ := hd; exact ⟨t, by omega⟩
  have h3b : ((3 : Nat) : Int) ∣ b1 := by
    have h := hb1.trans hbge
    have hd := quot_exact intGrp (modCong (3 ^ 1)) h
    rw [Nat.pow_one] at hd
    obtain ⟨t, ht⟩ := hd; exact ⟨t, by omega⟩
  have h3c : ((3 : Nat) : Int) ∣ c1 := by
    have h := hc1.trans hcge
    have hd := quot_exact intGrp (modCong (3 ^ 1)) h
    rw [Nat.pow_one] at hd
    obtain ⟨t, ht⟩ := hd; exact ⟨t, by omega⟩
  -- 各立方項は 3 で割れる
  have h3A : ((3 : Nat) : Int)
      ∣ q9csMulFst (q9csMulFst a1 a2 a1 a2) (q9csMulSnd a1 a2 a1 a2) a1 a2 := by
    show ((3 : Nat) : Int)
      ∣ ((q9csMulFst a1 a2 a1 a2) * a1 - 3 * ((q9csMulSnd a1 a2 a1 a2) * a2))
    have hm := q9cs_dvd_mull (q9csMulFst a1 a2 a1 a2) h3a
    omega
  have h3Bf : ((3 : Nat) : Int)
      ∣ q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2 := by
    show ((3 : Nat) : Int)
      ∣ ((q9csMulFst b1 b2 b1 b2) * b1 - 3 * ((q9csMulSnd b1 b2 b1 b2) * b2))
    have hm := q9cs_dvd_mull (q9csMulFst b1 b2 b1 b2) h3b
    omega
  have h3Bt : ((3 : Nat) : Int)
      ∣ q9csMulFst d1 d2
          (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2)
          (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2) := by
    show ((3 : Nat) : Int)
      ∣ (d1 * (q9csMulFst (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2)
          - 3 * (d2 * (q9csMulSnd (q9csMulFst b1 b2 b1 b2) (q9csMulSnd b1 b2 b1 b2) b1 b2)))
    have hm := q9cs_dvd_mull d1 h3Bf
    omega
  have h3Cf : ((3 : Nat) : Int)
      ∣ q9csMulFst (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2 := by
    show ((3 : Nat) : Int)
      ∣ ((q9csMulFst c1 c2 c1 c2) * c1 - 3 * ((q9csMulSnd c1 c2 c1 c2) * c2))
    have hm := q9cs_dvd_mull (q9csMulFst c1 c2 c1 c2) h3c
    omega
  have h3Ct : ((3 : Nat) : Int)
      ∣ q9csMulFst e1 e2
          (q9csMulFst (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2)
          (q9csMulSnd (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2) := by
    show ((3 : Nat) : Int)
      ∣ (e1 * (q9csMulFst (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2)
          - 3 * (e2 * (q9csMulSnd (q9csMulFst c1 c2 c1 c2) (q9csMulSnd c1 c2 c1 c2) c1 c2)))
    have hm := q9cs_dvd_mull e1 h3Cf
    omega
  omega

/-! ## q9c-8（B6）: 交互パリティ同時降下（q9cs 消費）で b = c = 0 -/

/-- 任意 z3 元のレベル 0 値は [0]（mod 1）。 -/
theorem q9c_val0 (w : z3.carrier) : w.val 0 = Quot.mk (modCong (3 ^ 0)).rel 0 := by
  obtain ⟨r, hr⟩ := Quot.exists_rep (w.val 0)
  rw [← hr]; apply Quot.sound
  show ((3 ^ 0 : Nat) : Int) ∣ (r - 0)
  rw [Nat.pow_zero]; exact ⟨r, by omega⟩

/-- rep が 3^n で割れる ⟹ レベル n 値は [0]。 -/
theorem q9c_valz_of_dvd (w : z3.carrier) (n : Nat) (j : Int)
    (hval : w.val n = Quot.mk (modCong (3 ^ n)).rel j)
    (hd : ((3 ^ n : Nat) : Int) ∣ j) :
    w.val n = Quot.mk (modCong (3 ^ n)).rel 0 := by
  rw [hval]; apply Quot.sound
  show ((3 ^ n : Nat) : Int) ∣ (j - 0)
  obtain ⟨t, ht⟩ := hd; exact ⟨t, by omega⟩

/-- 全レベルで [0] ⟹ z3.zero（∩ₘ3ᵐℤ₃=0・Subtype.ext funext）。 -/
theorem q9c_zero_of_allval (w : z3.carrier)
    (h : ∀ n, w.val n = Quot.mk (modCong (3 ^ n)).rel 0) : w = z3.zero := by
  apply Subtype.ext
  funext n
  show w.val n = Quot.mk (modCong (3 ^ n)).rel 0
  exact h n

/-- **B6 核: 交互降下（全レベル）** — a 単数・b,c 非単数・E1'=E2'=0 から、
    b,c の 4 つの ℤ₃ 座標が全レベルで [0]。 -/
theorem q9c_bc_val (x : q3kCar) (hu : q3kMul (q3kMul x x) x = q3kOne)
    (hanz : x.1.1.val 1 ≠ Quot.mk (modCong (3 ^ 1)).rel 0)
    (hbge : x.2.1.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0)
    (hcge : x.2.2.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0) :
    ∀ n, x.2.1.1.val n = Quot.mk (modCong (3 ^ n)).rel 0
      ∧ x.2.1.2.val n = Quot.mk (modCong (3 ^ n)).rel 0
      ∧ x.2.2.1.val n = Quot.mk (modCong (3 ^ n)).rel 0
      ∧ x.2.2.2.val n = Quot.mk (modCong (3 ^ n)).rel 0 := by
  intro n
  induction n with
  | zero => exact ⟨q9c_val0 _, q9c_val0 _, q9c_val0 _, q9c_val0 _⟩
  | succ m ih =>
    obtain ⟨ihb1, ihb2, ihc1, ihc2⟩ := ih
    obtain ⟨a1, ha1⟩ := Quot.exists_rep (x.1.1.val (m + 1))
    obtain ⟨a2, ha2⟩ := Quot.exists_rep (x.1.2.val (m + 1))
    obtain ⟨b1, hb1⟩ := Quot.exists_rep (x.2.1.1.val (m + 1))
    obtain ⟨b2, hb2⟩ := Quot.exists_rep (x.2.1.2.val (m + 1))
    obtain ⟨c1, hc1⟩ := Quot.exists_rep (x.2.2.1.val (m + 1))
    obtain ⟨c2, hc2⟩ := Quot.exists_rep (x.2.2.2.val (m + 1))
    obtain ⟨d1, hd1⟩ := Quot.exists_rep (q3rqZeta.1.val (m + 1))
    obtain ⟨d2, hd2⟩ := Quot.exists_rep (q3rqZeta.2.val (m + 1))
    have hna : ¬ ((3 : Nat) : Int) ∣ a1 := by
      intro h3a
      apply hanz
      have hp := q9c_val_proj_gen x.1.1 1 (m + 1) a1 (by omega) ha1.symm
      rw [hp]; apply Quot.sound
      show ((3 ^ 1 : Nat) : Int) ∣ (a1 - 0)
      obtain ⟨t, ht⟩ := h3a; exact ⟨t, by rw [Nat.pow_one]; omega⟩
    have hE1fv := q9c_e1fst_valn (m + 1) x.1 x.2.1 x.2.2 q3rqZeta a1 a2 b1 b2 c1 c2 d1 d2
      ha1.symm ha2.symm hb1.symm hb2.symm hc1.symm hc2.symm hd1.symm hd2.symm
    have hE1sv := q9c_e1snd_valn (m + 1) x.1 x.2.1 x.2.2 q3rqZeta a1 a2 b1 b2 c1 c2 d1 d2
      ha1.symm ha2.symm hb1.symm hb2.symm hc1.symm hc2.symm hd1.symm hd2.symm
    have hE2fv := q9c_e2fst_valn (m + 1) x.1 x.2.1 x.2.2 q3rqZeta a1 a2 b1 b2 c1 c2 d1 d2
      ha1.symm ha2.symm hb1.symm hb2.symm hc1.symm hc2.symm hd1.symm hd2.symm
    have hE2sv := q9c_e2snd_valn (m + 1) x.1 x.2.1 x.2.2 q3rqZeta a1 a2 b1 b2 c1 c2 d1 d2
      ha1.symm ha2.symm hb1.symm hb2.symm hc1.symm hc2.symm hd1.symm hd2.symm
    have hd_E1f := q9cs_zero_rep_dvd _ (congrArg Prod.fst (q9c_E1_zero x hu)) (m + 1)
      (q9csE1fst a1 a2 b1 b2 c1 c2 d1 d2) hE1fv
    have hd_E1s := q9cs_zero_rep_dvd _ (congrArg Prod.snd (q9c_E1_zero x hu)) (m + 1)
      (q9csE1snd a1 a2 b1 b2 c1 c2 d1 d2) hE1sv
    have hd_E2f := q9cs_zero_rep_dvd _ (congrArg Prod.fst (q9c_E2_zero x hu)) (m + 1)
      (q9csE2fst a1 a2 b1 b2 c1 c2 d1 d2) hE2fv
    have hd_E2s := q9cs_zero_rep_dvd _ (congrArg Prod.snd (q9c_E2_zero x hu)) (m + 1)
      (q9csE2snd a1 a2 b1 b2 c1 c2 d1 d2) hE2sv
    have hdb1m : ((3 ^ m : Nat) : Int) ∣ b1 := by
      have hp := q9c_val_proj_gen x.2.1.1 m (m + 1) b1 (Nat.le_succ m) hb1.symm
      have h := hp.symm.trans ihb1
      have hd := quot_exact intGrp (modCong (3 ^ m)) h
      obtain ⟨t, ht⟩ := hd; exact ⟨t, by omega⟩
    have hdb2m : ((3 ^ m : Nat) : Int) ∣ b2 := by
      have hp := q9c_val_proj_gen x.2.1.2 m (m + 1) b2 (Nat.le_succ m) hb2.symm
      have h := hp.symm.trans ihb2
      have hd := quot_exact intGrp (modCong (3 ^ m)) h
      obtain ⟨t, ht⟩ := hd; exact ⟨t, by omega⟩
    have hdc1m : ((3 ^ m : Nat) : Int) ∣ c1 := by
      have hp := q9c_val_proj_gen x.2.2.1 m (m + 1) c1 (Nat.le_succ m) hc1.symm
      have h := hp.symm.trans ihc1
      have hd := quot_exact intGrp (modCong (3 ^ m)) h
      obtain ⟨t, ht⟩ := hd; exact ⟨t, by omega⟩
    have hdc2m : ((3 ^ m : Nat) : Int) ∣ c2 := by
      have hp := q9c_val_proj_gen x.2.2.2 m (m + 1) c2 (Nat.le_succ m) hc2.symm
      have h := hp.symm.trans ihc2
      have hd := quot_exact intGrp (modCong (3 ^ m)) h
      obtain ⟨t, ht⟩ := hd; exact ⟨t, by omega⟩
    have hdb1_1 : ((3 ^ 1 : Nat) : Int) ∣ b1 := by
      have hp := q9c_val_proj_gen x.2.1.1 1 (m + 1) b1 (by omega) hb1.symm
      have h := hp.symm.trans hbge
      have hd := quot_exact intGrp (modCong (3 ^ 1)) h
      obtain ⟨t, ht⟩ := hd; exact ⟨t, by omega⟩
    have hdc1_1 : ((3 ^ 1 : Nat) : Int) ∣ c1 := by
      have hp := q9c_val_proj_gen x.2.2.1 1 (m + 1) c1 (by omega) hc1.symm
      have h := hp.symm.trans hcge
      have hd := quot_exact intGrp (modCong (3 ^ 1)) h
      obtain ⟨t, ht⟩ := hd; exact ⟨t, by omega⟩
    cases m with
    | zero =>
      have hodd := q9cs_descent_odd 0 a1 a2 b1 b2 c1 c2 d1 d2 hna
        hdb1_1 (q9cs_pow_zero_dvd b2) hdc1_1 (q9cs_pow_zero_dvd c2) hd_E1s hd_E2s
      exact ⟨q9c_valz_of_dvd x.2.1.1 (0 + 1) b1 hb1.symm hdb1_1,
        q9c_valz_of_dvd x.2.1.2 (0 + 1) b2 hb2.symm hodd.1,
        q9c_valz_of_dvd x.2.2.1 (0 + 1) c1 hc1.symm hdc1_1,
        q9c_valz_of_dvd x.2.2.2 (0 + 1) c2 hc2.symm hodd.2⟩
    | succ q =>
      have heven := q9cs_descent_even (q + 1) (by omega) a1 a2 b1 b2 c1 c2 d1 d2 hna
        hdb1m hdb2m hdc1m hdc2m hd_E1f hd_E2f
      have hodd := q9cs_descent_odd (q + 1) a1 a2 b1 b2 c1 c2 d1 d2 hna
        heven.1 hdb2m heven.2 hdc2m hd_E1s hd_E2s
      exact ⟨q9c_valz_of_dvd x.2.1.1 (q + 1 + 1) b1 hb1.symm heven.1,
        q9c_valz_of_dvd x.2.1.2 (q + 1 + 1) b2 hb2.symm hodd.1,
        q9c_valz_of_dvd x.2.2.1 (q + 1 + 1) c1 hc1.symm heven.2,
        q9c_valz_of_dvd x.2.2.2 (q + 1 + 1) c2 hc2.symm hodd.2⟩

/-- **B6: b = c = 0**（全レベル降下から座標消滅）。 -/
theorem q9c_bc_zero (x : q3kCar) (hu : q3kMul (q3kMul x x) x = q3kOne)
    (hanz : x.1.1.val 1 ≠ Quot.mk (modCong (3 ^ 1)).rel 0)
    (hbge : x.2.1.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0)
    (hcge : x.2.2.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0) :
    x.2.1 = q3rqZero ∧ x.2.2 = q3rqZero := by
  have hall := q9c_bc_val x hu hanz hbge hcge
  refine ⟨q3rq_ext ?_ ?_, q3rq_ext ?_ ?_⟩
  · exact q9c_zero_of_allval x.2.1.1 (fun n => (hall n).1)
  · exact q9c_zero_of_allval x.2.1.2 (fun n => (hall n).2.1)
  · exact q9c_zero_of_allval x.2.2.1 (fun n => (hall n).2.2.1)
  · exact q9c_zero_of_allval x.2.2.2 (fun n => (hall n).2.2.2)

/-! ## q9c-9（B7）: O_M 内 μ₃ 完全性（★★ B1–B6 束ね＋q3mc 消費 2） -/

/-- **B7（★★）: O_M 内 μ₃ 完全性** — x³=1 ⟹ x ∈ μ₃(L₂) ⊂ O_M（対角）。
    carrier レベル・単数性を仮定に取らない（§6.2 消費者互換）。 -/
theorem q9c_m_mu3_complete (x : q3kCar) (hu : q3kMul (q3kMul x x) x = q3kOne) :
    x = q3kOne ∨ x = ((q3rqZeta, q3rqZero, q3rqZero) : q3kCar)
      ∨ x = ((q3rqZetaSq, q3rqZero, q3rqZero) : q3kCar) := by
  obtain ⟨b1, hb1⟩ := Quot.exists_rep (x.2.1.1.val 1)
  obtain ⟨b2, hb2⟩ := Quot.exists_rep (x.2.1.2.val 1)
  obtain ⟨c1, hc1⟩ := Quot.exists_rep (x.2.2.1.val 1)
  obtain ⟨c2, hc2⟩ := Quot.exists_rep (x.2.2.2.val 1)
  cases (inferInstance : Decidable (((3 : Nat) : Int) ∣ b1)) with
  | isFalse hb0 =>
    exact (q9c_not_b_unit x hu
      (q9c_unit_of_fst_nondvd x.2.1 b1 b2 hb1.symm hb2.symm hb0)).elim
  | isTrue hb0 =>
    have hbge : x.2.1.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := by
      rw [← hb1]; apply Quot.sound
      show ((3 ^ 1 : Nat) : Int) ∣ (b1 - 0)
      obtain ⟨t, ht⟩ := hb0; exact ⟨t, by rw [Nat.pow_one]; omega⟩
    cases (inferInstance : Decidable (((3 : Nat) : Int) ∣ c1)) with
    | isFalse hc0 =>
      exact (q9c_not_c_unit x hu
        (q9c_unit_of_fst_nondvd x.2.2 c1 c2 hc1.symm hc2.symm hc0)).elim
    | isTrue hc0 =>
      have hcge : x.2.2.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := by
        rw [← hc1]; apply Quot.sound
        show ((3 ^ 1 : Nat) : Int) ∣ (c1 - 0)
        obtain ⟨t, ht⟩ := hc0; exact ⟨t, by rw [Nat.pow_one]; omega⟩
      have hanz := q9c_a_unit x hu hbge hcge
      obtain ⟨hb0z, hc0z⟩ := q9c_bc_zero x hu hanz hbge hcge
      have hxe : x = q3kEmbed x.1 := q3k_ext rfl hb0z hc0z
      have hcube : q3rqMul (q3rqMul x.1 x.1) x.1 = q3rqOne := by
        apply q3k_embed_inj
        rw [← q3k_embed_mul (q3rqMul x.1 x.1) x.1, ← q3k_embed_mul x.1 x.1,
            ← hxe, hu, q3k_embed_one]
      obtain h1 | hz | hzsq := q3mc_mu3_complete x.1 hcube
      · left; rw [hxe, h1]; exact q3k_embed_one
      · right; left; rw [hxe, hz]; rfl
      · right; right; rw [hxe, hzsq]; rfl

/-! ## q9c-10（B8）: 塔分解で μ₉ 完全性（★★★ 9 乗展開なし・Y-捻り） -/

/-- 可換環での立方の乗法: (xy)³ = x³·y³。 -/
theorem q9c_cube_mul (x y : q3kCar) :
    q3kMul (q3kMul (q3kMul x y) (q3kMul x y)) (q3kMul x y)
    = q3kMul (q3kMul (q3kMul x x) x) (q3kMul (q3kMul y y) y) := by
  rw [q3k_kM_eq, q3kRing.mul_mul_mul_comm x y x y,
      q3kRing.mul_mul_mul_comm (q3kRing.mul x x) (q3kRing.mul y y) x y]

/-- **Y⁻¹ = ζ₃²·Y²**（実元・Y·Y⁻¹=1）。 -/
def q9cYinv : q3kCar := q3kMul (q3kEmbed q3rqZetaSq) (q3kMul q3kZeta9 q3kZeta9)

/-- Y⁻¹ の座標形 = (0,0,ζ₃²)。 -/
theorem q9c_Yinv_tup : q9cYinv = ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) := by
  show q3kMul (q3kEmbed q3rqZetaSq) (q3kMul q3kZeta9 q3kZeta9) = _
  rw [q3k_zeta9_sq]
  apply q3k_ext
  · show q3rqAdd (q3rqMul q3rqZetaSq q3rqZero)
        (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero q3rqOne) (q3rqMul q3rqZero q3rqZero)))
        = q3rqZero
    rw [q9c_mz q3rqZetaSq, q9c_za, q9c_zm q3rqOne, q9c_zm q3rqZero, q9c_za, q9c_mz q3rqZeta]
  · show q3rqAdd (q3rqAdd (q3rqMul q3rqZetaSq q3rqZero) (q3rqMul q3rqZero q3rqZero))
        (q3rqMul q3rqZeta (q3rqMul q3rqZero q3rqOne)) = q3rqZero
    rw [q9c_mz q3rqZetaSq, q9c_zm q3rqZero, q9c_za, q9c_za, q9c_zm q3rqOne, q9c_mz q3rqZeta]
  · show q3rqAdd (q3rqAdd (q3rqMul q3rqZetaSq q3rqOne) (q3rqMul q3rqZero q3rqZero))
        (q3rqMul q3rqZero q3rqZero) = q3rqZetaSq
    rw [q3rq_mul_one q3rqZetaSq, q9c_zm q3rqZero, q9c_az, q9c_az]

/-- Y⁻¹·Y = 1。 -/
theorem q9c_Yinv_mul_Y : q3kMul q9cYinv q3kZeta9 = q3kOne := by
  show q3kMul (q3kMul (q3kEmbed q3rqZetaSq) (q3kMul q3kZeta9 q3kZeta9)) q3kZeta9 = q3kOne
  rw [q3k_mul_assoc (q3kEmbed q3rqZetaSq) (q3kMul q3kZeta9 q3kZeta9) q3kZeta9, q3k_zeta9_cube,
      q3k_embed_mul, show q3rqMul q3rqZetaSq q3rqZeta = q3rqOne from q3k_zsq_zR1, q3k_embed_one]

/-- Y·Y⁻¹ = 1。 -/
theorem q9c_Y_mul_Yinv : q3kMul q3kZeta9 q9cYinv = q3kOne := by
  rw [q3k_mul_comm]; exact q9c_Yinv_mul_Y

/-- (Y⁻¹)³ = ζ₃²（embed）。 -/
theorem q9c_Yinv3 : q3kMul (q3kMul q9cYinv q9cYinv) q9cYinv = q3kEmbed q3rqZetaSq := by
  have h1 : q3kMul (q3kMul (q3kMul q9cYinv q9cYinv) q9cYinv) (q3kEmbed q3rqZeta) = q3kOne := by
    rw [← q3k_zeta9_cube, ← q9c_cube_mul q9cYinv q3kZeta9, q9c_Yinv_mul_Y, q3k_one_mul,
        q3k_one_mul]
  calc q3kMul (q3kMul q9cYinv q9cYinv) q9cYinv
      = q3kMul (q3kMul (q3kMul q9cYinv q9cYinv) q9cYinv) q3kOne := (q3kRing.mul_one _).symm
    _ = q3kMul (q3kMul (q3kMul q9cYinv q9cYinv) q9cYinv)
          (q3kMul (q3kEmbed q3rqZeta) (q3kEmbed q3rqZetaSq)) := by
        rw [q3k_embed_mul, show q3rqMul q3rqZeta q3rqZetaSq = q3rqOne from q3k_z_zsqR1,
            q3k_embed_one]
    _ = q3kMul (q3kMul (q3kMul (q3kMul q9cYinv q9cYinv) q9cYinv) (q3kEmbed q3rqZeta))
          (q3kEmbed q3rqZetaSq) := (q3k_mul_assoc _ _ _).symm
    _ = q3kMul q3kOne (q3kEmbed q3rqZetaSq) := by rw [h1]
    _ = q3kEmbed q3rqZetaSq := q3k_one_mul _

/-- (a,0,0)·Y = (0,a,0)。 -/
theorem q9c_embed_mul_Y (a : q3rqCar) :
    q3kMul (q3kEmbed a) q3kZeta9 = ((q3rqZero, a, q3rqZero) : q3kCar) := by
  apply q3k_ext
  · show q3rqAdd (q3rqMul a q3rqZero)
        (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero q3rqZero) (q3rqMul q3rqZero q3rqOne)))
        = q3rqZero
    rw [q9c_mz a, q9c_za, q9c_zm q3rqZero, q9c_zm q3rqOne, q9c_za, q9c_mz q3rqZeta]
  · show q3rqAdd (q3rqAdd (q3rqMul a q3rqOne) (q3rqMul q3rqZero q3rqZero))
        (q3rqMul q3rqZeta (q3rqMul q3rqZero q3rqZero)) = a
    rw [q3rq_mul_one a, q9c_zm q3rqZero, q9c_az, q9c_mz q3rqZeta, q9c_az]
  · show q3rqAdd (q3rqAdd (q3rqMul a q3rqZero) (q3rqMul q3rqZero q3rqOne))
        (q3rqMul q3rqZero q3rqZero) = q3rqZero
    rw [q9c_mz a, q9c_zm q3rqOne, q9c_za, q9c_zm q3rqZero, q9c_az]

/-- (a,0,0)·Y⁻¹ = (0,0,a·ζ₃²)。 -/
theorem q9c_embed_mul_Yinv (a : q3rqCar) :
    q3kMul (q3kEmbed a) q9cYinv = ((q3rqZero, q3rqZero, q3rqMul a q3rqZetaSq) : q3kCar) := by
  rw [q9c_Yinv_tup]
  apply q3k_ext
  · show q3rqAdd (q3rqMul a q3rqZero)
        (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero q3rqZetaSq) (q3rqMul q3rqZero q3rqZero)))
        = q3rqZero
    rw [q9c_mz a, q9c_za, q9c_zm q3rqZetaSq, q9c_zm q3rqZero, q9c_za, q9c_mz q3rqZeta]
  · show q3rqAdd (q3rqAdd (q3rqMul a q3rqZero) (q3rqMul q3rqZero q3rqZero))
        (q3rqMul q3rqZeta (q3rqMul q3rqZero q3rqZetaSq)) = q3rqZero
    rw [q9c_mz a, q9c_zm q3rqZero, q9c_za, q9c_za, q9c_zm q3rqZetaSq, q9c_mz q3rqZeta]
  · show q3rqAdd (q3rqAdd (q3rqMul a q3rqZetaSq) (q3rqMul q3rqZero q3rqZero))
        (q3rqMul q3rqZero q3rqZero) = q3rqMul a q3rqZetaSq
    rw [q9c_zm q3rqZero, q9c_az, q9c_az]

/-- **μ₉ = 9 元集合**（ζ₉^{3i+j} = (ζ₃^i,0,0)・(0,ζ₃^i,0)・(0,0,ζ₃^i)）。 -/
def q3kMu9 (x : q3kCar) : Prop :=
  x = q3kOne
  ∨ x = ((q3rqZeta, q3rqZero, q3rqZero) : q3kCar)
  ∨ x = ((q3rqZetaSq, q3rqZero, q3rqZero) : q3kCar)
  ∨ x = ((q3rqZero, q3rqOne, q3rqZero) : q3kCar)
  ∨ x = ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar)
  ∨ x = ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar)
  ∨ x = ((q3rqZero, q3rqZero, q3rqOne) : q3kCar)
  ∨ x = ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar)
  ∨ x = ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar)

/-- **B8（★★★）: μ₉ 完全性** — u⁹=(u³)³=1 ⟹ u∈μ₉（塔分解・Y-捻り・9 乗展開なし）。 -/
theorem q9c_mu9_complete (u : q3kCar)
    (hu9 : q3kMul (q3kMul (q3kMul (q3kMul u u) u) (q3kMul (q3kMul u u) u))
        (q3kMul (q3kMul u u) u) = q3kOne) :
    q3kMu9 u := by
  obtain hw1 | hwz | hwzsq := q9c_m_mu3_complete (q3kMul (q3kMul u u) u) hu9
  · -- u³ = 1 ⟹ u ∈ μ₃(M) ⊂ μ₉
    obtain h | h | h := q9c_m_mu3_complete u hw1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · -- u³ = ζ₃: u·Y⁻¹ ∈ μ₃(M) ⟹ u ∈ μ₃·Y
    have hu'3 : q3kMul (q3kMul (q3kMul u q9cYinv) (q3kMul u q9cYinv)) (q3kMul u q9cYinv)
        = q3kOne := by
      rw [q9c_cube_mul u q9cYinv, hwz, q9c_Yinv3]
      show q3kMul (q3kEmbed q3rqZeta) (q3kEmbed q3rqZetaSq) = q3kOne
      rw [q3k_embed_mul, show q3rqMul q3rqZeta q3rqZetaSq = q3rqOne from q3k_z_zsqR1,
          q3k_embed_one]
    have hurec : q3kMul (q3kMul u q9cYinv) q3kZeta9 = u := by
      rw [q3k_mul_assoc u q9cYinv q3kZeta9, q9c_Yinv_mul_Y]
      exact (q3k_mul_comm u q3kOne).trans (q3k_one_mul u)
    obtain h | h | h := q9c_m_mu3_complete (q3kMul u q9cYinv) hu'3
    · right; right; right; left; rw [← hurec, h]; exact q9c_embed_mul_Y q3rqOne
    · right; right; right; right; left; rw [← hurec, h]; exact q9c_embed_mul_Y q3rqZeta
    · right; right; right; right; right; left; rw [← hurec, h]
      exact q9c_embed_mul_Y q3rqZetaSq
  · -- u³ = ζ₃²: u·Y ∈ μ₃(M) ⟹ u ∈ μ₃·Y²
    have hu'3 : q3kMul (q3kMul (q3kMul u q3kZeta9) (q3kMul u q3kZeta9)) (q3kMul u q3kZeta9)
        = q3kOne := by
      rw [q9c_cube_mul u q3kZeta9, hwzsq, q3k_zeta9_cube]
      show q3kMul (q3kEmbed q3rqZetaSq) (q3kEmbed q3rqZeta) = q3kOne
      rw [q3k_embed_mul, show q3rqMul q3rqZetaSq q3rqZeta = q3rqOne from q3k_zsq_zR1,
          q3k_embed_one]
    have hurec : q3kMul (q3kMul u q3kZeta9) q9cYinv = u := by
      rw [q3k_mul_assoc u q3kZeta9 q9cYinv, q9c_Y_mul_Yinv]
      exact (q3k_mul_comm u q3kOne).trans (q3k_one_mul u)
    obtain h | h | h := q9c_m_mu3_complete (q3kMul u q3kZeta9) hu'3
    · right; right; right; right; right; right; right; right
      rw [← hurec, h]
      have hh := q9c_embed_mul_Yinv q3rqOne
      rw [q3rq_one_mul] at hh
      exact hh
    · right; right; right; right; right; right; left
      rw [← hurec, h]
      have hh := q9c_embed_mul_Yinv q3rqZeta
      rw [show q3rqMul q3rqZeta q3rqZetaSq = q3rqOne from q3k_z_zsqR1] at hh
      exact hh
    · right; right; right; right; right; right; right; left
      rw [← hurec, h]
      have hh := q9c_embed_mul_Yinv q3rqZetaSq
      rw [show q3rqMul q3rqZetaSq q3rqZetaSq = q3rqZeta from q3k_zsq_zsqR] at hh
      exact hh

/-! ## q9c-11（B9）: capstone -/

/-- **B9: level-9 μ₉ 完全性データ** — O_M 内 μ₃ 完全性（対角）＋塔分解 μ₉ 完全性。 -/
structure Q3Mu9CompletenessData where
  /-- O_M 内 μ₃ 完全性: x³=1 ⟹ x∈μ₃(L₂)（対角埋め込み）。 -/
  mu3 : ∀ x : q3kCar, q3kMul (q3kMul x x) x = q3kOne →
    x = q3kOne ∨ x = ((q3rqZeta, q3rqZero, q3rqZero) : q3kCar)
      ∨ x = ((q3rqZetaSq, q3rqZero, q3rqZero) : q3kCar)
  /-- μ₉ 判定述語（9 元集合）。 -/
  mu9set : q3kCar → Prop
  /-- μ₉ 完全性: u⁹=(u³)³=1 ⟹ u∈μ₉。 -/
  mu9 : ∀ u : q3kCar,
    q3kMul (q3kMul (q3kMul (q3kMul u u) u) (q3kMul (q3kMul u u) u)) (q3kMul (q3kMul u u) u)
      = q3kOne → mu9set u

/-- **B9: 実例** — 実 O_M = q3kRing 上の μ₃(M)/μ₉ 完全性。 -/
def q9c_data : Q3Mu9CompletenessData where
  mu3 := q9c_m_mu3_complete
  mu9set := q3kMu9
  mu9 := q9c_mu9_complete

/-- **B9: level-9 μ₉ 完全性の存在**。 -/
theorem q9c_exists : Nonempty Q3Mu9CompletenessData := ⟨q9c_data⟩

end IUT
