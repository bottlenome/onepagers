/-
  IUT/Q3Mu27Mu3Kernel.lean — q27cm（μ₃(M₂₇) 完全性核 / **q27cMu3Complete の discharge**
    → 実 O_{M₂₇} の μ₉/μ₂₇ 完全性の**無条件化**）

  ── 主要成果の分類: **[実／(a) 昇格]**（named 実ターゲット = 柱A **A6** level-27 第 2 層
     KILL キャンペーンの μ₂₇ 完全性核。q27c（IUT/Q3Mu27Completeness.lean）が**名前付き
     入力仮定**として正直に残した命題 **q27cMu3Complete**（μ₃(M₂₇) 完全性: 実
     O_{M₂₇} = q27kRing 内で x³=1 ⟹ x ∈ μ₃ ⊂ O_{M₉} 対角）を、本ファイルで
     **無条件に証明**し（q27cm_mu3_complete）、q27c の条件付き塔分解定理
     q27c_mu9_complete_of_mu3 / q27c_mu27_complete_of_mu3 に代入して
     **μ₉(M₂₇)・μ₂₇ 完全性を無条件定理として輸出**する（q27cm_mu9_complete /
     q27cm_mu27_complete）。条件付き定理の仮定を実証明で置換する (a) 昇格。

  complete_pct 影響: **A6 の名前付き仮定 q27cMu3Complete を discharge（帽子 ≤0.65 内）**。
     本ファイル単体は kill も剛性もテータも橋も含まないため s_A6 は動かさない
     （complete_pct 0 前進・キャンペーン簿価は q27mb＋crk27 接続時に評価）——だが
     level-27 連鎖の**単一最大の残存仮定**が消え、μ₂₇ 完全性は実 O_{M₂₇} 上の
     無条件定理になった（q27c 正直限定 1 の解消）。A6 status の数値更新は親が判断する。

  数学的内容（level-9 の q9c B1–B8 テンプレートの 1 段上・ただし降下エンジン不要の
  短絡路を発見・採用）:
   * q27cm-1 cube slot 恒等式 — q9ci_cube0/1/2_raw（一般 CRing で証明済み）を
       R=q3kRing・d=ζ₉=q3kZeta9 で実例化: (x³)₀ = a³+ζ₉b³+ζ₉²c³+6ζ₉abc、
       (x³)₁ = 3E1′、(x³)₂ = 3E2′（E1′ = a²b+ζ₉ac²+ζ₉b²c、E2′ = a²c+ab²+ζ₉bc²）
   * q27cm-2 norm_sub — N_{M₂₇/M₉}(x) = (x³)₀ − 9ζ₉abc（q9ci_norm_sub の M₉ 係数版）
   * q27cm-3 B1′: x³=1 ⟹ N(x)=1 — N(x)³=N(x³)=1 と **level-9 の無条件 μ₃(M₉) 完全性
       q9c_m_mu3_complete** で N∈{1,ζ₃,ζ₃²}、N=1−9ζ₉abc の第 0 スロット λ-座標
       level-1 値 ≡ 0 mod 3 で ζ₃/ζ₃² 枝を排除（q9c_norm_one の 1 段上クローン）
   * q27cm-4 B2′: abc=0 — 9ζ₉abc=0 を 9-正則（q27ci_nine_reg_M）＋ζ₉ 単数正則
       （q27ci_zeta9_mul_zero）で剥がす
   * q27cm-5 E1′=E2′=0 — (x³)₁=(x³)₂=0 と 3-正則（q27ci_three_mul_zero）
   * q27cm-6 ★ a 単数（無条件・分岐なし）: (x³)₀=1 の第 0 L₂-スロットで
       a³ ≡ 1 mod 3O_{M₉}（ζ₉b³/ζ₉²c³/6ζ₉abc の第 0 スロットは全て 3 の倍数——
       cube slot 恒等式の帰結）⟹ q3kNormBase a = 1+3t ⟹ a ∈ O_{M₉}^×
       （q27ps_qnorm_one_add_three_unit 消費）。level-9 B4/B5 の「2 単数枝反証＋
       生存枝判定」が **不要になる**——a は常に単数
   * q27cm-7 ★★ b=c=0（純環算術・降下不要）: abc=0 ＋ a 単数 ⟹ bc=0 ⟹
       b²c=bc²=0 ⟹ E1′,E2′ が a(ab+ζ₉c²)=0・a(ac+b²)=0 に退化 ⟹（a 単数正則で）
       ab+ζ₉c²=0・ac+b²=0 ⟹（×b で）ab²=0 ⟹ b²=0 ⟹ ac=0 ⟹ c=0 ⟹ ab=0 ⟹ b=0。
       **12 座標交互パリティ降下（q27cs/q27ci 配線）はこの補題には不要**だった
       （q9c B6 の交互降下も同様に短絡可能だったことの発見・正直申告）
   * q27cm-8 ★★★ q27cm_mu3_complete : **q27cMu3Complete**（x=embed(a)・a³=1 を
       q9c_m_mu3_complete で分類）
   * q27cm-9 ★★★★ 見出し: q27cm_mu9_complete（u⁹=1 ⟹ u∈μ₉(M₂₇)）・
       q27cm_mu27_complete（u²⁷=1 ⟹ u∈μ₂₇）——**実 O_{M₂₇} 上の無条件定理**
   * q27cm-10 capstone: Q3Mu27KernelData / q27cm_data / q27cm_exists

  正直な限定（§4 規約により消さない・弱化しない・q27k/q27c/q27ci/q9c 継承の上に追記）:
  1. **q27c 正直限定 1 は解消**（q27cMu3Complete は本ファイルで無条件証明済み。
     q27c の条件付き定理はそのまま残り、本ファイルが無条件形を輸出する）。
     ただし q27cs スパイクの正直限定（E′ 影の全レベル可除・基底 TDF 1・スロット 1/2
     忠実性物量）は**本ファイルでは消費も解消もしない**——短絡路により μ₃ 核には
     そもそも不要だった。q27cs/q27ci の降下機構は将来の別ターゲット（例: 単数群の
     フィルトレーション論）用の実基盤として残る。
  2. **本モジュールは何も kill しない**（テータ群・Weil pairing・剛性ゼロ——
     それは後続 q27tl/q27mt/q27mr/q27mb）。A6 status を本ファイルでは動かさない。
  3. **奇部（u²⁷=−1 ⟹ μ₅₄）は収録しない**（q3mc/q9c/q27c の正直限定の前例どおり）。
  4. μ₂₇ の元は q27c のスロット分解存在形 q27cMu27 で表す（27 元列挙と同値・
     選択公理不要の Exists・q27c 正直限定 4 継承）。
  5. q27k/q3k/q3rq/q9c/q27ps の正直限定を全て継承(O_{M₂₇} と単数群のみ・体化なし・
     τ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体・
     tmzLimit 比較橋なし）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用（Or 破壊は
  obtain・rw/show/exact/refine/calc のみ・omega は純線形 Int ゴールのみ）。
-/
import IUT.Q3Mu27Completeness
import IUT.Q3KummerNonicRegular

namespace IUT

/-! ## q27cm-0: O_{M₉} = q3kCar の零・3 倍・9 倍簿記 -/

/-- y·0 = 0（q3kCar）。 -/
theorem q27cm_mz (y : q3kCar) : q3kMul y q3kZero = q3kZero := by
  rw [q3k_kM_eq, q27k_Z_eq]
  exact q3kRing.mul_zero y

/-- 0·y = 0（q3kCar）。 -/
theorem q27cm_zm (y : q3kCar) : q3kMul q3kZero y = q3kZero := by
  rw [q3k_mul_comm]
  exact q27cm_mz y

/-- 0+y = y（q3kCar）。 -/
theorem q27cm_za (y : q3kCar) : q3kAdd q3kZero y = y := by
  rw [q27k_A_eq, q27k_Z_eq]
  exact q3kRing.zero_add y

/-- y+0 = y（q3kCar）。 -/
theorem q27cm_az (y : q3kCar) : q3kAdd y q3kZero = y := by
  rw [q27k_A_eq, q27k_Z_eq]
  exact q3kRing.add_zero y

/-- 3·K = K+(K+K)（q3kCar・q9ci_three_mul の M₉ 版）。 -/
theorem q27cm_threeK (K : q3kCar) : q3kMul q27kThree K = q3kAdd K (q3kAdd K K) := by
  show q3kRing.mul (q3kRing.add q3kRing.one (q3kRing.add q3kRing.one q3kRing.one)) K
      = q3kRing.add K (q3kRing.add K K)
  rw [q3kRing.right_distrib q3kRing.one (q3kRing.add q3kRing.one q3kRing.one) K,
      q3kRing.right_distrib q3kRing.one q3kRing.one K,
      q3kRing.one_mul K]

/-- 9-fold の折り畳み（q9c_big_eq の M₉ 版）: 9 個の Z の再結合 = 9·Z。 -/
theorem q27cm_big_eq (Z : q3kCar) :
    q3kAdd
      (q3kAdd (q3kAdd (q3kAdd (q3kAdd (q3kAdd Z Z) Z) Z) Z) Z)
      (q3kAdd Z (q3kAdd Z Z))
    = q3kMul q27ciNineM Z := by
  have h1 : q3kAdd
        (q3kAdd (q3kAdd (q3kAdd (q3kAdd (q3kAdd Z Z) Z) Z) Z) Z)
        (q3kAdd Z (q3kAdd Z Z))
      = q3kAdd (q3kAdd Z (q3kAdd Z Z))
          (q3kAdd (q3kAdd Z (q3kAdd Z Z)) (q3kAdd Z (q3kAdd Z Z))) :=
    q9c_rawNine q3kRing Z
  have h2 : q3kMul q27ciNineM Z
      = q3kAdd (q3kAdd Z (q3kAdd Z Z))
          (q3kAdd (q3kAdd Z (q3kAdd Z Z)) (q3kAdd Z (q3kAdd Z Z))) := by
    show q3kMul (q3kMul q27kThree q27kThree) Z = _
    rw [q3k_kM_eq, q3kRing.mul_assoc q27kThree q27kThree Z, ← q3k_kM_eq,
        q27cm_threeK Z, q27cm_threeK (q3kAdd Z (q3kAdd Z Z))]
  rw [h1, h2]

/-- 左交換 a(bc) = b(ac)（q3kCar）。 -/
theorem q27cm_kmlc (a b c : q3kCar) :
    q3kMul a (q3kMul b c) = q3kMul b (q3kMul a c) := by
  rw [q3k_kM_eq, ← q3kRing.mul_assoc a b c, q3kRing.mul_comm a b,
      q3kRing.mul_assoc b a c]

/-- 左交換 a(bc) = b(ac)（q3rqCar）。 -/
theorem q27cm_rq_mlc (a b c : q3rqCar) :
    q3rqMul a (q3rqMul b c) = q3rqMul b (q3rqMul a c) := by
  rw [q3k_M_eq, ← q3rqRing.mul_assoc a b c, q3rqRing.mul_comm a b,
      q3rqRing.mul_assoc b a c]

/-! ## q27cm-1: cube slot 恒等式（q9ci_cube?_raw の R=q3kRing・d=ζ₉ 実例化） -/

/-- **E0（level-27）**: (x³).1 = a³ + ζ₉b³ + ζ₉²c³ + 6ζ₉abc（O_{M₉} 係数）。 -/
theorem q27cm_cube_0 (x : q27kCar) :
    (q27kMul (q27kMul x x) x).1
      = q3kAdd
          (q3kAdd
            (q3kAdd (q3kMul (q3kMul x.1 x.1) x.1)
              (q3kMul q3kZeta9 (q3kMul (q3kMul x.2.1 x.2.1) x.2.1)))
            (q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kMul (q3kMul x.2.2 x.2.2) x.2.2)))
          (q3kAdd
            (q3kAdd
              (q3kAdd
                (q3kAdd
                  (q3kAdd (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))
                           (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
                  (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
                (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
              (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
            (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))) := by
  rw [q27kMul_0, q27kMul_0, q27kMul_1, q27kMul_2, q27k_M_eq, q27k_A_eq]
  exact q9ci_cube0_raw q3kRing x.1 x.2.1 x.2.2 q3kZeta9

/-- **E1（level-27）**: (x³).2.1 = 3(a²b + ζ₉ac² + ζ₉b²c)。 -/
theorem q27cm_cube_1 (x : q27kCar) :
    (q27kMul (q27kMul x x) x).2.1
      = q3kAdd
          (q3kAdd
            (q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.1)
              (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.2 x.2.2))))
            (q3kMul q3kZeta9 (q3kMul (q3kMul x.2.1 x.2.1) x.2.2)))
          (q3kAdd
            (q3kAdd
              (q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.1)
                (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.2 x.2.2))))
              (q3kMul q3kZeta9 (q3kMul (q3kMul x.2.1 x.2.1) x.2.2)))
            (q3kAdd
              (q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.1)
                (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.2 x.2.2))))
              (q3kMul q3kZeta9 (q3kMul (q3kMul x.2.1 x.2.1) x.2.2)))) := by
  rw [q27kMul_1, q27kMul_0, q27kMul_1, q27kMul_2, q27k_M_eq, q27k_A_eq]
  exact q9ci_cube1_raw q3kRing x.1 x.2.1 x.2.2 q3kZeta9

/-- **E2（level-27）**: (x³).2.2 = 3(a²c + ab² + ζ₉bc²)。 -/
theorem q27cm_cube_2 (x : q27kCar) :
    (q27kMul (q27kMul x x) x).2.2
      = q3kAdd
          (q3kAdd
            (q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.2)
              (q3kMul x.1 (q3kMul x.2.1 x.2.1)))
            (q3kMul q3kZeta9 (q3kMul x.2.1 (q3kMul x.2.2 x.2.2))))
          (q3kAdd
            (q3kAdd
              (q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.2)
                (q3kMul x.1 (q3kMul x.2.1 x.2.1)))
              (q3kMul q3kZeta9 (q3kMul x.2.1 (q3kMul x.2.2 x.2.2))))
            (q3kAdd
              (q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.2)
                (q3kMul x.1 (q3kMul x.2.1 x.2.1)))
              (q3kMul q3kZeta9 (q3kMul x.2.1 (q3kMul x.2.2 x.2.2))))) := by
  rw [q27kMul_2, q27kMul_0, q27kMul_1, q27kMul_2, q27k_M_eq, q27k_A_eq]
  exact q9ci_cube2_raw q3kRing x.1 x.2.1 x.2.2 q3kZeta9

/-! ## q27cm-2: norm_sub — N_{M₂₇/M₉}(x) = (x³).1 − 9ζ₉abc -/

/-- **A4（level-27）**: q27kNormBase x = (x³).1 − 9ζ₉abc（9 個の ζ₉abc の再結合形）。 -/
theorem q27cm_norm_sub (x : q27kCar) :
    q27kNormBase x
      = q3kAdd ((q27kMul (q27kMul x x) x).1)
          (q3kNeg
            (q3kAdd
              (q3kAdd
                (q3kAdd
                  (q3kAdd
                    (q3kAdd
                      (q3kAdd (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))
                               (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
                      (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
                    (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
                  (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
                (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
              (q3kAdd (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))
                (q3kAdd (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))
                  (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))))) := by
  rw [q27cm_cube_0]
  have hVW : q3kMul q3kZeta9 (q3kMul (q3kMul x.1 x.2.1) x.2.2)
      = q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)) := by
    rw [q3k_kM_eq, q3kRing.mul_assoc x.1 x.2.1 x.2.2]
  show q3kAdd
        (q3kAdd
          (q3kAdd (q3kMul (q3kMul x.1 x.1) x.1)
            (q3kMul q3kZeta9 (q3kMul (q3kMul x.2.1 x.2.1) x.2.1)))
          (q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kMul (q3kMul x.2.2 x.2.2) x.2.2)))
        (q3kNeg (q3kMul q27kThree
          (q3kMul q3kZeta9 (q3kMul (q3kMul x.1 x.2.1) x.2.2))))
      = _
  rw [hVW, q27cm_threeK (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))]
  exact (q9ci_add_neg_cancel q3kRing
    (q3kAdd
      (q3kAdd (q3kMul (q3kMul x.1 x.1) x.1)
        (q3kMul q3kZeta9 (q3kMul (q3kMul x.2.1 x.2.1) x.2.1)))
      (q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kMul (q3kMul x.2.2 x.2.2) x.2.2)))
    (q3kAdd
      (q3kAdd
        (q3kAdd
          (q3kAdd
            (q3kAdd (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))
                     (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
            (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
          (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
        (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
      (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))))
    (q3kAdd (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))
      (q3kAdd (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))
        (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))))).symm

/-! ## q27cm-3（B1′）: x³=1 ⟹ N(x)=1（level-9 の無条件 μ₃(M₉) 完全性を消費） -/

/-- **B1′（★）: x³=1 ⟹ N_{M₂₇/M₉}(x)=1**。N(x)³=N(x³)=1 と q9c_m_mu3_complete で
    N∈{1,ζ₃,ζ₃²}、N=1−9ζ₉abc の第 0 スロット λ-座標 level-1 = [0] で ζ₃/ζ₃² を排除。 -/
theorem q27cm_norm_one (x : q27kCar)
    (hu : q27kMul (q27kMul x x) x = q27kOne) : q27kNormBase x = q3kOne := by
  have hcube1 : q3kMul (q3kMul (q27kNormBase x) (q27kNormBase x)) (q27kNormBase x)
      = q3kOne := by
    have h1 : q27kNormBase (q27kMul (q27kMul x x) x)
        = q3kMul (q3kMul (q27kNormBase x) (q27kNormBase x)) (q27kNormBase x) := by
      rw [q27k_normBase_mul (q27kMul x x) x, q27k_normBase_mul x x]
    rw [← h1, hu, q27k_normBase_one]
  have hmu3 := q9c_m_mu3_complete (q27kNormBase x) hcube1
  have hval : (q27kNormBase x).1.2.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := by
    rw [q27cm_norm_sub x, hu]
    show (q3rqAdd q3rqOne
        (q3rqNeg
          (q3rqAdd
            (q3rqAdd
              (q3rqAdd
                (q3rqAdd
                  (q3rqAdd
                    (q3rqAdd ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1)
                             ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))
                    ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))
                  ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))
                ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))
              ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))
            (q3rqAdd ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1)
              (q3rqAdd ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1)
                ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1)))))).2.val 1
      = Quot.mk (modCong (3 ^ 1)).rel 0
    rw [q9c_big_eq ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1)]
    show (z3.add z3.zero
        (z3.neg
          ((q3rqMul q9ciNine
            ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1)).2))).val 1
      = Quot.mk (modCong (3 ^ 1)).rel 0
    rw [z3.zero_add
          (z3.neg ((q3rqMul q9ciNine
            ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1)).2)),
        q3mc_neg_val1 _ 0
          (q9c_nineZ_snd_val1 ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))]
    apply Quot.sound
    show ((3 ^ 1 : Nat) : Int) ∣ (-0 - 0)
    exact ⟨0, by rw [Nat.pow_one]; omega⟩
  obtain h1 | hz | hzsq := hmu3
  · exact h1
  · exfalso
    have h2eq : (q27kNormBase x).1.2 = q3rqHalf :=
      congrArg (fun w : q3kCar => w.1.2) hz
    have heq : q3rqHalf.val 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := by
      rw [← h2eq]; exact hval
    have h2h : (z3.mul q3rqTwoZ q3rqHalf).val 1 = Quot.mk (modCong (3 ^ 1)).rel 1 := by
      rw [q3rq_two_half]; rfl
    rw [q3mc_mul_val1 q3rqTwoZ q3rqHalf 2 0 q9c_two_val1 heq] at h2h
    have hd := quot_exact intGrp (modCong (3 ^ 1)) h2h
    rw [Nat.pow_one] at hd
    obtain ⟨c, hc⟩ := hd
    omega
  · exfalso
    have hsnd : (q27kNormBase x).1.2 = q3rqZetaSq.2 :=
      congrArg (fun w : q3kCar => w.1.2) hzsq
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
    obtain ⟨c, hc⟩ := hd
    omega

/-! ## q27cm-4（B2′）: abc = 0 -/

/-- **B2′: abc=0**（N(x)=1 で 9ζ₉abc=0、9-正則＋ζ₉ 単数正則で剥がす）。 -/
theorem q27cm_abc_zero (x : q27kCar)
    (hu : q27kMul (q27kMul x x) x = q27kOne) :
    q3kMul x.1 (q3kMul x.2.1 x.2.2) = q3kZero := by
  have hns := q27cm_norm_sub x
  rw [hu, q27cm_big_eq (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))),
      q27cm_norm_one x hu] at hns
  have hcancel : q3kRing.add q3kOne
      (q3kRing.neg (q3kMul q27ciNineM
        (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)))))
      = q3kRing.add q3kOne q3kRing.zero := by
    rw [q3kRing.add_zero q3kOne]
    exact hns.symm
  have hnegz := q3kRing.add_left_cancel hcancel
  have hbig : q3kMul q27ciNineM
      (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))) = q3kZero := by
    have h := congrArg q3kRing.neg hnegz
    rw [q3kRing.neg_neg, q3kRing.neg_zero] at h
    exact h
  have hD : q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2)) = q3kZero := by
    apply q27ci_nine_reg_M
      (x := q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))) (y := q3kZero)
    rw [hbig, q3k_kM_eq, q27k_Z_eq, q3kRing.mul_zero q27ciNineM]
  exact q27ci_zeta9_mul_zero hD

/-! ## q27cm-5: E1′ = E2′ = 0（(x³) の Z/Z² 成分と 3-正則） -/

/-- E1′ = a²b + ζ₉ac² + ζ₉b²c = 0。 -/
theorem q27cm_E1_zero (x : q27kCar)
    (hu : q27kMul (q27kMul x x) x = q27kOne) :
    q3kAdd
      (q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.1)
        (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.2 x.2.2))))
      (q3kMul q3kZeta9 (q3kMul (q3kMul x.2.1 x.2.1) x.2.2)) = q3kZero := by
  have h : (q27kMul (q27kMul x x) x).2.1 = q3kZero :=
    congrArg (fun z : q27kCar => z.2.1) hu
  rw [q27cm_cube_1 x, ← q27cm_threeK _] at h
  exact q27ci_three_mul_zero _ h

/-- E2′ = a²c + ab² + ζ₉bc² = 0。 -/
theorem q27cm_E2_zero (x : q27kCar)
    (hu : q27kMul (q27kMul x x) x = q27kOne) :
    q3kAdd
      (q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.2)
        (q3kMul x.1 (q3kMul x.2.1 x.2.1)))
      (q3kMul q3kZeta9 (q3kMul x.2.1 (q3kMul x.2.2 x.2.2))) = q3kZero := by
  have h : (q27kMul (q27kMul x x) x).2.2 = q3kZero :=
    congrArg (fun z : q27kCar => z.2.2) hu
  rw [q27cm_cube_2 x, ← q27cm_threeK _] at h
  exact q27ci_three_mul_zero _ h

/-! ## q27cm-6（★）: a は無条件に O_{M₉} 単数（分岐不要・level-9 B4/B5 の短絡） -/

/-- ζ₉·v の第 0 スロット = ζ₃·v₂（ζ₉ = (0,1,0) の畳み込み）。 -/
theorem q27cm_z9mul_1 (v : q3kCar) :
    (q3kMul q3kZeta9 v).1 = q3rqMul q3rqZeta v.2.2 := by
  show q3rqAdd (q3rqMul q3rqZero v.1)
      (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqOne v.2.2) (q3rqMul q3rqZero v.2.1)))
    = q3rqMul q3rqZeta v.2.2
  rw [q9c_zm v.1, q9c_zm v.2.1, q3rq_one_mul v.2.2, q9c_az v.2.2,
      q9c_za (q3rqMul q3rqZeta v.2.2)]

/-- ζ₉²·v の第 0 スロット = ζ₃·v₁（ζ₉² = (0,0,1) の畳み込み）。 -/
theorem q27cm_z9sqmul_1 (v : q3kCar) :
    (q3kMul (q3kMul q3kZeta9 q3kZeta9) v).1 = q3rqMul q3rqZeta v.2.1 := by
  rw [q3k_zeta9_sq]
  show q3rqAdd (q3rqMul q3rqZero v.1)
      (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero v.2.2) (q3rqMul q3rqOne v.2.1)))
    = q3rqMul q3rqZeta v.2.1
  rw [q9c_zm v.1, q9c_zm v.2.2, q3rq_one_mul v.2.1, q9c_za v.2.1,
      q9c_za (q3rqMul q3rqZeta v.2.1)]

/-- 6-fold の折り畳み: 6 個の U の左結合和 = 3·(U+U)。 -/
theorem q27cm_six_fold (U : q3rqCar) :
    q3rqAdd (q3rqAdd (q3rqAdd (q3rqAdd (q3rqAdd U U) U) U) U) U
      = q3rqMul q3rqThreeElt (q3rqAdd U U) := by
  rw [q9c_three_mul_elt (q3rqAdd U U), q3k_A_eq,
      q3rqRing.add_assoc (q3rqRing.add (q3rqRing.add (q3rqRing.add U U) U) U) U U,
      q3rqRing.add_assoc (q3rqRing.add (q3rqRing.add U U) U) U (q3rqRing.add U U),
      q3rqRing.add_assoc (q3rqRing.add U U) U (q3rqRing.add U (q3rqRing.add U U)),
      q3rqRing.add_assoc U U (q3rqRing.add U U)]

/-- 3 個の 3-倍数の収集: ((K+3p)+3q)+3r = K + 3(p+(q+r))。 -/
theorem q27cm_collect3 (K p q r : q3rqCar) :
    q3rqAdd (q3rqAdd (q3rqAdd K (q3rqMul q3rqThreeElt p)) (q3rqMul q3rqThreeElt q))
        (q3rqMul q3rqThreeElt r)
      = q3rqAdd K (q3rqMul q3rqThreeElt (q3rqAdd p (q3rqAdd q r))) := by
  rw [q3k_A_eq, q3k_M_eq,
      q3rqRing.add_assoc (q3rqRing.add K (q3rqRing.mul q3rqThreeElt p))
        (q3rqRing.mul q3rqThreeElt q) (q3rqRing.mul q3rqThreeElt r),
      q3rqRing.add_assoc K (q3rqRing.mul q3rqThreeElt p)
        (q3rqRing.add (q3rqRing.mul q3rqThreeElt q) (q3rqRing.mul q3rqThreeElt r)),
      ← q3rqRing.left_distrib q3rqThreeElt q r,
      ← q3rqRing.left_distrib q3rqThreeElt p (q3rqRing.add q r)]

/-- K + S = 1 ⟹ K = 1 − S。 -/
theorem q27cm_one_sub (K S : q3rqCar) (h : q3rqAdd K S = q3rqOne) :
    K = q3rqAdd q3rqOne (q3rqNeg S) := by
  rw [← h, q3k_A_eq, q3k_N_eq, q3rqRing.add_assoc K S (q3rqRing.neg S),
      q3rqRing.add_neg S, q3rqRing.add_zero K]

/-- 9·V = 3·(3·V)。 -/
theorem q27cm_split9 (V : q3rqCar) :
    q3rqMul q9ciNine V = q3rqMul q3rqThreeElt (q3rqMul q3rqThreeElt V) := by
  show q3rqMul (q3rqMul q3rqThreeElt q3rqThreeElt) V
      = q3rqMul q3rqThreeElt (q3rqMul q3rqThreeElt V)
  rw [q3k_M_eq, q3rqRing.mul_assoc q3rqThreeElt q3rqThreeElt V]

/-- (1 − 3T) − 3V = 1 + 3(−T + −V)。 -/
theorem q27cm_one_three_shift (T V : q3rqCar) :
    q3rqAdd (q3rqAdd q3rqOne (q3rqNeg (q3rqMul q3rqThreeElt T)))
        (q3rqNeg (q3rqMul q3rqThreeElt V))
      = q3rqAdd q3rqOne (q3rqMul q3rqThreeElt (q3rqAdd (q3rqNeg T) (q3rqNeg V))) := by
  rw [q3k_A_eq, q3k_M_eq, q3k_N_eq,
      ← q3rqRing.mul_neg q3rqThreeElt T, ← q3rqRing.mul_neg q3rqThreeElt V,
      q3rqRing.add_assoc q3rqOne (q3rqRing.mul q3rqThreeElt (q3rqRing.neg T))
        (q3rqRing.mul q3rqThreeElt (q3rqRing.neg V)),
      ← q3rqRing.left_distrib q3rqThreeElt (q3rqRing.neg T) (q3rqRing.neg V)]

/-- **q27cm-6（★★）: x³=1 ⟹ a = x.1 は実 O_{M₉} 単数（無条件・分岐なし）**。
    (x³)₀=1 の第 0 L₂-スロットで ζ₉b³/ζ₉²c³/6ζ₉abc の寄与が全て 3 の倍数
    （cube slot 恒等式）となり q3kNormBase a = 1+3t、q27ps_qnorm_one_add_three_unit
    で単数判定。level-9 の B4 2 枝反証＋B5 生存枝判定がまるごと不要になる。 -/
theorem q27cm_a_unit (x : q27kCar)
    (hu : q27kMul (q27kMul x x) x = q27kOne) : q3kUnitMem x.1 := by
  have hc0 : (q27kMul (q27kMul x x) x).1 = q3kOne :=
    congrArg (fun z : q27kCar => z.1) hu
  rw [q27cm_cube_0 x] at hc0
  have hc1 :
      q3rqAdd
        (q3rqAdd
          (q3rqAdd ((q3kMul (q3kMul x.1 x.1) x.1).1)
            ((q3kMul q3kZeta9 (q3kMul (q3kMul x.2.1 x.2.1) x.2.1)).1))
          ((q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kMul (q3kMul x.2.2 x.2.2) x.2.2)).1))
        (q3rqAdd
          (q3rqAdd
            (q3rqAdd
              (q3rqAdd
                (q3rqAdd ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1)
                         ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))
                ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))
              ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))
            ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))
          ((q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.1 x.2.2))).1))
      = q3rqOne :=
    congrArg (fun w : q3kCar => w.1) hc0
  rw [q27cm_z9mul_1 (q3kMul (q3kMul x.2.1 x.2.1) x.2.1),
      q27cm_z9sqmul_1 (q3kMul (q3kMul x.2.2 x.2.2) x.2.2),
      q27cm_z9mul_1 (q3kMul x.1 (q3kMul x.2.1 x.2.2)),
      q9ci_cube_2 x.2.1, q9ci_cube_1 x.2.2,
      ← q9c_three_mul_elt
        (q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul x.2.1.1 x.2.1.1) x.2.1.2.2)
            (q3rqMul x.2.1.1 (q3rqMul x.2.1.2.1 x.2.1.2.1)))
          (q3rqMul q3rqZeta (q3rqMul x.2.1.2.1 (q3rqMul x.2.1.2.2 x.2.1.2.2)))),
      ← q9c_three_mul_elt
        (q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul x.2.2.1 x.2.2.1) x.2.2.2.1)
            (q3rqMul q3rqZeta (q3rqMul x.2.2.1 (q3rqMul x.2.2.2.2 x.2.2.2.2))))
          (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.2.2.1 x.2.2.2.1) x.2.2.2.2))),
      q27cm_rq_mlc q3rqZeta q3rqThreeElt
        (q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul x.2.1.1 x.2.1.1) x.2.1.2.2)
            (q3rqMul x.2.1.1 (q3rqMul x.2.1.2.1 x.2.1.2.1)))
          (q3rqMul q3rqZeta (q3rqMul x.2.1.2.1 (q3rqMul x.2.1.2.2 x.2.1.2.2)))),
      q27cm_rq_mlc q3rqZeta q3rqThreeElt
        (q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul x.2.2.1 x.2.2.1) x.2.2.2.1)
            (q3rqMul q3rqZeta (q3rqMul x.2.2.1 (q3rqMul x.2.2.2.2 x.2.2.2.2))))
          (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.2.2.1 x.2.2.2.1) x.2.2.2.2))),
      q27cm_six_fold
        (q3rqMul q3rqZeta ((q3kMul x.1 (q3kMul x.2.1 x.2.2)).2.2)),
      q27cm_collect3 ((q3kMul (q3kMul x.1 x.1) x.1).1)
        (q3rqMul q3rqZeta
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul x.2.1.1 x.2.1.1) x.2.1.2.2)
              (q3rqMul x.2.1.1 (q3rqMul x.2.1.2.1 x.2.1.2.1)))
            (q3rqMul q3rqZeta (q3rqMul x.2.1.2.1 (q3rqMul x.2.1.2.2 x.2.1.2.2)))))
        (q3rqMul q3rqZeta
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul x.2.2.1 x.2.2.1) x.2.2.2.1)
              (q3rqMul q3rqZeta (q3rqMul x.2.2.1 (q3rqMul x.2.2.2.2 x.2.2.2.2))))
            (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.2.2.1 x.2.2.2.1) x.2.2.2.2))))
        (q3rqAdd (q3rqMul q3rqZeta ((q3kMul x.1 (q3kMul x.2.1 x.2.2)).2.2))
          (q3rqMul q3rqZeta ((q3kMul x.1 (q3kMul x.2.1 x.2.2)).2.2)))] at hc1
  have hK := q27cm_one_sub ((q3kMul (q3kMul x.1 x.1) x.1).1)
    (q3rqMul q3rqThreeElt
      (q3rqAdd
        (q3rqMul q3rqZeta
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul x.2.1.1 x.2.1.1) x.2.1.2.2)
              (q3rqMul x.2.1.1 (q3rqMul x.2.1.2.1 x.2.1.2.1)))
            (q3rqMul q3rqZeta (q3rqMul x.2.1.2.1 (q3rqMul x.2.1.2.2 x.2.1.2.2)))))
        (q3rqAdd
          (q3rqMul q3rqZeta
            (q3rqAdd
              (q3rqAdd (q3rqMul (q3rqMul x.2.2.1 x.2.2.1) x.2.2.2.1)
                (q3rqMul q3rqZeta (q3rqMul x.2.2.1 (q3rqMul x.2.2.2.2 x.2.2.2.2))))
              (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.2.2.1 x.2.2.2.1) x.2.2.2.2))))
          (q3rqAdd (q3rqMul q3rqZeta ((q3kMul x.1 (q3kMul x.2.1 x.2.2)).2.2))
            (q3rqMul q3rqZeta ((q3kMul x.1 (q3kMul x.2.1 x.2.2)).2.2)))))) hc1
  have hns := q9ci_norm_sub x.1
  rw [q9c_big_eq (q3rqMul q3rqZeta (q3rqMul x.1.1 (q3rqMul x.1.2.1 x.1.2.2))),
      q27cm_split9 (q3rqMul q3rqZeta (q3rqMul x.1.1 (q3rqMul x.1.2.1 x.1.2.2))),
      hK,
      q27cm_one_three_shift
        (q3rqAdd
          (q3rqMul q3rqZeta
            (q3rqAdd
              (q3rqAdd (q3rqMul (q3rqMul x.2.1.1 x.2.1.1) x.2.1.2.2)
                (q3rqMul x.2.1.1 (q3rqMul x.2.1.2.1 x.2.1.2.1)))
              (q3rqMul q3rqZeta (q3rqMul x.2.1.2.1 (q3rqMul x.2.1.2.2 x.2.1.2.2)))))
          (q3rqAdd
            (q3rqMul q3rqZeta
              (q3rqAdd
                (q3rqAdd (q3rqMul (q3rqMul x.2.2.1 x.2.2.1) x.2.2.2.1)
                  (q3rqMul q3rqZeta (q3rqMul x.2.2.1 (q3rqMul x.2.2.2.2 x.2.2.2.2))))
                (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.2.2.1 x.2.2.2.1) x.2.2.2.2))))
            (q3rqAdd (q3rqMul q3rqZeta ((q3kMul x.1 (q3kMul x.2.1 x.2.2)).2.2))
              (q3rqMul q3rqZeta ((q3kMul x.1 (q3kMul x.2.1 x.2.2)).2.2)))))
        (q3rqMul q3rqThreeElt
          (q3rqMul q3rqZeta (q3rqMul x.1.1 (q3rqMul x.1.2.1 x.1.2.2))))] at hns
  show IsZpUnit 3 (q3rqNorm (q3kNormBase x.1))
  rw [hns]
  exact q27ps_qnorm_one_add_three_unit _

/-! ## q27cm-7（★★）: b = c = 0（純環算術・降下エンジン不要） -/

/-- **b = c = 0**: abc=0・E1′=E2′=0・a 単数から、単数正則だけで b,c が消える。
    （q9c B6 の 12 座標交互パリティ降下は本補題には不要——正直申告どおりの短絡。） -/
theorem q27cm_bc_zero (x : q27kCar)
    (hu : q27kMul (q27kMul x x) x = q27kOne) (hau : q3kUnitMem x.1) :
    x.2.1 = q3kZero ∧ x.2.2 = q3kZero := by
  have hbc : q3kMul x.2.1 x.2.2 = q3kZero :=
    q27ci_unit_mul_zero x.1 hau (q27cm_abc_zero x hu)
  have hbbc : q3kMul (q3kMul x.2.1 x.2.1) x.2.2 = q3kZero := by
    rw [q3k_mul_assoc x.2.1 x.2.1 x.2.2, hbc, q27cm_mz x.2.1]
  have hbcc : q3kMul x.2.1 (q3kMul x.2.2 x.2.2) = q3kZero := by
    rw [← q3k_mul_assoc x.2.1 x.2.2 x.2.2, hbc, q27cm_zm x.2.2]
  have hE1 := q27cm_E1_zero x hu
  rw [hbbc, q27cm_mz q3kZeta9,
      q27cm_az (q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.1)
        (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.2 x.2.2))))] at hE1
  have hE2 := q27cm_E2_zero x hu
  rw [hbcc, q27cm_mz q3kZeta9,
      q27cm_az (q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.2)
        (q3kMul x.1 (q3kMul x.2.1 x.2.1)))] at hE2
  have hkey1 : q3kAdd (q3kMul x.1 x.2.1) (q3kMul q3kZeta9 (q3kMul x.2.2 x.2.2))
      = q3kZero := by
    apply q27ci_unit_mul_zero x.1 hau
    have hdist : q3kMul x.1
        (q3kAdd (q3kMul x.1 x.2.1) (q3kMul q3kZeta9 (q3kMul x.2.2 x.2.2)))
        = q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.1)
            (q3kMul q3kZeta9 (q3kMul x.1 (q3kMul x.2.2 x.2.2))) := by
      rw [q3k_kM_eq, q27k_A_eq,
          q3kRing.left_distrib x.1 (q3kRing.mul x.1 x.2.1)
            (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 x.2.2)),
          ← q3kRing.mul_assoc x.1 x.1 x.2.1,
          show q3kRing.mul x.1 (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 x.2.2))
              = q3kRing.mul q3kZeta9 (q3kRing.mul x.1 (q3kRing.mul x.2.2 x.2.2)) from
            q27cm_kmlc x.1 q3kZeta9 (q3kMul x.2.2 x.2.2)]
    rw [hdist]
    exact hE1
  have hkey2 : q3kAdd (q3kMul x.1 x.2.2) (q3kMul x.2.1 x.2.1) = q3kZero := by
    apply q27ci_unit_mul_zero x.1 hau
    have hdist : q3kMul x.1 (q3kAdd (q3kMul x.1 x.2.2) (q3kMul x.2.1 x.2.1))
        = q3kAdd (q3kMul (q3kMul x.1 x.1) x.2.2)
            (q3kMul x.1 (q3kMul x.2.1 x.2.1)) := by
      rw [q3k_kM_eq, q27k_A_eq,
          q3kRing.left_distrib x.1 (q3kRing.mul x.1 x.2.2)
            (q3kRing.mul x.2.1 x.2.1),
          ← q3kRing.mul_assoc x.1 x.1 x.2.2]
    rw [hdist]
    exact hE2
  have hb2 : q3kMul x.2.1 x.2.1 = q3kZero := by
    apply q27ci_unit_mul_zero x.1 hau
    have h : q3kMul (q3kAdd (q3kMul x.1 x.2.1)
          (q3kMul q3kZeta9 (q3kMul x.2.2 x.2.2))) x.2.1
        = q3kMul q3kZero x.2.1 :=
      congrArg (fun w : q3kCar => q3kMul w x.2.1) hkey1
    rw [q27cm_zm x.2.1, q3k_kM_eq, q27k_A_eq,
        q3kRing.right_distrib (q3kRing.mul x.1 x.2.1)
          (q3kRing.mul q3kZeta9 (q3kRing.mul x.2.2 x.2.2)) x.2.1,
        q3kRing.mul_assoc x.1 x.2.1 x.2.1,
        q3kRing.mul_assoc q3kZeta9 (q3kRing.mul x.2.2 x.2.2) x.2.1,
        q3kRing.mul_comm (q3kRing.mul x.2.2 x.2.2) x.2.1,
        show q3kRing.mul x.2.1 (q3kRing.mul x.2.2 x.2.2) = q3kRing.zero from hbcc,
        q3kRing.mul_zero q3kZeta9,
        q3kRing.add_zero (q3kRing.mul x.1 (q3kRing.mul x.2.1 x.2.1))] at h
    exact h
  have hc00 : x.2.2 = q3kZero := by
    apply q27ci_unit_mul_zero x.1 hau
    have h := hkey2
    rw [hb2, q27cm_az (q3kMul x.1 x.2.2)] at h
    exact h
  have hb00 : x.2.1 = q3kZero := by
    apply q27ci_unit_mul_zero x.1 hau
    have h := hkey1
    rw [hc00, q27cm_zm q3kZero, q27cm_mz q3kZeta9,
        q27cm_az (q3kMul x.1 x.2.1)] at h
    exact h
  exact ⟨hb00, hc00⟩

/-! ## q27cm-8（★★★）: μ₃(M₂₇) 完全性 — q27cMu3Complete の discharge -/

/-- **μ₃(M₂₇) 完全性（無条件）**: x³=1 in 実 O_{M₂₇} ⟹ x ∈ μ₃ ⊂ O_{M₉} 対角。 -/
theorem q27cm_m_mu3_complete (x : q27kCar)
    (hu : q27kMul (q27kMul x x) x = q27kOne) :
    x = q27kOne ∨ x = q27kEmbed q27kZeta3 ∨ x = q27kEmbed q27kZeta3Sq := by
  obtain ⟨hb0, hc0⟩ := q27cm_bc_zero x hu (q27cm_a_unit x hu)
  have hxe : x = q27kEmbed x.1 := q27k_ext rfl hb0 hc0
  have hcube : q3kMul (q3kMul x.1 x.1) x.1 = q3kOne := by
    apply q27k_embed_inj
    rw [← q27k_embed_mul (q3kMul x.1 x.1) x.1, ← q27k_embed_mul x.1 x.1,
        ← hxe, hu, q27k_embed_one]
  obtain h1 | hz | hzsq := q9c_m_mu3_complete x.1 hcube
  · left; rw [hxe, h1]; exact q27k_embed_one
  · right; left; rw [hxe, hz]; exact rfl
  · right; right; rw [hxe, hzsq]; exact rfl

/-- **★★★ q27cMu3Complete の discharge** — q27c が名前付き入力仮定として残した
    μ₃(M₂₇) 完全性命題は、実 O_{M₂₇} 上で無条件に成立する。 -/
theorem q27cm_mu3_complete : q27cMu3Complete :=
  fun x hu => q27cm_m_mu3_complete x hu

/-! ## q27cm-9（★★★★）: 見出し — 実 O_{M₂₇} の μ₉/μ₂₇ 完全性（無条件） -/

/-- **★★★★ μ₉(M₂₇) 完全性（無条件）**: u⁹=1 ⟹ u ∈ μ₉（M₉ 対角）。
    q27c_mu9_complete_of_mu3 の仮定 q27cMu3Complete を実証明で置換した無条件形。 -/
theorem q27cm_mu9_complete (u : q27kCar)
    (hu9 : q27cCube (q27cCube u) = q27kOne) : q27cMu9 u :=
  q27c_mu9_complete_of_mu3 q27cm_mu3_complete u hu9

/-- **★★★★ μ₂₇ 完全性（無条件）**: u²⁷=((u³)³)³=1 ⟹ u ∈ μ₂₇ = μ₉×{1,Z,Z²}
    （スロット分解存在形）。実 O_{M₂₇} = q27kRing 上の無条件定理。 -/
theorem q27cm_mu27_complete (u : q27kCar)
    (hu27 : q27cCube (q27cCube (q27cCube u)) = q27kOne) : q27cMu27 u :=
  q27c_mu27_complete_of_mu3 q27cm_mu3_complete u hu27

/-! ## q27cm-10: capstone（無条件 μ₂₇ 完全性核データ） -/

/-- **capstone: level-27 μ₂₇ 完全性核（無条件）** — μ₃(M₂₇) 完全性（q27cMu3Complete
    の discharge）と、その帰結の無条件 μ₉/μ₂₇ 完全性の束ね。q27c の条件付き
    capstone（Q3Mu27CompletenessData）と異なり、入力仮定を持たない。 -/
structure Q3Mu27KernelData where
  /-- μ₃(M₂₇) 完全性（q27c の名前付き入力命題そのもの・無条件証明済み）。 -/
  mu3_complete : q27cMu3Complete
  /-- μ₉(M₂₇) 完全性（無条件）: u⁹=1 ⟹ u∈μ₉。 -/
  mu9_complete : ∀ u : q27kCar, q27cCube (q27cCube u) = q27kOne → q27cMu9 u
  /-- μ₂₇ 完全性（無条件・塔分解）: u²⁷=1 ⟹ u∈μ₂₇。 -/
  mu27_complete : ∀ u : q27kCar,
    q27cCube (q27cCube (q27cCube u)) = q27kOne → q27cMu27 u

/-- **capstone 実例** — 実 O_{M₂₇} = q27kRing 上の無条件 μ₂₇ 完全性核。 -/
def q27cm_data : Q3Mu27KernelData where
  mu3_complete := q27cm_mu3_complete
  mu9_complete := q27cm_mu9_complete
  mu27_complete := q27cm_mu27_complete

/-- **level-27 μ₂₇ 完全性核（無条件）の存在**。 -/
theorem q27cm_exists : Nonempty Q3Mu27KernelData := ⟨q27cm_data⟩

end IUT
