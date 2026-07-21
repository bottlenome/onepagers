/-
  IUT/Q3Mu27Completeness.lean — q27c（level-27 KILL キャンペーン / μ₂₇ 完全性の
    クローン層: 生環恒等式の (M₉, ζ₉) 実例化＋塔分解 μ₂₇ = μ₉-tower 1 段上）

  ── 主要成果の分類: **[実／(c) 承認済み足場]**（named 実ターゲット = 柱A **A6**
     level-27 第 2 層 KILL キャンペーンの μ₂₇ 完全性核 q27c。本ファイルは scope
     `audit/level27-kill-scope-2026-07-11.md` §3 が「~50–60% クリーンクローン」と
     査定した**クローン部分のみ**を先行して積む:
     (i) q9c の純 CRing 生恒等式 q9c_rawF1/F2/F3/F3'/rawNine を R=q3kRing・
         d=q3kZeta9（base=実 O_{M₉}・ねじれ=実 ζ₉）で実例化（再証明ゼロ・§3.1）、
     (ii) 塔分解 μ₂₇ 完全性（q9c_mu9_complete の 1 段上クローン・Z-捻り・
         27 乗展開なし・u²⁷=((u⁹))³ → μ₃(M₂₇) 核の 2 段消費）。
     genuine 新規＝μ₃(M₂₇) 完全性核（B1'–B7'：M₉ 正則性パック・6 座標ノルム
     単数判定・12 座標交互パリティ降下）は**並行モジュール q27ci/q27cs の仕事**
     であり、本ファイルでは **q27cMu3Complete という名前付き命題（入力仮定）**
     として正直に受け、塔分解はその仮定の下で完全証明する（→ 正直な限定 1）。
     後続本物化計画: q27ci（M₉ 正則性パック）＋q27cs 配線 → μ₃(M₂₇) 完全性の
     無条件証明 → 本ファイルの q27c_mu27_complete_of_mu3 に代入して μ₂₇ 完全性が
     無条件化 → q27tl/q27mt/q27mr → q27mb（kill_mod27）。

  complete_pct 影響: **complete_pct 0 前進（A6 は 0.61 のまま・帽子 ≤0.65 不変）**。
     本ファイルは kill も剛性もテータも橋も含まないクローン層＋条件付き塔分解で
     あり、実 IUT 完全証明率を動かさない。A6 status を一切動かさない（過大主張
     しない）。s_A6 が動き得るのはキャンペーン末端 q27mb＋crk27 接続時のみ。

  内容:
   * q27c_F1/F2/F3/F3'/rawNine — q9c 純 CRing 生恒等式の (R=q3kRing, d=ζ₉) 実例化
       （level-27 の G=a²+ζ₉bc 成分方程式の骨・B 連鎖（q27ci 側）が消費する形）
   * q27cCube / q27c_cube_mul / q27c_nine_mul / q27c_cube_embed — 立方演算の簿記
       （(xy)³=x³y³・(xy)⁹=x⁹y⁹・embed の立方）
   * q27cZinv / q27c_Zinv_mul_Z / q27c_Z_pow9 / q27c_Zinv_pow9
       — **Z⁻¹ = ζ₉⁻¹Z²（実元・座標形 (0,0,Y⁻¹)）**・Z⁹=ζ₃・(Z⁻¹)⁹=ζ₃²
   * q27c_embed_mul_Z / q27c_slotY_mul_Z / q27c_kslotY_mul_Y — スロット押し出し
   * q27cMu3Complete — **μ₃(M₂₇) 完全性の名前付き入力命題**（q9c B7 の level-27 版
       言明・証明は q27ci/q27cs 後続——本ファイルでは仮定として消費）
   * q27cMu9 / q27cMu27 — μ₉(M₂₇)＝M₉ 対角の 9 元・μ₂₇＝μ₉×{1,Z,Z²} スロット分解
   * q27c_mu9_complete_of_mu3 — ★ u⁹=1 ⟹ u∈μ₉（μ₃(M₂₇) 入力の下・Y-捻り）
   * q27c_mu27_complete_of_mu3 — ★★ u²⁷=1 ⟹ u∈μ₂₇（塔分解・Z-捻り・27 乗展開なし）
   * Q3Mu27CompletenessData / q27c_data / q27c_exists — capstone（条件付き形を明記）

  正直な限定（§4 規約により消さない・弱化しない・q27k/q9c/q3k 継承の上に追記）:
  1. **μ₃(M₂₇) 完全性は本ファイルでは証明しない**（q27cMu3Complete は入力仮定。
     その中身＝M₉ 正則性パック・6 座標ノルム単数判定・12 座標交互パリティ降下は
     genuine 新規で、並行モジュール q27ci（正則性）＋q27cs（降下核・実装済みの
     抽象降下エンジン）の配線後に別ラウンドで discharge する。本ファイルの
     μ₉/μ₂₇ 完全性は**この入力を仮定した条件付き定理**である）。
  2. **本モジュールは何も kill しない**（テータ群・Weil pairing・剛性ゼロ——
     それは後続 q27mt/q27mr/q27mb）。A6 status を動かさない。
  3. **奇部（u²⁷=−1 ⟹ μ₅₄）は収録しない**（q3mc/q9c の正直限定の前例どおり）。
  4. μ₂₇ の元は**スロット分解の存在形**（∃ w∈μ₉, u∈{(w,0,0),(0,w,0),(0,0,w)}）で
     表す（27 元の列挙と同値・選択公理不要の Exists）。
  5. q27k/q3k/q3rq/q9c の正直限定を全て継承（O_{M₂₇} と単数群のみ・体化なし・
     τ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・wild 分割/付値は
     q27ps 側・兄弟担体・tmzLimit 比較橋なし）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用（Or 破壊は
  obtain・rw/show/exact/refine/calc のみ）。
-/
import IUT.Q3KummerNonic
import IUT.Q3Mu9Completeness

namespace IUT

/-! ## q27c-0raw: q9c 純 CRing 生恒等式の (R=q3kRing, d=ζ₉) 実例化（再証明ゼロ）

    q9c_rawF1/F2/F3/F3'/rawNine は一般 `(R : CRing) (a b c d : R.carrier)` で
    証明済み（Q3Mu9Completeness:55–181）。level-27 の B 連鎖（q27ci 側）が消費する
    のは base=O_{M₉}=q3kRing・ねじれ d=ζ₉=q3kZeta9 の実例——ここで名前を付けて
    輸出する（scope §3.1 の「最も強く最も堅い再利用」）。 -/

/-- **F1 の level-27 実例**: E1' = b·G + ζ₉·a·c²（G = a² + ζ₉·bc・M₉ 係数）。 -/
theorem q27c_F1 (a b c : q3kCar) :
    q3kAdd (q3kAdd (q3kMul (q3kMul a a) b) (q3kMul q3kZeta9 (q3kMul a (q3kMul c c))))
          (q3kMul q3kZeta9 (q3kMul (q3kMul b b) c))
    = q3kAdd (q3kMul b (q3kAdd (q3kMul a a) (q3kMul q3kZeta9 (q3kMul b c))))
            (q3kMul q3kZeta9 (q3kMul a (q3kMul c c))) :=
  q9c_rawF1 q3kRing a b c q3kZeta9

/-- **F2 の level-27 実例**: E2' = c·G + a·b²。 -/
theorem q27c_F2 (a b c : q3kCar) :
    q3kAdd (q3kAdd (q3kMul (q3kMul a a) c) (q3kMul a (q3kMul b b)))
          (q3kMul q3kZeta9 (q3kMul b (q3kMul c c)))
    = q3kAdd (q3kMul c (q3kAdd (q3kMul a a) (q3kMul q3kZeta9 (q3kMul b c))))
            (q3kMul a (q3kMul b b)) :=
  q9c_rawF2 q3kRing a b c q3kZeta9

/-- **F3 の level-27 実例**: E1'·b = b²·G + ζ₉·(a·b·c)·c。 -/
theorem q27c_F3 (a b c : q3kCar) :
    q3kMul (q3kAdd (q3kAdd (q3kMul (q3kMul a a) b) (q3kMul q3kZeta9 (q3kMul a (q3kMul c c))))
                 (q3kMul q3kZeta9 (q3kMul (q3kMul b b) c))) b
    = q3kAdd (q3kMul (q3kMul b b) (q3kAdd (q3kMul a a) (q3kMul q3kZeta9 (q3kMul b c))))
            (q3kMul q3kZeta9 (q3kMul (q3kMul a (q3kMul b c)) c)) :=
  q9c_rawF3 q3kRing a b c q3kZeta9

/-- **F3' の level-27 実例**: E2'·c = c²·G + (a·b·c)·b。 -/
theorem q27c_F3' (a b c : q3kCar) :
    q3kMul (q3kAdd (q3kAdd (q3kMul (q3kMul a a) c) (q3kMul a (q3kMul b b)))
                 (q3kMul q3kZeta9 (q3kMul b (q3kMul c c)))) c
    = q3kAdd (q3kMul (q3kMul c c) (q3kAdd (q3kMul a a) (q3kMul q3kZeta9 (q3kMul b c))))
            (q3kMul (q3kMul a (q3kMul b c)) b) :=
  q9c_rawF3' q3kRing a b c q3kZeta9

/-- **9-fold の骨の level-27 実例**（M₉ 内の 9 個の W の再結合）。 -/
theorem q27c_rawNine (W : q3kCar) :
    q3kAdd (q3kAdd (q3kAdd (q3kAdd (q3kAdd (q3kAdd W W) W) W) W) W)
          (q3kAdd W (q3kAdd W W))
    = q3kAdd (q3kAdd W (q3kAdd W W))
            (q3kAdd (q3kAdd W (q3kAdd W W)) (q3kAdd W (q3kAdd W W))) :=
  q9c_rawNine q3kRing W

/-! ## q27c-1: 立方演算の簿記（(xy)³=x³y³・(xy)⁹=x⁹y⁹・embed の立方） -/

/-- 立方 x³ = (x·x)·x（q9c の hu9 形と同じ括り・27 乗は cube 3 回入れ子）。 -/
def q27cCube (x : q27kCar) : q27kCar := q27kMul (q27kMul x x) x

/-- 立方の展開形（rw 補助）。 -/
theorem q27c_cube_eq (x : q27kCar) : q27cCube x = q27kMul (q27kMul x x) x := rfl

/-- x·1 = x（可換＋one_mul）。 -/
theorem q27c_mul_one (x : q27kCar) : q27kMul x q27kOne = x :=
  (q27k_mul_comm x q27kOne).trans (q27k_one_mul x)

/-- 1³ = 1。 -/
theorem q27c_cube_one : q27cCube q27kOne = q27kOne := by
  show q27kMul (q27kMul q27kOne q27kOne) q27kOne = q27kOne
  rw [q27k_one_mul q27kOne, q27k_one_mul q27kOne]

/-- **(xy)³ = x³·y³**（可換環の並べ替え・q9c_cube_mul の level-27 クローン）。 -/
theorem q27c_cube_mul (x y : q27kCar) :
    q27cCube (q27kMul x y) = q27kMul (q27cCube x) (q27cCube y) := by
  show q27kMul (q27kMul (q27kMul x y) (q27kMul x y)) (q27kMul x y)
      = q27kMul (q27kMul (q27kMul x x) x) (q27kMul (q27kMul y y) y)
  rw [q27k_kM_eq, q27kRing.mul_mul_mul_comm x y x y,
      q27kRing.mul_mul_mul_comm (q27kRing.mul x x) (q27kRing.mul y y) x y]

/-- **(xy)⁹ = x⁹·y⁹**（cube_mul の 2 回適用・9 乗展開なし）。 -/
theorem q27c_nine_mul (x y : q27kCar) :
    q27cCube (q27cCube (q27kMul x y))
    = q27kMul (q27cCube (q27cCube x)) (q27cCube (q27cCube y)) := by
  rw [q27c_cube_mul x y, q27c_cube_mul (q27cCube x) (q27cCube y)]

/-- embed の立方: (E m)³ = E(m³)（q27k_embed_mul の 2 回適用）。 -/
theorem q27c_cube_embed (m : q3kCar) :
    q27cCube (q27kEmbed m) = q27kEmbed (q3kMul (q3kMul m m) m) := by
  show q27kMul (q27kMul (q27kEmbed m) (q27kEmbed m)) (q27kEmbed m)
      = q27kEmbed (q3kMul (q3kMul m m) m)
  rw [q27k_embed_mul m m, q27k_embed_mul (q3kMul m m) m]

/-! ## q27c-2: Z⁻¹ = ζ₉⁻¹Z²（実元・座標形 (0,0,Y⁻¹)）と Z の 9 乗 -/

/-- **Z⁻¹ = ζ₉⁻¹·Z²**（座標形 (0,0,q9cYinv)・q9cYinv = Y⁻¹ = ζ₃²Y² は q9c の実元）。 -/
def q27cZinv : q27kCar := ((q3kZero, q3kZero, q9cYinv) : q27kCar)

/-- Z⁻¹·Z = 1（ζ₉·ζ₉⁻¹ = 1 に帰着する座標計算）。 -/
theorem q27c_Zinv_mul_Z : q27kMul q27cZinv q27kZeta27 = q27kOne := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
          (q3kRing.mul q9cYinv q3kRing.one))) = q3kRing.one
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.mul_one q9cYinv,
        q3kRing.zero_add q9cYinv,
        show q3kRing.mul q3kZeta9 q9cYinv = q3kRing.one from q9c_Y_mul_Yinv,
        q3kRing.zero_add q3kRing.one]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.one)
        (q3kRing.mul q3kRing.zero q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul q9cYinv q3kRing.zero)) = q3kRing.zero
    rw [q3kRing.zero_mul q3kRing.one, q3kRing.mul_zero q3kRing.zero,
        q3kRing.zero_add q3kRing.zero, q3kRing.mul_zero q9cYinv,
        q3kRing.mul_zero q3kZeta9, q3kRing.zero_add q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kRing.zero q3kRing.one))
        (q3kRing.mul q9cYinv q3kRing.zero) = q3kRing.zero
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.zero_mul q3kRing.one,
        q3kRing.zero_add q3kRing.zero, q3kRing.mul_zero q9cYinv,
        q3kRing.zero_add q3kRing.zero]

/-- Z·Z⁻¹ = 1。 -/
theorem q27c_Z_mul_Zinv : q27kMul q27kZeta27 q27cZinv = q27kOne := by
  rw [q27k_mul_comm]; exact q27c_Zinv_mul_Z

/-- **Z⁹ = ζ₃**（q27k_zeta27_pow9 の cube-括り形・定義的に同一）。 -/
theorem q27c_Z_pow9 : q27cCube (q27cCube q27kZeta27) = q27kEmbed q27kZeta3 :=
  q27k_zeta27_pow9

/-- **(Z⁻¹)⁹ = ζ₃²**（(Z⁻¹·Z)⁹=1 と ζ₃·ζ₃²=1 から・q9c_Yinv3 のイディオム）。 -/
theorem q27c_Zinv_pow9 : q27cCube (q27cCube q27cZinv) = q27kEmbed q27kZeta3Sq := by
  have h1 : q27kMul (q27cCube (q27cCube q27cZinv)) (q27kEmbed q27kZeta3) = q27kOne := by
    rw [← q27c_Z_pow9, ← q27c_nine_mul q27cZinv q27kZeta27, q27c_Zinv_mul_Z,
        q27c_cube_one, q27c_cube_one]
  calc q27cCube (q27cCube q27cZinv)
      = q27kMul (q27cCube (q27cCube q27cZinv)) q27kOne :=
        (q27c_mul_one (q27cCube (q27cCube q27cZinv))).symm
    _ = q27kMul (q27cCube (q27cCube q27cZinv))
          (q27kMul (q27kEmbed q27kZeta3) (q27kEmbed q27kZeta3Sq)) := by
        rw [q27k_embed_mul q27kZeta3 q27kZeta3Sq,
            show q3kMul q27kZeta3 q27kZeta3Sq = q3kOne from q27k_z_zsqR1,
            q27k_embed_one]
    _ = q27kMul (q27kMul (q27cCube (q27cCube q27cZinv)) (q27kEmbed q27kZeta3))
          (q27kEmbed q27kZeta3Sq) :=
        (q27k_mul_assoc (q27cCube (q27cCube q27cZinv)) (q27kEmbed q27kZeta3)
          (q27kEmbed q27kZeta3Sq)).symm
    _ = q27kMul q27kOne (q27kEmbed q27kZeta3Sq) := by rw [h1]
    _ = q27kEmbed q27kZeta3Sq := q27k_one_mul (q27kEmbed q27kZeta3Sq)

/-! ## q27c-3: スロット押し出し（embed·Z = Z-スロット・Z-スロット·Z = Z²-スロット） -/

/-- (m,0,0)·Z = (0,m,0)（M₉ 対角の Z-スロットへの押し出し）。 -/
theorem q27c_embed_mul_Z (a : q3kCar) :
    q27kMul (q27kEmbed a) q27kZeta27 = ((q3kZero, a, q3kZero) : q27kCar) := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul a q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
          (q3kRing.mul q3kRing.zero q3kRing.one))) = q3kRing.zero
    rw [q3kRing.mul_zero a, q3kRing.mul_zero q3kRing.zero,
        q3kRing.zero_mul q3kRing.one, q3kRing.zero_add q3kRing.zero,
        q3kRing.mul_zero q3kZeta9, q3kRing.zero_add q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul a q3kRing.one)
        (q3kRing.mul q3kRing.zero q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul q3kRing.zero q3kRing.zero)) = a
    rw [q3kRing.mul_one a, q3kRing.mul_zero q3kRing.zero, q3kRing.add_zero a,
        q3kRing.mul_zero q3kZeta9, q3kRing.add_zero a]
  · show q3kRing.add (q3kRing.add (q3kRing.mul a q3kRing.zero)
        (q3kRing.mul q3kRing.zero q3kRing.one))
        (q3kRing.mul q3kRing.zero q3kRing.zero) = q3kRing.zero
    rw [q3kRing.mul_zero a, q3kRing.zero_mul q3kRing.one,
        q3kRing.zero_add q3kRing.zero, q3kRing.mul_zero q3kRing.zero,
        q3kRing.add_zero q3kRing.zero]

/-- (0,m,0)·Z = (0,0,m)（Z-スロットの Z²-スロットへの押し出し）。 -/
theorem q27c_slotY_mul_Z (a : q3kCar) :
    q27kMul ((q3kZero, a, q3kZero) : q27kCar) q27kZeta27
    = ((q3kZero, q3kZero, a) : q27kCar) := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul a q3kRing.zero)
          (q3kRing.mul q3kRing.zero q3kRing.one))) = q3kRing.zero
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.mul_zero a,
        q3kRing.zero_mul q3kRing.one, q3kRing.zero_add q3kRing.zero,
        q3kRing.mul_zero q3kZeta9, q3kRing.zero_add q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.one)
        (q3kRing.mul a q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul q3kRing.zero q3kRing.zero)) = q3kRing.zero
    rw [q3kRing.zero_mul q3kRing.one, q3kRing.mul_zero a,
        q3kRing.zero_add q3kRing.zero, q3kRing.mul_zero q3kRing.zero,
        q3kRing.mul_zero q3kZeta9, q3kRing.zero_add q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul a q3kRing.one))
        (q3kRing.mul q3kRing.zero q3kRing.zero) = a
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.mul_one a,
        q3kRing.zero_add a, q3kRing.add_zero a]

/-- M₉ 内スロット押し出し: (0,t,0)·Y = (0,0,t)（q9c_embed_mul_Y の隣・μ₉ 端点用）。 -/
theorem q27c_kslotY_mul_Y (t : q3rqCar) :
    q3kMul ((q3rqZero, t, q3rqZero) : q3kCar) q3kZeta9
    = ((q3rqZero, q3rqZero, t) : q3kCar) := by
  apply q3k_ext
  · show q3rqAdd (q3rqMul q3rqZero q3rqZero)
        (q3rqMul q3rqZeta (q3rqAdd (q3rqMul t q3rqZero) (q3rqMul q3rqZero q3rqOne)))
        = q3rqZero
    rw [q9c_zm q3rqZero, q9c_mz t, q9c_zm q3rqOne, q9c_za q3rqZero,
        q9c_mz q3rqZeta, q9c_za q3rqZero]
  · show q3rqAdd (q3rqAdd (q3rqMul q3rqZero q3rqOne) (q3rqMul t q3rqZero))
        (q3rqMul q3rqZeta (q3rqMul q3rqZero q3rqZero)) = q3rqZero
    rw [q9c_zm q3rqOne, q9c_mz t, q9c_za q3rqZero, q9c_zm q3rqZero,
        q9c_mz q3rqZeta, q9c_za q3rqZero]
  · show q3rqAdd (q3rqAdd (q3rqMul q3rqZero q3rqZero) (q3rqMul t q3rqOne))
        (q3rqMul q3rqZero q3rqZero) = t
    rw [q9c_zm q3rqZero, q3rq_mul_one t, q9c_za t, q9c_az t]

/-! ## q27c-4: μ 述語（μ₃(M₂₇) 入力・μ₉(M₂₇)・μ₂₇ スロット分解） -/

/-- **μ₃(M₂₇) 完全性の名前付き入力命題**（q9c_m_mu3_complete の level-27 版言明）。
    x³=1 in O_{M₂₇} ⟹ x ∈ μ₃ ⊂ L₂ ⊂ M₉ ⊂ M₂₇（対角）。
    **本ファイルでは証明しない**——中身（M₉ 正則性パック・6 座標ノルム単数判定・
    12 座標交互パリティ降下）は q27ci/q27cs 配線後の後続ラウンドで discharge。 -/
def q27cMu3Complete : Prop :=
  ∀ x : q27kCar, q27kMul (q27kMul x x) x = q27kOne →
    x = q27kOne ∨ x = q27kEmbed q27kZeta3 ∨ x = q27kEmbed q27kZeta3Sq

/-- **μ₉(M₂₇)** = M₉ 対角に埋め込まれた μ₉（q3kMu9 の 9 元・存在形）。 -/
def q27cMu9 (u : q27kCar) : Prop :=
  ∃ w : q3kCar, q3kMu9 w ∧ u = q27kEmbed w

/-- **μ₂₇** = μ₉ × {1, Z, Z²} のスロット分解（27 元 = ζ₉^m·Z^j・存在形）。 -/
def q27cMu27 (u : q27kCar) : Prop :=
  ∃ w : q3kCar, q3kMu9 w ∧
    (u = ((w, q3kZero, q3kZero) : q27kCar)
      ∨ u = ((q3kZero, w, q3kZero) : q27kCar)
      ∨ u = ((q3kZero, q3kZero, w) : q27kCar))

/-- 健全性チェック: 1 ∈ μ₂₇。 -/
theorem q27c_one_mem_mu27 : q27cMu27 q27kOne :=
  ⟨q3kOne, Or.inl rfl, Or.inl rfl⟩

/-- 健全性チェック: ζ₂₇ = Z ∈ μ₂₇（w=1 の Z-スロット）。 -/
theorem q27c_z27_mem_mu27 : q27cMu27 q27kZeta27 :=
  ⟨q3kOne, Or.inl rfl, Or.inr (Or.inl rfl)⟩

/-! ## q27c-5（★）: μ₉(M₂₇) 完全性（μ₃(M₂₇) 入力の下・Y-捻り・q9c B8 のクローン） -/

/-- **★ μ₉(M₂₇) 完全性**: u⁹=(u³)³=1 ⟹ u ∈ μ₉（M₉ 対角）——μ₃(M₂₇) 完全性入力
    h3 の 2 段消費＋Y-捻り（embed(Y⁻¹)=q9cYinv の埋め込みで u³ の ζ₃ 枝を還元）。
    q9c_mu9_complete の 1 段上クローン（9 乗展開なし）。 -/
theorem q27c_mu9_complete_of_mu3 (h3 : q27cMu3Complete) (u : q27kCar)
    (hu9 : q27cCube (q27cCube u) = q27kOne) : q27cMu9 u := by
  obtain hw1 | hwz | hwzsq := h3 (q27cCube u) hu9
  · -- u³ = 1 ⟹ u ∈ μ₃(M₂₇) ⊂ μ₉
    obtain g1 | gz | gzsq := h3 u hw1
    · exact ⟨q3kOne, Or.inl rfl, g1⟩
    · exact ⟨q27kZeta3, Or.inr (Or.inl rfl), gz⟩
    · exact ⟨q27kZeta3Sq, Or.inr (Or.inr (Or.inl rfl)), gzsq⟩
  · -- u³ = ζ₃: u·embed(Y⁻¹) ∈ μ₃(M₂₇) ⟹ u ∈ μ₃·Y（Z-スロットでなく M₉ 対角内）
    have hc : q27cCube (q27kMul u (q27kEmbed q9cYinv)) = q27kOne := by
      rw [q27c_cube_mul u (q27kEmbed q9cYinv), hwz, q27c_cube_embed q9cYinv,
          q9c_Yinv3, q27k_embed_mul q27kZeta3 (q3kEmbed q3rqZetaSq),
          show q3kMul q27kZeta3 (q3kEmbed q3rqZetaSq) = q3kOne from q27k_z_zsqR1,
          q27k_embed_one]
    have hurec : q27kMul (q27kMul u (q27kEmbed q9cYinv)) (q27kEmbed q3kZeta9) = u := by
      rw [q27k_mul_assoc u (q27kEmbed q9cYinv) (q27kEmbed q3kZeta9),
          q27k_embed_mul q9cYinv q3kZeta9, q9c_Yinv_mul_Y, q27k_embed_one,
          q27c_mul_one u]
    obtain g1 | gz | gzsq := h3 (q27kMul u (q27kEmbed q9cYinv)) hc
    · refine ⟨q3kZeta9, Or.inr (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
      rw [← hurec, g1]
      exact q27k_one_mul (q27kEmbed q3kZeta9)
    · refine ⟨((q3rqZero, q3rqZeta, q3rqZero) : q3kCar),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), ?_⟩
      rw [← hurec, gz, q27k_embed_mul q27kZeta3 q3kZeta9,
          show q3kMul q27kZeta3 q3kZeta9 = ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar)
            from q9c_embed_mul_Y q3rqZeta]
    · refine ⟨((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), ?_⟩
      rw [← hurec, gzsq, q27k_embed_mul q27kZeta3Sq q3kZeta9,
          show q3kMul q27kZeta3Sq q3kZeta9 = ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar)
            from q9c_embed_mul_Y q3rqZetaSq]
  · -- u³ = ζ₃²: u·embed(Y⁻¹)² ∈ μ₃(M₂₇) ⟹ u ∈ μ₃·Y²
    have hc : q27cCube (q27kMul (q27kMul u (q27kEmbed q9cYinv)) (q27kEmbed q9cYinv))
        = q27kOne := by
      rw [q27c_cube_mul (q27kMul u (q27kEmbed q9cYinv)) (q27kEmbed q9cYinv),
          q27c_cube_mul u (q27kEmbed q9cYinv), hwzsq, q27c_cube_embed q9cYinv,
          q9c_Yinv3, q27k_embed_mul q27kZeta3Sq (q3kEmbed q3rqZetaSq),
          show q3kMul q27kZeta3Sq (q3kEmbed q3rqZetaSq) = q27kZeta3 from q27k_zsq_zsqR,
          q27k_embed_mul q27kZeta3 (q3kEmbed q3rqZetaSq),
          show q3kMul q27kZeta3 (q3kEmbed q3rqZetaSq) = q3kOne from q27k_z_zsqR1,
          q27k_embed_one]
    have hurec : q27kMul (q27kMul (q27kMul (q27kMul u (q27kEmbed q9cYinv))
        (q27kEmbed q9cYinv)) (q27kEmbed q3kZeta9)) (q27kEmbed q3kZeta9) = u := by
      rw [q27k_mul_assoc (q27kMul u (q27kEmbed q9cYinv)) (q27kEmbed q9cYinv)
            (q27kEmbed q3kZeta9),
          q27k_embed_mul q9cYinv q3kZeta9, q9c_Yinv_mul_Y, q27k_embed_one,
          q27c_mul_one (q27kMul u (q27kEmbed q9cYinv)),
          q27k_mul_assoc u (q27kEmbed q9cYinv) (q27kEmbed q3kZeta9),
          q27k_embed_mul q9cYinv q3kZeta9, q9c_Yinv_mul_Y, q27k_embed_one,
          q27c_mul_one u]
    obtain g1 | gz | gzsq := h3 (q27kMul (q27kMul u (q27kEmbed q9cYinv))
        (q27kEmbed q9cYinv)) hc
    · refine ⟨((q3rqZero, q3rqZero, q3rqOne) : q3kCar),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), ?_⟩
      rw [← hurec, g1, q27k_one_mul (q27kEmbed q3kZeta9),
          q27k_embed_mul q3kZeta9 q3kZeta9, q3k_zeta9_sq]
    · refine ⟨((q3rqZero, q3rqZero, q3rqZeta) : q3kCar),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))), ?_⟩
      rw [← hurec, gz, q27k_embed_mul q27kZeta3 q3kZeta9,
          show q3kMul q27kZeta3 q3kZeta9 = ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar)
            from q9c_embed_mul_Y q3rqZeta,
          q27k_embed_mul ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) q3kZeta9,
          q27c_kslotY_mul_Y q3rqZeta]
    · refine ⟨((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))), ?_⟩
      rw [← hurec, gzsq, q27k_embed_mul q27kZeta3Sq q3kZeta9,
          show q3kMul q27kZeta3Sq q3kZeta9 = ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar)
            from q9c_embed_mul_Y q3rqZetaSq,
          q27k_embed_mul ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) q3kZeta9,
          q27c_kslotY_mul_Y q3rqZetaSq]

/-! ## q27c-6（★★）: 塔分解 μ₂₇ 完全性（Z-捻り・27 乗展開なし・q9c B8 の 1 段上） -/

/-- **★★ 塔分解 μ₂₇ 完全性**: u²⁷=((u³)³)³=1 ⟹ u ∈ μ₂₇——μ₃(M₂₇) 入力 h3 の下、
    u⁹ ∈ μ₃ に分岐し Z-捻り（Z⁻¹=ζ₉⁻¹Z²・(Z⁻¹)⁹=ζ₃²）で μ₉(M₂₇) 完全性へ還元。
    q9c_mu9_complete の塔をもう 1 段登る（27 乗の展開は一切しない）。 -/
theorem q27c_mu27_complete_of_mu3 (h3 : q27cMu3Complete) (u : q27kCar)
    (hu27 : q27cCube (q27cCube (q27cCube u)) = q27kOne) : q27cMu27 u := by
  obtain h9one | h9z | h9zsq := h3 (q27cCube (q27cCube u)) hu27
  · -- u⁹ = 1 ⟹ u ∈ μ₉（M₉ 対角スロット）
    obtain ⟨w, hw, he⟩ := q27c_mu9_complete_of_mu3 h3 u h9one
    exact ⟨w, hw, Or.inl he⟩
  · -- u⁹ = ζ₃: (u·Z⁻¹)⁹ = ζ₃·ζ₃² = 1 ⟹ u ∈ μ₉·Z（Z-スロット）
    have hu'9 : q27cCube (q27cCube (q27kMul u q27cZinv)) = q27kOne := by
      rw [q27c_nine_mul u q27cZinv, h9z, q27c_Zinv_pow9,
          q27k_embed_mul q27kZeta3 q27kZeta3Sq,
          show q3kMul q27kZeta3 q27kZeta3Sq = q3kOne from q27k_z_zsqR1,
          q27k_embed_one]
    have hurec : q27kMul (q27kMul u q27cZinv) q27kZeta27 = u := by
      rw [q27k_mul_assoc u q27cZinv q27kZeta27, q27c_Zinv_mul_Z, q27c_mul_one u]
    obtain ⟨w, hw, he⟩ := q27c_mu9_complete_of_mu3 h3 (q27kMul u q27cZinv) hu'9
    refine ⟨w, hw, Or.inr (Or.inl ?_)⟩
    rw [← hurec, he]
    exact q27c_embed_mul_Z w
  · -- u⁹ = ζ₃²: (u·Z⁻¹·Z⁻¹)⁹ = ζ₃²·ζ₃²·ζ₃² = 1 ⟹ u ∈ μ₉·Z²（Z²-スロット）
    have hu''9 : q27cCube (q27cCube (q27kMul (q27kMul u q27cZinv) q27cZinv))
        = q27kOne := by
      rw [q27c_nine_mul (q27kMul u q27cZinv) q27cZinv, q27c_nine_mul u q27cZinv,
          h9zsq, q27c_Zinv_pow9, q27k_embed_mul q27kZeta3Sq q27kZeta3Sq,
          show q3kMul q27kZeta3Sq q27kZeta3Sq = q27kZeta3 from q27k_zsq_zsqR,
          q27k_embed_mul q27kZeta3 q27kZeta3Sq,
          show q3kMul q27kZeta3 q27kZeta3Sq = q3kOne from q27k_z_zsqR1,
          q27k_embed_one]
    have hurec : q27kMul (q27kMul (q27kMul (q27kMul u q27cZinv) q27cZinv)
        q27kZeta27) q27kZeta27 = u := by
      rw [q27k_mul_assoc (q27kMul u q27cZinv) q27cZinv q27kZeta27,
          q27c_Zinv_mul_Z, q27c_mul_one (q27kMul u q27cZinv),
          q27k_mul_assoc u q27cZinv q27kZeta27, q27c_Zinv_mul_Z, q27c_mul_one u]
    obtain ⟨w, hw, he⟩ := q27c_mu9_complete_of_mu3 h3
      (q27kMul (q27kMul u q27cZinv) q27cZinv) hu''9
    refine ⟨w, hw, Or.inr (Or.inr ?_)⟩
    rw [← hurec, he, q27c_embed_mul_Z w]
    exact q27c_slotY_mul_Z w

/-! ## q27c-7: capstone（条件付き形を明記） -/

/-- **capstone: level-27 μ₂₇ 完全性データ（クローン層・条件付き）** — μ₃(M₂₇)
    完全性を**入力命題**として受け、μ₉(M₂₇)/μ₂₇ 完全性を塔分解で返す。
    mu3_input の discharge（M₉ 正則性パック＋12 座標降下）は q27ci/q27cs 後続——
    本 capstone は無条件の μ₂₇ 完全性を**主張しない**（正直な限定 1）。 -/
structure Q3Mu27CompletenessData where
  /-- μ₃(M₂₇) 完全性の入力命題（言明のみ・証明は後続 q27ci/q27cs 配線）。 -/
  mu3_input : Prop
  /-- μ₉(M₂₇) 判定述語（M₉ 対角の 9 元・存在形）。 -/
  mu9set : q27kCar → Prop
  /-- μ₂₇ 判定述語（μ₉×{1,Z,Z²} スロット分解・存在形）。 -/
  mu27set : q27kCar → Prop
  /-- μ₉(M₂₇) 完全性（μ₃ 入力の下）: u⁹=1 ⟹ u∈μ₉。 -/
  mu9_of_mu3 : mu3_input → ∀ u : q27kCar,
    q27cCube (q27cCube u) = q27kOne → mu9set u
  /-- μ₂₇ 完全性（μ₃ 入力の下・塔分解）: u²⁷=1 ⟹ u∈μ₂₇。 -/
  mu27_of_mu3 : mu3_input → ∀ u : q27kCar,
    q27cCube (q27cCube (q27cCube u)) = q27kOne → mu27set u

/-- **capstone 実例** — 実 O_{M₂₇} = q27kRing 上の条件付き μ₉/μ₂₇ 完全性。 -/
def q27c_data : Q3Mu27CompletenessData where
  mu3_input := q27cMu3Complete
  mu9set := q27cMu9
  mu27set := q27cMu27
  mu9_of_mu3 := fun h u => q27c_mu9_complete_of_mu3 h u
  mu27_of_mu3 := fun h u => q27c_mu27_complete_of_mu3 h u

/-- **level-27 μ₂₇ 完全性データ（条件付きクローン層）の存在**。 -/
theorem q27c_exists : Nonempty Q3Mu27CompletenessData := ⟨q27c_data⟩

end IUT
