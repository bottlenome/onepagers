/-
  IUT/Q3Mu27DescentSpike.lean — q27cs（level-27 μ₂₇ 完全性 / M₉ 基底 12 整数座標
  交互パリティ同時降下の de-risk スパイク）

  ── 主要成果の分類: **[実／本物の先行建設(b)]（de-risk スパイク）**（骨格・模型・代理でなく、
     level-27 kill キャンペーン（audit/level27-kill-scope-2026-07-11.md §3.3(b)）が
     「単一障害点（single failure point）」と査定した **μ₂₇ 完全性の B6 交互パリティ同時降下の
     M₉ 基底版**——b,c ∈ O_{M₂₇} = O_{M₉}[Z]/(Z³−ζ₉) の各係数が 6 ℤ₃-座標の O_{M₉} に住み、
     降下対象が 12 整数座標列になる段——の**単段（偶段・奇段）を、q3kMul（ζ₃-ねじれ畳み込み・
     Q3KummerCubic:99）のスロット毎に忠実な Int 影の上で完全証明**する。単数 peel は
     level-9 の 2 座標ノルム u₁²+3u₂² が使えず、**6 座標 q3k ノルム
     N = w₀³ + ζ₃w₁³ + ζ₃²w₂³ − 3ζ₃w₀w₁w₂ の随伴（adjugate）Cramer 恒等式**
     （q27cs_cramer0/1/2・本ファイルで新規に完全証明）で 3×3 ねじれ結合を対角化してから、
     L₂ 影の 2×2 peel（N₁²+3N₂²）を素冪 Euclid `q3cu_ppow_dvd` の消費で閉じる。
     交互合成 q27cs_descent_all（全レベル降下 glue）も同時に de-risk する。）

  complete_pct 影響: **complete_pct 0 前進（de-risk foundation）**。本スパイクは level-27
  kill の Module q27c（Q3Mu27Completeness・B6 降下核）の単一最大リスクの焼却であり、
  それ自体は実 IUT 完全証明率を動かさない。成果は「12 座標降下の数学が Lean で
  単段（偶・奇とも）＋交互合成まで choice-free に閉じた」という事実そのもの。

  内容:
   * q27cs-0: L₂ 影のペア演算（q27csAdd/Sub/Mul — q3rqMul の Int 影・q9csMulFst/Snd と
             成分ごとに定義一致 rfl）と射影補題
   * q27cs-1: ペア環計算キット（mul_comm/assoc/left_comm・分配・ras1/2/3 再結合）
   * q27cs-2: 可除性述語 PD/PM（ペア）・TD/TM/TDF/TDS（3 ペア組 = O_{M₉} 影）と閉包補題
             （q9cs toolbox 消費）
   * q27cs-3: O_{M₉} 影のねじれ畳み込み q27csTMul（q3kMul:99 のスロット毎 Int 影）と
             E1′/E2′ 影（E1′ = W·b + ζ₉(a·c²) + ζ₉(b²·c)、E2′ = W·c + a·b² + ζ₉(b·c²)、
             W = a²・ζ₉ 影 z と ζ₃ 影 e は任意抽象——非主要単項式の 3-content は値に非依存）
   * q27cs-4: **6 座標 q3k ノルム影 q27csNorm と随伴 Cramer 恒等式（★ 新規の核）**
             q27cs_cramer0/1/2 — u·(W·b) = N(W)·b の 3 スロット（u = 随伴、18 単項式相殺）
   * q27cs-5: **単数 peel** — q27cs_unit_sq_plus / q27cs_pair_peel（★q3cu_ppow_dvd 消費・
             2×2 L₂ peel）→ q27cs_norm_peel（Cramer 消費・6 座標一括 peel）
   * q27cs-6: **q27cs_descent_even（★）** 偶段 k=2m→2m+1（m≥1）: TD m (b,c) ＋ E′ 影の
             mod 3^{m+1} 可除から λ-自由 6 座標が 3^{m+1} へ
   * q27cs-7: **q27cs_descent_odd（★）** 奇段 k=2m+1→2m+2（全 m≥0）: 混合不変量 TM m から
             λ-側 6 座標が 3^{m+1} へ（基底 m=0 を含む——交互パリティの生命線）
   * q27cs-8: **q27cs_descent_all（★★）** 交互合成: 全レベル E′ 可除＋基底 TDF 1 から
             ∀m TD m（12 座標全消滅の帰納 glue）＋ W=a² 実例化 q27cs_descent_even_sq/odd_sq
   * q27cs-9: 忠実性影補題 — q3kMul スロット 0 の両 L₂ 座標のレベル n rep が q27csTMul 影と
             一致（q9cs_rq_mul_fst/snd_valn・q9cs_add_valn 消費・q9cs-7 の M₉ 版単一積橋）

  正直な限定（§4 規約・消さない・弱めない）:
  1. **スパイク＝単段＋交互合成のみ・Module q27c 本体ではない**。E1′/E2′ の可除性仮定
     （TD (m+1)）は仮定として取る——本物では u³=1 in O_{M₂₇} の Z/Z² 成分方程式（O_{M₉} の
     等式 E′=0）から q9cs_zero_rep_dvd 型の橋（level-9 と同一イディオム・再証明不要）で出る。
     その導出（立方展開・3 正則での 3 消去）は Module q27ci/q27c の仕事。
  2. **主語は O_{M₉} の 6 ℤ₃-座標 rep の Int 簿記**（b,c 各 6 座標 = 計 12 降下列と
     係数 W・a・ζ₉ 影 z・ζ₃ 影 e）。O_{M₂₇}（q27k 環）の元・乗法は登場しない（環は未建設・
     本スパイクが先行）。q27csTMul は q3kMul（Q3KummerCubic:99–105）のスロット毎忠実 Int 影
     （q27cs-9 でスロット 0 の両座標を実証・スロット 1/2 は同一合成の物量で Module 側）。
  3. **W（主要係数 a² の影）は自由変数として取り、単数正則性は 6 座標ノルム影の仮定
     hn : ¬3∣(q27csNorm e W₀ W₁ W₂).1 で受ける**。本物では a の O_{M₉} 単数性から
     ノルム乗法性（q27ci 正則性パックのターゲット）で discharge される。W = a·a 影の
     実例化形は q27cs_descent_even_sq/odd_sq に収録。
  4. **偶段は m≥1 のみ**（hm : 1 ≤ m）。基底 k=1→2 は奇段 m=0 が処理（q9cs と同一設計）。
     基底 TDF 1（λ-自由 6 座標の 3∣）は §3.4–3.5 型の単数枝反証の出口で、Module q27c の仕事。
  5. **de-risk 発見（正直申告）**: M₉ 基底の peel はノルム随伴経由で**両パリティを同時に**
     1 段深くする（level-9 の「偶段は第 1 座標のみ」より強い）。交互パリティが本質的に
     効くのは (i) 奇段 m=0 の混合 3-content（基底 bootstrap）と (ii) 偶段 m≥1 の
     2 次尾項 3^{2m} 評価のみ。単段の結論は設計文書の不変量増分（偶=λ-自由・奇=λ-側）に
     忠実に制限して述べる。

  全て選択公理不使用（新規 Classical.choice なし・sorry 皆無・禁止タクティク不使用。
  omega は純線形 Int/Nat ゴールのみ——非線形部分は全て Int.mul_assoc/mul_left_comm/
  mul_add/sub_mul 系の明示 rw で線形化してから）。#print axioms は [propext, Quot.sound] のみ。
-/
import IUT.Q3KummerCubeIdent
import IUT.Q3TateCuspidalization
import IUT.Q3Mu9Completeness

namespace IUT

/-! ## q27cs-0: L₂ 影のペア演算（q3rqMul の Int 影・q9cs と定義一致） -/

/-- L₂ = ℤ₃[√−3] の Int 影の担体: (λ-自由座標, λ-座標)。 -/
def q27csP : Type := Int × Int

/-- ペア加法（q3rqAdd の Int 影）。 -/
def q27csAdd (x y : q27csP) : q27csP := (x.1 + y.1, x.2 + y.2)

/-- ペア減法。 -/
def q27csSub (x y : q27csP) : q27csP := (x.1 - y.1, x.2 - y.2)

/-- ペア乗法（q3rqMul・D=−3 の Int 影）: (x·y)₁ = x₁y₁ − 3x₂y₂、(x·y)₂ = x₁y₂ + x₂y₁。 -/
def q27csMul (x y : q27csP) : q27csP :=
  (x.1 * y.1 - 3 * (x.2 * y.2), x.1 * y.2 + x.2 * y.1)

/-- **q9cs との定義一致（忠実性の第 1 の楔）**: q27csMul の第 1 座標は q9csMulFst
    （q9cs-7 で q3rqMul への忠実性が実証済みの Int 影）と定義的に同一。 -/
theorem q27cs_mul_fst_eq (x y : q27csP) :
    (q27csMul x y).1 = q9csMulFst x.1 x.2 y.1 y.2 := rfl

/-- 第 2 座標は q9csMulSnd と定義的に同一。 -/
theorem q27cs_mul_snd_eq (x y : q27csP) :
    (q27csMul x y).2 = q9csMulSnd x.1 x.2 y.1 y.2 := rfl

/-- ペア外延性。 -/
theorem q27cs_pext {x y : q27csP} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := by
  cases x with
  | mk a b =>
    cases y with
    | mk c d =>
      show (a, b) = (c, d)
      have ha : a = c := h1
      have hb : b = d := h2
      rw [ha, hb]

/-- 加法の第 1 射影。 -/
theorem q27cs_add_fst (x y : q27csP) : (q27csAdd x y).1 = x.1 + y.1 := rfl
/-- 加法の第 2 射影。 -/
theorem q27cs_add_snd (x y : q27csP) : (q27csAdd x y).2 = x.2 + y.2 := rfl
/-- 減法の第 1 射影。 -/
theorem q27cs_sub_fst (x y : q27csP) : (q27csSub x y).1 = x.1 - y.1 := rfl
/-- 減法の第 2 射影。 -/
theorem q27cs_sub_snd (x y : q27csP) : (q27csSub x y).2 = x.2 - y.2 := rfl

/-! ## q27cs-1: ペア環計算キット（choice-free・omega は線形化後のみ） -/

/-- ペア乗法の可換性。 -/
theorem q27cs_mul_comm (x y : q27csP) : q27csMul x y = q27csMul y x := by
  refine q27cs_pext ?_ ?_
  · show x.1 * y.1 - 3 * (x.2 * y.2) = y.1 * x.1 - 3 * (y.2 * x.2)
    rw [Int.mul_comm x.1 y.1, Int.mul_comm x.2 y.2]
  · show x.1 * y.2 + x.2 * y.1 = y.1 * x.2 + y.2 * x.1
    rw [Int.mul_comm x.1 y.2, Int.mul_comm x.2 y.1]
    omega

/-- ペア乗法の結合性（D=−3 の交叉項を明示線形化して omega）。 -/
theorem q27cs_mul_assoc (x y z : q27csP) :
    q27csMul (q27csMul x y) z = q27csMul x (q27csMul y z) := by
  refine q27cs_pext ?_ ?_
  · show (x.1 * y.1 - 3 * (x.2 * y.2)) * z.1 - 3 * ((x.1 * y.2 + x.2 * y.1) * z.2)
        = x.1 * (y.1 * z.1 - 3 * (y.2 * z.2)) - 3 * (x.2 * (y.1 * z.2 + y.2 * z.1))
    have e1 : (x.1 * y.1 - 3 * (x.2 * y.2)) * z.1
        = x.1 * (y.1 * z.1) - 3 * (x.2 * (y.2 * z.1)) := by
      rw [Int.sub_mul, Int.mul_assoc x.1 y.1 z.1, Int.mul_assoc 3 (x.2 * y.2) z.1,
        Int.mul_assoc x.2 y.2 z.1]
    have e2 : (x.1 * y.2 + x.2 * y.1) * z.2
        = x.1 * (y.2 * z.2) + x.2 * (y.1 * z.2) := by
      rw [Int.add_mul, Int.mul_assoc x.1 y.2 z.2, Int.mul_assoc x.2 y.1 z.2]
    have e3 : x.1 * (y.1 * z.1 - 3 * (y.2 * z.2))
        = x.1 * (y.1 * z.1) - 3 * (x.1 * (y.2 * z.2)) := by
      rw [Int.mul_sub, Int.mul_left_comm x.1 3 (y.2 * z.2)]
    have e4 : x.2 * (y.1 * z.2 + y.2 * z.1)
        = x.2 * (y.1 * z.2) + x.2 * (y.2 * z.1) := by
      rw [Int.mul_add]
    rw [e1, e2, e3, e4]
    omega
  · show (x.1 * y.1 - 3 * (x.2 * y.2)) * z.2 + (x.1 * y.2 + x.2 * y.1) * z.1
        = x.1 * (y.1 * z.2 + y.2 * z.1) + x.2 * (y.1 * z.1 - 3 * (y.2 * z.2))
    have e1 : (x.1 * y.1 - 3 * (x.2 * y.2)) * z.2
        = x.1 * (y.1 * z.2) - 3 * (x.2 * (y.2 * z.2)) := by
      rw [Int.sub_mul, Int.mul_assoc x.1 y.1 z.2, Int.mul_assoc 3 (x.2 * y.2) z.2,
        Int.mul_assoc x.2 y.2 z.2]
    have e2 : (x.1 * y.2 + x.2 * y.1) * z.1
        = x.1 * (y.2 * z.1) + x.2 * (y.1 * z.1) := by
      rw [Int.add_mul, Int.mul_assoc x.1 y.2 z.1, Int.mul_assoc x.2 y.1 z.1]
    have e3 : x.1 * (y.1 * z.2 + y.2 * z.1)
        = x.1 * (y.1 * z.2) + x.1 * (y.2 * z.1) := by
      rw [Int.mul_add]
    have e4 : x.2 * (y.1 * z.1 - 3 * (y.2 * z.2))
        = x.2 * (y.1 * z.1) - 3 * (x.2 * (y.2 * z.2)) := by
      rw [Int.mul_sub, Int.mul_left_comm x.2 3 (y.2 * z.2)]
    rw [e1, e2, e3, e4]
    omega

/-- 左交換。 -/
theorem q27cs_mul_left_comm (x y z : q27csP) :
    q27csMul x (q27csMul y z) = q27csMul y (q27csMul x z) := by
  rw [← q27cs_mul_assoc x y z, q27cs_mul_comm x y, q27cs_mul_assoc y x z]

/-- 左分配。 -/
theorem q27cs_mul_add (x y z : q27csP) :
    q27csMul x (q27csAdd y z) = q27csAdd (q27csMul x y) (q27csMul x z) := by
  refine q27cs_pext ?_ ?_
  · show x.1 * (y.1 + z.1) - 3 * (x.2 * (y.2 + z.2))
        = x.1 * y.1 - 3 * (x.2 * y.2) + (x.1 * z.1 - 3 * (x.2 * z.2))
    rw [Int.mul_add x.1 y.1 z.1, Int.mul_add x.2 y.2 z.2]
    omega
  · show x.1 * (y.2 + z.2) + x.2 * (y.1 + z.1)
        = x.1 * y.2 + x.2 * y.1 + (x.1 * z.2 + x.2 * z.1)
    rw [Int.mul_add x.1 y.2 z.2, Int.mul_add x.2 y.1 z.1]
    omega

/-- 右分配。 -/
theorem q27cs_add_mul (x y z : q27csP) :
    q27csMul (q27csAdd x y) z = q27csAdd (q27csMul x z) (q27csMul y z) := by
  rw [q27cs_mul_comm (q27csAdd x y) z, q27cs_mul_add z x y,
    q27cs_mul_comm z x, q27cs_mul_comm z y]

/-- 減法の右分配。 -/
theorem q27cs_sub_mul (x y z : q27csP) :
    q27csMul (q27csSub x y) z = q27csSub (q27csMul x z) (q27csMul y z) := by
  refine q27cs_pext ?_ ?_
  · show (x.1 - y.1) * z.1 - 3 * ((x.2 - y.2) * z.2)
        = x.1 * z.1 - 3 * (x.2 * z.2) - (y.1 * z.1 - 3 * (y.2 * z.2))
    rw [Int.sub_mul x.1 y.1 z.1, Int.sub_mul x.2 y.2 z.2]
    omega
  · show (x.1 - y.1) * z.2 + (x.2 - y.2) * z.1
        = x.1 * z.2 + x.2 * z.1 - (y.1 * z.2 + y.2 * z.1)
    rw [Int.sub_mul x.1 y.1 z.2, Int.sub_mul x.2 y.2 z.1]
    omega

/-- 減法の左分配。 -/
theorem q27cs_mul_sub (x y z : q27csP) :
    q27csMul x (q27csSub y z) = q27csSub (q27csMul x y) (q27csMul x z) := by
  rw [q27cs_mul_comm x (q27csSub y z), q27cs_sub_mul y z x,
    q27cs_mul_comm y x, q27cs_mul_comm z x]

/-- 再結合 1: (ab)(cd) = a(b(cd))。 -/
theorem q27cs_ras1 (a b c d : q27csP) :
    q27csMul (q27csMul a b) (q27csMul c d)
      = q27csMul a (q27csMul b (q27csMul c d)) :=
  q27cs_mul_assoc a b (q27csMul c d)

/-- 再結合 2: (ab)(cd) = c(a(bd))。 -/
theorem q27cs_ras2 (a b c d : q27csP) :
    q27csMul (q27csMul a b) (q27csMul c d)
      = q27csMul c (q27csMul a (q27csMul b d)) := by
  rw [q27cs_mul_assoc a b (q27csMul c d), q27cs_mul_left_comm b c d,
    q27cs_mul_left_comm a c (q27csMul b d)]

/-- 再結合 3: (ab)(cd) = a(c(bd))。 -/
theorem q27cs_ras3 (a b c d : q27csP) :
    q27csMul (q27csMul a b) (q27csMul c d)
      = q27csMul a (q27csMul c (q27csMul b d)) := by
  rw [q27cs_mul_assoc a b (q27csMul c d), q27cs_mul_left_comm b c d]

/-- g0 型分配: p(x + q(y+z)) = px + (p(qy) + p(qz))（W·b スロット 0 の展開）。 -/
theorem q27cs_mul_g0 (p q x y z : q27csP) :
    q27csMul p (q27csAdd x (q27csMul q (q27csAdd y z)))
      = q27csAdd (q27csMul p x)
          (q27csAdd (q27csMul p (q27csMul q y)) (q27csMul p (q27csMul q z))) := by
  rw [q27cs_mul_add q y z, q27cs_mul_add p x (q27csAdd (q27csMul q y) (q27csMul q z)),
    q27cs_mul_add p (q27csMul q y) (q27csMul q z)]

/-- g1/g2 型分配: p((x+y) + z) = (px + py) + pz（スロット 1/2 の展開）。 -/
theorem q27cs_mul_g12 (p x y z : q27csP) :
    q27csMul p (q27csAdd (q27csAdd x y) z)
      = q27csAdd (q27csAdd (q27csMul p x) (q27csMul p y)) (q27csMul p z) := by
  rw [q27cs_mul_add p (q27csAdd x y) z, q27cs_mul_add p x y]

/-- 3 項和の右分配: (x + (y+z))w = xw + (yw + zw)（Norm·b の展開）。 -/
theorem q27cs_add3_mul (x y z w : q27csP) :
    q27csMul (q27csAdd x (q27csAdd y z)) w
      = q27csAdd (q27csMul x w) (q27csAdd (q27csMul y w) (q27csMul z w)) := by
  rw [q27cs_add_mul x (q27csAdd y z) w, q27cs_add_mul y z w]

/-! ## q27cs-2: 可除性述語と閉包補題（q9cs toolbox 消費） -/

/-- ペア可除性: 3^t が両 Int 座標を割る。 -/
def q27csPD (t : Nat) (x : q27csP) : Prop :=
  ((3 ^ t : Nat) : Int) ∣ x.1 ∧ ((3 ^ t : Nat) : Int) ∣ x.2

/-- 混合（奇段）不変量: λ-自由座標は 3^{m+1}・λ-座標は 3^m。 -/
def q27csPM (m : Nat) (x : q27csP) : Prop :=
  ((3 ^ (m + 1) : Nat) : Int) ∣ x.1 ∧ ((3 ^ m : Nat) : Int) ∣ x.2

/-- PD の単調性。 -/
theorem q27cs_pd_of_le {s t : Nat} (h : s ≤ t) {x : q27csP} (hx : q27csPD t x) :
    q27csPD s x :=
  ⟨q9cs_dvd_of_le h hx.1, q9cs_dvd_of_le h hx.2⟩

/-- PD の加法閉包。 -/
theorem q27cs_pd_add {t : Nat} {x y : q27csP} (hx : q27csPD t x) (hy : q27csPD t y) :
    q27csPD t (q27csAdd x y) :=
  ⟨Int.dvd_add hx.1 hy.1, Int.dvd_add hx.2 hy.2⟩

/-- PD は左から任意ペアを掛けても保存。 -/
theorem q27cs_pd_mull {t : Nat} (x : q27csP) {y : q27csP} (hy : q27csPD t y) :
    q27csPD t (q27csMul x y) :=
  ⟨Int.dvd_sub (q9cs_dvd_mull x.1 hy.1) (q9cs_dvd_mull 3 (q9cs_dvd_mull x.2 hy.2)),
   Int.dvd_add (q9cs_dvd_mull x.1 hy.2) (q9cs_dvd_mull x.2 hy.1)⟩

/-- PD は右から任意ペアを掛けても保存。 -/
theorem q27cs_pd_mulr {t : Nat} {x : q27csP} (hx : q27csPD t x) (y : q27csP) :
    q27csPD t (q27csMul x y) :=
  ⟨Int.dvd_sub (q9cs_dvd_mulr hx.1 y.1) (q9cs_dvd_mull 3 (q9cs_dvd_mulr hx.2 y.2)),
   Int.dvd_add (q9cs_dvd_mulr hx.1 y.2) (q9cs_dvd_mulr hx.2 y.1)⟩

/-- PD の積は冪を加算（偶段 2 次尾項の 3-content）。 -/
theorem q27cs_pd_mul {s t : Nat} {x y : q27csP} (hx : q27csPD s x) (hy : q27csPD t y) :
    q27csPD (s + t) (q27csMul x y) :=
  ⟨Int.dvd_sub (q9cs_dvd_mul_pow hx.1 hy.1)
     (q9cs_dvd_mull 3 (q9cs_dvd_mul_pow hx.2 hy.2)),
   Int.dvd_add (q9cs_dvd_mul_pow hx.1 hy.2) (q9cs_dvd_mul_pow hx.2 hy.1)⟩

/-- **混合積（奇段の生命線）**: PM m x, PM m y ⟹ PD (m+1) (x·y)。
    λ-自由 = x₁y₁ − 3(x₂y₂)（第 1 項は 3^{m+1} 因子・第 2 項は明示 3 が 1 段深くする）、
    λ-側 = x₁y₂ + x₂y₁（各項が 3^{m+1} と 3^m·3^{m+1} ≥ 3^{m+1}）。 -/
theorem q27cs_pm_mul {m : Nat} {x y : q27csP} (hx : q27csPM m x) (hy : q27csPM m y) :
    q27csPD (m + 1) (q27csMul x y) :=
  ⟨Int.dvd_sub (q9cs_dvd_mulr hx.1 y.1)
     (q9cs_dvd_three_shift (q9cs_dvd_mulr hx.2 y.2)),
   Int.dvd_add (q9cs_dvd_mulr hx.1 y.2) (q9cs_dvd_mull x.2 hy.1)⟩

/-- PD の加法キャンセル: PD t (x+y), PD t y ⟹ PD t x。 -/
theorem q27cs_pd_cancel {t : Nat} {x y : q27csP}
    (h : q27csPD t (q27csAdd x y)) (hy : q27csPD t y) : q27csPD t x := by
  refine ⟨?_, ?_⟩
  · have hd : ((3 ^ t : Nat) : Int) ∣ x.1 + y.1 - y.1 := Int.dvd_sub h.1 hy.1
    have he : x.1 + y.1 - y.1 = x.1 := by omega
    rwa [he] at hd
  · have hd : ((3 ^ t : Nat) : Int) ∣ x.2 + y.2 - y.2 := Int.dvd_sub h.2 hy.2
    have he : x.2 + y.2 - y.2 = x.2 := by omega
    rwa [he] at hd

/-- 3^0 = 1 は全ペアを割る。 -/
theorem q27cs_pd_zero (x : q27csP) : q27csPD 0 x :=
  ⟨q9cs_pow_zero_dvd x.1, q9cs_pow_zero_dvd x.2⟩

/-! ## q27cs-3: O_{M₉} 影（3 ペア組）のねじれ畳み込みと E′ 影 -/

/-- O_{M₉} の Int 影の担体: 3 つの L₂ 影ペア（1, Y, Y² 係数）= 6 Int 座標。 -/
def q27csT : Type := q27csP × q27csP × q27csP

/-- 3 ペア組の加法。 -/
def q27csTAdd (x y : q27csT) : q27csT :=
  (q27csAdd x.1 y.1, q27csAdd x.2.1 y.2.1, q27csAdd x.2.2 y.2.2)

/-- **ねじれ畳み込みの Int 影**（q3kMul（Q3KummerCubic:99–105）のスロット毎写像・
    e = ζ₃ の L₂ 影）: スロット 0 = x₀y₀ + e(x₁y₂ + x₂y₁)、
    スロット 1 = x₀y₁ + x₁y₀ + e(x₂y₂)、スロット 2 = x₀y₂ + x₁y₁ + x₂y₀。 -/
def q27csTMul (e : q27csP) (x y : q27csT) : q27csT :=
  (q27csAdd (q27csMul x.1 y.1)
     (q27csMul e (q27csAdd (q27csMul x.2.1 y.2.2) (q27csMul x.2.2 y.2.1))),
   q27csAdd (q27csAdd (q27csMul x.1 y.2.1) (q27csMul x.2.1 y.1))
     (q27csMul e (q27csMul x.2.2 y.2.2)),
   q27csAdd (q27csAdd (q27csMul x.1 y.2.2) (q27csMul x.2.1 y.2.1))
     (q27csMul x.2.2 y.1))

/-- 3 ペア組の可除性（6 Int 座標全て）。 -/
def q27csTD (t : Nat) (x : q27csT) : Prop :=
  q27csPD t x.1 ∧ q27csPD t x.2.1 ∧ q27csPD t x.2.2

/-- 3 ペア組の混合（奇段）不変量。 -/
def q27csTM (m : Nat) (x : q27csT) : Prop :=
  q27csPM m x.1 ∧ q27csPM m x.2.1 ∧ q27csPM m x.2.2

/-- λ-自由 6 座標の可除性（偶段の結論）。 -/
def q27csTDF (t : Nat) (x : q27csT) : Prop :=
  ((3 ^ t : Nat) : Int) ∣ x.1.1 ∧ ((3 ^ t : Nat) : Int) ∣ x.2.1.1
    ∧ ((3 ^ t : Nat) : Int) ∣ x.2.2.1

/-- λ-側 6 座標の可除性（奇段の結論）。 -/
def q27csTDS (t : Nat) (x : q27csT) : Prop :=
  ((3 ^ t : Nat) : Int) ∣ x.1.2 ∧ ((3 ^ t : Nat) : Int) ∣ x.2.1.2
    ∧ ((3 ^ t : Nat) : Int) ∣ x.2.2.2

/-- TD の単調性。 -/
theorem q27cs_td_of_le {s t : Nat} (h : s ≤ t) {x : q27csT} (hx : q27csTD t x) :
    q27csTD s x :=
  ⟨q27cs_pd_of_le h hx.1, q27cs_pd_of_le h hx.2.1, q27cs_pd_of_le h hx.2.2⟩

/-- TD の加法閉包。 -/
theorem q27cs_td_add {t : Nat} {x y : q27csT} (hx : q27csTD t x) (hy : q27csTD t y) :
    q27csTD t (q27csTAdd x y) :=
  ⟨q27cs_pd_add hx.1 hy.1, q27cs_pd_add hx.2.1 hy.2.1, q27cs_pd_add hx.2.2 hy.2.2⟩

/-- TD は左から任意 3 ペア組を掛けても保存（ねじれ畳み込みの各スロットが
    y 座標の PD 線形結合であることの実証）。 -/
theorem q27cs_td_mull {t : Nat} (e : q27csP) (x : q27csT) {y : q27csT}
    (hy : q27csTD t y) : q27csTD t (q27csTMul e x y) :=
  ⟨q27cs_pd_add (q27cs_pd_mull x.1 hy.1)
     (q27cs_pd_mull e (q27cs_pd_add (q27cs_pd_mull x.2.1 hy.2.2)
        (q27cs_pd_mull x.2.2 hy.2.1))),
   q27cs_pd_add (q27cs_pd_add (q27cs_pd_mull x.1 hy.2.1) (q27cs_pd_mull x.2.1 hy.1))
     (q27cs_pd_mull e (q27cs_pd_mull x.2.2 hy.2.2)),
   q27cs_pd_add (q27cs_pd_add (q27cs_pd_mull x.1 hy.2.2) (q27cs_pd_mull x.2.1 hy.2.1))
     (q27cs_pd_mull x.2.2 hy.1)⟩

/-- TD は右から任意 3 ペア組を掛けても保存。 -/
theorem q27cs_td_mulr {t : Nat} (e : q27csP) {x : q27csT} (hx : q27csTD t x)
    (y : q27csT) : q27csTD t (q27csTMul e x y) :=
  ⟨q27cs_pd_add (q27cs_pd_mulr hx.1 y.1)
     (q27cs_pd_mull e (q27cs_pd_add (q27cs_pd_mulr hx.2.1 y.2.2)
        (q27cs_pd_mulr hx.2.2 y.2.1))),
   q27cs_pd_add (q27cs_pd_add (q27cs_pd_mulr hx.1 y.2.1) (q27cs_pd_mulr hx.2.1 y.1))
     (q27cs_pd_mull e (q27cs_pd_mulr hx.2.2 y.2.2)),
   q27cs_pd_add (q27cs_pd_add (q27cs_pd_mulr hx.1 y.2.2) (q27cs_pd_mulr hx.2.1 y.2.1))
     (q27cs_pd_mulr hx.2.2 y.1)⟩

/-- TD の積は冪を加算（偶段 2 次尾項）。 -/
theorem q27cs_td_mul {s t : Nat} (e : q27csP) {x y : q27csT}
    (hx : q27csTD s x) (hy : q27csTD t y) : q27csTD (s + t) (q27csTMul e x y) :=
  ⟨q27cs_pd_add (q27cs_pd_mul hx.1 hy.1)
     (q27cs_pd_mull e (q27cs_pd_add (q27cs_pd_mul hx.2.1 hy.2.2)
        (q27cs_pd_mul hx.2.2 hy.2.1))),
   q27cs_pd_add (q27cs_pd_add (q27cs_pd_mul hx.1 hy.2.1) (q27cs_pd_mul hx.2.1 hy.1))
     (q27cs_pd_mull e (q27cs_pd_mul hx.2.2 hy.2.2)),
   q27cs_pd_add (q27cs_pd_add (q27cs_pd_mul hx.1 hy.2.2) (q27cs_pd_mul hx.2.1 hy.2.1))
     (q27cs_pd_mul hx.2.2 hy.1)⟩

/-- **混合積（奇段の 2 次尾項）**: TM m x, TM m y ⟹ TD (m+1) (x·y)。全 m ≥ 0 で有効。 -/
theorem q27cs_tm_mul {m : Nat} (e : q27csP) {x y : q27csT}
    (hx : q27csTM m x) (hy : q27csTM m y) : q27csTD (m + 1) (q27csTMul e x y) :=
  ⟨q27cs_pd_add (q27cs_pm_mul hx.1 hy.1)
     (q27cs_pd_mull e (q27cs_pd_add (q27cs_pm_mul hx.2.1 hy.2.2)
        (q27cs_pm_mul hx.2.2 hy.2.1))),
   q27cs_pd_add (q27cs_pd_add (q27cs_pm_mul hx.1 hy.2.1) (q27cs_pm_mul hx.2.1 hy.1))
     (q27cs_pd_mull e (q27cs_pm_mul hx.2.2 hy.2.2)),
   q27cs_pd_add (q27cs_pd_add (q27cs_pm_mul hx.1 hy.2.2) (q27cs_pm_mul hx.2.1 hy.2.1))
     (q27cs_pm_mul hx.2.2 hy.1)⟩

/-- TD の加法キャンセル。 -/
theorem q27cs_td_cancel {t : Nat} {x y : q27csT}
    (h : q27csTD t (q27csTAdd x y)) (hy : q27csTD t y) : q27csTD t x :=
  ⟨q27cs_pd_cancel h.1 hy.1, q27cs_pd_cancel h.2.1 hy.2.1,
   q27cs_pd_cancel h.2.2 hy.2.2⟩

/-- 3^0 は全 3 ペア組を割る。 -/
theorem q27cs_td_zero (x : q27csT) : q27csTD 0 x :=
  ⟨q27cs_pd_zero x.1, q27cs_pd_zero x.2.1, q27cs_pd_zero x.2.2⟩

/-- **E1′ 影** = W·b + ζ₉(a·c²) + ζ₉(b²·c)（q9cs の E1′ = a²b + d(ac²) + d(b²c) の
    M₉ 基底版・W = a² の影・z = ζ₉ の 6 座標影・e = ζ₃ の 2 座標影）。 -/
def q27csE1 (e : q27csP) (z W a b c : q27csT) : q27csT :=
  q27csTAdd (q27csTMul e W b)
    (q27csTAdd (q27csTMul e z (q27csTMul e a (q27csTMul e c c)))
       (q27csTMul e z (q27csTMul e (q27csTMul e b b) c)))

/-- **E2′ 影** = W·c + a·b² + ζ₉(b·c²)。 -/
def q27csE2 (e : q27csP) (z W a b c : q27csT) : q27csT :=
  q27csTAdd (q27csTMul e W c)
    (q27csTAdd (q27csTMul e a (q27csTMul e b b))
       (q27csTMul e z (q27csTMul e b (q27csTMul e c c))))

/-- **6 座標 q3k ノルムの Int 影**（q3kNormBase（Q3KummerCubic:682）の形
    N = w₀³ + ζ₃w₁³ + ζ₃²w₂³ − 3ζ₃w₀w₁w₂ の L₂ 影・−3(…) は 3 重和で表す）。 -/
def q27csNorm (e w0 w1 w2 : q27csP) : q27csP :=
  q27csSub
    (q27csAdd (q27csMul w0 (q27csMul w0 w0))
       (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
          (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2))))))
    (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
       (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
          (q27csMul e (q27csMul w0 (q27csMul w1 w2)))))

/-! ## q27cs-4: 随伴 Cramer 恒等式（★ level-27 降下の新規の核）

ねじれ畳み込み行列 M(W)（W·b の 3×3 L₂-影行列・ねじれ e）の随伴 u =
(w₀²−e w₁w₂, e w₂²−w₀w₁, w₁²−w₀w₂) について u·(W·b) = N(W)·b。3 スロット
各 18 単項式（7 対相殺＋4 生存・−3e w₀w₁w₂ は 3 重和）を、ペア環キットの明示 rw で
完全右結合正規形に落とし、射影展開＋omega（一致アトムの線形相殺）で閉じる。
level-9 の「主要係数 1 個の peel」が 6 座標基底で「随伴 3×3 の対角化」に昇格する
——これが scope の言う「降下の連立構造が変わる」の Lean 実体。 -/

/-- **Cramer 行 0**: u₀·(W·b)₀ + (e·u₁)·(W·b)₂ + (e·u₂)·(W·b)₁ = N(W)·b₀。 -/
theorem q27cs_cramer0 (e w0 w1 w2 b0 b1 b2 : q27csP) :
    q27csAdd
      (q27csMul (q27csSub (q27csMul w0 w0) (q27csMul e (q27csMul w1 w2)))
        (q27csAdd (q27csMul w0 b0)
          (q27csMul e (q27csAdd (q27csMul w1 b2) (q27csMul w2 b1)))))
      (q27csAdd
        (q27csMul (q27csSub (q27csMul e (q27csMul e (q27csMul w2 w2)))
            (q27csMul e (q27csMul w0 w1)))
          (q27csAdd (q27csAdd (q27csMul w0 b2) (q27csMul w1 b1)) (q27csMul w2 b0)))
        (q27csMul (q27csSub (q27csMul e (q27csMul w1 w1)) (q27csMul e (q27csMul w0 w2)))
          (q27csAdd (q27csAdd (q27csMul w0 b1) (q27csMul w1 b0))
            (q27csMul e (q27csMul w2 b2)))))
    = q27csMul (q27csNorm e w0 w1 w2) b0 := by
  -- ブロック A: u₀·g₀ の平坦化（6 単項式）
  have hA : q27csMul (q27csSub (q27csMul w0 w0) (q27csMul e (q27csMul w1 w2)))
        (q27csAdd (q27csMul w0 b0)
          (q27csMul e (q27csAdd (q27csMul w1 b2) (q27csMul w2 b1))))
      = q27csSub
          (q27csAdd (q27csMul w0 (q27csMul w0 (q27csMul w0 b0)))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w0 (q27csMul w1 b2))))
              (q27csMul e (q27csMul w0 (q27csMul w0 (q27csMul w2 b1))))))
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b0))))
            (q27csAdd (q27csMul e (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w2 b2)))))
              (q27csMul e (q27csMul e (q27csMul w1 (q27csMul w2 (q27csMul w2 b1))))))) := by
    rw [q27cs_sub_mul (q27csMul w0 w0) (q27csMul e (q27csMul w1 w2))
          (q27csAdd (q27csMul w0 b0)
            (q27csMul e (q27csAdd (q27csMul w1 b2) (q27csMul w2 b1)))),
        q27cs_mul_g0 (q27csMul w0 w0) e (q27csMul w0 b0) (q27csMul w1 b2) (q27csMul w2 b1),
        q27cs_mul_g0 (q27csMul e (q27csMul w1 w2)) e (q27csMul w0 b0)
          (q27csMul w1 b2) (q27csMul w2 b1),
        q27cs_ras1 w0 w0 w0 b0,
        q27cs_ras2 w0 w0 e (q27csMul w1 b2),
        q27cs_ras2 w0 w0 e (q27csMul w2 b1),
        q27cs_ras3 e (q27csMul w1 w2) w0 b0, q27cs_mul_assoc w1 w2 b0,
        q27cs_ras3 e (q27csMul w1 w2) e (q27csMul w1 b2), q27cs_ras3 w1 w2 w1 b2,
        q27cs_ras3 e (q27csMul w1 w2) e (q27csMul w2 b1), q27cs_ras1 w1 w2 w2 b1]
  -- ブロック B: (e·u₁)·g₂ の平坦化
  have hB : q27csMul (q27csSub (q27csMul e (q27csMul e (q27csMul w2 w2)))
          (q27csMul e (q27csMul w0 w1)))
        (q27csAdd (q27csAdd (q27csMul w0 b2) (q27csMul w1 b1)) (q27csMul w2 b0))
      = q27csSub
          (q27csAdd
            (q27csAdd (q27csMul e (q27csMul e (q27csMul w0 (q27csMul w2 (q27csMul w2 b2)))))
              (q27csMul e (q27csMul e (q27csMul w1 (q27csMul w2 (q27csMul w2 b1))))))
            (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 (q27csMul w2 b0))))))
          (q27csAdd
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w0 (q27csMul w1 b2))))
              (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w1 b1)))))
            (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b0))))) := by
    rw [q27cs_sub_mul (q27csMul e (q27csMul e (q27csMul w2 w2)))
          (q27csMul e (q27csMul w0 w1))
          (q27csAdd (q27csAdd (q27csMul w0 b2) (q27csMul w1 b1)) (q27csMul w2 b0)),
        q27cs_mul_g12 (q27csMul e (q27csMul e (q27csMul w2 w2)))
          (q27csMul w0 b2) (q27csMul w1 b1) (q27csMul w2 b0),
        q27cs_mul_g12 (q27csMul e (q27csMul w0 w1))
          (q27csMul w0 b2) (q27csMul w1 b1) (q27csMul w2 b0),
        q27cs_ras1 e (q27csMul e (q27csMul w2 w2)) w0 b2,
        q27cs_ras3 e (q27csMul w2 w2) w0 b2, q27cs_mul_assoc w2 w2 b2,
        q27cs_ras1 e (q27csMul e (q27csMul w2 w2)) w1 b1,
        q27cs_ras3 e (q27csMul w2 w2) w1 b1, q27cs_mul_assoc w2 w2 b1,
        q27cs_ras1 e (q27csMul e (q27csMul w2 w2)) w2 b0,
        q27cs_ras3 e (q27csMul w2 w2) w2 b0, q27cs_mul_assoc w2 w2 b0,
        q27cs_ras3 e (q27csMul w0 w1) w0 b2, q27cs_mul_assoc w0 w1 b2,
        q27cs_ras1 e (q27csMul w0 w1) w1 b1, q27cs_ras1 w0 w1 w1 b1,
        q27cs_ras1 e (q27csMul w0 w1) w2 b0, q27cs_ras1 w0 w1 w2 b0]
  -- ブロック C: (e·u₂)·g₁ の平坦化
  have hC : q27csMul (q27csSub (q27csMul e (q27csMul w1 w1)) (q27csMul e (q27csMul w0 w2)))
        (q27csAdd (q27csAdd (q27csMul w0 b1) (q27csMul w1 b0))
          (q27csMul e (q27csMul w2 b2)))
      = q27csSub
          (q27csAdd
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w1 b1))))
              (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w1 b0)))))
            (q27csMul e (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w2 b2))))))
          (q27csAdd
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w0 (q27csMul w2 b1))))
              (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b0)))))
            (q27csMul e (q27csMul e (q27csMul w0 (q27csMul w2 (q27csMul w2 b2)))))) := by
    rw [q27cs_sub_mul (q27csMul e (q27csMul w1 w1)) (q27csMul e (q27csMul w0 w2))
          (q27csAdd (q27csAdd (q27csMul w0 b1) (q27csMul w1 b0))
            (q27csMul e (q27csMul w2 b2))),
        q27cs_mul_g12 (q27csMul e (q27csMul w1 w1))
          (q27csMul w0 b1) (q27csMul w1 b0) (q27csMul e (q27csMul w2 b2)),
        q27cs_mul_g12 (q27csMul e (q27csMul w0 w2))
          (q27csMul w0 b1) (q27csMul w1 b0) (q27csMul e (q27csMul w2 b2)),
        q27cs_ras3 e (q27csMul w1 w1) w0 b1, q27cs_mul_assoc w1 w1 b1,
        q27cs_ras1 e (q27csMul w1 w1) w1 b0, q27cs_ras1 w1 w1 w1 b0,
        q27cs_ras3 e (q27csMul w1 w1) e (q27csMul w2 b2), q27cs_ras1 w1 w1 w2 b2,
        q27cs_ras3 e (q27csMul w0 w2) w0 b1, q27cs_mul_assoc w0 w2 b1,
        q27cs_ras1 e (q27csMul w0 w2) w1 b0, q27cs_ras3 w0 w2 w1 b0,
        q27cs_ras3 e (q27csMul w0 w2) e (q27csMul w2 b2), q27cs_ras3 w0 w2 w2 b2]
  -- RHS: N(W)·b₀ の平坦化（4 生存単項式・三重和）
  have hD : q27csMul (q27csMul e (q27csMul w0 (q27csMul w1 w2))) b0
      = q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b0))) := by
    rw [q27cs_mul_assoc e (q27csMul w0 (q27csMul w1 w2)) b0,
        q27cs_mul_assoc w0 (q27csMul w1 w2) b0,
        q27cs_mul_assoc w1 w2 b0]
  have hR : q27csMul (q27csNorm e w0 w1 w2) b0
      = q27csSub
          (q27csAdd (q27csMul w0 (q27csMul w0 (q27csMul w0 b0)))
            (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w1 b0))))
              (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 (q27csMul w2 b0)))))))
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b0))))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b0))))
              (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b0)))))) := by
    show q27csMul
        (q27csSub
          (q27csAdd (q27csMul w0 (q27csMul w0 w0))
            (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
              (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2))))))
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
              (q27csMul e (q27csMul w0 (q27csMul w1 w2)))))) b0
      = _
    rw [q27cs_sub_mul
          (q27csAdd (q27csMul w0 (q27csMul w0 w0))
            (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
              (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2))))))
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
              (q27csMul e (q27csMul w0 (q27csMul w1 w2))))) b0,
        q27cs_add3_mul (q27csMul w0 (q27csMul w0 w0))
          (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
          (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2)))) b0,
        q27cs_add3_mul (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
          (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
          (q27csMul e (q27csMul w0 (q27csMul w1 w2))) b0,
        q27cs_mul_assoc w0 (q27csMul w0 w0) b0, q27cs_mul_assoc w0 w0 b0,
        q27cs_mul_assoc e (q27csMul w1 (q27csMul w1 w1)) b0,
        q27cs_mul_assoc w1 (q27csMul w1 w1) b0, q27cs_mul_assoc w1 w1 b0,
        q27cs_mul_assoc e (q27csMul e (q27csMul w2 (q27csMul w2 w2))) b0,
        q27cs_mul_assoc e (q27csMul w2 (q27csMul w2 w2)) b0,
        q27cs_mul_assoc w2 (q27csMul w2 w2) b0, q27cs_mul_assoc w2 w2 b0,
        hD]
  rw [hA, hB, hC, hR]
  refine q27cs_pext ?_ ?_
  · repeat (first | rw [q27cs_add_fst] | rw [q27cs_sub_fst])
    omega
  · repeat (first | rw [q27cs_add_snd] | rw [q27cs_sub_snd])
    omega

/-- **Cramer 行 1**: u₀·(W·b)₁ + u₁·(W·b)₀ + (e·u₂)·(W·b)₂ = N(W)·b₁。 -/
theorem q27cs_cramer1 (e w0 w1 w2 b0 b1 b2 : q27csP) :
    q27csAdd
      (q27csMul (q27csSub (q27csMul w0 w0) (q27csMul e (q27csMul w1 w2)))
        (q27csAdd (q27csAdd (q27csMul w0 b1) (q27csMul w1 b0))
          (q27csMul e (q27csMul w2 b2))))
      (q27csAdd
        (q27csMul (q27csSub (q27csMul e (q27csMul w2 w2)) (q27csMul w0 w1))
          (q27csAdd (q27csMul w0 b0)
            (q27csMul e (q27csAdd (q27csMul w1 b2) (q27csMul w2 b1)))))
        (q27csMul (q27csSub (q27csMul e (q27csMul w1 w1)) (q27csMul e (q27csMul w0 w2)))
          (q27csAdd (q27csAdd (q27csMul w0 b2) (q27csMul w1 b1)) (q27csMul w2 b0))))
    = q27csMul (q27csNorm e w0 w1 w2) b1 := by
  -- ブロック A: u₀·g₁
  have hA : q27csMul (q27csSub (q27csMul w0 w0) (q27csMul e (q27csMul w1 w2)))
        (q27csAdd (q27csAdd (q27csMul w0 b1) (q27csMul w1 b0))
          (q27csMul e (q27csMul w2 b2)))
      = q27csSub
          (q27csAdd
            (q27csAdd (q27csMul w0 (q27csMul w0 (q27csMul w0 b1)))
              (q27csMul w0 (q27csMul w0 (q27csMul w1 b0))))
            (q27csMul e (q27csMul w0 (q27csMul w0 (q27csMul w2 b2)))))
          (q27csAdd
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b1))))
              (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w2 b0)))))
            (q27csMul e (q27csMul e (q27csMul w1 (q27csMul w2 (q27csMul w2 b2)))))) := by
    rw [q27cs_sub_mul (q27csMul w0 w0) (q27csMul e (q27csMul w1 w2))
          (q27csAdd (q27csAdd (q27csMul w0 b1) (q27csMul w1 b0))
            (q27csMul e (q27csMul w2 b2))),
        q27cs_mul_g12 (q27csMul w0 w0) (q27csMul w0 b1) (q27csMul w1 b0)
          (q27csMul e (q27csMul w2 b2)),
        q27cs_mul_g12 (q27csMul e (q27csMul w1 w2)) (q27csMul w0 b1) (q27csMul w1 b0)
          (q27csMul e (q27csMul w2 b2)),
        q27cs_ras1 w0 w0 w0 b1,
        q27cs_ras1 w0 w0 w1 b0,
        q27cs_ras2 w0 w0 e (q27csMul w2 b2),
        q27cs_ras3 e (q27csMul w1 w2) w0 b1, q27cs_mul_assoc w1 w2 b1,
        q27cs_ras1 e (q27csMul w1 w2) w1 b0, q27cs_ras3 w1 w2 w1 b0,
        q27cs_ras3 e (q27csMul w1 w2) e (q27csMul w2 b2), q27cs_ras1 w1 w2 w2 b2]
  -- ブロック B: u₁·g₀
  have hB : q27csMul (q27csSub (q27csMul e (q27csMul w2 w2)) (q27csMul w0 w1))
        (q27csAdd (q27csMul w0 b0)
          (q27csMul e (q27csAdd (q27csMul w1 b2) (q27csMul w2 b1))))
      = q27csSub
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w2 (q27csMul w2 b0))))
            (q27csAdd (q27csMul e (q27csMul e (q27csMul w1 (q27csMul w2 (q27csMul w2 b2)))))
              (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 (q27csMul w2 b1)))))))
          (q27csAdd (q27csMul w0 (q27csMul w0 (q27csMul w1 b0)))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w1 b2))))
              (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b1)))))) := by
    rw [q27cs_sub_mul (q27csMul e (q27csMul w2 w2)) (q27csMul w0 w1)
          (q27csAdd (q27csMul w0 b0)
            (q27csMul e (q27csAdd (q27csMul w1 b2) (q27csMul w2 b1)))),
        q27cs_mul_g0 (q27csMul e (q27csMul w2 w2)) e (q27csMul w0 b0)
          (q27csMul w1 b2) (q27csMul w2 b1),
        q27cs_mul_g0 (q27csMul w0 w1) e (q27csMul w0 b0)
          (q27csMul w1 b2) (q27csMul w2 b1),
        q27cs_ras3 e (q27csMul w2 w2) w0 b0, q27cs_mul_assoc w2 w2 b0,
        q27cs_ras3 e (q27csMul w2 w2) e (q27csMul w1 b2), q27cs_ras2 w2 w2 w1 b2,
        q27cs_ras3 e (q27csMul w2 w2) e (q27csMul w2 b1), q27cs_ras1 w2 w2 w2 b1,
        q27cs_ras2 w0 w1 w0 b0,
        q27cs_ras2 w0 w1 e (q27csMul w1 b2),
        q27cs_ras2 w0 w1 e (q27csMul w2 b1)]
  -- ブロック C: (e·u₂)·g₂
  have hC : q27csMul (q27csSub (q27csMul e (q27csMul w1 w1)) (q27csMul e (q27csMul w0 w2)))
        (q27csAdd (q27csAdd (q27csMul w0 b2) (q27csMul w1 b1)) (q27csMul w2 b0))
      = q27csSub
          (q27csAdd
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w1 b2))))
              (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w1 b1)))))
            (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w2 b0)))))
          (q27csAdd
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w0 (q27csMul w2 b2))))
              (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b1)))))
            (q27csMul e (q27csMul w0 (q27csMul w2 (q27csMul w2 b0))))) := by
    rw [q27cs_sub_mul (q27csMul e (q27csMul w1 w1)) (q27csMul e (q27csMul w0 w2))
          (q27csAdd (q27csAdd (q27csMul w0 b2) (q27csMul w1 b1)) (q27csMul w2 b0)),
        q27cs_mul_g12 (q27csMul e (q27csMul w1 w1))
          (q27csMul w0 b2) (q27csMul w1 b1) (q27csMul w2 b0),
        q27cs_mul_g12 (q27csMul e (q27csMul w0 w2))
          (q27csMul w0 b2) (q27csMul w1 b1) (q27csMul w2 b0),
        q27cs_ras3 e (q27csMul w1 w1) w0 b2, q27cs_mul_assoc w1 w1 b2,
        q27cs_ras1 e (q27csMul w1 w1) w1 b1, q27cs_ras1 w1 w1 w1 b1,
        q27cs_ras1 e (q27csMul w1 w1) w2 b0, q27cs_ras1 w1 w1 w2 b0,
        q27cs_ras3 e (q27csMul w0 w2) w0 b2, q27cs_mul_assoc w0 w2 b2,
        q27cs_ras1 e (q27csMul w0 w2) w1 b1, q27cs_ras3 w0 w2 w1 b1,
        q27cs_ras1 e (q27csMul w0 w2) w2 b0, q27cs_ras1 w0 w2 w2 b0]
  -- RHS: N(W)·b₁
  have hD : q27csMul (q27csMul e (q27csMul w0 (q27csMul w1 w2))) b1
      = q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b1))) := by
    rw [q27cs_mul_assoc e (q27csMul w0 (q27csMul w1 w2)) b1,
        q27cs_mul_assoc w0 (q27csMul w1 w2) b1,
        q27cs_mul_assoc w1 w2 b1]
  have hR : q27csMul (q27csNorm e w0 w1 w2) b1
      = q27csSub
          (q27csAdd (q27csMul w0 (q27csMul w0 (q27csMul w0 b1)))
            (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w1 b1))))
              (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 (q27csMul w2 b1)))))))
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b1))))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b1))))
              (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b1)))))) := by
    show q27csMul
        (q27csSub
          (q27csAdd (q27csMul w0 (q27csMul w0 w0))
            (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
              (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2))))))
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
              (q27csMul e (q27csMul w0 (q27csMul w1 w2)))))) b1
      = _
    rw [q27cs_sub_mul
          (q27csAdd (q27csMul w0 (q27csMul w0 w0))
            (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
              (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2))))))
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
              (q27csMul e (q27csMul w0 (q27csMul w1 w2))))) b1,
        q27cs_add3_mul (q27csMul w0 (q27csMul w0 w0))
          (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
          (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2)))) b1,
        q27cs_add3_mul (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
          (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
          (q27csMul e (q27csMul w0 (q27csMul w1 w2))) b1,
        q27cs_mul_assoc w0 (q27csMul w0 w0) b1, q27cs_mul_assoc w0 w0 b1,
        q27cs_mul_assoc e (q27csMul w1 (q27csMul w1 w1)) b1,
        q27cs_mul_assoc w1 (q27csMul w1 w1) b1, q27cs_mul_assoc w1 w1 b1,
        q27cs_mul_assoc e (q27csMul e (q27csMul w2 (q27csMul w2 w2))) b1,
        q27cs_mul_assoc e (q27csMul w2 (q27csMul w2 w2)) b1,
        q27cs_mul_assoc w2 (q27csMul w2 w2) b1, q27cs_mul_assoc w2 w2 b1,
        hD]
  rw [hA, hB, hC, hR]
  refine q27cs_pext ?_ ?_
  · repeat (first | rw [q27cs_add_fst] | rw [q27cs_sub_fst])
    omega
  · repeat (first | rw [q27cs_add_snd] | rw [q27cs_sub_snd])
    omega

/-- **Cramer 行 2**: u₀·(W·b)₂ + u₁·(W·b)₁ + u₂·(W·b)₀ = N(W)·b₂。 -/
theorem q27cs_cramer2 (e w0 w1 w2 b0 b1 b2 : q27csP) :
    q27csAdd
      (q27csMul (q27csSub (q27csMul w0 w0) (q27csMul e (q27csMul w1 w2)))
        (q27csAdd (q27csAdd (q27csMul w0 b2) (q27csMul w1 b1)) (q27csMul w2 b0)))
      (q27csAdd
        (q27csMul (q27csSub (q27csMul e (q27csMul w2 w2)) (q27csMul w0 w1))
          (q27csAdd (q27csAdd (q27csMul w0 b1) (q27csMul w1 b0))
            (q27csMul e (q27csMul w2 b2))))
        (q27csMul (q27csSub (q27csMul w1 w1) (q27csMul w0 w2))
          (q27csAdd (q27csMul w0 b0)
            (q27csMul e (q27csAdd (q27csMul w1 b2) (q27csMul w2 b1))))))
    = q27csMul (q27csNorm e w0 w1 w2) b2 := by
  -- ブロック A: u₀·g₂
  have hA : q27csMul (q27csSub (q27csMul w0 w0) (q27csMul e (q27csMul w1 w2)))
        (q27csAdd (q27csAdd (q27csMul w0 b2) (q27csMul w1 b1)) (q27csMul w2 b0))
      = q27csSub
          (q27csAdd
            (q27csAdd (q27csMul w0 (q27csMul w0 (q27csMul w0 b2)))
              (q27csMul w0 (q27csMul w0 (q27csMul w1 b1))))
            (q27csMul w0 (q27csMul w0 (q27csMul w2 b0))))
          (q27csAdd
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b2))))
              (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w2 b1)))))
            (q27csMul e (q27csMul w1 (q27csMul w2 (q27csMul w2 b0))))) := by
    rw [q27cs_sub_mul (q27csMul w0 w0) (q27csMul e (q27csMul w1 w2))
          (q27csAdd (q27csAdd (q27csMul w0 b2) (q27csMul w1 b1)) (q27csMul w2 b0)),
        q27cs_mul_g12 (q27csMul w0 w0) (q27csMul w0 b2) (q27csMul w1 b1)
          (q27csMul w2 b0),
        q27cs_mul_g12 (q27csMul e (q27csMul w1 w2)) (q27csMul w0 b2) (q27csMul w1 b1)
          (q27csMul w2 b0),
        q27cs_ras1 w0 w0 w0 b2,
        q27cs_ras1 w0 w0 w1 b1,
        q27cs_ras1 w0 w0 w2 b0,
        q27cs_ras3 e (q27csMul w1 w2) w0 b2, q27cs_mul_assoc w1 w2 b2,
        q27cs_ras1 e (q27csMul w1 w2) w1 b1, q27cs_ras3 w1 w2 w1 b1,
        q27cs_ras1 e (q27csMul w1 w2) w2 b0, q27cs_ras1 w1 w2 w2 b0]
  -- ブロック B: u₁·g₁
  have hB : q27csMul (q27csSub (q27csMul e (q27csMul w2 w2)) (q27csMul w0 w1))
        (q27csAdd (q27csAdd (q27csMul w0 b1) (q27csMul w1 b0))
          (q27csMul e (q27csMul w2 b2)))
      = q27csSub
          (q27csAdd
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w2 (q27csMul w2 b1))))
              (q27csMul e (q27csMul w1 (q27csMul w2 (q27csMul w2 b0)))))
            (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 (q27csMul w2 b2))))))
          (q27csAdd
            (q27csAdd (q27csMul w0 (q27csMul w0 (q27csMul w1 b1)))
              (q27csMul w0 (q27csMul w1 (q27csMul w1 b0))))
            (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b2))))) := by
    rw [q27cs_sub_mul (q27csMul e (q27csMul w2 w2)) (q27csMul w0 w1)
          (q27csAdd (q27csAdd (q27csMul w0 b1) (q27csMul w1 b0))
            (q27csMul e (q27csMul w2 b2))),
        q27cs_mul_g12 (q27csMul e (q27csMul w2 w2)) (q27csMul w0 b1) (q27csMul w1 b0)
          (q27csMul e (q27csMul w2 b2)),
        q27cs_mul_g12 (q27csMul w0 w1) (q27csMul w0 b1) (q27csMul w1 b0)
          (q27csMul e (q27csMul w2 b2)),
        q27cs_ras3 e (q27csMul w2 w2) w0 b1, q27cs_mul_assoc w2 w2 b1,
        q27cs_ras3 e (q27csMul w2 w2) w1 b0, q27cs_mul_assoc w2 w2 b0,
        q27cs_ras3 e (q27csMul w2 w2) e (q27csMul w2 b2), q27cs_ras1 w2 w2 w2 b2,
        q27cs_ras2 w0 w1 w0 b1,
        q27cs_ras1 w0 w1 w1 b0,
        q27cs_ras2 w0 w1 e (q27csMul w2 b2)]
  -- ブロック C: u₂·g₀
  have hC : q27csMul (q27csSub (q27csMul w1 w1) (q27csMul w0 w2))
        (q27csAdd (q27csMul w0 b0)
          (q27csMul e (q27csAdd (q27csMul w1 b2) (q27csMul w2 b1))))
      = q27csSub
          (q27csAdd (q27csMul w0 (q27csMul w1 (q27csMul w1 b0)))
            (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w1 b2))))
              (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w2 b1))))))
          (q27csAdd (q27csMul w0 (q27csMul w0 (q27csMul w2 b0)))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b2))))
              (q27csMul e (q27csMul w0 (q27csMul w2 (q27csMul w2 b1)))))) := by
    rw [q27cs_sub_mul (q27csMul w1 w1) (q27csMul w0 w2)
          (q27csAdd (q27csMul w0 b0)
            (q27csMul e (q27csAdd (q27csMul w1 b2) (q27csMul w2 b1)))),
        q27cs_mul_g0 (q27csMul w1 w1) e (q27csMul w0 b0)
          (q27csMul w1 b2) (q27csMul w2 b1),
        q27cs_mul_g0 (q27csMul w0 w2) e (q27csMul w0 b0)
          (q27csMul w1 b2) (q27csMul w2 b1),
        q27cs_ras2 w1 w1 w0 b0,
        q27cs_ras2 w1 w1 e (q27csMul w1 b2),
        q27cs_ras2 w1 w1 e (q27csMul w2 b1),
        q27cs_ras2 w0 w2 w0 b0,
        q27cs_ras2 w0 w2 e (q27csMul w1 b2), q27cs_mul_left_comm w2 w1 b2,
        q27cs_ras2 w0 w2 e (q27csMul w2 b1)]
  -- RHS: N(W)·b₂
  have hD : q27csMul (q27csMul e (q27csMul w0 (q27csMul w1 w2))) b2
      = q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b2))) := by
    rw [q27cs_mul_assoc e (q27csMul w0 (q27csMul w1 w2)) b2,
        q27cs_mul_assoc w0 (q27csMul w1 w2) b2,
        q27cs_mul_assoc w1 w2 b2]
  have hR : q27csMul (q27csNorm e w0 w1 w2) b2
      = q27csSub
          (q27csAdd (q27csMul w0 (q27csMul w0 (q27csMul w0 b2)))
            (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 (q27csMul w1 b2))))
              (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 (q27csMul w2 b2)))))))
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b2))))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b2))))
              (q27csMul e (q27csMul w0 (q27csMul w1 (q27csMul w2 b2)))))) := by
    show q27csMul
        (q27csSub
          (q27csAdd (q27csMul w0 (q27csMul w0 w0))
            (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
              (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2))))))
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
              (q27csMul e (q27csMul w0 (q27csMul w1 w2)))))) b2
      = _
    rw [q27cs_sub_mul
          (q27csAdd (q27csMul w0 (q27csMul w0 w0))
            (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
              (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2))))))
          (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
            (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
              (q27csMul e (q27csMul w0 (q27csMul w1 w2))))) b2,
        q27cs_add3_mul (q27csMul w0 (q27csMul w0 w0))
          (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
          (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2)))) b2,
        q27cs_add3_mul (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
          (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
          (q27csMul e (q27csMul w0 (q27csMul w1 w2))) b2,
        q27cs_mul_assoc w0 (q27csMul w0 w0) b2, q27cs_mul_assoc w0 w0 b2,
        q27cs_mul_assoc e (q27csMul w1 (q27csMul w1 w1)) b2,
        q27cs_mul_assoc w1 (q27csMul w1 w1) b2, q27cs_mul_assoc w1 w1 b2,
        q27cs_mul_assoc e (q27csMul e (q27csMul w2 (q27csMul w2 w2))) b2,
        q27cs_mul_assoc e (q27csMul w2 (q27csMul w2 w2)) b2,
        q27cs_mul_assoc w2 (q27csMul w2 w2) b2, q27cs_mul_assoc w2 w2 b2,
        hD]
  rw [hA, hB, hC, hR]
  refine q27cs_pext ?_ ?_
  · repeat (first | rw [q27cs_add_fst] | rw [q27cs_sub_fst])
    omega
  · repeat (first | rw [q27cs_add_snd] | rw [q27cs_sub_snd])
    omega

/-! ## q27cs-5: 単数 peel（★ q3cu_ppow_dvd 消費・2×2 L₂ peel → 6 座標一括 peel） -/

/-- **単数正則の楔（＋版）**: 3 ∤ n₁ ⟹ 3 ∤ n₁²+3n₂²（q9cs_unit_sq の符号違いクローン・
    euclid_int 消費）。L₂ 影ノルム N·N̄ の主要係数が 3 と素であることの実体。 -/
theorem q27cs_unit_sq_plus {n1 n2 : Int} (h : ¬ ((3 : Nat) : Int) ∣ n1) :
    ¬ ((3 : Nat) : Int) ∣ (n1 * n1 + 3 * (n2 * n2)) := by
  intro hd
  obtain ⟨k, hk⟩ := hd
  have h3 : ((3 : Nat) : Int) ∣ n1 * n1 := ⟨k - n2 * n2, by omega⟩
  exact h (euclid_int 3 isPrime_three h3 h)

/-- **2×2 L₂ peel（★ q3cu_ppow_dvd 消費）**: N ペアが 3∤N₁ なら、PD t (N·x) から
    PD t x。共役結合 N₁·(N·x)₁ + 3N₂·(N·x)₂ = (N₁²+3N₂²)x₁（および
    N₁·(N·x)₂ − N₂·(N·x)₁ = (N₁²+3N₂²)x₂）を明示線形化して素冪 Euclid で剥がす。 -/
theorem q27cs_pair_peel (t : Nat) {n x : q27csP}
    (hn : ¬ ((3 : Nat) : Int) ∣ n.1) (h : q27csPD t (q27csMul n x)) :
    q27csPD t x := by
  have h1 : ((3 ^ t : Nat) : Int) ∣ n.1 * x.1 - 3 * (n.2 * x.2) := h.1
  have h2 : ((3 ^ t : Nat) : Int) ∣ n.1 * x.2 + n.2 * x.1 := h.2
  have hA : ((3 ^ t : Nat) : Int)
      ∣ n.1 * (n.1 * x.1 - 3 * (n.2 * x.2)) + 3 * (n.2 * (n.1 * x.2 + n.2 * x.1)) :=
    Int.dvd_add (q9cs_dvd_mull n.1 h1) (q9cs_dvd_mull 3 (q9cs_dvd_mull n.2 h2))
  have heqA : n.1 * (n.1 * x.1 - 3 * (n.2 * x.2)) + 3 * (n.2 * (n.1 * x.2 + n.2 * x.1))
      = (n.1 * n.1 + 3 * (n.2 * n.2)) * x.1 := by
    have e1 : n.1 * (n.1 * x.1 - 3 * (n.2 * x.2))
        = n.1 * (n.1 * x.1) - 3 * (n.1 * (n.2 * x.2)) := by
      rw [Int.mul_sub, Int.mul_left_comm n.1 3 (n.2 * x.2)]
    have e2 : n.2 * (n.1 * x.2 + n.2 * x.1)
        = n.1 * (n.2 * x.2) + n.2 * (n.2 * x.1) := by
      rw [Int.mul_add, Int.mul_left_comm n.2 n.1 x.2]
    have e3 : (n.1 * n.1 + 3 * (n.2 * n.2)) * x.1
        = n.1 * (n.1 * x.1) + 3 * (n.2 * (n.2 * x.1)) := by
      rw [Int.add_mul, Int.mul_assoc n.1 n.1 x.1, Int.mul_assoc 3 (n.2 * n.2) x.1,
        Int.mul_assoc n.2 n.2 x.1]
    rw [e1, e2, e3]
    omega
  rw [heqA] at hA
  rw [Int.mul_comm] at hA
  have hx1 : ((3 ^ t : Nat) : Int) ∣ x.1 :=
    q3cu_ppow_dvd t hA (q27cs_unit_sq_plus hn)
  have hB : ((3 ^ t : Nat) : Int)
      ∣ n.1 * (n.1 * x.2 + n.2 * x.1) - n.2 * (n.1 * x.1 - 3 * (n.2 * x.2)) :=
    Int.dvd_sub (q9cs_dvd_mull n.1 h2) (q9cs_dvd_mull n.2 h1)
  have heqB : n.1 * (n.1 * x.2 + n.2 * x.1) - n.2 * (n.1 * x.1 - 3 * (n.2 * x.2))
      = (n.1 * n.1 + 3 * (n.2 * n.2)) * x.2 := by
    have e1 : n.1 * (n.1 * x.2 + n.2 * x.1)
        = n.1 * (n.1 * x.2) + n.2 * (n.1 * x.1) := by
      rw [Int.mul_add, Int.mul_left_comm n.1 n.2 x.1]
    have e2 : n.2 * (n.1 * x.1 - 3 * (n.2 * x.2))
        = n.2 * (n.1 * x.1) - 3 * (n.2 * (n.2 * x.2)) := by
      rw [Int.mul_sub, Int.mul_left_comm n.2 3 (n.2 * x.2)]
    have e3 : (n.1 * n.1 + 3 * (n.2 * n.2)) * x.2
        = n.1 * (n.1 * x.2) + 3 * (n.2 * (n.2 * x.2)) := by
      rw [Int.add_mul, Int.mul_assoc n.1 n.1 x.2, Int.mul_assoc 3 (n.2 * n.2) x.2,
        Int.mul_assoc n.2 n.2 x.2]
    have e4 : n.2 * (n.1 * x.1) = n.1 * (n.2 * x.1) := Int.mul_left_comm n.2 n.1 x.1
    rw [e1, e2, e3, e4]
    omega
  rw [heqB] at hB
  rw [Int.mul_comm] at hB
  exact ⟨hx1, q3cu_ppow_dvd t hB (q27cs_unit_sq_plus hn)⟩

/-- **6 座標一括 peel（★★ Cramer 消費）**: W のノルム影が単数正則（3∤N₁）なら、
    TD t (W·B) から TD t B。3 スロットの随伴線形結合（PD 閉包で可除）を
    q27cs_cramer0/1/2 で N(W)·Bᵢ に書き換え、2×2 peel で 12 座標を一括に剥がす。
    ——level-9 の q9cs_unit_peel が 6 座標基底で「随伴対角化＋peel」に昇格した形。 -/
theorem q27cs_norm_peel (t : Nat) (e : q27csP) (W : q27csT) {B : q27csT}
    (hn : ¬ ((3 : Nat) : Int) ∣ (q27csNorm e W.1 W.2.1 W.2.2).1)
    (h : q27csTD t (q27csTMul e W B)) : q27csTD t B := by
  have h0 : q27csPD t (q27csAdd (q27csMul W.1 B.1)
      (q27csMul e (q27csAdd (q27csMul W.2.1 B.2.2) (q27csMul W.2.2 B.2.1)))) := h.1
  have h1 : q27csPD t (q27csAdd (q27csAdd (q27csMul W.1 B.2.1) (q27csMul W.2.1 B.1))
      (q27csMul e (q27csMul W.2.2 B.2.2))) := h.2.1
  have h2 : q27csPD t (q27csAdd (q27csAdd (q27csMul W.1 B.2.2) (q27csMul W.2.1 B.2.1))
      (q27csMul W.2.2 B.1)) := h.2.2
  have hLC0 := q27cs_pd_add
    (q27cs_pd_mull (q27csSub (q27csMul W.1 W.1) (q27csMul e (q27csMul W.2.1 W.2.2))) h0)
    (q27cs_pd_add
      (q27cs_pd_mull (q27csSub (q27csMul e (q27csMul e (q27csMul W.2.2 W.2.2)))
        (q27csMul e (q27csMul W.1 W.2.1))) h2)
      (q27cs_pd_mull (q27csSub (q27csMul e (q27csMul W.2.1 W.2.1))
        (q27csMul e (q27csMul W.1 W.2.2))) h1))
  rw [q27cs_cramer0 e W.1 W.2.1 W.2.2 B.1 B.2.1 B.2.2] at hLC0
  have hLC1 := q27cs_pd_add
    (q27cs_pd_mull (q27csSub (q27csMul W.1 W.1) (q27csMul e (q27csMul W.2.1 W.2.2))) h1)
    (q27cs_pd_add
      (q27cs_pd_mull (q27csSub (q27csMul e (q27csMul W.2.2 W.2.2))
        (q27csMul W.1 W.2.1)) h0)
      (q27cs_pd_mull (q27csSub (q27csMul e (q27csMul W.2.1 W.2.1))
        (q27csMul e (q27csMul W.1 W.2.2))) h2))
  rw [q27cs_cramer1 e W.1 W.2.1 W.2.2 B.1 B.2.1 B.2.2] at hLC1
  have hLC2 := q27cs_pd_add
    (q27cs_pd_mull (q27csSub (q27csMul W.1 W.1) (q27csMul e (q27csMul W.2.1 W.2.2))) h2)
    (q27cs_pd_add
      (q27cs_pd_mull (q27csSub (q27csMul e (q27csMul W.2.2 W.2.2))
        (q27csMul W.1 W.2.1)) h1)
      (q27cs_pd_mull (q27csSub (q27csMul W.2.1 W.2.1) (q27csMul W.1 W.2.2)) h0))
  rw [q27cs_cramer2 e W.1 W.2.1 W.2.2 B.1 B.2.1 B.2.2] at hLC2
  exact ⟨q27cs_pair_peel t hn hLC0, q27cs_pair_peel t hn hLC1,
    q27cs_pair_peel t hn hLC2⟩

/-! ## q27cs-6/7: 単段降下（★ 偶段 m≥1・奇段 全 m≥0） -/

/-- **q27cs-6（★）: 偶段降下** k=2m → 2m+1（m≥1） — 12 座標 IH（TD m）と E1′/E2′ 影の
    mod 3^{m+1} 可除・W ノルム影の単数正則から、b,c の λ-自由 6 座標が 3^{m+1} へ。
    2 次尾項（ζ₉(a·c²)・ζ₉(b²·c)・a·b²・ζ₉(b·c²)）は 3^{2m} ⊆ 3^{m+1}（m≥1）で消え、
    主要項 W·b / W·c が随伴 peel（q27cs_norm_peel）で剥がれる——主要項抽出の完全証明。 -/
theorem q27cs_descent_even (m : Nat) (hm : 1 ≤ m) (e : q27csP) (z W a b c : q27csT)
    (hn : ¬ ((3 : Nat) : Int) ∣ (q27csNorm e W.1 W.2.1 W.2.2).1)
    (hb : q27csTD m b) (hc : q27csTD m c)
    (hE1 : q27csTD (m + 1) (q27csE1 e z W a b c))
    (hE2 : q27csTD (m + 1) (q27csE2 e z W a b c)) :
    q27csTDF (m + 1) b ∧ q27csTDF (m + 1) c := by
  have hcc : q27csTD (m + 1) (q27csTMul e c c) :=
    q27cs_td_of_le (by omega : m + 1 ≤ m + m) (q27cs_td_mul e hc hc)
  have hbb : q27csTD (m + 1) (q27csTMul e b b) :=
    q27cs_td_of_le (by omega : m + 1 ≤ m + m) (q27cs_td_mul e hb hb)
  have ht1 : q27csTD (m + 1) (q27csTMul e z (q27csTMul e a (q27csTMul e c c))) :=
    q27cs_td_mull e z (q27cs_td_mull e a hcc)
  have ht2 : q27csTD (m + 1) (q27csTMul e z (q27csTMul e (q27csTMul e b b) c)) :=
    q27cs_td_mull e z (q27cs_td_mulr e hbb c)
  have hWb : q27csTD (m + 1) (q27csTMul e W b) :=
    q27cs_td_cancel hE1 (q27cs_td_add ht1 ht2)
  have hs1 : q27csTD (m + 1) (q27csTMul e a (q27csTMul e b b)) :=
    q27cs_td_mull e a hbb
  have hs2 : q27csTD (m + 1) (q27csTMul e z (q27csTMul e b (q27csTMul e c c))) :=
    q27cs_td_mull e z (q27cs_td_mull e b hcc)
  have hWc : q27csTD (m + 1) (q27csTMul e W c) :=
    q27cs_td_cancel hE2 (q27cs_td_add hs1 hs2)
  have hpb := q27cs_norm_peel (m + 1) e W hn hWb
  have hpc := q27cs_norm_peel (m + 1) e W hn hWc
  exact ⟨⟨hpb.1.1, hpb.2.1.1, hpb.2.2.1⟩, ⟨hpc.1.1, hpc.2.1.1, hpc.2.2.1⟩⟩

/-- **q27cs-7（★）: 奇段降下** k=2m+1 → 2m+2（全 m≥0） — 混合不変量 TM m
    （λ-自由 3^{m+1}・λ-側 3^m）から b,c の λ-側 6 座標が 3^{m+1} へ。2 次尾項は
    混合 3-content（q27cs_tm_mul: x₁y₁ は 3^{2m+2}・明示 3·x₂y₂ は 3^{2m+1}・
    交叉 x₁y₂+x₂y₁ は 3^{2m+1}）で全 m≥0 で消える——交互パリティの基底 bootstrap。 -/
theorem q27cs_descent_odd (m : Nat) (e : q27csP) (z W a b c : q27csT)
    (hn : ¬ ((3 : Nat) : Int) ∣ (q27csNorm e W.1 W.2.1 W.2.2).1)
    (hb : q27csTM m b) (hc : q27csTM m c)
    (hE1 : q27csTD (m + 1) (q27csE1 e z W a b c))
    (hE2 : q27csTD (m + 1) (q27csE2 e z W a b c)) :
    q27csTDS (m + 1) b ∧ q27csTDS (m + 1) c := by
  have hcc : q27csTD (m + 1) (q27csTMul e c c) := q27cs_tm_mul e hc hc
  have hbb : q27csTD (m + 1) (q27csTMul e b b) := q27cs_tm_mul e hb hb
  have ht1 : q27csTD (m + 1) (q27csTMul e z (q27csTMul e a (q27csTMul e c c))) :=
    q27cs_td_mull e z (q27cs_td_mull e a hcc)
  have ht2 : q27csTD (m + 1) (q27csTMul e z (q27csTMul e (q27csTMul e b b) c)) :=
    q27cs_td_mull e z (q27cs_td_mulr e hbb c)
  have hWb : q27csTD (m + 1) (q27csTMul e W b) :=
    q27cs_td_cancel hE1 (q27cs_td_add ht1 ht2)
  have hs1 : q27csTD (m + 1) (q27csTMul e a (q27csTMul e b b)) :=
    q27cs_td_mull e a hbb
  have hs2 : q27csTD (m + 1) (q27csTMul e z (q27csTMul e b (q27csTMul e c c))) :=
    q27cs_td_mull e z (q27cs_td_mull e b hcc)
  have hWc : q27csTD (m + 1) (q27csTMul e W c) :=
    q27cs_td_cancel hE2 (q27cs_td_add hs1 hs2)
  have hpb := q27cs_norm_peel (m + 1) e W hn hWb
  have hpc := q27cs_norm_peel (m + 1) e W hn hWc
  exact ⟨⟨hpb.1.2, hpb.2.1.2, hpb.2.2.2⟩, ⟨hpc.1.2, hpc.2.1.2, hpc.2.2.2⟩⟩

/-! ## q27cs-8: W = a² 実例化と交互合成（★★ 全レベル降下 glue） -/

/-- 偶段の W = a·a（ζ₉-ねじれ積影）実例化——設計文書の主要係数 a² に忠実な形。 -/
theorem q27cs_descent_even_sq (m : Nat) (hm : 1 ≤ m) (e : q27csP) (z a b c : q27csT)
    (hn : ¬ ((3 : Nat) : Int) ∣ (q27csNorm e (q27csTMul e a a).1
      (q27csTMul e a a).2.1 (q27csTMul e a a).2.2).1)
    (hb : q27csTD m b) (hc : q27csTD m c)
    (hE1 : q27csTD (m + 1) (q27csE1 e z (q27csTMul e a a) a b c))
    (hE2 : q27csTD (m + 1) (q27csE2 e z (q27csTMul e a a) a b c)) :
    q27csTDF (m + 1) b ∧ q27csTDF (m + 1) c :=
  q27cs_descent_even m hm e z (q27csTMul e a a) a b c hn hb hc hE1 hE2

/-- 奇段の W = a·a 実例化。 -/
theorem q27cs_descent_odd_sq (m : Nat) (e : q27csP) (z a b c : q27csT)
    (hn : ¬ ((3 : Nat) : Int) ∣ (q27csNorm e (q27csTMul e a a).1
      (q27csTMul e a a).2.1 (q27csTMul e a a).2.2).1)
    (hb : q27csTM m b) (hc : q27csTM m c)
    (hE1 : q27csTD (m + 1) (q27csE1 e z (q27csTMul e a a) a b c))
    (hE2 : q27csTD (m + 1) (q27csE2 e z (q27csTMul e a a) a b c)) :
    q27csTDS (m + 1) b ∧ q27csTDS (m + 1) c :=
  q27cs_descent_odd m e z (q27csTMul e a a) a b c hn hb hc hE1 hE2

/-- **q27cs-8（★★）: 交互パリティ同時降下・全レベル** — E1′/E2′ 影が全レベルで可除
    （本物では O_{M₉} の等式 E′=0 から q9cs_zero_rep_dvd 型の橋で出る）、W ノルム影の
    単数正則、基底 TDF 1（λ-自由 6 座標の 3∣・単数枝反証の出口）から、
    ∀m で 3^m が 12 座標全てを割る。帰納の各段: m=0→1 は奇段 m=0（k=1→2）、
    m≥1→m+1 は偶段＋奇段の合成——q9cs_descent_all と同一の交互 glue が
    12 座標・6 座標基底で閉じることの実証。 -/
theorem q27cs_descent_all (e : q27csP) (z W a b c : q27csT)
    (hn : ¬ ((3 : Nat) : Int) ∣ (q27csNorm e W.1 W.2.1 W.2.2).1)
    (hE1 : ∀ t : Nat, q27csTD t (q27csE1 e z W a b c))
    (hE2 : ∀ t : Nat, q27csTD t (q27csE2 e z W a b c))
    (hbb : q27csTDF 1 b) (hbc : q27csTDF 1 c) :
    ∀ m : Nat, q27csTD m b ∧ q27csTD m c := by
  intro m
  induction m with
  | zero => exact ⟨q27cs_td_zero b, q27cs_td_zero c⟩
  | succ p ih =>
    obtain ⟨ihb, ihc⟩ := ih
    cases p with
    | zero =>
      have htmb : q27csTM 0 b :=
        ⟨⟨hbb.1, q9cs_pow_zero_dvd b.1.2⟩, ⟨hbb.2.1, q9cs_pow_zero_dvd b.2.1.2⟩,
         ⟨hbb.2.2, q9cs_pow_zero_dvd b.2.2.2⟩⟩
      have htmc : q27csTM 0 c :=
        ⟨⟨hbc.1, q9cs_pow_zero_dvd c.1.2⟩, ⟨hbc.2.1, q9cs_pow_zero_dvd c.2.1.2⟩,
         ⟨hbc.2.2, q9cs_pow_zero_dvd c.2.2.2⟩⟩
      have hodd := q27cs_descent_odd 0 e z W a b c hn htmb htmc (hE1 1) (hE2 1)
      exact ⟨⟨⟨hbb.1, hodd.1.1⟩, ⟨hbb.2.1, hodd.1.2.1⟩, ⟨hbb.2.2, hodd.1.2.2⟩⟩,
        ⟨⟨hbc.1, hodd.2.1⟩, ⟨hbc.2.1, hodd.2.2.1⟩, ⟨hbc.2.2, hodd.2.2.2⟩⟩⟩
    | succ q =>
      have heven := q27cs_descent_even (q + 1) (by omega) e z W a b c hn ihb ihc
        (hE1 (q + 1 + 1)) (hE2 (q + 1 + 1))
      have htmb : q27csTM (q + 1) b :=
        ⟨⟨heven.1.1, ihb.1.2⟩, ⟨heven.1.2.1, ihb.2.1.2⟩, ⟨heven.1.2.2, ihb.2.2.2⟩⟩
      have htmc : q27csTM (q + 1) c :=
        ⟨⟨heven.2.1, ihc.1.2⟩, ⟨heven.2.2.1, ihc.2.1.2⟩, ⟨heven.2.2.2, ihc.2.2.2⟩⟩
      have hodd := q27cs_descent_odd (q + 1) e z W a b c hn htmb htmc
        (hE1 (q + 1 + 1)) (hE2 (q + 1 + 1))
      exact ⟨⟨⟨heven.1.1, hodd.1.1⟩, ⟨heven.1.2.1, hodd.1.2.1⟩,
          ⟨heven.1.2.2, hodd.1.2.2⟩⟩,
        ⟨⟨heven.2.1, hodd.2.1⟩, ⟨heven.2.2.1, hodd.2.2.1⟩,
          ⟨heven.2.2.2, hodd.2.2.2⟩⟩⟩

/-! ## q27cs-9: 忠実性影補題（q3kMul スロット 0 のレベル n rep 橋・q9cs-7 の M₉ 版）

q27csTMul は q3kMul（ζ₃-ねじれ畳み込み）のスロット毎 Int 影である——これを
「本物の q3kMul の出力 rep = 影の出力値」として実証する。q9cs-7 が q3rqMul 1 回分で
止めたのと同格に、ねじれの入るスロット 0 の両 L₂ 座標を単一積橋として実証する
（スロット 1/2 は同一合成の反復＝Module q27c の物量部分）。E′=0 を TD 仮定の形に読む
橋は既存 `q9cs_zero_rep_dvd` がレベル一般でそのまま消費できる（再証明不要）。 -/

/-- **忠実性（スロット 0・λ-自由座標）**: (q3kMul x y) のスロット 0 の第 1 座標の
    レベル n rep は、対応する rep 影に q27csTMul を適用したスロット 0 第 1 座標に一致。 -/
theorem q27cs_k_mul0_fst_valn (n : Nat) (x y : q3kCar)
    (e1 e2 x01 x02 x11 x12 x21 x22 y01 y02 y11 y12 y21 y22 : Int)
    (he1 : q3rqZeta.1.val n = Quot.mk (modCong (3 ^ n)).rel e1)
    (he2 : q3rqZeta.2.val n = Quot.mk (modCong (3 ^ n)).rel e2)
    (hx01 : x.1.1.val n = Quot.mk (modCong (3 ^ n)).rel x01)
    (hx02 : x.1.2.val n = Quot.mk (modCong (3 ^ n)).rel x02)
    (hx11 : x.2.1.1.val n = Quot.mk (modCong (3 ^ n)).rel x11)
    (hx12 : x.2.1.2.val n = Quot.mk (modCong (3 ^ n)).rel x12)
    (hx21 : x.2.2.1.val n = Quot.mk (modCong (3 ^ n)).rel x21)
    (hx22 : x.2.2.2.val n = Quot.mk (modCong (3 ^ n)).rel x22)
    (hy01 : y.1.1.val n = Quot.mk (modCong (3 ^ n)).rel y01)
    (hy02 : y.1.2.val n = Quot.mk (modCong (3 ^ n)).rel y02)
    (hy11 : y.2.1.1.val n = Quot.mk (modCong (3 ^ n)).rel y11)
    (hy12 : y.2.1.2.val n = Quot.mk (modCong (3 ^ n)).rel y12)
    (hy21 : y.2.2.1.val n = Quot.mk (modCong (3 ^ n)).rel y21)
    (hy22 : y.2.2.2.val n = Quot.mk (modCong (3 ^ n)).rel y22) :
    (q3kMul x y).1.1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          ((q27csTMul (e1, e2) ((x01, x02), (x11, x12), (x21, x22))
            ((y01, y02), (y11, y12), (y21, y22))).1.1) := by
  have hS1 : (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1)).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst x11 x12 y21 y22 + q9csMulFst x21 x22 y11 y12) :=
    q9cs_add_valn n (q3rqMul x.2.1 y.2.2).1 (q3rqMul x.2.2 y.2.1).1
      (q9csMulFst x11 x12 y21 y22) (q9csMulFst x21 x22 y11 y12)
      (q9cs_rq_mul_fst_valn n x.2.1 y.2.2 x11 x12 y21 y22 hx11 hx12 hy21 hy22)
      (q9cs_rq_mul_fst_valn n x.2.2 y.2.1 x21 x22 y11 y12 hx21 hx22 hy11 hy12)
  have hS2 : (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1)).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd x11 x12 y21 y22 + q9csMulSnd x21 x22 y11 y12) :=
    q9cs_add_valn n (q3rqMul x.2.1 y.2.2).2 (q3rqMul x.2.2 y.2.1).2
      (q9csMulSnd x11 x12 y21 y22) (q9csMulSnd x21 x22 y11 y12)
      (q9cs_rq_mul_snd_valn n x.2.1 y.2.2 x11 x12 y21 y22 hx11 hx12 hy21 hy22)
      (q9cs_rq_mul_snd_valn n x.2.2 y.2.1 x21 x22 y11 y12 hx21 hx22 hy11 hy12)
  exact q9cs_add_valn n (q3rqMul x.1 y.1).1
    (q3rqMul q3rqZeta (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1))).1
    (q9csMulFst x01 x02 y01 y02)
    (q9csMulFst e1 e2 (q9csMulFst x11 x12 y21 y22 + q9csMulFst x21 x22 y11 y12)
      (q9csMulSnd x11 x12 y21 y22 + q9csMulSnd x21 x22 y11 y12))
    (q9cs_rq_mul_fst_valn n x.1 y.1 x01 x02 y01 y02 hx01 hx02 hy01 hy02)
    (q9cs_rq_mul_fst_valn n q3rqZeta
      (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1)) e1 e2
      (q9csMulFst x11 x12 y21 y22 + q9csMulFst x21 x22 y11 y12)
      (q9csMulSnd x11 x12 y21 y22 + q9csMulSnd x21 x22 y11 y12) he1 he2 hS1 hS2)

/-- **忠実性（スロット 0・λ-座標）**: 同スロットの第 2 座標版。 -/
theorem q27cs_k_mul0_snd_valn (n : Nat) (x y : q3kCar)
    (e1 e2 x01 x02 x11 x12 x21 x22 y01 y02 y11 y12 y21 y22 : Int)
    (he1 : q3rqZeta.1.val n = Quot.mk (modCong (3 ^ n)).rel e1)
    (he2 : q3rqZeta.2.val n = Quot.mk (modCong (3 ^ n)).rel e2)
    (hx01 : x.1.1.val n = Quot.mk (modCong (3 ^ n)).rel x01)
    (hx02 : x.1.2.val n = Quot.mk (modCong (3 ^ n)).rel x02)
    (hx11 : x.2.1.1.val n = Quot.mk (modCong (3 ^ n)).rel x11)
    (hx12 : x.2.1.2.val n = Quot.mk (modCong (3 ^ n)).rel x12)
    (hx21 : x.2.2.1.val n = Quot.mk (modCong (3 ^ n)).rel x21)
    (hx22 : x.2.2.2.val n = Quot.mk (modCong (3 ^ n)).rel x22)
    (hy01 : y.1.1.val n = Quot.mk (modCong (3 ^ n)).rel y01)
    (hy02 : y.1.2.val n = Quot.mk (modCong (3 ^ n)).rel y02)
    (hy11 : y.2.1.1.val n = Quot.mk (modCong (3 ^ n)).rel y11)
    (hy12 : y.2.1.2.val n = Quot.mk (modCong (3 ^ n)).rel y12)
    (hy21 : y.2.2.1.val n = Quot.mk (modCong (3 ^ n)).rel y21)
    (hy22 : y.2.2.2.val n = Quot.mk (modCong (3 ^ n)).rel y22) :
    (q3kMul x y).1.2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          ((q27csTMul (e1, e2) ((x01, x02), (x11, x12), (x21, x22))
            ((y01, y02), (y11, y12), (y21, y22))).1.2) := by
  have hS1 : (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1)).1.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulFst x11 x12 y21 y22 + q9csMulFst x21 x22 y11 y12) :=
    q9cs_add_valn n (q3rqMul x.2.1 y.2.2).1 (q3rqMul x.2.2 y.2.1).1
      (q9csMulFst x11 x12 y21 y22) (q9csMulFst x21 x22 y11 y12)
      (q9cs_rq_mul_fst_valn n x.2.1 y.2.2 x11 x12 y21 y22 hx11 hx12 hy21 hy22)
      (q9cs_rq_mul_fst_valn n x.2.2 y.2.1 x21 x22 y11 y12 hx21 hx22 hy11 hy12)
  have hS2 : (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1)).2.val n
      = Quot.mk (modCong (3 ^ n)).rel
          (q9csMulSnd x11 x12 y21 y22 + q9csMulSnd x21 x22 y11 y12) :=
    q9cs_add_valn n (q3rqMul x.2.1 y.2.2).2 (q3rqMul x.2.2 y.2.1).2
      (q9csMulSnd x11 x12 y21 y22) (q9csMulSnd x21 x22 y11 y12)
      (q9cs_rq_mul_snd_valn n x.2.1 y.2.2 x11 x12 y21 y22 hx11 hx12 hy21 hy22)
      (q9cs_rq_mul_snd_valn n x.2.2 y.2.1 x21 x22 y11 y12 hx21 hx22 hy11 hy12)
  exact q9cs_add_valn n (q3rqMul x.1 y.1).2
    (q3rqMul q3rqZeta (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1))).2
    (q9csMulSnd x01 x02 y01 y02)
    (q9csMulSnd e1 e2 (q9csMulFst x11 x12 y21 y22 + q9csMulFst x21 x22 y11 y12)
      (q9csMulSnd x11 x12 y21 y22 + q9csMulSnd x21 x22 y11 y12))
    (q9cs_rq_mul_snd_valn n x.1 y.1 x01 x02 y01 y02 hx01 hx02 hy01 hy02)
    (q9cs_rq_mul_snd_valn n q3rqZeta
      (q3rqAdd (q3rqMul x.2.1 y.2.2) (q3rqMul x.2.2 y.2.1)) e1 e2
      (q9csMulFst x11 x12 y21 y22 + q9csMulFst x21 x22 y11 y12)
      (q9csMulSnd x11 x12 y21 y22 + q9csMulSnd x21 x22 y11 y12) he1 he2 hS1 hS2)

end IUT
