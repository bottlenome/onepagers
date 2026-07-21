/-
  IUT/Q3KummerNonicRegular.lean — q27ci（M₉ 正則性パック / level-27 第 2 層 KILL の
    genuine-new 障害 (i)・q27cs `hn` 仮定の discharge）

  ── 主要成果の分類: **[実／(c) 承認済み足場]**（named 実ターゲット = 柱A **A6**
     mono-anabelian 復元の **level-27 第 2 層 KILL キャンペーン**。scope
     （audit/level27-kill-scope-2026-07-11.md §3.3(a)）が名指しした genuine-new 障害
     **(i) M₉ 正則性パック**——level-9 の 2 座標ノルム N=p²+3q² が使えない O_{M₉}
     （6 ℤ₃-座標・wild e=6）上での 3-正則性・ζ₉ 単数正則性・**6 座標 q3k ノルムを使う
     単数判定**——を実対象（q3kCar・実 z3・実 q3kNormBase）の上で建設し、
     q27cs（IUT/Q3Mu27DescentSpike.lean）の 12 座標交互パリティ降下が仮定形で残した
     `hn : ¬3∣(q27csNorm e W₀ W₁ W₂).1`（spike 正直限定 3）を **本物の O_{M₉} 単数から
     discharge** する（q27ci_norm_unit_wedge・q27ci_descent_all_of_unit）。
     toy 主語なし——主語は実 q3k/q3rq/z3 とその実レベル rep。
     後続本物化計画（承認済み足場の昇格経路）: q27ci（本ファイル）→ q27c
     （μ₂₇ 完全性・E′=0 導出＋基底 TDF 1＋スロット 1/2 忠実性物量で q27cs を全 discharge）
     → q27tl/q27mt/q27mr → q27mb（kill_mod27）→ crk27（mod-27 接続）。

  complete_pct 影響: **A6 level-27 正則性 — complete_pct 0 前進（本ファイル）**。
     本ファイルは kill も剛性もテータも橋も含まない単数論・正則性の先行建設であり、
     実 IUT 完全証明率を動かさない。s_A6（現 0.61・帽子 ≤0.65）が動くのは
     キャンペーン末端の橋 q27mb ＋ mod-27 接続が閉じた時のみで、その時も帽子
     ≤0.65 の内側に留まる。本ファイルでは A6 status を一切動かさない（過大主張しない）。

  内容（detail 文書 audit/pillar-A6-level27-first-slice-detail-2026-07-20.md §2.3/§3
  Module 2（U-0/U-1/U-2）の実装）:
   * q27ci-1 正則性パック M₉ 版:
     - q27ci_embed_mul / q27ci_three_mul_zero / q27ci_three_reg_M — **3 は O_{M₉} で正則**
       （3x=3y ⟹ x=y・各 M₉ 座標を L₂ の q9ci_three_reg_L2 へ落とす）
     - q27ci_nine_reg_M / q27ci_pi9_reg_M — 9-正則・**π₉-正則**（π₉⁵u₆·π₉ = 3 の
       q27ps_pi9_T 消費で 3-正則へ帰着）
     - q27ci_unit_reg_M / q27ci_unit_mul_zero — 単数正則（q3kInv 閉形式逆元消費）
     - q27ci_zeta9_unit / q27ci_zeta9_reg — **ζ₉ は実単数（q9tl_zeta9_unit 消費）＋正則**
   * q27ci-2 主単数判定（U-1）:
     - q27ci_ufilt_unit / q27ci_one_add_pik_unit — **U^(k) ⊆ O_{M₉}^×（k≥6）**・
       1+π₉^k a は実単数（q27ps_ufilt6_unit の 3 段ノルム降下 M₉→L₂→ℤ₃ を消費）
     - q27ci_one_add_three_unit — **1+3t は実単数**（3 = π₉⁶u₆ 経由・q27c の標準形）
   * q27ci-3/4 rep 橋（U-2 の配管）:
     - q27ciRep / q27ci_rep_add/mul/neg/three / q27ci_val_down / q27ci_rep_down —
       L₂ 影ペアのレベル n rep 述語と構造的橋（q9cs_*_valn 消費）・レベル射影 n→1
     - q27ci_norm_shadow_eq / q27ci_normBase_rep — **実 q3kNormBase のレベル n rep が
       q27cs の 6 座標ノルム影 q27csNorm に一致**（随伴 Cramer の入力形そのもの）
   * q27ci-5 hn discharge（U-2・★ 本ファイルの核）:
     - q27ci_unit_rep_nondvd — 単数の L₂ ノルムのレベル 1 rep 第 1 座標は 3 と素
       （IsZpUnit のレベル 1 判定・q3mc_norm_lev1 消費）
     - **q27ci_norm_unit_wedge** — W ∈ O_{M₉}^× とそのレベル n rep 影（n≥1）に対し
       `¬3∣(q27csNorm e w0 w1 w2).1`——**q27cs の hn 仮定の discharge そのもの**
     - q27ci_norm_unit_wedge_sq — W = a·a（a 単数）実例化（ノルム乗法性 q3k_unit_mul）
     - **q27ci_descent_all_of_unit** — q27cs_descent_all の hn を実単数入力で消した
       無条件形（12 座標降下が本物の単数判定の上で回る）
   * q27ci-6 capstone: Q3KummerNonicRegularData / q27ciData / q27ci_exists

  正直な限定（§4 規約により消さない・弱化しない・q3k/q9ps/q27k/q27ps/q27cs 継承の上に
  追記のみ）:
  1. **M₉ 単数正則性インフラのみ**（kill もテータも剛性も橋も含まない）。μ₂₇ 完全性の
     本体（E′=0 の立方展開導出・基底 TDF 1 の単数枝反証・q27csTMul スロット 1/2 の
     忠実性物量）は Module q27c の仕事として残る——本ファイルが discharge するのは
     q27cs の `hn`（単数正則仮定）とその周辺の正則性・主単数判定のみ。
  2. **主単数判定は U^(6) = 1+3O_{M₉} から**（q27ps_ufilt6_unit 消費・k≥6）。
     U^(1)〜U^(5)（π₉¹〜π₉⁵ レベルの主単数）の単数性は未形式化（level-27 連鎖が
     必要とするのは 1+3t 形と N(w̃) ∈ U^(15) ⊆ U^(6) のみ・q27ps §2 継承）。
  3. **rep 橋は q3rq ペア（L₂ 6 座標中の 2 座標単位）の構造的合成のみ**。q27cs-9 と同格
     の単一演算橋の合成であり、q3kMul スロット 1/2 の一括橋は q27c の物量部分（spike
     正直限定 4 を継承・ここでは主張しない）。
  4. q3k/q9ps/q27k/q27ps/q27cs の正直限定を全継承（O と ^× のみ・体化なし・付値論なし・
     τ を超える Galois ゼロ・実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体・tmzLimit 橋なし）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用
  （omega は純線形 Int/Nat ゴールのみ——非線形部分は明示 rw で線形化してから）。
-/
import IUT.Q3KummerNonicSplit
import IUT.Q3Mu27DescentSpike
import IUT.Q3TateCurveL9

namespace IUT

/-! ## q27ci-1: 正則性パック M₉ 版（3-正則・π₉-正則・単数正則・ζ₉ 正則） -/

/-- embed 倍の 3 座標一括形: q3kEmbed(m)·v = (m·v₀, m·v₁, m·v₂)。 -/
theorem q27ci_embed_mul (m : q3rqCar) (v : q3kCar) :
    q3kMul (q3kEmbed m) v
      = ((q3rqMul m v.1, q3rqMul m v.2.1, q3rqMul m v.2.2) : q3kCar) := by
  apply q3k_ext
  · show q3rqAdd (q3rqMul m v.1)
        (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero v.2.2) (q3rqMul q3rqZero v.2.1)))
      = q3rqMul m v.1
    rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul v.2.2, q3rqRing.zero_mul v.2.1,
        q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
        q3rqRing.add_zero (q3rqRing.mul m v.1)]
  · show q3rqAdd (q3rqAdd (q3rqMul m v.2.1) (q3rqMul q3rqZero v.1))
        (q3rqMul q3rqZeta (q3rqMul q3rqZero v.2.2))
      = q3rqMul m v.2.1
    rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul v.1,
        q3rqRing.add_zero (q3rqRing.mul m v.2.1), q3rqRing.zero_mul v.2.2,
        q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero (q3rqRing.mul m v.2.1)]
  · show q3rqAdd (q3rqAdd (q3rqMul m v.2.2) (q3rqMul q3rqZero v.2.1))
        (q3rqMul q3rqZero v.1)
      = q3rqMul m v.2.2
    rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul v.2.1,
        q3rqRing.add_zero (q3rqRing.mul m v.2.2), q3rqRing.zero_mul v.1,
        q3rqRing.add_zero (q3rqRing.mul m v.2.2)]

/-- **q27ci-1a: 3 は零因子でない（O_{M₉}）** — 3·z = 0 ⟹ z = 0
    （embed 形＋各 M₉ 座標で q9ci_three_reg_L2）。 -/
theorem q27ci_three_mul_zero (z : q3kCar) (h : q3kMul q27kThree z = q3kZero) :
    z = q3kZero := by
  rw [q27ps_threeM, q27ci_embed_mul q3rqThreeElt z] at h
  apply q3k_ext
  · exact q9ci_three_reg_L2 z.1 (congrArg (fun w : q3kCar => w.1) h)
  · exact q9ci_three_reg_L2 z.2.1 (congrArg (fun w : q3kCar => w.2.1) h)
  · exact q9ci_three_reg_L2 z.2.2 (congrArg (fun w : q3kCar => w.2.2) h)

/-- **q27ci-1b（★）: 3 は正則（O_{M₉}）** — 3·x = 3·y ⟹ x = y。
    level-9 の q9ci_three_reg_L2（2 座標）の 6 座標 M₉ 版。 -/
theorem q27ci_three_reg_M {x y : q3kCar}
    (h : q3kMul q27kThree x = q3kMul q27kThree y) : x = y := by
  have hd : q3kMul q27kThree (q3kAdd x (q3kNeg y)) = q3kZero := by
    rw [q3k_kM_eq, q9nf_kA_eq, q9ps_kN_eq, q9nf_kZ_eq,
        q3kRing.left_distrib q27kThree x (q3kRing.neg y),
        q3kRing.mul_neg q27kThree y]
    rw [q3k_kM_eq] at h
    rw [h, q3kRing.add_neg (q3kRing.mul q27kThree y)]
  have hz := q27ci_three_mul_zero (q3kAdd x (q3kNeg y)) hd
  have h2 : q3kAdd (q3kAdd x (q3kNeg y)) y = q3kAdd q3kZero y := by rw [hz]
  rw [q9nf_kA_eq, q9ps_kN_eq, q9nf_kZ_eq,
      q3kRing.add_assoc x (q3kRing.neg y) y, q3kRing.neg_add y,
      q3kRing.add_zero x, q3kRing.zero_add y] at h2
  exact h2

/-- 9 = 3·3 ∈ O_{M₉}。 -/
def q27ciNineM : q3kCar := q3kMul q27kThree q27kThree

/-- **q27ci-1c: 9 は正則（O_{M₉}）**（3-正則の 2 回適用）。 -/
theorem q27ci_nine_reg_M {x y : q3kCar}
    (h : q3kMul q27ciNineM x = q3kMul q27ciNineM y) : x = y := by
  apply q27ci_three_reg_M
  apply q27ci_three_reg_M
  show q3kMul q27kThree (q3kMul q27kThree x) = q3kMul q27kThree (q3kMul q27kThree y)
  rw [q3k_kM_eq, ← q3kRing.mul_assoc q27kThree q27kThree x,
      ← q3kRing.mul_assoc q27kThree q27kThree y]
  exact h

/-- **q27ci-1d（★）: π₉ は正則（O_{M₉}）** — π₉·x = π₉·y ⟹ x = y
    （T = π₉⁵u₆ を左から掛けて π₉·T = 3（q27ps_pi9_T）で 3-正則へ帰着——
    wild 一様化子の正則性が分割恒等式 3 = π₉⁶u₆ の消費だけで出る）。 -/
theorem q27ci_pi9_reg_M {x y : q3kCar}
    (h : q3kMul q9psPi9 x = q3kMul q9psPi9 y) : x = y := by
  apply q27ci_three_reg_M
  have hT := congrArg (q3kMul q27psT) h
  rw [q3k_kM_eq] at hT
  rw [← q3kRing.mul_assoc q27psT q9psPi9 x, ← q3kRing.mul_assoc q27psT q9psPi9 y,
      q3kRing.mul_comm q27psT q9psPi9] at hT
  show q3kMul q27kThree x = q3kMul q27kThree y
  rw [← q27ps_pi9_T, q3k_kM_eq]
  exact hT

/-- π₉·z = 0 ⟹ z = 0。 -/
theorem q27ci_pi9_mul_zero (z : q3kCar) (h : q3kMul q9psPi9 z = q3kZero) :
    z = q3kZero := by
  apply q27ci_pi9_reg_M (x := z) (y := q3kZero)
  rw [h, q3k_kM_eq, q9nf_kZ_eq, q3kRing.mul_zero q9psPi9]

/-- **q27ci-1e: 単数は正則（O_{M₉}）** — u ∈ O_{M₉}^×, u·x = u·y ⟹ x = y
    （閉形式逆元 q3kInv 消費・choice-free）。 -/
theorem q27ci_unit_reg_M (u : q3kCar) (hu : q3kUnitMem u) {x y : q3kCar}
    (h : q3kMul u x = q3kMul u y) : x = y :=
  calc x = q3kMul q3kOne x := (q3k_one_mul x).symm
    _ = q3kMul (q3kMul (q3kInv u hu) u) x := by rw [q3k_inv_mul' u hu]
    _ = q3kMul (q3kInv u hu) (q3kMul u x) := q3k_mul_assoc _ _ _
    _ = q3kMul (q3kInv u hu) (q3kMul u y) := by rw [h]
    _ = q3kMul (q3kMul (q3kInv u hu) u) y := (q3k_mul_assoc _ _ _).symm
    _ = q3kMul q3kOne y := by rw [q3k_inv_mul' u hu]
    _ = y := q3k_one_mul y

/-- 単数 u に対し u·z = 0 ⟹ z = 0。 -/
theorem q27ci_unit_mul_zero (u : q3kCar) (hu : q3kUnitMem u) {z : q3kCar}
    (h : q3kMul u z = q3kZero) : z = q3kZero := by
  apply q27ci_unit_reg_M u hu
  rw [h, q3k_kM_eq, q9nf_kZ_eq, q3kRing.mul_zero u]

/-- **q27ci-1f: ζ₉ は実単数**（q9tl_zeta9_unit の消費・N(ζ₉) = ζ₃ 経由）。 -/
theorem q27ci_zeta9_unit : q3kUnitMem q3kZeta9 := q9tl_zeta9_unit

/-- **q27ci-1g（★）: ζ₉ は正則** — ζ₉·x = ζ₉·y ⟹ x = y。 -/
theorem q27ci_zeta9_reg {x y : q3kCar}
    (h : q3kMul q3kZeta9 x = q3kMul q3kZeta9 y) : x = y :=
  q27ci_unit_reg_M q3kZeta9 q9tl_zeta9_unit h

/-- ζ₉·z = 0 ⟹ z = 0。 -/
theorem q27ci_zeta9_mul_zero {z : q3kCar} (h : q3kMul q3kZeta9 z = q3kZero) :
    z = q3kZero :=
  q27ci_unit_mul_zero q3kZeta9 q9tl_zeta9_unit h

/-! ## q27ci-2: 主単数判定（U-1）——U^(k) ⊆ O_{M₉}^×（k≥6）・1+3t は実単数 -/

/-- **q27ci-2a: U^(k) ⊆ O_{M₉}^×（k ≥ 6）**（q27ps の 3 段ノルム降下 M₉→L₂→ℤ₃ 消費）。 -/
theorem q27ci_ufilt_unit {k : Nat} (hk : 6 ≤ k) {x : q3kCar}
    (h : q9nfUfilt k x) : q3kUnitMem x :=
  q27ps_ufilt6_unit (q9nf_dvd_of_le hk h)

/-- **q27ci-2b: 1 + π₉^k·a は実単数（k ≥ 6）**——「principal unit ⟹ unit」の
    π₉-冪明示形。level-9 の N(w) = −1 型の定数簿に依らない M₉ 固有の単数判定。 -/
theorem q27ci_one_add_pik_unit (k : Nat) (hk : 6 ≤ k) (a : q3kCar) :
    q3kUnitMem (q3kAdd q3kOne (q3kMul (q9nfPiPow k) a)) := by
  apply q27ci_ufilt_unit hk
  show q9wrDvd (q9nfPiPow k)
      (q3kAdd (q3kAdd q3kOne (q3kMul (q9nfPiPow k) a)) (q3kNeg q3kOne))
  rw [q9nf_one_add_cancel]
  exact ⟨a, rfl⟩

/-- **q27ci-2c（★ U-1）: 1 + 3t は実単数**（3 = π₉⁶·u₆ の q27ps_three_pi6_u6 消費・
    q27c の E′ 系で現れる標準形）。 -/
theorem q27ci_one_add_three_unit (t : q3kCar) :
    q3kUnitMem (q3kAdd q3kOne (q3kMul q27kThree t)) := by
  apply q27ps_ufilt6_unit
  show q9wrDvd (q9nfPiPow 6)
      (q3kAdd (q3kAdd q3kOne (q3kMul q27kThree t)) (q3kNeg q3kOne))
  rw [q9nf_one_add_cancel]
  refine ⟨q3kMul q9psU6 t, ?_⟩
  rw [q27ps_three_pi6_u6, q3k_kM_eq]
  exact q3kRing.mul_assoc (q9nfPiPow 6) q9psU6 t

/-- 定義的楔: O_{M₉} 単数の相対ノルムは O_{L₂} 単数（q3kUnitMem の定義そのもの）。 -/
theorem q27ci_normBase_unit {x : q3kCar} (hx : q3kUnitMem x) :
    q3rqUnitMem (q3kNormBase x) := hx

/-! ## q27ci-3: L₂ 影ペアの rep 述語と構造的橋（U-2 の配管・q9cs_*_valn 消費） -/

/-- ペア反元の Int 影。 -/
def q27ciPNeg (x : q27csP) : q27csP := (-x.1, -x.2)

/-- 反元影の第 1 射影。 -/
theorem q27ci_pneg_fst (x : q27csP) : (q27ciPNeg x).1 = -x.1 := rfl
/-- 反元影の第 2 射影。 -/
theorem q27ci_pneg_snd (x : q27csP) : (q27ciPNeg x).2 = -x.2 := rfl

/-- **rep 述語**: L₂ 元 x のレベル n rep が影ペア s（q27cs の Int 簿記の担体）に一致。 -/
def q27ciRep (n : Nat) (x : q3rqCar) (s : q27csP) : Prop :=
  x.1.val n = Quot.mk (modCong (3 ^ n)).rel s.1 ∧
    x.2.val n = Quot.mk (modCong (3 ^ n)).rel s.2

/-- rep は加法と両立。 -/
theorem q27ci_rep_add {n : Nat} {x y : q3rqCar} {s t : q27csP}
    (hx : q27ciRep n x s) (hy : q27ciRep n y t) :
    q27ciRep n (q3rqAdd x y) (q27csAdd s t) :=
  ⟨q9cs_add_valn n x.1 y.1 s.1 t.1 hx.1 hy.1,
   q9cs_add_valn n x.2 y.2 s.2 t.2 hx.2 hy.2⟩

/-- rep は乗法と両立（q9cs_rq_mul_fst/snd_valn 消費——q27csMul は q9csMulFst/Snd と
    定義一致）。 -/
theorem q27ci_rep_mul {n : Nat} {x y : q3rqCar} {s t : q27csP}
    (hx : q27ciRep n x s) (hy : q27ciRep n y t) :
    q27ciRep n (q3rqMul x y) (q27csMul s t) :=
  ⟨q9cs_rq_mul_fst_valn n x y s.1 s.2 t.1 t.2 hx.1 hx.2 hy.1 hy.2,
   q9cs_rq_mul_snd_valn n x y s.1 s.2 t.1 t.2 hx.1 hx.2 hy.1 hy.2⟩

/-- rep は反元と両立。 -/
theorem q27ci_rep_neg {n : Nat} {x : q3rqCar} {s : q27csP}
    (hx : q27ciRep n x s) : q27ciRep n (q3rqNeg x) (q27ciPNeg s) :=
  ⟨q9cs_neg_valn n x.1 s.1 hx.1, q9cs_neg_valn n x.2 s.2 hx.2⟩

/-- 3 ∈ O_{L₂}（ノルム多項式の −3K 係数 q3kThree）の rep は (3, 0)。 -/
theorem q27ci_rep_three (n : Nat) : q27ciRep n q3kThree ((3, 0) : q27csP) := by
  refine ⟨?_, ?_⟩
  · show (z3.add z3.one (z3.add z3.one z3.one)).val n
      = Quot.mk (modCong (3 ^ n)).rel 3
    exact q9cs_add_valn n z3.one (z3.add z3.one z3.one) 1 2 rfl
      (q9cs_add_valn n z3.one z3.one 1 1 rfl rfl)
  · show (z3.add z3.zero (z3.add z3.zero z3.zero)).val n
      = Quot.mk (modCong (3 ^ n)).rel 0
    exact q9cs_add_valn n z3.zero (z3.add z3.zero z3.zero) 0 0 rfl
      (q9cs_add_valn n z3.zero z3.zero 0 0 rfl rfl)

/-- **レベル射影 n→1**（逆極限の整合性・choice-free）: レベル n rep はレベル 1 rep。 -/
theorem q27ci_val_down (x : z3.carrier) {n : Nat} (h1n : 1 ≤ n) (v : Int)
    (hv : x.val n = Quot.mk (modCong (3 ^ n)).rel v) :
    x.val 1 = Quot.mk (modCong (3 ^ 1)).rel v := by
  have hproj := x.property h1n
  rw [hv] at hproj
  exact hproj.symm

/-- rep のレベル射影 n→1。 -/
theorem q27ci_rep_down {n : Nat} (h1n : 1 ≤ n) {x : q3rqCar} {s : q27csP}
    (h : q27ciRep n x s) : q27ciRep 1 x s :=
  ⟨q27ci_val_down x.1 h1n s.1 h.1, q27ci_val_down x.2 h1n s.2 h.2⟩

/-! ## q27ci-4: 6 座標ノルム影の橋——実 q3kNormBase の rep = q27csNorm -/

/-- 影ペアの 3 倍: (3,0)·x = x + (x + x)。 -/
theorem q27ci_pthree_mul (x : q27csP) :
    q27csMul ((3, 0) : q27csP) x = q27csAdd x (q27csAdd x x) := by
  refine q27cs_pext ?_ ?_
  · show (3 : Int) * x.1 - 3 * ((0 : Int) * x.2) = x.1 + (x.1 + x.1)
    rw [Int.zero_mul x.2]
    omega
  · show (3 : Int) * x.2 + (0 : Int) * x.1 = x.2 + (x.2 + x.2)
    rw [Int.zero_mul x.1]
    omega

/-- **影恒等式**: 実 q3kNormBase の構造をそのまま影に写した式
    （a³ + ζ₃b³ + ζ₃²c³ − 3(ζ₃abc) の左結合立方・(3,0) 係数・反元形）は
    q27cs の 6 座標ノルム影 q27csNorm（右結合立方・3 重和形）に一致する。 -/
theorem q27ci_norm_shadow_eq (e w0 w1 w2 : q27csP) :
    q27csAdd
      (q27csAdd
        (q27csAdd (q27csMul (q27csMul w0 w0) w0)
          (q27csMul e (q27csMul (q27csMul w1 w1) w1)))
        (q27csMul (q27csMul e e) (q27csMul (q27csMul w2 w2) w2)))
      (q27ciPNeg (q27csMul ((3, 0) : q27csP)
        (q27csMul e (q27csMul (q27csMul w0 w1) w2))))
    = q27csNorm e w0 w1 w2 := by
  show _ = q27csSub
      (q27csAdd (q27csMul w0 (q27csMul w0 w0))
        (q27csAdd (q27csMul e (q27csMul w1 (q27csMul w1 w1)))
          (q27csMul e (q27csMul e (q27csMul w2 (q27csMul w2 w2))))))
      (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
        (q27csAdd (q27csMul e (q27csMul w0 (q27csMul w1 w2)))
          (q27csMul e (q27csMul w0 (q27csMul w1 w2)))))
  rw [q27cs_mul_assoc w0 w0 w0, q27cs_mul_assoc w1 w1 w1, q27cs_mul_assoc w2 w2 w2,
      q27cs_mul_assoc e e (q27csMul w2 (q27csMul w2 w2)),
      q27cs_mul_assoc w0 w1 w2,
      q27ci_pthree_mul (q27csMul e (q27csMul w0 (q27csMul w1 w2)))]
  refine q27cs_pext ?_ ?_
  · repeat (first | rw [q27cs_add_fst] | rw [q27cs_sub_fst] | rw [q27ci_pneg_fst])
    omega
  · repeat (first | rw [q27cs_add_snd] | rw [q27cs_sub_snd] | rw [q27ci_pneg_snd])
    omega

/-- **q27ci-4a（★ U-2 配管の核）: 実相対ノルムの rep 橋** — W ∈ O_{M₉} の 3 座標の
    レベル n rep 影 (w0,w1,w2) と ζ₃ の rep 影 e から、実 q3kNormBase W のレベル n rep は
    q27cs の 6 座標ノルム影 q27csNorm e w0 w1 w2 に一致（構造的合成＋影恒等式）。 -/
theorem q27ci_normBase_rep (n : Nat) (W : q3kCar) (e w0 w1 w2 : q27csP)
    (he : q27ciRep n q3rqZeta e) (h0 : q27ciRep n W.1 w0)
    (h1 : q27ciRep n W.2.1 w1) (h2 : q27ciRep n W.2.2 w2) :
    q27ciRep n (q3kNormBase W) (q27csNorm e w0 w1 w2) := by
  have hS : q27ciRep n (q3kNormBase W)
      (q27csAdd
        (q27csAdd
          (q27csAdd (q27csMul (q27csMul w0 w0) w0)
            (q27csMul e (q27csMul (q27csMul w1 w1) w1)))
          (q27csMul (q27csMul e e) (q27csMul (q27csMul w2 w2) w2)))
        (q27ciPNeg (q27csMul ((3, 0) : q27csP)
          (q27csMul e (q27csMul (q27csMul w0 w1) w2))))) := by
    show q27ciRep n
        (q3rqAdd
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul W.1 W.1) W.1)
              (q3rqMul q3rqZeta (q3rqMul (q3rqMul W.2.1 W.2.1) W.2.1)))
            (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul W.2.2 W.2.2) W.2.2)))
          (q3rqNeg (q3rqMul q3kThree
            (q3rqMul q3rqZeta (q3rqMul (q3rqMul W.1 W.2.1) W.2.2)))))
        _
    exact q27ci_rep_add
      (q27ci_rep_add
        (q27ci_rep_add
          (q27ci_rep_mul (q27ci_rep_mul h0 h0) h0)
          (q27ci_rep_mul he (q27ci_rep_mul (q27ci_rep_mul h1 h1) h1)))
        (q27ci_rep_mul (q27ci_rep_mul he he)
          (q27ci_rep_mul (q27ci_rep_mul h2 h2) h2)))
      (q27ci_rep_neg (q27ci_rep_mul (q27ci_rep_three n)
        (q27ci_rep_mul he (q27ci_rep_mul (q27ci_rep_mul h0 h1) h2))))
  rw [q27ci_norm_shadow_eq e w0 w1 w2] at hS
  exact hS

/-! ## q27ci-5: hn discharge（★ 本ファイルの核・q27cs 仮定 3 の解消） -/

/-- **q27ci-5a: 単数のレベル 1 rep 判定** — x ∈ O_{L₂}^× なら、x の両座標の
    レベル 1 rep (n1, n2) に対し 3 ∤ n1（IsZpUnit のレベル 1 判定・N = n1²+3n2² の
    レベル 1 値 q3mc_norm_lev1 消費・choice-free）。 -/
theorem q27ci_unit_rep_nondvd (x : q3rqCar) (hx : q3rqUnitMem x) (n1 n2 : Int)
    (h1 : x.1.val 1 = Quot.mk (modCong (3 ^ 1)).rel n1)
    (h2 : x.2.val 1 = Quot.mk (modCong (3 ^ 1)).rel n2) :
    ¬ ((3 : Nat) : Int) ∣ n1 := by
  intro h3n
  obtain ⟨a, ha, hpa⟩ := hx
  have hn1 : (q3rqNorm x).val 1
      = Quot.mk (modCong (3 ^ 1)).rel (n1 * n1 + (-((-3) * (n2 * n2)))) :=
    q3mc_norm_lev1 x.1 x.2 n1 n2 h1 h2
  rw [ha] at hn1
  have hdvd := quot_exact intGrp (modCong (3 ^ 1)) hn1
  rw [Nat.pow_one] at hdvd
  obtain ⟨k, hk⟩ := h3n
  have h3sq : ((3 : Nat) : Int) ∣ (n1 * n1) :=
    ⟨k * n1, by rw [← Int.mul_assoc, ← hk]⟩
  obtain ⟨c1, hc1⟩ := h3sq
  obtain ⟨c2, hc2⟩ := hdvd
  apply hpa
  refine ⟨c2 + c1 + n2 * n2, ?_⟩
  omega

/-- **q27ci-5b（★★★ hn discharge）: 6 座標ノルム単数判定の楔** — W ∈ O_{M₉}^×
    （実単数）とそのレベル n rep 影（n ≥ 1）・ζ₃ の rep 影 e に対し、q27cs の
    降下が要求する単数正則仮定 `hn : ¬3∣(q27csNorm e w0 w1 w2).1` が成立する。
    level-9 の N = p²+3q² の一撃に代わる、実 q3kNormBase（三次・交差項 3ζ₃abc 込み）
    経由の M₉ 単数判定——spike 正直限定 3 の名指しした discharge。 -/
theorem q27ci_norm_unit_wedge (n : Nat) (h1n : 1 ≤ n) (W : q3kCar)
    (hW : q3kUnitMem W) (e w0 w1 w2 : q27csP)
    (he : q27ciRep n q3rqZeta e) (h0 : q27ciRep n W.1 w0)
    (h1 : q27ciRep n W.2.1 w1) (h2 : q27ciRep n W.2.2 w2) :
    ¬ ((3 : Nat) : Int) ∣ (q27csNorm e w0 w1 w2).1 := by
  have hrep := q27ci_rep_down h1n (q27ci_normBase_rep n W e w0 w1 w2 he h0 h1 h2)
  exact q27ci_unit_rep_nondvd (q3kNormBase W) hW
    (q27csNorm e w0 w1 w2).1 (q27csNorm e w0 w1 w2).2 hrep.1 hrep.2

/-- **q27ci-5c: W = a·a 実例化** — a ∈ O_{M₉}^× の平方（q27cs の主要係数 a² の実体）
    に対する hn discharge（ノルム乗法性 = q3k_unit_mul の消費）。 -/
theorem q27ci_norm_unit_wedge_sq (n : Nat) (h1n : 1 ≤ n)
    (a : q3kCar) (ha : q3kUnitMem a) (e w0 w1 w2 : q27csP)
    (he : q27ciRep n q3rqZeta e)
    (h0 : q27ciRep n (q3kMul a a).1 w0)
    (h1 : q27ciRep n (q3kMul a a).2.1 w1)
    (h2 : q27ciRep n (q3kMul a a).2.2 w2) :
    ¬ ((3 : Nat) : Int) ∣ (q27csNorm e w0 w1 w2).1 :=
  q27ci_norm_unit_wedge n h1n (q3kMul a a) (q3k_unit_mul ha ha)
    e w0 w1 w2 he h0 h1 h2

/-- **q27ci-5d（★★ 組立）: hn を消した 12 座標交互パリティ降下** —
    q27cs_descent_all の単数正則仮定 hn を、実 O_{M₉} 単数 Wr とそのレベル n rep 影
    から discharge した無条件形。残る入力（E′ 影の全レベル可除・基底 TDF 1）は
    Module q27c の仕事（spike 正直限定 1/4 を継承・ここでは仮定のまま）。 -/
theorem q27ci_descent_all_of_unit (n : Nat) (h1n : 1 ≤ n)
    (Wr : q3kCar) (hWr : q3kUnitMem Wr)
    (e : q27csP) (z W a b c : q27csT)
    (he : q27ciRep n q3rqZeta e)
    (hw0 : q27ciRep n Wr.1 W.1) (hw1 : q27ciRep n Wr.2.1 W.2.1)
    (hw2 : q27ciRep n Wr.2.2 W.2.2)
    (hE1 : ∀ t : Nat, q27csTD t (q27csE1 e z W a b c))
    (hE2 : ∀ t : Nat, q27csTD t (q27csE2 e z W a b c))
    (hbb : q27csTDF 1 b) (hbc : q27csTDF 1 c) :
    ∀ m : Nat, q27csTD m b ∧ q27csTD m c :=
  q27cs_descent_all e z W a b c
    (q27ci_norm_unit_wedge n h1n Wr hWr e W.1 W.2.1 W.2.2 he hw0 hw1 hw2)
    hE1 hE2 hbb hbc

/-! ## q27ci-6: capstone -/

/-- **q27ci-6a: M₉ 正則性パック** — 3-正則・π₉-正則・ζ₉ 単数＋正則・主単数判定
    （1+3t ∈ O_{M₉}^×）・6 座標ノルム単数判定の楔（q27cs hn discharge）の束ね。
    level-9 の N = p²+3q² が使えない M₉（6 ℤ₃-座標・wild e=6）で、level-27 連鎖
    q27ps/q27c が要する単数論の全入力を実対象上で供給する。 -/
structure Q3KummerNonicRegularData where
  /-- 3 は O_{M₉} で正則。 -/
  three_reg : ∀ {x y : q3kCar}, q3kMul q27kThree x = q3kMul q27kThree y → x = y
  /-- π₉ は O_{M₉} で正則。 -/
  pi9_reg : ∀ {x y : q3kCar}, q3kMul q9psPi9 x = q3kMul q9psPi9 y → x = y
  /-- ζ₉ は実単数。 -/
  zeta9_unit : q3kUnitMem q3kZeta9
  /-- ζ₉ は正則。 -/
  zeta9_reg : ∀ {x y : q3kCar}, q3kMul q3kZeta9 x = q3kMul q3kZeta9 y → x = y
  /-- 主単数 1+3t は実単数。 -/
  one_add_three_unit : ∀ t : q3kCar, q3kUnitMem (q3kAdd q3kOne (q3kMul q27kThree t))
  /-- 6 座標ノルム単数判定の楔（q27cs の hn 仮定の discharge）。 -/
  norm_unit_wedge : ∀ (n : Nat), 1 ≤ n → ∀ (W : q3kCar), q3kUnitMem W →
    ∀ (e w0 w1 w2 : q27csP), q27ciRep n q3rqZeta e → q27ciRep n W.1 w0 →
      q27ciRep n W.2.1 w1 → q27ciRep n W.2.2 w2 →
      ¬ ((3 : Nat) : Int) ∣ (q27csNorm e w0 w1 w2).1

/-- **q27ci-6b: 見出し実例** — 実 O_{M₉} = q3k 上の正則性パック。 -/
def q27ciData : Q3KummerNonicRegularData where
  three_reg := q27ci_three_reg_M
  pi9_reg := q27ci_pi9_reg_M
  zeta9_unit := q27ci_zeta9_unit
  zeta9_reg := q27ci_zeta9_reg
  one_add_three_unit := q27ci_one_add_three_unit
  norm_unit_wedge := fun n h1n W hW e w0 w1 w2 he h0 h1 h2 =>
    q27ci_norm_unit_wedge n h1n W hW e w0 w1 w2 he h0 h1 h2

/-- **q27ci-6c: 正則性パックの存在**（実 O_{M₉} 上・choice-free）。 -/
theorem q27ci_exists : Nonempty Q3KummerNonicRegularData := ⟨q27ciData⟩

end IUT
