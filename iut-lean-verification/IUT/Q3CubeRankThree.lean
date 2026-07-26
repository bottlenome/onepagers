/-
  IUT/Q3CubeRankThree.lean — 実局所体の立方剰余群 L₂^×/(L₂^×)³ の rank≥3 下界（B6・K2a）
    L₂^× = q3rqLx = ℤ×U₂ 上の部分群 ⟨[λ],[ζ₃],[4]⟩ ≅ (ℤ/3)³

  ── 主要成果の分類: **[実／(a) 昇格]** — q9cq の rank≥2（⟨[λ],[ζ₃]⟩）を、
     **実 ℤ₃-単数 4 ∈ O_{L₂}^×（B2 の tame 生成元 q9rcFour と同一の実元）を第 3 生成元**に
     加えた rank≥3 へ昇格する。主対象は実 q3rqLx = prodGrp intGrp q3rqU（付値部 ℤ ×
     実単数群 U₂ = O_{L₂}^×）と実 ℤ₃ = z3 のレベル 2（mod 9）——toy 主語なし
     （m202fVol 型・Bool 軌道・surrogate 群を一切使わない）。

  complete_pct 影響: **B6「Kummer 理論（実 Galois コホモロジー上）」0.18 →（監査次第）**。
  q9cq のヘッダ named target「L₂^×/(L₂^×)³ ≅ (ℤ/3)⁴（rank 4・|quotient|=81）」の
  **3 次元目**を閉じる（4 のうち 3 次元・下界のみ）。真水（新規主張）は
   (1) **実 ℤ₃ の立方剰余 mod 9 の完全決定** `q9c3_cube_mod9`（a³ ≡ 0, ±1 (mod 9)）——
       ℤ₃ 側の立方障害。これは q9cq 執筆時に無かった**新しい判別器 D2**であり、
       λ-係数判別器 D1（立方の第 2 成分は必ず 3 で割れる）だけでは原理的に
       検出できない類（有理数 4・16 の類）を殺す（§ 下記「2 判別器の必然性」）。
   (2) **ノルム経由の判別** `q9c3_noncube_of_norm9`（N(v³)=N(v)³ と mod 9 立方障害）。
   (3) **λ-係数判別** `q9c3_noncube_of_snd`（立方の第 2 成分 = 3·((a²−b²)b) の一般形）。
   (4) 8 個の単数側非自明結合 ζ₃^j·4^k（(j,k)≠(0,0)）が全て非立方であること、および
       付値方向 18 結合（q9cq_val_nontrivial 一般形）との束ね ⟹ **rank≥3 下界**。
  **消費（再主張しない）**:
   * ζ₃・ζ₃² の O_{L₂} 内 3 乗根非存在は `q9ci_no_cbrt_zeta`/`q9ci_no_cbrt_zetaSq`（柱A）。
   * 付値方向の非立方性は `q9cq_val_nontrivial`（B6・q9cq）。
   * 立方の第 2 成分公式は `q3mc_cube_snd`（柱A・q3mc）。
   * 実元 4 とその単数性は `q9rcFour`/`q9rc_four_unit`（B2・q9rc）——B2 の tame 生成元と
     同一の実元を使う（別の 4 を作らない）。
   * 3 次コファクタ恒等式 (Y−1)(Y²+Y+1) = Y³−1 は `q9ci_cofactor_raw`（柱A）を intRing へ
     specialize して消費。

  **2 判別器の必然性（設計上の発見・honest note）**:
  λ-係数判別器 D1（立方 (a+bλ)³ = (a³−9ab²) + 3(a²−b²)b·λ の第 2 成分は 3 で割れる）は
  U/U³ 上で指数 3 の核を持つ準同型的判別器であり、27 元の U/U³ 内の 9 元部分群
  ⟨[ζ₃],[4]⟩ とは必ず 3 元以上で交わる。実際 ζ₃·(1+λ) = −2・ζ₃²(1+λ)² = 4 のように
  **有理数になる類は D1 で検出できない**。したがって rank≥3 には ℤ₃ 側の立方障害
  （mod 9・D2）が**原理的に必要**である（設計書 K2a の「gr 簿記のみ」という見積りは
  この点で楽観的だった）。本モジュールは D1・D2 の両方を実装する。

  内容:
   * q9c3_add_val / q9c3_mul_val / q9c3_neg_val   — 任意レベル n の値計算（q3mc の level-1 版の一般化）
   * q9c3_cube9_of_one / q9c3_cube_mod9           — **実 ℤ₃/ℤ の立方 mod 9 完全決定（D2 の核）**
   * q9c3_not_cube_16 / q9c3_not_cube_256         — 16・256 は mod 9 で立方でない
   * q9c3_noncube_of_snd                          — D1（λ-係数判別）
   * q9c3_noncube_of_norm9                        — D2（ノルム mod 9 判別）
   * q9c3_four_zeta_noncube 他 4 本 + q9c3_four_noncube / q9c3_foursq_noncube  — 8 targets
   * q9c3_group_of_ring                           — 環レベル → 群提示レベルの橋
   * Q9c3Indep / q9c3_indep / **q9c3_rank_ge_three** — rank≥3 下界（capstone）
   * Q3CubeRankThreeData / q9c3_data / q9c3_exists

  正直な限定（§4 規約により消さない・弱化しない・q3rq/q9kd/q9cq/q9ci/q9rc 継承の上に追記のみ）:
  1. **rank ≥ 3 下界のみ**。q9cq の named target「full rank 4 = (ℤ/3)⁴・|quotient|=81」は
     **未達のまま据置**——第 4 次元（深い主単数 1+λ³ ∈ U^{(3)}_λ）と上界 exhaustion
     （立方 Hensel: U^{(4)}_λ ⊆ (L₂^×)³ と tame 断面の被覆）は本モジュールに無い。
     q9cq の正直限定 1（full rank 4 未計算）は**消さない**——3/4 次元まで前進しただけ。
  2. **非立方性の核は一部消費**。ζ₃・ζ₃² の非 3 乗は q9ci、付値方向は q9cq を消費する
     （本モジュール新規は D2（mod 9 立方障害）・D1 の一般形・8 結合の組み立て）。
  3. **商群オブジェクトは建てない**。q9kd/q9cq に合わせ「¬∃g, g³=x」の非立方性述語形で
     下界を述べる（quotientGroupN による L₂^×/(L₂^×)³ の対象化は未実施）。
  4. **量化は整元・単数のみ**（O_{L₂} と U₂ = O_{L₂}^×）。分数元 L₂^× 全体の bookkeeping は
     群提示 ℤ×U₂ による（体化なし・A2 恒久限定継承）。
  5. q3rq/q9kd/q9cq/q9ci/q9rc の恒久限定を全継承（n=3・体 L₂ 1 個・拡大 1 個・
     実テータ関数ゼロ・π₁ 同定ゼロ・tmzLimit 比較橋なし・兄弟担体）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用
  （omega は Int/Nat 原子のみ）。
-/
import IUT.Q3CubeQuotientReal
import IUT.Q3ReciprocityCokernelReal

namespace IUT

/-! ## q9c3-0: 任意レベル n の値計算（q3mc の level-1 版の一般化） -/

/-- (x+y) のレベル n 値。 -/
theorem q9c3_add_val (n : Nat) (x y : z3.carrier) (x1 y1 : Int)
    (hx : x.val n = Quot.mk (modCong (3 ^ n)).rel x1)
    (hy : y.val n = Quot.mk (modCong (3 ^ n)).rel y1) :
    (z3.add x y).val n = Quot.mk (modCong (3 ^ n)).rel (x1 + y1) := by
  show (zmod (3 ^ n)).mul (x.val n) (y.val n) = _
  rw [hx, hy]
  rfl

/-- (x·y) のレベル n 値。 -/
theorem q9c3_mul_val (n : Nat) (x y : z3.carrier) (x1 y1 : Int)
    (hx : x.val n = Quot.mk (modCong (3 ^ n)).rel x1)
    (hy : y.val n = Quot.mk (modCong (3 ^ n)).rel y1) :
    (z3.mul x y).val n = Quot.mk (modCong (3 ^ n)).rel (x1 * y1) := by
  show zmodMul (3 ^ n) (x.val n) (y.val n) = _
  rw [hx, hy]
  rfl

/-- (−x) のレベル n 値。 -/
theorem q9c3_neg_val (n : Nat) (x : z3.carrier) (x1 : Int)
    (hx : x.val n = Quot.mk (modCong (3 ^ n)).rel x1) :
    (z3.neg x).val n = Quot.mk (modCong (3 ^ n)).rel (-x1) := by
  show (zmod (3 ^ n)).inv (x.val n) = _
  rw [hx]
  rfl

/-- 1 のレベル n 値。 -/
theorem q9c3_one_val (n : Nat) : (z3.one).val n = Quot.mk (modCong (3 ^ n)).rel 1 := rfl

/-- 0 のレベル n 値。 -/
theorem q9c3_zero_val (n : Nat) : (z3.zero).val n = Quot.mk (modCong (3 ^ n)).rel 0 := rfl

/-- 2 のレベル n 値。 -/
theorem q9c3_two_val (n : Nat) : q3rqTwoZ.val n = Quot.mk (modCong (3 ^ n)).rel 2 := by
  show (z3.add z3.one z3.one).val n = Quot.mk (modCong (3 ^ n)).rel 2
  rw [q9c3_add_val n z3.one z3.one 1 1 (q9c3_one_val n) (q9c3_one_val n)]
  rfl

/-- D = −3 のレベル n 値。 -/
theorem q9c3_D_val (n : Nat) : q3rqD.val n = Quot.mk (modCong (3 ^ n)).rel (-3) := by
  rw [q3rq_D_eq, q9c3_neg_val n q3rqThree 3 (q3rq_three_val n)]

/-- 4 = 1+3 のレベル n 値。 -/
theorem q9c3_c4_val (n : Nat) :
    (z3.add z3.one q3rqThree).val n = Quot.mk (modCong (3 ^ n)).rel (1 + 3) :=
  q9c3_add_val n z3.one q3rqThree 1 3 (q9c3_one_val n) (q3rq_three_val n)

/-! ## q9c3-1: 実 ℤ₃/ℤ の立方 mod 9 完全決定（判別器 D2 の核） -/

/-- a ≡ 1 (mod 3) ⟹ a³ ≡ 1 (mod 9)。
    a³−1 = (a−1)(a²+a+1)（`q9ci_cofactor_raw` を intRing へ specialize）で、
    a−1 も a²+a+1 も 3 で割れる（後者は a²−1 = (a−1)(a+1) 経由）。 -/
theorem q9c3_cube9_of_one (a : Int) (h : (3 : Int) ∣ (a - 1)) :
    (9 : Int) ∣ (a * a * a - 1) := by
  obtain ⟨s, hs⟩ := h
  have hsq : (a - 1) * (a + 1) = a * a - 1 := by
    rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.one_mul, Int.mul_one, Int.one_mul]
    omega
  have h3sq : (3 : Int) ∣ (a * a - 1) := by
    refine ⟨s * (a + 1), ?_⟩
    rw [← hsq, hs, Int.mul_assoc]
  obtain ⟨q, hq⟩ := h3sq
  have hcof : (a + -1) * ((a * a + a) + 1) = (a * a) * a + -1 :=
    q9ci_cofactor_raw intRing a
  have hA : a + -1 = 3 * s := by omega
  have hB : (a * a + a) + 1 = 3 * (q + s + 1) := by omega
  rw [hA, hB] at hcof
  have e2 : (3 * s) * (3 * (q + s + 1)) = (3 * 3) * (s * (q + s + 1)) :=
    CRing.mul_mul_mul_comm intRing (3 : Int) s (3 : Int) (q + s + 1)
  rw [e2] at hcof
  exact ⟨s * (q + s + 1), by omega⟩

/-- **実 ℤ の立方 mod 9 完全決定**: a³ ≡ 0, 1, −1 (mod 9)。
    3∣a・3∣a−1・3∣a+1 の三分法（後 2 者は `q9c3_cube9_of_one` と符号反転）。 -/
theorem q9c3_cube_mod9 (a : Int) :
    (9 : Int) ∣ (a * a * a)
    ∨ (9 : Int) ∣ (a * a * a - 1)
    ∨ (9 : Int) ∣ (a * a * a + 1) := by
  have htri : (3 : Int) ∣ a ∨ (3 : Int) ∣ (a - 1) ∨ (3 : Int) ∣ (a + 1) := by
    obtain ⟨r, hr⟩ : ∃ r : Int, a = 3 * (a / 3) + r ∧ (r = 0 ∨ r = 1 ∨ r = 2) :=
      ⟨a - 3 * (a / 3), by omega, by omega⟩
    obtain h0 | h1 | h2 := hr.2
    · exact Or.inl ⟨a / 3, by omega⟩
    · exact Or.inr (Or.inl ⟨a / 3, by omega⟩)
    · exact Or.inr (Or.inr ⟨a / 3 + 1, by omega⟩)
  obtain h | h | h := htri
  · obtain ⟨t, ht⟩ := h
    refine Or.inl ⟨(t * t) * (3 * t), ?_⟩
    have e1 : (3 * t) * (3 * t) = (3 * 3) * (t * t) :=
      CRing.mul_mul_mul_comm intRing (3 : Int) t (3 : Int) t
    have e2 : ((3 * 3) * (t * t)) * (3 * t) = (3 * 3) * ((t * t) * (3 * t)) :=
      Int.mul_assoc (3 * 3) (t * t) (3 * t)
    rw [ht, e1, e2]
    omega
  · exact Or.inr (Or.inl (q9c3_cube9_of_one a h))
  · have hb : (3 : Int) ∣ ((-a) - 1) := by
      obtain ⟨k, hk⟩ := h
      exact ⟨-k, by omega⟩
    have h9 := q9c3_cube9_of_one (-a) hb
    have e : (-a) * (-a) * (-a) = -(a * a * a) := by
      rw [Int.neg_mul_neg, Int.mul_neg]
    rw [e] at h9
    obtain ⟨c, hc⟩ := h9
    exact Or.inr (Or.inr ⟨-c, by omega⟩)

/-- 16 は mod 9 で立方でない（16 ≡ 7 ∉ {0,1,−1}）。 -/
theorem q9c3_not_cube_16 (a : Int) : ¬ ((9 : Int) ∣ (a * a * a - 16)) := by
  intro h
  obtain ⟨c, hc⟩ := h
  obtain h0 | h1 | h2 := q9c3_cube_mod9 a
  · obtain ⟨d, hd⟩ := h0; omega
  · obtain ⟨d, hd⟩ := h1; omega
  · obtain ⟨d, hd⟩ := h2; omega

/-- 256 は mod 9 で立方でない（256 ≡ 4 ∉ {0,1,−1}）。 -/
theorem q9c3_not_cube_256 (a : Int) : ¬ ((9 : Int) ∣ (a * a * a - 256)) := by
  intro h
  obtain ⟨c, hc⟩ := h
  obtain h0 | h1 | h2 := q9c3_cube_mod9 a
  · obtain ⟨d, hd⟩ := h0; omega
  · obtain ⟨d, hd⟩ := h1; omega
  · obtain ⟨d, hd⟩ := h2; omega

/-! ## q9c3-2: 判別器 D1（λ-係数）——立方の第 2 成分は 3 で割れる -/

/-- **D1 `q9c3_noncube_of_snd`**: t の第 2 成分のレベル 1 値が 3 で割れないなら
    t は O_{L₂} 内で立方でない（立方 (a+bλ)³ の第 2 成分 = 3·((a²−b²)b)・
    `q3mc_cube_snd` 消費）。 -/
theorem q9c3_noncube_of_snd (t : q3rqCar) (t1 : Int)
    (ht : (t.2).val 1 = Quot.mk (modCong (3 ^ 1)).rel t1)
    (h3 : ¬ ((3 : Nat) : Int) ∣ t1) :
    ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ t := by
  intro v hv
  cases v with
  | mk a b =>
    have h2 : (q3rqMul (q3rqMul ((a, b) : q3rqCar) (a, b)) (a, b)).2 = t.2 :=
      congrArg Prod.snd hv
    rw [q3mc_cube_snd a b] at h2
    obtain ⟨k1, hk1⟩ := Quot.exists_rep
      ((z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b).val 1)
    have hmul := q9c3_mul_val 1 q3rqThree
      (z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b) 3 k1
      (q3rq_three_val 1) hk1.symm
    have hval : (z3.mul q3rqThree
        (z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b)).val 1
        = (t.2).val 1 := congrArg (fun z : z3.carrier => z.val 1) h2
    rw [hmul, ht] at hval
    have hd := quot_exact intGrp (modCong (3 ^ 1)) hval
    rw [Nat.pow_one] at hd
    obtain ⟨c, hc⟩ := hd
    exact h3 ⟨k1 - c, by omega⟩

/-! ## q9c3-3: 判別器 D2（ノルム mod 9）——ℤ₃ 側の立方障害 -/

/-- **D2 `q9c3_noncube_of_norm9`**: N(t) のレベル 2（mod 9）値が ℤ の立方でないなら
    t は O_{L₂} 内で立方でない（N(v³) = N(v)³ ＋ `q9c3_cube_mod9`）。 -/
theorem q9c3_noncube_of_norm9 (t : q3rqCar) (tn : Int)
    (ht : (q3rqNorm t).val 2 = Quot.mk (modCong (3 ^ 2)).rel tn)
    (h9 : ∀ a : Int, ¬ ((9 : Int) ∣ (a * a * a - tn))) :
    ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ t := by
  intro v hv
  have hn : q3rqNorm (q3rqMul (q3rqMul v v) v) = q3rqNorm t := congrArg q3rqNorm hv
  rw [q3rq_norm_mul (q3rqMul v v) v, q3rq_norm_mul v v] at hn
  obtain ⟨a, ha⟩ := Quot.exists_rep ((q3rqNorm v).val 2)
  have h1 : (z3.mul (z3.mul (q3rqNorm v) (q3rqNorm v)) (q3rqNorm v)).val 2
      = Quot.mk (modCong (3 ^ 2)).rel (a * a * a) :=
    q9c3_mul_val 2 (z3.mul (q3rqNorm v) (q3rqNorm v)) (q3rqNorm v) (a * a) a
      (q9c3_mul_val 2 (q3rqNorm v) (q3rqNorm v) a a ha.symm ha.symm) ha.symm
  have h2 : (z3.mul (z3.mul (q3rqNorm v) (q3rqNorm v)) (q3rqNorm v)).val 2
      = (q3rqNorm t).val 2 := congrArg (fun z : z3.carrier => z.val 2) hn
  rw [h1, ht] at h2
  have hd : ((3 ^ 2 : Nat) : Int) ∣ (a * a * a - tn) :=
    quot_exact intGrp (modCong (3 ^ 2)) h2
  have hd9 : (9 : Int) ∣ (a * a * a - tn) := hd
  exact h9 a hd9

/-! ## q9c3-4: 実元 4 とスカラー積の座標 -/

/-- スカラー元 (c,0) と任意元の積の第 2 成分は c·(第 2 成分)。 -/
theorem q9c3_snd_scalar (c : z3.carrier) (x : q3rqCar) :
    (q3rqMul ((c, z3.zero) : q3rqCar) x).2 = z3.mul c x.2 := by
  show z3.add (z3.mul c x.2) (z3.mul z3.zero x.1) = z3.mul c x.2
  rw [z3.zero_mul x.1]
  show z3.add (z3.mul c x.2) z3.zero = z3.mul c x.2
  rw [z3.add_comm (z3.mul c x.2) z3.zero, z3.zero_add]

/-- スカラー元同士の積は成分ごと（(c,0)·(d,0) = (cd,0)）。 -/
theorem q9c3_scalar_mul (c d : z3.carrier) :
    q3rqMul ((c, z3.zero) : q3rqCar) ((d, z3.zero) : q3rqCar)
      = ((z3.mul c d, z3.zero) : q3rqCar) := by
  apply q3rq_ext
  · show z3.add (z3.mul c d) (z3.mul q3rqD (z3.mul z3.zero z3.zero)) = z3.mul c d
    rw [z3.zero_mul z3.zero, CRing.mul_zero z3 q3rqD,
      z3.add_comm (z3.mul c d) z3.zero, z3.zero_add]
  · show z3.add (z3.mul c z3.zero) (z3.mul z3.zero d) = z3.zero
    rw [CRing.mul_zero z3 c, z3.zero_mul d, z3.zero_add]

/-- スカラー元のノルムのレベル n 値（N((c,0)) = c²）。 -/
theorem q9c3_norm_scalar_val (n : Nat) (c : z3.carrier) (c1 : Int)
    (hc : c.val n = Quot.mk (modCong (3 ^ n)).rel c1) :
    (q3rqNorm ((c, z3.zero) : q3rqCar)).val n
      = Quot.mk (modCong (3 ^ n)).rel (c1 * c1 + -((-3) * (0 * 0))) := by
  show (z3.add (z3.mul c c) (z3.neg (z3.mul q3rqD (z3.mul z3.zero z3.zero)))).val n = _
  exact q9c3_add_val n (z3.mul c c)
    (z3.neg (z3.mul q3rqD (z3.mul z3.zero z3.zero))) (c1 * c1) (-((-3) * (0 * 0)))
    (q9c3_mul_val n c c c1 c1 hc hc)
    (q9c3_neg_val n (z3.mul q3rqD (z3.mul z3.zero z3.zero)) ((-3) * (0 * 0))
      (q9c3_mul_val n q3rqD (z3.mul z3.zero z3.zero) (-3) (0 * 0) (q9c3_D_val n)
        (q9c3_mul_val n z3.zero z3.zero 0 0 (q9c3_zero_val n) (q9c3_zero_val n))))

/-- 半元 h = 2⁻¹ のレベル 1 データ（2h = 1 から 3∤h₁）。 -/
theorem q9c3_half_val1 :
    ∃ h1 : Int, q3rqHalf.val 1 = Quot.mk (modCong (3 ^ 1)).rel h1
      ∧ ∃ k : Int, 2 * h1 - 1 = 3 * k := by
  obtain ⟨h1, hh1⟩ := Quot.exists_rep (q3rqHalf.val 1)
  refine ⟨h1, hh1.symm, ?_⟩
  have hmul := q9c3_mul_val 1 q3rqTwoZ q3rqHalf 2 h1 (q9c3_two_val 1) hh1.symm
  rw [q3rq_two_half] at hmul
  have hone : (z3.one).val 1 = Quot.mk (modCong (3 ^ 1)).rel 1 := q9c3_one_val 1
  rw [hone] at hmul
  have hd := quot_exact intGrp (modCong (3 ^ 1)) hmul.symm
  rw [Nat.pow_one] at hd
  obtain ⟨c, hc⟩ := hd
  exact ⟨c, by omega⟩

/-! ## q9c3-5: 8 個の単数側 target が全て非立方 -/

/-- **[4] は非立方**（D2・N(4) = 16 は mod 9 で立方でない）。 -/
theorem q9c3_four_noncube : ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ q9rcFour := by
  rw [q9rc_four_pair]
  refine q9c3_noncube_of_norm9 _ ((1 + 3) * (1 + 3) + -((-3) * (0 * 0))) ?_ ?_
  · exact q9c3_norm_scalar_val 2 (z3.add z3.one q3rqThree) (1 + 3) (q9c3_c4_val 2)
  · intro a h
    exact q9c3_not_cube_16 a (by omega)

/-- **[4²] = [16] は非立方**（D2・N(16) = 256 は mod 9 で立方でない）。 -/
theorem q9c3_foursq_noncube :
    ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ q3rqMul q9rcFour q9rcFour := by
  rw [q9rc_four_pair, q9c3_scalar_mul]
  refine q9c3_noncube_of_norm9 _
    (((1 + 3) * (1 + 3)) * ((1 + 3) * (1 + 3)) + -((-3) * (0 * 0))) ?_ ?_
  · exact q9c3_norm_scalar_val 2 (z3.mul (z3.add z3.one q3rqThree) (z3.add z3.one q3rqThree))
      ((1 + 3) * (1 + 3))
      (q9c3_mul_val 2 (z3.add z3.one q3rqThree) (z3.add z3.one q3rqThree) (1 + 3) (1 + 3)
        (q9c3_c4_val 2) (q9c3_c4_val 2))
  · intro a h
    exact q9c3_not_cube_256 a (by omega)

/-- **[4·ζ₃] は非立方**（D1・第 2 成分 4h のレベル 1 値は 3 で割れない）。 -/
theorem q9c3_four_zeta_noncube :
    ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ q3rqMul q9rcFour q3rqZeta := by
  obtain ⟨h1, hh1, k, hk⟩ := q9c3_half_val1
  rw [q9rc_four_pair]
  refine q9c3_noncube_of_snd _ ((1 + 3) * h1) ?_ ?_
  · rw [q9c3_snd_scalar (z3.add z3.one q3rqThree) q3rqZeta]
    exact q9c3_mul_val 1 (z3.add z3.one q3rqThree) q3rqHalf (1 + 3) h1
      (q9c3_c4_val 1) hh1
  · intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    omega

/-- **[4·ζ₃²] は非立方**（D1・第 2 成分 4·(−h)）。 -/
theorem q9c3_four_zetaSq_noncube :
    ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ q3rqMul q9rcFour q3rqZetaSq := by
  obtain ⟨h1, hh1, k, hk⟩ := q9c3_half_val1
  rw [q9rc_four_pair, show q3rqZetaSq = ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar)
    from q3rq_zeta_sq_eq]
  refine q9c3_noncube_of_snd _ ((1 + 3) * (-h1)) ?_ ?_
  · rw [q9c3_snd_scalar (z3.add z3.one q3rqThree)
      ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar)]
    exact q9c3_mul_val 1 (z3.add z3.one q3rqThree) (z3.neg q3rqHalf) (1 + 3) (-h1)
      (q9c3_c4_val 1) (q9c3_neg_val 1 q3rqHalf h1 hh1)
  · intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    omega

/-- **[16·ζ₃] は非立方**（D1・第 2 成分 16h）。 -/
theorem q9c3_foursq_zeta_noncube :
    ∀ v : q3rqCar,
      q3rqMul (q3rqMul v v) v ≠ q3rqMul (q3rqMul q9rcFour q9rcFour) q3rqZeta := by
  obtain ⟨h1, hh1, k, hk⟩ := q9c3_half_val1
  rw [q9rc_four_pair, q9c3_scalar_mul]
  refine q9c3_noncube_of_snd _ (((1 + 3) * (1 + 3)) * h1) ?_ ?_
  · rw [q9c3_snd_scalar (z3.mul (z3.add z3.one q3rqThree) (z3.add z3.one q3rqThree))
      q3rqZeta]
    exact q9c3_mul_val 1 (z3.mul (z3.add z3.one q3rqThree) (z3.add z3.one q3rqThree))
      q3rqHalf ((1 + 3) * (1 + 3)) h1
      (q9c3_mul_val 1 (z3.add z3.one q3rqThree) (z3.add z3.one q3rqThree) (1 + 3) (1 + 3)
        (q9c3_c4_val 1) (q9c3_c4_val 1)) hh1
  · intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    omega

/-- **[16·ζ₃²] は非立方**（D1・第 2 成分 16·(−h)）。 -/
theorem q9c3_foursq_zetaSq_noncube :
    ∀ v : q3rqCar,
      q3rqMul (q3rqMul v v) v ≠ q3rqMul (q3rqMul q9rcFour q9rcFour) q3rqZetaSq := by
  obtain ⟨h1, hh1, k, hk⟩ := q9c3_half_val1
  rw [q9rc_four_pair, q9c3_scalar_mul,
    show q3rqZetaSq = ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar) from q3rq_zeta_sq_eq]
  refine q9c3_noncube_of_snd _ (((1 + 3) * (1 + 3)) * (-h1)) ?_ ?_
  · rw [q9c3_snd_scalar (z3.mul (z3.add z3.one q3rqThree) (z3.add z3.one q3rqThree))
      ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar)]
    exact q9c3_mul_val 1 (z3.mul (z3.add z3.one q3rqThree) (z3.add z3.one q3rqThree))
      (z3.neg q3rqHalf) ((1 + 3) * (1 + 3)) (-h1)
      (q9c3_mul_val 1 (z3.add z3.one q3rqThree) (z3.add z3.one q3rqThree) (1 + 3) (1 + 3)
        (q9c3_c4_val 1) (q9c3_c4_val 1))
      (q9c3_neg_val 1 q3rqHalf h1 hh1)
  · intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    omega

/-! ## q9c3-6: 群提示レベルへの橋と rank≥3 -/

/-- 環レベルの非立方性 ⟹ 群提示 ℤ×U₂ 上の非立方性（第 2 成分へ射影）。 -/
theorem q9c3_group_of_ring (u : q3rqU.carrier)
    (h : ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ u.val) :
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((0 : Int), u) := by
  intro hex
  obtain ⟨g, hg⟩ := hex
  have h2 : (q3rqLx.mul (q3rqLx.mul g g) g).2 = u := congrArg Prod.snd hg
  exact h g.2.val (congrArg Subtype.val h2)

/-- U₂ の元としての 4（B2 の tame 生成元 `q9rcFour` と同一の実元）。 -/
def q9c3FourUnit : q3rqU.carrier := ⟨q9rcFour, q9rc_four_unit⟩

/-- U₂ の元としての 16 = 4²。 -/
def q9c3FourSqUnit : q3rqU.carrier := q3rqU.mul q9c3FourUnit q9c3FourUnit

/-- **8 個の単数側非自明結合 [ζ₃]^j·[4]^k（(j,k)≠(0,0)）が全て非立方**
    ＝ ⟨[ζ₃],[4]⟩ ≅ (ℤ/3)² ↪ 立方剰余群（単数側 2 次元）。 -/
def Q9c3Indep : Prop :=
  (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = ((0 : Int), q9cq_zetaUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = ((0 : Int), q9cq_zetaSqUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = ((0 : Int), q9c3FourUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = ((0 : Int), q9c3FourSqUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = ((0 : Int), q3rqU.mul q9c3FourUnit q9cq_zetaUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = ((0 : Int), q3rqU.mul q9c3FourUnit q9cq_zetaSqUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = ((0 : Int), q3rqU.mul q9c3FourSqUnit q9cq_zetaUnit))
  ∧ (¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
      = ((0 : Int), q3rqU.mul q9c3FourSqUnit q9cq_zetaSqUnit))

/-- **`q9c3_indep`**: 単数側 8 結合の非立方性（ζ₃・ζ₃² は q9ci 消費・
    4・16 は D2・混合 4 本は D1）。 -/
theorem q9c3_indep : Q9c3Indep :=
  ⟨q9c3_group_of_ring q9cq_zetaUnit (fun v => q9ci_no_cbrt_zeta v),
   q9c3_group_of_ring q9cq_zetaSqUnit (fun v => q9ci_no_cbrt_zetaSq v),
   q9c3_group_of_ring q9c3FourUnit q9c3_four_noncube,
   q9c3_group_of_ring q9c3FourSqUnit q9c3_foursq_noncube,
   q9c3_group_of_ring (q3rqU.mul q9c3FourUnit q9cq_zetaUnit) q9c3_four_zeta_noncube,
   q9c3_group_of_ring (q3rqU.mul q9c3FourUnit q9cq_zetaSqUnit) q9c3_four_zetaSq_noncube,
   q9c3_group_of_ring (q3rqU.mul q9c3FourSqUnit q9cq_zetaUnit) q9c3_foursq_zeta_noncube,
   q9c3_group_of_ring (q3rqU.mul q9c3FourSqUnit q9cq_zetaSqUnit)
     q9c3_foursq_zetaSq_noncube⟩

/-- **（★）`q9c3_rank_ge_three`**: ⟨[λ],[ζ₃],[4]⟩ ≅ (ℤ/3)³ の honest 下界形。
    付値方向（3∤i の 18 結合・任意単数 u で成立・`q9cq_val_nontrivial` 消費）と
    単数側 8 結合（`q9c3_indep`）の束ね ⟹ 26 個の非自明結合が全て非立方
    ＝ (ℤ/3)³ が実立方剰余群 L₂^×/(L₂^×)³ へ単射する。
    **full rank 4 は主張しない**（q9cq の named target は据置・ヘッダ正直限定 1）。 -/
theorem q9c3_rank_ge_three :
    (∀ i : Int, ¬ (3 : Int) ∣ i → ∀ u : q3rqU.carrier,
      ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((i : Int), u))
    ∧ Q9c3Indep :=
  ⟨fun i hi u => q9cq_val_nontrivial i hi u, q9c3_indep⟩

/-! ## q9c3-7: capstone（データ束ね・新規証明ゼロ） -/

/-- **`Q3CubeRankThreeData`**: rank≥3 下界データ束ね。 -/
structure Q3CubeRankThreeData where
  /-- 実 ℤ の立方 mod 9 完全決定（D2 の核・新規）。 -/
  cube_mod9 : ∀ a : Int,
    (9 : Int) ∣ (a * a * a) ∨ (9 : Int) ∣ (a * a * a - 1) ∨ (9 : Int) ∣ (a * a * a + 1)
  /-- [4] は非立方（D2）。 -/
  four_noncube : ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
    = ((0 : Int), q9c3FourUnit)
  /-- [16] は非立方（D2）。 -/
  foursq_noncube : ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g
    = ((0 : Int), q9c3FourSqUnit)
  /-- 単数側 8 結合の非立方性（⟨[ζ₃],[4]⟩ ≅ (ℤ/3)²）。 -/
  indep : Q9c3Indep
  /-- 付値方向（3∤i・任意単数 u）。 -/
  val_dir : ∀ i : Int, ¬ (3 : Int) ∣ i → ∀ u : q3rqU.carrier,
    ¬ ∃ g : q3rqLx.carrier, q3rqLx.mul (q3rqLx.mul g g) g = ((i : Int), u)

/-- **`q9c3_data`**: 見出し実例——実 L₂ = ℚ₃(√−3) の立方剰余群の rank≥3 下界。 -/
def q9c3_data : Q3CubeRankThreeData where
  cube_mod9 := q9c3_cube_mod9
  four_noncube := q9c3_group_of_ring q9c3FourUnit q9c3_four_noncube
  foursq_noncube := q9c3_group_of_ring q9c3FourSqUnit q9c3_foursq_noncube
  indep := q9c3_indep
  val_dir := fun i hi u => q9cq_val_nontrivial i hi u

/-- **`q9c3_exists`**: 実立方剰余群の rank≥3 下界の存在。 -/
theorem q9c3_exists : Nonempty Q3CubeRankThreeData := ⟨q9c3_data⟩

end IUT
