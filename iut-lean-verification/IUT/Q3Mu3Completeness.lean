/-
  IUT/Q3Mu3Completeness.lean — R2a（μ₃/μ₆ 完全性 in O_{ℚ₃(ζ₃)} = ℤ₃[√−3]）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**（骨格・模型・代理でなく、R1 の実
     分岐 2 次局所拡大 O_{L₂}=q3rqRing（実 z3=zpRing 3 上の実対環）の**単数群 U₂=q3rqU
     内で「u³=1 ⟹ u∈μ₃={1,ζ₃,ζ₃²}」という円分完全性を本物に証明**する。中核は
     実 ℤ₃ 内の立方根一意性 x³=1⟹x=1（レベルシフト帰納＋素冪 Euclid）と、成分立方
     方程式 (a+bλ)³=1 ⟺ a³−9ab²=1 ∧ 3b(a²−b²)=0 の本物の導出、そして「単数は正則」
     による choice-free な因子消去。toy 主語なし——主語は実 z3 上の実対環 U₂。）

  complete_pct 影響: **R2a foundation**（level-3 テータ群 R3 の mem_iff の急所＝μ₆
  完全性の de-risk）。R1→R4 の ℤ₃^× kill キャンペーンの単一障害点の解消。単体では
  complete_pct 丸め値の前進は ~0（foundation・R3/R4 の前提の本物 discharge）。本
  ラウンドは「complete_pct 0 前進（骨格でなく本物基盤の先行建設）」と正直申告する。

  内容:
   * int_cube_emod3 / int_cube_one_imp — Fermat 型 j³≡j (mod 3)（emod 計算）
   * int_9mm / int_sq_3m1 / int_cube_factor_ident / int_cofactor / int_cube_peel
                                        — 立方の Int 恒等式（cofactor = 3·単数）
   * q3mc_croot_val / q3mc_croot_lev1 / q3mc_croot_level
                                        — ℤ₃ 立方根のレベル簿記（素冪 Euclid 消費）
   * **q3mc_z3_cube_root_one（★★★）** — 実 ℤ₃ 内 x³=1 ⟹ x=1（本ファイルの再利用核）
   * q3mc_three_mul_zero / q3mc_unit_regular — 3 正則・単数正則（choice-free 因子消去）
   * q3mc_cube_snd / q3mc_cube_fst / q3mc_norm_cube_one
                                        — 成分立方方程式（mem_iff の急所・本物）
   * q3mc_a_unit — u³=1 ⟹ a=u.1 は ℤ₃ 単数（N(u)=1 のレベル 1）
   * q3mc_mu3_of_b_zero / q3mc_mu3_of_a_eq_b / q3mc_mu3_of_a_eq_neg_b
                                        — 3 枝（b=0・a=b・a=−b）の μ₃ 帰着（b 成分消去）
   * **q3mc_mu3_complete（★★★）** — U₂ 内 u³=1 ⟹ u∈μ₃（level-1 正則決定木で枝選択）
   * Q3Mu3CompletenessData / q3mc_data — capstone

  正直な限定（§4 規約により消さない・弱化しない・追記のみ）:
  1. **foundation（kill は未達）**。μ₃ 完全性は R3 の mem_iff の材料であって、テータ群・
     mono-theta 剛性・ℤ₃^× kill そのものは後続 R3/R4。本ファイルは何も殺さない。
  2. **LOCAL な O_{L₂}^× 内の μ₃ のみ**。大域円分・tmzLimit・Galois 作用は範囲外
     （R1 の正直限定 2/4/5/7 を継承）。
  3. **単一切片**（p=3・L₂=ℚ₃(ζ₃)・level 3 相当）。μ_{3ⁿ}（n≥2・wild）完全性は F-wild
     の後続 named target。
  4. **μ₆（u³=±1⟹u∈μ₆）版は本ファイルでは未収録**。u³=1⟹u∈μ₃ を完全 discharge し、
     ±1 拡張（−1 は R1 に q3rqNegOne が無いため別ラウンドで q3tNegOne 埋め込み経由）を
     named next とする（§6 段階分割の設計に整合）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3RamifiedQuadratic
import IUT.Q3TateCuspidalization

namespace IUT

/-! ## q3mc-0: Int 立方の基本補題 -/

/-- **q3mc-0a: Fermat 型** j³ ≡ j (mod 3)（emod の乗法計算・3 分律）。 -/
theorem int_cube_emod3 (j : Int) : (j * j * j) % 3 = j % 3 := by
  have e2 : (j * j) % 3 = ((j % 3) * (j % 3)) % 3 := Int.mul_emod j j 3
  have e1 : (j * j * j) % 3 = ((j * j) % 3 * (j % 3)) % 3 := Int.mul_emod (j * j) j 3
  rw [e2] at e1
  have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  obtain h | h | h := hr <;> rw [h] at e1 <;> omega

/-- **q3mc-0b: 3∣j³−1 ⟹ 3∣j−1**（j³≡j ⟹ j≡1 mod 3）。 -/
theorem int_cube_one_imp (j : Int) (h : ((3 : Nat) : Int) ∣ (j * j * j - 1)) :
    ((3 : Nat) : Int) ∣ (j - 1) := by
  have he := int_cube_emod3 j
  omega

/-- **q3mc-0c: (3m)² = 3(3(m²))**（単一の平方の分配）。 -/
theorem int_9mm (m : Int) : (3 * m) * (3 * m) = 3 * (3 * (m * m)) := by
  rw [Int.mul_assoc, Int.mul_comm m (3 * m), Int.mul_assoc]

/-- **q3mc-0d: (3m+1)² = 9m²+6m+1**（3(3(m²)) 形で）。 -/
theorem int_sq_3m1 (m : Int) :
    (3 * m + 1) * (3 * m + 1) = 3 * (3 * (m * m)) + 6 * m + 1 := by
  rw [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul, int_9mm]
  generalize m * m = s
  omega

/-- **q3mc-0e: 立方−1 の因数分解** j³−1 = (j−1)(j²+j+1)。 -/
theorem int_cube_factor_ident (j : Int) :
    j * j * j - 1 = (j - 1) * (j * j + j + 1) := by
  rw [Int.sub_mul, Int.one_mul, Int.mul_add, Int.mul_add, Int.mul_one,
    Int.mul_comm j (j * j)]
  generalize (j * j) * j = A
  generalize j * j = B
  omega

/-- **q3mc-0f: cofactor は 3·単数** — j−1=3m のとき j²+j+1 = 3(3m²+3m+1)。 -/
theorem int_cofactor (j m : Int) (hm : j - 1 = 3 * m) :
    j * j + j + 1 = 3 * (3 * (m * m) + 3 * m + 1) := by
  have hj : j = 3 * m + 1 := by omega
  rw [hj, int_sq_3m1 m]
  generalize m * m = s
  omega

/-- **q3mc-0g: peel** — j−1=3m のとき j³−1 = (3(j−1))·(3m²+3m+1)（素冪 Euclid の入力形）。 -/
theorem int_cube_peel (j m : Int) (hm : j - 1 = 3 * m) :
    j * j * j - 1 = (3 * (j - 1)) * (3 * (m * m) + 3 * m + 1) := by
  rw [int_cube_factor_ident j, int_cofactor j m hm, ← Int.mul_assoc,
    Int.mul_comm (j - 1) 3]

/-- cofactor は 3 と素。 -/
theorem int_cofactor_coprime (m : Int) :
    ¬ ((3 : Nat) : Int) ∣ (3 * (m * m) + 3 * m + 1) := by
  intro h
  have : ((3 : Nat) : Int) ∣ (3 * (m * m) + 3 * m + 1) := h
  omega

/-! ## q3mc-1: 立方値のレベル簿記 -/

/-- **q3mc-1a: 立方成分** — x.val n = [j] なら (x·x·x).val n = [j³]。 -/
theorem q3mc_croot_val (x : z3.carrier) (n : Nat) (j : Int)
    (hj : x.val n = Quot.mk (modCong (3 ^ n)).rel j) :
    (z3.mul (z3.mul x x) x).val n = Quot.mk (modCong (3 ^ n)).rel (j * j * j) := by
  show zmodMul (3 ^ n) ((z3.mul x x).val n) (x.val n)
    = Quot.mk (modCong (3 ^ n)).rel (j * j * j)
  show zmodMul (3 ^ n) (zmodMul (3 ^ n) (x.val n) (x.val n)) (x.val n)
    = Quot.mk (modCong (3 ^ n)).rel (j * j * j)
  rw [hj]
  rfl

/-- **q3mc-1b: レベル 1** — x³=1 ⟹ x ≡ 1 (mod 3)。 -/
theorem q3mc_croot_lev1 (x : z3.carrier)
    (hx : z3.mul (z3.mul x x) x = z3.one) :
    x.val 1 = Quot.mk (modCong (3 ^ 1)).rel 1 := by
  obtain ⟨j, hj⟩ := Quot.exists_rep (x.val 1)
  have hcube : (z3.mul (z3.mul x x) x).val 1
      = Quot.mk (modCong (3 ^ 1)).rel (j * j * j) :=
    q3mc_croot_val x 1 j hj.symm
  have hone : (z3.mul (z3.mul x x) x).val 1 = Quot.mk (modCong (3 ^ 1)).rel 1 :=
    congrFun (congrArg Subtype.val hx) 1
  rw [hcube] at hone
  have hdvd : ((3 ^ 1 : Nat) : Int) ∣ (j * j * j - 1) :=
    quot_exact intGrp (modCong (3 ^ 1)) hone
  rw [Nat.pow_one] at hdvd
  have hd1 : ((3 : Nat) : Int) ∣ (j - 1) := int_cube_one_imp j hdvd
  rw [← hj]
  apply Quot.sound
  show ((3 ^ 1 : Nat) : Int) ∣ (j - 1)
  rw [Nat.pow_one]
  exact hd1

/-- **q3mc-1c: レベル補題** — x³=1 のとき各 n≥1 で x.val n = [j] かつ 3ⁿ ∣ (j−1)。
    レベル n+1 の代表で 3^{n+1}∣(3(j−1))·(単数) を得て素冪 Euclid で 3ⁿ∣(j−1)。 -/
theorem q3mc_croot_level (x : z3.carrier)
    (hx : z3.mul (z3.mul x x) x = z3.one) (n : Nat) :
    ∃ j : Int, x.val n = Quot.mk (modCong (3 ^ n)).rel j
      ∧ ((3 ^ n : Nat) : Int) ∣ (j - 1) := by
  obtain ⟨j, hj⟩ := Quot.exists_rep (x.val (n + 1))
  -- レベル 1 整合: 3 ∣ (j − 1)
  have hlev1 : x.val 1 = Quot.mk (modCong (3 ^ 1)).rel 1 := q3mc_croot_lev1 x hx
  have hproj := x.property (show (1 : Nat) ≤ n + 1 by omega)
  have h3j1 : ((3 : Nat) : Int) ∣ (j - 1) := by
    rw [← hj] at hproj
    have hp2 : Quot.mk (modCong (3 ^ 1)).rel j = x.val 1 := hproj
    rw [hlev1] at hp2
    have := quot_exact intGrp (modCong (3 ^ 1)) hp2
    rw [Nat.pow_one] at this
    exact this
  obtain ⟨m, hm⟩ := h3j1
  -- 3^{n+1} ∣ (j³ − 1)
  have hcube : (z3.mul (z3.mul x x) x).val (n + 1)
      = Quot.mk (modCong (3 ^ (n + 1))).rel (j * j * j) :=
    q3mc_croot_val x (n + 1) j hj.symm
  have hone : (z3.mul (z3.mul x x) x).val (n + 1)
      = Quot.mk (modCong (3 ^ (n + 1))).rel 1 :=
    congrFun (congrArg Subtype.val hx) (n + 1)
  rw [hcube] at hone
  have hdvd : ((3 ^ (n + 1) : Nat) : Int) ∣ (j * j * j - 1) :=
    quot_exact intGrp (modCong (3 ^ (n + 1))) hone
  -- peel: j³−1 = (3(j−1))·(単数)
  rw [int_cube_peel j m hm] at hdvd
  have hpeel : ((3 ^ (n + 1) : Nat) : Int) ∣ (3 * (j - 1)) :=
    q3cu_ppow_dvd (n + 1) hdvd (int_cofactor_coprime m)
  -- 3^{n+1} ∣ 3(j−1) ⟹ 3ⁿ ∣ (j−1)
  have hn1 : ((3 ^ n : Nat) : Int) ∣ (j - 1) := by
    obtain ⟨k, hk⟩ := hpeel
    refine ⟨k, ?_⟩
    have hpow : ((3 ^ (n + 1) : Nat) : Int)
        = ((3 : Nat) : Int) * ((3 ^ n : Nat) : Int) := by
      rw [Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]
    rw [hpow, Int.mul_assoc] at hk
    exact Int.eq_of_mul_eq_mul_left (by omega) hk
  refine ⟨j, ?_, hn1⟩
  -- x.val n = [j]（射影 n+1 → n）
  have hprojn := x.property (show (n : Nat) ≤ n + 1 by omega)
  rw [← hj] at hprojn
  have hpn : Quot.mk (modCong (3 ^ n)).rel j = x.val n := hprojn
  exact hpn.symm

/-- **q3mc-2（★★★）: 実 ℤ₃ 内 立方根一意性** — x³=1 ⟹ x=1。
    q3cu_mu2_complete（平方版）の立方アナログ。cofactor が 3 で割れる分の 1 段損失を
    レベル n+1 の代表 → level n 結論で吸収する（本ファイルの再利用核）。 -/
theorem q3mc_z3_cube_root_one (x : z3.carrier)
    (hx : z3.mul (z3.mul x x) x = z3.one) : x = z3.one := by
  apply Subtype.ext
  funext n
  show x.val n = Quot.mk (modCong (3 ^ n)).rel 1
  cases n with
  | zero =>
    obtain ⟨b, hb⟩ := Quot.exists_rep (x.val 0)
    rw [← hb]
    apply Quot.sound
    show ((3 ^ 0 : Nat) : Int) ∣ (b - 1)
    rw [Nat.pow_zero]
    exact ⟨b - 1, by omega⟩
  | succ m =>
    obtain ⟨j, hj, hdvd⟩ := q3mc_croot_level x hx (m + 1)
    rw [hj]
    apply Quot.sound
    show ((3 ^ (m + 1) : Nat) : Int) ∣ (j - 1)
    exact hdvd

/-! ## q3mc-3: 正則性（3 正則・単数正則）と z3 の代数補題 -/

/-- q3rqThree のレベル値 [3]。 -/
theorem q3rq_three_val (n : Nat) :
    q3rqThree.val n = Quot.mk (modCong (3 ^ n)).rel 3 := by
  show (zmod (3 ^ n)).mul ((zmod (3 ^ n)).mul (Quot.mk (modCong (3 ^ n)).rel 1)
        (Quot.mk (modCong (3 ^ n)).rel 1)) (Quot.mk (modCong (3 ^ n)).rel 1)
    = Quot.mk (modCong (3 ^ n)).rel 3
  apply Quot.sound
  show ((3 ^ n : Nat) : Int) ∣ (1 + 1 + 1 - 3)
  exact ⟨0, by omega⟩

/-- q3rqD = −3 のレベル 1 値 [−3]。 -/
theorem q3rq_D_val1 : q3rqD.val 1 = Quot.mk (modCong (3 ^ 1)).rel (-3) := by
  show (zmod (3 ^ 1)).inv (q3rqThree.val 1) = Quot.mk (modCong (3 ^ 1)).rel (-3)
  rw [q3rq_three_val 1]
  rfl

/-- **q3mc-3a: 3·x = 3 の展開** — z3.mul 3 x = (x+x)+x。 -/
theorem q3mc_three_mul (x : z3.carrier) :
    z3.mul q3rqThree x = z3.add (z3.add x x) x := by
  show z3.mul (z3.add (z3.add z3.one z3.one) z3.one) x = z3.add (z3.add x x) x
  rw [z3.right_distrib (z3.add z3.one z3.one) z3.one x,
    z3.right_distrib z3.one z3.one x, z3.one_mul x]

/-- **q3mc-3b: 3 は正則** — z3.mul 3 y = 0 ⟹ y = 0（3 は零因子でない・レベルシフト）。 -/
theorem q3mc_three_mul_zero (y : z3.carrier)
    (h : z3.mul q3rqThree y = z3.zero) : y = z3.zero := by
  apply Subtype.ext
  funext n
  show y.val n = Quot.mk (modCong (3 ^ n)).rel 0
  cases n with
  | zero =>
    obtain ⟨b, hb⟩ := Quot.exists_rep (y.val 0)
    rw [← hb]
    apply Quot.sound
    show ((3 ^ 0 : Nat) : Int) ∣ (b - 0)
    rw [Nat.pow_zero]
    exact ⟨b, by omega⟩
  | succ m =>
    obtain ⟨r, hr⟩ := Quot.exists_rep (y.val (m + 2))
    have h3y : (z3.mul q3rqThree y).val (m + 2)
        = Quot.mk (modCong (3 ^ (m + 2))).rel (3 * r) := by
      show zmodMul (3 ^ (m + 2)) (q3rqThree.val (m + 2)) (y.val (m + 2)) = _
      rw [q3rq_three_val (m + 2), ← hr]
      rfl
    have hz : (z3.mul q3rqThree y).val (m + 2)
        = Quot.mk (modCong (3 ^ (m + 2))).rel 0 :=
      congrFun (congrArg Subtype.val h) (m + 2)
    rw [h3y] at hz
    have hdvd : ((3 ^ (m + 2) : Nat) : Int) ∣ (3 * r - 0) :=
      quot_exact intGrp (modCong (3 ^ (m + 2))) hz
    have hr1 : ((3 ^ (m + 1) : Nat) : Int) ∣ r := by
      have hdvd2 : ((3 ^ (m + 2) : Nat) : Int) ∣ (3 * r) := by
        obtain ⟨k, hk⟩ := hdvd
        exact ⟨k, by omega⟩
      obtain ⟨k, hk⟩ := hdvd2
      refine ⟨k, ?_⟩
      have hpow : ((3 ^ (m + 2) : Nat) : Int)
          = ((3 : Nat) : Int) * ((3 ^ (m + 1) : Nat) : Int) := by
        rw [Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]
      rw [hpow, Int.mul_assoc] at hk
      exact Int.eq_of_mul_eq_mul_left (by omega) hk
    have hproj := y.property (show (m + 1 : Nat) ≤ m + 2 by omega)
    rw [← hr] at hproj
    have hpn : Quot.mk (modCong (3 ^ (m + 1))).rel r = y.val (m + 1) := hproj
    rw [← hpn]
    apply Quot.sound
    show ((3 ^ (m + 1) : Nat) : Int) ∣ (r - 0)
    obtain ⟨k, hk⟩ := hr1
    exact ⟨k, by omega⟩

/-- **q3mc-3c: 単数は正則** — c 単数, c·x = 0 ⟹ x = 0（明示逆元・choice-free）。 -/
theorem q3mc_unit_regular (c x : z3.carrier) (hc : IsZpUnit 3 c)
    (h : z3.mul c x = z3.zero) : x = z3.zero := by
  have hinv : z3.mul (zpUnitInv 3 isPrime_three c hc) c = z3.one :=
    zpUnitInv_mul 3 isPrime_three c hc
  calc x = z3.mul z3.one x := (z3.one_mul x).symm
    _ = z3.mul (z3.mul (zpUnitInv 3 isPrime_three c hc) c) x := by rw [hinv]
    _ = z3.mul (zpUnitInv 3 isPrime_three c hc) (z3.mul c x) := z3.mul_assoc _ _ _
    _ = z3.mul (zpUnitInv 3 isPrime_three c hc) z3.zero := by rw [h]
    _ = z3.zero := z3.mul_zero _

/-- x + (−y) = 0 ⟹ x = y。 -/
theorem q3mc_eq_of_sub_zero (x y : z3.carrier)
    (h : z3.add x (z3.neg y) = z3.zero) : x = y := by
  have h2 : z3.add (z3.add x (z3.neg y)) y = z3.add z3.zero y := by rw [h]
  rw [z3.add_assoc x (z3.neg y) y, z3.neg_add y, z3.add_zero x, z3.zero_add y] at h2
  exact h2

/-- x + y = 0 ⟹ x = −y。 -/
theorem q3mc_neg_of_add_zero (x y : z3.carrier)
    (h : z3.add x y = z3.zero) : x = z3.neg y := by
  have h2 : z3.add (z3.add x y) (z3.neg y) = z3.add z3.zero (z3.neg y) := by rw [h]
  rw [z3.add_assoc x y (z3.neg y), z3.add_neg y, z3.add_zero x,
    z3.zero_add (z3.neg y)] at h2
  exact h2

/-- **q3mc-3d: 差の平方** (a−b)(a+b) = a²−b²（z3 の環恒等式）。 -/
theorem q3mc_diff_sq (a b : z3.carrier) :
    z3.mul (z3.add a (z3.neg b)) (z3.add a b)
      = z3.add (z3.mul a a) (z3.neg (z3.mul b b)) := by
  rw [z3.left_distrib (z3.add a (z3.neg b)) a b,
    z3.right_distrib a (z3.neg b) a, z3.right_distrib a (z3.neg b) b,
    z3.neg_mul b a, z3.neg_mul b b, z3.mul_comm b a,
    z3.add_assoc (z3.mul a a) (z3.neg (z3.mul a b))
      (z3.add (z3.mul a b) (z3.neg (z3.mul b b))),
    ← z3.add_assoc (z3.neg (z3.mul a b)) (z3.mul a b) (z3.neg (z3.mul b b)),
    z3.neg_add (z3.mul a b), z3.zero_add (z3.neg (z3.mul b b))]

/-! ## q3mc-4: 成分立方方程式（mem_iff の急所） -/

/-- **q3mc-4a: 立方第 2 成分の生形（任意 CRing・D 抽象）** — 4 項を並べ替えて
    (K+K)+(K + D·b³) 形へ（K = a²·b）。 -/
theorem q3mc_cube_snd_raw (R : CRing) (a b D : R.carrier) :
    R.add (R.mul (R.add (R.mul a a) (R.mul D (R.mul b b))) b)
          (R.mul (R.add (R.mul a b) (R.mul b a)) a)
      = R.add (R.add (R.mul (R.mul a a) b) (R.mul (R.mul a a) b))
              (R.add (R.mul (R.mul a a) b) (R.mul D (R.mul (R.mul b b) b))) := by
  rw [R.right_distrib (R.mul a a) (R.mul D (R.mul b b)) b,
    R.right_distrib (R.mul a b) (R.mul b a) a,
    R.mul_assoc D (R.mul b b) b,
    R.mul_assoc a b a, R.mul_assoc b a a,
    R.mul_comm b a, ← R.mul_assoc a a b,
    R.mul_comm b (R.mul a a),
    R.add_comm (R.add (R.mul (R.mul a a) b) (R.mul D (R.mul (R.mul b b) b)))
      (R.add (R.mul (R.mul a a) b) (R.mul (R.mul a a) b))]

/-- **q3mc-4b（★）: 立方第 2 成分の因数分解** — (a,b)³ の第 2 成分 = 3·((a²−b²)·b)。 -/
theorem q3mc_cube_snd (a b : z3.carrier) :
    (q3rqMul (q3rqMul ((a, b) : q3rqCar) (a, b)) (a, b)).2
      = z3.mul q3rqThree
          (z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b) := by
  show z3.add (z3.mul (z3.add (z3.mul a a) (z3.mul q3rqD (z3.mul b b))) b)
              (z3.mul (z3.add (z3.mul a b) (z3.mul b a)) a)
    = z3.mul q3rqThree
        (z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b)
  rw [q3mc_cube_snd_raw z3 a b q3rqD,
    q3rq_D_eq, z3.neg_mul q3rqThree (z3.mul (z3.mul b b) b),
    z3.right_distrib (z3.mul a a) (z3.neg (z3.mul b b)) b,
    z3.neg_mul (z3.mul b b) b,
    z3.left_distrib q3rqThree (z3.mul (z3.mul a a) b)
      (z3.neg (z3.mul (z3.mul b b) b)),
    z3.mul_neg q3rqThree (z3.mul (z3.mul b b) b),
    q3mc_three_mul (z3.mul (z3.mul a a) b),
    z3.add_assoc (z3.add (z3.mul (z3.mul a a) b) (z3.mul (z3.mul a a) b))
      (z3.mul (z3.mul a a) b)
      (z3.neg (z3.mul q3rqThree (z3.mul (z3.mul b b) b)))]

/-! ## q3mc-5: レベル 1 値の補題（単数判定用） -/

/-- (x+y) のレベル 1 値。 -/
theorem q3mc_add_val1 (x y : z3.carrier) (x1 y1 : Int)
    (hx : x.val 1 = Quot.mk (modCong (3 ^ 1)).rel x1)
    (hy : y.val 1 = Quot.mk (modCong (3 ^ 1)).rel y1) :
    (z3.add x y).val 1 = Quot.mk (modCong (3 ^ 1)).rel (x1 + y1) := by
  show (zmod (3 ^ 1)).mul (x.val 1) (y.val 1) = _
  rw [hx, hy]
  rfl

/-- (−x) のレベル 1 値。 -/
theorem q3mc_neg_val1 (x : z3.carrier) (x1 : Int)
    (hx : x.val 1 = Quot.mk (modCong (3 ^ 1)).rel x1) :
    (z3.neg x).val 1 = Quot.mk (modCong (3 ^ 1)).rel (-x1) := by
  show (zmod (3 ^ 1)).inv (x.val 1) = _
  rw [hx]
  rfl

/-- (x·y) のレベル 1 値。 -/
theorem q3mc_mul_val1 (x y : z3.carrier) (x1 y1 : Int)
    (hx : x.val 1 = Quot.mk (modCong (3 ^ 1)).rel x1)
    (hy : y.val 1 = Quot.mk (modCong (3 ^ 1)).rel y1) :
    (z3.mul x y).val 1 = Quot.mk (modCong (3 ^ 1)).rel (x1 * y1) := by
  show zmodMul (3 ^ 1) (x.val 1) (y.val 1) = _
  rw [hx, hy]
  rfl

/-- ノルムのレベル 1 値 [a₁²+3b₁²]（−(−3·b₁²) 形）。 -/
theorem q3mc_norm_lev1 (a b : z3.carrier) (a1 b1 : Int)
    (ha : a.val 1 = Quot.mk (modCong (3 ^ 1)).rel a1)
    (hb : b.val 1 = Quot.mk (modCong (3 ^ 1)).rel b1) :
    (q3rqNorm ((a, b) : q3rqCar)).val 1
      = Quot.mk (modCong (3 ^ 1)).rel (a1 * a1 + (-((-3) * (b1 * b1)))) := by
  show (z3.add (z3.mul a a) (z3.neg (z3.mul q3rqD (z3.mul b b)))).val 1 = _
  rw [q3mc_add_val1 (z3.mul a a) (z3.neg (z3.mul q3rqD (z3.mul b b)))
        (a1 * a1) (-((-3) * (b1 * b1)))
      (q3mc_mul_val1 a a a1 a1 ha ha)
      (q3mc_neg_val1 (z3.mul q3rqD (z3.mul b b)) ((-3) * (b1 * b1))
        (q3mc_mul_val1 q3rqD (z3.mul b b) (-3) (b1 * b1) q3rq_D_val1
          (q3mc_mul_val1 b b b1 b1 hb hb)))]

/-- **q3mc-5a: a=u.1 は ℤ₃ 単数** — N(u)=1 の レベル 1（3∤a₁）。 -/
theorem q3mc_a_unit (a b : z3.carrier) (a1 b1 : Int)
    (ha : a.val 1 = Quot.mk (modCong (3 ^ 1)).rel a1)
    (hb : b.val 1 = Quot.mk (modCong (3 ^ 1)).rel b1)
    (hnorm : q3rqNorm ((a, b) : q3rqCar) = z3.one) :
    ¬ ((3 : Nat) : Int) ∣ a1 := by
  have hn1 : (q3rqNorm ((a, b) : q3rqCar)).val 1
      = Quot.mk (modCong (3 ^ 1)).rel (a1 * a1 + (-((-3) * (b1 * b1)))) :=
    q3mc_norm_lev1 a b a1 b1 ha hb
  have hone : (q3rqNorm ((a, b) : q3rqCar)).val 1
      = Quot.mk (modCong (3 ^ 1)).rel 1 := by rw [hnorm]; rfl
  rw [hn1] at hone
  have hdvd := quot_exact intGrp (modCong (3 ^ 1)) hone
  rw [Nat.pow_one] at hdvd
  intro h3a
  obtain ⟨k, hk⟩ := h3a
  have h3aa : ((3 : Nat) : Int) ∣ (a1 * a1) := ⟨k * a1, by rw [← Int.mul_assoc, ← hk]⟩
  obtain ⟨c1, hc1⟩ := h3aa
  obtain ⟨c2, hc2⟩ := hdvd
  omega

/-- **q3mc-5b: N(u)=1**（N(u)³=N(u³)=N(1)=1 と ℤ₃ 立方根一意性）。 -/
theorem q3mc_norm_cube_one (u : q3rqCar)
    (hu : q3rqMul (q3rqMul u u) u = q3rqOne) :
    q3rqNorm u = z3.one := by
  apply q3mc_z3_cube_root_one
  rw [← q3rq_norm_mul u u, ← q3rq_norm_mul (q3rqMul u u) u, hu, q3rq_norm_one]

/-! ## q3mc-6: 積の立方 (xy)³ = x³y³ -/

/-- **q3mc-6a: (xy)³ = x³·y³**（可換環・4 因子入替 2 回）。 -/
theorem q3rq_cube_mul (x y : q3rqCar) :
    q3rqMul (q3rqMul (q3rqMul x y) (q3rqMul x y)) (q3rqMul x y)
      = q3rqMul (q3rqMul (q3rqMul x x) x) (q3rqMul (q3rqMul y y) y) := by
  rw [q3rq_mmmc x y x y, q3rq_mmmc (q3rqMul x x) (q3rqMul y y) x y]

/-! ## q3mc-7: 3 枝（b=0・a=b・a=−b）の μ₃ 帰着 -/

/-- **q3mc-7a: b=0 枝** — u=(a,0), u³=1 ⟹ a³=1 ⟹ a=1 ⟹ u=1。 -/
theorem q3mc_mu3_of_b_zero (a b : z3.carrier)
    (hu : q3rqMul (q3rqMul ((a, b) : q3rqCar) (a, b)) (a, b) = q3rqOne)
    (hb : b = z3.zero) : q3rqMu3 ((a, b) : q3rqCar) := by
  subst hb
  have hcube1 : z3.mul (z3.mul a a) a = z3.one := by
    have h := congrArg Prod.fst hu
    rw [q3rq_pair_mul a a, q3rq_pair_mul (z3.mul a a) a] at h
    exact h
  have ha1 : a = z3.one := q3mc_z3_cube_root_one a hcube1
  left
  show ((a, z3.zero) : q3rqCar) = q3rqOne
  rw [ha1]
  rfl

/-- **q3mc-7b: a=b 枝** — u=(a,a), u·ζ₃ の b 成分が消え (u·ζ₃)³=1 ⟹ u·ζ₃=1 ⟹ u=ζ₃²。 -/
theorem q3mc_mu3_of_a_eq_b (a b : z3.carrier)
    (hu : q3rqMul (q3rqMul ((a, b) : q3rqCar) (a, b)) (a, b) = q3rqOne)
    (hab : a = b) : q3rqMu3 ((a, b) : q3rqCar) := by
  subst hab
  -- w := u·ζ₃、w.2 = 0
  have hw2 : (q3rqMul ((a, a) : q3rqCar) q3rqZeta).2 = z3.zero := by
    show z3.add (z3.mul a q3rqHalf) (z3.mul a (z3.neg q3rqHalf)) = z3.zero
    rw [z3.mul_neg a q3rqHalf, z3.add_neg (z3.mul a q3rqHalf)]
  have weq : q3rqMul ((a, a) : q3rqCar) q3rqZeta
      = ((q3rqMul ((a, a) : q3rqCar) q3rqZeta).1, z3.zero) := q3rq_ext rfl hw2
  generalize hz : (q3rqMul ((a, a) : q3rqCar) q3rqZeta).1 = z at weq
  -- w³ = 1
  have hcube_w : q3rqMul (q3rqMul (q3rqMul ((a, a) : q3rqCar) q3rqZeta)
        (q3rqMul ((a, a) : q3rqCar) q3rqZeta)) (q3rqMul ((a, a) : q3rqCar) q3rqZeta)
      = q3rqOne := by
    rw [q3rq_cube_mul ((a, a) : q3rqCar) q3rqZeta, hu, q3rq_zeta_cube]
    exact q3rq_one_mul q3rqOne
  rw [weq] at hcube_w
  -- (z,0)³ = (z³, 0) = 1 ⟹ z³ = 1
  have hz3 : z3.mul (z3.mul z z) z = z3.one := by
    have h := congrArg Prod.fst hcube_w
    rw [q3rq_pair_mul z z, q3rq_pair_mul (z3.mul z z) z] at h
    exact h
  have hz1 : z = z3.one := q3mc_z3_cube_root_one z hz3
  rw [hz1] at weq
  -- weq : u·ζ₃ = (1,0) = 1；u = ζ₃²
  have hw1 : q3rqMul ((a, a) : q3rqCar) q3rqZeta = q3rqOne := weq
  right; right
  show ((a, a) : q3rqCar) = q3rqZetaSq
  calc ((a, a) : q3rqCar)
      = q3rqMul (a, a) q3rqOne := (q3rq_mul_one (a, a)).symm
    _ = q3rqMul (a, a) (q3rqMul q3rqZeta q3rqZetaSq) := by rw [q3rq_zeta_mul_zetaSq]
    _ = q3rqMul (q3rqMul (a, a) q3rqZeta) q3rqZetaSq :=
        (q3rqRing.mul_assoc (a, a) q3rqZeta q3rqZetaSq).symm
    _ = q3rqMul q3rqOne q3rqZetaSq := by rw [hw1]
    _ = q3rqZetaSq := q3rq_one_mul q3rqZetaSq

/-- **q3mc-7c: a=−b 枝** — u=(−b,b), u·ζ₃² の b 成分が消え (u·ζ₃²)³=1 ⟹ u·ζ₃²=1 ⟹ u=ζ₃。 -/
theorem q3mc_mu3_of_a_eq_neg_b (a b : z3.carrier)
    (hu : q3rqMul (q3rqMul ((a, b) : q3rqCar) (a, b)) (a, b) = q3rqOne)
    (hab : a = z3.neg b) : q3rqMu3 ((a, b) : q3rqCar) := by
  subst hab
  have hz2 : q3rqZetaSq = ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar) :=
    q3rq_zeta_sq_eq
  -- w := u·ζ₃²、w.2 = 0
  have hw2 : (q3rqMul ((z3.neg b, b) : q3rqCar) q3rqZetaSq).2 = z3.zero := by
    rw [hz2]
    show z3.add (z3.mul (z3.neg b) (z3.neg q3rqHalf)) (z3.mul b (z3.neg q3rqHalf))
      = z3.zero
    rw [z3.neg_mul b (z3.neg q3rqHalf), z3.mul_neg b q3rqHalf, z3.neg_neg,
      z3.add_neg (z3.mul b q3rqHalf)]
  have weq : q3rqMul ((z3.neg b, b) : q3rqCar) q3rqZetaSq
      = ((q3rqMul ((z3.neg b, b) : q3rqCar) q3rqZetaSq).1, z3.zero) :=
    q3rq_ext rfl hw2
  generalize hz : (q3rqMul ((z3.neg b, b) : q3rqCar) q3rqZetaSq).1 = z at weq
  have hcube_zsq : q3rqMul (q3rqMul q3rqZetaSq q3rqZetaSq) q3rqZetaSq = q3rqOne := by
    rw [q3rq_zetaSq_mul_zetaSq]
    exact q3rq_zeta_mul_zetaSq
  have hcube_w : q3rqMul (q3rqMul (q3rqMul ((z3.neg b, b) : q3rqCar) q3rqZetaSq)
        (q3rqMul ((z3.neg b, b) : q3rqCar) q3rqZetaSq))
        (q3rqMul ((z3.neg b, b) : q3rqCar) q3rqZetaSq)
      = q3rqOne := by
    rw [q3rq_cube_mul ((z3.neg b, b) : q3rqCar) q3rqZetaSq, hu, hcube_zsq]
    exact q3rq_one_mul q3rqOne
  rw [weq] at hcube_w
  have hz3 : z3.mul (z3.mul z z) z = z3.one := by
    have h := congrArg Prod.fst hcube_w
    rw [q3rq_pair_mul z z, q3rq_pair_mul (z3.mul z z) z] at h
    exact h
  have hz1 : z = z3.one := q3mc_z3_cube_root_one z hz3
  rw [hz1] at weq
  have hw1 : q3rqMul ((z3.neg b, b) : q3rqCar) q3rqZetaSq = q3rqOne := weq
  right; left
  show ((z3.neg b, b) : q3rqCar) = q3rqZeta
  calc ((z3.neg b, b) : q3rqCar)
      = q3rqMul (z3.neg b, b) q3rqOne := (q3rq_mul_one (z3.neg b, b)).symm
    _ = q3rqMul (z3.neg b, b) (q3rqMul q3rqZetaSq q3rqZeta) := by
        rw [← q3rq_zeta_cube]; rfl
    _ = q3rqMul (q3rqMul (z3.neg b, b) q3rqZetaSq) q3rqZeta :=
        (q3rqRing.mul_assoc (z3.neg b, b) q3rqZetaSq q3rqZeta).symm
    _ = q3rqMul q3rqOne q3rqZeta := by rw [hw1]
    _ = q3rqZeta := q3rq_one_mul q3rqZeta

/-! ## q3mc-8: b 単数の枝（a²=b² ⟹ a=b ∨ a=−b） -/

/-- **q3mc-8a: b 単数の枝** — b∈ℤ₃^×, (a²−b²)·b=0 ⟹ a²=b² ⟹ (a−b)(a+b)=0；
    a−b, a+b の和 2a が単数ゆえレベル 1 で一方が単数（正則）となり消去して a=b ∨ a=−b。 -/
theorem q3mc_mu3_b_unit (a b : z3.carrier) (a1 b1 : Int)
    (ha1 : Quot.mk (modCong (3 ^ 1)).rel a1 = a.val 1)
    (hb1 : Quot.mk (modCong (3 ^ 1)).rel b1 = b.val 1)
    (h3a : ¬ ((3 : Nat) : Int) ∣ a1) (h3b : ¬ ((3 : Nat) : Int) ∣ b1)
    (hu : q3rqMul (q3rqMul ((a, b) : q3rqCar) (a, b)) (a, b) = q3rqOne)
    (hF : z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b = z3.zero) :
    q3rqMu3 ((a, b) : q3rqCar) := by
  -- b は単数 ⟹ 正則
  have hbunit : IsZpUnit 3 b := ⟨b1, hb1.symm, h3b⟩
  have hF' : z3.mul b (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) = z3.zero := by
    rw [z3.mul_comm b (z3.add (z3.mul a a) (z3.neg (z3.mul b b)))]; exact hF
  have hX0 : z3.add (z3.mul a a) (z3.neg (z3.mul b b)) = z3.zero :=
    q3mc_unit_regular b _ hbunit hF'
  -- (a−b)(a+b) = 0
  have hprod : z3.mul (z3.add a (z3.neg b)) (z3.add a b) = z3.zero := by
    rw [q3mc_diff_sq a b]; exact hX0
  -- a−b, a+b のレベル 1 で一方が単数
  -- level-1 で a+b が単数か否かを構成的に決定（choice-free）
  cases (inferInstance : Decidable (((3 : Nat) : Int) ∣ (a1 + b1))) with
  | isFalse hp =>
    -- a+b 単数 ⟹ a−b = 0 ⟹ a = b
    have habunit : IsZpUnit 3 (z3.add a b) :=
      ⟨a1 + b1, q3mc_add_val1 a b a1 b1 ha1.symm hb1.symm, hp⟩
    have hprod' : z3.mul (z3.add a b) (z3.add a (z3.neg b)) = z3.zero := by
      rw [z3.mul_comm (z3.add a b) (z3.add a (z3.neg b))]; exact hprod
    have hab0 : z3.add a (z3.neg b) = z3.zero :=
      q3mc_unit_regular (z3.add a b) _ habunit hprod'
    exact q3mc_mu3_of_a_eq_b a b hu (q3mc_eq_of_sub_zero a b hab0)
  | isTrue hp =>
    -- 3∣(a1+b1) と 3∤a1 ⟹ 3∤(a1−b1) ⟹ a−b 単数 ⟹ a+b = 0 ⟹ a = −b
    have hm : ¬ ((3 : Nat) : Int) ∣ (a1 + (-b1)) := by omega
    have hambunit : IsZpUnit 3 (z3.add a (z3.neg b)) :=
      ⟨a1 + (-b1),
        q3mc_add_val1 a (z3.neg b) a1 (-b1) ha1.symm
          (q3mc_neg_val1 b b1 hb1.symm), hm⟩
    have hab0 : z3.add a b = z3.zero :=
      q3mc_unit_regular (z3.add a (z3.neg b)) _ hambunit hprod
    exact q3mc_mu3_of_a_eq_neg_b a b hu (q3mc_neg_of_add_zero a b hab0)

/-! ## q3mc-9（★★★）: U₂ 内 μ₃ 完全性と capstone -/

/-- **q3mc-9a（★★★）: μ₃ 完全性** — U₂ 内 u³=1 ⟹ u ∈ μ₃ = {1, ζ₃, ζ₃²}。
    成分方程式 3b(a²−b²)=0 から 3 正則で b(a²−b²)=0；a=u.1 は N(u)=1 ゆえ ℤ₃ 単数
    （3∤a₁）。level-1 剰余の omega 決定で「b 単数か a²−b² 単数か」を choice-free に選び、
    単数正則で b=0 / a=b / a=−b の枝へ確定させる（域の因数分解の非構成性を単数消去で回避）。 -/
theorem q3mc_mu3_complete (u : q3rqCar)
    (hu : q3rqMul (q3rqMul u u) u = q3rqOne) : q3rqMu3 u := by
  obtain ⟨a, b⟩ := u
  have hsnd0 : (q3rqMul (q3rqMul ((a, b) : q3rqCar) (a, b)) (a, b)).2 = z3.zero :=
    congrArg Prod.snd hu
  rw [q3mc_cube_snd a b] at hsnd0
  have hF : z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b = z3.zero :=
    q3mc_three_mul_zero _ hsnd0
  obtain ⟨a1, ha1⟩ := Quot.exists_rep (a.val 1)
  obtain ⟨b1, hb1⟩ := Quot.exists_rep (b.val 1)
  have hnorm : q3rqNorm ((a, b) : q3rqCar) = z3.one := q3mc_norm_cube_one (a, b) hu
  have h3a : ¬ ((3 : Nat) : Int) ∣ a1 := q3mc_a_unit a b a1 b1 ha1.symm hb1.symm hnorm
  -- b が単数か否かを構成的に決定（choice-free）
  cases (inferInstance : Decidable (((3 : Nat) : Int) ∣ b1)) with
  | isTrue hb0 =>
    -- 3 ∣ b1: a²−b² 単数 ⟹ b = 0
    obtain ⟨k, hk⟩ := hb0
    have h3bb : ((3 : Nat) : Int) ∣ (b1 * b1) :=
      ⟨k * b1, by rw [← Int.mul_assoc, ← hk]⟩
    have h3aa : ¬ ((3 : Nat) : Int) ∣ (a1 * a1) :=
      fun h => h3a (euclid_int 3 isPrime_three h h3a)
    have hXunit : ¬ ((3 : Nat) : Int) ∣ (a1 * a1 + (-(b1 * b1))) := by
      intro h
      obtain ⟨d, hd⟩ := h
      obtain ⟨e, he⟩ := h3bb
      exact h3aa ⟨d + e, by omega⟩
    have hXval1 : (z3.add (z3.mul a a) (z3.neg (z3.mul b b))).val 1
        = Quot.mk (modCong (3 ^ 1)).rel (a1 * a1 + (-(b1 * b1))) :=
      q3mc_add_val1 (z3.mul a a) (z3.neg (z3.mul b b)) (a1 * a1) (-(b1 * b1))
        (q3mc_mul_val1 a a a1 a1 ha1.symm ha1.symm)
        (q3mc_neg_val1 (z3.mul b b) (b1 * b1)
          (q3mc_mul_val1 b b b1 b1 hb1.symm hb1.symm))
    have hXunitFull : IsZpUnit 3 (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) :=
      ⟨a1 * a1 + (-(b1 * b1)), hXval1, hXunit⟩
    have hbz : b = z3.zero := q3mc_unit_regular _ b hXunitFull hF
    exact q3mc_mu3_of_b_zero a b hu hbz
  | isFalse h3b =>
    exact q3mc_mu3_b_unit a b a1 b1 ha1 hb1 h3a h3b hu hF

/-- **q3mc-9b: μ₃ 完全性データ** — 実 ℤ₃ 立方根一意性・U₂ 内 μ₃ 完全性の束ね。 -/
structure Q3Mu3CompletenessData where
  /-- ℤ₃ 立方根一意性 x³=1 ⟹ x=1。 -/
  z3_cube_root_one : ∀ x : z3.carrier,
    z3.mul (z3.mul x x) x = z3.one → x = z3.one
  /-- 立方第 2 成分の因数分解（mem_iff の急所）。 -/
  cube_snd : ∀ a b : z3.carrier,
    (q3rqMul (q3rqMul ((a, b) : q3rqCar) (a, b)) (a, b)).2
      = z3.mul q3rqThree
          (z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b)
  /-- U₂ 内 μ₃ 完全性 u³=1 ⟹ u∈μ₃。 -/
  mu3_complete : ∀ u : q3rqCar,
    q3rqMul (q3rqMul u u) u = q3rqOne → q3rqMu3 u

/-- **q3mc-9c: 見出し実例** — 実 O_{L₂}=ℤ₃[√−3] 内の μ₃ 完全性。 -/
def q3mc_data : Q3Mu3CompletenessData where
  z3_cube_root_one := q3mc_z3_cube_root_one
  cube_snd := q3mc_cube_snd
  mu3_complete := q3mc_mu3_complete

/-- **q3mc-9d: μ₃ 完全性の存在**（実 ℤ₃ 上・L₂=ℚ₃(ζ₃)）。 -/
theorem q3mc_exists : Nonempty Q3Mu3CompletenessData := ⟨q3mc_data⟩

end IUT
