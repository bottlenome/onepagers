/-
  IUT/Q3KummerCubeIdent.lean — F-wild level-9 μ₉-completeness campaign / Module A
    （実巡回 3 次 Kummer 拡大 M = ℚ₃(ζ₉) = q3kRing 上の恒等式＋正則性パック）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**（骨格・模型・代理でなく、R1/R2a で
     建てた**実** O_{L₂}=q3rqRing・実 O_M=q3kRing の上に、level-9 μ₉ 完全性核が消費する
     本物の恒等式（ねじれ 3 次冪 x³ の 3 成分展開 E0/E1/E2・3 次ノルムとの整合）と
     本物の正則性（3・9・λ・ζ₃−1・π₉=ζ₉−1・単数 の非零因子性）をゼロから積む。
     主語は実 q3rq/q3k の元——toy 模型（m202fVol 型・Bool 軌道・surrogate 群）を一切
     使わない。）

  complete_pct 影響: **F-wild (ii)（μ₉ 完全性 / level-9 kill）の急所支援・foundation**。
  本モジュール単体は何も kill せず（恒等式＋正則性のみ）、**単体では complete_pct 丸め
  値 0 前進（本物基盤の先行建設）**。表示が動くのは後続の level-9 kill（Module B q9c）で
  あり、本ファイルはその消費される本物入力を先に建てる。「complete_pct 0 前進（骨格でなく
  本物基盤の先行建設）」と正直申告する。

  内容（§6.1 Module A = A1–A4）:
   * A1 q9ci_cube_0/_1/_2  — ねじれ 3 次冪 x³ = (x·x)·x の 3 成分恒等式（E0/E1/E2）
       E0 = a³+ζ₃b³+ζ₃²c³+6ζ₃abc・E1 = 3(a²b+ζ₃ac²+ζ₃b²c)・E2 = 3(a²c+ab²+ζ₃bc²)
       （6ζ₃abc・3(...) は honest に反復和で明示；抽象 CRing raw 補題を specialize）
   * A2 q9ci_three_reg_L2 / q9ci_nine_reg / q9ci_lambda_reg / q9ci_unit_reg_L2 /
       q9ci_unit_reg_M / q9ci_zeta_norm3 / q9ci_zeta_sub_one_reg / q9ci_pi9_reg
       — 正則性パック（3/9/λ/単数/ζ₃−1/π₉=ζ₉−1 の非零因子性；π₉ は cofactor
         (Y−1)(Y²+Y+1)=Y³−1=embed(ζ₃−1) と embed(λ·単数) 正則で帰着）
   * A3 q9ci_no_cbrt_zeta / q9ci_no_cbrt_zetaSq — O_{L₂} 内に ζ₃・ζ₃² の 3 乗根なし
       （立方第 2 成分 ≡0 mod 3 vs ζ₃ の第 2 成分 h＝単数 の矛盾）
   * A4 q9ci_norm_sub — N(x) = E0 − 9ζ₃abc（3 次ノルムと冪展開の整合）

  正直な限定（§4 規約により消さない・弱化しない・R1/R2a/q3k 継承の上に追記のみ）:
  1. **恒等式＋正則性のみ**（完全性・kill は本ファイルに無い——それは Module B q9c）。
     μ₉ 完全性・level-9 テータ群・剛性は後続。本ファイルは何も殺さない。
  2. q3k/q3rq の正直限定を継承（O_M と M^× のみ・体化なし・σ を超える Galois ゼロ・
     実テータ関数ゼロ・π₁ 同定ゼロ・tmzLimit 比較橋なし・兄弟担体）。
  3. 正則性は**零因子でない**の代数的言明のみ（付値・位相・完備化は範囲外）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3KummerCubic
import IUT.Q3Mu3Completeness

namespace IUT

/-! ## q9ci-0: スカラー橋（3 = 1+1+1 と q3kThree 展開） -/

/-- 3 = (1+1)+1（対）は q3rqThreeElt = (3,0) に一致。 -/
theorem q9ci_three_pair :
    q3rqAdd (q3rqAdd q3rqOne q3rqOne) q3rqOne = q3rqThreeElt := by
  apply q3rq_ext
  · rfl
  · show z3.add (z3.add z3.zero z3.zero) z3.zero = z3.zero
    rw [z3.add_zero, z3.add_zero]

/-- q3kThree·K = K+(K+K)（右分配 + 1·K=K）。 -/
theorem q9ci_three_mul (K : q3rqCar) :
    q3rqMul q3kThree K = q3rqAdd K (q3rqAdd K K) := by
  show q3rqRing.mul (q3rqRing.add q3rqRing.one (q3rqRing.add q3rqRing.one q3rqRing.one)) K
      = q3rqRing.add K (q3rqRing.add K K)
  rw [q3rqRing.right_distrib q3rqRing.one (q3rqRing.add q3rqRing.one q3rqRing.one) K,
      q3rqRing.right_distrib q3rqRing.one q3rqRing.one K,
      q3rqRing.one_mul K]

/-! ## q9ci-1（A1）: ねじれ 3 次冪 x³ の 3 成分恒等式（抽象 raw + specialize） -/

/-- 加法隣接入替（E0 用）。 -/
theorem q9ci_cube0_add_swap (R : CRing) (u v w : R.carrier) :
    R.add u (R.add v w) = R.add v (R.add u w) := by
  rw [← R.add_assoc u v w, R.add_comm u v, R.add_assoc v u w]

/-- 9 項順列（E0 用・分配形 → 標準形）。 -/
theorem q9ci_cube0_addperm (R : CRing) (p q r s t u v w x : R.carrier) :
    R.add (R.add p (R.add s t))
      (R.add (R.add (R.add u v) r) (R.add (R.add w q) x))
    = R.add (R.add (R.add p q) r)
      (R.add (R.add (R.add (R.add (R.add s t) u) v) w) x) := by
  rw [R.add_assoc p (R.add s t) (R.add (R.add (R.add u v) r) (R.add (R.add w q) x)),
      R.add_assoc s t (R.add (R.add (R.add u v) r) (R.add (R.add w q) x)),
      R.add_assoc (R.add u v) r (R.add (R.add w q) x),
      R.add_assoc u v (R.add r (R.add (R.add w q) x)),
      R.add_assoc w q x,
      q9ci_cube0_add_swap R w q x,
      q9ci_cube0_add_swap R r q (R.add w x),
      q9ci_cube0_add_swap R v q (R.add r (R.add w x)),
      q9ci_cube0_add_swap R u q (R.add v (R.add r (R.add w x))),
      q9ci_cube0_add_swap R t q (R.add u (R.add v (R.add r (R.add w x)))),
      q9ci_cube0_add_swap R s q (R.add t (R.add u (R.add v (R.add r (R.add w x))))),
      q9ci_cube0_add_swap R v r (R.add w x),
      q9ci_cube0_add_swap R u r (R.add v (R.add w x)),
      q9ci_cube0_add_swap R t r (R.add u (R.add v (R.add w x))),
      q9ci_cube0_add_swap R s r (R.add t (R.add u (R.add v (R.add w x)))),
      R.add_assoc (R.add p q) r (R.add (R.add (R.add (R.add (R.add s t) u) v) w) x),
      R.add_assoc p q (R.add r (R.add (R.add (R.add (R.add (R.add s t) u) v) w) x)),
      R.add_assoc (R.add (R.add (R.add s t) u) v) w x,
      R.add_assoc (R.add (R.add s t) u) v (R.add w x),
      R.add_assoc (R.add s t) u (R.add v (R.add w x)),
      R.add_assoc s t (R.add u (R.add v (R.add w x)))]

/-- **A1 raw E0**: x³ の定数成分（抽象 CRing・6ζ₃abc は反復和で明示）。 -/
theorem q9ci_cube0_raw (R : CRing) (a b c d : R.carrier) :
    R.add
      (R.mul
        (R.add (R.mul a a)
          (R.mul d (R.add (R.mul b c) (R.mul c b))))
        a)
      (R.mul d
        (R.add
          (R.mul
            (R.add (R.add (R.mul a b) (R.mul b a)) (R.mul d (R.mul c c)))
            c)
          (R.mul
            (R.add (R.add (R.mul a c) (R.mul b b)) (R.mul c a))
            b)))
    =
    R.add
      (R.add
        (R.add (R.mul (R.mul a a) a) (R.mul d (R.mul (R.mul b b) b)))
        (R.mul (R.mul d d) (R.mul (R.mul c c) c)))
      (R.add
        (R.add
          (R.add
            (R.add
              (R.add (R.mul d (R.mul a (R.mul b c))) (R.mul d (R.mul a (R.mul b c))))
              (R.mul d (R.mul a (R.mul b c))))
            (R.mul d (R.mul a (R.mul b c))))
          (R.mul d (R.mul a (R.mul b c))))
        (R.mul d (R.mul a (R.mul b c)))) := by
  have hM1 : R.mul (R.mul d (R.mul b c)) a = R.mul d (R.mul a (R.mul b c)) := by
    rw [R.mul_assoc d (R.mul b c) a, R.mul_comm (R.mul b c) a]
  have hM2 : R.mul (R.mul d (R.mul c b)) a = R.mul d (R.mul a (R.mul b c)) := by
    rw [R.mul_assoc d (R.mul c b) a, R.mul_comm (R.mul c b) a, R.mul_comm c b]
  have h4 : R.mul d (R.mul (R.mul a b) c) = R.mul d (R.mul a (R.mul b c)) := by
    rw [R.mul_assoc a b c]
  have h5 : R.mul d (R.mul (R.mul b a) c) = R.mul d (R.mul a (R.mul b c)) := by
    rw [R.mul_comm b a, R.mul_assoc a b c]
  have h7 : R.mul d (R.mul (R.mul a c) b) = R.mul d (R.mul a (R.mul b c)) := by
    rw [R.mul_assoc a c b, R.mul_comm c b]
  have h9 : R.mul d (R.mul (R.mul c a) b) = R.mul d (R.mul a (R.mul b c)) := by
    rw [R.mul_comm c a, R.mul_assoc a c b, R.mul_comm c b]
  have h6 : R.mul d (R.mul (R.mul d (R.mul c c)) c)
      = R.mul (R.mul d d) (R.mul (R.mul c c) c) := by
    rw [R.mul_assoc d (R.mul c c) c, ← R.mul_assoc d d (R.mul (R.mul c c) c)]
  rw [R.left_distrib d (R.mul b c) (R.mul c b),
      R.right_distrib (R.mul a a) (R.add (R.mul d (R.mul b c)) (R.mul d (R.mul c b))) a,
      R.right_distrib (R.mul d (R.mul b c)) (R.mul d (R.mul c b)) a,
      R.right_distrib (R.add (R.mul a b) (R.mul b a)) (R.mul d (R.mul c c)) c,
      R.right_distrib (R.mul a b) (R.mul b a) c,
      R.right_distrib (R.add (R.mul a c) (R.mul b b)) (R.mul c a) b,
      R.right_distrib (R.mul a c) (R.mul b b) b,
      R.left_distrib d
        (R.add (R.add (R.mul (R.mul a b) c) (R.mul (R.mul b a) c)) (R.mul (R.mul d (R.mul c c)) c))
        (R.add (R.add (R.mul (R.mul a c) b) (R.mul (R.mul b b) b)) (R.mul (R.mul c a) b)),
      R.left_distrib d (R.add (R.mul (R.mul a b) c) (R.mul (R.mul b a) c)) (R.mul (R.mul d (R.mul c c)) c),
      R.left_distrib d (R.mul (R.mul a b) c) (R.mul (R.mul b a) c),
      R.left_distrib d (R.add (R.mul (R.mul a c) b) (R.mul (R.mul b b) b)) (R.mul (R.mul c a) b),
      R.left_distrib d (R.mul (R.mul a c) b) (R.mul (R.mul b b) b),
      hM1, hM2, h4, h5, h7, h9, h6]
  exact q9ci_cube0_addperm R (R.mul (R.mul a a) a) (R.mul d (R.mul (R.mul b b) b))
    (R.mul (R.mul d d) (R.mul (R.mul c c) c)) (R.mul d (R.mul a (R.mul b c)))
    (R.mul d (R.mul a (R.mul b c))) (R.mul d (R.mul a (R.mul b c)))
    (R.mul d (R.mul a (R.mul b c))) (R.mul d (R.mul a (R.mul b c)))
    (R.mul d (R.mul a (R.mul b c)))

/-- 加法隣接入替（E1 用）。 -/
theorem q9ci_cube1_add_swap (R : CRing) (u v w : R.carrier) :
    R.add u (R.add v w) = R.add v (R.add u w) := by
  rw [← R.add_assoc u v w, R.add_comm u v, R.add_assoc v u w]

/-- 9 項順列（E1 用・3P+3Q+3W → S+(S+S)）。 -/
theorem q9ci_cube1_add_perm (R : CRing) (P Q W : R.carrier) :
    R.add (R.add (R.add P (R.add W W)) (R.add (R.add P P) Q)) (R.add (R.add Q W) Q)
    = R.add (R.add (R.add P Q) W)
        (R.add (R.add (R.add P Q) W) (R.add (R.add P Q) W)) := by
  have hL : R.add (R.add (R.add P (R.add W W)) (R.add (R.add P P) Q)) (R.add (R.add Q W) Q)
      = R.add P (R.add P (R.add P (R.add Q (R.add Q (R.add Q (R.add W (R.add W W))))))) := by
    rw [R.add_assoc (R.add P (R.add W W)) (R.add (R.add P P) Q) (R.add (R.add Q W) Q),
        R.add_assoc P (R.add W W) (R.add (R.add (R.add P P) Q) (R.add (R.add Q W) Q)),
        R.add_assoc W W (R.add (R.add (R.add P P) Q) (R.add (R.add Q W) Q)),
        R.add_assoc (R.add P P) Q (R.add (R.add Q W) Q),
        R.add_assoc P P (R.add Q (R.add (R.add Q W) Q)),
        R.add_assoc Q W Q,
        q9ci_cube1_add_swap R W P (R.add P (R.add Q (R.add Q (R.add W Q)))),
        q9ci_cube1_add_swap R W P (R.add Q (R.add Q (R.add W Q))),
        q9ci_cube1_add_swap R W Q (R.add Q (R.add W Q)),
        q9ci_cube1_add_swap R W Q (R.add W Q),
        R.add_comm W Q,
        q9ci_cube1_add_swap R W P (R.add P (R.add Q (R.add Q (R.add W (R.add Q W))))),
        q9ci_cube1_add_swap R W P (R.add Q (R.add Q (R.add W (R.add Q W)))),
        q9ci_cube1_add_swap R W Q (R.add Q (R.add W (R.add Q W))),
        q9ci_cube1_add_swap R W Q (R.add W (R.add Q W)),
        q9ci_cube1_add_swap R W Q W,
        q9ci_cube1_add_swap R W Q (R.add W W)]
  have hR : R.add (R.add (R.add P Q) W)
        (R.add (R.add (R.add P Q) W) (R.add (R.add P Q) W))
      = R.add P (R.add P (R.add P (R.add Q (R.add Q (R.add Q (R.add W (R.add W W))))))) := by
    rw [R.add_assoc P Q W,
        R.add_assoc P (R.add Q W) (R.add (R.add P (R.add Q W)) (R.add P (R.add Q W))),
        R.add_assoc Q W (R.add (R.add P (R.add Q W)) (R.add P (R.add Q W))),
        R.add_assoc P (R.add Q W) (R.add P (R.add Q W)),
        R.add_assoc Q W (R.add P (R.add Q W)),
        q9ci_cube1_add_swap R W P (R.add Q (R.add W (R.add P (R.add Q W)))),
        q9ci_cube1_add_swap R W Q (R.add W (R.add P (R.add Q W))),
        q9ci_cube1_add_swap R W P (R.add Q W),
        q9ci_cube1_add_swap R W Q W,
        q9ci_cube1_add_swap R Q P (R.add Q (R.add W (R.add P (R.add Q (R.add W W))))),
        q9ci_cube1_add_swap R W P (R.add Q (R.add W W)),
        q9ci_cube1_add_swap R W Q (R.add W W),
        q9ci_cube1_add_swap R Q P (R.add Q (R.add W (R.add W W))),
        q9ci_cube1_add_swap R Q P (R.add Q (R.add Q (R.add W (R.add W W))))]
  exact hL.trans hR.symm

/-- **A1 raw E1**: x³ の Y 成分（抽象 CRing・3(...) は反復和で明示）。 -/
theorem q9ci_cube1_raw (R : CRing) (a b c d : R.carrier) :
    R.add
      (R.add
        (R.mul
          (R.add (R.mul a a)
            (R.mul d (R.add (R.mul b c) (R.mul c b))))
          b)
        (R.mul
          (R.add (R.add (R.mul a b) (R.mul b a)) (R.mul d (R.mul c c)))
          a))
      (R.mul d
        (R.mul
          (R.add (R.add (R.mul a c) (R.mul b b)) (R.mul c a))
          c))
    =
    R.add
      (R.add (R.add (R.mul (R.mul a a) b) (R.mul d (R.mul a (R.mul c c)))) (R.mul d (R.mul (R.mul b b) c)))
      (R.add
        (R.add (R.add (R.mul (R.mul a a) b) (R.mul d (R.mul a (R.mul c c)))) (R.mul d (R.mul (R.mul b b) c)))
        (R.add (R.add (R.mul (R.mul a a) b) (R.mul d (R.mul a (R.mul c c)))) (R.mul d (R.mul (R.mul b b) c)))) := by
  rw [R.right_distrib (R.mul a a) (R.mul d (R.add (R.mul b c) (R.mul c b))) b,
      R.mul_assoc d (R.add (R.mul b c) (R.mul c b)) b,
      R.right_distrib (R.mul b c) (R.mul c b) b,
      R.left_distrib d (R.mul (R.mul b c) b) (R.mul (R.mul c b) b),
      R.mul_assoc c b b,
      R.mul_comm c (R.mul b b),
      R.mul_assoc b c b,
      R.mul_comm c b,
      ← R.mul_assoc b b c,
      R.right_distrib (R.add (R.mul a b) (R.mul b a)) (R.mul d (R.mul c c)) a,
      R.right_distrib (R.mul a b) (R.mul b a) a,
      R.mul_assoc b a a,
      R.mul_comm b (R.mul a a),
      R.mul_assoc a b a,
      R.mul_comm b a,
      ← R.mul_assoc a a b,
      R.mul_assoc d (R.mul c c) a,
      R.mul_comm (R.mul c c) a,
      R.right_distrib (R.add (R.mul a c) (R.mul b b)) (R.mul c a) c,
      R.right_distrib (R.mul a c) (R.mul b b) c,
      R.left_distrib d (R.add (R.mul (R.mul a c) c) (R.mul (R.mul b b) c)) (R.mul (R.mul c a) c),
      R.left_distrib d (R.mul (R.mul a c) c) (R.mul (R.mul b b) c),
      R.mul_assoc a c c,
      R.mul_assoc c a c,
      R.mul_comm c (R.mul a c),
      R.mul_assoc a c c]
  exact q9ci_cube1_add_perm R (R.mul (R.mul a a) b)
    (R.mul d (R.mul a (R.mul c c))) (R.mul d (R.mul (R.mul b b) c))

/-- 加法隣接入替（E2 用）。 -/
theorem q9ci_cube2_add_swap (R : CRing) (u v w : R.carrier) :
    R.add u (R.add v w) = R.add v (R.add u w) := by
  rw [← R.add_assoc u v w, R.add_comm u v, R.add_assoc v u w]

/-- 9 項順列（E2 用・分配形 → 3 copies of S=(A+B)+C）。 -/
theorem q9ci_cube2_reassoc (R : CRing) (A B C : R.carrier) :
    R.add (R.add (R.add A (R.add C C)) (R.add (R.add B B) C)) (R.add (R.add A B) A)
    = R.add (R.add (R.add A B) C)
        (R.add (R.add (R.add A B) C) (R.add (R.add A B) C)) := by
  rw [R.add_assoc (R.add A (R.add C C)) (R.add (R.add B B) C) (R.add (R.add A B) A),
      R.add_assoc A (R.add C C)
        (R.add (R.add (R.add B B) C) (R.add (R.add A B) A)),
      R.add_assoc C C (R.add (R.add (R.add B B) C) (R.add (R.add A B) A)),
      R.add_assoc (R.add B B) C (R.add (R.add A B) A),
      R.add_assoc B B (R.add C (R.add (R.add A B) A)),
      R.add_assoc A B A,
      q9ci_cube2_add_swap R C B (R.add B (R.add C (R.add A (R.add B A)))),
      q9ci_cube2_add_swap R C B (R.add C (R.add B (R.add C (R.add A (R.add B A))))),
      q9ci_cube2_add_swap R C A (R.add B A),
      q9ci_cube2_add_swap R B A (R.add C (R.add B A)),
      q9ci_cube2_add_swap R C A (R.add B (R.add C (R.add B A))),
      q9ci_cube2_add_swap R C B (R.add C (R.add B A)),
      R.add_comm B A,
      q9ci_cube2_add_swap R C A B,
      R.add_comm C B,
      R.add_assoc (R.add A B) C
        (R.add (R.add (R.add A B) C) (R.add (R.add A B) C)),
      R.add_assoc A B
        (R.add C (R.add (R.add (R.add A B) C) (R.add (R.add A B) C))),
      R.add_assoc (R.add A B) C (R.add (R.add A B) C),
      R.add_assoc A B (R.add C (R.add (R.add A B) C)),
      R.add_assoc A B C]

/-- **A1 raw E2**: x³ の Y² 成分（抽象 CRing・3(...) は反復和で明示）。 -/
theorem q9ci_cube2_raw (R : CRing) (a b c d : R.carrier) :
    R.add
      (R.add
        (R.mul
          (R.add (R.mul a a)
            (R.mul d (R.add (R.mul b c) (R.mul c b))))
          c)
        (R.mul
          (R.add (R.add (R.mul a b) (R.mul b a)) (R.mul d (R.mul c c)))
          b))
      (R.mul
        (R.add (R.add (R.mul a c) (R.mul b b)) (R.mul c a))
        a)
    =
    R.add
      (R.add (R.add (R.mul (R.mul a a) c) (R.mul a (R.mul b b))) (R.mul d (R.mul b (R.mul c c))))
      (R.add
        (R.add (R.add (R.mul (R.mul a a) c) (R.mul a (R.mul b b))) (R.mul d (R.mul b (R.mul c c))))
        (R.add (R.add (R.mul (R.mul a a) c) (R.mul a (R.mul b b))) (R.mul d (R.mul b (R.mul c c))))) := by
  have e1 : R.mul (R.add (R.mul a a) (R.mul d (R.add (R.mul b c) (R.mul c b)))) c
      = R.add (R.mul (R.mul a a) c)
          (R.add (R.mul d (R.mul b (R.mul c c))) (R.mul d (R.mul b (R.mul c c)))) := by
    rw [R.right_distrib (R.mul a a) (R.mul d (R.add (R.mul b c) (R.mul c b))) c,
        R.left_distrib d (R.mul b c) (R.mul c b),
        R.right_distrib (R.mul d (R.mul b c)) (R.mul d (R.mul c b)) c,
        R.mul_assoc d (R.mul b c) c,
        R.mul_assoc d (R.mul c b) c,
        R.mul_comm c b,
        R.mul_assoc b c c]
  have e2 : R.mul (R.add (R.add (R.mul a b) (R.mul b a)) (R.mul d (R.mul c c))) b
      = R.add (R.add (R.mul a (R.mul b b)) (R.mul a (R.mul b b)))
          (R.mul d (R.mul b (R.mul c c))) := by
    rw [R.right_distrib (R.add (R.mul a b) (R.mul b a)) (R.mul d (R.mul c c)) b,
        R.right_distrib (R.mul a b) (R.mul b a) b,
        R.mul_comm b a,
        R.mul_assoc a b b,
        R.mul_assoc d (R.mul c c) b,
        R.mul_comm (R.mul c c) b]
  have e3 : R.mul (R.add (R.add (R.mul a c) (R.mul b b)) (R.mul c a)) a
      = R.add (R.add (R.mul (R.mul a a) c) (R.mul a (R.mul b b))) (R.mul (R.mul a a) c) := by
    rw [R.right_distrib (R.add (R.mul a c) (R.mul b b)) (R.mul c a) a,
        R.right_distrib (R.mul a c) (R.mul b b) a,
        R.mul_comm (R.mul b b) a,
        R.mul_comm c a,
        R.mul_assoc a c a,
        R.mul_comm c a,
        ← R.mul_assoc a a c]
  rw [e1, e2, e3]
  exact q9ci_cube2_reassoc R (R.mul (R.mul a a) c) (R.mul a (R.mul b b))
    (R.mul d (R.mul b (R.mul c c)))

/-- **A1 E0**: (x³).1 = a³+ζ₃b³+ζ₃²c³+6ζ₃abc。 -/
theorem q9ci_cube_0 (x : q3kCar) :
    (q3kMul (q3kMul x x) x).1
      = q3rqAdd
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.1)
              (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)))
            (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)))
          (q3rqAdd
            (q3rqAdd
              (q3rqAdd
                (q3rqAdd
                  (q3rqAdd (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))
                           (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
                  (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
                (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
              (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
            (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))) := by
  rw [q3kMul_0, q3kMul_0, q3kMul_1, q3kMul_2, q3k_M_eq, q3k_A_eq]
  exact q9ci_cube0_raw q3rqRing x.1 x.2.1 x.2.2 q3rqZeta

/-- **A1 E1**: (x³).2.1 = 3(a²b+ζ₃ac²+ζ₃b²c)。 -/
theorem q9ci_cube_1 (x : q3kCar) :
    (q3kMul (q3kMul x x) x).2.1
      = q3rqAdd
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.1)
              (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.2 x.2.2))))
            (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.2)))
          (q3rqAdd
            (q3rqAdd
              (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.1)
                (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.2 x.2.2))))
              (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.2)))
            (q3rqAdd
              (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.1)
                (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.2 x.2.2))))
              (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.2)))) := by
  rw [q3kMul_1, q3kMul_0, q3kMul_1, q3kMul_2, q3k_M_eq, q3k_A_eq]
  exact q9ci_cube1_raw q3rqRing x.1 x.2.1 x.2.2 q3rqZeta

/-- **A1 E2**: (x³).2.2 = 3(a²c+ab²+ζ₃bc²)。 -/
theorem q9ci_cube_2 (x : q3kCar) :
    (q3kMul (q3kMul x x) x).2.2
      = q3rqAdd
          (q3rqAdd
            (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.2)
              (q3rqMul x.1 (q3rqMul x.2.1 x.2.1)))
            (q3rqMul q3rqZeta (q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2))))
          (q3rqAdd
            (q3rqAdd
              (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.2)
                (q3rqMul x.1 (q3rqMul x.2.1 x.2.1)))
              (q3rqMul q3rqZeta (q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2))))
            (q3rqAdd
              (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.2.2)
                (q3rqMul x.1 (q3rqMul x.2.1 x.2.1)))
              (q3rqMul q3rqZeta (q3rqMul x.2.1 (q3rqMul x.2.2 x.2.2))))) := by
  rw [q3kMul_2, q3kMul_0, q3kMul_1, q3kMul_2, q3k_M_eq, q3k_A_eq]
  exact q9ci_cube2_raw q3rqRing x.1 x.2.1 x.2.2 q3rqZeta

/-! ## q9ci-2（A2）: 正則性パック -/

/-- **A2-1: 3 は正則** — 3·z=0 ⟹ z=0（各座標で q3mc_three_mul_zero）。 -/
theorem q9ci_three_reg_L2 (z : q3rqCar)
    (h : q3rqMul q3rqThreeElt z = q3rqZero) : z = q3rqZero := by
  apply q3rq_ext
  · apply q3mc_three_mul_zero z.1
    have e : (q3rqMul q3rqThreeElt z).1 = z3.mul q3rqThree z.1 := by
      show z3.add (z3.mul q3rqThree z.1) (z3.mul q3rqD (z3.mul z3.zero z.2))
          = z3.mul q3rqThree z.1
      rw [z3.zero_mul z.2, z3.mul_zero q3rqD, z3.add_zero]
    rw [← e]; exact congrArg Prod.fst h
  · apply q3mc_three_mul_zero z.2
    have e : (q3rqMul q3rqThreeElt z).2 = z3.mul q3rqThree z.2 := by
      show z3.add (z3.mul q3rqThree z.2) (z3.mul z3.zero z.1) = z3.mul q3rqThree z.2
      rw [z3.zero_mul z.1, z3.add_zero]
    rw [← e]; exact congrArg Prod.snd h

/-- 9 = 3·3。 -/
def q9ciNine : q3rqCar := q3rqMul q3rqThreeElt q3rqThreeElt

/-- **A2-2: 9 は正則**（3 を 2 回）。 -/
theorem q9ci_nine_reg (z : q3rqCar)
    (h : q3rqMul q9ciNine z = q3rqZero) : z = q3rqZero := by
  have h' : q3rqMul q3rqThreeElt (q3rqMul q3rqThreeElt z) = q3rqZero := by
    have e : q3rqMul (q3rqMul q3rqThreeElt q3rqThreeElt) z
        = q3rqMul q3rqThreeElt (q3rqMul q3rqThreeElt z) :=
      q3rqRing.mul_assoc q3rqThreeElt q3rqThreeElt z
    rw [← e]; exact h
  exact q9ci_three_reg_L2 z (q9ci_three_reg_L2 (q3rqMul q3rqThreeElt z) h')

/-- **A2-3: λ は正則** — λ·z=0 ⟹ z=0（λ(p,q)=(−3q,p)）。 -/
theorem q9ci_lambda_reg (z : q3rqCar)
    (h : q3rqMul q3rqLambda z = q3rqZero) : z = q3rqZero := by
  apply q3rq_ext
  · -- 第 1 成分: λ·z の .2 = z.1 = 0
    have e2 : (q3rqMul q3rqLambda z).2 = z.1 := by
      show z3.add (z3.mul z3.zero z.2) (z3.mul z3.one z.1) = z.1
      rw [z3.zero_mul z.2, z3.one_mul z.1, z3.zero_add z.1]
    rw [← e2]; exact congrArg Prod.snd h
  · -- 第 2 成分: λ·z の .1 = −3·z.2 = 0 ⟹ z.2 = 0
    apply q3mc_three_mul_zero z.2
    have e1 : (q3rqMul q3rqLambda z).1 = z3.neg (z3.mul q3rqThree z.2) := by
      show z3.add (z3.mul z3.zero z.1) (z3.mul q3rqD (z3.mul z3.one z.2))
          = z3.neg (z3.mul q3rqThree z.2)
      rw [z3.zero_mul z.1, z3.zero_add, z3.one_mul z.2, q3rq_D_eq,
          z3.neg_mul q3rqThree z.2]
    have hneg : z3.neg (z3.mul q3rqThree z.2) = z3.zero := by
      rw [← e1]; exact congrArg Prod.fst h
    have hnn := congrArg z3.neg hneg
    rw [z3.neg_neg, z3.neg_zero] at hnn
    exact hnn

/-- **A2-4: 単数は正則（O_{L₂}）** — w 単数, w·z=0 ⟹ z=0。 -/
theorem q9ci_unit_reg_L2 (w z : q3rqCar) (hw : q3rqUnitMem w)
    (h : q3rqMul w z = q3rqZero) : z = q3rqZero := by
  have hinv : q3rqMul (q3rqInv w hw) w = q3rqOne := q3rq_inv_mul w hw
  calc z = q3rqMul q3rqOne z := (q3rq_one_mul z).symm
    _ = q3rqMul (q3rqMul (q3rqInv w hw) w) z := by rw [hinv]
    _ = q3rqMul (q3rqInv w hw) (q3rqMul w z) := q3rqRing.mul_assoc _ _ _
    _ = q3rqMul (q3rqInv w hw) q3rqZero := by rw [h]
    _ = q3rqZero := q3rqRing.mul_zero _

/-- **A2-5: 単数は正則（O_M）** — w 単数, w·z=0 ⟹ z=0。 -/
theorem q9ci_unit_reg_M (w z : q3kCar) (hw : q3kUnitMem w)
    (h : q3kMul w z = q3kZero) : z = q3kZero := by
  have hinv : q3kMul (q3kInv w hw) w = q3kOne := q3k_inv_mul' w hw
  calc z = q3kMul q3kOne z := (q3k_one_mul z).symm
    _ = q3kMul (q3kMul (q3kInv w hw) w) z := by rw [hinv]
    _ = q3kMul (q3kInv w hw) (q3kMul w z) := q3kRing.mul_assoc _ _ _
    _ = q3kMul (q3kInv w hw) q3kZero := by rw [h]
    _ = q3kZero := q3kRing.mul_zero _

/-- **A2-6a: (ζ₃²−1)(ζ₃−1) = 3**（円分関係 1+ζ₃+ζ₃²=0 と ζ₃³=1）。 -/
theorem q9ci_zeta_norm3 :
    q3rqMul (q3rqAdd q3rqZetaSq (q3rqNeg q3rqOne)) (q3rqAdd q3rqZeta (q3rqNeg q3rqOne))
      = q3rqThreeElt := by
  have h2 : q3rqRing.add q3rqOne (q3rqRing.add q3rqZeta q3rqZetaSq) = q3rqRing.zero :=
    q3k_zeta_sum_zero
  have hsum : q3rqRing.add q3rqZetaSq q3rqZeta = q3rqRing.neg q3rqRing.one := by
    rw [q3rqRing.add_comm q3rqZetaSq q3rqZeta]
    exact (q3rqRing.neg_eq_of_add_eq_zero h2).symm
  show q3rqRing.mul (q3rqRing.add q3rqZetaSq (q3rqRing.neg q3rqRing.one))
        (q3rqRing.add q3rqZeta (q3rqRing.neg q3rqRing.one)) = q3rqThreeElt
  rw [q3rqRing.right_distrib q3rqZetaSq (q3rqRing.neg q3rqRing.one)
        (q3rqRing.add q3rqZeta (q3rqRing.neg q3rqRing.one)),
      q3rqRing.left_distrib q3rqZetaSq q3rqZeta (q3rqRing.neg q3rqRing.one),
      q3k_zsq_zR1,
      q3rqRing.mul_neg q3rqZetaSq q3rqRing.one,
      q3rqRing.mul_one q3rqZetaSq,
      q3rqRing.neg_mul q3rqRing.one (q3rqRing.add q3rqZeta (q3rqRing.neg q3rqRing.one)),
      q3rqRing.one_mul (q3rqRing.add q3rqZeta (q3rqRing.neg q3rqRing.one)),
      q3rqRing.neg_add_dist q3rqZeta (q3rqRing.neg q3rqRing.one),
      q3rqRing.neg_neg q3rqRing.one,
      q3rqRing.add_comm (q3rqRing.neg q3rqZeta) q3rqRing.one,
      q3rqRing.add_add_add_comm q3rqRing.one (q3rqRing.neg q3rqZetaSq) q3rqRing.one
        (q3rqRing.neg q3rqZeta),
      ← q3rqRing.neg_add_dist q3rqZetaSq q3rqZeta,
      hsum,
      q3rqRing.neg_neg q3rqRing.one]
  exact q9ci_three_pair

/-- **A2-6b: ζ₃−1 は正則** — (ζ₃−1)·z=0 ⟹ z=0（(ζ₃²−1) を掛けて 3z=0）。 -/
theorem q9ci_zeta_sub_one_reg (z : q3rqCar)
    (h : q3rqMul (q3rqAdd q3rqZeta (q3rqNeg q3rqOne)) z = q3rqZero) :
    z = q3rqZero := by
  have key : q3rqMul q3rqThreeElt z = q3rqZero := by
    calc q3rqMul q3rqThreeElt z
        = q3rqMul (q3rqMul (q3rqAdd q3rqZetaSq (q3rqNeg q3rqOne))
              (q3rqAdd q3rqZeta (q3rqNeg q3rqOne))) z := by rw [← q9ci_zeta_norm3]
      _ = q3rqMul (q3rqAdd q3rqZetaSq (q3rqNeg q3rqOne))
            (q3rqMul (q3rqAdd q3rqZeta (q3rqNeg q3rqOne)) z) :=
          q3rqRing.mul_assoc _ _ _
      _ = q3rqMul (q3rqAdd q3rqZetaSq (q3rqNeg q3rqOne)) q3rqZero := by rw [h]
      _ = q3rqZero := q3rqRing.mul_zero _
  exact q9ci_three_reg_L2 z key

/-- **A2-7a: embed(w) の正則性を w の正則性に帰着**（embed(w)·z=(w·z₀,w·z₁,w·z₂)）。 -/
theorem q9ci_embed_reg_M (w : q3rqCar)
    (hw : ∀ a : q3rqCar, q3rqMul w a = q3rqZero → a = q3rqZero)
    (z : q3kCar) (h : q3kMul (q3kEmbed w) z = q3kZero) : z = q3kZero := by
  apply q3k_ext
  · apply hw z.1
    have e : (q3kMul (q3kEmbed w) z).1 = q3rqMul w z.1 := by
      show q3rqAdd (q3rqMul w z.1)
          (q3rqMul q3rqZeta (q3rqAdd (q3rqMul q3rqZero z.2.2) (q3rqMul q3rqZero z.2.1)))
          = q3rqMul w z.1
      rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul z.2.2, q3rqRing.zero_mul z.2.1,
          q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta,
          q3rqRing.add_zero (q3rqRing.mul w z.1)]
    rw [← e]; exact congrArg Prod.fst h
  · apply hw z.2.1
    have e : (q3kMul (q3kEmbed w) z).2.1 = q3rqMul w z.2.1 := by
      show q3rqAdd (q3rqAdd (q3rqMul w z.2.1) (q3rqMul q3rqZero z.1))
          (q3rqMul q3rqZeta (q3rqMul q3rqZero z.2.2)) = q3rqMul w z.2.1
      rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul z.1,
          q3rqRing.add_zero (q3rqRing.mul w z.2.1), q3rqRing.zero_mul z.2.2,
          q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero (q3rqRing.mul w z.2.1)]
    rw [← e]; exact congrArg (fun t : q3kCar => t.2.1) h
  · apply hw z.2.2
    have e : (q3kMul (q3kEmbed w) z).2.2 = q3rqMul w z.2.2 := by
      show q3rqAdd (q3rqAdd (q3rqMul w z.2.2) (q3rqMul q3rqZero z.2.1))
          (q3rqMul q3rqZero z.1) = q3rqMul w z.2.2
      rw [q3k_M_eq, q3k_A_eq, q3k_Z_eq, q3rqRing.zero_mul z.2.1,
          q3rqRing.add_zero (q3rqRing.mul w z.2.2), q3rqRing.zero_mul z.1,
          q3rqRing.add_zero (q3rqRing.mul w z.2.2)]
    rw [← e]; exact congrArg (fun t : q3kCar => t.2.2) h

/-- **A2-7b: embed(ζ₃)−1 = embed(ζ₃−1)**（embed の加法整合の局所版）。 -/
theorem q9ci_embed_sub :
    q3kAdd (q3kEmbed q3rqZeta) (q3kNeg q3kOne)
      = q3kEmbed (q3rqAdd q3rqZeta (q3rqNeg q3rqOne)) := by
  apply q3k_ext
  · rfl
  · show q3rqAdd q3rqZero (q3rqNeg q3rqZero) = q3rqZero
    rw [q3k_A_eq, q3k_N_eq, q3k_Z_eq, q3rqRing.neg_zero, q3rqRing.add_zero]
  · show q3rqAdd q3rqZero (q3rqNeg q3rqZero) = q3rqZero
    rw [q3k_A_eq, q3k_N_eq, q3k_Z_eq, q3rqRing.neg_zero, q3rqRing.add_zero]

/-- 一般 CRing の遠隔相殺（cofactor 用の 6 項テレスコープ）。 -/
theorem q9ci_tele (R : CRing) (p q r t : R.carrier) :
    R.add (R.add (R.add p q) r) (R.add (R.add (R.neg q) (R.neg r)) t) = R.add p t := by
  rw [R.add_assoc p q r,
      R.add_assoc (R.neg q) (R.neg r) t,
      R.add_assoc p (R.add q r) (R.add (R.neg q) (R.add (R.neg r) t)),
      R.add_assoc q r (R.add (R.neg q) (R.add (R.neg r) t)),
      ← R.add_assoc r (R.neg q) (R.add (R.neg r) t),
      R.add_comm r (R.neg q),
      R.add_assoc (R.neg q) r (R.add (R.neg r) t),
      ← R.add_assoc r (R.neg r) t,
      R.add_neg r,
      R.zero_add t,
      ← R.add_assoc q (R.neg q) t,
      R.add_neg q,
      R.zero_add t]

/-- **A2-8a: cofactor 恒等式**（一般 CRing）(Y−1)(Y²+Y+1) = Y³−1。 -/
theorem q9ci_cofactor_raw (R : CRing) (Y : R.carrier) :
    R.mul (R.add Y (R.neg R.one)) (R.add (R.add (R.mul Y Y) Y) R.one)
      = R.add (R.mul (R.mul Y Y) Y) (R.neg R.one) := by
  rw [R.right_distrib Y (R.neg R.one) (R.add (R.add (R.mul Y Y) Y) R.one),
      R.left_distrib Y (R.add (R.mul Y Y) Y) R.one,
      R.left_distrib Y (R.mul Y Y) Y,
      ← R.mul_assoc Y Y Y,
      R.mul_one Y,
      R.neg_mul R.one (R.add (R.add (R.mul Y Y) Y) R.one),
      R.one_mul (R.add (R.add (R.mul Y Y) Y) R.one),
      R.neg_add_dist (R.add (R.mul Y Y) Y) R.one,
      R.neg_add_dist (R.mul Y Y) Y]
  exact q9ci_tele R (R.mul (R.mul Y Y) Y) (R.mul Y Y) Y (R.neg R.one)

/-- **A2-8b: π₉ = ζ₉−1 は正則** — (Y−1)·z=0 ⟹ z=0
    （cofactor で Y³−1=embed(ζ₃−1)、embed(ζ₃−1) 正則）。 -/
theorem q9ci_pi9_reg (z : q3kCar)
    (h : q3kMul (q3kAdd q3kZeta9 (q3kNeg q3kOne)) z = q3kZero) : z = q3kZero := by
  have hPC : q3kMul (q3kAdd q3kZeta9 (q3kNeg q3kOne))
        (q3kAdd (q3kAdd (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) q3kOne)
      = q3kAdd (q3kMul (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) (q3kNeg q3kOne) :=
    q9ci_cofactor_raw q3kRing q3kZeta9
  have hkey : q3kMul (q3kAdd (q3kMul (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) (q3kNeg q3kOne)) z
      = q3kZero := by
    calc q3kMul (q3kAdd (q3kMul (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) (q3kNeg q3kOne)) z
        = q3kMul (q3kMul (q3kAdd q3kZeta9 (q3kNeg q3kOne))
              (q3kAdd (q3kAdd (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) q3kOne)) z := by rw [hPC]
      _ = q3kMul (q3kMul (q3kAdd (q3kAdd (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) q3kOne)
            (q3kAdd q3kZeta9 (q3kNeg q3kOne))) z := by
            rw [q3k_mul_comm (q3kAdd q3kZeta9 (q3kNeg q3kOne))
              (q3kAdd (q3kAdd (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) q3kOne)]
      _ = q3kMul (q3kAdd (q3kAdd (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) q3kOne)
            (q3kMul (q3kAdd q3kZeta9 (q3kNeg q3kOne)) z) :=
          q3kRing.mul_assoc _ _ _
      _ = q3kMul (q3kAdd (q3kAdd (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) q3kOne) q3kZero := by rw [h]
      _ = q3kZero := q3kRing.mul_zero _
  rw [q3k_zeta9_cube, q9ci_embed_sub] at hkey
  exact q9ci_embed_reg_M (q3rqAdd q3rqZeta (q3rqNeg q3rqOne)) q9ci_zeta_sub_one_reg z hkey

/-! ## q9ci-3（A3）: O_{L₂} 内に ζ₃・ζ₃² の 3 乗根なし -/

/-- **A3-1: ζ₃ は O_{L₂} 内に 3 乗根を持たない**（立方第 2 成分 ≡0 mod 3 vs h=単数）。 -/
theorem q9ci_no_cbrt_zeta : ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ q3rqZeta := by
  intro v hv
  cases v with
  | mk a b =>
    have h2 : (q3rqMul (q3rqMul ((a, b) : q3rqCar) (a, b)) (a, b)).2 = q3rqZeta.2 :=
      congrArg Prod.snd hv
    rw [q3mc_cube_snd a b] at h2
    have h2' : z3.mul q3rqThree
        (z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b) = q3rqHalf := h2
    cases Quot.exists_rep
        ((z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b).val 1) with
    | intro k1 hk1 =>
      have hmul := q3mc_mul_val1 q3rqThree
        (z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b) 3 k1
        (q3rq_three_val 1) hk1.symm
      have hh0 : q3rqHalf.val 1 = Quot.mk (modCong (3 ^ 1)).rel (3 * k1) := by
        rw [← h2']; exact hmul
      have htwo : q3rqTwoZ.val 1 = Quot.mk (modCong (3 ^ 1)).rel 2 := by
        show (z3.add z3.one z3.one).val 1 = Quot.mk (modCong (3 ^ 1)).rel 2
        show (zmod (3 ^ 1)).mul ((zpOne 3).val 1) ((zpOne 3).val 1)
          = Quot.mk (modCong (3 ^ 1)).rel 2
        show Quot.mk (modCong (3 ^ 1)).rel (1 + 1) = Quot.mk (modCong (3 ^ 1)).rel 2
        rfl
      have hone : (z3.mul q3rqTwoZ q3rqHalf).val 1
          = Quot.mk (modCong (3 ^ 1)).rel 1 := by
        rw [q3rq_two_half]; rfl
      rw [q3mc_mul_val1 q3rqTwoZ q3rqHalf 2 (3 * k1) htwo hh0] at hone
      have hd := quot_exact intGrp (modCong (3 ^ 1)) hone
      rw [Nat.pow_one] at hd
      cases hd with
      | intro c hc => omega

/-- **A3-2: ζ₃² は O_{L₂} 内に 3 乗根を持たない**（第 2 成分 −h=単数）。 -/
theorem q9ci_no_cbrt_zetaSq : ∀ v : q3rqCar, q3rqMul (q3rqMul v v) v ≠ q3rqZetaSq := by
  intro v hv
  cases v with
  | mk a b =>
    have h2 : (q3rqMul (q3rqMul ((a, b) : q3rqCar) (a, b)) (a, b)).2 = q3rqZetaSq.2 :=
      congrArg Prod.snd hv
    rw [q3mc_cube_snd a b] at h2
    have h2' : z3.mul q3rqThree
        (z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b) = z3.neg q3rqHalf :=
      h2.trans (congrArg Prod.snd q3rq_zeta_sq_eq)
    cases Quot.exists_rep
        ((z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b).val 1) with
    | intro k1 hk1 =>
      have hmul := q3mc_mul_val1 q3rqThree
        (z3.mul (z3.add (z3.mul a a) (z3.neg (z3.mul b b))) b) 3 k1
        (q3rq_three_val 1) hk1.symm
      have hh0 : (z3.neg q3rqHalf).val 1 = Quot.mk (modCong (3 ^ 1)).rel (3 * k1) := by
        rw [← h2']; exact hmul
      have htwo : q3rqTwoZ.val 1 = Quot.mk (modCong (3 ^ 1)).rel 2 := by
        show (z3.add z3.one z3.one).val 1 = Quot.mk (modCong (3 ^ 1)).rel 2
        show (zmod (3 ^ 1)).mul ((zpOne 3).val 1) ((zpOne 3).val 1)
          = Quot.mk (modCong (3 ^ 1)).rel 2
        show Quot.mk (modCong (3 ^ 1)).rel (1 + 1) = Quot.mk (modCong (3 ^ 1)).rel 2
        rfl
      have hone : (z3.mul q3rqTwoZ (z3.neg q3rqHalf)).val 1
          = Quot.mk (modCong (3 ^ 1)).rel (-1) := by
        rw [z3.mul_neg q3rqTwoZ q3rqHalf, q3rq_two_half]
        exact q3mc_neg_val1 z3.one 1 rfl
      rw [q3mc_mul_val1 q3rqTwoZ (z3.neg q3rqHalf) 2 (3 * k1) htwo hh0] at hone
      have hd := quot_exact intGrp (modCong (3 ^ 1)) hone
      rw [Nat.pow_one] at hd
      cases hd with
      | intro c hc => omega

/-! ## q9ci-4（A4）: N(x) = E0 − 9ζ₃abc（ノルムと冪展開の整合） -/

/-- 一般 CRing の加法相殺 (base+six) − (six+Y) = base − Y。 -/
theorem q9ci_add_neg_cancel (R : CRing) (base six Y : R.carrier) :
    R.add (R.add base six) (R.neg (R.add six Y)) = R.add base (R.neg Y) := by
  rw [R.neg_add_dist six Y,
      R.add_assoc base six (R.add (R.neg six) (R.neg Y)),
      ← R.add_assoc six (R.neg six) (R.neg Y),
      R.add_neg six,
      R.zero_add (R.neg Y)]

/-- **A4: N(x) = E0 − 9ζ₃abc**（E0=(x³).1、q3kNormBase = a³+ζ₃b³+ζ₃²c³−3ζ₃abc）。 -/
theorem q9ci_norm_sub (x : q3kCar) :
    q3kNormBase x
      = q3rqAdd ((q3kMul (q3kMul x x) x).1)
          (q3rqNeg
            (q3rqAdd
              (q3rqAdd
                (q3rqAdd
                  (q3rqAdd
                    (q3rqAdd
                      (q3rqAdd (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))
                               (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
                      (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
                    (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
                  (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
                (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
              (q3rqAdd (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))
                (q3rqAdd (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))
                  (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))))) := by
  rw [q9ci_cube_0]
  have hVW : q3rqMul q3rqZeta (q3rqMul (q3rqMul x.1 x.2.1) x.2.2)
           = q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)) := by
    rw [q3k_M_eq, q3rqRing.mul_assoc x.1 x.2.1 x.2.2]
  show q3rqAdd
        (q3rqAdd
          (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.1)
            (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)))
          (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)))
        (q3rqNeg (q3rqMul q3kThree (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.1 x.2.1) x.2.2))))
      = _
  rw [hVW, q9ci_three_mul (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))]
  exact (q9ci_add_neg_cancel q3rqRing
    (q3rqAdd
      (q3rqAdd (q3rqMul (q3rqMul x.1 x.1) x.1)
        (q3rqMul q3rqZeta (q3rqMul (q3rqMul x.2.1 x.2.1) x.2.1)))
      (q3rqMul q3rqZetaSq (q3rqMul (q3rqMul x.2.2 x.2.2) x.2.2)))
    (q3rqAdd
      (q3rqAdd
        (q3rqAdd
          (q3rqAdd
            (q3rqAdd (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))
                     (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
            (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
          (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
        (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
      (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2))))
    (q3rqAdd (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))
      (q3rqAdd (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))
        (q3rqMul q3rqZeta (q3rqMul x.1 (q3rqMul x.2.1 x.2.2)))))).symm

end IUT
