/-
  IUT/Q3KummerNonicYPow.lean — q27yp（level-27 テータ kill 用 Z-冪（ζ₂₇-冪）
    単項式正規形パック・q9yp（Q3KummerYPow.lean・level-9 Y-冪パック）の忠実な
    1 段上クローン）

  ── 主要成果の分類: **[実／(c) 承認済み足場]**（named 実ターゲット = 柱A **A6**
     mono-anabelian 復元の **level-27 第 2 層 KILL キャンペーン**。本ファイルは
     q27k（Q3KummerNonic.lean・実 O_{M₂₇} = O_{M₉}[Z]/(Z³−ζ₉)）の上で、実
     ζ₂₇ = Z の冪 Zᵏ (k=2..27) を Z³ = ζ₉（= q3kZeta9）のねじれ畳み込みで
     単項式正規形（ζ₉^m の入る座標三つ組）へ還元し、Zᵏ ≠ 1 (k=1..26) の位数
     ちょうど 27 補助補題を実に建てる。level-9 の q9yp を Z=ζ₂₇・ねじれ ζ₉ で
     忠実にクローンした承認済み足場（level-27 テータ群 q27tl/q27mt/q27mb の
     再利用部品）。toy 主語なし——主語は実 q3k-係数 3 次代数 O_{M₂₇}。
     後続本物化計画: q27tl（実 Tate 曲線 [ζ₂₇] 位数ちょうど 27）→ q27mt/q27mr
     → q27mb（kill_mod27）→ crk27 接続（q27k ヘッダの承認済み経路に同じ）。

  complete_pct 影響: **complete_pct 0 前進（foundation・再利用部品）**。本モジュール
  は代数段の Z-冪正規形のみで、テータ・kill・剛性・橋を一切含まない。s_A6（現
  0.61・帽子 ≤0.65）は動かさない——A6 status を一切動かさない（過大主張しない）。

  内容:
   * q27ypZ2 .. q27ypZ27 — Zᵏ を左結合 q27kMul 連鎖 Zᵏ=Zᵏ⁻¹·Z で定義
        （q9yp/q3k の連鎖慣習に整合）
   * q27yp_mulZ_100 / q27yp_mulZ_010 / q27yp_mulZ_001
        — 「·Z」1 段の実還元ヘルパ: embed n·Z=(0,n,0)・(0,b,0)·Z=(0,0,b)・
          (0,0,c)·Z=embed(ζ₉·c)（q9yp_mulY_* の level-27 クローン）
   * q27yp_Ymul_100 / q27yp_Ymul_010 / q27yp_Ymul_001・q27yp_w2 .. q27yp_w9
        — M₉ 内の ζ₉-冪はしご（ζ₉·ζ₉^m の座標形・q9yp の正規形を可換律で
          左乗へ持ち替えた再利用）
   * q27yp_z2 .. q27yp_z26 / q27yp_z27 — 単項式正規形の厳密恒等式:
        Z^{3m}=embed(ζ₉^m)・Z^{3m+1}=(0,ζ₉^m,0)・Z^{3m+2}=(0,0,ζ₉^m)・
        特に Z³=ζ₉・Z⁹=ζ₃・Z¹⁸=ζ₃²・**Z²⁷=1**（左結合連鎖形。
        q27yp_z4_prod は Z⁴ の積形も提供——q9yp_y4_prod のクローン）
   * q27yp_z1_ne_one .. q27yp_z26_ne_one — 位数ちょうど 27 補助: Zᵏ≠1 (k=1..26)
        3∤k は非零スロット矛盾・3|k は embed(ζ₉^{k/3})≠1（q9yp の位数 9 側
        非自明性を embed 経由で消費）
   * Q3KummerNonicYPowData / q27yp_data / q27yp_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・q27k/q9yp 継承の上に追記のみ）:
  1. **純単項式恒等式＋位数 27 補助のみ**（代数段）。テータ関数ゼロ・kill ゼロ・
     剛性ゼロ・橋ゼロ（level-27 kill 本体は後続 q27tl/q27mt/q27mr/q27mb が担う）。
     A6 status を動かさない。
  2. q27k の全正直限定（O_{M₂₇} と M₂₇^× のみ・体でない・付値/位相/wild 分岐は
     範囲外・τ を超える Galois 作用ゼロ・π₁ 同定ゼロ・兄弟担体等）および q9yp/q3k
     の全正直限定を**そのまま継承**する。
  3. Z の冪の Nat 添字関数・一般積法則 Zᵏ·Zᵐ=Z^{k+m mod 27} の一括定理は導入
     しない（q9yp §3 の慣習継承——数値簡約の脆さ回避）。下流が直接消費するのは
     左結合連鎖の名前付き定義 q27ypZ2..q27ypZ27 を正準形とし、積の畳み込みは
     1 段ヘルパ q27yp_mulZ_100/010/001（一般係数で成立）で行う。
  4. ζ₉-冪はしご（q27yp_w2..q27yp_w9）は ζ₉ 左乗の座標形のみ（q9yp の右乗
     正規形の可換持ち替え）。M₉ 側の新しい代数事実は導入しない。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3KummerNonic
import IUT.Q3KummerYPow

namespace IUT

/-! ## q27yp-0: q3rq レベルの非零ヘルパ（1・ζ₃・ζ₃² ≠ 0） -/

/-- 1 ≠ 0（L₂ 内・第 1 成分 z3.one ≠ z3.zero）。 -/
theorem q27yp_one_nz : q3rqOne ≠ q3rqZero := by
  intro h
  have h1 : z3.one = z3.zero := congrArg (fun p : q3rqCar => p.1) h
  exact q3rq_z3_one_ne_zero h1

/-- ζ₃ ≠ 0（第 2 成分 h ≠ 0）。 -/
theorem q27yp_zeta_nz : q3rqZeta ≠ q3rqZero := by
  intro h
  have h1 : q3rqHalf = z3.zero := congrArg (fun p : q3rqCar => p.2) h
  exact q3rq_half_ne_zero h1

/-- ζ₃² ≠ 0（第 2 成分 −h ≠ 0）。 -/
theorem q27yp_zetasq_nz : q3rqZetaSq ≠ q3rqZero := by
  intro h
  have h1 : q3rqMul q3rqZeta q3rqZeta = q3rqZero := h
  rw [q3rq_zeta_sq_eq] at h1
  have h2 : z3.neg q3rqHalf = z3.zero := congrArg (fun p : q3rqCar => p.2) h1
  exact q3rq_neg_half_ne_zero h2

/-! ## q27yp-1: M₉ 内の ζ₉-冪はしご（ζ₉ 左乗の座標形・q9yp の可換持ち替え） -/

/-- **q27yp-1a: ζ₉·embed(n) = (0,n,0)**（q9yp_mulY_100 の左乗版）。 -/
theorem q27yp_Ymul_100 (n : q3rqCar) :
    q3kMul q3kZeta9 (q3kEmbed n) = ((q3rqZero, n, q3rqZero) : q3kCar) := by
  show q3kRing.mul q3kZeta9 (q3kEmbed n) = _
  rw [q3kRing.mul_comm q3kZeta9 (q3kEmbed n)]
  exact q9yp_mulY_100 n

/-- **q27yp-1b: ζ₉·(0,b,0) = (0,0,b)**（q9yp_mulY_010 の左乗版）。 -/
theorem q27yp_Ymul_010 (b : q3rqCar) :
    q3kMul q3kZeta9 ((q3rqZero, b, q3rqZero) : q3kCar)
      = ((q3rqZero, q3rqZero, b) : q3kCar) := by
  show q3kRing.mul q3kZeta9 ((q3rqZero, b, q3rqZero) : q3kCar) = _
  rw [q3kRing.mul_comm q3kZeta9 ((q3rqZero, b, q3rqZero) : q3kCar)]
  exact q9yp_mulY_010 b

/-- **q27yp-1c: ζ₉·(0,0,c) = embed(ζ₃·c)**（q9yp_mulY_001 の左乗版）。 -/
theorem q27yp_Ymul_001 (c : q3rqCar) :
    q3kMul q3kZeta9 ((q3rqZero, q3rqZero, c) : q3kCar)
      = q3kEmbed (q3rqMul q3rqZeta c) := by
  show q3kRing.mul q3kZeta9 ((q3rqZero, q3rqZero, c) : q3kCar) = _
  rw [q3kRing.mul_comm q3kZeta9 ((q3rqZero, q3rqZero, c) : q3kCar)]
  exact q9yp_mulY_001 c

/-- ζ₉·ζ₉ = ζ₉² = (0,0,1)（q3k_zeta9_sq の再掲）。 -/
theorem q27yp_w2 : q3kMul q3kZeta9 q3kZeta9
    = ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) := q3k_zeta9_sq

/-- ζ₉·ζ₉² = ζ₉³ = embed ζ₃。 -/
theorem q27yp_w3 : q3kMul q3kZeta9 ((q3rqZero, q3rqZero, q3rqOne) : q3kCar)
    = q3kEmbed q3rqZeta := by
  rw [q27yp_Ymul_001 q3rqOne, q3rq_mul_one q3rqZeta]

/-- ζ₉·ζ₉³ = ζ₉⁴ = (0,ζ₃,0)。 -/
theorem q27yp_w4 : q3kMul q3kZeta9 (q3kEmbed q3rqZeta)
    = ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) := q27yp_Ymul_100 q3rqZeta

/-- ζ₉·ζ₉⁴ = ζ₉⁵ = (0,0,ζ₃)。 -/
theorem q27yp_w5 : q3kMul q3kZeta9 ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar)
    = ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) := q27yp_Ymul_010 q3rqZeta

/-- ζ₉·ζ₉⁵ = ζ₉⁶ = embed ζ₃²（embed(ζ₃·ζ₃)=embed ζ₃²）。 -/
theorem q27yp_w6 : q3kMul q3kZeta9 ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar)
    = q3kEmbed q3rqZetaSq := q27yp_Ymul_001 q3rqZeta

/-- ζ₉·ζ₉⁶ = ζ₉⁷ = (0,ζ₃²,0)。 -/
theorem q27yp_w7 : q3kMul q3kZeta9 (q3kEmbed q3rqZetaSq)
    = ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) := q27yp_Ymul_100 q3rqZetaSq

/-- ζ₉·ζ₉⁷ = ζ₉⁸ = (0,0,ζ₃²)。 -/
theorem q27yp_w8 : q3kMul q3kZeta9 ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar)
    = ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) := q27yp_Ymul_010 q3rqZetaSq

/-- ζ₉·ζ₉⁸ = ζ₉⁹ = 1（ζ₃·ζ₃²=1 で定数部へ）。 -/
theorem q27yp_w9 : q3kMul q3kZeta9 ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar)
    = q3kOne := by
  rw [q27yp_Ymul_001 q3rqZetaSq, q3rq_zeta_mul_zetaSq]
  exact q3k_embed_one

/-! ## q27yp-2: Z の冪（左結合 q27kMul 連鎖 Zᵏ = Zᵏ⁻¹·Z、Z=q27kZeta27） -/

/-- Z² = Z·Z。 -/
def q27ypZ2 : q27kCar := q27kMul q27kZeta27 q27kZeta27
/-- Z³ = Z²·Z。 -/
def q27ypZ3 : q27kCar := q27kMul q27ypZ2 q27kZeta27
/-- Z⁴ = Z³·Z。 -/
def q27ypZ4 : q27kCar := q27kMul q27ypZ3 q27kZeta27
/-- Z⁵ = Z⁴·Z。 -/
def q27ypZ5 : q27kCar := q27kMul q27ypZ4 q27kZeta27
/-- Z⁶ = Z⁵·Z。 -/
def q27ypZ6 : q27kCar := q27kMul q27ypZ5 q27kZeta27
/-- Z⁷ = Z⁶·Z。 -/
def q27ypZ7 : q27kCar := q27kMul q27ypZ6 q27kZeta27
/-- Z⁸ = Z⁷·Z。 -/
def q27ypZ8 : q27kCar := q27kMul q27ypZ7 q27kZeta27
/-- Z⁹ = Z⁸·Z。 -/
def q27ypZ9 : q27kCar := q27kMul q27ypZ8 q27kZeta27
/-- Z¹⁰ = Z⁹·Z。 -/
def q27ypZ10 : q27kCar := q27kMul q27ypZ9 q27kZeta27
/-- Z¹¹ = Z¹⁰·Z。 -/
def q27ypZ11 : q27kCar := q27kMul q27ypZ10 q27kZeta27
/-- Z¹² = Z¹¹·Z。 -/
def q27ypZ12 : q27kCar := q27kMul q27ypZ11 q27kZeta27
/-- Z¹³ = Z¹²·Z。 -/
def q27ypZ13 : q27kCar := q27kMul q27ypZ12 q27kZeta27
/-- Z¹⁴ = Z¹³·Z。 -/
def q27ypZ14 : q27kCar := q27kMul q27ypZ13 q27kZeta27
/-- Z¹⁵ = Z¹⁴·Z。 -/
def q27ypZ15 : q27kCar := q27kMul q27ypZ14 q27kZeta27
/-- Z¹⁶ = Z¹⁵·Z。 -/
def q27ypZ16 : q27kCar := q27kMul q27ypZ15 q27kZeta27
/-- Z¹⁷ = Z¹⁶·Z。 -/
def q27ypZ17 : q27kCar := q27kMul q27ypZ16 q27kZeta27
/-- Z¹⁸ = Z¹⁷·Z。 -/
def q27ypZ18 : q27kCar := q27kMul q27ypZ17 q27kZeta27
/-- Z¹⁹ = Z¹⁸·Z。 -/
def q27ypZ19 : q27kCar := q27kMul q27ypZ18 q27kZeta27
/-- Z²⁰ = Z¹⁹·Z。 -/
def q27ypZ20 : q27kCar := q27kMul q27ypZ19 q27kZeta27
/-- Z²¹ = Z²⁰·Z。 -/
def q27ypZ21 : q27kCar := q27kMul q27ypZ20 q27kZeta27
/-- Z²² = Z²¹·Z。 -/
def q27ypZ22 : q27kCar := q27kMul q27ypZ21 q27kZeta27
/-- Z²³ = Z²²·Z。 -/
def q27ypZ23 : q27kCar := q27kMul q27ypZ22 q27kZeta27
/-- Z²⁴ = Z²³·Z。 -/
def q27ypZ24 : q27kCar := q27kMul q27ypZ23 q27kZeta27
/-- Z²⁵ = Z²⁴·Z。 -/
def q27ypZ25 : q27kCar := q27kMul q27ypZ24 q27kZeta27
/-- Z²⁶ = Z²⁵·Z。 -/
def q27ypZ26 : q27kCar := q27kMul q27ypZ25 q27kZeta27
/-- Z²⁷ = Z²⁶·Z。 -/
def q27ypZ27 : q27kCar := q27kMul q27ypZ26 q27kZeta27

/-! ## q27yp-3: 「·Z」1 段の実還元ヘルパ（Z=(0,1,0) の右乗の座標作用・
    q9yp_mulY_* の level-27 クローン） -/

/-- **q27yp-3a: embed(n)·Z = (0,n,0)**（(n,0,0)·(0,1,0) の還元）。 -/
theorem q27yp_mulZ_100 (n : q3kCar) :
    q27kMul (q27kEmbed n) q27kZeta27 = ((q3kZero, n, q3kZero) : q27kCar) := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul n q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
          (q3kRing.mul q3kRing.zero q3kRing.one))) = q3kRing.zero
    rw [q3kRing.mul_zero n, q3kRing.mul_zero q3kRing.zero, q3kRing.zero_mul q3kRing.one,
      q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9, q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul n q3kRing.one)
        (q3kRing.mul q3kRing.zero q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul q3kRing.zero q3kRing.zero)) = n
    rw [q3kRing.mul_one n, q3kRing.mul_zero q3kRing.zero, q3kRing.add_zero n,
      q3kRing.mul_zero q3kZeta9, q3kRing.add_zero n]
  · show q3kRing.add (q3kRing.add (q3kRing.mul n q3kRing.zero)
        (q3kRing.mul q3kRing.zero q3kRing.one)) (q3kRing.mul q3kRing.zero q3kRing.zero)
        = q3kRing.zero
    rw [q3kRing.mul_zero n, q3kRing.zero_mul q3kRing.one, q3kRing.add_zero q3kRing.zero,
      q3kRing.mul_zero q3kRing.zero, q3kRing.add_zero q3kRing.zero]

/-- **q27yp-3b: (0,b,0)·Z = (0,0,b)**。 -/
theorem q27yp_mulZ_010 (b : q3kCar) :
    q27kMul ((q3kZero, b, q3kZero) : q27kCar) q27kZeta27
      = ((q3kZero, q3kZero, b) : q27kCar) := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul b q3kRing.zero)
          (q3kRing.mul q3kRing.zero q3kRing.one))) = q3kRing.zero
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.mul_zero b, q3kRing.zero_mul q3kRing.one,
      q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9, q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.one)
        (q3kRing.mul b q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul q3kRing.zero q3kRing.zero)) = q3kRing.zero
    rw [q3kRing.zero_mul q3kRing.one, q3kRing.mul_zero b, q3kRing.add_zero q3kRing.zero,
      q3kRing.mul_zero q3kRing.zero, q3kRing.mul_zero q3kZeta9, q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul b q3kRing.one)) (q3kRing.mul q3kRing.zero q3kRing.zero) = b
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.mul_one b, q3kRing.zero_add b,
      q3kRing.add_zero b]

/-- **q27yp-3c: (0,0,c)·Z = embed(ζ₉·c)**（Z³=ζ₉ のねじれで定数部へ）。 -/
theorem q27yp_mulZ_001 (c : q3kCar) :
    q27kMul ((q3kZero, q3kZero, c) : q27kCar) q27kZeta27
      = q27kEmbed (q3kMul q3kZeta9 c) := by
  apply q27k_ext
  · show q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kZeta9 (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
          (q3kRing.mul c q3kRing.one))) = q3kRing.mul q3kZeta9 c
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.mul_one c,
      q3kRing.zero_add c, q3kRing.zero_add (q3kRing.mul q3kZeta9 c)]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.one)
        (q3kRing.mul q3kRing.zero q3kRing.zero))
        (q3kRing.mul q3kZeta9 (q3kRing.mul c q3kRing.zero)) = q3kRing.zero
    rw [q3kRing.zero_mul q3kRing.one, q3kRing.mul_zero q3kRing.zero,
      q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero c, q3kRing.mul_zero q3kZeta9,
      q3kRing.add_zero q3kRing.zero]
  · show q3kRing.add (q3kRing.add (q3kRing.mul q3kRing.zero q3kRing.zero)
        (q3kRing.mul q3kRing.zero q3kRing.one)) (q3kRing.mul c q3kRing.zero) = q3kRing.zero
    rw [q3kRing.mul_zero q3kRing.zero, q3kRing.zero_mul q3kRing.one,
      q3kRing.add_zero q3kRing.zero, q3kRing.mul_zero c, q3kRing.add_zero q3kRing.zero]

/-! ## q27yp-4: 単項式正規形の厳密恒等式 Zᵏ (k=2..27)
    （Z^{3m}=embed(ζ₉^m)・Z^{3m+1}=(0,ζ₉^m,0)・Z^{3m+2}=(0,0,ζ₉^m)） -/

/-- **q27yp-4a: Z² = (0,0,1)**（q27k_zeta27_sq の連鎖形）。 -/
theorem q27yp_z2 : q27ypZ2 = ((q3kZero, q3kZero, q3kOne) : q27kCar) := q27k_zeta27_sq

/-- **q27yp-4b: Z³ = ζ₉**（embed・q27k_zeta27_cube の再掲）。 -/
theorem q27yp_z3 : q27ypZ3 = q27kEmbed q3kZeta9 := q27k_zeta27_cube

/-- **q27yp-4c: Z⁴ = ζ₉·Z = (0,ζ₉,0)**。 -/
theorem q27yp_z4 : q27ypZ4 = ((q3kZero, q3kZeta9, q3kZero) : q27kCar) := by
  show q27kMul q27ypZ3 q27kZeta27 = _
  rw [q27yp_z3]; exact q27yp_mulZ_100 q3kZeta9

/-- Z⁴ の積形 ζ₉·Z（下流の積形消費用・q9yp_y4_prod のクローン）。 -/
theorem q27yp_z4_prod : q27ypZ4 = q27kMul (q27kEmbed q3kZeta9) q27kZeta27 := by
  show q27kMul q27ypZ3 q27kZeta27 = _
  rw [q27yp_z3]

/-- **q27yp-4d: Z⁵ = ζ₉·Z² = (0,0,ζ₉)**。 -/
theorem q27yp_z5 : q27ypZ5 = ((q3kZero, q3kZero, q3kZeta9) : q27kCar) := by
  show q27kMul q27ypZ4 q27kZeta27 = _
  rw [q27yp_z4]; exact q27yp_mulZ_010 q3kZeta9

/-- **q27yp-4e: Z⁶ = ζ₉² = embed(0,0,1)**。 -/
theorem q27yp_z6 : q27ypZ6 = q27kEmbed ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) := by
  show q27kMul q27ypZ5 q27kZeta27 = _
  rw [q27yp_z5, q27yp_mulZ_001 q3kZeta9, q27yp_w2]

/-- **q27yp-4f: Z⁷ = ζ₉²·Z = (0,ζ₉²,0)**。 -/
theorem q27yp_z7 : q27ypZ7
    = ((q3kZero, ((q3rqZero, q3rqZero, q3rqOne) : q3kCar), q3kZero) : q27kCar) := by
  show q27kMul q27ypZ6 q27kZeta27 = _
  rw [q27yp_z6]; exact q27yp_mulZ_100 ((q3rqZero, q3rqZero, q3rqOne) : q3kCar)

/-- **q27yp-4g: Z⁸ = ζ₉²·Z² = (0,0,ζ₉²)**。 -/
theorem q27yp_z8 : q27ypZ8
    = ((q3kZero, q3kZero, ((q3rqZero, q3rqZero, q3rqOne) : q3kCar)) : q27kCar) := by
  show q27kMul q27ypZ7 q27kZeta27 = _
  rw [q27yp_z7]; exact q27yp_mulZ_010 ((q3rqZero, q3rqZero, q3rqOne) : q3kCar)

/-- **q27yp-4h: Z⁹ = ζ₉³ = ζ₃ = embed(embed ζ₃)**（q27k_zeta27_pow9 の連鎖形）。 -/
theorem q27yp_z9 : q27ypZ9 = q27kEmbed (q3kEmbed q3rqZeta) := by
  show q27kMul q27ypZ8 q27kZeta27 = _
  rw [q27yp_z8, q27yp_mulZ_001 ((q3rqZero, q3rqZero, q3rqOne) : q3kCar), q27yp_w3]

/-- **q27yp-4i: Z¹⁰ = ζ₃·Z = (0,ζ₃,0)**。 -/
theorem q27yp_z10 : q27ypZ10
    = ((q3kZero, q3kEmbed q3rqZeta, q3kZero) : q27kCar) := by
  show q27kMul q27ypZ9 q27kZeta27 = _
  rw [q27yp_z9]; exact q27yp_mulZ_100 (q3kEmbed q3rqZeta)

/-- **q27yp-4j: Z¹¹ = ζ₃·Z² = (0,0,ζ₃)**。 -/
theorem q27yp_z11 : q27ypZ11
    = ((q3kZero, q3kZero, q3kEmbed q3rqZeta) : q27kCar) := by
  show q27kMul q27ypZ10 q27kZeta27 = _
  rw [q27yp_z10]; exact q27yp_mulZ_010 (q3kEmbed q3rqZeta)

/-- **q27yp-4k: Z¹² = ζ₉⁴ = embed(0,ζ₃,0)**。 -/
theorem q27yp_z12 : q27ypZ12
    = q27kEmbed ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) := by
  show q27kMul q27ypZ11 q27kZeta27 = _
  rw [q27yp_z11, q27yp_mulZ_001 (q3kEmbed q3rqZeta), q27yp_w4]

/-- **q27yp-4l: Z¹³ = ζ₉⁴·Z = (0,ζ₉⁴,0)**。 -/
theorem q27yp_z13 : q27ypZ13
    = ((q3kZero, ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar), q3kZero) : q27kCar) := by
  show q27kMul q27ypZ12 q27kZeta27 = _
  rw [q27yp_z12]; exact q27yp_mulZ_100 ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar)

/-- **q27yp-4m: Z¹⁴ = ζ₉⁴·Z² = (0,0,ζ₉⁴)**。 -/
theorem q27yp_z14 : q27ypZ14
    = ((q3kZero, q3kZero, ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar)) : q27kCar) := by
  show q27kMul q27ypZ13 q27kZeta27 = _
  rw [q27yp_z13]; exact q27yp_mulZ_010 ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar)

/-- **q27yp-4n: Z¹⁵ = ζ₉⁵ = embed(0,0,ζ₃)**。 -/
theorem q27yp_z15 : q27ypZ15
    = q27kEmbed ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) := by
  show q27kMul q27ypZ14 q27kZeta27 = _
  rw [q27yp_z14, q27yp_mulZ_001 ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar), q27yp_w5]

/-- **q27yp-4o: Z¹⁶ = ζ₉⁵·Z = (0,ζ₉⁵,0)**。 -/
theorem q27yp_z16 : q27ypZ16
    = ((q3kZero, ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar), q3kZero) : q27kCar) := by
  show q27kMul q27ypZ15 q27kZeta27 = _
  rw [q27yp_z15]; exact q27yp_mulZ_100 ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar)

/-- **q27yp-4p: Z¹⁷ = ζ₉⁵·Z² = (0,0,ζ₉⁵)**。 -/
theorem q27yp_z17 : q27ypZ17
    = ((q3kZero, q3kZero, ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar)) : q27kCar) := by
  show q27kMul q27ypZ16 q27kZeta27 = _
  rw [q27yp_z16]; exact q27yp_mulZ_010 ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar)

/-- **q27yp-4q: Z¹⁸ = ζ₉⁶ = ζ₃² = embed(embed ζ₃²)**。 -/
theorem q27yp_z18 : q27ypZ18 = q27kEmbed (q3kEmbed q3rqZetaSq) := by
  show q27kMul q27ypZ17 q27kZeta27 = _
  rw [q27yp_z17, q27yp_mulZ_001 ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar), q27yp_w6]

/-- **q27yp-4r: Z¹⁹ = ζ₃²·Z = (0,ζ₃²,0)**。 -/
theorem q27yp_z19 : q27ypZ19
    = ((q3kZero, q3kEmbed q3rqZetaSq, q3kZero) : q27kCar) := by
  show q27kMul q27ypZ18 q27kZeta27 = _
  rw [q27yp_z18]; exact q27yp_mulZ_100 (q3kEmbed q3rqZetaSq)

/-- **q27yp-4s: Z²⁰ = ζ₃²·Z² = (0,0,ζ₃²)**。 -/
theorem q27yp_z20 : q27ypZ20
    = ((q3kZero, q3kZero, q3kEmbed q3rqZetaSq) : q27kCar) := by
  show q27kMul q27ypZ19 q27kZeta27 = _
  rw [q27yp_z19]; exact q27yp_mulZ_010 (q3kEmbed q3rqZetaSq)

/-- **q27yp-4t: Z²¹ = ζ₉⁷ = embed(0,ζ₃²,0)**。 -/
theorem q27yp_z21 : q27ypZ21
    = q27kEmbed ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) := by
  show q27kMul q27ypZ20 q27kZeta27 = _
  rw [q27yp_z20, q27yp_mulZ_001 (q3kEmbed q3rqZetaSq), q27yp_w7]

/-- **q27yp-4u: Z²² = ζ₉⁷·Z = (0,ζ₉⁷,0)**。 -/
theorem q27yp_z22 : q27ypZ22
    = ((q3kZero, ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar), q3kZero) : q27kCar) := by
  show q27kMul q27ypZ21 q27kZeta27 = _
  rw [q27yp_z21]; exact q27yp_mulZ_100 ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar)

/-- **q27yp-4v: Z²³ = ζ₉⁷·Z² = (0,0,ζ₉⁷)**。 -/
theorem q27yp_z23 : q27ypZ23
    = ((q3kZero, q3kZero, ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar)) : q27kCar) := by
  show q27kMul q27ypZ22 q27kZeta27 = _
  rw [q27yp_z22]; exact q27yp_mulZ_010 ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar)

/-- **q27yp-4w: Z²⁴ = ζ₉⁸ = embed(0,0,ζ₃²)**。 -/
theorem q27yp_z24 : q27ypZ24
    = q27kEmbed ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) := by
  show q27kMul q27ypZ23 q27kZeta27 = _
  rw [q27yp_z23, q27yp_mulZ_001 ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar), q27yp_w8]

/-- **q27yp-4x: Z²⁵ = ζ₉⁸·Z = (0,ζ₉⁸,0)**。 -/
theorem q27yp_z25 : q27ypZ25
    = ((q3kZero, ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar), q3kZero) : q27kCar) := by
  show q27kMul q27ypZ24 q27kZeta27 = _
  rw [q27yp_z24]; exact q27yp_mulZ_100 ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar)

/-- **q27yp-4y: Z²⁶ = ζ₉⁸·Z² = (0,0,ζ₉⁸)**。 -/
theorem q27yp_z26 : q27ypZ26
    = ((q3kZero, q3kZero, ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar)) : q27kCar) := by
  show q27kMul q27ypZ25 q27kZeta27 = _
  rw [q27yp_z25]; exact q27yp_mulZ_010 ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar)

/-- **q27yp-4z（★）: Z²⁷ = 1**（左結合連鎖形。q27k_zeta27_pow27 の
    ((Z⁹)Z⁹)Z⁹ 括りに対する連鎖版の新恒等式）。 -/
theorem q27yp_z27 : q27ypZ27 = q27kOne := by
  show q27kMul q27ypZ26 q27kZeta27 = _
  rw [q27yp_z26, q27yp_mulZ_001 ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar), q27yp_w9]
  exact q27k_embed_one

/-! ## q27yp-5: M₉ 内 ζ₉-冪の非零・非 1 ヘルパ（スロット判定用） -/

/-- 1 ≠ 0（M₉ 内）。 -/
theorem q27yp_w0_nz : q3kOne ≠ q3kZero := by
  intro h
  have h1 : q3rqOne = q3rqZero := congrArg (fun p : q3kCar => p.1) h
  exact q27yp_one_nz h1

/-- ζ₉ ≠ 0（第 2 スロット 1 ≠ 0）。 -/
theorem q27yp_w1_nz : q3kZeta9 ≠ q3kZero := by
  intro h
  have h1 : q3rqOne = q3rqZero := congrArg (fun p : q3kCar => p.2.1) h
  exact q27yp_one_nz h1

/-- ζ₉² = (0,0,1) ≠ 0。 -/
theorem q27yp_w2_nz : ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) ≠ q3kZero := by
  intro h
  have h1 : q3rqOne = q3rqZero := congrArg (fun p : q3kCar => p.2.2) h
  exact q27yp_one_nz h1

/-- ζ₉³ = embed ζ₃ ≠ 0。 -/
theorem q27yp_w3_nz : q3kEmbed q3rqZeta ≠ q3kZero := by
  intro h
  have h1 : q3rqZeta = q3rqZero := congrArg (fun p : q3kCar => p.1) h
  exact q27yp_zeta_nz h1

/-- ζ₉⁴ = (0,ζ₃,0) ≠ 0。 -/
theorem q27yp_w4_nz : ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) ≠ q3kZero := by
  intro h
  have h1 : q3rqZeta = q3rqZero := congrArg (fun p : q3kCar => p.2.1) h
  exact q27yp_zeta_nz h1

/-- ζ₉⁵ = (0,0,ζ₃) ≠ 0。 -/
theorem q27yp_w5_nz : ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) ≠ q3kZero := by
  intro h
  have h1 : q3rqZeta = q3rqZero := congrArg (fun p : q3kCar => p.2.2) h
  exact q27yp_zeta_nz h1

/-- ζ₉⁶ = embed ζ₃² ≠ 0。 -/
theorem q27yp_w6_nz : q3kEmbed q3rqZetaSq ≠ q3kZero := by
  intro h
  have h1 : q3rqZetaSq = q3rqZero := congrArg (fun p : q3kCar => p.1) h
  exact q27yp_zetasq_nz h1

/-- ζ₉⁷ = (0,ζ₃²,0) ≠ 0。 -/
theorem q27yp_w7_nz : ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) ≠ q3kZero := by
  intro h
  have h1 : q3rqZetaSq = q3rqZero := congrArg (fun p : q3kCar => p.2.1) h
  exact q27yp_zetasq_nz h1

/-- ζ₉⁸ = (0,0,ζ₃²) ≠ 0。 -/
theorem q27yp_w8_nz : ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) ≠ q3kZero := by
  intro h
  have h1 : q3rqZetaSq = q3rqZero := congrArg (fun p : q3kCar => p.2.2) h
  exact q27yp_zetasq_nz h1

/-- ζ₉² = (0,0,1) ≠ 1（第 3 スロット 1 ≠ 0）。 -/
theorem q27yp_w2_no : ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) ≠ q3kOne := by
  intro h
  have h1 : q3rqOne = q3rqZero := congrArg (fun p : q3kCar => p.2.2) h
  exact q27yp_one_nz h1

/-- ζ₉⁴ = (0,ζ₃,0) ≠ 1。 -/
theorem q27yp_w4_no : ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) ≠ q3kOne := by
  intro h
  have h1 : q3rqZeta = q3rqZero := congrArg (fun p : q3kCar => p.2.1) h
  exact q27yp_zeta_nz h1

/-- ζ₉⁵ = (0,0,ζ₃) ≠ 1。 -/
theorem q27yp_w5_no : ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) ≠ q3kOne := by
  intro h
  have h1 : q3rqZeta = q3rqZero := congrArg (fun p : q3kCar => p.2.2) h
  exact q27yp_zeta_nz h1

/-- ζ₉⁶ = embed ζ₃² ≠ 1（ζ₃² ≠ 1）。 -/
theorem q27yp_w6_no : q3kEmbed q3rqZetaSq ≠ q3kOne := by
  intro h
  have h1 : q3rqZetaSq = q3rqOne := congrArg (fun p : q3kCar => p.1) h
  exact q3rq_zeta_sq_ne_one h1

/-- ζ₉⁷ = (0,ζ₃²,0) ≠ 1。 -/
theorem q27yp_w7_no : ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) ≠ q3kOne := by
  intro h
  have h1 : q3rqZetaSq = q3rqZero := congrArg (fun p : q3kCar => p.2.1) h
  exact q27yp_zetasq_nz h1

/-- ζ₉⁸ = (0,0,ζ₃²) ≠ 1。 -/
theorem q27yp_w8_no : ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) ≠ q3kOne := by
  intro h
  have h1 : q3rqZetaSq = q3rqZero := congrArg (fun p : q3kCar => p.2.2) h
  exact q27yp_zetasq_nz h1

/-! ## q27yp-6: 位数ちょうど 27 補助 Zᵏ ≠ 1 (k=1..26) -/

/-- **q27yp-6a: Z ≠ 1**（q27k_zeta27_ne_one の再掲）。 -/
theorem q27yp_z1_ne_one : q27kZeta27 ≠ q27kOne := q27k_zeta27_ne_one

/-- **Z² ≠ 1**（第 3 スロット 1 ≠ 0）。 -/
theorem q27yp_z2_ne_one : q27ypZ2 ≠ q27kOne := by
  intro h
  rw [q27yp_z2] at h
  have h1 : q3kOne = q3kZero := congrArg (fun z : q27kCar => z.2.2) h
  exact q27yp_w0_nz h1

/-- **Z³ ≠ 1**（Z³=embed ζ₉・ζ₉≠1）。 -/
theorem q27yp_z3_ne_one : q27ypZ3 ≠ q27kOne := by
  intro h
  rw [q27yp_z3] at h
  have h1 : q3kZeta9 = q3kOne := congrArg (fun z : q27kCar => z.1) h
  exact q3k_zeta9_ne_one h1

/-- **Z⁴ ≠ 1**（第 2 スロット ζ₉ ≠ 0）。 -/
theorem q27yp_z4_ne_one : q27ypZ4 ≠ q27kOne := by
  intro h
  rw [q27yp_z4] at h
  have h1 : q3kZeta9 = q3kZero := congrArg (fun z : q27kCar => z.2.1) h
  exact q27yp_w1_nz h1

/-- **Z⁵ ≠ 1**（第 3 スロット ζ₉ ≠ 0）。 -/
theorem q27yp_z5_ne_one : q27ypZ5 ≠ q27kOne := by
  intro h
  rw [q27yp_z5] at h
  have h1 : q3kZeta9 = q3kZero := congrArg (fun z : q27kCar => z.2.2) h
  exact q27yp_w1_nz h1

/-- **Z⁶ ≠ 1**（Z⁶=embed ζ₉²・ζ₉²≠1）。 -/
theorem q27yp_z6_ne_one : q27ypZ6 ≠ q27kOne := by
  intro h
  rw [q27yp_z6] at h
  have h1 : ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) = q3kOne :=
    congrArg (fun z : q27kCar => z.1) h
  exact q27yp_w2_no h1

/-- **Z⁷ ≠ 1**（第 2 スロット ζ₉² ≠ 0）。 -/
theorem q27yp_z7_ne_one : q27ypZ7 ≠ q27kOne := by
  intro h
  rw [q27yp_z7] at h
  have h1 : ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) = q3kZero :=
    congrArg (fun z : q27kCar => z.2.1) h
  exact q27yp_w2_nz h1

/-- **Z⁸ ≠ 1**（第 3 スロット ζ₉² ≠ 0）。 -/
theorem q27yp_z8_ne_one : q27ypZ8 ≠ q27kOne := by
  intro h
  rw [q27yp_z8] at h
  have h1 : ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) = q3kZero :=
    congrArg (fun z : q27kCar => z.2.2) h
  exact q27yp_w2_nz h1

/-- **Z⁹ ≠ 1**（Z⁹=embed ζ₃・ζ₃≠1——位数ちょうど 27 の核心）。 -/
theorem q27yp_z9_ne_one : q27ypZ9 ≠ q27kOne := by
  intro h
  rw [q27yp_z9] at h
  have h1 : q3kEmbed q3rqZeta = q3kOne := congrArg (fun z : q27kCar => z.1) h
  exact q27k_zeta3_ne_one h1

/-- **Z¹⁰ ≠ 1**（第 2 スロット ζ₃ ≠ 0）。 -/
theorem q27yp_z10_ne_one : q27ypZ10 ≠ q27kOne := by
  intro h
  rw [q27yp_z10] at h
  have h1 : q3kEmbed q3rqZeta = q3kZero := congrArg (fun z : q27kCar => z.2.1) h
  exact q27yp_w3_nz h1

/-- **Z¹¹ ≠ 1**（第 3 スロット ζ₃ ≠ 0）。 -/
theorem q27yp_z11_ne_one : q27ypZ11 ≠ q27kOne := by
  intro h
  rw [q27yp_z11] at h
  have h1 : q3kEmbed q3rqZeta = q3kZero := congrArg (fun z : q27kCar => z.2.2) h
  exact q27yp_w3_nz h1

/-- **Z¹² ≠ 1**（Z¹²=embed ζ₉⁴・ζ₉⁴≠1）。 -/
theorem q27yp_z12_ne_one : q27ypZ12 ≠ q27kOne := by
  intro h
  rw [q27yp_z12] at h
  have h1 : ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) = q3kOne :=
    congrArg (fun z : q27kCar => z.1) h
  exact q27yp_w4_no h1

/-- **Z¹³ ≠ 1**（第 2 スロット ζ₉⁴ ≠ 0）。 -/
theorem q27yp_z13_ne_one : q27ypZ13 ≠ q27kOne := by
  intro h
  rw [q27yp_z13] at h
  have h1 : ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) = q3kZero :=
    congrArg (fun z : q27kCar => z.2.1) h
  exact q27yp_w4_nz h1

/-- **Z¹⁴ ≠ 1**（第 3 スロット ζ₉⁴ ≠ 0）。 -/
theorem q27yp_z14_ne_one : q27ypZ14 ≠ q27kOne := by
  intro h
  rw [q27yp_z14] at h
  have h1 : ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) = q3kZero :=
    congrArg (fun z : q27kCar => z.2.2) h
  exact q27yp_w4_nz h1

/-- **Z¹⁵ ≠ 1**（Z¹⁵=embed ζ₉⁵・ζ₉⁵≠1）。 -/
theorem q27yp_z15_ne_one : q27ypZ15 ≠ q27kOne := by
  intro h
  rw [q27yp_z15] at h
  have h1 : ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) = q3kOne :=
    congrArg (fun z : q27kCar => z.1) h
  exact q27yp_w5_no h1

/-- **Z¹⁶ ≠ 1**（第 2 スロット ζ₉⁵ ≠ 0）。 -/
theorem q27yp_z16_ne_one : q27ypZ16 ≠ q27kOne := by
  intro h
  rw [q27yp_z16] at h
  have h1 : ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) = q3kZero :=
    congrArg (fun z : q27kCar => z.2.1) h
  exact q27yp_w5_nz h1

/-- **Z¹⁷ ≠ 1**（第 3 スロット ζ₉⁵ ≠ 0）。 -/
theorem q27yp_z17_ne_one : q27ypZ17 ≠ q27kOne := by
  intro h
  rw [q27yp_z17] at h
  have h1 : ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) = q3kZero :=
    congrArg (fun z : q27kCar => z.2.2) h
  exact q27yp_w5_nz h1

/-- **Z¹⁸ ≠ 1**（Z¹⁸=embed ζ₃²・ζ₃²≠1）。 -/
theorem q27yp_z18_ne_one : q27ypZ18 ≠ q27kOne := by
  intro h
  rw [q27yp_z18] at h
  have h1 : q3kEmbed q3rqZetaSq = q3kOne := congrArg (fun z : q27kCar => z.1) h
  exact q27yp_w6_no h1

/-- **Z¹⁹ ≠ 1**（第 2 スロット ζ₃² ≠ 0）。 -/
theorem q27yp_z19_ne_one : q27ypZ19 ≠ q27kOne := by
  intro h
  rw [q27yp_z19] at h
  have h1 : q3kEmbed q3rqZetaSq = q3kZero := congrArg (fun z : q27kCar => z.2.1) h
  exact q27yp_w6_nz h1

/-- **Z²⁰ ≠ 1**（第 3 スロット ζ₃² ≠ 0）。 -/
theorem q27yp_z20_ne_one : q27ypZ20 ≠ q27kOne := by
  intro h
  rw [q27yp_z20] at h
  have h1 : q3kEmbed q3rqZetaSq = q3kZero := congrArg (fun z : q27kCar => z.2.2) h
  exact q27yp_w6_nz h1

/-- **Z²¹ ≠ 1**（Z²¹=embed ζ₉⁷・ζ₉⁷≠1）。 -/
theorem q27yp_z21_ne_one : q27ypZ21 ≠ q27kOne := by
  intro h
  rw [q27yp_z21] at h
  have h1 : ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) = q3kOne :=
    congrArg (fun z : q27kCar => z.1) h
  exact q27yp_w7_no h1

/-- **Z²² ≠ 1**（第 2 スロット ζ₉⁷ ≠ 0）。 -/
theorem q27yp_z22_ne_one : q27ypZ22 ≠ q27kOne := by
  intro h
  rw [q27yp_z22] at h
  have h1 : ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) = q3kZero :=
    congrArg (fun z : q27kCar => z.2.1) h
  exact q27yp_w7_nz h1

/-- **Z²³ ≠ 1**（第 3 スロット ζ₉⁷ ≠ 0）。 -/
theorem q27yp_z23_ne_one : q27ypZ23 ≠ q27kOne := by
  intro h
  rw [q27yp_z23] at h
  have h1 : ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) = q3kZero :=
    congrArg (fun z : q27kCar => z.2.2) h
  exact q27yp_w7_nz h1

/-- **Z²⁴ ≠ 1**（Z²⁴=embed ζ₉⁸・ζ₉⁸≠1）。 -/
theorem q27yp_z24_ne_one : q27ypZ24 ≠ q27kOne := by
  intro h
  rw [q27yp_z24] at h
  have h1 : ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) = q3kOne :=
    congrArg (fun z : q27kCar => z.1) h
  exact q27yp_w8_no h1

/-- **Z²⁵ ≠ 1**（第 2 スロット ζ₉⁸ ≠ 0）。 -/
theorem q27yp_z25_ne_one : q27ypZ25 ≠ q27kOne := by
  intro h
  rw [q27yp_z25] at h
  have h1 : ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) = q3kZero :=
    congrArg (fun z : q27kCar => z.2.1) h
  exact q27yp_w8_nz h1

/-- **Z²⁶ ≠ 1**（第 3 スロット ζ₉⁸ ≠ 0）。 -/
theorem q27yp_z26_ne_one : q27ypZ26 ≠ q27kOne := by
  intro h
  rw [q27yp_z26] at h
  have h1 : ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) = q3kZero :=
    congrArg (fun z : q27kCar => z.2.2) h
  exact q27yp_w8_nz h1

/-! ## q27yp-7: capstone -/

/-- **q27yp-7a: Z-冪単項式正規形パックのデータ** — Zᵏ (k=2..26) の厳密単項式恒等式・
    Z²⁷=1（連鎖形）・位数ちょうど 27 補助 Zᵏ≠1 (k=1..26) を束ねる
    （q27tl/q27mb 再利用インタフェース・Q3KummerYPowData の level-27 クローン）。 -/
structure Q3KummerNonicYPowData where
  /-- Z² = (0,0,1)。 -/
  z2 : q27ypZ2 = ((q3kZero, q3kZero, q3kOne) : q27kCar)
  /-- Z³ = ζ₉。 -/
  z3 : q27ypZ3 = q27kEmbed q3kZeta9
  /-- Z⁴ = (0,ζ₉,0)。 -/
  z4 : q27ypZ4 = ((q3kZero, q3kZeta9, q3kZero) : q27kCar)
  /-- Z⁵ = (0,0,ζ₉)。 -/
  z5 : q27ypZ5 = ((q3kZero, q3kZero, q3kZeta9) : q27kCar)
  /-- Z⁶ = embed ζ₉²。 -/
  z6 : q27ypZ6 = q27kEmbed ((q3rqZero, q3rqZero, q3rqOne) : q3kCar)
  /-- Z⁷ = (0,ζ₉²,0)。 -/
  z7 : q27ypZ7 = ((q3kZero, ((q3rqZero, q3rqZero, q3rqOne) : q3kCar), q3kZero) : q27kCar)
  /-- Z⁸ = (0,0,ζ₉²)。 -/
  z8 : q27ypZ8 = ((q3kZero, q3kZero, ((q3rqZero, q3rqZero, q3rqOne) : q3kCar)) : q27kCar)
  /-- Z⁹ = ζ₃。 -/
  z9 : q27ypZ9 = q27kEmbed (q3kEmbed q3rqZeta)
  /-- Z¹⁰ = (0,ζ₃,0)。 -/
  z10 : q27ypZ10 = ((q3kZero, q3kEmbed q3rqZeta, q3kZero) : q27kCar)
  /-- Z¹¹ = (0,0,ζ₃)。 -/
  z11 : q27ypZ11 = ((q3kZero, q3kZero, q3kEmbed q3rqZeta) : q27kCar)
  /-- Z¹² = embed ζ₉⁴。 -/
  z12 : q27ypZ12 = q27kEmbed ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar)
  /-- Z¹³ = (0,ζ₉⁴,0)。 -/
  z13 : q27ypZ13 = ((q3kZero, ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar), q3kZero) : q27kCar)
  /-- Z¹⁴ = (0,0,ζ₉⁴)。 -/
  z14 : q27ypZ14 = ((q3kZero, q3kZero, ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar)) : q27kCar)
  /-- Z¹⁵ = embed ζ₉⁵。 -/
  z15 : q27ypZ15 = q27kEmbed ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar)
  /-- Z¹⁶ = (0,ζ₉⁵,0)。 -/
  z16 : q27ypZ16 = ((q3kZero, ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar), q3kZero) : q27kCar)
  /-- Z¹⁷ = (0,0,ζ₉⁵)。 -/
  z17 : q27ypZ17 = ((q3kZero, q3kZero, ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar)) : q27kCar)
  /-- Z¹⁸ = ζ₃²。 -/
  z18 : q27ypZ18 = q27kEmbed (q3kEmbed q3rqZetaSq)
  /-- Z¹⁹ = (0,ζ₃²,0)。 -/
  z19 : q27ypZ19 = ((q3kZero, q3kEmbed q3rqZetaSq, q3kZero) : q27kCar)
  /-- Z²⁰ = (0,0,ζ₃²)。 -/
  z20 : q27ypZ20 = ((q3kZero, q3kZero, q3kEmbed q3rqZetaSq) : q27kCar)
  /-- Z²¹ = embed ζ₉⁷。 -/
  z21 : q27ypZ21 = q27kEmbed ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar)
  /-- Z²² = (0,ζ₉⁷,0)。 -/
  z22 : q27ypZ22 = ((q3kZero, ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar), q3kZero) : q27kCar)
  /-- Z²³ = (0,0,ζ₉⁷)。 -/
  z23 : q27ypZ23 = ((q3kZero, q3kZero, ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar)) : q27kCar)
  /-- Z²⁴ = embed ζ₉⁸。 -/
  z24 : q27ypZ24 = q27kEmbed ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar)
  /-- Z²⁵ = (0,ζ₉⁸,0)。 -/
  z25 : q27ypZ25 = ((q3kZero, ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar), q3kZero) : q27kCar)
  /-- Z²⁶ = (0,0,ζ₉⁸)。 -/
  z26 : q27ypZ26 = ((q3kZero, q3kZero, ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar)) : q27kCar)
  /-- Z²⁷ = 1（連鎖形）。 -/
  z27 : q27ypZ27 = q27kOne
  /-- Z ≠ 1。 -/
  z1_ne : q27kZeta27 ≠ q27kOne
  /-- Z² ≠ 1。 -/
  z2_ne : q27ypZ2 ≠ q27kOne
  /-- Z³ ≠ 1。 -/
  z3_ne : q27ypZ3 ≠ q27kOne
  /-- Z⁴ ≠ 1。 -/
  z4_ne : q27ypZ4 ≠ q27kOne
  /-- Z⁵ ≠ 1。 -/
  z5_ne : q27ypZ5 ≠ q27kOne
  /-- Z⁶ ≠ 1。 -/
  z6_ne : q27ypZ6 ≠ q27kOne
  /-- Z⁷ ≠ 1。 -/
  z7_ne : q27ypZ7 ≠ q27kOne
  /-- Z⁸ ≠ 1。 -/
  z8_ne : q27ypZ8 ≠ q27kOne
  /-- Z⁹ ≠ 1。 -/
  z9_ne : q27ypZ9 ≠ q27kOne
  /-- Z¹⁰ ≠ 1。 -/
  z10_ne : q27ypZ10 ≠ q27kOne
  /-- Z¹¹ ≠ 1。 -/
  z11_ne : q27ypZ11 ≠ q27kOne
  /-- Z¹² ≠ 1。 -/
  z12_ne : q27ypZ12 ≠ q27kOne
  /-- Z¹³ ≠ 1。 -/
  z13_ne : q27ypZ13 ≠ q27kOne
  /-- Z¹⁴ ≠ 1。 -/
  z14_ne : q27ypZ14 ≠ q27kOne
  /-- Z¹⁵ ≠ 1。 -/
  z15_ne : q27ypZ15 ≠ q27kOne
  /-- Z¹⁶ ≠ 1。 -/
  z16_ne : q27ypZ16 ≠ q27kOne
  /-- Z¹⁷ ≠ 1。 -/
  z17_ne : q27ypZ17 ≠ q27kOne
  /-- Z¹⁸ ≠ 1。 -/
  z18_ne : q27ypZ18 ≠ q27kOne
  /-- Z¹⁹ ≠ 1。 -/
  z19_ne : q27ypZ19 ≠ q27kOne
  /-- Z²⁰ ≠ 1。 -/
  z20_ne : q27ypZ20 ≠ q27kOne
  /-- Z²¹ ≠ 1。 -/
  z21_ne : q27ypZ21 ≠ q27kOne
  /-- Z²² ≠ 1。 -/
  z22_ne : q27ypZ22 ≠ q27kOne
  /-- Z²³ ≠ 1。 -/
  z23_ne : q27ypZ23 ≠ q27kOne
  /-- Z²⁴ ≠ 1。 -/
  z24_ne : q27ypZ24 ≠ q27kOne
  /-- Z²⁵ ≠ 1。 -/
  z25_ne : q27ypZ25 ≠ q27kOne
  /-- Z²⁶ ≠ 1。 -/
  z26_ne : q27ypZ26 ≠ q27kOne

/-- **q27yp-7b: 見出し実例** — 実 O_{M₂₇}=q27k 上の Z=ζ₂₇ の単項式正規形パック。 -/
def q27yp_data : Q3KummerNonicYPowData where
  z2 := q27yp_z2
  z3 := q27yp_z3
  z4 := q27yp_z4
  z5 := q27yp_z5
  z6 := q27yp_z6
  z7 := q27yp_z7
  z8 := q27yp_z8
  z9 := q27yp_z9
  z10 := q27yp_z10
  z11 := q27yp_z11
  z12 := q27yp_z12
  z13 := q27yp_z13
  z14 := q27yp_z14
  z15 := q27yp_z15
  z16 := q27yp_z16
  z17 := q27yp_z17
  z18 := q27yp_z18
  z19 := q27yp_z19
  z20 := q27yp_z20
  z21 := q27yp_z21
  z22 := q27yp_z22
  z23 := q27yp_z23
  z24 := q27yp_z24
  z25 := q27yp_z25
  z26 := q27yp_z26
  z27 := q27yp_z27
  z1_ne := q27yp_z1_ne_one
  z2_ne := q27yp_z2_ne_one
  z3_ne := q27yp_z3_ne_one
  z4_ne := q27yp_z4_ne_one
  z5_ne := q27yp_z5_ne_one
  z6_ne := q27yp_z6_ne_one
  z7_ne := q27yp_z7_ne_one
  z8_ne := q27yp_z8_ne_one
  z9_ne := q27yp_z9_ne_one
  z10_ne := q27yp_z10_ne_one
  z11_ne := q27yp_z11_ne_one
  z12_ne := q27yp_z12_ne_one
  z13_ne := q27yp_z13_ne_one
  z14_ne := q27yp_z14_ne_one
  z15_ne := q27yp_z15_ne_one
  z16_ne := q27yp_z16_ne_one
  z17_ne := q27yp_z17_ne_one
  z18_ne := q27yp_z18_ne_one
  z19_ne := q27yp_z19_ne_one
  z20_ne := q27yp_z20_ne_one
  z21_ne := q27yp_z21_ne_one
  z22_ne := q27yp_z22_ne_one
  z23_ne := q27yp_z23_ne_one
  z24_ne := q27yp_z24_ne_one
  z25_ne := q27yp_z25_ne_one
  z26_ne := q27yp_z26_ne_one

/-- **q27yp-7c: Z-冪単項式正規形パックの存在**（実 O_{M₂₇}=q27k 上）。 -/
theorem q27yp_exists : Nonempty Q3KummerNonicYPowData := ⟨q27yp_data⟩

end IUT
