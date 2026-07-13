/-
  IUT/Q3KummerYPow.lean — level-9 テータ kill 用 Y-冪（ζ₉-冪）単項式正規形パック
    （実 3 次代数 M = q3k 上の Y=ζ₉ の冪 Yᵏ (k=2..8) の単項式還元＋位数ちょうど 9 補助）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**（骨格・模型・代理でなく、q3k で建てた
     **実** M = ℚ₃(ζ₉) = L₂[Y]/(Y³−ζ₃) の上で、実 ζ₉ = Y の冪 Yᵏ を Y³=ζ₃ の
     ねじれ畳み込みで単項式正規形（ζ₃ᵢ·Yʲ 型の座標三つ組）へ還元し、Yᵏ≠1 (k=1..8) の
     位数ちょうど 9 補助補題を実に建てる。toy 主語なし——主語は実 q3rq-係数 3 次代数。）

  complete_pct 影響: **0 前進**（foundation・再利用部品）。本モジュールは level-9
  実 Tate 曲線 [ζ₉] の位数ちょうど 9 証明（q9tl）と橋の kill 分岐解析（q9mb）の
  再利用部品であって、kill 本体・μ₉ 完全性・剛性は後続モジュール。complete_pct は
  動かさない（正直に「complete_pct 0 前進（骨格でなく本物の再利用部品の先行建設）」）。

  内容:
   * q9ypY2 .. q9ypY8 — Yᵏ を左結合 q3kMul 連鎖 Yᵏ=Yᵏ⁻¹·Y で定義（q3k の連鎖慣習に整合）
   * q9yp_mulY_100 / q9yp_mulY_010 / q9yp_mulY_001
        — 「·Y」1 段の実還元ヘルパ: embed n·Y=(0,n,0)・(0,b,0)·Y=(0,0,b)・(0,0,c)·Y=embed(ζ₃c)
   * q9yp_y2 .. q9yp_y8 — 単項式正規形の厳密恒等式:
        Y²=(0,0,1)・Y³=ζ₃・Y⁴=ζ₃Y=(0,ζ₃,0)・Y⁵=ζ₃Y²=(0,0,ζ₃)・
        Y⁶=ζ₃²・Y⁷=ζ₃²Y=(0,ζ₃²,0)・Y⁸=ζ₃²Y²=(0,0,ζ₃²)（q9yp_y4_prod は Y⁴ の積形も提供）
   * q9yp_y1_ne_one .. q9yp_y8_ne_one — 位数ちょうど 9 補助: Yᵏ≠1 (k=1..8)
        k∈{1,2,4,5,7,8} は非零スロット矛盾・k=3,6 は embed ζ₃^{±1}≠1
   * Q3KummerYPowData / q9yp_data / q9yp_exists — capstone

  正直な限定（§4 規約により消さない・弱化しない・q3k 継承の上に追記のみ）:
  1. **純単項式恒等式＋位数 9 補助のみ**。テータ関数ゼロ・kill ゼロ・剛性ゼロ
     （level-9 kill 本体は q9tl/q9mt/q9mr/q9mb が担う）。
  2. q3k の全正直限定（O_M と M^× のみ・体でない・付値/位相は範囲外・σ を超える
     Galois 作用ゼロ・π₁ 同定ゼロ等）を**そのまま継承**する。
  3. Y の冪の Nat 添字関数は導入せず、下流（q9tl/q9mb）が直接消費する左結合連鎖
     の名前付き定義 q9ypY2..q9ypY8 を正準形とする（数値簡約の脆さ回避・q3k 慣習整合）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3KummerCubic

namespace IUT

/-! ## q9yp-0: Y の冪（左結合 q3kMul 連鎖 Yᵏ = Yᵏ⁻¹·Y、Y=q3kZeta9） -/

/-- Y² = Y·Y。 -/
def q9ypY2 : q3kCar := q3kMul q3kZeta9 q3kZeta9
/-- Y³ = Y²·Y。 -/
def q9ypY3 : q3kCar := q3kMul q9ypY2 q3kZeta9
/-- Y⁴ = Y³·Y。 -/
def q9ypY4 : q3kCar := q3kMul q9ypY3 q3kZeta9
/-- Y⁵ = Y⁴·Y。 -/
def q9ypY5 : q3kCar := q3kMul q9ypY4 q3kZeta9
/-- Y⁶ = Y⁵·Y。 -/
def q9ypY6 : q3kCar := q3kMul q9ypY5 q3kZeta9
/-- Y⁷ = Y⁶·Y。 -/
def q9ypY7 : q3kCar := q3kMul q9ypY6 q3kZeta9
/-- Y⁸ = Y⁷·Y。 -/
def q9ypY8 : q3kCar := q3kMul q9ypY7 q3kZeta9

/-! ## q9yp-1: 「·Y」1 段の実還元ヘルパ（Y=(0,1,0) の右乗の座標作用） -/

/-- **q9yp-1a: embed(n)·Y = (0,n,0)**（(n,0,0)·(0,1,0) の還元）。 -/
theorem q9yp_mulY_100 (n : q3rqCar) :
    q3kMul (q3kEmbed n) q3kZeta9 = ((q3rqZero, n, q3rqZero) : q3kCar) := by
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul n q3rqRing.zero)
        (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero)
          (q3rqRing.mul q3rqRing.zero q3rqRing.one))) = q3rqRing.zero
    rw [q3rqRing.mul_zero n, q3rqRing.mul_zero q3rqRing.zero, q3rqRing.zero_mul q3rqRing.one,
      q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul n q3rqRing.one)
        (q3rqRing.mul q3rqRing.zero q3rqRing.zero))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqRing.zero q3rqRing.zero)) = n
    rw [q3rqRing.mul_one n, q3rqRing.mul_zero q3rqRing.zero, q3rqRing.add_zero n,
      q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero n]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul n q3rqRing.zero)
        (q3rqRing.mul q3rqRing.zero q3rqRing.one)) (q3rqRing.mul q3rqRing.zero q3rqRing.zero)
        = q3rqRing.zero
    rw [q3rqRing.mul_zero n, q3rqRing.zero_mul q3rqRing.one, q3rqRing.add_zero q3rqRing.zero,
      q3rqRing.mul_zero q3rqRing.zero, q3rqRing.add_zero q3rqRing.zero]

/-- **q9yp-1b: (0,b,0)·Y = (0,0,b)**。 -/
theorem q9yp_mulY_010 (b : q3rqCar) :
    q3kMul ((q3rqZero, b, q3rqZero) : q3kCar) q3kZeta9 = ((q3rqZero, q3rqZero, b) : q3kCar) := by
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero)
        (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul b q3rqRing.zero)
          (q3rqRing.mul q3rqRing.zero q3rqRing.one))) = q3rqRing.zero
    rw [q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_zero b, q3rqRing.zero_mul q3rqRing.one,
      q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.one)
        (q3rqRing.mul b q3rqRing.zero))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqRing.zero q3rqRing.zero)) = q3rqRing.zero
    rw [q3rqRing.zero_mul q3rqRing.one, q3rqRing.mul_zero b, q3rqRing.add_zero q3rqRing.zero,
      q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero)
        (q3rqRing.mul b q3rqRing.one)) (q3rqRing.mul q3rqRing.zero q3rqRing.zero) = b
    rw [q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_one b, q3rqRing.zero_add b,
      q3rqRing.add_zero b]

/-- **q9yp-1c: (0,0,c)·Y = embed(ζ₃·c)**（Y³=ζ₃ のねじれで定数部へ）。 -/
theorem q9yp_mulY_001 (c : q3rqCar) :
    q3kMul ((q3rqZero, q3rqZero, c) : q3kCar) q3kZeta9 = q3kEmbed (q3rqMul q3rqZeta c) := by
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero)
        (q3rqRing.mul q3rqZeta (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero)
          (q3rqRing.mul c q3rqRing.one))) = q3rqRing.mul q3rqZeta c
    rw [q3rqRing.mul_zero q3rqRing.zero, q3rqRing.mul_one c,
      q3rqRing.zero_add c, q3rqRing.zero_add (q3rqRing.mul q3rqZeta c)]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.one)
        (q3rqRing.mul q3rqRing.zero q3rqRing.zero))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul c q3rqRing.zero)) = q3rqRing.zero
    rw [q3rqRing.zero_mul q3rqRing.one, q3rqRing.mul_zero q3rqRing.zero,
      q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero c, q3rqRing.mul_zero q3rqZeta,
      q3rqRing.add_zero q3rqRing.zero]
  · show q3rqRing.add (q3rqRing.add (q3rqRing.mul q3rqRing.zero q3rqRing.zero)
        (q3rqRing.mul q3rqRing.zero q3rqRing.one)) (q3rqRing.mul c q3rqRing.zero) = q3rqRing.zero
    rw [q3rqRing.mul_zero q3rqRing.zero, q3rqRing.zero_mul q3rqRing.one,
      q3rqRing.add_zero q3rqRing.zero, q3rqRing.mul_zero c, q3rqRing.add_zero q3rqRing.zero]

/-! ## q9yp-2: 単項式正規形の厳密恒等式 Yᵏ (k=2..8) -/

/-- **q9yp-2a: Y² = (0,0,1)**。 -/
theorem q9yp_y2 : q9ypY2 = ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) := q3k_zeta9_sq

/-- **q9yp-2b: Y³ = ζ₃**（embed・q3k_zeta9_cube の再掲）。 -/
theorem q9yp_y3 : q9ypY3 = q3kEmbed q3rqZeta := q3k_zeta9_cube

/-- **q9yp-2c: Y⁴ = ζ₃·Y = (0,ζ₃,0)**。 -/
theorem q9yp_y4 : q9ypY4 = ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) := by
  show q3kMul q9ypY3 q3kZeta9 = _
  rw [q9yp_y3]; exact q9yp_mulY_100 q3rqZeta

/-- Y⁴ の積形 ζ₃·Y（下流の積形消費用）。 -/
theorem q9yp_y4_prod : q9ypY4 = q3kMul (q3kEmbed q3rqZeta) q3kZeta9 := by
  show q3kMul q9ypY3 q3kZeta9 = _
  rw [q9yp_y3]

/-- **q9yp-2d: Y⁵ = ζ₃·Y² = (0,0,ζ₃)**。 -/
theorem q9yp_y5 : q9ypY5 = ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) := by
  show q3kMul q9ypY4 q3kZeta9 = _
  rw [q9yp_y4]; exact q9yp_mulY_010 q3rqZeta

/-- **q9yp-2e: Y⁶ = ζ₃²**（embed・(0,0,ζ₃)·Y=embed(ζ₃·ζ₃)=embed ζ₃²）。 -/
theorem q9yp_y6 : q9ypY6 = q3kEmbed q3rqZetaSq := by
  show q3kMul q9ypY5 q3kZeta9 = _
  rw [q9yp_y5]; exact q9yp_mulY_001 q3rqZeta

/-- **q9yp-2f: Y⁷ = ζ₃²·Y = (0,ζ₃²,0)**。 -/
theorem q9yp_y7 : q9ypY7 = ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) := by
  show q3kMul q9ypY6 q3kZeta9 = _
  rw [q9yp_y6]; exact q9yp_mulY_100 q3rqZetaSq

/-- **q9yp-2g: Y⁸ = ζ₃²·Y² = (0,0,ζ₃²)**。 -/
theorem q9yp_y8 : q9ypY8 = ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) := by
  show q3kMul q9ypY7 q3kZeta9 = _
  rw [q9yp_y7]; exact q9yp_mulY_010 q3rqZetaSq

/-! ## q9yp-3: 位数ちょうど 9 補助 Yᵏ ≠ 1 (k=1..8) -/

/-- **q9yp-3a: Y ≠ 1**（q3k_zeta9_ne_one の再掲）。 -/
theorem q9yp_y1_ne_one : q3kZeta9 ≠ q3kOne := q3k_zeta9_ne_one

/-- **q9yp-3b: Y² ≠ 1**（第 3 スロット 1 ≠ 0）。 -/
theorem q9yp_y2_ne_one : q9ypY2 ≠ q3kOne := by
  intro h
  rw [q9yp_y2] at h
  have h1 : q3rqOne = q3rqZero := congrArg (fun z : q3kCar => z.2.2) h
  have h2 : z3.one = z3.zero := congrArg (fun p : q3rqCar => p.1) h1
  exact q3rq_z3_one_ne_zero h2

/-- **q9yp-3c: Y³ ≠ 1**（Y³=embed ζ₃・ζ₃≠1）。 -/
theorem q9yp_y3_ne_one : q9ypY3 ≠ q3kOne := by
  intro h
  rw [q9yp_y3, ← q3k_embed_one] at h
  exact q3rq_zeta_ne_one (q3k_embed_inj h)

/-- **q9yp-3d: Y⁴ ≠ 1**（第 2 スロット ζ₃≠0・h≠0）。 -/
theorem q9yp_y4_ne_one : q9ypY4 ≠ q3kOne := by
  intro h
  rw [q9yp_y4] at h
  have h1 : q3rqZeta = q3rqZero := congrArg (fun z : q3kCar => z.2.1) h
  have h2 : q3rqHalf = z3.zero := congrArg (fun p : q3rqCar => p.2) h1
  exact q3rq_half_ne_zero h2

/-- **q9yp-3e: Y⁵ ≠ 1**（第 3 スロット ζ₃≠0）。 -/
theorem q9yp_y5_ne_one : q9ypY5 ≠ q3kOne := by
  intro h
  rw [q9yp_y5] at h
  have h1 : q3rqZeta = q3rqZero := congrArg (fun z : q3kCar => z.2.2) h
  have h2 : q3rqHalf = z3.zero := congrArg (fun p : q3rqCar => p.2) h1
  exact q3rq_half_ne_zero h2

/-- **q9yp-3f: Y⁶ ≠ 1**（Y⁶=embed ζ₃²・ζ₃²≠1）。 -/
theorem q9yp_y6_ne_one : q9ypY6 ≠ q3kOne := by
  intro h
  rw [q9yp_y6, ← q3k_embed_one] at h
  exact q3rq_zeta_sq_ne_one (q3k_embed_inj h)

/-- **q9yp-3g: Y⁷ ≠ 1**（第 2 スロット ζ₃²≠0・−h≠0）。 -/
theorem q9yp_y7_ne_one : q9ypY7 ≠ q3kOne := by
  intro h
  rw [q9yp_y7] at h
  have h1 : q3rqZetaSq = q3rqZero := congrArg (fun z : q3kCar => z.2.1) h
  have h1' : q3rqMul q3rqZeta q3rqZeta = q3rqZero := h1
  rw [q3rq_zeta_sq_eq] at h1'
  have h2 : z3.neg q3rqHalf = z3.zero := congrArg (fun p : q3rqCar => p.2) h1'
  exact q3rq_neg_half_ne_zero h2

/-- **q9yp-3h: Y⁸ ≠ 1**（第 3 スロット ζ₃²≠0）。 -/
theorem q9yp_y8_ne_one : q9ypY8 ≠ q3kOne := by
  intro h
  rw [q9yp_y8] at h
  have h1 : q3rqZetaSq = q3rqZero := congrArg (fun z : q3kCar => z.2.2) h
  have h1' : q3rqMul q3rqZeta q3rqZeta = q3rqZero := h1
  rw [q3rq_zeta_sq_eq] at h1'
  have h2 : z3.neg q3rqHalf = z3.zero := congrArg (fun p : q3rqCar => p.2) h1'
  exact q3rq_neg_half_ne_zero h2

/-! ## q9yp-4: capstone -/

/-- **q9yp-4a: Y-冪単項式正規形パックのデータ** — Yᵏ (k=2..8) の厳密単項式恒等式と
    位数ちょうど 9 補助 Yᵏ≠1 (k=1..8) を束ねる（q9tl/q9mb 再利用インタフェース）。 -/
structure Q3KummerYPowData where
  /-- Y² = (0,0,1)。 -/
  y2 : q9ypY2 = ((q3rqZero, q3rqZero, q3rqOne) : q3kCar)
  /-- Y³ = ζ₃。 -/
  y3 : q9ypY3 = q3kEmbed q3rqZeta
  /-- Y⁴ = (0,ζ₃,0)。 -/
  y4 : q9ypY4 = ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar)
  /-- Y⁵ = (0,0,ζ₃)。 -/
  y5 : q9ypY5 = ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar)
  /-- Y⁶ = ζ₃²。 -/
  y6 : q9ypY6 = q3kEmbed q3rqZetaSq
  /-- Y⁷ = (0,ζ₃²,0)。 -/
  y7 : q9ypY7 = ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar)
  /-- Y⁸ = (0,0,ζ₃²)。 -/
  y8 : q9ypY8 = ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar)
  /-- Y ≠ 1。 -/
  y1_ne : q3kZeta9 ≠ q3kOne
  /-- Y² ≠ 1。 -/
  y2_ne : q9ypY2 ≠ q3kOne
  /-- Y³ ≠ 1。 -/
  y3_ne : q9ypY3 ≠ q3kOne
  /-- Y⁴ ≠ 1。 -/
  y4_ne : q9ypY4 ≠ q3kOne
  /-- Y⁵ ≠ 1。 -/
  y5_ne : q9ypY5 ≠ q3kOne
  /-- Y⁶ ≠ 1。 -/
  y6_ne : q9ypY6 ≠ q3kOne
  /-- Y⁷ ≠ 1。 -/
  y7_ne : q9ypY7 ≠ q3kOne
  /-- Y⁸ ≠ 1。 -/
  y8_ne : q9ypY8 ≠ q3kOne

/-- **q9yp-4b: 見出し実例** — 実 M=q3k 上の Y=ζ₉ の単項式正規形パック。 -/
def q9yp_data : Q3KummerYPowData where
  y2 := q9yp_y2
  y3 := q9yp_y3
  y4 := q9yp_y4
  y5 := q9yp_y5
  y6 := q9yp_y6
  y7 := q9yp_y7
  y8 := q9yp_y8
  y1_ne := q9yp_y1_ne_one
  y2_ne := q9yp_y2_ne_one
  y3_ne := q9yp_y3_ne_one
  y4_ne := q9yp_y4_ne_one
  y5_ne := q9yp_y5_ne_one
  y6_ne := q9yp_y6_ne_one
  y7_ne := q9yp_y7_ne_one
  y8_ne := q9yp_y8_ne_one

/-- **q9yp-4c: Y-冪単項式正規形パックの存在**（実 M=q3k 上）。 -/
theorem q9yp_exists : Nonempty Q3KummerYPowData := ⟨q9yp_data⟩

end IUT
