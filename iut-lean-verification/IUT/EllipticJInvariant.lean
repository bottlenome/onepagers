/-
  IUT/EllipticJInvariant.lean — M310F: 楕円曲線の j-不変量と同型分類の核 — 柱A

  ── 主要成果の分類: **[実]**（本物の体 K 上の本物の短 Weierstrass 楕円曲線
     y²=x³+ax+b の j-不変量 j(E)=1728·4a³/(4a³+27b²) の本物構成と、変数変換
     (a,b)↦(u⁴a,u⁶b) の下での **j の同型不変性 j(E)=j(E')** の完全証明。
     toy 主語なし——M304F の本物の Weierstrass データと M264F の本物の体の上で建てる）。

  complete_pct 影響: **柱A「楕円曲線の分類（j-不変量）」の本物の先行建設**。IUT は
  数体上の楕円曲線 E を主対象に据え、その同型類（=モジュライ点）を j-不変量で
  分類する。現状コードベースには「楕円曲線の同型不変量 j」の本物構成が無い。
  本ファイルは M304F の本物の Weierstrass データ（判別式 Δ=−16(4a³+27b²)）の上に:
  (1) **j-不変量 j=1728·4a³/(4a³+27b²) を本物構成**（M264F の体の逆元 inv で除算）、
  (2) **判別式の u¹² 変換 Δ(u⁴a,u⁶b)=u¹²·Δ(a,b) を本物で証明**、
  (3) **j の同型不変性 j(u⁴a,u⁶b)=j(a,b) を本物で証明**（比 u¹² が分子分母で相殺）、
  (4) 特殊値 j=0 ⟺ a=0（構成的な対偶を含む本物）・b=0 ⟹ j=1728（本物）、
  (5) ℚ 上の実例 y²=x³+1 の j=0、y²=x³+x の j=1728 を本物で確認。
  これで柱Aの「j による同型分類」の代数的核が本物で閉じる。

  * M310F-1 冪 `ellJPow`（u^n）・冪の和則 `ellJPow_add`・非零性 `ellJPow_ne_zero`
  * M310F-2 斉次性 `ellJ_cube_mul`/`ellJ_sq_mul`・(u⁴)³=(u⁶)²=u¹²
    (`ellJ_cube_pow4`/`ellJ_sq_pow6`)・変換の斉次性 `ellJ_cube_transform`/`ellJ_sq_transform`
  * M310F-3 変数変換 `ellJTransform` (a,b)↦(u⁴a,u⁶b)
  * M310F-4 **簡約判別式の u¹² 変換** `ellJ_reduced_discr_transform`・
    **判別式の u¹² 変換** `ellJ_discr_transform`（本丸の一つ）
  * M310F-5 **j-不変量** `ellJInvariant`・well-defined `ellJ_reduced_ne_zero_of_nonsingular`
  * M310F-6 **j の同型不変性** `ellJ_iso_invariant`（本丸）= j(u⁴a,u⁶b)=j(a,b)
  * M310F-7 特殊値: `ellJ_zero_of_a_zero`（a=0⟹j=0）/ `ellJ_cube_ne_zero` /
    `ellJ_ne_zero_of_a_ne_zero`（a≠0⟹j≠0＝j=0⟺a=0 の構成的対偶）/
    `ellJ_1728_of_b_zero`（b=0⟹j=1728）
  * M310F-8 capstone `EllipticJData`・`ellJ_exists`・`ellJ_invariant`・`ellJ_discr_scaling`・
    ℚ 実例 y²=x³+1 の j=0、y²=x³+x の j=1728

  正直な限定（何が本物で何が未達か）:
  - **本物（完全証明・sorry 皆無・新規 Classical.choice 皆無）**:
    (1) j-不変量 j=1728·4a³/(4a³+27b²) の定義と、Δ≠0（⇔4a³+27b²≠0）での
        well-defined 性（`ellJ_reduced_ne_zero_of_nonsingular`）、
    (2) 判別式の u¹² 変換 Δ(u⁴a,u⁶b)=u¹²·Δ(a,b)（`ellJ_discr_transform`）、
    (3) j の同型不変性 j(u⁴a,u⁶b)=j(a,b)（`ellJ_iso_invariant`）、
    (4) j=0 ⟺ a=0（a=0⟹j=0 と、その構成的対偶 a≠0⟹j≠0）、b=0⟹j=1728、
    (5) ℚ 上 y²=x³+1 の j=0、y²=x³+x の j=1728。
  - **未達（正直申告・後続）**:
    * **変数変換 (u⁴a,u⁶b) による同型は「係数の変換」レベルで本物**。点の対応
      x↦u²x, y↦u³y が曲線 y²=x³+ax+b を保つこと（点集合・群構造レベルの同型）の
      完全証明は M304F の一般弦接線加法の閉性接続の後続。
    * **j 完全分類定理**（同一 j ⟹ 同型、代数閉体上）は後続。ここは j の定義・
      Δ の u¹² 変換・j の同型不変性を本物で閉じる（分類の「必要方向＝不変量が一致」）。
    * j=1728 の逆（j=1728 ⟹ b=0）は 1728·(4a³+27b²)=1728·4a³ ⟹ 27b²=0 の判定に
      char≠2,3 と b=0 判定を要し、一般体では未達（b=0 ⟹ j=1728 の順方向のみ本物）。
    * 特殊値 j=0⟺a=0 の逆は「a≠0⟹j≠0」の**構成的対偶**として本物に閉じる
      （1728≠0・4≠0・分母≠0 を仮説に取る。一般体では 1728,4 の非零性は char に依存）。
    * j-line（モジュライ空間）・supersingular j・還元・Tate 曲線は後続（柱E 等）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
-/
import IUT.EllipticCurve

namespace IUT

/-! ## M310F-1: 冪 u^n・冪の和則・非零性 -/

/-- **M310F-1a: 冪** u^n（変数変換 u⁴,u⁶,u¹² 用）。 -/
def ellJPow (F : IUTField) (u : F.carrier) : Nat → F.carrier
  | 0 => F.one
  | n + 1 => F.mul (ellJPow F u n) u

/-- **M310F-1b: 冪の和則** u^(m+n) = u^m · u^n（本物・n について帰納）。 -/
theorem ellJPow_add (F : IUTField) (u : F.carrier) (m : Nat) :
    ∀ n, ellJPow F u (m + n) = F.mul (ellJPow F u m) (ellJPow F u n)
  | 0 => by
      show ellJPow F u m = F.mul (ellJPow F u m) F.one
      rw [ellCurve_mul_one F (ellJPow F u m)]
  | n + 1 => by
      show F.mul (ellJPow F u (m + n)) u
        = F.mul (ellJPow F u m) (F.mul (ellJPow F u n) u)
      rw [ellJPow_add F u m n, F.mul_assoc (ellJPow F u m) (ellJPow F u n) u]

/-- **M310F-1c: 冪の非零性** u≠0 ⟹ u^n≠0（本物）。 -/
theorem ellJPow_ne_zero (F : IUTField) {u : F.carrier} (hu : u ≠ F.zero) :
    ∀ n, ellJPow F u n ≠ F.zero
  | 0 => F.one_ne_zero
  | n + 1 => F.mul_ne_zero (ellJPow_ne_zero F hu n) hu

/-! ## M310F-2: 斉次性（cube・sq の乗法分離）と (u⁴)³=(u⁶)²=u¹² -/

/-- 左入れ替え x·(y·z) = y·(x·z)（本物）。 -/
theorem ellJ_mul_left_swap (F : IUTField) (x y z : F.carrier) :
    F.mul x (F.mul y z) = F.mul y (F.mul x z) := by
  rw [← F.mul_assoc x y z, F.mul_comm x y, F.mul_assoc y x z]

/-- **M310F-2a: 立方の斉次性** (p·a)³ = p³·a³（本物）。 -/
theorem ellJ_cube_mul (F : IUTField) (p a : F.carrier) :
    ellCurveCube F (F.mul p a)
      = F.mul (ellCurveCube F p) (ellCurveCube F a) := by
  show F.mul (F.mul p a) (F.mul (F.mul p a) (F.mul p a))
    = F.mul (F.mul p (F.mul p p)) (F.mul a (F.mul a a))
  rw [F.mul_mul_mul_comm p a p a,
    F.mul_mul_mul_comm p a (F.mul p p) (F.mul a a)]

/-- **M310F-2b: 平方の斉次性** (q·b)² = q²·b²（本物）。 -/
theorem ellJ_sq_mul (F : IUTField) (q b : F.carrier) :
    ellCurveSq F (F.mul q b) = F.mul (ellCurveSq F q) (ellCurveSq F b) := by
  show F.mul (F.mul q b) (F.mul q b) = F.mul (F.mul q q) (F.mul b b)
  rw [F.mul_mul_mul_comm q b q b]

/-- **M310F-2c: (u⁴)³ = u¹²**（本物・冪の和則で 4+4=8, 4+8=12）。 -/
theorem ellJ_cube_pow4 (F : IUTField) (u : F.carrier) :
    ellCurveCube F (ellJPow F u 4) = ellJPow F u 12 := by
  have h1 : ellJPow F u 8 = F.mul (ellJPow F u 4) (ellJPow F u 4) :=
    ellJPow_add F u 4 4
  have h2 : ellJPow F u 12 = F.mul (ellJPow F u 4) (ellJPow F u 8) :=
    ellJPow_add F u 4 8
  show F.mul (ellJPow F u 4) (F.mul (ellJPow F u 4) (ellJPow F u 4))
    = ellJPow F u 12
  rw [← h1, ← h2]

/-- **M310F-2d: (u⁶)² = u¹²**（本物・6+6=12）。 -/
theorem ellJ_sq_pow6 (F : IUTField) (u : F.carrier) :
    ellCurveSq F (ellJPow F u 6) = ellJPow F u 12 := by
  have h : ellJPow F u 12 = F.mul (ellJPow F u 6) (ellJPow F u 6) :=
    ellJPow_add F u 6 6
  show F.mul (ellJPow F u 6) (ellJPow F u 6) = ellJPow F u 12
  rw [← h]

/-- **M310F-2e: 立方の変換** (u⁴·a)³ = u¹²·a³（本物）。 -/
theorem ellJ_cube_transform (F : IUTField) (u a : F.carrier) :
    ellCurveCube F (F.mul (ellJPow F u 4) a)
      = F.mul (ellJPow F u 12) (ellCurveCube F a) := by
  rw [ellJ_cube_mul F (ellJPow F u 4) a, ellJ_cube_pow4 F u]

/-- **M310F-2f: 平方の変換** (u⁶·b)² = u¹²·b²（本物）。 -/
theorem ellJ_sq_transform (F : IUTField) (u b : F.carrier) :
    ellCurveSq F (F.mul (ellJPow F u 6) b)
      = F.mul (ellJPow F u 12) (ellCurveSq F b) := by
  rw [ellJ_sq_mul F (ellJPow F u 6) b, ellJ_sq_pow6 F u]

/-! ## M310F-3: 変数変換 (a,b) ↦ (u⁴a, u⁶b) -/

/-- **M310F-3: Weierstrass 係数の変数変換** — x↦u²x, y↦u³y に対応する
    (a,b)↦(u⁴a, u⁶b)（同型 E≅E' の係数レベル）。 -/
def ellJTransform (F : IUTField) (u : F.carrier)
    (w : ellCurveWeierstrass F) : ellCurveWeierstrass F where
  a := F.mul (ellJPow F u 4) w.a
  b := F.mul (ellJPow F u 6) w.b

/-! ## M310F-4: 判別式の u¹² 変換（本丸の一つ） -/

/-- **M310F-4a: 簡約判別式の u¹² 変換** — 4(u⁴a)³+27(u⁶b)² = u¹²·(4a³+27b²)（本物）。 -/
theorem ellJ_reduced_discr_transform (F : IUTField) (u : F.carrier)
    (w : ellCurveWeierstrass F) :
    ellCurveReducedDiscr F (ellJTransform F u w)
      = F.mul (ellJPow F u 12) (ellCurveReducedDiscr F w) := by
  show F.add
      (F.mul (ellCurveNat F 4) (ellCurveCube F (F.mul (ellJPow F u 4) w.a)))
      (F.mul (ellCurveNat F 27) (ellCurveSq F (F.mul (ellJPow F u 6) w.b)))
    = F.mul (ellJPow F u 12)
        (F.add (F.mul (ellCurveNat F 4) (ellCurveCube F w.a))
          (F.mul (ellCurveNat F 27) (ellCurveSq F w.b)))
  rw [ellJ_cube_transform F u w.a, ellJ_sq_transform F u w.b,
    ellJ_mul_left_swap F (ellCurveNat F 4) (ellJPow F u 12) (ellCurveCube F w.a),
    ellJ_mul_left_swap F (ellCurveNat F 27) (ellJPow F u 12) (ellCurveSq F w.b),
    ← F.left_distrib (ellJPow F u 12)
        (F.mul (ellCurveNat F 4) (ellCurveCube F w.a))
        (F.mul (ellCurveNat F 27) (ellCurveSq F w.b))]

/-- **M310F-4b: 判別式の u¹² 変換** — Δ(u⁴a,u⁶b) = u¹²·Δ(a,b)（本物）。 -/
theorem ellJ_discr_transform (F : IUTField) (u : F.carrier)
    (w : ellCurveWeierstrass F) :
    ellCurveDiscriminant F (ellJTransform F u w)
      = F.mul (ellJPow F u 12) (ellCurveDiscriminant F w) := by
  show F.neg (F.mul (ellCurveNat F 16)
      (ellCurveReducedDiscr F (ellJTransform F u w)))
    = F.mul (ellJPow F u 12)
        (F.neg (F.mul (ellCurveNat F 16) (ellCurveReducedDiscr F w)))
  rw [ellJ_reduced_discr_transform F u w,
    ellJ_mul_left_swap F (ellCurveNat F 16) (ellJPow F u 12)
      (ellCurveReducedDiscr F w),
    ellCurve_mul_neg F (ellJPow F u 12)
      (F.mul (ellCurveNat F 16) (ellCurveReducedDiscr F w))]

/-! ## M310F-5: j-不変量 j = 1728·4a³/(4a³+27b²) -/

/-- **M310F-5a: j-不変量** j(E) = 1728·4a³/(4a³+27b²)（本物・M264F 逆元 inv で除算）。
    分母 4a³+27b² は Δ=−16(4a³+27b²)≠0 のとき非零で、j は well-defined。 -/
def ellJInvariant (F : IUTField) (w : ellCurveWeierstrass F) : F.carrier :=
  F.mul
    (F.mul (ellCurveNat F 1728) (F.mul (ellCurveNat F 4) (ellCurveCube F w.a)))
    (F.inv (ellCurveReducedDiscr F w))

/-- neg 0 = 0（本物）。 -/
theorem ellJ_neg_zero (F : IUTField) : F.neg F.zero = F.zero := by
  have h : F.add (F.neg F.zero) F.zero = F.zero := F.neg_add F.zero
  rw [ellCurve_add_zero F (F.neg F.zero)] at h
  exact h

/-- **M310F-5b: well-defined 性** — 非特異（Δ≠0）なら分母 4a³+27b²≠0（本物）。 -/
theorem ellJ_reduced_ne_zero_of_nonsingular (F : IUTField)
    (w : ellCurveWeierstrass F) (h : ellCurveNonsingular F w) :
    ellCurveReducedDiscr F w ≠ F.zero := by
  intro hc
  apply h
  show F.neg (F.mul (ellCurveNat F 16) (ellCurveReducedDiscr F w)) = F.zero
  rw [hc, F.toCRing.mul_zero (ellCurveNat F 16), ellJ_neg_zero F]

/-! ## M310F-6: 分子の u¹² 変換と j の同型不変性（本丸） -/

/-- **M310F-6a: 分子の u¹² 変換** — 1728·4(u⁴a)³ = u¹²·(1728·4a³)（本物）。 -/
theorem ellJ_num_transform (F : IUTField) (u : F.carrier)
    (w : ellCurveWeierstrass F) :
    F.mul (ellCurveNat F 1728)
        (F.mul (ellCurveNat F 4) (ellCurveCube F (ellJTransform F u w).a))
      = F.mul (ellJPow F u 12)
          (F.mul (ellCurveNat F 1728)
            (F.mul (ellCurveNat F 4) (ellCurveCube F w.a))) := by
  show F.mul (ellCurveNat F 1728)
      (F.mul (ellCurveNat F 4) (ellCurveCube F (F.mul (ellJPow F u 4) w.a)))
    = F.mul (ellJPow F u 12)
        (F.mul (ellCurveNat F 1728)
          (F.mul (ellCurveNat F 4) (ellCurveCube F w.a)))
  rw [ellJ_cube_transform F u w.a,
    ellJ_mul_left_swap F (ellCurveNat F 4) (ellJPow F u 12) (ellCurveCube F w.a),
    ellJ_mul_left_swap F (ellCurveNat F 1728) (ellJPow F u 12)
      (F.mul (ellCurveNat F 4) (ellCurveCube F w.a))]

/-- **M310F-6b: j の同型不変性**（本丸）— u≠0 かつ 4a³+27b²≠0 のとき、
    変数変換 (a,b)↦(u⁴a,u⁶b) の下で **j(u⁴a,u⁶b) = j(a,b)**。
    分子・分母がともに u¹² 倍され、比で u¹² が相殺する。 -/
theorem ellJ_iso_invariant (F : IUTField) (u : F.carrier)
    (w : ellCurveWeierstrass F) (hu : u ≠ F.zero)
    (hD : ellCurveReducedDiscr F w ≠ F.zero) :
    ellJInvariant F (ellJTransform F u w) = ellJInvariant F w := by
  have hp : ellJPow F u 12 ≠ F.zero := ellJPow_ne_zero F hu 12
  have hD' : ellCurveReducedDiscr F (ellJTransform F u w)
      = F.mul (ellJPow F u 12) (ellCurveReducedDiscr F w) :=
    ellJ_reduced_discr_transform F u w
  show F.mul
      (F.mul (ellCurveNat F 1728)
        (F.mul (ellCurveNat F 4) (ellCurveCube F (ellJTransform F u w).a)))
      (F.inv (ellCurveReducedDiscr F (ellJTransform F u w)))
    = F.mul
        (F.mul (ellCurveNat F 1728)
          (F.mul (ellCurveNat F 4) (ellCurveCube F w.a)))
        (F.inv (ellCurveReducedDiscr F w))
  rw [ellJ_num_transform F u w, hD', F.inv_mul hp hD,
    F.mul_mul_mul_comm (ellJPow F u 12)
      (F.mul (ellCurveNat F 1728)
        (F.mul (ellCurveNat F 4) (ellCurveCube F w.a)))
      (F.inv (ellJPow F u 12)) (F.inv (ellCurveReducedDiscr F w)),
    F.mul_inv_cancel (ellJPow F u 12) hp, F.one_mul]

/-! ## M310F-7: 特殊値 j=0 ⟺ a=0・b=0 ⟹ j=1728 -/

/-- **M310F-7a: a=0 ⟹ j=0**（本物・分子が消える）。 -/
theorem ellJ_zero_of_a_zero (F : IUTField) (w : ellCurveWeierstrass F)
    (ha : w.a = F.zero) : ellJInvariant F w = F.zero := by
  show F.mul
      (F.mul (ellCurveNat F 1728) (F.mul (ellCurveNat F 4) (ellCurveCube F w.a)))
      (F.inv (ellCurveReducedDiscr F w)) = F.zero
  rw [ha, ellCurve_cube_zero F, F.toCRing.mul_zero (ellCurveNat F 4),
    F.toCRing.mul_zero (ellCurveNat F 1728),
    ellCurve_zero_mul F (F.inv (ellCurveReducedDiscr F w))]

/-- **M310F-7b: a≠0 ⟹ a³≠0**（整域性・本物）。 -/
theorem ellJ_cube_ne_zero (F : IUTField) {a : F.carrier} (ha : a ≠ F.zero) :
    ellCurveCube F a ≠ F.zero := by
  show F.mul a (F.mul a a) ≠ F.zero
  exact F.mul_ne_zero ha (F.mul_ne_zero ha ha)

/-- **M310F-7c: a≠0 ⟹ j≠0**（j=0⟺a=0 の構成的対偶・本物）。
    1728≠0・4≠0・分母≠0 を仮説に取る（一般体では 1728,4 の非零性は char に依存）。 -/
theorem ellJ_ne_zero_of_a_ne_zero (F : IUTField) (w : ellCurveWeierstrass F)
    (h1728 : ellCurveNat F 1728 ≠ F.zero) (h4 : ellCurveNat F 4 ≠ F.zero)
    (hD : ellCurveReducedDiscr F w ≠ F.zero) (ha : w.a ≠ F.zero) :
    ellJInvariant F w ≠ F.zero := by
  have hcube : ellCurveCube F w.a ≠ F.zero := ellJ_cube_ne_zero F ha
  have hN : F.mul (ellCurveNat F 1728)
      (F.mul (ellCurveNat F 4) (ellCurveCube F w.a)) ≠ F.zero :=
    F.mul_ne_zero h1728 (F.mul_ne_zero h4 hcube)
  have hID : F.inv (ellCurveReducedDiscr F w) ≠ F.zero := F.inv_ne_zero hD
  show F.mul
      (F.mul (ellCurveNat F 1728) (F.mul (ellCurveNat F 4) (ellCurveCube F w.a)))
      (F.inv (ellCurveReducedDiscr F w)) ≠ F.zero
  exact F.mul_ne_zero hN hID

/-- **M310F-7d: b=0 ⟹ j=1728**（本物・分母が 4a³ に落ち分子=1728·4a³ と相殺）。
    分母 4a³+27b²≠0 を仮説に取る。 -/
theorem ellJ_1728_of_b_zero (F : IUTField) (w : ellCurveWeierstrass F)
    (hb : w.b = F.zero) (hD : ellCurveReducedDiscr F w ≠ F.zero) :
    ellJInvariant F w = ellCurveNat F 1728 := by
  have hDM : ellCurveReducedDiscr F w
      = F.mul (ellCurveNat F 4) (ellCurveCube F w.a) := by
    show F.add (F.mul (ellCurveNat F 4) (ellCurveCube F w.a))
        (F.mul (ellCurveNat F 27) (ellCurveSq F w.b))
      = F.mul (ellCurveNat F 4) (ellCurveCube F w.a)
    rw [hb,
      show ellCurveSq F F.zero = F.zero from ellCurve_zero_mul F F.zero,
      F.toCRing.mul_zero (ellCurveNat F 27),
      ellCurve_add_zero F (F.mul (ellCurveNat F 4) (ellCurveCube F w.a))]
  have hM : F.mul (ellCurveNat F 4) (ellCurveCube F w.a) ≠ F.zero := by
    rw [hDM] at hD
    exact hD
  show F.mul
      (F.mul (ellCurveNat F 1728) (F.mul (ellCurveNat F 4) (ellCurveCube F w.a)))
      (F.inv (ellCurveReducedDiscr F w)) = ellCurveNat F 1728
  rw [hDM,
    F.mul_assoc (ellCurveNat F 1728)
      (F.mul (ellCurveNat F 4) (ellCurveCube F w.a))
      (F.inv (F.mul (ellCurveNat F 4) (ellCurveCube F w.a))),
    F.mul_inv_cancel (F.mul (ellCurveNat F 4) (ellCurveCube F w.a)) hM,
    ellCurve_mul_one F (ellCurveNat F 1728)]

/-! ## M310F-8: capstone・ℚ 実例 -/

/-- 立方 1³ = 1（本物）。 -/
theorem ellJ_cube_one (F : IUTField) : ellCurveCube F F.one = F.one := by
  show F.mul F.one (F.mul F.one F.one) = F.one
  rw [F.one_mul (F.mul F.one F.one), F.one_mul F.one]

/-- **M310F-8a: j-不変量データ** — Weierstrass データ + 分母非零 + j 値。 -/
structure EllipticJData (F : IUTField) where
  /-- Weierstrass 係数。 -/
  weier : ellCurveWeierstrass F
  /-- 分母 4a³+27b²≠0（j の well-defined 性）。 -/
  reduced_ne_zero : ellCurveReducedDiscr F weier ≠ F.zero
  /-- j 値。 -/
  j : F.carrier
  /-- j 値は j-不変量に一致。 -/
  j_eq : j = ellJInvariant F weier

/-- **M310F-8b: j の同型不変性（capstone 再輸出）** — 同型 (a,b)↦(u⁴a,u⁶b) で j 不変。 -/
theorem ellJ_invariant (F : IUTField) (u : F.carrier)
    (w : ellCurveWeierstrass F) (hu : u ≠ F.zero)
    (hD : ellCurveReducedDiscr F w ≠ F.zero) :
    ellJInvariant F (ellJTransform F u w) = ellJInvariant F w :=
  ellJ_iso_invariant F u w hu hD

/-- **M310F-8c: 判別式の u¹² スケーリング（capstone 再輸出）**。 -/
theorem ellJ_discr_scaling (F : IUTField) (u : F.carrier)
    (w : ellCurveWeierstrass F) :
    ellCurveDiscriminant F (ellJTransform F u w)
      = F.mul (ellJPow F u 12) (ellCurveDiscriminant F w) :=
  ellJ_discr_transform F u w

/-- **M310F-8d: ℚ 上 y²=x³+1 の分母 27≠0**（本物）。 -/
theorem ellJExample_reduced_ne_zero :
    ellCurveReducedDiscr ratIUTField ellCurveExampleW ≠ ratIUTField.zero := by
  rw [ellCurve_example_reduced]
  exact ellCurveNat_rat_ne_zero 27 (by omega)

/-- **M310F-8e: ℚ 上 y²=x³+1（a=0,b=1）の j = 0**（本物）。 -/
theorem ellJ_example_j_zero :
    ellJInvariant ratIUTField ellCurveExampleW = ratIUTField.zero :=
  ellJ_zero_of_a_zero ratIUTField ellCurveExampleW rfl

/-- **M310F-8f: y²=x³+x（a=1,b=0）の Weierstrass データ**。 -/
def ellJExample1728W : ellCurveWeierstrass ratIUTField where
  a := ratIUTField.one
  b := ratIUTField.zero

/-- **M310F-8g: y²=x³+x の分母 4≠0**（本物・4·1³+27·0²=4）。 -/
theorem ellJExample1728_reduced_ne_zero :
    ellCurveReducedDiscr ratIUTField ellJExample1728W ≠ ratIUTField.zero := by
  have hrd : ellCurveReducedDiscr ratIUTField ellJExample1728W
      = ellCurveNat ratIUTField 4 := by
    show ratIUTField.add
        (ratIUTField.mul (ellCurveNat ratIUTField 4)
          (ellCurveCube ratIUTField ratIUTField.one))
        (ratIUTField.mul (ellCurveNat ratIUTField 27)
          (ellCurveSq ratIUTField ratIUTField.zero))
      = ellCurveNat ratIUTField 4
    rw [ellJ_cube_one ratIUTField,
      ellCurve_mul_one ratIUTField (ellCurveNat ratIUTField 4),
      show ellCurveSq ratIUTField ratIUTField.zero = ratIUTField.zero from
        ellCurve_zero_mul ratIUTField ratIUTField.zero,
      ratIUTField.toCRing.mul_zero (ellCurveNat ratIUTField 27),
      ellCurve_add_zero ratIUTField (ellCurveNat ratIUTField 4)]
  rw [hrd]
  exact ellCurveNat_rat_ne_zero 4 (by omega)

/-- **M310F-8h: y²=x³+x（a=1,b=0）の j = 1728**（本物）。 -/
theorem ellJExample1728_j :
    ellJInvariant ratIUTField ellJExample1728W = ellCurveNat ratIUTField 1728 :=
  ellJ_1728_of_b_zero ratIUTField ellJExample1728W rfl
    ellJExample1728_reduced_ne_zero

/-- **M310F-8i: y²=x³+1 の j-不変量データ**（j=0）。 -/
def ellJExampleData : EllipticJData ratIUTField where
  weier := ellCurveExampleW
  reduced_ne_zero := ellJExample_reduced_ne_zero
  j := ratIUTField.zero
  j_eq := ellJ_example_j_zero.symm

/-- **M310F-8j: j-不変量データは存在する**（ℚ 上の本物の実例）。 -/
theorem ellJ_exists : Nonempty (EllipticJData ratIUTField) :=
  ⟨ellJExampleData⟩

end IUT
