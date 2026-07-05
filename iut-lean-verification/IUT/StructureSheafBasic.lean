/-
  IUT/StructureSheafBasic.lean — M293F（柱 A スキーム論 先行建設:
  アフィンスキームの構造層 O_Spec の基本開集合 D(f) 上の骨組み）

  ── 分類 **[実]**（本物の数学的実体の新規建設: 局所環付き空間＝
  スキームの定義の心臓部である「構造層 O」の基本開 D(f) 上の値
  O(D(f)) = R_f と制限写像・前層公理を本物構成）。

  **complete_pct 影響: 実 IUT のアフィンスキーム Spec R の構造層 O を
  基本開 D(f) の基の上の前層として初構成**。任意可換環 R（零因子なし
  不要・整域不要）に対し f-べき局所化 R_f = R[1/f] を交差積 Quot 商
  として建て、可換環公理を完全証明。D(g)⊆D(f)（gⁿ = a·f 型の可除
  witness）に対する制限準同型 R_f → R_g を普遍性で誘導し環準同型と証明。
  前層公理（制限の恒等・合成）と大域切断 O(D(1)) = R を完全証明。
  茎 R_P の局所性は骨組み（非単元全体がイデアルの候補）。

  設計の鍵: 一般局所化の well-defined 性は整域を要さず、関係
  (a,n) ~ (b,m) ⟺ ∃k, fᵏ(a·fᵐ − b·fⁿ) = 0 の**追加乗数 fᵏ**で閉じる。
  推移律は k = k₁ + k₂ + m を明示（分母べき m を挟む古典構成の
  構成的翻訳）。制限 R_f → R_g は f が R_g で可逆（gⁿ = a·f より
  f·(a·fⁿ⁻¹…) 型）になることから普遍性で誘導する。

  * M293F-1 `structSheafPow` / `structSheafPow_add` — 分母 fⁿ のべき
  * M293F-2 `structSheafCR_*` — 可換環の一般補題（積の並べ替え群・
    符号積・差ゼロ⇒相等）。restrict/rel の交差積計算の土台
  * M293F-3 `StructSheafPreLoc` / `structSheafRel` — 前分数 a/fⁿ と
    交差積関係（追加乗数付き）。refl/symm/trans を完全証明
  * M293F-4 `structSheafPfAdd`/`Mul`/`Neg`/`Zero`/`One` と well-defined
  * M293F-5 `StructSheafSection`（= R_f の Quot 商）と
    `structSheaf_section_isCRing` — **O(D(f)) = R_f は可換環**
  * M293F-6 `structSheaf_incl` / `structSheafRestrict` /
    `structSheaf_restrict_isHom` — 制限準同型 R_f → R_g（環準同型）
  * M293F-7 `structSheaf_restrict_id` / `structSheaf_restrict_comp` —
    **前層公理（制限の恒等・合成）**
  * M293F-8 `structSheafStalk` / `structSheaf_stalk_local` — 茎 R_P の
    局所性骨組み
  * M293F-9 `StructureSheafData` / `structSheaf_presheaf` /
    `structSheaf_exists` / `structSheaf_global_eq_ring` — capstone。
    大域切断 O(D(1)) = R

  **正直な限定（必守申告・消去弱化禁止）**:
  1. 構造層は**基本開集合 D(f) の基の上の前層**として構成。一般開集合
     への層化・貼り合わせ（層条件）は後続。前層則（制限の恒等・合成）は
     本物で閉じる。
  2. 茎 R_P の局所性は**骨組み**（R_P の非単元全体がイデアルの候補と
     いう命題レベル）。局所環付き空間としての完全公理（唯一の極大
     イデアル）と R_P の環構造は後続。
  3. 局所化 R_f は分母を f のべきに限る**自前最小版**（M290F 未存在の
     ため import せず自前構成）。一般の乗法系局所化は後続。
  4. 制限の存在は D(g)⊆D(f) の witness（gⁿ = a·f）を仮定に取る形。
     基本開の包含判定そのもの（付値・素イデアルでの一致）は後続。

  全て選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。
  共有ファイル未変更（新規 1 本のみ）。
-/
import IUT.Ring

namespace IUT

/-! ## M293F-1: 分母のべき fⁿ -/

/-- **M293F-1a: f のべき** fⁿ（分母に置く元）。 -/
def structSheafPow (R : CRing) (f : R.carrier) : Nat → R.carrier
  | 0 => R.one
  | (n + 1) => R.mul f (structSheafPow R f n)

/-! ## M293F-2: 可換環の一般補題 -/

/-- a·1 = a。 -/
theorem structSheafCR_mul_one (R : CRing) (a : R.carrier) :
    R.mul a R.one = a := by
  rw [R.mul_comm, R.one_mul]

/-- 0·a = 0。 -/
theorem structSheafCR_zero_mul (R : CRing) (a : R.carrier) :
    R.mul R.zero a = R.zero := by
  rw [R.mul_comm, R.mul_zero]

/-- a + 0 = a。 -/
theorem structSheafCR_add_zero (R : CRing) (a : R.carrier) :
    R.add a R.zero = a := by
  rw [R.add_comm, R.zero_add]

/-- a + (−a) = 0。 -/
theorem structSheafCR_add_neg (R : CRing) (a : R.carrier) :
    R.add a (R.neg a) = R.zero := by
  rw [R.add_comm, R.neg_add]

/-- −0 = 0。 -/
theorem structSheafCR_neg_zero (R : CRing) : R.neg R.zero = R.zero := by
  have h := structSheafCR_add_neg R R.zero
  rw [R.zero_add] at h
  exact h

/-- (−a)·b = −(a·b)。 -/
theorem structSheafCR_neg_mul (R : CRing) (a b : R.carrier) :
    R.mul (R.neg a) b = R.neg (R.mul a b) := by
  apply R.add_left_cancel (a := R.mul a b)
  rw [structSheafCR_add_neg R (R.mul a b), ← R.right_distrib,
    structSheafCR_add_neg R a, structSheafCR_zero_mul]

/-- a·(−b) = −(a·b)。 -/
theorem structSheafCR_mul_neg (R : CRing) (a b : R.carrier) :
    R.mul a (R.neg b) = R.neg (R.mul a b) := by
  rw [R.mul_comm a (R.neg b), structSheafCR_neg_mul, R.mul_comm b a]

/-- 差がゼロなら相等。 -/
theorem structSheafCR_eq_of_sub_zero (R : CRing) {a b : R.carrier}
    (h : R.add a (R.neg b) = R.zero) : a = b := by
  have h1 : R.add (R.add a (R.neg b)) b = R.add R.zero b := by rw [h]
  rw [R.add_assoc, R.neg_add, structSheafCR_add_zero, R.zero_add] at h1
  exact h1

/-- 相等なら差がゼロ。 -/
theorem structSheafCR_sub_zero_of_eq (R : CRing) {a b : R.carrier}
    (h : a = b) : R.add a (R.neg b) = R.zero := by
  rw [h, structSheafCR_add_neg]

/-- 積の左入れ替え a(bc) = b(ac)。 -/
theorem structSheafCR_mul_left_comm (R : CRing) (a b c : R.carrier) :
    R.mul a (R.mul b c) = R.mul b (R.mul a c) := by
  rw [← R.mul_assoc, R.mul_comm a b, R.mul_assoc]

/-- 積の右入れ替え (ab)c = (ac)b。 -/
theorem structSheafCR_mul_right_comm (R : CRing) (a b c : R.carrier) :
    R.mul (R.mul a b) c = R.mul (R.mul a c) b := by
  rw [R.mul_assoc, R.mul_comm b c, ← R.mul_assoc]

/-- 4 因子の入れ替え (ab)(cd) = (ac)(bd)。 -/
theorem structSheafCR_mul_comm4 (R : CRing) (a b c d : R.carrier) :
    R.mul (R.mul a b) (R.mul c d) = R.mul (R.mul a c) (R.mul b d) := by
  rw [R.mul_assoc a b (R.mul c d), structSheafCR_mul_left_comm R b c d,
    ← R.mul_assoc a c (R.mul b d), R.mul_assoc]

/-- fᵐ⁺ⁿ = fᵐ·fⁿ。 -/
theorem structSheafPow_add (R : CRing) (f : R.carrier) (m n : Nat) :
    structSheafPow R f (m + n)
      = R.mul (structSheafPow R f m) (structSheafPow R f n) := by
  induction n with
  | zero =>
    show structSheafPow R f m = R.mul (structSheafPow R f m) R.one
    rw [structSheafCR_mul_one]
  | succ k ih =>
    show R.mul f (structSheafPow R f (m + k))
      = R.mul (structSheafPow R f m) (R.mul f (structSheafPow R f k))
    rw [ih, structSheafCR_mul_left_comm]

/-- c·(P − Q) = c·P − c·Q。 -/
theorem structSheafCR_mul_sub (R : CRing) (c P Q : R.carrier) :
    R.mul c (R.add P (R.neg Q)) = R.add (R.mul c P) (R.neg (R.mul c Q)) := by
  rw [R.left_distrib, structSheafCR_mul_neg]

/-- (P − Q)·c = P·c − Q·c。 -/
theorem structSheafCR_sub_mul (R : CRing) (P Q c : R.carrier) :
    R.mul (R.add P (R.neg Q)) c = R.add (R.mul P c) (R.neg (R.mul Q c)) := by
  rw [R.right_distrib, structSheafCR_neg_mul]

/-- 中間項の相殺 (P − Q) + (Q − S) = P − S。 -/
theorem structSheafCR_cancel_mid (R : CRing) (P Q S : R.carrier) :
    R.add (R.add P (R.neg Q)) (R.add Q (R.neg S)) = R.add P (R.neg S) := by
  rw [R.add_assoc, ← R.add_assoc (R.neg Q) Q (R.neg S), R.neg_add, R.zero_add]

/-- 差の対称化: A − B = 0 なら B − A = 0。 -/
theorem structSheafCR_swap_sub (R : CRing) {A B : R.carrier}
    (h : R.add A (R.neg B) = R.zero) : R.add B (R.neg A) = R.zero := by
  have hab := structSheafCR_eq_of_sub_zero R h
  rw [← hab]
  exact structSheafCR_add_neg R A

/-! ## M293F-3: 前分数 a/fⁿ と交差積関係（追加乗数付き） -/

/-- **M293F-3a: 前分数** a/fⁿ を分子 num と分母べき den で表す。 -/
structure StructSheafPreLoc (R : CRing) (f : R.carrier) where
  /-- 分子。 -/
  num : R.carrier
  /-- 分母べき（f の指数）。 -/
  den : Nat

/-- 前分数の外延性（den は Nat・num は環元）。 -/
theorem structSheafPreLoc_ext {R : CRing} {f : R.carrier} :
    ∀ {x y : StructSheafPreLoc R f}, x.num = y.num → x.den = y.den → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

/-- **M293F-3b: 交差積関係**（追加乗数 fᵏ 付き）
    a/fⁿ ~ b/fᵐ ⟺ ∃k, fᵏ·(a·fᵐ − b·fⁿ) = 0。 -/
def structSheafRel (R : CRing) (f : R.carrier)
    (x y : StructSheafPreLoc R f) : Prop :=
  ∃ k, R.mul (structSheafPow R f k)
    (R.add (R.mul x.num (structSheafPow R f y.den))
      (R.neg (R.mul y.num (structSheafPow R f x.den)))) = R.zero

/-- 反射律（k = 0）。 -/
theorem structSheafRel_refl {R : CRing} {f : R.carrier}
    (x : StructSheafPreLoc R f) : structSheafRel R f x x := by
  refine ⟨0, ?_⟩
  rw [structSheafCR_add_neg, R.mul_zero]

/-- 対称律（同じ乗数 fᵏ）。 -/
theorem structSheafRel_symm {R : CRing} {f : R.carrier}
    {x y : StructSheafPreLoc R f} (h : structSheafRel R f x y) :
    structSheafRel R f y x := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [structSheafCR_mul_sub] at hk
  rw [structSheafCR_mul_sub]
  exact structSheafCR_swap_sub R hk

/-- **M293F-3c: 推移律** — 乗数 k = k₁ + k₂ + m（中間分母べき m を挟む）。 -/
theorem structSheafRel_trans {R : CRing} {f : R.carrier}
    {x y z : StructSheafPreLoc R f}
    (h1 : structSheafRel R f x y) (h2 : structSheafRel R f y z) :
    structSheafRel R f x z := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  -- 略記: a,b,c = num; n,m,p = den; g i = fⁱ
  -- hk1 : g k1 · (a·gm − b·gn) = 0
  -- hk2 : g k2 · (b·gp − c·gm) = 0
  -- 目標: ∃K, g K · (a·gp − c·gn) = 0、K = k1+k2+m
  refine ⟨k1 + k2 + y.den, ?_⟩
  -- e1: (g k2 · gp)·(g k1 · (a·gm − b·gn)) = 0
  have e1 : R.mul (R.mul (structSheafPow R f k2) (structSheafPow R f z.den))
      (R.mul (structSheafPow R f k1)
        (R.add (R.mul x.num (structSheafPow R f y.den))
          (R.neg (R.mul y.num (structSheafPow R f x.den))))) = R.zero := by
    rw [hk1, R.mul_zero]
  -- e2: (g k1 · gn)·(g k2 · (b·gp − c·gm)) = 0
  have e2 : R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f x.den))
      (R.mul (structSheafPow R f k2)
        (R.add (R.mul y.num (structSheafPow R f z.den))
          (R.neg (R.mul z.num (structSheafPow R f y.den))))) = R.zero := by
    rw [hk2, R.mul_zero]
  -- 和 = 0
  have esum : R.add
      (R.mul (R.mul (structSheafPow R f k2) (structSheafPow R f z.den))
        (R.mul (structSheafPow R f k1)
          (R.add (R.mul x.num (structSheafPow R f y.den))
            (R.neg (R.mul y.num (structSheafPow R f x.den))))))
      (R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f x.den))
        (R.mul (structSheafPow R f k2)
          (R.add (R.mul y.num (structSheafPow R f z.den))
            (R.neg (R.mul z.num (structSheafPow R f y.den)))))) = R.zero := by
    rw [e1, e2, R.zero_add]
  -- 積の並べ替え恒等式 3 本
  have hLbRb :
      R.mul (R.mul (structSheafPow R f k2) (structSheafPow R f z.den))
          (R.mul (structSheafPow R f k1)
            (R.mul y.num (structSheafPow R f x.den)))
        = R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f x.den))
          (R.mul (structSheafPow R f k2)
            (R.mul y.num (structSheafPow R f z.den))) := by
    rw [structSheafCR_mul_comm4 R (structSheafPow R f k2) (structSheafPow R f z.den)
        (structSheafPow R f k1) (R.mul y.num (structSheafPow R f x.den)),
      R.mul_comm (structSheafPow R f k2) (structSheafPow R f k1),
      structSheafCR_mul_left_comm R (structSheafPow R f z.den) y.num
        (structSheafPow R f x.den),
      R.mul_comm (structSheafPow R f z.den) (structSheafPow R f x.den),
      structSheafCR_mul_comm4 R (structSheafPow R f k1) (structSheafPow R f x.den)
        (structSheafPow R f k2) (R.mul y.num (structSheafPow R f z.den)),
      structSheafCR_mul_left_comm R (structSheafPow R f x.den) y.num
        (structSheafPow R f z.den)]
  have hLaGa :
      R.mul (R.mul (structSheafPow R f k2) (structSheafPow R f z.den))
          (R.mul (structSheafPow R f k1)
            (R.mul x.num (structSheafPow R f y.den)))
        = R.mul (R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f k2))
            (structSheafPow R f y.den)) (R.mul x.num (structSheafPow R f z.den)) := by
    rw [structSheafCR_mul_comm4 R (structSheafPow R f k2) (structSheafPow R f z.den)
        (structSheafPow R f k1) (R.mul x.num (structSheafPow R f y.den)),
      R.mul_comm (structSheafPow R f k2) (structSheafPow R f k1),
      structSheafCR_mul_left_comm R (structSheafPow R f z.den) x.num
        (structSheafPow R f y.den),
      R.mul_comm (structSheafPow R f z.den) (structSheafPow R f y.den),
      R.mul_assoc (R.mul (structSheafPow R f k1) (structSheafPow R f k2))
        (structSheafPow R f y.den) (R.mul x.num (structSheafPow R f z.den)),
      structSheafCR_mul_left_comm R (structSheafPow R f y.den) x.num
        (structSheafPow R f z.den)]
  have hRcGc :
      R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f x.den))
          (R.mul (structSheafPow R f k2)
            (R.mul z.num (structSheafPow R f y.den)))
        = R.mul (R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f k2))
            (structSheafPow R f y.den)) (R.mul z.num (structSheafPow R f x.den)) := by
    rw [structSheafCR_mul_comm4 R (structSheafPow R f k1) (structSheafPow R f x.den)
        (structSheafPow R f k2) (R.mul z.num (structSheafPow R f y.den)),
      structSheafCR_mul_left_comm R (structSheafPow R f x.den) z.num
        (structSheafPow R f y.den),
      R.mul_comm (structSheafPow R f x.den) (structSheafPow R f y.den),
      R.mul_assoc (R.mul (structSheafPow R f k1) (structSheafPow R f k2))
        (structSheafPow R f y.den) (R.mul z.num (structSheafPow R f x.den)),
      structSheafCR_mul_left_comm R (structSheafPow R f y.den) z.num
        (structSheafPow R f x.den)]
  -- 和を La − Rc へ簡約
  have hexp : R.add
      (R.mul (R.mul (structSheafPow R f k2) (structSheafPow R f z.den))
        (R.mul (structSheafPow R f k1)
          (R.add (R.mul x.num (structSheafPow R f y.den))
            (R.neg (R.mul y.num (structSheafPow R f x.den))))))
      (R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f x.den))
        (R.mul (structSheafPow R f k2)
          (R.add (R.mul y.num (structSheafPow R f z.den))
            (R.neg (R.mul z.num (structSheafPow R f y.den))))))
    = R.add
        (R.mul (R.mul (structSheafPow R f k2) (structSheafPow R f z.den))
          (R.mul (structSheafPow R f k1)
            (R.mul x.num (structSheafPow R f y.den))))
        (R.neg (R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f x.den))
          (R.mul (structSheafPow R f k2)
            (R.mul z.num (structSheafPow R f y.den))))) := by
    rw [structSheafCR_mul_sub R (structSheafPow R f k1)
        (R.mul x.num (structSheafPow R f y.den))
        (R.mul y.num (structSheafPow R f x.den)),
      structSheafCR_mul_sub R
        (R.mul (structSheafPow R f k2) (structSheafPow R f z.den))
        (R.mul (structSheafPow R f k1) (R.mul x.num (structSheafPow R f y.den)))
        (R.mul (structSheafPow R f k1) (R.mul y.num (structSheafPow R f x.den))),
      structSheafCR_mul_sub R (structSheafPow R f k2)
        (R.mul y.num (structSheafPow R f z.den))
        (R.mul z.num (structSheafPow R f y.den)),
      structSheafCR_mul_sub R
        (R.mul (structSheafPow R f k1) (structSheafPow R f x.den))
        (R.mul (structSheafPow R f k2) (R.mul y.num (structSheafPow R f z.den)))
        (R.mul (structSheafPow R f k2) (R.mul z.num (structSheafPow R f y.den))),
      hLbRb,
      structSheafCR_cancel_mid R
        (R.mul (R.mul (structSheafPow R f k2) (structSheafPow R f z.den))
          (R.mul (structSheafPow R f k1) (R.mul x.num (structSheafPow R f y.den))))
        (R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f x.den))
          (R.mul (structSheafPow R f k2) (R.mul y.num (structSheafPow R f z.den))))
        (R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f x.den))
          (R.mul (structSheafPow R f k2) (R.mul z.num (structSheafPow R f y.den))))]
  -- 目標を La − Rc へ書き換え、esum で閉じる
  rw [structSheafPow_add R f (k1 + k2) y.den, structSheafPow_add R f k1 k2,
    structSheafCR_mul_sub R
      (R.mul (R.mul (structSheafPow R f k1) (structSheafPow R f k2))
        (structSheafPow R f y.den))
      (R.mul x.num (structSheafPow R f z.den))
      (R.mul z.num (structSheafPow R f x.den)),
    ← hLaGa, ← hRcGc, ← hexp]
  exact esum

/-- −(P + Q) = (−P) + (−Q)。 -/
theorem structSheafCR_neg_add (R : CRing) (P Q : R.carrier) :
    R.neg (R.add P Q) = R.add (R.neg P) (R.neg Q) := by
  apply R.add_left_cancel (a := R.add P Q)
  rw [structSheafCR_add_neg R (R.add P Q), R.add_comm (R.neg P) (R.neg Q),
    R.add_assoc P Q (R.add (R.neg Q) (R.neg P)),
    ← R.add_assoc Q (R.neg Q) (R.neg P), structSheafCR_add_neg R Q,
    R.zero_add, structSheafCR_add_neg R P]

/-- 4 項相殺: (A + B₁) + ((−A) + (−B₂)) = B₁ − B₂。 -/
theorem structSheafCR_add4_cancel (R : CRing) (A B1 B2 : R.carrier) :
    R.add (R.add A B1) (R.add (R.neg A) (R.neg B2)) = R.add B1 (R.neg B2) := by
  rw [R.add_assoc A B1 (R.add (R.neg A) (R.neg B2)),
    ← R.add_assoc B1 (R.neg A) (R.neg B2), R.add_comm B1 (R.neg A),
    R.add_assoc (R.neg A) B1 (R.neg B2),
    ← R.add_assoc A (R.neg A) (R.add B1 (R.neg B2)),
    structSheafCR_add_neg R A, R.zero_add]

/-- 符号入れ替え: P − Q = 0 なら (−P) + Q = 0。 -/
theorem structSheafCR_neg_add_swap (R : CRing) {P Q : R.carrier}
    (h : R.add P (R.neg Q) = R.zero) : R.add (R.neg P) Q = R.zero := by
  have hpq := structSheafCR_eq_of_sub_zero R h
  rw [← hpq, R.add_comm, structSheafCR_add_neg]

/-! ## M293F-4: 代表演算 -/

/-- **M293F-4a: 加法**（a/fⁿ + b/fᵐ = (a·fᵐ + b·fⁿ)/fⁿ⁺ᵐ）。 -/
def structSheafPfAdd {R : CRing} {f : R.carrier}
    (x y : StructSheafPreLoc R f) : StructSheafPreLoc R f :=
  ⟨R.add (R.mul x.num (structSheafPow R f y.den))
      (R.mul y.num (structSheafPow R f x.den)), x.den + y.den⟩

/-- **M293F-4b: 乗法**（a/fⁿ · b/fᵐ = (a·b)/fⁿ⁺ᵐ）。 -/
def structSheafPfMul {R : CRing} {f : R.carrier}
    (x y : StructSheafPreLoc R f) : StructSheafPreLoc R f :=
  ⟨R.mul x.num y.num, x.den + y.den⟩

/-- **M293F-4c: 反元**。 -/
def structSheafPfNeg {R : CRing} {f : R.carrier}
    (x : StructSheafPreLoc R f) : StructSheafPreLoc R f :=
  ⟨R.neg x.num, x.den⟩

/-- 0 の代表 0/f⁰。 -/
def structSheafPfZero {R : CRing} {f : R.carrier} : StructSheafPreLoc R f :=
  ⟨R.zero, 0⟩

/-- 1 の代表 1/f⁰。 -/
def structSheafPfOne {R : CRing} {f : R.carrier} : StructSheafPreLoc R f :=
  ⟨R.one, 0⟩

/-- 二重符号 −(−a) = a。 -/
theorem structSheafCR_neg_neg (R : CRing) (a : R.carrier) :
    R.neg (R.neg a) = a := by
  apply R.add_left_cancel (a := R.neg a)
  rw [structSheafCR_add_neg R (R.neg a), R.neg_add]

/-! ## M293F-4d: 演算の well-definedness（片側ずつ） -/

/-- 乗法は第 2 引数の関係を保つ。 -/
theorem structSheafRel_mul_left {R : CRing} {f : R.carrier}
    (x : StructSheafPreLoc R f) {y y' : StructSheafPreLoc R f}
    (h : structSheafRel R f y y') :
    structSheafRel R f (structSheafPfMul x y) (structSheafPfMul x y') := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  show R.mul (structSheafPow R f k)
    (R.add (R.mul (R.mul x.num y.num) (structSheafPow R f (x.den + y'.den)))
      (R.neg (R.mul (R.mul x.num y'.num) (structSheafPow R f (x.den + y.den)))))
    = R.zero
  rw [structSheafPow_add R f x.den y'.den, structSheafPow_add R f x.den y.den,
    structSheafCR_mul_comm4 R x.num y.num (structSheafPow R f x.den)
      (structSheafPow R f y'.den),
    structSheafCR_mul_comm4 R x.num y'.num (structSheafPow R f x.den)
      (structSheafPow R f y.den),
    ← structSheafCR_mul_sub R (R.mul x.num (structSheafPow R f x.den))
      (R.mul y.num (structSheafPow R f y'.den))
      (R.mul y'.num (structSheafPow R f y.den)),
    structSheafCR_mul_left_comm R (structSheafPow R f k)
      (R.mul x.num (structSheafPow R f x.den))
      (R.add (R.mul y.num (structSheafPow R f y'.den))
        (R.neg (R.mul y'.num (structSheafPow R f y.den)))),
    hk, R.mul_zero]

/-- 乗法は第 1 引数の関係を保つ。 -/
theorem structSheafRel_mul_right {R : CRing} {f : R.carrier}
    (y : StructSheafPreLoc R f) {x x' : StructSheafPreLoc R f}
    (h : structSheafRel R f x x') :
    structSheafRel R f (structSheafPfMul x y) (structSheafPfMul x' y) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  show R.mul (structSheafPow R f k)
    (R.add (R.mul (R.mul x.num y.num) (structSheafPow R f (x'.den + y.den)))
      (R.neg (R.mul (R.mul x'.num y.num) (structSheafPow R f (x.den + y.den)))))
    = R.zero
  rw [structSheafPow_add R f x'.den y.den, structSheafPow_add R f x.den y.den,
    structSheafCR_mul_comm4 R x.num y.num (structSheafPow R f x'.den)
      (structSheafPow R f y.den),
    structSheafCR_mul_comm4 R x'.num y.num (structSheafPow R f x.den)
      (structSheafPow R f y.den),
    ← structSheafCR_sub_mul R (R.mul x.num (structSheafPow R f x'.den))
      (R.mul x'.num (structSheafPow R f x.den))
      (R.mul y.num (structSheafPow R f y.den)),
    ← R.mul_assoc (structSheafPow R f k)
      (R.add (R.mul x.num (structSheafPow R f x'.den))
        (R.neg (R.mul x'.num (structSheafPow R f x.den))))
      (R.mul y.num (structSheafPow R f y.den)),
    hk, structSheafCR_zero_mul]

/-- 反元は関係を保つ。 -/
theorem structSheafRel_neg {R : CRing} {f : R.carrier}
    {x x' : StructSheafPreLoc R f} (h : structSheafRel R f x x') :
    structSheafRel R f (structSheafPfNeg x) (structSheafPfNeg x') := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [structSheafCR_mul_sub R (structSheafPow R f k)
    (R.mul x.num (structSheafPow R f x'.den))
    (R.mul x'.num (structSheafPow R f x.den))] at hk
  show R.mul (structSheafPow R f k)
    (R.add (R.mul (R.neg x.num) (structSheafPow R f x'.den))
      (R.neg (R.mul (R.neg x'.num) (structSheafPow R f x.den)))) = R.zero
  rw [structSheafCR_neg_mul R x.num (structSheafPow R f x'.den),
    structSheafCR_neg_mul R x'.num (structSheafPow R f x.den),
    structSheafCR_neg_neg R (R.mul x'.num (structSheafPow R f x.den)),
    R.left_distrib (structSheafPow R f k)
      (R.neg (R.mul x.num (structSheafPow R f x'.den)))
      (R.mul x'.num (structSheafPow R f x.den)),
    structSheafCR_mul_neg R (structSheafPow R f k)
      (R.mul x.num (structSheafPow R f x'.den))]
  exact structSheafCR_neg_add_swap R hk

/-- 4 項相殺（第 2 項相殺型）: (A₁ + B) + ((−A₂) + (−B)) = A₁ − A₂。 -/
theorem structSheafCR_add4_cancel2 (R : CRing) (A1 B A2 : R.carrier) :
    R.add (R.add A1 B) (R.add (R.neg A2) (R.neg B)) = R.add A1 (R.neg A2) := by
  rw [R.add_assoc A1 B (R.add (R.neg A2) (R.neg B)), R.add_comm (R.neg A2) (R.neg B),
    ← R.add_assoc B (R.neg B) (R.neg A2), structSheafCR_add_neg R B, R.zero_add]

/-- 加法は第 2 引数の関係を保つ。 -/
theorem structSheafRel_add_left {R : CRing} {f : R.carrier}
    (x : StructSheafPreLoc R f) {y y' : StructSheafPreLoc R f}
    (h : structSheafRel R f y y') :
    structSheafRel R f (structSheafPfAdd x y) (structSheafPfAdd x y') := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hA : R.mul (R.mul x.num (structSheafPow R f y'.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den))
      = R.mul (R.mul x.num (structSheafPow R f y.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y'.den)) := by
    rw [structSheafCR_mul_comm4 R x.num (structSheafPow R f y'.den)
        (structSheafPow R f x.den) (structSheafPow R f y.den),
      structSheafCR_mul_comm4 R x.num (structSheafPow R f y.den)
        (structSheafPow R f x.den) (structSheafPow R f y'.den),
      R.mul_comm (structSheafPow R f y'.den) (structSheafPow R f y.den)]
  have hB1 : R.mul (R.mul y.num (structSheafPow R f x.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y'.den))
      = R.mul (R.mul (structSheafPow R f x.den) (structSheafPow R f x.den))
        (R.mul y.num (structSheafPow R f y'.den)) := by
    rw [R.mul_assoc y.num (structSheafPow R f x.den)
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y'.den)),
      R.mul_assoc (structSheafPow R f x.den) (structSheafPow R f x.den)
        (R.mul y.num (structSheafPow R f y'.den)),
      structSheafCR_mul_left_comm R (structSheafPow R f x.den) y.num
        (structSheafPow R f y'.den),
      structSheafCR_mul_left_comm R (structSheafPow R f x.den) y.num
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y'.den))]
  have hB2 : R.mul (R.mul y'.num (structSheafPow R f x.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den))
      = R.mul (R.mul (structSheafPow R f x.den) (structSheafPow R f x.den))
        (R.mul y'.num (structSheafPow R f y.den)) := by
    rw [R.mul_assoc y'.num (structSheafPow R f x.den)
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den)),
      R.mul_assoc (structSheafPow R f x.den) (structSheafPow R f x.den)
        (R.mul y'.num (structSheafPow R f y.den)),
      structSheafCR_mul_left_comm R (structSheafPow R f x.den) y'.num
        (structSheafPow R f y.den),
      structSheafCR_mul_left_comm R (structSheafPow R f x.den) y'.num
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den))]
  show R.mul (structSheafPow R f k)
    (R.add
      (R.mul (R.add (R.mul x.num (structSheafPow R f y.den))
          (R.mul y.num (structSheafPow R f x.den)))
        (structSheafPow R f (x.den + y'.den)))
      (R.neg (R.mul (R.add (R.mul x.num (structSheafPow R f y'.den))
          (R.mul y'.num (structSheafPow R f x.den)))
        (structSheafPow R f (x.den + y.den))))) = R.zero
  rw [structSheafPow_add R f x.den y'.den, structSheafPow_add R f x.den y.den,
    R.right_distrib (R.mul x.num (structSheafPow R f y.den))
      (R.mul y.num (structSheafPow R f x.den))
      (R.mul (structSheafPow R f x.den) (structSheafPow R f y'.den)),
    R.right_distrib (R.mul x.num (structSheafPow R f y'.den))
      (R.mul y'.num (structSheafPow R f x.den))
      (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den)),
    structSheafCR_neg_add R
      (R.mul (R.mul x.num (structSheafPow R f y'.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den)))
      (R.mul (R.mul y'.num (structSheafPow R f x.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den))),
    hA,
    structSheafCR_add4_cancel R
      (R.mul (R.mul x.num (structSheafPow R f y.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y'.den)))
      (R.mul (R.mul y.num (structSheafPow R f x.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y'.den)))
      (R.mul (R.mul y'.num (structSheafPow R f x.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den))),
    hB1, hB2,
    ← structSheafCR_mul_sub R
      (R.mul (structSheafPow R f x.den) (structSheafPow R f x.den))
      (R.mul y.num (structSheafPow R f y'.den))
      (R.mul y'.num (structSheafPow R f y.den)),
    structSheafCR_mul_left_comm R (structSheafPow R f k)
      (R.mul (structSheafPow R f x.den) (structSheafPow R f x.den))
      (R.add (R.mul y.num (structSheafPow R f y'.den))
        (R.neg (R.mul y'.num (structSheafPow R f y.den)))),
    hk, R.mul_zero]

/-- 加法は第 1 引数の関係を保つ。 -/
theorem structSheafRel_add_right {R : CRing} {f : R.carrier}
    (y : StructSheafPreLoc R f) {x x' : StructSheafPreLoc R f}
    (h : structSheafRel R f x x') :
    structSheafRel R f (structSheafPfAdd x y) (structSheafPfAdd x' y) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hBeq : R.mul (R.mul y.num (structSheafPow R f x'.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den))
      = R.mul (R.mul y.num (structSheafPow R f x.den))
        (R.mul (structSheafPow R f x'.den) (structSheafPow R f y.den)) := by
    rw [structSheafCR_mul_comm4 R y.num (structSheafPow R f x'.den)
        (structSheafPow R f x.den) (structSheafPow R f y.den)]
  have hA1 : R.mul (R.mul x.num (structSheafPow R f y.den))
        (R.mul (structSheafPow R f x'.den) (structSheafPow R f y.den))
      = R.mul (R.mul (structSheafPow R f y.den) (structSheafPow R f y.den))
        (R.mul x.num (structSheafPow R f x'.den)) := by
    rw [R.mul_assoc x.num (structSheafPow R f y.den)
        (R.mul (structSheafPow R f x'.den) (structSheafPow R f y.den)),
      R.mul_comm (structSheafPow R f x'.den) (structSheafPow R f y.den),
      R.mul_assoc (structSheafPow R f y.den) (structSheafPow R f y.den)
        (R.mul x.num (structSheafPow R f x'.den)),
      structSheafCR_mul_left_comm R (structSheafPow R f y.den) x.num
        (structSheafPow R f x'.den),
      structSheafCR_mul_left_comm R (structSheafPow R f y.den) x.num
        (R.mul (structSheafPow R f y.den) (structSheafPow R f x'.den))]
  have hA2 : R.mul (R.mul x'.num (structSheafPow R f y.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den))
      = R.mul (R.mul (structSheafPow R f y.den) (structSheafPow R f y.den))
        (R.mul x'.num (structSheafPow R f x.den)) := by
    rw [R.mul_assoc x'.num (structSheafPow R f y.den)
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den)),
      R.mul_comm (structSheafPow R f x.den) (structSheafPow R f y.den),
      R.mul_assoc (structSheafPow R f y.den) (structSheafPow R f y.den)
        (R.mul x'.num (structSheafPow R f x.den)),
      structSheafCR_mul_left_comm R (structSheafPow R f y.den) x'.num
        (structSheafPow R f x.den),
      structSheafCR_mul_left_comm R (structSheafPow R f y.den) x'.num
        (R.mul (structSheafPow R f y.den) (structSheafPow R f x.den))]
  show R.mul (structSheafPow R f k)
    (R.add
      (R.mul (R.add (R.mul x.num (structSheafPow R f y.den))
          (R.mul y.num (structSheafPow R f x.den)))
        (structSheafPow R f (x'.den + y.den)))
      (R.neg (R.mul (R.add (R.mul x'.num (structSheafPow R f y.den))
          (R.mul y.num (structSheafPow R f x'.den)))
        (structSheafPow R f (x.den + y.den))))) = R.zero
  rw [structSheafPow_add R f x'.den y.den, structSheafPow_add R f x.den y.den,
    R.right_distrib (R.mul x.num (structSheafPow R f y.den))
      (R.mul y.num (structSheafPow R f x.den))
      (R.mul (structSheafPow R f x'.den) (structSheafPow R f y.den)),
    R.right_distrib (R.mul x'.num (structSheafPow R f y.den))
      (R.mul y.num (structSheafPow R f x'.den))
      (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den)),
    structSheafCR_neg_add R
      (R.mul (R.mul x'.num (structSheafPow R f y.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den)))
      (R.mul (R.mul y.num (structSheafPow R f x'.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den))),
    hBeq,
    structSheafCR_add4_cancel2 R
      (R.mul (R.mul x.num (structSheafPow R f y.den))
        (R.mul (structSheafPow R f x'.den) (structSheafPow R f y.den)))
      (R.mul (R.mul y.num (structSheafPow R f x.den))
        (R.mul (structSheafPow R f x'.den) (structSheafPow R f y.den)))
      (R.mul (R.mul x'.num (structSheafPow R f y.den))
        (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den))),
    hA1, hA2,
    ← structSheafCR_mul_sub R
      (R.mul (structSheafPow R f y.den) (structSheafPow R f y.den))
      (R.mul x.num (structSheafPow R f x'.den))
      (R.mul x'.num (structSheafPow R f x.den)),
    structSheafCR_mul_left_comm R (structSheafPow R f k)
      (R.mul (structSheafPow R f y.den) (structSheafPow R f y.den))
      (R.add (R.mul x.num (structSheafPow R f x'.den))
        (R.neg (R.mul x'.num (structSheafPow R f x.den)))),
    hk, R.mul_zero]

/-! ## M293F-5: 商 O(D(f)) = R_f と可換環構造 -/

/-- f⁰ = 1（定義的）。 -/
theorem structSheafPow_zero (R : CRing) (f : R.carrier) :
    structSheafPow R f 0 = R.one := rfl

/-- gʲ 倍のスケール（分子分母に fʲ を掛ける・左分配の Quot.sound 用）。 -/
def structSheafPfScalePow {R : CRing} {f : R.carrier}
    (x : StructSheafPreLoc R f) (j : Nat) : StructSheafPreLoc R f :=
  ⟨R.mul (structSheafPow R f j) x.num, j + x.den⟩

/-- スケールは関係を変えない。 -/
theorem structSheafRel_scalePow {R : CRing} {f : R.carrier}
    (x : StructSheafPreLoc R f) (j : Nat) :
    structSheafRel R f (structSheafPfScalePow x j) x := by
  refine ⟨0, ?_⟩
  show R.mul (structSheafPow R f 0)
    (R.add (R.mul (R.mul (structSheafPow R f j) x.num) (structSheafPow R f x.den))
      (R.neg (R.mul x.num (structSheafPow R f (j + x.den))))) = R.zero
  rw [structSheafPow_zero, R.one_mul, structSheafPow_add R f j x.den,
    R.mul_assoc (structSheafPow R f j) x.num (structSheafPow R f x.den),
    structSheafCR_mul_left_comm R x.num (structSheafPow R f j)
      (structSheafPow R f x.den), structSheafCR_add_neg]

/-- 加法の可換律。 -/
theorem structSheafPfAdd_comm {R : CRing} {f : R.carrier}
    (x y : StructSheafPreLoc R f) :
    structSheafPfAdd x y = structSheafPfAdd y x := by
  apply structSheafPreLoc_ext
  · show R.add (R.mul x.num (structSheafPow R f y.den))
        (R.mul y.num (structSheafPow R f x.den))
      = R.add (R.mul y.num (structSheafPow R f x.den))
        (R.mul x.num (structSheafPow R f y.den))
    exact R.add_comm _ _
  · show x.den + y.den = y.den + x.den
    exact Nat.add_comm _ _

/-- 加法の結合律（strict・分母 Nat は結合律で一致）。 -/
theorem structSheafPfAdd_assoc {R : CRing} {f : R.carrier}
    (x y z : StructSheafPreLoc R f) :
    structSheafPfAdd (structSheafPfAdd x y) z
      = structSheafPfAdd x (structSheafPfAdd y z) := by
  apply structSheafPreLoc_ext
  · show R.add (R.mul (R.add (R.mul x.num (structSheafPow R f y.den))
          (R.mul y.num (structSheafPow R f x.den))) (structSheafPow R f z.den))
        (R.mul z.num (structSheafPow R f (x.den + y.den)))
      = R.add (R.mul x.num (structSheafPow R f (y.den + z.den)))
        (R.mul (R.add (R.mul y.num (structSheafPow R f z.den))
          (R.mul z.num (structSheafPow R f y.den))) (structSheafPow R f x.den))
    rw [structSheafPow_add R f x.den y.den, structSheafPow_add R f y.den z.den,
      R.right_distrib (R.mul x.num (structSheafPow R f y.den))
        (R.mul y.num (structSheafPow R f x.den)) (structSheafPow R f z.den),
      R.right_distrib (R.mul y.num (structSheafPow R f z.den))
        (R.mul z.num (structSheafPow R f y.den)) (structSheafPow R f x.den),
      R.add_assoc
        (R.mul (R.mul x.num (structSheafPow R f y.den)) (structSheafPow R f z.den))
        (R.mul (R.mul y.num (structSheafPow R f x.den)) (structSheafPow R f z.den))
        (R.mul z.num
          (R.mul (structSheafPow R f x.den) (structSheafPow R f y.den))),
      R.mul_assoc x.num (structSheafPow R f y.den) (structSheafPow R f z.den),
      structSheafCR_mul_right_comm R y.num (structSheafPow R f x.den)
        (structSheafPow R f z.den),
      ← R.mul_assoc z.num (structSheafPow R f x.den) (structSheafPow R f y.den),
      structSheafCR_mul_right_comm R z.num (structSheafPow R f x.den)
        (structSheafPow R f y.den)]
  · show (x.den + y.den) + z.den = x.den + (y.den + z.den)
    exact Nat.add_assoc _ _ _

/-- 左零元。 -/
theorem structSheafPfZero_add {R : CRing} {f : R.carrier}
    (x : StructSheafPreLoc R f) :
    structSheafPfAdd structSheafPfZero x = x := by
  apply structSheafPreLoc_ext
  · show R.add (R.mul R.zero (structSheafPow R f x.den))
        (R.mul x.num (structSheafPow R f 0)) = x.num
    rw [structSheafPow_zero, structSheafCR_mul_one R x.num,
      structSheafCR_zero_mul R (structSheafPow R f x.den), R.zero_add]
  · show 0 + x.den = x.den
    exact Nat.zero_add _

/-- 左反元（分母べき 2n vs 0 のため Quot.sound 必須）。 -/
theorem structSheafPfNeg_add_rel {R : CRing} {f : R.carrier}
    (x : StructSheafPreLoc R f) :
    structSheafRel R f (structSheafPfAdd (structSheafPfNeg x) x)
      structSheafPfZero := by
  refine ⟨0, ?_⟩
  show R.mul (structSheafPow R f 0)
    (R.add (R.mul (R.add (R.mul (R.neg x.num) (structSheafPow R f x.den))
        (R.mul x.num (structSheafPow R f x.den))) (structSheafPow R f 0))
      (R.neg (R.mul R.zero (structSheafPow R f (x.den + x.den))))) = R.zero
  rw [structSheafPow_zero,
    structSheafCR_zero_mul R (structSheafPow R f (x.den + x.den)),
    structSheafCR_neg_zero R,
    structSheafCR_add_zero R
      (R.mul (R.add (R.mul (R.neg x.num) (structSheafPow R f x.den))
        (R.mul x.num (structSheafPow R f x.den))) R.one),
    structSheafCR_mul_one R (R.add (R.mul (R.neg x.num) (structSheafPow R f x.den))
      (R.mul x.num (structSheafPow R f x.den))),
    R.one_mul, structSheafCR_neg_mul R x.num (structSheafPow R f x.den),
    R.neg_add (R.mul x.num (structSheafPow R f x.den))]

/-- 乗法の結合律。 -/
theorem structSheafPfMul_assoc {R : CRing} {f : R.carrier}
    (x y z : StructSheafPreLoc R f) :
    structSheafPfMul (structSheafPfMul x y) z
      = structSheafPfMul x (structSheafPfMul y z) := by
  apply structSheafPreLoc_ext
  · show R.mul (R.mul x.num y.num) z.num = R.mul x.num (R.mul y.num z.num)
    exact R.mul_assoc _ _ _
  · show (x.den + y.den) + z.den = x.den + (y.den + z.den)
    exact Nat.add_assoc _ _ _

/-- 左単位元。 -/
theorem structSheafPfOne_mul {R : CRing} {f : R.carrier}
    (x : StructSheafPreLoc R f) :
    structSheafPfMul structSheafPfOne x = x := by
  apply structSheafPreLoc_ext
  · show R.mul R.one x.num = x.num
    exact R.one_mul _
  · show 0 + x.den = x.den
    exact Nat.zero_add _

/-- 乗法の可換律。 -/
theorem structSheafPfMul_comm {R : CRing} {f : R.carrier}
    (x y : StructSheafPreLoc R f) :
    structSheafPfMul x y = structSheafPfMul y x := by
  apply structSheafPreLoc_ext
  · show R.mul x.num y.num = R.mul y.num x.num
    exact R.mul_comm _ _
  · show x.den + y.den = y.den + x.den
    exact Nat.add_comm _ _

/-- 左分配は「x.den べきスケール」との strict 等式に落ちる（分母べきが
    真に異なるため congrArg では閉じず、この等式 + scalePow の
    Quot.sound 経由）。 -/
theorem structSheafPfLeftDistrib_scale {R : CRing} {f : R.carrier}
    (x y z : StructSheafPreLoc R f) :
    structSheafPfAdd (structSheafPfMul x y) (structSheafPfMul x z)
      = structSheafPfScalePow (structSheafPfMul x (structSheafPfAdd y z))
        x.den := by
  apply structSheafPreLoc_ext
  · show R.add
        (R.mul (R.mul x.num y.num) (structSheafPow R f (x.den + z.den)))
        (R.mul (R.mul x.num z.num) (structSheafPow R f (x.den + y.den)))
      = R.mul (structSheafPow R f x.den)
        (R.mul x.num (R.add (R.mul y.num (structSheafPow R f z.den))
          (R.mul z.num (structSheafPow R f y.den))))
    rw [structSheafPow_add R f x.den z.den, structSheafPow_add R f x.den y.den,
      R.left_distrib x.num (R.mul y.num (structSheafPow R f z.den))
        (R.mul z.num (structSheafPow R f y.den)),
      R.left_distrib (structSheafPow R f x.den)
        (R.mul x.num (R.mul y.num (structSheafPow R f z.den)))
        (R.mul x.num (R.mul z.num (structSheafPow R f y.den))),
      ← R.mul_assoc (structSheafPow R f x.den) x.num
        (R.mul y.num (structSheafPow R f z.den)),
      ← R.mul_assoc (structSheafPow R f x.den) x.num
        (R.mul z.num (structSheafPow R f y.den)),
      R.mul_comm (structSheafPow R f x.den) x.num,
      structSheafCR_mul_comm4 R x.num y.num (structSheafPow R f x.den)
        (structSheafPow R f z.den),
      structSheafCR_mul_comm4 R x.num z.num (structSheafPow R f x.den)
        (structSheafPow R f y.den)]
  · show (x.den + y.den) + (x.den + z.den)
      = x.den + (x.den + (y.den + z.den))
    omega

/-- **M293F-5a: O(D(f)) の台** = R_f = 前分数 / 交差積関係。 -/
def StructSheafSection (R : CRing) (f : R.carrier) :=
  Quot (structSheafRel R f)

/-- 加法（二重 Quot.lift）。 -/
def structSheafQsAdd {R : CRing} {f : R.carrier}
    (a b : StructSheafSection R f) : StructSheafSection R f :=
  Quot.lift
    (fun x => Quot.lift
      (fun y => Quot.mk (structSheafRel R f) (structSheafPfAdd x y))
      (fun _ _ hy => Quot.sound (structSheafRel_add_left x hy)) b)
    (fun _ _ hx => by
      induction b using Quot.ind
      rename_i y
      exact Quot.sound (structSheafRel_add_right y hx)) a

/-- 反元。 -/
def structSheafQsNeg {R : CRing} {f : R.carrier}
    (a : StructSheafSection R f) : StructSheafSection R f :=
  Quot.lift (fun x => Quot.mk (structSheafRel R f) (structSheafPfNeg x))
    (fun _ _ hx => Quot.sound (structSheafRel_neg hx)) a

/-- 乗法。 -/
def structSheafQsMul {R : CRing} {f : R.carrier}
    (a b : StructSheafSection R f) : StructSheafSection R f :=
  Quot.lift
    (fun x => Quot.lift
      (fun y => Quot.mk (structSheafRel R f) (structSheafPfMul x y))
      (fun _ _ hy => Quot.sound (structSheafRel_mul_left x hy)) b)
    (fun _ _ hx => by
      induction b using Quot.ind
      rename_i y
      exact Quot.sound (structSheafRel_mul_right y hx)) a

/-- **M293F-5b: O(D(f)) = R_f は可換環**。 -/
def structSheaf_section_isCRing (R : CRing) (f : R.carrier) : CRing where
  carrier := StructSheafSection R f
  add := structSheafQsAdd
  zero := Quot.mk (structSheafRel R f) structSheafPfZero
  neg := structSheafQsNeg
  mul := structSheafQsMul
  one := Quot.mk (structSheafRel R f) structSheafPfOne
  add_assoc := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    exact congrArg (Quot.mk (structSheafRel R f)) (structSheafPfAdd_assoc x y z)
  zero_add := by
    intro a
    induction a using Quot.ind; rename_i x
    exact congrArg (Quot.mk (structSheafRel R f)) (structSheafPfZero_add x)
  neg_add := by
    intro a
    induction a using Quot.ind; rename_i x
    exact Quot.sound (structSheafPfNeg_add_rel x)
  add_comm := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    exact congrArg (Quot.mk (structSheafRel R f)) (structSheafPfAdd_comm x y)
  mul_assoc := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    exact congrArg (Quot.mk (structSheafRel R f)) (structSheafPfMul_assoc x y z)
  one_mul := by
    intro a
    induction a using Quot.ind; rename_i x
    exact congrArg (Quot.mk (structSheafRel R f)) (structSheafPfOne_mul x)
  mul_comm := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    exact congrArg (Quot.mk (structSheafRel R f)) (structSheafPfMul_comm x y)
  left_distrib := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    show Quot.mk (structSheafRel R f) (structSheafPfMul x (structSheafPfAdd y z))
      = Quot.mk (structSheafRel R f)
        (structSheafPfAdd (structSheafPfMul x y) (structSheafPfMul x z))
    rw [structSheafPfLeftDistrib_scale x y z]
    exact (Quot.sound (structSheafRel_scalePow
      (structSheafPfMul x (structSheafPfAdd y z)) x.den)).symm

/-! ## M293F-6: 制限準同型 R_f → R_g（D(g) ⊆ D(f)） -/

/-- (gⁿ)ᵏ = g^{n·k}。 -/
theorem structSheafPow_mul (R : CRing) (g : R.carrier) (n k : Nat) :
    structSheafPow R g (n * k)
      = structSheafPow R (structSheafPow R g n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show structSheafPow R g (n * (k + 1))
      = R.mul (structSheafPow R g n) (structSheafPow R (structSheafPow R g n) k)
    rw [← ih, Nat.mul_succ n k, structSheafPow_add R g (n * k) n, R.mul_comm]

/-- (a·f)ᵏ = aᵏ·fᵏ（可換環）。 -/
theorem structSheafPow_mul_base (R : CRing) (a f : R.carrier) (k : Nat) :
    structSheafPow R (R.mul a f) k
      = R.mul (structSheafPow R a k) (structSheafPow R f k) := by
  induction k with
  | zero =>
    show R.one = R.mul R.one R.one
    rw [R.one_mul]
  | succ k ih =>
    show R.mul (R.mul a f) (structSheafPow R (R.mul a f) k)
      = R.mul (R.mul a (structSheafPow R a k)) (R.mul f (structSheafPow R f k))
    rw [ih, structSheafCR_mul_comm4 R a f (structSheafPow R a k)
      (structSheafPow R f k)]

/-- **M293F-6a: 基本開の包含 D(g) ⊆ D(f)** の witness: gⁿ = a·f。
    （f が gⁿ を割る ⟺ V(f) ⊆ V(g)ᶜ 上で f 可逆 ⟺ D(g) ⊆ D(f)。
    包含判定そのものは後続。ここでは witness を仮定に取る。） -/
structure StructSheafIncl (R : CRing) (f g : R.carrier) where
  /-- 指数 n。 -/
  pow : Nat
  /-- 係数 a。 -/
  cof : R.carrier
  /-- gⁿ = a·f。 -/
  diveq : structSheafPow R g pow = R.mul cof f

/-- gⁿᵏ = aᵏ·fᵏ（包含 witness から）。 -/
theorem structSheafIncl_gpow {R : CRing} {f g : R.carrier}
    (incl : StructSheafIncl R f g) (k : Nat) :
    structSheafPow R g (incl.pow * k)
      = R.mul (structSheafPow R incl.cof k) (structSheafPow R f k) := by
  rw [structSheafPow_mul R g incl.pow k, incl.diveq,
    structSheafPow_mul_base R incl.cof f k]

/-- **M293F-6b: 制限の代表写像** R_f → R_g、num/fᵏ ↦ num·aᵏ/g^{n·k}
    （f⁻¹ = a/gⁿ を代入）。 -/
def structSheafRestrictPre {R : CRing} {f g : R.carrier}
    (incl : StructSheafIncl R f g) (x : StructSheafPreLoc R f) :
    StructSheafPreLoc R g :=
  ⟨R.mul x.num (structSheafPow R incl.cof x.den), incl.pow * x.den⟩

/-- 制限は交差積関係を保つ（乗数 J = n·j。gⁿ = a·f で f 関係を g 関係へ翻訳）。 -/
theorem structSheafRestrict_rel {R : CRing} {f g : R.carrier}
    (incl : StructSheafIncl R f g) {x x' : StructSheafPreLoc R f}
    (h : structSheafRel R f x x') :
    structSheafRel R g (structSheafRestrictPre incl x)
      (structSheafRestrictPre incl x') := by
  obtain ⟨j, hj⟩ := h
  refine ⟨incl.pow * j, ?_⟩
  have hP1 : R.mul (R.mul x.num (structSheafPow R incl.cof x.den))
        (R.mul (structSheafPow R incl.cof x'.den) (structSheafPow R f x'.den))
      = R.mul (R.mul (structSheafPow R incl.cof x.den)
          (structSheafPow R incl.cof x'.den))
        (R.mul x.num (structSheafPow R f x'.den)) := by
    rw [R.mul_assoc x.num (structSheafPow R incl.cof x.den)
        (R.mul (structSheafPow R incl.cof x'.den) (structSheafPow R f x'.den)),
      R.mul_assoc (structSheafPow R incl.cof x.den)
        (structSheafPow R incl.cof x'.den)
        (R.mul x.num (structSheafPow R f x'.den)),
      structSheafCR_mul_left_comm R (structSheafPow R incl.cof x'.den) x.num
        (structSheafPow R f x'.den),
      structSheafCR_mul_left_comm R (structSheafPow R incl.cof x.den) x.num
        (R.mul (structSheafPow R incl.cof x'.den) (structSheafPow R f x'.den))]
  have hP2 : R.mul (R.mul x'.num (structSheafPow R incl.cof x'.den))
        (R.mul (structSheafPow R incl.cof x.den) (structSheafPow R f x.den))
      = R.mul (R.mul (structSheafPow R incl.cof x.den)
          (structSheafPow R incl.cof x'.den))
        (R.mul x'.num (structSheafPow R f x.den)) := by
    rw [R.mul_assoc x'.num (structSheafPow R incl.cof x'.den)
        (R.mul (structSheafPow R incl.cof x.den) (structSheafPow R f x.den)),
      structSheafCR_mul_left_comm R (structSheafPow R incl.cof x'.den)
        (structSheafPow R incl.cof x.den) (structSheafPow R f x.den),
      R.mul_assoc (structSheafPow R incl.cof x.den)
        (structSheafPow R incl.cof x'.den)
        (R.mul x'.num (structSheafPow R f x.den)),
      structSheafCR_mul_left_comm R (structSheafPow R incl.cof x'.den) x'.num
        (structSheafPow R f x.den),
      structSheafCR_mul_left_comm R (structSheafPow R incl.cof x.den) x'.num
        (R.mul (structSheafPow R incl.cof x'.den) (structSheafPow R f x.den))]
  show R.mul (structSheafPow R g (incl.pow * j))
    (R.add (R.mul (R.mul x.num (structSheafPow R incl.cof x.den))
        (structSheafPow R g (incl.pow * x'.den)))
      (R.neg (R.mul (R.mul x'.num (structSheafPow R incl.cof x'.den))
        (structSheafPow R g (incl.pow * x.den))))) = R.zero
  rw [structSheafIncl_gpow incl x'.den, structSheafIncl_gpow incl x.den,
    structSheafIncl_gpow incl j, hP1, hP2,
    ← structSheafCR_mul_sub R
      (R.mul (structSheafPow R incl.cof x.den) (structSheafPow R incl.cof x'.den))
      (R.mul x.num (structSheafPow R f x'.den))
      (R.mul x'.num (structSheafPow R f x.den)),
    structSheafCR_mul_comm4 R (structSheafPow R incl.cof j)
      (structSheafPow R f j)
      (R.mul (structSheafPow R incl.cof x.den)
        (structSheafPow R incl.cof x'.den))
      (R.add (R.mul x.num (structSheafPow R f x'.den))
        (R.neg (R.mul x'.num (structSheafPow R f x.den)))),
    hj, R.mul_zero]

/-- **M293F-6c: 制限写像** O(D(f)) → O(D(g))。 -/
def structSheafRestrict {R : CRing} {f g : R.carrier}
    (incl : StructSheafIncl R f g) (s : StructSheafSection R f) :
    StructSheafSection R g :=
  Quot.lift (fun x => Quot.mk (structSheafRel R g) (structSheafRestrictPre incl x))
    (fun _ _ h => Quot.sound (structSheafRestrict_rel incl h)) s

/-- 1 のべきは 1。 -/
theorem structSheafPow_one_eq_one (R : CRing) (k : Nat) :
    structSheafPow R R.one k = R.one := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show R.mul R.one (structSheafPow R R.one k) = R.one
    rw [ih, R.one_mul]

/-! ## M293F-7: 制限は環準同型・前層公理 -/

/-- 制限は加法を保つ（代表 strict 等式）。 -/
theorem structSheafRestrictPre_add {R : CRing} {f g : R.carrier}
    (incl : StructSheafIncl R f g) (x y : StructSheafPreLoc R f) :
    structSheafRestrictPre incl (structSheafPfAdd x y)
      = structSheafPfAdd (structSheafRestrictPre incl x)
        (structSheafRestrictPre incl y) := by
  have hT1 : R.mul (R.mul x.num (structSheafPow R f y.den))
        (R.mul (structSheafPow R incl.cof x.den)
          (structSheafPow R incl.cof y.den))
      = R.mul (R.mul x.num (structSheafPow R incl.cof x.den))
        (R.mul (structSheafPow R incl.cof y.den) (structSheafPow R f y.den)) := by
    rw [R.mul_assoc x.num (structSheafPow R f y.den)
        (R.mul (structSheafPow R incl.cof x.den)
          (structSheafPow R incl.cof y.den)),
      structSheafCR_mul_left_comm R (structSheafPow R f y.den)
        (structSheafPow R incl.cof x.den) (structSheafPow R incl.cof y.den),
      R.mul_comm (structSheafPow R f y.den) (structSheafPow R incl.cof y.den),
      R.mul_assoc x.num (structSheafPow R incl.cof x.den)
        (R.mul (structSheafPow R incl.cof y.den) (structSheafPow R f y.den))]
  have hT2 : R.mul (R.mul y.num (structSheafPow R f x.den))
        (R.mul (structSheafPow R incl.cof x.den)
          (structSheafPow R incl.cof y.den))
      = R.mul (R.mul y.num (structSheafPow R incl.cof y.den))
        (R.mul (structSheafPow R incl.cof x.den) (structSheafPow R f x.den)) := by
    rw [R.mul_assoc y.num (structSheafPow R f x.den)
        (R.mul (structSheafPow R incl.cof x.den)
          (structSheafPow R incl.cof y.den)),
      structSheafCR_mul_left_comm R (structSheafPow R f x.den)
        (structSheafPow R incl.cof x.den) (structSheafPow R incl.cof y.den),
      R.mul_comm (structSheafPow R f x.den) (structSheafPow R incl.cof y.den),
      R.mul_assoc y.num (structSheafPow R incl.cof y.den)
        (R.mul (structSheafPow R incl.cof x.den) (structSheafPow R f x.den)),
      structSheafCR_mul_left_comm R (structSheafPow R incl.cof y.den)
        (structSheafPow R incl.cof x.den) (structSheafPow R f x.den)]
  apply structSheafPreLoc_ext
  · show R.mul (R.add (R.mul x.num (structSheafPow R f y.den))
          (R.mul y.num (structSheafPow R f x.den)))
        (structSheafPow R incl.cof (x.den + y.den))
      = R.add (R.mul (R.mul x.num (structSheafPow R incl.cof x.den))
          (structSheafPow R g (incl.pow * y.den)))
        (R.mul (R.mul y.num (structSheafPow R incl.cof y.den))
          (structSheafPow R g (incl.pow * x.den)))
    rw [structSheafIncl_gpow incl y.den, structSheafIncl_gpow incl x.den,
      structSheafPow_add R incl.cof x.den y.den,
      R.right_distrib (R.mul x.num (structSheafPow R f y.den))
        (R.mul y.num (structSheafPow R f x.den))
        (R.mul (structSheafPow R incl.cof x.den)
          (structSheafPow R incl.cof y.den)),
      hT1, hT2]
  · show incl.pow * (x.den + y.den) = incl.pow * x.den + incl.pow * y.den
    exact Nat.mul_add _ _ _

/-- 制限は乗法を保つ。 -/
theorem structSheafRestrictPre_mul {R : CRing} {f g : R.carrier}
    (incl : StructSheafIncl R f g) (x y : StructSheafPreLoc R f) :
    structSheafRestrictPre incl (structSheafPfMul x y)
      = structSheafPfMul (structSheafRestrictPre incl x)
        (structSheafRestrictPre incl y) := by
  apply structSheafPreLoc_ext
  · show R.mul (R.mul x.num y.num) (structSheafPow R incl.cof (x.den + y.den))
      = R.mul (R.mul x.num (structSheafPow R incl.cof x.den))
        (R.mul y.num (structSheafPow R incl.cof y.den))
    rw [structSheafPow_add R incl.cof x.den y.den,
      structSheafCR_mul_comm4 R x.num y.num (structSheafPow R incl.cof x.den)
        (structSheafPow R incl.cof y.den)]
  · show incl.pow * (x.den + y.den) = incl.pow * x.den + incl.pow * y.den
    exact Nat.mul_add _ _ _

/-- 制限は 1 を保つ。 -/
theorem structSheafRestrictPre_one {R : CRing} {f g : R.carrier}
    (incl : StructSheafIncl R f g) :
    structSheafRestrictPre incl structSheafPfOne = structSheafPfOne := by
  apply structSheafPreLoc_ext
  · show R.mul R.one (structSheafPow R incl.cof 0) = R.one
    rw [structSheafPow_zero, structSheafCR_mul_one]
  · rfl

/-- **M293F-7a: 制限 O(D(f)) → O(D(g)) は環準同型**。 -/
def structSheaf_restrict_isHom {R : CRing} {f g : R.carrier}
    (incl : StructSheafIncl R f g) :
    RingHom (structSheaf_section_isCRing R f) (structSheaf_section_isCRing R g) where
  map := structSheafRestrict incl
  map_add := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    exact congrArg (Quot.mk (structSheafRel R g))
      (structSheafRestrictPre_add incl x y)
  map_mul := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    exact congrArg (Quot.mk (structSheafRel R g))
      (structSheafRestrictPre_mul incl x y)
  map_one :=
    congrArg (Quot.mk (structSheafRel R g)) (structSheafRestrictPre_one incl)

/-- 恒等包含 D(f) ⊆ D(f)（f¹ = 1·f）。 -/
def structSheafInclRefl {R : CRing} (f : R.carrier) : StructSheafIncl R f f where
  pow := 1
  cof := R.one
  diveq := by
    show R.mul f R.one = R.mul R.one f
    rw [structSheafCR_mul_one, R.one_mul]

/-- 包含の合成 D(h) ⊆ D(g) ⊆ D(f)（h^{mn} = (bⁿ·a)·f）。 -/
def structSheafInclComp {R : CRing} {f g h : R.carrier}
    (i1 : StructSheafIncl R f g) (i2 : StructSheafIncl R g h) :
    StructSheafIncl R f h where
  pow := i2.pow * i1.pow
  cof := R.mul (structSheafPow R i2.cof i1.pow) i1.cof
  diveq := by
    rw [structSheafPow_mul R h i2.pow i1.pow, i2.diveq,
      structSheafPow_mul_base R i2.cof g i1.pow, i1.diveq,
      ← R.mul_assoc (structSheafPow R i2.cof i1.pow) i1.cof f]

/-- 恒等包含の制限は恒等（代表 strict）。 -/
theorem structSheafRestrictPre_reflEq {R : CRing} {f : R.carrier}
    (x : StructSheafPreLoc R f) :
    structSheafRestrictPre (structSheafInclRefl f) x = x := by
  apply structSheafPreLoc_ext
  · show R.mul x.num (structSheafPow R R.one x.den) = x.num
    rw [structSheafPow_one_eq_one, structSheafCR_mul_one]
  · show 1 * x.den = x.den
    exact Nat.one_mul _

/-- 合成の制限は制限の合成（代表 strict）。 -/
theorem structSheafRestrictPre_comp {R : CRing} {f g h : R.carrier}
    (i1 : StructSheafIncl R f g) (i2 : StructSheafIncl R g h)
    (x : StructSheafPreLoc R f) :
    structSheafRestrictPre i2 (structSheafRestrictPre i1 x)
      = structSheafRestrictPre (structSheafInclComp i1 i2) x := by
  apply structSheafPreLoc_ext
  · show R.mul (R.mul x.num (structSheafPow R i1.cof x.den))
        (structSheafPow R i2.cof (i1.pow * x.den))
      = R.mul x.num (structSheafPow R
          (R.mul (structSheafPow R i2.cof i1.pow) i1.cof) x.den)
    rw [structSheafPow_mul_base R (structSheafPow R i2.cof i1.pow) i1.cof x.den,
      ← structSheafPow_mul R i2.cof i1.pow x.den,
      R.mul_assoc x.num (structSheafPow R i1.cof x.den)
        (structSheafPow R i2.cof (i1.pow * x.den)),
      R.mul_comm (structSheafPow R i1.cof x.den)
        (structSheafPow R i2.cof (i1.pow * x.den))]
  · show i2.pow * (i1.pow * x.den) = (i2.pow * i1.pow) * x.den
    exact (Nat.mul_assoc _ _ _).symm

/-- **M293F-7b: 前層公理（制限の恒等）** D(f)⊆D(f) の制限は恒等。 -/
theorem structSheaf_restrict_id {R : CRing} (f : R.carrier)
    (s : StructSheafSection R f) :
    structSheafRestrict (structSheafInclRefl f) s = s := by
  induction s using Quot.ind; rename_i x
  exact congrArg (Quot.mk (structSheafRel R f)) (structSheafRestrictPre_reflEq x)

/-- **M293F-7c: 前層公理（制限の合成）** D(h)⊆D(g)⊆D(f) で制限の合成
    ＝直接制限。 -/
theorem structSheaf_restrict_comp {R : CRing} {f g h : R.carrier}
    (i1 : StructSheafIncl R f g) (i2 : StructSheafIncl R g h)
    (s : StructSheafSection R f) :
    structSheafRestrict i2 (structSheafRestrict i1 s)
      = structSheafRestrict (structSheafInclComp i1 i2) s := by
  induction s using Quot.ind; rename_i x
  exact congrArg (Quot.mk (structSheafRel R h))
    (structSheafRestrictPre_comp i1 i2 x)

/-! ## M293F-8: 茎 R_P の局所性（骨組み） -/

/-- 環 S の単元（可逆元）。 -/
def StructSheafUnit (S : CRing) (u : S.carrier) : Prop :=
  ∃ v, S.mul u v = S.one

/-- 1 は単元。 -/
theorem structSheaf_unit_one (S : CRing) : StructSheafUnit S S.one :=
  ⟨S.one, S.one_mul S.one⟩

/-- 単元の積は単元（＝単元は乗法部分モノイド、非単元がイデアル候補の骨組み）。 -/
theorem structSheaf_unit_mul (S : CRing) {a b : S.carrier}
    (ha : StructSheafUnit S a) (hb : StructSheafUnit S b) :
    StructSheafUnit S (S.mul a b) := by
  obtain ⟨va, hva⟩ := ha
  obtain ⟨vb, hvb⟩ := hb
  refine ⟨S.mul va vb, ?_⟩
  rw [structSheafCR_mul_comm4 S a b va vb, hva, hvb, S.one_mul]

/-- **M293F-8a: 局所化 O(D(f)) では f/1 が単元**（f⁻¹ = 1/f）。
    ＝局所化が f を可逆化するという局所性の種。 -/
theorem structSheaf_section_f_unit (R : CRing) (f : R.carrier) :
    StructSheafUnit (structSheaf_section_isCRing R f)
      (Quot.mk (structSheafRel R f) ⟨f, 0⟩) := by
  refine ⟨Quot.mk (structSheafRel R f) ⟨R.one, 1⟩, ?_⟩
  show Quot.mk (structSheafRel R f)
      (structSheafPfMul (⟨f, 0⟩ : StructSheafPreLoc R f) ⟨R.one, 1⟩)
    = Quot.mk (structSheafRel R f) structSheafPfOne
  apply Quot.sound
  refine ⟨0, ?_⟩
  show R.mul (structSheafPow R f 0)
    (R.add (R.mul (R.mul f R.one) (structSheafPow R f 0))
      (R.neg (R.mul R.one (R.mul f (structSheafPow R f 0))))) = R.zero
  rw [structSheafPow_zero, R.one_mul, structSheafCR_mul_one R (R.mul f R.one),
    R.one_mul (R.mul f R.one), structSheafCR_add_neg]

/-- **M293F-8b: 局所環の特徴づけ**（骨組み）: 0 は非単元、かつ和が単元
    ならどちらかが単元（＝非単元全体が唯一の極大イデアルを成す条件）。
    茎 R_P（S = R∖P での局所化）がこれを満たすことの完全証明と R_P の
    環構成は後続（正直申告）。 -/
def StructSheafIsLocal (S : CRing) : Prop :=
  (¬ StructSheafUnit S S.zero)
    ∧ (∀ a b, StructSheafUnit S (S.add a b)
        → StructSheafUnit S a ∨ StructSheafUnit S b)

/-- 茎の局所性骨組み: 任意環で単元は 1 を含む乗法部分モノイド（非単元＝
    極大イデアル候補）。R_P が `StructSheafIsLocal` を満たすことは後続。 -/
theorem structSheaf_stalk_local (S : CRing) :
    StructSheafUnit S S.one
      ∧ (∀ a b, StructSheafUnit S a → StructSheafUnit S b
          → StructSheafUnit S (S.mul a b)) :=
  ⟨structSheaf_unit_one S, fun _ _ ha hb => structSheaf_unit_mul S ha hb⟩

/-! ## M293F-9: capstone（構造層データ・前層・大域切断） -/

/-- **M293F-9a: 構造層データ** — アフィンスキーム Spec R の構造層 O の
    基本開 D(f) の基の上の前層構造を束ねる。 -/
structure StructureSheafData (R : CRing) where
  /-- 基本開 D(f) 上の切断環 O(D(f)) = R_f。 -/
  sec : R.carrier → CRing
  /-- O(D(f)) は f-局所化 R_f。 -/
  sec_spec : ∀ f, sec f = structSheaf_section_isCRing R f
  /-- 制限写像 O(D(f)) → O(D(g))。 -/
  restr : {f g : R.carrier} → StructSheafIncl R f g →
    StructSheafSection R f → StructSheafSection R g
  /-- 前層公理（恒等）。 -/
  restr_id : ∀ (f : R.carrier) (s : StructSheafSection R f),
    restr (structSheafInclRefl f) s = s
  /-- 前層公理（合成）。 -/
  restr_comp : ∀ {f g h : R.carrier} (i1 : StructSheafIncl R f g)
    (i2 : StructSheafIncl R g h) (s : StructSheafSection R f),
    restr i2 (restr i1 s) = restr (structSheafInclComp i1 i2) s

/-- **M293F-9b: 構造層データの存在**（本物の前層）。 -/
def structSheaf_exists (R : CRing) : StructureSheafData R where
  sec := fun f => structSheaf_section_isCRing R f
  sec_spec := fun _ => rfl
  restr := fun {_ _} incl => structSheafRestrict incl
  restr_id := structSheaf_restrict_id
  restr_comp := fun {_ _ _} i1 i2 s => structSheaf_restrict_comp i1 i2 s

/-- **M293F-9c: 前層公理の束ね**（恒等・合成）。 -/
theorem structSheaf_presheaf (R : CRing) :
    (∀ (f : R.carrier) (s : StructSheafSection R f),
      structSheafRestrict (structSheafInclRefl f) s = s)
    ∧ (∀ {f g h : R.carrier} (i1 : StructSheafIncl R f g)
        (i2 : StructSheafIncl R g h) (s : StructSheafSection R f),
      structSheafRestrict i2 (structSheafRestrict i1 s)
        = structSheafRestrict (structSheafInclComp i1 i2) s) :=
  ⟨structSheaf_restrict_id,
    fun {_ _ _} i1 i2 s => structSheaf_restrict_comp i1 i2 s⟩

/-- 大域評価 O(D(1)) → R の well-defined 性（R_1 では 1 のべきが 1 ゆえ
    関係は num の一致に退化）。 -/
theorem structSheafGlobalEval_wd {R : CRing}
    {x y : StructSheafPreLoc R R.one} (h : structSheafRel R R.one x y) :
    x.num = y.num := by
  obtain ⟨j, hj⟩ := h
  rw [structSheafPow_one_eq_one R j, structSheafPow_one_eq_one R y.den,
    structSheafPow_one_eq_one R x.den, R.one_mul, structSheafCR_mul_one,
    structSheafCR_mul_one] at hj
  exact structSheafCR_eq_of_sub_zero R hj

/-- 大域評価 O(D(1)) → R、num/1ᵏ ↦ num。 -/
def structSheafGlobalEval {R : CRing} (s : StructSheafSection R R.one) :
    R.carrier :=
  Quot.lift (fun x => x.num) (fun _ _ h => structSheafGlobalEval_wd h) s

/-- **M293F-9d: 大域切断の環準同型** R → O(D(1))、r ↦ r/1。 -/
def structSheaf_globalHom (R : CRing) :
    RingHom R (structSheaf_section_isCRing R R.one) where
  map := fun r => Quot.mk (structSheafRel R R.one) ⟨r, 0⟩
  map_add := fun a b => by
    show Quot.mk (structSheafRel R R.one) (⟨R.add a b, 0⟩ : StructSheafPreLoc R R.one)
      = Quot.mk (structSheafRel R R.one)
        (structSheafPfAdd (⟨a, 0⟩ : StructSheafPreLoc R R.one) ⟨b, 0⟩)
    apply congrArg (Quot.mk (structSheafRel R R.one))
    apply structSheafPreLoc_ext
    · show R.add a b
        = R.add (R.mul a (structSheafPow R R.one 0))
          (R.mul b (structSheafPow R R.one 0))
      rw [structSheafPow_zero, structSheafCR_mul_one, structSheafCR_mul_one]
    · rfl
  map_mul := fun a b => by
    show Quot.mk (structSheafRel R R.one) (⟨R.mul a b, 0⟩ : StructSheafPreLoc R R.one)
      = Quot.mk (structSheafRel R R.one)
        (structSheafPfMul (⟨a, 0⟩ : StructSheafPreLoc R R.one) ⟨b, 0⟩)
    apply congrArg (Quot.mk (structSheafRel R R.one))
    apply structSheafPreLoc_ext
    · rfl
    · rfl
  map_one := rfl

/-- **M293F-9e: 大域切断は元の環 O(D(1)) = O(Spec R) = R**
    （R → O(D(1)) と評価 O(D(1)) → R が互いに逆＝環同型）。 -/
theorem structSheaf_global_eq_ring (R : CRing) :
    (∀ r : R.carrier,
        structSheafGlobalEval ((structSheaf_globalHom R).map r) = r)
    ∧ (∀ s : StructSheafSection R R.one,
        (structSheaf_globalHom R).map (structSheafGlobalEval s) = s) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro s
  induction s using Quot.ind; rename_i x
  show Quot.mk (structSheafRel R R.one) (⟨x.num, 0⟩ : StructSheafPreLoc R R.one)
    = Quot.mk (structSheafRel R R.one) x
  apply Quot.sound
  refine ⟨0, ?_⟩
  show R.mul (structSheafPow R R.one 0)
    (R.add (R.mul x.num (structSheafPow R R.one x.den))
      (R.neg (R.mul x.num (structSheafPow R R.one 0)))) = R.zero
  rw [structSheafPow_one_eq_one R x.den, structSheafPow_zero,
    structSheafCR_add_neg, R.mul_zero]

end IUT
