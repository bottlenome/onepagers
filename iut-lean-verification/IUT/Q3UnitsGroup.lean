/-
  IUT/Q3UnitsGroup.lean — A2c-2（柱A2: 実 ℚ₃^× 単数群 — 3^ℤ × ℤ₃^× ↪ ℚ₃^× の実現形）

  ── 主要成果の分類: **[実／昇格(a)]**。`FullReciprocity.lean:64` の抽象直積代理
     `QpUnits 3 isPrime_three = prodGrp intGrp (zpUnits 3 isPrime_three)`（「ℚ_p^× =
     p^ℤ × ℤ_p^× の明示同型は未形式化」と honest な K^× 代理）を、A2c で本物構成した
     実体 ℚ₃ = ℤ₃[1/3]（q3Ring）の上へ**昇格**する。準同型 (k,u) ↦ [3^k·u]（k<0 は
     分母 3^{-k}）を、実 ℚ₃ の局所化 Quot 上に明示構成し、単射・積保存を完全証明する。
     toy 主語なし——主語は実 zpRing 3 の実局所化 q3Ring と実単数群 zpUnits 3。

  complete_pct 影響: **A2 A2c-2 を前進**（FullReciprocity の抽象直積 K^× 代理を
  実 ℚ₃^× へ昇格・設計見込み A2 →0.65・柱A 45→46・q3f と共に A2c）。内容:
  (i) 埋め込み q3uEmbed : (3^ℤ × ℤ₃^×) → ℚ₃（(k,u) ↦ [3^{k.toNat}·u / 3^{(-k).toNat}]・
      Int の符号を toNat の分子/分母振り分けで if 無しに一様化）、
  (ii) 積保存 q3u_embed_hom（prodGrp の積 (k+k', u·u') が ℚ₃ の分数積へ・3 冪の指数法則）、
  (iii) 単射 q3u_embed_inj（v=k 分離は z3v_exact_mul + 単数の exact=0・単数部は 3 冪の
       正則性による消去 q3S_regular）、
  (iv) 全射性の像特徴付け q3u_image_char（非零 witness ¬z3vGe a (k+1) を持つ mk(a,3ⁿ) は
      全て 3^κ·単数形＝z3v_extract の副産物・∃ 形）、
  (v) 束ね q3uData（実 ℚ₃^× への単射準同型 3^ℤ×ℤ₃^× ↪ ℚ₃ の構造レコード）。

  **A8（Tate 曲線 K^×/q^ℤ を実 ℚ₃^× 上で・v(q)≥1 の実 q）と B2（相互写像の主語）の
  ブロッカー解消はこのファイルが直接の接点**。

  正直な限定（§3 準拠・消去/弱化しない・既存 surrogate は消さない）:
  - **total（全域）逆元は主張しない**。埋め込みの像は ℚ₃^× の部分集合（3^ℤ × ℤ₃^× の像）で、
    全射性 q3u_image_char は「正の非零 witness（¬z3vGe a (k+1)）付き元」に対する ∃ 形。
    任意元の逆元計算は v(x) 特定（否定形からの witness 抽出・Markov）を要し choice-free 断片で
    関数化不能（ℚ_p は構成的には離散体でない）。この限定は A2c の q3f_has_inverses と同じライン。
  - **p = 3 固定**・基礎体 ℚ のみ。ℚ↪ℚ₃（A2c-3）・ℚ₃ の位相・G_{ℚ₃}・分岐は範囲外（後続）。
  - 群構造としては ℚ₃ が CRing（体でない）なので、埋め込みは「乗法モノイドへの単射準同型」
    として束ねる（Grp Hom ではなく Q3UnitsGroupData レコード）。FullReciprocity の
    `QpUnits`/`recQp` surrogate はそのまま保持（消さない）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ（Classical.choice 無し）。
-/
import IUT.Q3LocalField
import IUT.FullReciprocity

namespace IUT

/-! ## A2c-2-0: 埋め込みの前分数と本体 -/

/-- **A2c-2-0a: 埋め込みの前分数** (k, u) ↦ 3^{k.toNat}·u / 3^{(-k).toNat}。
    Int k の符号を toNat の分子側 / 分母側への振り分けで if 無しに一様化する:
    k ≥ 0 なら分子 3^k·u・分母 3^0=1、k < 0 なら分子 3^0·u=u・分母 3^{-k}。 -/
def q3uEmbedPre (k : Int) (u : z3.carrier) : ringLocPre z3 q3S :=
  ⟨z3.mul (ringLocPow z3 q3fThree k.toNat) u,
   ringLocPow z3 q3fThree (-k).toNat, ⟨(-k).toNat, rfl⟩⟩

/-- **A2c-2-0b（★）: 実 ℚ₃^× 埋め込み** (k, u) ↦ [3^k·u] : 3^ℤ × ℤ₃^× → ℚ₃。
    FullReciprocity の抽象直積代理 `QpUnits 3 isPrime_three` を実 ℚ₃ の上へ昇格。 -/
def q3uEmbed (ku : (QpUnits 3 isPrime_three).carrier) : q3Ring.carrier :=
  Quot.mk (ringLocRel q3S) (q3uEmbedPre ku.1 ku.2.val)

/-! ## A2c-2-1: 3 冪の入れ替え補題と分数同値の一般形 -/

/-- 3 冪と単数の積の入れ替え: (3^m·u)·(3^n·w) = 3^{m+n}·(u·w)。 -/
theorem q3u_pow_mul_interchange (m n : Nat) (u w : z3.carrier) :
    z3.mul (z3.mul (ringLocPow z3 q3fThree m) u) (z3.mul (ringLocPow z3 q3fThree n) w)
      = z3.mul (ringLocPow z3 q3fThree (m + n)) (z3.mul u w) := by
  rw [cring_mul_mul_swap' z3 (ringLocPow z3 q3fThree m) u (ringLocPow z3 q3fThree n) w,
      ← ringLocPow_add z3 q3fThree m n]

/-- **A2c-2-1（★補題）: 分数同値の指数形** — 分子の単数部 w が共通なら、
    分子/分母の 3 冪の指数が交差和で一致するとき ℚ₃ で等しい:
    3^p·w / 3^q = 3^{p'}·w / 3^{q'} ⟺ p + q' = p' + q。
    3^ℤ の分子/分母簿記を一手に閉じる（hom・image_char で共用）。 -/
theorem q3u_frac_eq (p q p' q' : Nat) (w : z3.carrier)
    (hpq : p + q' = p' + q) :
    Quot.mk (ringLocRel q3S)
        (⟨z3.mul (ringLocPow z3 q3fThree p) w, ringLocPow z3 q3fThree q, ⟨q, rfl⟩⟩
          : ringLocPre z3 q3S)
      = Quot.mk (ringLocRel q3S)
        (⟨z3.mul (ringLocPow z3 q3fThree p') w, ringLocPow z3 q3fThree q', ⟨q', rfl⟩⟩
          : ringLocPre z3 q3S) := by
  apply Quot.sound
  refine ⟨z3.one, q3S.one_mem, ?_⟩
  show z3.mul z3.one (z3.mul (z3.mul (ringLocPow z3 q3fThree p) w) (ringLocPow z3 q3fThree q'))
     = z3.mul z3.one (z3.mul (z3.mul (ringLocPow z3 q3fThree p') w) (ringLocPow z3 q3fThree q))
  rw [z3.one_mul, z3.one_mul,
      cring_mul_right_swap z3 (ringLocPow z3 q3fThree p) w (ringLocPow z3 q3fThree q'),
      cring_mul_right_swap z3 (ringLocPow z3 q3fThree p') w (ringLocPow z3 q3fThree q),
      ← ringLocPow_add z3 q3fThree p q',
      ← ringLocPow_add z3 q3fThree p' q, hpq]

/-! ## A2c-2-2: 単数の厳密付値は 0 -/

/-- **A2c-2-2: ℤ₃ の単数は厳密付値 0**（v(u)=0）——単射の v=k 分離の材料。 -/
theorem q3u_unit_exact0 {u : z3.carrier} (hu : IsZpUnit 3 u) : z3vExact 3 u 0 := by
  refine ⟨z3vGe_zero 3 u, ?_⟩
  intro h
  obtain ⟨a, ha, hpa⟩ := hu
  apply hpa
  have h1 : Quot.mk (modCong (3 ^ 1)).rel a = Quot.mk (modCong (3 ^ 1)).rel 0 := by
    rw [← ha]; exact h
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (3 ^ 1)) h1
  rw [Nat.pow_one] at hk
  exact ⟨k, by omega⟩

/-! ## A2c-2-3（★）: 積保存 -/

/-- **A2c-2-3（★）: 埋め込みは積を保存する** — prodGrp の積
    (k, u)·(k', u') = (k+k', u·u') が ℚ₃ の分数積 [3^k·u]·[3^{k'}·u'] へ写る。
    3 冪の指数法則（分子 3^{(k+k').toNat} と分母 3^{(-(k+k')).toNat}）を q3u_frac_eq で閉じる。 -/
theorem q3u_embed_hom (x y : (QpUnits 3 isPrime_three).carrier) :
    q3uEmbed ((QpUnits 3 isPrime_three).mul x y)
      = q3Ring.mul (q3uEmbed x) (q3uEmbed y) := by
  show Quot.mk (ringLocRel q3S) (q3uEmbedPre (x.1 + y.1) (z3.mul x.2.val y.2.val))
     = Quot.mk (ringLocRel q3S)
         (ringLocMul (q3uEmbedPre x.1 x.2.val) (q3uEmbedPre y.1 y.2.val))
  have hcanon : ringLocMul (q3uEmbedPre x.1 x.2.val) (q3uEmbedPre y.1 y.2.val)
      = (⟨z3.mul (ringLocPow z3 q3fThree (x.1.toNat + y.1.toNat)) (z3.mul x.2.val y.2.val),
          ringLocPow z3 q3fThree ((-x.1).toNat + (-y.1).toNat),
          ⟨(-x.1).toNat + (-y.1).toNat, rfl⟩⟩ : ringLocPre z3 q3S) := by
    apply ringLocPre_ext
    · show z3.mul (z3.mul (ringLocPow z3 q3fThree x.1.toNat) x.2.val)
            (z3.mul (ringLocPow z3 q3fThree y.1.toNat) y.2.val)
        = z3.mul (ringLocPow z3 q3fThree (x.1.toNat + y.1.toNat)) (z3.mul x.2.val y.2.val)
      exact q3u_pow_mul_interchange x.1.toNat y.1.toNat x.2.val y.2.val
    · show z3.mul (ringLocPow z3 q3fThree (-x.1).toNat) (ringLocPow z3 q3fThree (-y.1).toNat)
        = ringLocPow z3 q3fThree ((-x.1).toNat + (-y.1).toNat)
      exact (ringLocPow_add z3 q3fThree (-x.1).toNat (-y.1).toNat).symm
  rw [hcanon]
  exact q3u_frac_eq (x.1 + y.1).toNat (-(x.1 + y.1)).toNat
    (x.1.toNat + y.1.toNat) ((-x.1).toNat + (-y.1).toNat)
    (z3.mul x.2.val y.2.val) (by omega)

/-- 付値の交差和からの Int 復元（単射の第 1 成分抽出の算術核・omega）。 -/
theorem q3u_toNat_cancel {s : Nat} {p q : Int}
    (h : s + (p.toNat + 0 + (-q).toNat) = s + (q.toNat + 0 + (-p).toNat)) : p = q := by
  omega

/-! ## A2c-2-4（★）: 単射 -/

/-- **A2c-2-4（★）: 埋め込みは単射** — 付値 v=k の分離（z3v_exact_mul + 単数の exact=0・
    z3v_exact_unique）で第 1 成分 k を復元し、第 2 成分は 3 冪の正則性 q3S_regular による
    消去で単数 u を復元する。 -/
theorem q3u_embed_inj (x y : (QpUnits 3 isPrime_three).carrier)
    (h : q3uEmbed x = q3uEmbed y) : x = y := by
  have h' : Quot.mk (ringLocRel q3S) (q3uEmbedPre x.1 x.2.val)
          = Quot.mk (ringLocRel q3S) (q3uEmbedPre y.1 y.2.val) := h
  obtain ⟨t, ht, e⟩ := q3f_exact h'
  obtain ⟨s, hs⟩ := ht
  have ht' : z3vExact 3 t s := by rw [hs]; exact q3_pow_exact s
  have e2 : z3.mul t (z3.mul (z3.mul (ringLocPow z3 q3fThree x.1.toNat) x.2.val)
              (ringLocPow z3 q3fThree (-y.1).toNat))
          = z3.mul t (z3.mul (z3.mul (ringLocPow z3 q3fThree y.1.toNat) y.2.val)
              (ringLocPow z3 q3fThree (-x.1).toNat)) := e
  -- 第 1 成分 k の復元（付値 v=k 分離）
  have hxu : z3vExact 3 x.2.val 0 := q3u_unit_exact0 x.2.property
  have hyu : z3vExact 3 y.2.val 0 := q3u_unit_exact0 y.2.property
  have hExL : z3vExact 3 (z3.mul t (z3.mul (z3.mul (ringLocPow z3 q3fThree x.1.toNat) x.2.val)
                (ringLocPow z3 q3fThree (-y.1).toNat)))
              (s + ((x.1.toNat + 0) + (-y.1).toNat)) :=
    z3v_exact_mul ht' (z3v_exact_mul (z3v_exact_mul (q3_pow_exact x.1.toNat) hxu)
      (q3_pow_exact (-y.1).toNat))
  have hExR : z3vExact 3 (z3.mul t (z3.mul (z3.mul (ringLocPow z3 q3fThree y.1.toNat) y.2.val)
                (ringLocPow z3 q3fThree (-x.1).toNat)))
              (s + ((y.1.toNat + 0) + (-x.1).toNat)) :=
    z3v_exact_mul ht' (z3v_exact_mul (z3v_exact_mul (q3_pow_exact y.1.toNat) hyu)
      (q3_pow_exact (-x.1).toNat))
  rw [e2] at hExL
  have hvaleq := z3v_exact_unique hExL hExR
  have hx1 : x.1 = y.1 := q3u_toNat_cancel hvaleq
  -- 第 2 成分 u の復元（3 冪の正則性による消去）
  rw [hx1] at e2
  rw [cring_mul_right_swap z3 (ringLocPow z3 q3fThree y.1.toNat) x.2.val
        (ringLocPow z3 q3fThree (-y.1).toNat),
      cring_mul_right_swap z3 (ringLocPow z3 q3fThree y.1.toNat) y.2.val
        (ringLocPow z3 q3fThree (-y.1).toNat),
      ← z3.mul_assoc t (z3.mul (ringLocPow z3 q3fThree y.1.toNat)
        (ringLocPow z3 q3fThree (-y.1).toNat)) x.2.val,
      ← z3.mul_assoc t (z3.mul (ringLocPow z3 q3fThree y.1.toNat)
        (ringLocPow z3 q3fThree (-y.1).toNat)) y.2.val] at e2
  have hmemR : q3S.set (z3.mul t (z3.mul (ringLocPow z3 q3fThree y.1.toNat)
      (ringLocPow z3 q3fThree (-y.1).toNat))) :=
    q3S.mul_mem t _ ⟨s, hs⟩
      (q3S.mul_mem _ _ ⟨y.1.toNat, rfl⟩ ⟨(-y.1).toNat, rfl⟩)
  have hx2 : x.2 = y.2 := by
    apply Subtype.ext
    apply cring_eq_of_sub_zero z3
    apply q3S_regular hmemR
    rw [z3.left_distrib (z3.mul t (z3.mul (ringLocPow z3 q3fThree y.1.toNat)
          (ringLocPow z3 q3fThree (-y.1).toNat))) x.2.val (z3.neg y.2.val),
        ringLoc_mul_neg z3 (z3.mul t (z3.mul (ringLocPow z3 q3fThree y.1.toNat)
          (ringLocPow z3 q3fThree (-y.1).toNat))) y.2.val, e2]
    exact cring_add_neg z3 (z3.mul (z3.mul t (z3.mul (ringLocPow z3 q3fThree y.1.toNat)
      (ringLocPow z3 q3fThree (-y.1).toNat))) y.2.val)
  show x = y
  rw [show x = (x.1, x.2) from rfl, show y = (y.1, y.2) from rfl, hx1, hx2]

/-! ## A2c-2-5: 全射性の像特徴付け（∃ 形） -/

/-- **A2c-2-5: 像の特徴付け（全射性の ∃ 形）** — 非零 witness（¬ z3vGe a (k+1)）を持つ
    分子 a の元 mk(a, 3ⁿ) は全て 3^κ·単数形（κ = v − n）＝埋め込みの像に入る。
    z3v_extract で得た a = 3^v·u（choice-free）の副産物。total ではなく ∃ 形（§3.1）。 -/
theorem q3u_image_char (a : z3.carrier) (n k : Nat) (h : ¬ z3vGe 3 a (k + 1)) :
    ∃ (κ : Int) (u : (zpUnits 3 isPrime_three).carrier),
      Quot.mk (ringLocRel q3S)
          (⟨a, ringLocPow z3 q3fThree n, ⟨n, rfl⟩⟩ : ringLocPre z3 q3S)
        = q3uEmbed (κ, u) := by
  obtain ⟨v, u0, _hvk, hu0, hae, _hex⟩ := z3v_extract k a h
  refine ⟨(v : Int) - (n : Int), ⟨u0, hu0⟩, ?_⟩
  have ha : a = z3.mul (ringLocPow z3 q3fThree v) u0 := by
    rw [q3_ringLocPow_eq_zpPow v]; exact hae
  show Quot.mk (ringLocRel q3S) (⟨a, ringLocPow z3 q3fThree n, ⟨n, rfl⟩⟩ : ringLocPre z3 q3S)
     = Quot.mk (ringLocRel q3S) (q3uEmbedPre ((v : Int) - (n : Int)) u0)
  rw [ha]
  exact q3u_frac_eq v n ((v : Int) - (n : Int)).toNat (-((v : Int) - (n : Int))).toNat u0
    (by omega)

/-! ## A2c-2-6: 束ね — 実 ℚ₃^× 単数群構造 -/

/-- **A2c-2-6: 実 ℚ₃^× 単数群データ** — 3^ℤ × ℤ₃^× ↪ ℚ₃ の単射準同型（乗法モノイドへ）
    の構造レコード。FullReciprocity の抽象直積代理を実体化した昇格の束ね。 -/
structure Q3UnitsGroupData where
  /-- 埋め込み (k, u) ↦ [3^k·u]。 -/
  embed : (QpUnits 3 isPrime_three).carrier → q3Ring.carrier
  /-- 積保存（prodGrp の積 → ℚ₃ の分数積）。 -/
  embed_hom : ∀ x y, embed ((QpUnits 3 isPrime_three).mul x y)
      = q3Ring.mul (embed x) (embed y)
  /-- 単射（付値分離 × 3 冪正則性）。 -/
  embed_inj : ∀ x y, embed x = embed y → x = y

/-- **A2c-2-6（★）: 実 ℚ₃^× への単射準同型 3^ℤ × ℤ₃^× ↪ ℚ₃**。
    FullReciprocity の `QpUnits 3 isPrime_three` 抽象直積代理を、実 ℚ₃ = ℤ₃[1/3] の
    乗法構造の上へ昇格した実現形（全射性は q3u_image_char が ∃ 形で別掲）。 -/
def q3uData : Q3UnitsGroupData where
  embed := q3uEmbed
  embed_hom := q3u_embed_hom
  embed_inj := q3u_embed_inj

end IUT
