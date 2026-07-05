/-
  IUT/NilradicalReduced.lean — M298F: 冪零根基・被約環・被約化 R_red = R/nil(R)
                              （柱A: 実スキーム論への本物の先行建設）

  ── 主要成果の分類: **[実]**（本物の可換環 `CRing`（M38）・本物の素イデアル
     `primeSpecPrime`（M289F）・本物の体 `IUTField`（M264F）の上に、
     **本物の冪零根基 nil(R)・本物の被約環・本物の被約化 R_red = R/nil(R)** を
     ゼロから実構成する。toy 主語なし——主語は既存の本物の代数対象 `CRing` そのもの）。

  complete_pct 影響: **柱A の実スキーム論の最下層を前進させる**。M289F で Spec R と
  Zariski 位相の基底までは建ったが、「冪零根基 nil(R)・被約環 R_red・被約化商」は 0
  であった。被約スキーム・整域性・既約成分（Spec R 既約 ⟺ nil(R) 素）はスキーム論の
  基礎であり、本ファイルはその代数的核心を**本物**に建てる。既存 `CRing`（M38）・
  `primeSpecPrime`（M289F）・`rpow`（環の冪）・`binomial2`（M44 二変数二項定理）・
  `rpow_mul_dist`（冪の積分配）・`rsum_const_zero`・CRing 負元ツールキット（M42）を
  土台に、以下を sorry 皆無・新規 choice 皆無で閉じる。

  * M298F-1 `nilRadNilpotent` / `nilRadNilIdeal` — 冪零元と**冪零根基 nil(R) が
    イデアルであること**（0 冪零・和は M44 二項定理で a^m=0,b^n=0 ⟹ (a+b)^{m+n}=0・
    R 倍は rpow_mul_dist で (ra)^n = r^n a^n = 0）。**完全**。
  * M298F-2 `nilRad_prime_pow_not_mem` / `nilRad_sub_prime` — 冪零元は全素イデアルに
    入る（a∉P → a^n∉P を素性 witness で本物に、対偶で nil ⊆ ∩P の片包含）。
  * M298F-3 `nilRadReduced` / `nilRad_field_reduced` — 被約環（冪零元は 0 のみ）と、
    体は被約（a≠0 ⟹ ¬nilpotent、整域性 mul_ne_zero の反復）。
  * M298F-4 `nilRadQuot` / `nilRadProj` / `nilRad_quot_reduced` — **被約化 R_red =
    R/nil(R)**（一般イデアル商環を Quot で実構成し可換環であることを本物に、
    商写像 RingHom、**R_red が被約であること**を本物に）。**完全**。
  * M298F-5 `nilRad_irreducible` — 既約性の骨組み（nil(R) 素 ⟹ R_red が整域＝
    零因子なし、既約成分の代数的核心の一方向を本物で）。
  * M298F-6 capstone `NilradicalData` / `nilRad_exists` / `nilRad_reduced_quotient`
    / `nilRad_field_is_reduced`。

  正直な限定（何が本物で何が未達か）:
  - **本物（完全証明）**:
    ・nil(R) がイデアルであること（0 冪零・和の冪零性を M44 二項定理で完全証明・
      R 倍の冪零性を rpow_mul_dist で完全証明）。
    ・冪零元は全素イデアルに属す方向の構成的核 `a∉P → a^n∉P`（素性 witness の反復）。
    ・被約化 R_red = R/nil(R) が**本物の可換環**であること（一般イデアル商環を Quot で
      実構成、各環公理は代表元の CRing 公理 + congrArg）。
    ・**R_red が被約であること**（[a]^n=0 ⟹ a^n∈nil ⟹ a∈nil ⟹ [a]=0。商での等号
      は Quot.sound で本物に得られる——ここは体の場合と違い 0 判定の排中律を要しない）。
    ・nil(R) 素 ⟹ R_red 整域（零因子なし、witness 形）。
  - **正直申告（未達・非構成的ゆえ対象外）**:
    ・「冪零元 a は素イデアル P に属す a∈P」は構成的には `¬¬(a∈P)` までしか出ない
      （`a∉P → a^n∉P` かつ `a^n=0∈P` の矛盾で `a∉P` は偽、しかし所属 Prop から
      二重否定除去は排中律を要す）。`nilRad_sub_prime` は `¬¬ P.mem a` の honest 形で
      述べる。従って **nil(R) ⊆ ∩P は片包含（二重否定つき）を本物で**、逆包含
      （∩P ⊆ nil = 非冪零元を避ける素イデアルの存在）は **Zorn=Krull で非構成的**
      ゆえ骨組み/後続とする（消去・弱化せず明記）。
    ・**体 K が被約**（nil(K)={0}）は、`a≠0 → ¬nilpotent a` の構成的対偶形で述べる。
      「nilpotent a → a=0」の等号形は 0 判定の排中律を要す（M264F 整域性と同じ限定）。
      一方 R_red の被約性は Quot 上の等号なので排中律不要で完全（上記本物側）。
    ・既約 ⟺ nil 素 の完全同値は骨組み。**一方向「nil 素 ⟹ R_red 整域」を本物で**
      閉じ（既約成分の代数的核心）、位相的 Spec 既約性の完全な包み込みは後続。
    ・素イデアルの**存在**（Krull=Zorn）は仮定しない。既約性補題は「nil が素である」
      という仮説を明示的に取る形で述べる。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
-/
import IUT.PSFunctor
import IUT.LubinTateZp
import IUT.PrimeSpectrum

namespace IUT

/-! ## M298F-0: 冪の補助補題（局所・nilRad 接頭辞で衝突回避） -/

/-- 冪の加法性 a^{k+l} = a^k · a^l（局所版）。 -/
theorem nilRadRpowAdd (R : CRing) (a : R.carrier) (k l : Nat) :
    rpow R a (k + l) = R.mul (rpow R a k) (rpow R a l) := by
  induction l with
  | zero =>
    show rpow R a k = R.mul (rpow R a k) R.one
    rw [CRing.mul_one]
  | succ l ih =>
    show R.mul (rpow R a (k + l)) a = R.mul (rpow R a k) (R.mul (rpow R a l) a)
    rw [ih, R.mul_assoc]

/-- 冪の冪 (a^n)^m = a^{n·m}（局所版）。 -/
theorem nilRadRpowRpow (R : CRing) (a : R.carrier) (n : Nat) :
    ∀ m, rpow R (rpow R a n) m = rpow R a (n * m) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    show R.mul (rpow R (rpow R a n) m) (rpow R a n) = rpow R a (n * (m + 1))
    rw [ih, ← nilRadRpowAdd R a (n * m) n]
    have he : n * (m + 1) = n * m + n := Nat.mul_succ n m
    rw [he]

/-- −0 = 0（局所版）。 -/
theorem nilRadNegZero (R : CRing) : R.neg R.zero = R.zero :=
  CRing.neg_eq_of_add_eq_zero R (R.zero_add R.zero)

/-! ## M298F-1: 冪零元・冪零根基 nil(R) -/

/-- **M298F-1a: 冪零元**（witness 形: 或る n で a^n = 0）。 -/
def nilRadNilpotent (R : CRing) (a : R.carrier) : Prop := ∃ n, rpow R a n = R.zero

/-- **0 は冪零**（0^1 = 0）。 -/
theorem nilRad_zero_nilpotent (R : CRing) : nilRadNilpotent R R.zero := by
  refine ⟨1, ?_⟩
  show R.mul R.one R.zero = R.zero
  exact R.mul_zero R.one

/-- **冪零元の和は冪零**（M44 二変数二項定理による本物の証明）。
    a^m = 0, b^n = 0 ならば (a+b)^{m+n} = 0：二項展開の各項 C(m+n,k)·a^k·b^{m+n−k}
    で、k ≥ m なら a^k = 0、k < m なら m+n−k ≥ n で b^{m+n−k} = 0。 -/
theorem nilRad_add_nilpotent (R : CRing) {a b : R.carrier}
    (ha : nilRadNilpotent R a) (hb : nilRadNilpotent R b) :
    nilRadNilpotent R (R.add a b) := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  refine ⟨m + n, ?_⟩
  rw [binomial2 R a b (m + n)]
  have hterm : ∀ k, k < (m + n) + 1 →
      R.mul (rofNat R (chs (m + n) k))
        (R.mul (rpow R a k) (rpow R b (m + n - k))) = R.zero := by
    intro k _
    have hinner : R.mul (rpow R a k) (rpow R b (m + n - k)) = R.zero := by
      cases Nat.lt_or_ge k m with
      | inr hge =>
        -- k ≥ m ⟹ a^k = a^m · a^{k−m} = 0
        have hak : rpow R a k = R.zero := by
          have hsplit : rpow R a k = R.mul (rpow R a m) (rpow R a (k - m)) := by
            rw [← nilRadRpowAdd R a m (k - m)]
            have he : m + (k - m) = k := by omega
            rw [he]
          rw [hsplit, hm, CRing.zero_mul]
        rw [hak, CRing.zero_mul]
      | inl hlt =>
        -- k < m ⟹ m+n−k ≥ n ⟹ b^{m+n−k} = b^n · b^{m+n−k−n} = 0
        have hbk : rpow R b (m + n - k) = R.zero := by
          have hsplit : rpow R b (m + n - k)
              = R.mul (rpow R b n) (rpow R b (m + n - k - n)) := by
            rw [← nilRadRpowAdd R b n (m + n - k - n)]
            have he : n + (m + n - k - n) = m + n - k := by omega
            rw [he]
          rw [hsplit, hn, CRing.zero_mul]
        rw [hbk, R.mul_zero]
    rw [hinner, R.mul_zero]
  exact (rsum_congr R ((m + n) + 1) hterm).trans (rsum_const_zero R ((m + n) + 1))

/-- **冪零元の R 倍は冪零**（rpow_mul_dist: (r·a)^n = r^n·a^n = 0）。 -/
theorem nilRad_smul_nilpotent (R : CRing) (r : R.carrier) {a : R.carrier}
    (ha : nilRadNilpotent R a) : nilRadNilpotent R (R.mul r a) := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨n, ?_⟩
  rw [rpow_mul_dist R r a n, hn, R.mul_zero]

/-- **M298F-1b: 冪零根基 nil(R)** — 冪零元全体が**本物のイデアル**をなす。 -/
def nilRadNilIdeal (R : CRing) : primeSpecIdeal R where
  mem := nilRadNilpotent R
  zero_mem := nilRad_zero_nilpotent R
  add_mem := fun _ _ hx hy => nilRad_add_nilpotent R hx hy
  smul_mem := fun r _ hx => nilRad_smul_nilpotent R r hx

/-! ## M298F-2: 冪零元は全素イデアルに属す（片包含 nil ⊆ ∩P） -/

/-- **a ∉ P ならば a^{n+1} ∉ P**（素性 witness の反復・完全構成）。 -/
theorem nilRad_prime_pow_not_mem (R : CRing) (P : PrimeSpectrum R) {a : R.carrier}
    (ha : ¬ P.toPrime.mem a) : ∀ n, ¬ P.toPrime.mem (rpow R a (n + 1)) := by
  intro n
  induction n with
  | zero =>
    show ¬ P.toPrime.mem (R.mul R.one a)
    rw [R.one_mul]
    exact ha
  | succ n ih =>
    show ¬ P.toPrime.mem (R.mul (rpow R a (n + 1)) a)
    exact P.toPrime.prime_witness (rpow R a (n + 1)) a ih ha

/-- **M298F-2: 冪零元は任意の素イデアルに属す**（honest 二重否定形）。
    a^n = 0 ∈ P だが a ∉ P なら a^n ∉ P で矛盾。所属 Prop の二重否定除去は
    排中律を要すため `¬¬(a∈P)` が構成的な本物の内容。 -/
theorem nilRad_sub_prime (R : CRing) (P : PrimeSpectrum R) {a : R.carrier}
    (ha : nilRadNilpotent R a) : ¬ ¬ P.toPrime.mem a := by
  intro hna
  obtain ⟨n, hn⟩ := ha
  cases n with
  | zero =>
    -- a^0 = 1 = 0 ⟹ 1 ∈ P、真イデアル性に反する
    apply P.toPrime.proper
    have h1 : R.one = R.zero := hn
    rw [h1]
    exact P.toPrime.zero_mem
  | succ m =>
    have hnp := nilRad_prime_pow_not_mem R P hna m
    apply hnp
    rw [hn]
    exact P.toPrime.zero_mem

/-- **nil(R) ⊆ ∩P の片包含**（二重否定形・honest）。逆包含は Zorn=Krull で非構成的。 -/
theorem nilRad_sub_inter_primes (R : CRing) {a : R.carrier}
    (ha : nilRadNilpotent R a) : ∀ P : PrimeSpectrum R, ¬ ¬ P.toPrime.mem a :=
  fun P => nilRad_sub_prime R P ha

/-! ## M298F-3: 被約環と体の被約性 -/

/-- **M298F-3a: 被約環**（冪零元は 0 のみ = nil(R) = {0}）。 -/
def nilRadReduced (R : CRing) : Prop := ∀ a, nilRadNilpotent R a → a = R.zero

/-- **体では非零元の冪は非零**（整域性 mul_ne_zero の反復）。 -/
theorem nilRad_field_pow_ne_zero (F : IUTField) {a : F.carrier} (ha : a ≠ F.zero) :
    ∀ n, rpow F.toCRing a n ≠ F.zero := by
  intro n
  induction n with
  | zero =>
    show F.one ≠ F.zero
    exact F.one_ne_zero
  | succ n ih =>
    show F.mul (rpow F.toCRing a n) a ≠ F.zero
    exact F.mul_ne_zero ih ha

/-- **M298F-3b: 体は被約**（構成的対偶形: a ≠ 0 ⟹ ¬nilpotent a）。
    等号形「nilpotent → a=0」は 0 判定の排中律を要すため対偶で述べる（M264F と同じ限定）。 -/
theorem nilRad_field_reduced (F : IUTField) {a : F.carrier} (ha : a ≠ F.zero) :
    ¬ nilRadNilpotent F.toCRing a := by
  intro h
  obtain ⟨n, hn⟩ := h
  exact nilRad_field_pow_ne_zero F ha n hn

/-! ## M298F-4: 被約化 R_red = R/nil(R)（一般イデアル商環） -/

/-- **一般イデアル合同 f ≡ g (mod I)** — f − g ∈ I。 -/
def nilRadIdealRel (R : CRing) (I : primeSpecIdeal R) (f g : R.carrier) : Prop :=
  I.mem (R.add f (R.neg g))

/-- イデアルは負元で閉じる（−a = (−1)·a ∈ I）。 -/
theorem nilRad_ideal_neg_mem (R : CRing) (I : primeSpecIdeal R) {a : R.carrier}
    (h : I.mem a) : I.mem (R.neg a) := by
  have h2 := I.smul_mem (R.neg R.one) a h
  rw [CRing.neg_mul, R.one_mul] at h2
  exact h2

/-- 反射律: f − f = 0 ∈ I。 -/
theorem nilRad_ideal_rel_refl (R : CRing) (I : primeSpecIdeal R) (f : R.carrier) :
    nilRadIdealRel R I f f := by
  show I.mem (R.add f (R.neg f))
  rw [CRing.add_neg]
  exact I.zero_mem

/-- 対称律: g − f = −(f − g) ∈ I。 -/
theorem nilRad_ideal_rel_symm (R : CRing) (I : primeSpecIdeal R) {f g : R.carrier}
    (h : nilRadIdealRel R I f g) : nilRadIdealRel R I g f := by
  show I.mem (R.add g (R.neg f))
  have hn := nilRad_ideal_neg_mem R I h
  rw [CRing.neg_add_dist R f (R.neg g), CRing.neg_neg, R.add_comm] at hn
  exact hn

/-- 推移律: (f − g) + (g − k) = f − k ∈ I。 -/
theorem nilRad_ideal_rel_trans (R : CRing) (I : primeSpecIdeal R) {f g k : R.carrier}
    (h1 : nilRadIdealRel R I f g) (h2 : nilRadIdealRel R I g k) :
    nilRadIdealRel R I f k := by
  show I.mem (R.add f (R.neg k))
  have hsum := I.add_mem _ _ h1 h2
  have heq : R.add (R.add f (R.neg g)) (R.add g (R.neg k)) = R.add f (R.neg k) := by
    rw [R.add_assoc f (R.neg g) (R.add g (R.neg k)),
      ← R.add_assoc (R.neg g) g (R.neg k), R.neg_add g, R.zero_add]
  rw [heq] at hsum
  exact hsum

/-- 右加法両立: (a+c) − (b+c) = a − b ∈ I。 -/
theorem nilRad_ideal_rel_add_right (R : CRing) (I : primeSpecIdeal R) (c : R.carrier)
    {a b : R.carrier} (h : nilRadIdealRel R I a b) :
    nilRadIdealRel R I (R.add a c) (R.add b c) := by
  show I.mem (R.add (R.add a c) (R.neg (R.add b c)))
  have heq : R.add (R.add a c) (R.neg (R.add b c)) = R.add a (R.neg b) := by
    rw [CRing.neg_add_dist R b c, CRing.add_add_add_comm R a c (R.neg b) (R.neg c),
      CRing.add_neg R c, CRing.add_zero R (R.add a (R.neg b))]
  rw [heq]
  exact h

/-- 左加法両立（可換性で右に帰着）。 -/
theorem nilRad_ideal_rel_add_left (R : CRing) (I : primeSpecIdeal R) (c : R.carrier)
    {a b : R.carrier} (h : nilRadIdealRel R I a b) :
    nilRadIdealRel R I (R.add c a) (R.add c b) := by
  rw [R.add_comm c a, R.add_comm c b]
  exact nilRad_ideal_rel_add_right R I c h

/-- 右乗法両立: ac − bc = c·(a − b) ∈ I。 -/
theorem nilRad_ideal_rel_mul_right (R : CRing) (I : primeSpecIdeal R) (c : R.carrier)
    {a b : R.carrier} (h : nilRadIdealRel R I a b) :
    nilRadIdealRel R I (R.mul a c) (R.mul b c) := by
  show I.mem (R.add (R.mul a c) (R.neg (R.mul b c)))
  have heq : R.add (R.mul a c) (R.neg (R.mul b c)) = R.mul c (R.add a (R.neg b)) := by
    rw [← CRing.neg_mul R b c, ← R.right_distrib a (R.neg b) c,
      R.mul_comm (R.add a (R.neg b)) c]
  rw [heq]
  exact I.smul_mem c (R.add a (R.neg b)) h

/-- 左乗法両立（可換性で右に帰着）。 -/
theorem nilRad_ideal_rel_mul_left (R : CRing) (I : primeSpecIdeal R) (c : R.carrier)
    {a b : R.carrier} (h : nilRadIdealRel R I a b) :
    nilRadIdealRel R I (R.mul c a) (R.mul c b) := by
  rw [R.mul_comm c a, R.mul_comm c b]
  exact nilRad_ideal_rel_mul_right R I c h

/-- 負元両立: (−a) − (−b) = −(a − b) ∈ I。 -/
theorem nilRad_ideal_rel_neg (R : CRing) (I : primeSpecIdeal R) {a b : R.carrier}
    (h : nilRadIdealRel R I a b) : nilRadIdealRel R I (R.neg a) (R.neg b) := by
  show I.mem (R.add (R.neg a) (R.neg (R.neg b)))
  have hn := nilRad_ideal_neg_mem R I h
  rw [CRing.neg_add_dist R a (R.neg b)] at hn
  exact hn

/-- **M298F-4a: 商の台** R/I。 -/
def nilRadQuotCarrier (R : CRing) (I : primeSpecIdeal R) := Quot (nilRadIdealRel R I)

/-- 商の加法（Quot.lift の二重持ち上げ）。 -/
def nilRadQAdd (R : CRing) (I : primeSpecIdeal R)
    (x y : nilRadQuotCarrier R I) : nilRadQuotCarrier R I :=
  Quot.lift
    (fun f => Quot.lift
      (fun g => Quot.mk (nilRadIdealRel R I) (R.add f g))
      (fun _ _ hg => Quot.sound (nilRad_ideal_rel_add_left R I f hg)) y)
    (fun _ _ hf => by
      induction y using Quot.ind
      rename_i g
      exact Quot.sound (nilRad_ideal_rel_add_right R I g hf)) x

/-- 商の負元。 -/
def nilRadQNeg (R : CRing) (I : primeSpecIdeal R)
    (x : nilRadQuotCarrier R I) : nilRadQuotCarrier R I :=
  Quot.lift
    (fun f => Quot.mk (nilRadIdealRel R I) (R.neg f))
    (fun _ _ hf => Quot.sound (nilRad_ideal_rel_neg R I hf)) x

/-- 商の乗法（Quot.lift の二重持ち上げ）。 -/
def nilRadQMul (R : CRing) (I : primeSpecIdeal R)
    (x y : nilRadQuotCarrier R I) : nilRadQuotCarrier R I :=
  Quot.lift
    (fun f => Quot.lift
      (fun g => Quot.mk (nilRadIdealRel R I) (R.mul f g))
      (fun _ _ hg => Quot.sound (nilRad_ideal_rel_mul_left R I f hg)) y)
    (fun _ _ hf => by
      induction y using Quot.ind
      rename_i g
      exact Quot.sound (nilRad_ideal_rel_mul_right R I g hf)) x

/-- **M298F-4b: 被約化商環 R/I は本物の可換環**（各法則は代表元の CRing 法則 +
    congrArg (Quot.mk)）。 -/
def nilRadQuot (R : CRing) (I : primeSpecIdeal R) : CRing where
  carrier := nilRadQuotCarrier R I
  add := nilRadQAdd R I
  zero := Quot.mk (nilRadIdealRel R I) R.zero
  neg := nilRadQNeg R I
  mul := nilRadQMul R I
  one := Quot.mk (nilRadIdealRel R I) R.one
  add_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    induction z using Quot.ind; rename_i c
    exact congrArg (Quot.mk (nilRadIdealRel R I)) (R.add_assoc a b c)
  zero_add := by
    intro x
    induction x using Quot.ind; rename_i a
    exact congrArg (Quot.mk (nilRadIdealRel R I)) (R.zero_add a)
  neg_add := by
    intro x
    induction x using Quot.ind; rename_i a
    exact congrArg (Quot.mk (nilRadIdealRel R I)) (R.neg_add a)
  add_comm := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    exact congrArg (Quot.mk (nilRadIdealRel R I)) (R.add_comm a b)
  mul_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    induction z using Quot.ind; rename_i c
    exact congrArg (Quot.mk (nilRadIdealRel R I)) (R.mul_assoc a b c)
  one_mul := by
    intro x
    induction x using Quot.ind; rename_i a
    exact congrArg (Quot.mk (nilRadIdealRel R I)) (R.one_mul a)
  mul_comm := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    exact congrArg (Quot.mk (nilRadIdealRel R I)) (R.mul_comm a b)
  left_distrib := by
    intro x y z
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    induction z using Quot.ind; rename_i c
    exact congrArg (Quot.mk (nilRadIdealRel R I)) (R.left_distrib a b c)

/-- **M298F-4c: R/I は本物の可換環**（`nilRadQuot` そのもの、名前付け）。 -/
def nilRad_quot_isCRing (R : CRing) (I : primeSpecIdeal R) : CRing := nilRadQuot R I

/-- **M298F-4d: 商写像 R → R/I は環準同型**。 -/
def nilRadProj (R : CRing) (I : primeSpecIdeal R) : RingHom R (nilRadQuot R I) where
  map := Quot.mk (nilRadIdealRel R I)
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- 商での等号抽出: [a] = [b] ならば a ≡ b (mod I)（rel が同値であることを
    Quot.lift で持ち上げて評価）。propext のみ使用（choice 不使用）。 -/
theorem nilRad_quot_exact (R : CRing) (I : primeSpecIdeal R) {a b : R.carrier}
    (h : Quot.mk (nilRadIdealRel R I) a = Quot.mk (nilRadIdealRel R I) b) :
    nilRadIdealRel R I a b := by
  have hlift : ∀ z z', nilRadIdealRel R I z z' →
      (nilRadIdealRel R I a z) = (nilRadIdealRel R I a z') :=
    fun z z' hzz => propext
      ⟨fun haz => nilRad_ideal_rel_trans R I haz hzz,
       fun haz' => nilRad_ideal_rel_trans R I haz'
         (nilRad_ideal_rel_symm R I hzz)⟩
  have e : nilRadIdealRel R I a a = nilRadIdealRel R I a b :=
    congrArg (Quot.lift (fun z => nilRadIdealRel R I a z) hlift) h
  rw [← e]
  exact nilRad_ideal_rel_refl R I a

/-- 商での冪は代表元の冪: [a]^n = [a^n]。 -/
theorem nilRad_quot_rpow_mk (R : CRing) (I : primeSpecIdeal R) (a : R.carrier) :
    ∀ n, rpow (nilRadQuot R I) (Quot.mk (nilRadIdealRel R I) a) n
      = Quot.mk (nilRadIdealRel R I) (rpow R a n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    calc rpow (nilRadQuot R I) (Quot.mk (nilRadIdealRel R I) a) (n + 1)
        = (nilRadQuot R I).mul
            (rpow (nilRadQuot R I) (Quot.mk (nilRadIdealRel R I) a) n)
            (Quot.mk (nilRadIdealRel R I) a) := rfl
      _ = (nilRadQuot R I).mul (Quot.mk (nilRadIdealRel R I) (rpow R a n))
            (Quot.mk (nilRadIdealRel R I) a) := by rw [ih]
      _ = Quot.mk (nilRadIdealRel R I) (R.mul (rpow R a n) a) := rfl

/-- **M298F-4e: 被約化 R_red = R/nil(R) は被約**（本物・排中律不要）。
    [a]^n = 0 ⟹ [a^n] = 0 ⟹ a^n ∈ nil ⟹ (a^n)^m = a^{nm} = 0 ⟹ a ∈ nil ⟹ [a] = 0。
    商での等号 [a]=0 は Quot.sound で得られるので、体の場合と違い 0 判定を要さない。 -/
theorem nilRad_quot_reduced (R : CRing) :
    nilRadReduced (nilRadQuot R (nilRadNilIdeal R)) := by
  intro x
  induction x using Quot.ind
  rename_i a
  intro hx
  obtain ⟨n, hn⟩ := hx
  rw [nilRad_quot_rpow_mk R (nilRadNilIdeal R) a n] at hn
  have hrel := nilRad_quot_exact R (nilRadNilIdeal R) hn
  have hmem : (nilRadNilIdeal R).mem (rpow R a n) := by
    have hthis : (nilRadNilIdeal R).mem (R.add (rpow R a n) (R.neg R.zero)) := hrel
    rw [nilRadNegZero, R.add_zero] at hthis
    exact hthis
  obtain ⟨m, hm⟩ := hmem
  have hzero : rpow R a (n * m) = R.zero := by
    rw [← nilRadRpowRpow R a n m]
    exact hm
  show Quot.mk (nilRadIdealRel R (nilRadNilIdeal R)) a
    = Quot.mk (nilRadIdealRel R (nilRadNilIdeal R)) R.zero
  apply Quot.sound
  show (nilRadNilIdeal R).mem (R.add a (R.neg R.zero))
  rw [nilRadNegZero, R.add_zero]
  exact ⟨n * m, hzero⟩

/-! ## M298F-5: 既約性の骨組み（nil 素 ⟹ R_red 整域） -/

/-- **M298F-5: nil(R) が素イデアルならば R_red = R/nil(R) は整域**（零因子なし・
    witness 形）。既約成分の代数的核心「Spec R 既約 ⟺ nil 素 ⟺ R_red 整域」の
    一方向。位相的 Spec 既約性の完全な包み込みは後続。 -/
theorem nilRad_irreducible (R : CRing)
    (hprime : ∀ a b, ¬ (nilRadNilIdeal R).mem a → ¬ (nilRadNilIdeal R).mem b →
        ¬ (nilRadNilIdeal R).mem (R.mul a b)) :
    ∀ x y : (nilRadQuot R (nilRadNilIdeal R)).carrier,
      x ≠ (nilRadQuot R (nilRadNilIdeal R)).zero →
      y ≠ (nilRadQuot R (nilRadNilIdeal R)).zero →
      (nilRadQuot R (nilRadNilIdeal R)).mul x y
        ≠ (nilRadQuot R (nilRadNilIdeal R)).zero := by
  intro x y
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  intro hx hy hxy
  have hmemab : (nilRadNilIdeal R).mem (R.mul a b) := by
    have h0 : Quot.mk (nilRadIdealRel R (nilRadNilIdeal R)) (R.mul a b)
        = Quot.mk (nilRadIdealRel R (nilRadNilIdeal R)) R.zero := hxy
    have hrel := nilRad_quot_exact R (nilRadNilIdeal R) h0
    have hthis : (nilRadNilIdeal R).mem (R.add (R.mul a b) (R.neg R.zero)) := hrel
    rw [nilRadNegZero, R.add_zero] at hthis
    exact hthis
  have hna : ¬ (nilRadNilIdeal R).mem a := by
    intro hna
    apply hx
    show Quot.mk (nilRadIdealRel R (nilRadNilIdeal R)) a
      = Quot.mk (nilRadIdealRel R (nilRadNilIdeal R)) R.zero
    apply Quot.sound
    show (nilRadNilIdeal R).mem (R.add a (R.neg R.zero))
    rw [nilRadNegZero, R.add_zero]
    exact hna
  have hnb : ¬ (nilRadNilIdeal R).mem b := by
    intro hnb
    apply hy
    show Quot.mk (nilRadIdealRel R (nilRadNilIdeal R)) b
      = Quot.mk (nilRadIdealRel R (nilRadNilIdeal R)) R.zero
    apply Quot.sound
    show (nilRadNilIdeal R).mem (R.add b (R.neg R.zero))
    rw [nilRadNegZero, R.add_zero]
    exact hnb
  exact hprime a b hna hnb hmemab

/-! ## M298F-6: capstone -/

/-- **M298F-6a: 被約化データ**（環 R・冪零根基 nil(R)・被約化 R_red・商写像・
    R_red の被約性を束ねる本物のレコード）。 -/
structure NilradicalData (R : CRing) where
  /-- 冪零根基 nil(R)（本物のイデアル）。 -/
  nilIdeal : primeSpecIdeal R
  /-- 被約化 R_red = R/nil(R)（本物の可換環）。 -/
  redRing : CRing
  /-- 商写像 R → R_red（本物の環準同型）。 -/
  proj : RingHom R redRing
  /-- R_red が被約であること（本物）。 -/
  reduced : nilRadReduced redRing

/-- **M298F-6b: 被約化データの構成**。 -/
def nilRadData (R : CRing) : NilradicalData R where
  nilIdeal := nilRadNilIdeal R
  redRing := nilRadQuot R (nilRadNilIdeal R)
  proj := nilRadProj R (nilRadNilIdeal R)
  reduced := nilRad_quot_reduced R

/-- **M298F-6c: 任意の可換環に被約化が存在する**（本物の構成）。 -/
theorem nilRad_exists (R : CRing) : Nonempty (NilradicalData R) := ⟨nilRadData R⟩

/-- **M298F-6d: 被約化 R_red は被約**（本物）。 -/
theorem nilRad_reduced_quotient (R : CRing) :
    nilRadReduced (nilRadQuot R (nilRadNilIdeal R)) := nilRad_quot_reduced R

/-- **M298F-6e: 体は被約**（構成的対偶形・実例）。 -/
theorem nilRad_field_is_reduced (F : IUTField) {a : F.carrier}
    (ha : a ≠ F.zero) : ¬ nilRadNilpotent F.toCRing a :=
  nilRad_field_reduced F ha

end IUT
