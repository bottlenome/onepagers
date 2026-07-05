/-
  IUT/ResidueField.lean — M295F: 極大イデアルと剰余体 R/m
                          （柱A: 実スキーム論／mono-anabelian の本物の先行建設）

  ── 主要成果の分類: **[実]**（本物の可換環 `CRing`（M38）と本物の体 `IUTField`
     （M264F）の上に、本物の極大イデアル・本物の剰余環 R/m・**本物の剰余体
     （m 極大 ⟹ R/m は体）**・本物の商写像（環準同型・全射・核 = m）を
     ゼロから実構成する。toy 主語なし——主語は既存 M38 `CRing`／M264F
     `IUTField`／M289F `primeSpecIdeal`・`primeSpecPrime` という**本物の
     代数対象**そのもの）。

  complete_pct 影響: **柱A の実スキーム論／mono-anabelian の最下層を前進させる**。
  遠アーベル幾何・π₁^ét 復元は「基礎スキーム Spec R の閉点における剰余体
  κ(x) = R/m_x」を局所的な入力に要求する（閉点の剰余体とその Galois 群こそ
  mono-anabelian 復元の局所素材）。M289F で Spec R（位相空間）と素イデアルまで
  建てたが、**極大イデアル・剰余環 R/m・剰余体の体性**という構造層側の最下層は
  0 であった。本ファイルはそれを**本物**に建てる:
  極大イデアル `resFieldMaximal`（witness 形の極大性）、剰余環 R/m
  `resFieldQuot`（イデアル合同 a−b∈m による Quot 商・可換環）、**剰余体の本丸
  `resField_quot_isField`（m 極大 ⟹ 非零元 [a]（a∉m）が可逆、逆元を極大性の
  witness r,s（r·a+s=1, s∈m）から構成）**、商写像 `resFieldProj`（環準同型・
  全射・核 = m `resFieldProj_ker`）、**極大 ⟹ 素 `resFieldMaximalPrime`**（R/m
  整域の核 = m 素、極大性の witness から本物に）、**極大 ⟹ 閉点
  `resField_maximal_closed`**（m を真に含む素イデアルは R しかない = 閉性の
  本物の核）を sorry 皆無・新規 choice 皆無で閉じる。体 K の (0) が極大で
  K/(0) ≅ K（商写像が単射）であることも本物に確定する。

  * M295F-1 `resField_mul4comm` / `resField_add_right_cancel`
            / `resField_neg_mem` / `resField_neg_zero`
                              — CRing の可換/加法群ツールキット（本物）
  * M295F-2 `resFieldMaximal` — 極大イデアル（真イデアル + 極大性の witness 形
                                x∉m → ∃ r s, s∈m ∧ r·x+s=1、排中律回避）
  * M295F-3 `resFieldRel` + 合同律 — a≡b (mod m) ⟺ a−b∈m の合同関係
                                （refl/symm/trans/加法・乗法両立・負元両立、本物）
  * M295F-4 `resFieldQuot`    — 剰余環 R/m（Quot 商・可換環、法則は代表の法則）
  * M295F-5 `resFieldProj`    — 商写像 R → R/m（環準同型・全射・核 = m）
  * M295F-6 `resField_quot_isField` — **本丸: m 極大 ⟹ R/m は体**（非零元可逆、
                                逆元を極大性 witness から構成、choice 不使用）
  * M295F-7 `resFieldMaximalPrime` — **極大 ⟹ 素**（witness 展開で本物）
  * M295F-8 `resField_maximal_closed` — **極大 ⟹ 閉点**（m⊊Q（素）⟹ Q=R、本物）
  * M295F-9 `ResidueFieldData` / `resField_of_maximal` / `resField_exists`
            / `resFieldFieldZeroMaximal` / `resField_field_zero`
            / `resField_field_zero_injective` — capstone + 実例（体の (0)）

  正直な限定（何が本物で何が未達か）:
  - **本物（完全証明）**: CRing 加法群ツールキット、極大イデアルの合同関係が
    可換環合同をなすこと（refl/symm/trans/加法・乗法・負元両立）、剰余環 R/m が
    可換環であること、商写像が全射環準同型で核 = m であること、**剰余体の本丸
    `resField_quot_isField`（m 極大 ⟹ 非零元 [a] が可逆）**、**極大 ⟹ 素
    `resFieldMaximalPrime`**、**極大 ⟹ 閉点 `resField_maximal_closed`（m を真に
    含む素イデアルは単位イデアルのみ）**、そして「体 K の (0) は極大で商写像
    R → R/(0) が単射（K ≅ K/(0)）」は完全証明（sorry 皆無・新規 choice 皆無）。
  - **正直申告（未達）**:
    ・極大性は選言形（「m⊊I なら I=R」を所属判定つき）ではなく**構成的 witness 形**
      `x∉m → ∃ r s, s∈m ∧ r·x+s=1` で述べる（抽象環上で「m を真に含む」を所属の
      排中律なしに扱うため。witness 形が構成的な極大イデアル内容であり、選言形は
      古典論理でのみ従う）。素性も M289F と同じ対偶 witness 形。
    ・**剰余体は「非零元は可逆」の witness 形**で述べる（`∀ x ≠ 0, ∃ y, x·y = 1`）。
      全域の逆元関数 `inv : R/m → R/m` として `IUTField` 構造を載せるには非零類
      ごとに逆元代表を選ぶ必要があり選択公理を要するため（choice 回避のため）
      本モジュールでは witness 形に留める。これは M264F 整域性・M114 単純拡大の
      体性と同じ正直な限定であり、witness 形が構成的な体の内容である。
    ・**極大イデアルの存在（Krull=Zorn）は非構成的なので仮定しない**。極大
      イデアル m を入力に剰余体を作る。体の (0) は本物で極大なので実例は本物。
    ・**閉点 ↔ 極大の完全な両方向（V(m)={m} の単射的一意性）は骨組み**。極大 ⟹ 閉
      （m を真に含む素イデアルは R のみ）は本物、逆（閉 ⟹ 極大）と点の集合等号は
      所属の完全 ↔ を要し排中律ゆえ対象外。
    ・整数環 ℤ の極大イデアル (p) からの剰余体 F_p は Bézout（gcd 互除）を要する
      ため本モジュールでは扱わず、体の (0) を実例とする（後続）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
-/
import IUT.PrimeSpectrum
import IUT.PowerSeries
import IUT.LubinTateZp

namespace IUT

/-! ## M295F-1: CRing の可換／加法群ツールキット -/

/-- **M295F-1a: 4 因子の入れ替え** (a·b)·(c·d) = (a·c)·(b·d)（結合・可換から）。 -/
theorem resField_mul4comm (R : CRing) (a b c d : R.carrier) :
    R.mul (R.mul a b) (R.mul c d) = R.mul (R.mul a c) (R.mul b d) := by
  rw [R.mul_assoc a b (R.mul c d), ← R.mul_assoc b c d, R.mul_comm b c,
    R.mul_assoc c b d, ← R.mul_assoc a c (R.mul b d)]

/-- **M295F-1b: 加法の右簡約** a+c = b+c ⟹ a = b。 -/
theorem resField_add_right_cancel (R : CRing) {a b c : R.carrier}
    (h : R.add a c = R.add b c) : a = b := by
  apply CRing.add_left_cancel R (a := c)
  rw [R.add_comm c a, R.add_comm c b]
  exact h

/-- **M295F-1c: イデアルは負元で閉じる** — x ∈ I ⟹ (−x) ∈ I
    （(−1)·x = −x を環倍吸収に流す）。 -/
theorem resField_neg_mem {R : CRing} (I : primeSpecIdeal R) {x : R.carrier}
    (hx : I.mem x) : I.mem (R.neg x) := by
  have h := I.smul_mem (R.neg R.one) x hx
  rw [CRing.neg_mul R R.one x, R.one_mul] at h
  exact h

/-- **M295F-1d: −0 = 0**。 -/
theorem resField_neg_zero (R : CRing) : R.neg R.zero = R.zero := by
  have h := CRing.add_neg R R.zero
  rw [R.zero_add (R.neg R.zero)] at h
  exact h

/-! ## M295F-2: 極大イデアル -/

/-- **M295F-2: 極大イデアル** — 真イデアル（1 ∉ m）で、**極大性の witness 形**
    `x ∉ m → ∃ r s, s ∈ m ∧ r·x + s = 1` を満たすもの。すなわち m に属さない
    元 x を足すと単位イデアルを生成する（m + (x) = R）。選言形「m ⊊ I なら
    I = R」は抽象環上で排中律を要するため、構成的に等価内容を持つ witness 形で
    述べる（M289F 素イデアルの対偶 witness と同じ設計）。 -/
structure resFieldMaximal (R : CRing) extends primeSpecIdeal R where
  /-- 真イデアル: 1 ∉ m。 -/
  proper : ¬ mem R.one
  /-- 極大性（witness 形）: x ∉ m なら r·x + s = 1（s ∈ m）が取れる。 -/
  maximal_witness : ∀ x, ¬ mem x → ∃ r s, mem s ∧ R.add (R.mul r x) s = R.one

/-! ## M295F-3: イデアル合同 a ≡ b (mod I) -/

/-- **M295F-3a: イデアル合同** — a ≡ b (mod I) ⟺ a − b ∈ I。 -/
def resFieldRel {R : CRing} (I : primeSpecIdeal R) (a b : R.carrier) : Prop :=
  I.mem (R.add a (R.neg b))

/-- 反射律: a − a = 0 ∈ I。 -/
theorem resFieldRel_refl {R : CRing} (I : primeSpecIdeal R) (a : R.carrier) :
    resFieldRel I a a := by
  show I.mem (R.add a (R.neg a))
  rw [CRing.add_neg R a]
  exact I.zero_mem

/-- 対称律: b − a = −(a − b) ∈ I。 -/
theorem resFieldRel_symm {R : CRing} (I : primeSpecIdeal R) {a b : R.carrier}
    (h : resFieldRel I a b) : resFieldRel I b a := by
  show I.mem (R.add b (R.neg a))
  have hn := resField_neg_mem I h
  rw [CRing.neg_add_dist R a (R.neg b), CRing.neg_neg R b, R.add_comm (R.neg a) b] at hn
  exact hn

/-- 推移律: a − c = (a − b) + (b − c) ∈ I。 -/
theorem resFieldRel_trans {R : CRing} (I : primeSpecIdeal R) {a b c : R.carrier}
    (h1 : resFieldRel I a b) (h2 : resFieldRel I b c) : resFieldRel I a c := by
  show I.mem (R.add a (R.neg c))
  have hsum := I.add_mem (R.add a (R.neg b)) (R.add b (R.neg c)) h1 h2
  have key : R.add (R.add a (R.neg b)) (R.add b (R.neg c)) = R.add a (R.neg c) := by
    rw [R.add_assoc a (R.neg b) (R.add b (R.neg c)),
      ← R.add_assoc (R.neg b) b (R.neg c), R.neg_add b, R.zero_add]
  rw [key] at hsum
  exact hsum

/-- 右加法両立: (a+c) − (b+c) = a − b。 -/
theorem resFieldRel_add_right {R : CRing} (I : primeSpecIdeal R) (c : R.carrier)
    {a b : R.carrier} (h : resFieldRel I a b) :
    resFieldRel I (R.add a c) (R.add b c) := by
  show I.mem (R.add (R.add a c) (R.neg (R.add b c)))
  have key : R.add (R.add a c) (R.neg (R.add b c)) = R.add a (R.neg b) := by
    rw [CRing.neg_add_dist R b c, CRing.add_add_add_comm R a c (R.neg b) (R.neg c),
      CRing.add_neg R c, CRing.add_zero R (R.add a (R.neg b))]
  rw [key]
  exact h

/-- 左加法両立（可換性で右に帰着）。 -/
theorem resFieldRel_add_left {R : CRing} (I : primeSpecIdeal R) (c : R.carrier)
    {a b : R.carrier} (h : resFieldRel I a b) :
    resFieldRel I (R.add c a) (R.add c b) := by
  rw [R.add_comm c a, R.add_comm c b]
  exact resFieldRel_add_right I c h

/-- 右乗法両立: a·c − b·c = (a − b)·c ∈ I（環倍吸収）。 -/
theorem resFieldRel_mul_right {R : CRing} (I : primeSpecIdeal R) (c : R.carrier)
    {a b : R.carrier} (h : resFieldRel I a b) :
    resFieldRel I (R.mul a c) (R.mul b c) := by
  show I.mem (R.add (R.mul a c) (R.neg (R.mul b c)))
  have key : R.add (R.mul a c) (R.neg (R.mul b c)) = R.mul (R.add a (R.neg b)) c := by
    rw [CRing.right_distrib R a (R.neg b) c, CRing.neg_mul R b c]
  rw [key, R.mul_comm (R.add a (R.neg b)) c]
  exact I.smul_mem c (R.add a (R.neg b)) h

/-- 左乗法両立（可換性で右に帰着）。 -/
theorem resFieldRel_mul_left {R : CRing} (I : primeSpecIdeal R) (c : R.carrier)
    {a b : R.carrier} (h : resFieldRel I a b) :
    resFieldRel I (R.mul c a) (R.mul c b) := by
  rw [R.mul_comm c a, R.mul_comm c b]
  exact resFieldRel_mul_right I c h

/-- 負元両立: (−a) − (−b) = −(a − b) ∈ I。 -/
theorem resFieldRel_neg {R : CRing} (I : primeSpecIdeal R) {a b : R.carrier}
    (h : resFieldRel I a b) : resFieldRel I (R.neg a) (R.neg b) := by
  show I.mem (R.add (R.neg a) (R.neg (R.neg b)))
  have key : R.add (R.neg a) (R.neg (R.neg b)) = R.neg (R.add a (R.neg b)) := by
    rw [CRing.neg_add_dist R a (R.neg b)]
  rw [key]
  exact resField_neg_mem I h

/-! ## M295F-4: 剰余環 R/m -/

/-- **M295F-4a: 剰余環の台** R/I = Quot (a ≡ b mod I)。 -/
def resFieldQuotCarrier {R : CRing} (I : primeSpecIdeal R) := Quot (resFieldRel I)

/-- **M295F-4b: 剰余環の加法**（Quot.lift の二重持ち上げ、両立は加法両立律）。 -/
def resFieldQuotAdd {R : CRing} (I : primeSpecIdeal R)
    (x y : resFieldQuotCarrier I) : resFieldQuotCarrier I :=
  Quot.lift
    (fun f => Quot.lift
      (fun g => Quot.mk (resFieldRel I) (R.add f g))
      (fun _ _ hg => Quot.sound (resFieldRel_add_left I f hg)) y)
    (fun _ _ hf => by
      induction y using Quot.ind
      rename_i g
      exact Quot.sound (resFieldRel_add_right I g hf)) x

/-- **M295F-4c: 剰余環の負元**。 -/
def resFieldQuotNeg {R : CRing} (I : primeSpecIdeal R)
    (x : resFieldQuotCarrier I) : resFieldQuotCarrier I :=
  Quot.lift (fun f => Quot.mk (resFieldRel I) (R.neg f))
    (fun _ _ hf => Quot.sound (resFieldRel_neg I hf)) x

/-- **M295F-4d: 剰余環の乗法**（Quot.lift の二重持ち上げ、両立は乗法両立律）。 -/
def resFieldQuotMul {R : CRing} (I : primeSpecIdeal R)
    (x y : resFieldQuotCarrier I) : resFieldQuotCarrier I :=
  Quot.lift
    (fun f => Quot.lift
      (fun g => Quot.mk (resFieldRel I) (R.mul f g))
      (fun _ _ hg => Quot.sound (resFieldRel_mul_left I f hg)) y)
    (fun _ _ hf => by
      induction y using Quot.ind
      rename_i g
      exact Quot.sound (resFieldRel_mul_right I g hf)) x

/-- **M295F-4e: 剰余環 R/I は可換環**（各法則は代表元の R 法則 + congrArg）。 -/
def resFieldQuot {R : CRing} (I : primeSpecIdeal R) : CRing where
  carrier := resFieldQuotCarrier I
  add := resFieldQuotAdd I
  zero := Quot.mk (resFieldRel I) R.zero
  neg := resFieldQuotNeg I
  mul := resFieldQuotMul I
  one := Quot.mk (resFieldRel I) R.one
  add_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    induction z using Quot.ind; rename_i k
    exact congrArg (Quot.mk (resFieldRel I)) (R.add_assoc f g k)
  zero_add := by
    intro x
    induction x using Quot.ind; rename_i f
    exact congrArg (Quot.mk (resFieldRel I)) (R.zero_add f)
  neg_add := by
    intro x
    induction x using Quot.ind; rename_i f
    exact congrArg (Quot.mk (resFieldRel I)) (R.neg_add f)
  add_comm := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    exact congrArg (Quot.mk (resFieldRel I)) (R.add_comm f g)
  mul_assoc := by
    intro x y z
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    induction z using Quot.ind; rename_i k
    exact congrArg (Quot.mk (resFieldRel I)) (R.mul_assoc f g k)
  one_mul := by
    intro x
    induction x using Quot.ind; rename_i f
    exact congrArg (Quot.mk (resFieldRel I)) (R.one_mul f)
  mul_comm := by
    intro x y
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    exact congrArg (Quot.mk (resFieldRel I)) (R.mul_comm f g)
  left_distrib := by
    intro x y z
    induction x using Quot.ind; rename_i f
    induction y using Quot.ind; rename_i g
    induction z using Quot.ind; rename_i k
    exact congrArg (Quot.mk (resFieldRel I)) (R.left_distrib f g k)

/-- **M295F-4f: 剰余環は可換環**（`resFieldQuot` の CRing 性を明示束ね）。 -/
theorem resField_quot_isCRing {R : CRing} (I : primeSpecIdeal R) :
    Nonempty CRing := ⟨resFieldQuot I⟩

/-- **M295F-4g: 分離性** — mk a = mk b なら a ≡ b (mod I)
    （Prop への Quot.lift、`quot_exact_ideal` の一般化）。 -/
theorem resFieldQuot_exact {R : CRing} (I : primeSpecIdeal R) {a b : R.carrier}
    (h : Quot.mk (resFieldRel I) a = Quot.mk (resFieldRel I) b) :
    resFieldRel I a b := by
  have hf : Quot.lift (resFieldRel I a)
      (fun x y hxy => propext
        ⟨fun hax => resFieldRel_trans I hax hxy,
         fun hay => resFieldRel_trans I hay (resFieldRel_symm I hxy)⟩)
      (Quot.mk (resFieldRel I) a) := resFieldRel_refl I a
  rw [h] at hf
  exact hf

/-! ## M295F-5: 商写像 R → R/m -/

/-- **M295F-5a: 商写像 π : R → R/I**（環準同型、成分は Quot.mk）。 -/
def resFieldProj {R : CRing} (I : primeSpecIdeal R) : RingHom R (resFieldQuot I) where
  map := fun a => Quot.mk (resFieldRel I) a
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- **M295F-5b: 商写像は全射**。 -/
theorem resFieldProj_surjective {R : CRing} (I : primeSpecIdeal R) :
    ∀ x, ∃ a, (resFieldProj I).map a = x := by
  intro x
  induction x using Quot.ind
  rename_i a
  exact ⟨a, rfl⟩

/-- **M295F-5c: 商写像の核はちょうど m** — π(a) = 0 ⟺ a ∈ m。 -/
theorem resFieldProj_ker {R : CRing} (m : resFieldMaximal R) (a : R.carrier) :
    (resFieldProj m.toprimeSpecIdeal).map a
        = (resFieldQuot m.toprimeSpecIdeal).zero ↔ m.mem a := by
  refine ⟨?_, ?_⟩
  · intro h
    have h' : Quot.mk (resFieldRel m.toprimeSpecIdeal) a
        = Quot.mk (resFieldRel m.toprimeSpecIdeal) R.zero := h
    have hr : m.toprimeSpecIdeal.mem (R.add a (R.neg R.zero)) :=
      resFieldQuot_exact m.toprimeSpecIdeal h'
    have e : R.add a (R.neg R.zero) = a := by
      rw [resField_neg_zero R, CRing.add_zero R a]
    rw [e] at hr
    exact hr
  · intro h
    show Quot.mk (resFieldRel m.toprimeSpecIdeal) a
       = Quot.mk (resFieldRel m.toprimeSpecIdeal) R.zero
    apply Quot.sound
    show m.toprimeSpecIdeal.mem (R.add a (R.neg R.zero))
    rw [resField_neg_zero R, CRing.add_zero R a]
    exact h

/-! ## M295F-6: 剰余体（本丸）— m 極大 ⟹ R/m は体 -/

/-- **M295F-6: 剰余体の本丸** — m が極大なら剰余環 R/m の非零元 [a]（a ∉ m）は
    可逆。逆元は極大性の witness r, s（r·a + s = 1, s ∈ m）から [r] として構成する:
    a·r ≡ 1 (mod m)（a·r − 1 = −s ∈ m）。全域逆元関数（`IUTField` 構造）は非零類
    ごとの選択を要し choice を使うため、**「非零元は可逆」の witness 形**で述べる
    （M264F/M114 と同じ正直な限定、構成的な体の内容）。 -/
theorem resField_quot_isField {R : CRing} (m : resFieldMaximal R) :
    ∀ x : (resFieldQuot m.toprimeSpecIdeal).carrier,
      x ≠ (resFieldQuot m.toprimeSpecIdeal).zero →
      ∃ y, (resFieldQuot m.toprimeSpecIdeal).mul x y
             = (resFieldQuot m.toprimeSpecIdeal).one := by
  intro x
  induction x using Quot.ind
  rename_i a
  intro hx
  have ha : ¬ m.mem a := by
    intro hmem
    apply hx
    show Quot.mk (resFieldRel m.toprimeSpecIdeal) a
       = Quot.mk (resFieldRel m.toprimeSpecIdeal) R.zero
    apply Quot.sound
    show m.toprimeSpecIdeal.mem (R.add a (R.neg R.zero))
    rw [resField_neg_zero R, CRing.add_zero R a]
    exact hmem
  obtain ⟨r, s, hs, hrs⟩ := m.maximal_witness a ha
  refine ⟨Quot.mk (resFieldRel m.toprimeSpecIdeal) r, ?_⟩
  show Quot.mk (resFieldRel m.toprimeSpecIdeal) (R.mul a r)
     = Quot.mk (resFieldRel m.toprimeSpecIdeal) R.one
  apply Quot.sound
  show m.toprimeSpecIdeal.mem (R.add (R.mul a r) (R.neg R.one))
  have hrs' : R.add (R.mul a r) s = R.one := by
    rw [R.mul_comm a r]
    exact hrs
  have hmar : R.mul a r = R.add R.one (R.neg s) := by
    apply resField_add_right_cancel R (c := s)
    rw [R.add_assoc R.one (R.neg s) s, R.neg_add s, CRing.add_zero R R.one]
    exact hrs'
  have key2 : R.add (R.add R.one (R.neg s)) (R.neg R.one) = R.neg s := by
    rw [R.add_comm R.one (R.neg s), R.add_assoc (R.neg s) R.one (R.neg R.one),
      CRing.add_neg R R.one, CRing.add_zero R (R.neg s)]
  rw [hmar, key2]
  exact resField_neg_mem m.toprimeSpecIdeal hs

/-! ## M295F-7: 極大 ⟹ 素 -/

/-- **M295F-7: 極大イデアルは素イデアル** — R/m が体 ⟹ 整域 ⟹ m 素。構成的に:
    a ∉ m, b ∉ m から極大 witness (r,s),(r',s') を取り、
    1 = (r·a+s)(r'·b+s') = (r·r')(a·b) + [s,s' を含む m の元] を展開する。
    a·b ∈ m と仮定すると (r·r')(a·b) ∈ m、右辺全体が m に落ち 1 ∈ m で
    真イデアル性 proper に反する。ゆえ a·b ∉ m（対偶 witness 形の素条件）。 -/
def resFieldMaximalPrime {R : CRing} (m : resFieldMaximal R) : primeSpecPrime R where
  toprimeSpecIdeal := m.toprimeSpecIdeal
  proper := m.proper
  prime_witness := by
    intro a b ha hb hab
    obtain ⟨r, s, hs, hrs⟩ := m.maximal_witness a ha
    obtain ⟨r', s', hs', hrs'⟩ := m.maximal_witness b hb
    apply m.proper
    have hone : R.mul (R.add (R.mul r a) s) (R.add (R.mul r' b) s') = R.one := by
      rw [hrs, hrs', R.one_mul]
    rw [← hone]
    have hexp : R.mul (R.add (R.mul r a) s) (R.add (R.mul r' b) s')
        = R.add (R.add (R.mul (R.mul r a) (R.mul r' b)) (R.mul s (R.mul r' b)))
                (R.mul (R.add (R.mul r a) s) s') := by
      rw [R.left_distrib (R.add (R.mul r a) s) (R.mul r' b) s',
        CRing.right_distrib R (R.mul r a) s (R.mul r' b)]
    rw [hexp]
    refine m.add_mem _ _ (m.add_mem _ _ ?_ ?_) ?_
    · rw [resField_mul4comm R r a r' b]
      exact m.smul_mem (R.mul r r') (R.mul a b) hab
    · rw [R.mul_comm s (R.mul r' b)]
      exact m.smul_mem (R.mul r' b) s hs
    · exact m.smul_mem (R.add (R.mul r a) s) s' hs'

/-! ## M295F-8: 極大 ⟹ 閉点 -/

/-- **M295F-8: 極大 ⟹ 閉点の本物の核** — 極大イデアル m を（イデアルとして）真に
    含む素イデアル Q は単位イデアルしかない。すなわち Q ⊇ m で x ∈ Q かつ x ∉ m
    なる x があれば Q は非真（1 ∈ Q）。極大性の witness r·x + s = 1（s ∈ m ⊆ Q,
    r·x ∈ Q）から 1 ∈ Q が出て Q.proper に反する。これが「Spec R で極大イデアルの
    点は閉（V(m) は m を真に含む素点を持たない）」の構成的核。
    **限定**: V(m)={m} の点集合等号（両方向）は所属の完全 ↔ を要し排中律ゆえ骨組み。 -/
theorem resField_maximal_closed {R : CRing} (m : resFieldMaximal R)
    (Q : primeSpecPrime R) (hmQ : ∀ x, m.mem x → Q.mem x)
    {x : R.carrier} (hxQ : Q.mem x) (hxm : ¬ m.mem x) : False := by
  obtain ⟨r, s, hs, hrs⟩ := m.maximal_witness x hxm
  apply Q.proper
  rw [← hrs]
  exact Q.add_mem _ _ (Q.smul_mem r x hxQ) (hmQ s hs)

/-! ## M295F-9: capstone + 実例（体の (0)） -/

/-- **M295F-9a: 剰余体データ** — 極大イデアル m と、その剰余環 R/m・全射商写像・
    核 = m・**剰余体性（非零元可逆）**・**極大 ⟹ 素**を束ねる。 -/
structure ResidueFieldData (R : CRing) where
  /-- 極大イデアル m。 -/
  ideal : resFieldMaximal R
  /-- m は素イデアル（極大 ⟹ 素）。 -/
  isPrime : primeSpecPrime R
  /-- 商写像 π : R → R/m。 -/
  proj : RingHom R (resFieldQuot ideal.toprimeSpecIdeal)
  /-- π は全射。 -/
  proj_surjective : ∀ x, ∃ a, proj.map a = x
  /-- **R/m は体**（非零元は可逆、witness 形）。 -/
  isField : ∀ x : (resFieldQuot ideal.toprimeSpecIdeal).carrier,
    x ≠ (resFieldQuot ideal.toprimeSpecIdeal).zero →
    ∃ y, (resFieldQuot ideal.toprimeSpecIdeal).mul x y
       = (resFieldQuot ideal.toprimeSpecIdeal).one
  /-- 核 = m。 -/
  ker_eq : ∀ a, proj.map a = (resFieldQuot ideal.toprimeSpecIdeal).zero ↔ ideal.mem a

/-- **M295F-9b: 極大イデアルから剰余体データを構成**。 -/
def resField_of_maximal {R : CRing} (m : resFieldMaximal R) : ResidueFieldData R where
  ideal := m
  isPrime := resFieldMaximalPrime m
  proj := resFieldProj m.toprimeSpecIdeal
  proj_surjective := resFieldProj_surjective m.toprimeSpecIdeal
  isField := resField_quot_isField m
  ker_eq := resFieldProj_ker m

/-- **M295F-9c: 体 F の零イデアル (0) は極大** — 真イデアル性は 1 ≠ 0、極大性は
    x ∉ (0)（= x ≠ 0）に対し r := x⁻¹, s := 0 で x⁻¹·x + 0 = 1（逆元公理）。
    体では (0) が本物の極大イデアルである。 -/
def resFieldFieldZeroMaximal (F : IUTField) : resFieldMaximal F.toCRing where
  mem := fun x => x = F.zero
  zero_mem := rfl
  add_mem := fun x y hx hy => by
    show F.toCRing.add x y = F.zero
    rw [hx, hy, F.toCRing.zero_add]
  smul_mem := fun r x hx => by
    show F.toCRing.mul r x = F.zero
    rw [hx, F.toCRing.mul_zero r]
  proper := F.one_ne_zero
  maximal_witness := fun x hx => by
    refine ⟨F.inv x, F.zero, rfl, ?_⟩
    rw [F.inv_mul_cancel hx, CRing.add_zero F.toCRing F.one]

/-- **M295F-9d: 体 K の剰余体 K/(0)**（（0）が極大なので剰余体データが本物に存在）。 -/
def resField_field_zero (F : IUTField) : ResidueFieldData F.toCRing :=
  resField_of_maximal (resFieldFieldZeroMaximal F)

/-- **M295F-9e: K/(0) ≅ K（商写像の単射性）** — 零イデアルの合同は a − b = 0、
    すなわち a = b。商写像 R → R/(0) は単射（全射は M295F-5b）ゆえ K ≅ K/(0)。 -/
theorem resField_field_zero_injective (F : IUTField) :
    ∀ a b, (resFieldProj (resFieldFieldZeroMaximal F).toprimeSpecIdeal).map a
         = (resFieldProj (resFieldFieldZeroMaximal F).toprimeSpecIdeal).map b →
      a = b := by
  intro a b h
  have h' : Quot.mk (resFieldRel (resFieldFieldZeroMaximal F).toprimeSpecIdeal) a
      = Quot.mk (resFieldRel (resFieldFieldZeroMaximal F).toprimeSpecIdeal) b := h
  have hr := resFieldQuot_exact (resFieldFieldZeroMaximal F).toprimeSpecIdeal h'
  exact CRing.eq_of_sub_eq_zero F.toCRing hr

/-- **M295F-9f: 剰余体データの存在**（体 F の (0) から本物の剰余体データが存在）。
    極大イデアルの一般存在（Krull=Zorn）は非構成的なので仮定しないが、体では
    (0) が本物の極大イデアルとして存在する。 -/
theorem resField_exists (F : IUTField) : Nonempty (ResidueFieldData F.toCRing) :=
  ⟨resField_field_zero F⟩

end IUT
