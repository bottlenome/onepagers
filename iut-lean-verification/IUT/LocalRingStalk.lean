/-
  IUT/LocalRingStalk.lean — M296F（柱 A 先行建設: アフィンスキーム
  Spec R の点 P（素イデアル）における**茎 O_{Spec R, P} = R_P** が
  **局所環**であることの本物構成。M293F で骨組みだった「茎の局所性」を完成させる）

  ── 分類 **[実]**（本物の数学的実体の新規建設。M290F の一般乗法系
     局所化 R_S と M289F の素イデアル P を接続し、**S = R∖P** による
     局所化 R_P を本物に建て、その**唯一の極大イデアル m_P**（分子が P
     に入る分数）を実構成し、**「m_P に入らない元＝単元」**という局所環の
     定義そのものを完全証明する。toy 主語なし——主語は M38 `CRing`・
     M289F `primeSpecPrime`・M290F `ringLocRing` という**本物の代数対象**）。

  complete_pct 影響: **柱 A の実スキーム論（構造層 O_X の茎＝局所環）の
  最下層を前進させる**。遠アーベル復元・実 Frobenioid が要求する
  「局所環付き空間 (Spec R, O_Spec)」の茎 O_{Spec R,P} の**代数的実体
  R_P が局所環である**ことを本物で確定する。M289F は位相空間 Spec R まで、
  M290F は一般乗法系 R_S まで、M293F は茎の局所性が骨組みのままだった。
  本ファイルはその局所性を**本物（sorry 皆無・新規 choice 皆無）で閉じる**。
  昇格対象: M293F の骨組み「茎の局所性」→ R_P が局所環であることの完全証明。

  * M296F-1 `locStalkComplement`      — P での乗法系 S = R∖P（1∈S は P の
                                          真イデアル性 `proper`、積閉
                                          a∉P∧b∉P→ab∉P は素性の対偶 `prime_witness`）
  * M296F-2 `locStalkRing`            — 茎 R_P := ringLocRing R (R∖P)（M290F 再利用）
  * M296F-3 `locStalkMaximalMem` / `locStalkMaximal`
                                        — 極大イデアル m_P = {a/s ∈ R_P | a∈P}
                                          （**∃ 代表形**で Quot 上に well-defined。
                                          0∈m_P・加法閉・環倍吸収を完全証明）
  * M296F-4 `locStalkRel_exact`       — Quot.mk 相等 ⟹ 関係（同値関係の
                                          exactness を propext で自作、choice 不使用）
  * M296F-5 `locStalk_max_proper`     — m_P は真イデアル（1∉m_P、素性で完全証明）
  * M296F-6 `locStalk_isLocal`（本丸） — **m_P に入らない元＝単元**
                                          （a/s で a∉P ⟹ a∈S ⟹ 逆元 s/a が存在）
  * M296F-7 `locStalk_proper_no_unit` / `locStalk_maximal_unique`
                                        — 任意の真イデアルは単元を含まない（構成的）／
                                          真イデアルは m_P に含まれる（正直な ¬¬ 形）
  * M296F-8 `locStalkResidueRel` + 同値性 + `locStalkResidue`
                                        — 剰余体 κ(P)=R_P/m_P の**合同関係が同値関係**
                                          （m_P による congruence、剰余集合の骨組み）
  * M296F-9 `LocalRingStalkData` / `locStalk_exists` / `locStalk_stalk_is_local`
                                        — capstone（茎 R_P・m_P・真性・局所性の束ね）
  * M296F-10 体 K の (0) での茎 K_{(0)}: m_(0)={0}・非零元は単元（実例）

  正直な限定（何が本物で何が骨組みか）:
  - **本物（完全証明）**: S=R∖P が乗法系であること、R_P=R_S の可換環性
    （M290F）、m_P が R_P のイデアルであること（0∈m_P・加法閉・環倍吸収）、
    m_P が真イデアル（1∉m_P、素性 prime_witness を本質的に使用）、
    **局所環性の本丸「m_P に入らない元は単元」（a∉P ⟹ a∈S ⟹ 逆 s/a）**、
    「真イデアルは単元を含まない」（構成的）、m_P による合同関係が**同値関係**、
    体 K の茎 K_{(0)} で m_(0)={0}・非零元は単元、これらすべてを完全証明。
  - **正直申告（骨組み/限定）**:
    ・素性・単元性・乗法系所属はすべて **witness / 対偶 witness 形**
      （S.set a := ¬P.mem a、単元は逆元の明示、素性は prime_witness）。
      抽象環上で所属の排中律を使えないため（本規約が証明本体での
      Classical.choice を禁ずる）、これが構成的な本物の内容である。
    ・「唯一の極大イデアル」は **(i) 局所性「m_P に入らない元＝単元」
      (ii)「真イデアルは単元を含まない」** の 2 本で本物に達成する。
      「真イデアル I ⊆ m_P」は所属の排中律を要するため **¬¬(q∈m_P) の
      正直な形**（`locStalk_maximal_unique`）で述べる（q∉m_P なら単元、
      単元は真イデアルに入らない、の対偶。生の q∈m_P は 0 判定の排中律を要す）。
    ・剰余体 κ(P)=R_P/m_P は**合同関係が同値関係であること + 剰余集合
      `locStalkResidue`（Quot）の構成まで**が本物。剰余「環／体」構造
      （加法・乗法の well-defined と体性）は M295F 剰余体と接続する**後続**。
    ・茎を基本開 D(f)（P∈D(f)）上の切断の filtered colimit として構成する
      完全な層論版は**後続**——ここは R_P（P での局所化）が局所環である
      という**茎の代数的実体**を本物で確定する。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 不使用。
-/
import IUT.RingLocalization
import IUT.PrimeSpectrum

namespace IUT

/-! ## M296F-0: 可換環の負号補題（本モジュール内で自作・choice 不使用） -/

/-- 二重否定 −(−a) = a（左簡約で導出）。 -/
theorem locStalk_neg_neg (T : CRing) (a : T.carrier) : T.neg (T.neg a) = a := by
  apply T.add_left_cancel (a := T.neg a)
  have h : T.add (T.neg a) (T.neg (T.neg a)) = T.add (T.neg a) a := by
    rw [cring_add_neg T (T.neg a), T.neg_add a]
  exact h

/-- 和の負号 −(x+y) = (−x)+(−y)（左簡約で導出）。 -/
theorem locStalk_neg_add_dist (T : CRing) (x y : T.carrier) :
    T.neg (T.add x y) = T.add (T.neg x) (T.neg y) := by
  apply T.add_left_cancel (a := T.add x y)
  rw [cring_add_neg T (T.add x y),
    T.add_assoc x y (T.add (T.neg x) (T.neg y)),
    ← T.add_assoc y (T.neg x) (T.neg y),
    T.add_comm y (T.neg x),
    T.add_assoc (T.neg x) y (T.neg y),
    cring_add_neg T y,
    cring_add_zero T (T.neg x),
    cring_add_neg T x]

/-- 差の和 (q−q')+(q'−q'') = q−q''（合同関係の推移律の代数核）。 -/
theorem locStalk_sub_add_sub (T : CRing) (q q' q'' : T.carrier) :
    T.add (T.add q (T.neg q')) (T.add q' (T.neg q''))
      = T.add q (T.neg q'') := by
  rw [T.add_assoc q (T.neg q') (T.add q' (T.neg q'')),
    ← T.add_assoc (T.neg q') q' (T.neg q''),
    T.neg_add q',
    T.zero_add (T.neg q'')]

/-! ## M296F-1: P での乗法系 S = R∖P -/

/-- **M296F-1: 素イデアル P の補集合 S = R∖P は乗法系**。
    1∈S は P の真イデアル性（`proper`: 1∉P）、積閉性 a∉P ∧ b∉P → ab∉P は
    素性の**対偶 witness 形** `prime_witness`。これが局所化 R_P の分母集合。 -/
def locStalkComplement (R : CRing) (P : primeSpecPrime R) : ringLocMulSet R where
  set := fun a => ¬ P.mem a
  one_mem := P.proper
  mul_mem := fun a b ha hb => P.prime_witness a b ha hb

/-- **S = R∖P が乗法系であることの明示**（1∈S は真イデアル性、積閉は素性）。 -/
theorem locStalk_compl_isMulSet (R : CRing) (P : primeSpecPrime R) :
    (locStalkComplement R P).set R.one ∧
      (∀ a b, ¬ P.mem a → ¬ P.mem b → ¬ P.mem (R.mul a b)) :=
  ⟨P.proper, P.prime_witness⟩

/-! ## M296F-2: 茎 R_P = P での局所化 -/

/-- **M296F-2: 茎 O_{Spec R, P} = R_P** — S = R∖P による局所化環
    （M290F `ringLocRing` を再利用）。可換環であることは M290F で完全証明済み。 -/
def locStalkRing (R : CRing) (P : primeSpecPrime R) : CRing :=
  ringLocRing R (locStalkComplement R P)

/-! ## M296F-3: 極大イデアル m_P = {a/s | a∈P} -/

/-- **M296F-3a: m_P への所属**（∃ 代表形で Quot 上に well-defined）
    — 分数 q が「分子が P に入る代表 a/s を持つ」こと。∃ 形なので
    Quot.lift の well-definedness 証明（排中律を要する a∈P↔a'∈P）を
    回避し、剰余類の性質として構成的に定義できる。 -/
def locStalkMaximalMem (R : CRing) (P : primeSpecPrime R)
    (q : (locStalkRing R P).carrier) : Prop :=
  ∃ x : ringLocPre R (locStalkComplement R P),
    q = Quot.mk (ringLocRel (locStalkComplement R P)) x ∧ P.mem x.num

/-- **M296F-3b: m_P は R_P のイデアル** — 0∈m_P（0/1 の分子 0∈P）、
    加法閉（(a u + b s)/(s u) の分子は P の加法閉性で P に入る）、
    環倍吸収（(z a)/(w s) の分子 z·a は P の環倍吸収で P に入る）。 -/
def locStalkMaximal (R : CRing) (P : primeSpecPrime R) :
    primeSpecIdeal (locStalkRing R P) where
  mem := locStalkMaximalMem R P
  zero_mem := ⟨ringLocZero, rfl, P.zero_mem⟩
  add_mem := fun a b ha hb => by
    obtain ⟨x, hx, hxP⟩ := ha
    obtain ⟨y, hy, hyP⟩ := hb
    refine ⟨ringLocAdd x y, ?_, ?_⟩
    · rw [hx, hy]
      rfl
    · show P.mem (R.add (R.mul x.num y.den) (R.mul y.num x.den))
      apply P.add_mem
      · rw [R.mul_comm x.num y.den]
        exact P.smul_mem y.den x.num hxP
      · rw [R.mul_comm y.num x.den]
        exact P.smul_mem x.den y.num hyP
  smul_mem := fun r a ha => by
    obtain ⟨y, hy, hyP⟩ := ha
    rw [hy]
    induction r using Quot.ind with
    | _ z =>
      refine ⟨ringLocMul z y, rfl, ?_⟩
      show P.mem (R.mul z.num y.num)
      exact P.smul_mem z.num y.num hyP

/-! ## M296F-4: Quot の exactness（同値関係なので propext で自作） -/

/-- **M296F-4: exactness** — 局所化関係 `ringLocRel S` は同値関係（M290F で
    反射・対称・推移を完全証明済み）なので、`Quot.mk` の相等から関係を復元できる。
    propext のみ使用（新規 Classical.choice 不使用）。真イデアル性の証明で使用。 -/
theorem locStalkRel_exact {R : CRing} {S : ringLocMulSet R} {a b : ringLocPre R S}
    (h : Quot.mk (ringLocRel S) a = Quot.mk (ringLocRel S) b) : ringLocRel S a b := by
  let f : ringLocCarrier R S → Prop :=
    Quot.lift (fun y => ringLocRel S a y)
      (fun y z hyz => propext
        ⟨fun hay => ringLocRel_trans hay hyz,
         fun haz => ringLocRel_trans haz (ringLocRel_symm hyz)⟩)
  have hf : f (Quot.mk (ringLocRel S) a) = f (Quot.mk (ringLocRel S) b) := congrArg f h
  exact cast hf (ringLocRel_refl a)

/-! ## M296F-5: m_P は真イデアル（1∉m_P） -/

/-- **M296F-5: m_P は真イデアル** — 1∈m_P なら 1 の代表 x/s（x∈P）が
    1/1 と同値、witness t で t·(1·s) = t·(x·1)。x∈P ⟹ t·(x·1)∈P、
    よって t·(1·s) = t·s ∈P。だが t∉P・s∉P ⟹ t·s∉P（素性）で矛盾。 -/
theorem locStalk_max_proper (R : CRing) (P : primeSpecPrime R) :
    ¬ (locStalkMaximal R P).mem (locStalkRing R P).one := by
  intro h
  obtain ⟨x, hx, hxP⟩ := h
  have hrel : ringLocRel (locStalkComplement R P) ringLocOne x :=
    locStalkRel_exact hx
  obtain ⟨t, ht, e⟩ := hrel
  have e' : R.mul t (R.mul R.one x.den) = R.mul t (R.mul x.num R.one) := e
  have hRHS : P.mem (R.mul t (R.mul x.num R.one)) := by
    apply P.smul_mem
    rw [cring_mul_one R x.num]
    exact hxP
  have hmem : P.mem (R.mul t x.den) := by
    have hL : P.mem (R.mul t (R.mul R.one x.den)) := by
      rw [e']; exact hRHS
    rw [R.one_mul x.den] at hL
    exact hL
  exact P.prime_witness t x.den ht x.den_mem hmem

/-! ## M296F-6: 局所環性の本丸（m_P に入らない元＝単元） -/

/-- **M296F-6: 局所環性（本丸）** — R_P の元 q が m_P に入らないなら q は単元。
    q = a/s の代表で q∉m_P ⟹ a∉P（a∈P なら ⟨a/s, rfl, a∈P⟩ で q∈m_P に反する）
    ⟹ a∈S=R∖P。よって逆元 s/a（分母 a∈S）が存在し (a/s)·(s/a)=1。
    これが**「m_P に入らない元は単元」＝局所環の定義**の完全証明。 -/
theorem locStalk_isLocal (R : CRing) (P : primeSpecPrime R) :
    ∀ q : (locStalkRing R P).carrier, ¬ (locStalkMaximal R P).mem q →
      ∃ inv : (locStalkRing R P).carrier,
        (locStalkRing R P).mul q inv = (locStalkRing R P).one := by
  intro q
  induction q using Quot.ind with
  | _ x =>
    intro h
    have hnum : ¬ P.mem x.num := fun hp => h ⟨x, rfl, hp⟩
    refine ⟨Quot.mk (ringLocRel (locStalkComplement R P)) ⟨x.den, x.num, hnum⟩, ?_⟩
    show Quot.mk (ringLocRel (locStalkComplement R P))
        (ringLocMul x ⟨x.den, x.num, hnum⟩)
      = Quot.mk (ringLocRel (locStalkComplement R P)) ringLocOne
    apply Quot.sound
    refine ⟨R.one, (locStalkComplement R P).one_mem, ?_⟩
    show R.mul R.one (R.mul (R.mul x.num x.den) R.one)
      = R.mul R.one (R.mul R.one (R.mul x.den x.num))
    rw [R.one_mul (R.mul (R.mul x.num x.den) R.one),
      cring_mul_one R (R.mul x.num x.den),
      R.one_mul (R.mul R.one (R.mul x.den x.num)),
      R.one_mul (R.mul x.den x.num),
      R.mul_comm x.num x.den]

/-! ## M296F-7: 極大イデアルの一意性（唯一の極大イデアル） -/

/-- **M296F-7a: 真イデアルは単元を含まない**（構成的・完全証明）
    — q∈I が単元なら逆元 inv で inv·q=1∈I、真イデアル性 1∉I に反する。 -/
theorem locStalk_proper_no_unit (R : CRing) (P : primeSpecPrime R)
    (I : primeSpecIdeal (locStalkRing R P))
    (hI : ¬ I.mem (locStalkRing R P).one)
    (q : (locStalkRing R P).carrier) (hq : I.mem q)
    (hu : ∃ inv : (locStalkRing R P).carrier,
      (locStalkRing R P).mul q inv = (locStalkRing R P).one) : False := by
  obtain ⟨inv, hinv⟩ := hu
  apply hI
  have h2 : I.mem ((locStalkRing R P).mul inv q) := I.smul_mem inv q hq
  rw [(locStalkRing R P).mul_comm inv q, hinv] at h2
  exact h2

/-- **M296F-7b: 唯一の極大イデアル（正直な ¬¬ 形）** — 任意の真イデアル I の
    元 q は m_P に含まれる。q∉m_P なら局所性で q は単元、真イデアルは単元を
    含まないので矛盾。生の q∈m_P は 0 判定の排中律を要すため ¬¬ 形で述べる
    （これが局所環「m_P が唯一の極大イデアル」の構成的核）。 -/
theorem locStalk_maximal_unique (R : CRing) (P : primeSpecPrime R)
    (I : primeSpecIdeal (locStalkRing R P))
    (hI : ¬ I.mem (locStalkRing R P).one)
    (q : (locStalkRing R P).carrier) (hq : I.mem q) :
    ¬ ¬ (locStalkMaximal R P).mem q := by
  intro hnot
  exact locStalk_proper_no_unit R P I hI q hq (locStalk_isLocal R P q hnot)

/-! ## M296F-8: 剰余体 κ(P)=R_P/m_P の合同関係（骨組み: 同値関係まで） -/

/-- m_P は負号で閉じる（(−1)·q の環倍吸収）。 -/
theorem locStalk_max_neg_mem (R : CRing) (P : primeSpecPrime R)
    {q : (locStalkRing R P).carrier} (h : (locStalkMaximal R P).mem q) :
    (locStalkMaximal R P).mem ((locStalkRing R P).neg q) := by
  have h2 := (locStalkMaximal R P).smul_mem
    ((locStalkRing R P).neg (locStalkRing R P).one) q h
  rw [cring_neg_mul (locStalkRing R P) (locStalkRing R P).one q,
    (locStalkRing R P).one_mul q] at h2
  exact h2

/-- **M296F-8a: 合同関係 q ≡ q' (mod m_P)** := q − q' ∈ m_P。κ(P)=R_P/m_P の
    同値関係。 -/
def locStalkResidueRel (R : CRing) (P : primeSpecPrime R)
    (q q' : (locStalkRing R P).carrier) : Prop :=
  (locStalkMaximal R P).mem ((locStalkRing R P).add q ((locStalkRing R P).neg q'))

/-- 反射律（q−q = 0 ∈ m_P）。 -/
theorem locStalkResidueRel_refl (R : CRing) (P : primeSpecPrime R)
    (q : (locStalkRing R P).carrier) : locStalkResidueRel R P q q := by
  show (locStalkMaximal R P).mem ((locStalkRing R P).add q ((locStalkRing R P).neg q))
  rw [cring_add_neg (locStalkRing R P) q]
  exact (locStalkMaximal R P).zero_mem

/-- 対称律（q'−q = −(q−q') ∈ m_P、負号閉性）。 -/
theorem locStalkResidueRel_symm (R : CRing) (P : primeSpecPrime R)
    {q q' : (locStalkRing R P).carrier} (h : locStalkResidueRel R P q q') :
    locStalkResidueRel R P q' q := by
  have hn := locStalk_max_neg_mem R P h
  rw [locStalk_neg_add_dist (locStalkRing R P) q ((locStalkRing R P).neg q'),
    locStalk_neg_neg (locStalkRing R P) q',
    (locStalkRing R P).add_comm ((locStalkRing R P).neg q) q'] at hn
  exact hn

/-- 推移律（(q−q')+(q'−q'') = q−q'' ∈ m_P、加法閉性）。 -/
theorem locStalkResidueRel_trans (R : CRing) (P : primeSpecPrime R)
    {q q' q'' : (locStalkRing R P).carrier}
    (h1 : locStalkResidueRel R P q q') (h2 : locStalkResidueRel R P q' q'') :
    locStalkResidueRel R P q q'' := by
  have hs := (locStalkMaximal R P).add_mem _ _ h1 h2
  rw [locStalk_sub_add_sub (locStalkRing R P) q q' q''] at hs
  exact hs

/-- **M296F-8b: 合同関係は同値関係**（剰余体 κ(P) の商の well-defined 前提）。 -/
theorem locStalkResidueRel_equiv (R : CRing) (P : primeSpecPrime R) :
    Equivalence (locStalkResidueRel R P) :=
  ⟨locStalkResidueRel_refl R P,
   fun {_ _} h => locStalkResidueRel_symm R P h,
   fun {_ _ _} h1 h2 => locStalkResidueRel_trans R P h1 h2⟩

/-- **M296F-8c: 剰余集合 κ(P) = R_P / m_P**（合同関係による商集合の骨組み。
    剰余「環／体」構造は M295F 剰余体と接続する後続）。 -/
def locStalkResidue (R : CRing) (P : primeSpecPrime R) : Type :=
  Quot (locStalkResidueRel R P)

/-- κ(P) への標準射影 R_P → κ(P)。 -/
def locStalkResidueMk (R : CRing) (P : primeSpecPrime R)
    (q : (locStalkRing R P).carrier) : locStalkResidue R P :=
  Quot.mk (locStalkResidueRel R P) q

/-! ## M296F-9: capstone -/

/-- **M296F-9a: 局所環茎データ** — 茎 R_P・極大イデアル m_P・真性・局所性
    （m_P に入らない元は単元）の束。 -/
structure LocalRingStalkData (R : CRing) (P : primeSpecPrime R) where
  /-- 茎 R_P。 -/
  ring : CRing
  /-- 極大イデアル m_P。 -/
  maximal : primeSpecIdeal ring
  /-- m_P は真イデアル（1∉m_P）。 -/
  max_proper : ¬ maximal.mem ring.one
  /-- **局所性**: m_P に入らない元は単元。 -/
  is_local : ∀ q : ring.carrier, ¬ maximal.mem q →
    ∃ inv : ring.carrier, ring.mul q inv = ring.one

/-- **M296F-9b: witness**（全フィールドが本モジュールの完全証明）。 -/
def locStalkData_mk (R : CRing) (P : primeSpecPrime R) : LocalRingStalkData R P where
  ring := locStalkRing R P
  maximal := locStalkMaximal R P
  max_proper := locStalk_max_proper R P
  is_local := locStalk_isLocal R P

/-- **見出し定理 (M296F-9c)**: 任意の可換環 R と素イデアル P に対し、茎 R_P は
    局所環である（局所環茎データが存在）。 -/
theorem locStalk_exists (R : CRing) (P : primeSpecPrime R) :
    Nonempty (LocalRingStalkData R P) :=
  ⟨locStalkData_mk R P⟩

/-- **M296F-9d: 茎は局所環**（真性 ∧ 局所性の束ね）。 -/
theorem locStalk_stalk_is_local (R : CRing) (P : primeSpecPrime R) :
    (¬ (locStalkMaximal R P).mem (locStalkRing R P).one) ∧
      (∀ q : (locStalkRing R P).carrier, ¬ (locStalkMaximal R P).mem q →
        ∃ inv : (locStalkRing R P).carrier,
          (locStalkRing R P).mul q inv = (locStalkRing R P).one) :=
  ⟨locStalk_max_proper R P, locStalk_isLocal R P⟩

/-! ## M296F-10: 実例 — 体 K の (0) での茎 K_{(0)} -/

/-- **M296F-10a: 体 K の茎 K_{(0)} の m_(0) は零イデアル** — m_(0) の元は
    R_P の 0 に等しい（分子 a∈(0) ⟹ a=0 ⟹ a/s = 0/1）。局所環の極大
    イデアルが (0) であること＝K_{(0)} ≅ K の骨格。 -/
theorem locStalk_field_max_is_zero (F : IUTField)
    (q : (locStalkRing F.toCRing (primeSpecFieldZeroPrime F)).carrier)
    (h : (locStalkMaximal F.toCRing (primeSpecFieldZeroPrime F)).mem q) :
    q = (locStalkRing F.toCRing (primeSpecFieldZeroPrime F)).zero := by
  obtain ⟨x, hx, hxP⟩ := h
  rw [hx]
  apply Quot.sound
  refine ⟨F.one, (locStalkComplement F.toCRing (primeSpecFieldZeroPrime F)).one_mem, ?_⟩
  show F.toCRing.mul F.one (F.toCRing.mul x.num F.one)
    = F.toCRing.mul F.one (F.toCRing.mul F.toCRing.zero x.den)
  rw [hxP, cring_mul_one F.toCRing F.toCRing.zero,
    cring_zero_mul F.toCRing x.den]

/-- **M296F-10b: 体 K の茎 K_{(0)} は局所環で非零元（m_(0) 外の元）は単元**
    — 一般局所性の体への具体化（K_{(0)} ≅ K の単元性）。 -/
theorem locStalk_field_is_local (F : IUTField) :
    ∀ q : (locStalkRing F.toCRing (primeSpecFieldZeroPrime F)).carrier,
      ¬ (locStalkMaximal F.toCRing (primeSpecFieldZeroPrime F)).mem q →
        ∃ inv : (locStalkRing F.toCRing (primeSpecFieldZeroPrime F)).carrier,
          (locStalkRing F.toCRing (primeSpecFieldZeroPrime F)).mul q inv
            = (locStalkRing F.toCRing (primeSpecFieldZeroPrime F)).one :=
  locStalk_isLocal F.toCRing (primeSpecFieldZeroPrime F)

end IUT
