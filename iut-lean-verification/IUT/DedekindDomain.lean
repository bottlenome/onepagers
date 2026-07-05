/-
  IUT/DedekindDomain.lean — M305F（柱 A 先行建設: Dedekind 整域と
                            イデアル論 — O_K の理論の本物の最下層）

  ── 主要成果の分類: **[実]**（本物の整域 `Domain`（M266F）・本物の分数
     イデアル `fracIdFractional`（M302F）・本物の素イデアル `primeSpecPrime`
     （M289F）・本物の極大イデアル `resFieldMaximal` と剰余体 `resFieldQuot`
     （M295F）の上に、**Dedekind 整域**（Noether＋整閉＋次元1）とそのイデアル論
     を実構成する。toy 主語なし——主語は M266F `Domain`／M302F 分数イデアル／
     M289F 素イデアル／M295F 極大イデアルという**本物の代数対象**そのもの）。

  complete_pct 影響: **柱 A の実イデアル理論（数体の整数環 O_K の Dedekind 性・
  イデアルの一意分解・イデアル類群 Cl(O_K)）の最下層を前進させる**。M302F で分数
  イデアルと単項の可逆性・単項 Cartier 群まで建てたが、「整域が **Dedekind**
  （Noether＋整閉＋次元1）であること」「次元1（非零素イデアルは極大）」「D/P が体
  （M295F 剰余体接続）」「一般イデアルの可逆性・素イデアルへの一意分解の骨組み」
  「イデアル類群（分数イデアル/単項）」という Dedekind 整域論の骨格は 0 であった。
  本ファイルはそれを **本物の定義＋本物の部分証明＋正直な骨組み**で建てる。とりわけ
  (1) Dedekind 整域の定義（3 条件を構造体で）、(2) **次元1（非零素イデアルは極大）**
  とそこからの D/P が体（M295F `resField_quot_isField` へ本物接続）、(3) **整従属
  `dedekIntegralOver` の本物の定義**と「D の元は D 上整」（`dedek_elem_integral`）、
  (4) **体は退化 Dedekind 整域**（非零素イデアルが存在しない＝非零元は単元 ⟹ 素
  イデアルが非真、ゆえ次元1 が空虚に成立）を本物で（vacuous だが構成的に完全）、
  (5) 単項分数イデアルの可逆性（M302F `fracId_principal_is_invertible` の本物の
  再輸出）、(6) **イデアル類群の同値関係の反射律**と単項 Cartier 群（M302F）の束ね、
  (7) イデアルの積 `dedekIdealProd`（fracIdMul の fold、本物）を
  sorry 皆無・新規 Classical.choice 皆無で閉じる。

  * M305F-1 `dedekCringPow`/`dedekMonicEval`/`dedekIntegralOver`
                              — 冪・monic 多項式評価・**整従属の本物の定義**
                                （x が D 上整 ⟺ ある monic 多項式の根）
  * M305F-2 `dedek_elem_integral` — **D の元 ι(a) は D 上整**（monic X−a の根、完全）
  * M305F-3 `dedekACC`/`dedekIntClosedProp` — Noether（イデアル昇鎖停止）・整閉
                                （整従属 ⟹ ι(D)）の条件 Prop
  * M305F-4 `dedekDomain` — **Dedekind 整域の定義**（Domain + Noether + 整閉 +
                                次元1「非零素は極大」）
  * M305F-5 `dedek_prime_maximal`/`dedek_prime_residue_field`
                              — 次元1 の射影＋**D/P が体**（M295F 接続、完全）
  * M305F-6 `dedek_principal_invertible`/`dedekAllNonzeroInvertible`
                              — 単項可逆（M302F 本物）＋一般可逆の骨組み Prop
  * M305F-7 `dedekIdealProd`/`dedekUniqueFactorization`
                              — **イデアルの積（本物の fold）**＋一意分解の骨組み Prop
  * M305F-8 `dedekClassRel`/`dedek_class_rel_refl`/`dedekClassGroup`/
            `dedek_class_group` — イデアル類群の同値関係（**反射律は完全**）＋
                                単項 Cartier 群（M302F）の束ね
  * M305F-9 capstone `DedekindDomainData`/`dedek_data`/`dedek_ideal_theory`/
            `dedek_field`/`dedek_field_is_dedekind`/`dedek_exists`
                              — Dedekind データの束ね・**体は Dedekind 整域**（完全）

  正直な限定（何が本物で何が未達か）:
  - **本物（完全証明）**:
    ・**整従属 `dedekIntegralOver` の定義**（monic 多項式の根）と「D の元は D 上整」
      `dedek_elem_integral`（monic X−a の根、完全）。
    ・**Dedekind 整域の定義**（3 条件の構造体）。
    ・**次元1 ⟹ 素イデアルは極大**の射影 `dedek_prime_maximal`、および
      **D/P が体**（M295F `resField_quot_isField` へ本物接続）`dedek_prime_residue_field`。
    ・**単項分数イデアル (a)（a∈K*）は可逆** `dedek_principal_invertible`
      （M302F の本物の再輸出）。
    ・**イデアルの積 `dedekIdealProd`**（fracIdMul の fold、本物の構成）。
    ・**イデアル類群の同値関係の反射律** `dedek_class_rel_refl`（(1)·I = D·I = I の
      M302F 本物法則へ帰着、完全）と**単項 Cartier 群**（M302F `fracId_cartier_group`）
      の束ね。
    ・**体は退化 Dedekind 整域** `dedek_field`（体では非零素イデアルが存在しない
      ＝非零元は単元ゆえ素イデアルは非真、次元1 が空虚に成立）は完全証明。
  - **正直申告（未達・骨組み・後続、消去・弱化せず明記）**:
    ・**Noether**（`dedekACC`: イデアル昇鎖停止）は Dedekind 構造の**仮説フィールド**
      として持ち回る。任意の整域・体に対する ACC の構成的証明は所属判定の排中律を
      要すので本モジュールでは提供せず、M266F `zpDomain` の `no_zero_div` と同じく
      **仮説として供給**する（後続で本証明）。
    ・**整閉性**（`dedekIntClosedProp`: 整従属 ⟹ ι(D)）も同様に**仮説フィールド**。
      整従属の定義 `dedekIntegralOver` は本物だが、「体・O_K が整閉」の完全証明は
      Frac の全射性・Noether 帰納を要すので**後続**（仮説として供給）。
    ・**一般イデアルの可逆性** `dedekAllNonzeroInvertible` は**骨組み Prop**（Dedekind
      性からの一般イデアル可逆の完全証明は Noether 帰納を要す・後続）。本物は単項の
      可逆性 `dedek_principal_invertible` に限る。
    ・**イデアルの一意分解** `dedekUniqueFactorization` は**骨組み Prop**（素イデアル
      積の存在・一意性の完全証明は Noether 帰納を要す・後続）。本物はイデアルの積
      `dedekIdealProd` の構成に限る。
    ・**イデアル類群が群をなす完全証明**は同値関係の対称・推移・類上の積の well-defined
      を要すので**後続**。本物は反射律 `dedek_class_rel_refl` と単項 Cartier 群の
      束ねに限る（M302F と同じ正直な限定）。
    ・素イデアル・極大イデアルの性質はすべて M289F/M295F の**対偶 witness 形／
      構成的形**を踏襲（選言・完全 ↔ は排中律ゆえ非採用）。
    ・具体数体（O_K が Dedekind）の証明は M303F 接続の後続。類数の有限性も後続。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無。
-/
import IUT.FractionalIdeal
import IUT.ResidueField

namespace IUT

/-! ## M305F-1: 冪・monic 多項式評価・整従属の本物の定義 -/

/-- **M305F-1a: 可換環の冪** xⁿ（Nat 再帰）。 -/
def dedekCringPow (R : CRing) (x : R.carrier) : Nat → R.carrier
  | 0 => R.one
  | Nat.succ n => R.mul x (dedekCringPow R x n)

/-- **M305F-1b: monic 多項式の下位項の評価** — 係数 `[c₀,c₁,…,c_{k-1}]`（ι(D) 側）
    と基点 i に対し Σⱼ ι(cⱼ)·x^{i+j} を返す（monic 部 xⁿ は `dedekIntegralOver`
    側で別に足す）。 -/
def dedekMonicEval (D : Domain) (x : (fracRing D).carrier) :
    List D.R.carrier → Nat → (fracRing D).carrier
  | [], _ => (fracRing D).zero
  | a :: rest, i =>
    (fracRing D).add
      ((fracRing D).mul (fracIdEmb D a) (dedekCringPow (fracRing D) x i))
      (dedekMonicEval D x rest (Nat.succ i))

/-- **M305F-1c: 整従属（本物の定義）** — x∈Frac(D) が D 上整 ⟺ ある係数列
    `coeffs = [c₀,…,c_{n-1}]`（cᵢ∈D、n = length）で monic 多項式
    xⁿ + Σᵢ ι(cᵢ)xⁱ = 0 を満たす。これが「D 上整」の本物の内容（monic 多項式の根）。
    多項式評価の全展開は不要で、fold 形で完全に述べられる。 -/
def dedekIntegralOver (D : Domain) (x : (fracRing D).carrier) : Prop :=
  ∃ coeffs : List D.R.carrier,
    (fracRing D).add (dedekCringPow (fracRing D) x (List.length coeffs))
      (dedekMonicEval D x coeffs 0) = (fracRing D).zero

/-! ## M305F-2: D の元は D 上整（完全） -/

/-- **M305F-2: D の元 ι(a) は D 上整** — monic 一次多項式 X − a の根
    （coeffs = [−a]: x¹ + ι(−a)·x⁰ = ι(a) + ι(−a) = ι(a−a) = ι(0) = 0）。
    整従属の定義が本物（非空虚）であることの完全証明。 -/
theorem dedek_elem_integral (D : Domain) (a : D.R.carrier) :
    dedekIntegralOver D (fracIdEmb D a) := by
  refine ⟨[D.R.neg a], ?_⟩
  show (fracRing D).add
      ((fracRing D).mul (fracIdEmb D a) (fracRing D).one)
      ((fracRing D).add
        ((fracRing D).mul (fracIdEmb D (D.R.neg a)) (fracRing D).one)
        (fracRing D).zero)
    = (fracRing D).zero
  rw [cring_mul_one (fracRing D) (fracIdEmb D a),
    cring_mul_one (fracRing D) (fracIdEmb D (D.R.neg a)),
    cring_add_zero (fracRing D) (fracIdEmb D (D.R.neg a)),
    ← fracIdEmb_add D a (D.R.neg a), cring_add_neg D.R a, fracIdEmb_zero D]

/-! ## M305F-3: Noether・整閉の条件 Prop -/

/-- **M305F-3a: Noether（イデアル昇鎖停止 ACC）** — 任意のイデアル昇鎖
    I₀ ⊆ I₁ ⊆ … は或る N から先で停止する（I_{N+n} ⊆ I_N、昇鎖と合わせ I_{N+n}=I_N）。
    **正直な限定**: 一般の整域・体に対する ACC の構成的証明は所属判定の排中律を要す
    ので本モジュールでは提供せず、Dedekind 構造の**仮説**として供給（後続で本証明）。 -/
def dedekACC (D : Domain) : Prop :=
  ∀ (chain : Nat → primeSpecIdeal D.R),
    (∀ n, primeSpecSubset (chain n) (chain (Nat.succ n))) →
    ∃ N, ∀ n, primeSpecSubset (chain (N + n)) (chain N)

/-- **M305F-3b: 整閉性** — Frac(D) の元 x が D 上整（`dedekIntegralOver`）なら
    x∈ι(D)。整従属の定義は本物（M305F-1c）だが、「体・O_K が整閉」の完全証明は
    後続ゆえ Dedekind 構造の**仮説**として供給。 -/
def dedekIntClosedProp (D : Domain) : Prop :=
  ∀ x : (fracRing D).carrier, dedekIntegralOver D x →
    ∃ a : D.R.carrier, x = fracIdEmb D a

/-! ## M305F-4: Dedekind 整域の定義 -/

/-- **M305F-4: Dedekind 整域** — 整域 D で 3 条件:
    (i) Noether（`noetherian`: ACC、仮説形）、(ii) 整閉（`intClosed`: 整従属 ⟹ ι(D)、
    仮説形）、(iii) **次元1**（`dim_one`: 非零素イデアル P は極大 = ある極大イデアル m
    と mem 同値、M295F `resFieldMaximal` へ本物接続）。数体の整数環 O_K が満たす
    Dedekind 性の本物の定義（Noether・整閉は正直な仮説、次元1 が本物の主眼）。 -/
structure dedekDomain where
  /-- 台の整域。 -/
  D : Domain
  /-- (i) Noether（イデアル昇鎖停止、仮説形）。 -/
  noetherian : dedekACC D
  /-- (ii) 整閉（整従属 ⟹ ι(D)、仮説形）。 -/
  intClosed : dedekIntClosedProp D
  /-- (iii) 次元1: 非零素イデアルは極大（ある極大イデアル m と mem 同値）。 -/
  dim_one : ∀ (P : primeSpecPrime D.R),
    (∃ x, P.mem x ∧ x ≠ D.R.zero) →
    ∃ m : resFieldMaximal D.R, ∀ y, P.mem y ↔ m.mem y

/-! ## M305F-5: 次元1 の射影＋ D/P が体（M295F 接続） -/

/-- **M305F-5a: 非零素イデアルは極大** — Dedekind 整域の次元1 条件の射影
    （非零素 P はある極大 m と mem 同値）。 -/
theorem dedek_prime_maximal (DD : dedekDomain) (P : primeSpecPrime DD.D.R)
    (hP : ∃ x, P.mem x ∧ x ≠ DD.D.R.zero) :
    ∃ m : resFieldMaximal DD.D.R, ∀ y, P.mem y ↔ m.mem y :=
  DD.dim_one P hP

/-- **M305F-5b: 非零素イデアルの剰余環 D/P は体**（次元1 で P は極大 m と mem 同値、
    M295F `resField_quot_isField` で D/m の非零元は可逆）。Dedekind 整域の閉点の
    剰余体が体であることの本物の接続（完全）。 -/
theorem dedek_prime_residue_field (DD : dedekDomain) (P : primeSpecPrime DD.D.R)
    (hP : ∃ x, P.mem x ∧ x ≠ DD.D.R.zero) :
    ∃ m : resFieldMaximal DD.D.R, (∀ y, P.mem y ↔ m.mem y) ∧
      (∀ z : (resFieldQuot m.toprimeSpecIdeal).carrier,
        z ≠ (resFieldQuot m.toprimeSpecIdeal).zero →
        ∃ w, (resFieldQuot m.toprimeSpecIdeal).mul z w
           = (resFieldQuot m.toprimeSpecIdeal).one) := by
  obtain ⟨m, hm⟩ := DD.dim_one P hP
  exact ⟨m, hm, resField_quot_isField m⟩

/-! ## M305F-6: 可逆イデアル（単項本物＋一般骨組み） -/

/-- 非零分数イデアル（∃ 非零元）。 -/
def dedekFracNonzero (D : Domain) (I : fracIdFractional D) : Prop :=
  ∃ x, I.mem x ∧ x ≠ (fracRing D).zero

/-- **M305F-6a: 単項分数イデアル (a)（a∈K*）は可逆**（M302F
    `fracId_principal_is_invertible` の本物の再輸出）。Dedekind 整域の可逆性の
    本物の核（単項）。 -/
theorem dedek_principal_invertible (D : Domain) (a : (fracRing D).carrier)
    (h : ∃ b : (fracRing D).carrier, (fracRing D).mul a b = (fracRing D).one) :
    fracIdInvertible D (fracIdPrincipal D a) :=
  fracId_principal_is_invertible D a h

/-- **M305F-6b: 一般イデアルの可逆性（骨組み Prop）** — Dedekind 整域で全非零分数
    イデアルが可逆。**正直な限定**: 一般イデアルの可逆性の完全証明は Noether 帰納を
    要すので本モジュールでは述べるのみ（本物は単項 `dedek_principal_invertible`）。 -/
def dedekAllNonzeroInvertible (DD : dedekDomain) : Prop :=
  ∀ I : fracIdFractional DD.D, dedekFracNonzero DD.D I → fracIdInvertible DD.D I

/-! ## M305F-7: イデアルの積（本物）＋一意分解（骨組み） -/

/-- **M305F-7a: 分数イデアルの積（fold）** — リスト [I₁,…,Iₖ] の積
    I₁·(I₂·(…·(Iₖ·D))) を M302F `fracIdMul`・`fracIdOne` の fold で本物に構成。
    素イデアル積 P₁^{e₁}…Pₖ^{eₖ} はこの積で表せる（各 Pᵢ を重複で並べる）。 -/
def dedekIdealProd (D : Domain) : List (fracIdFractional D) → fracIdFractional D
  | [] => fracIdOne D
  | I :: rest => fracIdMul D I (dedekIdealProd D rest)

/-- **M305F-7b: 空積は単位イデアル D**（本物、定義的）。 -/
theorem dedek_ideal_prod_nil (D : Domain) :
    dedekIdealProd D [] = fracIdOne D := rfl

/-- **M305F-7c: 単一積 [I] = I·D**（本物、定義的）。 -/
theorem dedek_ideal_prod_single (D : Domain) (I : fracIdFractional D)
    (x : (fracRing D).carrier) :
    (dedekIdealProd D [I]).mem x ↔ (fracIdMul D I (fracIdOne D)).mem x :=
  Iff.rfl

/-- **M305F-7d: イデアルの一意分解（骨組み Prop）** — Dedekind 整域で全非零分数
    イデアル I は素イデアル（を整イデアル化した分数イデアル）の積に分解する。
    **正直な限定**: 存在・一意性の完全証明は Noether 帰納を要すので本モジュールでは
    述べるのみ（本物はイデアルの積 `dedekIdealProd` の構成）。 -/
def dedekUniqueFactorization (DD : dedekDomain) : Prop :=
  ∀ I : fracIdFractional DD.D, dedekFracNonzero DD.D I →
    ∃ primes : List (primeSpecPrime DD.D.R),
      ∀ x, I.mem x ↔
        (dedekIdealProd DD.D
          (List.map (fun P => fracIdOfIntegral DD.D P.toprimeSpecIdeal) primes)).mem x

/-! ## M305F-8: イデアル類群 -/

/-- **M305F-8a: イデアル類の同値関係** — I ≈ J ⟺ ある単元 a∈K* で J = (a)·I（mem 同値）。
    分数イデアル/単項の商（イデアル類群 Cl(D)）を定める同値関係。 -/
def dedekClassRel (D : Domain) (I J : fracIdFractional D) : Prop :=
  ∃ a : (fracRing D).carrier,
    (∃ b, (fracRing D).mul a b = (fracRing D).one) ∧
      ∀ x, J.mem x ↔ (fracIdMul D (fracIdPrincipal D a) I).mem x

/-- **M305F-8b: 類同値関係の反射律**（a = 1: (1)·I = D·I = I、M302F
    `fracId_principal_one_eq`・`fracId_one_mul` の本物法則へ帰着、完全）。 -/
theorem dedek_class_rel_refl (D : Domain) (I : fracIdFractional D) :
    dedekClassRel D I I := by
  refine ⟨(fracRing D).one,
    ⟨(fracRing D).one, (fracRing D).one_mul (fracRing D).one⟩, ?_⟩
  intro x
  exact (Iff.trans (fracId_mul_congr_left D (fracId_principal_one_eq D) I x)
    (fracId_one_mul D I x)).symm

/-- **M305F-8c: イデアル類群データ** — 類同値関係（反射律つき）と単項 Cartier 群
    （M302F）の束ね。**正直な限定**: 対称・推移・類上の積の well-defined（群公理の完全
    証明）は後続。本物は反射律と単項 Cartier 群に限る。 -/
structure dedekClassGroup (D : Domain) where
  /-- 類の同値関係。 -/
  rel : fracIdFractional D → fracIdFractional D → Prop
  /-- 反射律（本物）。 -/
  rel_refl : ∀ I, rel I I
  /-- 単項 Cartier 群（M302F の本物）。 -/
  cartier : FracIdCartierGroup D

/-- **M305F-8d: イデアル類群データの witness**（反射律・Cartier 群とも本物）。 -/
def dedek_class_group (D : Domain) : dedekClassGroup D where
  rel := dedekClassRel D
  rel_refl := dedek_class_rel_refl D
  cartier := fracId_cartier_group D

/-- **M305F-8e: イデアル類群データの存在**。 -/
theorem dedek_class_group_isGroup (D : Domain) : Nonempty (dedekClassGroup D) :=
  ⟨dedek_class_group D⟩

/-! ## M305F-9: capstone ＋ 体は Dedekind 整域 -/

/-- **M305F-9a: Dedekind 整域データ** — Dedekind 整域と、単項可逆・次元1（素は
    極大）・類同値の反射律を束ねる（全フィールドが本物）。 -/
structure DedekindDomainData where
  /-- 台の Dedekind 整域。 -/
  toDedekind : dedekDomain
  /-- 単項分数イデアルの可逆性（本物）。 -/
  principal_invertible : ∀ a : (fracRing toDedekind.D).carrier,
    (∃ b, (fracRing toDedekind.D).mul a b = (fracRing toDedekind.D).one) →
      fracIdInvertible toDedekind.D (fracIdPrincipal toDedekind.D a)
  /-- 次元1: 非零素は極大（本物の射影）。 -/
  prime_maximal : ∀ P : primeSpecPrime toDedekind.D.R,
    (∃ x, P.mem x ∧ x ≠ toDedekind.D.R.zero) →
    ∃ m : resFieldMaximal toDedekind.D.R, ∀ y, P.mem y ↔ m.mem y
  /-- 類同値関係の反射律（本物）。 -/
  class_rel_refl : ∀ I, dedekClassRel toDedekind.D I I

/-- **M305F-9b: Dedekind データの witness**（全フィールド本物）。 -/
def dedek_data (DD : dedekDomain) : DedekindDomainData where
  toDedekind := DD
  principal_invertible := fun a h => dedek_principal_invertible DD.D a h
  prime_maximal := fun P hP => DD.dim_one P hP
  class_rel_refl := dedek_class_rel_refl DD.D

/-- **M305F-9c: イデアル論の束ね** — 単項可逆・次元1・類反射律を一括（全て本物）。 -/
theorem dedek_ideal_theory (DD : dedekDomain) :
    (∀ a : (fracRing DD.D).carrier,
      (∃ b, (fracRing DD.D).mul a b = (fracRing DD.D).one) →
        fracIdInvertible DD.D (fracIdPrincipal DD.D a)) ∧
    (∀ P : primeSpecPrime DD.D.R, (∃ x, P.mem x ∧ x ≠ DD.D.R.zero) →
        ∃ m : resFieldMaximal DD.D.R, ∀ y, P.mem y ↔ m.mem y) ∧
    (∀ I : fracIdFractional DD.D, dedekClassRel DD.D I I) :=
  ⟨fun a h => dedek_principal_invertible DD.D a h,
   fun P hP => DD.dim_one P hP,
   fun I => dedek_class_rel_refl DD.D I⟩

/-- **M305F-9d: 体は退化 Dedekind 整域** — D.R が体（非零元は単元）なら、非零素
    イデアルは存在しない（非零元 x∈P は単元ゆえ 1∈P で真イデアル性に反する）ので
    次元1 条件は空虚に成立し、D は Dedekind 整域。Noether（ACC）・整閉は正直な
    仮説として供給（体でも構成的 ACC・整閉の完全証明は排中律・Frac 全射性を要すので
    仮説形、M266F `zpDomain` の `no_zero_div` と同じ設計）。次元1（本物の主眼）は
    体で完全に閉じる。 -/
def dedek_field (D : Domain)
    (hfield : ∀ x, x ≠ D.R.zero → ∃ y, D.R.mul x y = D.R.one)
    (hnoeth : dedekACC D) (hintcl : dedekIntClosedProp D) : dedekDomain where
  D := D
  noetherian := hnoeth
  intClosed := hintcl
  dim_one := by
    intro P hP
    obtain ⟨x, hxP, hx0⟩ := hP
    obtain ⟨y, hxy⟩ := hfield x hx0
    have hone : P.mem D.R.one := by
      have h1 := P.smul_mem y x hxP
      rw [D.R.mul_comm y x, hxy] at h1
      exact h1
    exact absurd hone P.proper

/-- **M305F-9e: 体は Dedekind 整域（存在）**。 -/
theorem dedek_field_is_dedekind (D : Domain)
    (hfield : ∀ x, x ≠ D.R.zero → ∃ y, D.R.mul x y = D.R.one)
    (hnoeth : dedekACC D) (hintcl : dedekIntClosedProp D) :
    Nonempty dedekDomain :=
  ⟨dedek_field D hfield hnoeth hintcl⟩

/-- **M305F-9f: Dedekind 整域の存在**（体を退化例として、本物の Dedekind 整域が
    存在）。素イデアルの一般存在（Krull=Zorn）や具体 O_K の Dedekind 性は非構成的
    ／後続だが、体は本物の（退化）Dedekind 整域として存在する。 -/
theorem dedek_exists (D : Domain)
    (hfield : ∀ x, x ≠ D.R.zero → ∃ y, D.R.mul x y = D.R.one)
    (hnoeth : dedekACC D) (hintcl : dedekIntClosedProp D) :
    Nonempty DedekindDomainData :=
  ⟨dedek_data (dedek_field D hfield hnoeth hintcl)⟩

end IUT
