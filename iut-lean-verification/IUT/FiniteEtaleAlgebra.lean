/-
  IUT/FiniteEtaleAlgebra.lean — M272F: 有限エタール K-代数の圏 FÉt(K) の対象と射
  ── 柱A 実 π₁^ét(Spec K) の被覆側対象の本物の先行建設

  分類 **[実]**（本物の K-代数・本物の分裂エタール被覆・圏構造の実構成）。

  **complete_pct 影響: 柱A 実 π₁^ét(Spec K) の被覆側対象（有限エタール
  K-代数の圏）の本物の先行建設**。Spec K の有限エタール被覆 = 有限次分離的
  K-代数（分離拡大の有限直積）であり、この圏 FÉt(K) のガロア圏構造から
  π₁^ét(Spec K) = Gal(K̄/K) が復元される（遠アーベルの入口）。本モジュールは
  その**対象と射を本物の K-代数として初構成**する: K-代数（可換環 + 構造射）・
  K-代数準同型（構造射両立）・圏公理、そして**分裂エタール代数 K^n**
  （自明 n 枚被覆 = Spec K の n 点の非交和の座標環）を本物で建て、
  直交冪等元系（Spec(K^n) の n 個の連結成分）・分割完全性 Σeᵢ = 1・
  被約性（エタールの帰結）・n 本の相異なる切断（ファイバーの n 点）を
  完全証明する。既存 M264F（IUTField）・M38（CRing/RingHom）・
  M19（Cat/CatIso/Functor）を土台に接続し、実例は本物の数体 ℚ
  （M264F の ratIUTField）上の分裂被覆で確定する。

  * M272F-1 `KAlgebra` / `KAlgHom` / `kAlgHom_ext` — K-代数（可換環 A +
    構造射 K → A）と K-代数準同型（構造射と両立する環準同型）・射の外延性
  * M272F-2 `kAlgIdHom` / `kAlgCompHom` / `kAlgCat` — 恒等・合成と
    **K-代数の圏**（圏公理の完全証明）
  * M272F-3 `trivialEtaleAlgebra` / `kAlgInitialHom(_unique)` — 自明被覆
    A = K（Spec K 自身）と **K が K-代数の圏の始対象**であること
    （= Spec K は FÉt(K) の終対象; 被覆の基点）
  * M272F-4 `funPowCRing` / `splitEtaleAlgebra` — 直積環 K^n と
    **分裂エタール K-代数 K^n**（自明 n 枚被覆の座標環）の実構成
  * M272F-5 `splitIdem` / `splitIdem_mul_self` / `splitIdem_mul_orth` /
    `kPowSum` / `splitIdem_complete` — **直交冪等元系**: eᵢ² = eᵢ・
    eᵢeⱼ = 0 (i≠j)・Σᵢ eᵢ = 1（Spec(K^n) が n 個の連結成分に分解する
    ことの環論的実体）
  * M272F-6 `splitEtale_reduced` — **被約性**（witness 形）: 成分が非零
    なら x·x ≠ 0（エタール代数に冪零元が無いことの構成的核）
  * M272F-7 `splitSection` / `splitSection_inj` / `fEtale_sections_distinct`
    — 分裂被覆の **n 本の切断**（K-代数準同型 K^n → K = ファイバーの点）
    が相異なること（|fiber| ≥ n; ファイバー関手の値の実体）
  * M272F-8 `trivialSplitIso` — 自明被覆 K ≅ K¹（K-代数同型）
  * M272F-9 `FiniteEtaleData` / `fEtCat` / `fEtForget` / `splitFEt` /
    `trivialFEt` / `ratSplitCover` / `finiteEtale_exists(_rat)` — capstone:
    有限エタール対象（分裂構造 witness 付き K-代数）・**圏 FÉt(K) の骨格**・
    忘却関手・実例（Spec ℚ の n 枚分裂被覆）・存在定理

  正直な限定（何が本物で何が未達か）:
  1. **本物**: K-代数・K-代数準同型・圏公理・K^n の分裂エタール構造・
     直交冪等元の完全系・被約性 witness・n 本の相異なる切断・K の始対象性は
     全て完全証明（sorry 皆無・新規 Classical.choice 皆無）。K^n は toy 代理
     ではなく**自明エタール被覆の本物**（Spec K の n 点非交和の座標環）である。
  2. **未達（正直申告）**: 本モジュールの「有限エタール対象」は**分裂
     （split étale）witness 付き**の対象に限る。一般の有限エタール K-代数
     （非自明な分離拡大 L/K の有限直積）は分離性理論（多項式の微分判定・
     根の非重複）を要し後続で建設する。分裂対象は分離閉体上では全対象を
     尽くすが、一般の K 上では FÉt(K) の充満部分圏（自明被覆の圏）である。
  3. エタール性の**完全判定**（平坦 + 非分岐、または分離冪等元による特徴付け）
     は未形式化。ここでは分裂構造そのもの（K^n との K-代数同型）をエタール性の
     witness として持つ（分裂 ⇒ エタールは定義的に正当）。
  4. **π₁^ét の復元は範囲外（後続）**: ガロア圏公理（ファイバー関手・
     連結成分分解）と Aut(F) = Gal(K̄/K) は既存 M14/M16 の抽象ガロア圏機構と
     後続で接続する。本モジュールが確定させたのは「FÉt(K) の対象と射が
     本物の K-代数として定義された」こと。
  5. 「K^n の切断はちょうど n 本」（≤ n 側）は体の冪等元の 0/1 二分に
     排中律を要するため未形式化（≥ n 側 = 相異なる n 本は完全証明）。

  選択公理不使用・sorry 不使用・新規 Classical.choice 不使用
  （場合分けは全て Decidable witness の構成的分解）。禁止タクティク不使用。
-/
import IUT.Field
import IUT.CategoryTheory

namespace IUT

/-! ## M272F-0: 構成的補助（Decidable の分解・Fin の外延性・add_zero） -/

/-- Decidable な命題の構成的二分（Classical.em ではなく instance の分解）。 -/
theorem kAlgDecEm (p : Prop) [inst : Decidable p] : p ∨ ¬ p :=
  match inst with
  | isTrue h => Or.inl h
  | isFalse h => Or.inr h

/-- Fin の外延性（値が等しければ等しい）。 -/
theorem kAlgFin_ext {n : Nat} {a b : Fin n} (h : a.val = b.val) : a = b := by
  cases a with
  | mk av ah =>
    cases b with
    | mk bv bh =>
      cases h
      rfl

/-- 可換環の右零加法 a + 0 = a（可換性から）。 -/
theorem kAlg_add_zero (R : CRing) (a : R.carrier) : R.add a R.zero = a := by
  rw [R.add_comm, R.zero_add]

/-! ## M272F-1: K-代数と K-代数準同型 -/

/-- **M272F-1a: K-代数** — 可換環 A と構造射（環準同型）K → A の対。
    Spec A → Spec K の（アフィン）射の環論的実体。 -/
structure KAlgebra (K : IUTField) where
  /-- 台の可換環 A。 -/
  alg : CRing
  /-- 構造射 K → A（環準同型）。 -/
  structMap : RingHom K.toCRing alg

/-- **M272F-1b: K-代数準同型** — 構造射と両立する環準同型 A → B。
    被覆側では Spec B → Spec A（Spec K 上の射）に対応（反変）。 -/
structure KAlgHom {K : IUTField} (A B : KAlgebra K) where
  /-- 台の環準同型。 -/
  hom : RingHom A.alg B.alg
  /-- 構造射との両立（K 上の射であること）。 -/
  compat : ∀ c : K.carrier, hom.map (A.structMap.map c) = B.structMap.map c

/-- **M272F-1c: 射の外延性** — K-代数準同型は台写像で決まる。 -/
theorem kAlgHom_ext {K : IUTField} {A B : KAlgebra K} {f g : KAlgHom A B}
    (h : ∀ x, f.hom.map x = g.hom.map x) : f = g := by
  cases f with
  | mk fh fc =>
    cases g with
    | mk gh gc =>
      cases fh with
      | mk fmap fa fm fo =>
        cases gh with
        | mk gmap ga gm go =>
          have hm : fmap = gmap := funext h
          cases hm
          rfl

/-! ## M272F-2: 恒等・合成と K-代数の圏 -/

/-- 恒等 K-代数準同型。 -/
def kAlgIdHom {K : IUTField} (A : KAlgebra K) : KAlgHom A A where
  hom :=
    { map := fun a => a
      map_add := fun _ _ => rfl
      map_mul := fun _ _ => rfl
      map_one := rfl }
  compat := fun _ => rfl

/-- K-代数準同型の合成。 -/
def kAlgCompHom {K : IUTField} {A B C : KAlgebra K}
    (f : KAlgHom A B) (g : KAlgHom B C) : KAlgHom A C where
  hom :=
    { map := fun a => g.hom.map (f.hom.map a)
      map_add := fun a b => by rw [f.hom.map_add, g.hom.map_add]
      map_mul := fun a b => by rw [f.hom.map_mul, g.hom.map_mul]
      map_one := by rw [f.hom.map_one, g.hom.map_one] }
  compat := fun c => by
    show g.hom.map (f.hom.map (A.structMap.map c)) = C.structMap.map c
    rw [f.compat, g.compat]

/-- **M272F-2: K-代数の圏**（対象 = 本物の K-代数、射 = K-代数準同型）。
    FÉt(K) はこの圏の充満部分圏として切り出される（M272F-9）。 -/
def kAlgCat (K : IUTField) : Cat where
  Obj := KAlgebra K
  Hom := KAlgHom
  id := kAlgIdHom
  comp := kAlgCompHom
  id_comp := fun _ => kAlgHom_ext (fun _ => rfl)
  comp_id := fun _ => kAlgHom_ext (fun _ => rfl)
  assoc := fun _ _ _ => kAlgHom_ext (fun _ => rfl)

/-- K-代数の同型（圏の中の同型として）。 -/
def kAlgIdIso (K : IUTField) (A : KAlgebra K) : CatIso (kAlgCat K) A A where
  hom := kAlgIdHom A
  inv := kAlgIdHom A
  hom_inv := kAlgHom_ext (fun _ => rfl)
  inv_hom := kAlgHom_ext (fun _ => rfl)

/-! ## M272F-3: 自明被覆 A = K と K の始対象性 -/

/-- **M272F-3a: 自明被覆** — K 自身を K-代数と見る（Spec K 自身、恒等被覆）。 -/
def trivialEtaleAlgebra (K : IUTField) : KAlgebra K where
  alg := K.toCRing
  structMap :=
    { map := fun c => c
      map_add := fun _ _ => rfl
      map_mul := fun _ _ => rfl
      map_one := rfl }

/-- **M272F-3b: K は始対象（存在）** — 任意の K-代数 A への K-代数準同型
    K → A は構造射で与えられる。被覆側: Spec K は FÉt(K) の終対象（基点）。 -/
def kAlgInitialHom {K : IUTField} (A : KAlgebra K) :
    KAlgHom (trivialEtaleAlgebra K) A where
  hom := A.structMap
  compat := fun _ => rfl

/-- **M272F-3c: K は始対象（一意性）** — K → A の K-代数準同型は構造射のみ。 -/
theorem kAlgInitialHom_unique {K : IUTField} {A : KAlgebra K}
    (f : KAlgHom (trivialEtaleAlgebra K) A) : f = kAlgInitialHom A :=
  kAlgHom_ext (fun c => f.compat c)

/-! ## M272F-4: 直積環 K^n と分裂エタール代数 -/

/-- **M272F-4a: 直積環 R^n**（成分ごとの演算）。Spec の n 点非交和の座標環。 -/
def funPowCRing (R : CRing) (n : Nat) : CRing where
  carrier := Fin n → R.carrier
  add := fun x y i => R.add (x i) (y i)
  zero := fun _ => R.zero
  neg := fun x i => R.neg (x i)
  mul := fun x y i => R.mul (x i) (y i)
  one := fun _ => R.one
  add_assoc := fun x y z => funext fun i => R.add_assoc (x i) (y i) (z i)
  zero_add := fun x => funext fun i => R.zero_add (x i)
  neg_add := fun x => funext fun i => R.neg_add (x i)
  add_comm := fun x y => funext fun i => R.add_comm (x i) (y i)
  mul_assoc := fun x y z => funext fun i => R.mul_assoc (x i) (y i) (z i)
  one_mul := fun x => funext fun i => R.one_mul (x i)
  mul_comm := fun x y => funext fun i => R.mul_comm (x i) (y i)
  left_distrib := fun x y z => funext fun i => R.left_distrib (x i) (y i) (z i)

/-- **M272F-4b: 分裂エタール K-代数 K^n** — 自明 n 枚被覆
    （Spec K の n 点非交和）の座標環。構造射は対角埋め込み c ↦ (c,…,c)。
    分離閉体上ではあらゆる有限エタール代数がこの形に同型（分裂）。 -/
def splitEtaleAlgebra (K : IUTField) (n : Nat) : KAlgebra K where
  alg := funPowCRing K.toCRing n
  structMap :=
    { map := fun c _ => c
      map_add := fun _ _ => rfl
      map_mul := fun _ _ => rfl
      map_one := rfl }

/-! ## M272F-5: 直交冪等元系（Spec(K^n) の n 個の連結成分） -/

/-- **M272F-5a: 標準冪等元** eᵢ = (0,…,0,1,0,…,0)（第 i 成分のみ 1）。
    Spec(K^n) の第 i 連結成分の特性関数。 -/
def splitIdem (K : IUTField) (n : Nat) (i : Fin n) :
    (funPowCRing K.toCRing n).carrier :=
  fun j => if i = j then K.one else K.zero

/-- **M272F-5b: 冪等性** eᵢ·eᵢ = eᵢ。 -/
theorem splitIdem_mul_self (K : IUTField) (n : Nat) (i : Fin n) :
    (funPowCRing K.toCRing n).mul (splitIdem K n i) (splitIdem K n i)
      = splitIdem K n i := by
  funext j
  show K.mul (if i = j then K.one else K.zero) (if i = j then K.one else K.zero)
    = (if i = j then K.one else K.zero)
  cases kAlgDecEm (i = j) with
  | inl h => rw [if_pos h, K.one_mul]
  | inr h => rw [if_neg h, K.toCRing.mul_zero]

/-- **M272F-5c: 直交性** i ≠ j なら eᵢ·eⱼ = 0（成分が交わらない）。 -/
theorem splitIdem_mul_orth (K : IUTField) (n : Nat) {i j : Fin n} (hij : i ≠ j) :
    (funPowCRing K.toCRing n).mul (splitIdem K n i) (splitIdem K n j)
      = (funPowCRing K.toCRing n).zero := by
  funext k
  show K.mul (if i = k then K.one else K.zero) (if j = k then K.one else K.zero)
    = K.zero
  cases kAlgDecEm (j = k) with
  | inl h =>
    have hik : ¬ i = k := fun hc => hij (hc.trans h.symm)
    rw [if_pos h, if_neg hik, K.mul_comm, K.toCRing.mul_zero]
  | inr h =>
    rw [if_neg h, K.toCRing.mul_zero]

/-- **M272F-5d: 有限和**（Fin n 添字の環元の和; 左から順に加える）。 -/
def kPowSum (R : CRing) : (n : Nat) → (Fin n → R.carrier) → R.carrier
  | 0, _ => R.zero
  | n + 1, x =>
    R.add (kPowSum R n (fun i => x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      (x ⟨n, Nat.lt_succ_self n⟩)

/-- kPowSum の一段展開（定義等式）。 -/
theorem kPowSum_succ (R : CRing) (n : Nat) (f : Fin (n + 1) → R.carrier) :
    kPowSum R (n + 1) f
      = R.add (kPowSum R n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
          (f ⟨n, Nat.lt_succ_self n⟩) := rfl

/-- 和の各項が一致すれば和も一致（合同性）。 -/
theorem kPowSum_congr (R : CRing) : ∀ (n : Nat) (f g : Fin n → R.carrier),
    (∀ i, f i = g i) → kPowSum R n f = kPowSum R n g := by
  intro n
  induction n with
  | zero =>
    intro f g h
    rfl
  | succ m ih =>
    intro f g h
    rw [kPowSum_succ R m f, kPowSum_succ R m g,
      ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩),
      h ⟨m, Nat.lt_succ_self m⟩]

/-- 各項が 0 なら和は 0。 -/
theorem kPowSum_zero (R : CRing) : ∀ (n : Nat) (f : Fin n → R.carrier),
    (∀ i, f i = R.zero) → kPowSum R n f = R.zero := by
  intro n
  induction n with
  | zero =>
    intro f h
    rfl
  | succ m ih =>
    intro f h
    rw [kPowSum_succ R m f,
      ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩),
      h ⟨m, Nat.lt_succ_self m⟩, R.zero_add]

/-- クロネッカーの δ の和は 1（添字 j がちょうど一度だけ拾われる）。 -/
theorem kPowSum_delta (R : CRing) : ∀ (n : Nat) (j : Fin n),
    kPowSum R n (fun i => if i = j then R.one else R.zero) = R.one := by
  intro n
  induction n with
  | zero =>
    intro j
    exact absurd j.isLt (Nat.not_lt_zero j.val)
  | succ m ih =>
    intro j
    rw [kPowSum_succ R m (fun i => if i = j then R.one else R.zero)]
    show R.add
        (kPowSum R m fun i =>
          if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = j
            then R.one else R.zero)
        (if (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = j then R.one else R.zero)
      = R.one
    cases kAlgDecEm (j.val = m) with
    | inl hval =>
      have hj : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = j :=
        kAlgFin_ext hval.symm
      have hz : kPowSum R m
          (fun i =>
            if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = j
              then R.one else R.zero) = R.zero := by
        apply kPowSum_zero
        intro i
        have hlt := i.isLt
        have hne : ¬ (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = j := by
          intro hc
          have hv : i.val = j.val := congrArg Fin.val hc
          omega
        show (if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = j
          then R.one else R.zero) = R.zero
        rw [if_neg hne]
      rw [if_pos hj, hz, R.zero_add]
    | inr hval =>
      have hjlt : j.val < m := by
        have h1 := j.isLt
        omega
      have hlast : ¬ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = j := by
        intro hc
        have hv : m = j.val := congrArg Fin.val hc
        omega
      have hcongr : ∀ i : Fin m,
          (if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = j
            then R.one else R.zero)
            = (if i = (⟨j.val, hjlt⟩ : Fin m) then R.one else R.zero) := by
        intro i
        cases kAlgDecEm (i = (⟨j.val, hjlt⟩ : Fin m)) with
        | inl h =>
          have hv : i.val = j.val := congrArg Fin.val h
          have hcs : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = j :=
            kAlgFin_ext hv
          rw [if_pos hcs, if_pos h]
        | inr h =>
          have hcs : ¬ (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = j := by
            intro hc
            apply h
            have hv2 := congrArg Fin.val hc
            exact kAlgFin_ext hv2
          rw [if_neg hcs, if_neg h]
      rw [if_neg hlast,
        kPowSum_congr R m _ _ hcongr, ih ⟨j.val, hjlt⟩, kAlg_add_zero]

/-- 直積環での和は成分ごとの和（第 j 成分の読み出し）。 -/
theorem kPowSum_apply (R : CRing) (m : Nat) (j : Fin m) :
    ∀ (n : Nat) (f : Fin n → (funPowCRing R m).carrier),
      kPowSum (funPowCRing R m) n f j = kPowSum R n (fun i => f i j) := by
  intro n
  induction n with
  | zero =>
    intro f
    rfl
  | succ k ih =>
    intro f
    show R.add
        (kPowSum (funPowCRing R m) k
          (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j)
        (f ⟨k, Nat.lt_succ_self k⟩ j)
      = R.add (kPowSum R k fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j)
          (f ⟨k, Nat.lt_succ_self k⟩ j)
    rw [ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]

/-- **M272F-5e: 分割の完全性** Σᵢ eᵢ = 1 — Spec(K^n) は n 個の連結成分に
    **過不足なく**分解する（直交冪等元の完全系）。 -/
theorem splitIdem_complete (K : IUTField) (n : Nat) :
    kPowSum (funPowCRing K.toCRing n) n (splitIdem K n)
      = (funPowCRing K.toCRing n).one := by
  funext j
  rw [kPowSum_apply K.toCRing n j n (splitIdem K n)]
  exact kPowSum_delta K.toCRing n j

/-! ## M272F-6: 被約性（エタール代数に冪零元は無い） -/

/-- **M272F-6: 被約性（witness 形）** — ある成分が非零なら x·x ≠ 0。
    体の整域性（M264F の mul_ne_zero）の成分ごとの帰結であり、
    「エタール代数は被約」の構成的核（冪零 witness の排除）。 -/
theorem splitEtale_reduced (K : IUTField) (n : Nat)
    (x : (funPowCRing K.toCRing n).carrier) (i : Fin n)
    (hx : x i ≠ K.zero) :
    (funPowCRing K.toCRing n).mul x x ≠ (funPowCRing K.toCRing n).zero := by
  intro hc
  have hcomp : K.mul (x i) (x i) = K.zero := congrFun hc i
  exact K.mul_ne_zero hx hx hcomp

/-! ## M272F-7: 分裂被覆の n 本の切断（ファイバーの点） -/

/-- **M272F-7a: 第 i 切断** — 第 i 成分への射影 K^n → K は K-代数準同型。
    被覆側では Spec K → Spec(K^n) の切断（ファイバーの第 i 点）。 -/
def splitSection (K : IUTField) (n : Nat) (i : Fin n) :
    KAlgHom (splitEtaleAlgebra K n) (trivialEtaleAlgebra K) where
  hom :=
    { map := fun x => x i
      map_add := fun _ _ => rfl
      map_mul := fun _ _ => rfl
      map_one := rfl }
  compat := fun _ => rfl

/-- **M272F-7b: 切断の分離** — 切断が一致すれば添字が一致
    （冪等元 eᵢ での値 1 ≠ 0 で分離; K の非自明性 M264F を使用）。 -/
theorem splitSection_inj {K : IUTField} {n : Nat} {i j : Fin n}
    (h : splitSection K n i = splitSection K n j) : i = j := by
  have h1 : (splitSection K n i).hom.map (splitIdem K n i)
      = (splitSection K n j).hom.map (splitIdem K n i) := by
    rw [h]
  have h2 : (if i = i then K.one else K.zero)
      = (if i = j then K.one else K.zero) := h1
  rw [if_pos rfl] at h2
  cases kAlgDecEm (i = j) with
  | inl hij => exact hij
  | inr hij =>
    rw [if_neg hij] at h2
    exact absurd h2 K.one_ne_zero

/-- **M272F-7c: n 本の切断は相異なる** — 分裂 n 枚被覆のファイバーは
    少なくとも n 点を持つ（ファイバー関手の値 |F(K^n)| ≥ n の実体）。 -/
theorem fEtale_sections_distinct (K : IUTField) (n : Nat) {i j : Fin n}
    (hij : i ≠ j) : splitSection K n i ≠ splitSection K n j :=
  fun hc => hij (splitSection_inj hc)

/-! ## M272F-8: 自明被覆 K ≅ K¹ -/

/-- **M272F-8: K-代数同型 K ≅ K¹** — 1 枚被覆は自明被覆そのもの。 -/
def trivialSplitIso (K : IUTField) :
    CatIso (kAlgCat K) (trivialEtaleAlgebra K) (splitEtaleAlgebra K 1) where
  hom :=
    { hom :=
        { map := fun c _ => c
          map_add := fun _ _ => rfl
          map_mul := fun _ _ => rfl
          map_one := rfl }
      compat := fun _ => rfl }
  inv :=
    { hom :=
        { map := fun x => x ⟨0, Nat.zero_lt_one⟩
          map_add := fun _ _ => rfl
          map_mul := fun _ _ => rfl
          map_one := rfl }
      compat := fun _ => rfl }
  hom_inv := kAlgHom_ext (fun _ => rfl)
  inv_hom := kAlgHom_ext (fun x => funext fun i => by
    have hi : i = (⟨0, Nat.zero_lt_one⟩ : Fin 1) :=
      kAlgFin_ext (show i.val = 0 from by
        have h1 := i.isLt
        omega)
    rw [hi]
    exact rfl)

/-! ## M272F-9: capstone — 有限エタール対象と圏 FÉt(K) の骨格 -/

/-- **M272F-9a: 有限エタール K-代数（分裂 witness 付き）** — 本物の
    K-代数 A と、有限性・エタール性の witness たる分裂構造
    （K-代数同型 A ≅ K^rank）。rank が被覆の枚数（K-加群としての次元）。
    正直な限定: 一般の分離拡大の直積は後続（ヘッダ参照）。 -/
structure FiniteEtaleData (K : IUTField) where
  /-- 台の K-代数（本物）。 -/
  obj : KAlgebra K
  /-- 被覆の枚数（K 上の次元）。 -/
  rank : Nat
  /-- 分裂構造: A ≅ K^rank（有限性 + エタール性の witness）。 -/
  splitIso : CatIso (kAlgCat K) obj (splitEtaleAlgebra K rank)

/-- **M272F-9b: 圏 FÉt(K) の骨格** — 対象 = 有限エタール対象（分裂
    witness 付き K-代数）、射 = 台の K-代数準同型。圏公理は K-代数の圏から
    継承（充満部分圏）。 -/
def fEtCat (K : IUTField) : Cat where
  Obj := FiniteEtaleData K
  Hom := fun A B => KAlgHom A.obj B.obj
  id := fun A => kAlgIdHom A.obj
  comp := kAlgCompHom
  id_comp := fun _ => kAlgHom_ext (fun _ => rfl)
  comp_id := fun _ => kAlgHom_ext (fun _ => rfl)
  assoc := fun _ _ _ => kAlgHom_ext (fun _ => rfl)

/-- **M272F-9c: 忘却関手 FÉt(K) → (K-代数)** — 充満部分圏の包含。 -/
def fEtForget (K : IUTField) : Functor (fEtCat K) (kAlgCat K) where
  onObj := FiniteEtaleData.obj
  onHom := fun f => f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- **M272F-9d: 分裂被覆は FÉt(K) の対象**（witness は恒等同型）。 -/
def splitFEt (K : IUTField) (n : Nat) : FiniteEtaleData K :=
  ⟨splitEtaleAlgebra K n, n, kAlgIdIso K (splitEtaleAlgebra K n)⟩

/-- **M272F-9e: 自明被覆 Spec K 自身は FÉt(K) の対象**（witness は
    M272F-8 の同型 K ≅ K¹）。 -/
def trivialFEt (K : IUTField) : FiniteEtaleData K :=
  ⟨trivialEtaleAlgebra K, 1, trivialSplitIso K⟩

/-- **M272F-9f: 実例 — 本物の数体 ℚ 上の n 枚分裂被覆**（M264F の
    ratIUTField 上の FÉt(ℚ) の対象）。 -/
def ratSplitCover (n : Nat) : FiniteEtaleData ratIUTField :=
  splitFEt ratIUTField n

/-- **M272F-9g: capstone — 有限エタール対象の存在**（任意の体 K 上で
    FÉt(K) は空でない: Spec K 自身が対象）。 -/
theorem finiteEtale_exists (K : IUTField) : Nonempty (FiniteEtaleData K) :=
  ⟨trivialFEt K⟩

/-- **M272F-9h: capstone — 実 ℚ 上の存在**（本物の数体上の 2 枚分裂被覆
    = Spec ℚ ⊔ Spec ℚ が FÉt(ℚ) の対象）。 -/
theorem finiteEtale_exists_rat : Nonempty (FiniteEtaleData ratIUTField) :=
  ⟨ratSplitCover 2⟩

end IUT
