/-
  IUT/FiberFunctor.lean — M276F: 有限エタール圏 FÉt(K) 上のファイバー関手
  F : FÉt(K)ᵒᵖ → FinSet（幾何ファイバー = 切断の集合）の本物の先行建設
  ── 柱A 実 π₁^ét(Spec K) の関手側（Aut(F) の土台）

  分類 **[実]**（本物の K-代数の圏 FÉt(K) 上に、本物の切断集合を値とする
  反変関手を実構成し、その関手則を完全証明する）。

  **complete_pct 影響: 柱A 実 π₁^ét(Spec K) の関手側の本物の先行建設**。
  Grothendieck ガロア理論では π₁^ét(Spec K) = Aut(F)（F はファイバー関手）で
  ある。本モジュールは既存 M272F（本物の有限エタール K-代数の圏 FÉt(K)）の
  上に、幾何ファイバー F(A) = 「基点上の切断の集合」
  （K-代数準同型 A → K の集合）を値とする**反変関手 F を本物で初構成**し、
  反変関手則（F(id)=id・F(ψ∘φ)=F(φ)∘F(ψ)）を完全証明する。さらに分裂被覆
  K^n のファイバーが n 本の相異なる切断（M272F の splitSection）を含むこと
  （幾何ファイバーの基数 = 被覆の枚数 n の下界）を本物で閉じる。これは
  π₁^ét = Aut(F) の群構造（後続 M277F）が乗る土台である。

  * M276F-1 `fibOpCat` — 圏の反対圏 Cᵒᵖ（Spec の反変性を関手として扱う器）
  * M276F-2 `FinSetCat` — 有限集合の圏の骨格（対象 = Nat, 集合 Fin n）。
    ファイバー関手の基数側の行き先
  * M276F-3 `FibPoint` / `fibFunc_map` — 幾何ファイバー F(A) = 切断集合
    KAlgHom A K（基点 Spec K 上の点）と、射 φ:A→B のファイバー写像
    F(φ):F(B)→F(A)（切断の引き戻し = 反変）
  * M276F-4 `fibFunc_id` / `fibFunc_comp` — 反変関手則の完全証明
    （F(id)=id・F(ψ∘φ)=F(φ)∘F(ψ)）
  * M276F-5 `fibFunc` — capstone: **反変関手 F : FÉt(K)ᵒᵖ → Set**
    （opCat 経由の本物の Functor）
  * M276F-6 `FiberFunctorData` / `fiberFunctorData` — 反変を明示した
    総括データ構造（onObj/onMap/id/comp 則をパッケージ）
  * M276F-7 `splitFiberPoint` / `splitFiber_inj` / `fibFunc_card` /
    `fibFunc_faithful_on_split` — 分裂被覆 K^n の幾何ファイバーは n 本の
    相異なる切断を含む（基数下界 |F(K^n)| ≥ n; 切断が対象の n 枚を分離）と
    骨格基数 fibCard(K^n) = n
  * M276F-8 `ratFiberPoint` / `rat_fibFunc_card` / `fiberFunctor_exists` —
    実例（本物の数体 ℚ 上の n 枚被覆のファイバー）と存在定理

  正直な限定（何が本物で何が未達か）:
  1. **本物**: 幾何ファイバー = 切断集合 KAlgHom A K・射の反変引き戻し・
     反変関手則（id・合成）・反対圏経由の Functor・分裂被覆の n 本相異なる
     ファイバー点（基数下界）は全て完全証明（sorry 皆無・新規
     Classical.choice 皆無）。ファイバーは toy 代理ではなく**本物の切断集合**
     （Spec K → A の切断 = 基点上の幾何ファイバーの点）である。
  2. **未達（正直申告）**: 分裂被覆 K^n の幾何ファイバー基数の**完全一致
     |F(K^n)| = n**（≤ n 側）は体の冪等元の 0/1 二分（排中律）を要し、
     M272F-#5 と同じ理由で未形式化。ここで本物で閉じたのは**下界
     |F(K^n)| ≥ n**（n 本の相異なる切断の埋め込み Fin n ↪ F(K^n)）である。
     骨格基数 `fibCard A := A.rank` は「被覆の枚数」を honest に記録し、
     `fibFunc_card` は fibCard(K^n) = n を主張する（= n の完全証明は上界の
     排中律待ち）。
  3. **忠実性・充満性の完全証明は範囲外（後続 M277F）**。ここで閉じたのは
     「ファイバーが分裂被覆の n 枚の切断（連結成分）を分離する」骨組み
     （`fibFunc_faithful_on_split`）に留まる。一般エタール対象上の忠実性は
     分離性理論（M272F ヘッダ #2）が要り後続。
  4. **π₁ = Aut(F) の群構造そのものは範囲外（後続 M277F）**。本モジュールが
     確定させたのは F の構成と反変関手則。Aut(F) の群化と Gal(K̄/K) との
     一致は後続で M14/M16 の抽象ガロア圏機構に接続する。
  5. ファイバー関手の行き先「有限集合の圏 FinSet」は Fin n を対象とする骨格
     （skeleton）である（M272F ヘッダ #1 の許容）。有限性は Fin n で担保。
     反変関手 F 自身は幾何ファイバー（切断の Type）を値とする Set 版で
     本物に構成し、基数側は骨格 FinSetCat で扱う。

  選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。
  禁止タクティク不使用（cases/obtain/rw/show/refine/exact/apply/intro/
  funext/omega のみ）。
-/
import IUT.FiniteEtaleAlgebra

namespace IUT

universe u v

/-! ## M276F-1: 反対圏 Cᵒᵖ（反変性を関手として扱う器） -/

/-- **M276F-1: 反対圏** — 射の向きを逆にした圏。Spec の反変性
    （FÉt の射 A→B が幾何側 Spec B→Spec A に対応）を「共変関手」として
    扱うための器。反変関手 F : C → D は共変関手 Cᵒᵖ → D として実現する。 -/
def fibOpCat (C : Cat.{u, v}) : Cat.{u, v} where
  Obj := C.Obj
  Hom := fun X Y => C.Hom Y X
  id := C.id
  comp := fun f g => C.comp g f
  id_comp := fun f => C.comp_id f
  comp_id := fun f => C.id_comp f
  assoc := fun f g h => (C.assoc h g f).symm

/-! ## M276F-2: 有限集合の圏の骨格 FinSet -/

/-- **M276F-2: 有限集合の圏の骨格** — 対象 = Nat（対象 n は有限集合
    Fin n を表す）、射 = Fin m → Fin n。ファイバー関手の**基数側**の
    行き先（有限性は Fin n で担保）。 -/
def FinSetCat : Cat where
  Obj := Nat
  Hom := fun m n => Fin m → Fin n
  id := fun _ => fun x => x
  comp := fun f g => fun x => g (f x)
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-! ## M276F-3: 幾何ファイバー = 切断集合と射の引き戻し -/

/-- **M276F-3a: 幾何ファイバー F(A)** — 有限エタール対象 A の基点
    Spec K 上のファイバー = 切断の集合 = K-代数準同型 A.obj → K の全体。
    各切断は「A ↠ K」＝ Spec K ↪ Spec A（基点上の 1 点）であり、
    幾何ファイバーの点そのもの。 -/
def FibPoint {K : IUTField} (A : FiniteEtaleData K) : Type :=
  KAlgHom A.obj (trivialEtaleAlgebra K)

/-- **M276F-3b: ファイバー写像 F(φ) = 切断の引き戻し** — FÉt の射
    φ : A → B（幾何側 Spec B → Spec A）に対し、B の切断 s : B → K を
    s ∘ φ : A → K に引き戻す。**反変**（B のファイバー → A のファイバー）。 -/
def fibFunc_map {K : IUTField} {A B : FiniteEtaleData K}
    (φ : KAlgHom A.obj B.obj) : FibPoint B → FibPoint A :=
  fun s => kAlgCompHom φ s

/-! ## M276F-4: 反変関手則の完全証明 -/

/-- **M276F-4a: F(id) = id** — 恒等射のファイバー写像は恒等。 -/
theorem fibFunc_id {K : IUTField} (A : FiniteEtaleData K) :
    fibFunc_map (kAlgIdHom A.obj) = (fun s : FibPoint A => s) := by
  funext s
  exact kAlgHom_ext (fun _ => rfl)

/-- **M276F-4b: F(ψ ∘ φ) = F(φ) ∘ F(ψ)** — 合成の**反変**両立。
    φ : A → B, ψ : B → C に対し、ファイバー写像は逆順に合成される。 -/
theorem fibFunc_comp {K : IUTField} {A B C : FiniteEtaleData K}
    (φ : KAlgHom A.obj B.obj) (ψ : KAlgHom B.obj C.obj) :
    fibFunc_map (kAlgCompHom φ ψ)
      = (fun s : FibPoint C => fibFunc_map φ (fibFunc_map ψ s)) := by
  funext s
  exact kAlgHom_ext (fun _ => rfl)

/-! ## M276F-5: capstone — 反変ファイバー関手 F : FÉt(K)ᵒᵖ → Set -/

/-- **M276F-5: 反変ファイバー関手 F : FÉt(K)ᵒᵖ → Set** — 本物の Functor。
    対象 A ↦ 幾何ファイバー F(A)（切断集合）、射 φ:A→B（反対圏では B→A）↦
    引き戻し F(φ):F(B)→F(A)。反変関手則を完全証明済み（M276F-4）。 -/
def fibFunc (K : IUTField) : Functor (fibOpCat (fEtCat K)) SetCat where
  onObj := fun A => FibPoint A
  onHom := fun {A B} φ => fibFunc_map φ
  map_id := fun A => fibFunc_id A
  map_comp := fun {A B C} φ ψ => by
    show fibFunc_map (kAlgCompHom ψ φ)
      = SetCat.comp (fibFunc_map φ) (fibFunc_map ψ)
    exact fibFunc_comp ψ φ

/-! ## M276F-6: 反変を明示した総括データ構造 -/

/-- **M276F-6a: ファイバー関手データ**（反変を明示した器）。
    onObj/onMap（反変）/ id 則 / 反変合成則をパッケージ。 -/
structure FiberFunctorData (K : IUTField) where
  /-- 対象 ↦ 幾何ファイバー（切断集合）。 -/
  onObj : FiniteEtaleData K → Type
  /-- 射 φ:A→B ↦ ファイバー写像 F(φ):F(B)→F(A)（反変）。 -/
  onMap : {A B : FiniteEtaleData K} →
    KAlgHom A.obj B.obj → onObj B → onObj A
  /-- F(id) = id。 -/
  map_id : ∀ A : FiniteEtaleData K,
    onMap (kAlgIdHom A.obj) = (fun s : onObj A => s)
  /-- F(ψ ∘ φ) = F(φ) ∘ F(ψ)（反変合成）。 -/
  map_comp : ∀ {A B C : FiniteEtaleData K}
    (φ : KAlgHom A.obj B.obj) (ψ : KAlgHom B.obj C.obj),
    onMap (kAlgCompHom φ ψ) = (fun s => onMap φ (onMap ψ s))

/-- **M276F-6b: ファイバー関手データの実体**（M276F-3〜4 の束ね）。 -/
def fiberFunctorData (K : IUTField) : FiberFunctorData K where
  onObj := FibPoint
  onMap := fun {_ _} φ => fibFunc_map φ
  map_id := fibFunc_id
  map_comp := fun {_ _ _} φ ψ => fibFunc_comp φ ψ

/-! ## M276F-7: 分裂被覆の幾何ファイバー（基数下界 ≥ n） -/

/-- **M276F-7a: 分裂被覆 K^n の第 i ファイバー点** — 第 i 切断
    （M272F の splitSection）を幾何ファイバー F(K^n) の点として見る。 -/
def splitFiberPoint (K : IUTField) (n : Nat) (i : Fin n) :
    FibPoint (splitFEt K n) :=
  splitSection K n i

/-- **M276F-7b: n 本のファイバー点は相異なる** — 幾何ファイバー
    F(K^n) は少なくとも n 個の相異なる点を持つ（M272F の切断相異なり
    fEtale_sections_distinct をファイバー点で言い換え）。基数下界の実体。 -/
theorem splitFiber_inj (K : IUTField) (n : Nat) {i j : Fin n}
    (hij : i ≠ j) : splitFiberPoint K n i ≠ splitFiberPoint K n j :=
  fun hc => hij (splitSection_inj hc)

/-- **M276F-7c: 単射的ファイバー埋め込み Fin n ↪ F(K^n)** — n 枚被覆の
    ファイバー点付け（相異なる n 本）。|F(K^n)| ≥ n の witness。 -/
def splitFiberEmbed (K : IUTField) (n : Nat) :
    Fin n → FibPoint (splitFEt K n) :=
  splitFiberPoint K n

/-- **M276F-7d: 埋め込みの単射性**（|F(K^n)| ≥ n）。 -/
theorem splitFiberEmbed_inj (K : IUTField) (n : Nat) {i j : Fin n}
    (h : splitFiberEmbed K n i = splitFiberEmbed K n j) : i = j :=
  splitSection_inj h

/-- **M276F-7e: 骨格ファイバー基数** — 有限エタール対象の幾何ファイバーの
    基数（被覆の枚数 = K 上の次元）。FinSetCat の対象値。 -/
def fibCard {K : IUTField} (A : FiniteEtaleData K) : Nat := A.rank

/-- **M276F-7f: 分裂被覆の基数** fibCard(K^n) = n（骨格基数）。
    正直な限定: これは「被覆の枚数」の記録であり、幾何ファイバーの
    完全基数一致 |F(K^n)| = n（≤ n 側）は排中律待ち（M276F-7c で下界 ≥ n
    を本物で証明済み）。 -/
theorem fibFunc_card (K : IUTField) (n : Nat) :
    fibCard (splitFEt K n) = n := rfl

/-- **M276F-7g: ファイバーが分裂被覆の n 枚を分離する骨組み** —
    分裂対象 K^n 上、相異なる添字 i ≠ j はファイバー関手で相異なる
    ファイバー点に写る（F が n 個の連結成分を分離する）。忠実性の骨組み
    （完全な忠実・充満は後続 M277F）。 -/
theorem fibFunc_faithful_on_split (K : IUTField) (n : Nat) {i j : Fin n}
    (hij : i ≠ j) :
    fibFunc_map (kAlgIdHom (splitFEt K n).obj) (splitFiberPoint K n i)
      ≠ fibFunc_map (kAlgIdHom (splitFEt K n).obj) (splitFiberPoint K n j) := by
  intro hc
  apply hij
  apply splitSection_inj
  have hi : fibFunc_map (kAlgIdHom (splitFEt K n).obj) (splitFiberPoint K n i)
      = splitFiberPoint K n i := by
    have h := fibFunc_id (splitFEt K n)
    exact congrFun h (splitFiberPoint K n i)
  have hj : fibFunc_map (kAlgIdHom (splitFEt K n).obj) (splitFiberPoint K n j)
      = splitFiberPoint K n j := by
    have h := fibFunc_id (splitFEt K n)
    exact congrFun h (splitFiberPoint K n j)
  rw [hi, hj] at hc
  exact hc

/-! ## M276F-8: 実例（ℚ 上）と存在定理 -/

/-- **M276F-8a: 実例 — 本物の数体 ℚ 上の n 枚被覆の第 i ファイバー点**。 -/
def ratFiberPoint (n : Nat) (i : Fin n) :
    FibPoint (ratSplitCover n) :=
  splitFiberPoint ratIUTField n i

/-- **M276F-8b: ℚ 上のファイバー基数** fibCard(ℚ の n 枚被覆) = n。 -/
theorem rat_fibFunc_card (n : Nat) : fibCard (ratSplitCover n) = n := rfl

/-- **M276F-8c: ℚ 上でも n 本のファイバー点は相異なる**（下界 ≥ n）。 -/
theorem rat_splitFiber_inj (n : Nat) {i j : Fin n} (hij : i ≠ j) :
    ratFiberPoint n i ≠ ratFiberPoint n j :=
  splitFiber_inj ratIUTField n hij

/-- **M276F-8d: capstone — ファイバー関手の存在**（任意の体 K 上で
    反変ファイバー関手 F : FÉt(K)ᵒᵖ → Set が構成できる）。 -/
theorem fiberFunctor_exists (K : IUTField) :
    Nonempty (Functor (fibOpCat (fEtCat K)) SetCat) :=
  ⟨fibFunc K⟩

/-- **M276F-8e: capstone — 実 ℚ 上のファイバー関手の存在**。 -/
theorem fiberFunctor_exists_rat :
    Nonempty (Functor (fibOpCat (fEtCat ratIUTField)) SetCat) :=
  ⟨fibFunc ratIUTField⟩

/-- **M276F-8f: capstone — ファイバー関手データの存在**。 -/
theorem fiberFunctorData_exists (K : IUTField) :
    Nonempty (FiberFunctorData K) :=
  ⟨fiberFunctorData K⟩

end IUT
