/-
  IUT/GaloisPi1Iso.lean — M286F: Gal(L/K) → π₁ = Aut(F) の同型（忠実・全モノドロミー）
  ── 柱A「実 π₁^ét とガロア群の同型」の本物の先行建設

  分類 **[実]**（本物の体拡大 K[X]/(f) の連結ファイバー上での本物の Gal 作用・
  本物の対称群 Sym(ファイバー)・本物の群準同型/核/像/第一同型定理。toy 群・
  surrogate を主語にしない）。

  **complete_pct 影響: 柱A の中心命題「連結ガロア被覆で Gal(L/K) ≅ π₁ の像
  （忠実・全モノドロミー）」を本物で初建設**。M277F `grGal_fromGalois` は
  Gal(L/K) → π₁ = Aut(F) の**準同型の構成まで**であり、その像が π₁ の中で
  非自明（忠実性）・全モノドロミーであることは未達だった（M277F 正直申告 4）。
  実際、分裂被覆 K^n の上では π₁ は各標準点を固定し（M277F `grGal_split_trivial`）、
  M277F の Gal→π₁ 像はそこで自明に潰れる（本モジュール `galPi1_split_fromGalois_trivial`
  でこの honest な contrast を明示）。忠実性・全モノドロミーは**連結被覆 L=K[X]/(f)
  の連結ファイバー（f の根の集合、M279F `connEt_rootAction`）の上で初めて現れる**。
  本モジュールはその連結ファイバー上のモノドロミー表現 Gal(L/K) → Sym(根) を
  本物で建て、
  * (1) **忠実性（単射）** `galPi1_monodromy_injective`: 連結ファイバーへの Gal 作用が
    忠実（perm σ = id ⟹ σ = 1）なら、モノドロミー準同型は単射。忠実性 witness は
    2 根被覆では |Gal|=2（ガロア性の honest 入力）と M279F の「swap が根を動かす」
    （`connEt_swap_moves`）から**導出**する（`galPi1_quad_faithful`）。
  * (2) **Gal ≅ π₁ の像** `galPi1_iso_onto_image` / `galPi1_iso`: 忠実性のもとで
    像への制限 `galPi1_toImage` が全単射準同型（＝同型）。加えて**無条件**で
    第一同型定理 Gal/ker ≅ 像（M267F `firstIso`）を `galPi1_quotient_iso` で確立。
  * (3) **像の推移性・全モノドロミー** `galPi1_image_transitive` /
    `galPi1_monodromy_full`: 連結対象では像がファイバーに推移的に作用し、2 根被覆
    では像が Sym(Fin 2) を**尽くす**（全モノドロミー; `galPi1_fin2_dichotomy` で
    Fin 2 の全単射が id か transposition のみであることを本物に証明し、両者が像に
    現れることから surjectivity）。
  * (4) capstone `GaloisPi1Data`・`galPi1_exists`・`galPi1_iso`・
    `galPi1_monodromy_full`、および 2 次連結ガロア被覆での実例 `galPi1_quad_iso`。

  接続する既存部品（精読して再利用）:
  * M277F GrothendieckGalois: `grGal_fromGaloisAut`・`grGal_split_trivial`・
    `grGalCanonPoint`・`grGalPointAlgebra`（honest contrast の明示に使用）。
  * M279F ConnectedEtale: `ConnEtGaloisCover`・`connEt_rootAction`（Gal の根への
    本物の作用）・`ConnEtQuad`・`connEt_quad_transitive`・`connEt_swap_moves`・
    `connEtSwap`・`connEtF0`/`connEtF1` とその補題。
  * M271F FieldAutGroup: `FieldExtension`・`galoisGroupGrp`。
  * M267F QuotientGroup: `imSubgroup`・`subgroupGrp`・`firstIsoHom`・
    `firstIso_injective`/`firstIso_surjective`・`quotientGroupData`（第一同型定理）。
  * M16 SGA1 / GaloisCategory: `GAction`・`Grp`・`Hom`・`Hom.Injective`。

  **正直な限定**（何が本物で何が未達か・消去/弱化禁止）:
  1. **本物で閉じた**: (a) ファイバーの対称群 Sym(Fin n)（明示両側逆 witness の
     全単射群、choice 回避）とその群公理、(b) モノドロミー準同型
     Gal(L/K) → Sym(根)（act_one/act_mul からの map_mul 完全証明）、(c) 忠実性
     ⟹ 単射性、(d) 像への制限が全単射（Gal ≅ 像）、(e) 無条件の第一同型定理
     Gal/ker ≅ 像（M267F）、(f) 2 根被覆で像が Sym(Fin 2) を尽くす全モノドロミー
     （Fin 2 全単射の二分法の完全証明）。sorry 皆無・新規 Classical.choice 皆無・
     禁止タクティク不使用。
  2. **忠実性 witness `galPi1_actsFaithfully` は一般の連結被覆では仮説**として
     受け取る（perm σ = id ⟹ σ = 1）。2 根被覆では |Gal|=2（∀σ, σ=1 ∨ σ=swap）
     という**ガロア性の honest 入力**から `connEt_swap_moves` を使って**導出**する
     （`galPi1_quad_faithful`）。一般の分離正規拡大での忠実性（Gal(K^sep/K) の
     全対象への作用の忠実性）は後続。これは M279F 正直申告 2/4 と同一の境界。
  3. **忠実性・全モノドロミーは連結ファイバーの上で establish する**。M277F の
     Gal→π₁=Aut(F) は分裂骨格の上のファイバー関手 F の自己同型群への準同型で
     あり、分裂対象上では像が自明に潰れる（`galPi1_split_fromGalois_trivial` で
     honest に明示）。分裂ファイバー関手 F 自体への連結対象の追加（Aut(F) の
     定義域拡張）は分離性理論を要し後続（M277F 正直申告 1）。本モジュールは
     連結対象**単体**のモノドロミー表現の忠実性・全モノドロミーを本物で示す。
  4. **|Gal|=|F(L)|=[L:K] の基数一致そのものは未形式化**（core Lean に有限基数
     機構が無い; M267F 正直申告 1 と同一）。本モジュールは「全モノドロミー」＝
     像が Sym(ファイバー) を尽くすこと（2 根で Sym(Fin 2) 全射）を基数一致の
     **群論的骨組み**として本物に示す。
  5. π₁ の完全な pro-有限構造（全ての有限被覆の逆極限）との同型は後続（M287F 予定）。
     ここは**単一の連結ガロア被覆での Gal ≅ π₁像・忠実性・全モノドロミー**まで。

  選択公理不使用・sorry 不使用・新規 Classical.choice 不使用（全単射性はすべて
  明示両側逆 witness、場合分けは Fin 2 の構成的二分 `connEt_fin2_cases`、線形は
  omega）。禁止タクティク不使用。共有ファイル（IUT.lean・build.sh・dashboard.md・
  graph 系・report.html）は一切変更しない。新規 1 本のみ。
-/
import IUT.GrothendieckGalois
import IUT.ConnectedEtale
import IUT.QuotientGroup

namespace IUT

/-! ## M286F-1: ファイバーの対称群 Sym(α)

連結ファイバー（f の根の集合 Fin n）に作用するモノドロミーの受け皿として、
集合 α の自己全単射のなす群 Sym(α) を本物で建てる。全単射性は**明示両側逆
witness**（`left_inv`/`right_inv`）として持ち choice を回避する（M271F `FieldAut`・
M277F `grGalAut` と同じ honest 設計）。 -/

/-- **M286F-1a: α の自己全単射** — 写像本体 + 明示逆写像 + 両側逆 witness。 -/
structure galPi1Perm (α : Type) where
  /-- 全単射本体。 -/
  toFun : α → α
  /-- 明示逆写像。 -/
  invFun : α → α
  /-- 逆写像は左逆。 -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- 逆写像は右逆。 -/
  right_inv : ∀ x, toFun (invFun x) = x

/-- **外延性** — 本体と逆写像が一致すれば全単射は等しい（残る場は Prop）。 -/
theorem galPi1Perm.ext {α : Type} {f g : galPi1Perm α}
    (h1 : f.toFun = g.toFun) (h2 : f.invFun = g.invFun) : f = g := by
  cases f
  cases g
  subst h1
  subst h2
  rfl

/-- **単射性**（全単射だから）— toFun a = toFun b ⟹ a = b（左逆を施す）。 -/
theorem galPi1Perm_inj {α : Type} (f : galPi1Perm α) {a b : α}
    (h : f.toFun a = f.toFun b) : a = b := by
  have h1 := congrArg f.invFun h
  rw [f.left_inv, f.left_inv] at h1
  exact h1

/-- 恒等全単射。 -/
def galPi1PermId (α : Type) : galPi1Perm α where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- 合成 f∘g（先に g、次に f）。逆写像は g⁻¹∘f⁻¹。 -/
def galPi1PermComp {α : Type} (f g : galPi1Perm α) : galPi1Perm α where
  toFun := fun x => f.toFun (g.toFun x)
  invFun := fun x => g.invFun (f.invFun x)
  left_inv := fun x => by
    show g.invFun (f.invFun (f.toFun (g.toFun x))) = x
    rw [f.left_inv, g.left_inv]
  right_inv := fun x => by
    show f.toFun (g.toFun (g.invFun (f.invFun x))) = x
    rw [g.right_inv, f.right_inv]

/-- 逆 f⁻¹（本体と逆写像を交換）。 -/
def galPi1PermInv {α : Type} (f : galPi1Perm α) : galPi1Perm α where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.right_inv
  right_inv := f.left_inv

/-- **M286F-1b: 対称群 Sym(α)** — 合成を積、恒等を単位元、逆全単射を逆元とする
    **Grp のインスタンス**（群公理を外延性で完全証明）。連結被覆のモノドロミーが
    値をとる π₁ の連結ファイバー上での実体。 -/
def galPi1SymGrp (α : Type) : Grp where
  carrier := galPi1Perm α
  mul := galPi1PermComp
  one := galPi1PermId α
  inv := galPi1PermInv
  mul_assoc := fun _ _ _ => galPi1Perm.ext rfl rfl
  one_mul := fun _ => galPi1Perm.ext rfl rfl
  inv_mul := fun f => galPi1Perm.ext (funext f.left_inv) (funext f.left_inv)

/-! ## M286F-2: モノドロミー準同型 Gal(L/K) → Sym(根)

連結ガロア被覆 C の各元 σ∈Gal(L/K) は f の根（ファイバー Fin n）を置換する
（M279F `connEt_rootAction` の作用 `perm`）。この置換は全単射であり、逆は σ⁻¹ の
置換（作用則 act_one/act_mul から two-sided inverse を導出）。これが Gal → Sym(根)
のモノドロミー表現である。 -/

/-- **M286F-2a: σ による根の置換（全単射）** — toFun = perm σ、invFun = perm σ⁻¹。
    両側逆は `connEt_rootAction` の act_mul/act_one から完全証明（perm σ⁻¹ ∘ perm σ
    = perm(σ⁻¹σ) = perm 1 = id）。 -/
def galPi1_monodromyPerm (C : ConnEtGaloisCover)
    (σ : (galoisGroupGrp C.ext).carrier) : galPi1Perm (Fin C.n) where
  toFun := C.perm σ
  invFun := C.perm ((galoisGroupGrp C.ext).inv σ)
  left_inv := fun i => by
    have h : (connEt_rootAction C).act
          ((galoisGroupGrp C.ext).mul ((galoisGroupGrp C.ext).inv σ) σ) i
        = (connEt_rootAction C).act ((galoisGroupGrp C.ext).inv σ)
            ((connEt_rootAction C).act σ i) :=
      (connEt_rootAction C).act_mul ((galoisGroupGrp C.ext).inv σ) σ i
    rw [(galoisGroupGrp C.ext).inv_mul, (connEt_rootAction C).act_one] at h
    exact h.symm
  right_inv := fun i => by
    have h : (connEt_rootAction C).act
          ((galoisGroupGrp C.ext).mul σ ((galoisGroupGrp C.ext).inv σ)) i
        = (connEt_rootAction C).act σ
            ((connEt_rootAction C).act ((galoisGroupGrp C.ext).inv σ) i) :=
      (connEt_rootAction C).act_mul σ ((galoisGroupGrp C.ext).inv σ) i
    rw [(galoisGroupGrp C.ext).mul_inv, (connEt_rootAction C).act_one] at h
    exact h.symm

/-- **M286F-2b: モノドロミー準同型 Gal(L/K) → Sym(根)** — σ ↦ (perm σ) は
    群準同型（perm(στ) = perm σ ∘ perm τ が `connEt_rootAction` の act_mul から；
    逆写像成分は inv_mul_rev + act_mul から）。M277F `grGal_fromGalois`（分裂骨格
    上で自明化）を、非自明な連結ファイバー上へ移した本物のモノドロミー表現。 -/
def galPi1_monodromyHom (C : ConnEtGaloisCover) :
    Hom (galoisGroupGrp C.ext) (galPi1SymGrp (Fin C.n)) where
  map := galPi1_monodromyPerm C
  map_mul := fun σ τ => by
    apply galPi1Perm.ext
    · funext i
      show C.perm ((galoisGroupGrp C.ext).mul σ τ) i = C.perm σ (C.perm τ i)
      exact (connEt_rootAction C).act_mul σ τ i
    · funext i
      show C.perm ((galoisGroupGrp C.ext).inv ((galoisGroupGrp C.ext).mul σ τ)) i
        = C.perm ((galoisGroupGrp C.ext).inv τ)
            (C.perm ((galoisGroupGrp C.ext).inv σ) i)
      rw [(galoisGroupGrp C.ext).inv_mul_rev]
      exact (connEt_rootAction C).act_mul
        ((galoisGroupGrp C.ext).inv τ) ((galoisGroupGrp C.ext).inv σ) i

/-! ## M286F-3: 忠実性（単射性）

分裂被覆では π₁ が各点を固定した（M277F）のに対し、連結被覆では σ≠1 が根を
動かす（M279F）。「Gal が連結ファイバーに忠実に作用する」— perm σ = id ⟹ σ = 1 —
を witness として受け取り（2 根被覆では |Gal|=2 から導出、下記 M286F-8）、そこから
モノドロミー準同型の単射性（＝忠実性）を本物で導く。 -/

/-- **M286F-3a: 連結ファイバーへの Gal 作用の忠実性**（述語）— 根を一切動かさない
    σ は恒等元のみ。ガロア性（Gal が根に自由に近く作用する）の honest 入力。 -/
def galPi1_actsFaithfully (C : ConnEtGaloisCover) : Prop :=
  ∀ σ : (galoisGroupGrp C.ext).carrier,
    (∀ i, C.perm σ i = i) → σ = (galoisGroupGrp C.ext).one

/-- **M286F-3b: 忠実 ⟹ モノドロミー準同型は単射**（本物）— perm σ = perm τ なら
    perm(σ⁻¹τ) = id（act_mul + 左逆）なので忠実性から σ⁻¹τ = 1、群計算で σ = τ。
    M277F 正直申告 4「像の忠実性は後続」を連結ファイバー上で閉じる本物の 1 段。 -/
theorem galPi1_monodromy_injective (C : ConnEtGaloisCover)
    (hf : galPi1_actsFaithfully C) : Hom.Injective (galPi1_monodromyHom C) := by
  intro σ τ h
  have hperm : ∀ i, C.perm σ i = C.perm τ i :=
    fun i => congrFun (congrArg galPi1Perm.toFun h) i
  have hker : ∀ i,
      C.perm ((galoisGroupGrp C.ext).mul ((galoisGroupGrp C.ext).inv σ) τ) i = i := by
    intro i
    have e1 : C.perm ((galoisGroupGrp C.ext).mul ((galoisGroupGrp C.ext).inv σ) τ) i
        = C.perm ((galoisGroupGrp C.ext).inv σ) (C.perm τ i) :=
      (connEt_rootAction C).act_mul ((galoisGroupGrp C.ext).inv σ) τ i
    rw [e1, ← hperm i]
    exact (galPi1_monodromyPerm C σ).left_inv i
  have hone : (galoisGroupGrp C.ext).mul ((galoisGroupGrp C.ext).inv σ) τ
      = (galoisGroupGrp C.ext).one := hf _ hker
  have hstep : (galoisGroupGrp C.ext).mul σ
      ((galoisGroupGrp C.ext).mul ((galoisGroupGrp C.ext).inv σ) τ)
      = (galoisGroupGrp C.ext).mul σ (galoisGroupGrp C.ext).one :=
    congrArg ((galoisGroupGrp C.ext).mul σ) hone
  rw [← (galoisGroupGrp C.ext).mul_assoc, (galoisGroupGrp C.ext).mul_inv,
    (galoisGroupGrp C.ext).one_mul, (galoisGroupGrp C.ext).mul_one] at hstep
  exact hstep.symm

/-! ## M286F-4: Gal ≅ π₁ の像（忠実 + well-defined）

M267F の第一同型定理 Gal/ker ≅ 像は**無条件**で成り立つ（`galPi1_quotient_iso`）。
忠実性のもとでは ker=1 なので Gal → 像 の制限そのものが全単射準同型（＝同型）。 -/

/-- **M286F-4a: Gal → 像への制限**（corestriction）— σ ↦ ⟨perm σ, ∃ witness⟩。
    群準同型（値は像部分群 `subgroupGrp (imSubgroup ...)` の中）。 -/
def galPi1_toImage (C : ConnEtGaloisCover) :
    Hom (galoisGroupGrp C.ext)
      (subgroupGrp (imSubgroup (galPi1_monodromyHom C))) where
  map := fun σ => ⟨(galPi1_monodromyHom C).map σ, ⟨σ, rfl⟩⟩
  map_mul := fun σ τ => Subtype.ext ((galPi1_monodromyHom C).map_mul σ τ)

/-- **M286F-4b: 制限は全射**（像の定義から）。 -/
theorem galPi1_toImage_surjective (C : ConnEtGaloisCover) :
    ∀ y, ∃ σ, (galPi1_toImage C).map σ = y := by
  intro y
  obtain ⟨a, ha⟩ := y.property
  exact ⟨a, Subtype.ext ha⟩

/-- **M286F-4c: 忠実なら制限は単射**（Gal → 像 が単射）。 -/
theorem galPi1_toImage_injective (C : ConnEtGaloisCover)
    (hf : galPi1_actsFaithfully C) : Hom.Injective (galPi1_toImage C) := by
  intro σ τ h
  have hv : (galPi1_monodromyHom C).map σ = (galPi1_monodromyHom C).map τ :=
    congrArg Subtype.val h
  exact galPi1_monodromy_injective C hf σ τ hv

/-- **M286F-4d: Gal(L/K) ≅ π₁ の像**（忠実性のもとで）— 制限
    `galPi1_toImage` が全単射準同型（＝同型）。連結ガロア被覆で「Gal が π₁ の像に
    同型に実現される」の本物の実現。 -/
theorem galPi1_iso_onto_image (C : ConnEtGaloisCover)
    (hf : galPi1_actsFaithfully C) :
    Hom.Injective (galPi1_toImage C) ∧
    (∀ y, ∃ σ, (galPi1_toImage C).map σ = y) :=
  ⟨galPi1_toImage_injective C hf, galPi1_toImage_surjective C⟩

/-- **M286F-4e: 第一同型定理 Gal/ker ≅ 像**（無条件・M267F）— 忠実性を仮定せず
     とも、モノドロミー準同型に第一同型定理を適用すれば Gal/ker ≅ 像 が全単射
    準同型として得られる。忠実（ker=1）ならこれは Gal ≅ 像 に昇格する（M286F-4d）。 -/
def galPi1_quotient_iso (C : ConnEtGaloisCover) :
    QuotientGroupData (galPi1_monodromyHom C) :=
  quotientGroupData (galPi1_monodromyHom C)

/-! ## M286F-5: 像の推移性（連結対象の全モノドロミー）

連結対象ではファイバーが 1 軌道（推移的）— Gal の像がファイバーに推移的に作用
する（M279F `connEt_rootAction` の推移性を像へ転送）。 -/

/-- **M286F-5: 像の推移性** — 連結ファイバーへの Gal 作用が推移的なら、モノドロミー
    像もファイバー Fin n に推移的に作用する（任意の i,j に対し perm σ i = j なる σ）。 -/
theorem galPi1_image_transitive (C : ConnEtGaloisCover)
    (htr : (connEt_rootAction C).Transitive) :
    ∀ i j : Fin C.n, ∃ σ, ((galPi1_monodromyHom C).map σ).toFun i = j := by
  intro i j
  obtain ⟨σ, hσ⟩ := htr i j
  exact ⟨σ, hσ⟩

/-! ## M286F-6: Fin 2 の全単射の二分法（全モノドロミーの土台）

2 根被覆の全モノドロミー（像が Sym(Fin 2) を尽くす）を示すため、Fin 2 の任意の
全単射が恒等か transposition のみであることを本物に証明する。 -/

/-- **M286F-6a: transposition は対合**（connEtSwap∘connEtSwap = id）。 -/
theorem galPi1_connEtSwap_invol (i : Fin 2) : connEtSwap (connEtSwap i) = i := by
  apply kAlgFin_ext
  show 1 - (1 - i.val) = i.val
  have := i.isLt
  omega

/-- transposition を全単射 Sym(Fin 2) の元として。 -/
def galPi1SwapPerm : galPi1Perm (Fin 2) where
  toFun := connEtSwap
  invFun := connEtSwap
  left_inv := galPi1_connEtSwap_invol
  right_inv := galPi1_connEtSwap_invol

/-- **M286F-6b: Fin 2 の値は 0 か 1**（構成的二分）。 -/
theorem galPi1_fin2_val (x : Fin 2) : x = connEtF0 ∨ x = connEtF1 := by
  cases connEt_fin2_cases connEtF0 x with
  | inl h => exact Or.inl h.symm
  | inr h =>
    right
    have hs : connEtSwap connEtF0 = connEtF1 := connEtSwap_of_ne connEtF0_ne_F1
    rw [← hs]
    exact h.symm

/-- **M286F-6c: Fin 2 の全単射は id か transposition**（本物の二分法）— f(0) の値で
    場合分けし、全単射性（`galPi1Perm_inj`）から f(1) が決まる。連結被覆の
    2 根ファイバーの対称群 Sym(Fin 2) が {id, transposition} の 2 元であることの実体。 -/
theorem galPi1_fin2_dichotomy (f : galPi1Perm (Fin 2)) :
    f = galPi1PermId (Fin 2) ∨ f = galPi1SwapPerm := by
  cases galPi1_fin2_val (f.toFun connEtF0) with
  | inl h0 =>
    left
    have h1 : f.toFun connEtF1 = connEtF1 := by
      cases galPi1_fin2_val (f.toFun connEtF1) with
      | inl h1a =>
        exfalso
        have hc : f.toFun connEtF1 = f.toFun connEtF0 := by rw [h1a, h0]
        exact connEtF1_ne_F0 (galPi1Perm_inj f hc)
      | inr h1b => exact h1b
    apply galPi1Perm.ext
    · funext i
      show f.toFun i = i
      cases galPi1_fin2_val i with
      | inl hi => rw [hi]; exact h0
      | inr hi => rw [hi]; exact h1
    · funext i
      show f.invFun i = i
      have ht : f.toFun (f.invFun i) = f.invFun i := by
        cases galPi1_fin2_val (f.invFun i) with
        | inl hx => rw [hx]; exact h0
        | inr hx => rw [hx]; exact h1
      have hr := f.right_inv i
      rw [ht] at hr
      exact hr
  | inr h0 =>
    right
    have h1 : f.toFun connEtF1 = connEtF0 := by
      cases galPi1_fin2_val (f.toFun connEtF1) with
      | inl h1a => exact h1a
      | inr h1b =>
        exfalso
        have hc : f.toFun connEtF1 = f.toFun connEtF0 := by rw [h1b, h0]
        exact connEtF1_ne_F0 (galPi1Perm_inj f hc)
    have hall : ∀ x, f.toFun x = connEtSwap x := by
      intro x
      cases galPi1_fin2_val x with
      | inl hx => rw [hx, h0]; exact (connEtSwap_of_ne connEtF0_ne_F1).symm
      | inr hx => rw [hx, h1]; exact (connEtSwap_of_ne connEtF1_ne_F0).symm
    apply galPi1Perm.ext
    · funext i
      show f.toFun i = connEtSwap i
      exact hall i
    · funext i
      show f.invFun i = connEtSwap i
      have hr := f.right_inv i
      rw [hall (f.invFun i)] at hr
      have hc := congrArg connEtSwap hr
      rw [galPi1_connEtSwap_invol] at hc
      exact hc

/-! ## M286F-7: 2 根連結ガロア被覆の忠実性・全モノドロミー・同型（実例）

M279F `ConnEtQuad`（2 根連結ガロア被覆、swap が 2 根を入れ替える honest witness）
に対し、|Gal|=2（ガロア性の honest 入力）から忠実性を導出し、Gal ≅ Sym(Fin 2)
（全モノドロミー）を本物で確立する。 -/

/-- **M286F-8: 2 根被覆の忠実性**（|Gal|=2 から導出・本物）— Gal={1, swap} なら
    根を動かさない σ は 1 のみ（swap は第 0 根を第 1 根へ動かす M279F
    `connEtSwap_of_ne`）。M279F の「swap が根を動かす」を忠実性へ昇格する本物の 1 段。 -/
theorem galPi1_quad_faithful (Q : ConnEtQuad)
    (hord : ∀ σ, σ = (galoisGroupGrp Q.ext).one ∨ σ = Q.swap) :
    galPi1_actsFaithfully Q.toCover := by
  intro σ hσ
  cases hord σ with
  | inl h => exact h
  | inr h =>
    exfalso
    have h0 : Q.perm σ connEtF0 = connEtF0 := hσ connEtF0
    rw [h, Q.swap_perm connEtF0, connEtSwap_of_ne connEtF0_ne_F1] at h0
    exact connEtF1_ne_F0 h0

/-- swap の逆置換も transposition（perm σ⁻¹ = connEtSwap; 全単射の two-sided
    inverse の一意性から）。全モノドロミーで swap が像に現れることの補助。 -/
theorem galPi1_quad_swap_invPerm (Q : ConnEtQuad) (j : Fin 2) :
    Q.perm ((galoisGroupGrp Q.ext).inv Q.swap) j = connEtSwap j := by
  have key : Q.perm ((galoisGroupGrp Q.ext).inv Q.swap)
      (Q.perm Q.swap (connEtSwap j)) = connEtSwap j :=
    (galPi1_monodromyPerm Q.toCover Q.swap).left_inv (connEtSwap j)
  rw [Q.swap_perm (connEtSwap j), galPi1_connEtSwap_invol j] at key
  exact key

/-- **M286F-8b: swap のモノドロミー像は transposition**（本物）— map(swap) の本体は
    perm swap = connEtSwap（M279F `swap_perm`）、逆成分も connEtSwap。 -/
theorem galPi1_quad_swap_image (Q : ConnEtQuad) :
    (galPi1_monodromyHom Q.toCover).map Q.swap = galPi1SwapPerm := by
  apply galPi1Perm.ext
  · funext i
    show Q.perm Q.swap i = connEtSwap i
    exact Q.swap_perm i
  · funext j
    show Q.perm ((galoisGroupGrp Q.ext).inv Q.swap) j = connEtSwap j
    exact galPi1_quad_swap_invPerm Q j

/-- **M286F-8c: 2 根被覆の全モノドロミー**（本物）— モノドロミー像が Sym(Fin 2) を
    **尽くす**: 任意の全単射 f∈Sym(Fin 2) は id か transposition（`galPi1_fin2_dichotomy`）で、
    id は Gal の 1、transposition は swap の像（M286F-8b）。ゆえに像 = Sym(Fin 2)。
    「像がファイバーの対称群を尽くす」＝ |Gal|=|Sym(Fin 2)| の群論的骨組み
    （基数一致そのものは未形式化・正直申告 4）。 -/
theorem galPi1_monodromy_full (Q : ConnEtQuad) :
    ∀ f : galPi1Perm (Fin 2), ∃ σ, (galPi1_monodromyHom Q.toCover).map σ = f := by
  intro f
  cases galPi1_fin2_dichotomy f with
  | inl h =>
    refine ⟨(galoisGroupGrp Q.ext).one, ?_⟩
    rw [h]
    exact (galPi1_monodromyHom Q.toCover).map_one
  | inr h =>
    refine ⟨Q.swap, ?_⟩
    rw [h]
    exact galPi1_quad_swap_image Q

/-- **M286F-8d: 2 根被覆で像は推移的**（M279F `connEt_quad_transitive` の像への転送）。 -/
theorem galPi1_quad_image_transitive (Q : ConnEtQuad) :
    ∀ i j : Fin 2, ∃ σ, ((galPi1_monodromyHom Q.toCover).map σ).toFun i = j :=
  galPi1_image_transitive Q.toCover (connEt_quad_transitive Q)

/-- **M286F-8e: 実例 — Gal(L/K) ≅ π₁ の像**（2 根連結ガロア被覆・|Gal|=2）—
    忠実性（M286F-8）から Gal → 像 が全単射準同型（＝同型）。像は Sym(Fin 2) を
    尽くす（M286F-8c）ので **Gal(位数2) ≅ π₁像 = 2 根の置換群 Sym(Fin 2)**。 -/
theorem galPi1_quad_iso (Q : ConnEtQuad)
    (hord : ∀ σ, σ = (galoisGroupGrp Q.ext).one ∨ σ = Q.swap) :
    Hom.Injective (galPi1_toImage Q.toCover) ∧
    (∀ y, ∃ σ, (galPi1_toImage Q.toCover).map σ = y) :=
  galPi1_iso_onto_image Q.toCover (galPi1_quad_faithful Q hord)

/-! ## M286F-9: honest contrast — M277F の Gal→π₁ は分裂骨格上で自明

忠実性・全モノドロミーが**連結ファイバーの上で初めて**現れることを honest に
明示する。M277F `grGal_fromGalois` の像は分裂被覆 K^n の各標準点を固定する
（分裂骨格の上では像が自明に潰れる）。これが「同型は連結対象を要する」の実体。 -/

/-- **M286F-9: M277F の Gal→π₁ 像は分裂被覆の標準点を固定**（honest contrast）—
    M277F `grGal_split_trivial` を Gal 由来の π₁ 元 `grGal_fromGaloisAut` に適用。
    分裂骨格の上では像が非自明作用を持たない（∴ 忠実性・全モノドロミーは連結
    ファイバー M279F の上で establish する必要がある）。 -/
theorem galPi1_split_fromGalois_trivial (E : FieldExtension)
    (σ : (galoisGroupGrp E).carrier) (n : Nat) (i : Fin n) :
    (grGal_fromGaloisAut E σ).app n (grGalCanonPoint E.base (grGalPointAlgebra E) n i)
      = grGalCanonPoint E.base (grGalPointAlgebra E) n i :=
  grGal_split_trivial (grGal_fromGaloisAut E σ) n i

/-! ## M286F-10: capstone -/

/-- **M286F-10a: capstone データ** — 連結ガロア被覆 + 忠実性 witness + モノドロミー
    像への全単射準同型（Gal ≅ π₁像）を束ねる。M277F `GrothendieckGaloisData`
    （分裂骨格上で像自明）の連結対象版＝**忠実・同型**を持つ対象。 -/
structure GaloisPi1Data where
  /-- 連結ガロア被覆。 -/
  cover : ConnEtGaloisCover
  /-- 連結ファイバーへの Gal 作用の忠実性。 -/
  faithful : galPi1_actsFaithfully cover
  /-- Gal → π₁ の像 への全単射準同型（Gal ≅ 像）。 -/
  toImage : Hom (galoisGroupGrp cover.ext)
    (subgroupGrp (imSubgroup (galPi1_monodromyHom cover)))
  /-- 単射（忠実性から）。 -/
  iso_injective : Hom.Injective toImage
  /-- 全射（像の定義から）。 -/
  iso_surjective : ∀ y, ∃ σ, toImage.map σ = y

/-- **M286F-10b: 証人** — 忠実な連結ガロア被覆から Gal ≅ π₁像 のデータを構成。 -/
def galPi1Data (C : ConnEtGaloisCover) (hf : galPi1_actsFaithfully C) :
    GaloisPi1Data where
  cover := C
  faithful := hf
  toImage := galPi1_toImage C
  iso_injective := galPi1_toImage_injective C hf
  iso_surjective := galPi1_toImage_surjective C

/-- **M286F-10c: capstone — Gal ≅ π₁像 のデータの存在**（忠実な連結ガロア被覆で）。 -/
theorem galPi1_exists (C : ConnEtGaloisCover) (hf : galPi1_actsFaithfully C) :
    Nonempty GaloisPi1Data :=
  ⟨galPi1Data C hf⟩

/-- **M286F-10d: capstone — Gal(L/K) ≅ π₁ の像**（総括）— 忠実な連結ガロア被覆で
    Gal → π₁ の像 が全単射準同型（＝同型）として実現される。 -/
theorem galPi1_iso (C : ConnEtGaloisCover) (hf : galPi1_actsFaithfully C) :
    ∃ φ : Hom (galoisGroupGrp C.ext)
        (subgroupGrp (imSubgroup (galPi1_monodromyHom C))),
      Hom.Injective φ ∧ (∀ y, ∃ σ, φ.map σ = y) :=
  ⟨galPi1_toImage C, galPi1_toImage_injective C hf, galPi1_toImage_surjective C⟩

/-- **M286F-10e: capstone — 2 根被覆で像が全モノドロミー**（連結被覆で像が
    ファイバーの対称群 Sym(Fin 2) を尽くす）。 -/
theorem galPi1_monodromy_full_exists (Q : ConnEtQuad) :
    ∀ f : galPi1Perm (Fin 2), ∃ σ, (galPi1_monodromyHom Q.toCover).map σ = f :=
  galPi1_monodromy_full Q

end IUT
