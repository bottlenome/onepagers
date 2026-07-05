/-
  IUT/ConnectedEtale.lean — M279F: 連結（非分裂）有限エタール対象と π₁/Gal の
  非自明作用
  ── 柱A 実 π₁^ét(Spec K) 非自明化の本丸（連結対象＝体拡大上での Gal の
     非自明推移作用）の本物の先行建設

  分類 **[実]**（本物の体拡大 K[X]/(f)＝連結対象・本物の Gal(L/K) の本物の
  根への作用・本物の非自明性/推移性。toy 群・surrogate を主語にしない）。

  **complete_pct 影響: 柱A 実 π₁^ét の非自明化の本物の先行建設**。
  M277F `grGal_split_trivial` は「分裂被覆 K^n のモノドロミーは自明」＝
  「分裂対象だけでは π₁^ét は（古典論理では）自明群に潰れる」という本物の
  定理だった。本モジュールはこれを**乗り越える**: 連結対象（＝体拡大
  L = K[X]/(f), f 既約）を導入し、その上で **Gal(L/K) がファイバー（f の根の
  集合）に非自明かつ推移的に作用する**ことを本物で確立する。すなわち
  * (1) **連結体拡大の連結性**（`connEt_simpleExt_connected`）: M269F の本物の
    体拡大 K[X]/(f)（`SimpleFieldExt`）が M280F の意味で連結（非零冪等元は 1）。
    ∃ 形逆元（体性）から直接、排中律なしで導出する。
  * (2) **連結対象のファイバーへの Gal 作用**（`connEt_rootAction`）: 分裂被覆
    では π₁ が各標準点を固定する（M277F）のに対し、連結被覆では Gal が根を
    置換する。Gal が根を置換するという Galois 被覆の本物の性質を witness で
    受け取り、そこから本物の GAction（作用則 e·x=x, (gh)·x=g·(h·x) を
    根の相異性から完全証明）を構成する。作用の単位則・結合則は仮定でなく
    **根の相異性から導出**する（本物）。
  * (3) **非自明性**（`connEt_swap_ne_one`）: 2 根を入れ替える σ∈Gal(L/K) は
    Gal の恒等元でない（σ(ρ₀)=ρ₁≠ρ₀）。M277F の「分裂だけでは π₁ 自明」を
    破る本物の 1 段。
  * (4) **推移性**（`connEt_cosetAction_transitive`＝任意部分群の剰余類作用は
    推移的・本物; `connEt_quad_transitive`＝2 根被覆のファイバー上で推移的;
    `connEt_fiber_cosetModel`＝軌道-安定化で連結ファイバー ≅ Gal/Stab）。
  * (5) capstone `ConnectedEtaleData`（連結対象＋埋め込み＋連結性＋非自明性）・
    `ConnectedActionData`（連結ファイバー＋推移作用＋非自明作用）・
    `connEt_exists`・`connEt_nontrivial_action_exists`、および実例（2 根の
    非自明入れ替えを持つ 2 次被覆の witness からの構成）。

  接続する既存部品:
  * M280F IdempotentSpectrum: `idemSpec_connected`（連結性の witness 形）・
    `idemSpec_isIdem`。連結性定義を再利用（重複定義しない）。
  * M269F SimpleExtension: `SimpleFieldExt`/`SimpleExtData`/`.build`（本物の
    体拡大 K[X]/(f) と ∃ 形逆元 `has_inverses`）。
  * M271F FieldAutGroup: `FieldExtension`・`FieldAut`・`galoisSubgroup`・
    `galoisGroupGrp`（本物の Gal(L/K)）。
  * M16/M14 SGA1/GaloisCategory: `GAction`・`GAction.Transitive`・`cosetAction`・
    `stabilizer`・`orbit_stabilizer`・`ActHom`。

  **正直な限定**（何が本物で何が未達か・消去/弱化禁止）:
  1. **本物**: (a) 連結体拡大 K[X]/(f) の連結性（∃ 形逆元からの非零冪等元＝1）、
     (b) Gal が根に作用する GAction の作用則（根の相異性からの単位則・結合則の
     完全証明）、(c) 2 根入れ替え σ の Gal 恒等元でないこと、(d) 剰余類作用の
     推移性・2 根ファイバーの推移性・軌道安定化での Gal/Stab 同定は全て完全
     証明（sorry 皆無・新規 Classical.choice 皆無・禁止タクティク不使用）。
  2. **「ガロア被覆」の分解 witness は仮説で受け取る**（`ConnEtGaloisCover`/
     `ConnEtQuad` の `root`/`perm`/`perm_spec`/`swap`）: f が L 上で分解する
     こと（根の族）・Gal が根を置換すること・2 根入れ替え σ の存在は honest
     仮説として持つ。これは M271F（非自明 Gal は自明拡大のみ完全証明）・
     M277F（`grGal_fromGalois` は E:FieldExtension を仮説で受け取る）と同一の
     honest イディオムである。**根の置換写像 `perm` の単位則/結合則は仮定でなく
     根の相異性から導出**しており、作用そのものは本物。分離閉包の一般構成
     （実分離拡大からの根の族の生成・二次拡大体の実 involution の構成）は後続。
  3. **推移性は具体的な根の置換（2 根 Fin 2 の transposition）で示す**。一般の
     抽象ガロア理論全体（Gal(K^sep/K) の各連結対象への推移性）は後続。少なくとも
     2 根の非自明入れ替えを本物で構成し、π₁ 非自明性の核を立てる。
  4. **Gal → π₁ = Aut(F) への転送と像の非自明性は後続**。本モジュールは
     **Gal(L/K) 自身が連結ファイバーに非自明に作用する**ことを本物で示す。
     M277F `grGal_fromGalois` で Gal → π₁ の準同型は既に本物にあるが、その像が
     π₁ の中で非自明（＝忠実性）は分離正規性が要り後続（M277F 正直申告 4）。
  5. π₁ の完全な pro-有限構造・Gal(K^sep/K) との同型は後続。ここは連結対象上の
     **非自明・推移作用の存在**まで。

  選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。禁止タクティク
  不使用（場合分けは Decidable witness の構成的分解 `kAlgDecEm`、線形は omega）。
  共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系・report.html）は
  一切変更しない。新規 1 本のみ。
-/
import IUT.IdempotentSpectrum
import IUT.FieldAutGroup
import IUT.SimpleExtension
import IUT.SGA1

namespace IUT

/-! ## M279F-1: ∃ 形逆元（体性）からの連結性

M280F `idemSpec_field_is_connected` は全域 inv を持つ `IUTField` にしか使えない
が、M269F の体拡大 K[X]/(f) は ∃ 形逆元（`has_inverses`）しか持たない（全域 inv
の昇格は選択原理を要するため M269F では honest に ∃ 形で止めている）。そこで
**∃ 形逆元から直接、非零冪等元が 1 であること**を排中律なしで導出する。 -/

/-- **M279F-1a: ∃ 形逆元の性質**（体性の構成的形; M269F `has_inverses` と同型）。 -/
def connEt_hasInverses (R : CRing) : Prop :=
  ∀ x : R.carrier, x ≠ R.zero → ∃ y, R.mul x y = R.one

/-- **M279F-1b: ∃ 形逆元 ⟹ 連結**（本物の核）— 非零冪等元 e は逆元 y を持ち、
    e = e·1 = e·(e·y) = (e·e)·y = e·y = 1。よって Spec R の開閉部分は自明のみ
    ＝連結（M280F `idemSpec_connected` の witness 形をそのまま満たす）。排中律・
    選択公理不使用。 -/
theorem connEt_hasInv_connected (R : CRing) (h : connEt_hasInverses R) :
    idemSpec_connected R := by
  intro e he hne
  have he' : R.mul e e = e := he
  obtain ⟨y, hy⟩ := h e hne
  have h1 : R.mul (R.mul e e) y = R.mul e y := by rw [he']
  rw [R.mul_assoc, hy, R.mul_comm e R.one, R.one_mul] at h1
  exact h1

/-! ## M279F-2: 連結体拡大 K[X]/(f) — 連結有限エタール対象の本物 -/

/-- **M279F-2a: 単純体拡大は連結**（本物の連結対象）— M269F の本物の体拡大
    K[X]/(f)（`SimpleFieldExt`）は M280F の意味で連結。体（連結）＝ Spec が 1 点
    の環論的実体を、実際の体拡大環に対して確立する。分裂 K^n（n≥2）が非連結
    （M280F `idemSpec_split_disconnected`）だったのと対照的に、L=K[X]/(f) は
    連結＝ FÉt(K) の**連結対象**（＝非分裂対象）である。 -/
theorem connEt_simpleExt_connected (K : Field268) (d : SimpleExtData K) :
    idemSpec_connected (SimpleExtData.build K d).ring :=
  connEt_hasInv_connected (SimpleExtData.build K d).ring
    (SimpleExtData.build K d).has_inverses

/-- **M279F-2b: 連結有限エタール対象のデータ** — 基礎体 K の連結対象（連結な
    K-代数 = 体拡大）を、台環・埋め込み・連結性・非自明性で束ねる。M280F の
    `IdemSpectrumData`（分裂 = 多成分）と対をなす「1 連結成分（連結）」側。 -/
structure ConnectedEtaleData (K : Field268) where
  /-- 台の可換環（連結対象の座標環 = 体拡大 K[X]/(f)）。 -/
  obj : CRing
  /-- 基礎体の埋め込み K → obj。 -/
  emb : RingHom K.ring obj
  /-- **連結性**（非零冪等元は 1 ＝ Spec obj は連結）。 -/
  connected : idemSpec_connected obj
  /-- 非自明（1 ≠ 0）。 -/
  nontrivial : obj.one ≠ obj.zero

/-- **M279F-2c: 連結対象の構成** — 単純拡大データ（f の Bezout/既約性を honest
    仮説に持つ）から連結有限エタール対象を本物に組み上げる。 -/
def connEt_connectedEtaleData (K : Field268) (d : SimpleExtData K) :
    ConnectedEtaleData K where
  obj := (SimpleExtData.build K d).ring
  emb := (SimpleExtData.build K d).emb
  connected := connEt_simpleExt_connected K d
  nontrivial := (SimpleExtData.build K d).nontrivial

/-- **M279F-2d: 連結有限エタール対象の存在**（体拡大 K[X]/(f) が連結対象として
    存在する）。 -/
theorem connEt_exists (K : Field268) (d : SimpleExtData K) :
    Nonempty (ConnectedEtaleData K) :=
  ⟨connEt_connectedEtaleData K d⟩

/-! ## M279F-3: Fin 2 の transposition（2 根の入れ替え） -/

/-- 第 0 根の添字。 -/
def connEtF0 : Fin 2 := ⟨0, by omega⟩

/-- 第 1 根の添字。 -/
def connEtF1 : Fin 2 := ⟨1, by omega⟩

/-- 0 ≠ 1（Fin 2 の 2 点は相異なる）。 -/
theorem connEtF0_ne_F1 : connEtF0 ≠ connEtF1 := by
  intro h
  have h2 : (0 : Nat) = 1 := congrArg Fin.val h
  omega

/-- 1 ≠ 0。 -/
theorem connEtF1_ne_F0 : connEtF1 ≠ connEtF0 := fun h => connEtF0_ne_F1 h.symm

/-- **transposition** σ : Fin 2 → Fin 2（0↔1 の入れ替え、i ↦ 1−i）。 -/
def connEtSwap (i : Fin 2) : Fin 2 := ⟨1 - i.val, by omega⟩

/-- **transposition は相異なる 2 点を入れ替える** — i ≠ j なら swap i = j
    （Fin 2 では {i,j}={0,1} ゆえ 1−i = j）。omega による線形計算。 -/
theorem connEtSwap_of_ne {i j : Fin 2} (h : i ≠ j) : connEtSwap i = j := by
  apply kAlgFin_ext
  show 1 - i.val = j.val
  have hi : i.val < 2 := i.isLt
  have hj : j.val < 2 := j.isLt
  have hne : i.val ≠ j.val := fun e => h (kAlgFin_ext e)
  omega

/-- **Fin 2 の二分**（排中律不使用・`Nat.decEq` の構成的分解）— 2 点 i,j は
    等しいか、transposition で入れ替わる（swap i = j）かのいずれか。 -/
theorem connEt_fin2_cases (i j : Fin 2) : i = j ∨ connEtSwap i = j := by
  cases Nat.decEq i.val j.val with
  | isTrue h => exact Or.inl (kAlgFin_ext h)
  | isFalse h => exact Or.inr (connEtSwap_of_ne (fun e => h (congrArg Fin.val e)))

/-! ## M279F-4: 連結ガロア被覆と Gal の根への本物の作用

分裂被覆 K^n では π₁ が各標準点を固定した（M277F `grGal_split_trivial`）。連結
被覆 L=K[X]/(f) では Gal(L/K) が f の根を**置換**する。f の根の族 `root : Fin n → L`
と、Gal が根を置換する事実 `perm`/`perm_spec` を honest 仮説で受け取り（分離閉包
での根の族の一般生成は後続）、そこから**本物の GAction**（作用則を根の相異性から
導出）を構成する。 -/

/-- **M279F-4a: 連結ガロア被覆の witness** — 体拡大 E=(K⊆L)、f の n 個の相異なる
    根 `root : Fin n → L`、そして Gal(L/K) の各元が根を置換する置換写像 `perm` と
    その両立 `perm_spec`（σ が第 i 根を第 perm(σ,i) 根へ送る）。root/perm/perm_spec
    は「f が L 上で分解し Gal が根を置換する」という Galois 被覆の本物の性質の
    honest witness（消さず明示; §4 準拠）。 -/
structure ConnEtGaloisCover where
  /-- 体拡大 K ⊆ L。 -/
  ext : FieldExtension
  /-- 根の枚数（ファイバーの点数）。 -/
  n : Nat
  /-- f の n 個の根（L の元 = ファイバーの点）。 -/
  root : Fin n → ext.top.carrier
  /-- 根は相異なる（分離性 = 重根なし; ファイバーは n 点）。 -/
  roots_distinct : ∀ i j, i ≠ j → root i ≠ root j
  /-- Gal(L/K) の元 σ による根の置換写像。 -/
  perm : (galoisGroupGrp ext).carrier → Fin n → Fin n
  /-- 両立: σ は第 i 根を第 perm(σ,i) 根へ送る（Gal が根を置換）。 -/
  perm_spec : ∀ (σ : (galoisGroupGrp ext).carrier) (i : Fin n),
    σ.val.toFun (root i) = root (perm σ i)

/-- **M279F-4b: Gal の根への作用**（本物の GAction）— 連結ガロア被覆の
    ファイバー Fin n に Gal(L/K) が `perm` で作用する。**作用則
    e·x=x, (gh)·x=g·(h·x) を仮定せず、根の相異性 `roots_distinct` と両立
    `perm_spec` から完全証明**する（これが「本物の作用」の核心）。 -/
def connEt_rootAction (C : ConnEtGaloisCover) : GAction (galoisGroupGrp C.ext) where
  carrier := Fin C.n
  act := C.perm
  act_one := fun i => by
    have hs : C.root i = C.root (C.perm (galoisGroupGrp C.ext).one i) :=
      C.perm_spec (galoisGroupGrp C.ext).one i
    cases kAlgDecEm (C.perm (galoisGroupGrp C.ext).one i = i) with
    | inl h => exact h
    | inr h => exact absurd hs.symm (C.roots_distinct _ _ h)
  act_mul := fun g h i => by
    have hgh : g.val.toFun (h.val.toFun (C.root i))
        = C.root (C.perm ((galoisGroupGrp C.ext).mul g h) i) :=
      C.perm_spec ((galoisGroupGrp C.ext).mul g h) i
    have hh := C.perm_spec h i
    have hg := C.perm_spec g (C.perm h i)
    rw [hh] at hgh
    rw [hg] at hgh
    cases kAlgDecEm
        (C.perm ((galoisGroupGrp C.ext).mul g h) i = C.perm g (C.perm h i)) with
    | inl heq => exact heq
    | inr hne => exact absurd hgh.symm (C.roots_distinct _ _ hne)

/-- **M279F-4c: Gal の L 全体への作用**（本物の GAction）— Gal(L/K) は上体 L の
    元に σ·x = σ(x) で作用する（部分群 Gal ⊆ Aut(L) の自然作用）。ファイバーの
    根はこの作用の軌道の一部。 -/
def connEt_galAction (E : FieldExtension) : GAction (galoisGroupGrp E) where
  carrier := E.top.carrier
  act := fun σ x => σ.val.toFun x
  act_one := fun _ => rfl
  act_mul := fun _ _ _ => rfl

/-! ## M279F-5: 剰余類作用の推移性（連結被覆のファイバー = G/H は推移的） -/

/-- **M279F-5: 剰余類作用は推移的**（本物・任意の部分群で成立）— 任意の群 G と
    部分群 H に対し、G/H への左移動作用は推移的（[a] から [b] へは g=b·a⁻¹ で
    到達）。Grothendieck ガロア理論の「連結被覆のファイバーは推移的 G-集合
    ＝ G/H」の群論的核心。M16 `orbit_stabilizer` と合わせ、連結対象のファイバーが
    Gal/Stab と同定される。 -/
theorem connEt_cosetAction_transitive (G : Grp) (H : Subgroup G) :
    (cosetAction G H).Transitive := by
  intro x y
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  refine ⟨G.mul b (G.inv a), ?_⟩
  show Quot.mk (cosetRel G H) (G.mul (G.mul b (G.inv a)) a)
      = Quot.mk (cosetRel G H) b
  have he : G.mul (G.mul b (G.inv a)) a = b := by
    rw [G.mul_assoc, G.inv_mul, G.mul_one]
  rw [he]

/-! ## M279F-6: 2 根連結被覆 — 非自明・推移作用の実例 -/

/-- **M279F-6a: 2 根連結ガロア被覆の witness** — 体拡大 E、f の 2 個の相異なる根、
    Gal の根置換 `perm`/`perm_spec`、そして 2 根を**入れ替える** σ∈Gal(L/K)
    （`swap` とその置換が transposition であること `swap_perm`）。2 根の非自明
    入れ替えの honest witness（実 involution の構成は後続）。 -/
structure ConnEtQuad where
  /-- 体拡大 K ⊆ L。 -/
  ext : FieldExtension
  /-- f の 2 根（ファイバーの 2 点）。 -/
  root : Fin 2 → ext.top.carrier
  /-- 2 根は相異なる。 -/
  roots_distinct : ∀ i j, i ≠ j → root i ≠ root j
  /-- Gal の根置換写像。 -/
  perm : (galoisGroupGrp ext).carrier → Fin 2 → Fin 2
  /-- 両立（σ が根を置換）。 -/
  perm_spec : ∀ (σ : (galoisGroupGrp ext).carrier) (i : Fin 2),
    σ.val.toFun (root i) = root (perm σ i)
  /-- 2 根を入れ替える Gal の元。 -/
  swap : (galoisGroupGrp ext).carrier
  /-- swap の置換は transposition（0↔1）。 -/
  swap_perm : ∀ i, perm swap i = connEtSwap i

/-- 2 根被覆を一般の連結ガロア被覆へ。 -/
def ConnEtQuad.toCover (Q : ConnEtQuad) : ConnEtGaloisCover where
  ext := Q.ext
  n := 2
  root := Q.root
  roots_distinct := Q.roots_distinct
  perm := Q.perm
  perm_spec := Q.perm_spec

/-- **M279F-6b: 2 根ファイバーの Gal 作用は推移的**（本物）— 任意の 2 点 i,j に
    対し、i=j なら恒等元、i≠j なら swap が i を j へ送る（transposition ゆえ）。
    連結対象のモノドロミーが非自明＝推移的であることの実体（M277F の分裂被覆の
    自明モノドロミーとの対比）。 -/
theorem connEt_quad_transitive (Q : ConnEtQuad) :
    (connEt_rootAction Q.toCover).Transitive := by
  intro i j
  cases connEt_fin2_cases i j with
  | inl hij =>
    exact ⟨(galoisGroupGrp Q.ext).one,
      Eq.trans ((connEt_rootAction Q.toCover).act_one i) hij⟩
  | inr hsw =>
    refine ⟨Q.swap, ?_⟩
    show Q.perm Q.swap i = j
    rw [Q.swap_perm i]
    exact hsw

/-- **M279F-6c: 非自明性 — 2 根入れ替え σ は Gal の恒等元でない**（本物）—
    swap が恒等なら perm swap 0 = perm 1 0 = 0（M279F-4b `act_one`）。しかし
    swap_perm より perm swap 0 = swap 0 = 1 ≠ 0。矛盾。これが M277F
    「分裂だけでは π₁ 自明」を破る本物の 1 段。 -/
theorem connEt_swap_ne_one (Q : ConnEtQuad) :
    Q.swap ≠ (galoisGroupGrp Q.ext).one := by
  intro hc
  have h1 : Q.perm Q.swap connEtF0 = connEtSwap connEtF0 := Q.swap_perm connEtF0
  have hswap0 : connEtSwap connEtF0 = connEtF1 := connEtSwap_of_ne connEtF0_ne_F1
  rw [hswap0] at h1
  rw [hc] at h1
  have hone : Q.perm (galoisGroupGrp Q.ext).one connEtF0 = connEtF0 :=
    (connEt_rootAction Q.toCover).act_one connEtF0
  rw [hone] at h1
  exact connEtF0_ne_F1 h1

/-- **M279F-6d: 作用の非自明性 — swap は第 0 根を動かす**（本物）—
    swap·ρ₀ = ρ₁ ≠ ρ₀（ファイバー Fin 2 上で perm swap 0 = 1 ≠ 0）。「連結
    対象上でモノドロミーが非自明に作用する」の直接の実体。 -/
theorem connEt_swap_moves (Q : ConnEtQuad) :
    (connEt_rootAction Q.toCover).act Q.swap connEtF0 ≠ connEtF0 := by
  show Q.perm Q.swap connEtF0 ≠ connEtF0
  rw [Q.swap_perm connEtF0, connEtSwap_of_ne connEtF0_ne_F1]
  exact connEtF1_ne_F0

/-- **M279F-6e: 2 根の推移性（L 上の作用形）** — Gal の作用（L 全体への自然作用）
    で第 0 根 ρ₀ は第 1 根 ρ₁ へ移る（∃ g, g·ρ₀ = ρ₁）。連結対象のファイバーが
    1 軌道（連結）である直接の実体。 -/
theorem connEt_roots_reachable (Q : ConnEtQuad) :
    ∃ g : (galoisGroupGrp Q.ext).carrier,
      (connEt_galAction Q.ext).act g (Q.root connEtF0) = Q.root connEtF1 := by
  refine ⟨Q.swap, ?_⟩
  show Q.swap.val.toFun (Q.root connEtF0) = Q.root connEtF1
  rw [Q.perm_spec Q.swap connEtF0, Q.swap_perm connEtF0,
    connEtSwap_of_ne connEtF0_ne_F1]

/-! ## M279F-7: capstone — 連結ファイバーの非自明推移作用 -/

/-- **M279F-7a: 連結対象の非自明推移作用のデータ** — 連結対象の体拡大 E、その
    ファイバー（Gal-集合）、推移性、そして非自明性（ある元がある点を動かす）を
    束ねる。M277F `GrothendieckGaloisData`（分裂骨格上で π₁ 自明）の連結対象版
    ＝**非自明**モノドロミーを持つ対象。 -/
structure ConnectedActionData where
  /-- 連結対象の体拡大 K ⊆ L。 -/
  ext : FieldExtension
  /-- 連結ファイバー（Gal(L/K)-集合）。 -/
  fiber : GAction (galoisGroupGrp ext)
  /-- ファイバーは推移的（連結）。 -/
  transitive : fiber.Transitive
  /-- 作用は非自明（ある元 g がある点 x を動かす）。 -/
  action_nontrivial : ∃ (g : (galoisGroupGrp ext).carrier) (x : fiber.carrier),
    fiber.act g x ≠ x

/-- **M279F-7b: 2 根被覆から非自明推移作用データを構成**（本物）。 -/
def ConnEtQuad.actionData (Q : ConnEtQuad) : ConnectedActionData where
  ext := Q.ext
  fiber := connEt_rootAction Q.toCover
  transitive := connEt_quad_transitive Q
  action_nontrivial := ⟨Q.swap, connEtF0, connEt_swap_moves Q⟩

/-- **M279F-7c: 非自明作用を持つ連結対象の存在**（2 根入れ替え witness から）—
    分裂対象では π₁ が自明群に潰れた（M277F）のに対し、**連結対象上には Gal が
    非自明かつ推移的に作用するファイバーが存在する**。実 π₁^ét 非自明化の核。 -/
theorem connEt_nontrivial_action_exists (Q : ConnEtQuad) :
    Nonempty ConnectedActionData :=
  ⟨Q.actionData⟩

/-- **M279F-7d: 連結ファイバー ≅ Gal/Stab**（軌道-安定化）— 2 根連結被覆の
    ファイバーは推移的なので、基点 x₀ の安定化部分群 Stab(x₀) による剰余類空間
    Gal/Stab(x₀) と Gal-同変全単射で一致する。「全ての連結被覆は G/H の形」
    （Grothendieck ガロア対応）の連結対象上での本物の実現。 -/
theorem connEt_fiber_cosetModel (Q : ConnEtQuad) (x0 : Fin 2) :
    ∃ φ : ActHom
        (cosetAction (galoisGroupGrp Q.ext)
          (stabilizer (galoisGroupGrp Q.ext) (connEt_rootAction Q.toCover) x0))
        (connEt_rootAction Q.toCover),
      (∀ p q, φ.map p = φ.map q → p = q) ∧ (∀ y, ∃ p, φ.map p = y) :=
  orbit_stabilizer (galoisGroupGrp Q.ext) (connEt_rootAction Q.toCover) x0
    (connEt_quad_transitive Q)

end IUT
