/-
  IUT/GaloisCorrespondence.lean — M283F: Galois 対応の本物の 1 段
    （部分群 H ≤ Gal(L/K) ↔ 中間体 L^H の反変ガロア接続）
  ── 柱A 実 Galois 群論の本物の先行建設（遠アーベル復元の中心構造）

  主要成果の分類 **[実]**（本物の体拡大 L/K・本物の体の自己同型群 Aut(L)・
  本物の Galois 部分群の上での **Galois 対応（ガロア接続）**）。

  complete_pct 影響: **柱A 実 Galois 対応（部分群 ↔ 中間体）の本物の 1 段を
  先行建設**。既存資産では
  * `FieldAutGroup.lean`（M271F）が本物の体の自己同型群 Aut(L)・Galois 部分群
    `galoisSubgroup E`（Gal(L/K)=Aut_K(L)）を構成、
  * `QuotientGroup.lean`（M267F）が本物の群論（正規部分群 `IsNormalSubgroup`・
    部分群 `Subgroup`）を持つ
  が、**部分群と中間体（部分体）の間の対応そのもの**（固定体 L^H・固定群
  Gal(L/M)・両者の反変ガロア接続）は無かった。本モジュールが本物で建設する。
  遠アーベル幾何は「Gal(L/K) の部分群構造が中間体の格子を復元する」ことを本質と
  するので、この対応は柱A の中心構造である。

  内容（本物・toy 群を主語にしない）:
  * M283F-1 `GalCorrSubfield`/`GalCorrInterField` — L の部分体・K を含む中間体。
  * M283F-2 補題 `galCorr_aut_neg`/`galCorr_aut_inv_ne`/`galCorr_aut_ne_zero`
    — 体自己同型が加法逆元・（非零元の）乗法逆元・非零性を保つ（本物の証明。
    map_neg は加法簡約、map_inv は逆元一意性、いずれも choice / 場合分けなし）。
  * M283F-3 `galCorr_fixedField`/`galCorr_fixedField_isSubfield` — 固定体
    L^H = {x | ∀σ∈H, σx=x} が **L の部分体**（0,1 を含み加法・加法逆・乗法・
    非零元の乗法逆で閉じる）を本物に証明。`galCorr_fixedInterField`（H ≤ Gal で
    K を含む中間体）。
  * M283F-4 `galCorr_fixingGroup`/`_le_galois` — 固定群 Gal(L/M)={σ|∀x∈M,σx=x}
    が Aut(L) の**部分群**、中間体なら Gal(L/K) の部分群。
  * M283F-5 `galCorr_antitone`/`galCorr_fixing_antitone`/`galCorr_field_fixing_field`
    /`galCorr_fix_fixing`/**`galCorr_galois_connection`** — 両写像の反変性
    （包含反転）・往復包含（M⊆L^{Gal(L/M)}, H⊆Gal(L/L^H)）・**反変ガロア接続
    H⊆Gal(L/M) ⟺ M⊆L^H** を本物に証明（対応の骨組み）。
  * M283F-6 `galCorr_normal_stable` — 正規部分群 H⊴Gal の固定体 L^H は Aut(L) で
    **安定**（σ∈Aut(L), x∈L^H ⟹ σx∈L^H）＝「L^H/K が正規」の ⟹ 方向を本物に。
  * M283F-7 capstone `GaloisCorrData`/`galCorrData`/`galCorr_exists`
    /`galCorr_connection`。
  * M283F-8 実例 `galCorr_trivial_top`（自明群 ↔ L 全体）・`galCorr_top_base`
    （Gal 全体 ↔ K、L^Gal=K を仮説で受け取り K⊆L^Gal を本物に）。

  **正直な限定**（何が本物で何が未達か・消去弱化禁止）:
  1. **対応の全単射（基本定理の完全形）は未達**: L^{Gal(L/M)}=M・Gal(L/L^H)=H の
     **等号**は分離正規性・次数計算 [L:L^H]=|H| を要し後続。本モジュールは
     **反変ガロア接続（両 antitone + 往復包含）**まで本物で閉じる。往復包含の
     片側（H⊆Gal(L/L^H) 等）は本物、逆包含（等号）は後続。
  2. **部分体の逆元閉性は非零元に限定**（`inv_mem : mem x → x≠0 → mem (inv x)`）。
     これは体の部分体の**正しい**閉性条件であり弱化ではない（inv 0 = 0 規約下で
     0 の逆は自明に属す）。σ(inv x)=inv(σx) の無条件形は x=0 の判定に排中律を
     要する（Field.lean の整域性と同じ理由）ため、非零仮説形が本物の内容。
  3. **正規対応は ⟹ 方向のみ**: H⊴Gal ⟹ L^H が安定（＝L^H/K 正規）を本物に。
     逆（L^H/K 正規 ⟹ H⊴Gal）は基本定理の全単射（限定 1）を要し後続。
  4. L^Gal=K（L/K がガロアであることの定義）は `galCorr_top_base` で**仮説**として
     受け取る（K⊆L^Gal の非自明でない側は本物に証明）。中間体は「K を含み L に
     含まれる部分体」を witness 構造 `GalCorrInterField` で扱う。

  **選択公理不使用**（新規 `Classical.choice` を証明本体に導入しない）: 逆元は
  明示、非零性は単射 witness、場合分けなし。禁止タクティク不使用
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp なし）。
  サブエージェント並行部品（新規 1 ファイルのみ・共有ファイル未変更）。
-/
import IUT.FieldAutGroup

namespace IUT

/-! ## M283F-1: 部分体・中間体（K を含む L の部分体） -/

/-- **M283F-1a: L の部分体** — 0,1 を含み加法・加法逆・乗法・**非零元の乗法逆**で
    閉じる述語。逆元閉性を非零元に限定するのは体の部分体の正しい閉性条件
    （inv 0 = 0 規約下で 0 の逆は自明）。 -/
structure GalCorrSubfield (L : IUTField) where
  /-- 部分体への所属。 -/
  mem : L.carrier → Prop
  /-- 0 を含む。 -/
  zero_mem : mem L.zero
  /-- 1 を含む。 -/
  one_mem : mem L.one
  /-- 加法で閉じる。 -/
  add_mem : ∀ {x y}, mem x → mem y → mem (L.add x y)
  /-- 加法逆元で閉じる。 -/
  neg_mem : ∀ {x}, mem x → mem (L.neg x)
  /-- 乗法で閉じる。 -/
  mul_mem : ∀ {x y}, mem x → mem y → mem (L.mul x y)
  /-- 非零元の乗法逆元で閉じる。 -/
  inv_mem : ∀ {x}, mem x → x ≠ L.zero → mem (L.inv x)

/-- **M283F-1b: 中間体 K ⊆ M ⊆ L** — L の部分体で、基礎体 K の像 ι(K) を全て含む。 -/
structure GalCorrInterField (E : FieldExtension) where
  /-- 台となる L の部分体。 -/
  toSubfield : GalCorrSubfield E.top
  /-- 基礎体 K の像を含む。 -/
  incl_mem : ∀ k, toSubfield.mem (E.incl k)

/-! ## M283F-2: 体自己同型が保つ構造（加法逆・非零・乗法逆） -/

/-- **M283F-2a: 自己同型は単射**（明示逆写像 `invFun` から。choice 不使用）。 -/
theorem galCorr_aut_inj {L : IUTField} (σ : FieldAut L) {a b : L.carrier}
    (h : σ.toFun a = σ.toFun b) : a = b := by
  have h2 := congrArg σ.invFun h
  rw [σ.left_inv, σ.left_inv] at h2
  exact h2

/-- **M283F-2b: 非零性の保存** — x ≠ 0 なら σ(x) ≠ 0（単射性と σ(0)=0 から）。 -/
theorem galCorr_aut_ne_zero {L : IUTField} (σ : FieldAut L) {x : L.carrier}
    (hx : x ≠ L.zero) : σ.toFun x ≠ L.zero := by
  intro hc
  apply hx
  apply galCorr_aut_inj σ
  rw [σ.map_zero]
  exact hc

/-- **M283F-2c: 加法逆元の保存** σ(-x) = -(σ x) — 加法性 σ(-x + x)=σ(0)=0 と
    加法簡約から。**場合分け・choice 不使用**の本物。 -/
theorem galCorr_aut_neg {L : IUTField} (σ : FieldAut L) (x : L.carrier) :
    σ.toFun (L.neg x) = L.neg (σ.toFun x) := by
  have h1 : L.add (σ.toFun (L.neg x)) (σ.toFun x) = L.zero := by
    have e := σ.map_add (L.neg x) x
    rw [L.neg_add] at e
    rw [σ.map_zero] at e
    exact e.symm
  have h2 : L.add (L.neg (σ.toFun x)) (σ.toFun x) = L.zero := L.neg_add (σ.toFun x)
  have h3 : L.add (σ.toFun x) (σ.toFun (L.neg x))
      = L.add (σ.toFun x) (L.neg (σ.toFun x)) := by
    rw [L.add_comm (σ.toFun x) (σ.toFun (L.neg x)), h1,
      L.add_comm (σ.toFun x) (L.neg (σ.toFun x)), h2]
  exact L.add_left_cancel h3

/-- **M283F-2d: 乗法逆元の保存（非零）** σ(x⁻¹) = (σ x)⁻¹ — σ(x)·σ(x⁻¹)=σ(1)=1
    と逆元一意性から。**場合分け・choice 不使用**（x ≠ 0 仮説形が本物）。 -/
theorem galCorr_aut_inv_ne {L : IUTField} (σ : FieldAut L) {x : L.carrier}
    (hx : x ≠ L.zero) : σ.toFun (L.inv x) = L.inv (σ.toFun x) := by
  have hσx : σ.toFun x ≠ L.zero := galCorr_aut_ne_zero σ hx
  have h1 : L.mul (σ.toFun x) (σ.toFun (L.inv x)) = L.one := by
    have e := σ.map_mul x (L.inv x)
    rw [L.mul_inv_cancel x hx] at e
    rw [σ.map_one] at e
    exact e.symm
  have h2 : L.mul (σ.toFun x) (L.inv (σ.toFun x)) = L.one :=
    L.mul_inv_cancel (σ.toFun x) hσx
  exact L.inv_unique h1 h2

/-! ## M283F-3: 固定体 L^H とそれが部分体であること -/

/-- **M283F-3a: 固定体 L^H** — H の全元が固定する L の元 {x | ∀σ∈H, σx=x}。 -/
def galCorr_fixedField (E : FieldExtension) (H : Subgroup (fieldAutGroup E.top)) :
    E.top.carrier → Prop :=
  fun x => ∀ σ, H.mem σ → σ.toFun x = x

/-- 所属の特徴づけ。 -/
theorem galCorr_fixedField_mem_iff (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) (x : E.top.carrier) :
    galCorr_fixedField E H x ↔ (∀ σ, H.mem σ → σ.toFun x = x) :=
  Iff.rfl

/-- **M283F-3b: 固定体は L の部分体** — 0,1 を含み加法・加法逆・乗法・非零元の
    乗法逆で閉じる。各閉性は σ が対応する演算を保つこと（M283F-2）と、H の元での
    固定条件から従う。**本物の完全証明**。 -/
def galCorr_fixedField_isSubfield (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) : GalCorrSubfield E.top where
  mem := galCorr_fixedField E H
  zero_mem := fun σ _ => σ.map_zero
  one_mem := fun σ _ => σ.map_one
  add_mem := fun {x y} hx hy => fun σ hσ => by
    show σ.toFun (E.top.add x y) = E.top.add x y
    rw [σ.map_add, hx σ hσ, hy σ hσ]
  neg_mem := fun {x} hx => fun σ hσ => by
    show σ.toFun (E.top.neg x) = E.top.neg x
    rw [galCorr_aut_neg σ x, hx σ hσ]
  mul_mem := fun {x y} hx hy => fun σ hσ => by
    show σ.toFun (E.top.mul x y) = E.top.mul x y
    rw [σ.map_mul, hx σ hσ, hy σ hσ]
  inv_mem := fun {x} hx hxne => fun σ hσ => by
    show σ.toFun (E.top.inv x) = E.top.inv x
    rw [galCorr_aut_inv_ne σ hxne, hx σ hσ]

/-- **M283F-3c: H ≤ Gal(L/K) の固定体は K を含む中間体** — H が Gal(L/K) の
    部分群なら L^H は ι(K) を含む。 -/
def galCorr_fixedInterField (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top))
    (hHG : ∀ σ, H.mem σ → (galoisSubgroup E).mem σ) : GalCorrInterField E where
  toSubfield := galCorr_fixedField_isSubfield E H
  incl_mem := fun k σ hσ => hHG σ hσ k

/-! ## M283F-4: 固定群 Gal(L/M) -/

/-- **M283F-4a: 固定群 Gal(L/M)** — M の全元を固定する L の自己同型
    {σ | ∀x∈M, σx=x} が **Aut(L) の部分群**（恒等・合成・逆で閉じる本物の内容）。 -/
def galCorr_fixingGroup (E : FieldExtension) (M : GalCorrSubfield E.top) :
    Subgroup (fieldAutGroup E.top) where
  mem := fun σ => ∀ x, M.mem x → σ.toFun x = x
  one_mem := fun _ _ => rfl
  mul_mem := fun {σ τ} hσ hτ => fun x hx => by
    show σ.toFun (τ.toFun x) = x
    rw [hτ x hx, hσ x hx]
  inv_mem := fun {σ} hσ => fun x hx => by
    show σ.invFun x = x
    have h := σ.left_inv x
    rw [hσ x hx] at h
    exact h

/-- 所属の特徴づけ。 -/
theorem galCorr_fixingGroup_mem_iff (E : FieldExtension) (M : GalCorrSubfield E.top)
    (σ : FieldAut E.top) :
    (galCorr_fixingGroup E M).mem σ ↔ (∀ x, M.mem x → σ.toFun x = x) :=
  Iff.rfl

/-- **M283F-4b: 中間体の固定群は Gal(L/K) の部分群** — M が ι(K) を含むなら
    Gal(L/M) ⊆ Gal(L/K)（M を固定する自己同型は特に ι(K) を固定）。 -/
theorem galCorr_fixingGroup_le_galois (E : FieldExtension) (M : GalCorrInterField E) :
    ∀ σ, (galCorr_fixingGroup E M.toSubfield).mem σ → (galoisSubgroup E).mem σ := by
  intro σ hσ k
  exact hσ (E.incl k) (M.incl_mem k)

/-! ## M283F-5: 反変ガロア接続（両 antitone + 往復包含） -/

/-- **M283F-5a: 固定体の反変性** — H₁ ⊆ H₂ ⟹ L^{H₂} ⊆ L^{H₁}（包含反転）。 -/
theorem galCorr_antitone (E : FieldExtension)
    (H₁ H₂ : Subgroup (fieldAutGroup E.top))
    (h : ∀ σ, H₁.mem σ → H₂.mem σ) :
    ∀ x, galCorr_fixedField E H₂ x → galCorr_fixedField E H₁ x := by
  intro x hx σ hσ
  exact hx σ (h σ hσ)

/-- **M283F-5b: 固定群の反変性** — M₁ ⊆ M₂ ⟹ Gal(L/M₂) ⊆ Gal(L/M₁)。 -/
theorem galCorr_fixing_antitone (E : FieldExtension)
    (M₁ M₂ : GalCorrSubfield E.top)
    (h : ∀ x, M₁.mem x → M₂.mem x) :
    ∀ σ, (galCorr_fixingGroup E M₂).mem σ → (galCorr_fixingGroup E M₁).mem σ := by
  intro σ hσ x hx
  exact hσ x (h x hx)

/-- **M283F-5c: 往復包含（中間体側）** M ⊆ L^{Gal(L/M)} — M の元は Gal(L/M) の
    全元に固定される（ガロア接続の単位、本物）。 -/
theorem galCorr_field_fixing_field (E : FieldExtension) (M : GalCorrSubfield E.top) :
    ∀ x, M.mem x → galCorr_fixedField E (galCorr_fixingGroup E M) x := by
  intro x hx σ hσ
  exact hσ x hx

/-- **M283F-5d: 往復包含（部分群側）** H ⊆ Gal(L/L^H) — H の元は L^H を固定する
    （ガロア接続の余単位、本物）。 -/
theorem galCorr_fix_fixing (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) :
    ∀ σ, H.mem σ →
      (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem σ := by
  intro σ hσ x hx
  exact hx σ hσ

/-- **M283F-5e: 反変ガロア接続** — H ⊆ Gal(L/M) ⟺ M ⊆ L^H。両写像
    (H ↦ L^H, M ↦ Gal(L/M)) が反変随伴をなす（対応の骨組み・本物の完全証明）。 -/
theorem galCorr_galois_connection (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) (M : GalCorrSubfield E.top) :
    (∀ σ, H.mem σ → (galCorr_fixingGroup E M).mem σ) ↔
    (∀ x, M.mem x → galCorr_fixedField E H x) := by
  constructor
  · intro hHG x hx σ hσ
    exact hHG σ hσ x hx
  · intro hMF σ hσ x hx
    exact hMF x hx σ hσ

/-! ## M283F-6: 正規部分群 ⟹ 固定体の安定性（正規拡大の ⟹ 方向） -/

/-- **M283F-6: 正規部分群の固定体は安定** — H ⊴ Gal ならば任意の σ∈Aut(L) と
    x∈L^H に対し σ(x)∈L^H。「L^H/K が正規（ガロア）」の ⟹ 方向の本物の内容。
    証明: h∈H に対し σ⁻¹hσ∈H（正規性）ゆえ (σ⁻¹hσ)(x)=x、両辺に σ を施し
    h(σx)=σx。**逆包含（L^H 安定 ⟹ H⊴Gal）は基本定理の全単射を要し後続**。 -/
theorem galCorr_normal_stable (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top))
    (hHnorm : IsNormalSubgroup (fieldAutGroup E.top) H)
    (σ : FieldAut E.top) {x : E.top.carrier}
    (hx : galCorr_fixedField E H x) :
    galCorr_fixedField E H (σ.toFun x) := by
  intro h hh
  have hw := hHnorm (fieldAutInv σ) h hh
  have hstab : σ.invFun (h.toFun (σ.toFun x)) = x := hx _ hw
  have hc := congrArg σ.toFun hstab
  rw [σ.right_inv] at hc
  exact hc

/-! ## M283F-7: capstone — Galois 対応データ -/

/-- **M283F-7a: Galois 対応データ** — Galois 群 Gal(L/K)・両写像
    (部分群 ↦ 固定体, 中間体 ↦ 固定群)・反変ガロア接続・往復包含（両単位）を束ねる。 -/
structure GaloisCorrData (E : FieldExtension) where
  /-- Galois 群 Gal(L/K)。 -/
  Gal : Subgroup (fieldAutGroup E.top)
  /-- 部分群 ↦ 固定体 L^H。 -/
  fixedOf : Subgroup (fieldAutGroup E.top) → GalCorrSubfield E.top
  /-- 部分体 ↦ 固定群 Gal(L/M)。 -/
  fixingOf : GalCorrSubfield E.top → Subgroup (fieldAutGroup E.top)
  /-- 反変ガロア接続 H⊆Gal(L/M) ⟺ M⊆L^H。 -/
  connection : ∀ (H : Subgroup (fieldAutGroup E.top)) (M : GalCorrSubfield E.top),
    (∀ σ, H.mem σ → (fixingOf M).mem σ) ↔ (∀ x, M.mem x → (fixedOf H).mem x)
  /-- 往復包含（中間体側）M ⊆ L^{Gal(L/M)}。 -/
  unit_field : ∀ (M : GalCorrSubfield E.top) (x : E.top.carrier),
    M.mem x → (fixedOf (fixingOf M)).mem x
  /-- 往復包含（部分群側）H ⊆ Gal(L/L^H)。 -/
  unit_group : ∀ (H : Subgroup (fieldAutGroup E.top)) (σ : FieldAut E.top),
    H.mem σ → (fixingOf (fixedOf H)).mem σ

/-- **M283F-7b: 証人** — 固定体・固定群・ガロア接続・往復包含が全条件を満たす。 -/
def galCorrData (E : FieldExtension) : GaloisCorrData E where
  Gal := galoisSubgroup E
  fixedOf := fun H => galCorr_fixedField_isSubfield E H
  fixingOf := fun M => galCorr_fixingGroup E M
  connection := fun H M => galCorr_galois_connection E H M
  unit_field := fun M x hx => galCorr_field_fixing_field E M x hx
  unit_group := fun H σ hσ => galCorr_fix_fixing E H σ hσ

/-- **M283F-7c: Galois 対応データの存在**。 -/
theorem galCorr_exists (E : FieldExtension) : Nonempty (GaloisCorrData E) :=
  ⟨galCorrData E⟩

/-- **M283F-7d: 反変ガロア接続の存在（対応の骨組み）** — 任意の H, M で
    H⊆Gal(L/M) ⟺ M⊆L^H が成り立つ。 -/
theorem galCorr_connection (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) (M : GalCorrSubfield E.top) :
    (∀ σ, H.mem σ → (galCorr_fixingGroup E M).mem σ) ↔
    (∀ x, M.mem x → galCorr_fixedField E H x) :=
  galCorr_galois_connection E H M

/-! ## M283F-8: 実例（両端の対応） -/

/-- **自明部分群 {1} ≤ Aut(L)**（恒等のみ）。 -/
def galCorr_trivialSubgroup (G : Grp) : Subgroup G where
  mem := fun g => g = G.one
  one_mem := rfl
  mul_mem := fun {a b} ha hb => by
    show G.mul a b = G.one
    rw [ha, hb, G.one_mul]
  inv_mem := fun {a} ha => by
    show G.inv a = G.one
    rw [ha]
    have h := G.inv_mul G.one
    rw [G.mul_one] at h
    exact h

/-- **M283F-8a: 自明群 ↔ L 全体** — 固定体 L^{{1}} は L 全体（恒等は全元を固定）。 -/
theorem galCorr_trivial_top (E : FieldExtension) :
    ∀ x, galCorr_fixedField E (galCorr_trivialSubgroup (fieldAutGroup E.top)) x := by
  intro x σ hσ
  rw [hσ]
  exact rfl

/-- **M283F-8b: Gal 全体 ↔ K** — L/K がガロア（仮説 L^Gal ⊆ ι(K)）のとき、固定体
    L^{Gal(L/K)} はちょうど ι(K)。**非自明でない側 K ⊆ L^Gal は本物に証明**
    （ι(K) の各元は Gal(L/K) の定義により固定される）、逆側は仮説（ガロアの定義）。 -/
theorem galCorr_top_base (E : FieldExtension)
    (hGalois : ∀ x, galCorr_fixedField E (galoisSubgroup E) x → ∃ k, E.incl k = x) :
    ∀ x, galCorr_fixedField E (galoisSubgroup E) x ↔ ∃ k, E.incl k = x := by
  intro x
  constructor
  · exact hGalois x
  · intro hk σ hσ
    obtain ⟨k, hkx⟩ := hk
    rw [← hkx]
    exact hσ k

end IUT
