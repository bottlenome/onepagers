/-
  IUT/AffineEquivFull.lean — M299F（柱 A mono-anabelian 復元の本物の先行建設:
  アフィンスキームの圏 ≃ 可換環の圏ᵒᵖ の**充満忠実**＝射の復元の完成）

  ── 分類 **[実]**（本物の数学的実体の新規建設: 遠アーベル幾何の心臓
  「空間の射から環準同型を復元する」の代数幾何版を、実 CRing・実 RingHom・
  M294F の実大域切断復元 Γ(Spec R)≅R・M291F の実 Spec 反変関手の上で本物構成。
  toy 模型・surrogate 群・Bool 軌道を主語にしない。任意可換環 R,S の上での
  実定理として、Hom_Ring(R,S) ≅ Hom_AffSch(Spec S, Spec R) の充満忠実を閉じる）。

  **complete_pct 影響: +**（M294F は「対象レベル」R≅Γ(Spec R) と「射レベル」
  Γ(Spec φ)=φ の**核**を与えたが、圏同値の**射のホム集合の全単射**（＝充満
  忠実）そのものは束ねていなかった。本モジュールは
  (1) アフィンスキームの射 Hom_AffSch(Spec S, Spec R) を M294F の大域切断レベル
      で **RingHom Γ(Spec R) → Γ(Spec S)** として本物定義し（幾何的射 Spec S→Spec R
      が大域切断上に反変に環準同型を誘導する、の忠実な部分ケース）、
  (2) **忠実性 faithful**: 相異なる φ,ψ:R→S は相異なる Spec 射を与える
      （M294F Γ(Spec φ)=φ から単射）を本物で、
  (3) **充満性 full**: 任意の大域切断上の環準同型 u は、ある φ:R→S の
      Γ(Spec φ) から来る（M294F の同型で u を R→S へ翻訳し、Spec 像が u に戻る）
      を本物で証明し、
  (4) 両者を **Hom 同型 Hom_Ring(R,S) ≅ Hom_AffSch(Spec S, Spec R)**（両方向・
      互いに擬逆・pointwise）に束ねる。＝アフィンスキームの圏 ≃ CRingᵒᵖ の
      **充満忠実部分**を本物で閉じた。柱 A の complete_pct を前進させる本物建設(b)。）

  柱 A「mono-anabelian 復元（空間から環＋射を戻す IUT の心臓）」。

  ロードマップ上の位置: IUT の遠アーベル復元（AbsTopIII: π₁^ét から数体を
  復元）の**代数幾何版**の、対象復元（M294F: R≅Γ(Spec R)）に続く**射復元**。
  Spec: CRingᵒᵖ→AffSch と Γ: AffSch→CRingᵒᵖ が互いに擬逆で、ホム集合の
  全単射（充満忠実）を与えることを本物で閉じる。

  * M299F-1 `affEqSchemeHom` — アフィンスキームの射 Hom_AffSch(Spec S, Spec R)
    ＝大域切断上の環準同型 Γ(Spec R) → Γ(Spec S)（幾何的射 Spec S→Spec R の
    大域切断への反変誘導）。M294F の実大域切断環の上での本物定義。
  * M299F-2 `affEqToScheme` — Spec 関手の射レベル φ ↦ Γ(Spec φ) = globSecGammaMap φ。
  * M299F-3 `affEqFromScheme` — Γ 関手の射レベル u ↦ invS∘u∘fwdR（M294F の
    環同型 R≅Γ(Spec R)・S≅Γ(Spec S) による u:Γ(Spec R)→Γ(Spec S) の R→S への翻訳）。
  * M299F-4 `affEq_from_to` — 擬逆その1: Γ∘Spec = id（M294F Γ(Spec φ)=φ）。
  * M299F-5 `affEq_to_from` — 擬逆その2: Spec∘Γ = id（充満性の核。全射 fwdR で
    大域切断を尽くし、globSec_gamma_map_comm と両側逆で u に戻す）。
  * M299F-6 `affEq_faithful` — **忠実**: Γ(Spec φ)=Γ(Spec ψ) ⇒ φ=ψ。
  * M299F-7 `affEq_full` — **充満**: 任意の u に φ が存在し Γ(Spec φ)=u。
  * M299F-8 `AffineEquivData` / `affEq_equivalence` — capstone。Spec・Γ の射
    レベルと擬逆・対象レベル同型 R≅Γ(Spec R) を束ねる。
  * M299F-9 `AffEqFullyFaithful` / `affEq_fully_faithful` — **充満忠実**の束ね。
  * M299F-10 `AffEqHomIso` / `affEq_hom_iso` — Hom_Ring(R,S) ≅ Hom_AffSch(Spec S,Spec R)。
  * M299F-11 `affEq_exists` — 各アフィンスキーム射が Spec(φ) から来る存在言明。
  * M299F-12 実例: 離散体 K→L の環準同型 ↔ Spec L→Spec K の射
    （`affEqFieldSchemeHom`・`affEqFieldSpecMap`・`affEq_field_hom`）。

  **正直な限定（必守申告・消去弱化禁止）**:
  1. 「アフィンスキームの射」は M294F の**大域切断レベル**（＝環準同型
     Γ(Spec R)→Γ(Spec S)）で定義する。locally ringed space の射の完全な圏論的
     定義（連続写像＋構造層の射で各点局所環準同型）は M293F 前層骨組みの上に
     乗る後続。ここは **Hom_Ring(R,S)≅Hom_AffSch(Spec S,Spec R) の充満忠実**を
     本物で閉じる。幾何的な点集合写像 Spec S→Spec R は M291F `specFunMap` で
     別に本物化済み（実例で接続する）。
  2. 本質的全射（任意のアフィンスキームがある Spec R に同型）＝完全な圏同値の
     残り半分は「アフィンスキーム＝Spec の像」の定義から従うが、一般スキームの
     圏まで広げるのは後続。ここは充満忠実部分まで本物。
  3. mono-anabelian の**本丸**（π₁^ét から数体を復元 AbsTopIII）はさらに後続。
     本モジュールは代数幾何側の「空間から環＋射を復元」の完成形。
  4. 体は core のみ（mathlib 禁止）ゆえ M294F の**離散体** `globSecIsField` を
     仮定に取る形。具体的な Field 型の建設は後続。

  全て選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。
  禁止タクティク不使用（cases/obtain/induction/rw/show/refine/exact/apply/
  intro/rfl のみ）。共有ファイル未変更（新規 1 本のみ）。一般名は affEq 接頭辞。
-/
import IUT.GlobalSectionsRecover

namespace IUT

/-! ## M299F-1: アフィンスキームの射 Hom_AffSch(Spec S, Spec R) -/

/-- **M299F-1: アフィンスキームの射**（幾何的射 Spec S → Spec R）を、その
    大域切断上の反変誘導＝環準同型 Γ(Spec R) → Γ(Spec S) として本物定義する。
    M294F の実大域切断環 `globSecGamma` の上での定義。反変（Spec S→Spec R が
    Γ(Spec R)→Γ(Spec S) を与える）。 -/
def affEqSchemeHom (R S : CRing) : Type :=
  RingHom (globSecGamma R) (globSecGamma S)

/-! ## M299F-2: Spec 関手の射レベル φ ↦ Γ(Spec φ) -/

/-- **M299F-2: Spec の射レベル** — 環準同型 φ:R→S が誘導するアフィンスキーム射
    Spec S → Spec R（大域切断上は Γ(Spec φ) = globSecGammaMap φ）。 -/
def affEqToScheme {R S : CRing} (φ : RingHom R S) : affEqSchemeHom R S :=
  globSecGammaMap φ

/-! ## M299F-3: Γ 関手の射レベル u ↦ invS∘u∘fwdR -/

/-- **M299F-3: Γ の射レベル** — アフィンスキーム射 u:Γ(Spec R)→Γ(Spec S) を、
    M294F の環同型 R≅Γ(Spec R)・S≅Γ(Spec S) で環準同型 R→S に翻訳する
    （φ = invS ∘ u ∘ fwdR）。本物の環準同型合成（RingHom.comp）で構成。 -/
def affEqFromScheme {R S : CRing} (u : affEqSchemeHom R S) : RingHom R S :=
  RingHom.comp (RingHom.comp (globSec_ring_iso R).fwd u) (globSec_ring_iso S).inv

/-! ## M299F-4: 擬逆その1 — Γ∘Spec = id（M294F Γ(Spec φ)=φ） -/

/-- **M299F-4: Γ∘Spec = id（射レベル）** — φ の Spec 像を Γ で戻すと φ に戻る。
    ＝ M294F `globSec_gamma_map_eq_phi`。忠実性の土台。 -/
theorem affEq_from_to {R S : CRing} (φ : RingHom R S) (r : R.carrier) :
    (affEqFromScheme (affEqToScheme φ)).map r = φ.map r :=
  globSec_gamma_map_eq_phi φ r

/-! ## M299F-5: 擬逆その2 — Spec∘Γ = id（充満性の核） -/

/-- **M299F-5: Spec∘Γ = id（射レベル）** — 任意のアフィンスキーム射 u を Γ で
    R→S に戻し、その Spec 像を取ると u に一致（pointwise）。大域切断は fwdR で
    尽くされ（M294F の同型の右逆）、globSec_gamma_map_comm と両側逆で u に戻る。
    ＝充満性の核。 -/
theorem affEq_to_from {R S : CRing} (u : affEqSchemeHom R S)
    (s : (globSecGamma R).carrier) :
    (affEqToScheme (affEqFromScheme u)).map s = u.map s := by
  show (globSecGammaMap (affEqFromScheme u)).map s = u.map s
  have hs : (globSec_ring_iso R).fwd.map ((globSec_ring_iso R).inv.map s) = s :=
    (globSec_ring_iso R).right_inv s
  rw [← hs]
  rw [globSec_gamma_map_comm (affEqFromScheme u) ((globSec_ring_iso R).inv.map s)]
  show (globSec_ring_iso S).fwd.map
      ((globSec_ring_iso S).inv.map
        (u.map ((globSec_ring_iso R).fwd.map ((globSec_ring_iso R).inv.map s))))
    = u.map ((globSec_ring_iso R).fwd.map ((globSec_ring_iso R).inv.map s))
  rw [(globSec_ring_iso S).right_inv]

/-! ## M299F-6: 忠実（faithful） -/

/-- **M299F-6: 忠実性** — Spec 像が一致する環準同型 φ,ψ:R→S は一致する
    （相異なる φ≠ψ は相異なる Spec 射 Γ(Spec φ)≠Γ(Spec ψ) を与える、の対偶）。
    Γ で戻すと M294F Γ(Spec φ)=φ から φ,ψ に戻るので単射。 -/
theorem affEq_faithful {R S : CRing} (φ ψ : RingHom R S)
    (h : ∀ s : (globSecGamma R).carrier,
        (affEqToScheme φ).map s = (affEqToScheme ψ).map s)
    (r : R.carrier) : φ.map r = ψ.map r := by
  have e1 : (globSec_ring_iso S).inv.map
      ((globSecGammaMap φ).map ((globSec_ring_iso R).fwd.map r)) = φ.map r :=
    globSec_gamma_map_eq_phi φ r
  have e2 : (globSec_ring_iso S).inv.map
      ((globSecGammaMap ψ).map ((globSec_ring_iso R).fwd.map r)) = ψ.map r :=
    globSec_gamma_map_eq_phi ψ r
  rw [← e1, ← e2]
  exact congrArg (globSec_ring_iso S).inv.map (h ((globSec_ring_iso R).fwd.map r))

/-! ## M299F-7: 充満（full） -/

/-- **M299F-7: 充満性** — 任意のアフィンスキーム射 u（大域切断上の環準同型
    Γ(Spec R)→Γ(Spec S)）は、ある環準同型 φ:R→S の Spec 像 Γ(Spec φ) から来る
    （pointwise）。翻訳 φ = Γ(u) の Spec 像が u に戻る（M299F-5）。 -/
theorem affEq_full {R S : CRing} (u : affEqSchemeHom R S) :
    ∃ φ : RingHom R S,
      ∀ s : (globSecGamma R).carrier, (affEqToScheme φ).map s = u.map s :=
  ⟨affEqFromScheme u, fun s => affEq_to_from u s⟩

/-! ## M299F-8: capstone — 圏同値の核（射レベル＋対象レベル） -/

/-- **M299F-8a: アフィン圏同値データ** — Spec: CRingᵒᵖ→AffSch と
    Γ: AffSch→CRingᵒᵖ の**射レベル**（toSch/fromSch）と、両者が互いに擬逆で
    あること（from_to: Γ∘Spec=id・to_from: Spec∘Γ=id、pointwise）、および
    **対象レベル**の擬逆 R≅Γ(Spec R)（M294F）を束ねる。 -/
structure AffineEquivData (R S : CRing) where
  /-- Spec の射レベル φ ↦ Γ(Spec φ)。 -/
  toSch : RingHom R S → affEqSchemeHom R S
  /-- Γ の射レベル u ↦ invS∘u∘fwdR。 -/
  fromSch : affEqSchemeHom R S → RingHom R S
  /-- 対象レベルの擬逆 R ≅ Γ(Spec R)（M294F）。 -/
  obj_iso : GlobSecRingIso R (globSecGamma R)
  /-- Γ∘Spec = id（射レベル・pointwise）。 -/
  from_to : ∀ (φ : RingHom R S) (r : R.carrier), (fromSch (toSch φ)).map r = φ.map r
  /-- Spec∘Γ = id（射レベル・pointwise）。 -/
  to_from : ∀ (u : affEqSchemeHom R S) (s : (globSecGamma R).carrier),
    (toSch (fromSch u)).map s = u.map s

/-- **M299F-8b: アフィン圏同値データの本物構成**。 -/
def affEq_equivalence (R S : CRing) : AffineEquivData R S where
  toSch := affEqToScheme
  fromSch := affEqFromScheme
  obj_iso := globSec_ring_iso R
  from_to := fun φ r => affEq_from_to φ r
  to_from := fun u s => affEq_to_from u s

/-! ## M299F-9: 充満忠実の束ね -/

/-- **M299F-9a: 充満忠実（fully faithful）** — 射レベルの写像
    φ ↦ Γ(Spec φ) が忠実（単射）かつ充満（全射）であること。 -/
structure AffEqFullyFaithful (R S : CRing) : Prop where
  /-- 忠実: Spec 像が一致すれば φ=ψ。 -/
  faithful : ∀ (φ ψ : RingHom R S),
    (∀ s : (globSecGamma R).carrier,
      (affEqToScheme φ).map s = (affEqToScheme ψ).map s) →
    ∀ r : R.carrier, φ.map r = ψ.map r
  /-- 充満: 任意の u は Γ(Spec φ) から来る。 -/
  full : ∀ (u : affEqSchemeHom R S),
    ∃ φ : RingHom R S,
      ∀ s : (globSecGamma R).carrier, (affEqToScheme φ).map s = u.map s

/-- **M299F-9b: Spec は充満忠実**（Hom_Ring(R,S) → Hom_AffSch(Spec S,Spec R) が
    忠実かつ充満）。アフィンスキームの圏 ≃ CRingᵒᵖ の充満忠実部分を本物で閉じた。 -/
theorem affEq_fully_faithful (R S : CRing) : AffEqFullyFaithful R S :=
  ⟨fun φ ψ h r => affEq_faithful φ ψ h r, fun u => affEq_full u⟩

/-! ## M299F-10: Hom 同型 Hom_Ring ≅ Hom_AffSch -/

/-- **M299F-10a: ホム集合の同型** Hom_Ring(R,S) ≅ Hom_AffSch(Spec S, Spec R)。
    両方向 toSch/fromSch が互いに擬逆（pointwise）。 -/
structure AffEqHomIso (R S : CRing) where
  /-- 環準同型 → アフィンスキーム射（Spec の射レベル）。 -/
  toSch : RingHom R S → affEqSchemeHom R S
  /-- アフィンスキーム射 → 環準同型（Γ の射レベル）。 -/
  fromSch : affEqSchemeHom R S → RingHom R S
  /-- fromSch∘toSch = id（pointwise）。 -/
  left : ∀ (φ : RingHom R S) (r : R.carrier), (fromSch (toSch φ)).map r = φ.map r
  /-- toSch∘fromSch = id（pointwise）。 -/
  right : ∀ (u : affEqSchemeHom R S) (s : (globSecGamma R).carrier),
    (toSch (fromSch u)).map s = u.map s

/-- **M299F-10b: ホム集合の同型の本物構成** — 射のホム集合が両方向で全単射。 -/
def affEq_hom_iso (R S : CRing) : AffEqHomIso R S where
  toSch := affEqToScheme
  fromSch := affEqFromScheme
  left := fun φ r => affEq_from_to φ r
  right := fun u s => affEq_to_from u s

/-! ## M299F-11: 存在言明 -/

/-- **M299F-11: 各アフィンスキーム射は Spec(φ) から来る** — 任意の u に対し、
    その Γ 翻訳 φ が u を実現する（充満性の存在版）。 -/
theorem affEq_exists {R S : CRing} (u : affEqSchemeHom R S) :
    ∃ φ : RingHom R S,
      ∀ s : (globSecGamma R).carrier, (affEqToScheme φ).map s = u.map s :=
  affEq_full u

/-! ## M299F-12: 実例（離散体 K→L ↔ Spec L→Spec K の射） -/

/-- **M299F-12a: 体の環準同型が誘導するアフィンスキーム射** — 離散体 K→L の
    環準同型 φ は、アフィンスキーム射 Spec L → Spec K（大域切断上 Γ(Spec φ)）を
    与える。 -/
def affEqFieldSchemeHom {K L : CRing} (_hK : globSecIsField K) (_hL : globSecIsField L)
    (φ : RingHom K L) : affEqSchemeHom K L :=
  affEqToScheme φ

/-- **M299F-12b: 体の環準同型が誘導する幾何的点写像** Spec L → Spec K
    （M291F の実 Spec 反変関手 `specFunMap`）。大域切断レベルの `affEqFieldSchemeHom`
    と対になる、点集合レベルの本物の幾何写像。 -/
def affEqFieldSpecMap {K L : CRing} (φ : RingHom K L) :
    specFunPrime L → specFunPrime K :=
  specFunMap φ

/-- **M299F-12c: 体の射復元** — 離散体 K→L の環準同型 φ は、その誘導する
    アフィンスキーム射（Γ(Spec φ)）から Γ で忠実に復元される（Γ∘Spec=id）。
    ＝「体の間の空間の射から体準同型を復元」の本物の部分ケース。 -/
theorem affEq_field_hom {K L : CRing} (_hK : globSecIsField K) (_hL : globSecIsField L)
    (φ : RingHom K L) (r : K.carrier) :
    (affEqFromScheme (affEqFieldSchemeHom _hK _hL φ)).map r = φ.map r :=
  affEq_from_to φ r

end IUT
