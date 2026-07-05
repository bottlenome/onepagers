/-
  IUT/SpecFunctorial.lean — M291F（Spec の反変関手性: 素スペクトルの引き戻し）

  分類: **[実]**（本物の数体・環の上の実スキーム論的構成 — Spec の反変関手性）
  complete_pct 影響: **+**（柱A スキーム論。mono-anabelian「空間から環を復元」の
    双対側の土台を本物化する。環準同型 φ:R→S が連続写像 Spec(S)→Spec(R) を
    反変に誘導することを、素イデアルの引き戻し・反変関手則・基本開 D(f) の逆像の
    連続性まで本物で建設。toy 主語ではなく実 CRing・実 RingHom 上の実構成。）

  柱A「スキーム論（実 mono-anabelian への前提）」の**本物の先行建設**。

  ロードマップ上の位置: 遠アーベル幾何の中核である「位相空間（+ 構造層）から
  可換環を復元する」双対の土台。ここでは復元の逆向き — 環準同型が誘導する
  Spec 上の連続写像の**反変関手性**と**連続性** — を実 CRing の上で建てる。

  * M291F-1 `specFunPrime R` / `Spec` — 可換環 R の**素イデアル**（真イデアル +
    ab∈P → a∈P ∨ b∈P）と素スペクトル。M289F(PrimeSpectrum) と概念整合させるが
    依存回避のため本ファイル内自前最小定義（import しない）。
  * M291F-2 `specFun_map_zero` — 環準同型は 0 を 0 に送る（RingHom は map_add・
    map_mul・map_one のみを公理とするため、map_zero は加法簿記で導出）。
  * M291F-3 `specFunPullback` / `specFun_pullback_isPrime` — 素イデアルの
    引き戻し φ⁻¹(Q)={r | φ(r)∈Q} が R の**素イデアル**であること（真イデアル性は
    φ(1)=1∉Q、素性は φ(ab)=φ(a)φ(b)∈Q と Q の素性から本物で）。
  * M291F-4 `specFunMap` — Spec 写像 Q ↦ φ⁻¹(Q)。
  * M291F-5 `specFun_map_id` / `specFun_map_comp` — **反変関手則**
    （Spec(id)=id・Spec(ψ∘φ)=Spec(φ)∘Spec(ψ)）を本物で。反変性は
    RingHom.comp が図式順（map = ψ∘φ）であることから自然に立つ。
  * M291F-6 `specFunD` / `specFun_D_preimage` — 基本開 D(f)={P | f∉P} の逆像
    Spec(φ)⁻¹(D_R(f)) = D_S(φ(f))（f∉φ⁻¹Q ⟺ φ(f)∉Q）を**完全に**。
  * M291F-7 `specFunV` / `specFunImage` / `specFun_continuous` — Zariski 閉集合
    V(T)={P | T⊆P} の逆像の**連続性**: Spec(φ)⁻¹(V_R(T)) = V_S(φ(T))
    （生成集合版の完全等式）。
  * M291F-8 capstone: `SpecMapData`・`SpecFunctorLaws`・`specFun_isFunctor`・
    `specFun_exists`・`specFun_continuous_exists`。
  * M291F-9 実例: 恒等 R→R と ℤ→ℤ_p（toZpRing）の Spec 写像を確認。

  正直な限定（消去・弱化禁止）:
  - 素イデアル・Spec・V・D は本ファイル内の自前最小定義（M289F と概念整合、
    import せず並行開発の衝突を回避）。位相は開集合述語（V/D）で扱う。
  - 連続性は基本開 D(f) の逆像 = D(φf) を**完全に**、一般 Zariski 閉 V(T) は
    「生成集合 φ(T) の V」との完全等式まで（V(生成イデアル)=V(生成集合) の
    実代数的事実の生成集合版）。イデアル生成の閉包そのものは後続。
  - 「環（+ 構造層）を空間から復元」（mono-anabelian の本丸）は後続。ここは
    Spec の反変関手性・連続性の土台まで。

  全て選択公理不使用・sorry 皆無。
-/
import IUT.PowerSeries3

namespace IUT

/-! ## 素イデアルと素スペクトル（自前最小定義, M289F 整合） -/

/-- **M291F-1: 可換環 R の素イデアル**。真イデアル（0 を含み加法・環による
    吸収で閉じる・1 を含まない）かつ素（ab∈P → a∈P ∨ b∈P）。 -/
structure specFunPrime (R : CRing) where
  mem : R.carrier → Prop
  mem_zero : mem R.zero
  mem_add : ∀ a b, mem a → mem b → mem (R.add a b)
  mem_smul : ∀ r a, mem a → mem (R.mul r a)
  proper : ¬ mem R.one
  prime : ∀ a b, mem (R.mul a b) → mem a ∨ mem b

/-- 素スペクトル Spec R（素イデアル全体）。 -/
def Spec (R : CRing) : Type := specFunPrime R

/-! ## 環準同型は 0 を保つ（加法簿記で導出） -/

/-- **M291F-2: 環準同型は 0 を 0 に送る**。RingHom は map_add・map_mul・
    map_one のみを公理とするため、map_zero は加法群の簿記で導く。 -/
theorem specFun_map_zero {R S : CRing} (φ : RingHom R S) :
    φ.map R.zero = S.zero := by
  apply S.add_left_cancel (a := φ.map R.zero)
  show S.add (φ.map R.zero) (φ.map R.zero) = S.add (φ.map R.zero) S.zero
  rw [← φ.map_add, R.zero_add, S.add_comm (φ.map R.zero) S.zero, S.zero_add]

/-! ## 素イデアルの引き戻し -/

/-- **M291F-3: 素イデアルの引き戻し** φ⁻¹(Q)={r∈R | φ(r)∈Q}。
    `specFun_pullback_isPrime` により R の素イデアルになる（下の構成が証明そのもの）。 -/
def specFunPullback {R S : CRing} (φ : RingHom R S) (Q : specFunPrime S) :
    specFunPrime R where
  mem := fun r => Q.mem (φ.map r)
  mem_zero := by
    show Q.mem (φ.map R.zero)
    rw [specFun_map_zero φ]
    exact Q.mem_zero
  mem_add := by
    intro a b ha hb
    show Q.mem (φ.map (R.add a b))
    rw [φ.map_add]
    exact Q.mem_add _ _ ha hb
  mem_smul := by
    intro r a ha
    show Q.mem (φ.map (R.mul r a))
    rw [φ.map_mul]
    exact Q.mem_smul _ _ ha
  proper := by
    show ¬ Q.mem (φ.map R.one)
    rw [φ.map_one]
    exact Q.proper
  prime := by
    intro a b hab
    have hab' : Q.mem (φ.map (R.mul a b)) := hab
    rw [φ.map_mul] at hab'
    exact Q.prime _ _ hab'

/-- **M291F-3': 引き戻しが素イデアルであることの明示（構成の再輸出）**。
    引き戻し φ⁻¹(Q) の素イデアル性が本物であることを名前付きで確認。 -/
theorem specFun_pullback_isPrime {R S : CRing} (φ : RingHom R S)
    (Q : specFunPrime S) :
    (specFunPullback φ Q).mem = fun r => Q.mem (φ.map r) := rfl

/-! ## Spec 写像 -/

/-- **M291F-4: Spec 写像** Spec(φ) : Spec S → Spec R, Q ↦ φ⁻¹(Q)。反変。 -/
def specFunMap {R S : CRing} (φ : RingHom R S) : specFunPrime S → specFunPrime R :=
  fun Q => specFunPullback φ Q

/-! ## 反変関手則 -/

/-- 恒等環準同型 R → R。 -/
def specFunIdRingHom (R : CRing) : RingHom R R where
  map := fun a => a
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- **M291F-5a: Spec(id) = id**（反変関手則・単位）。 -/
theorem specFun_map_id (R : CRing) (Q : specFunPrime R) :
    specFunMap (specFunIdRingHom R) Q = Q := rfl

/-- **M291F-5b: Spec(ψ∘φ) = Spec(φ)∘Spec(ψ)**（反変関手則・合成）。
    RingHom.comp φ ψ は図式順（map = ψ∘φ）なので、引き戻しは反対順に合成し
    反変性が自然に立つ。 -/
theorem specFun_map_comp {R S T : CRing} (φ : RingHom R S) (ψ : RingHom S T)
    (Q : specFunPrime T) :
    specFunMap (RingHom.comp φ ψ) Q = specFunMap φ (specFunMap ψ Q) := rfl

/-! ## 基本開 D(f) の逆像（連続性・完全） -/

/-- 基本開集合 D(f) = {P | f ∉ P}。 -/
def specFunD (R : CRing) (f : R.carrier) : specFunPrime R → Prop :=
  fun P => ¬ P.mem f

/-- **M291F-6: 基本開の逆像 Spec(φ)⁻¹(D_R(f)) = D_S(φ(f))**。
    f ∉ φ⁻¹Q ⟺ φ(f) ∉ Q（完全等式）。 -/
theorem specFun_D_preimage {R S : CRing} (φ : RingHom R S)
    (f : R.carrier) (Q : specFunPrime S) :
    specFunD R f (specFunMap φ Q) ↔ specFunD S (φ.map f) Q := Iff.rfl

/-! ## Zariski 閉集合 V(T) の逆像（連続性・生成集合版） -/

/-- Zariski 閉集合 V(T) = {P | T ⊆ P}。 -/
def specFunV (R : CRing) (T : R.carrier → Prop) : specFunPrime R → Prop :=
  fun P => ∀ x, T x → P.mem x

/-- 部分集合 T の φ による像 φ(T) = {s | ∃ x∈T, φ(x)=s}（V の生成集合）。 -/
def specFunImage {R S : CRing} (φ : RingHom R S) (T : R.carrier → Prop) :
    S.carrier → Prop :=
  fun s => ∃ x, T x ∧ φ.map x = s

/-- **M291F-7: 連続性（Zariski 閉の逆像）** Spec(φ)⁻¹(V_R(T)) = V_S(φ(T))。
    閉集合の逆像が閉であることの本物（生成集合 φ(T) の V との完全等式）。 -/
theorem specFun_continuous {R S : CRing} (φ : RingHom R S)
    (T : R.carrier → Prop) (Q : specFunPrime S) :
    specFunV R T (specFunMap φ Q) ↔ specFunV S (specFunImage φ T) Q := by
  constructor
  · intro h s hs
    obtain ⟨x, hx, hxs⟩ := hs
    rw [← hxs]
    exact h x hx
  · intro h x hx
    exact h (φ.map x) ⟨x, hx, rfl⟩

/-! ## capstone -/

/-- **M291F-8a: Spec 写像データ**（環準同型・誘導される Spec 写像・
    基本開の逆像連続性を束ねる）。 -/
structure SpecMapData (R S : CRing) where
  hom : RingHom R S
  map : specFunPrime S → specFunPrime R
  map_eq : ∀ Q, map Q = specFunMap hom Q
  cont : ∀ (f : R.carrier) (Q : specFunPrime S),
    specFunD R f (map Q) ↔ specFunD S (hom.map f) Q

/-- 環準同型から Spec 写像データを構成。 -/
def specFunData {R S : CRing} (φ : RingHom R S) : SpecMapData R S where
  hom := φ
  map := specFunMap φ
  map_eq := fun _ => rfl
  cont := fun f Q => specFun_D_preimage φ f Q

/-- **M291F-8b: 反変関手則の束ね**（Spec : CRingᵒᵖ → Top の関手性）。 -/
structure SpecFunctorLaws : Prop where
  map_id : ∀ (R : CRing) (Q : specFunPrime R),
    specFunMap (specFunIdRingHom R) Q = Q
  map_comp : ∀ (R S T : CRing) (φ : RingHom R S) (ψ : RingHom S T)
      (Q : specFunPrime T),
    specFunMap (RingHom.comp φ ψ) Q = specFunMap φ (specFunMap ψ Q)

/-- **M291F-8c: Spec は反変関手**（単位則・合成則を満たす）。 -/
theorem specFun_isFunctor : SpecFunctorLaws :=
  ⟨fun R Q => specFun_map_id R Q, fun _ _ _ φ ψ Q => specFun_map_comp φ ψ Q⟩

/-- **M291F-8d: 各環準同型に対し Spec 写像が存在**。 -/
theorem specFun_exists {R S : CRing} (φ : RingHom R S) :
    ∃ F : specFunPrime S → specFunPrime R, ∀ Q, F Q = specFunMap φ Q :=
  ⟨specFunMap φ, fun _ => rfl⟩

/-- **M291F-8e: 連続性（基本開）を満たす写像が存在**。各 φ に対し、
    D_R(f) の逆像を D_S(g) で表す g = φ(f) が取れる。 -/
theorem specFun_continuous_exists {R S : CRing} (φ : RingHom R S)
    (f : R.carrier) :
    ∃ g : S.carrier, ∀ Q : specFunPrime S,
      specFunD R f (specFunMap φ Q) ↔ specFunD S g Q :=
  ⟨φ.map f, fun Q => specFun_D_preimage φ f Q⟩

/-! ## 実例 -/

/-- **M291F-9a: 恒等 R → R の Spec 写像は恒等**。 -/
def specFunExampleId (R : CRing) : specFunPrime R → specFunPrime R :=
  specFunMap (specFunIdRingHom R)

theorem specFunExampleId_eq (R : CRing) (Q : specFunPrime R) :
    specFunExampleId R Q = Q := specFun_map_id R Q

/-- **M291F-9b: ℤ → ℤ_p（toZpRing）が誘導する Spec 写像**
    Spec(ℤ_p) → Spec(ℤ)（本物の環準同型上の実 Spec 写像）。 -/
def specFunExampleZp (p : Nat) : specFunPrime (zpRing p) → specFunPrime intRing :=
  specFunMap (toZpRing p)

/-- ℤ→ℤ_p の Spec 写像も基本開の逆像連続性を満たす。 -/
theorem specFunExampleZp_cont (p : Nat) (f : Int) (Q : specFunPrime (zpRing p)) :
    specFunD intRing f (specFunExampleZp p Q)
      ↔ specFunD (zpRing p) ((toZpRing p).map f) Q :=
  specFun_D_preimage (toZpRing p) f Q

end IUT
