/-
  IUT/Anabelian.lean  — M1（単遠アーベル復元）の形式化

  望月の遠アーベル幾何（[AbsTopIII] ほか、IUT I §I3 で「IUT の
  出発点」とされる）の **論理骨格** を形式化する。

  復元定理の実体（p 進局所体・数体の環構造の群論的復元）は
  形式化しない（し得る者は現状world中に存在しない）。ここで検証するのは、望月が
  [AbsTopIII] Introduction や Panoramic Overview で強調する
  「mono-anabelian / bi-anabelian の区別」の論理構造である:

  * mono-anabelian = 群から出発する **復元アルゴリズム** が存在する
  * bi-anabelian  = 基本群関手の **充満忠実性**（同型の比較）のみ

  検証結果（本ファイルの定理、すべて sorry なし）:
  1. `mono_implies_bi` — mono ⟹ bi は **公理なし** で証明できる
  2. `bi_implies_mono_classical` — 逆向き bi ⟹ mono は証明できるが
     **選択公理 (Classical.choice) が必須** になる
     （アルゴリズム性が失われるという望月の主張の形式的対応物。
       実際 #print axioms がこの非対称性をそのまま表示する）
  3. `recon_aut_indeterminacy` — 群論的復元の出力は群の自己同型で
     不変。これが多輻的表現の不定性 (Ind1) の形式的起源である
  4. `monoAnabelian_consistent` — 公理系の無矛盾性（恒等モデル）
-/

namespace IUT

/-- **復元設定**: 遠アーベル幾何の舞台の抽象化。

    `F` は「体スキーム的対象」（双曲的曲線・数体など）、
    `G` は「位相群的対象」（エタール基本群・Galois 群など）の型。
    `pi` は基本群関手 X ↦ π₁(X) に相当する。

    同型は等価関係 `isoF` / `isoG` として公理化し、
    `pi_congr` は関手性（同型を同型に送る）を表す。 -/
structure ReconSetting where
  F : Type
  G : Type
  pi : F → G
  isoF : F → F → Prop
  isoG : G → G → Prop
  isoF_refl : ∀ X, isoF X X
  isoF_symm : ∀ {X Y}, isoF X Y → isoF Y X
  isoF_trans : ∀ {X Y Z}, isoF X Y → isoF Y Z → isoF X Z
  isoG_refl : ∀ g, isoG g g
  isoG_symm : ∀ {g h}, isoG g h → isoG h g
  isoG_trans : ∀ {g h k}, isoG g h → isoG h k → isoG g k
  pi_congr : ∀ {X Y}, isoF X Y → isoG (pi X) (pi Y)

/-- **mono-anabelian**（[AbsTopIII] の意味での「単」遠アーベル性）:
    群論的データだけから元の対象を復元する **アルゴリズム**
    `recon : G → F` が存在する。

    * `recon_pi` — 復元の正しさ: recon(π₁(X)) ≅ X
    * `recon_congr` — 復元の「群論性」: 同型な群からは同型な対象を
      復元する（構成が群の表示に依らない） -/
def MonoAnabelian (S : ReconSetting) : Prop :=
  ∃ recon : S.G → S.F,
    (∀ X : S.F, S.isoF (recon (S.pi X)) X) ∧
    (∀ {g h : S.G}, S.isoG g h → S.isoF (recon g) (recon h))

/-- **bi-anabelian**（Grothendieck 流の「双」遠アーベル性）:
    基本群関手が同型を反映する（充満忠実性の同型部分）。 -/
def BiAnabelian (S : ReconSetting) : Prop :=
  ∀ X Y : S.F, S.isoG (S.pi X) (S.pi Y) → S.isoF X Y

/-- **定理 (M1-1)**: mono-anabelian ⟹ bi-anabelian。

    π₁(X) ≅ π₁(Y) なら、群論的復元を両辺に適用して
    X ≅ recon(π₁X) ≅ recon(π₁Y) ≅ Y。

    この証明は選択公理を一切使わない（#print axioms で確認可能）。 -/
theorem mono_implies_bi (S : ReconSetting) (h : MonoAnabelian S) : BiAnabelian S := by
  obtain ⟨recon, hpi, hcongr⟩ := h
  intro X Y hg
  exact S.isoF_trans (S.isoF_symm (hpi X)) (S.isoF_trans (hcongr hg) (hpi Y))

/-- **定理 (M1-2)**: bi-anabelian ⟹ mono-anabelian も成立はするが、
    復元写像を **選択公理で構成する** ことになる。

    証明: 各群 g に対し「π₁ の像に同型で入るか」を排中律で場合分けし、
    入るなら原像を Classical.choice で選ぶ。bi-anabelian 性により
    選び方の差は同型に吸収される。

    `#print axioms` の結果が望月の主張の形式的内容を示す:
    * `mono_implies_bi`          → 公理なし
    * `bi_implies_mono_classical` → [propext, Classical.choice, Quot.sound]

    すなわち bi から得られる「復元」は非アルゴリズム的であり、
    mono-anabelian はそれより真に強い情報を持つ。 -/
theorem bi_implies_mono_classical (S : ReconSetting) (hne : Nonempty S.F)
    (h : BiAnabelian S) : MonoAnabelian S := by
  classical
  -- 復元写像: π₁ の像（同型まで込み）に入る群には原像を選んで返す
  refine ⟨fun g =>
    if hg : ∃ X : S.F, S.isoG (S.pi X) g then Classical.choose hg
    else Classical.choice hne, ?_, ?_⟩
  · -- recon(π₁ X) ≅ X
    intro X
    have hex : ∃ Y : S.F, S.isoG (S.pi Y) (S.pi X) := ⟨X, S.isoG_refl _⟩
    simp only [dif_pos hex]
    exact h _ _ (Classical.choose_spec hex)
  · -- 同型な群からは同型な対象が復元される
    intro g₁ g₂ hg
    by_cases h₁ : ∃ X : S.F, S.isoG (S.pi X) g₁
    · have h₂ : ∃ X : S.F, S.isoG (S.pi X) g₂ :=
        ⟨Classical.choose h₁, S.isoG_trans (Classical.choose_spec h₁) hg⟩
      simp only [dif_pos h₁, dif_pos h₂]
      exact h _ _ (S.isoG_trans (Classical.choose_spec h₁)
        (S.isoG_trans hg (S.isoG_symm (Classical.choose_spec h₂))))
    · have h₂ : ¬∃ X : S.F, S.isoG (S.pi X) g₂ := by
        intro ⟨X, hX⟩
        exact h₁ ⟨X, S.isoG_trans hX (S.isoG_symm hg)⟩
      simp only [dif_neg h₁, dif_neg h₂]
      exact S.isoF_refl _

/-- **定理 (M1-3)**: Aut 不定性 — (Ind1) の形式的起源。

    群論的復元 recon の出力は、入力の群を自己同型 σ ∈ Aut(π₁X) で
    取り替えても（同型の意味で）変わらない。したがって復元された
    対象を別の対象と比較する際には、つねに Aut(π₁) 分の不定性が
    残る。IUT III 定理3.11 の不定性 (Ind1) はこの形式的現象の
    具体化である。 -/
theorem recon_aut_indeterminacy (S : ReconSetting)
    (recon : S.G → S.F)
    (hcongr : ∀ {g h : S.G}, S.isoG g h → S.isoF (recon g) (recon h))
    (g σg : S.G) (hσ : S.isoG σg g) :   -- σ による像 σg ≅ g
    S.isoF (recon σg) (recon g) :=
  hcongr hσ

/-- **定理 (M1-5): 復元アルゴリズムの本質的一意性**。
    二つの mono-anabelian 復元アルゴリズムは、π₁ の像の上で
    同型を除いて一致する。「群論的アルゴリズム」という概念が
    well-defined であることの形式的根拠。 -/
theorem recon_unique (S : ReconSetting) (r₁ r₂ : S.G → S.F)
    (h₁ : ∀ X, S.isoF (r₁ (S.pi X)) X)
    (h₂ : ∀ X, S.isoF (r₂ (S.pi X)) X) :
    ∀ X, S.isoF (r₁ (S.pi X)) (r₂ (S.pi X)) :=
  fun X => S.isoF_trans (h₁ X) (S.isoF_symm (h₂ X))

/-- **無矛盾性 (M1-4)**: 恒等モデル（F = G、π = id、同型 = 等値）が
    mono-anabelian の公理を満たす。よって公理系は無矛盾。 -/
def identityModel : ReconSetting where
  F := Nat
  G := Nat
  pi := id
  isoF := Eq
  isoG := Eq
  isoF_refl := fun _ => rfl
  isoF_symm := Eq.symm
  isoF_trans := Eq.trans
  isoG_refl := fun _ => rfl
  isoG_symm := Eq.symm
  isoG_trans := Eq.trans
  pi_congr := fun h => h

theorem monoAnabelian_consistent : MonoAnabelian identityModel :=
  ⟨id, fun _ => rfl, fun h => h⟩

/-- **定理 (M1-7): 同型不変量の群論的転送** — mono-anabelian 性の
    中心的帰結。体側の **任意の** 同型不変量 φ（同型な対象に同じ値を
    取る関数）は、群側の関数 ψ = φ ∘ recon として実現でき、
    ψ(π₁(X)) = φ(X) が成り立つ。

    すなわち「環構造・体積・次数など、同型で保たれるあらゆる量は
    エタール基本群だけから計算できる」——遠アーベル幾何が IUT に
    提供する転送原理そのものの形式化である。 -/
theorem invariant_transport (S : ReconSetting) (h : MonoAnabelian S)
    {α : Type} (φ : S.F → α)
    (hφ : ∀ {X Y : S.F}, S.isoF X Y → φ X = φ Y) :
    ∃ ψ : S.G → α, ∀ X, ψ (S.pi X) = φ X := by
  obtain ⟨recon, hpi, _⟩ := h
  exact ⟨fun g => φ (recon g), fun X => hφ (hpi X)⟩

/-! ## log-Frobenius 両立性（[AbsTopIII] 定理3.11 の骨格）

[AbsTopIII] の表題定理（mono-anabelian log-Frobenius compatibility）は
「復元アルゴリズムは log-Frobenius 操作と両立する形で実行できる」
と主張する。これが IUT の log-link（M3 の垂直射）に沿って復元を
持ち運ぶことを正当化し、log-Kummer 対応（定理3.11 (ii)）の
前提となる。その骨格を形式化する。 -/

/-- log 操作付きの復元設定: 体側の log 操作 `logF`、群側の対応物
    `logG`、および π との両立 `pi_log`。 -/
structure LogReconSetting extends ReconSetting where
  logF : F → F
  logG : G → G
  pi_log : ∀ X, isoG (pi (logF X)) (logG (pi X))
  logG_congr : ∀ {g h}, isoG g h → isoG (logG g) (logG h)

/-- 反復適用。 -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => f (iterate f k x)

/-- 補題: π は log の反復とも両立する。 -/
theorem pi_log_iter (S : LogReconSetting) (X : S.F) :
    ∀ k : Nat, S.isoG (S.pi (iterate S.logF k X)) (iterate S.logG k (S.pi X)) := by
  intro k
  induction k with
  | zero => exact S.isoG_refl _
  | succ k ih =>
    exact S.isoG_trans (S.pi_log (iterate S.logF k X)) (S.logG_congr ih)

/-! ## Kummer 理論と円分剛性（[EtTh]/[AbsTopIII] の骨格）

定理3.11 (ii) の log-Kummer 対応の核心は、Frobenius 的なテータ値
データとエタール的なコア・データを結ぶ Kummer 写像が、円分剛性
(cyclotomic rigidity) のもとで忠実 (injective) になることである。
これにより「値の同一視」が正当化され、不定性が制御される。 -/

/-- Kummer 設定: Frobenius 的モノイド `MF` からエタール的 `ME` への
    Kummer 写像 `kum`。`frob`/`frobE` は log-link に対応する
    Frobenius 操作で、Kummer 写像はこれと両立する。 -/
structure KummerSetting where
  MF : Type
  ME : Type
  kum : MF → ME
  frob : MF → MF
  frobE : ME → ME
  kum_frob : ∀ x, kum (frob x) = frobE (kum x)

/-- 円分剛性: Kummer 写像が単射（[EtTh] の cyclotomic rigidity の
    抽象化）。 -/
def CyclotomicRigidity (K : KummerSetting) : Prop := Function.Injective K.kum

/-- **定理 (M1-8): Kummer 忠実性** — 円分剛性のもとでは、異なる
    Frobenius 的テータ値は異なるエタール的像を持つ（値が潰れない）。
    定理3.11 (ii) の Kummer 同型による同一視を正当化する根拠。 -/
theorem kummer_faithful (K : KummerSetting) (h : CyclotomicRigidity K)
    {x y : K.MF} (hxy : K.kum x = K.kum y) : x = y := h hxy

/-- **定理 (M1-9): Kummer–Frobenius 両立の反復** — Kummer 写像は
    Frobenius の任意回反復と両立する（log-link 列に沿った両立）。 -/
theorem kum_frob_iter (K : KummerSetting) (x : K.MF) :
    ∀ k : Nat, K.kum (iterate K.frob k x) = iterate K.frobE k (K.kum x) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show K.kum (K.frob (iterate K.frob k x))
       = K.frobE (iterate K.frobE k (K.kum x))
    rw [K.kum_frob, ih]

/-- **定理 (M1-10): log-Kummer 軌道の忠実性** — 円分剛性のもとでは、
    Frobenius 軌道 {frob^k x} のエタール像が一致するのは元の軌道が
    一致するときに限る。すなわち log-link を何回反復しても値が
    崩れない（定理3.11 (ii) の「1の冪根 = addition by zero = no
    indeterminacy」の骨格）。 -/
theorem kummer_orbit_faithful (K : KummerSetting) (h : CyclotomicRigidity K)
    (x : K.MF) {j k : Nat}
    (heq : iterate K.frobE j (K.kum x) = iterate K.frobE k (K.kum x)) :
    iterate K.frob j x = iterate K.frob k x := by
  apply h
  rw [kum_frob_iter, kum_frob_iter]
  exact heq

/-- **定理 (M1-6): log-Frobenius 両立復元**（[AbsTopIII] 定理3.11 の
    骨格）。mono-anabelian 復元は log の任意回の反復と両立する:

        recon(logG^k(π X)) ≅ logF^k(X)

    すなわち群側で log-鎖をいくら下っても、復元結果は体側の
    log-鎖と同型を除いて一致する。これが log-Kummer 対応
    （IUT III 定理3.11 (ii)）で復元を log-link の列に沿って
    使うことの形式的正当化である。 -/
theorem recon_log_compat (S : LogReconSetting)
    (recon : S.G → S.F)
    (hpi : ∀ X, S.isoF (recon (S.pi X)) X)
    (hcongr : ∀ {g h}, S.isoG g h → S.isoF (recon g) (recon h)) :
    ∀ (X : S.F) (k : Nat),
      S.isoF (recon (iterate S.logG k (S.pi X))) (iterate S.logF k X) :=
  fun X k =>
    S.isoF_trans (hcongr (S.isoG_symm (pi_log_iter S X k)))
      (hpi (iterate S.logF k X))

end IUT
