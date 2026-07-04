/-
  # M188F: Tate 曲線のテンパード基本群の具体提示 — デッキ群 ℤ・被覆群・副有限完備化の三層束ね（柱A A-3β-1・並行部品）

  A-3（エタール的入力の代理化）の β 系列第一歩。Tate 曲線
  X = E_q ∖ {O} のエタール/テンパード被覆圏をスキーム論でなく
  **具体的に提示された π₁** で実現する A-3β 計画の、まず「群」を
  建設する。[EtTh] §1 のテータ被覆 Ÿ → X のデッキ群は ℤ（有界指数
  でない = 有限エタールで実現不能 = テンパード、M9-6）であり、
  数論的テンパード基本群 Π はこの幾何的部分 Δ を基礎体のガロア群
  G_K で拡大した完全列 1 → Δ → Π → G_K → 1 に乗る（M9）。その
  副有限完備化（デッキ部分では ẑ = lim_n ℤ/n、M13）がエタール π₁
  の幾何的部分である。本モジュールは M9 の `tateModel`（Tate 曲線型
  モデル）と M13 の `zmodSystem` / `zhat` / `toZhat` を**再利用**して、
  この三層（テンパード群・有限商の逆系・副有限完備化）を一つの
  具体提示に束ねる:

  * M188F-1 `tateDeckGrp` / `tateDeckGrp_tempered` — テンパード
    デッキ群 ℤ（テータ被覆 Ÿ → X のガロア群）と、その非有界指数性
    （= 有限エタール被覆で実現不能。M9-6 の再利用）
  * M188F-2 `boundedExponent_no_int_embedding` — 汎用補題: ℤ が
    忠実に埋め込まれる群は有界指数を持たない（M9-6 の埋め込み版。
    デッキ群を含む群のテンパード性が埋め込みから伝播する）
  * M188F-3 `tateCoverGrp` / `tateDeckProj` / `tateDeckProj_theta` /
    `tateCoverGrp_exact` / `tateCoverGrp_pr_surjective` /
    `tateCoverGrp_tempered` — **被覆群**（数論的テンパード π₁ の
    提示）= `tateModel.Pi`。完全列 1 → Δ → Π → G_K → 1 を
    `tateModel` から継承し、デッキ群への引き込み（retraction）と
    Π 自身のテンパード性（M188F-2 + M9 のテータ埋め込み）を検証
  * M188F-4 `tateFiniteSystem` / `tateProfinite` — デッキ部分の
    **有限商の逆系** = `zmodSystem`（ℤ/n たち、割り切り順序）と
    その逆極限 = **副有限完備化** `zhat`（エタール π₁ の幾何的部分）
  * M188F-5 `tateCompletion` / `tateCompletion_proj` /
    `tateCompletion_unique` — **完備化写像** Π → ẑ（デッキ射影と
    対角埋め込み `toZhat` の合成）。各有限レベルへの射影が
    mod n 還元と一致し（rfl）、この錐条件が写像を**一意に**決める
    （M13-6 逆極限の普遍性の適用）
  * M188F-6 `tateCompletion_deck_injective` /
    `tateFinite_collapses_theta` — **テンパード↔エタールの対比**:
    完備化はデッキ群 ℤ 上で単射（M13-8 の再利用。テンパード π₁ の
    デッキ情報は副有限完備化 = エタール π₁ に忠実に写る）、しかし
    どの有限レベル ℤ/n もテータ簿記 j ↦ j² を必ず潰す（M13-9b の
    再利用。だからエタール側だけでは足りずテンパード提示が要る）
  * M188F-7 `TateCoverGroupData` / `tateCoverGroupData` /
    `tateCoverGroup_exists` — 総括データ・証人・存在定理

  **意義**: A-3β-2（被覆圏 = このπ₁の作用圏）・A-3β-3（有限商作用
  との対応）の型基盤となる「具体群 + その有限商逆系 + 副有限極限」
  の三つ組が、既存資産（M9 の完全列モデル・M13 の ẑ 実構成）の
  再利用だけで一ファイルに束ねられた。「テンパード π₁ の副有限
  完備化がエタール π₁ であり、デッキ群 ℤ はそこに単射で入るが、
  どの有限段でもテータ簿記は見えない」という A-3β の出発点が、
  スキーム論を経由せず全て構成的に成立している。

  **正直な限定**: (1) 本モジュールが与えるのは**群の提示**であって、
  被覆圏（A-3β-2）でもスキーム論的エタール性でもない。π₁ の提示は
  幾何からの**入力**（構造体データ `tateModel`）であり、実際の
  Tate 曲線から計算された不変量ではない。(2) G_K は玩具モデル
  `tateModel.Gal` = ℤ（可換）であり、実際の絶対ガロア群 G_K は
  非可換、実際の Δ^temp は ℤ を真に含む大きな群である。ここで
  捉えているのは「デッキ群 ℤ による拡大」という骨格のみ。
  (3) 副有限完備化はデッキ（幾何的）方向についてのみ取る:
  `tateCompletion` は G_K 方向を潰してデッキ座標を完備化する
  （Π = ℤ×ℤ 全体の完備化 ẑ×ẑ は A-3β では不要のため範囲外）。
  (4) M13 と同じく位相（副有限位相・テンパード位相）は未導入で、
  逆極限は代数的に構成する。

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.Profinite

namespace IUT

/-! ## M188F-1: テンパードデッキ群 ℤ -/

/-- **テンパードデッキ群**（M188F-1）: テータ被覆 Ÿ → X の
    ガロア群 ℤ（M9 の `intGrp`）。エタールテータ関数 q^{j²} の
    ラベル j はこの群の元である。 -/
def tateDeckGrp : Grp := intGrp

/-- **デッキ群のテンパード性**（M188F-1、M9-6 の再利用）:
    デッキ群 ℤ は有界指数を持たない。よってテータ被覆は有限
    エタール被覆の枠内に存在せず、テンパード理論が真に必要。 -/
theorem tateDeckGrp_tempered : ¬ BoundedExponent tateDeckGrp :=
  theta_deck_not_finite

/-! ## M188F-2: 埋め込みによるテンパード性の伝播 -/

/-- **補題 (M188F-2): ℤ を忠実に含む群は有界指数を持たない** —
    f : ℤ → G が単射なら G は有界指数でない（f(N) = f(0) が
    N 乗消滅から従い、単射性で N = 0 となり矛盾）。M9-6 の
    埋め込み版であり、デッキ群を含む被覆群全体のテンパード性が
    この補題で伝播する。 -/
theorem boundedExponent_no_int_embedding (G : Grp) (f : Hom intGrp G)
    (hf : f.Injective) (hG : BoundedExponent G) : False := by
  obtain ⟨N, hN, hpow⟩ := hG
  obtain h1 : f.map ((N : Nat) : Int) = f.map 0 := by
    rw [← intGrp_pow_one N, f.map_pow, hpow]
    exact f.map_one.symm
  obtain h2 : ((N : Nat) : Int) = 0 := hf _ _ h1
  omega

/-! ## M188F-3: 被覆群（数論的テンパード π₁ の提示） -/

/-- **被覆群**（M188F-3）: Tate 曲線の数論的テンパード基本群の
    具体提示 = `tateModel.Pi`（デッキ群 ℤ の G_K による拡大、
    玩具モデルでは ℤ × ℤ）。完全列 1 → Δ → Π → G_K → 1・
    テータ被覆の埋め込み θ : ℤ ↪ Δ を `tateModel` から継承する。 -/
def tateCoverGrp : Grp := tateModel.Pi

/-- **デッキ射影**（M188F-3）: 被覆群からデッキ群への引き込み
    （第 1 成分への射影）。幾何的方向の座標を読み出す。 -/
def tateDeckProj : Hom tateCoverGrp tateDeckGrp where
  map := fun p => p.1
  map_mul := fun _ _ => rfl

/-- デッキ射影はテータ埋め込み ℤ → Δ → Π の引き込み（retraction）:
    デッキ群の元は被覆群を往復しても保たれる（定義的に rfl）。 -/
theorem tateDeckProj_theta (a : Int) :
    tateDeckProj.map (tateModel.ι.map (tateModel.θ.map a)) = a := rfl

/-- **完全列の継承**（M188F-3）: 被覆群は完全列
    1 → Δ → Π → G_K → 1 に乗る（ker(pr) = im(ι)、`tateModel` 由来）。 -/
theorem tateCoverGrp_exact (x : tateCoverGrp.carrier) :
    tateModel.pr.map x = tateModel.Gal.one ↔
      ∃ d : tateModel.Δ.carrier, tateModel.ι.map d = x :=
  tateModel.exact_seq x

/-- ガロア群への射影は全射（完全列の右端、`tateModel` 由来）。 -/
theorem tateCoverGrp_pr_surjective (g : tateModel.Gal.carrier) :
    ∃ x : tateCoverGrp.carrier, tateModel.pr.map x = g :=
  tateModel.pr_surj g

/-- **被覆群のテンパード性**（M188F-3）: デッキ群だけでなく
    数論的基本群 Π 全体も有界指数を持たない（テータ埋め込み
    ι ∘ θ : ℤ ↪ Π の忠実性 M9 + M188F-2）。Π 自体が有限被覆の
    ガロア群として実現できない = テンパード群である。 -/
theorem tateCoverGrp_tempered : ¬ BoundedExponent tateCoverGrp :=
  fun h => boundedExponent_no_int_embedding tateCoverGrp
    (tateModel.ι.comp tateModel.θ) (theta_in_arithmetic tateModel) h

/-! ## M188F-4: 有限商の逆系と副有限完備化 -/

/-- **有限商の逆系**（M188F-4）: デッキ部分 ℤ の有限商 ℤ/n たちの
    逆系（添字 = 自然数、順序 = 割り切り。M13 の `zmodSystem` の
    再利用）。エタール π₁ はこの逆系の極限である。 -/
def tateFiniteSystem : InverseSystem := zmodSystem

/-- **副有限完備化**（M188F-4）: 有限商逆系の逆極限
    ẑ = lim_n ℤ/n（M13 の `zhat` の再利用）。テンパード π₁ の
    デッキ部分の副有限完備化 = エタール π₁ の幾何的部分。 -/
def tateProfinite : Grp := zhat

/-! ## M188F-5: 完備化写像とその普遍性 -/

/-- **完備化写像**（M188F-5）: 被覆群 Π → 副有限完備化 ẑ
    （デッキ射影と対角埋め込み `toZhat` の合成）。テンパード π₁ を
    エタール π₁ に送る「副有限化」の具体形。 -/
def tateCompletion : Hom tateCoverGrp tateProfinite :=
  toZhat.comp tateDeckProj

/-- 完備化写像の各有限レベルへの射影は「デッキ座標の mod n 還元」
    そのもの（定義的に rfl。錐条件の成立）。 -/
theorem tateCompletion_proj (n : Nat) (x : tateCoverGrp.carrier) :
    (limitProj tateFiniteSystem n).map (tateCompletion.map x)
      = (quotProj intGrp (modCong n)).map (tateDeckProj.map x) := rfl

/-- **完備化写像の一意性**（M188F-5、M13-6 の適用）: 全有限レベルで
    mod n 還元と整合する Π → ẑ は `tateCompletion` ただ一つ。
    逆極限の普遍性により、完備化は錐条件から一意に決まる。 -/
theorem tateCompletion_unique (u' : Hom tateCoverGrp tateProfinite)
    (hu' : ∀ (n : Nat) (x : tateCoverGrp.carrier),
      (limitProj tateFiniteSystem n).map (u'.map x)
        = (quotProj intGrp (modCong n)).map (tateDeckProj.map x)) :
    ∀ x, u'.map x = tateCompletion.map x := by
  obtain ⟨u, hu, huniq⟩ := limit_universal tateFiniteSystem tateCoverGrp
    (fun n => (quotProj intGrp (modCong n)).comp tateDeckProj)
    (fun {i j} h x => rfl)
  intro x
  exact (huniq u' hu' x).trans (huniq tateCompletion (fun n x => rfl) x).symm

/-! ## M188F-6: テンパード ↔ エタールの対比 -/

/-- **定理 (M188F-6a): 完備化はデッキ群上で単射**（M13-8 の再利用）:
    テータ埋め込み ℤ → Δ → Π と完備化 Π → ẑ の合成は単射。
    テンパード π₁ のデッキ情報は副有限完備化（= エタール π₁）に
    **忠実に**写る（ℤ の残余有限性）。 -/
theorem tateCompletion_deck_injective :
    (tateCompletion.comp (tateModel.ι.comp tateModel.θ)).Injective := by
  intro a b h
  exact toZhat_injective a b h

/-- **定理 (M188F-6b): どの有限レベルもテータ簿記を潰す**（M13-9b の
    再利用）: 逆系のどの群 ℤ/n への準同型も、テータ指数の異なる
    ラベル j, k（j² ≠ k²）を衝突させる。M188F-6a と併せて:
    完備化は ℤ を覚えているのに有限近似ではテータが見えない——
    エタール入力だけでは足りずテンパード提示（本モジュール）が
    必要である所以。 -/
theorem tateFinite_collapses_theta (n : Nat) (hn : 0 < n)
    (f : Hom intGrp (tateFiniteSystem.G n)) :
    ∃ j k : Int, f.map j = f.map k ∧ j * j ≠ k * k :=
  zmod_collapses_theta n hn f

/-! ## M188F-7: 総括 -/

/-- **Tate 被覆群データ**（M188F-7）: A-3β-1 の成果物の束。
    テンパードデッキ群・数論的テンパード基本群（完全列付き）・
    有限商の逆系・副有限完備化・完備化写像、およびテンパード性と
    デッキ群上の単射性を一つに束ねる。A-3β-2（被覆圏）・A-3β-3
    （有限商作用との対応）はこのデータを入力にとる。 -/
structure TateCoverGroupData where
  /-- テンパードデッキ群（テータ被覆 Ÿ → X のガロア群 ℤ）。 -/
  deck : Grp
  /-- デッキ群は有界指数でない（有限エタール被覆で実現不能）。 -/
  deck_tempered : ¬ BoundedExponent deck
  /-- 数論的テンパード基本群のデータ
      （完全列 1 → Δ → Π → G_K → 1 とテータ埋め込み）。 -/
  arith : TemperedArithmetic
  /-- デッキ群の幾何的部分 Δ への埋め込み。 -/
  deckEmbed : Hom deck arith.Δ
  /-- 埋め込みの忠実性。 -/
  deckEmbed_inj : deckEmbed.Injective
  /-- 被覆群 Π 自体もテンパード（有界指数でない）。 -/
  tempered : ¬ BoundedExponent arith.Pi
  /-- デッキ部分の有限商の逆系。 -/
  finiteSystem : InverseSystem
  /-- 副有限完備化（エタール π₁ の幾何的部分）。 -/
  profinite : Grp
  /-- 完備化は有限商逆系の逆極限である。 -/
  profinite_eq : profinite = limitGrp finiteSystem
  /-- 完備化写像 Π → 副有限完備化。 -/
  completion : Hom arith.Pi profinite
  /-- 完備化はデッキ群上で単射（テンパード情報の忠実な副有限化）。 -/
  deck_injective : (completion.comp (arith.ι.comp deckEmbed)).Injective

/-- **証人**（M188F-7）: 本モジュールの構成が Tate 被覆群データを
    実際に充足する。 -/
def tateCoverGroupData : TateCoverGroupData where
  deck := tateDeckGrp
  deck_tempered := tateDeckGrp_tempered
  arith := tateModel
  deckEmbed := tateModel.θ
  deckEmbed_inj := tateModel.θ_inj
  tempered := tateCoverGrp_tempered
  finiteSystem := tateFiniteSystem
  profinite := tateProfinite
  profinite_eq := rfl
  completion := tateCompletion
  deck_injective := tateCompletion_deck_injective

/-- **定理 (M188F-7): Tate 被覆群データの存在** — テンパード π₁ の
    具体提示・有限商逆系・副有限完備化の三層束ねは無矛盾に存在する。 -/
theorem tateCoverGroup_exists : Nonempty TateCoverGroupData :=
  ⟨tateCoverGroupData⟩

end IUT
