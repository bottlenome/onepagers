/-
  IUT/TemperedTower.lean — M374F [実／本物]
  分類: 実 (tempered π₁ の被覆塔＝deck 群 ℤ/l^n の逆系・逆極限 ℤ_l)
  complete_pct 影響: 柱A を前進（M369F 単一 l 被覆・M364F tempered π₁ を詳細化＝テータ被覆の塔
    E_{q^{l^n}}→…→E_q・deck 群 ℤ/l^n の逆系（遷移 ℤ/l^{n+1}→ℤ/l^n）・逆極限 lim ℤ/l^n=ℤ_l・
    離散部が各 ℤ/l^n へ全射を本物で）。
  正直な限定: 完全 tempered π₁=塔の極限＋anabelian 構造は外部仮説等。
-/
import IUT.ThetaCovering
import IUT.LocalCFT

namespace IUT

/-! ## M374F-1: 部分格子の被覆塔 l^n·ℤ ⊆ ℤ（= q^{l^n ℤ} ⊆ q^ℤ）

  M369F の単一 l 被覆（部分格子 lℤ ⊆ ℤ）を塔に詳細化する。テータ被覆塔
  E_{q^{l^n}} → … → E_{q^l} → E_q の格子レベルは、周期束 q^ℤ の指数格子 ℤ の
  部分格子の降鎖 … ⊆ l^{n+1}ℤ ⊆ l^n ℤ ⊆ … ⊆ lℤ ⊆ ℤ である。各段は M369F の
  本物の部分格子 `tcvSublattice`（指数 l^n）で与える。 -/

/-- **M374F-1: 被覆塔の第 n 段部分格子** — l^n·ℤ ⊆ ℤ（= 周期束 q^{l^n ℤ}）。
    M369F `tcvSublattice` を指数 l^n に特化した本物の部分群。 -/
def ttwSublatticeTower (l n : Nat) : Subgroup intGrp := tcvSublattice (l ^ n)

/-- **定理 (M374F-1a): 塔は降鎖** — l^{n+1}ℤ ⊆ l^n ℤ（次の段は前の段の部分格子）。
    l^n ∣ l^{n+1} ゆえ整除が伝播する。被覆塔が本当に入れ子であることの本物の内容。 -/
theorem ttw_sublattice_nested (l n : Nat) (a : Int)
    (h : (ttwSublatticeTower l (n + 1)).mem a) : (ttwSublatticeTower l n).mem a :=
  Int.dvd_trans (Int.ofNat_dvd.mpr (pow_dvd_mono l (Nat.le_succ n))) h

/-- **定理 (M374F-1b): 塔の一般降鎖** — i ≤ j なら l^j ℤ ⊆ l^i ℤ。 -/
theorem ttw_sublattice_dvd (l : Nat) {i j : Nat} (h : i ≤ j) (a : Int)
    (ha : (ttwSublatticeTower l j).mem a) : (ttwSublatticeTower l i).mem a :=
  Int.dvd_trans (Int.ofNat_dvd.mpr (pow_dvd_mono l h)) ha

/-! ## M374F-2: 被覆変換群の塔 deck(n) = ℤ/l^n ℤ

  塔の第 n 段のデッキ群（被覆変換群）は ℤ/l^n ℤ である。既存の本物の商群 `zmod`
  （M13-7、= intGrp/(l^n ℤ)）を指数 l^n に特化して用いる。 -/

/-- **M374F-2: 第 n 段のデッキ群 deck(n) = ℤ/l^n ℤ** — 本物の商群 `zmod (l^n)`。
    E_{q^{l^n}} → E_q の被覆変換群。 -/
def ttwDeckTower (l n : Nat) : Grp := zmod (l ^ n)

/-- **定理 (M374F-2a): 各段のデッキ群は有界指数 l^n**（有限群 ℤ/l^n の実証）。
    M13-9a `zmod_bounded_exponent` の特化。各段が位数 l^n の本物の有限群。 -/
theorem ttw_deck_bounded (l n : Nat) (hl : 1 ≤ l) :
    BoundedExponent (ttwDeckTower l n) :=
  zmod_bounded_exponent (l ^ n) (pow_pos' l hl n)

/-! ## M374F-3: 遷移射 ℤ/l^{n+1} → ℤ/l^n（mod l^n 還元）と逆系 -/

/-- **M374F-3: 遷移射 t_n : ℤ/l^{n+1} → ℤ/l^n** — mod l^n 還元（l^n ∣ l^{n+1}）。
    塔 E_{q^{l^{n+1}}} → E_{q^{l^n}} のデッキ商の還元。本物の群準同型（M13 `zmodTrans`）。 -/
def ttwTransition (l n : Nat) : Hom (ttwDeckTower l (n + 1)) (ttwDeckTower l n) :=
  zmodTrans (pow_dvd_mono l (Nat.le_succ n))

/-- **定理 (M374F-3a): 遷移は還元 mk a ↦ mk a**（代表元での還元）。 -/
theorem ttw_transition_reduce (l n : Nat) (a : Int) :
    (ttwTransition l n).map (Quot.mk (modCong (l ^ (n + 1))).rel a)
      = Quot.mk (modCong (l ^ n)).rel a := rfl

/-- **定理 (M374F-3b): 遷移は群準同型**（積を保つ）。塔が群の逆系であることの半分。 -/
theorem ttw_transition_hom (l n : Nat) (x y : (ttwDeckTower l (n + 1)).carrier) :
    (ttwTransition l n).map ((ttwDeckTower l (n + 1)).mul x y)
      = (ttwDeckTower l n).mul ((ttwTransition l n).map x) ((ttwTransition l n).map y) :=
  (ttwTransition l n).map_mul x y

/-- **M374F-3c: デッキ群の塔の逆系**（添字 = 段数 n、順序 = ≤、G n = ℤ/l^n、
    推移射 = mod l^n 還元）。既存の `padicSystem` に一致（塔＝ℤ/l^n の副有限逆系）。 -/
@[reducible] def ttwTowerSystem (l : Nat) : InverseSystem := padicSystem l

/-- **定理 (M374F-3d): 塔は整合的逆系**（遷移が合成則を満たす: t_i∘t_j = t_{i→k}）。
    塔が genuine な逆系であることの本物の証明（`InverseSystem.t_comp` の特化）。 -/
theorem ttw_tower_compat (l : Nat) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k)
    (x : (ttwDeckTower l k).carrier) :
    (zmodTrans (pow_dvd_mono l hij)).map ((zmodTrans (pow_dvd_mono l hjk)).map x)
      = (zmodTrans (pow_dvd_mono l (Nat.le_trans hij hjk))).map x :=
  (ttwTowerSystem l).t_comp hij hjk x

/-! ## M374F-4: 逆極限 lim_n ℤ/l^n = ℤ_l（l 進整数） -/

/-- **M374F-4: 塔の逆極限 lim_n ℤ/l^n = ℤ_l** — l 進整数（tempered π₁ の離散部の
    l 進完備化）。既存の本物の逆極限 `Zp l = limitGrp (padicSystem l)` に一致する
    genuine な群。 -/
def ttwInverseLimit (l : Nat) : Grp := Zp l

/-- **定理 (M374F-4a): 逆極限は本物の逆極限 lim ℤ/l^n = ℤ_l**（構成そのもの）。 -/
theorem ttw_limit_is_ladic (l : Nat) :
    ttwInverseLimit l = limitGrp (padicSystem l) := rfl

/-- **M374F-4b: 逆極限の各段への射影 lim ℤ/l^n ↠ ℤ/l^n**（極限の錐）。 -/
def ttwLimitProj (l n : Nat) : Hom (ttwInverseLimit l) (ttwDeckTower l n) :=
  limitProj (padicSystem l) n

/-- **定理 (M374F-4c): 射影の錐は遷移と整合**（逆極限の普遍錐）。 -/
theorem ttw_limit_proj_compat (l : Nat) {i j : Nat} (h : i ≤ j)
    (x : (ttwInverseLimit l).carrier) :
    (zmodTrans (pow_dvd_mono l h)).map ((ttwLimitProj l j).map x) = (ttwLimitProj l i).map x :=
  limitProj_compat (padicSystem l) h x

/-! ## M374F-5: 極限は tempered π₁ の副有限部 Ẑ の l-部（M364F 接続）

  M364F の tempered π₁ = 1 → Ẑ → π₁^temp → ℤ → 1 において、塔の逆極限 ℤ_l は
  副有限部 Ẑ（`tmpProfinitePart` = zhat）の l-部である。整合族を l 冪の添字に
  制限する射影 Ẑ ↠ ℤ_l を本物で構成する（自然な向きは制限＝射影）。 -/

/-- **M374F-5: 副有限部から l 進部への射影 Ẑ ↠ ℤ_l** — M364F の副有限部
    `tmpProfinitePart` (= Ẑ = lim_n ℤ/n) の整合族を l 冪の添字 n ↦ l^n に制限して
    ℤ_l = lim_n ℤ/l^n を得る本物の群準同型。塔の極限が π₁^temp の副有限部に
    住むこと（副有限完備化の l-部）の形式化。 -/
def ttwProfiniteToLadic (l : Nat) : Hom tmpProfinitePart (ttwInverseLimit l) where
  map := fun x => ⟨fun n => x.val (l ^ n), fun {_ _} h => x.property (pow_dvd_mono l h)⟩
  map_mul := fun _ _ => by
    apply Subtype.ext
    funext n
    rfl

/-- **定理 (M374F-5a): 射影は l^n 成分の取り出し** — Ẑ ↠ ℤ_l を第 n 段へ射影すると
    元の Ẑ 族の l^n 成分になる。塔の極限が副有限部の l-部である接続の本物の中身。 -/
theorem ttw_limit_in_zhat (l : Nat) (x : tmpProfinitePart.carrier) (n : Nat) :
    (ttwLimitProj l n).map ((ttwProfiniteToLadic l).map x) = x.val (l ^ n) := rfl

/-! ## M374F-6: 離散部 ℤ は各段 ℤ/l^n へ全射（M369F/M364F 詳細化の核心）

  M364F の tempered π₁ の離散部 ℤ（`tmpDiscretePart`）は、塔の各有限段 ℤ/l^n の
  上に**全射**する（各 ℤ/l^n は離散 ℤ の商）。この全射は遷移射と整合する錐をなし、
  逆極限への完備化 ℤ → ℤ_l を誘導する。単一 l 被覆（M369F `tcvCovering`）が塔全体に
  持ち上がる本物の内容。 -/

/-- **M374F-6: 離散部の各段への射影 ℤ ↠ ℤ/l^n** — 商射影（M13 `quotProj`）。
    M364F 離散部 `tmpDiscretePart` (= ℤ) が塔の第 n 段のデッキ群 ℤ/l^n を商として実現。 -/
def ttwDiscreteProj (l n : Nat) : Hom tmpDiscretePart (ttwDeckTower l n) :=
  quotProj intGrp (modCong (l ^ n))

/-- **定理 (M374F-6a): 離散部は各段へ全射**（各 ℤ/l^n は離散 ℤ の商）。 -/
theorem ttw_discrete_surjective (l n : Nat) :
    ∀ x, ∃ a, (ttwDiscreteProj l n).map a = x :=
  quotProj_surjective intGrp (modCong (l ^ n))

/-- **定理 (M374F-6b): 離散部の全射は遷移と整合する錐** —
    t_n ∘ (ℤ ↠ ℤ/l^{n+1}) = (ℤ ↠ ℤ/l^n)。全射の族が塔の逆系と整合する
    （＝離散 ℤ から各段への商が両立する）本物の内容。 -/
theorem ttw_discrete_cone (l n : Nat) (a : tmpDiscretePart.carrier) :
    (ttwTransition l n).map ((ttwDiscreteProj l (n + 1)).map a) = (ttwDiscreteProj l n).map a :=
  rfl

/-- **M374F-6c: 離散部の l 進完備化 ℤ → ℤ_l** — 離散部 `tmpDiscretePart` (= ℤ) から
    塔の逆極限 ℤ_l への完備化（M27 `toZp`）。各段の全射の錐が誘導する普遍写像。 -/
def ttwDiscreteComplete (l : Nat) : Hom tmpDiscretePart (ttwInverseLimit l) := toZp l

/-- **定理 (M374F-6d): 完備化を第 n 段へ射影すると離散射影**（錐の整合）。 -/
theorem ttw_discrete_to_level (l n : Nat) (a : Int) :
    (ttwLimitProj l n).map ((ttwDiscreteComplete l).map a) = (ttwDiscreteProj l n).map a := rfl

/-- **定理 (M374F-6e): 離散部の完備化は単射**（l 進分離性、l ≥ 2）— 離散 ℤ の情報は
    l 進完備化 ℤ → ℤ_l で失われない（M27-3 `toZp_injective`）。tempered の離散部が
    塔の極限に忠実に埋まることの本物の内容。 -/
theorem ttw_discrete_complete_injective (l : Nat) (hl : 2 ≤ l) :
    (ttwDiscreteComplete l).Injective := toZp_injective l hl

/-! ## M374F-7: 単一 l 被覆（M369F）との橋 ℤ/l ≅ deck(1) 型

  塔の（指数 l の）デッキ群 `zmod l` と M369F の単一被覆のデッキ群 `tcvDeckGroup l`
  （= 剰余類商）は、同じ ℤ/l を二つの商構成で与えたもので、正準同型である。 -/

/-- **M374F-7: 橋 tcvDeckGroup l → zmod l** — M369F 単一被覆のデッキ群（剰余類商）から
    塔の zmod 商への正準同型（代表元 a ↦ mk a）。cosetRel（l ∣ −a+b）と modCong
    （l ∣ a−b）が同値であることで well-defined。 -/
def ttwDeckBridge (l : Nat) : Hom (tcvDeckGroup l) (zmod l) where
  map := Quot.lift (fun a => Quot.mk (modCong l).rel a)
    (fun a b h => by
      apply Quot.sound
      obtain ⟨k, hk⟩ := h
      have hk' : -a + b = ((l : Nat) : Int) * k := hk
      show ((l : Nat) : Int) ∣ (a - b)
      refine ⟨-k, ?_⟩
      rw [Int.mul_neg, ← hk']
      omega)
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    rfl

/-- **定理 (M374F-7a): 橋は全射**（両方 ℤ/l を実現）。 -/
theorem ttw_deck_bridge_surjective (l : Nat) :
    ∀ y, ∃ x, (ttwDeckBridge l).map x = y := by
  intro y
  induction y using Quot.ind; rename_i a
  exact ⟨Quot.mk _ a, rfl⟩

/-- **定理 (M374F-7b): 橋は単射**（cosetRel と modCong の同値）。両合わせて
    M369F の単一被覆デッキ群と塔の ℤ/l が正準同型（全単射準同型）であることの本物。 -/
theorem ttw_deck_bridge_injective (l : Nat) : Hom.Injective (ttwDeckBridge l) := by
  intro x y hxy
  induction x using Quot.ind; rename_i a
  induction y using Quot.ind; rename_i b
  have hrel : (modCong l).rel a b := quot_exact intGrp (modCong l) hxy
  apply Quot.sound
  have hd : ((l : Nat) : Int) ∣ (b - a) := dvd_sub_symm hrel
  show ((l : Nat) : Int) ∣ (intGrp.mul (intGrp.inv a) b)
  have hswap : intGrp.mul (intGrp.inv a) b = b - a :=
    Int.add_comm (-a) b
  rw [hswap]
  exact hd

/-! ## M374F-8: 正直な外部仮説（決して導出しない） -/

/-- **外部仮説（正直な限定・決して導出しない）**: 全被覆塔 E_{q^{l^n}} → E_q が忠実
    ＝ 周期 q が無限位数で塔が各段崩れない（各 ℤ/l^n が非自明）。M369F/M364F と同じく、
    正 valuation の素元 v(q)≠0 の具体構成は柱B ℤ_p 接続の後続ゆえ外部仮説として受ける。 -/
def ttw_full_tower_hypothesis (K : IUTField) (q : (tateMultGroup K).carrier) : Prop :=
  tcv_full_tower_hypothesis K q

/-- **外部仮説（正直な限定・決して導出しない）**: 完全な tempered π₁ ＝ 塔の逆極限 ℤ_l に
    anabelian（slim, M9 `Slim`）構造を載せたもの。本モデルの可換な ℤ_l は slim でないため、
    André・Mochizuki [SemiAnbd] の tempered 遠アーベルの前提は本質的に外部（幾何的入力）。 -/
def ttw_tempered_tower_hypothesis (T : Grp) : Prop := Slim T

/-! ## M374F-9: capstone -/

/-- **M374F-9a: tempered 被覆塔の総括データ** — 被覆度 l・Tate パラメータ q・塔の逆極限
    ℤ_l・離散部の完備化 ℤ ↪ ℤ_l（単射）・副有限部からの射影 Ẑ ↠ ℤ_l・部分格子塔の降鎖・
    離散部が各段 ℤ/l^n へ全射・各段の有界指数・全塔忠実性仮説（正直な外部 crux）を束ねる。
    主語は本物の部分格子 l^n ℤ と本物の商群 ℤ/l^n・本物の逆極限 ℤ_l（toy 代理なし）。 -/
structure TemperedTowerData (K : IUTField) where
  /-- 被覆度 l（≥ 2）。 -/
  l : Nat
  /-- l ≥ 2（l 進分離性・非自明塔に必要）。 -/
  hl : 2 ≤ l
  /-- Tate パラメータ q ∈ K^×。 -/
  q : (tateMultGroup K).carrier
  /-- 塔の逆極限 ℤ_l。 -/
  limit : Grp
  /-- limit ＝ lim_n ℤ/l^n（本物の逆極限）。 -/
  limit_isLadic : limit = ttwInverseLimit l
  /-- 離散部の完備化 ℤ → ℤ_l。 -/
  discreteComplete : Hom tmpDiscretePart limit
  /-- 完備化は単射（離散部が塔の極限に忠実に埋まる）。 -/
  discrete_inj : discreteComplete.Injective
  /-- 副有限部からの射影 Ẑ ↠ ℤ_l（l-部）。 -/
  profiniteToLimit : Hom tmpProfinitePart limit
  /-- 部分格子塔は降鎖 l^{n+1}ℤ ⊆ l^n ℤ。 -/
  sublattice_nested : ∀ n a, (ttwSublatticeTower l (n + 1)).mem a → (ttwSublatticeTower l n).mem a
  /-- 離散部は各段 ℤ/l^n へ全射。 -/
  discrete_surj : ∀ n x, ∃ a : tmpDiscretePart.carrier, (ttwDiscreteProj l n).map a = x
  /-- 各段のデッキ群は有界指数（有限群 ℤ/l^n）。 -/
  deck_bounded : ∀ n, BoundedExponent (ttwDeckTower l n)
  /-- 全塔忠実性仮説（正直な外部 crux）。 -/
  fullTower : ttw_full_tower_hypothesis K q

/-- **M374F-9b: witness 本体** — 全塔忠実性仮説 hTower を受けて全フィールドを
    M374F-1〜6 の本物の証明で埋める（hTower 以外はすべて完全証明で埋まる）。 -/
def temperedTowerData (K : IUTField) (q : (tateMultGroup K).carrier)
    (l : Nat) (hl : 2 ≤ l) (hTower : ttw_full_tower_hypothesis K q) :
    TemperedTowerData K where
  l := l
  hl := hl
  q := q
  limit := ttwInverseLimit l
  limit_isLadic := rfl
  discreteComplete := ttwDiscreteComplete l
  discrete_inj := ttw_discrete_complete_injective l hl
  profiniteToLimit := ttwProfiniteToLadic l
  sublattice_nested := fun n a h => ttw_sublattice_nested l n a h
  discrete_surj := fun n => ttw_discrete_surjective l n
  deck_bounded := fun n => ttw_deck_bounded l n (by omega)
  fullTower := hTower

/-- **定理 (M374F-9c): tempered 被覆塔データの（条件付き）存在** — 被覆度 l ≥ 2 と
    全塔忠実性仮説が与えられれば、テータ被覆塔・デッキ群 ℤ/l^n の逆系・逆極限 ℤ_l・
    離散部の全射と完備化を束ねたデータが存在する。存在が塔仮説に条件付くのは正直な限定
    （正 valuation の素元の具体構成は柱B の後続）。 -/
theorem ttw_exists (K : IUTField) (q : (tateMultGroup K).carrier)
    (l : Nat) (hl : 2 ≤ l) (hTower : ttw_full_tower_hypothesis K q) :
    Nonempty (TemperedTowerData K) :=
  ⟨temperedTowerData K q l hl hTower⟩

/-! ## 実例（l = 2、塔 ℤ/2 → ℤ/4 → ℤ/8 → …、逆極限 ℤ_2） -/

/-- 実例: 塔の逆極限は本物の l 進整数 ℤ_2 = lim ℤ/2^n。 -/
example : ttwInverseLimit 2 = limitGrp (padicSystem 2) := rfl

/-- 実例: 第 3 段のデッキ群 ℤ/8 は有界指数（有限群、位数 2^3 = 8）。 -/
example : BoundedExponent (ttwDeckTower 2 3) := ttw_deck_bounded 2 3 (by omega)

/-- 実例: 遷移 ℤ/4 → ℤ/2（塔 E_{q^4}→E_{q^2}）は離散射影と整合する。 -/
example (a : Int) :
    (ttwTransition 2 1).map ((ttwDiscreteProj 2 2).map a) = (ttwDiscreteProj 2 1).map a :=
  ttw_discrete_cone 2 1 a

/-- 実例: 離散部 ℤ は第 3 段 ℤ/8 へ全射（各段は離散部の商）。 -/
example : ∀ x, ∃ a : tmpDiscretePart.carrier, (ttwDiscreteProj 2 3).map a = x :=
  ttw_discrete_surjective 2 3

/-- 実例: 単一被覆デッキ群 tcvDeckGroup 2 は塔の ℤ/2 と正準全単射（M369F 接続）。 -/
example : (∀ y, ∃ x, (ttwDeckBridge 2).map x = y) ∧ Hom.Injective (ttwDeckBridge 2) :=
  ⟨ttw_deck_bridge_surjective 2, ttw_deck_bridge_injective 2⟩

end IUT
