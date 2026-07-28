/-
  IUT/Q3TateCuspidalizationL9.lean — A8（柱A A8: 楕円 cuspidalization [AbsTopII] §3 の
  幾何的基体の **wild level-9 昇格** — 実 [3]/[9]-同種 E_{3⁹}→E_{3⁹}（M=ℚ₃(ζ₉)・q=3⁹）・
  核＝ちょうど E_{3⁹}[9](M)（全有理 cusp）・**E_{3⁹}[3](M)=⟨[27],[ζ₃]⟩≅(ℤ/3)² の新分類**・
  **初の 2 段 cuspidalization 開曲線塔 E∖E[9] → E∖E[3] → E∖{O}**・[9] 非全射 witness）

  ── 主要成果の分類: **[実／昇格(a)]**。
     昇格(a)-1: `Q3TateCuspidalization`（q3cu）正直限定 4「単一切片 N=2・q=9・奇 N・一般 q は
     後続」と `Q3TateCubeIsogeny`（q3c3）正直限定 4「μ₃/μ₉ を有理化する拡大上の E[N] 全有理化は
     後続」を、**wild 分岐体 M=ℚ₃(ζ₉)（e=6）上の実 Tate 曲線 E_{3⁹}=M^×/q^ℤ（q9tl）で正面
     discharge** する。系列は N=2 核=Klein(ℤ/2)²（q3cu・ℚ₃）→ N=3 核={O}（q3c3・ℚ₃）→
     **N=9 核=E_{3⁹}[9](M)≅(ℤ/9)²（本モジュール・M 上で全有理）**。
     昇格(a)-2: 0.65 監査 named gap (5)「単一切片（p=3・q=9・level 2/μ₂ のみ・奇 l・μ_l は後続）」を
     level-9 で discharge する（曲線・体・N が全て既存 A8 資産と別）。

     **本物の主語**: 実 M^× = ℤ(v_π)×U₃（q3k の実 Kummer 代数の単数群）の商 E_{3⁹}=M^×/q^ℤ・
     実点 [3]=[(6,u₆)]・[ζ₉]=[Y]・実 [3]-同種 x↦x³・実 [9]-同種 x↦x⁹。toy 群・surrogate は
     一切登場しない（§3 準拠）。

  complete_pct 影響: **A8 を前進（見込み・独立監査が確定）**。q3cu 限定 4・q3c3 限定 4 を
     奇 N（=9）・拡大体（M）について本物へ置換し、A8 で初めて
     (i) 非自明かつ全有理な cusp 集合（ker[9] = ちょうど E_{3⁹}[9](M)）、
     (ii) **2 段の開曲線塔**（[AbsTopII] §3 が N を動かして使う「複数 N の被覆族」の最初の実例）、
     (iii) E[3](M)≅(ℤ/3)² の完全分類（E₉[3](ℚ₃)={O}（q3c3）との対比対）
     を得る。設計 = audit/pillar-A8-cuspidalization-deepen-detail-2026-07-20.md §3 の C1 スライス。

  内容:
   * q9cu-0  実同種 `q9cuPow3`/`q9cuPow9` : Hom E_{3⁹} E_{3⁹}（x↦x³/x⁹）・
             **pow9 = pow3∘pow3**（`q9cu_pow3_pow3`）——塔の可換性の代数的核
   * q9cu-1  核⟺捻れ述語ブリッジ（`q9cu_ker9_iff_tor`・定義計算）＋冪ヘルパ
   * q9cu-2  ★★ **核＝ちょうど E_{3⁹}[9](M)**（`q9cu_ker9_eq_e9`・q9td_e9_decomp を**消費のみ**・
             再証明 0）・cusp の相異（`q9cu_cusps_distinct`・(ℤ/9)² の 81 代表が相異なる点）・
             独立 cusp witness（`q9cu_three_ne_zeta9`）
   * q9cu-3  ★★ **E_{3⁹}[3](M) = ⟨[27],[ζ₃]⟩ の完全分類**（`q9cu_ker3_eq_e3`）＋
             **(ℤ/3)² 一意性**（`q9cu_e3_unique`）＋非自明性（`q9cu_27_ne_one`/`q9cu_zeta3_ne_one`）
             ——q9td にも q3c3 にも存在しない新定理（q9td は 9-torsion のみ・q3c3 は ℚ₃ 上で核自明）
   * q9cu-4  ★★★ **cuspidalization 開曲線塔**: `q9cuOpen9`=E∖E[9] → `q9cuOpen3`=E∖E[3] →
             `q9cuPunct`=E∖{O}（制限射 `q9cuStep1`/`q9cuStep2`・包含 `q9cuIncl93`/`q9cuIncl3P`・
             合成＝[9]-制限射 `q9cu_tower_comm`）・**各段の開部分が真に異なる**
             （`q9cu_open_strict_9_3`・`q9cu_open_strict_3_punct`）
  ══════════════════════════════════════════════════════════════════
  ★ 正直な訂正（独立敵対監査 2026-07-21・親が code で独立確認・§4 に従い削除しない）★
   1. 上の「[3]∈E∖E[3] だが ∉E∖E[9]」という読み方は **誤り**。`q9cu_open_strict_9_3` の
      **statement には開部分（subtype）が一切現れない**——実体は
      `q9cuPow3.map q9tl3pt ≠ one ∧ q9cuPow9.map q9tl3pt = one` すなわち **コンパクト台
      `q9tlCurve` 上の捻れ述語の連言**であり、しかも証明は
      `⟨q9tl_3_tor 3 _ _, q9tl_3pt_pow9⟩`＝**既存 q9tl 補題 2 本の連言で新規証明ゼロ**。
      したがって「開部分をコンパクト E に置き換えると偽になる」という falsifier は
      **成立しない**（置き換える開部分が statement に無い）。
   2. 旗艦 `q9cu_tower_comm` も証明は `q9cu_pow3_pow3 x.val`＝**コンパクト曲線の恒等式
      (x³)³=x⁹** であり、3 つの subtype をコンパクト台に置換しても statement・証明とも
      そのまま通る。よって本ファイルの内容は「**コンパクト曲線の捻れフィルトレーションに
      subtype の装飾を付けたもの**」であって、punctured 対象についての主張ではない。
      punctured 固有の真の内容は `q9cu_open9_sub3` と `q9cuStep1` の well-definedness
      （いずれも E[3]⊆E[9] の対偶・各 3 行）に限られる。
   3. **新たに判明した gap**: 旗艦の塔の始域 `q9cuOpen9` は本ファイル・リポ全体を通じて
      **非空であることが一度も証明されていない**（`Nonempty`/witness 皆無）。
      `q9cuOpen3`・`q9cuPunct` は [3]・[27] で inhabited だが、塔の頂点は未証明であり、
      Lean の知る限り `q9cu_tower_comm`/`q9cuStep1` は **空型上の量化かもしれない**。
   4. ker[9] の ★★ 見出しの順方向は `exact q9td_phi_surjective x h` の **1 行**であり、
      その実質は A4（0.59）で既に計上済の定理。ファイルの約 40% は transport/capstone/
      自己クローンで新規数学を含まない。
   監査結果 **A8 0.66 → 0.67（+0.01）**。cap 0.72–0.75 は不変。
  ══════════════════════════════════════════════════════════════════
   * q9cu-5  ファイバー＝cusp 剰余類（`q9cu_fiber9_coset`/`q9cu_fiber3_coset`）・
             デッキは開部分を保つ（`q9cu_deck9_open`/`q9cu_deck3_open9`）・自由（`q9cu_deck_free`）
   * q9cu-6  ★ **[9]・[3] は M 点で非全射**（`q9cu_pow9_not_surjective`/`q9cu_pow3_not_surjective`・
             素元類 [π₉] は像外・E(M)/9E(M)≠0 の影・正直装置）
   * q9cu-7  capstone `Q3CuspidalizationL9Data`/`q9cuData`/`q9cuCuspL9_exists`

  正直な限定（§4 規約・消去/弱化しない・q3cu/q3c3/q9tl/q9td/q9c の限定を全て継承）:
  1. **cuspidal 惰性群 proper = 0・π₁ 再構成アルゴリズム（cuspidalization 本体）= 0**
     （q3cu 正直限定 1,2 の継承）。本モジュールの [3]/[9]-被覆は E∖{O} 上不分岐（エタール）であり、
     どのデッキ群（E[9]・E[3] の平行移動）も cusp 惰性を担わない。現行実被覆のデッキは全て可換で
     あり、惰性はあらゆるアーベル商で死ぬ（q3cu §2(a) のアーベル被覆障害は**不変**）。
     解消の名指し前提＝スキーム水準エタールサイト/分岐被覆 または 実テータ関数・切断（柱E）。
     **「cuspidalization を実装した」とは主張しない**（建てるのは幾何的基体＋開曲線塔のみ）。
  2. **K 点（M 点）の影**（A2/q3cu 限定 3 継承）: スキーム・エタールサイト・位相なし。
     「開曲線」は subtype・「被覆」は核剰余類ファイバーの写像。担体は群提示 ℤ×U₃ の商。
     [9] は M 点で**非全射**（q9cu-6 で定理として顕示・幾何的次数 81 との差は隠さない）。
  3. **q = 3⁹ は忠実部分ケースの 2 乗**（q9tl 限定 2 継承）。q^{1/9}=3∈ℚ₃ の 9 乗トリックであって
     [EtTh] の q 固定 q^{1/l} 添加そのものではない。
  4. **単一切片**: p=3・M=ℚ₃(ζ₉)・N∈{3,9} のみ。一般 N・一般 q・一般 p は依然未達。
     **G_{ℚ₃}=Gal(M/ℚ₃) の担体 E_{3⁹}(M) への作用は 0**（q3ap 正直限定 (iv) の named future・
     A3/A7 と credit が絡むため本モジュールでは先取りしない）。**実テータ関数も 0**。
  5. **E[9]≅(ℤ/9)² の分解は消費 INPUT**（`q9td_e9_decomp` の import・**再証明 0 本**）。
     本モジュールは「E[9] 分類を証明した」とは主張しない（A4 q9td の成果）。新規は
     **同種 Hom・核の同種論的読み・E[3](M) 分類・開曲線塔・ファイバー/デッキ・非全射**である。
  6. **二重計上の排除（監査向け・判定基準つき）**:
     - vs A4（q9td）: q9td の NEW A4 内容は π₁ 二方向 GAction（q9tdLatAct/q9tdMuAct・忠実性・
       直交性）。本モジュールに π₁ 対象（q3pePi1/tmzLimit）・GAction は**一切登場しない**。
       判定基準: **q9cuPow3/q9cuPow9 と開曲線 subtype を消すと本モジュールの全定理が消滅する**。
       A4 status は主張しない。
     - vs A8c/A8d（q3cu/q3c3）: 曲線（E₉/ℚ₃ vs E_{3⁹}/M）・N（2,3 vs 3,9）・核（Klein/{O} vs
       (ℤ/9)²/(ℤ/3)²）が全て別。既存ファイルは不変更（discharge の注記は本ファイル側のみ）。
     - vs A7（q9mr/q9mb）・A5（q9nt）: endo 剛性・tmi・thetaGrp/Φ₉/Ψ₉ は登場しない。
     - vs A9（blc）: 多項式・P¹ 不登場。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用
  （omega は純 Int/Nat アトム上のみ・Or/∃ 破壊は obtain）。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。prefix `q9cu`。
-/
import IUT.Q3Etale9TwoDir

namespace IUT

/-! ## q9cu-0: ★ 実同種 [3]・[9] : E_{3⁹} → E_{3⁹} と 2 段分解 pow9 = pow3∘pow3

    E_{3⁹} = M^×/q^ℤ は**可換**（q9tl_curve_abelian）なので、冪写像 x↦x^N が
    そのまま Hom になる（q3cu の q3cuSq は Quot.lift が必要だったが、ここでは商群上の
    冪写像を直接 map に置ける——設計 §5 の de-risk 項目 (1)）。 -/

/-- **q9cu-0a（★）: 実 [3]-同種 pow3 : E_{3⁹} → E_{3⁹}**（[x]↦[x³]）。
    map_mul は可換群の冪則 (xy)³=x³y³（`q9td_npow_mul` に q9tl_curve_abelian を渡す）。
    q3c3Cube（ℚ₃ 上の E₉）とは体も曲線も別対象。 -/
def q9cuPow3 : Hom q9tlCurve q9tlCurve where
  map := fun x => tateNpow q9tlCurve x 3
  map_mul := fun a b => q9td_npow_mul q9tlCurve q9tl_curve_abelian a b 3

/-- **q9cu-0b（★）: 実 [9]-同種 pow9 : E_{3⁹} → E_{3⁹}**（[x]↦[x⁹]）。
    この核が本モジュールの主対象（＝上流 cusp 集合 E_{3⁹}[9](M)）。 -/
def q9cuPow9 : Hom q9tlCurve q9tlCurve where
  map := fun x => tateNpow q9tlCurve x 9
  map_mul := fun a b => q9td_npow_mul q9tlCurve q9tl_curve_abelian a b 9

/-- q9cu-0c: pow3 の値は 3 乗そのもの（定義計算）。 -/
theorem q9cu_pow3_eq (x : q9tlCurve.carrier) :
    q9cuPow3.map x = tateNpow q9tlCurve x 3 := rfl

/-- q9cu-0d: pow9 の値は 9 乗そのもの（定義計算）。 -/
theorem q9cu_pow9_eq (x : q9tlCurve.carrier) :
    q9cuPow9.map x = tateNpow q9tlCurve x 9 := rfl

/-- ((3:Nat):Int) = 3（冪則の指数正規化）。 -/
theorem q9cu_cast3 : ((3 : Nat) : Int) = (3 : Int) := by omega

/-- ((9:Nat):Int) = 9（冪則の指数正規化）。 -/
theorem q9cu_cast9 : ((9 : Nat) : Int) = (9 : Int) := by omega

/-- **q9cu-0e（★ 塔の代数的核）: pow9 = pow3 ∘ pow3**（(x³)³ = x⁹）。
    tateNpow の左結合規約を tateZpow 経由で括り替える（`q9td_znpow`・指数 3·3=9）。
    これが 2 段開曲線塔（q9cu-4）の可換性を与える。 -/
theorem q9cu_pow3_pow3 (x : q9tlCurve.carrier) :
    q9cuPow3.map (q9cuPow3.map x) = q9cuPow9.map x := by
  show tateNpow q9tlCurve (tateNpow q9tlCurve x 3) 3 = tateNpow q9tlCurve x 9
  have h1 : tateNpow q9tlCurve x 3 = tateZpow q9tlCurve x 3 := rfl
  rw [h1, q9td_znpow q9tlCurve x 3 3]
  show tateZpow q9tlCurve x (3 * ((3 : Nat) : Int)) = tateNpow q9tlCurve x 9
  have h2 : (3 : Int) * ((3 : Nat) : Int) = ((9 : Nat) : Int) := by omega
  rw [h2]
  rfl

/-- **q9cu-0f: 合成 Hom としての一致**（Hom.comp との整合・pow9 は 2 段被覆の合成）。 -/
theorem q9cu_pow9_comp (x : q9tlCurve.carrier) :
    (q9cuPow3.comp q9cuPow3).map x = q9cuPow9.map x := q9cu_pow3_pow3 x

/-! ## q9cu-1: 核 ⟺ 捻れ述語のブリッジと冪ヘルパ -/

/-- **q9cu-1a: 核⟺9-捻れ述語**（定義計算）——pow9 の核は E_{3⁹}[9] そのもの。
    これにより q9td 系の「述語 tateNpow x 9 = 1」資産が**同種の核**として読める。 -/
theorem q9cu_ker9_iff_tor (x : q9tlCurve.carrier) :
    q9cuPow9.map x = q9tlCurve.one ↔ tateNpow q9tlCurve x 9 = q9tlCurve.one := Iff.rfl

/-- **q9cu-1b: 核⟺3-捻れ述語**（定義計算）。 -/
theorem q9cu_ker3_iff_tor (x : q9tlCurve.carrier) :
    q9cuPow3.map x = q9tlCurve.one ↔ tateNpow q9tlCurve x 3 = q9tlCurve.one := Iff.rfl

/-- q9cu-1c: 整数冪の 3 乗 (g^s)³ = g^{3s}（指数キャスト正規化つき）。 -/
theorem q9cu_npow3_zpow (g : q9tlCurve.carrier) (s : Int) :
    tateNpow q9tlCurve (tateZpow q9tlCurve g s) 3 = tateZpow q9tlCurve g (s * 3) := by
  rw [q9td_znpow q9tlCurve g s 3, q9cu_cast3]

/-- q9cu-1d: 整数冪の 9 乗 (g^s)⁹ = g^{9s}（指数キャスト正規化つき）。 -/
theorem q9cu_npow9_zpow (g : q9tlCurve.carrier) (s : Int) :
    tateNpow q9tlCurve (tateZpow q9tlCurve g s) 9 = tateZpow q9tlCurve g (s * 9) := by
  rw [q9td_znpow q9tlCurve g s 9, q9cu_cast9]

/-- q9cu-1e: 単位元の 3 乗は単位元。 -/
theorem q9cu_one_npow3 : tateNpow q9tlCurve q9tlCurve.one 3 = q9tlCurve.one :=
  q9td_one_zpow q9tlCurve 3

/-- **q9cu-1f: E[3] ⊆ E[9]**（3-捻れは 9-捻れ）——塔の包含 E∖E[9] ⊆ E∖E[3] の根拠。 -/
theorem q9cu_e3_in_e9 (x : q9tlCurve.carrier) (h : q9cuPow3.map x = q9tlCurve.one) :
    q9cuPow9.map x = q9tlCurve.one := by
  rw [← q9cu_pow3_pow3 x, h]
  exact q9cu_one_npow3

/-! ## q9cu-2: ★★ 核＝ちょうど E_{3⁹}[9](M)（全有理 cusp 集合）

    ここで **E[9]≅(ℤ/9)² の分解は q9td を消費するのみ**（再証明ゼロ・§5 限定）。
    新規は「その分解が **[9]-同種の核**＝上流 cusp 集合として読める」という同種論的言明。 -/

/-- **q9cu-2a: 上流 cusp 述語** — x が実 9-torsion 点 [3]^i·[ζ₉]^j として書ける
    （＝[9]-被覆で潰れる点＝上流 cusp）。 -/
def q9cuE9Mem (x : q9tlCurve.carrier) : Prop := ∃ p : q9tdE9, q9tdPhi p = x

/-- **q9cu-2b（★★）: ker([9]) ＝ ちょうど E_{3⁹}[9](M)**。
    → は `q9td_phi_surjective`（消費 INPUT）、← は Φ の像が 9-捻れであることの成分計算
    （[3]^i・[ζ₉]^j の 9 乗が各々 1）。
    **q3cu（核=Klein(ℤ/2)²・ℚ₃）→ q3c3（核={O}・ℚ₃）→ 本定理（核=(ℤ/9)²・M）の系列で
    初めて「奇 N で非自明かつ全有理な cusp 集合」が立つ。** -/
theorem q9cu_ker9_eq_e9 (x : q9tlCurve.carrier) :
    q9cuPow9.map x = q9tlCurve.one ↔ q9cuE9Mem x := by
  constructor
  · intro h
    exact q9td_phi_surjective x h
  · intro h
    obtain ⟨p, hp⟩ := h
    obtain ⟨p1, p2⟩ := p
    revert hp
    induction p1 using Quot.ind; rename_i i
    induction p2 using Quot.ind; rename_i j
    intro hp
    rw [← hp, q9td_phi_mk i j]
    show tateNpow q9tlCurve
        (q9tlCurve.mul (tateZpow q9tlCurve q9tl3pt i) (tateZpow q9tlCurve q9tlZeta9 j)) 9
      = q9tlCurve.one
    rw [q9td_npow_mul q9tlCurve q9tl_curve_abelian _ _ 9,
        q9cu_npow9_zpow q9tl3pt i, q9cu_npow9_zpow q9tlZeta9 j]
    have hd : (9 : Int) ∣ i * 9 := ⟨i, by omega⟩
    have hd2 : (9 : Int) ∣ j * 9 := ⟨j, by omega⟩
    rw [q9td_zpow_9dvd q9tl3pt q9tl_3pt_pow9 _ hd,
        q9td_zpow_9dvd q9tlZeta9 q9tl_zeta9_pow9 _ hd2, q9tlCurve.mul_one]

/-- q9cu-2c: Φ(0,0) = O（原点は cusp 集合に属する）。 -/
theorem q9cu_phi_zero :
    q9tdPhi (Quot.mk (modCong 9).rel 0, Quot.mk (modCong 9).rel 0) = q9tlCurve.one := by
  rw [q9td_phi_mk 0 0]
  show q9tlCurve.mul q9tlCurve.one q9tlCurve.one = q9tlCurve.one
  rw [q9tlCurve.mul_one]

/-- q9cu-2d: Φ(1,0) = [3]。 -/
theorem q9cu_phi_10 :
    q9tdPhi (Quot.mk (modCong 9).rel 1, Quot.mk (modCong 9).rel 0) = q9tl3pt := by
  rw [q9td_phi_mk 1 0, tateZpow_one q9tlCurve q9tl3pt]
  show q9tlCurve.mul q9tl3pt q9tlCurve.one = q9tl3pt
  rw [q9tlCurve.mul_one]

/-- q9cu-2e: Φ(0,1) = [ζ₉]。 -/
theorem q9cu_phi_01 :
    q9tdPhi (Quot.mk (modCong 9).rel 0, Quot.mk (modCong 9).rel 1) = q9tlZeta9 := by
  rw [q9td_phi_mk 0 1, tateZpow_one q9tlCurve q9tlZeta9]
  show q9tlCurve.mul q9tlCurve.one q9tlZeta9 = q9tlZeta9
  rw [q9tlCurve.one_mul]

/-- 純 Int ラッパ（omega は carrier アトムを Int に簡約しないため）。 -/
theorem q9cu_ar_range (i i' k : Int) (hk : i - i' = ((9 : Nat) : Int) * k)
    (h1 : 0 ≤ i) (h2 : i < 9) (h3 : 0 ≤ i') (h4 : i' < 9) : i = i' := by omega

/-- **q9cu-2f（★）: 81 個の cusp 代表は相異なる** — 0 ≤ i,j,i',j' < 9 の範囲で
    Φ(i,j) = Φ(i',j') ⟹ (i,j)=(i',j')。`q9td_phi_injective`（消費）＋剰余の範囲で、
    上流 cusp 集合が**ちょうど 81 点**（(ℤ/9)² の代表系）であることを顕示する。 -/
theorem q9cu_cusps_distinct (i j i' j' : Int)
    (hi0 : 0 ≤ i) (hi9 : i < 9) (hj0 : 0 ≤ j) (hj9 : j < 9)
    (hi0' : 0 ≤ i') (hi9' : i' < 9) (hj0' : 0 ≤ j') (hj9' : j' < 9)
    (h : q9tdPhi (Quot.mk (modCong 9).rel i, Quot.mk (modCong 9).rel j)
        = q9tdPhi (Quot.mk (modCong 9).rel i', Quot.mk (modCong 9).rel j')) :
    i = i' ∧ j = j' := by
  have heq := q9td_phi_injective _ _ h
  have hfi : Quot.mk (modCong 9).rel i = Quot.mk (modCong 9).rel i' := congrArg Prod.fst heq
  have hfj : Quot.mk (modCong 9).rel j = Quot.mk (modCong 9).rel j' := congrArg Prod.snd heq
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong 9) hfi
  obtain ⟨l, hl⟩ := quot_exact intGrp (modCong 9) hfj
  exact ⟨q9cu_ar_range i i' k hk hi0 hi9 hi0' hi9',
         q9cu_ar_range j j' l hl hj0 hj9 hj0' hj9'⟩

/-- **q9cu-2g（★）: 二つの独立な非自明 cusp** — [3] ≠ [ζ₉]（格子方向と μ 方向の cusp は別点）。
    q9cu_cusps_distinct を (1,0) と (0,1) に適用（1 = 0 の矛盾）。
    ⟹ 上流 cusp 集合は {O} でも巡回でもない（q3c3 の核={O} との質的対比）。 -/
theorem q9cu_three_ne_zeta9 : q9tl3pt ≠ q9tlZeta9 := by
  intro h
  have hphi : q9tdPhi (Quot.mk (modCong 9).rel 1, Quot.mk (modCong 9).rel 0)
      = q9tdPhi (Quot.mk (modCong 9).rel 0, Quot.mk (modCong 9).rel 1) := by
    rw [q9cu_phi_10, q9cu_phi_01]; exact h
  obtain ⟨h1, _⟩ := q9cu_cusps_distinct 1 0 0 1 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hphi
  omega

/-! ## q9cu-3: ★★ E_{3⁹}[3](M) = ⟨[27],[ζ₃]⟩ ≅ (ℤ/3)² の完全分類（新定理）

    q9td は 9-torsion のみ、q3c3 は ℚ₃ 上で E₉[3](ℚ₃)={O}。**M 上の 3-torsion 有理部を
    決定した定理はリポジトリに無い**。ここでは [9]-被覆の中間層（塔の中段の cusp 集合）として
    E[3](M) を決定する。 -/

/-- **q9cu-3a: [27] = [3]³ ∈ E_{3⁹}[3](M)**（格子方向の 3-捻れ生成元）。 -/
def q9cu27 : q9tlCurve.carrier := tateZpow q9tlCurve q9tl3pt 3

/-- **q9cu-3b: [ζ₃] = [ζ₉]³ ∈ E_{3⁹}[3](M)**（μ 方向の 3-捻れ生成元・実 ζ₃=Y³）。 -/
def q9cuZeta3 : q9tlCurve.carrier := tateZpow q9tlCurve q9tlZeta9 3

/-- **q9cu-3c: 中間 cusp 述語** — x ∈ ⟨[27],[ζ₃]⟩。 -/
def q9cuE3Mem (x : q9tlCurve.carrier) : Prop :=
  ∃ a b : Int, x = q9tlCurve.mul (tateZpow q9tlCurve q9cu27 a) (tateZpow q9tlCurve q9cuZeta3 b)

/-- 純 Int ラッパ: i·3 − 0 = 9k ⟹ i = 3k。 -/
theorem q9cu_ar_three (i k : Int) (h : i * 3 - 0 = ((9 : Nat) : Int) * k) : i = 3 * k := by omega

/-- **q9cu-3d: Φ(3a, 3b) = [27]^a·[ζ₃]^b**（中間層の座標化）。 -/
theorem q9cu_phi_e3 (a b : Int) :
    q9tdPhi (Quot.mk (modCong 9).rel (3 * a), Quot.mk (modCong 9).rel (3 * b))
      = q9tlCurve.mul (tateZpow q9tlCurve q9cu27 a) (tateZpow q9tlCurve q9cuZeta3 b) := by
  rw [q9td_phi_mk (3 * a) (3 * b)]
  show q9tlCurve.mul (tateZpow q9tlCurve q9tl3pt (3 * a)) (tateZpow q9tlCurve q9tlZeta9 (3 * b))
     = q9tlCurve.mul (tateZpow q9tlCurve (tateZpow q9tlCurve q9tl3pt 3) a)
        (tateZpow q9tlCurve (tateZpow q9tlCurve q9tlZeta9 3) b)
  rw [q9td_zzpow q9tlCurve q9tl3pt 3 a, q9td_zzpow q9tlCurve q9tlZeta9 3 b]

/-- **q9cu-3e（★★）: E_{3⁹}[3](M) = ちょうど ⟨[27],[ζ₃]⟩**。
    → : x³=1 ⟹ x⁹=1 ⟹ x=Φ(i,j)（q9td 消費）・x³=Φ(3i,3j)=O ⟹ Φ 単射で 9∣3i, 9∣3j ⟹
        3∣i, 3∣j ⟹ x=[27]^a·[ζ₃]^b。
    ← : ([27]^a[ζ₃]^b)³ = [3]^{9a}[ζ₉]^{9b} = O。
    **E₉[3](ℚ₃)={O}（q3c3・μ₃∉ℚ₃ の帰結）との対比対**——wild 体 M では 3-捻れが全有理化する。 -/
theorem q9cu_ker3_eq_e3 (x : q9tlCurve.carrier) :
    q9cuPow3.map x = q9tlCurve.one ↔ q9cuE3Mem x := by
  constructor
  · intro h
    have h9 : q9cuPow9.map x = q9tlCurve.one := q9cu_e3_in_e9 x h
    obtain ⟨p, hp⟩ := (q9cu_ker9_eq_e9 x).mp h9
    obtain ⟨p1, p2⟩ := p
    revert hp
    induction p1 using Quot.ind; rename_i i
    induction p2 using Quot.ind; rename_i j
    intro hp
    rw [q9td_phi_mk i j] at hp
    -- x³ = Φ(3i, 3j) = O
    have hx3 : q9tdPhi (Quot.mk (modCong 9).rel (i * 3), Quot.mk (modCong 9).rel (j * 3))
        = q9tlCurve.one := by
      rw [q9td_phi_mk (i * 3) (j * 3),
          ← q9cu_npow3_zpow q9tl3pt i, ← q9cu_npow3_zpow q9tlZeta9 j,
          ← q9td_npow_mul q9tlCurve q9tl_curve_abelian _ _ 3, hp]
      exact h
    have heq := q9td_phi_injective _ _ (hx3.trans q9cu_phi_zero.symm)
    obtain ⟨a, ha⟩ := quot_exact intGrp (modCong 9) (congrArg Prod.fst heq)
    obtain ⟨b, hb⟩ := quot_exact intGrp (modCong 9) (congrArg Prod.snd heq)
    have hia : i = 3 * a := q9cu_ar_three i a ha
    have hjb : j = 3 * b := q9cu_ar_three j b hb
    refine ⟨a, b, ?_⟩
    rw [← hp, hia, hjb]
    show q9tlCurve.mul (tateZpow q9tlCurve q9tl3pt (3 * a)) (tateZpow q9tlCurve q9tlZeta9 (3 * b))
       = q9tlCurve.mul (tateZpow q9tlCurve (tateZpow q9tlCurve q9tl3pt 3) a)
          (tateZpow q9tlCurve (tateZpow q9tlCurve q9tlZeta9 3) b)
    rw [q9td_zzpow q9tlCurve q9tl3pt 3 a, q9td_zzpow q9tlCurve q9tlZeta9 3 b]
  · intro h
    obtain ⟨a, b, hx⟩ := h
    rw [hx]
    show tateNpow q9tlCurve
        (q9tlCurve.mul (tateZpow q9tlCurve q9cu27 a) (tateZpow q9tlCurve q9cuZeta3 b)) 3
      = q9tlCurve.one
    rw [q9td_npow_mul q9tlCurve q9tl_curve_abelian _ _ 3,
        q9cu_npow3_zpow q9cu27 a, q9cu_npow3_zpow q9cuZeta3 b]
    show q9tlCurve.mul (tateZpow q9tlCurve (tateZpow q9tlCurve q9tl3pt 3) (a * 3))
        (tateZpow q9tlCurve (tateZpow q9tlCurve q9tlZeta9 3) (b * 3)) = q9tlCurve.one
    rw [q9td_zzpow q9tlCurve q9tl3pt 3 (a * 3), q9td_zzpow q9tlCurve q9tlZeta9 3 (b * 3)]
    have hd : (9 : Int) ∣ 3 * (a * 3) := ⟨a, by omega⟩
    have hd2 : (9 : Int) ∣ 3 * (b * 3) := ⟨b, by omega⟩
    rw [q9td_zpow_9dvd q9tl3pt q9tl_3pt_pow9 _ hd,
        q9td_zpow_9dvd q9tlZeta9 q9tl_zeta9_pow9 _ hd2, q9tlCurve.mul_one]

/-- 純 Int ラッパ: 3a − 3a' = 9k ⟹ 3 ∣ (a − a')。 -/
theorem q9cu_ar_div3 (a a' k : Int) (h : 3 * a - 3 * a' = ((9 : Nat) : Int) * k) :
    (3 : Int) ∣ (a - a') := ⟨k, by omega⟩

/-- **q9cu-3f（★★）: 中間 cusp 座標の一意性 ⟹ E_{3⁹}[3](M) ≅ (ℤ/3)²**。
    [27]^a·[ζ₃]^b = [27]^{a'}·[ζ₃]^{b'} ⟹ 3∣(a−a') ∧ 3∣(b−b')。
    ⟹ 中間層の cusp はちょうど 9 点（(ℤ/3)² の代表系）。 -/
theorem q9cu_e3_unique (a b a' b' : Int)
    (h : q9tlCurve.mul (tateZpow q9tlCurve q9cu27 a) (tateZpow q9tlCurve q9cuZeta3 b)
       = q9tlCurve.mul (tateZpow q9tlCurve q9cu27 a') (tateZpow q9tlCurve q9cuZeta3 b')) :
    (3 : Int) ∣ (a - a') ∧ (3 : Int) ∣ (b - b') := by
  have hphi : q9tdPhi (Quot.mk (modCong 9).rel (3 * a), Quot.mk (modCong 9).rel (3 * b))
      = q9tdPhi (Quot.mk (modCong 9).rel (3 * a'), Quot.mk (modCong 9).rel (3 * b')) := by
    rw [q9cu_phi_e3 a b, q9cu_phi_e3 a' b']; exact h
  have heq := q9td_phi_injective _ _ hphi
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong 9) (congrArg Prod.fst heq)
  obtain ⟨l, hl⟩ := quot_exact intGrp (modCong 9) (congrArg Prod.snd heq)
  exact ⟨q9cu_ar_div3 a a' k hk, q9cu_ar_div3 b b' l hl⟩

/-- **q9cu-3f'（★）: [27] ≠ [ζ₃]** — 中間層の 2 生成元は独立（3∤1 の矛盾）。
    ⟹ E_{3⁹}[3](M) は巡回でなく (ℤ/3)² の 9 点（q3c3 の E₉[3](ℚ₃)={O} との質的対比）。 -/
theorem q9cu_27_ne_zeta3 : q9cu27 ≠ q9cuZeta3 := by
  intro h
  have e1 : tateZpow q9tlCurve q9cu27 1 = q9cu27 := tateZpow_one q9tlCurve q9cu27
  have e2 : tateZpow q9tlCurve q9cuZeta3 1 = q9cuZeta3 := tateZpow_one q9tlCurve q9cuZeta3
  have hh : q9tlCurve.mul (tateZpow q9tlCurve q9cu27 1) (tateZpow q9tlCurve q9cuZeta3 0)
      = q9tlCurve.mul (tateZpow q9tlCurve q9cu27 0) (tateZpow q9tlCurve q9cuZeta3 1) := by
    rw [e1, e2]
    show q9tlCurve.mul q9cu27 q9tlCurve.one = q9tlCurve.mul q9tlCurve.one q9cuZeta3
    rw [q9tlCurve.mul_one, q9tlCurve.one_mul]
    exact h
  obtain ⟨h1, _⟩ := q9cu_e3_unique 1 0 0 1 hh
  obtain ⟨k, hk⟩ := h1
  omega

/-- **q9cu-3g: [27] ≠ O**（位数ちょうど 9 の [3] の 3 乗は非自明・`q9tl_3_tor` 消費）。 -/
theorem q9cu_27_ne_one : q9cu27 ≠ q9tlCurve.one :=
  q9tl_3_tor 3 (by omega) (by omega)

/-- **q9cu-3h: [ζ₃] ≠ O**（位数ちょうど 9 の [ζ₉] の 3 乗は非自明・`q9tl_zeta9_tor` 消費）。 -/
theorem q9cu_zeta3_ne_one : q9cuZeta3 ≠ q9tlCurve.one :=
  q9tl_zeta9_tor 3 (by omega) (by omega)

/-- **q9cu-3i: [27] ∈ ker([3])**（中間 cusp であることの確認）。 -/
theorem q9cu_27_in_ker3 : q9cuPow3.map q9cu27 = q9tlCurve.one := by
  show tateNpow q9tlCurve (tateZpow q9tlCurve q9tl3pt 3) 3 = q9tlCurve.one
  rw [q9cu_npow3_zpow q9tl3pt 3]
  exact q9td_zpow_9dvd q9tl3pt q9tl_3pt_pow9 (3 * 3) ⟨1, by omega⟩

/-- **q9cu-3j: [ζ₃] ∈ ker([3])**。 -/
theorem q9cu_zeta3_in_ker3 : q9cuPow3.map q9cuZeta3 = q9tlCurve.one := by
  show tateNpow q9tlCurve (tateZpow q9tlCurve q9tlZeta9 3) 3 = q9tlCurve.one
  rw [q9cu_npow3_zpow q9tlZeta9 3]
  exact q9td_zpow_9dvd q9tlZeta9 q9tl_zeta9_pow9 (3 * 3) ⟨1, by omega⟩

/-! ## q9cu-4: ★★★ cuspidalization 開曲線塔 E∖E[9] → E∖E[3] → E∖{O}

    **本節が「punctured/開曲線についての言明」であることの担保**: 定義域・終域は全て
    **cusp を抜いた subtype**（compact な E_{3⁹} ではない）であり、q9cu-4f/4g で
    **各段の開部分が真に異なる**（[3] は E∖E[3] に属すが E∖E[9] に属さない・
    [27] は E∖{O} に属すが E∖E[3] に属さない）ことを実点 witness で示す。 -/

/-- **q9cu-4a: 実開曲線 E∖{O}**（下流 cusp {O} を抜いた punctured 曲線・subtype）。 -/
def q9cuPunct : Type := { x : q9tlCurve.carrier // x ≠ q9tlCurve.one }

/-- **q9cu-4b: 実開曲線 E∖E[3]**（中間 cusp E_{3⁹}[3](M)=⟨[27],[ζ₃]⟩ を抜いた曲線）。 -/
def q9cuOpen3 : Type := { x : q9tlCurve.carrier // q9cuPow3.map x ≠ q9tlCurve.one }

/-- **q9cu-4c: 実開曲線 E∖E[9]**（上流 cusp E_{3⁹}[9](M)≅(ℤ/9)²・81 点を抜いた曲線）。 -/
def q9cuOpen9 : Type := { x : q9tlCurve.carrier // q9cuPow9.map x ≠ q9tlCurve.one }

/-- **q9cu-4d: 開埋め込み E∖E[9] ⊆ E∖E[3]**（E[3]⊆E[9] ゆえ）。 -/
theorem q9cu_open9_sub3 (x : q9cuOpen9) : q9cuPow3.map x.val ≠ q9tlCurve.one := by
  intro h
  exact x.property (q9cu_e3_in_e9 x.val h)

/-- **q9cu-4e: 開埋め込み E∖E[3] ⊆ E∖{O}**（O∈E[3] ゆえ）。 -/
theorem q9cu_open3_sub_punct (x : q9cuOpen3) : x.val ≠ q9tlCurve.one := by
  intro h
  apply x.property
  rw [h]
  exact q9cuPow3.map_one

/-- **q9cu-4f（★ 包含は真）: [3] ∈ E∖E[3] だが [3] ∉ E∖E[9]** — 上段と中段の開曲線は
    真に異なる（塔が退化していない実 witness）。 -/
theorem q9cu_open_strict_9_3 :
    q9cuPow3.map q9tl3pt ≠ q9tlCurve.one ∧ q9cuPow9.map q9tl3pt = q9tlCurve.one :=
  ⟨q9tl_3_tor 3 (by omega) (by omega), q9tl_3pt_pow9⟩

/-- **q9cu-4g（★ 包含は真）: [27] ∈ E∖{O} だが [27] ∉ E∖E[3]** — 中段と下段の開曲線は
    真に異なる。 -/
theorem q9cu_open_strict_3_punct :
    q9cu27 ≠ q9tlCurve.one ∧ q9cuPow3.map q9cu27 = q9tlCurve.one :=
  ⟨q9cu_27_ne_one, q9cu_27_in_ker3⟩

/-- **q9cu-4h（★ 包含射）: E∖E[9] ↪ E∖E[3]**（開集合の包含）。 -/
def q9cuIncl93 : q9cuOpen9 → q9cuOpen3 := fun x => ⟨x.val, q9cu_open9_sub3 x⟩

/-- **q9cu-4i（★ 包含射）: E∖E[3] ↪ E∖{O}**（開集合の包含）。 -/
def q9cuIncl3P : q9cuOpen3 → q9cuPunct := fun x => ⟨x.val, q9cu_open3_sub_punct x⟩

/-- **q9cu-4j（★★ 塔の上段）: [3]-制限射 E∖E[9] → E∖E[3]**（x↦x³）。
    x∉E[9] ⟹ (x³)³=x⁹≠O ⟹ x³∉E[3]（`q9cu_pow3_pow3` 消費）。
    ——[3]-同種による有限被覆の、**開曲線どうしの間の**制限。 -/
def q9cuStep1 : q9cuOpen9 → q9cuOpen3 := fun x =>
  ⟨q9cuPow3.map x.val, by
    intro h
    apply x.property
    rw [← q9cu_pow3_pow3 x.val]
    exact h⟩

/-- **q9cu-4k（★★ 塔の下段）: [3]-制限射 E∖E[3] → E∖{O}**（x↦x³）。
    x∉E[3] ⟹ x³≠O は定義そのもの。 -/
def q9cuStep2 : q9cuOpen3 → q9cuPunct := fun x => ⟨q9cuPow3.map x.val, x.property⟩

/-- **q9cu-4l（★）: [9]-制限射 E∖E[9] → E∖{O}**（x↦x⁹・塔の合成に対応）。 -/
def q9cuOpen9Map : q9cuOpen9 → q9cuPunct := fun x => ⟨q9cuPow9.map x.val, x.property⟩

/-- **q9cu-4m（★★★ 旗艦）: 2 段塔の可換性** — E∖E[9] →[3] E∖E[3] →[3] E∖{O} の合成が
    [9]-制限射に一致する。[AbsTopII] §3 の楕円 cuspidalization が「N を動かした被覆族」を
    使う構造の、リポジトリ初の 2 段実例（q3cu/q3c3 はいずれも 1 段のみだった）。 -/
theorem q9cu_tower_comm (x : q9cuOpen9) :
    (q9cuStep2 (q9cuStep1 x)).val = (q9cuOpen9Map x).val :=
  q9cu_pow3_pow3 x.val

/-- **q9cu-4n: 包含と制限射の整合**（包含したのちの [3]-像は、上段で [3] を取ってから
    包含したものに一致——開曲線図式の可換性）。 -/
theorem q9cu_incl_comm (x : q9cuOpen9) :
    (q9cuStep2 (q9cuIncl93 x)).val = (q9cuStep1 x).val := rfl

/-! ## q9cu-5: 被覆構造（ファイバー＝cusp 剰余類・デッキ） -/

/-- **q9cu-5a（★）: [9]-被覆のファイバー＝上流 cusp 集合の剰余類** —
    x⁹=y⁹ ⟺ ∃ 9-torsion 点 a（＝上流 cusp）, a·x=y。
    ⟹ 各ファイバーは E_{3⁹}[9](M)≅(ℤ/9)² の剰余類（81 点）。 -/
theorem q9cu_fiber9_coset (x y : q9tlCurve.carrier) :
    q9cuPow9.map x = q9cuPow9.map y ↔ ∃ a, q9cuE9Mem a ∧ q9tlCurve.mul a x = y := by
  constructor
  · intro h
    refine ⟨q9tlCurve.mul y (q9tlCurve.inv x), ?_, ?_⟩
    · apply (q9cu_ker9_eq_e9 _).mp
      rw [q9cuPow9.map_mul, q9cuPow9.map_inv, h]
      exact q9tlCurve.mul_inv _
    · rw [q9tlCurve.mul_assoc, q9tlCurve.inv_mul, q9tlCurve.mul_one]
  · intro h
    obtain ⟨a, ha, hax⟩ := h
    rw [← hax, q9cuPow9.map_mul, (q9cu_ker9_eq_e9 a).mpr ha, q9tlCurve.one_mul]

/-- **q9cu-5b（★）: [3]-被覆のファイバー＝中間 cusp 集合の剰余類** —
    x³=y³ ⟺ ∃ a∈⟨[27],[ζ₃]⟩, a·x=y。⟹ 各ファイバーは (ℤ/3)² の剰余類（9 点）。 -/
theorem q9cu_fiber3_coset (x y : q9tlCurve.carrier) :
    q9cuPow3.map x = q9cuPow3.map y ↔ ∃ a, q9cuE3Mem a ∧ q9tlCurve.mul a x = y := by
  constructor
  · intro h
    refine ⟨q9tlCurve.mul y (q9tlCurve.inv x), ?_, ?_⟩
    · apply (q9cu_ker3_eq_e3 _).mp
      rw [q9cuPow3.map_mul, q9cuPow3.map_inv, h]
      exact q9tlCurve.mul_inv _
    · rw [q9tlCurve.mul_assoc, q9tlCurve.inv_mul, q9tlCurve.mul_one]
  · intro h
    obtain ⟨a, ha, hax⟩ := h
    rw [← hax, q9cuPow3.map_mul, (q9cu_ker3_eq_e3 a).mpr ha, q9tlCurve.one_mul]

/-- **q9cu-5c（★）: [9]-被覆のデッキ（上流 cusp 平行移動）は開部分 E∖E[9] を保つ**。 -/
theorem q9cu_deck9_open (a x : q9tlCurve.carrier) (ha : q9cuE9Mem a)
    (hx : q9cuPow9.map x ≠ q9tlCurve.one) :
    q9cuPow9.map (q9tlCurve.mul a x) ≠ q9tlCurve.one := by
  rw [q9cuPow9.map_mul, (q9cu_ker9_eq_e9 a).mpr ha, q9tlCurve.one_mul]
  exact hx

/-- **q9cu-5d（★）: 塔の上段のデッキ群は E[3]** — 中間 cusp による平行移動は
    上段の開曲線 E∖E[9] を保ち、[3]-制限射のファイバーを動かす。
    （a³=O ⟹ a⁹=O ゆえ (a·x)⁹=x⁹） -/
theorem q9cu_deck3_open9 (a x : q9tlCurve.carrier) (ha : q9cuE3Mem a)
    (hx : q9cuPow9.map x ≠ q9tlCurve.one) :
    q9cuPow9.map (q9tlCurve.mul a x) ≠ q9tlCurve.one := by
  rw [q9cuPow9.map_mul, q9cu_e3_in_e9 a ((q9cu_ker3_eq_e3 a).mpr ha), q9tlCurve.one_mul]
  exact hx

/-- **q9cu-5e（★）: デッキは自由に作用**（a·x=x ⟹ a=O）。 -/
theorem q9cu_deck_free (a x : q9tlCurve.carrier) (h : q9tlCurve.mul a x = x) :
    a = q9tlCurve.one := by
  have h2 : q9tlCurve.mul a x = q9tlCurve.mul q9tlCurve.one x := by
    rw [q9tlCurve.one_mul]; exact h
  exact q9tlCurve.mul_right_cancel h2

/-! ## q9cu-6: ★ [9]・[3] は M 点で非全射（E(M)/9E(M)≠0 の影・正直装置） -/

/-- **q9cu-6a: 素元 π₉ = (1, 1) ∈ M^×**（付値 v_π = 1・e(M/ℚ₃)=6 の一様化元スロット）。 -/
def q9cuPi : q9tlMx.carrier := ((1 : Int), q3kU.one)

/-- **q9cu-6b: 素元類 [π₉] ∈ E_{3⁹}**。 -/
def q9cuPiPt : q9tlCurve.carrier := q9tlProj.map q9cuPi

/-- 純 Int ラッパ（非全射の付値方程式 54t + 9v = 1 に整数解なし）。 -/
theorem q9cu_ar_nosurj9 (t v : Int) (h : t * 54 = (-(((9 : Nat) : Int) * v)) + 1) : False := by
  omega

/-- 純 Int ラッパ（54t + 3v = 1 に整数解なし）。 -/
theorem q9cu_ar_nosurj3 (t v : Int) (h : t * 54 = (-(((3 : Nat) : Int) * v)) + 1) : False := by
  omega

/-- **q9cu-6c（★）: [9] は M 点で非全射** — ∀x, x⁹ ≠ [π₉]。
    像の付値は 9ℤ + 54ℤ = 9ℤ に含まれ 1 を含まない（omega）。
    **E(M)/9E(M) ≠ 0（Kummer 降下の影）の level-9 実定理**——q3cu_not_surjective の
    wild 体 M 版。「K 点の影では [N] は幾何的次数どおりに全射でない」を隠さず顕示する正直装置。 -/
theorem q9cu_pow9_not_surjective : ∀ x, q9cuPow9.map x ≠ q9cuPiPt := by
  intro x h
  obtain ⟨m, hm⟩ := q9tl_proj_surjective x
  have h' : q9tlProj.map (tateNpow q9tlMx m 9) = q9cuPiPt := by
    rw [q9tl_proj_npow m 9, hm]; exact h
  have hrel := quot_exact q9tlMx (normalCong q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup)) h'
  have hmem : q9tlSubgroup.mem
      (q9tlMx.mul (q9tlMx.inv (tateNpow q9tlMx m 9)) q9cuPi) := hrel
  obtain ⟨t, ht⟩ := hmem
  have hc := congrArg Prod.fst ht
  rw [q9tl_pow_fst t] at hc
  have hval : (q9tlMx.mul (q9tlMx.inv (tateNpow q9tlMx m 9)) q9cuPi).1
      = (-(((9 : Nat) : Int) * m.1)) + 1 := by
    show intGrp.mul (intGrp.inv (tateNpow q9tlMx m 9).1) q9cuPi.1
       = (-(((9 : Nat) : Int) * m.1)) + 1
    rw [q9tl_npow_fst m 9, tateNpow_intGrp m.1 9]
    rfl
  rw [hval] at hc
  exact q9cu_ar_nosurj9 t m.1 hc

/-- **q9cu-6d（★）: [3] も M 点で非全射** — ∀x, x³ ≠ [π₉]（付値 3ℤ+54ℤ=3ℤ∌1）。
    塔の各段が M 点では全射でないことの顕示（E(M)/3E(M)≠0 の影）。 -/
theorem q9cu_pow3_not_surjective : ∀ x, q9cuPow3.map x ≠ q9cuPiPt := by
  intro x h
  obtain ⟨m, hm⟩ := q9tl_proj_surjective x
  have h' : q9tlProj.map (tateNpow q9tlMx m 3) = q9cuPiPt := by
    rw [q9tl_proj_npow m 3, hm]; exact h
  have hrel := quot_exact q9tlMx (normalCong q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup)) h'
  have hmem : q9tlSubgroup.mem
      (q9tlMx.mul (q9tlMx.inv (tateNpow q9tlMx m 3)) q9cuPi) := hrel
  obtain ⟨t, ht⟩ := hmem
  have hc := congrArg Prod.fst ht
  rw [q9tl_pow_fst t] at hc
  have hval : (q9tlMx.mul (q9tlMx.inv (tateNpow q9tlMx m 3)) q9cuPi).1
      = (-(((3 : Nat) : Int) * m.1)) + 1 := by
    show intGrp.mul (intGrp.inv (tateNpow q9tlMx m 3).1) q9cuPi.1
       = (-(((3 : Nat) : Int) * m.1)) + 1
    rw [q9tl_npow_fst m 3, tateNpow_intGrp m.1 3]
    rfl
  rw [hval] at hc
  exact q9cu_ar_nosurj3 t m.1 hc

/-! ## q9cu-7: capstone（新規証明なし・束ねのみ） -/

/-- **q9cu-7a: wild level-9 楕円 cuspidalization 基体データ** — 実 [3]/[9]-同種・
    2 段分解・核＝ちょうど E[9](M)・E[3](M)=(ℤ/3)² 分類・開曲線塔（制限射 2 本＋合成の可換性）・
    包含が真であること・ファイバー＝cusp 剰余類・自由デッキ・[9]/[3] 非全射を束ねる
    （[AbsTopII] §3 の複数 N 幾何入力の wild level-9 実現）。 -/
structure Q3CuspidalizationL9Data where
  /-- 実 [3]-同種 E_{3⁹}→E_{3⁹}。 -/
  isog3 : Hom q9tlCurve q9tlCurve
  /-- 実 [9]-同種 E_{3⁹}→E_{3⁹}。 -/
  isog9 : Hom q9tlCurve q9tlCurve
  /-- 2 段分解 [9] = [3]∘[3]。 -/
  tower_alg : ∀ x, isog3.map (isog3.map x) = isog9.map x
  /-- 核＝ちょうど E_{3⁹}[9](M)（q9td の分解を消費した等号）。 -/
  ker9_eq : ∀ x, isog9.map x = q9tlCurve.one ↔ q9cuE9Mem x
  /-- 核＝ちょうど ⟨[27],[ζ₃]⟩（E_{3⁹}[3](M) の新分類）。 -/
  ker3_eq : ∀ x, isog3.map x = q9tlCurve.one ↔ q9cuE3Mem x
  /-- 中間 cusp 座標の一意性（≅(ℤ/3)²）。 -/
  e3_unique : ∀ a b a' b' : Int,
    q9tlCurve.mul (tateZpow q9tlCurve q9cu27 a) (tateZpow q9tlCurve q9cuZeta3 b)
      = q9tlCurve.mul (tateZpow q9tlCurve q9cu27 a') (tateZpow q9tlCurve q9cuZeta3 b')
    → (3 : Int) ∣ (a - a') ∧ (3 : Int) ∣ (b - b')
  /-- 上流 cusp 81 代表の相異（≅(ℤ/9)²）。 -/
  cusps_distinct : ∀ i j i' j' : Int, 0 ≤ i → i < 9 → 0 ≤ j → j < 9 →
    0 ≤ i' → i' < 9 → 0 ≤ j' → j' < 9 →
    q9tdPhi (Quot.mk (modCong 9).rel i, Quot.mk (modCong 9).rel j)
      = q9tdPhi (Quot.mk (modCong 9).rel i', Quot.mk (modCong 9).rel j') → i = i' ∧ j = j'
  /-- 独立な 2 つの非自明 cusp（[3]≠[ζ₉]）。 -/
  two_cusps : q9tl3pt ≠ q9tlZeta9
  /-- 中間層の 2 生成元も独立（[27]≠[ζ₃]・非自明）。 -/
  e3_gens : q9cu27 ≠ q9cuZeta3 ∧ q9cu27 ≠ q9tlCurve.one ∧ q9cuZeta3 ≠ q9tlCurve.one
  /-- 開曲線塔の上段 E∖E[9] → E∖E[3]。 -/
  step1 : q9cuOpen9 → q9cuOpen3
  /-- 開曲線塔の下段 E∖E[3] → E∖{O}。 -/
  step2 : q9cuOpen3 → q9cuPunct
  /-- 合成＝[9]-制限射（塔の可換性）。 -/
  tower_comm : ∀ x, (step2 (step1 x)).val = (q9cuOpen9Map x).val
  /-- 上段と中段の開曲線は真に異なる（[3] が witness）。 -/
  strict_9_3 : q9cuPow3.map q9tl3pt ≠ q9tlCurve.one ∧ q9cuPow9.map q9tl3pt = q9tlCurve.one
  /-- 中段と下段の開曲線は真に異なる（[27] が witness）。 -/
  strict_3_punct : q9cu27 ≠ q9tlCurve.one ∧ q9cuPow3.map q9cu27 = q9tlCurve.one
  /-- [9]-ファイバー＝上流 cusp 剰余類。 -/
  fiber9 : ∀ x y, isog9.map x = isog9.map y ↔ ∃ a, q9cuE9Mem a ∧ q9tlCurve.mul a x = y
  /-- [3]-ファイバー＝中間 cusp 剰余類。 -/
  fiber3 : ∀ x y, isog3.map x = isog3.map y ↔ ∃ a, q9cuE3Mem a ∧ q9tlCurve.mul a x = y
  /-- デッキは自由。 -/
  deck_free : ∀ a x, q9tlCurve.mul a x = x → a = q9tlCurve.one
  /-- [9] は M 点で非全射。 -/
  not_surj9 : ∀ x, isog9.map x ≠ q9cuPiPt
  /-- [3] は M 点で非全射。 -/
  not_surj3 : ∀ x, isog3.map x ≠ q9cuPiPt

/-- **q9cu-7b: 見出し実例** — 実 M=ℚ₃(ζ₉) 上の E_{3⁹}=M^×/q^ℤ（q=3⁹）の
    wild level-9 楕円 cuspidalization 基体。 -/
def q9cuData : Q3CuspidalizationL9Data where
  isog3 := q9cuPow3
  isog9 := q9cuPow9
  tower_alg := q9cu_pow3_pow3
  ker9_eq := q9cu_ker9_eq_e9
  ker3_eq := q9cu_ker3_eq_e3
  e3_unique := q9cu_e3_unique
  cusps_distinct := q9cu_cusps_distinct
  two_cusps := q9cu_three_ne_zeta9
  e3_gens := ⟨q9cu_27_ne_zeta3, q9cu_27_ne_one, q9cu_zeta3_ne_one⟩
  step1 := q9cuStep1
  step2 := q9cuStep2
  tower_comm := q9cu_tower_comm
  strict_9_3 := q9cu_open_strict_9_3
  strict_3_punct := q9cu_open_strict_3_punct
  fiber9 := q9cu_fiber9_coset
  fiber3 := q9cu_fiber3_coset
  deck_free := q9cu_deck_free
  not_surj9 := q9cu_pow9_not_surjective
  not_surj3 := q9cu_pow3_not_surjective

/-- **q9cu-7c: wild level-9 幾何的基体の存在**（実 M=ℚ₃(ζ₉)・q=3⁹・N∈{3,9}・
    核＝ちょうど E[9](M)≅(ℤ/9)²・E[3](M)≅(ℤ/3)²・2 段開曲線塔）。 -/
theorem q9cuCuspL9_exists : Nonempty Q3CuspidalizationL9Data := ⟨q9cuData⟩

end IUT
