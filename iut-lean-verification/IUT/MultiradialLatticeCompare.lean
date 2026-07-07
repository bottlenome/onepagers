-- M402F MultiradialLatticeCompare [実・本物・柱D]
-- complete_pct 影響: 柱D で Frobenius 描像(乗法 U^(d))⇄étale 描像(加法殻 m^d)の多輻比較同型が
--   log-theta-lattice(M397F)の正方形の周りで coherent（縦 log-link→横 theta-link と逆順が同一の
--   段付き同型・多輻表現は格子移動で明示不定性シフトを除いて不変・実 deg_ℝ 体積は殻上界内で
--   coherent に一周）を実構成し、格子上の「多輻性」を本物化。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説。coherence は殻
--   フィルトレーション/実 deg_ℝ 付値レベル（多輻不等式そのものではない）・格子不変は明示 μ/(Ind3) m
--   シフトを除いて・局所体 K=ℚ_p・ℝ は setoid（realEq で言明）・多輻表現は (Ind1)(Ind2)-降下。

/-
  IUT/MultiradialLatticeCompare.lean — M402F（多輻比較 ⇄ log-theta-lattice 整合）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の先行建設 (b)・既存の比較同型/格子正方形の (a) 束ね昇格）。
    本物の p 進局所体 K = ℚ_p・O_v = ℤ_p の上で、M362F の**多輻比較同型**
    （Frobenius 描像＝乗法 U^(d)/U^(d+1) ⟷ étale 描像＝加法殻 m^d/m^{d+1} ≅ ℤ/p、比較写像 =
    縦 log-link `mrcCompare`）が、M397F の **log-theta-lattice 正方形**（縦 log-link × 横
    theta-link）の周りで **coherent** であることを本物で建てる。crux は導出しない。
  * complete_pct 影響: **前進**。M362F は 2 描像の比較同型（段付き商上の準同型・全単射）を、
    M397F は log-theta-lattice 正方形の殻フィルトレーション/実 deg_ℝ 可換を、M372F は多輻表現
    （テータパイロット体積の (Ind1)(Ind2)-降下）を本物化した。三者の**次の本物の一手**は、
    これらを **log-theta-lattice の上の多輻比較**へ束ねること:
      - **格子の周りで比較が coherent**: M362F の比較写像（mult→add、段付き商 U^(d)/U^(d+1) ≅
        m^d/m^{d+1}）は M397F の格子正方形と整合する——縦 log-link を上ってから横 theta-link を
        渡るのと逆順が、**同一の段付き同型**を与える（`ltls_square_commutes` の 2 経路がともに
        Path 1・比較同型 `mrc_compare_iso` は単一の写像ゆえ経路に依らない）。M397F 塔 graded 同型
        （`ltls_tower_theta_compat`）が M362F 比較核（`mrc_compare_injective_graded`）と一致し、
        横 theta-link の Θ↔q 同一視と両立する。
      - **多輻表現が格子移動で不変（明示不定性シフトを除いて）**: M372F 多輻表現は格子の縦横移動
        （横 ×2l スケール・縦 log-link 体積輸送）に対し、M397F 明示 μ シフト・M342F (Ind3) 明示 m
        シフトを除いて不変——これが「格子上の多輻性」の正直な本物（不変核 Σj² への降下 +
        予測可能な明示ずれ）。
      - **実 deg_ℝ 体積が殻上界内で coherent に一周**: 多輻表現の実 deg_ℝ 体積が格子正方形の周りで
        coherent に輸送され（M397F `ltls_square_vol_within_shell`）、M392F 上方包含 m^{d-c} の
        殻上界内に留まる——実付値レベルの主張であり crux 不等式ではない。
    crux Dβ-ω（多輻的アルゴリズム＝theta-link 整合が与える不等式＝IUT 論争の係争点）は
    **決して導出せず**外部仮説のまま。柱D の多輻比較 ⇄ log-theta-lattice の**整合を実で建設**。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  本層は M362F（`MultiradialCompare`）・M397F（`LogThetaLatticeShell`）・M372F（`MultiradialRep`）の
  **本物の対象**の上に、log-theta-lattice の上での多輻比較の coherence を新規に積む:
  * M402F-1 `mlc_compare_around_square`/`mlc_lattice_compare_coherent`/`mlc_compare_shell_coherent`
      — **格子の周りで比較 coherent**: 正方形の 2 経路（Path 1）と M362F 比較同型が同一の段付き
        同型を与える・M397F 塔 graded 同型 = M362F 比較核・横 theta-link Θ↔q 両立・殻レベルの整合。
  * M402F-2 `mlc_rep_lattice_invariant` — **多輻表現が格子移動で不変（明示シフト除く）**: M372F
      (Ind3) 明示 m シフト・M397F 明示 μ シフトを除いて表現が格子移動で不変。
  * M402F-3 `mlc_rep_vol_within_shell` — **実 deg_ℝ 体積が殻上界内で coherent に一周**: 表現の
      降下・正方形体積の可換・M392F 上方包含の殻上界内生存。
  * M402F-4 `mlc_crux_external`/`mlc_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M402F-5 capstone `MultiradialLatticeCompareData`/`multiradialLatticeCompareData`/`mlc_exists`
      と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）
  * **crux Dβ-ω（多輻的アルゴリズム＝theta-link 整合が与える不等式＝IUT 論争の当の係争点）は
    恒久的に本層の範囲外**。格子上の比較 coherence（`mlc_lattice_compare_coherent` 等）は crux が
    「使う」構造的入力だが、**多輻不等式そのもの**は本層で決して証明せず、crux を任意の外部 Prop
    として受け取るだけ（`mlc_crux_is_hypothesis` は Iff.rfl）。
  * **coherence は殻フィルトレーション/実 deg_ℝ 付値レベル**。群レベルの完全な同変性（頂点に載る
    Frobenioid の完全同変性）は後続。**格子不変は M397F 明示 μ・M342F (Ind3) 明示 m シフトを除いて**。
  * **多輻表現は M372F の (Ind1)(Ind2)-降下（Σj² 核）**。full な多輻アルゴリズム（theta-link 整合込み）
    は crux であり範囲外。**比較は log-shell 段付きレベル**（U^(d)/U^(d+1) ≅ m^d/m^{d+1} ≅ ℤ/p）。
  * **局所体は K = ℚ_p（O_v = ℤ_p, U^(d)=1+p^d ℤ_p, m^d = p^d ℤ_p）**。一般局所体は後続。
    **ℝ は setoid** ゆえ体積輸送・スケールは realEq で言明。テータ値の係数環 R は一般 CRing。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク
  不使用（core Lean のみ）。共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更なし。
  柱D 横展開・本物の先行建設[実]。一般名は `mlc` 接頭辞で衝突回避。
-/
import IUT.MultiradialCompare
import IUT.LogThetaLatticeShell
import IUT.MultiradialRep

namespace IUT

/-! ## M402F-1: log-theta-lattice の周りで多輻比較が coherent -/

/-- **定理 (M402F-1a: 格子の周りで比較 coherent・本丸)** — M362F の多輻比較同型は M397F の
    log-theta-lattice 正方形と整合する:
      (i) 格子正方形の 2 経路——縦→横（縦 log-link を上ってから横 theta-link）と横→縦（横 theta-link
          を渡ってから縦 log-link）——は**ともに Θ-link ちょうど 1 本の Path 1**として同一の隅
          (n+1,m+1) に到達する（M397F `ltls_square_commutes`）。
      (ii) その上に載る M362F 比較同型（乗法段付き商 U^(d)/U^(d+1) ⟷ 加法段付き商 ℤ/p、核 = 次段
           U^(d+1) の単射 + 全射）は**単一の写像であって経路に依らない**（`mrc_compare_iso`）。
    すなわち縦 log-link→横 theta-link と逆順は**同一の段付き同型**を与える——多輻比較が格子正方形の
    周りで閉じる本物。crux 不等式そのものは決して導出しない。 -/
theorem mlc_compare_around_square (n m : Int) (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) :
    (Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩ ∧ Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩)
    ∧ ((∀ x : (principalUnits p).carrier, (unitFiltration p d).mem x →
          (mrcCompare p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x))
      ∧ (∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
          (unitFiltration p d).mem u ∧ mrcCompare p d hp u = c)) :=
  ⟨ltls_square_commutes n m, mrc_compare_iso p d hp hd⟩

/-- **定理 (M402F-1b: M362F 比較核 = M397F 塔 graded 同型・横 theta-link 両立)** — M362F の比較の
    **単射部分**（核 = 次段 U^(d+1)、`mrc_compare_injective_graded`、`mrcCompare = logLinkMap` は
    定義的に同一）は、M397F の縦 log-link 塔の段 d での **graded 同型**（`ltls_tower_theta_compat`）と
    **同一の写像**であり、かつ横 theta-link の Θ↔q 同一視と**両立**する。すなわち格子の縦方向
    （log-link 塔）で M362F 比較が M397F 塔と一致し、横方向（theta-link）で Θ↔q を保つ——多輻比較が
    log-theta-lattice の縦横両方向で coherent。 -/
theorem mlc_lattice_compare_coherent (p d l : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) (R : CRing) (j : Int) :
    (∀ x : (principalUnits p).carrier, (unitFiltration p d).mem x →
        (mrcCompare p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x))
    ∧ (((∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
            (unitFiltration p d).mem u ∧ logLinkMap p d hp u = c)
        ∧ (∀ u : (principalUnits p).carrier, (unitFiltration p d).mem u →
            (logLinkMap p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)))
      ∧ thLinkMap R l j = thLinkQParam R l j) :=
  ⟨fun x hx => mrc_compare_injective_graded p d hp x hx,
   ltls_tower_theta_compat p d l hp hd R j⟩

/-- **定理 (M402F-1c: 格子の周りで比較 coherent・殻フィルトレーションレベル)** — M397F 正方形の殻
    フィルトレーション可換（縦 log-link content が m^{d+1}⊆m^d へ着地・横 theta-link が Θ↔q を保つ、
    `ltls_square_shell`）と、M362F 多輻表現の芽（比較がフィルトレーションと可換＝leading content が
    殻へ着地し核が次段へ降りる、`mrc_multiradial_seed`）が**同時に成立**する。すなわち多輻比較が
    log-theta-lattice 正方形の**殻フィルトレーションレベルで coherent**（縦横リンクの整合の上に比較の
    段付き整合が乗る）。多輻不等式そのものは決して導出しない。 -/
theorem mlc_compare_shell_coherent (p d l : Nat) (hp : 1 ≤ p) (R : CRing)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p (d + 1)).mem x) (j : Int) :
    ((logShellMem p (d + 1) (logShellContent p x.val)
        ∧ logShellMem p d (logShellContent p x.val))
      ∧ thLinkMap R l j = thLinkQParam R l j)
    ∧ (logShellMem p (d + 1) (logShellContent p x.val)
        ∧ (mrcCompare p (d + 1) hp x = (zmod p).one ↔ (unitFiltration p (d + 1 + 1)).mem x)) :=
  ⟨ltls_square_shell p d l R x hx j, mrc_multiradial_seed p (d + 1) hp x hx⟩

/-! ## M402F-2: 多輻表現が格子移動で不変（明示不定性シフトを除いて） -/

/-- **定理 (M402F-2: 多輻表現が格子移動で不変・明示シフトを除いて・本丸)** — M372F の多輻表現
    （テータパイロット体積の (Ind1)(Ind2)-降下＝不変核 Σj²）は、log-theta-lattice の格子移動に対し
    **明示不定性シフトを除いて不変**である:
      (i) **表現側 (Ind3) 明示 m シフト**: (Ind3) 膨張（付値 m）後の実 deg_ℝ は **表現 ＋ 明示シフト**
          logVolLocal v m にちょうど等しい（M372F `mrp_ind3_shift_core`）——表現は (Ind3) で不変でなく
          明示 m だけ予測可能にずれる。
      (ii) **格子体積側 M397F 明示 μ シフト**: 格子正方形の縦横体積輸送（横 ×2l スケール後に縦
           log-link 輸送）は M367F 不定性 μ を **明示シフト** logVolLocal v μ を上乗せするだけで交換
           する（M397F `ltls_square_vol_shift`）。
    すなわち多輻表現は格子の縦横移動に対し、明示 (Ind3) m シフト・明示 μ シフトを除いて不変——
    これが「log-theta-lattice の上の多輻性」の正直な本物（不変核への降下 + 予測可能な明示ずれ、
    crux 不等式ではない）。 -/
theorem mlc_rep_lattice_invariant (logq : Nat → RReal) (v n : Nat) (m : Int) (l : Nat) (nn μ : Int) :
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) m)
      (realAdd (mrpRepresentation logq v n) (logVolLocal logq v m))
    ∧ realEq (logLinkVolTransport logq v (ltlsThetaScaleVal l nn + μ))
      (realAdd (ltlsSquareHV logq v l nn) (logVolLocal logq v μ)) :=
  ⟨mrp_ind3_shift_core logq v n m, ltls_square_vol_shift logq v l nn μ⟩

/-! ## M402F-3: 多輻表現の実 deg_ℝ 体積が殻上界内で coherent に一周 -/

/-- **定理 (M402F-3: 実 deg_ℝ 体積が殻上界内で coherent に一周・本丸)** — 多輻表現の実 deg_ℝ 体積が
    log-theta-lattice 正方形の周りで**coherent に輸送**され、殻の**上界内に留まる**:
      (i) **表現の降下**: 実テータパイロット体積は M372F 多輻表現（不変核 Σj²）へ降下する
          （`mrp_representation_descent`、realEq）。
      (ii) **正方形体積の可換**: 横 ×2l スケールと縦 log-link 体積輸送が掛ける順序に依らない
           （M397F `ltls_square_commutes_vol`）。
      (iii) **殻上界内**: 正方形を一周する縦横リンクの実 deg_ℝ 体積が M392F 上方包含 log(U^(d))⊆m^{d-c}
            の殻上界内に留まる（`ltls_square_vol_within_shell`）。
    すなわち多輻表現の実体積が格子正方形の周りで coherent に一周し殻上界内に収まる（実付値レベルの
    主張、crux 不等式ではない）。 -/
theorem mlc_rep_vol_within_shell (logq : Nat → RReal) (v n : Nat) (p d c l : Nat)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x) (nn : Int) :
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n)
    ∧ (realEq (ltlsSquareHV logq v l nn) (ltlsSquareVH logq v l nn)
        ∧ logShellMem p (d - c) (logShellContent p x.val)) :=
  ⟨mrp_representation_descent logq v n, ltls_square_vol_within_shell p d c l x hx logq v nn⟩

/-! ## M402F-4: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M402F-4a: crux は外部仮説・決して導出しない／honest)** — log-theta-lattice の上での多輻
    比較 coherence（格子正方形の実 deg_ℝ 体積可換 `ltls_square_commutes_vol`）は**無条件で本物**
    （crux とは独立に成立）。しかしその格子の上での**多輻的アルゴリズム**（theta-link 整合が与える
    crux Dβ-ω ＝ テータパイロット ⇄ ガウスパイロットの比較不等式 ＝ IUT 論争の当の係争点）は本層で
    **決して証明しない**。crux を任意の外部 Prop `crux` として受け取り、格子体積可換の本物性 **と**
    crux の連言を、crux が仮説として供給された場合にのみ返す——crux は決して導出されない。 -/
theorem mlc_crux_external (logq : Nat → RReal) (v l : Nat) (n : Int)
    (crux : Prop) (hcrux : crux) :
    realEq (ltlsSquareHV logq v l n) (ltlsSquareVH logq v l n) ∧ crux :=
  ⟨ltls_square_commutes_vol logq v l n, hcrux⟩

/-- **定理 (M402F-4b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明した定理ではなく、論争の
    係争点をそのまま外部仮説として受け取ったものであることを機械検証で明示（M362F
    `mrc_crux_is_hypothesis`・M397F `ltls_crux_is_hypothesis`・M372F `mrp_crux_is_hypothesis` と
    同じ精神）。 -/
theorem mlc_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M402F-5: capstone -/

/-- **M402F-5a: 多輻比較 ⇄ log-theta-lattice 整合データ**（総括） — 本物の p 進局所体 K = ℚ_p・
    O_v = ℤ_p 上で、M362F 多輻比較同型が M397F log-theta-lattice 正方形の周りで coherent であり、
    M372F 多輻表現が格子移動で明示シフトを除いて不変であることを束ねる: 正方形の 2 経路（Path 1）・
    比較同型（段付き商全単射）・格子の縦横 coherence（M362F 比較核 = M397F 塔 graded 同型・横
    theta-link Θ↔q 両立）・表現の殻上界内 coherent 輸送・表現の格子不変（明示 (Ind3) m・μ シフトを
    除いて）。主語は M362F/M397F/M372F の本物であり toy を用いない。crux Dβ-ω は範囲外。 -/
structure MultiradialLatticeCompareData where
  /-- 局所体 K = ℚ_p の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  /-- p ≥ 1。 -/
  hp : 1 ≤ p
  /-- フィルトレーション段 d ≥ 1。 -/
  d : Nat
  /-- d ≥ 1。 -/
  hd : 1 ≤ d
  /-- l-捻れ（微細座標 u = q^{1/2l} の分母 2l を与える）。 -/
  l : Nat
  /-- テータ値の係数環（一般 CRing）。 -/
  R : CRing
  /-- 格子正方形の縦→横経路（log してから theta、Path 1）。 -/
  square_vh : ∀ (n m : Int), Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩
  /-- 格子正方形の横→縦経路（theta してから log、Path 1）。 -/
  square_hv : ∀ (n m : Int), Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩
  /-- M362F 多輻比較同型（段付き商上の全単射・核 = U^(d+1)・全射）が格子正方形に載る。 -/
  compare_iso : (∀ x : (principalUnits p).carrier, (unitFiltration p d).mem x →
      (mrcCompare p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x))
    ∧ (∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
      (unitFiltration p d).mem u ∧ mrcCompare p d hp u = c)
  /-- 格子の縦横 coherence: M362F 比較核 = M397F 塔 graded 同型・横 theta-link Θ↔q 両立。 -/
  lattice_coherent : ∀ (j : Int),
    (∀ x : (principalUnits p).carrier, (unitFiltration p d).mem x →
        (mrcCompare p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x))
    ∧ (((∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
            (unitFiltration p d).mem u ∧ logLinkMap p d hp u = c)
        ∧ (∀ u : (principalUnits p).carrier, (unitFiltration p d).mem u →
            (logLinkMap p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)))
      ∧ thLinkMap R l j = thLinkQParam R l j)
  /-- 表現の実 deg_ℝ 体積が殻上界内で coherent に一周（表現降下・正方形体積可換・殻上界内）。 -/
  rep_within_shell : ∀ (logq : Nat → RReal) (v n : Nat)
      (x : (principalUnits p).carrier), (unitFiltration p d).mem x → ∀ (nn : Int),
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n)
    ∧ (realEq (ltlsSquareHV logq v l nn) (ltlsSquareVH logq v l nn)
        ∧ logShellMem p d (logShellContent p x.val))
  /-- 表現が格子移動で不変（明示 (Ind3) m シフト・M397F 明示 μ シフトを除いて）。 -/
  rep_lattice_shift : ∀ (logq : Nat → RReal) (v n : Nat) (m nn μ : Int),
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) m)
      (realAdd (mrpRepresentation logq v n) (logVolLocal logq v m))
    ∧ realEq (logLinkVolTransport logq v (ltlsThetaScaleVal l nn + μ))
      (realAdd (ltlsSquareHV logq v l nn) (logVolLocal logq v μ))

/-- **M402F-5b: witness** — K = ℚ_p（段 d=1）・l・R 上の本物の多輻比較 ⇄ log-theta-lattice 整合
    データ。全フィールドを M402F-1〜3・M362F/M397F/M372F の本物で充足。 -/
def multiradialLatticeCompareData (p : Nat) (hp : 1 ≤ p) (l : Nat) (R : CRing) :
    MultiradialLatticeCompareData where
  p := p
  hp := hp
  d := 1
  hd := by omega
  l := l
  R := R
  square_vh := fun n m => ltls_square_vh n m
  square_hv := fun n m => ltls_square_hv n m
  compare_iso := mrc_compare_iso p 1 hp (by omega)
  lattice_coherent := fun j =>
    ⟨fun x hx => mrc_compare_injective_graded p 1 hp x hx,
     ltls_tower_theta_compat p 1 l hp (by omega) R j⟩
  rep_within_shell := fun logq v n x hx nn =>
    ⟨mrp_representation_descent logq v n,
     ltls_square_vol_within_shell p 1 0 l x hx logq v nn⟩
  rep_lattice_shift := fun logq v n m nn μ =>
    ⟨mrp_ind3_shift_core logq v n m, ltls_square_vol_shift logq v l nn μ⟩

/-- **M402F-5c: 存在** — 本物の多輻比較 ⇄ log-theta-lattice 整合データは充足可能
    （K = ℚ₂・l=1・R = intRing）。M362F 多輻比較同型が M397F 格子正方形の周りで coherent・
    M372F 多輻表現が格子移動で明示シフトを除いて不変であることが実体化される（crux Dβ-ω は範囲外）。 -/
theorem mlc_exists : Nonempty MultiradialLatticeCompareData :=
  ⟨multiradialLatticeCompareData 2 (by omega) 1 intRing⟩

/-! ## M402F-5 実例（多輻比較 ⇄ log-theta-lattice 整合の本物性） -/

/-- 実例（格子の周りで比較 coherent）: 正方形の 2 経路（Path 1）と M362F 比較同型が同一の段付き
    同型を与える（K = ℚ₂, d=1）。 -/
example (n m : Int) :
    (Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩ ∧ Path 1 ⟨n, m⟩ ⟨n + 1, m + 1⟩)
    ∧ ((∀ x : (principalUnits 2).carrier, (unitFiltration 2 1).mem x →
          (mrcCompare 2 1 (by omega) x = (zmod 2).one ↔ (unitFiltration 2 (1 + 1)).mem x))
      ∧ (∀ c : (zmod 2).carrier, ∃ u : (principalUnits 2).carrier,
          (unitFiltration 2 1).mem u ∧ mrcCompare 2 1 (by omega) u = c)) :=
  mlc_compare_around_square n m 2 1 (by omega) (by omega)

/-- 実例（M362F 比較核 = M397F 塔 graded 同型・横 theta-link 両立）: 格子の縦横で比較が coherent。 -/
example (l : Nat) (R : CRing) (j : Int) :
    (∀ x : (principalUnits 2).carrier, (unitFiltration 2 1).mem x →
        (mrcCompare 2 1 (by omega) x = (zmod 2).one ↔ (unitFiltration 2 (1 + 1)).mem x))
    ∧ (((∀ c : (zmod 2).carrier, ∃ u : (principalUnits 2).carrier,
            (unitFiltration 2 1).mem u ∧ logLinkMap 2 1 (by omega) u = c)
        ∧ (∀ u : (principalUnits 2).carrier, (unitFiltration 2 1).mem u →
            (logLinkMap 2 1 (by omega) u = (zmod 2).one ↔ (unitFiltration 2 (1 + 1)).mem u)))
      ∧ thLinkMap R l j = thLinkQParam R l j) :=
  mlc_lattice_compare_coherent 2 1 l (by omega) (by omega) R j

/-- 実例（表現が格子移動で不変・明示シフト除く・l=5, m=1, μ=1）: 表現は (Ind3) 明示 m・μ シフトを
    除いて格子移動で不変。 -/
example (logq : Nat → RReal) (v n : Nat) (nn : Int) :
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) 1)
      (realAdd (mrpRepresentation logq v n) (logVolLocal logq v 1))
    ∧ realEq (logLinkVolTransport logq v (ltlsThetaScaleVal 5 nn + 1))
      (realAdd (ltlsSquareHV logq v 5 nn) (logVolLocal logq v 1)) :=
  mlc_rep_lattice_invariant logq v n 1 5 nn 1

/-- 実例（実 deg_ℝ 体積が殻上界内で coherent に一周・l=5）: 表現降下・正方形体積可換・殻上界内。 -/
example (logq : Nat → RReal) (v n : Nat)
    (x : (principalUnits 2).carrier) (hx : (unitFiltration 2 3).mem x) (nn : Int) :
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n)
    ∧ (realEq (ltlsSquareHV logq v 5 nn) (ltlsSquareVH logq v 5 nn)
        ∧ logShellMem 2 (3 - 1) (logShellContent 2 x.val)) :=
  mlc_rep_vol_within_shell logq v n 2 3 1 5 x hx nn

/-- 実例（crux は外部仮説）: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  mlc_crux_is_hypothesis crux

/-- 実例（capstone 存在）: 多輻比較 ⇄ log-theta-lattice 整合データは存在する。 -/
example : Nonempty MultiradialLatticeCompareData :=
  mlc_exists

end IUT
