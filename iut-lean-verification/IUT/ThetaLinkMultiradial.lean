-- M407F ThetaLinkMultiradial [実・本物・柱D]
-- complete_pct 影響: 柱D で 多輻表現(M372F)が横 theta-link(M328F, Θ^{2l}=q^{j²})と整合し、theta-link が
--   多輻表現の実 deg_ℝ 体積を ×2l で coherent に輸送する（theta-link then 降下 = 降下 then theta-link）
--   ことを実で建設（多輻的アルゴリズムが USE する「多輻性は theta-link と両立」の本物化）。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説。theta-link 整合は
--   実 deg_ℝ 体積/×2l スケール・段付き比較レベル（多輻不等式そのものではない）・格子不変は明示
--   (Ind3) m・μ シフトを除いて・局所体 K=ℚ_p・ℝ は setoid（realEq で言明）・多輻表現は (Ind1)(Ind2)-降下。

/-
  IUT/ThetaLinkMultiradial.lean — M407F（横 theta-link × 多輻表現の整合）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の先行建設 (b)・既存の theta-link/多輻表現/格子比較の (a) 束ね昇格）。
    本物の p 進局所体 K = ℚ_p・O_v = ℤ_p、および M318F の本物のテータ値 Θ(q,u_j)=u^{j²} の上で、
    M328F の**横 theta-link**（Θ^{2l}=q^{j²}、指数輸送 j² ↦ 2l·j²、実 deg_ℝ は ×2l）が、M372F の
    **多輻表現**（テータパイロット体積の (Ind1)(Ind2)-不変核 Σj² への降下）と**整合**することを本物で
    建てる。crux は導出しない。
  * complete_pct 影響: **前進**。M328F は theta-link 写像（Θ↔q 同一視）と次数変換 deg_ℝ(q^{j²})≈2l·deg_ℝ(Θ)
    を、M372F は多輻表現（実 deg_ℝ の (Ind1)(Ind2)-降下）を、M402F は多輻比較 ⇄ log-theta-lattice の
    coherence を本物化した。三者の**次の本物の一手**は、これらを **横 theta-link 上の多輻表現整合**へ束ねる:
      - **theta-link が多輻表現を coherent に輸送**: q パラメータ側総体積（M328F `thLinkQParamTotalVol`）は
        テータパイロット総体積の ×2l（M328F `thLink_total_degree`）で、テータパイロット体積は多輻表現へ
        降下する（M372F `mrp_representation_descent`）——ゆえ **theta-link を渡してから多輻降下**した値は
        **多輻降下してから theta-link で ×2l** した値に一致（realEq）。theta-link then 降下 = 降下 then
        theta-link の実 deg_ℝ 可換（多輻的アルゴリズムが USE する「多輻性は theta-link と両立」の本物）。
      - **theta-link 体積 = 格子の横辺体積**: theta-link の q パラメータ deg_ℝ(q^{j²})（M328F
        `thLinkQParamDeg`）は、M402F/M397F 格子正方形の**横辺**（横 theta-link ×2l スケール）の実 deg_ℝ
        体積 `ltlsSquareHV`（付値 n=j²）に一致し、その横辺は縦横可換（M397F `ltls_square_commutes_vol`）。
      - **多輻表現は theta-link 不変（明示不定性シフトを除いて）**: theta-link は横辺で表現を ×2l する
        （明示スケール）——(Ind3) 明示 m シフト（M372F `mrp_ind3_shift_core`）・格子 μ シフト（M397F
        `ltls_square_vol_shift`）を除いて表現は theta-link で不変（M402F `mlc_rep_lattice_invariant` を再利用）。
      - **theta-link 写像は多輻比較 coherence と両立**: M328F 写像 Θ↔q（`thLink_map_eq_qparam`）は M402F
        格子比較 coherence（`mlc_lattice_compare_coherent`、比較核 = 塔 graded 同型 ∧ 横 theta-link Θ↔q）
        と両立し、多輻表現の降下と連立する。
    crux Dβ-ω（多輻的アルゴリズム＝theta-link 整合が与える不等式＝IUT 論争の係争点）は
    **決して導出せず**外部仮説のまま。柱D の横 theta-link × 多輻表現の**整合を実で建設**。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  本層は M328F（`ThetaLinkReal`）・M372F（`MultiradialRep`）・M402F（`MultiradialLatticeCompare`、
  従属して M397F `LogThetaLatticeShell`）の**本物の対象**の上に、横 theta-link 上での多輻表現整合を新規に積む:
  * M407F-1 `tlm_thetaLink_transports_rep`/`tlm_thetaLink_rep_commutes`/`tlm_thetaLink_rep_square`
      — **theta-link が多輻表現を coherent に輸送**: theta-link then 降下 = 降下 then theta-link（実 deg_ℝ、
        M328F `thLink_total_degree` + M372F `mrp_representation_descent`）。
  * M407F-2 `tlm_thetaLink_vol_eq_lattice_edge`/`tlm_lattice_edge_commutes`/`tlm_thetaLink_edge_coherent`
      — **theta-link 体積 = 格子横辺体積**: q パラメータ deg_ℝ(q^{j²}) = 格子横辺 `ltlsSquareHV`（付値 j²）で、
        横辺は縦横可換（M397F `ltls_square_commutes_vol`）。
  * M407F-3 `tlm_rep_thetaLink_invariant_mod_ind` — **多輻表現が theta-link 不変（明示シフト除く）**: M372F
      (Ind3) 明示 m シフト・M397F 明示 μ シフトを除いて表現が theta-link ×2l 輸送で不変（M402F 再利用）。
  * M407F-4 `tlm_thetaLink_map_coherent_with_rep`/`tlm_compat_with_lattice_compare` — **theta-link 写像 Θ↔q が
      多輻比較 coherence と両立**（M328F `thLink_map_eq_qparam` + M402F `mlc_lattice_compare_coherent`）と
      多輻表現の降下の連立。
  * M407F-5 `tlm_crux_external`/`tlm_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M407F-6 capstone `ThetaLinkMultiradialData`/`thetaLinkMultiradialData`/`tlm_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）
  * **crux Dβ-ω（多輻的アルゴリズム＝theta-link 整合が与える不等式＝IUT 論争の当の係争点）は恒久的に
    本層の範囲外**。theta-link 上の多輻表現整合（`tlm_thetaLink_transports_rep` 等）は crux が「使う」
    構造的入力だが、**多輻不等式そのもの**は本層で決して証明せず、crux を任意の外部 Prop として受け取る
    だけ（`tlm_crux_is_hypothesis` は Iff.rfl）。
  * **整合は実 deg_ℝ 体積/×2l スケール・段付き比較レベル**。theta-link は指数を ×2l する明示スケールで、
    その下でのテータパイロット ⇄ ガウスパイロットの比較不等式（crux）は範囲外。群レベルの完全同変性は後続。
  * **多輻表現は M372F の (Ind1)(Ind2)-降下（Σj² 核）**。theta-link 不変は M372F (Ind3) 明示 m・M397F 明示 μ
    シフトを除いて。full な多輻アルゴリズム（theta-link 整合込みの不等式）は crux であり範囲外。
  * **局所体は K = ℚ_p（O_v = ℤ_p）**。テータ値の係数環 R は一般 CRing。**ℝ は setoid** ゆえ体積輸送・
    ×2l スケールは realEq で言明する。有理冪 q^{j²/2l} の分母 2l は微細格子 witness（指数の分子 j² が本物）。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク
  不使用（core Lean のみ）。共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更なし。
  柱D 横展開・本物の先行建設[実]。一般名は `tlm` 接頭辞で衝突回避。
-/
import IUT.MultiradialLatticeCompare
import IUT.MultiradialRep
import IUT.ThetaLinkReal

namespace IUT

/-! ## M407F-1: 横 theta-link が多輻表現を coherent に輸送する（theta-link then 降下 = 降下 then theta-link） -/

/-- **定理 (M407F-1a: theta-link が多輻表現を coherent に輸送・本丸)** — リンク先の q パラメータ側総体積
    Σ deg_ℝ(q^{j²})（M328F `thLinkQParamTotalVol`）は、多輻表現（M372F `mrpRepresentation`、テータ
    パイロット体積の (Ind1)(Ind2)-不変核 Σj² への降下）の **×2l 倍**にちょうど等しい:
      Σ deg_ℝ(q^{j²}) ≈ 2l · (多輻表現)。
    証明は M328F `thLink_total_degree`（q パラメータ総体積 ≈ 2l·テータパイロット総体積）と M372F
    `mrp_representation_descent`（テータパイロット体積 ≈ 多輻表現）を連結する。すなわち **theta-link を
    渡してから多輻降下**した値と、**多輻降下してから theta-link で ×2l** した値が一致する——横 theta-link
    が多輻表現を実 deg_ℝ で coherent に輸送する本物（多輻的アルゴリズムが USE する両立、crux 不等式でない）。 -/
theorem tlm_thetaLink_transports_rep (logq : Nat → RReal) (v l n : Nat) :
    realEq (thLinkQParamTotalVol logq v l n)
      (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n)) :=
  realEq_trans (thLink_total_degree logq v l n)
    (rmul_congr_right (intToReal ((2 * l : Nat) : Int)) (mrp_representation_descent logq v n))

/-- **定理 (M407F-1b: 降下は ×2l と可換)** — テータパイロット総体積の ×2l と多輻表現の ×2l は一致する
    （M372F `mrp_representation_descent` を ×2l で押し出す、`rmul_congr_right`）。theta-link の ×2l
    スケールが多輻降下の前後で整合する（表現側で ×2l しても同じ値）。 -/
theorem tlm_thetaLink_rep_commutes (logq : Nat → RReal) (v l n : Nat) :
    realEq (rmul (intToReal ((2 * l : Nat) : Int)) (thPilotTotalVol logq v n))
      (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n)) :=
  rmul_congr_right (intToReal ((2 * l : Nat) : Int)) (mrp_representation_descent logq v n)

/-- **定理 (M407F-1c: theta-link × 多輻の可換正方形)** — q パラメータ側総体積は、(i) **多輻降下 then ×2l**
    （2l · 多輻表現）と、(ii) **theta-link ×2l のみ**（2l · テータパイロット総体積）の**両方**に一致する。
    両者は M372F 降下（`mrp_representation_descent`）で結ばれる——theta-link then 降下 = 降下 then
    theta-link の可換正方形が実 deg_ℝ で閉じる本物。 -/
theorem tlm_thetaLink_rep_square (logq : Nat → RReal) (v l n : Nat) :
    realEq (thLinkQParamTotalVol logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n))
    ∧ realEq (thLinkQParamTotalVol logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (thPilotTotalVol logq v n)) :=
  ⟨tlm_thetaLink_transports_rep logq v l n, thLink_total_degree logq v l n⟩

/-! ## M407F-2: theta-link の体積 = log-theta-lattice の横辺の体積 -/

/-- **定理 (M407F-2a: theta-link 体積 = 格子横辺体積・本丸)** — theta-link の q パラメータの実 Arakelov
    次数 deg_ℝ(q^{j²})（M328F `thLinkQParamDeg` = logVolLocal v (2l·j²)）は、M402F/M397F の log-theta-lattice
    正方形の**横辺**（横 theta-link の ×2l 付値スケール）の実 deg_ℝ 体積 `ltlsSquareHV`（付値 n=j²）に
    **定義的に一致**する（両者とも logVolLocal v (2l·j²)、M328F `thLtorExp_sq` により指数 thLtorExp j = j·j）。
    横 theta-link 辺の多輻性（M402F が確立）の体積が theta-link の次数変換とちょうど同じ本物。 -/
theorem tlm_thetaLink_vol_eq_lattice_edge (logq : Nat → RReal) (v l : Nat) (j : Int) :
    thLinkQParamDeg logq v l j = ltlsSquareHV logq v l (j * j) :=
  rfl

/-- **定理 (M407F-2b: 格子横辺の縦横可換)** — log-theta-lattice 正方形の横辺（横 theta-link ×2l）の実
    deg_ℝ 体積 `ltlsSquareHV` は縦→横体積 `ltlsSquareVH` と可換（M397F `ltls_square_commutes_vol`）。
    theta-link が横辺として担う ×2l スケールが縦 log-link 輸送と交換する本物（実付値レベル）。 -/
theorem tlm_lattice_edge_commutes (logq : Nat → RReal) (v l : Nat) (n : Int) :
    realEq (ltlsSquareHV logq v l n) (ltlsSquareVH logq v l n) :=
  ltls_square_commutes_vol logq v l n

/-- **定理 (M407F-2c: theta-link 体積 = 可換な格子横辺体積)** — theta-link の q パラメータ deg_ℝ(q^{j²}) が
    格子横辺 `ltlsSquareHV`（付値 j²）に一致し、**かつ**その横辺が縦横可換であること（`ltls_square_commutes_vol`）
    を連立で束ねる。横 theta-link 辺の体積が M402F 格子正方形の横辺として coherent に閉じる本物。 -/
theorem tlm_thetaLink_edge_coherent (logq : Nat → RReal) (v l : Nat) (j : Int) :
    thLinkQParamDeg logq v l j = ltlsSquareHV logq v l (j * j)
    ∧ realEq (ltlsSquareHV logq v l (j * j)) (ltlsSquareVH logq v l (j * j)) :=
  ⟨rfl, ltls_square_commutes_vol logq v l (j * j)⟩

/-! ## M407F-3: 多輻表現が theta-link で不変（明示不定性シフトを除いて） -/

/-- **定理 (M407F-3: 多輻表現が theta-link 不変・明示シフトを除いて・本丸)** — 横 theta-link は多輻表現を
    格子の横辺で **×2l する明示スケール**であり、多輻表現はこの theta-link 輸送に対し**明示不定性シフトを
    除いて不変**である:
      (i) **表現側 (Ind3) 明示 m シフト**: (Ind3) 膨張後の実 deg_ℝ は **表現 ＋ 明示シフト** logVolLocal v m
          に等しい（M372F `mrp_ind3_shift_core`）——表現は (Ind3) で不変でなく明示 m だけずれる。
      (ii) **格子横辺側 M397F 明示 μ シフト**: 格子横辺の体積輸送は不定性 μ を **明示シフト** logVolLocal v μ
           を上乗せするだけで交換する（M397F `ltls_square_vol_shift`）。
      (iii) **theta-link の ×2l 輸送**: q パラメータ総体積は多輻表現の ×2l（`tlm_thetaLink_transports_rep`）。
    すなわち多輻表現は横 theta-link に対し、明示 (Ind3) m・μ シフトと ×2l スケールを除いて不変——
    「横 theta-link 上の多輻性」の正直な本物（不変核への降下 + 予測可能な明示ずれ + ×2l、crux 不等式でない）。 -/
theorem tlm_rep_thetaLink_invariant_mod_ind (logq : Nat → RReal) (v n : Nat) (m : Int) (l : Nat)
    (nn μ : Int) :
    (realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) m)
        (realAdd (mrpRepresentation logq v n) (logVolLocal logq v m))
      ∧ realEq (logLinkVolTransport logq v (ltlsThetaScaleVal l nn + μ))
        (realAdd (ltlsSquareHV logq v l nn) (logVolLocal logq v μ)))
    ∧ realEq (thLinkQParamTotalVol logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n)) :=
  ⟨mlc_rep_lattice_invariant logq v n m l nn μ, tlm_thetaLink_transports_rep logq v l n⟩

/-! ## M407F-4: theta-link 写像 Θ↔q が多輻比較 coherence と両立 -/

/-- **定理 (M407F-4a: theta-link 写像 Θ↔q が多輻表現の降下と両立)** — M328F の横 theta-link 写像
    thLinkMap R l j = thLinkQParam R l j（テータ値の 2l 乗 = q パラメータ q^{j²}）は、多輻表現の降下
    （M372F `mrp_representation_descent`、テータパイロット体積 ≈ 多輻表現）と**連立**する。横 theta-link の
    Θ↔q 同一視が多輻表現の実 deg_ℝ 降下と両方向で coherent な本物。 -/
theorem tlm_thetaLink_map_coherent_with_rep (R : CRing) (l : Nat) (j : Int)
    (logq : Nat → RReal) (v n : Nat) :
    thLinkMap R l j = thLinkQParam R l j
    ∧ realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n) :=
  ⟨thLink_map_eq_qparam R l j, mrp_representation_descent logq v n⟩

/-- **定理 (M407F-4b: theta-link 写像が多輻比較 ⇄ 格子 coherence と両立)** — M402F の多輻比較 ⇄
    log-theta-lattice coherence（`mlc_lattice_compare_coherent`: M362F 比較核 = M397F 塔 graded 同型 ∧
    横 theta-link Θ↔q 両立）と、多輻表現の降下（M372F `mrp_representation_descent`）が**同時に成立**する。
    横 theta-link 写像が格子上の多輻比較 coherence と多輻表現の降下の**両方**と両立する本物
    （crux 不等式は導出しない）。 -/
theorem tlm_compat_with_lattice_compare (p d l : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) (R : CRing) (j : Int)
    (logq : Nat → RReal) (v n : Nat) :
    ((∀ x : (principalUnits p).carrier, (unitFiltration p d).mem x →
        (mrcCompare p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x))
      ∧ (((∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
              (unitFiltration p d).mem u ∧ logLinkMap p d hp u = c)
          ∧ (∀ u : (principalUnits p).carrier, (unitFiltration p d).mem u →
              (logLinkMap p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)))
        ∧ thLinkMap R l j = thLinkQParam R l j))
    ∧ realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n) :=
  ⟨mlc_lattice_compare_coherent p d l hp hd R j, mrp_representation_descent logq v n⟩

/-! ## M407F-5: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M407F-5a: crux は外部仮説・決して導出しない／honest)** — 横 theta-link が多輻表現を coherent に
    輸送すること（`tlm_thetaLink_transports_rep`: q パラメータ総体積 ≈ 2l·多輻表現）は**無条件で本物**
    （crux とは独立に成立）。しかしその theta-link 上での**多輻的アルゴリズム**（theta-link 整合が与える
    crux Dβ-ω ＝ テータパイロット ⇄ ガウスパイロットの比較不等式 ＝ IUT 論争の当の係争点）は本層で
    **決して証明しない**。crux を任意の外部 Prop `crux` として受け取り、theta-link 輸送の本物性 **と** crux の
    連言を、crux が仮説として供給された場合にのみ返す——crux は決して導出されない。 -/
theorem tlm_crux_external (logq : Nat → RReal) (v l n : Nat)
    (crux : Prop) (hcrux : crux) :
    realEq (thLinkQParamTotalVol logq v l n)
      (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n)) ∧ crux :=
  ⟨tlm_thetaLink_transports_rep logq v l n, hcrux⟩

/-- **定理 (M407F-5b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明した定理ではなく、論争の係争点を
    そのまま外部仮説として受け取ったものであることを機械検証で明示（M328F `thLink_stage_hypothesis`・
    M372F `mrp_crux_is_hypothesis`・M402F `mlc_crux_is_hypothesis` と同じ精神）。 -/
theorem tlm_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M407F-6: capstone -/

/-- **M407F-6a: 横 theta-link × 多輻表現整合データ**（総括） — 本物の p 進局所体 K = ℚ_p・O_v = ℤ_p、
    M318F の本物のテータ値の上で、M328F 横 theta-link が M372F 多輻表現を実 deg_ℝ で coherent に輸送する
    （×2l）ことを束ねる: theta-link then 降下 = 降下 then theta-link・theta-link 体積 = 格子横辺体積（縦横
    可換）・多輻表現の降下・theta-link 写像 Θ↔q が格子比較 coherence と両立・表現が明示 (Ind3) m・μ シフトを
    除いて theta-link 不変。主語は M328F/M372F/M402F の本物であり toy を用いない。crux Dβ-ω は範囲外。 -/
structure ThetaLinkMultiradialData where
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
  /-- theta-link が多輻表現を ×2l で coherent に輸送（theta-link then 降下 = 降下 then theta-link）。 -/
  transports_rep : ∀ (logq : Nat → RReal) (v n : Nat),
    realEq (thLinkQParamTotalVol logq v l n)
      (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n))
  /-- theta-link の q パラメータ deg_ℝ(q^{j²}) = 格子横辺体積 `ltlsSquareHV`（付値 j²）。 -/
  vol_eq_edge : ∀ (logq : Nat → RReal) (v : Nat) (j : Int),
    thLinkQParamDeg logq v l j = ltlsSquareHV logq v l (j * j)
  /-- 格子横辺（横 theta-link ×2l）の実 deg_ℝ 体積が縦横可換。 -/
  edge_commutes : ∀ (logq : Nat → RReal) (v : Nat) (n : Int),
    realEq (ltlsSquareHV logq v l n) (ltlsSquareVH logq v l n)
  /-- theta-link 写像 Θ↔q（テータ値の 2l 乗 = q パラメータ）。 -/
  map_eq : ∀ (j : Int), thLinkMap R l j = thLinkQParam R l j
  /-- 多輻表現はテータパイロット体積の降下。 -/
  rep_descent : ∀ (logq : Nat → RReal) (v n : Nat),
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n)
  /-- 表現は theta-link 不変（明示 (Ind3) m シフト・M397F 明示 μ シフトを除いて）。 -/
  rep_shift : ∀ (logq : Nat → RReal) (v n : Nat) (m nn μ : Int),
    realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) m)
        (realAdd (mrpRepresentation logq v n) (logVolLocal logq v m))
    ∧ realEq (logLinkVolTransport logq v (ltlsThetaScaleVal l nn + μ))
        (realAdd (ltlsSquareHV logq v l nn) (logVolLocal logq v μ))

/-- **M407F-6b: witness** — K = ℚ_p（段 d=1）・l・R 上の本物の横 theta-link × 多輻表現整合データ。
    全フィールドを M407F-1〜3・M328F/M372F/M402F の本物で充足。 -/
def thetaLinkMultiradialData (p : Nat) (hp : 1 ≤ p) (l : Nat) (R : CRing) :
    ThetaLinkMultiradialData where
  p := p
  hp := hp
  d := 1
  hd := by omega
  l := l
  R := R
  transports_rep := fun logq v n => tlm_thetaLink_transports_rep logq v l n
  vol_eq_edge := fun logq v j => tlm_thetaLink_vol_eq_lattice_edge logq v l j
  edge_commutes := fun logq v n => tlm_lattice_edge_commutes logq v l n
  map_eq := fun j => thLink_map_eq_qparam R l j
  rep_descent := fun logq v n => mrp_representation_descent logq v n
  rep_shift := fun logq v n m nn μ => mlc_rep_lattice_invariant logq v n m l nn μ

/-- **M407F-6c: 存在** — 本物の横 theta-link × 多輻表現整合データは充足可能（K = ℚ₂・l=1・R = intRing）。
    M328F 横 theta-link が M372F 多輻表現を実 deg_ℝ で coherent に輸送し（×2l）、theta-link 体積 = 格子横辺
    体積・多輻表現が明示シフトを除いて theta-link 不変であることが実体化される（crux Dβ-ω は範囲外）。 -/
theorem tlm_exists : Nonempty ThetaLinkMultiradialData :=
  ⟨thetaLinkMultiradialData 2 (by omega) 1 intRing⟩

/-! ## M407F-6 実例（横 theta-link × 多輻表現整合の本物性） -/

/-- 実例（theta-link が多輻表現を ×2l 輸送・l=5, n=2）: q パラメータ総体積 ≈ 10·多輻表現。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thLinkQParamTotalVol logq v 5 2)
      (rmul (intToReal ((2 * 5 : Nat) : Int)) (mrpRepresentation logq v 2)) :=
  tlm_thetaLink_transports_rep logq v 5 2

/-- 実例（theta-link then 降下 = 降下 then theta-link・可換正方形・l=5, n=2）。 -/
example (logq : Nat → RReal) (v : Nat) :
    realEq (thLinkQParamTotalVol logq v 5 2)
        (rmul (intToReal ((2 * 5 : Nat) : Int)) (mrpRepresentation logq v 2))
    ∧ realEq (thLinkQParamTotalVol logq v 5 2)
        (rmul (intToReal ((2 * 5 : Nat) : Int)) (thPilotTotalVol logq v 2)) :=
  tlm_thetaLink_rep_square logq v 5 2

/-- 実例（theta-link 体積 = 格子横辺体積・l=5, j=2）: deg_ℝ(q^{4}) = 格子横辺（付値 4）。 -/
example (logq : Nat → RReal) (v : Nat) :
    thLinkQParamDeg logq v 5 2 = ltlsSquareHV logq v 5 (2 * 2) :=
  tlm_thetaLink_vol_eq_lattice_edge logq v 5 2

/-- 実例（表現が theta-link 不変・明示シフト除く・l=5, m=1, μ=1）: (Ind3) 明示 m・μ シフトと ×2l を除いて不変。 -/
example (logq : Nat → RReal) (v n : Nat) (nn : Int) :
    (realEq (indR_ind3Vol logq v (thPilotTotalVol logq v n) 1)
        (realAdd (mrpRepresentation logq v n) (logVolLocal logq v 1))
      ∧ realEq (logLinkVolTransport logq v (ltlsThetaScaleVal 5 nn + 1))
        (realAdd (ltlsSquareHV logq v 5 nn) (logVolLocal logq v 1)))
    ∧ realEq (thLinkQParamTotalVol logq v 5 n)
        (rmul (intToReal ((2 * 5 : Nat) : Int)) (mrpRepresentation logq v n)) :=
  tlm_rep_thetaLink_invariant_mod_ind logq v n 1 5 nn 1

/-- 実例（theta-link 写像 Θ↔q が多輻表現の降下と両立・l=5, j=1）。 -/
example (R : CRing) (logq : Nat → RReal) (v n : Nat) :
    thLinkMap R 5 1 = thLinkQParam R 5 1
    ∧ realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n) :=
  tlm_thetaLink_map_coherent_with_rep R 5 1 logq v n

/-- 実例（crux は外部仮説）: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  tlm_crux_is_hypothesis crux

/-- 実例（capstone 存在）: 横 theta-link × 多輻表現整合データは存在する。 -/
example : Nonempty ThetaLinkMultiradialData :=
  tlm_exists

end IUT
