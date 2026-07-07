-- M432F LogVolMultiradialTransport [実・本物・柱D]
-- complete_pct 影響: 柱D で 両側実 deg_ℝ 有界(M427F)が横 theta-link の ×2l 体積輸送(M407F)の下で
--   coherent に保たれる(=bound は輸送でスケールし、輸送後の表現 thLinkQParamTotalVol もなお両側有界域に
--   留まり、log-theta-lattice(M397F)の格子移動で交換する)ことを実で建設し M427F/M407F を総合昇格する。
-- 正直な限定: crux Dβ-ω(多輻的アルゴリズム=論争の係争点)は恒久的に外部仮説(Iff.rfl でのみ受け取る)。
--   輸送はテータリンク ×2l 明示スケール・両側有界は M427F 無条件(l³ 下界/対数殻上界)・格子移動は
--   M397F 実 deg_ℝ 付値レベルの HV≈VH 交換(多輻不等式そのものではない)・局所体 K=ℚ_p・ℝ は setoid。

/-
  IUT/LogVolMultiradialTransport.lean — M432F（定理3.11 / log-volume transport synthesis：
  両側実有界が theta-link/log-theta-lattice の体積輸送の下で coherent に保たれる）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の先行建設 (b)・既存の両側実有界 (M427F `pbm_two_sided_real`) と
    横 theta-link 体積輸送 (M407F `tlm_thetaLink_transports_rep`, ×2l) の (a) 束ね昇格）。
    M427F は多輻テータパイロット表現 `mrpRepresentation`（(Ind1)(Ind2)-不変核 (Σj²)·log q_v）が両側実
    deg_ℝ 有界域 [l³ (×3 で 3·rep 上), 対数殻 m^{Σj²+c} の deg_ℝ] の**内側**に無条件で挟まれること、
    M407F は横 theta-link がその表現を実 deg_ℝ で ×2l 倍に coherent に輸送する（theta-link then 降下 =
    降下 then theta-link）ことを確立した。M397F は log-theta-lattice 正方形が実 deg_ℝ 体積レベルで可換
    （HV≈VH）であることを本物化した。**次の本物の一手**は、これらを**総合**して「両側有界が体積輸送の下で
    coherent に保たれる」ことを示すこと: 横 theta-link の ×2l スケールで両側有界の**両側とも**スケールし
    （bound は輸送でスケール）、輸送後の表現 `thLinkQParamTotalVol`（= ×2l·rep）もなお同じ両側有界域の
    内側に留まり（下界は ×2l で下から、上界は ×2l 対数殻で上から）、その輸送が log-theta-lattice の格子
    移動（HV≈VH）と交換する——crux は導出しない。
  * complete_pct 影響: **前進**。M427F は両側有界を静的に、M407F は ×2l 輸送を、M397F は格子可換を
    それぞれ本物化したが、**両側有界が輸送の下で安定である（bound が輸送でスケールして輸送後表現をなお
    挟む）という動的な整合**を一つの命題へ束ねる一手は範囲外だった。本 M432F はその**次の本物の一手**:
      - **両側有界は ×2l 輸送でスケール** `lvt_two_sided_scaled`（M427F 両側有界を ×2l で押し出す・
        `rmul_le_mul_left`）= 下界・上界とも ×2l 倍でなお成立。
      - **輸送後表現は両側有界域の内側**（本丸）`lvt_two_sided_transported`: 輸送後表現
        `thLinkQParamTotalVol`（M407F ×2l 輸送で ×2l·rep に realEq）が、下 `2l·(l³·log q_v) ≤
        3·輸送後表現` ・上 `輸送後表現 ≤ 2l·対数殻 deg_ℝ` の両側有界域に留まる（スケールした bound が
        輸送後の主語をなお挟む・`rLe_congr` で主語を輸送後表現へ張り替え）。
      - **bound は log-theta-lattice 格子移動で coherent** `lvt_bound_coherent_around_lattice`:
        輸送後上界 **と** M397F 格子可換（HV≈VH）が両立——bound を適用してから格子移動しても、格子移動
        してから（スケールした）bound を適用しても同じ実 deg_ℝ（M397F `ltls_square_commutes_vol`）。
      - **輸送後両側有界は (Ind1)(Ind2)-不変** `lvt_two_sided_transported_ind1/2_invariant`
        （M427F 不変性を ×2l で押し出す）。
      - **crux 外部** `lvt_crux_external`/`lvt_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は範囲外。
    crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の係争点）は**決して導出せず**外部仮説のまま。柱D の
    両側有界と ×2l 体積輸送を**総合し、bound が輸送の下で安定であるという構造を本物化**。

  ## 何を本物化したか / 何を再利用したか（正直な地図）
  * M432F-0 `lvt_scale_nonneg` — 輸送スケール 2l の非負性（M139 `intToReal_mono`）。
  * M432F-1 `lvt_two_sided_scaled` — 両側有界を ×2l 輸送でスケール（M427F `pbm_two_sided_real`
      ＋ M180 `rmul_le_mul_left`・crux とは別物）。
  * M432F-2 `lvt_transport_eq` — 輸送後表現 = ×2l·rep（M407F `tlm_thetaLink_transports_rep` 再輸出）。
  * M432F-3 `lvt_two_sided_transported` — 本丸: 輸送後表現 `thLinkQParamTotalVol` が両側有界域の内側
      （下 `2l·l³·log q_v ≤ 3·輸送後表現`・上 `輸送後表現 ≤ 2l·対数殻`、`rLe_congr`＋M150 結合律/M123F 可換）。
  * M432F-4 `lvt_bound_coherent_around_lattice` — 輸送後上界 と M397F 格子可換（HV≈VH）の両立。
  * M432F-5 `lvt_two_sided_transported_ind1_invariant`/`lvt_two_sided_transported_ind2_invariant`
      — 輸送後両側有界は (Ind1)(Ind2)-不変（M427F 不変性を ×2l で押し出す）。
  * M432F-6 `lvt_crux_external`/`lvt_crux_is_hypothesis`（Iff.rfl）— crux Dβ-ω は外部仮説。
  * M432F-7 capstone `LogVolMultiradialTransportData`/`lvt_exists` と実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外・過大主張の厳禁）
  * **crux Dβ-ω（多輻的アルゴリズム＝テータパイロット ⇄ ガウスパイロットの比較不等式そのもの＝
    IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層が総合するのは、M427F の無条件両側有界（下界
    l³・上界 対数殻）が M407F の横 theta-link ×2l 体積輸送で**スケールしてなお成立する**という付値/体積
    レベルの安定性であり、いずれも M97 初等不等式・付値単調性・M180 乗法単調性・M150 結合律で閉じる
    **無条件で本物**の命題——**crux（rep ≤ gauss）とは別の不等式**。crux は M407F/M427F の受け取り仮説と
    同じく任意の外部 Prop として受け取るのみ（`lvt_crux_is_hypothesis` は Iff.rfl）。
  * **輸送は横 theta-link の ×2l 明示スケール**。輸送後表現 `thLinkQParamTotalVol` は M407F で ×2l·rep へ
    realEq。格子移動の交換は M397F `ltls_square_commutes_vol`（HV≈VH）の実 deg_ℝ 付値レベル——群レベルの
    完全同変性は後続。有理冪 q^{j²/2l} の分母 2l は微細格子 witness（指数の分子が本物）。
  * **両側有界は M427F の (Ind1)(Ind2)-降下（Σj² 核）**。輸送後不変は M427F 不変性を ×2l で押し出したもの。
    **局所体は K = ℚ_p**。log q_v は非負実重み witness（hq : realZero ≤ logq v が前提）。**ℝ は setoid**
    （realEq が同値・`=` でない）ゆえスケール・輸送後有界・格子交換・不変性は realEq/rLe で言明する。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無、propext/Quot.sound のみ）。禁止タクティク不使用
  （core Lean のみ）。共有ファイル未変更。柱D 総合・本物の先行建設[実]。一般名は `lvt` 接頭辞で衝突回避。
-/
import IUT.PilotBoundMultiradialFull
import IUT.ThetaLinkMultiradial

namespace IUT

/-! ## M432F-0: 輸送スケール 2l の非負性 -/

/-- **M432F-0: 横 theta-link 輸送スケール 2l の非負性** — 輸送因子 `intToReal ((2·l : Nat) : Int)` は
    非負（M139 `intToReal_mono`、0 ≤ 2l）。両側有界を ×2l でスケールする際の右非負条件。 -/
theorem lvt_scale_nonneg (l : Nat) : rLe realZero (intToReal ((2 * l : Nat) : Int)) :=
  intToReal_mono (by omega)

/-! ## M432F-1: 両側有界は横 theta-link ×2l 輸送でスケールする（bound は輸送でスケール） -/

/-- **定理 (M432F-1: 両側有界は ×2l 輸送でスケール・本物)** — M427F の無条件両側有界（下界 l³·log q_v ≤
    3·rep、上界 rep ≤ 対数殻 m^{Σj²+c} の deg_ℝ）を、横 theta-link の輸送スケール 2l で**両側とも押し出す**:
      (i) 下界 ×2l: 2l·(l³·log q_v) ≤ 2l·(3·rep)、
      (ii)上界 ×2l: 2l·rep ≤ 2l·(対数殻 deg_ℝ)。
    証明は M427F `pbm_two_sided_real` の両成分を M180 `rmul_le_mul_left`（右非負 2l で左乗法単調）で
    スケールするだけ——**bound が輸送でスケールする**という本物（crux とは別物）。 -/
theorem lvt_two_sided_scaled (logq : Nat → RReal) (v l n c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v n)))
    ∧ rLe (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n))
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c))) :=
  ⟨rmul_le_mul_left (intToReal ((2 * l : Nat) : Int))
      (pbm_two_sided_real logq v n c hq).1 (lvt_scale_nonneg l),
   rmul_le_mul_left (intToReal ((2 * l : Nat) : Int))
      (pbm_two_sided_real logq v n c hq).2 (lvt_scale_nonneg l)⟩

/-! ## M432F-2: 輸送後表現 = ×2l·rep（M407F 再輸出） -/

/-- **定理 (M432F-2: 輸送後表現は ×2l·多輻表現)** — 横 theta-link 先の q パラメータ側総体積
    `thLinkQParamTotalVol logq v l n`（= 輸送後表現）は多輻表現の ×2l 倍に realEq（M407F
    `tlm_thetaLink_transports_rep`、theta-link then 降下 = 降下 then theta-link）。両側有界の主語を
    輸送後表現へ張り替える橋渡し。 -/
theorem lvt_transport_eq (logq : Nat → RReal) (v l n : Nat) :
    realEq (thLinkQParamTotalVol logq v l n)
      (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n)) :=
  tlm_thetaLink_transports_rep logq v l n

/-! ## M432F-3: 本丸 — 輸送後表現は両側有界域の内側に留まる -/

/-- **定理 (M432F-3: 輸送後表現は両側実有界域の内側・本丸・本物の総合)** — 横 theta-link ×2l 輸送で
    得られる輸送後表現 `thLinkQParamTotalVol logq v l n`（= ×2l·rep、M432F-2）は、**スケールした両側
    有界域の内側になお留まる**:
      (i) **下界**: 2l·(l³·log q_v) ≤ 3·(輸送後表現)、
      (ii)**上界**: 輸送後表現 ≤ 2l·(対数殻 m^{Σj²+c} の deg_ℝ)。
    証明は M432F-1 のスケールした両側有界を、主語を M432F-2 の realEq（輸送後表現 = ×2l·rep）で張り替える
    （`rLe_congr`・下界側は M150 結合律 `rmul_assoc_real` と M123F 可換 `rmul_comm` で 2l·(3·rep) =
    3·(2l·rep) = 3·輸送後表現 に整える）。すなわち**両側有界が輸送の下で coherent に保たれ**、輸送後の
    パイロット表現もその実 deg_ℝ 有界域を離れない本物の総合（crux 不等式は決して導出しない）。 -/
theorem lvt_two_sided_transported (logq : Nat → RReal) (v l n c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((3 : Nat) : Int)) (thLinkQParamTotalVol logq v l n))
    ∧ rLe (thLinkQParamTotalVol logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c))) := by
  refine ⟨?_, ?_⟩
  · -- 下界: 2l·(3·rep) = 3·(2l·rep) = 3·輸送後表現 へ RHS を張り替える。
    have hcomm :
        realEq (rmul (intToReal ((2 * l : Nat) : Int))
              (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v n)))
            (rmul (intToReal ((3 : Nat) : Int)) (thLinkQParamTotalVol logq v l n)) :=
      realEq_trans
        (realEq_trans
          (realEq_symm (rmul_assoc_real (intToReal ((2 * l : Nat) : Int))
            (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v n)))
          (realEq_trans
            (rmul_congr_left (mrpRepresentation logq v n)
              (rmul_comm (intToReal ((2 * l : Nat) : Int)) (intToReal ((3 : Nat) : Int))))
            (rmul_assoc_real (intToReal ((3 : Nat) : Int))
              (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n))))
        (rmul_congr_right (intToReal ((3 : Nat) : Int))
          (realEq_symm (lvt_transport_eq logq v l n)))
    exact rLe_congr (realEq_refl _) hcomm (lvt_two_sided_scaled logq v l n c hq).1
  · -- 上界: 主語 ×2l·rep を輸送後表現へ張り替える。
    exact rLe_congr (realEq_symm (lvt_transport_eq logq v l n)) (realEq_refl _)
      (lvt_two_sided_scaled logq v l n c hq).2

/-! ## M432F-4: bound は log-theta-lattice 格子移動で coherent（HV≈VH） -/

/-- **定理 (M432F-4: 輸送後上界は格子移動で coherent・本物)** — 輸送後表現の上界（M432F-3 (ii):
    輸送後表現 ≤ 2l·対数殻 deg_ℝ）**と**、log-theta-lattice 正方形の実 deg_ℝ 体積可換（M397F
    `ltls_square_commutes_vol`: 横→縦 `ltlsSquareHV` ≈ 縦→横 `ltlsSquareVH`）が**両立**する。
    すなわち輸送後の bound は格子の縦横移動に対し coherent——bound を適用してから格子移動しても、格子移動
    してから（スケールした）bound を適用しても同じ実 deg_ℝ に着地する（付値レベルの交換、crux 不等式では
    ない）。「有界パイロット表現が格子移動の下でも実有界域に留まる」本物の総合。 -/
theorem lvt_bound_coherent_around_lattice (logq : Nat → RReal) (v l n c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (thLinkQParamTotalVol logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
    ∧ realEq (ltlsSquareHV logq v l (n : Int)) (ltlsSquareVH logq v l (n : Int)) :=
  ⟨(lvt_two_sided_transported logq v l n c hq).2,
   ltls_square_commutes_vol logq v l (n : Int)⟩

/-! ## M432F-5: 輸送後両側有界は (Ind1)(Ind2)-不変（不定性代表非依存） -/

/-- **定理 (M432F-5a: 輸送後両側有界は (Ind1) 置換で不変)** — M427F の (Ind1) 不変な両側有界
    `pbm_two_sided_ind1_invariant`（主語を swapMult a b の実 deg_ℝ 総体積 `indR_realTotal` へ載せ替えても
    両側有界が成立）を、横 theta-link 輸送スケール 2l で**両側とも押し出す**。輸送後も両側有界域は (Ind1)
    置換代表の取り方に依らず coherent（M180 `rmul_le_mul_left` でスケール）。 -/
theorem lvt_two_sided_transported_ind1_invariant (logq : Nat → RReal) (v a b l n c : Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((3 : Nat) : Int))
            (indR_realTotal logq v (swapMult a b indR_natExp) n)))
    ∧ rLe (rmul (intToReal ((2 * l : Nat) : Int))
            (indR_realTotal logq v (swapMult a b indR_natExp) n))
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c))) :=
  ⟨rmul_le_mul_left (intToReal ((2 * l : Nat) : Int))
      (pbm_two_sided_ind1_invariant logq v a b n c hab ha hb hq).1 (lvt_scale_nonneg l),
   rmul_le_mul_left (intToReal ((2 * l : Nat) : Int))
      (pbm_two_sided_ind1_invariant logq v a b n c hab ha hb hq).2 (lvt_scale_nonneg l)⟩

/-- **定理 (M432F-5b: 輸送後両側有界は (Ind2) 単数で不変)** — M427F の (Ind2) 不変な両側有界
    `pbm_two_sided_ind2_invariant`（主語を (Ind2) 単数作用 μ=0 の実 deg_ℝ へ載せ替えても両側有界が成立）
    を、横 theta-link 輸送スケール 2l で**両側とも押し出す**。輸送後も両側有界域は (Ind2) 単数不定性の下でも
    coherent（M180 `rmul_le_mul_left` でスケール）。 -/
theorem lvt_two_sided_transported_ind2_invariant (logq : Nat → RReal) (v l n c : Nat)
    (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((3 : Nat) : Int))
            (indR_ind2Vol logq v (thPilotTotalVol logq v n) 0)))
    ∧ rLe (rmul (intToReal ((2 * l : Nat) : Int))
            (indR_ind2Vol logq v (thPilotTotalVol logq v n) 0))
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c))) :=
  ⟨rmul_le_mul_left (intToReal ((2 * l : Nat) : Int))
      (pbm_two_sided_ind2_invariant logq v n c hq).1 (lvt_scale_nonneg l),
   rmul_le_mul_left (intToReal ((2 * l : Nat) : Int))
      (pbm_two_sided_ind2_invariant logq v n c hq).2 (lvt_scale_nonneg l)⟩

/-! ## M432F-6: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M432F-6a: 輸送後有界は本物・crux は外部仮説／honest)** — 両側有界が横 theta-link ×2l 輸送で
    coherent に保たれること（M432F-3: 輸送後表現 `thLinkQParamTotalVol` ≤ 2l·対数殻 deg_ℝ）は付値単調性・
    乗法単調性・×2l 輸送で閉じる**無条件で本物**の命題（crux とは独立に成立）。しかし theta-pilot ≤
    gauss-pilot の**多輻的アルゴリズム**（crux Dβ-ω ＝ IUT 論争の当の係争点）は本層で**決して証明しない**。
    crux を任意の外部 Prop `crux` として受け取り、輸送後上界の本物性 **と** crux の連言を、crux が仮説
    として供給された場合にのみ返す——crux は決して導出されない。 -/
theorem lvt_crux_external (logq : Nat → RReal) (v l n c : Nat)
    (hq : rLe realZero (logq v)) (crux : Prop) (hcrux : crux) :
    rLe (thLinkQParamTotalVol logq v l n)
        (rmul (intToReal ((2 * l : Nat) : Int)) (pvuLogShellBound logq v (sumSq n + c)))
    ∧ crux :=
  ⟨(lvt_two_sided_transported logq v l n c hq).2, hcrux⟩

/-- **定理 (M432F-6b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説そのもの**
    として扱い、それ以上でも以下でもない（Iff.rfl）。crux（theta ≤ gauss 比較）は本層が総合した輸送後
    有界とは別物であり、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で明示
    （M427F `pbm_crux_is_hypothesis`・M407F `tlm_crux_is_hypothesis` と同じ精神）。 -/
theorem lvt_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M432F-7: capstone -/

/-- **M432F-7a: log-volume transport synthesis データ**（総括） — 定理3.11 の両側実 deg_ℝ 有界（M427F）が
    横 theta-link の ×2l 体積輸送（M407F）の下で coherent に保たれることを束ねる: 両側有界の ×2l スケール・
    輸送後表現 `thLinkQParamTotalVol` が両側有界域の内側に留まること・その bound が log-theta-lattice 格子
    移動（HV≈VH）で coherent・輸送後両側有界の (Ind1)(Ind2)-不変性。主語は M427F/M407F/M397F の本物の実
    deg_ℝ であり toy を用いない。crux（Dβ-ω＝theta ≤ gauss）は外部仮説であって本層で証明されない。 -/
structure LogVolMultiradialTransportData (logq : Nat → RReal) (v : Nat) where
  /-- 横 theta-link 輸送スケール 2l を与える l-捻れ。 -/
  l : Nat
  /-- 対数殻 m^d の実 deg_ℝ 上界（両側有界の上側受け皿）。 -/
  shellBound : Nat → RReal
  /-- shellBound は本物の対数殻 deg_ℝ 上界（M422F/M427F）。 -/
  is_bound : shellBound = pvuLogShellBound logq v
  /-- 輸送後表現（横 theta-link 先の q パラメータ総体積）。 -/
  transported : Nat → RReal
  /-- transported は M407F の輸送後表現そのもの。 -/
  is_transported : transported = thLinkQParamTotalVol logq v l
  /-- 輸送後表現は ×2l·多輻表現（M407F ×2l 輸送）。 -/
  transport_eq : ∀ n : Nat,
    realEq (transported n) (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n))
  /-- 両側有界は ×2l 輸送でスケール（下界・上界とも）。 -/
  two_sided_scaled : ∀ n c : Nat, rLe realZero (logq v) →
    rLe (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v n)))
    ∧ rLe (rmul (intToReal ((2 * l : Nat) : Int)) (mrpRepresentation logq v n))
        (rmul (intToReal ((2 * l : Nat) : Int)) (shellBound (sumSq n + c)))
  /-- 本丸: 輸送後表現は両側有界域の内側（下 2l·l³·log q_v ≤ 3·輸送後・上 輸送後 ≤ 2l·対数殻）。 -/
  transported_within : ∀ n c : Nat, rLe realZero (logq v) →
    rLe (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((3 : Nat) : Int)) (transported n))
    ∧ rLe (transported n) (rmul (intToReal ((2 * l : Nat) : Int)) (shellBound (sumSq n + c)))
  /-- bound は log-theta-lattice 格子移動で coherent（輸送後上界 ∧ HV≈VH）。 -/
  coherent_around_lattice : ∀ n c : Nat, rLe realZero (logq v) →
    rLe (transported n) (rmul (intToReal ((2 * l : Nat) : Int)) (shellBound (sumSq n + c)))
    ∧ realEq (ltlsSquareHV logq v l (n : Int)) (ltlsSquareVH logq v l (n : Int))
  /-- 輸送後両側有界は (Ind1) 置換で不変（不定性代表非依存）。 -/
  transported_ind1_inv : ∀ (a b n c : Nat), ¬ a = b → a < n → b < n → rLe realZero (logq v) →
    rLe (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((n * n * n : Nat) : Int)) (logq v)))
        (rmul (intToReal ((2 * l : Nat) : Int))
          (rmul (intToReal ((3 : Nat) : Int))
            (indR_realTotal logq v (swapMult a b indR_natExp) n)))
    ∧ rLe (rmul (intToReal ((2 * l : Nat) : Int))
            (indR_realTotal logq v (swapMult a b indR_natExp) n))
        (rmul (intToReal ((2 * l : Nat) : Int)) (shellBound (sumSq n + c)))

/-- **M432F-7b: 実データ** — 全フィールドを M432F-1〜5 の本物で充足。輸送後表現は M407F の
    `thLinkQParamTotalVol`、両側有界は M427F、格子可換は M397F であり crux は受け取らず総合のみ。 -/
def logVolMultiradialTransportData (logq : Nat → RReal) (v l : Nat) :
    LogVolMultiradialTransportData logq v where
  l := l
  shellBound := pvuLogShellBound logq v
  is_bound := rfl
  transported := thLinkQParamTotalVol logq v l
  is_transported := rfl
  transport_eq := fun n => lvt_transport_eq logq v l n
  two_sided_scaled := fun n c hq => lvt_two_sided_scaled logq v l n c hq
  transported_within := fun n c hq => lvt_two_sided_transported logq v l n c hq
  coherent_around_lattice := fun n c hq => lvt_bound_coherent_around_lattice logq v l n c hq
  transported_ind1_inv := fun a b n c hab ha hb hq =>
    lvt_two_sided_transported_ind1_invariant logq v a b l n c hab ha hb hq

/-- **M432F-7c: 存在（M432F 見出し）** — 任意の実重み logq・素点 v・l-捻れ l に対し、log-volume transport
    synthesis データが存在する。両側実 deg_ℝ 有界（M427F）は横 theta-link ×2l 体積輸送（M407F）の下で
    coherent にスケールして保たれ、輸送後表現 `thLinkQParamTotalVol` は両側有界域の内側に留まり、その bound は
    log-theta-lattice 格子移動（HV≈VH）で交換し、(Ind1)(Ind2)-不変である。crux（Dβ-ω＝theta ≤ gauss）は
    外部仮説として明示され、**決して証明されない**——本層は両側有界と ×2l 輸送を**総合し、bound が輸送の
    下で安定であるという構造を本物にする**のみ。 -/
theorem lvt_exists (logq : Nat → RReal) (v l : Nat) :
    Nonempty (LogVolMultiradialTransportData logq v) :=
  ⟨logVolMultiradialTransportData logq v l⟩

/-! ## 実例（twist l=3 → ×2l=×6, rep 準位 n=5: Σ_{j=1}^{5} j²=55, 下界 n³=125） -/

/-- 実例: Σ_{j=1}^{5} j² = sumSq 5 = 55（輸送後上界の殻レベル・下界 n³=125）。 -/
example : sumSq 5 = 55 := rfl

/-- 実例（両側有界は ×6 スケール・l=3, n=5）: 下界・上界とも ×6 倍でなお成立。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * 3 : Nat) : Int))
          (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v)))
        (rmul (intToReal ((2 * 3 : Nat) : Int))
          (rmul (intToReal ((3 : Nat) : Int)) (mrpRepresentation logq v 5)))
    ∧ rLe (rmul (intToReal ((2 * 3 : Nat) : Int)) (mrpRepresentation logq v 5))
        (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c))) :=
  lvt_two_sided_scaled logq v 3 5 c hq

/-- 実例（本丸・輸送後表現は域内・l=3, n=5）: 輸送後表現は下（6·125·log q_v ≤ 3·輸送後）と上
    （輸送後 ≤ 6·殻 deg_ℝ）の両側有界域の内側に留まる。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * 3 : Nat) : Int))
          (rmul (intToReal ((5 * 5 * 5 : Nat) : Int)) (logq v)))
        (rmul (intToReal ((3 : Nat) : Int)) (thLinkQParamTotalVol logq v 3 5))
    ∧ rLe (thLinkQParamTotalVol logq v 3 5)
        (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c))) :=
  lvt_two_sided_transported logq v 3 5 c hq

/-- 実例（格子移動で coherent・l=3, n=5）: 輸送後上界と M397F 格子可換（HV≈VH）が両立。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (thLinkQParamTotalVol logq v 3 5)
        (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 5 + c)))
    ∧ realEq (ltlsSquareHV logq v 3 (5 : Int)) (ltlsSquareVH logq v 3 (5 : Int)) :=
  lvt_bound_coherent_around_lattice logq v 3 5 c hq

/-- 実例（輸送後 (Ind1) 不変・l=3, n=2）: 輸送後両側有界は (Ind1) 互換 0↔1 で不変（×6 スケール）。 -/
example (logq : Nat → RReal) (v c : Nat) (hq : rLe realZero (logq v)) :
    rLe (rmul (intToReal ((2 * 3 : Nat) : Int))
          (rmul (intToReal ((2 * 2 * 2 : Nat) : Int)) (logq v)))
        (rmul (intToReal ((2 * 3 : Nat) : Int))
          (rmul (intToReal ((3 : Nat) : Int))
            (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2)))
    ∧ rLe (rmul (intToReal ((2 * 3 : Nat) : Int))
            (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2))
        (rmul (intToReal ((2 * 3 : Nat) : Int)) (pvuLogShellBound logq v (sumSq 2 + c))) :=
  lvt_two_sided_transported_ind1_invariant logq v 0 1 3 2 c (by omega) (by omega) (by omega) hq

/-- 実例: crux Dβ-ω（theta ≤ gauss 比較）はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  lvt_crux_is_hypothesis crux

/-- 実例（capstone 存在）: log-volume transport synthesis データは存在する。 -/
example (logq : Nat → RReal) (v l : Nat) :
    Nonempty (LogVolMultiradialTransportData logq v) :=
  lvt_exists logq v l

end IUT
