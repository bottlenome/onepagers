# A8 楕円 cuspidalization 深化スライス詳細化（0.66 の次の実増分の到達可能性）— 2026-07-20

**分類: [設計のみ / design-only]・tier-L 詳細化・complete_pct 0 前進（Lean コードなし・共有ファイル変更なし）・§4 規約（既存の正直な限定を消さない・弱めない・過大主張しない）**

- 対象: 柱A **A8**「楕円曲線/Tate 曲線の実被覆・cuspidalization」（weight 12・現 s_A8 = **0.66**・
  `target_ledger.json` 実測・note「q3c3 [3]-isogeny E₉[3](ℚ₃)={O} trivial-deck (audit +0.01→0.66)」）。
- 手法: `audit/pillar-A5-tempered-pi1-deepen-detail-2026-07-20.md` / `pillar-A4-…` と同じ
  **disproof-first 到達可能性検査**。既存の正直な限定を敵対的に再検査し、**前提が失効した条項**
  （後続ラウンドの実装で到達可能に変わったもの）と**依然 research-blocked な条項**を峻別する。
- 結論の先出し: **到達可能なマイルストーンが 1 本（本命）＋条件付き 1 本（副）ある。**
  q3cu 正直限定 4「単一切片 N=2・奇 N・一般 q は後続」と q3c3 正直限定 4「μ₃/μ₉ を有理化する
  拡大上の E[N] 全有理化は後続」は、その**後**に建った M=ℚ₃(ζ₉) 生態系
  （q3k→q9c→q9tl→**q9td の E[9]≅(ℤ/9)² 完全分解**）により**失効**しており、
  **wild level-9 の楕円 cuspidalization 基体**（実 [9]-同種・核＝ちょうど E_{3⁹}[9](M)＝81 有理
  cusp・開曲線塔 E∖E[9]→E∖E[3]→E∖{O}）が**既存資産の消費のみ・choice-free** に建つ。
  A5 q9nt / A6 crk と同型の「実装済み資産による判定失効」である。

---

## 0. TL;DR

| 問い | 答え |
|---|---|
| 次の実増分は到達可能か | **YES（research-blocked ではない・choice-free）** |
| 本命 | **C1: wild level-9 cuspidalization 基体**（`IUT/Q3TateCuspidalizationL9.lean`・prefix `q9cu`・opus 1 枠）。q3cu（N=2・核=Klein 4）と q3c3（N=3・核={O} 自明）の系列を、E_{3⁹}(M)・N=9 へ昇格: 実 [9]-同種 Hom・**核＝ちょうど E_{3⁹}[9](M)≅(ℤ/9)²（81 有理 cusp・q9td_e9_decomp を消費）**・E[3](M)=⟨[27],[ζ₃]⟩≅(ℤ/3)² の新分類・**初の cuspidalization 開曲線塔** E∖E[9]→E∖E[3]→E∖{O}・[9] 非全射 witness（E(M)/9E(M)≠0 の影）。保守見込み **+0.01〜+0.02** |
| 副（条件付き） | **C2: level-9 テータ拡大 shadow**（`IUT/Q3Mu9ThetaExtension.lean`・prefix `q9ce`・opus 1 枠）。q3th（A8 計上・射影像=Klein）の level-9 対応: q9mtGrp の射影像＝**ちょうど E_{3⁹}[9](M)**・核＝中心スカラー・**交換子値＝ちょうど μ₉**（種数 1 の cusp 惰性関係 c=[a,b]⁻¹ の mod-9 影）。A5/A7 との firewall 検査つき（§2.4）。保守見込み **+0.01** |
| 合算の保守 forecast | s_A8 0.66 → **0.67〜0.69**（敵対的下限 0.67）。Σ_A=57.40 は Δs_A8≥0.01 で 57.52→表示 **58**（算術上の事実。merit は独立監査が決める——表示狙いを動機にしない） |
| research-blocked（正直申告） | (i) **cuspidalization 本体＝π₁ 再構成アルゴリズム・π₁-identification**（q3cu §2(a) のアーベル被覆障害は不変・実開曲線 π₁ 対象が存在しない）。(ii) **実 cuspidal 惰性 proper**（スキーム分岐被覆 or 実テータ関数/切断が前提）。(iii) **E_{3⁹}(M) 担体への実 Gal(M/ℚ₃) 作用**（ζ₉↦ζ₉^k 実自己同型の建設は A3/A7 と credit が絡む named future・q3ap 限定 (iv) と同一）。(iv) **q^{1/27} 以深の幾何的 Tate 加群塔**（3^{1/3}∉M・実 ℚ₃(ζ₂₇,3^{1/3}) 建設前提・q3ap 限定 (ii) と同一）。A8 soft cap **0.72–0.75** は本 2 スライスの後も不変 |

---

## 1. 正確なギャップ（何が有り・何が無いか）

### 1.1 A8 が現在持っているもの（0.66 の内訳・全て本体精読済み）

| 資産 | ファイル / 主定理 | 内容 | 計上 |
|---|---|---|---|
| A8a/A8b | `IUT/Q3TateCurve.lean`（q3t）・`IUT/Q3TateTorsion.lean`（q3tt） | 実 Tate 曲線 E_q(ℚ₃)=（3^ℤ×ℤ₃^×)/q^ℤ・実 v(q)=m・実 2-捻れ w=3, w²=9・Klein 4 群 | 0.57（reaudit-A8-real-tate-curve） |
| A8c | `IUT/Q3TateCuspidalization.lean`（q3cu） | リポジトリ初の実 [2]-同種 `q3cuSq`・**μ₂ 完全性 `q3cu_mu2_complete`**・核＝ちょうど Klein `q3cu_ker_eq_klein`・開曲線 `q3cuOpen→q3cuPunct`（`q3cuOpenMap`）・ファイバー=Klein 剰余類・自由デッキ・**[2] 非全射 `q3cu_not_surjective`**（E(ℚ₃)/2E(ℚ₃)≠0 の影） | 0.60（+0.03） |
| A8（テータ half） | `IUT/Q3ThetaGroup.lean`（q3th） | 実 Mumford テータ群 `q3thGrp`=C_M(g_τ)・射影像＝Klein=E₉[2]・核＝中心・**交換子＝実 μ₂ 値 Weil `q3th_comm_eq_weil`・非可換 `q3th_nonabelian`** | 0.65（+0.05） |
| A8d | `IUT/Q3TateCubeIsogeny.lean`（q3c3） | 奇 N=3 切片: 実 [3]-同種 `q3c3Cube`・**核＝ちょうど {O}**（`q3c3_ker_eq_trivial`・E₉[3](ℚ₃)=0・μ₃∉ℚ₃ の正の帰結）・[3] 単射・デッキ自明 | 0.66（+0.01） |

### 1.2 0.65 監査（reaudit-A8-theta-group §結論）が残した named gaps

(1) cuspidalization 本体（π₁-identification・再構成アルゴリズム）＝0、(2) 実テータ関数＝0、
(3) スキーム水準分岐被覆 half 残存、(4) G_{ℚ₃} 作用＝0、(5) **単一切片（p=3・q=9・level 2/μ₂
のみ・奇 l・μ_l は後続）**。本設計はこのうち **(5) を wild level-9 で正面 discharge** できるかを
検査する（(1)(2)(3) は §2.5 で research-blocked を再確定する）。

### 1.3 候補 4 方向と現状の欠落（プロンプト指定 (a)–(d) の実測）

**(a) full cuspidalization**（π₁(E_q∖{O}) を π₁(E_q) の惰性拡大として）: 実開曲線の π₁ 対象は
リポジトリに**存在しない**（grep: `q3cuPunct`/`q3cuOpen`/`q9cu` 系 subtype に π₁ 構成なし。
punctured π₁ の群提示は代理 `thetaGrp`/`tpeGroup`（M384F/M429F）のみで、その実現 q3nt/q9nt は
**A5 計上**・π₁-identification は q9nt ヘッダも未主張）。q3cu §2(a) のアーベル被覆障害
（現行実被覆のデッキは全て可換 ⟹ 惰性は自明にしか作用できない）は**今も真**——§2.5-1。

**(b) [3^n]-同種塔／一般 N**: ℚ₃ 上の E₉ で cube を反復しても核は全段 {O}
（`q3c3_cube_injective` の反復・新内容ほぼゼロ＝骨格水増し）。**しかし** M=ℚ₃(ζ₉)・q=3⁹ の
E_{3⁹}（`IUT/Q3TateCurveL9.lean` q9tl）では [9] の核＝⟨[3],[ζ₉]⟩ が**全有理**（q^{1/9}=3∈ℚ₃・
ζ₉=Y∈M）で、しかもその完全分類は **`q9td_e9_decomp`（`IUT/Q3Etale9TwoDir.lean:447`・
存在＋一意性: 任意の 9-torsion 点は一意に [3]^i·[ζ₉]^j）として既に定理化済み**。
欠落は「**同種そのもの**」——E_{3⁹} 上の自己 Hom（[3]・[9]）・その核としての E[N] の読み・
開曲線図式・非全射 witness は**どこにも無い**（grep 実測: `q9tlCurve` の自己 Hom はゼロ・
消費者 q9td/q3ap/q9mr はいずれも `tateNpow x 9 = 1` を**述語**として使うのみで写像を建てない）。

**(c) テータ接続 cuspidalization**: q3th の A8 定理系（射影像=Klein・核=中心・交換子=μ₂ 値
Weil）の level-9 対応は**未着手**。`IUT/Q3Mu9ThetaGroup.lean`（q9mt・complete_pct 0 の
foundation）には `q9mt_comm_eq_weil`・`q9mt_weil_nondeg`（e₉(g₃,g_ζ)=ζ₉⁻¹≠1）・
`q9mt_proj_e9_three/zeta`（射影が [3]・[ζ₉] に**到達**）まで在るが、
「射影像＝**ちょうど** E[9]」「交換子値＝**ちょうど** μ₉」「核＝中心」の拡大構造 3 定理は無い
（grep: q9mtGrp の消費者は A7 kill 連鎖 q9mr/q9mb と A5 実現 q9nt のみ・§2.4 で firewall 検査）。

**(d) cuspidalized π₁ への外 Galois 作用**: 外 Galois は `q3ap_outer_galois`・
`q3aw_weil_galois`（**A4 計上**・2026-07-20 R5/R6）が π₁/指標レベルで既に持つ。曲線担体
E_{3⁹}(M) への実 Galois 作用は q3ap 正直限定 (iv) が「未構成・A3/A7 と調整の named future」と
明記——A8 で先取りすると credit 衝突＋新規建設（実 Gal(M/ℚ₃) 自己同型 ζ₉↦ζ₉^k の実書き下し）
が要る。**本ラウンドの梯子には載せない**（§2.5-3）。

---

## 2. Disproof-first 検査

### 2.1 攻撃 1（本命 C1 の核心）: 「奇 N・拡大体上の E[N] 全有理化は後続」は今も真か？

**判定: 失効（FALSE になった）。** q3cu 正直限定 4・q3c3 正直限定 4 が書かれた時点
（2026-07-11）以後に、必要資産が**全て実対象として**建った:

| 必要部品 | 実体（実測） | 状態 |
|---|---|---|
| 実 ζ₉ を持つ体上の Tate 曲線 | `q9tlCurve` = M^×/q^ℤ（q=3⁹・`q9tlMx`=ℤ(v_π)×U₃）・[3]=`q9tl3pt`・[ζ₉]=`q9tlZeta9` **位数ちょうど 9**（`q9tl_3_tor`/`q9tl_zeta9_tor`） | 済（foundation・0 計上） |
| μ₉ 完全性 | `q9c_mu9_complete`（`IUT/Q3Mu9Completeness.lean:1311`・carrier レベル・u⁹=1 ⟹ `q3kMu9` 9 元） | 済（0 計上） |
| E[9] の完全分類 | **`q9td_e9_decomp`**（単射 `q9td_phi_injective`＋全射 `q9td_phi_surjective`・`q9tdPhi : (ℤ/9)²→E_{3⁹}`） | 済（q9td・分類部は「消費 INPUT スキャフォルド」と自己申告） |
| 成分冪算術 | `q9tl_pow_fst`・`q9td_zpow_snd`・`q9td_npow_mul`（可換 npow 積・一般 Grp）・`q9mt_ninth_gen`（w⁹ の括り替え・一般 Grp） | 済 |

ゆえに C1 の各定理は**新イディオム 0**で落ちる。設計時手計算で確認した核心 3 点:
- **[9]-同種の核の前方向**: `pow9.map [k,u] = O` ⟺ ∃t, 9k=54t ∧ u⁹=u₆^{9t}
  （`tateQPowersSubgroup` の mem は ∃n, qⁿ=x・`TateCurve.lean:209`・成分は
  `q9tl_pow_fst`/`q9td_zpow_snd`）。これは `tateNpow x 9 = 1` と同値（pow9.map x = x⁹ が
  定義計算）なので、**分類は `q9td_e9_decomp` の消費 1 行**——μ₉ 完全性を再証明しない。
- **E[3](M) の新分類**: x³=O ⟹ x⁹=O ⟹ x=Φ(i,j)・x³=Φ(3i,3j)=O ⟹（Φ 単射消費）
  3i≡0≡3j mod 9 ⟹ 3∣i ∧ 3∣j ⟹ x∈⟨[27],[ζ₃]⟩≅(ℤ/3)²（zmod 代表の omega のみ）。
  **q9td にも q3c3 にも無い新定理**（q9td は 9-torsion のみ・q3c3 は ℚ₃ 上で核自明）。
- **[9] 非全射 witness**: pow9[k,u]=[9k,u⁹] の第 1 成分は 9k−54t ∈ 9ℤ ⟹ [1, 1] は像外
  （9∤1・omega）。`q3cu_not_surjective` の M/level-9 版＝E(M)/9E(M)≠0 の影。

### 2.2 攻撃 2: C1 は q3cu のクローンに過ぎず、新規 A8 内容ゼロでは？

**判定: クローン割引は見込むが、クローンで尽きない新規内容が 4 点ある。**
- **同形部分（割引対象）**: 開曲線 subtype・制限射・ファイバー剰余類・自由デッキ・非全射の
  証明テンプレートは q3cu の写経（tier M の確立イディオム）。
- **新規 1（質的）**: **奇 N で初めて核が非自明**。系列は N=2 核=Klein(ℤ/2)²（q3cu）→
  N=3 核={O}（q3c3・ℚ₃ の非有理性の正の帰結）→ **N=9 核=(ℤ/9)²・81 有理 cusp（C1・wild 体 M
  上の全有理化）**。q3c3 正直限定 4 の named defer の正面 discharge。
- **新規 2（質的）**: **初の cuspidalization 塔**。pow9 = pow3∘pow3（`q9mt_ninth_gen` の
  括り替え）による 2 段開曲線図式 E∖E[9] → E∖E[3] → E∖{O}——q3cu/q3c3 は 1 段のみだった。
  [AbsTopII] §3 楕円 cuspidalization が N を動かして使う「複数 N の被覆族」の最初の実例。
- **新規 3**: E[3](M)=⟨[27],[ζ₃]⟩≅(ℤ/3)² の完全分類（§2.1・E₉[3](ℚ₃)={O} との対比対）。
- **新規 4**: 0.65 監査 named gap (5)「単一切片・奇 l/μ_l 後続」の discharge——A8 の同種・
  cusp 集合言明が初めて wild 分岐体（e=6 の M）上に立つ。
敵対的相場: q3c3（奇 N 切片・核自明）+0.01 の先例に対し、C1 は非自明核＋塔＋新分類 2 本で
半ノッチ上＝**+0.01〜+0.02**（§4）。

### 2.3 攻撃 3: C1 の二重計上 firewall（vs A4 q9td・A7・A5・A9）

**判定: 境界は引ける。判定基準つきで明示する。**
- **vs A4（q9td）——最重要**: q9td の **NEW A4 内容は π₁ 二方向 GAction**
  （`q9tdLatAct`/`q9tdMuAct`・忠実性・直交性）であり、E[9]≅(ℤ/9)² 分解はヘッダが
  「消費 INPUT スキャフォルド（A4 の新規でない）」と明示。C1 は分解を**消費のみ**
  （`q9td_e9_decomp` を import・**再証明 0 本**）し、C1 の新主語＝同種 Hom・開曲線塔・
  ファイバー/デッキ・非全射・E[3](M) 分類は q9td に存在しない（§1.3(b) grep）。
  判定基準: **C1 から pow9/pow3 Hom と開曲線 subtype を消すと全定理が消滅する**こと・
  π₁ 対象（q3pePi1/tmzLimit）が C1 に一切登場しないこと・A4 status を主張しないこと。
- **vs A7（q9mr/q9mb・level-9 kill）**: あちらの主語はテータ両立 endo の剛性と tmi 輸送。
  C1 に endo・tmi・cyclotome 剛性は登場しない。逆依存もない。
- **vs A5（q9nt）**: thetaGrp/tpeGroup/Φ₉/Ψ₉ は C1 に登場しない。
- **vs A9（blc）**: 多項式・P¹ 不登場。
- **vs A8 既存（q3cu/q3c3）**: 曲線（E₉/ℚ₃ vs E_{3⁹}/M）・N（2,3 vs 9）・核（Klein/{O} vs
  (ℤ/9)²）が全て別。既存ファイル不変更・正直限定は「discharge の参照追記」も新ファイル側のみ。

### 2.4 攻撃 4（副 C2）: テータ拡大 shadow は q3th のクローン or A5/A7 の再計上では？

**判定: 構成可能・ただし C1 より計上リスクが高い（条件付き採用・第 2 枠）。**
- **構成可能性（choice-free・設計時手計算済み）**: g∈q9mtGrp（所属 qᵃw⁹=1・`q9mt_mem_iff`）
  に対し (i) **射影像⊆E[9]**: [w]⁹=[w⁹]=[q^{−a}]=1。(ii) **⊇（ちょうど）**: x∈E[9] ⟹
  x=[3]^i[ζ₉]^j（`q9td_e9_decomp` 消費）⟹ g₃^i·g_ζ^j ∈ q9mtGrp（`q9mt_g3_mem`/`q9mt_gz_mem`
  ＋部分群冪閉性 `q9nt_mem_zpow` の消費）が x へ射影。(iii) **交換子値＝ちょうど μ₉**:
  [g,g']=(w'^a w^{−a'},0,1)（`q9mt_commutator`）のスカラーは v = a(−6a')−a'(−6a) = 0 かつ
  9 乗 = q^{−aa'}q^{aa'} = 1 ⟹ `q9c_mu9_complete` で ∈μ₉。⊇ は非退化 witness ζ₉⁻¹
  （`q9mt_weil_nondeg`）の冪。(iv) 核＝中心スカラー（`q3th_ker_central` の写経）。
  ⟹ **拡大 shadow 1 → (中心スカラー) → q9mtGrp → E_{3⁹}[9](M) → 1・交換子部分群＝μ₉**＝
  「種数 1・1 点抜きの cusp 惰性関係 c=[a,b]⁻¹」の mod-9 実 shadow（q3th 0.65 計上の
  level-9 版・A8 テータ half の帰属先例あり）。
- **リスク（正直申告）**: (i) q9mt 自身は 0 計上 foundation だが A7（q9mr/q9mb）と A5（q9nt）
  が既にこれ期に消費して計上済み——3 本目の消費は監査が「同一キャンペーンの薄切り」割引を
  かけうる。(ii) q3th のクローン査定（テンプレート同形）。firewall 判定基準:
  **C2 の各定理から Φ₉/Ψ₉（A5）と endo/決定性（A7 q9mr-2/3/9）を消しても命題が成立する**
  こと（実測: どれも登場しない設計）・`q9mt_weil_*` は消費のみ・A5/A7 status 不主張。
  ⟹ 採用順位は C1 の後。単独では +0.01 を超えない見込み。

### 2.5 攻撃 5: research-blocked なもの（正直に列挙・梯子に載せない）

1. **cuspidalization 本体（π₁ 再構成アルゴリズム・π₁-identification）**: q3cu §2(a) の
   アーベル被覆障害（惰性はあらゆるアーベル商で死ぬ・現行実被覆のデッキは全て可換）は
   **不変**。C2 の交換子=μ₉ は「惰性の CARRIER の mod-9 影」であって π₁(E∖{O}) の惰性部分群
   との同定ではない（q3th 正直限定 3 の線を越えない）。解消の名指し前提＝スキーム水準
   エタールサイト/分岐被覆 or 実テータ関数・切断（柱E 幾何実現）——research-blocked。
2. **実 cuspidal 惰性 proper・実テータ関数**: 同上（収束 p 進テータ級数・切断空間 Γ(L) は
   リポジトリ皆無）。A8 soft cap 0.72–0.75 の根拠であり本 2 スライスの後も外れない。
3. **E_{3⁹}(M) 担体への実 Galois 作用（候補 (d)）**: 実 Gal(M/ℚ₃)≅(ℤ/9)^× 自己同型
   （ζ₉↦ζ₉^k・Y 像の実書き下し）の建設が前提。q3ap 限定 (iv)・A5 詳細化 §2.5-3 と同一の
   named future（credit が A3/A7 と絡む）。A8 で先取りしない。
4. **q^{1/2^n}・q^{1/27} 以深の幾何的 Tate 加群塔**: √3∉ℚ₃（既判定・A8-real-tate-curve
   §5）・3^{1/3}∉M。実 ℚ₃(ζ₂₇,3^{1/3}) の建設（q3ap 限定 (ii) の named future）が前提。
5. **一般 N・一般 q・一般 p**: p=3 恒久スコープ。ℚ₃ 上の [3^n] 反復は核自明の繰り返しで
   新内容ゼロ（§1.3(b)）——骨格水増しになるため着手しない。

---

## 3. マイルストーン梯子（到達可能・全 choice-free・新イディオム 0）

### C1（本命・opus 1 枠）: `IUT/Q3TateCuspidalizationL9.lean`（prefix `q9cu`・想定 450–650 行）

import: `IUT.Q3Etale9TwoDir`（→ Q3TateCurveL9・Q3Mu9Completeness を継承）。共有ファイル変更なし。
分類ヘッダ: [実／昇格(a)]——q3cu 限定 4・q3c3 限定 4（奇 N・拡大体上の全有理化は後続）と
0.65 監査 gap (5)（単一切片）を wild level-9 で discharge。

| 段 | 内容 | 消費資産 | 難度 |
|---|---|---|---|
| q9cu-0 | 実同種 Hom `q9cuPow3`/`q9cuPow9` : E_{3⁹}→E_{3⁹}（x↦x³/x⁹・map_mul は可換 npow 積 `q9td_npow_mul`＋`q9tl_curve_abelian`）・合成 pow9=pow3∘pow3（`q9mt_ninth_gen` 括り替え） | q9td §A ヘルパ | 低 |
| q9cu-1 | 核⟺9-torsion 述語ブリッジ: `q9cuPow9.map x = 1 ⟺ tateNpow q9tlCurve x 9 = 1`（定義計算）＋成分抽出（`tateQPowersSubgroup` mem・`q9tl_pow_fst`・`q9td_zpow_snd`） | TateCurve.lean:209 | 低〜中（de-risk 対象・§5） |
| q9cu-2（★） | **核＝ちょうど E_{3⁹}[9](M)**: ker(pow9) = im(q9tdPhi)≅(ℤ/9)²・81 有理 cusp 相異（`q9td_phi_injective` 消費・再証明 0） | **`q9td_e9_decomp`** | 低（消費のみ） |
| q9cu-3（★） | **E[3](M) 新分類**: ker(pow3) = ⟨[27],[ζ₃]⟩ ≅ (ℤ/3)²（分解消費＋3i≡0 mod 9 の omega・§2.1）——E₉[3](ℚ₃)={O}（q3c3）との対比対 | q9td 分解 | 中の下 |
| q9cu-4（★旗艦） | **cuspidalization 開曲線塔**: `q9cuOpen9`=E∖E[9] → `q9cuOpen3`=E∖E[3] → `q9cuPunct`=E∖{O}（包含 2 本＋制限射 2 本・x∉ker9 ⟹ x³∉ker3 は定義計算）——初の 2 段図式 | q3cu-5 写経 | 中 |
| q9cu-5 | ファイバー＝E[9] 剰余類（`q3cu_fiber_coset` 写経）・デッキ自由（mul_right_cancel）・デッキは開部分を保つ | q3cu-6 写経 | 低 |
| q9cu-6（★） | **[9] 非全射 witness**: ∀x, pow9.map x ≠ [(1, 1)]（第 1 成分 9ℤ+54ℤ=9ℤ∌1・omega）——E(M)/9E(M)≠0 の影・正直装置 | q3cu-7 写経 | 低 |
| q9cu-7 | 正直核＋capstone `Q3CuspidalizationL9Data`/witness/exists（§4 の限定 5 項をヘッダ・フィールド注記に並置） | — | 低（束ね） |

### C2（副・条件付き・opus 1 枠・C1 と独立並列可）: `IUT/Q3Mu9ThetaExtension.lean`（prefix `q9ce`・300–450 行）

import: `IUT.Q3Mu9ThetaGroup`・`IUT.Q3Etale9TwoDir`。§2.4 の firewall 判定基準をヘッダに明記。

| 段 | 内容 | 消費資産 | 難度 |
|---|---|---|---|
| q9ce-0 | 射影 q9mtGrp 元 ↦ [g.2]∈E_{3⁹}・**像⊆E[9]**（[w]⁹=[q^{−a}]=1・`q9mt_mem_iff`） | q9mt | 低 |
| q9ce-1（★） | **像＝ちょうど E[9]**（`q9td_e9_decomp`＋`q9mt_g3_mem`/`q9mt_gz_mem`＋冪閉性） | q9td・q9mt | 中 |
| q9ce-2 | 核＝中心スカラー（`q3th_ker_central` の level-9 写経） | q3th 型 | 低 |
| q9ce-3（★★） | **交換子値＝ちょうど μ₉**（⊆: 付値 0＋9 乗=1＋`q9c_mu9_complete`。⊇: `q9mt_weil_nondeg` の冪）——c=[a,b]⁻¹ の mod-9 実 shadow | q9c・q9mt | 中 |
| q9ce-4 | 正直核（π₁-identification でないこと明記）＋capstone | — | 低 |

新規イディオム: **0**（両ファイルとも成分算術＋既存一般補題の消費＋q3cu/q3th テンプレート写経）。

---

## 4. 保守的 status forecast と、持ち越す A8 の帽子・限定

**verdict: 到達可能（research-blocked ではない）。**

**s_A8 予測（過大主張しない・独立監査が確定）**: 現 0.66 →
- C1 単独: 中央値 **+0.01〜+0.02**（q3c3 +0.01 の先例に対し、非自明核 81 cusp・塔・
  E[3](M) 新分類・named gap (5) discharge の分で半ノッチ上）。敵対的下限 +0.01
  （「q3cu の主語で体とレベルだけ替えた」査定）。
- C2 単独: 中央値 **+0.01**（q3th +0.05 の先例はあるが、あれは初のテータ群建設。C2 は
  クローン＋同一キャンペーン 3 本目消費の割引・§2.4）。敵対的下限 0（割引満額なら据え置き
  もありうる——だからこそ第 2 枠・単独計上を前提にしない）。
- 合算中央値 **0.67〜0.69**・敵対的下限 **0.67**。
- **柱A 表示の算術（事実として記す・動機にしない）**: Σ_A（ledger 実測 2026-07-20）
  = 8·0.85+8·0.69+12·0.75+14·0.59+10·0.27+14·0.61+12·0.58+12·0.66+10·0.17 = **57.40**（表示 57・
  graph-meta 整合確認済み）。Δs_A8=+0.01 で Σ_A=57.52 → round **58**。境界は
  Σ_A≥57.5 ⟺ Δ≥0.0084。表示前進は監査の merit 判定に従う（境界クロス狙いの計上は求めない）。

**消さない・弱めない帽子（新ファイルに必ず並置）**:
1. **cuspidal 惰性 proper＝0・π₁ 再構成アルゴリズム＝0**（q3cu 限定 1,2・q3th 限定 3 の継承）。
   C1 の被覆は E∖{O} 上不分岐・C2 の交換子=μ₉ は惰性 CARRIER の mod-9 影であって
   π₁-identification ではない。**A8 soft cap 0.72–0.75 は不変**。
2. **K 点の影**（スキーム・エタールサイト・位相なし・「開曲線」は subtype・担体は群提示
   ℤ×U₃ の商・A2 恒久限定継承）。[9] は M 点で非全射（幾何次数 81 との差を q9cu-6 で
   定理として顕示・隠さない）。
3. **q=3⁹ は忠実部分ケースの 2 乗**（9 乗トリック・[EtTh] の q 固定 q^{1/l} 添加そのもの
   ではない・q9tl 限定 2 の継承）。
4. **単一切片**: p=3・M=ℚ₃(ζ₉)・N∈{3,9} のみ。一般 N・一般 q・G_{ℚ₃} 作用・実テータ関数は
   依然 0（§2.5）。
5. q3cu/q3c3/q9tl/q9td/q9mt/q9c の正直限定は全て継承・既存ヘッダ不変更（discharge の注記は
   新ファイル側にのみ書く）。

**overclaim 禁止リスト**: 「cuspidalization を実装した」と書かない（基体＋shadow のみ）／
「E[9] 分類を証明した」と A8 で書かない（q9td の消費と明記）／A4・A5・A7 status の再主張禁止／
q9mt の Weil 定理の再証明禁止。

---

## 5. 推奨第一実装スライスと de-risk-first

- **第一スライス（opus 1 枠）**: **C1 = `IUT/Q3TateCuspidalizationL9.lean`（q9cu）**。
  理由: (i) A8 title の残 named gap（単一切片・奇 N）を正面 discharge、(ii) 新イディオム 0
  （分類は `q9td_e9_decomp` 消費・図式は q3cu 写経）、(iii) 二重計上 firewall が最も明瞭
  （§2.3 の消去テストつき）、(iv) q3cu（同 opus 級・1 ラウンド通過）の先例に載る。
- **de-risk-first 項目（実装前 30 分・scratch 1 本）**: **q9cu-1 のブリッジ 3 点**だけ先に
  コンパイルして確定する——(1) `q9cuPow9.map x = tateNpow q9tlCurve x 9` が定義計算で通る
  こと（Hom の map を Quot 上どう置くか: E_{3⁹} は商群なので `fun x => tateNpow _ x 9` を
  直接 map にでき Quot.lift 不要・ここが q3cuSq と違う唯一の設計点）、(2) `q9tlSubgroup` mem
  からの成分抽出（∃t, 9k=54t ∧ u⁹=u₆^{9t}）、(3) `q9td_e9_decomp` の前提形
  （`tateNpow q9tlCurve x 9 = q9tlCurve.one`）への変換。ここが通れば残りは全て写経で
  機械的に落ちる。詰まった場合のみ fable HELP（想定詰まりは tateNpow の左結合規約合わせのみ・
  `q9td_pow9val` が既に同種の括り替えを解決済み）。
- **並列枠**: C2（q9ce・opus）は C1 と**ファイル独立**で同一ラウンド並列可。ただし §2.4 の
  計上リスクを親報告に明記し、監査が割引満額でも C1 の増分は独立に立つ構成にする
  （C1 は C2 を import しない・逆も然り）。残り枠は他柱（A5 N1 残件等）を優先し、
  complete_pct を動かさない capstone で埋めない（§2 規約）。
- 統合時の共有ファイル更新（IUT.lean・build.sh・gen_graph.py PILLAR・graph-meta/dashboard・
  target_ledger）は親が一括。status 確定は独立敵対監査後（本書の見込み値を先に書き込まない）。

---

*設計: tier-L 詳細化ラウンド 2026-07-20。本書は設計のみで complete_pct を動かさない。
§1–§3 の全主張は実ファイル精読（Q3TateCuspidalization・Q3TateCubeIsogeny・Q3ThetaGroup・
Q3TateCurveL9・Q3Etale9TwoDir・Q3Mu9Completeness・Q3Mu9ThetaGroup・Q3TemperedThetaClassL9・
Q3EtaleArithPi1・TateCurve.lean）と監査記録（reaudit-A8-real-tate-curve/-cuspidalization/
-theta-group・reaudit-q9td-twodir-a4・reaudit-q9mt-theta-l9）と ledger 実測（s_A8=0.66・
Σ_A=57.40）に基づく。核成分抽出・E[3](M) 分類・非全射 witness・交換子 μ₉ 所属の付値計算は
設計時に手計算済み。*
