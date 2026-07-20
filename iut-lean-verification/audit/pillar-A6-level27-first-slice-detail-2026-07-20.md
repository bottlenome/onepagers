# A6 level-27 第 2 層 KILL キャンペーン: 最初の opus スライス同定（disproof-first de-risk）— 2026-07-20

**分類: [設計のみ / design-only]・tier-L 詳細化・complete_pct 0 前進・§4 規約遵守（Lean コードなし・共有ファイル変更なし・既存の正直な限定を消さない・弱めない・過大主張しない）**

- 対象: 柱A **A6**（mono-anabelian 復元・現 s_A6=**0.61**・帽子 **A6 ≤ 0.65**——`target_ledger.json` pillars.A items 実測: `{"id":"A6","status":0.61,"note":"crt realization-mult + base-point-free torsor (audit +0.02→0.60)"}`、直近 commit `28c10b0` "A6 0.60→0.61 (crk mono-theta KILL torsor-reduction)"）。
- 前提資産: `IUT/CyclotomeRecoveryThetaKill.lean`（crk・実装済み・IUT.lean 統合済み）が crt torsor の構造群を ℤ₃^× → S={u:(u.val 1).val=1}（mod-9 スライス）へ縮小した。crk 正直限定 (1) が明記する通り **1+9ℤ₃ torsor は SURVIVES** し、その次の一手として「level-27 の q27* 連鎖で第 2 層 {1,10,19} まで拡張可能」が named future target になっている（crk ヘッダ :15・:46・本文 :296）。
- 本書の任務: `audit/level27-kill-scope-2026-07-11.md` が 10 モジュール（q27k/q27ci/q27yp/q27cs/q27c/q27ps/q27tl/q27mt/q27mr/q27mb）・4–5 ラウンドと査定した level-27 キャンペーンを分解し、**最初に実装すべき opus サイズ 1 スライス**を disproof-first で同定する。

---

## 0. 結論先出し（TL;DR）

1. **【最重要の状態更新】scope 文書が「単一障害点（single failure point）」と名指しした q27cs（12 座標 B6 交互パリティ同時降下）は、既に実装済み・焼却済みである。** `IUT/Q3Mu27DescentSpike.lean`（**1192 行・commit `3b99808` 2026-07-14・IUT.lean:649 で import 済み・sorry 皆無**）が、随伴 Cramer 恒等式 `q27cs_cramer0/1/2`（:451/:593/:730・各 18 単項式の完全 rw 証明）・6 座標一括 peel `q27cs_norm_peel`（:932）・偶段 `q27cs_descent_even`（:973）・奇段 `q27cs_descent_odd`（:1003・基底 m=0 込み）・**交互合成 `q27cs_descent_all`（:1055・全レベル 12 座標消滅の帰納 glue）**・忠実性橋 `q27cs_k_mul0_fst/snd_valn`（:1101/:1147・q3kMul スロット 0 の rep 橋）まで完全証明している。scope R1（q27cs fable de-risk）は完了しており、**キャンペーンの最難点は「genuinely reachable」を超えて「already reached（仮定形）」**。
2. **ただし spike は仮定形である（正直申告・spike 正直限定 1–4）**: E1′/E2′ の可除性（本物では u³=1 の Z/Z² 成分方程式から導出）・単数正則仮定 `hn : ¬3∣(q27csNorm …).1`・基底 TDF 1 は**仮定として取られており**、これらの discharge は Module q27ci/q27c の仕事として明示的に残されている。したがってキャンペーンの残存最大リスクは q27cs 本体ではなく、**(i) hn（6 座標ノルム単数判定）の discharge と (ii) N(w̃) 原始単数証明（q27ps）**——どちらも「level-9 の綺麗な定数 N(w)=−1 が消える」ことに由来する同一の補題族（§2.3）。
3. **推奨する最初の opus スライス = q27k（Q3KummerNonic・環オープナー）**。O_{M₂₇} = O_{M₉}[Z]/(Z³−ζ₉) 環＋τ＋相対ノルム＋閉形式逆元は、q3k（`Q3KummerCubic.lean` 1032 行）の**忠実な 1 段上クローン**であり、環公理部は base=CRing・ねじれ d=抽象元で書かれた q3k-2 の設計（q3k :122「d = ζ₃ を抽象環元として扱う」）がそのまま base=`q3kRing`（:454 で CRing 実在）・d=`q3kZeta9` に写る。**今ラウンド到達可能（M-tier opus 1 枠・§2.1）**。
4. **同時に潰すべき単一 de-risk 項目 = M₉ 主単数補題 `q3kUnitMem (1 + 3t)`（＋その系としての N(w̃) 単数証明の設計検証）**。scope §1.3 は「N(w̃)=1+O(π₉¹⁵) の単数性は M₉ の付値/主単数論を要する」と警告したが、本書の検査（§2.3）では **`IsZpUnit` がレベル 1 剰余のみの述語（`ZpUnits.lean:38`）である**ため、必要なのは付値論ではなく **mod-3 剰余簿記 2 段（q3kNormBase → q3rqNorm）**に還元される——形式化可能・ただし rep 抽出の配管が fiddly なので**最初に小 spike で閉じる**のが規律。
5. **s_A6 影響: 本スライス（q27k＋単数 spike）は 0 前進申告**（foundation・kill も橋も含まない）。A6 が動くのはキャンペーン末端の橋 q27mb ＋ crk の mod-27 拡張（crk27 接続補題）が閉じた時のみで、その時も **A6 ≤ 0.65 帽子の内側**（せいぜい 0.61→0.62–0.63 への nudge・帽子は π₁ 連続 χ・幾何 cyclotome 未のあいだ外れない——crk 正直限定 (3) 継承）。過大主張しない。

---

## 1. 正確な現状（level-9 資産のクローン可能域 vs 真に新規な残り）

### 1.1 存在する level-9 資産（本体確認・クローン元）

| 資産 | ファイル:行 | 内容 | level-27 での使い方 |
|---|---|---|---|
| `q3kCar`/`q3kMul`/`q3kRing` | `IUT/Q3KummerCubic.lean` :67/:99/:454 | O_{M₉}=O_{L₂}[Y]/(Y³−ζ₃)・ねじれ畳み込み・**CRing インスタンス** | q27k のテンプレ（base を q3rqRing→q3kRing・d を q3rqZeta→q3kZeta9 に置換） |
| `q3kSigma`/`q3k_sigma_mul`/`q3k_sigma3_id` | 同 :504/:518/:560 | 相対 Galois σ: Y↦ζ₃Y・位数 3 | τ=q27kSigma（Z↦ζ₃Z・ζ₂₇↦ζ₂₇¹⁰・新層 {1,10,19} 実現）の 1 段上クローン |
| `q3kNormBase`/`q3k_norm_eq`/`q3k_normBase_mul` | 同 :682/:810/:856 | N(x)=x·σx·σ²x=a³+ζ₃b³+ζ₃²c³−3ζ₃abc・乗法性 | 相対ノルム N_{M₂₇/M₉}（d=ζ₉ 版）のテンプレ |
| `q3kUnitMem`/`q3kInv`/`q3k_inv_mul`/`q3kU` | 同 :868–:917 | 単数判定（ノルム経由）・閉形式逆元・単数群 | q27kUnitMem := q3kUnitMem∘相対ノルム・q27kInv（q3kInv 消費）のテンプレ |
| `q3kZeta9` = Y・`q3k_zeta9_pow9` | 同 :929/:962 | 実 ζ₉・位数ちょうど 9 | ζ₂₇ := Z（Z²⁷=(Z³)⁹=ζ₉⁹=1）・位数 27 のテンプレ |
| `q9psPi9`=Y−1・`q9ps_pi9_cube`・**`q9ps_w_norm : N(w)=−1`**・`q9ps_three_split : 3=π₉⁶·u₆`・`q9psU6` | `IUT/Q3KummerPiSplit.lean` :104/:219/:312/:467/:443 | level-9 wild 分割（実装済み・要石） | §1.3 閉形式（(Z−1)³=π₉·w̃）の帰着先＝**消費のみ・再証明ゼロ** |
| `q9c_rawF1/F2/F3/F3'`/`q9c_rawNine`/`q9c_cube_mul` | `IUT/Q3Mu9Completeness.lean` :87 等 | **一般 CRing・一般ねじれ d パラメータ**の純環恒等式 | `q9c_rawF3 q3kRing a b c q3kZeta9` の代入で**再証明ゼロ**（scope §3.1 の主張を本体で再確認） |
| `q9c_m_mu3_complete`（:1176）・`q9c_mu9_complete`（:1311） | 同 | μ₃(M₉) 完全性・μ₉ 完全性（塔分解） | q27c の中間層吸収（消費のみ） |
| `q9ci_cube_1`（:370）・`q9ci_three_reg_L2`（:412）・`q9ci_nine_reg`（:431）・`q9ci_unit_reg_L2`（:463）・`q9ci_embed_reg_M`（:527）・`q9ci_no_cbrt_zeta/zetaSq`（:628/:661） | `IUT/Q3KummerCubeIdent.lean` | M₉ 立方公式・L₂ 正則性パック | q27ci の部品（no-cbrt of ζ₉ は q9ci_cube_1 帰着で level-9 より綺麗にクローン——scope §3.2 検証済み） |
| `q9cs_*` toolbox（`q9cs_unit_peel` :129・`q9cs_descent_even/odd/all` :223/:330/:435・`q9cs_add_valn` :475・`q9cs_rq_mul_fst/snd_valn` :509/:532・`q9cs_zero_rep_dvd` :547） | `IUT/Q3KummerDescentSpike.lean` | level-9 降下 spike ＋ rep 橋 | **q27cs spike が既に消費済み**（下記） |
| `q3cu_ppow_dvd`（`Q3TateCuspidalization.lean:126`）・`euclid_int`（`RootsOfUnity.lean:63`） | — | 素冪 Euclid | q27cs spike の peel が消費済み |

### 1.2 既に実装済みの level-27 資産（scope 文書からの状態更新・最重要）

**`IUT/Q3Mu27DescentSpike.lean`（q27cs・1192 行・[実／本物の先行建設(b)]・complete_pct 0 前進申告済み）**。glob 実測で IUT/ の q27* はこの 1 本のみ（他 9 モジュールは未建設）。中身:

- q27cs-0/1: L₂ 影ペア環（`q27csP`/`q27csMul`・q9csMulFst/Snd と**定義一致 rfl**——`q27cs_mul_fst_eq` :92）＋計算キット（assoc/distrib/ras1-3/g0/g12）。
- q27cs-2/3: 可除性述語 `q27csPD/PM/TD/TM/TDF/TDS`・**ねじれ畳み込み影 `q27csTMul`（q3kMul:99–105 のスロット毎 Int 影）**・E1′/E2′ 影・6 座標ノルム影 `q27csNorm`。
- q27cs-4（★新規の核・完了）: **随伴 Cramer 恒等式 `q27cs_cramer0/1/2`** — u·(W·b)=N(W)·b の 3 スロット。level-9 の「主要係数 1 個の peel」が「随伴 3×3 対角化」に昇格する段——scope が「降下の連立構造が変わる」と警告した箇所そのものが、明示 rw＋射影展開＋omega で閉じている。
- q27cs-5〜8（★完了）: `q27cs_norm_peel`（Cramer 消費・12 座標一括 peel）→ `q27cs_descent_even`（m≥1）/`q27cs_descent_odd`（全 m≥0・基底 bootstrap）→ **`q27cs_descent_all`（交互帰納 glue・∀m 12 座標消滅）**＋ W=a² 実例化。
- q27cs-9: 忠実性橋（q3kMul スロット 0 の両 L₂ 座標 rep = 影値・`q9cs_rq_mul_*_valn`/`q9cs_add_valn` 消費）。
- **de-risk 発見（spike 正直限定 5・興味深い強化）**: M₉ 基底 peel はノルム随伴経由で**両パリティを同時に** 1 段深くする（level-9 の「偶段は第 1 座標のみ」より強い）。

**spike が仮定のまま残したもの（正直限定 1–4・Module q27ci/q27c へ委譲）**:
- (A) E1′/E2′ の TD (m+1) 可除性——本物では u³=1 in O_{M₂₇} の Z/Z² 成分方程式（O_{M₉} の等式 E′=0）から `q9cs_zero_rep_dvd` 型橋で導出（立方展開・3 消去は q27ci/q27c）。
- (B) **`hn : ¬3∣(q27csNorm e W₀ W₁ W₂).1`（W=a² の 6 座標ノルム影の単数正則）**——本物では a の O_{M₉} 単数性からノルム乗法性で discharge（q27ci 正則性パックのターゲットと明記）。
- (C) 基底 TDF 1——単数枝反証の出口（q27c）。
- (D) スロット 1/2 の忠実性橋の物量（同一合成の反復・q27c）。

### 1.3 真に新規な残り（scope §3.3 の 2 障害の現況）

| scope の genuine-new | 現況 | 残作業 |
|---|---|---|
| (ii) q27cs 12 座標降下（「単一障害点」） | **spike で焼却済み**（§1.2） | 仮定 (A)–(D) の discharge のみ（イディオムは level-9 と同一） |
| (i) M₉ 正則性パック＋6 座標ノルム単数判定 | **未着手・残存最大リスクに昇格** | hn discharge（上記 B）と N(w̃) 単数（q27ps）の共通核 = **M₉ 単数判定補題族**（§2.3 で disproof-first 検査） |

計上面の現況: s_A6=0.61（crk 済）・s_A7=0.57・A6 帽子 ≤0.65 維持。scope §5 の表示計算（Σ_A=47.62+12·s_A7・表示 54/55 閾）は**既に失効**している（柱A 表示は 2026-07-20 現在 57・`graph-meta.json` complete_pct=57）——本書は表示閾値の再計算をせず、A6 軸（crk mod-9 → mod-27 拡張）のみを追う。

---

## 2. Disproof-first: 最初のスライスは本当に到達可能か

### 2.1 攻撃 1: q27k「安全クローン」は本当に安全か（環公理が base 固有の補題に依存していないか）

**判定: 安全（M-tier 1 枠で到達可能）。** 実測根拠:

- q3k の環公理節（q3k-2 :122–453）はヘッダ通り「d = ζ₃ を**抽象環元**として扱う」——`q3k_mul_assoc`（:293）等は座標変換ブリッジ `q3k_M_eq : q3rqMul = q3rqRing.mul`（:59・rfl）で **base の CRing 界面**（one_mul/mul_comm/distrib）だけに帰着している。d の性質（d³ 等）は環公理に**不使用**。したがって base=`q3kRing`（CRing・:454 実在）・d=`q3kZeta9` の置換でそのまま写る。q27k 側ブリッジは `q27k_M_eq : q3kMul = q3kRing.mul`（q3k :837 `q3k_kM_eq` として既に存在——再輸出で足りる）。
- d 固有の補題が要るのは σ／ノルム節のみ: q3k は :477–:492 で `q3rq_zeta_mul_zetaSq`（ζ₃·ζ₃²=1）等を消費した。level-27 の対応物は「M₉ 内の embed(ζ₃)・embed(ζ₃²) の積規則」であり、`q3k_embed_mul`（:818）＋同じ q3rq 補題の合成で数行（新規イディオムなし）。σ=τ の乗法性 `q3k_sigma_mul`（:518）は係数側で ζ₃ の積規則しか使わないので同型にクローン。norm 消去恒等式（1+ζ₃+ζ₃²=0 が Z/Z² 成分を消す・`q3k_zeta_sum_zero` :492）も embed 経由で透過。
- 単数・逆元: `q27kUnitMem x := q3kUnitMem (q27kNormBase x)`（相対ノルムが O_{M₉} に落ち、その単数性は既存 `q3kUnitMem`→`q3rqUnitMem`→`IsZpUnit 3` の既存 2 段に再帰）。閉形式逆元は `q3kInv`（:869）の 1 段上（随伴 `q3kWt` 型 :620 の d=ζ₉ 版×base 逆元）——q3rqInv→q3kInv の置換のみ。
- ζ₂₇ := Z=(0,1,0)（M₉-座標）: Z³=ζ₉（q27kMul の定義から座標計算・`q3k_zeta9_cube` :946 のクローン）、Z²⁷=(Z³)⁹=ζ₉⁹=1 は **`q3k_zeta9_pow9`（:962）の消費**で出る。位数ちょうど 27（Z⁹=ζ₉³=ζ₃≠1・`q3k_zeta9_cube_ne_one` :974 消費）も同型。

**反証に失敗した点は無い**。規模見積り: q3k 1032 行の写経＋embed 補題 ≈ 900–1400 行・確立イディオムの新インスタンス＝**CLAUDE.md tier 表の M（opus）そのもの**。

### 2.2 攻撃 2: wild 分割 3 = π₂₇¹⁸·u₁₈ は形式化可能か

**判定: 恒等式部は可能（q9ps の忠実クローン＋π₉ 括り出し 1 段）。ただし w̃ の単数性だけが真に新規（→ §2.3）。**

- 二項恒等式 (Z−1)³ = (ζ₉−1) + 3(Z−Z²) は q27kCar の**座標計算**（`q9ps_pi9_cube` :219 が q9ci_cube 公式＋座標計算で閉じたのと同じパターン・M₉ 係数になるだけ）。ζ₉−1 = `q9psPi9`（:104・(−1,1,0) 実装済み）は q27k での embed 像。
- π₉ 括り出し: (Z−1)³ = π₉·w̃・w̃ = 1 + π₉⁵u₆(Z−Z²) は、3 = π₉⁶u₆（`q9ps_three_split` :467・**消費のみ**）を代入した**環等式**であり、付値論不要——q27k の環律で rw できる。
- 3 = π₂₇¹⁸·u₁₈（u₁₈=w̃⁻⁶u₆）: π₉ = (Z−1)³·w̃⁻¹ の 6 乗＋q9ps_three_split。**ここで初めて w̃⁻¹ が要る = q27kUnitMem w̃ が必要**。scope の手計算（N_rel(w̃)=1+3ζ₉u₆²π₉¹⁰+(ζ₉−ζ₉²)u₆³π₉¹⁵）は本書でも再検算し正しい（中項 val 16・末項 val 15）。

### 2.3 攻撃 3（本丸）: level-9 の「N(w)=−1 という綺麗な定数」は本当に消えるのか・消えたらクローンが折れるのか

**判定: 消える（scope の指摘は正しい）。ただし折れ方は scope の悲観（「M₉ の付値/主単数論を要する」）より軽い——`IsZpUnit` の定義がレベル 1 剰余のみであることが決定的。**

- level-9 では `q9ps_w_norm : q3kNormBase q9psW = −1`（:312）が一撃で `q9ps_w_unit` を与えた。level-27 の N_rel(w̃) は 1+O(π₉¹⁰) の主単数で、定数簿では閉じない——**この点でクローンは確かに折れる**（scope §1.3 の第 1 の正直な差分・追認）。
- しかし必要なのは `q27kUnitMem w̃` = `q3kUnitMem (N_rel(w̃))` = `q3rqUnitMem (q3kNormBase (N_rel(w̃)))` = **`IsZpUnit 3 (q3rqNorm …)`**。`IsZpUnit`（`ZpUnits.lean:38`）は「**レベル 1 の剰余が p と素**」（∃a, x.val 1 = [a] ∧ ¬3∣a）だけの述語である。ゆえに要るのは付値フィルトレーションではなく:
  1. **環恒等式**: N_rel(w̃) = 1 + 3·T（T : q3kCar 閉形式）。π₉¹⁰ = 3·u₆⁻¹·π₉⁴、π₉¹⁵ = 3²·u₆⁻²·π₉³（`q9ps_three_split` の再代入・環 rw のみ）から従う。
  2. **M₉ 主単数補題（新規・小）**: `q3kUnitMem (1 + 3t)` for all t : q3kCar。q3kNormBase(1+3t) を立方ノルム多項式で展開すると 1 + 3·s（s : q3rqCar 閉形式）——(1+3t₀)³ の定数 1 以外は全項 3 因子持ち。次に q3rqNorm(1+3s) = 1 + 3·(…) in z3。最後に IsZpUnit: レベル 1 rep が 1+3k ≡ 1 ≢ 0 (mod 3)。rep 抽出は Prop 内 ∃ ゴールなので Quot 表現（`q9cs_add_valn`/`q9cs_rq_mul_*_valn` 型の既存 rep 橋・choice-free）で足りる。
- **同じ補題族が spike の hn 仮定も discharge する**: `hn : ¬3∣(q27csNorm …).1` は「a（M₉ 単数）の 6 座標ノルム影の第 1 Int 座標が 3 と素」——a=単数 ⟹ q3kNormBase a のレベル 1 rep が 3 と素（`IsZpUnit` の定義そのまま）⟹ 影の値へ rep 橋で輸送。すなわち **(i) M₉ 正則性パックの核心は「q3kUnitMem ↔ mod-3 rep 簿記」の往復補題 1 族**に収斂し、q27ps（w̃ 単数）と q27c（hn discharge）の両方に同時に効く。
- **残るリスク（正直）**: q3kNormBase(1+3t) の「1 以外は全項 3 因子」展開は 6 座標×立方の物量計算であり、rep 橋の配管（14 引数型の valn 補題連鎖・q27cs-9 と同型）が fiddly。**数学リスクは小・配管リスクは中**——だからこそ着工前に**この 1 点だけを小 spike で閉じる**（§5）。

### 2.4 攻撃 4: そもそも A6 の乗り物になるのか（計上の対象不一致）

**判定: 直接はならない——正直に順序を明記する。** scope のキャンペーンは A7 計上設計（表示 mover は橋 q27mb）。A6 が動く経路は **q27mb（kill_mod27）→ crk の mod-27 拡張（crk27: S={mod-9 で 1} を S'={mod-27 で 1} へさらに縮小する torsor reduction・crk と同じ glue 構図）**であり、crk 先例（transport/glue に +0.01）から **A6 は 0.61 → 0.62–0.63 の nudge が上限・帽子 0.65 は不変**。最初のスライス（q27k＋単数 spike）は kill も橋も含まず **complete_pct/s_A6 とも 0 前進申告**。「level-27 に着工したから A6 が動く」とは書かない。

### 2.5 総合判定

- **q27k は今ラウンド到達可能**（攻撃 1 で反証失敗・全帰着先が named 実在補題）。
- q27cs はもはや de-risk 対象ではない（実装済み）。**キャンペーンの残存単一最大リスクは「M₉ 単数判定補題族」**（w̃ 単数＋hn discharge の共通核）に移った——これが**最初に潰すべき唯一の de-risk 項目**。
- 「さらに de-risk が要る／今ラウンド不到達」という verdict は**不成立**（q27k について）。ただし q27ps 全体（3=π₂₇¹⁸u₁₈ の完成）は単数 spike が閉じるまで着工しないのが規律。

---

## 3. マイルストーン梯子（最初の 1–2 モジュールのみ・キャンペーン全体ではない）

### Module 1: `IUT/Q3KummerNonic.lean`（prefix `q27k`・tier M/opus・900–1400 行・依存: q3k, q9ps）

| 段 | 内容 | 消費資産（再証明ゼロ） | 難度 |
|---|---|---|---|
| K-0 | ブリッジ `q27k_M_eq`（=既存 `q3k_kM_eq` :837 の再輸出）・台 `q27kCar := q3kCar × q3kCar × q3kCar`・外延性 | `q3kRing`（:454） | 低 |
| K-1 | ねじれ畳み込み `q27kMul`（d=`q3kZeta9`）・環公理（q3k-2 :122–453 の base 置換写経）・`q27kRing : CRing` | q3kRing の CRing 界面 | 低〜中（物量） |
| K-2 | embed `q27kEmbed : q3kCar → q27kCar`・`q27k_embed_mul/inj`・ζ₃/ζ₉ の像の積規則 | `q3k_embed_mul`（:818）・q3rq ζ 補題（:477–:492） | 低 |
| K-3 | τ=`q27kSigma`（Z↦ζ₃Z: x↦(x.1, ζ₃·x.2.1, ζ₃²·x.2.2)）・`q27k_sigma_mul`・`q27k_sigma3_id`・**新層 payoff の種: τ(Z)=ζ₂₇¹⁰≠ζ₂₇・τ は μ₉ 対角を各点固定** | `q3k_sigma_mul`（:518）テンプレ・`q3k_zeta9_*` | 中 |
| K-4 | 相対ノルム `q27kNormBase`（d=ζ₉ 版 a³+ζ₉b³+ζ₉²c³−3ζ₉abc）・`q27k_norm_eq`・乗法性 | `q3kWt`/`q3k_norm_collect` パターン（:620–:682）・`q9c_rawF*` の d 代入 | 中（物量最大） |
| K-5 | `q27kUnitMem := q3kUnitMem ∘ q27kNormBase`・閉形式逆元 `q27kInv`・単数群 `q27kU : Grp` | `q3kInv`/`q3k_inv_mul`（:869/:872） | 低〜中 |
| K-6 | **ζ₂₇ := Z・Z³=ζ₉・Z²⁷=1・位数ちょうど 27**（Z⁹=ζ₃≠1） | `q3k_zeta9_pow9`（:962）・`q3k_zeta9_cube_ne_one`（:974） | 低 |
| K-7 | capstone `Q3KummerNonicData` ＋ scope 定理（正直な限定の機械可読形） | — | 低 |

ヘッダ分類: [実／本物の先行建設(b)]・**complete_pct 0 前進**（foundation・q3k と同じ申告様式 :14–18 を踏襲）。正直な限定は q3k 1–7（O_M のみ・何も kill しない・σ=τ のみ・付値未・橋なし・兄弟担体）を 1 段上で継承。

### Module 2（並走可・小）: M₉ 単数判定 spike（`IUT/Q3NonicUnitSpike.lean` 仮・prefix `q27u`・tier M/opus・fable HELP 予約・250–500 行・依存: q3k, q9ci, q9cs）

| 段 | 内容 | 消費資産 | 難度 |
|---|---|---|---|
| U-0 | 3 倍元の閉形式: `q3kThreeMul t`・q3kNormBase の 3-可除分解補題（「1+3t の norm = 1+3s」の環恒等式） | `q3k_normBase_*`・`q9ci_three_reg_L2`（:412） | 中 |
| U-1 | **★ M₉ 主単数補題**: `q27u_one_add_three_unit : q3kUnitMem (q3kAdd q3kOne (3·t))` — U-0 → `q3rqUnitMem (1+3s)` → `IsZpUnit 3` レベル 1 rep ≡ 1 | `IsZpUnit`（ZpUnits:38）・rep 橋（`q9cs_add_valn` 型） | 中（配管） |
| U-2 | **★ hn 側の楔**: 単数 x に対し q3kNormBase x のレベル n rep が 3 と素（`IsZpUnit` の消去形）→ q27cs の `hn` へ輸送する形の補題（q27cs-9 の rep 橋と接続） | `q27cs_k_mul0_*_valn`（DescentSpike :1101/:1147）・`q9cs_zero_rep_dvd`（:547） | 中 |

これが閉じれば q27ps（w̃・u₁₈・3=π₂₇¹⁸u₁₈）と q27c の hn discharge が両方 unblock される。**閉じなければ（=U-1/U-2 が予想外に重ければ）q27ps を M→L に格上げして fable スポットを充てる**——判定点が 1 ファイルに局在するので損切りが効く。

### 期待 s 移動（正直・帽子遵守）

- 本 2 モジュール: **s_A6 0.61 のまま・s_A7 0.57 のまま・complete_pct 0 前進**（両ヘッダに明記）。
- キャンペーン完走時（q27mb＋crk27）: A6 は帽子 ≤0.65 の内側で +0.01–0.02 の nudge（crk 先例準拠）・**帽子は超えない・外さない**。A7 側は scope §5 の敵対的相場（+0.01〜+0.03）を維持——本書は上方修正しない。

---

## 4. 正直な予測: クリーンクローン（sonnet 可）と真に新規（opus/de-risk 先行）の切り分け

| 部品 | 分類 | 根拠 |
|---|---|---|
| q27k K-0〜K-2（台・環公理・embed） | **クリーンクローン（大部は sonnet 可・ただし 1 ファイル一貫性のため opus 1 枠推奨）** | q3k-2 が base 抽象で書かれている（§2.1）|
| q27k K-3〜K-6（τ・ノルム・単数・ζ₂₇） | クローン＋新インスタンス（opus） | d 固有補題の差し替えが入る |
| q27yp（Z 冪正規形・後続） | クリーンクローン（sonnet） | scope 表の通り |
| q27ci の rawF 実例化・no-cbrt of ζ₉ | クリーンクローン（opus 下限） | `q9c_rawF*` 一般 CRing・`q9ci_cube_1` 帰着（scope §3.1–3.2 を本体で追認） |
| **M₉ 単数判定補題族（U-1/U-2）** | **真に新規・de-risk 先行必須** | N(w)=−1 の消失点（§2.3）——ただし付値論でなく mod-3 簿記 |
| q27ps の恒等式部（(Z−1)³=π₉w̃ 等） | クローン（opus） | q9ps 消費・環 rw のみ（§2.2） |
| q27c の E′=0 導出・基底 TDF 1・スロット 1/2 忠実性物量 | 新規だがイディオム既知（opus・spike 仮定の discharge） | spike 正直限定 1/3/4 が経路を名指し済み |
| q27cs 降下核 | **完了**（spike） | §1.2 |

**ラウンド見積り更新**: scope の「詳細化 1＋実装 3–4＝4–5 ラウンド」のうち詳細化 R1 相当（q27cs de-risk）は 2026-07-14 に消化済み。残りは **実装 3–4 ラウンド**（R-a: q27k＋q27u spike＋q27yp ∥／R-b: q27ci＋q27ps／R-c: q27c＋q27tl／R-d: q27mt→q27mr→q27mb＋crk27）。下振れシナリオ（明記）: U-1/U-2 の配管が 1 ラウンドで閉じない場合＋監査が「通算 3 度目のクローン」割引を最大適用する場合、A6/A7 とも据え置きで物量だけ増える——その場合も spike 群は本物基盤として残る（水増しではないが、着工継続の可否はその時点で親がユーザーに確認するのが §2 規約適合）。

---

## 5. 推奨（最初の実装スライス＋先行 spike 項目）

1. **最初の opus スライス = q27k（`Q3KummerNonic.lean`・§3 Module 1）**。依存ゼロ（q3k/q9ps 消費のみ）・全段の帰着先が named 実在補題・キャンペーン 10 モジュール中 7 本（q27ci/q27yp/q27ps/q27tl/q27mt/q27mr/q27mb）の共通土台。ヘッダに complete_pct 0 前進と後続本物化計画（q27* 連鎖→q27mb→crk27）を明記して着工可。
2. **同ラウンドで先に潰す単一 de-risk 項目 = M₉ 単数判定 spike（q27u・§3 Module 2・U-1 主単数補題 `q3kUnitMem (1+3t)` と U-2 hn 楔)**。これは scope が名指しした genuine-new (i) の核心であり、q27cs spike が仮定で回避した `hn` と、level-9 の N(w)=−1 が消える q27ps の w̃ 単数の**両方の唯一の未検証点**。q27k と独立（q3k 語彙のみ）なので並走できる。
3. やってはいけないこと: q27u が閉じる前に q27ps 本体・q27c 本体へ着工しない／「q27cs は克服済みだから残りは全部クローン」と書かない（E′=0 導出・基底・物量は残る）／本スライスで s_A6/s_A7 を動かしたと申告しない／crk・q9mb・spike の正直限定の消去・弱化をしない。

---
*作成: 詳細化ラウンド（設計のみ・Lean 実装なし・tier-L 枠）。判定の根拠に読んだもの——**.lean 本体**: `IUT/Q3Mu27DescentSpike.lean` 全 1192 行（ヘッダ正直限定 1–5・`q27cs_cramer0/1/2` :451/:593/:730 の完全 rw 証明・`q27cs_norm_peel` :932・`q27cs_descent_even/odd` :973/:1003・`q27cs_descent_all` :1055・`q27cs_k_mul0_fst/snd_valn` :1101/:1147・sorry 出現はヘッダ注記 :65 の「sorry 皆無」のみ）・`IUT/Q3KummerCubic.lean`（:59 ブリッジ・:67 台・:99 q3kMul・:122 「d を抽象環元として扱う」・:454 `q3kRing : CRing`・:504–:560 σ・:620–:682 Wt/normBase・:810 norm_eq・:837 `q3k_kM_eq`・:868–:917 UnitMem/Inv/U・:929–:974 ζ₉ 位数 9）・`IUT/Q3KummerPiSplit.lean`（:104 π₉・:219 pi9_cube・:312 `q9ps_w_norm : N(w)=−1`・:443 u₆・:446 u6_unit・:467 `q9ps_three_split` 本体全読）・`IUT/Q3RamifiedQuadratic.lean`（:140 q3rqNorm・:352 `q3rqUnitMem := IsZpUnit 3 (q3rqNorm x)`・:364–:380 閉形式逆元）・`IUT/ZpUnits.lean`（:38 `IsZpUnit` = レベル 1 剰余のみ——§2.3 の決定的根拠）。**grep/glob 実測**: IUT/ の q27* は Q3Mu27DescentSpike.lean のみ・IUT.lean:649 で import 済み・`q9ci_cube_1` :370・`q9ci_three_reg_L2` :412・`q9ci_unit_reg_L2` :463・`q9ci_embed_reg_M` :527・`q9ci_no_cbrt_zeta/zetaSq` :628/:661・`q9c_rawF3` :87（CRing パラメータ形）・`q9c_m_mu3_complete` :1176・`q9c_mu9_complete` :1311・`q9cs_*` :129–:547・`q3cu_ppow_dvd` Q3TateCuspidalization:126・`euclid_int` RootsOfUnity:63。**git 実測**: spike commit `3b99808`（2026-07-14 "Level-27 de-risk: μ₂₇-completeness descent spike"）・crk commit `28c10b0`（"A6 0.60→0.61"）。**metric 実測**: `target_ledger.json` A6 status 0.61／A7 status 0.57・`graph-meta.json` complete_pct 57。**設計文書**: `audit/level27-kill-scope-2026-07-11.md` 全文・`audit/pillar-A6-monotheta-kill-detail-2026-07-11.md` 全文・`IUT/CyclotomeRecoveryThetaKill.lean` ヘッダ（正直限定 (1)–(4)・level-27 named future target :15/:46/:296）。scope §1.3 の N_rel(w̃) 閉形式（=1+3ζ₉u₆²π₉¹⁰+(ζ₉−ζ₉²)u₆³π₉¹⁵・中項 val16・末項 val15）は本書で再検算済み。*
