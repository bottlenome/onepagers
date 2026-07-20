# A9 tripod（ℙ¹∖{0,1,∞}）基本群・第一データの到達可能性詳細化 — 2026-07-20

**分類: [設計のみ / design-only]・tier-L 詳細化・complete_pct 0 前進（Lean コードなし・共有ファイル変更なし）・§4 規約（既存の正直な限定を消さない・弱めない・過大主張しない）**

- 対象: 柱A **A9「Belyi 化 / 遠アーベル幾何入力(実)」**（weight 10・現 s_A9 = 0.12）。
  既実装 blc（`IUT/BelyiCubicReal.lean`・分岐値集合 {0,1,∞} の決定）と
  blr（`IUT/BelyiCubicRamification.lean`・正確な分岐プロファイル (2,2,3)）の監査が
  名指しで残した正直な限定——「**noncritical Belyi / cuspidalization ではない:
  tripod の実 π₁ は 0 のまま**」（blr ヘッダ正直限定 2・blc §4.2-3）——を
  disproof-first で再検査し、次の実 A9 増分「**tripod 基本群の第一データ**」の
  到達可能性を判定する。
- 先例手順: `audit/pillar-B2-T3-M2-M3-completeness-detail-2026-07-11.md`（choice 障害の
  実検査・付録つき）と `audit/pillar-A6-monotheta-kill-detail-2026-07-11.md`
  （対象不一致の攻撃）の型に従う。本書も**核イディオムの実コンパイル検査**
  （付録 A・core Lean で PASS）を実行した。

---

## 0. TL;DR（先出し結論）

**verdict は二層に分かれる。**

1. **到達可能（research-blocked ではない）**: 「tripod π₁ の第一データ」を正直に
   定義した対象——(i) **自由群 F₂ の実 Grp 構成**（reduced words・choice-free・
   普遍性つき）＋ (ii) その有限商 ℤ/3 × ℤ/3 の「**{0,1,∞} の外で不分岐な実
   Kummer 被覆の実デッキ群**」としての実現——は、既存資産
   （`galPi1Perm`/`galPi1SymGrp`・`cnfPhi3Field`・`polyCRing`・`RingHom`・
   blc の分岐イディオム）の上に **4 ファイル・2 ラウンド**で建設できる。
   唯一の新イディオム（相殺 prepend の両側逆補題）は**本ラウンドで使い捨て
   スパイクを実コンパイルし PASS を確認済み**（付録 A・SPIKE-OK・禁止タクティク
   なし・choice なし）。
2. **research-blocked / 恒久限定**: 「**tripod の π₁ そのもの**」——位相ループの
   群 π₁^top(ℂℙ¹∖{0,1,∞})、スキームのエタール基本群 π₁^ét = F̂₂（副有限完備化）、
   π₁^temp——は建たない。ℂ・位相・被覆空間・スキーム・エタールサイトが core に
   無い（リポジトリ恒久限定）ためであり、この四半期の射程外。よって新モジュールの
   正直な主語は「F₂（tripod π₁ の群論的内容）＋その実被覆デッキ実現」であって
   「tripod の π₁」ではない、とヘッダに明記する（§3 正直な限定 1）。

**s_A9 予測（敵対的・監査確定が条件）**: 梯子 BLW-1〜4 完了で 0.12 →
**中央値 0.16–0.18**（敵対的下限 0.14）。**F₂ 単独（BLW-1 のみ）は +0.00–0.01 に
留まる**（§2 攻撃 3——bare F₂ は抽象群論と査定されるリスクが高い）。
推奨第一手は **BLW-1（F₂）と BLW-2（実 Kummer 被覆）の並列 opus 2 枠**（§5）。

---

## 1. 正確なギャップ（何が有り・何が無いか）

### 1.1 有るもの（本体確認済み・ファイル実在）

**A9 側（Belyi 幾何・監査済 0.12）**

| 資産 | 場所 | 内容 |
|---|---|---|
| 実 Belyi 多項式 f=3X²−2X³・分岐値 {0,1,∞} の決定 | `IUT/BelyiCubicReal.lean`（blc 848 行） | `blc_branch_locus`（上界・任意零因子なし CRing）・`blc_fiber_zero`=X²(3−2X)・`blc_fiber_one`=(X−1)²(−(2X+1))・`blc_infty_chart`（e_∞=3 チャート）。独立監査 0→0.1（`audit/reaudit-A9-belyi-cubic-2026-07-11.md`） |
| 正確な分岐プロファイル (2,2,3)・臨界ファイバー第三根・RH 数値 | `IUT/BelyiCubicRamification.lean`（blr 204 行） | `blr_ram0_exact`/`blr_ram1_exact`（e=ちょうど 2）・`blr_fiber0_simple`(3/2)/`blr_fiber1_simple`(−1/2) |
| blr の正直限定 2（本書の検査対象） | blr ヘッダ | 「noncritical Belyi / cuspidalization ではない: 高さ制御・**tripod の実 π₁ は 0 のまま**」 |

**π₁・群機構（他柱計上・消費可能）**

| 資産 | 場所 | tripod π₁ での役割 |
|---|---|---|
| `Grp`/`Hom`/`prodGrp`/`intGrp`（デッキ ℤ） | `IUT/FundamentalGroup.lean` 74/125/444/283 | 群の土台。intGrp はリポジトリ唯一の「自由群」（=F₁） |
| **`galPi1Perm α`（明示両側逆 witness の全単射）・`galPi1SymGrp α : Grp`** | `IUT/GaloisPi1Iso.lean` 144（M286F-1b） | **van der Waerden 埋め込みの受け皿**（choice 回避済の実対称群・群公理は外延性で完全証明済） |
| `limitGrp`/`zmod n : Grp`/`quotGrp` | `IUT/Profinite.lean` 167/262/78 | 有限商 ℤ/3 の実 Grp |
| `Subgroup`/`imSubgroup`/第一同型定理 | `IUT/QuotientGroup.lean` 189 ほか | 像・商の帳簿 |
| `GAction G` | `IUT/GaloisCategory.lean` 50 | デッキ作用の器 |
| 実デッキ先例: q3td（ℤ を実 Tate 被覆 ℚ₃^×→E_q(ℚ₃) 上で本物化） | `IUT/Q3TateDeck.lean`（`q3tdPeriodHom` 85・`q3td_deck_free`） | **本物化の確立パターン**: 「抽象群 + 実被覆上の実現準同型」で初めて π₁ 対象になる |
| 実 pro-3 tempered π₁ = tmzLimit × intGrp | `IUT/Q3TemperedPi1.lean`（q3tpGroup） | A5 計上・Tate 曲線側。tripod とは主語素 disjoint |

**環・円分部品（Kummer 実現用・消費可能）**

| 資産 | 場所 |
|---|---|
| 実 ℚ(ζ₃) = `cnfPhi3Field : IUTField`（Φ₃ 関係 `cq0PS` つき）・`cnfExt3`・`cnfGal3` | `IUT/CyclotomicField3.lean` 59–77・`IUT/Cq3Base.lean` |
| `polyCRing (R : CRing) : CRing`（実多項式環）・`psSingle`/`psAdd`/`psMul` | `IUT/SimpleExtension.lean` 146・`IUT/PowerSeries.lean` |
| **`RingHom (R S : CRing)`** | `IUT/Ring.lean` 197 |
| `formalDeriv`・一次因子ライプニッツ・重根→導関数零（blc-4 の分岐イディオム一式） | `IUT/SeparablePoly.lean`（M270F） |
| `evalSum`/`evalHomId`（打ち切り評価） | `IUT/EvaluationHom.lean`（M274F） |
| `IUTField extends CRing`・零因子なし消去 | `IUT/Field.lean` 44 |

**A8 の楕円 cuspidalization（q3cu/q3c3）は Tate 曲線側**であり、[AbsTopII] の
Belyi cuspidalization（tripod・strictly Belyi type）とは別物。A9 の tripod 側は 0。

### 1.2 無いもの（grep・本体確認）

1. **自由群・自由積・語（word）簿記が一切ない**。`grep -riE "free group|word|reduced"`
   の実ヒットは CyclotomicGal9 の「reduced value」（多項式簡約・無関係）のみ。
   F₂ を作る部品（reduced words・相殺乗法）はゼロから要る。
2. **tripod という主語がない**。`grep -ri tripod IUT/` のヒットは blc/blr の
   正直限定の文言のみ。ℙ¹∖{0,1,∞} の座標環（局所化 K[t, 1/t, 1/(1−t)]）も無い。
3. **有理関数体 ℚ(t) が無い**（前回 A9 設計書 `audit/A9-belyi-anabelian-input-detail-2026-07-11.md`
   候補 a′ のブロッカーの継承）。
4. **位相・ループ・被覆空間・ℂ・スキームのエタールサイトが無い**（リポジトリ恒久限定）。
   `GrothendieckGalois`/`ProfinitePi1` は体上の有限エタール代数と Galois 塔まで。

### 1.3 本書の問い

blr 正直限定 2 の「tripod の実 π₁ = 0」に対し、**choice-free・本物**の第一増分は
何か。「tripod π₁ = F₂（幾何的・pro 離散）」の**どの層**が core Lean に降りるか、
降りない層はどこで**正直に**切るか。

---

## 2. Disproof-first 検査（対象不一致・choice 障害・toy 主語リスクの攻撃）

### 2.1 攻撃 1（最重要・object-mismatch）: 「tripod の π₁」は何を意味し得るか

本物の数学で tripod π₁ は (a) 位相的 π₁ = F₂（2 つのパンクチャ周りのループが自由生成）、
(b) π₁^ét = F̂₂（副有限完備化・Mochizuki の Belyi cuspidalization の主語）、
(c) π₁^temp（p 進）のいずれかである。**判定: (a)(b)(c) いずれも「空間の π₁」としては
建たない**——ループ（位相）・エタール被覆の分類（スキーム）・Berkovich 被覆が core に
皆無であり、これは A9 前回設計・blc §4.2-4 が既に恒久限定として明記した境界である。

**残る誠実な標的**は「π₁ の**群論的内容**とその**有限商の実現**」の対:
- **F₂ という群それ自体**（reduced words による実 Grp・生成元 2・普遍性）——
  これは空間なしで定義できる本物の無限非可換群であり、リポジトリに存在しない。
- **F₂ の有限商が、実際に {0,1,∞} の外で不分岐な実被覆のデッキ群として実現される**
  こと——「tripod の被覆」を空間なしで語る正直な形式は blc が確立済み
  （「分岐値集合 ⊆ {0,1,∞}」を任意零因子なし CRing にわたる幾何的主張として言明）。

この対は q3td の確立パターン（intGrp が実 Tate 被覆上の `q3tdPeriodHom` で初めて
「実デッキ群 ℤ」になった）の tripod 版であり、対象不一致はない。**「=π₁(空間)」の
同定だけが恒久限定として残る**（§3 正直な限定 1 に搭載・消さない）。

### 2.2 攻撃 2: F₂ は本当に choice-free に建つか（新イディオムの実検査）

自由群の古典的構成の Lean 化には悪名高い罠が 2 つある。

1. **簡約語の乗法の結合律**（直接証明は場合分けの爆発）。
   **回避策: van der Waerden の埋め込み**——各文字を「簡約語の集合上の全単射
   （相殺つき prepend `lcons x` と逆文字の `lcons (linv x)`）」として
   `galPi1Perm`（M286F・**明示両側逆 witness・choice 回避済**）に実現し、
   語の乗法を `galPi1SymGrp` の合成から輸送する。結合律は Sym の結合律
   （`galPi1Perm.ext rfl rfl`・証明済）から**無料**で降りる。
   この経路の**唯一の核補題**は「reduced 語上で `lcons x ∘ lcons (linv x) = id`」
   （文字レベルの両側逆）である。
2. **決定可能性・Markov 型障害**: 簡約判定が Prop だと `decide`/選択が要る。
   **回避策**: `cancels`/`red` を **Bool 値再帰関数**で定義し、担体を
   `{w : List Ltr // red w = true}` にする（B2 詳細化 §2.3 の O2 教訓の遵守:
   語・簡約・作用は全て**データ関数**であり ∃ 消去は一度も出ない）。

**検査結果: 障害なし——核補題を本ラウンドで実際に core Lean でコンパイルし PASS**
（付録 A・`TfgSpike.lean`・mathlib なし・簡禁止タクティク（simp/decide/by_cases/
rcases）なし・choice なし・`lcons_cancel`/`lcons_cancel'`/`red_lcons` 全て証明完了・
SPIKE-OK）。核補題が閉じた以上、残り（φ : 語 → Sym の準同型性・φ(w)([]) = w による
単射性・逆元 = 逆順逆文字列・普遍性 lift）は同じ帰納の foldr 簿記であり、
新しい障害クラスを含まない。

### 2.3 攻撃 3（敵対的・最大の値切りポイント）: bare F₂ は toy 主語ではないか

**判定: 単独では YES のリスクが高い。** 前回 A9 設計書が候補 (c)（置換対 dessin 単独）を
「実 Belyi 写像との対応を証明しない限り、敵対的既定で模型判定」と**却下**した刃は、
bare F₂ にもそのまま当たる: 生成元を「0 の周りのループ」と**呼ぶ**のは命名であって
定理ではない。AUDIT_RUBRIC の敵対的既定では、実現なしの F₂ は
「[抽象]——本物の群論だが A9 の主語（Belyi/遠アーベル入力）ではない」と査定され、
**s_A9 +0.00–0.01 止まり**が相場である（q3td 先例の逆読み: intGrp 自体は M9 時代から
存在したが A5 加点は実被覆実現 q3td を待った）。

**帰結（設計制約）**: F₂ モジュールは実現モジュール（§2.4）と**束で**計画し、
capstone（BLW-4）で「生成元 ↦ 実デッキ自己同型」の実現準同型を必ず立てる。
BLW-1 単独で止まった場合は「A9 未加点・柱横断の群論インフラ」と正直に報告する。

### 2.4 攻撃 4: 実現先の「tripod の実被覆＋非自明実デッキ群」は建設可能か

現物は無い（§1.2）。候補を敵対的に検査した:

- **blc の f = 3X²−2X³ 自身**は tripod の実次数 3 被覆だが**ガロアでない**
  （モノドロミー S₃）ため被覆変換は id のみ——F₂ の非自明商の実現先に**ならない**。
  ガロア閉包（次数 6・resolvent 体）は実建設が重い（後続候補・§3 末）。
- **Kummer 被覆 t = u³（採用）**: K = ℚ(ζ₃) = `cnfPhi3Field` 上で、埋め込み
  ι : K[t] → K[u]（t ↦ u³・係数 3 倍間引きの実 `RingHom`）と、デッキ変換
  σ : K[u] → K[u] を**係数スケーリング (σf)ₙ = ζ₃ⁿ·fₙ** で定義する。
  - σ は実環準同型: 加法は係数ごと、乗法は Cauchy 積の各項で
    ζ₃ⁿ = ζ₃ⁱ·ζ₃^{n−i}（冪加法・帰納）を分配する総和 congruence——中難度・
    確立イディオム帯（blc の係数 funext 計算の族）。
  - σ³ = id は ζ₃³ = 1 から係数ごと（ζ₃³=1 は Φ₃ 関係 `cq0PS`: ζ²+ζ+1=0 と
    ζ³−1 = (ζ−1)(ζ²+ζ+1) の環計算）。σ∘ι = ι は (u³ の像の係数は 3∣n のみ) から。
  - **固定係数定理**（Kummer descent の核）: σf = f ⟺ (3∤n → fₙ = 0)。
    ⟸ は自明、⟹ は「ζ₃ⁿ·x = x かつ ζ₃ⁿ ≠ 1 ⟹ x = 0」——体の消去
    （`IUTField.eq_zero_of_mul_eq_zero_left` 型）と ζ₃ ≠ 1・ζ₃² ≠ 1
    （ζ=1 なら Φ₃(1)=3=0 で char 0 に矛盾）で閉じる。**choice-free**。
  - **分岐値 ⊆ {0, ∞}**: X³ − y の二重根 (X−a)² ⟹ D(X³) = 3a² = 0 ⟹ a = 0
    ⟹ y = 0——**blc-4 と同一のイディオム**（`formalDeriv_mul_linFactor` 2 回＋
    `evalSum` 分配）で、blc より単純な多項式。∞ チャートは blc_infty_chart の写経。
  - **ℚ(t) 不要**: 被覆は環の拡大 K[t] ↪ K[u] で言明し、「tripod への制限」は
    blc 流の「分岐値 ⊆ {0,1,∞}」形式で顕示する。前回設計の候補 a′ を塞いだ
    分数体ブロッカーを**回避**できる。
- **twin 被覆 v³ = 1−t**: 同じ σ: v ↦ ζ₃v が 1−v³ を固定。分岐値 ⊆ {1, ∞}。
  BLW-2 の写経（tier S/M）。二本の分岐値の**和集合が {0,1,∞} 全体**という
  tripod 三点性の言明が対で閉じる。

**判定: 建設可能・確立イディオム帯。** 残る要注意点は σ の乗法性（総和 congruence）
1 点のみで、fallback（σ を係数条件 witness 形で運ぶ弱形）はあるがデッキ「群」
主張が弱まるため原則本形で行く（§5 de-risk 順位 1）。

### 2.5 攻撃 5: 本物の π₁^ét(tripod) = F̂₂ はどうか

**blocked（この四半期は着手しない・named future target）。** 3 層の障害:
(i) 副有限完備化は「F₂ の全有限指数正規部分群」上の逆系を要し、choice-free な
索引化・cofinal 鎖の選定が未整備（既存 `limitGrp` は Nat 鎖 `natSystem` が主）。
(ii) F₂ ↪ F̂₂（自由群の residual finiteness）は本物の定理——Stallings の置換構成で
原理的には choice-free に落ちるが、独立の 1 モジュール級。
(iii) そもそも「= スキームの π₁^ét」の同定は恒久限定（§2.1）。
現実的な後続レバーは **pro-3 アーベル商** π₁^{ab,(3)} = ℤ₃×ℤ₃ を `zmodSystem`/
`limitGrp` で建て、Kummer 塔 t^{1/3ⁿ} のデッキ = 実 μ_{3ⁿ}（`cmrGrp`・`tmzLimit`）に
結ぶ道（A3/A7 資産の**消費**として・二重計上 firewall つき）。

### 2.6 攻撃 6: import 循環・二重計上

**無い。** 新規 4 ファイルは葉のみ: BLW-1 は `IUT.GaloisPi1Iso`（＋List core）、
BLW-2/3 は `IUT.CyclotomicField3`・`IUT.SeparablePoly`・`IUT.EvaluationHom`・
`IUT.Ring`、BLW-4 は BLW-1/2/3 と `IUT.Profinite`（zmod）を import——全て既存 DAG の
下流。二重計上 firewall: 円分（cnf/cq3・A3 計上）・対称群（M286F・A4 系計上）・
Tate デッキ（q3td・A5 計上）は**消費のみ・再証明ゼロ**。blc/blr は BLW 系から
参照するだけで再輸出しない。A5 の q3tp と主語素 disjoint（Tate 曲線・q は非登場）。

### 2.7 総合判定

**「tripod π₁ の第一データ」＝ F₂（実 Grp・choice-free）＋ μ₃ Kummer 実現、は
到達可能（research-blocked ではない）。** 核イディオムは実コンパイル検証済（付録 A）。
一方「tripod の π₁ そのもの」（位相・エタール・tempered）は blocked であり、
新モジュールはその旨を正直な限定として恒久搭載する。blr 正直限定 2 は
「tripod π₁ は 0」から「第一データ（F₂＋μ₃ デッキ実現）まで前進・
cuspidalization / noncritical / F̂₂ は 0 のまま」へ**更新されるだけで消えない**。

---

## 3. マイルストーン梯子（新規 4 ファイル・全 choice-free・共有ファイル不変更）

| 段 | ファイル（prefix） | 内容 | 消費資産 | 難度 tier |
|---|---|---|---|---|
| **BLW-1** | `IUT/TripodFreeGroup.lean`（tfg） | **F₂ の実 Grp**: 文字 `Ltr = Bool × Bool`・Bool 値 `red`/`cancels`・担体 = 簡約語 Subtype・`lcons` 相殺 prepend（付録 A の核補題）→ van der Waerden: 文字ごとの `galPi1Perm`、φ : 語 → `galPi1SymGrp`、乗法 = φ 経由・結合律は Sym から輸送・単射性は φ(w)([]) = w・逆元 = 逆順逆文字・生成元 `tfgA`/`tfgB`・**普遍性 `tfg_lift : (G : Grp) → G.carrier → G.carrier → Hom tfgGrp G`**（語 ↦ 像の積・map_mul は lcons 帰納）＋生成元上の一意性・非可換 witness `tfg_ab_ne_ba`（リスト計算） | `galPi1Perm`/`galPi1SymGrp`（M286F）・List core | **M+**（opus・φ 準同型補題の簿記で fable スポット許容）・500–800 行 |
| **BLW-2** | `IUT/TripodKummerMu3.lean`（tkm） | **実 Kummer 被覆 t = u³**（K = `cnfPhi3Field`）: ζ₃³ = 1 / ζ₃ ≠ 1 / ζ₃² ≠ 1（tkm-0・Φ₃ 環計算）・埋め込み ι : `RingHom (polyCRing K) (polyCRing K)`（係数 3 倍間引き）・σ 係数スケーリング `RingHom`・**σ³ = id・σ∘ι = ι・固定係数定理**（Kummer descent 核・§2.4）・デッキ `GAction (zmod 3)`（σ 冪・作用則）・**分岐値 ⊆ {0,∞}**（blc-4 イディオムの X³ 版）＋ ∞ チャート | `cnfPhi3Field`・`cq0PS`・`polyCRing`・`RingHom`・`psMul` 係数機構・`formalDeriv` 系・`evalSum` 系・`zmod` | **M**（opus）・400–600 行 |
| **BLW-3** | `IUT/TripodKummerOne.lean`（tk1） | twin 被覆 **v³ = 1−t**: 同 σ・固定係数・分岐値 ⊆ {1,∞}（D(1−X³) = −3a²）・**二被覆の分岐値和集合 = {0,1,∞}**（tripod 三点性の対言明） | BLW-2 の写経＋blc | **S/M**（opus か sonnet）・~300 行 |
| **BLW-4** | `IUT/TripodPi1FirstData.lean`（tpf） | **実現束ね**: `tfg_lift` による全射 F₂ ↠ `prodGrp (zmod 3) (zmod 3)`（a↦(1,0)・b↦(0,1)・全射は生成元命中）・**実現準同型**「a の像 = tkm の実デッキ σ_u・b の像 = tk1 の実デッキ σ_v」（各 zmod 3 → 実環自己準同型群の作用で言明）・capstone `TripodPi1FirstData` 構造（F₂ + 2 実被覆 + 実現の witness を要求する grounded 構造）＋正直 scope | BLW-1/2/3・`prodGrp`・`zmod`・`GAction` | **S**（sonnet 可・束ね） |

依存: **BLW-1 ∥ BLW-2 並列可**（独立）。BLW-3 ← BLW-2、BLW-4 ← 全部。
合計 **2 ラウンド**（R1: BLW-1 opus + BLW-2 opus 並列／R2: BLW-3 + BLW-4）。

### 正直な限定（新ファイル群のヘッダに必ず書く・消去/弱化禁止）

1. **「tripod の π₁ そのもの」ではない**: F₂ は簡約語による組合せ群であり、
   位相ループの群・スキームの π₁^ét との同定は不主張（ℂ・位相・エタールサイト
   皆無の恒久限定の継承）。機械可検証内容は「自由群 F₂ ＋ その ℤ/3×ℤ/3 商の
   {0,1,∞} 外不分岐実被覆デッキとしての実現」。
2. **実現は商ごと**: 各 ℤ/3 が別々の実被覆（u³ = t と v³ = 1−t）に実現される。
   単一の (ℤ/3)² 被覆（fiber 積）・**非可換商**（S₃ 等・blc の f のガロア閉包）の
   実現は未達（named future targets）。
3. **π₁^ét = F̂₂（副有限完備化）・π₁^temp・residual finiteness は 0**（§2.5）。
4. **tripod の座標環（局所化 K[t,1/t,1/(1−t)]）不在**: 「被覆」は環の拡大
   K[t] ↪ K[u] で、「tripod 性」は分岐値 ⊆ {0,1,∞} で顕示（blc §4.2-4 の
   Option K / チャート流儀の継承）。
5. **Belyi cuspidalization（[AbsTopII]）・noncritical Belyi（[GenEll]）は 0 のまま**:
   blr 正直限定 1–2 は全文継承・並置。
6. K = ℚ(ζ₃)・3 次 Kummer スライス固定（p = 3 恒久限定の族）。位相・解析なし。

---

## 4. 正直な status 予測（敵対的・過大主張しない）

- **BLW-1 単独: s_A9 +0.00–0.01**。攻撃 3 の通り、実現なしの F₂ は「[抽象]・
  柱横断インフラ」査定が敵対的既定。単独では A9 を動かさない前提で計画する。
- **梯子完了（BLW-1〜4）: s_A9 0.12 → 中央値 0.16–0.18**。相場根拠: blc の
  「主語クラス初の実対象＋完全証明」= +0.10、blr の「同主語の実深化」= +0.02 に
  対し、本梯子は **A9 の第 2 系統（遠アーベル入力・[AbsTopII] 側）の初の実対象**
  （実 F₂ ＋ 実デッキ実現）であり +0.04–0.06 帯。
- **敵対的下限 0.14**: 監査が「Kummer 被覆は円分機構の再包装・F₂ は抽象群論」と
  値切るケース。反論材料: (i) 円分の再証明ゼロ（消費のみ・firewall §2.6）、
  (ii) 固定係数定理・分岐値決定・実現準同型は円分にも群論にも無い新言明で、
  主語は「{0,1,∞} 外不分岐被覆のデッキ幾何」という A9 固有クラス。
- **Σ_A 算術**（現 ledger 実測: Σ_A = 55.96 → 表示 56）: +0.04 で 56.36（表示 56
  据え置き）、+0.06 で 56.56（表示 57）。**表示 mover は期待しない**と正直に報告する。
- **残る cap**: 正直な限定 1–5 が残る限り **A9 ≤ 0.35 目安**。本丸は
  ①Belyi cuspidalization（[AbsTopII]・strictly Belyi type）、②noncritical Belyi
  （[GenEll]・IUT IV 高さ制御）、③F̂₂/π₁^temp——いずれも研究級で、①③は §2.5 の
  pro-3 アーベル商・residual finiteness が現実的な次の足場。
- **過大主張の禁止リスト（実装ラウンドのヘッダへ転記）**: 「tripod の π₁ を構成した」
  と書かない（第一データのみ）／定理名・見出しに「π₁^ét」「π₁^temp」を使わない／
  blc・blr・A5 q3td/q3tp の正直な限定の消去・弱化・再主張をしない／
  「Belyi cuspidalization に着手した」と書かない（前提部品が別）。

---

## 5. 推奨する第一実装スライス（opus 帯）と de-risk 順位

**推奨第一手 = BLW-1 と BLW-2 の並列 opus 2 枠**（独立・共有ファイル不変更・
サブエージェント新規ファイルのみ規約に適合）。単一枠しか取れない場合は
**BLW-2 を先**にする（確立イディオム帯で確実に実加点素材になる。F₂ 抜きでも
「実 Kummer 被覆の実デッキ μ₃ と固定係数定理」単体で A9 の遠アーベル入力側の
最初の実対象になり得る）。BLW-1 には本設計書の van der Waerden 経路と
付録 A のスパイクを実装指示に添付する。

**de-risk 順位**:
1. **BLW-2 の σ 乗法性（Cauchy 積の総和 congruence）**——実装冒頭で `psMul` の
   係数表示と既存の総和 congruence 補題の有無を確認し、無ければ最初に
   汎用補題（「各項が等しい有限和は等しい」＋ ζ 冪加法）を立てる。
   fallback: σ を係数条件 witness 形で運ぶ弱形（ただしデッキ「群」主張が
   弱まるため最終形では不採用）。
2. **BLW-1 の φ 準同型補題**（φ(lcons x v) = letterPerm x ∘ φ(v)・相殺分岐は
   付録 A の `lcons_cancel` で閉じる）——数学的障害はないが簿記量が多い。
   opus が詰まったら fable スポット 1 回で解消可能な種類。
3. BLW-4 の実現準同型の言明形（「zmod 3 の生成元 ↦ σ」を `GAction` で受けるか
   自己準同型のべき乗準同型で受けるか）——BLW-2 の着地形式を見てから確定する
   （インターフェース要件: σ とその冪は **def（データ）** で着地させること。
   B2 詳細化 §2.3 O2 教訓の遵守）。

親の統合時共有ファイル更新（実装後）: `IUT.lean` import・`tools/gen_graph.py`
PILLAR に BLW 系 4 件を `"A"` で追記・`graph.json` 再生成・`dashboard.md`/
`graph-meta.json`/`target_ledger.json` は**独立再監査（敵対的・AUDIT_RUBRIC）通過後のみ**。

---

## 付録 A: disproof-first スパイク（F₂ 核イディオムの実コンパイル検査・再現用）

使い捨てファイル `TfgSpike.lean`（scratchpad・成果物ではない・リポジトリ非追加）を
core Lean（`/root/lean4/bin/lean`・mathlib なし・import なし）で単体コンパイルし、
**PASS（SPIKE-OK）** を確認した。検査対象 = van der Waerden 経路の唯一の核補題:

```lean
abbrev Ltr := Bool × Bool                      -- (生成元, 符号)
def linv (x : Ltr) : Ltr := (x.1, !x.2)
def cancels (x y : Ltr) : Bool := (x.1 == y.1) && (x.2 == !y.2)
def red : List Ltr → Bool                      -- Bool 値・Markov 不要
  | [] => true | [_] => true
  | x :: y :: r => (!(cancels x y)) && red (y :: r)
def lcons (x : Ltr) : List Ltr → List Ltr      -- 相殺つき prepend（データ関数）
  | [] => [x]
  | y :: r => if cancels x y then r else x :: y :: r

theorem red_lcons   (x w) (hw : red w = true) : red (lcons x w) = true
theorem lcons_cancel  (x w) (hw : red w = true) : lcons x (lcons (linv x) w) = w  -- ★核
theorem lcons_cancel' (x w) (hw : red w = true) : lcons (linv x) (lcons x w) = w
```

証明は `cases`/`show`（ite の定義的簡約）/`rw`/`Bool.and_eq_true` のみ——
**禁止タクティク（simp/decide/by_cases/rcases）不使用・Classical.choice 不使用**。
`lcons_cancel`/`lcons_cancel'` が閉じたことで、各文字は簡約語集合上の
`galPi1Perm`（明示両側逆）になり、φ : 語 → `galPi1SymGrp` の foldr 定義・
結合律の輸送・φ(w)([]) = w による単射性は全て同型の帰納簿記に還元される
（§2.2）。すなわち **F₂ の choice-free 構成に数学的障害はなく、残るのは
実装リスク（簿記量）のみ**である。
