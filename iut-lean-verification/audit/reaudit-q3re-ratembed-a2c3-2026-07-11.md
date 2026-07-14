# 独立敵対的再監査 — A2c-3: 実環埋め込み ℚ↪ℚ₃（Q3RatEmbed・q3re）

- 日付: 2026-07-11
- 対象: `IUT/Q3RatEmbed.lean`（prefix `q3re`・534 行・commit 7d135df）
- 分類（自己申告）: **[実／(a) 昇格]**、A2 status=0.65、forecast +0.02〜0.04
- 監査者: 独立敵対的監査（本モジュール非執筆・default SKEPTICAL）
- 決定: **A2 0.65 → 0.67（+0.02）**、柱A complete_pct **54 → 55**（実ツール出力）
- 種別: この監査が s_A2 を SET する（display-mover attempt の評定）

---

## 0. 背景の警戒事項（threshold-shopping の疑い）

commit 履歴が本モジュールを明示的な「54→55 shortest path」キャンペーンの一次部品と位置づける:

```
7d135df A2c-3: real ring embedding ℚ↪ℚ₃ (Q3RatEmbed) — the completion link
3ba2de2 Detailing: level-27 second-layer kill (fallback for A→55) (design doc)
c0de15f Scope: shortest path pillar A 54→55 — 2-stage plan (A2c-3 primary + level-27 fallback)
```

CLAUDE.md §2 は「丸め閾越え専用の capstone 追加」を原則禁止する。よって本監査の第一の争点は
**A2c-3 が事前に名指しされた genuine な A2 残欠か、それとも表示を動かすためだけに追加された
capstone か**である。結論は §Part1(5): **事前名指し済の genuine 残欠**（後述）。ただし
「表示を動かすために merit 値を +0.03 へ inflate していないか」は Part2 で厳格に検証した。

---

## Part 1 — 正確性検証（全項目 YES）

### (1) 本物の環準同型・ratRel 同値上で well-defined・非空虚 — **YES**

- `q3reMap : ratRing.carrier → q3Ring.carrier`（L278）は `Quot.lift` で定義され、
  代表 `x : PreRat` を `q3reFrac x.num x.den.natAbs` へ送る。
- **well-defined 性が本物**: `Quot.lift` の第 2 引数（L280–306）が
  `x ~ x'`（＝`x.num * x'.den = x'.num * x.den`、ratRel）から
  `q3reFrac x.num x.den = q3reFrac x'.num x'.den` を**証明している**。証明は
  特徴付け方程式 `q3re_frac_spec`（image·q3reQ(den)=q3reQ(num)、L249）と単数右消去
  `q3_unit_cancel`（L256）で、共通単数 `q3reQ(x.den·x'.den)`（正整数像＝単元、
  `q3reQ_unit_pos` L266）を消去して降下する。**代表を 1 つ選んで同値を握り潰す
  「代表押し付け」ではない**——同値を単数消去で真に discharge している。
- 環準同型性 `q3re_map_add`（L346）・`q3re_map_mul`（L321）・`q3re_map_one`（L382）・
  `q3re_map_zero`（L391）はいずれも `q3_unit_cancel` ＋ `q3re_spec`（PreRat 上の特徴付け、
  L311）で本物に証明。**加法・乗法・0・1 すべて保存**。
- **非空虚**: `q3re_map_one : q3reMap ratRing.one = q3Ring.one`＝1↦1。零写像でも
  「全て↦0」でもない。単射（下記）も非退化を裏づける。

### (2) 単射・付値両立 — **YES / YES**

- 単射 `q3re_map_inj`（L416）: 非零分子の有理数の像は非零。`q3reQ_ne_zero`（L402）を経由し、
  `q3f_exact`（局所化の exactness）・`q3S_regular`（3 冪の正則性）・`toZp_injective`（ℤ→ℤ₃ 分離、
  LocalCFT.lean:143）を消費。環準同型の単射性の構成的忠実形（核自明＝非零↦非零）。**主張でなく証明**。
- 付値両立 `q3re_val_compat`（L446）: `q3fValRel (q3reMap x) (v₃(num) − v₃(den))`。
  `z3c_val_compat`（実 ℚ 側 pvq 付値＝ℤ₃ 内付値の一致、Zp3Complete.lean:173・本監査で proof body
  精読＝genuine）・`pvqNatVal_spec` を消費し、分母の 3 冪分解 `q3reSplit` の w が
  `pvqNatVal 3 den` に一致することを `pvqNatVal_spec` で結ぶ。**v₃(a/b)=v₃(a)−v₃(b) を証明**。

### (3) 稠密の honest scope — **YES（正直・過大主張なし）**

- `q3re_dense`（L485）は `z3c_int_dense`（ℤ が ℤ₃ で稠密）に三角可換 `q3re_int_compat` を
  付したもので、述べているのは **ℤ₃⊂ℚ₃ での整数像稠密**。
- ヘッダ「正直な限定」L31–33 が **full ℚ-density は主張しない**と明記。実際、本定理は
  ℚ の稠密性ではなく ℤ（⊂ℚ）の ℤ₃（⊂ℚ₃）内稠密の再ラベルであり、**位相的完備化の核心は
  未達**（これは Part2 の下げ要因）。honest scoping は正しく述べられている（消去・弱化なし）。

### (4) named 残欠 A2c-3 の discharge・threshold-shopping でない — **YES**

- A2 詳細文書 `audit/A2-real-padic-local-field-detail-2026-07-10.md` §5.2（**2026-07-10 付・
  本キャンペーン commit 7d135df=07-11 より前**）が A2c-3（ℚ↪ℚ₃）を明示的に列挙し
  「den=±3^w·d' 分解＋d' の単数逆元で環準同型は書けるが …0.65 到達に不要のため後続
  （**A2 0.65→0.7 の主部品**）」と記載。
- A2 の 0.65 監査（graph-meta A note）は残る限定 (ii) として
  「**ℚ↪ℚ₃ 体埋め込み（A2c-3）未接続で「K の完備化」は整数付値一致どまり**」と名指し。
- ゆえに A2c-3 は**閾を跨ぐためだけに発明された capstone ではなく、事前に名指しされた
  A2 の genuine な残欠 (missing completion link)** である。CLAUDE.md §2 抵触なし。

### (5) 二重計上なし — **YES**

- 既存 A2 資産（`q3Ring` 構成＝Q3LocalField、整数付値 z3vExact）とは**別対象**。
  q3re が新規に与えるのは **ℚ→ℚ₃ の写像そのもの**（既存には ℚ₃ 体オブジェクトと ℤ₃ 内付値は
  あったが ℚ からの埋め込みは皆無）。再ラベルでない。

### (6) 公理・禁止タクティク — **静的 clean（実行不能の限定を明記）**

- **本監査環境に lean/lake が未導入**（`which lean lake elan`＝該当なし・build.sh は elan 前提）。
  したがって `lake build IUT.Q3RatEmbed` および要求された 7 対象の `#print axioms`
  （q3re_map_mul/add/one/inj/val_compat/dense/exists）を**実行できなかった**。この限定を正直に記す。
- 代替の静的検査:
  - `grep sorry|admit|Classical|native_decide|axiom` → ヒットは L37 の**日本語コメント
    「Classical.choice を証明本体に導入しない・sorry 皆無」のみ**（実コードなし）。
  - 禁止タクティク `decide/simp/ring/nlinarith/linarith/by_cases/rcases/field_simp/norm_num`
    → **0 件**。`omega` 11 件はすべて純 Int/Nat（付値・指数・分母正値）で許容。
  - choice-free 性: `q3reSplit`（L117）は `Nat.strongRecOn`＋`Nat.decidable_dvd`（決定可能整除）
    のみ＝新規 choice なし。単数逆元は `zpUnitInv`（ZpUnits.lean:117、**明示的な幾何級数逆元関数**・
    ∃ 取り出しなし・本監査で proof body 精読）。
  - 全依存（`zpUnitInv`/`zpUnitInv_mul`/`z3c_val_compat`/`z3c_int_dense`/`q3f_exact`/
    `q3S_regular`/`toZp_injective`/`pvqNatVal_spec`）は**直前の A2 監査（reaudit-A2-…-07-10）で
    全 public 対象 70 個が [propext, Quot.sound] と確認済**。
- 評定: 静的検査の範囲で **clean**（新規 Classical.choice・sorry・axiom の混入は認められない）。
  ただし `#print axioms` 実行不能ゆえ「[propext, Quot.sound] を監査者自身が再実行して確認」の
  水準には未達＝**この 1 点のみ静的評定**である旨を honest に残す。

**Part 1 総合判定: 環準同型は genuine かつ ratRel 上 well-defined（YES）・単射/付値両立 genuine
（YES）・稠密 honest（YES）・named 残欠で padding でない（YES）・二重計上なし（YES）・
公理は静的 clean（実行不能の限定付き YES）。**

---

## Part 2 — s_A2 の敵対的決定

### 2.1 台帳・重量・丸め

- 柱 A の weight 総和 = 8+8+12+14+10+14+12+12+10 = **100**。
- 現状 status（A2=0.65 時）: Σ_A(w·s) = 6.8+5.2+9.0+7.7+2.0+8.12+6.72+7.8+1.0 = **54.34** → 表示 54。
- `tools/compute_complete_pct.py` は `round(num / den * 100)`（Python round＝banker's・round-half-to-even）。

### 2.2 s_A2 の merit 決定（表示に依存させない）

**決定値: s_A2 = 0.67（+0.02）。**

**上げ要因:**
1. **コードベース初の大域→局所埋め込み ℚ↪ℚ₃**。従来 0.65 は ℚ₃ 体オブジェクトと ℤ₃ 内付値まで
   だが ℚ からの写像は皆無だった。gap (ii) の名指し残欠を discharge。
2. **ratRel 同値上で well-defined の実証明**（q3_unit_cancel＋特徴付け方程式）＝非自明な proof work。
3. 環準同型＋単射＋付値両立の**三定理**が genuine（主張でなく証明）・choice-free。

**下げ要因（+0.03 を採らない理由）:**
1. **稠密は `z3c_int_dense` の再ラベル**（ℤ-in-ℤ₃）。『完備化』の位相的核心たる ℚ-density は
   未達で、埋め込みは**代数的（環＋付値）接続どまり**。ヘッドライン「completion link が接続」は
   半分しか達成されていない。
2. **なお ∃-inverse CRing への環射**であって total-inverse IUTField への体射でない
   （A2 恒久限定・0.65 cap に織込済＝二重には数えないが、埋め込みの「格上げ度」を抑える）。
3. A2c-3 は 0.7 到達に必要な **2 つの named 部品（A2c-3＋A2d：比較定理/位相）の一つ**
   （詳細文書 §6「0.7 以上は A2c-3＋A2d を要する」）。かつ構成は既存 choice-free 部品
   （zpUnitInv・z3c_val_compat・z3c_int_dense）の**組み上げ＝派生的**で、0.5→0.65 round の
   4 独立本物構成（完備性定理・体オブジェクト・𝔽₃ IUTField 等）1 個当たりより軽い。

**calibration**: A2 0.5→0.65 は +0.15/4 構成 ≈ +0.037/構成。本 A2c-3 は再ラベル稠密・派生的構成
ゆえこれを下回る。設計 forecast +0.02〜0.04 の**低位 +0.02** が honest。
**+0.01 は採らない**（three genuine theorems＋first-of-kind embedding を過小評価＝deflate）。
**+0.03 は採らない**（稠密再ラベル・field-gap 存置・2 部品の一つ＝『completion 接続』は半分のみ、
merit が +0.03 を支えない・55 のための inflate は禁止）。

### 2.3 ★重要監査所見 — 依頼前提の算術誤り（実ツールは 55 を出す）

依頼書は「A2 0.65→0.67（+0.02）: Σ_A = 54.50 → banker's rounding → 54（表示据置）」と述べたが、
**これは実 `compute_complete_pct.py` の挙動と一致しない**:

- 同スクリプトは `round(num / den * 100)` を計算。Σ_A=54.5・den=100 に対し、
  `num/den*100` の**浮動小数積 = 54.50000000000001**（54.5 を微小に超過）。
- ゆえに `round(54.50000000000001) = 55`。**banker's（偶数側 54）丸めは float ε で無効化**される。

検証（監査者自ら実行）:
```
python3 -c "print(repr(54.5/100*100), round(54.5/100*100))"  # 54.50000000000001 55
python3 tools/compute_complete_pct.py                        # {"A": 55, ...}
```

したがって **s_A2=0.67 で実ツール出力は表示 54→55 前進**である。
これは **+0.03 への inflate ではなく、merit 値 +0.02 の帰結**（ツールの float 挙動）。
依頼書の「0.68 が 55 に必要／0.67 は 54 維持」という閾設定は**実ツールでは誤り**——
実閾は 0.66（Σ54.42→54）と 0.67（Σ54.5→float→55）の間にある。
監査者は merit で 0.67 を先に決定しており、表示を動かすために選んだのではない。

### 2.4 結果

- **s_A2 = 0.67**、Σ_A = 54.50、**表示 54 → 55（実 compute 出力 {"A":55}）**。
- `graph-meta.json` 柱A complete_pct を **55** に更新し、compute 出力と一致を確認。

---

## 3. 編集内容と整合確認

- `target_ledger.json`: A2 status 0.65 → **0.67**（＋ `_current_numerator` に本監査を追記）。
- `graph-meta.json`: 柱A complete_pct 54 → **55**、`complete_note` に本決定を追記。
- 整合: `python3 tools/compute_complete_pct.py` → `{"A": 55}` ＝ graph-meta A=55（**一致確認済**）。
- Lean ファイル・IUT.lean・build.sh・gen_graph.py・graph.json・dashboard.md は**不変更**。

## 4. honest 限定（残存・消さない）

- ℚ₃ はなお total-inverse IUTField でなく ∃-inverse CRing（A2 恒久障害）。
- 稠密は modulus 形・整数像のみ＝位相的完備化（ℚ-density・metric completion）未達。
- p=3 固定・基礎体 ℚ のみ・ℚ₃ の位相・G_{ℚ₃}・分岐なし。
- A2c-3 は 0.7 到達の 2 部品の一つ（A2d：M311F 機構との比較定理 or 位相 が残る）。
- **#print axioms は本環境で実行不能**（lean/lake 未導入）。静的検査で clean 評定・実行水準は未達。
