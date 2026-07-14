# 独立再監査: `IUT/Q3WildRamFiltrationReal.lean`（prefix q9wr, commit 219f4e3, 484 行）

- 監査者: 独立敵対的監査（本コードの作者ではない・既定 SKEPTICAL）
- 対象柱/項目: **柱B / B1**「実局所体の実付値・実分岐フィルトレーション（実 Galois 群上）」weight=20, current status=0.5
- 申告分類: **[実／(a) 昇格]**、forecast B1 0.5→0.55–0.65
- 本監査はレポート専用（target_ledger.json / graph-meta.json は編集しない — 並行監査が別途統合）

---

## 1. 正当性チェック（実 Lean 証明本体から判定）

### 1.1 Galois 側の実分岐が genuine か — **YES**

- `q3kSigma`（`Q3KummerCubic.lean:504`）は **本物の環自己同型**: σ: a+bY+cY² ↦ a+ζ₃bY+ζ₃²cY²。
  - `q3k_sigma_mul`（環準同型 σ(xy)=σx·σy）・`q3k_sigma3_id`（σ³=id・位数ちょうど 3）が実証明済み。
    toy/surrogate ではない実相対 Galois 生成元。
- 核 **★ `q9wr_sigma_pi_eq`（U3, L219）**: σ(π₉)−π₉ = π₉³·u\* を実証明。
  - π₉ = `q9psPi9` = Y−1（実一様化子）、u\* = `q9wrUStar` = w⁻¹·embed(ζ₃+1)·Y（実閉形式）。
  - 経路: `q9wr_sigma_pi_sub`（座標計算で σπ₉−π₉=embed(−1+ζ₃)·Y）→ `q9ps_pi9_cube`（π₉³=λ·w）
    と `q9ps_coord0`（λ·(ζ₃+1)=−1+ζ₃, 実 explicit 計算・`Q3KummerPiSplit.lean:153` で確認）を消費。
    水増しなく実 σ の作用を座標で計算している。
- σ² 版 **`q9wr_sigma2_pi_eq`（U4, L315）**: σ²(π₉)−π₉ = π₉³·u\*\* も同型に実証明（`q9wr_coord0_sq` 経由）。
- **u\* が genuine な単数か — YES**: `q9wr_ustar_unit`（L151）は w⁻¹（`q9ps_w_unit` の逆）・
  embed(ζ₃+1)（`q9wr_zeta_add_one_unit`: ζ₃+1=−ζ₃²・N が単数）・Y（`q9tl_zeta9_unit`）の
  実単数三積。`q3kUnitMem x := IsZpUnit 3 (q3rqNorm (q3kNormBase x))` で本物のノルム単数性。

### 1.2 break + different が genuine か — **YES（U6 gate が核心で非循環）**

- `q9wr_G2_mem`（U5, L352）: σ,σ²∈G₂（π₉³∣(σᵏπ₉−π₉)）— 1.1 の等式の witness ⟨u\*,…⟩ で即。
- **★ `q9wr_G3_trivial`（U6 break 上界, L386）: ¬ π₉⁴∣(σπ₉−π₉)** を FULL に精読。経路は申告どおり:
  1. 仮定 σπ₉−π₉=π₉⁴·x と ★ σπ₉−π₉=π₉³·u\* を突合 → π₉³·u\*=π₉³·(π₉·x)。
  2. **π₉³ 正則消去** `q9wr_pi3_cancel`（= `q9wr_pi9_cancel` 三段, `q9ci_pi9_reg` を消費）→ u\*=π₉·x。
     `q9ci_pi9_reg`（`Q3KummerCubeIdent.lean:602`）は cofactor 経由の**実正則性**（Y−1 は非零因子）で本物。
  3. ノルム: N(u\*)=N(π₉)·N(x)（`q3k_normBase_mul` 乗法性）、`q9wr_normBase_pi9` で N(π₉)=ζ₃−1。
  4. **`q9wr_qnorm_zeta_sub`: q3rqNorm(ζ₃−1)=3**（(−1−h,h) の a²+3b²=9/4+3/4=3 を explicit 実計算）。
  5. u\* は単数ゆえ q3rqNorm(N(u\*))=3·q3rqNorm(N(x)) が IsZpUnit 3 → `q9wr_three_mul_not_unit`
     （3·s のレベル1値 ≡0 mod 3）で矛盾。
  - **非循環性確認**: 上界は仮定 π₉⁴∣ の否定を、π₉ の実ノルムの 3 進付値（N(π₉)=ζ₃−1, その q3rq
    ノルム=3）から導く本物の数論的議論。Nat 模型の再掲・定義の言い換えではなく、
    **q3kNormBase = a³+ζ₃b³+ζ₃²c³−3ζ₃abc（= x·σx·σ²x の共役積, `Q3KummerCubic.lean:682`）**を
    通じ実 Galois 構造に結びつく。gate は genuine。
- `q9wr_break`（U7, L408）: break t=2（G₀=G₁=G₂=⟨σ⟩・G₃∩{σ,σ²}=∅）を 1.1/U6 で束ね。
- `q9wr_different`（U8, L420）: (σπ₉−π₉)(σ²π₉−π₉)=π₉⁶·(u\*·u\*\*) を実証明（d(M/L₂)=6 生成元）。
- `q9wr_matches_wcd`（U9, L438）: `wcdDiffSum (wcdRamGroups 3 2) 2 = 6` 他を rfl で cross-check。
  Nat 模型（`wcdRamGroups p m i = bif ble i m then p else 1`）との**形状一致**確認であり、
  実側を模型から「証明」してはいない（honest cross-check）。

### 1.3 consume であって re-claim でないか — **YES**

- **3=π₉⁶·u₆ は再主張なし**: 対象ファイル内に `q9ps_three_split` / `three_eq` の呼出しは無い
  （grep 0 件）。`q9psPi6` を `q9wr_different` で使うのみ（π₉⁶ の記号消費）。header の e=6/v_π(3)=6
  も q9ps 成果の参照。**新規内容は Galois 側データ σπ−π** に限定されている。
- **q9ps は Galois 作用を一切持たない**: `Q3KummerPiSplit.lean` 内の automorphism/Galois/Sigma 定義は
  **0 件**（grep 確認）。header 自身も「σ を超える Galois ゼロ」と明記。よって q9wr が σ を主語に
  据えるのは q9ps の重複ではなく genuine な新規 Galois 側データである。

### 1.4 公理 — **CLEAN**

`lake build IUT.Q3WildRamFiltrationReal` → exit 0。scratch `#print axioms`:

```
q9wr_sigma_pi_eq   : [propext, Quot.sound]
q9wr_sigma2_pi_eq  : [propext, Quot.sound]
q9wr_G2_mem        : [propext, Quot.sound]
q9wr_G3_trivial    : [propext, Quot.sound]
q9wr_break         : [propext, Quot.sound]
q9wr_different     : [propext, Quot.sound]
q9wr_matches_wcd   : [propext, Quot.sound]
q9wr_exists        : [propext, Quot.sound]
q9wr_ustar_unit    : [propext, Quot.sound]
```

全て **exactly [propext, Quot.sound]**。`sorryAx` / `Classical.choice` 無し。
禁止タクティク（sorry/admit/native_decide/decide/axiom/unsafe）grep 0 件（header コメント内の
「sorry 皆無」等の記述を除く）。

---

## 2. 二重計上チェック（既存 B 分岐モジュール対）— **NEW と判定**

- 柱B の既存分岐モジュール（`WildConductorDiscriminant` / `MultiJumpWildDiscriminant` /
  `ArbitraryJumpWild` / `HasseArfUnconditional`・`HasseArfAbelian`・`HasseArfFiniteAbelian` /
  `RamifiedNormFiltration` / `ConductorDiscriminant`・`ArtinConductor` 等）に対し
  **`q3kSigma`／実 Galois 自己同型 `Sigma` の使用は 0 件**（grep 空）。
- 既存は `wcdRamGroups`（Nat 階段 `bif ble i m then p else 1`）＝ **Nat 模型 archetype**（AUDIT_RUBRIC が
  「Hasse–Arf 群は List Nat」と模型判定済み）。
- 従って q9wr は **実 Galois 群上の分岐フィルトレーションの初の実現**（実 σ が実 O_M に作用・
  下付き break・different 指数）であり、Nat 階段模型とは主語・内容が別。二重計上ではない。

---

## 3. s_B1 の判定（レポートのみ・ファイル非編集）

`tools/compute_complete_pct.py` は `round(num/den*100)`（Python `round` = **banker's rounding**）。
柱B weights = {B1:20,B2:20,B3:20,B4:15,B5:15,B6:10}=100、現状 {B1:.5,B5:.5, 他0}。

| B1 status | Σ(weight·status) | 表示（B6=0, round） |
|---|---|---|
| 0.5（現状） | 17.5 | 18 |
| 0.55 | 18.5 | **18**（動かず・knife-edge） |
| 0.60 | 19.5 | **20** |
| 0.65 | 20.5 | 20 |

### 判定: **s_B1 = 0.60**（実装、B6=0 なら表示 18→20）

B1 の題名前半「実付値」は現状 0.5（実 ℤ₃ の 1+3ℤ₃/U^(d), Galois 無し）、後半「実 Galois 群上の
分岐フィルトレーション」は **0**。q9wr はこの後半を初めて実にする。

**上方要因（3）**:
1. **Galois 側半分が 0→実**: 本物の環自己同型 σ（位数 3・環準同型を実証明）が実 O_M に作用し、
   σπ₉−π₉=π₉³·u\*（u\* 実閉形式単数）・下付き break t=2・different 指数 d=6 を実実現。
2. **U6 break 上界が実数論**: π₉ 正則消去（実 `q9ci_pi9_reg`）→ N(π₉)=ζ₃−1・q3rqNorm(ζ₃−1)=3
   （explicit 実計算）→ 単数矛盾。定義の言い換えでない delicate・non-circular な gate。
3. **公理 clean・consume 徹底**: 全て [propext, Quot.sound]、q9ps（Galois ゼロ）の重複でない
   genuine 新規 Galois データ、模型との honest cross-check。

**下方要因（3）**:
1. **付値関数 v_M を建てない**: フィルトレーションは π₉ 冪の可除性形式（∃c, y=π₉ⁿc）のみ、
   一様化子 π₉ 限定、任意 x∈O_M の v_π はゼロ。完備化・位相なし。
2. **拡大 1 個（M/L₂）・下付き番号のみ**: 上付き番号・Herbrand ψ/φ・実 Hasse–Arf(B4)・
   実 Artin 導手(B3)は Nat 模型のまま。break は G₃-trivial の**単一 jump**のみ。
3. **付値半分は据え置き**: B1 前半「実付値」は依然 0.5（v_M 未建設）。Galois 半分の実現も
   単塔・単 break と狭い。

**敵対的秤量**: 0.55 は「前半が丸ごと 0 だった Galois 側の初の実実現＋非循環な実 gate」を過小評価。
0.65 は v_M 関数不在・単一拡大・下付きのみで過大。forecast の中心 0.60 が、実 σ・実 gate・clean
公理という本物性と、単塔・可除性形式のみという honest 限定の双方に整合。**表示 knife-edge（0.60 で
18→20）は認識するが、判定は merit ベース**（genuine な初 Galois 側実現＋delicate な U6 証明）。より
保守的な監査者が単一拡大・v_M 不在を重く見て 0.55（表示据え置き 18）とする余地も明記する。

---

## 4. 総括

| 検査項目 | 判定 |
|---|---|
| Galois 側分岐 genuine | YES（実環自己同型 σ・σπ₉−π₉=π₉³·u\*・u\* 実単数） |
| U6 gate 非循環 | YES（π₉ 正則消去→N(π₉)=ζ₃−1・qNorm=3→単数矛盾） |
| consume not re-claim | YES（three_split 呼出 0・q9ps に Galois 定義 0） |
| 公理 clean | YES（全て [propext, Quot.sound]・sorry/choice 無し） |
| 二重計上 | NO（既存 B は Nat 模型・実 σ 使用 0 → q9wr が初の実 Galois 分岐） |

**s_B1 = 0.60**（B6=0 のとき柱B 表示 18→20）。
