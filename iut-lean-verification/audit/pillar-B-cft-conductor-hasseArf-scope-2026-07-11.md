# 柱B 次の一手スコープ: B2（実局所類体論）/ B3（実 Artin 導手・different）/ B4（実 Hasse–Arf）— 実 Gal(M/L₂) 基盤の上の最高レバレッジ判定（2026-07-11）

**種別**: 詳細化ドキュメント（design-only・Lean 実装なし・tier-L 枠の消費）
**対象**: `target_ledger.json` 柱B の status=0 高重み 3 項目 — B2 (w20)・B3 (w20)・B4 (w15)
**前提**: B 表示 21（B1=0.60・B5=0.5・B6=0.15、独立監査確定）。q3kSigma＝実 Gal(M/L₂)（実 O_M の位数 3 環自己同型）が存在し、監査ブロッカー「コード全体に実 Galois 群が存在しない」は既に破壊済み。
**姿勢**: 敵対的・正直。デフォルト判定は「既存 Nat 模型 B 群がそれを既にカバーしている／前進は薄い」。この推定を覆せた項目だけを推奨する。

---

## TL;DR

- **B3（実 Artin 導手／different, w20）が最高レバレッジ**。`Q3WildRamFiltrationReal`（q9wr）が実 different 元恒等式 `(σπ₉−π₉)(σ²π₉−π₉) = π₉⁶·(u*·u**)`（d(M/L₂)=6）と実分岐フィルトレーション（break t=2）を**既に実 O_M 上で持っている**ため、残る新規実定理は (i) σ² 側の break 上界 `¬π₉⁴∣(σ²π₉−π₉)`、(ii) different の鋭さ `¬π₉⁷∣D`、(iii) 実指標群 Hom(Gal(M/L₂),μ₃)（q9kd が完全枚挙済み）ごとの実 Artin 導手 a(χ⁰)=0, a(χ)=a(χ²)=3 と実 conductor–discriminant Σ_χ a(χ)=6=d。どれも q9wr の確立イディオム（π₉ 正則消去→ノルム 2 段→mod-3 矛盾）の新インスタンス＝**tier M（opus）1 本で閉じる**。
- **B4（実 Hasse–Arf, w15）は「可能だが薄い」**。M/L₂ は位数 3・単一 break t=2 で G₀=G₂ ゆえ φ は break まで恒等——上付き break=2 の整数性は数値としてはほぼ自明。実の新規分は「実の可除性形式 G_i を ψ 経由の実上付き述語 G^v に持ち上げ、σ∈G^2・σ∉G^3 を実 O_M 上で証明」する部分のみ。**B3 と独立に並列可**（q9wr+hau のみ消費）だが、監査予測は 0.10–0.15 に留まると正直に見込む。
- **B2（実相互律, w20）は今ラウンド見送り**。正の半分（N=q3kNormBase の乗法性・N(π₉)=ζ₃−1・ノルム群述語）は建つが、crux「ζ₃ ∉ N(M^×)」（=指数ちょうど 3・核=ノルム群）は実 O_M 上の高次単数フィルトレーション（q9wr 正直限定 1 により v_M 不在）を要し、既存イディオムが無い。薄い正半分だけで B2 status を主張するのは閾値ショッピングであり却下。
- **推奨表示動線**: B3（0→0.15–0.25 予測）＋B4（0→0.10–0.15 予測）並列で **B 21→26 前後（幅 24–28）**。status は AUDIT_RUBRIC により独立監査が決める——本書の数値は予測であり自己申告に使わない。

---

## 1. 算術: 何がいくつ表示を動かすか

`tools/compute_complete_pct.py` は厳密分数＋銀行家丸め。分母 Σw(B)=100。現在の分子:

```
Σ_B = 20·0.60 (B1) + 20·0 (B2) + 20·0 (B3) + 15·0 (B4) + 15·0.5 (B5) + 10·0.15 (B6)
    = 12 + 7.5 + 1.5 = 21.0 → 表示 21   ✔（ledger・graph-meta と一致を検算済み）
```

status 上げ 1 段あたりの表示（分数計算・banker's rounding 適用済み）:

| 変更 | 分子増 | Σ_B | 表示 | 備考 |
|---|---|---|---|---|
| B3 0→0.15 | +3.0 | 24.0 | **24** | w20 |
| B3 0→0.20 | +4.0 | 25.0 | **25** | |
| B3 0→0.25 | +5.0 | 26.0 | **26** | |
| B3 0→0.50 | +10.0 | 31.0 | 31 | 監査上（拡大 1 個では非現実的） |
| B4 0→0.10 | +1.5 | 22.5 | **22** | 同点 22.5 は偶数側 22 へ（banker's）|
| B4 0→0.15 | +2.25 | 23.25 | **23** | |
| B4 0→0.20 | +3.0 | 24.0 | 24 | |
| B4 0→0.50 | +7.5 | 28.5 | 28 | 同点→偶数 28（`compute_complete_pct.py` の規約通り） |
| B2 0→0.15 | +3.0 | 24.0 | 24 | w20 だが後述の通り status>0 の見込み薄 |
| **B3 0.15＋B4 0.10** | +4.5 | 25.5 | **26** | 同点→偶数 26 |
| **B3 0.20＋B4 0.10** | +5.5 | 26.5 | **26** | 同点→偶数 26 |
| **B3 0.20＋B4 0.15** | +6.25 | 27.25 | **27** | |
| B3 0.25＋B4 0.15 | +7.25 | 28.25 | 28 | 監査上振れケース |

**結論（算術）**: 1 ラウンドの表示効率は **B3 ≫ B4 > B2**。B3 は w20 かつ基盤（q9wr の d=6・実フィルトレーション）が完成済みで限界コストが最小。B4 は w15 で内容が薄く、単独では +1.5〜2.25。B2 は w20 だが crux 未達なら監査 0 のままで +0。**B3+B4 並列が 1 ラウンドの最善**（中心予測 21→26、幅 24–28）。

なお同点丸めに注意: B4 が単独 0.10 なら 22.5→22 で「1 しか動かない」。B4 は**単独では出さず B3 と同ラウンドに束ねる**のが表示上も正直さの上でも正しい（監査は独立でも、表示更新は統合ラウンド一括）。

---

## 2. 実基盤の棚卸し（def/theorem 本体を読んだ結果）

以下は**本文を読んで確認した**消費可能資産。再主張禁止（消費のみ）。

### 2.1 `IUT/Q3WildRamFiltrationReal.lean`（q9wr, B1=0.60 の実体）

- `q9wr_sigma_pi_eq` (U3★): `σ(π₉)−π₉ = π₉³·u*`、`q9wr_sigma2_pi_eq` (U4): `σ²(π₉)−π₉ = π₉³·u**`。u*, u** は**閉形式実単数**（`q9wrUStar = w⁻¹·embed(ζ₃+1)·Y` 等、`q9wr_ustar_unit`/`q9wr_ustarstar_unit`）。
- `q9wrDvd d x := ∃c, x = d·c` — 付値関数を建てない**可除性形式**（B1 正直限定 1）。
- `q9wr_G2_mem`: σ,σ²∈G₂（π₉³∣）。`q9wr_G3_trivial` (U6★): `¬π₉⁴∣(σπ₉−π₉)`——**σ 側のみ**。σ² 側の上界は**存在しない**（ヘッダの「G₃∩{σ,σ²}=∅」は capstone には σ 側しか束ねられていない。q9ac が埋めるべき実ギャップ）。
- `q9wr_different` (U8): `(σπ₉−π₉)(σ²π₉−π₉) = π₉⁶·(u*·u**)` — 実 different 生成元、d(M/L₂)=6。ただし**鋭さ `¬π₉⁷∣D` は未証明**（u*·u** の単数性から従うが定理化されていない）。
- `q9wr_matches_wcd` (U9): Nat 模型 `wcdRamGroups 3 2` との cross-check（`wcdDiffSum … = 6`）。
- 補助イディオム: `q9wr_pi9_cancel`/`q9wr_pi3_cancel`（π₉ 正則消去、`q9ci_pi9_reg` 消費）、`q9wr_three_mul_not_unit`（3·s 非単数）、`q9wr_normBase_pi9`（N(π₉)=ζ₃−1）、`q9wr_qnorm_zeta_sub`（q3rqNorm(ζ₃−1)=3）。U6 の証明構造＝**π₉ 正則消去→ノルム 2 段→mod-3 矛盾**は q9ac/q9ha が丸ごと再利用できる確立イディオム。
- **正直限定 3 が本スコープの根拠**: 「上付き番号・Herbrand φ/ψ の実版・実 Hasse–Arf（B4）・Artin 導手の実表現論（B3）はゼロ——wcd/ajw/hau の Nat 模型が引き続きそれを担う」。つまり **q9wr 自身が B3/B4 の実版の不在を申告しており、二重計上の初期リスクはゼロ**（埋めるべき穴が定義済み）。

### 2.2 `IUT/Q3KummerDualityReal.lean`（q9kd, B6=0.15 の実体）

- `q9kdG : Grp` — 実 Gal(M/L₂)=⟨σ⟩ の 3 元群、`q9kdAct` — 実環自己同型作用（e↦id, s↦q3kSigma, s2↦q3kSigma2、`q9kd_act_mul` で準同型性）。
- `q9kdMu3 : Grp` — μ₃(O_M)={x:x³=1} 実群。`q9kdChi`/`q9kdChi0`/`q9kdChi2` — 実指標 3 本。
- **`q9kd_hom_complete` (T9b): Hom(⟨σ⟩,μ₃) = {χ⁰,χ¹,χ²} の完全枚挙**（`q9c_m_mu3_complete` 消費）——B3 の「Σ_χ を全指標にわたって取る」を**本物**にする鍵。
- `q9kd_chi_faithful` (T5)・`q9kd_z_ne_one`/`q9kd_zsq_ne_one` — χ,χ² が σ 上非自明であることの実証明——B3 の codim(V^{G_i})=1 の実根拠。
- `q9kd_pairing_nondeg_left/right`・`q9kd_class_nontrivial`（`q9ci_no_cbrt_zeta` 消費、群提示 `q3rqLx = ℤ×U₂` 上）——B2 の Kummer 側素材。

### 2.3 `IUT/Q3KummerPiSplit.lean`（q9ps）・`IUT/Q3KummerCubic.lean`（q3k）・`IUT/Q3RamifiedQuadratic.lean`（q3rq）

- `q9psPi9 = Y−1`・`q9ps_pi9_cube`（(Y−1)³=λ·w）・`q9ps_three_split`（3=π₉⁶·u₆）・`q9psPi6`。
- `q3kNormBase x`（3 次ノルム）＋ `q3k_normBase_mul`（乗法性・L856）＋ `x·σx·σ²x = embed(N x)`（L811）——**実ノルム N_{M/L₂} は既に群準同型として使える**（B2 の正半分の素材）。
- `q3kSigma` は環自己同型（`q3k_sigma_mul` L518、加法性は q9kd）。`q3rqNorm`/`q3rqUnitMem`/`q3rqU`/`q3rqLx`（L₂^× の群提示 ℤ×U₂）。

---

## 3. B3（実 Artin 導手／different, w20, status 0）— **推奨・最高レバレッジ**

### 3.1 数学的内容（この拡大での本物）

M/L₂ は全分岐・巡回 ℤ/3・下付き break t=2（q9wr 実証済み）。ゆえに:

- **分岐群**: G₀=G₁=G₂=⟨σ⟩、G_i=1 (i≥3)。
- **実指標の Artin 導手**: 非自明 1 次元指標 χ, χ²（q9kd の実物）は G_i (i≤2) 上非自明（χ faithful）→ codim(V^{G_i})=1 (i=0,1,2), 0 (i≥3)、[G₀:G_i]=1 → **a(χ)=a(χ²)=3**（=tame 1 + Swan 2、Swan=break t=2）。自明指標 a(χ⁰)=0。
- **conductor–discriminant（実両面）**: Σ_{φ∈Hom(Gal,μ₃)} a(φ) = 0+3+3 = **6 = d(M/L₂)**。右辺は q9wr_different の実環恒等式 `D=(σπ₉−π₉)(σ²π₉−π₉)=π₉⁶·(u*u**)` で実現され、**鋭さ**（¬π₉⁷∣D）まで込みで「d=6 ちょうど」。

### 3.2 モジュール設計: `IUT/Q3ArtinConductorReal.lean`（prefix `q9ac`）

分類ヘッダ: **[実／(a) 昇格]** — wcd/mjw/ajw/arc の Nat 階段 Artin 導手・conductor–discriminant を、実 Gal(M/L₂) の実指標（q9kd）×実分岐フィルトレーション（q9wr）の上の実 conductor–discriminant で置換。complete_pct 影響: **B3 0→（監査次第・予測 0.15–0.25）— display-moving**。

| # | 定理（案） | 内容 | 消費 | 新規性 |
|---|---|---|---|---|
| A1 | `q9ac_dvd_of_le` / `q9ac_not_dvd_of_ge` | π₉ 冪可除性の下降/上昇（a≤b: π₉^b∣x→π₉^a∣x、¬π₉⁴∣x→¬π₉^k∣x (k≥4)） | q3k 環演算 | 小補題（両モジュール共通イディオム） |
| A2 | `q9ac_sigma2_G3_trivial` ★ | **¬π₉⁴∣(σ²π₉−π₉)**（σ² 側 break 上界——q9wr の欠落） | `q9wr_sigma2_pi_eq`・`q9wr_pi3_cancel`・`q9wr_ustarstar_unit`・`q9wr_normBase_pi9`・`q9wr_qnorm_zeta_sub`・`q9wr_three_mul_not_unit` | **新規実定理**（U6 イディオムの σ² 新インスタンス） |
| A3 | `q9acGiMem g i` (Prop) ＋ `q9ac_gi_le`/`q9ac_gi_gt` | 実 G_i 帰属述語（q9wrDvd π₉^{i+1} (act g π₉ − π₉)、g∈{s,s2}）: i≤2 で成立・i≥3 で不成立（σ・σ² 両方） | `q9wr_G2_mem`・`q9wr_G3_trivial`・A1・A2 | 実（フィルトレーション全帰属の完成） |
| A4 | `q9acCodim φ i : Nat` ＋ `q9ac_codim_spec` | codim(V^{G_i})∈{0,1} を **iff-spec で実 Prop に緊縛**: `q9acCodim φ i = 1 ↔ (φ.map s ≠ q9kdMu3One ∧ q9acGiMem .s i)` | `q9kd_z_ne_one`/`q9kd_zsq_ne_one`/`q9kd_chi_faithful` | 実（Nat 値の全てが実定理で強制される） |
| A5 | `q9acArtin φ := Σ_{i=0}^{2} q9acCodim φ i` ＋ `q9ac_artin_chi`/`_chi2`/`_chi0` | a(χ)=a(χ²)=3、a(χ⁰)=0 | A3・A4 | 実（実表現＝実指標の導手） |
| A6 | `q9ac_swan_eq_break` | Swan(χ)=a(χ)−1=2=実 break t（q9wr break との同定） | A5・`q9wr_break` | 実 |
| A7 | `q9ac_different_sharp` ★ | **¬π₉⁷∣D**（D=π₉⁶·(u*u**) の鋭さ。π₉⁶ 消去→u*u**=π₉·x→ノルム→3·s 非単数矛盾） | `q9wr_different`・`q9wr_pi3_cancel`×2・ノルム鎖 | **新規実定理**（d=6「ちょうど」の実証） |
| A8 | `q9ac_conductor_discriminant_real` ★ | **Σ_{φ} a(φ) = 6 ∧ D = π₉⁶·(u*u**) ∧ ¬π₉⁷∣D**、和は `q9kd_hom_complete` により**全指標**を尽くす | A5・A7・`q9kd_hom_complete`・`q9wr_different` | **本命題**（実 Führerdiskriminanten 公式・両辺実） |
| A9 | `q9ac_matches_wcd` | Nat 模型 cross-check: Σ=6=`wcdConductorTotal 3 2`、a(χ)=3=`wcdArtinExpWild 2` | wcd（q9wr 経由 import 済み） | cross-check（新規証明ゼロと明記） |
| A10 | `Q3ArtinConductorRealData`/`q9ac_data`/`q9ac_exists` | capstone（束ねのみ） | — | — |

正直な限定（ヘッダに必須）: 拡大 1 個（M/L₂）・1 次元指標 3 本のみ・付値関数 v_M なし（可除性形式、q9wr 限定 1 継承）・Artin 導手の一般公式 a(χ)=Σ(1/[G₀:G_i])dim(V/V^{G_i}) は**この拡大でのインスタンス化**であり一般定理ではない・合成 different（推移公式・d(M/ℚ₃)）は範囲外。

### 3.3 二重計上判定（敵対的）

デフォルト仮説「wcd/mjw/ajw/arc が既にカバー」を検証した:

- **wcd（M441F）**: 主語は `wcdRamGroups p m : Nat→Nat`・`wcdCodim`・`wcdArtinSum` の **Nat 階段関数**（`bif wcdBle` で定義）。p,m は任意パラメタで、実の体・環・Galois 作用は一切登場しない。AUDIT_RUBRIC・graph-meta 監査注記も「Artin導手はBool→Nat」と模型判定済み。q9ac の主語は実 `Hom q9kdG q9kdMu3` と実 O_M 内の可除性述語であり、**同じ数 6 を出すが同じ定理ではない**。
- **mjw/ajw**: 多跳躍/任意跳躍の Nat 階段一般化。M/L₂ は単一跳躍なので接点は wcd 経由の cross-check のみ。
- **arc（M430F）**: tame・f∈{0,1} の Nat 模型。q9ac は wild（a=3, Swan=2）でそもそも別命題。
- **q9wr 自身との二重計上（最大リスク）**: q9wr は既に (i) d=6 の実恒等式、(ii) `wcdRamGroups 3 2` cross-check（Σ(|G_i|−1)=6）を持つ。**q9ac が「6=6」を言い換えるだけなら水増し**。これを回避する q9ac の真水は 3 点に限定して主張する: **A2（σ² 側上界——q9wr に無い）・A7（different の鋭さ——q9wr に無い）・A4/A5/A8（指標側: q9kd の実指標×実 G_i から導手を導出し、`q9kd_hom_complete` で和の全数性を担保——q9wr にも q9kd にも無い接合）**。d=6・G₂ 帰属・cross-check の数値自体は「消費」と明記し再主張しない。
- **判定**: 上記 3 点を守る限り**リラベルではない（クリア）**。逆に、q9ac が独自の Nat 階段（`bif` 定義の codim 関数）を spec 定理なしに立てたら監査は模型判定すべき——実装指示に A4 の iff-spec を必須条項として入れる。

### 3.4 見込みとコスト

- tier **M（opus）**、**約 450–550 行**、依存 `Q3WildRamFiltrationReal`＋`Q3KummerDualityReal`（wcd は推移 import）。A2/A7 は U6 の写経＋座標差し替え（u** のノルムは (ζ₃+1)² 単数で同構造）。sorry/選択公理なし・#print axioms=[propext,Quot.sound] を要求。
- 監査予測: **0→0.15–0.25**（B6 が「完全双対でも拡大 1 個・n=3」で 0.15 だった前例に整合。B3 は両辺実＋鋭さ＋全指標和で 0.20 中心、拡大 1 個・v_M 不在が上限を抑える）。表示 +3〜+5。

---

## 4. B4（実 Hasse–Arf, w15, status 0）— 可能だが薄い・B3 と並列なら価値あり

### 4.1 内容と敵対的評価

M/L₂ の Herbrand: [G₀:G_t]=1 (0≤t≤2) ゆえ φ(u)=u (u≤2)、u>2 で傾き 1/3。**上付き break = φ(2) = 2 = 下付き break**。Hasse–Arf 整数性はこの拡大では「2 は整数」——**数値内容はほぼ自明**であることを最初に認める。graph-meta 監査注記も「上付き番号は Nat 模型据置」と、q9wr が残した穴として明示している。では実の真水は何か:

1. **実上付き述語**: `q9haUpperMem g v := q9acGiMem g (ψ(v))` を実可除性で定義し、**σ∈G^2（実: π₉³∣σπ₉−π₉）・σ∉G^3（実: ¬π₉⁶∣…、これは ¬π₉⁴∣ から可除性下降で従う）**を実 O_M 上で証明——上付き番号の実現は codebase 初。
2. **実階段の hau への同定**: M/L₂ は hau の符号化で `p=3, us=[2]`（単一段・上付き増分 2）。`hauLowerFrom 3 1 [2] = 2`（実下付き break と一致）・`hauUpperFrom 3 1 [2] = hauUpperBreak [2] = 2`（整数 landing、`hau_upper_break_integer` 消費）。**実データが Nat 模型 hau の一具体点を実現する**ことの spec 定理（q9wr U9 の hau 版）。
3. **order-spec**: `q9haOrder : Nat→Nat`（3,3,3,1,…）を立てるなら、各値を実 Prop に iff-spec で緊縛（`q9haOrder i = 3 ↔ (q9acGiMem .s i ∧ q9acGiMem .s2 i)` 形）——素の Nat 階段の再生産を禁止。

### 4.2 モジュール設計: `IUT/Q3HasseArfReal.lean`（prefix `q9ha`）

分類: **[実／(a) 昇格]**（hau/haa/hfa の List-Nat Hasse–Arf の「実 Galois 側主語」を M/L₂ 一拡大で実現）。主定理: `q9ha_upper_G2_real`（σ∈G^2 実）・`q9ha_upper_G3_trivial_real`（σ∉G^3 実）・`q9ha_break_transform`（実下付き break 2 → ψ/φ → 上付き break 2・`rnf_phi_psi`/`hau_upper_break_integer` 消費）・`q9ha_hasse_arf_instance`（この拡大の上付き jump が整数 2、`hauDataOf 3 _ [2]` との同定）・capstone。正直な限定: 拡大 1 個・単一 break・v は Nat のみ（有理数上付き番号なし）・G₀=G₂ ゆえ φ が break まで恒等で整数性の数値内容は退化的、が主張の中心は上付き述語の実現である旨を明記。

- **並列性**: 依存は `Q3WildRamFiltrationReal`＋`HasseArfUnconditional` のみで **B3 モジュールと独立＝並列可**。σ 側だけで完結する（σ² の G^v 帰属を含めたければ A2 が要るが、その場合は q9ha は B3 の後段に直列化するか、σ 生成元主語の言明に絞る——**σ 主語に絞って並列を推奨**。A1 相当の可除性下降補題は各自 5 行、重複許容）。
- tier **M（opus）**、**約 300–400 行**。
- **二重計上判定**: hau/haa/hfa は任意 List Nat 上の整数性（実 Galois ゼロ）。q9ha は「実拡大が us=[2] を実現し、その上付き帰属を実可除性で言う」——hau の再証明を一切せず消費に徹する限りクリア。**最大リスクは「φ=id なので変換が空虚」批判**であり、これは正直限定に明記した上で、真水を上付き述語の実現（4.1-1）に置くことで応える。監査予測: **0→0.10–0.15**（0.10 なら単独表示 +1.5 で丸め損もあり得る——B3 と同ラウンド束ねが必須）。

---

## 5. B2（実局所類体論・相互律, w20, status 0）— 今ラウンド見送り（正直評価）

- **既存資産の判定**: `LocalReciprocity`（locRec, 分裂表示 ℤ×O^× 上の Artin 写像）・`NormGroup`（normG, 不分岐次数 d の模型で核=ノルム群）・`LubinTateReciprocity`/`LubinTateNormGroup`（p=2 捻れレベル・不分岐 d）・`HilbertSymbol*`/`TameSymbol`/`LocalBrauer`/`BrauerInvariant*`/`ReciprocityBrauerCompat` はいずれも**分裂表示模型または不分岐限定**で、実 Gal(L/K) 主語の分岐 LCFT は各ヘッダが自ら「後続」と申告している。実 Gal(M/L₂) は分岐（全分岐 wild）拡大なので、既存 B2 群と主語が重なる余地はほぼ無い＝二重計上リスクは低いが、**その分ゼロから重い**。
- **実基盤で今建つもの（正半分）**: N=q3kNormBase は乗法的（`q3k_normBase_mul`）・N(π₉)=ζ₃−1（`q9wr_normBase_pi9`）・N(unit)=unit。ゆえに「ノルム群述語 N(M^×)⊆L₂^× と、その元の付値が全付値を尽くす（ζ₃−1 が L₂ の一様化子）」までは書ける。
- **crux（欠けているもの）**: 相互律の実体は **[L₂^× : N(M^×)] = 3、同値に ζ₃ ∉ N(M^×)**（q9kd の χ と合成して rec: L₂^×/N ≅ Gal(M/L₂)）。これは「N(x)=ζ₃ なる x∈O_M が存在しない」という**非存在命題**で、q9ci_no_cbrt_zeta（O_{L₂} 内の非 3 乗）からは従わない。標準証明は U^{(i)} 高次単数フィルトレーション上のノルムの像解析（本物の ramified norm 計算）を要するが、q9wr 正直限定 1 の通り **v_M も U_M^{(i)} も実 O_M 上に存在しない**。可除性形式で建てるのは新イディオム発明＝tier L 案件。
- **判定**: 正半分だけのモジュールで B2 status を動かそうとするのは §2/§3 違反すれすれの水増し（監査は crux 不在で 0 を維持する見込み）。**B2 は次々ラウンドに tier-L 詳細化（「実 O_M の可除性形式高次単数フィルトレーションとノルム像」）を 1 枠立ててから着手**する。B3 の A2/A7 が鍛えるノルム 2 段イディオムはその直接の足場になる。

---

## 6. 実装計画（次ラウンド推奨・5 並列の B 枠分）

| 枠 | モジュール | prefix | 項目 | tier/model | 行数目安 | 依存（import） | 監査予測 status | 表示寄与 |
|---|---|---|---|---|---|---|---|---|
| 1 | `IUT/Q3ArtinConductorReal.lean` | `q9ac` | **B3** | **M / opus** | 450–550 | Q3WildRamFiltrationReal, Q3KummerDualityReal | 0→**0.15–0.25** | +3〜+5 |
| 2 | `IUT/Q3HasseArfReal.lean` | `q9ha` | **B4** | **M / opus** | 300–400 | Q3WildRamFiltrationReal, HasseArfUnconditional | 0→**0.10–0.15** | +1.5〜+2.25 |
| — | B2 詳細化（後続ラウンド） | — | B2 | L / fable（設計のみ） | doc | — | 0 のまま | 0 |

- **並列**: 枠 1・2 は独立ファイル・独立 import で同時起動可（q9ha は σ 主語に限定し A2 を待たない）。σ² 側の G^v 帰属を q9ha に足すのは統合後の小追補で可。
- 統合時（親作業）: `IUT.lean` へ 2 import 追加、`tools/gen_graph.py` PILLAR に `"Q3ArtinConductorReal": "B", "Q3HasseArfReal": "B"`、`gen_graph.py` 再実行、独立監査 2 本→ `target_ledger.json` status→ `graph-meta.json`/`dashboard.md` 二軸更新。
- **却下事項（閾値ショッピング禁止の明示）**: (i) B4 単独ラウンド（22.5→22 の丸め損・内容も薄い）、(ii) B2 の正半分のみモジュール（crux 不在で status 0 のまま）、(iii) q9ac/q9ha 内での素の Nat 階段新設（spec 定理なしの `bif` codim/order は wcd リラベル＝監査で模型判定されるべき）、(iv) capstone 束ねだけの枠埋め。
- **表示予測**: 中心 **B 21→26**（B3=0.20＋B4=0.10 で 26.5→26、または 0.15＋0.15 で 26.25→26）。幅 24（B3=0.15 のみ通過）〜28（両方上振れ）。status は独立監査が決め、`.complete_pct_baseline.json` 更新はユーザー人手署名——本書の数値を自己申告に流用しない。

---

## 7. 三行結論

(a) 動かすのは **B3（0→0.15–0.25 予測）と B4（0→0.10–0.15 予測）**で、B2 は crux「ζ₃∉N(M^×)」が実 O_M 上の未発明イディオムを要するため今回見送り——表示予測は **B 21→26（幅 24–28）**。
(b) `Q3ArtinConductorReal`（q9ac, opus, 450–550 行）と `Q3HasseArfReal`（q9ha, opus, 300–400 行）はどちらも q9wr の確立イディオム（π₉ 正則消去→ノルム 2 段→mod-3 矛盾）と q9kd の完全指標枚挙の消費で 1 ラウンド完結が現実的であり、**σ 主語に絞れば相互依存なく並列起動できる**。
(c) 最大の二重計上リスクは「q9wr が既に持つ d=6・wcd cross-check の言い換え」だが、q9ac の真水を **σ² 側 break 上界・different 鋭さ ¬π₉⁷∣D・実指標×実 G_i からの導手導出（q9kd_hom_complete による全数和）** の 3 点に限定し、全 Nat 値を実 Prop への iff-spec で緊縛する設計条項によって**クリアと判定**する（この条項が守られない実装は監査で模型に落とすべき）。

---

## 読了した .lean 本体（本書の根拠・全て def/theorem 本文まで確認）

- `/home/user/onepagers/iut-lean-verification/IUT/Q3WildRamFiltrationReal.lean`（全 485 行）
- `/home/user/onepagers/iut-lean-verification/IUT/Q3KummerDualityReal.lean`（全 593 行）
- `/home/user/onepagers/iut-lean-verification/IUT/Q3KummerPiSplit.lean`（全 527 行）
- `/home/user/onepagers/iut-lean-verification/IUT/Q3KummerCubic.lean`（q3kSigma/q3k_sigma_mul/q3kNormBase/q3k_normBase_mul/q3kUnitMem/q3kInv 周辺）
- `/home/user/onepagers/iut-lean-verification/IUT/Q3RamifiedQuadratic.lean`（q3rqNorm/q3rq_norm_mul/q3rqUnitMem/q3rqU/q3rqLx）
- `/home/user/onepagers/iut-lean-verification/IUT/WildConductorDiscriminant.lean`（全 516 行）
- `/home/user/onepagers/iut-lean-verification/IUT/HasseArfUnconditional.lean`（全 372 行）
- `/home/user/onepagers/iut-lean-verification/IUT/HasseArfAbelian.lean`・`HasseArfFiniteAbelian.lean`・`MultiJumpWildDiscriminant.lean`・`ArbitraryJumpWild.lean`（ヘッダ＋主定理宣言）
- `/home/user/onepagers/iut-lean-verification/IUT/RamifiedNormFiltration.lean`（rnfPhi/rnfPsi/rnf_phi_psi 本体）・`ArtinConductor.lean`・`DifferentFromFiltration.lean`（ヘッダ＋主定理）
- `/home/user/onepagers/iut-lean-verification/IUT/LocalReciprocity.lean`・`NormGroup.lean`・`LubinTateReciprocity.lean`・`LubinTateNormGroup.lean`（ヘッダ＋主定理・正直限定）
- 台帳/道具: `target_ledger.json`（柱B 全項目）・`tools/compute_complete_pct.py`（全文）・`tools/gen_graph.py`（PILLAR 辞書）・`graph-meta.json`（柱B 監査注記）・`AUDIT_RUBRIC.md`（模型判定基準）・`CLAUDE.md` §1–§5
