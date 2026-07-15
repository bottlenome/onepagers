# 独立敵対監査: `IUT/Q3ArtinConductorReal.lean`（q9ac・柱B B3）2026-07-11

**対象**: `IUT/Q3ArtinConductorReal.lean`（prefix `q9ac`・368 行・commit 4a4a26a）
**申告**: 分類 **[実／(a) 昇格]**・B3（weight=20・現 status=0）・予測 0→0.15–0.25
**監査官の姿勢**: 独立・敵対的・デフォルト懐疑。実 .lean 証明本体からのみ判定。当該コードは監査官が書いていない。
**環境**: `/root/lean4/bin` に lean/lake（v4.30.0）在。`lake build IUT.Q3ArtinConductorReal` = **EXIT 0**（153 jobs, no sorry）。`#print axioms` 実行済（下記）。

---

## 結論（先出し）

| 検査項目 | 判定 |
|---|---|
| 3 真水（A2 σ² 側 break 上界・A7 different 鋭さ・A4/A5/A8 指標導手）は本物・非空虚か | **YES（3/3）** |
| iff-spec `q9ac_codim_spec` は実 Prop 緊縛（Nat 階段模型でない）か | **YES** |
| 消費-非再主張（d=6・G₂・σ側・wcd を消費し再証明しない）か | **YES** |
| 軸 `#print axioms` = [propext, Quot.sound] 以下か | **YES** |
| Nat 模型 B 群（wcd 等）との二重計上か | **NO（主語が別・別定理）** |

**s_B3 決定 = 0.20**（表示: Σ_B=21→25・柱B 表示 21→25）。予測帯 0.15–0.25 の中央。

---

## Part 1: 正確性検査

### 1.1 真水 A2 `q9ac_sigma2_G3_trivial`（¬π₉⁴∣(σ²π₉−π₉)）

証明本体（:98–115）を精読。intro hd → obtain ⟨x,hx⟩ →
- `hcomb`: `q9wr_sigma2_pi_eq.symm.trans hx` ＋ `q3k_mul_assoc` で π₉³·u** = π₉³·(π₉·x) を構成。
- `hux`: `q9wr_pi3_cancel hcomb` で u** = π₉·x（π₉³ 正則消去）。
- `hnorm`: `q3k_normBase_mul` → `q9wr_normBase_pi9`（N(π₉)=ζ₃−1）。
- `huu`: `q9wr_ustarstar_unit`（u** 実単数）を norm 経由で受け、`q3rq_norm_mul`＋`q9wr_qnorm_zeta_sub`（q3rqNorm(ζ₃−1)=3）で 3·N(x) が単数化。
- 矛盾: `q9wr_three_mul_not_unit`（3·s は非単数）。

**判定**: q9wr は σ 側 `q9wr_G3_trivial`（:386–403、`q9wr_sigma_pi_eq`/`q9wrUStar`/`q9wr_ustar_unit` を使用）**しか持たない**。A2 は同一 U6 イディオム（π₉ 正則消去→ノルム 2 段→mod-3 矛盾）を **σ² の対象**（`q9wr_sigma2_pi_eq`/`q9wrUStarStar`/`q9wr_ustarstar_unit`）へ忠実に新インスタンス化した**新規実定理**。可除性否定を実際に証明しており空虚でない。**GENUINE。**（正直に言えば、A2 は σ 側証明の機械的 σ²-clone であり新イディオムではない——下げ要因で計上。）

### 1.2 真水 A7 `q9ac_different_sharp`（¬π₉⁷∣D, D=π₉⁶·(u*·u**)）

証明本体（:279–298）＋補助 `q9ac_pi6_cancel`（:264–274、`q9wr_pi3_cancel` を 2 段合成した新規消去補題）を精読。
- `hcomb`: `q9wr_different.symm.trans hc`（**D の恒等式を消費**）＋ assoc。
- `hux`: `q9ac_pi6_cancel` で u*·u** = π₉·c。
- norm 鎖 → `hunit`: `q3k_unit_mul q9wr_ustar_unit q9wr_ustarstar_unit`（u*·u** 実単数）→ 3·N(c) 単数化 → `q9wr_three_mul_not_unit` で矛盾。

**判定**: scope 文書・q9wr ヘッダとも「鋭さ ¬π₉⁷∣D は q9wr に無い（未定理化）」を確認。A7 は D=π₉⁶·(u*u**) を**消費**し、d(M/L₂)=6「ちょうど」を実証する**新規実定理**。非空虚。**GENUINE。**

### 1.3 真水 A4/A5/A8 指標導手

**A4 `q9ac_codim_spec`（:203–229）= iff-spec（anti-model 条件）**:
`q9acCodim g i = 1 ↔ ((q9kdChiPow g).map q9kdGCar.s ≠ q9kdMu3One ∧ q9acGiMem q9kdGCar.s i)`。
- `q9acCodim`（:185–188）は Nat 階段（e↦0, s/s2↦q9acLe2 i）——**素の Nat 値は模型的**。しかし iff-spec が全ての「1」を実 Prop に緊縛する:
  - 左緊縛子 `(q9kdChiPow g).map s ≠ q9kdMu3One` は**実 Kummer 指標**を実 σ で評価した μ₃(O_M) 内の非自明性。g=s は `q9ac_chi_s_ne`→`q9kd_z_ne_one`（実: embed ζ₃≠1）、g=s2 は `q9kd_zsq_ne_one`。
  - 右緊縛子 `q9acGiMem s i` は**実可除性**述語で、証明は `q9ac_giMem_s_le`（`q9wr_sigma_pi_eq` 消費）/`q9ac_giMem_s_gt`（`q9wr_G3_trivial` 消費）を使う。
- 全 3 分岐（e/s/s2）で iff の両方向を実際に証明済（監査官が場合分けを追跡）。

**判定**: Nat 値が実指標非自明性・実 G_i 帰属で**強制されており、素の Nat 階段でない**。scope 文書が必須条項とした anti-model 緊縛を満たす。**iff-spec は本物。**
（下げ要因: codim∈{0,1} は実表現空間 V・実固定部分空間 V^{G_i} から計算されておらず、Prop に緊縛した手置き値。実 dim/codim 計算は不在＝正直限定 3 と整合。）

**A5**（:238–244）: a(χ)=a(χ²)=3, a(χ⁰)=0 は `q9acArtin g = codim g 0+1+2` の rfl。内容は A4 の spec＋A2/A3 に在り、A5 自体は定義的総和。

**A8 `q9ac_conductor_discriminant_real`（:306–315）= 本命題**: 4 連言:
1. `q9acArtin e+s+s2 = 6`（0+3+3）rfl。
2. `∀ φ:Hom q9kdG q9kdMu3, φ=χ⁰∨χ∨χ²` = **`q9kd_hom_complete`**（実指標の完全枚挙）。ゆえに Σ は**全指標**にわたる（手選びでない）。**完全枚挙を genuinely 消費。**
3. D=(σπ₉−π₉)(σ²π₉−π₉)=π₉⁶·(u*u**) = `q9wr_different`（消費）。
4. ¬π₉⁷∣D = A7。

**判定**: 左辺（実指標和・全数）と右辺（実 different・鋭さ込み）がともに実で 6 に一致する実 Führerdiskriminanten。**GENUINE。**
（下げ要因: **v_M 不在**——A8 の連言 1 と 3/4 は「両辺が literal Nat 6」で接合されており、`v_M(𝔡)=Σ_χ a(χ)` の付値等式ではない。正直限定 2「付値関数 v_M なし・可除性形式」と整合。忠実な部分ケースであって一般 conductor-discriminant でない。）

### 1.4 軸（`#print axioms`）

`lake env lean` で列挙:
```
q9ac_sigma2_G3_trivial          : [propext, Quot.sound]
q9ac_different_sharp            : [propext, Quot.sound]
q9ac_conductor_discriminant_real: [propext, Quot.sound]
q9ac_codim_spec                 : [propext, Quot.sound]
q9ac_artin_chi                  : （公理依存なし・rfl）
q9ac_exists                     : [propext, Quot.sound]
q9ac_matches_wcd                : （公理依存なし・rfl）
```
全て [propext, Quot.sound] 以下・**新規 Classical.choice 皆無。CLEAN。**

**禁止タクティク**: grep で sorry/simp/decide/by_cases/rcases/ring/nlinarith/native_decide = **0**（"sorry" ヒットは日本語コメント「sorry 皆無」のみ）。omega は 13 箇所だが全て純 Nat/Int 算術（π₉ 冪指数・i≤2 判定）で許容。

---

## Part 2: 消費-非再主張 & 二重計上検査

### 2.1 消費-非再主張（二重計上回避の要）

| 消費対象 | 消費箇所 | 再証明していないか |
|---|---|---|
| d=6 恒等式 `q9wr_different` | A7 hcomb・A8 連言 3（literal =） | **YES**（再証明ゼロ） |
| G₂ 帰属 `q9wr_G2_mem`/`q9wr_break` | A6 `q9ac_swan_eq_break`（`q9wr_break.1`）・A3 giMem_le | **YES** |
| σ 側 break 上界 `q9wr_G3_trivial` | A3 `q9ac_giMem_s_gt`（exact）・A6（`q9wr_break.2.2`） | **YES**（σ² 側=A2 が新規） |
| wcd Nat 数 | A9 `q9ac_matches_wcd`（rfl・「新規証明ゼロ」明記） | **YES** |

真水は**厳密に A2/A7/A4-A5-A8** に限定され、消費した数値（d=6・G₂・wcd cross-check）を新規主張として再計上していない。**規律クリア。**

### 2.2 Nat 模型 B 群との二重計上

`WildConductorDiscriminant.lean`（wcd/M441F）を精読: 主語は `wcdRamGroups p m : Nat→Nat`（`bif wcdBle` の Bool→Nat 階段）・`wcdCodim`・`wcdArtinSum`——**実の体・環・Galois 作用は皆無**。p,m は任意パラメタ。AUDIT_RUBRIC も「Artin 導手は Bool→Nat」と模型判定済。

q9ac の主語は**実 `Hom q9kdG q9kdMu3`（実指標）＋実 O_M 内可除性 `q9wrDvd`（q3kCar 上）**。**同じ数 6 を出すが同じ定理でない。** A9 cross-check は明示的に「新規証明ゼロ」でありwcd を消費するのみ。**二重計上なし。**

---

## Part 3: s_B3 決定（敵対的・merit）

`compute_complete_pct.py`（Fraction＋round）で検算: den(B)=100, 現 Σ_B=21（B1 12＋B5 7.5＋B6 1.5）→表示 21。
- B3=0.15 → Σ_B=24 → 表示 **24**
- B3=0.20 → Σ_B=25 → 表示 **25**
- B3=0.25 → Σ_B=26 → 表示 **26**
（全て整数・丸め曖昧性なし。）

### 上げ要因
1. **コードベース初の、実 Galois 群上の実 Artin 導手／conductor-discriminant**。柱B の自監査が B2–B6 を「コード全体に実 Galois 群なし」で 0 にブロックしていた——q3kSigma がそれを破壊し、q9ac がその上に実 Artin 導手を初 landing。質的な「初」。
2. 3 真水すべて genuine・非空虚（σ² 上界の実否定証明・鋭さ ¬π₉⁷∣D・全指標群にわたる Σ_χ a(χ)=6）。
3. iff-spec `q9ac_codim_spec` が Nat codim を実 Prop（実指標非自明性 ∧ 実 G_i 帰属）に緊縛＝**anti-model トラップ回避**が本物に達成されている。
4. 軸 clean・二重計上なし・消費規律クリア。

### 下げ要因（0.25 に届かせない cap）
1. **拡大 1 個（M/L₂）・1 次元指標 3 本のみ**。一般 Artin 公式でない。
2. **v_M 不在**——conductor-discriminant は「両辺 literal Nat 6」の一致であって付値等式 `v_M(𝔡)=Σa(χ)` でない。Führerdiskriminanten の忠実な部分ケースに留まる。
3. codim∈{0,1} は実表現空間 V・実 V^{G_i} から計算されず、Prop 緊縛した手置き値（実表現論の dim 計算は不在）。
4. 真水の proof-content は薄い: A2/A7 は q9wr U6 イディオムの機械的 σ²/π₉⁶-clone（プロジェクト自身が tier-M と分類）、A4/A5/A8 の新規分は iff-spec 緊縛＋`q9kd_hom_complete` 消費に還元。内容の約半分（d=6・G₂・wcd）は q9wr から消費。
5. 合成 different（推移公式・d(M/ℚ₃)）は範囲外。

### 決定
**s_B3 = 0.20。**
- 0.15（floor）を採らない理由: q9kd（B6）が完全 Kummer 双対で 0→0.15 を得た precedent に対し、q9ac はその上に**新層**（Artin 導手＋conductor-discriminant＋2 本の新規鋭利可除性境界＋anti-model iff-spec）を積む。q9kd の 0.15 と同値以下に評価するのは、追加された実不変量と anti-model 規律の達成を過小評価する。監査で vacuity/model-trap/二重計上/汚染軸のいずれの欠陥も発見されなかった。
- 0.25（ceiling）を採らない理由: v_M 不在（付値等式でなく Nat-6 一致）・実表現空間不在・単一拡大/3 指標・A2/A7 のイディオム-clone 性・約半分が q9wr 消費、という実質的限定が上限を画す。
- 中央 0.20 が: 実初・完全指標群和・iff-spec・2 本の新規境界を credit しつつ、上記 cap を honor する正直な着地。

**表示影響**: Σ_B=21→25、**柱B 表示 21→25（+4）**。（sibling B4 監査が別途上乗せする可能性あり——本監査は B3 のみ判定。）

---

## 付記（report-only）

本監査は report-only。`target_ledger.json`・`graph-meta.json` は編集していない（sibling 監査と親が一括適用）。上記 s_B3=0.20 は決定値として親へ報告する。
