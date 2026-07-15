# 独立敵対的再監査: Q3HasseArfReal (q9ha) — 柱B・B4

- 監査日: 2026-07-11
- 対象: `IUT/Q3HasseArfReal.lean`（prefix `q9ha`, 185 行, commit 3801a0d）
- 監査者: 独立敵対的監査（本コードを書いていない・既定 SKEPTICAL）
- 分類申告: **[実／(a) 昇格]**、forecast 0→0.10–0.15
- モード: report-only（`target_ledger.json`・`graph-meta.json` は編集しない。s_B4 を決定・報告のみ）

---

## 0. 結論サマリ

| 検査項目 | 判定 |
|---|---|
| 真水（実上付き番号帰属）は genuine か | **Yes（ただし退化的・薄い）** |
| コードベース初の実上付き番号帰属か | **Yes**（q9wr・q9ac は下付きのみ・明示的に「上付き番号ゼロ」） |
| 正直な薄さは最前面に保たれているか / 退化的整数性の過大主張は無いか | **Yes（保持）／過大主張なし** |
| anti-Nat-staircase（q9haOrder の iff 緊縛） | **Yes（ただし弱い iff）** |
| consume-not-reprove（q9wr/hau/rnf を消費・再証明せず） | **Yes** |
| 公理 = [propext, Quot.sound] のみ（5 定理） | **Yes** |
| 禁止タクティク不使用・build 成功 | **Yes**（`lake build` EXIT=0, 158 jobs） |
| double-counting（hau/haa/hfa は List-Nat・q9ha は再証明せず） | **Yes（新規は消費のみ）** |

**決定 s_B4 = 0.10**（forecast 下端）。理由: 「実上付き番号が存在しない」ブロックは discharge されるが、G₀=G₂ ゆえ数値内容は退化的で、真水は既存 q9wr より論理的に弱い 1 命題＋実 Herbrand ψ 閉形式にとどまる。

---

## 1. 真水（genuinely new）の検査

### 1.1 `q9ha_upper_G2_real`（σ∈G^2, π₉³∣(σπ₉−π₉)）

```
theorem q9ha_upper_G2_real : q9wrDvd q9haPi3 q9haSigmaDiff := q9wr_G2_mem.1
```

- `q9haPi3 = q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9`（=π₉³）、`q9haSigmaDiff = q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)`（=σπ₉−π₉）。
- `q9wr_G2_mem.1` の型は `q9wrDvd (π₉³) (σπ₉−π₉)` と**定義的に同一**。
- **敵対的所見**: これは q9wr_G2_mem.1 を「上付き」とラベルし直しただけ。G₀=G₂ ⟹ ψ(2)=2 ⟹ 上付き G^2 除子 = 下付き G_2 除子 = π₉³ なので、**新しい命題ではない**（下付き=上付きの退化の直接帰結）。真水ではあるが realization の relabel。ヘッダはこれを正直に「退化的」と認めている（正当）。

### 1.2 `q9ha_upper_G3_trivial_real`（σ∉G^3, ¬π₉⁶∣(σπ₉−π₉)）★真の新規命題

```
theorem q9ha_upper_G3_trivial_real : ¬ q9wrDvd q9haPi6 q9haSigmaDiff :=
  q9ha_not_dvd_descent (rfl) q9wr_G3_trivial
```

- `q9haPi6 = q3kMul q9haPi4 (q3kMul q9psPi9 q9psPi9)`（=π₉⁴·π₉²=π₉⁶）。`q9haPi4 = π₉⁴`。
- `q9ha_not_dvd_descent {smallD extra bigD x} (hb: bigD = smallD·extra) (hnd: ¬smallD∣x) : ¬bigD∣x`。ここで smallD=π₉⁴, extra=π₉², bigD=π₉⁶。`rfl : q9haPi6 = q3kMul q9haPi4 (π₉²)` は定義的に成立（q9haPi6 の定義そのもの）。hnd=`q9wr_G3_trivial`（¬π₉⁴∣）。
- 可除性下降補題 `q9ha_dvd_descent` は正しい（bigD=smallD·extra ∧ bigD∣x ⟹ smallD∣x, 結合律で c↦extra·c）。対偶も正しい。
- **これは新しい除子指数 π₉⁶（q9wr の π₉⁴・q9ac の π₉⁴/π₉⁷ には現れない）を、正しく計算された Herbrand ψ(3)=5（除子指数 ψ(3)+1=6）に結び付けた、コードベース初の実上付き番号除子での帰属命題**。非空虚（実 σ・実 π₉ 可除性・実 O_M 上）。
- **敵対的所見**: しかし ¬π₉⁶∣ は q9wr が既に証明済みの ¬π₉⁴∣ より**論理的に弱い**（π₉⁶∣ ⟹ π₉⁴∣ なので ¬π₉⁴∣ ⟹ ¬π₉⁶∣、5 行の粗い下降）。よって真水は「新しい論理的強さ」ではなく「上付き番号の正しい除子での再表現」。数学的には正しく honest だが薄い。

### 1.3 実 Herbrand ψ の実除子への緊縛

- `q9haPsi v = v + 2*(v−2)`（Nat 切り捨て減算）。ψ(2)=2, ψ(3)=5 を `rfl` で検証（`q9ha_psi_two`/`q9ha_psi_three`）。
- 分岐論の検算: 下付き break t=2、G₀=G₁=G₂=位数3, G_{≥3}=1。φ(u)=∫₀^u dt/[G₀:G_t], u≤2 で [G₀:G_t]=1 ⟹ φ(u)=u ⟹ 上付き break=φ(2)=2。u>2 で傾き 1/[3:1]=1/3 ⟹ ψ=φ⁻¹ は break 後傾き 3: ψ(3)=2+3·1=5。閉形式 v+2(v−2) は v≥2 で 3v−4=2+3(v−2) と一致。**数学的に正しい**。
- `q9ha_upper_exponents : ψ(2)+1=3 ∧ ψ(3)+1=6`（rfl）で ψ を実 π₉ 冪除子 q9haPi3/q9haPi6 に緊縛。除子の実可除性定理（1.1/1.2）が実際に π₉³/π₉⁶ を主語に使うため、緊縛は名目以上に機能している。
- **これはコードベース初の実 Herbrand ψ 閉形式**（rnf の ψ=rnfPsi は Nat 模型・実 Galois なし）。

**真水判定: genuine かつ non-vacuous。ただし内実は「退化的な G^2 relabel ＋ 既存より弱い G^3 命題 ＋ 実 ψ 閉形式」で薄い。**

---

## 2. 正直な薄さの検査（退化的整数性の過大主張はあるか）

ヘッダの「正直な限定」（23–31 行）は要求どおり最前面に保持:

1. 拡大 1 個（M/L₂）・単一 break（t=2）のみ。
2. **G₀=G₂ ⟹ φ は break まで恒等 ⟹ 上付き=下付き=2 ⟹ 整数性の数値内容は退化的（ほぼ自明）。本モジュールの真水は「上付き述語の realization」であって新しい整数性定理ではない**——task が要求する honesty をそのまま明記。
3. 上付き番号は Nat 値のみ（有理数上付き番号なし・v_M なし・可除性形式）。
4. σ を主語（σ² 側は範囲外・q9ac が別枠）。

**過大主張の検査**: §6 `q9ha_break_transform` と capstone `Q3HasseArfRealData.integrality` は退化的整数性（rnfPhi 1 (rnfPsi 1 2)=2 の Herbrand 往復・上付き=下付き=2 の landing）を扱うが、ヘッダ・docstring とも一貫して「退化的（degenerate）」「hau 消費」と明記し、深い新定理として提示していない。**過大主張なし。** むしろ真水を G^3 realization に限定して明言している点は誠実。

---

## 3. anti-Nat-staircase の検査

- `q9haOrder v = if v ≤ 2 then 3 else 1`（素の Nat 階段）。
- 緊縛 `q9ha_order_two_iff : q9haOrder 2 = 3 ↔ q9wrDvd q9haPi3 q9haSigmaDiff`、`q9ha_order_three_iff : q9haOrder 3 = 1 ↔ ¬ q9wrDvd q9haPi6 q9haSigmaDiff`。両方とも実 σ 可除性 Prop に iff 緊縛されており、**bare Nat staircase ではない**。
- **敵対的所見**: iff は両辺とも無条件に true（順方向は仮説を無視して `q9ha_upper_G2_real`、逆方向は `rfl`）なので、Nat 値が実 Prop を非自明に追跡することを強制しない**弱い iff**（コスメティック）。ただし本リポジトリの標準イディオムであり、anti-staircase 規則の字義は満たす。**合格（弱い）。**

---

## 4. consume-not-reprove の検査

| q9ha 定理 | 消費元 | 再証明していないか |
|---|---|---|
| `q9ha_upper_G2_real` | `q9wr_G2_mem.1`（そのまま） | ✓ 消費のみ |
| `q9ha_upper_G3_trivial_real` | `q9wr_G3_trivial`（5 行下降） | ✓ 消費＋下降 |
| `q9ha_break_transform` | `hau_upper_break_integer 3 _ [2]`, `rnf_phi_psi 1 2 _` | ✓ hau 整数性・rnf 変換を消費 |
| `q9ha_hasse_arf_instance` | `(hauDataOf 3 _ [2]).integrality` | ✓ hau の `.integrality` フィールドを消費 |
| `q9ha_data.integrality` | `hau_upper_break_integer 3 _ [2]` | ✓ 消費 |

- `hauUpperBreak [2]=2`, `hauLowerFrom 3 1 [2]=2` は rfl（計算）で妥当、整数性そのもの（hauUpperFrom=hauUpperBreak）は hau 定理を呼んで消費（rfl で潰していない）。
- **consume-not-reprove: 合格。** hau の Hasse–Arf 整数性を再証明せず、q9wr の下付き break を再証明せず、rnf の φ/ψ 変換を再証明していない。

---

## 5. 公理・禁止タクティク・build

- `lake build IUT.Q3HasseArfReal` → **EXIT=0（158 jobs, Build completed successfully）**。
- `#print axioms`（scratch）:

```
q9ha_upper_G2_real          : [propext, Quot.sound]
q9ha_upper_G3_trivial_real  : [propext, Quot.sound]
q9ha_break_transform        : [propext, Quot.sound]
q9ha_hasse_arf_instance     : [propext, Quot.sound]
q9ha_exists                 : [propext, Quot.sound]
```

**全て exactly [propext, Quot.sound]。** sorryAx・Classical.choice なし。

- 禁止タクティク grep（sorry/admit/native_decide/Classical.choice/axiom/decide）: 実タクティクにヒットなし（コメント行 32 の「Classical.choice を導入しない・sorry 皆無」の自己申告のみ）。

---

## 6. double-counting vs hau/haa/hfa

- `HasseArfUnconditional.lean`: `hauUpperBreak : List Nat → Nat`, `hauLowerFrom (p) : Nat → List Nat → Nat`, `hauUpperFrom (p) : Nat → List Nat → Nat` — **純 List-Nat 模型・実 Galois（q3kSigma）を一切持たない**。監査済み判定「Hasse–Arf 群は List Nat」と整合。
- q9ha の実上付き番号帰属（π₉ 可除性・実 σ）は hau の List-Nat 整数性とは別軸で、hau を**消費するのみ**（§4）。
- 兄弟 B3 `Q3ArtinConductorReal.lean`（q9ac）は honest 限定で明示的に「一般元 x の v_π・**上付き番号・Herbrand φ/ψ はゼロ**」——q9ac の G_i（q9acGiMem）は**下付き番号のみ**（除子 π₉^{i+1}）。q9wr も下付きのみ。
- したがって q9ha の**実上付き番号帰属＋実 Herbrand ψ 閉形式はコードベース初**であり、double-counting なし。

---

## 7. s_B4 の決定（report-only）

台帳 B: B1(w20,0.6) B2(w20,0) B3(w20,0) B4(w15,0) B5(w15,0.5) B6(w10,0.15)、Σw=100。
現状 num = 21.0 → complete_pct(B)=21。compute_complete_pct.py は Fraction 厳密＋Python round（銀行家丸め）。

### 上げる要因
- **コードベース初の実上付き番号ラミフィケーション帰属**——「実 Galois 群での上付き番号が存在しない」B4 ブロックを discharge（q9wr/q9ac はいずれも下付きのみ）。
- σ∉G^3 の**新しい実除子 π₉⁶**（Herbrand ψ(3)=5 に正しく緊縛）を実 π₉ 可除性で realization。**初の実 Herbrand ψ 閉形式**。
- 実拡大が hau の Nat 模型点 `hauDataOf 3 _ [2]` を実現（cross-check）。公理クリーン・build 成功・honest 限定最前面・過大主張なし。

### 下げる要因
- **退化的**: G₀=G₂ ⟹ 上付き=下付き=2、整数性は数値的に自明。
- **G^2 帰属は q9wr_G2_mem.1 の relabel**（定義的に同一命題）で新規性ゼロ。
- **G^3 命題（¬π₉⁶∣）は既存 q9wr の ¬π₉⁴∣ より論理的に弱い**（粗い除子への下降）——新しい強さではなく再表現。
- 拡大 1 個・単一 break・σ 主語のみ・Nat 値上付き番号のみ（有理上付き番号なし・v_M なし・可除性形式）。整数性・break・φ/ψ 変換の大半は q9wr/hau/rnf から消費。
- q9haOrder の iff は両辺無条件 true の弱い緊縛。

### 決定

**s_B4 = 0.10**（forecast 0.10–0.15 の下端）。

ブロック discharge の事実で 0 超えは正当だが、実質的な新規数学は「退化的な G^2 relabel」＋「既存より弱い G^3 realization」＋「実 Herbrand ψ 閉形式」に限られ、深い定理ではない modest realization。正直に下端 0.10。

### 表示影響（parent が兄弟 B3 監査と合算・本監査は編集しない）

- s_B4=0.10 単独: B num 21.0→22.5、**銀行家丸めで 22.5→22（偶数）**、complete_pct(B) 21→22。
- 参考 s_B4=0.15 単独: B num 21.0→23.25→23。
- **銀行家丸めトラップ注意**: 22.5 は 23 でなく **22** に丸まる。B3 が同時に動く場合の合算 .5 同点は parent が処理。

---

## 8. 監査記録の要約

q9ha はコードベース初の実上付き番号ラミフィケーション帰属＋実 Herbrand ψ 閉形式を、実 σ=q3kSigma・実 π₉ 可除性・実 O_M 上に建てる genuine な昇格である。公理は [propext, Quot.sound] のみ、build 成功、禁止タクティクなし、consume-not-reprove・anti-staircase を満たし、double-counting なし。ただし G₀=G₂ ゆえ内容は退化的で、G^2 は relabel、G^3 は既存より弱い再表現、大半は消費——ヘッダはこれを正直に最前面で認めており過大主張はない。**modest realization。s_B4 = 0.10。**
