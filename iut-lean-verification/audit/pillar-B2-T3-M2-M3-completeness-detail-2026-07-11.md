# B2・T3-M2/M3（逐次近似の有限深度降下 + 完備性・無限積の組み立て）詳細化設計 — 2026-07-11

**分類: [設計のみ / design-only]・tier-L 詳細化ラウンド・complete_pct 0 前進（Lean コードなし・共有ファイル変更なし）**

- 対象: 柱 B・B2 T3（上界 index(U_{L₂} : N(U_M)) ≤ 3）の残り 2 段 **T3-M2（逐次近似）と
  T3-M3（完備性 = 最難所）**。親設計 `audit/pillar-B2-T3-index-artin-detail-2026-07-11.md` §4 の
  M2/M3 スケッチを、実 Lean 到達可能なサブマイルストーンへ分解する。
- 本書の成果: (i) **disproof-first の choice 障害検査の実行と結果**（peel 塔の
  coherence を厳密整数演算で 3 標的 × 9 段検証・障害ゼロ・付録 A）、
  (ii) 「z3cLim の 6 座標適用は無限積を閉じるか」への**判定 = YES**（choice-free・
  ただし §2.3 の設計制約 1 件つき）、(iii) マイルストーン梯子 T3-M2a〜d / M3a〜c、
  (iv) 正直な verdict（到達可能・最短 opus 経路・過大主張禁止事項）。
- §4 規約: 既存モジュールの正直な限定を消さない・弱めない。到達可能性を過大主張しない。
- 前提 status（2026-07-11 時点）: T3-M1 は `IUT/Q3NormSurjGraded.lean`（q9ns イディオム）+
  `IUT/Q3NormSurjPeel.lean`（q9np peel 還元・defect λ^j 無条件可除・general j）まで実装済み。
  **M1 の残り 1 段（∃a 剰余整合）は実装中**であり、本書は §2.3 でその**着地形式への
  インターフェース要件**を M1 実装ラウンドに向けて明示する。

---

## 1. 出発点の正確な棚卸し（何が既にあり、何が無いか）

### 1.1 M2/M3 が消費する既存資産（確認済み・ファイル実在）

| 資産 | 場所 | M2/M3 での役割 |
|---|---|---|
| peel 還元 `q9np_peel_of_lamdvd`（general j） | Q3NormSurjPeel | M2 の 1 段: λ^{j+1}∣(u−N(v)) ⟹ U^{(3(j+1))} |
| defect 無条件可除 `q9np_defect_lam` | 同上 | M2 帰納の前提整備（λ^j まで無条件） |
| λ-lift/descent `q9np_lam_lift`/`q9np_lam_descent` | 同上 | λ-番号 ⟺ π₉-番号 3:1 の双方向（k 帰納・実在） |
| v 単数性 `q9np_v_unit`・`q9np_unit_of_resM_one` | 同上 | 補正因子と極限の単数性（choice-free） |
| 𝔽₃ 構成的切断 `q9nsLiftInt`/`q9nsCorr` | Q3NormSurjGraded | 剰余→補正データの choice-free 取り出し |
| **modulus-Cauchy 完備性 `z3cLim`/`z3c_converges`/`z3c_sub_eq`** | Zp3Complete | **M3b の心臓**（座標ごと極限・閉じた式・choice ゼロ） |
| level-1 可除判定 `zp_dvd_p_iff`・除算 `zpDivP` | PadicDivision | M3a level-k 判定の原型（k=1 は完成済み） |
| σ の可除性保存 `q9nf_dvd_sigma`/`_sigma2` | Q3NormFiltrationSpike | M3c ノルム Lipschitz |
| 積閉性 `q9nf_ufilt_mul`・単数機構 q3kInv/q3rqInv/zpUnitInv | 各所 | 塔の帳簿（全て幾何級数逆元ベース・choice-free） |
| 3 = π₉⁶·u₆（`q9ps_three_split`・u₆ 単数 `q9ps_u6_unit`） | Q3PiSplit 系 | M3a の π₉ ⟺ 3 変換 |
| 実 v_M（部分モノイド）`q9v_dvd_iff` | Q3ValuationReal | 使用は**任意**（M3 は可除性形式で完結・§2.2 O3） |

### 1.2 まだ無いもの（本書が設計する新規機械）

1. **z3 の level-k 可除性判定**（`zp_dvd_p_iff` の k 一般化・zpDivP の k 回反復）— M3a。
2. **O_M の座標ブリッジ**（3^k∣z ⟺ 6 個の z3 座標が 3^k 可除 ⟺ 座標 val k = 0）— M3a。
3. **π₉^{6k} ∣ z ⟺ 3^k ∣ z**（O_M 内・k 帰納）— M3a。
4. **塔の陽な再帰**（x_n をデータとして持つ構造体 + coherence 補題）— M2b/M2d。
5. **ノルム Lipschitz**（π₉^m∣(x−y) ⟹ π₉^m∣(embed(Nx)−embed(Ny))）— M3c。
6. **O_M / O_{L₂} の分離性**（∀k π₉^{6k}∣z ⟹ z=0）— M3c（逆極限表現ではほぼ自明）。

いずれも**既存パターンの k 一般化・6 重化・望遠鏡恒等式**であり、未知の数学を含まない
（§2 の検査でこの主張自体を disproof-first にかける）。

---

## 2. Disproof-first: 完備性ステップの choice/完備性障害の探索（実行結果）

最難所 M3 に対し「反証を先に探す」——障害候補を 4 つ列挙し、各々が実際に発生するかを
codebase の実定義と厳密整数演算（付録 A）で検査した。

### 2.1 障害候補 O1: ∃ 形 Cauchy からの modulus 抽出（可算選択）

Zp3Complete の正直な限定はこう明言する:
「∃ 形 Cauchy（∀n∃N…）からの modulus 抽出は可算選択で choice-free に書けない。
completeness は **modulus 形のみが本物**」。もし M2 の列 {x_n} が ∃ 形でしか
Cauchy 性を持たなければ、M3 はここで研究ブロックする。

**検査結果: 障害は発生しない。** peel 塔は **modulus が定義から陽に読める**:

> x_{n+1} = x_n · v_n、v_n = 1 + π₉^{3(3+n)−4}·a_n = 1 + π₉^{3n+5}·a_n
> ⟹ x_{n+1} − x_n = x_n · π₉^{3n+5} · a_n（**witness = x_n·a_n が式そのもの**）
> ⟹ 望遠鏡和で m ≥ n に対し π₉^{3n+5} ∣ (x_m − x_n)（q9nf_dvd_add の有限和）。

z3 座標のレベル t 一致（z3cIsModCauchy の要求形）には 3^t∣差 ⟸ π₉^{6t}∣差 で足り、
3n+5 ≥ 6t ⟺ n ≥ 2t。よって **modulus M(t) = 2t が閉じた式**で取れる
（3·(2t)+5 = 6t+5 ≥ 6t ✓）。∃ 消去は一度も要らない。これは Zp3Complete が
modulus 形に限定した設計判断が**まさに本ケースのための正しい形だった**ことを意味する。

付録 A の数値検査は、この coherence 下界 v₃(x_{n+1}−x_n の全係数) ≥ ⌊(3n+5)/6⌋ を
実際の peel 塔（3 標的 × 9 段・厳密整数演算）で**全段確認**した（違反ゼロ）。

### 2.2 障害候補 O3（先に潰す）: total-v_M / Markov 型障害の再発

Q3ValuationReal の正直な限定 1 は「total な v_M : q3kCar → Nat は choice-free に不可能
（非零判定 = Π⁰₂ = Markov 断片）」。M3 の極限議論が一般元の付値**関数**を要するなら再発する。

**検査結果: 再発しない。** M3 の全議論は付値関数を一切使わず、
**可除性 witness 形**（q9wrDvd・z3vGe = 座標 val n の等式）だけで書ける:
- Cauchy 性 = 「π₉^{3n+5} ∣ 差」の witness（§2.1 の通り式から陽に出る）。
- 収束 = z3c_converges（レベルごと座標一致・witness 演算）。
- 分離性 = 「∀n 座標 val n = 0 ⟹ Subtype.ext + funext で 0」——逆極限表現では
  非零判定なしの**正方向**の消去であり、Markov を要しない。
- 必要な「除算」は 3 除算 zpDivP（**total・choice-free・実在**）と、その反復のみ。
v_M（q9v）は部分モノイド上の関数として存在するが、M3 はそれに依存**しない**
（依存しない設計にすることが O3 回避の要点）。

### 2.3 障害候補 O2（本書が発見した唯一の実トラップ）: Prop→データ抽出

Lean の ∃（Prop）から witness を**データとして**取り出すのは choice である。M3 が
choice-free であるためには、塔 {x_n} が「∀n ∃x_n（Prop）」ではなく
**関数 n ↦ x_n（データ）**として存在しなければならない。ここに 2 つの罠がある:

1. **M1 の ∃a が Prop のまま着地すると、M2 の再帰が書けない**（各段の a_n を
   ∃ から取り出せない）。⟹ **インターフェース要件（M1 実装ラウンドへ・必須）**:
   剰余整合 ∃a は `def q9naPeelA : (j : Nat) → q3rqCar → q3kCar`（**データ関数**）+
   定理 `q9na_peel_step`（そのデータが λ^{j+1} 昇格を満たす）の**二本立て**で着地させること。
   これは可能である: a = q9nsCorr(r)、r は defect の λ^j 余因子の 𝔽₃ 剰余から
   閉形式で計算でき（先頭係数 C_j = ±1 は j の偶奇の閉形式・q9ns_resM_w）、
   余因子自体も **λ 除算の total 関数**で再計算できる（下記 2）。
2. **λ^j 余因子の再計算**: q9npLamDvd は ∃c（Prop）。しかし λ = (0,1) ∈ z3² なので
   λ 除算は **total 関数**で書ける: λ·(a,b) = (−3b, a) より
   `q3rqDivLam (s,t) := (t, zpDivP 3 (z3.neg s))`（zpDivP は total・PadicDivision 実在）。
   λ∣m のとき λ·(q3rqDivLam m) = m が level 判定条件下で成り立つ（zpDivP_mul_cancel の
   λ 版・機械的）。これで「余因子をデータとして持ち回る」必要すら消え、
   **u と x_n から次の a_n を計算する total 関数**が組める。

**検査結果: 罠は実在するが、回避策は既存イディオム（zpDivP 系）の写経で閉じる。**
付録 A は「a_n ∈ {0,1,2} が全段で存在し（a=0 の无操作段も正しく通過）、
defect レベルが単調降下する」ことを数値で確認済み——関数化の障害はない。

### 2.4 障害候補 O4: 極限での厳密等式 N(x) = u が閉じない

近似 N(x_n) ≡ u が極限で厳密等式になるには (i) ノルムの連続性と (ii) 分離性が要る。

**検査結果: 障害なし。** (i) は望遠鏡恒等式
aσaσ²a − bσbσ²b = (a−b)·σa·σ²a + b·(σa−σb)·σ²a + b·σb·(σ²a−σ²b)
（純可換環恒等式 + q9nf_dvd_sigma/sigma2）で π₉^m∣(x−y) ⟹ π₉^m∣(embed(Nx)−embed(Ny))。
(ii) は §2.2 の通り逆極限表現で自明に choice-free。さらに親設計 §4-M3 の
「λ-descent 経由の O_{L₂} 分離」は**不要と判明**——embed(u − N(x)) の分離を
**O_M の 6 座標で直接**行い、embed の単射性（成分射影で自明）で u − N(x) = 0 に落とす方が
短い（本書の M3c はこの短縮経路を採用。λ-descent 資産は既にあるので fallback にもなる）。

### 2.5 disproof-first 総合判定

**障害ゼロ。peel 塔の極限は choice-free に構成できる。**
- 塔は**構成により coherent**（modulus M(t)=2t が閉じた式・§2.1・付録 A で数値確認）。
- z3cLim の 6 座標適用（+ level-k 可除判定ブリッジ）は無限積を**閉じる**（§2.1/§2.2）。
- 唯一の実トラップは O2（Prop→データ）であり、**M1 の着地形式をデータ関数にする**という
  設計制約（§2.3 要件）で回避される。これは数学的障害ではなく実装規約である。
- total-v_M 型の Markov 障害・可算選択・新規公理は一切不要。

よって T3-M3 は **research-blocked ではなく実装対象**である（§5 verdict）。

---

## 3. T3-M2 の精密分解（逐次近似の有限深度降下）

### 3.0 主命題（codebase 語彙・データ形式）

> **M2-core**: 関数 `q9naSeq : (u : q3rqCar) → Nat → q3kCar`（陽な再帰・データ）と定理
> `q9na_approx : ∀ u, q3rqUnitMem u → q9nfUfilt 9 (q3kEmbed u) → ∀ n,
>   q3kUnitMem (q9naSeq u n) ∧
>   q9nfUfilt (3*(3+n)) (q3kEmbed (q3rqMul u (q3rqInv (q3kNormBase (q9naSeq u n)) _)))`

再帰: x_0 = 1、x_{n+1} = x_n · (1 + π₉^{3n+5} · q9naPeelA (3+n) u_n)、
u_n = u·N(x_n)⁻¹（残差・λ-level 3+n 以深）。

**正直な限定（ヘッダ転記必須）**: M2 は「任意精度でノルムに近い」までであり
「u はノルムである」（T3-core）は**主張しない**。U^{(3)}⊆N は M3 完了まで未達。

### 3.1 サブマイルストーン

- **M2a: λ 除算の total 関数**（§2.3 の O2 回避・M1 が ∃ 形で着地した場合の保険兼
  剰余計算の実装部品）。`q3rqDivLam : q3rqCar → q3rqCar` +
  `q3rqDivLam_cancel`（λ∣m ⟹ λ·(divLam m) = m・level 判定条件形）+ j 回反復版。
  消費: zpDivP・zpDivP_mul_cancel・q3rq 成分簿記。
  **難度: 小（tier-M 前半・0.3 ラウンド相当）**。M1 がデータ関数で着地すれば薄くなるが、
  M3c の座標 witness 再組立てでも同型部品を使うため無駄にならない。
- **M2b: peel 1 段のデータ化**（M1 出力の消費）: `q9naStep`（x, u ↦ x·v）+
  1 段降下定理（q9np_peel_of_lamdvd + M1 剰余整合 + q9np_v_unit + q3rq 逆元帳簿）。
  **難度: 小〜中**。
- **M2c: 再帰と主定理 q9na_approx**（n 帰納・q9nf_ufilt 系 + q3k_normBase_mul +
  逆元の積公式）。単数性・残差 filt・の 2 本を構造体で同時に運ぶ。
  **難度: 中（帳簿量が主）**。
- **M2d: 塔の coherence（M3 への引き渡し・M2 の一部として実装）**:
  `q9na_tower_dvd : ∀ n m, n ≤ m → q9wrDvd (q9nfPiPow (3*n+5)) (x_m − x_n)`
  （望遠鏡・各項 π₉^{3k+5}∣x_{k+1}−x_k は再帰の定義から witness 陽）。
  **難度: 小**。

### 3.2 M2 の難度・予測

**1 ラウンド（opus・M1 データ形式着地が前提）**。M1 が ∃ 形着地なら +0.5（M2a が肥大）。
**s_B2 予測: 0.39–0.40 → 0.42**（親設計と同値・監査次第）。

---

## 4. T3-M3 マイルストーン梯子（完備性・最難所の分解）

### M3a: 可除性ブリッジ（level-k 判定・座標・π₉⇔3）

- **M3a-1（本 M3 で最も新しい機械）: z3 の level-k 可除性判定**。
  `zpDivPPow (k) := zpDivP の k 回反復` +
  `zp_dvd_pow_iff : (∃e, x = 3^k·e) ↔ x.val k = 0`（k 帰納。降下段:
  x.val k = 0 ⟹ x.val 1 = 0（整合射影）⟹ zpDivP x が定義通り働き
  (zpDivP x).val (k−1) = zmodDivP(x.val k) = 0 で帰納が回る）。付随して
  **z3 分離性** `zp_sep : (∀ k, x.val k = 0) → x = 0`（Subtype.ext + funext・自明）。
  リスク: zmodDivP 合成の商 val 整合の帳簿（親設計の指摘通りここが最重）。
  fallback: witness（q9wrDvd の c）持ち回りで座標判定を迂回（等価・やや冗長）。
- **M3a-2: O_M 座標ブリッジ**: 3 = embed スカラーの乗法は 6 座標ごとの z3 スカラー作用
  （q3kMul の embed 引数展開・q9ns_tr_linear の証明内部と同型の成分計算）⟹
  `3^k ∣ z (O_M) ↔ 全 6 座標が 3^k 可除 ↔ 全 6 座標の val k = 0`。
  逆向き（座標 witness 6 本 → O_M witness 1 本）は zpDivPPow がデータを供給。
- **M3a-3: π₉ ⇔ 3 変換**: `π₉^{6k} ∣ z ↔ 3^k ∣ z`（k 帰納・3 = π₉⁶·u₆
  ［q9ps_three_split］・u₆ 単数［q9ps_u6_unit］・単数消去 q9gn_unit_dvd_cancel・
  π₉ 冪相殺 q9np_pipow_cancel——全部品実在）。片側単調版 π₉^m∣z ⟹ 3^{⌊m/6⌋}∣z も併設。
- **難度: 1 ラウンド（opus）**。新イディオムは M3a-1 のみ、残りは既存の k 一般化。
- **s_B2 予測: → 0.44–0.45**（インフラ・単体では T3-core を動かさないと正直申告）。

### M3b: 極限構成（z3cLim の 6 座標適用）

- **主張スケッチ**: `q9naLim (u) : q3kCar` :=（q9naSeq u の第 s 座標列, modulus M(t)=2t,
  M2d + M3a による z3cIsModCauchy 証明）への **z3cLim の座標ごと適用**（s = 1..6）。
  z3cIsModCauchy の「val t 一致」形は M2d の π₉^{6t}∣差 → M3a-3 → M3a-2 →
  z3c_sub_eq（差の val 形 → 成分一致）で供給。
- **収束定理**: `q9na_lim_conv : ∀ t, q9wrDvd (q9nfPiPow (6*t)) (x_{M'(t)} − q9naLim u)`
  — z3c_converges（座標）→ 座標 witness 6 本 → M3a-2 逆向きで O_M witness に再組立て →
  M3a-3 で π₉ 番号へ。
- **消費**: z3cLim・z3c_converges・z3c_sub_eq・z3cModUp 系（全部 Zp3Complete 実在）+ M3a。
- **難度: 1 ラウンド（opus）**。数学的新規性ゼロ（6 重化と番号換算のみ）。**choice ゼロ**
  （z3cLim は閉じた式・modulus は M(t)=2t の閉じた式）。
- **s_B2 予測: → 0.46–0.48**（極限は建つが N(lim)=u は未だ・正直申告）。

### M3c: N の連続性・分離性・厳密等式 N(x)=u（T3-core 確立）

- **M3c-1 ノルム Lipschitz**: 純環望遠鏡恒等式（§2.4）+ q9nf_dvd_sigma/sigma2 +
  q3k_norm_eq ⟹ `π₉^m ∣ (x−y) → π₉^m ∣ (embed(N x) − embed(N y))`。
- **M3c-2 分離性（O_M 直行・短縮経路）**:
  `(∀ k, q9wrDvd (q9nfPiPow (6*k)) z) → z = 0`（M3a-3 → M3a-2 → zp_sep × 6 →
  q3k_ext）。embed の単射性（第 1 成分射影・自明）と合わせ O_{L₂} 等式へ。
  fallback: 親設計の λ-descent 経路（q9np_lam_descent 実在）。
- **M3c-3 組み立て**: embed(u − N(q9naLim u)) =
  (embed(u − N x_n)) + (embed(N x_n − N(q9naLim u)))。第 1 項は M2
  （π₉^{9+3n}・比→差変換は q9np_ratio_ring の逆向き＝N(x_n) 単数倍）、第 2 項は
  M3b 収束 + M3c-1（π₉^{6t}）。n = M'(t) と流し ∀t π₉^{6t}∣ ⟹ M3c-2 で
  **N(q9naLim u) = u 厳密等式**。単数性: res_M(q9naLim u) = res_M(x_n) + res_M(差) =
  1 + 0（q9rf_resM_add・q9np_resM_dvd_pi9・q9np_resM_v 系）⟹
  q9np_unit_of_resM_one（**実在**）。⟹ **T3-core**:
  > ∀ u, q3rqUnitMem u → q9nfUfilt 9 (q3kEmbed u) →
  > ∃ x, q3kUnitMem x ∧ q3kNormBase x = u
  （∃ は Prop 結論なので構成 q9naLim を refine で与えるだけ・choice 無縁）。
- **難度: 1 ラウンド（opus・レベル簿記の min/max 整理に fable スポット 1 回の余地）**。
- **s_B2 予測: → 0.48–0.52**（T3-core 確立・親設計と同値）。

### 予測サマリ（M2/M3 詳細版）

| 段 | 内容 | 新イディオム | 難度 | s_B2 予測（監査次第） |
|---|---|---|---|---|
| M2a | λ 除算 total 関数 | q3rqDivLam（zpDivP 写経） | 小 | （M2 に含む） |
| M2b/c | peel データ化 + 塔再帰 + 近似定理 | なし（M1 消費） | 中 | 0.42 |
| M2d | 塔 coherence（witness 陽） | なし | 小 | （同上） |
| M3a | level-k 判定・座標・π₉⇔3 ブリッジ | zp_dvd_pow_iff（k 帰納） | 中 = 1R opus | 0.44–0.45 |
| M3b | z3cLim 6 座標適用・収束 | なし（6 重化） | 中 = 1R opus | 0.46–0.48 |
| M3c | Lipschitz・分離・N(x)=u・単数 | 望遠鏡恒等式 | 中 = 1R opus (+fable spot) | 0.48–0.52 |

M2+M3 合計 **3–4 ラウンド**（親設計の「M2 1 + M3 2–3」と整合・M3 が 3 に滑るリスク込み）。

---

## 5. 正直な verdict

1. **T3-M3 は到達可能（research-blocked ではない）**。disproof-first 検査（§2・付録 A）で
   4 つの障害候補は全て解体された。核心の問い「z3cLim の 6 座標適用は無限積を閉じるか」の
   答えは **YES**: peel 塔は補正因子の深さ 3n+5 が定義から読めるため
   **構成により modulus-Cauchy**（M(t)=2t 閉形式）であり、Zp3Complete が意図的に
   modulus 形へ限定した choice-free 完備性がそのまま働く。可算選択・Markov・
   新規公理は一切不要。total-v_M 障害は再発しない（全議論が witness 可除性形式）。
2. **唯一の本質的な設計制約（数学障害ではない）**: choice-free 性は「塔がデータ関数で
   ある」ことに懸かっている。**M1 の残り 1 段（∃a 剰余整合）は
   `def`（データ関数）+ 定理の二本立てで着地させること**（§2.3 インターフェース要件）。
   ∃ 形のみで着地した場合も λ 除算 total 関数（M2a）で復元可能だが +0.5 ラウンド。
3. **最短 opus 経路**: (0) M1 残段をデータ形式で完了（実装中）→ (1) M2a–d 1 ラウンド →
   (2) M3a 1 ラウンド →（3) M3b 1 ラウンド →（4) M3c 1 ラウンド（fable スポット許容）
   → T3-core。M3a は M2 と独立なので **M2 と M3a は並列可**（依存: M3b ← {M2d, M3a}、
   M3c ← {M3b, M3a}）。その後 M4（index≤3・Gal≅余核）は親設計 §4 の通り。
4. **過大主張の禁止事項（実装ラウンドのヘッダへ転記）**:
   - M2 完了時点で「u はノルム」を主張しない（有限深度近似のみ・s_B2 0.42 止まり）。
   - M3a/M3b は単体で T3-core を動かさない（インフラと極限存在のみ）と正直申告。
   - M3c 完了後も **cap(b)（分数元込み L₂^×/N(M^×)）・Artin 正規化・一般局所体は未達**
     （q9qc 限定 1 の継承・T3 スコープ外）。complete_pct への反映は独立監査次第。
   - 本書は設計のみであり **complete_pct 0 前進**。数値予測はすべて監査次第。
5. **残リスク（順位付き）**: (i) M3a-1 の zmodDivP 合成簿記が重い（fallback: witness
   持ち回り・§4 M3a）、(ii) M1 残段の着地形式（§2.3 要件が守られない場合 +0.5R）、
   (iii) M3c のレベル簿記（min/max の整理・fable スポットで解消可能な種類）。
   いずれも研究リスクではなく実装リスク。

---

## 付録 A: disproof-first 検査スクリプト（peel 塔の coherence・再現用・依存なし）

ℤ[ζ₉]（Φ₉ 厳密整数演算）で実際の逐次近似塔を走らせ、(1) 各段で a_n ∈ {0,1,2} が存在し
defect の λ-level が j を超えて昇格すること、(2) 塔差分の係数 3 進付値が coherence 下界
⌊(3n+5)/6⌋ を全段満たすこと、を検査する。

```python
# Z[zeta9] mod Phi9 = x^6+x^3+1 (exact), sigma: x->x^4, N(z)=z*sz*s2z
MOD = 3**60
def red(a): return tuple(((c % MOD) if c % MOD <= MOD//2 else c % MOD - MOD) for c in a)
def pmul(a,b):
    c=[0]*11
    for i in range(6):
        if a[i]:
            for j in range(6): c[i+j]+=a[i]*b[j]
    for k in range(10,5,-1):
        v=c[k]
        if v: c[k]=0; c[k-6]-=v; c[k-3]-=v
    return red(tuple(c[:6]))
padd=lambda a,b: red(tuple(x+y for x,y in zip(a,b)))
psub=lambda a,b: red(tuple(x-y for x,y in zip(a,b)))
ONE=(1,0,0,0,0,0); PI=(-1,1,0,0,0,0)
SIG=[(1,0,0,0,0,0),(0,0,0,0,1,0),(0,0,-1,0,0,-1),(0,0,0,1,0,0),(0,-1,0,0,-1,0),(0,0,1,0,0,0)]
def sigma(a):
    r=(0,)*6
    for k in range(6):
        if a[k]: r=padd(r,tuple(a[k]*t for t in SIG[k]))
    return r
def N(z):
    n=pmul(pmul(z,sigma(z)),sigma(sigma(z)))
    assert n[1]==n[2]==n[4]==n[5]==0
    return (n[0],n[3])
def lam_val_exact(t, cap=45):   # lambda-val in Z[zeta3], lambda=1+2*zeta3
    a,b=t
    if a==0 and b==0: return 999
    v=0
    while v<cap:
        if (a+b)%3!=0: return v
        m0=a-2*b; m1=2*a+b-2*b   # t*lambda
        a,b=-m0//3,-m1//3        # t/lambda = -(t*lambda)/3
        v+=1
    return v
def pip(k):
    r=ONE
    for _ in range(k): r=pmul(r,PI)
    return r
def v3(n):
    if n==0: return 99
    v=0
    while n%3==0: n//=3; v+=1
    return v
def run_tower(u, steps=9):
    x=ONE; ok=True
    for n in range(steps):
        j=3+n
        found=None
        for a in (0,1,2):
            cand=x if a==0 else pmul(x, padd(ONE, tuple(a*t for t in pip(3*j-4))))
            d2=(u[0]-N(cand)[0], u[1]-N(cand)[1])
            if lam_val_exact(d2)>=j+1: found=(a,cand); break
        if found is None: ok=False; break
        a,x_new = found
        diffs=[v3(abs(c)) for c in psub(x_new,x) if c!=0]
        if diffs and min(diffs) < (3*n+5)//6: ok=False; break
        x=x_new
    return ok
# U^(3)_lambda targets: 1-3*lambda=(-2,-6), 10=(10,0), 1+3*lambda+9=(13,6)
print(all(run_tower(u) for u in [(-2,-6),(10,0),(13,6)]))   # expect True
```

実行結果（本ラウンドで実施・§2 に転記）: 3 標的 × 9 段（λ-level 12 まで）で
**a_n 存在・defect 単調降下・coherence 下界、全段 PASS・違反ゼロ**。
a=0 の無操作段（defect が既に深い場合）も正しく通過し、塔の関数的定義
（x_{n+1} = x_n·(1+π₉^{3n+5}a_n)・a_n ∈ {0,1,2}）に障害がないことを確認した。
