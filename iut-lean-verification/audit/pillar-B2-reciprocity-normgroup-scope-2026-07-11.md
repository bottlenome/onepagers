# 柱B2 再評価: 実局所類体論（相互写像・ノルム群）の crux「ζ₃∉N(M^×)」は今ラウンドで割れるか — 敵対的再監査（2026-07-11）

**種別**: 詳細化ドキュメント（design-only・Lean 実装なし・tier-L 枠の消費）
**対象**: `target_ledger.json` 柱B B2「実局所類体論(相互写像・実)」（w20・status 0・柱B 最大の残ゼロ）
**前提**: 柱B 表示 26（Σ_B = 20·0.60(B1) + 20·0(B2) + 20·0.20(B3) + 15·0.10(B4) + 15·0.5(B5) + 10·0.15(B6) = 26.5 → 26、banker's）。実 Gal(M/L₂)=⟨q3kSigma⟩・実 3 次ノルム N=q3kNormBase・実 Kummer 双対 q9kd・実野性分岐 q9wr は既存。
**姿勢**: 敵対的・正直。**デフォルト判定 =「B2 の crux は既存資産の未発明イディオムを要し、薄い閾値ショッピングを B2 status に化けさせてはならない」**。この推定を、実 def/theorem 本体を読んで覆せるか検証した。先行スコープ（`audit/pillar-B-cft-conductor-hasseArf-scope-2026-07-11.md` §5）の「B2 見送り」判定を、割りにいく側から再攻撃する。

---

## TL;DR

- **crux「ζ₃∉N(M^×)」は今ラウンドでは割れない（先行 §5 判定を維持・敵対再検証済み）**。理由は 1 点に集約される: コードベースが持つ**唯一の「付値的」判別器**は合成 ℤ₃-ノルム `φ(x) := q3rqNorm(q3kNormBase(x))`（＝N_{M/ℚ₃}・乗法的）とその可除性版だが、`q3rq_zeta_norm : q3rqNorm q3rqZeta = 1` により **φ は ζ₃ と 1 を区別できない**（両方 φ=1）。U6（`q9wr_G3_trivial`）の矛盾エンジン「3·s は非単数」は、一様化子 π₉ が混じって φ に因子 3 を落とすときだけ発火する。ζ₃ は単数で φ=1 を落とすので**何も発火しない**。crux は付値の外＝高次単数フィルトレーション U^(i) の中にあり、そこは v_M 不在で未建設。
- **極大イデアル還元も level 1 で空振り**する（本物の障害は mod m² から）。残余体は 𝔽₃、Frobenius t³=t で N(x) ≡ ā+b̄+c̄ (mod m)、ζ₃≡1 (mod m)。よって「N(x)=ζ₃」は mod m で ā+b̄+c̄=1̄ という**充足可能**条件に退化し障害ゼロ。ζ₃ と 1 の差は mod m²（√−3 係数）＝ U^(1) の graded piece で初めて現れる。**有限 mod-m 計算では原理的に決着不能**。
- **q9kd は crux を供給しない**。q9kd の対は Gal(M/L₂)×⟨[ζ₃]⟩→μ₃ の**Kummer 対（Galois の根への作用）**であり、L₂^×/N ↔ Gal の**ノルム剰余対（Artin/Hilbert 記号）ではない**。q9kd は Kummer 双対の「易しい側」（Gal ≅ Hom(⟨[ζ₃]⟩,μ₃)）を建て、「難しい側」（Artin 写像 L₂^×→Gal）を建てていない。さらに `q9kd_class_nontrivial`（ζ₃ は L₂ で非 3 乗）は crux **より真に弱い**——非 3 乗 ⊉ 非ノルム（ノルム群 ⊋ 3 乗群）。この差がまさに単数フィルトレーション分。
- **二重計上リスクは低い**（既存 B2 群は全て分裂表示模型／不分岐／p=2 LT／従順記号で、実 Gal(M/L₂) 分岐主語を各ヘッダが自ら「後続」と申告）。**が、その分ゼロから重い**——実 Gal(M/L₂) 上の分岐相互律は本当に新規建設であり、正の半分だけで status を主張すれば水増し。
- **推奨**: B2 に**薄い閾値ショッピングをしない**。B2 は**2–3 ラウンド案件**（欠けているのは実 U^(i) フィルトレーション＋ノルムの graded 挙動＋v_M）。最善の次の一手は §4 の通り、**（第一候補）B2 の de-risk 詳細化 1 枠（tier-L・design-only・今ラウンド complete_pct 0 前進だが w20 を解錠）**、（第二候補・表示を動かしたい場合）§4 で唯一 genuine と確認できた小前進。B2 の正の半分（ノルムが L₂ 一様化子を打つ＝相互律の値群側）は真だが表示を動かさない。

---

## 1. crux「ζ₃∉N(M^×)」は既存資産で証明可能か — 具体計算による敵対的判定

### 1.1 目標命題の正確化

ノルム写像 `N = q3kNormBase : q3kCar → q3rqCar`（O_M → O_{L₂}、`q3k-5c`）。単数 x に対し N(x) は q3rq-単数（`q3k_unit_mul`/`q3kUnitMem`）で、N(U₃) ⊆ U₂ = q3rqU。crux は:

> **∃ x, q3kUnitMem x ∧ q3kNormBase x = q3rqZeta** — が **偽**であること（ζ₃ ∉ N(U₃)、同値に [U₂:N(U₃)]=3・[L₂^×:N(M^×)]=3）。

ここで一様化子は既に処理済み: `q9wr_normBase_pi9 : N(π₉) = ζ₃−1` かつ `q9wr_qnorm_zeta_sub : q3rqNorm(ζ₃−1) = 3`。すなわち **N(π₉)=ζ₃−1 は L₂ の一様化子**（v_{L₂}=1）で、N(M^×) は値群 L₂^×/U₂=ℤ に全射。ゆえに指数 3 は完全に**単数部** [U₂:N(U₃)] に落ちる。crux は単数の話に還元される。

### 1.2 唯一の判別器（合成 ℤ₃-ノルム）は crux に対して盲目

U6 = `q9wr_G3_trivial`（¬π₉⁴∣(σπ₉−π₉)）の証明本体が使う確立イディオムは:

```
u* = π₉·x を仮定 → N を取る → N(u*) = N(π₉)·N(x) = (ζ₃−1)·N(x)
→ q3rqNorm 両辺 → q3rqNorm(N(u*)) = q3rqNorm(ζ₃−1)·q3rqNorm(N(x)) = 3·s
→ u* 単数ゆえ左辺 ℤ₃-単数、しかし 3·s は非単数（q9wr_three_mul_not_unit）→ 矛盾
```

矛盾の駆動力は `q9wr_qnorm_zeta_sub` が落とす**因子 3**（＝π₉ が値群側に持つ痕跡）。この因子は φ(x)=q3rqNorm(q3kNormBase(x))（乗法的・`q3k_normBase_mul`＋`q3rq_norm_mul`）が **π₉ を非単数側に射影する**から出る。

crux に同じイディオムを当てると即座に崩れる。仮に q3kNormBase(x)=ζ₃ なら、φ を取って:

```
q3rqNorm(q3kNormBase(x)) = q3rqNorm(q3rqZeta) = 1   （q3rq_zeta_norm）
```

**右辺は 1（単数）で、x 単数なら左辺も自動的に単数——矛盾ゼロ**。U6 の「3·s 非単数」は発火しない。すなわち codebase 唯一の付値的判別器 φ（と π₉ 可除性フィルトレーション）は、**ζ₃ と 1 を分離できない**（`q3rq_zeta_norm` が両者を 1 に潰す）。ζ₃ は単数であって一様化子を含まないので、U6 型の議論は構造的に無力。**これが「割れない」ことの中核的な機械的理由**であり、先行 §5 の「v_M の壁」を精密化する。

（傍証: `q9ps_normBase_embed : N(embed n)=n³`。よって全ての 3 乗 t³=N(embed t) は既にノルム。ノルム群 ⊇ (L₂^×)³。crux は「ζ₃ はこの**より大きい**ノルム群の外」——3 乗群の外（`q9ci_no_cbrt_zeta`）より真に強い。差 = ノルム群/3 乗群 ⊆ U₂ の単数フィルトレーション。）

### 1.3 極大イデアル還元も level 1 で空振り

「N(x)=ζ₃ の非存在を有限計算（mod m^k）で示せないか」を試す。L₂=ℚ₃(√−3) の残余体は 𝔽₃、m_{L₂}=(√−3)=(ζ₃−1)、3=−λ²∈m²（`q3rq_lambda_sq`）。N(x)=a³+ζ₃b³+ζ₃²c³−3ζ₃abc を mod m 還元: ζ₃≡ζ₃²≡1、3≡0 なので N(x) ≡ a³+b³+c³。𝔽₃ 上 Frobenius t³=t で ≡ ā+b̄+c̄。ζ₃≡1。ゆえに:

> **N(x)=ζ₃ (mod m) ⟺ ā+b̄+c̄ = 1̄ ∈ 𝔽₃** — 充足可能（例 a=1,b=c=0）。**level 1 障害ゼロ**。

ζ₃ と 1 の差は mod m²（√−3 の 1 次係数、＝ U^(1)=1+π₉O_M の graded piece）で初めて現れる。**したがって有限 mod-m 計算では原理的に決着できず、U^(1) フィルトレーションのノルム像解析が必須**。これは choice-free 可除性形式でも「一般元 x=(a,b,c) の π₉-adic 単数フィルトレーション所属」を要し、q9wr 正直限定 1・2 が明示的に建てていない対象（v_M 不在・一般元の σx−x 一様可除性は未形式化）である。

### 1.4 §1 判定

**crux は付値・有限還元・合成ノルム・q9kd のいずれでも割れない。v_M の壁（正確には高次単数フィルトレーション U^(i) とその上のノルムの graded 挙動）に確定的に当たる**。先行 §5 判定を敵対再検証の上で維持する。

---

## 2. 「もし可能なら」の設計と、正の半分の正直な位置づけ（二重計上判定込み）

§1 の通り crux は今ラウンドで不可なので、本節は (i) 今建つ正の半分が何で、なぜ B2 status を動かさないか、(ii) 仮に crux が入ったときのモジュール像、(iii) 既存 B2 群との二重計上判定、を与える。

### 2.1 今建つ「正の半分」（真だが status を動かさない）

`Q3LocalReciprocityReal.lean`（仮 prefix `q9lr`）として次は**既存資産だけで閉じる**:

| # | 命題 | 消費 | 判定 |
|---|---|---|---|
| P1 | N=q3kNormBase は群準同型 U₃→U₂（乗法性・単数保存） | `q3k_normBase_mul`・`q3k_unit_mul` | 真・**q3k の再輸出**（新規性ほぼゼロ） |
| P2 | N(π₉)=ζ₃−1 は L₂ 一様化子（q3rqNorm=3） | `q9wr_normBase_pi9`・`q9wr_qnorm_zeta_sub` | 真・**q9wr の消費**（再主張禁止） |
| P3 | **N(M^×) は値群 L₂^×/U₂=ℤ に全射**（相互律の値群側・不分岐商） | P2 | **新規だが薄い**（相互律の「易しい半分」） |
| P4 | ノルム群述語 N(U₃)⊆U₂ を部分群として構成 | P1・imSubgroup 系 | 真・定型 |
| P5 | (L₂^×)³ ⊆ N(M^×)（3 乗は全てノルム） | `q9ps_normBase_embed` | 真・q9ps 消費 |

**これらは crux（[U₂:N(U₃)]=3・ζ₃∉N(U₃)）を含まない**。監査は crux 不在で B2 を **0 のまま**に据える見込みで、P1–P5 だけのモジュールで B2 status>0 を主張するのは §2/§3 違反の水増し（**却下**）。P3（値群側全射）は真の新規だが、相互律の核 = ノルム群の**核の特徴付け**が無いので単独では 0.05 未満の寄与しか持たず、B2 を動かさない。

### 2.2 crux が入ったときのモジュール像（後続ラウンド用の目標）

crux `q9lr_zeta_not_norm : ¬∃ x, q3kUnitMem x ∧ q3kNormBase x = q3rqZeta` が建った暁の主定理列:

- `q9lr_norm_index_three`: [U₂:N(U₃)]=3（P3 の値群全射と併せ [L₂^×:N(M^×)]=3）。
- `q9lr_rec` : Artin 写像 L₂^×/N(M^×) → Gal(M/L₂)=q9kdG の同型（honest ∃/index 形）。**q9kd を消費**——q9kd の Gal ≅ Hom(⟨[ζ₃]⟩,μ₃) と接合し、ノルム剰余対 = Kummer 対の随伴として rec を定義。
- `q9lr_hilbert_zeta` : Hilbert 記号 (ζ₃,ζ₃)_3 ≠ 1（crux の記号版・ζ₃∉N の言い換え）。
- tier 見込み **L（fable）**、行数**未確定（新イディオム発明を含むため見積り不能）**、依存 Q3WildRamFiltrationReal＋Q3KummerDualityReal＋（新規）実 U^(i) モジュール。

### 2.3 二重計上判定（敵対的・既存 B2 群を本体まで確認）

デフォルト仮説「既存 reciprocity 群が B2 を既にカバー」を各ヘッダ本体で検証し、**却下（＝実 Gal(M/L₂) 分岐主語は新規）**を確認:

- `LocalReciprocity`(M330F)・`FullReciprocity`(M37)・`NormGroup`(M335F): **分裂表示 K^×=ℤ×O^×** 上の Artin 写像・ノルム群。実の体・環・Galois 作用なし。各自「一般分岐・実 Gal(L/K) 主語は後続」と申告。
- `LubinTateReciprocity`/`LubinTateNormGroup`(M385/390F): **p=2・乗法形式群 G_m・有限捻れレベル・不分岐次数 d** の模型。実 O_{L₂} 分岐拡大ではない。
- `HilbertSymbol`(M370F)/`HilbertSymbolReciprocity`(M410F)/`TameSymbol`(M375F): 抽象 galH1Module コホモロジー上のカップ積記号、または**従順**付値記号 v(a)w(b)−v(b)w(a)。**野性記号・非退化性・Steinberg は外部仮説/後続**と各自申告。実 ζ₃∈O_{L₂} を食わせる橋は無い（q9kd 正直限定 1 が「galH1Module 接続なし・M 体化後の後続」と明言）。
- `LocalBrauer`/`BrauerInvariant`/`ReciprocityBrauerCompat`/`ReciprocityNondegenerate`: 巡回代数の Hasse 不変量 inv=v(a)/n、**不分岐次数 n・分裂表示模型**。野性・実 Gal は後続。
- `RamifiedReciprocity`(M107): レベル 1 分岐相互律 [u]λ=ω(ū)λ だが**Lubin–Tate/Eisenstein 模型環 eisRing 上**であり実 O_M=q3kRing ではない。

**判定**: 実 Gal(M/L₂) を主語とする分岐 LCFT（crux 込み）は既存群と主語が重ならず、二重計上リスクは低い。**逆にそれは「ゼロから重い」ことを意味する**——足場は無く、正の半分（§2.1）だけでは監査 0。

---

## 3. 欠けている厳密なイディオムの局在化と de-risk 見積り

**B2 crux を建てるのに欠けている厳密なイディオムは 3 つ**（いずれも v_M / 高次単数フィルトレーションを前提とする）:

1. **実高次単数フィルトレーション U^(i)_M = 1+π₉^i·O_M を一般単数上の可除性形式述語として建てる**。q9wr は特定元（σπ₉−π₉）の π₉ 可除性しか持たず（正直限定 1・2）、一般 x∈U₃ の「x−1 の π₉ 可除位数」を扱う述語が無い。最低限 `q9uf_U i x := q9wrDvd (π₉^i) (x−1)` と、その乗法群フィルトレーション性（U^(i)·U^(j)⊆U^(min)、U^(i)/U^(i+1) の graded 構造）が要る。
2. **ノルムの graded 挙動（核心の新イディオム）**: 全分岐 degree p=3 で N: gr^i(U_M) → gr^{?}(U_{L₂}) が誘導する写像の計算——底の graded piece で x↦x^p（Frobenius 型）・中間で trace 型。これは N の**加法的近似** N(1+π₉^i a) ≡ 1 + (項) mod π₉^{i+1} を要し、q3kNormBase の 3 次多項式を π₉-adic に展開して主要項を抽出する必要がある。**これが未発明のイディオム**（tier-L 案件）で、v_M による位数の制御が無いと定式化できない。
3. **余核の同定** U₂/N(U₃) ≅ μ₃（位数 3）と [ζ₃] が非自明類、すなわち ζ₃∉N(U₃)＝(ζ₃,ζ₃)_3≠1。1・2 が建てば有限計算で閉じるが、1・2 が本丸。

**代替ルート（同じ壁）**: rec: L₂^×→Gal(M/L₂) を Lubin–Tate で直接建てる案は、実 O_{L₂} 上の形式群と v_M を要し（既存 LubinTate は p=2 模型 eisRing 上）、やはり v_M の壁。

**de-risk spike の見積り**: (a) tier-L 詳細化 1 枠で「実 U^(i) 可除性形式フィルトレーション」と「ノルム graded 補題」の設計分解（項の抽出戦略・π₉-adic 展開の choice-free 化・termination）を行い、(b) その上に実装 1–2 枠（U^(i) 建設 opus + graded/crux fable）。**合計 2–3 ラウンド**（v_M の部分建設が別途要るなら +1）。**B2 は確定的に multi-round item**。

---

## 4. より安い genuine な B 前進との比較（重要）— 次の一手の選定

### 4.1 表示算術（`compute_complete_pct.py`・分母 Σw(B)=100・banker's）

現在 Σ_B=26.5→**26**。1 手あたりの表示:

| 変更 | 分子増 | Σ_B | 表示 | genuine 1 ラウンド可否（正直） |
|---|---|---|---|---|
| **B2 0→0.15** | +3.0 | 29.5 | 30 | **不可**（crux 未達で監査 0 維持・§1–§3） |
| B1 0.60→0.65 (w20) | +1.0 | 27.5 | **28** | 実 v_M は multi-round（下記）。値群側 P3 は薄い |
| B1 0.60→0.70 | +2.0 | 28.5 | 28 | 同上（0.65 も 0.70 も表示 28・banker's） |
| B5 0.5→0.60 (w15) | +1.5 | 28.0 | 28 | **未精査**（下記・別スコープ要） |
| B5 0.5→0.65 | +2.25 | 28.75 | 29 | 同上 |
| B3 0.20→0.30 (w20) | +2.0 | 28.5 | 28 | 残件精査要（q9ac 直後で薄い可能性） |
| B4 0.10→0.20 (w15) | +1.5 | 28.0 | 28 | 内容退化的（先行 §4 で「薄い」判定済み） |
| B6 0.15→0.25 (w10) | +1.0 | 27.5 | 28 | 実 L₂^×/(L₂^×)³ 全体構造は真だが有界 |

**観察**: どの genuine な +1.0〜+2.0 も表示は横並びで **26→28**。表示効率では差がつかない。差は「genuine か・de-risk 価値があるか」で決まる。

### 4.2 各代替の正直な評価

- **(i) B1 深化（実 v_M / 塔 M_n, w20）**: 実 v_M: O_M→ℕ の**全域関数**建設は、O_M が三つ組環で DVR の while 抽出が無く、一般元の π₉ 冪抽出の termination を choice-free に要する——q9wr 正直限定 1 が明示的に見送った対象で、**それ自体 multi-round**。ただし B1 に**真で小さい**前進はある: §2.1 の P3（N が L₂ 一様化子を打つ＝分岐相互律の値群側 v_{L₂}(N(π₉))=1）を「ノルム両立フィルトレーション」として B1 の分岐データに追記する。`q9wr_normBase_pi9`＋`q9wr_qnorm_zeta_sub` で 9 割完成済みゆえ 1 ラウンド確実だが**寄与は +0.05 未満**（表示は 26 据置の見込み）。genuine だが薄い。
- **(ii) B5 深化（大域 CFT/積公式, w15, 0.5）**: 重み 15 で B2 に次ぐ残枠。ただし**本スコープでは B5 の実資産本体を精査していない**——1 ラウンド genuine 前進が実在するか padding かを断定できない。**別スコープ（B5 専用の詳細化）を経てから**推奨すべき。ここで盲目的に推さない（正直）。
- **(iii) B3 深化（Artin 導手, w20, 0.20）/ B6 深化（Kummer, w10, 0.15）**: B3 は q9ac が直近で 0.20 に上げたばかりで、合成 different d(M/ℚ₃)（推移公式）・全指標 Swan など残件はあるが薄い可能性。B6 は L₂^×/(L₂^×)³ 全体構造（現状 ⟨[ζ₃]⟩ 部分のみ）が真の残件で 1 ラウンド genuine 可能だが w10 で有界（0.15→0.25 で +1.0）。

### 4.3 推奨（次の 1 手）

**第一推奨: B2 の de-risk 詳細化を 1 枠（tier-L / fable・design-only）**。理由: 残る最大の weight×gap は B2（20×1.0）に集中し、§4.1 の通り他の genuine 前進は全て表示 26→28 で横並び・かつ薄い。B2 を multi-round と確定した以上、最短の価値は「§3 の実 U^(i) フィルトレーション＋ノルム graded 補題」を段階分解する詳細化ラウンドで**w20 を解錠する設計を先に作る**こと。今ラウンドは **complete_pct 0 前進（骨格でなく B2 本丸の設計先行）**と正直申告する。

**併走候補（表示を動かしたい場合のみ）**: §4.2(i) の B1 値群側 P3 か、§4.2(iii) の B6 の L₂^×/(L₂^×)³ 構造。いずれも genuine だが小（表示 26→26 か 26→28 の下振れ）。**B2 の正の半分（P1–P5）だけを B2 モジュールとして出すのは §2.1 の通り却下（水増し）**。

---

## 5. 三行結論

(a) crux「ζ₃∉N(M^×)」は**今ラウンドでは割れない・確定的に multi-round（2–3 ラウンド）**——codebase 唯一の付値的判別器 φ=q3rqNorm∘q3kNormBase が `q3rq_zeta_norm`（norm ζ₃=1）により ζ₃ を 1 と潰し、U6 の「3·s 非単数」エンジンが発火せず、mod-m 還元も level 1 で空振りし、障害は未建設の高次単数フィルトレーション U^(i)（v_M 依存）の中にある。
(b) 推奨する次の B モジュールは、B2 status を薄く動かすのではなく **B2 de-risk 詳細化 1 枠（tier-L/fable・design-only・今ラウンド表示 0 前進で w20 を解錠する「実 U^(i) 可除性フィルトレーション＋ノルム graded 補題」の段階分解）**——表示を動かしたい場合の genuine な代替は B1 値群側（+<0.05）か B6 の L₂^×/(L₂^×)³（0.15→0.25, +1.0, 表示 26→28）だが、いずれも B2 の weight×gap には及ばない。
(c) 最大のリスクは**閾値ショッピング**——B2 の正の半分（ノルム乗法性・N(π₉)=ζ₃−1・値群側全射）は真だが crux を含まず、それを B2 status に化けさせれば §2/§3 違反の水増しであり、監査は crux 不在で 0 を維持すべき。

---

## 読了した .lean 本体（本書の根拠・全て def/theorem 本文まで確認）

- `/home/user/onepagers/iut-lean-verification/IUT/Q3KummerCubic.lean`（全 1033 行・q3kNormBase / q3k_normBase_mul / q3kWt / q3k_norm_eq / q3kSigma / q3kUnitMem / q3kInv / q3kU / q9ps_normBase_embed 関連まで）
- `/home/user/onepagers/iut-lean-verification/IUT/Q3KummerDualityReal.lean`（全 593 行・q9kdG / q9kdAct / q9kdMu3 / q9kdChi / q9kd_class_nontrivial / q9kd_pairing_* / q9kd_hom_complete / q9kd_kummer_iso）
- `/home/user/onepagers/iut-lean-verification/IUT/Q3WildRamFiltrationReal.lean`（全 485 行・q9wr_normBase_pi9 / q9wr_qnorm_zeta_sub / q9wr_three_mul_not_unit / q9wr_G3_trivial の U6 イディオム本体 / q9wr_pi9_cancel / q9wr_pi3_cancel / q9wr_different）
- `/home/user/onepagers/iut-lean-verification/IUT/Q3KummerPiSplit.lean`（q9ps_normBase_embed 本体・N(embed n)=n³）
- `/home/user/onepagers/iut-lean-verification/IUT/Q3RamifiedQuadratic.lean`（ヘッダ＋ q3rqNorm / q3rq_zeta_norm : q3rqNorm ζ₃=1 / q3rqU / q3rqLx=ℤ×U₂ / q3rq_ramification / q3rq_lambda_sq＝3=−λ²）
- `/home/user/onepagers/iut-lean-verification/IUT/Q3LocalField.lean`・`Q3RatEmbed.lean`（ヘッダ＋正直限定——v_M は関係形のみ・total inverse 無し・一般元付値の choice-free 不能を確認）
- B2 側既存モジュールのヘッダ本体（二重計上判定の根拠）: `NormGroup.lean`・`LocalReciprocity.lean`・`FullReciprocity.lean`・`LubinTateReciprocity.lean`・`LubinTateNormGroup.lean`・`HilbertSymbol.lean`・`HilbertSymbolReciprocity.lean`・`TameSymbol.lean`・`LocalBrauer.lean`・`BrauerInvariant.lean`・`ReciprocityBrauerCompat.lean`・`ReciprocityNondegenerate.lean`・`RamifiedReciprocity.lean`
- 台帳: `target_ledger.json`（柱B 全 6 項目 weight/status）・先行スコープ `audit/pillar-B-cft-conductor-hasseArf-scope-2026-07-11.md` §5（B2 見送り判定）

---

## ★訂正（2026-07-11・q9nf de-risk スパイクによる）— 本文の crux「ζ₃∉N(M^×)」は数学的に誤り

de-risk スパイク `IUT/Q3NormFiltrationSpike.lean`（q9nf）が本 scope の中心的主張を**反証**した。正直に記録する（§4・設計文書の誤りは消さず訂正で上書きする）。

- **`q9nf_zeta_is_norm : ∃ x, q3kUnitMem x ∧ q3kNormBase x = q3rqZeta`**（証明 `⟨q3kZeta9, q9tl_zeta9_unit, q9tl_normBase_zeta9⟩`・axioms=[propext,Quot.sound]）。すなわち **ζ₃ は N(M^×) の元である**（witness ζ₉: N(ζ₉)=ζ₉·(ζ₃ζ₉)·(ζ₃²ζ₉)=ζ₉³=ζ₃）。しかもこれを支える `q9tl_normBase_zeta9`/`q9tl_zeta9_unit` は本 scope 作成時点で**既にコードベースに存在**していた。
- 本文 §1 の誤りの根源: **Kummer ペアリング(σ,[ζ₃])≠1 と Hilbert 記号(ζ₃,ζ₃)₃ を混同**した。実際 (ζ₃,ζ₃)₃=(ζ₃,−1)₃⁻¹=1（−1 は立方）で ζ₃ は本当にノルム。ゆえに「ζ₃∉N を証明する」B2 実装は**偽命題を主語にする**もので、着工していれば §3(toy 主語)違反級の誤りになっていた。スパイクの敵対的検証がこれを未然に捕捉した。

### de-risk の正味成果（machinery は本物・cracked）
- U^(i)=1+π₉^i·O_M フィルトレーション＋**ノルム graded behavior** `q9nf_norm_expand`（embed N(1+t)=1+Tr(t)+E₂(t)+embed N(t)）・`q9nf_norm_filt`（N(U^(i))⊆U^(i+1)・1≤i≤5、i≤5 の cap は粗い座標 trace 界＝v_M 不在の正直な限界）を choice-free に実証。B2 の「未発明イディオム」の半分は retired。
- ζ₃ の正確な位置 `q9nf_zeta_U3`/`q9nf_zeta_not_U4`（embed ζ₃∈U^(3)∖U^(4)）・trace は π₉⁶ 可除で level<6 の全 graded piece 上ゼロ写像（`q9nf_trace_kill`）。

### 正しい retarget（後続 B2 の真の crux）
真の非ノルムは graded level 6（上付き break t=2 ⇔ π₉⁶）に置く。候補 **4=1+3∉N(M^×)**（Artin: N_{L₂/ℚ₃}(4)=16≡7 mod 9・ζ₉↦ζ₉⁴≠id）。位置は `q9nf_retarget_witness`/`q9nf_retarget_sharp`（1+3∈U^(6)∖U^(7)）で確定。**B2 は実装前に crux を 4∉N へ retarget する再設計ラウンドが必須**——残る hard core は level-6 graded cokernel 同定（genuine な新規仕事）。
