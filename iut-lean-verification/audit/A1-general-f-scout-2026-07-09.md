# A1 一般 f スカウト — 一般既約 f の ℚ[x]/(f) 実体化が A1→1 と A3 実 Galois 塔に効くか

日付: 2026-07-09 / 契機: A1 が 2026-07-09 に **0.5→0.7**（実 ℚ[x]/(x³−2)＝ℚ(∛2) の真の商環体化、
`audit/reaudit-A-cbrt2-2026-07-09.md`）へ昇格済み。並行して一般既約 f への拡張
（`PolyBezoutQ.lean` の `hlead_oracle` を ℚ で討ち・既約⟹gcd 単元 で hBez を埋める）が進行中
（`plo_lead_oracle_Q` 着地済み・`PolyDivisibility`(pdv)・`PolyIrreducible`(pir) 準備中）。
本文書は**新規 .md 1 個のみ**（コード・共有ファイル不可）。読んだファイル: `IUT/CbrtTwoField.lean`・
`IUT/CbrtBezoutChain.lean`・`IUT/PolyBezoutQ.lean`・`IUT/PolyLeadOracleQ.lean`・
`IUT/SimpleExtension.lean`・`IUT/RatZeroDecide.lean`・`IUT/QuadraticField.lean`・
`IUT/CyclotomicFieldQ3.lean`・`IUT/FieldAutGroup.lean`・`IUT/GaloisFundamental.lean`・
`IUT/Profinite.lean`・`IUT/TowerLaw.lean`・`IUT/PrimitiveElement.lean`・`IUT/CyclotomicPrimePower.lean`・
`target_ledger.json`・`audit/A1-machinery-scout-2026-07-09.md`・`audit/reaudit-A-cbrt2-2026-07-09.md`。

---

## 0. 結論（先出し）

一般既約 f への拡張は**A1→1 への必要条件だが十分条件ではない**。埋まるのは「単一 f=x³−2 のみ」
という限定の**一部**（hBez の一般エンジンは `PolyBezoutQ`+`PolyLeadOracleQ` で既に実 ℚ 上完成）
だけで、既約性そのものの判定・全域 inv・基底/次数理論の 3 つの下位ギャップは一般 f 化それ自体では
埋まらない。A3 実 G_K への波及は「材料は理論上揃っている」が、円分塔の実体化（Φ_{p^n} の係数列・
既約性・塔の制限埋め込み）は**この 1 ラウンドの範囲を大きく超える複数 Wave 規模の新規建設**であり、
`InverseSystem`/`limitGrp`（`Profinite.lean`）自体は完全に汎用で流用可能というのが唯一の朗報。

---

## 1. A1→1 に何が要るか — 棚卸し表

| 部品 | 現状(実/未) | 一般 f 対応で埋まるか | 残るか |
|---|---|---|---|
| **(a) 一般既約 f の hBez 本体（gcd 計算エンジン）** | **実**。`PolyBezoutQ.lean`（M270F）の `pbzBezout`/`pbzBezout_one_of_unit` は任意の `f,g : PS R`（g の先頭係数≠0）に対し gcd と Bezout `gg=s·f+t·g ∧ gg∣f ∧ gg∣g` を拡張ユークリッド互除法で完全構成（choice 不使用）。唯一の honest 仮説だった `hlead_oracle` は `IUT/PolyLeadOracleQ.lean`（`plo_lead_oracle_Q`、未コミットだが着地済み）が実 ℚ 上 `rzd_zero_or_ne`（choice-free）で**充足済み**。`pbzBezoutQ` は実 ℚ[X] 上そのまま呼べる。 | **大きく埋まる**。gcd/Bezout の計算自体は f の既約性を問わず任意の f,g に対して既に本物。 | 「f 既約 ⟹ gcd(f,a) は単元（非零定数）」の導出（`pir` 未着地）、および PS 版 Bezout（`pbzBezoutQ` の出力、`PS ratRing` の元）を `Poly ratRing`（`IsPoly` 付き Subtype）へ梱包する plumbing（`cbc_bezout` が x³−2 で手作業実施したパターンの汎用化、`pdv`/`pir` 未着地）。 |
| **(b) 全域 inv 付き IUTField インスタンス（∃形からの昇格）** | **未**。`SimpleFieldExt.has_inverses`・`ctf_has_inverses` は `∀x≠0, ∃y, x·y=1` の Prop-∃ 形。`IUTField` は**全域函数** `inv : carrier → carrier` を要求する構造体（`FieldAutGroup.lean`/`QuadraticField.lean`/`CyclotomicFieldQ3.lean` の `qdfField`/`cq3Field` は全て `inv` を明示式で持つ全域実装）。 | **埋まらない**。f を一般化しても ∃→∀ の壁は不変。 | Lean の Prop-∃ から Type 世界の函数 `inv` を各 x ごとに引き出すには、通常 `Classical.choice`（本規約が禁じる新規 choice）を要する。回避するには `SimpleExtData.bezout`（およびそれを支える `pbzExtGcdAux` 等）を **Prop `∃` でなく `Σ'`（データを運ぶ構成的存在）で最初から書き直す**大規模リファクタが要る（`field_division_exists` 以下の階層を貫通）。単一 f 版（`ctfField`）でも一般 f 版でも**共通の未解決ブロッカー**であり、一般 f 化それ自体はこの壁を動かさない。 |
| **(c) {1,α,…,α^{n-1}} 基底・次数=[K:ℚ] の理論** | **部分的に実**。`IUT/TowerLaw.lean`（M281F）が `TowerLawModule`/`TowerLawBasis`/`towerLawDegree`/塔法則 `[M:K]=[M:L]·[L:K]` を**抽象的に**完全証明済み（基底は witness として受け取る）。しかしこれと `SimpleExtension`/`genExtData` の K[X]/(f) を結ぶ橋（{1,α,…,α^{deg-1}} が実際に spans+独立の基底であることの証明）は**ゼロ**。`MinimalPolynomial.lean` も「K(α)≅K[X]/(m) の同型構成そのものは範囲外」と明記。 | **部分的に埋まりやすくなる**。一般 f（deg = n パラメータ）にしておけば、橋渡しの証明を deg 固定でなく一般 n で 1 回書けば済む（単一 f 版より効率がよい）。 | 橋渡し自体は新規証明が要る: (i) spans — 多項式除法（`field_division_exists`）で任意元を deg<n の剰余へ落とし、その係数列を K-結合として読む。(ii) 独立性 — `simpleExt_const_mul_zero`（M269F-6、定数=bound 1 の場合の次数論法）を bound=n（deg f）へ一般化。既存部品の組み合わせなので**射程内だが未着手**。「deg = [K:ℚ] そのもの（これ以上下がらない最小性）」は既約性と相関する一段上の主張でさらに重い。 |

**A1→1 の見込み（保守的）**: (a) の一般エンジンが `pdv`/`pir`/plumbing で閉じれば、**一般 f 用コンストラクタ `genExtData`/`genField`**（既約性を仮説として受け取る）は本物に組める。これは「単一 f=x³−2 のみ」という限定の**字面**を消すが、(b)(c) が手つかずのままなら「体としての完全性」「基底/次数理論」という**別の限定**が残るため、A1 が 1.0 に届くことはない。§3 で述べる通り、一般コンストラクタ単体（具体例の追加なし）が 0.7 を超えて動くかどうかも不確実——監査の過去実績（後述）に照らすと**動かない可能性が高い**。(b) は choice か大規模リファクタ、(c) は橋渡し新規証明が要る独立ギャップであり、いずれも本ラウンドの「一般 f 対応」作業の範囲外。

---

## 2. A3 実 G_K への波及

### 2.1 既存で使える部品（汎用・手つかずで流用可）

| 部品 | ファイル | 汎用性 |
|---|---|---|
| `InverseSystem`/`limitGrp`/`limitProj`/`limit_universal` | `IUT/Profinite.lean`（M13） | **完全汎用**。任意の有向添字上の `Grp` の族＋推移射があれば逆極限が取れる。`zmodSystem`/`zhat`（ℤ→ℤ/n の塔）が実例テンプレート。 |
| `fieldAutGroup`/`FieldExtension`/`galoisSubgroup`/`galoisGroupGrp` | `IUT/FieldAutGroup.lean`（M271F） | **完全汎用**。任意の `IUTField` 拡大に対し Gal(L/K) を `Subgroup (fieldAutGroup L)` として構成。 |
| Galois 群の**完全決定**の計算パターン（σ(√D)=±√D の場合分け→σ=id∨σ=conj） | `IUT/QuadraticField.lean`（`qdf_galois_order_two`） | 位数 2 の具体計算だが、**手法**（拡大元の像を成分計算で追い、選言→自己同型の一意決定）は円分塔の各段の制限写像を構成する際の雛形になる。 |
| ℚ(ζ_3) の実体（μ_3 まで） | `IUT/CyclotomicFieldQ3.lean` | carrier=ℚ×ℚ の**手書き次数2実装**（`QuadraticField` と同型の別コピー）。K[X]/(Φ_3) の商環版ではない。 |
| φ(p^k)・分岐指数等の**数値**簿記 | `IUT/CyclotomicPrimePower.lean`（M386F） | **ℕ 算術のみ**。実体（実 ℚ・実商環・実自己同型群）に一切接続していない。次数の整合性チェックには使えるが、それ自体は場・群を構成しない。 |

### 2.2 新規に要るもの（円分塔 ℚ(ζ_{p^n}) を実商環で構成し逆極限へ組む場合）

1. **Φ_{p^n} の係数列 `PS ratRing`** — G2（`A1-machinery-scout` の用語）の一般化。Φ_p(X)=1+X+…+X^{p-1} は書き下しやすいが、Φ_{p^n}(X)=Φ_p(X^{p^{n-1}}) の**係数置換**を `PS`/`Poly` の一般操作として持つ必要がある（現状「多項式の合成」演算はコードベースに見当たらない——要確認だが本スカウトの範囲では未発見）。
2. **Φ_{p^n} の既約性の証明** — 円分多項式の既約性の標準証明は Eisenstein の判定法を X↦X+1 のシフト後に適用する（p 進付値の議論）。`IUT/EisTowerRings.lean` は名前が似るが**局所体のアイゼンシュタイン拡大の環塔**であり、古典的 Eisenstein 既約判定法とは別物（要注意・混同禁止）。既約性証明はゼロから積む数論的に重い新規建設。
3. **塔の制限埋め込み** ℚ(ζ_{p^n}) ↪ ℚ(ζ_{p^{n+1}})（ζ_{p^n} ↦ ζ_{p^{n+1}}^p）と、そこから誘導される**制限準同型** Gal(ℚ(ζ_{p^{n+1}})/ℚ) → Gal(ℚ(ζ_{p^n})/ℚ)（σ ↦ σ|_{ℚ(ζ_{p^n})}、well-defined 性は埋め込みの像の安定性を要する）— 完全に新規。`FieldAutGroup.lean`/`GaloisFundamental.lean` のどこにも「拡大の塔から誘導される制限準同型」の一般機構はない。
4. **`InverseSystem` インスタンス化** — Idx=ℕ（またはべき指数の順序）、G n = `galoisGroupGrp`(cycloExt p n)、t = 上記制限準同型、`t_self`/`t_comp`/`directed` は `zmodSystem` と同型の簿記だが**#3 が先に要る**。
5. 以上が揃って初めて `limitGrp`(cycloSystem) が**実体を持つ**実プロファイナイト Galois 群（≅ ℤ_p^×、A3 の文言「有限 Galois 群の逆極限」を字義通り満たす）になる。現状の `zhat` は ℤ/n という抽象商群の塔であって、**体・自己同型群を一切経由しない**——A3 が要求する「Galois 群」の逆極限としては空虚（今回はじめて場理論と接続する）。

### 2.3 スケール感

上記 1〜4 はそれぞれ CbrtTwoField Wave（9〜12 モジュール規模）に匹敵する新規建設であり、**円分塔全体を狙うのは複数 Wave 規模**（数週間オーダー）。§1 の一般 f コンストラクタ（`genExtData`/`genField`）は**前提条件**（無限塔を x³−2 のように毎段手書き Bezout チェーンで構成するのは非現実的）であって、それ自体は A3 を進めない——A3 側の本丸（#2,#3）はさらに別の新規数学。

より現実的な**次の一歩**は「無限塔」でなく**有限 2 段の塔**（例: ℚ ⊂ ℚ(ζ_3) ⊂ ℚ(ζ_9)、または ℚ(ζ_p) ⊂ ℚ(ζ_{p²})）を Φ_3・Φ_9 を手書きの係数（`CyclotomicFieldQ3.lean` の ζ_3=(−1/2,1/2) 的な具体数値と同精神）で実体化し、**制限準同型 1 本を実際に構成**すること。これは #2,#3 の縮小版だが、#3（制限準同型の well-defined 性）は 2 段でも n 段でも**同じ核心の新規証明**を要するため、「小さいから安い」わけではない——扱う対象を具体数値に絞ることで #1（Φ_{p^n} の一般係数列＋合成演算）だけを回避できる、という意味で現実的。

---

## 3. 既約性を仮説にする方針の妥当性

**方針**: 「∀ 既約 f, ℚ[x]/(f) は体」という**一般コンストラクタ**を作り、既約性テストそのものは仮説として外に出す。

**肯定的な読み**: `TowerLaw.lean` の基底 witness・`GaloisFundamental.lean` の指数一致 witness など、本コードベースには「深い数論的事実を honest 仮説として受け取り、その ⟹ 方向を本物に証明する」設計が多数ある。carrier・環演算・埋め込み・「f 既約 ⟹ 体」の含意が全て本物に証明されるなら、genExtData/genField はこの精神に合致した**本物の一般機構**であり、「既約性の証人」を外部から受け取ること自体は toy 化ではない。

**否定的な読み（監査の過去実績から）**: A1 が長らく 0.5 に据え置かれていた理由は、まさに「`SimpleExtension.lean` の一般機構（`bezout` を仮説として持つ）は既に存在していたが、監査はそれを『実際の商環として構成』と認めなかった」ことだった。0.7 への昇格は**具体 f=x³−2 で `bezout` の仮説を完全に消した**ことに紐づく（`reaudit-A-cbrt2-2026-07-09.md`: 「Bezout は本物に証明済み（仮説引数でない）」を昇格の核心論拠として明記）。genExtData が「既約性」を仮説のまま持つ構造は、旧 `SimpleExtData`（`bezout` を仮説のまま持つ）と**構造的に同型**——仮説の置き場所が「Bezout 直接」から「既約性（より原始的だが依然仮説）」へ一段下がっただけで、未解決の仮説が残る点は変わらない。

**予測**: 監査は一貫して「仮説を残したままの一般機構」には昇格を認めず、「具体対象で仮説を完全に消したこと」を昇格の必要条件としてきた（0.7 の導入自体が「部分ケースの質的超過」という中間評定を初めて認めた保守的な判断だった経緯を踏まえると、さらに保守的な判定が続く可能性が高い）。したがって **一般コンストラクタのみ（新規具体例なし）では A1 は 0.7 から動かない**と予測する。0.7→0.8〜0.9 に進むには、**少なくとも 1 個の新規具体 f（x³−2 と別の次数・別の既約性証明パターン）で既約性の仮説を完全に消した第二の実例**が要ると考えられる。候補として **Φ_3 = x²+x+1** を推す: (i) 既約性証明が二次式なので x³−2 の「有理根なし＋次数3」論法より単純（判別式<0、または「有理根なし ⟺ 既約」を素直に適用できる）、(ii) 次数 2 という**異なる次数**の実例になり「一般次数機構」の実証として x³−2 単独より説得力が増す、(iii) §2 の円分塔の最下段（p=3, n=1）にそのまま転用できる——A1 の第二実例と A3 の塔の初段を同一成果物で兼ねられる。

いずれにせよ (b) 全域 inv・(c) 基底/次数理論が手つかずである限り、この経路が最終的に到達できる上限は 1.0 には遠く、楽観的に見ても 0.8 程度が天井と見る。

---

## 4. 並行スライスとの対応

| 並行スライス | 埋めるギャップ | 対応する棚卸し行 |
|---|---|---|
| **plo_lead_oracle_Q**（`IUT/PolyLeadOracleQ.lean`・着地済み） | `PolyBezoutQ` の `hlead_oracle` を実 ℚ で choice-free に充足。gcd/Bezout エンジンを実 ℚ[X] 上で完成。 | §1(a) の「gcd 計算エンジン」を実で確定。 |
| **PolyDivisibility (pdv)**（未着地） | `pbzDvd` を軸にした割り切れ・真の約元・次数比較の整形（推測: `f が a を割らない` と `gcd(f,a)` の関係の言い換え）。 | §1(a) の plumbing、および §1(c) の次数論法（degree-drop）で使う可能性のある共有部品。 |
| **PolyIrreducible (pir)**（未着地） | 「f 既約」の定義（真の約元なし）と「f 既約 ∧ f∤a ⟹ gcd(f,a) は単元」の導出——`PolyBezoutQ.lean` ヘッダが明記する未解決の接続 (i) そのもの。 | §1(a) の残ギャップを直接埋める。§3 の「既約性を仮説にする方針」の**仮説側の定義**を与える（仮説自体を消すわけではない——「∀f既約, …」の**既約の意味**を固定する層）。 |
| **次 Wave 候補 1: `genExtData`/`genField`** | pdv+pir 着地後、`SimpleExtData.build` を「既約性証人つき任意 f」で回せる一般コンストラクタとして組む（`ctfData`/`ctfField` の一般版）。 | §1(a) の総仕上げ。§3 の「一般コンストラクタ」そのもの。 |
| **次 Wave 候補 2: 具体 2 例目 ℚ(ζ_3)**（f=Φ_3=x²+x+1、genExtData/genField 経由） | §3 で推した第二の具体実例。既約性の完全証明＋商環体化。 | §3 の推奨に対応。§2.3 の円分塔最下段の材料も兼ねる（`CyclotomicFieldQ3.lean` の ℚ×ℚ 版との一致確認は独立監査向けの追加傍証になりうる）。 |
| **(本スカウト範囲外・別途計画が要る)**: (b) Σ' ベースの全域 inv リファクタ、(c) TowerLaw↔SimpleExtension の基底橋渡し、A3 の Φ_{p^n} 一般係数列・既約性・制限準同型 | それぞれ独立の重い新規建設。 | §1(b)(c)・§2.2 全体。詳細化ラウンド（fable tier）で段階分解してから実装枠を割り当てるのが妥当（`CLAUDE.md` の Phase III 運用指針に合致）。 |

---

## 5. 最終判定について

本文書の見積もり（「0.7→0.8 程度が現実的」「Φ_3 が有望な第二実例」「A3 は複数 Wave 規模」等）は
すべて**執筆者（サブエージェント）による予測**であり、`target_ledger.json` の status・
`complete_pct` の確定は**独立監査**（敵対的・自己申告非共有・`#print axioms` 自検）が行う。
本文書は次の実装ラウンドの優先順位付けのための計画資料であり、成果の自己申告ではない。
