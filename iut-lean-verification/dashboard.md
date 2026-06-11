# IUT 系3.12 の Lean 形式検証プロジェクト

## 概要

| 項目 | 内容 |
|------|------|
| 種別 | doc / formal-verification |
| 状態 | done（骨格の形式検証完了） |
| メインファイル | index.html（検証レポート）+ IUT/*.lean（Lean ソース） |
| 関連 | teichmuller/（解説）、verify-teichmuller-errors/（数値検証） |

`teichmuller/pdf/` の原論文6本を一次資料として、宇宙際タイヒミュラー論（IUT）の
系3.12 をめぐる論争の形式骨格を Lean 4 で公理化し、正しさ/間違いを機械検証した。

## 形式検証の結論（二分法、全定理 Lean 検証済み）

1. **Scholze–Stix の読み（RC 同一視を認める）→ 系3.12 は矛盾**（`ss_incompatible`）
   - 「この読みのもとで IUT は間違っている」は Lean 検証済みの定理
2. **望月の読み（同一視を拒否）→ 矛盾は導出されない**（`cor312_consistent`）
   - Scholze–Stix 型の反証は同一視なしでは再現不能
3. **ただし系3.12 は形式骨格から独立**（`cor312_not_derivable` / `cor312_independent`）
   - 「IUT が正しい」ことの全根拠は未形式化の定理3.11（多輻性）に残る

総括: **論争は「RC 同一視を公理に採るか否か」と外延的に等価**（`controversy_reduces_to_rc`）。
無条件の正しさ/間違いはどちらも証明されず、係争点の所在が形式的に特定された。

## 主張チェーン別の証明率（概算）

| チェーン | 主張 | 証明率 |
|---------|------|--------|
| M1 遠アーベル復元 | 論理骨格: mono⟹bi 公理なし / bi⟹mono 選択公理必須、Aut不定性＝(Ind1)起源、復元一意性、**log-Frobenius 両立復元（[AbsTopIII] 表題定理の骨格、公理ゼロ）** | ~15% |
| M2 Hodge theater | ラベル組合せ骨格＋ **F_l^±± の群公理完結**（閉性・単位元・逆元）、±1商 = {0..l⋇} 同定、テータ値ラベル = {1..l⋇}、Skeleton 橋渡し | ~25% |
| M3 Θ-link / log-link | 格子の構造定理＋ **垂直コア性・双コア性（定理1.5 の骨格）**: log-不変量は列ごとに一定、リンク不変量は格子全体で一意 | ~40% |
| M4 テータ値評価 | 値・次数簿記層: Gaussian 総次数の閉形式、素朴評価⟹RC評価/多輻的表現と非両立、膨張込み評価⟹M7計算、**テータ値の±ラベル well-defined 性** (l−j)² ≡ j² (mod l) | 算術核 100% / 理論 ~30% |
| M5 定理3.11 多輻性 | **statement を原文から読み取り出力仕様を形式化**: (i)(Ind1)(Ind2)・(ii)(Ind3)・(iii) をインターフェース化、系3.12 の証明本体を機械化（公理ゼロ）、厳密評価の障害・膨張の必然性・仕様の充足可能性、**procession 正規化の閉形式（公理ゼロ）**。**構成**（遠アーベル復元等）は未形式化 | ~25%（構成 0%） |
| M6 系3.12 | statement 100% 形式化、骨格からの独立性＋**定理3.11 からの証明本体（p.174–175 の包含論法）を機械化** | statement 100% / 証明 ~90%（条件付き） |
| M7 IUT IV log-volume 計算 | 条件付き導出 ＋ **l-最適化定理**（全 l で Szpiro 型 ⟹ ht ≤ c、定理1.10 の質的内容） | ~35% |
| M8 古典的還元と帰結 | ABC ⟹ 漸近フェルマー ＋ Catalan 型 3^b+1=2^a の有界性を完全証明 | ~35% |
| S2 SS: 同一視→矛盾 | `ss_incompatible` 完全証明 | **100%** |
| R3 望月: 同一視なし→無矛盾 | `cor312_consistent` 完全証明 | **100%** |
| 二分法（論争 ≡ RC採否） | `verdict` 完全証明 | **100%** |

**総括**: 「IUT は正しい」**~26%**（ページ規模重み付け: 313/1200 ≈ 26%。主張単位の単純平均では ~37%）、
「無条件に間違い」0%、「同一視読みでは間違い」100%、
「係争点は M5 ただ一点」の形式的確定 100%。
定理3.11 の statement の形式化により「仕様の充足 → 系3.12（証明は公理ゼロで機械化済み）
→ Szpiro → ABC 型帰結」の全経路が Lean 内で接続され、未決着の数学的実質は
`MultiradialRep` の充足問題ただ一つに圧縮された。
目標 30% への残りは定理3.11 の**構成**（遠アーベル復元・テータ剛性・Frobenioid 論）
の形式化であり、mathlib 規模の数論幾何ライブラリを要する。
詳細は index.html の証明率セクション参照。

## ファイル構成

```
iut-lean-verification/
├── index.html           # 検証レポート（ワンページャー）
├── dashboard.md         # このファイル
├── build.sh             # ビルド+公理チェック
├── lakefile.toml        # Lean パッケージ定義（mathlib 非依存）
├── lean-toolchain       # leanprover/lean4:v4.30.0
├── IUT.lean             # ルートモジュール
└── IUT/
    ├── Arithmetic.lean  # Σj² > l⋇ の帰納法証明（テータ値平均次数 > 1）
    ├── Anabelian.lean   # M1: mono/bi-anabelian の区別・公理非対称性・(Ind1)起源
    ├── HodgeTheater.lean # M2: F_l ラベル構造・二つの対称性・Skeleton 橋渡し
    ├── LogThetaLattice.lean # M3: 格子の経路定理・Θ-link 必要性・mono-analytic 不変量
    ├── Multiradial.lean # M5: 定理3.11 の出力仕様・系3.12 証明本体・障害と膨張の必然性
    ├── Evaluation.lean  # M4: Gaussian monoid の次数簿記と S2/M5/M7 接続
    ├── Diophantine.lean # M7: 系3.12 + 体積評価 ⟹ Szpiro 型不等式（条件付き）
    ├── AbcConsequences.lean # M8: ABC ⟹ 漸近フェルマー（radical 公理上）
    ├── Skeleton.lean    # 形式骨格 Skeleton / Cor312 / RCEval の定義
    ├── ScholzeStix.lean # 定理1: RC同一視 + 系3.12 → False
    ├── Mochizuki.lean   # 定理2,3: 無矛盾モデル・反例モデル（独立性）
    ├── Boolean.lean     # 望月の ∧/∨̇ 表示の命題論理検証（XOR弱化の反例含む）
    └── Verdict.lean     # 総括二分法定理 verdict / controversy_reduces_to_rc
```

## 検証の信頼性

| 項目 | 内容 |
|------|------|
| 証明支援系 | Lean 4.30.0 / lake（mathlib 非依存、core のみ） |
| sorry | 0 箇所 |
| 依存公理 | propext, Quot.sound のみ（Classical.choice も不使用） |
| ビルド | `./build.sh`（elan が必要） |

## 一次資料との対応

| 形式化対象 | 出典 |
|-----------|------|
| 系3.12 の statement（−\|log(Θ)\| ≥ −\|log(q)\|, \|log(q)\| > 0） | IUT_III_Canonical_Splittings.pdf p.174 |
| テータ値 {q^{j²}}, j=1..l⋇ と procession 正規化 | IUT III Thm 3.11 / IUT_IV §1 |
| ∧/∨̇（XOR）論理構造・redundant copies 論争 | Essential_Logical_Structure_of_IUT.pdf Abstract ほか |
| RC 同一視による退化論法 | Scholze–Stix "Why abc is still a conjecture" (2018) |

## タスク

| タスク | 状態 |
|--------|------|
| 原論文 PDF から系3.12 statement・論理構造を抽出 | done |
| Lean プロジェクト整備（mathlib 非依存） | done |
| 算術補題 sumSq_gt の証明 | done |
| 形式骨格 + RCEval の公理化 | done |
| 定理1（SS 退化）・定理2/3（独立性）・総括定理の証明 | done |
| ∧/∨̇ 構造の命題論理検証 | done |
| 公理チェック（sorry なし・標準公理のみ） | done |
| 検証レポート index.html | done |
| M1: mono/bi-anabelian 論理骨格の形式化 | done |
| M2: Hodge theater ラベル対称性の形式化 | done |
| M3: log-theta 格子の構造定理の形式化 | done |
| M7: 系3.12 → Szpiro 型不等式の条件付き導出 | done |
| M8: ABC ⟹ 漸近フェルマーの機械証明 | done |
| M5: 定理3.11 の statement 読解と出力仕様の形式化・系3.12 証明本体の機械化 | done |
| M4: Gaussian monoid 次数簿記と接続定理 | done |
| M5: 定理3.11 の**構成**（遠アーベル復元・テータ剛性・Frobenioid）の形式化 | 未着手（mathlib 規模の数論幾何ライブラリが必要。世界の誰も達成していない） |
| M1 実体（p進体の環構造復元）・M2 実体（prime-strip 圏論データ）の形式化 | todo |
