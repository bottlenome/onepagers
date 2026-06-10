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
| M1 遠アーベル復元 | 論理骨格を形式化: mono⟹bi 公理なし / bi⟹mono 選択公理必須の非対称性、Aut不定性＝(Ind1)起源、無矛盾性 | ~10% |
| M2 Hodge theater | ラベル組合せ骨格を形式化: F_l^±± の閉性・推移性、±1商 = {0..l⋇} 同定、テータ値ラベル = {1..l⋇}、Skeleton 橋渡し | ~25% |
| M3 Θ-link / log-link | log-theta 格子の構造定理: 列変化 = Θ-link 通過本数、異正則構造の比較は Θ-link 必須、環構造はリンク不変量になれない | ~30% |
| M4 テータ値評価 | 算術核 Σj² > l⋇ を完全証明 | 算術核 100% / 理論 ~10% |
| M5 定理3.11 多輻性 | 未形式化（最大の係争点と特定） | 0% |
| M6 系3.12 | statement 100% 形式化、骨格からの独立性を証明 | statement 100% / 証明 0% |
| M7 IUT IV log-volume 計算 | 未形式化 | 0% |
| M8 古典的還元と帰結 | ABC ⟹ 漸近フェルマーを完全証明（radical は使用 3 性質のみ公理化） | ~25% |
| S2 SS: 同一視→矛盾 | `ss_incompatible` 完全証明 | **100%** |
| R3 望月: 同一視なし→無矛盾 | `cor312_consistent` 完全証明 | **100%** |
| 二分法（論争 ≡ RC採否） | `verdict` 完全証明 | **100%** |

**総括**: 「IUT は正しい」**~10%**（ページ規模重み付け: 133/1200 ≈ 11% を保守的に丸め）、
「無条件に間違い」0%、「同一視読みでは間違い」100%、
「係争点は M5 ただ一点」の形式的確定 100%。詳細は index.html の証明率セクション参照。

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
| M8: ABC ⟹ 漸近フェルマーの機械証明 | done |
| 定理3.11 内部（多輻的アルゴリズム）の形式化 | 未着手（現状、世界の誰も達成していない） |
| M1 実体（p進体の環構造復元）・M2 実体（prime-strip 圏論データ）の形式化 | todo |
