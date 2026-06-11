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
| M1 遠アーベル復元 | 論理骨格: mono⟹bi 公理なし / bi⟹mono 選択公理必須、Aut不定性＝(Ind1)起源、復元一意性、**log-Frobenius 両立復元（[AbsTopIII] 表題定理の骨格、公理ゼロ）**。＋ **M10 復元アルゴリズムの実装**（IUT/Reconstruction.lean）: 局所体の (p,d) を G^ab の rank profile から復元する手続きを整礎再帰で実装し正当性を証明、`MonoAnabelian` を**選択公理不使用で充足**（M1 の述語の初の実体化） | ~20% |
| M2 Hodge theater | ラベル組合せ骨格＋ **F_l^±± の群公理完結**（閉性・単位元・逆元）、±1商 = {0..l⋇} 同定、テータ値ラベル = {1..l⋇}、Skeleton 橋渡し | ~25% |
| M3 Θ-link / log-link | 格子の構造定理＋ **垂直コア性・双コア性（定理1.5 の骨格）**: log-不変量は列ごとに一定、リンク不変量は格子全体で一意 | ~40% |
| M4 テータ値評価 | 値・次数簿記層: Gaussian 総次数の閉形式、素朴評価⟹RC評価/多輻的表現と非両立、膨張込み評価⟹M7計算、**テータ値の±ラベル well-defined 性** (l−j)² ≡ j² (mod l)。＋ **M11 cyclotomic rigidity の骨格**（IUT/EtaleTheta.lean、[EtTh] Cor 2.19）: テータ群（Heisenberg 群）の交換子＝シンプレクティック形式がシクロトームの標準生成元を指定し、**テータ切断の不定性が交換子で完全相殺**されることを公理化ゼロの完全証明で機械検証（裸のシクロトームの ±1 不定性との対比込み） | 算術核 100% / 理論 ~35% |
| M5 定理3.11 多輻性 | **statement を原文から読み取り出力仕様を形式化**: (i)(Ind1)(Ind2)・(ii)(Ind3)・(iii) をインターフェース化、系3.12 の証明本体を機械化（公理ゼロ）、厳密評価の障害・膨張の必然性・仕様の充足可能性、**procession 正規化の閉形式（公理ゼロ）**。＋ **M12 Frobenioid 次数層**（IUT/Frobenioid.lean、[FrdI/II]）: deg(0)=0 の導出・Frobenius 合成則・**Frobenius-like 非可逆性**・Gaussian 束の次数公式（M4 接続）・**次数＝log-volume 両立 ⟹ `vol_q` の供給**（定理3.11 (i)(c) の骨格、M5 接続）。構成の実体は未形式化 | ~28%（構成は土台のみ） |
| M6 系3.12 | statement 100% 形式化、骨格からの独立性＋**定理3.11 からの証明本体（p.174–175 の包含論法）を機械化** | statement 100% / 証明 ~90%（条件付き） |
| M7 IUT IV log-volume 計算 | 条件付き導出 ＋ **l-最適化定理**（全 l で Szpiro 型 ⟹ ht ≤ c、定理1.10 の質的内容） | ~35% |
| M8 古典的還元と帰結 | ABC ⟹ 漸近フェルマー ＋ Catalan 型 3^b+1=2^a の有界性を完全証明 | ~35% |
| M9 テンパード・数論的基本群（土台） | **基本群理論の骨格を形式化**: 完全列 1→Δ→Π→G→1 の正規性・**外ガロア作用の well-defined 性**・slim ⟹ 共役忠実・切断の一意分解（公理ゼロ）、**テータ被覆のデッキ群 ℤ の非有限性**、差分方程式 ⟹ 指数 j² の一意性、**有限商はテータ簿記 q^{j²} を必ず潰す ⟹ π₁^temp の必然性**（M1/M4/M5 の土台） | ~20% |
| M13 副有限群（基盤インフラ） | **逆極限理論の実構成**: 商群（Quot 構成・分離性・普遍性）、逆系と逆極限群・**逆極限の普遍性**、**ẑ = lim ℤ/n の実構成**、完備化 ℤ→ẑ の単射性（残余有限性）、各有限レベルがテータ簿記を潰すことの実例化（M9 接続）。全構成・公理化なし | 実体構成 |
| M14 Galois 圏・étale π₁（基盤インフラ） | **ファイバー関手の復元機構の完全証明**: 正則作用の同変自己写像 = 右移動のみ（Aut(F) ≅ G、公理ゼロ）、π₁^ét の有限レベルへの作用が**自然変換**であること（M13 接続）、反変 Galois 接続の単位・余単位・閉包冪等性。SGA1 主定理（圏同値）は未形式化 | 実体構成 |
| M15 位相付き副有限群（基盤インフラ） | **位相の自前建設**: 位相空間・生成位相（最小性込み）・直積位相・連続性の準開基検査を構成し、**逆極限群が位相群**（積・逆元連続）であること、射影核が**開部分群**で**単位元の開近傍基**をなすこと（近傍基定理）、ẑ → ℤ/n の全射性（構成的）を完全証明 | 実体構成 |
| M16 SGA1 主定理の核心（基盤インフラ） | **被覆の分類定理**: 剰余類作用 G/H の構成、軌道分解と**軌道-安定化定理**（全ての連結被覆 ≅ G/H、主定理対象側）、**Galois 対応の実現**（基点付き同変写像 G/H → G/K の存在 ⟺ H ⊆ K、主定理射側）、SGA1 の連続作用条件（安定化群 ⊇ 開部分群、M15 接続）。圏同値の関手的パッケージングは未形式化 | 実体構成 |
| S2 SS: 同一視→矛盾 | `ss_incompatible` 完全証明 | **100%** |
| R3 望月: 同一視なし→無矛盾 | `cor312_consistent` 完全証明 | **100%** |
| 二分法（論争 ≡ RC採否） | `verdict` 完全証明 | **100%** |

**総括**: 「IUT は正しい」**~28%**（ページ規模重み付け: 364/1300 ≈ 28%。主張単位の単純平均では ~36%）、
「無条件に間違い」0%、「同一視読みでは間違い」100%、
「係争点は M5 ただ一点」の形式的確定 100%。
定理3.11 の statement の形式化により「仕様の充足 → 系3.12（証明は公理ゼロで機械化済み）
→ Szpiro → ABC 型帰結」の全経路が Lean 内で接続され、未決着の数学的実質は
`MultiradialRep` の充足問題ただ一つに圧縮された。
issue #29 の4基盤理論はすべて骨格を形式化済み: **基本群（M9）・遠アーベル復元
アルゴリズム（M10、選択公理不使用）・cyclotomic rigidity（M11、公理化ゼロ）・
Frobenioid 次数層（M12）**。残部（環構造復元の本体・p進テータ関数の関数等式・
Frobenioid の圏論的実体）は mathlib 規模の数論幾何ライブラリを要する。
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
    ├── FundamentalGroup.lean # M9: テンパード・数論的基本群の骨格（完全列・外作用・テータ被覆 ℤ・有限商崩壊）
    ├── Reconstruction.lean # M10: 局所体 (p,d) 復元アルゴリズム実装・MonoAnabelian 充足（選択公理不使用）
    ├── EtaleTheta.lean  # M11: cyclotomic rigidity（テータ群交換子⟹シクロトーム剛性、公理化ゼロ）
    ├── Frobenioid.lean  # M12: Frobenioid 次数層（Frobenius 非可逆性・次数＝log-volume・vol_q 供給）
    ├── Profinite.lean   # M13: 商群・逆極限・ẑ = lim ℤ/n の実構成（普遍性・残余有限性）
    ├── GaloisCategory.lean # M14: ファイバー関手復元機構・π₁^ét の自然作用・Galois 接続
    ├── Topology.lean    # M15: 位相の自前建設・逆極限は位相群・射影核 = 開近傍基
    ├── SGA1.lean        # M16: 軌道-安定化定理・Galois 対応の実現・連続作用条件
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
| M9: テンパード基本群・数論的基本群の理論の骨格形式化（issue #29 の土台項目） | done |
| M10: 遠アーベル復元アルゴリズムの実装と MonoAnabelian 充足（issue #29 項目1の骨格） | done（選択公理不使用） |
| M11: エタールテータの cyclotomic rigidity の機構（issue #29 項目2の骨格） | done（公理化ゼロの完全証明） |
| M12: Frobenioid 次数層と vol_q 供給（issue #29 項目3の骨格） | done |
| M5: 定理3.11 の**構成**の完全形式化 | 4基盤の骨格（M9–M12）は done。残り（環構造復元の本体・p進テータ関数の関数等式・Frobenioid の圏論的実体・実際の数体での充足）は mathlib 規模の数論幾何ライブラリが必要。世界の誰も達成していない |
| M13: 副有限群（商群・逆極限・ẑ の実構成）— 実体建設フェーズ第1弾 | done（公理化なしの実構成） |
| M14: Galois 圏・étale π₁ のファイバー関手機構 — 実体建設フェーズ第2弾 | done（Aut(F) ≅ G は公理ゼロ） |
| M15: 位相付き副有限群（位相群性・開部分群・近傍基定理） — 実体建設フェーズ第3弾 | done（Classical.choice ゼロ） |
| M16: SGA1 主定理の核心（軌道-安定化定理・Galois 対応の実現・連続作用条件） — 実体建設フェーズ第4弾 | done（Classical.choice ゼロ） |
| 実体建設の続き: 有限性の本格的定義・コンパクト性・SGA1 の圏論的パッケージング（圏同値） | todo |
| 実体建設の続き: ℤ_p の構成 → 局所体の構造論 → 局所類体論（M10 の公理化フィールドの実証明化） | todo |
| M2 実体（prime-strip 圏論データ）の形式化 | todo |
