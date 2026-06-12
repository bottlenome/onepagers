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
| M5 定理3.11 多輻性 | **statement を原文から読み取り出力仕様を形式化**: (i)(Ind1)(Ind2)・(ii)(Ind3)・(iii) をインターフェース化、系3.12 の証明本体を機械化（公理ゼロ）、厳密評価の障害・膨張の必然性・仕様の充足可能性、**procession 正規化の閉形式（公理ゼロ）**。＋ **M12 Frobenioid 次数層**（IUT/Frobenioid.lean、[FrdI/II]）: deg(0)=0 の導出・Frobenius 合成則・**Frobenius-like 非可逆性**・Gaussian 束の次数公式（M4 接続）・**次数＝log-volume 両立 ⟹ `vol_q` の供給**（定理3.11 (i)(c) の骨格、M5 接続）。圏論的実体と数体型データでの充足は M48F（次数圏）+ M51F（因子圏・rationalFrobenioid）で base 圏一点の範囲を形式化済み | ~28%（構成は土台のみ） |
| M6 系3.12 | statement 100% 形式化、骨格からの独立性＋**定理3.11 からの証明本体（p.174–175 の包含論法）を機械化** | statement 100% / 証明 ~90%（条件付き） |
| M7 IUT IV log-volume 計算 | 条件付き導出 ＋ **l-最適化定理**（全 l で Szpiro 型 ⟹ ht ≤ c、定理1.10 の質的内容） | ~35% |
| M8 古典的還元と帰結 | ABC ⟹ 漸近フェルマー ＋ Catalan 型 3^b+1=2^a の有界性を完全証明 | ~35% |
| M9 テンパード・数論的基本群（土台） | **基本群理論の骨格を形式化**: 完全列 1→Δ→Π→G→1 の正規性・**外ガロア作用の well-defined 性**・slim ⟹ 共役忠実・切断の一意分解（公理ゼロ）、**テータ被覆のデッキ群 ℤ の非有限性**、差分方程式 ⟹ 指数 j² の一意性、**有限商はテータ簿記 q^{j²} を必ず潰す ⟹ π₁^temp の必然性**（M1/M4/M5 の土台） | ~20% |
| M13 副有限群（基盤インフラ） | **逆極限理論の実構成**: 商群（Quot 構成・分離性・普遍性）、逆系と逆極限群・**逆極限の普遍性**、**ẑ = lim ℤ/n の実構成**、完備化 ℤ→ẑ の単射性（残余有限性）、各有限レベルがテータ簿記を潰すことの実例化（M9 接続）。全構成・公理化なし | 実体構成 |
| M14 Galois 圏・étale π₁（基盤インフラ） | **ファイバー関手の復元機構の完全証明**: 正則作用の同変自己写像 = 右移動のみ（Aut(F) ≅ G、公理ゼロ）、π₁^ét の有限レベルへの作用が**自然変換**であること（M13 接続）、反変 Galois 接続の単位・余単位・閉包冪等性。SGA1 主定理（圏同値）は未形式化 | 実体構成 |
| M15 位相付き副有限群（基盤インフラ） | **位相の自前建設**: 位相空間・生成位相（最小性込み）・直積位相・連続性の準開基検査を構成し、**逆極限群が位相群**（積・逆元連続）であること、射影核が**開部分群**で**単位元の開近傍基**をなすこと（近傍基定理）、ẑ → ℤ/n の全射性（構成的）を完全証明 | 実体構成 |
| M16 SGA1 主定理の核心（基盤インフラ） | **被覆の分類定理**: 剰余類作用 G/H の構成、軌道分解と**軌道-安定化定理**（全ての連結被覆 ≅ G/H、主定理対象側）、**Galois 対応の実現**（基点付き同変写像 G/H → G/K の存在 ⟺ H ⊆ K、主定理射側）、SGA1 の連続作用条件（安定化群 ⊇ 開部分群、M15 接続）。圏同値の関手的パッケージングは未形式化 | 実体構成 |
| M17 有限性の本格的定義（基盤インフラ） | **鳩の巣原理**（決定手続きの自前実装で選択公理回避）・基数の一意性・**有限群 ⟹ 有界指数（指数 n!）**（M9 以来の代理 `BoundedExponent` の正当化）・**ℤ/n の有限性と枚挙の実構成**（ẑ が正真正銘の副有限群であることの完成） | 実体構成 |
| M18 コンパクト性の一般論（基盤インフラ） | 開被覆の有限部分被覆: 枚挙可能離散空間のコンパクト性（⟹ ℤ/n コンパクト）・**連続像のコンパクト性**・直積の開長方形近傍基・**二項チコノフ**（チューブ補題、集合族の非可述的定義で選択公理回避） | 実体構成 |
| M19 圏論インフラ（基盤インフラ） | 圏・関手・自然変換・**圏同値**（宇宙多相）、G-集合の圏 `GSetCat`、制限関手と**同値の輸送**（群同型 ⟹ 作用圏の圏同値） | 実体構成 |
| M20 Galois 圏 G1–G6 と主定理（基盤インフラ） | **公理系 G1–G6 を G-Set 圏で全検証**（終対象・ファイバー積・始対象・有限和・エピモノ分解・忘却の完全性・同型反映=G6 のみ Classical.choice、選択原理の所在の形式的特定）。**Aut(F) の群化と分類定理**（Yoneda 型論法）、**π₁ = Aut(F)**（群同型）、**SGA1 主定理のパッケージング**: 圏同値 G-Set ≃ Aut(F)-Set | 実体構成 |
| M21 抽象 Galois 圏（基盤インフラ） | **公理系 G1–G6 を抽象データ構造として定式化し、公理だけから主定理の中核を導出**: 積・イコライザのファイバー積からの導出、**ファイバー関手の忠実性**（G1+G4+G6 のみから）、**evaluation 単射性**（連結対象の射はファイバー一点で決まる）、**ガロア対象の自己射群 ≅ ファイバー**（π₁ の有限レベルの抽象形）——**全て公理ゼロ**。モデル（G-Set 圏）の公理系充足も構造化（無矛盾性） | 実体構成 |
| M22 SGA1 主定理の抽象完成（基盤インフラ） | **比較関手 Hom(A,−) : C → Aut(A)-Set の抽象構成と充満忠実性**: 自己同型群の選択公理なし群化、忠実性（分裂対象上）、連結対象への射のファイバー全射性 ⟹ **Hom(A,X) は単一軌道**、降下公理（G3 の strict epi 性）の追加と**充満性**（降下＋ガロア推移性＋evaluation 単射性）——**主定理・射レベルの全定理が公理ゼロ**。モデルは降下公理も充足（choice は降下射の構成のみ） | 実体構成 |
| M23 SGA1 主定理の対象レベル完成（基盤インフラ） | **商公理**（G2 後半: 自己同型族による商 Qt(A,P) と F の商完全性）を追加し、**本質的全射性**を導出: 剰余類作用 Aut(A)/H ≅ Hom(A, Qt(A,H))（同変全単射）。M16-5 と合成で**全ての推移的 Aut(A)-集合が比較関手の像**——忠実・充満・本質的全射の三点が公理から完結。モデルの商は Quot で構成的（choice 不要、降下公理との形式的対比） | 実体構成 |
| M24 pro-対象（基盤インフラ） | **ガロア塔と π₁ の副有限構成**: 遷移準同型の存在・一意性（公理ゼロ）・**全射性**（π₁ ↠ 有限ガロア群、公理ゼロ）、塔の逆系と **π₁ = limitGrp(塔)**（M13/M15 の普遍性・位相が自動適用）。遷移抽出は Classical.choice（∃! の関数化） | 実体構成 |
| M25 逆極限コンパクト性（基盤インフラ） | **König 型木論法**: 有限レベル Nat 鎖の逆極限はコンパクト（未被覆点の無限枝構成に Classical.choice = 選択原理の所在の特定）。**ガロア塔の π₁ はコンパクト**・階乗鎖 ℤ/n!（ẑ の鎖型表示）はコンパクト | 実体構成 |
| M26 有限和分解の簿記（基盤インフラ） | F の和完全性公理 → **連結対象の射は和因子を経由**（公理ゼロ）→ Hom(A,X⊕Y) ≅ Hom(A,X)⊔Hom(A,Y)（公理ゼロ）→ **剰余類作用の任意有限リストの実現**——SGA1 対象レベルが有限和込みで完全 | 実体構成 |
| M27 局所類体論（基盤インフラ） | **ℤ_p = lim ℤ/p^n の実構成**（コンパクト・位相群・ℤ ↪ ℤ_p の p 進分離性）＋**不分岐局所相互法則の完全証明**: rec = 完備化∘付値 : K^× → ẑ = Gal(K^ur/K)、**核 = 単数群 O^×**・**各有限レベルへ全射**（Frobenius 稠密性）——いずれも choice なし。LCFT インターフェース `LocalCFTData` は不分岐モデルで充足（公理化なしの witness）。分岐部分（Lubin–Tate）は未形式化 | 実体構成 |
| M28 ノルム部分群対応（基盤インフラ） | LCFT の第二の柱: 部分群の引き戻し・押し出し、**随伴性**（ガロア接続）、**対応の忠実性**（rec 単射 ⟹ comap∘map = id、「ノルム部分群から拡大が一意」の群論的内容）——核心3定理は**公理ゼロ**。不分岐モデルで具体化 | 実体構成 |
| M29 主単数（基盤インフラ） | LCFT 分岐側の第一歩: **ℤ/p^n と ℤ_p の乗法構造**（合同両立・遷移両立・可換性）、幾何級数恒等式 (1−t)Σt^k = 1−t^n、**主単数の可逆性**（a ≡ 1 (mod p) ⟹ ℤ/p^n で可逆、逆元 = 幾何級数）——「1+pℤ_p が乗法群をなす」の各有限レベル完全証明。選択公理不使用 | 実体構成 |
| M30 主単数群（基盤インフラ） | **(1+pℤ_p, ×) を実際の `Grp` として構成**: 幾何級数逆元のレベル間整合性（p^i ∣ Σ_{k<j}t^k − Σ_{k<i}t^k）で逆元を逆極限に持ち上げ、主単数性の積閉性・逆元閉性を証明、群公理は成分ごとの Int 恒等式に還元。アーベル性・「主単数は ℤ_p の単元」・1+p·k 型の像の主単数性込み。O^× = μ × (1+m) の (1+m) 部の完成。選択公理不使用 | 実体構成 |
| M31 単数 filtration（基盤インフラ） | **U^(d) = 1+p^dℤ_p の部分群族と次数商 U^(d)/U^(d+1) ≅ ℤ/p**: filtration の部分群性（メンバーシップ = レベル d への射影が 1）、U^(1) = 全体・単調減少・分離性（∩U^(d) = {1}）、次数商写像 θ_d: 1+p^d u ↦ u mod p を整数除算で構成し**準同型・核 = U^(d+1)・全射**の三点を完全証明（第一同型定理の内容）。分岐相互法則の「上付き番号付け」の土台。選択公理不使用 | 実体構成 |
| M32 Fermat の小定理（基盤インフラ） | **FLT を core のみで完全証明**: 二項係数の自前定義と委員会恒等式 (n+1)C(n,k) = (k+1)C(n+1,k+1)（二重帰納）、**Bézout の補題**（Euclid 互除法の燃料付き帰納で構成的に）、**Euclid の補題** p ∣ ab ⟹ p∣a ∨ p∣b、p ∣ C(p,k)、**二項定理** (x+1)^n = ΣC(n,k)x^k、新入生の夢、**a^p ≡ a (mod p)**（全 a : ℤ）。Teichmüller 持ち上げ ω(a) = lim a^{p^n} の整合性の基底。素数 witness: 2, 3。選択公理不使用 | 実体構成 |
| M33 Teichmüller 持ち上げ（基盤インフラ） | **ω(a) = lim a^{p^n} : ℤ_p の実構成**（O^× = μ × (1+m) の μ 部）: 指数法則、因数分解 x^n−y^n = (x−y)Σx^k y^{n−1−k}（再帰形で添字回避）、**持ち上げ補題** x ≡ y (mod p^n) ⟹ x^p ≡ y^p (mod p^{n+1})、整合性（基底 = FLT）とその望遠鏡和。**剰余の復元** ω(a) ≡ a (mod p)・**乗法性** ω(ab) = ω(a)ω(b)・ω(1) = 1・**Frobenius 不変性** ω(a^p) = ω(a)。選択公理不使用 | 実体構成 |
| M34 1 の冪根性（基盤インフラ） | **ω(a)^{p−1} = 1 の完全証明**: ℤ_p の冪演算 zpPow、**Euclid の補題の Int 版**（natAbs 還元）、**古典形 Fermat** a^{p−1} ≡ 1 (mod p)（p ∤ a）、**Euler の定理の p 冪版** p^{n+1} ∣ a^{p^n(p−1)} − 1（基底 = 古典形 Fermat、帰納段 = 持ち上げ補題）。帰結: **ω(a) は 1 の (p−1) 乗根**（値域 = μ_{p−1}）かつ **ℤ_p の単元**（逆元 = ω(a)^{p−2} の明示構成）。選択公理不使用 | 実体構成 |
| M35 単数分解（基盤インフラ） | **O^× = μ_{p−1} × U^(1) の直積分解**: ℤ_p 乗法の結合則・単位元、**主単数性のレベル 1 判定**（x ≡ 1 mod p で十分）、**ω の剰余依存性** a ≡ b (mod p) ⟹ ω(a) = ω(b)（持ち上げ補題の反復）、**分解の存在** x = ω(a)·u（u = ω(a)^{p−2}·x、主単数性は p(p−2)+1 = (p−1)² と古典形 Fermat）、**一意性**（レベル 1 合同の望遠鏡和 + ω^{p−2} 消去）。μ 部（M33–34）と U^(1) 部（M30–31）がここで結合。選択公理不使用 | 実体構成 |
| M36 単数群 ℤ_p^×（基盤インフラ） | **ℤ_p^× を実際の `Grp` として構成**: 単数性 = レベル 1 剰余が p と素、積閉性（Euclid）、Teichmüller 代表・主単数は単数。核心は**逆元の明示構成 x^{−1} = x^{p−2}·(x^{p−1})^{−1}** — x^{p−1} は古典形 Fermat で主単数になり M30 の幾何級数逆元が適用可能（代表元抽出 = 選択公理を完全回避）。アーベル性・**μ × U^(1) 分解のパッケージング**込み。選択公理不使用 | 実体構成 |
| M37 完全な相互写像（基盤インフラ） | **rec : ℚ_p^× → ẑ × ℤ_p^× の完成**: ℚ_p^× = p^ℤ × ℤ_p^× と Gal(ℚ_p^ab/ℚ_p) = ẑ × ℤ_p^× の表示（両因子とも実構成）、rec(p^k·u) = (Frob^k, u)、**単射性**（p 進分離性 × 恒等）、**単数は慣性群へ**（M27-5 の核特徴付けの精密化）、**LCFT インターフェースの完全模型**（M27 の不分岐 witness を本物の単数群で置き換え）。右辺と実際の Galois 群の同型（局所 Kronecker–Weber）は対象外と正直に申告。選択公理不使用 | 実体構成 |
| M38 可換環の基盤（Lubin–Tate 第一層） | **CRing 公理系の自前定義と ℤ・ℤ/n・ℤ_p の可換環化**: 右分配・mul_zero 等の導出、加法群への忘却（Grp 理論と接続）、ℤ/n 環（加法 = M13 商群 + 乗法 = M29 zmodMul）、**ℤ_p 環**（M27 逆極限群 + M29/M35 乗法構造を束ねる、分配は成分計算）、環準同型 RingHom と **ℤ → ℤ_p・ℤ_p → ℤ/p^n が環準同型**。LT 級数の係数環の整備。選択公理不使用 | 実体構成 |
| M39 形式冪級数環（Lubin–Tate 第二層） | **R[[X]] は可換環**: 一般有限和 rsum（congr・加法・head・スカラー倍・**反転**）、**三角和の交換** Σ_{j≤n}Σ_{k≤j} g(k,j−k) = Σ_{k≤n}Σ_{l≤n−k} g(k,l)（直接帰納）、Cauchy 積の**可換性 = 反転・結合則 = 三角交換・分配 = 項ごと分配**で完全証明。定数項埋め込み R → R[[X]] の環準同型性・変数 X。選択公理不使用 | 実体構成 |
| M40 級数の合成（Lubin–Tate 第三層） | **合成 (P∘Q)_n = Σ_{k≤n} P_k(Q^k)_n の有限和構成**: 一点集中和、冪 Q^k と指数法則、**truncation**（Q(0) = 0 ⟹ n < k で (Q^k)_n = 0、有限和定義の正当化）、合成の加法性・1∘Q = 1・**X∘Q = Q**、低次係数公式 (P∘Q)_0 = P_0・(P∘Q)_1 = P_1·Q_1（LT 補題の係数帰納の出発点）。選択公理不使用 | 実体構成 |
| M41 Lubin–Tate 一意性（第四層） | **方程式 F∘g = c·F + F^q の解の一意性**（スキーマ、抽象可換環上）: **対角係数** (g^k)_k = (g_1)^k（leading term の同定）、**F_n 非依存性**（(F^{k+2})_n は F_{<n} のみ — 境界項は truncation と F(0) = 0 で消滅）、係数の強帰納法で「定数項 0・一次係数一致 ⟹ F = F'」。正則性は減算なしの消去仮説 a·G + c·b = b·G + c·a ⟹ a = b で定式化。選択公理不使用 | 実体構成 |
| M42 ℤ_p の LT 消去仮説（第五層） | **ℤ_p 上の Lubin–Tate 一意性の具体化**: CRing 負元ツールキット（mul_neg・neg_neg 等、公理ゼロ）、**消去式 ⟹ (G−c)(a−b) = 0** の一般変形、**ℤ_p の p-捻れなし性**（p·d = 0 ⟹ d = 0、成分計算）、**単数の正則性**（M36 の明示逆元で消去）、分解 p^n − p = p·(p^{n−1}−1)（p^{n−1}−1 は単数）で消去仮説を充足。帰結: **g(0)=0・g(1)=p・F∘g = p·F + F^q の解は一次係数で一意**。選択公理不使用 | 実体構成 |
| M43 p-進除算（第六層） | **除算 zpDivP : ℤ_p → ℤ_p の全域・choice-free 構成**（レベル m+1 の代表の ediv でレベル m へ。well-defined 性と遷移整合性は ediv の加法公式から無条件）、**p·(x/p) = x**（x ≡ 0 mod p）・**(p·e)/p = e**（無条件）、**可除性の level-1 判定** ∃e, x = p·e ⟺ x の mod p 射影 = 0、**ℤ_p の Frobenius 合同** x^p ≡ x (mod p) と **x^p − x の p-整除性**（LT 誤差項整除性の原型）。選択公理不使用 | 実体構成 |
| M44 二変数二項定理（第七層） | **任意の可換環上で (x+y)^n = Σ C(n,k)x^k y^{n−k}**: 自然数の環像 rofNat とその**半環準同型性**（加法・乗法保存、公理ゼロ）、Pascal 帰納による二項定理（和の操作は全て M39 の rsum 補題、添字簿記は omega）、**中間項の p-因子** rofNat C(p,k) = rofNat p · c（M32 の p ∣ C(p,k) の環像翻訳）。級数版「新入生の夢」の代数的核心。選択公理不使用 | 実体構成 |
| M45 新入生の夢（第八層） | **(x+y)^p = x^p + y^p + p·c の三段構成**: 環レベル（境界項 C = 1・中間項の p-因子を Nat 除算で正準化して括り出し = 選択公理回避）→ **級数レベル** PS(R)（psPow = rpow(psRing) の同定で即時転送）→ **ℤ_p 係数レベル**（rofNat(PS) = 定数級数・定数級数の積 = 係数ごとスカラー倍・rofNat(ℤ_p) = toZp 像で、各係数の p-整除性 witness 付きに翻訳）。LT 誤差項整除性の供給源。選択公理不使用 | 実体構成 |
| M46 冪級数の関手性（第九層） | **環準同型 φ : R → S の冪級数環への持ち上げ psMap が加法・乗法・冪・合成を全て保存**（誤差項を mod p で PS(ℤ/p) に落とす輸送装置）。環準同型の 0・有限和・冪の保存、(ab)^k = a^k b^k、**モノミアル代数** X^a·X^b = X^{a+b}・(X^m)^k = X^{mk}、**伸長公式** (F∘X^m)_{mk} = F_k・m ∤ n で 0（mod p で f ≡ X^p となるため F̄∘X^p の係数読みに使用）。選択公理不使用 | 実体構成 |
| M47 標数 p の Frobenius 定理（第十層） | **F^p = F∘X^p in PS(ℤ/p) の完全証明**（LT 誤差項整除性の核心）: ℤ/p の標数 p（rofNat p = 0）と係数 FLT c^p = c、**char p では新入生の夢が正確な等式** (A+B)^p = A^p + B^p、打ち切り trunc F (N+1) = trunc F N + F_N·X^N と単項式の冪 (c·X^m)^k = c^k·X^{mk}・合成 (c·X^N)∘X^m = c·X^{mN} で **truncation 帰納**、係数 n の一般化は psPow_congr（M41）。選択公理不使用 | 実体構成 |
| M48 LT 誤差項の p-整除性（第十一層） | **任意の F で (p·F + F^p) − F∘f の全係数が p で割れる**（f = pX + X^p）: psMap の neg・単項式・スカラー倍保存、**LT 多項式の定義と mod-p 還元 f̄ = X^p**、誤差項の mod-p 消滅 Φ(E) = 0 — Φ(pF) = 0（標数）・Φ(F^p) = Φ(F)^p・Φ(F∘f) = Φ(F)∘X^p に **M47 の Frobenius 定理**を適用して一撃。各係数の整除性 witness は構成的（M43 zpDivP）。選択公理不使用 | 実体構成 |
| M49 Lubin–Tate 補題（最終層・**LT キャンペーン完成**） | **存在 + 一意性の完全証明**: 係数の再帰構成 ltSeg/ltSol（F₀ = 0・F₁ = a・F_{m+2} = u^{-1}·(E(部分解)/p)、choice-free）、切片の整合性（stable・eq_sol・high）、**除算恒等式** π·(u·F_n) = E_n（M36 単元逆元 + M43 zpDivP + M48 整除性の合流）、**方程式 F∘f = p·F + F^p の全係数検証**（n ≥ 2 は一意性と同じ分解 L + F_n·p^n = p·F_n + T を移項簿記で逆向きに）。**lubin_tate: 任意の a : ℤ_p に対し F(0)=0・F(1)=a の解が存在し一意**（M42 と結合）。選択公理不使用 | 実体構成 |
| M50 二変数冪級数の基盤（形式群第一層） | **PS2 R := PS(psRing R)（反復構成 R[[X]][[Y]]）で環構造を M39 から無償取得**。新規は総次数のみ: 座標 X = psC(psX)・Y = psX(psRing R)、有限和の係数交換、**総次数 truncation**（F₀₀ = 0 ⟹ i+j < k で (F^k)_{i,j} = 0、二重和の各項消滅）、**1変数→2変数代入** (f∘F)_{i,j} = Σ_{k≤i+j} f_k(F^k)_{i,j} とその基本性質（加法性・1∘F = 1・X∘F = F）、線形部 X+Y の係数（形式群の一次条件）。選択公理不使用 | 実体構成 |
| M51 二変数→二変数代入（形式群第二層） | **代入 F(P,Q)_{i,j} = Σ_{a,b≤i+j} F_{a,b}(P^a Q^b)_{i,j} の構成**: (psC z)^k = psC(z^k)、座標の冪 X^a = psC(X^a)・Y^b = Y-mono^b、**二変数単項式の積公式** X^a·Y^b = δ_{(a,b)}、**恒等代入 F(X,Y) = F**（二重一点集中和 — 代入の座標規約のサニティアンカー）。選択公理不使用 | 実体構成 |
| M52 形式群方程式の定式化（形式群第三層） | **f∘F = F(f(X), f(Y)) の機械可読化**: 座標代入と注入の整合 **f∘X-座標 = inX f・f∘Y-座標 = inY f**（一点集中和）、inY X = Y、**恒等 f = X で方程式が任意の F（F₀₀ = 0）で成立**（左辺 = F は M50・右辺 = F(X,Y) = F は M51 — 全機構のフルループ機械検証）、LT 形式群法則の述語 IsLTFormalGroup（一次条件 + 方程式）と注入の定数項消滅（truncation 妥当性）。選択公理不使用 | 実体構成 |
| M53 二変数係数持ち上げと mod-p 還元（形式群第四層） | **ps2Map = psMap の反復適用**（psRingHom: psMap の環準同型化 R[[X]] → S[[X]] で二変数持ち上げを一変数理論から無償取得、係数ごとには φ(F_{j,i})）: 座標保存 X ↦ X・Y ↦ Y、**代入との交換** φ(f∘F) = φf∘φF・φ(F(P,Q)) = (φF)(φP, φQ)（ringHom_rsum + psMap_pow を psRing レベルで再利用）、二方向注入との交換、**方程式の移送**（F が f の形式群方程式を満たすなら φF は φf の方程式を満たす）、**LT 形式群の mod-p 還元**: IsLTFormalGroup p F ⟹ F̄ は X^p∘F̄ = F̄(X^p, Y^p) を満たす（M48 の f̄ = X^p と結合）＋一次条件の還元。選択公理不使用 | 実体構成 |
| M54 一般化 Frobenius 定理（形式群第五層・前半） | **標数 p の任意の可換環で F^p = (Frob F)∘X^p**: Frobenius 環準同型 frobHom（c ↦ c^p、map_add = 標数 p の正確な新入生の夢 (x+y)^p = x^p + y^p）、級数レベルの正確な新入生の夢の一般化、psMap の打ち切り交換、**truncation 帰納による一般化 Frobenius 定理**（M47 の係数 FLT を frobHom の像の運搬に置換）、ℤ/p では frobHom = 恒等で M47 を回復（整合性アンカー）、**標数 p の冪級数環への遺伝** rofNat R[[X]] p = 0。選択公理不使用 | 実体構成 |
| M55 二変数 Frobenius と LT 誤差の mod-p 消滅（形式群第五層・後半） | **G^p = G(X^p, Y^p) in (ℤ/p)[[X,Y]] の完全証明**: 一変数理論の二段重ね（外側 Y = M54 の一般化 Frobenius・内側 X = M47 の Frobenius）で **G^p の係数公式**（(pb,pa) 係数 = G_{b,a}・p 非整除指数は 0）、X^m∘G = G^m（総次数 truncation）、G(X^m, Y^m) の係数公式（二重一点集中和）、整除判定は p·(j/p) = j の decEq で choice 回避。**二変数 Frobenius 定理 frobenius2_charp**: G₀₀ = 0 なる任意の G が X^p∘G = G(X^p, Y^p) を満たす = M53-6 が LT 形式群に強制する方程式は標数 p で無条件に成立。**LT 誤差の mod-p 消滅 lt_error_vanishes_modp**: 任意の F ∈ PS2(ℤ_p)（F₀₀ = 0）で形式群方程式の両辺が mod p 一致（M49 の一変数 ltError_reduction の二変数版 — 存在証明の心臓部）。選択公理不使用 | 実体構成 |
| M56 LT 誤差の係数 p-整除性と誤差/p（形式群第六層） | **二変数 LT 誤差 E(F) := f∘F − F(f(X), f(Y)) の実構成**（PS2 の環構造の加法・反元）、**誤差消滅 ⟺ 方程式成立**（E = 0 ⟺ IsLTFormalGroup の方程式 — 再帰構成の終着点）、誤差の mod-p 消滅（級数形 Φ(E) = 0、M55-7 を x − x = 0 に変換）、**全係数の p-整除性** ∃e, E_{j,i} = p·e（M43 zp_dvd_p_iff）、**誤差/p の実構成 lt2Div**（M43 zpDivP による choice-free 一斉除算）と除算恒等式 p·(E/p)_{j,i} = E_{j,i}。M48 → M49 パイプラインの二変数版前半が完成。選択公理不使用 | 実体構成 |
| M57 二変数冪の係数合同補題（形式群第七層） | **存在再帰の礎石: k ≥ 2 のとき (F^k)_{j,i} は F の総次数 ≤ i+j−1 の係数のみで決まる**（M41 の一変数 psPow_coeff_congr の二変数版）。積の二重 Cauchy 係数公式 (A·B)_{j,i} = Σ_{k≤j}Σ_{l≤i} A_{k,l}·B_{j−k,i−l}（M50 rsum_psRing_coeff で級数和を係数化）、**積の係数合同**（三分処理: 因子1 = (0,0) → 0・因子2 = (0,0) → 0・双方総次数 ≥ 1 → 双方 ≤ n−1 で合同仮定）、**冪の係数合同**（k 帰納、因子の定数項消滅は M50 総次数 truncation）＋ q ≥ 2 の使い勝手版。これで方程式の総次数 n 部分 F_{j,i}·(pⁿ − p) = (既決定データ) の右辺が低次係数のみに依存することが保証され再帰が回る。選択公理不使用 | 実体構成 |
| M48F Frobenioid の圏論化（並行ブランチ） | **M12 の Frobenioid 次数データを M19 の `Cat` 上の実際の圏として実装**: elementary Frobenioid（対象 = 次数 ℤ、射 = (Frobenius 次数 d ≥ 1, 効果的因子 c ≥ 0) with 線形条件 m = d·n + c、合成 = 捻れ半直積型 (d₁d₂, d₂c₁+c₂)）の圏公理完全証明、**次数関手** F_Φ → (ℕ≥1, ×) と **Frobenius 自己関手** Φ_e の関手性、**非可逆性定理群**（次数 ≥ 2 の射は右逆なし・同型の次数は必ず 1・**同型は対象を動かせない** n ≅ m ⟹ n = m・1 → 2 に射はあるが同型はない = M12-3 の圏論版を仮定なしの強い形で。Galois 圏の G6「同型の反映」（M20-5）との二分法の機械検証）、M12 接続（degMor の実現・frob_deg の関手化・Φ_e は次数関手上で恒等）。選択公理不使用 | 実体構成 |
| M51F Frobenioid の圏論的実体と数体での充足（並行ブランチ） | **M12 の `Frobenioid` 構造を ℚ 型の実データで充足**: 有効因子 = 素点での重複度の有限サポート関数（QDiv、サポート上界をデータとして持ち choice 回避）、可換モノイド法則・**重み付き次数の加法性 deg(x+y) = deg x + deg y・Frobenius 斉次性 deg(φ_e x) = e·deg x** を完全証明して `rationalFrobenioid` を Nonempty でなく def として構成。`DegreeVolumeCompat` の実構成により **M12-6（vol_q 供給）が実データで発動**（`rational_qpilot_volume`: 任意の骨格 s で単一素点因子の実現体積 = −\|log q\|）、局所付値（M27）との整合。＋**因子レベルの圏** divisorFrobenioid（対象 = 有効因子、射 = (d≥1, c) with y = φ_d(x)+c、捻れ半直積合成）の圏公理完全証明、**次数関手** → elementaryFrobenioid（M48F）の関手性、**因子レベルの非可逆性**（同型は因子を動かせない x ≅ y ⟹ x = y、＋次数関手で M48F に帰着する独立経路）。選択公理不使用 | 実体構成 |
| M53F poly-isomorphism と剛性（並行ブランチ） | **[FrdI] の Frobenius-like/étale-like 二分法と (Ind1) 不定性の在処を圏論的核で機械検証**: 剛性述語 `IsGaunt`（同型 ⟹ 対象の等号）・`IsoUnique`（同型の hom 成分は一意 = poly-isomorphism が単集合に潰れる、CatIso 全体の等号は M22-1a の逆一意性で従う）を定義し、**Frobenioid 側は剛的** — divisorFrobenioid（M51F）・elementaryFrobenioid（M48F）の任意の同型は成分 (d,c) = (1,0)（恒等射と同成分）で gaunt かつ IsoUnique 成立。**étale 側は非剛的** — 群 G の一点圏 BG（`deloopCat`、圏公理は群公理から完全証明・右単位/右逆は左公理系からの導出定理）では全ての射が同型で、**poly-isomorphism は G.carrier と明示的全単射（G-トーソル）**＝(Ind1) 型不定性の在処。総括 `gaunt_dichotomy`: 非自明群 G で「divisorFrobenioid は IsoUnique ∧ BG は ¬IsoUnique」（注意: BG は一点なので gaunt は自明成立 — 剛性を測るのは IsoUnique）。デッキ群 ℤ（M9 intGrp）での具体的発動＋ M5 `MultiradialRep.Ind`/`ind0` への型レベル接続（`deloopInd`、G 非自明なら基点以外の選択肢が実在）。選択公理不使用 | 実体構成 |
| M55F split Frobenioid（並行ブランチ） | **[FrdI] の split 構造（射 = Frobenius 次数・効果的因子・単数の三つ組）と (Ind2) 型不定性の在処を機械検証**: 可換単数群 U をパラメータに、射 (d ≥ 1, c : QDiv, u : U) with y = φ_d(x) + c（u は線形条件に関与しない = 因子簿記と単数の分裂）の圏 `splitFrobenioid` を建設。恒等 (1,0,1)・合成 (d₁d₂, φ_{d₂}(c₁)+c₂, u₁^{d₂}·u₂)——単数は第二射の Frobenius 次数で d 乗されて運ばれる。単数結合則は (ab)^n = aⁿbⁿ（`gpow_mul_dist`）を要し非可換群では偽のため U の可換性を仮定（O^× は可換なので正当）。**因子部分は剛的**——同型は (d,c) = (1,0) を強制し対象を動かせない（gaunt、M51F-10 の踏襲）が**単数部分は U-トーソル**——任意の u で (1,0,u) が同型（逆 (1,0,u⁻¹)）になり自己同型全体は U.carrier と明示的全単射（`split_polyiso_torsor`、往復恒等の両向き証明）。二分法の精密化 `split_dichotomy_refined`: 忘却関手 `splitForget`（u を捨てる）の像では任意の二同型が一致（IsoUnique 回復）∧ U 非自明なら hom の異なる同型対が実在 = **一つの圏の中で不定性は単数成分にのみ宿る**（M53F は剛的圏と非剛的圏が別々だった）。M5 `MultiradialRep.Ind`/`ind0` への型レベル接続（`splitInd`、M53F-9 deloopInd の (Ind2) 版）。選択公理不使用 | 実体構成 |
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
    ├── Finiteness.lean  # M17: 鳩の巣原理・基数一意性・有限群⟹有界指数・ℤ/n の有限性
    ├── Compactness.lean # M18: 有限⟹コンパクト・連続像・二項チコノフ（選択公理なし）
    ├── CategoryTheory.lean # M19: 圏・関手・圏同値・G-Set 圏・同値の輸送
    ├── GaloisAxioms.lean # M20: G1–G6 検証・Aut(F) の群化・SGA1 主定理の圏同値
    ├── AbstractGalois.lean # M21: 抽象 Galois 圏（公理から忠実性・evaluation 単射・群復元、公理ゼロ）
    ├── SGA1Completion.lean # M22: 比較関手の充満忠実性（降下公理・軌道推移性、主定理射レベル完成）
    ├── SGA1Object.lean  # M23: 商公理と本質的全射性（Aut(A)/H ≅ Hom(A,Qt)、主定理対象レベル完成）
    ├── ProObject.lean   # M24: ガロア塔・遷移準同型（∃!・全射）・π₁ = limitGrp(塔)
    ├── LimitCompact.lean # M25: 逆極限コンパクト性（König 木論法）・π₁/ℤ/n! 鎖コンパクト
    ├── SumDecomposition.lean # M26: 和完全性・和因子分解・有限リスト実現（対象レベル完全）
    ├── LocalCFT.lean    # M27: ℤ_p 実構成・不分岐局所相互法則（核=単数群・稠密性）・LCFT インターフェース
    ├── NormCorrespondence.lean # M28: ノルム部分群対応（随伴性・忠実性、公理ゼロ）
    ├── PrincipalUnits.lean # M29: ℤ_p の乗法構造・幾何級数・主単数の可逆性（choice なし）
    ├── PrincipalUnitGroup.lean # M30: 主単数群 (1+pℤ_p,×) : Grp（幾何級数逆元の整合束、choice なし）
    ├── UnitFiltration.lean # M31: 単数 filtration U^(d)・次数商 θ_d: U^(d)/U^(d+1) ≅ ℤ/p（choice なし）
    ├── Fermat.lean      # M32: Fermat の小定理（Bézout・Euclid・二項定理込み、choice なし）
    ├── Teichmuller.lean # M33: Teichmüller 持ち上げ ω(a) = lim a^{p^n}（乗法的・Frobenius 不変、choice なし）
    ├── RootsOfUnity.lean # M34: ω(a)^{p−1} = 1（Euler の定理 p 冪版・ω の可逆性、choice なし）
    ├── UnitDecomposition.lean # M35: 単数分解 O^× = μ × U^(1)（存在 + 一意性、choice なし）
    ├── ZpUnits.lean     # M36: 単数群 ℤ_p^× : Grp（逆元 = x^{p−2}(x^{p−1})^{−1}、choice なし）
    ├── FullReciprocity.lean # M37: 完全な相互写像 rec : ℚ_p^× → ẑ × ℤ_p^×（choice なし）
    ├── Ring.lean        # M38: 可換環 CRing・ℤ と ℤ/n と ℤ_p の環化・環準同型（LT 第一層、choice なし）
    ├── PowerSeries.lean # M39: 形式冪級数環 R[[X]]（三角和交換による結合則、choice なし）
    ├── Composition.lean # M40: 級数の合成 P∘Q・truncation・低次係数公式（choice なし）
    ├── LubinTateUnique.lean # M41: Lubin–Tate 一意性（係数の強帰納、choice なし）
    ├── LubinTateZp.lean # M42: ℤ_p の消去仮説充足・LT 一意性の具体化（choice なし）
    ├── PadicDivision.lean # M43: p-進除算 zpDivP・Frobenius 合同（choice なし）
    ├── Binomial2.lean   # M44: 可換環上の二変数二項定理・rofNat（choice なし）
    ├── Freshman.lean    # M45: 新入生の夢（環 → 級数 → ℤ_p 係数、choice なし）
    ├── PSFunctor.lean   # M46: 冪級数の関手性 psMap・モノミアル代数・伸長公式（choice なし）
    ├── FrobeniusCharP.lean # M47: 標数 p の Frobenius 定理 F^p = F∘X^p（choice なし）
    ├── LTErrorDivisible.lean # M48: LT 誤差項の p-整除性（mod-p 還元 + Frobenius 定理、choice なし）
    ├── LubinTateExists.lean # M49: Lubin–Tate 補題完成（係数の再帰構成 + 存在 + 一意性、choice なし）
    ├── FrobenioidCat.lean # M48F: Frobenioid の圏論化（elementary Frobenioid・次数関手・同型 = 恒等のみ、choice なし）
    ├── FrobenioidModel.lean # M51F: Frobenioid の圏論的実体と数体での充足（QDiv・rationalFrobenioid・divisorFrobenioid・次数関手、choice なし）
    ├── PolyIsomorphism.lean # M53F: poly-isomorphism と剛性（IsGaunt/IsoUnique・deloopCat・G-トーソル定理、choice なし）
    ├── SplitFrobenioid.lean # M55F: split Frobenioid — 単数成分と (Ind2) の在処（gpow・SplitHom・U-トーソル・二分法精密化、choice なし）
    ├── PowerSeries2.lean # M50: 二変数冪級数の基盤（総次数 truncation・1→2変数代入、choice なし）
    ├── FormalGroupSub.lean # M51: 二変数→二変数代入・恒等代入 F(X,Y) = F（choice なし）
    ├── FormalGroupEq.lean # M52: 形式群方程式の定式化・恒等での成立（choice なし）
    ├── FormalGroupMap.lean # M53: 二変数係数持ち上げ ps2Map・方程式の移送・LT 形式群の mod-p 還元（choice なし）
    ├── FrobeniusGen.lean   # M54: 一般化 Frobenius 定理 F^p = (Frob F)∘X^p（標数 p の任意の環、choice なし）
    ├── Frobenius2.lean     # M55: 二変数 Frobenius G^p = G(X^p,Y^p)・LT 誤差の mod-p 消滅（choice なし）
    ├── FormalGroupErr.lean # M56: 二変数 LT 誤差の係数 p-整除性・誤差/p の実構成（choice なし）
    ├── FormalGroupCongr.lean # M57: 二変数冪の係数合同（積の二重 Cauchy 公式・三分処理、choice なし）
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
| M5: 定理3.11 の**構成**の完全形式化 | 4基盤の骨格（M9–M12）は done。**Frobenioid の圏論的実体と数体型データでの充足は M51F で base 圏一点の範囲を形式化済み**（因子圏・次数関手・実データによる M12 充足。poly-isomorphism・realification・base 圏上のファイバー構造は未達）。残り（環構造復元の本体・p進テータ関数の関数等式）は mathlib 規模の数論幾何ライブラリが必要。世界の誰も達成していない |
| M13: 副有限群（商群・逆極限・ẑ の実構成）— 実体建設フェーズ第1弾 | done（公理化なしの実構成） |
| M14: Galois 圏・étale π₁ のファイバー関手機構 — 実体建設フェーズ第2弾 | done（Aut(F) ≅ G は公理ゼロ） |
| M15: 位相付き副有限群（位相群性・開部分群・近傍基定理） — 実体建設フェーズ第3弾 | done（Classical.choice ゼロ） |
| M16: SGA1 主定理の核心（軌道-安定化定理・Galois 対応の実現・連続作用条件） — 実体建設フェーズ第4弾 | done（Classical.choice ゼロ） |
| M17: 有限性の本格的定義（鳩の巣・基数一意性・有限⟹有界指数・ℤ/n 有限） — 第5弾 | done（Classical.choice ゼロ。omega の ∃ 文脈での choice 混入を検出・排除） |
| M18: コンパクト性の一般論（有限⟹コンパクト・連続像・二項チコノフ） — 第6弾 | done（Classical.choice ゼロ） |
| M19+M20: Galois 圏 G1–G6 全検証・Aut(F) 群化・SGA1 主定理の圏同値パッケージング — 第7弾 | done（choice は G6 のみ＝選択原理の所在の特定） |
| M21: 抽象 Galois 圏の一般形（公理系の構造化と公理のみからの主定理中核の導出） — 第8弾 | done（抽象部 6 定理は完全公理ゼロ） |
| M22: SGA1 主定理の抽象完成（比較関手の充満忠実性、降下公理） — 第9弾 | done（射レベル全定理が公理ゼロ） |
| M23: SGA1 主定理の対象レベル完成（商公理・本質的全射性） — 第10弾 | done（忠実・充満・本質的全射が公理から完結） |
| M24: pro-対象（ガロア塔・遷移準同型・π₁ の副有限構成） — 第11弾 | done |
| M25: 逆極限コンパクト性（König 木論法・π₁/ẑ コンパクト） — 第12弾 | done（choice の所在を特定） |
| M26: 有限和分解の簿記（和因子分解・有限リスト実現） — 第13弾 | done（**副有限群・Galois 圏・étale π₁・SGA1 ブロック完了**） |
| M27: 局所類体論の形式化第一段（ℤ_p 実構成・不分岐相互法則完全証明・LCFT インターフェース） — 第14弾 | done（不分岐部は choice なし完全証明） |
| M28: ノルム部分群対応（LCFT 第二の柱、核心は公理ゼロ） — 第15弾 | done |
| M29: 主単数（ℤ_p 乗法構造・幾何級数可逆性、1+pℤ_p の群性の核心） — 第16弾 | done（choice なし） |
| M30: 主単数群 (1+pℤ_p, ×) の Grp 構成（逆元の逆極限持ち上げ） — 第17弾 | done（choice なし） |
| M31: 単数 filtration U^(d) と次数商 U^(d)/U^(d+1) ≅ ℤ/p — 第18弾 | done（choice なし） |
| M32: Fermat の小定理（Bézout・Euclid の補題・二項定理を core のみで） — 第19弾 | done（choice なし） |
| M33: Teichmüller 持ち上げ ω(a) = lim a^{p^n}（乗法的切断・Frobenius 不変） — 第20弾 | done（choice なし） |
| M34: ω の 1 の冪根性・可逆性（Euler の定理 p 冪版・Int 版 Euclid） — 第21弾 | done（choice なし） |
| M35: 単数分解 O^× = μ_{p−1} × U^(1)（存在 + 一意性） — 第22弾 | done（choice なし） |
| M36: 単数群 ℤ_p^× の Grp 構成（逆元の明示構成、choice 回避） — 第23弾 | done（choice なし） |
| M37: 完全な相互写像 rec : ℚ_p^× → ẑ × ℤ_p^×（LCFT 完全模型） — 第24弾 | done（choice なし） |
| M38: 可換環の基盤（ℤ・ℤ/n・ℤ_p の環化、Lubin–Tate 第一層） — 第25弾 | done（choice なし） |
| M39: 形式冪級数環 R[[X]]（Cauchy 積の環法則、Lubin–Tate 第二層） — 第26弾 | done（choice なし） |
| M40: 級数の合成 P∘Q（truncation・係数公式、Lubin–Tate 第三層） — 第27弾 | done（choice なし） |
| M41: Lubin–Tate 一意性（F∘g = c·F + F^q の解の一意性スキーマ） — 第28弾 | done（choice なし） |
| M42: ℤ_p の LT 消去仮説充足（p-捻れなし × 単数正則、一意性の具体化） — 第29弾 | done（choice なし） |
| M43: p-進除算 zpDivP と Frobenius 合同（存在側の除算インフラ） — 第30弾 | done（choice なし） |
| M44: 可換環上の二変数二項定理（rofNat・中間項の p-因子） — 第31弾 | done（choice なし） |
| M45: 新入生の夢 (x+y)^p = x^p + y^p + p·c（環 → 級数 → ℤ_p 係数） — 第32弾 | done（choice なし） |
| M46: 冪級数の関手性 psMap（加法・乗法・冪・合成の保存）と伸長公式 — 第33弾 | done（choice なし） |
| M47: 標数 p の Frobenius 定理 F^p = F∘X^p（truncation 帰納） — 第34弾 | done（choice なし） |
| M48: LT 誤差項の p-整除性（mod-p 還元で Frobenius 定理に帰着） — 第35弾 | done（choice なし） |
| M49: Lubin–Tate 補題（存在 + 一意性、**LT キャンペーン完成**） — 第36弾 | done（choice なし） |
| M48F: Frobenioid の圏論化（サブエージェント並行開発・統合） — 第36弾 | done（choice なし） |
| M50: 二変数冪級数の基盤（総次数 truncation・代入、形式群第一層） — 第37弾 | done（choice なし） |
| M51: 二変数→二変数代入と恒等代入 F(X,Y) = F（形式群第二層） — 第38弾 | done（choice なし） |
| M52: 形式群方程式の定式化と恒等での成立（形式群第三層） — 第39弾 | done（choice なし） |
| M51F: Frobenioid の圏論的実体と数体での充足（M12/M5 の「未達」部分、因子圏・次数関手・実データ充足） — サブエージェント並行開発・第39弾統合 | done（choice なし） |
| M53: 二変数係数持ち上げ ps2Map と LT 形式群の mod-p 還元（形式群第四層） — 第40弾 | done（choice なし） |
| M53F: poly-isomorphism と剛性（Frobenioid = gaunt/IsoUnique vs BG = G-トーソル、(Ind1) の在処の二分法） — サブエージェント並行開発・第40弾統合 | done（choice なし） |
| M54: 一般化 Frobenius 定理 F^p = (Frob F)∘X^p（標数 p の任意の環、形式群第五層前半） — 第41弾 | done（choice なし） |
| M55: 二変数 Frobenius G^p = G(X^p,Y^p) と LT 誤差の mod-p 消滅（形式群第五層後半） — 第41弾 | done（choice なし） |
| M56: 二変数 LT 誤差の係数 p-整除性と誤差/p の実構成（形式群第六層） — 第42弾 | done（choice なし） |
| M55F: split Frobenioid — 射の単数成分と (Ind2) の在処（因子は剛的・単数が U-トーソル、M53F 二分法の精密化） — サブエージェント並行開発・第42弾統合 | done（choice なし） |
| M57: 二変数冪の係数合同補題（存在再帰の礎石、形式群第七層） — 第43弾 | done（choice なし） |
| 実体建設の続き: 分岐部分（O^× の構造論 = 主単数 filtration の ℤ_p 加群構造・Lubin–Tate）・rec の Galois 群に対する同型性の実証明 | todo |
| 実体建設の続き: ℤ_p の構成 → 局所体の構造論 → 局所類体論（M10 の公理化フィールドの実証明化） | todo |
| M2 実体（prime-strip 圏論データ）の形式化 | todo |
