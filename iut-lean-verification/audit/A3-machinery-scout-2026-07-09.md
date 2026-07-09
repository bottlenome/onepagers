# A3 円分塔（実 G_K）機構 棚卸し — scout 2026-07-09

分類: **[調査／新規モジュール0]**。本ドキュメントはコードを一切変更しない独立監査用の
偵察メモ。complete_pct には影響しない（調査のみ）。対象: A3「実絶対 Galois 群
G_K = 有限 Galois 群の逆極限」を円分塔で建てる準備として、既存の (a) 逆系/逆極限、
(b) 体の実 Galois 群、(c) 体拡大・埋め込み の機構が実 ℚ 上でそのまま使えるかを精査する。

結論を先に一行で: **逆系・逆極限・Aut(K)・Gal(L/K) の「機構」は全て本物で完成しており
汎用（型として任意の有限 Galois 群列を受け付ける）。しかし現在コードベースに存在する
Galois 塔インスタンスは全て「制限準同型 restr を witness データとして受け取る」設計で、
体の包含から restr を実際に計算で構成した例は 0 件。ここが A3 を非自明塔に進める際の
唯一かつ最大のボトルネック**。

---

## 1. 棚卸し表

| 機構 | 何 | carrier/主語 | 実/抽象/模型 | A3 塔に使えるか |
|---|---|---|---|---|
| `InverseSystem`（`IUT/Profinite.lean` M13-5） | 有向前順序 `Idx`・群族 `G:Idx→Grp`・推移射 `t`・整合性 `t_self`/`t_comp` | 完全汎用（`Idx`・`G` は自由パラメータ） | **実**（構造そのものが本物・模型なし。`G i` に実際の有限 Galois 群を代入できる型） | ○ そのまま使える。既に `profPi1System`（下記）で `G n = galoisGroupGrp (ext n)` を代入済み |
| `limitGrp`（M13-5）/ `limit_universal`（M13-6） | 整合族のなす群、普遍性 | 汎用 | **実**（完全証明・choice なし） | ○ そのまま使える |
| `natSystem`（`IUT/ProObject.lean` M24-3） | `InverseSystem` の Nat 添字特殊化（`le=(≤)`） | 汎用 | **実** | ○ 円分塔（Nat 添字 K⊆ℚ(ζ_3)⊆ℚ(ζ_9)⊆…）に直接使える |
| `zmodSystem`/`zhat`（M13-7〜9） | ℤ/n の逆系と ẑ=lim ℤ/n | 具体（ℤ/n） | **実**（可換な副有限群の実例。Gal 塔ではなく加法群） | △ 参考実例のみ。A3 の非可換版 Gal 塔には転用不可（別物） |
| `FieldAut K`（`IUT/FieldAutGroup.lean` M271F-1） | 体の自己同型（加法・乗法・1 保存の全単射・明示逆写像） | 任意の `IUTField` | **実** | ○ そのまま使える |
| `fieldAutGroup K`（M271F-3） | Aut(K) の群構造 | 任意の `IUTField` | **実** | ○ そのまま使える |
| `FieldExtension`（M271F-4） | `base`/`top`/`incl`（環準同型埋め込み） | 任意 | **実**（ただし `incl` の**単射性は公理化されていない**——加法・乗法・1 の保存のみ） | ○ 使えるが、単射性は呼び出し側が別途要求・証明する必要 |
| `galoisSubgroup E`/`galoisGroupGrp E`（M271F-4/5） | Gal(L/K)=Aut_K(L)、Aut(L) の部分群として | 任意の `FieldExtension` | **実**（合成・逆で閉じることを完全証明） | ○ そのまま使える。**一般 `FieldExtension` で本物**（模型・特殊ケース限定なし） |
| `qdfField D hD`（`IUT/QuadraticField.lean` qdf-4/9） | ℚ(√D) の実体構成＋`qdf_galois_order_two`（Gal 位数ちょうど2、**一般の非平方 D で証明**） | 実 ℚ×ℚ | **実**（D=−1,−2 で具体例化。D=−3=cq3D も同じ定理が無条件に使える） | ○ A3 塔の**第1段候補**として即使える（ℚ(√−3)=ℚ(ζ_3) の Gal 計算に転用可） |
| `gaussQField`（`GaussianRationalField.lean`）/`cq3Field`（`CyclotomicFieldQ3.lean`） | ℚ(i)／ℚ(√−3) の実体＋非自明 Gal（**位数2の証明はなし、非自明性のみ**） | 実 ℚ×ℚ | **実**（qdfField と同型だが**別の具体型**——同型輸送は未形式化） | △ ζ_3 の明示元がある点で有用だが、qdfField(−3) と型が違うため「Gal 位数2」を得るには qdf 版へ差し替えるか輸送補題が要る |
| `gefField`（`IUT/GenExtField.lean`）/`gfiCq3Field`（`GenFieldInstances.lean`） | 任意既約 f に対し ℚ[x]/(f) を実体化する一般構成器。ℚ(ζ_3)=ℚ[x]/(Φ_3) を実例化済み | 商環（PolyBezoutQ 系） | **実**（一般 f で体化は完全証明） | ○ ℚ(ζ_9)=ℚ[x]/(Φ_9) も**既約性さえ用意できれば同じ関数で体化可能**。ただし Galois 群・FieldExtension への接続は未着手（体としての存在証明のみ） |
| `ProfinitePi1Tower`（`IUT/ProfinitePi1.lean` M287F-1） | 塔 `ext:Nat→FieldExtension` ＋ **`restr` は witness データ**（Hom として仮説で受け取る）＋ `restr_self`/`restr_comp` も仮説 | 任意 | **実の型・中身は witness** | ◎ 型としては A3 の主役そのもの。**しかし restr を体の包含から構成した例が 1 つもない**（正直な限定2に明記） |
| `profPi1System`/`profPi1Limit`/`profPi1_proj`（M287F-2/3） | 塔→逆系→逆極限群→射影（`natSystem`/`limitGrp` の直接適用） | 任意の `ProfinitePi1Tower` | **実** | ○ 塔さえ埋まれば自動的に本物の pro-有限群が出る |
| `profPi1_kernel_open`/`profPi1_nbhd_base`（M287F-4） | 射影核が開部分群・開部分群系が1の近傍基（`IUT/ProfiniteTopology.lean` 経由） | 任意の塔 | **実** | ○ pro-有限位相込みで自動的に付与される |
| `profPi1_trivialTower`（M287F-7a） | K=ℚ、全段 `trivialExtension`、`restr`=恒等 | ℚ | **実だが自明（Gal=1 の塔のみ）** | ✗ 非自明塔の実例としては使えない（複数段あっても中身は全て自明群） |
| `AlgCloTower`（`IUT/AlgClosureColimit.lean` M315F-1） | K^sep=colim Lₙ・段間 ring hom embed `step`・`restr` も**同じく witness** | 任意 | **実（同値関係・embAdd は本物）／restr は witness のまま** | ◎ より上位の絶対 Galois群/分離閉包の枠組みだが、**A3 のボトルネックと同一**（restr witness） |
| `GaloisFundamental.lean`（M285F、正直申告4） | Gal(L/L^H)=H の完全定理はあるが「Gal(L^H/K)≅Gal(L/K)/H の**Gal(L^H/K) を FieldExtension として構成する必要**は範囲外」と明記 | — | **実定理だが商体側の FieldExtension 化は未着手** | 参考: restr 構成に必要な「部分体上の Galois 群」自体の構成コストを裏付ける正直申告 |
| `CyclotomicPrimePower.lean`（M386F） | ℚ(ζ_{p^k}) の**次数・分岐指数・different 指数を ℕ 算術で**計算（ℚ(ζ_9): 次数6・e=6・d=9・disc=3^9） | ℕ（整数不変量のみ） | **模型（算術不変量のみ・体そのものは構成していない）** | ✗ A3 塔には使えない。ℚ(ζ_9) の**実体構成は未着手**（別途 `gefField`+Φ_9既約性が必要） |

**要点**: `InverseSystem`/`limitGrp`/`natSystem`/`FieldAut`/`fieldAutGroup`/`FieldExtension`/
`galoisSubgroup`/`galoisGroupGrp` は**すべて一般パラメータで本物**（模型・特殊ケース限定は
一切ない）。`galoisGroupGrp` は任意の `FieldExtension` に対して定義域無制限に本物である
（棚卸し表の主張どおり）。ギャップは機構ではなく「**非自明な体拡大の具体タワーと、
それに付随する具体 restr**」の不在に一元化される。

---

## 2. 制限準同型 res: Gal(E'/K)→Gal(E/K)（E⊆E'）の実装に何が要るか

現状、`ProfinitePi1Tower.restr` と `AlgCloTower.restr` は**どちらも構造体のフィールド
（witness）**であり、σ∈Gal(E'/K) から σ|_E∈Gal(E/K) を計算で作る関数は**コードベースに
1つも存在しない**。既存に近い部品を洗うと:

- **σ の部分体への制限そのもの（σ∘incl' 型の合成）**: 直接の実装はないが、`FieldExtension`
  の `incl : base→top` と `FieldAut.toFun` は合成可能な生の関数なので、`res(σ) := incl⁻¹ ∘
  σ.toFun ∘ incl`（incl の**像の上で**）という定義は原理的に書ける。ただし:
  1. **incl が単射であることの証明**が必要（`FieldExtension` 構造体に単射性公理がないため、
     呼び出し側で証明するか公理として追加する必要がある）。
  2. **σ(incl(E)) ⊆ incl(E) という「部分体保存」の証明**が必要——これが本質的な欠落。
     一般の体拡大 E⊆E' で E'の自己同型が Eを保つとは限らない（正規拡大性が要る）。
     円分塔 ℚ(ζ_3)⊆ℚ(ζ_9) の具体例では代数的には常に成立する（ζ_3=ζ_9³ なので
     σ(ζ_9)=ζ_9^k ⟹ σ(ζ_3)=ζ_9^{3k}=(ζ_9³)^k=ζ_3^k∈ℚ(ζ_3)）が、これを Lean で
     `IsPoly`/商環の正規形（`gefField` の内部表現）の言葉で書き下す証明はゼロから書く必要がある。
  3. **res(σ) の逆写像 invFun の構成**——`FieldAut` は明示逆写像を要求するため、
     res(σ⁻¹) を res(σ) の逆として用意するか、res がその場で invFun を構成する必要がある
     （σ⁻¹ も同様に部分体を保つことの証明が要る＝上記2の対称版）。
  4. **res が群準同型であること**（res(σ∘τ)=res(σ)∘res(τ)）——σ,τ それぞれの部分体保存の
     証明があれば合成は形式的に従う（`fieldAutComp`/`FieldAut.ext` の外延性で閉じる）。

- **既存に「近い」部品**: `GaloisCorrespondence.lean`/`GaloisFundamental.lean` は
  「固定体 L^H」「固定群 Gal(L/M)」という Galois 対応の骨格を持つが、**M285F 正直申告4が
  明記する通り「Gal(L^H/K) を L^H の FieldExtension として構成する必要があり範囲外」**
  ——つまりこの既存機構も、部分体上の Galois 群を独立した `FieldExtension` として
  具体的に立ち上げる作業を素通りしている。res の実装はこの同じ隙間を埋める必要がある。
  `TowerLaw.lean` の `towerLawRestrict`（M281F 系）は**加群**の制限（ベクトル空間の
  scalar restriction）であり、Galois **群**の制限とは無関係（名前が紛らわしいが別物）。

- **新規実装の見積り**: 一般論として「res: Aut_K(E')→Aut_K(E)（E⊆E' 正規かつ σ が E を
  保つ場合）」を抽象的に一発で作る定理は、正規性・分離性の一般論が core に無いため
  射程外（`GaloisFundamental.lean` の正直申告と同型のギャップ）。**現実的な戦略は
  「一般 res 定理」を狙わず、円分塔のような具体ケースで「σ(ζ_9)=ζ_9^k ⟹
  σ(ζ_3)=ζ_3^k」を直接計算で証明し、その計算から res を手組みする**こと
  （QuadraticField.lean の `qdf_decompose`/`qdf_apply` が「σ は σ(√D) で決まる」を
  手組みで閉じたのと同じ精神）。見積り規模: ℚ(√D) の位数2 Galois 計算
  （`QuadraticField.lean`）が約 400 行だったのに対し、ℚ(ζ_9) の次数6 の場合は
  「自己同型は生成元の像で決まる」の一般化（n項分解、下記§4）が必要になり、
  同程度〜数倍の新規行数（概算 400〜800 行規模の新規モジュール）を要すると見込む。

---

## 3. ギャップ表（A3 塔の各段）

| 部品 | 既存で埋まる | 新規が必要 | A1エンジン依存 |
|---|---|---|---|
| 体 K=ℚ | ✅ `ratIUTField` | — | — |
| 体 L₁=ℚ(ζ_3) | ✅ 二重に存在（`qdfField cq3D`／`cq3Field`／`gfiCq3Field`）。ただし3実装は**互いに定義的に別型**（同型輸送は未形式化、`QuadraticField.lean`正直申告2・`GenFieldInstances.lean`も個別体） | 三者のどれを正本にするか選定 ＋（qdf版を使うなら）ζ_3 元の明示構成（cq3-5 と同型の追加証明、小規模） | GEF系(`gfiCq3Field`経由なら要)／qdf系なら不要 |
| Gal(L₁/K) | ✅ `qdfField` 版なら `qdf_galois_order_two` で**位数ちょうど2が既に一般定理として証明済み**（D=cq3D=−3 を代入するだけ） | ほぼ無し（代入＋非平方 witness `qdf_neg_not_square cq3Three` の適用、数行） | 不要 |
| 体 L₂=ℚ(ζ_9) | ✗ 皆無（`CyclotomicPrimePower.lean` は ℕ 算術の不変量のみで実体化していない） | **Φ_9=x⁶+x³+1 の既約性の完全証明**（新規・下記§4で規模評価）＋`gefField` 適用で体化 | ✅ `gefField`/`pgbBezoutQ`/`pibIrreducible` 系（A1 一般構成器）に強く依存 |
| ℚ(ζ_3)↪ℚ(ζ_9) の埋め込み | ✅ 代数的事実 Φ_9(x)=Φ_3(x³) は既に手計算で確認可能（両円分多項式の定義から） | **x↦x³ が商環の関係を保つことの Lean 証明**（`IsPoly`/`pdbDvd` 言葉での well-defined 性、新規・中規模） | ✅ GEF の商環表現に依存 |
| Gal(L₂/K) | ✗ 皆無 | **次数6・巡回・位数ちょうど6 の完全証明**（一般化した「自己同型は生成元の像で決まる」機構が新規に必要、QuadraticFieldのpair分解のn項一般化、新規・大規模） | ✅ GEF の商環表現・正規形に依存 |
| res: Gal(L₂/K)→Gal(L₁/K) | ✗ 皆無（型は`ProfinitePi1Tower.restr`として受け皿があるのみ） | §2で述べた具体計算による手組み構成（新規・中規模、Gal(L₂/K)計算に依存） | Gal(L₂/K)の完成に依存 |
| 逆系・逆極限 | ✅ `natSystem`/`limitGrp`/`profPi1System`/`profPi1Limit` がそのまま適用可 | 無し（2段塔を`ProfinitePi1Tower`に詰めるだけ） | 上記全段の完成に依存 |
| pro-有限位相（開核・近傍基） | ✅ `profPi1_kernel_open`/`profPi1_nbhd_base` が自動的に付与 | 無し | 塔の完成に依存 |

---

## 4. near-term の現実性: 2段塔 ℚ(ζ_3)⊆ℚ(ζ_9) の手組み

**必要な具体部品の列挙**:
1. Φ_9 既約性（`pibIrreducible`/`pibIrreducible_poly` 型）——**最大のボトルネック**。
   既存の既約性証明（`CbrtTwoIrreducible.lean`＝x³−2、`Cq3Irreducible.lean`＝Φ_3）は
   いずれも**次数2・3**で「有理根が無い ⟹ 既約」という一次因子排除だけで閉じる
   （因子分解の可能な次数分割が「1×2」「1×3」しかないため）。Φ_9 は**次数6**であり、
   根がなくても 2×3・2×2×2 等に分解しうるため、この技法は通用しない。標準的な数学の
   証明は「x→x+1 シフト＋Eisenstein の既約性判定法（p=3）」だが、**Eisenstein 判定法
   そのものがコードベースに存在しない**（`Eis*.lean` 群は ℤ_p[[X]] 上の別の理論＝
   Lubin-Tate 形式群の話であり、ℚ[x] 上の Eisenstein 既約性判定とは無関係）。
   ゆえに Φ_9 既約性は「シフト＋Eisenstein 判定法の新規定理」から作るか、あるいは
   次数分割を全数除外する別ルートを新規に組む必要があり、**既存の deg≤3 既約性証明
   （約250行）より確実に大きい新規モジュール**（見積り数百行、Eisenstein版なら
   シフト計算＋判定法本体＋適用の3層）。
2. 埋め込み ℚ(ζ_3)↪ℚ(ζ_9)（x↦x³）——Φ_9(x)=Φ_3(x³) の恒等式はほぼ自明（両辺を
   展開すれば x⁶+x³+1 = x⁶+x³+1）だが、これを GEF の商環（`IsPoly`/`pdbDvd`）の
   言葉で「well-defined な環準同型」として厳密化するのは中規模の新規作業。
3. Gal(ℚ(ζ_9)/ℚ)（位数6・巡回 ≅(ℤ/9)^×）——「自己同型は ζ_9 の像で決まり、像は
   Φ_9 の根でなければならない」という一般化された分解定理が新規に必要
   （`qdf_decompose`/`qdf_apply` の n=6 版、既存に一切なし）。
4. res: Gal(ζ_9)→Gal(ζ_3)——§2 の具体計算（σ(ζ_9)=ζ_9^k ⟹ σ(ζ_3)=ζ_3^{k mod 3}）
   から手組み。Gal(ζ_9) が閉じた後でないと着手不可（依存順）。

**判定**: full 逆極限（無限塔）よりは狭いが、**2段塔でも Φ_9 既約性＋次数6 Galois 分解
という2つの新規・非自明な数学的核が要り、「小さい足場」ではない**。むしろ現時点で
最も安価に「非自明な真の2段 profPi1Limit」を作る近道は、**円分塔そのものではなく
既存の qdf/gqi 二次拡大を使った「定数化する塔」**である: K=L₀(自明)⊊L₁=L₂=…=ℚ(√D)
（D=−1 等、`qdfField`で位数2 Galois 済み）とし、restr(i,j)（1≤i≤j）は**同一体なので
恒等写像**（部分体保存の証明が不要——保存すべき「部分体」が存在しない自明ケース）、
restr(0,j) は**自明群への写像なので任意の関数が自明に群準同型**（Gal(L₀/K)=1 の
一意性）。これは既存の `qdf_galois_order_two` だけで**新規の Φ 既約性・n項分解なしに**
今すぐ構成でき、`profPi1Limit` が Z/2 に収束する**最初の非自明 pro-有限 G_K 近似**を
即座に実証できる（円分塔の代わりの現実的な near-term ターゲットとして推奨）。

---

## 5. A3 status 昇格の保守的見込み（独立監査が最終判定）

- 現状 A3 = 0.5（機構は実だが実例が自明/退化——`graph-meta.json` の柱A注記と整合）。
- **「定数化する二次塔」**（K⊊ℚ(√D)=ℚ(√D)=…、restr が恒等/自明写像で真に構成可能・
  上記near-term近道）が実装されれば、**非自明な pro-有限極限が初めて実現**する。
  ただし塔の非自明性は「1段だけ」で以降定数——円分塔特有の内容（複数の相異なる非自明
  拡大が連鎖する塔）ではないため、保守的に **A3 0.5→0.55 程度**（実例の質は上がるが
  「連鎖する複数非自明拡大」という A3 の本丸には未到達）。
- **ℚ(ζ_3)⊆ℚ(ζ_9) の完全な2段塔**（Φ_9既約性・埋め込み・次数6 Galois・res 全て本物）
  が完成すれば、真に相異なる2段の非自明拡大と本物の制限準同型が揃うため
  **A3 0.5→0.6 程度**が妥当な保守的見積り（「本物の非自明塔」の最初の実例だが、
  無限塔・一般 res 定理・正規性の一般論は依然未達のため 0.6 止まり）。
- **フル逆極限**（Nat 添字の無限に続く円分塔 ℚ(ζ_3)⊆ℚ(ζ_9)⊆ℚ(ζ_27)⊆… や、一般の
  有限 Galois 拡大を尽くす有向系）が実装され、かつ res が個別 witness でなく
  一般定理（正規拡大からの自動構成）として閉じれば **A3 0.7+** まで見込めるが、
  これは正規性・分離性の一般論という core に無い機構を要する大工事であり、
  近道ではない。
- 数値はいずれも本監査ドキュメントの見積りであり、**最終判定は独立監査
  （AUDIT_RUBRIC.md 準拠・自己申告非共有）が実 Lean 定義から確定する**。

---

*本ドキュメントはコード変更なし。共有ファイル（IUT.lean/build.sh/dashboard.md/
graph-meta.json/graph.json/target_ledger.json）は未変更。*
