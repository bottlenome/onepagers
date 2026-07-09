# A1 機構棚卸し — 実 ℚ[x]/(f) 商環構成に使える既存 API の精査

日付: 2026-07-09 / 対象: A1「実数体 K = ℚ[x]/(f) を実際の商環として構成」（`target_ledger.json` status 0.5, weight 8）
入力: `IUT/SimpleExtension.lean`・`IUT/PolyFieldDivision.lean`・`IUT/PolyDivision.lean`・
`IUT/MinimalPolynomial.lean`・`IUT/SeparablePoly.lean`・`IUT/PolyIsomorphism.lean`・
`IUT/RootAdjunction.lean`・`IUT/Field.lean`・`IUT/GaussianRationalField.lean`・`IUT/QuadraticField.lean`

本ドキュメントは**新規 .md 1 個のみ**。コード・共有ファイルは未変更（読解のみ）。

---

## 0. 結論（先出し）

A1 現物（`gqiField`/`qdfField` 系、`IUT/GaussianRationalField.lean`・`IUT/QuadraticField.lean`）は
**carrier = ℚ×ℚ（次数 2 固定・"a+b√D" ハードコード表現）**であり、真の商環 `K[X]/(f)` ではない。
一方 `IUT/SimpleExtension.lean` の `polyCRing`・`quotCRing`・`quotField_of_bezout` は
**任意の可換環・任意次数**で本物に動く一般機構であり、**型は通る**（下記 §2）。
**A1 を「一般次数の真の商環」へ昇格させる本丸の障害は既存機構の欠如ではなく、
(i) `Field268`（抽象体パラメータ）と `IUTField`/`ratRing`（実 ℚ）の間の**接着アダプタが 1 つ欠けている**こと、
(ii) 具体多項式 `f = x³−2` に対する **Bezout 証人（既約性）が honest 仮説のまま持ち回りで、
一度も具体的に埋められていない**ことの 2 点である。両方とも小さい・独立に閉じられる。
既約性さえ埋まれば、A1 は「次数 2 固定」から「次数 3 の本物の商環＋体」へ**動く**（保守的に見て 0.5→0.7 程度、
「一般次数 f」までは動かない——下記 §4）。**最終判定は独立監査に委ねる**。

---

## 1. 機構棚卸し表

| 名前 | 何を構成 | carrier/主語 | 実/抽象/模型 | A1 昇格に使えるか |
|---|---|---|---|---|
| `IUT/SimpleExtension.lean` `polyCRing R` | 多項式環 K[X]（冪級数環 `psRing` の有限台部分環） | 任意 `CRing R`（`R.carrier` 係数列 `PS R` のうち有界台） | **実**（部分環の全環法則を本物証明、sorry 皆無） | **可**。`R := ratRing` を渡せば型が通り `ratRing[X]` が得られる |
| 同 `quotField_of_bezout` | 一般可換環の Bezout ⟹ 商が体 | 任意 `CRing S`・元 `E` | **実**（一般定理、体固有部分なし） | **可**。`S := polyCRing ratRing` で使える |
| 同 `simpleExtRing K f m hf` | 単純拡大環 K[X]/(f) | `Field268 K` 経由（`K.ring`） | **実だが `Field268` 止まり**（K が抽象体パラメータ） | **要接着**。`K : Field268` に ℚ を渡すアダプタが必要（§2 参照。既存ゼロ） |
| 同 `simpleExtC`・`simpleExtC_injective` | 基礎体埋め込み K ↪ K[X]/(f)、単射性 | 同上 | **実**（deg f ≥ 1 で完全証明） | 可（アダプタ経由） |
| 同 `simpleExt_nontrivial` | K[X]/(f) は 1≠0 | 同上 | **実** | 可 |
| 同 `simpleExt_field`（M269F-9） | Bezout（honest 仮説）⟹ K[X]/(f) は体 | 同上 | **実の含意**、前提 `bezout` は **honest 仮説**（未証明入力） | 可だが `bezout` 証人が必要（§3 のギャップ） |
| 同 `SimpleExtData`/`.build`/`simpleExt_exists` | capstone：入力データ（modulus・deg・lead・bezout witness）から体拡大レコード | 同上 | **実の骨組み**、`bezout` フィールドは honest 仮説 | A1 の直接の器。**具体 f の witness を積めば A1 の本体になる** |
| `IUT/PolyFieldDivision.lean` `Field268` | 体の抽象定義（inv 函数 + mul_inv_cancel） | 抽象パラメータ | **抽象**（体固有の除法定理の土台。ℚ に固有化されていない） | 接着アダプタの土台。ratIUTField を Field268 に写す 3 行の def が要る（未実装） |
| 同 `field_division_exists`/`_unique`/`_exists_unique` | 体上除法定理（存在・剰余一意性） | `Field268` パラメータ | **実**（体固有、先頭係数の逆元を本質使用） | A1 直接には不要（既約性判定/gcd 側で将来使う） |
| `IUT/MinimalPolynomial.lean` `PolyEval`/`IsAlgebraic`/`MinPolyData` | 評価準同型・代数的元・最小多項式（一意性・既約性・核=(m)） | `Field268` K, E パラメータ | **実**（ev は honest 仮説として持つ準同型、それ以外完全証明） | A1 に直接不要（K(α)≅K[X]/(m) の**同型構成そのものは範囲外**とヘッダに明記） |
| `IUT/SeparablePoly.lean` `formalDeriv`/`sep_repeated_factor` | 形式微分・重根判定（⟹ 方向のみ） | 任意 `CRing R` | **実**（本物のライプニッツ則の実ケース） | A1 に直接不要（分離性は次層。gcd(f,Df)=1 の⟸方向・体上ユークリッド互除法は未着） |
| `IUT/PolyIsomorphism.lean` 全体 | poly-isomorphism の圏論的剛性（Frobenius-like vs étale-like 二分法） | `Cat`/`Grp` パラメータ（M48F/M51F/M9） | **実**（圏論側）だが**A1（体の代数構成）と無関係** | **不使用**。誤って調査対象に含まれているが多項式環とは無関係の圏論モジュール |
| `IUT/RootAdjunction.lean` `rootAdj_root`/`rootAdj_is_root` | 根 ρ=[X] が f(ρ)=0 を満たすことの本物証明 | `Field268` K パラメータ | **実**（本丸 f(ρ)=0 は完全証明） | A1 の**次の層**（根の存在）に直接使える。接着アダプタ後は無料で付いてくる |
| 同 `rootAdj_root_not_in_base` | deg f≥2 で ρ∉K の像（真の拡大） | 同上 | **実** | A1 の非自明性 witness として直接使える |
| `IUT/Field.lean` `IUTField` | 体の公理系（CRing extend） | 抽象構造 | **実**（公理系自体は本物） | 直接不使用だが `ratIUTField` の型 |
| 同 `ratIUTField` | ℚ が本物の体 | `ratRing`（M115F、`Quot ratRel`） | **実**（本物の ℚ、Bool/Fin 代理でない） | **これが A1 の f のかかる本物の base field**。ただし型が `IUTField` であり `Field268` ではない（§2 のギャップ） |
| `IUT/GaussianRationalField.lean` `gaussQField`/`gqiCarrier` | ℚ(i) を実 ℚ×ℚ 対で構成 | carrier = `ratIUTField.carrier × ratIUTField.carrier` | **実だが次数 2 専用の手書き実装**（`SimpleExtension` の商環を経由しない） | A1 の**現物そのもの**（0.5 の由来）。一般 f への拡張力なし |
| `IUT/QuadraticField.lean` `qdfField D hD` | ℚ(√D) を実 ℚ×ℚ 対で構成、Gal 位数 2 | 同上（D パラメータ化はされたが次数は 2 固定） | **実だが次数 2 専用の手書き実装** | 同上。D 一般化はできたが**次数一般化はできていない**（"a+b√D" のペア表現に構造的に縛られる） |

---

## 2. 昇格に直接使える本物 API — 型チェックの追跡

目標: `ratRing[X]/(x³−2)` を `SimpleExtension.lean` の一般機構で構成できるか。

1. `polyCRing (R : CRing) : CRing` — `R := ratRing`（`IUT/Rationals.lean` の `def ratRing : CRing`）を渡すと
   `polyCRing ratRing : CRing` が**そのまま型チェックを通る**。これは本物の `ℚ[X]`（有限台冪級数）。
2. `quotCRing (S : CRing) (E : S.carrier) : CRing`（`IUT/EisTowerRings.lean`）は完全に一般。
   `S := polyCRing ratRing`, `E : Poly ratRing` を渡せば `quotCRing (polyCRing ratRing) E : CRing` が通る。
   これが「真の商環」＝A1 の目標そのもの。
3. `quotField_of_bezout (S : CRing) (E : S.carrier) (hBez : …) : …` も一般可換環でよく、
   `S := polyCRing ratRing` でそのまま使える——体固有の仕組み（先頭係数の逆元）を要求しない
   一般 Bezout⟹体の定理なので、**ここに `Field268` は要らない**。
4. ただし `SimpleExtension.lean` の capstone 経路（`simpleExtRing`/`SimpleExtData.build`）は
   **`K : Field268` を引数に取る形で書かれている**（`K.ring` を `polyCRing K.ring` に渡す）。
   `ratIUTField : IUTField` は `Field268` ではない——**別の構造体**（`Field268` は `ring : CRing` フィールドで
   包む形、`IUTField` は `CRing` を `extend` する形）。したがって
   `simpleExtRing (K := ratIUTField) …` は**そのままでは型エラー**になる。
   **必要な接着（未実装・3〜5 行で閉じる見込み）**:
   ```
   def ratField268 : Field268 where
     ring := ratRing
     invf := ratIUTField.inv
     mul_inv_cancel := ratIUTField.mul_inv_cancel
   ```
   `IUTField.mul_inv_cancel` の型 `∀ x, x ≠ zero → mul x (inv x) = one` は `Field268.mul_inv_cancel` の型と
   **同一シグネチャ**（フィールド名だけ違う）なので、上記アダプタは本物の再証明不要な純粋な glue。
   これが存在しないことが、`quotField_of_bezout`（型は通る・一般）と
   `simpleExt_field`/`SimpleExtData`（`Field268` 経由・現状 ℚ に未接続）の間の**唯一の配線ギャップ**。

**結論**: `polyCRing ratRing` と `quotCRing (polyCRing ratRing) E` は**ratRing のままで直接使える**
（アダプタ不要）。`SimpleExtension.lean` の capstone（体化まで含む完成形）を使うには
`Field268` アダプタ（上記 3〜5 行）が要る。**型チェックそのものに障害はない**——
アダプタの新規作成（承認済み足場 (c) 相当、または昇格 (a) の一部）だけが要る。

---

## 3. ギャップ表

ℚ[x]/(f) の**一般次数の真の商環+体**を得るために欠けているものを列挙し、既存で埋まるか新規実装が要るかを判定。

| ギャップ | 内容 | 既存で埋まるか | 埋める新規実装（想定） |
|---|---|---|---|
| G1: `Field268` ↔ `ratRing`/`ratIUTField` 接着 | `SimpleExtension`/`PolyFieldDivision`/`MinimalPolynomial`/`RootAdjunction` が要求する `Field268 K` に ℚ を渡す変換 | **既存で埋まる**（§2 の 3〜5 行 glue、新規数学ゼロ） | `ratField268`（アダプタ def 1 個） |
| G2: 具体多項式 f の係数列表現 | `f = x³−2` を `PS ratRing = Nat → QRat` の有限台元として書き下す（`hf : IsPolyBounded ratRing f 4`・`hlead : f 3 ≠ 0`） | 部分的（`psSingle`/`psC`/`psAdd` 等の組立部品は既存、具体 f のインスタンスは**未実装**） | 並行スライス **CubicPolyQ**（f=x³−2 の多項式インスタンス）がここを埋める想定 |
| G3: 既約性 ⟹ Bezout（`SimpleExtData.bezout`） | 「f で割り切れない任意 a が f と互いに素」の**具体証人**（cubic x³−2 の場合） | **既存で埋まらない**（`SimpleExtension.lean` ヘッダが明言する honest 仮説。素の既約性からの拡張ユークリッド互除法は「別モジュール」と明記） | 並行スライス **PolyBezoutQ**（拡張ユークリッド）が一般の gcd 計算を提供、それを x³−2 の既約性判定に適用する接続層が追加で要る。x³−2 の既約性は「次数 3 で有理根なし ⟺ 既約」（有理根定理）に帰着するのが定石 |
| G4: x³−2 に有理根がない | ∛2 ∉ ℚ（有理根定理の適用に必要な事実） | 既存で埋まらない（数論的命題、未実装） | 並行スライス **CubeRootTwoIrrational**（∛2∉ℚ）がここを埋める想定。ただし厳密には「次数 3 多項式が有理根を持たない ⟹ 既約」は次数 3 特有の定理でありこれ自体も一段の補題が必要（有理根定理そのものは本監査対象ファイルに存在しない） |
| G5: 一般次数 f への拡張 | 任意次数・任意既約多項式に対する同じ構成 | 既存の `SimpleExtension` 機構自体は次数非依存（`m : Nat` パラメータ）なので**構造的には可能** | 「一般 f の既約性判定手続き」自体は未実装（gcd/ユークリッド互除法を体上除法 `field_division_exists` の上に構成する層が要る——`PolyFieldDivision.lean` ヘッダが「別途重い後続」と明記） |
| G6: 現行 A1 実体（`gqiField`/`qdfField`）からの乗換え | 既存の次数 2 ハードコード実装を `SimpleExtension` ベースの一般商環に置換するか、並存させるか | N/A（設計判断、独立監査/親の承認事項） | 方針要決定（本ドキュメントは判定しない） |

---

## 4. A1 台帳の昇格見込み（保守的予測）

- **単一 f = x³−2 の実三次数体**を上記 G1〜G4 を埋めて構成できれば、A1 は
  「carrier=ℚ×ℚ・次数2固定」から「**carrier=真の商環 `quotCRing (polyCRing ratRing) f`・次数3・本物の Bezout 証人つき**」
  へ**具体的に**動く。これは AUDIT_RUBRIC の 0.5（実の忠実部分ケース）の**中でも上位**——
  「次数 2 のみ」という限定が「次数 3 の具体例で一般次数機構を実証」に置き換わるため、
  保守的に見て **0.5 → 0.6〜0.7 相当**が妥当な範囲と推測する（0.5→1.0 への飛躍は不可——
  一般 f への拡張（G5）が別途残るため「実の忠実部分ケース」の域を出ない）。
- **一般次数 f（任意の既約多項式）**まで到達するには G5（ユークリッド互除法による既約性判定の一般化）が要り、
  これは `field_division_exists`（体上除法、既に完全証明済み）の上に構成する**次の一段**であって、
  今回棚卸しした 10 ファイルの範囲には含まれない（`PolyFieldDivision.lean`/`SeparablePoly.lean` の
  正直な限定欄がともに「gcd/ユークリッド互除法は次層」と明記）。
- 現行 `gqiField`/`qdfField`（ℚ×ℚ 対のハードコード次数 2 実装）を A1 の実体として残すか、
  `SimpleExtension` ベースの一般商環に置き換えるかは設計判断であり、本ドキュメントは判定しない。
  どちらにせよ**独立監査が最終的な status 判定を行う**（本ドキュメントの見積もりは実装前の予測に留まる）。

---

## 5. 並行スライスとの対応付け

親が並行実行中の実装スライス（新規ファイルのみ・本ドキュメント作成時点では `IUT/` に未着地）が
埋めるギャップは以下の通り対応する:

| 並行スライス | 埋めるギャップ | 対応する表の行 |
|---|---|---|
| **CubeRootTwoIrrational**（∛2 ∉ ℚ） | x³−2 に有理根がないことの数論的事実 | G4（§3）。有理根定理経由で x³−2 の既約性判定の前提を供給 |
| **CubicPolyQ**（x³−2 の多項式インスタンス） | 具体多項式 f を `PS ratRing` の有界係数列として書き下す | G2（§3）。`SimpleExtData.modulus`/`deg`/`bound`/`lead` の具体 witness |
| **PolyBezoutQ**（拡張ユークリッド） | 既約性 ⟹ Bezout 証人 `∃u v, uf+va=1` の構成手続き | G3（§3）。`SimpleExtData.bezout` フィールドの具体証人（CubeRootTwoIrrational・CubicPolyQ と合わせて使う） |

3 スライスが揃えば、`ratField268`（G1・本ドキュメントが指摘した未実装の glue、G1 自体は 3〜5 行で
別途埋める必要がある——3 スライスの範囲外）と合わせて、`SimpleExtData` の全フィールドが具体値で埋まり
`SimpleExtData.build ratField268 d` が **x³−2 の実三次数体**（真の商環・本物の Bezout 由来体構造）を
産出できる状態になる、というのが本棚卸しの結論である。G1（`ratField268` アダプタ）は
どのスライスの担当にもなっていないため、**統合時に親が追加で用意する必要がある**（3〜5 行、新規数学ゼロ）。

---

## 6. 要約（8〜12 行）

`IUT/SimpleExtension.lean` の `polyCRing`/`quotCRing`/`quotField_of_bezout` は一般可換環・任意次数で動く
**本物の API**であり、`ratRing`（実 ℚ、`IUT/Rationals.lean`）にそのまま型が通る（アダプタ不要）。
一方、体化まで含む capstone（`simpleExtRing`/`SimpleExtData.build`）は `Field268`（抽象体パラメータ）を
要求し、実 ℚ の型は `IUTField`（`ratIUTField`）で別構造体のため、**3〜5 行の接着アダプタ
（`ratField268`）が未実装**という唯一の配線ギャップがある——新規数学は不要。
現行 A1 実体（`gqiField`/`qdfField`、`IUT/GaussianRationalField.lean`・`IUT/QuadraticField.lean`）は
carrier=ℚ×ℚ・次数 2 固定のハードコード実装であり、`SimpleExtension` の一般商環を経由していない
（0.5 の由来そのもの）。真の障害は既約性の Bezout 証人（`SimpleExtData.bezout`）が
`SimpleExtension.lean`/`PolyFieldDivision.lean`/`SeparablePoly.lean` いずれのファイルでも
honest 仮説のまま一度も具体的に埋められていないこと。並行スライス CubeRootTwoIrrational
（∛2∉ℚ）・CubicPolyQ（x³−2 の多項式化）・PolyBezoutQ（拡張ユークリッド）はこのギャップを直接埋める設計であり、
3 つが揃えば x³−2 の実三次数体（真の商環＋本物の Bezout 由来体構造）が構成可能になる。
`MinimalPolynomial.lean`・`RootAdjunction.lean` は根の存在・最小多項式の性質を無料で供給する上位層で
A1 の直接ブロッカーではなく、`SeparablePoly.lean`（分離性）・`PolyIsomorphism.lean`（poly-isomorphism 圏論）は
A1 に無関係。保守的な見積もりでは、G1〜G4 が埋まれば A1 は 0.5→0.6〜0.7 程度まで動きうるが、
一般次数 f への拡張（既約性判定の一般ユークリッド互除法、G5）は別途残るため 1.0 には届かない。
最終判定は独立監査に委ねる。
