# A1 実数体建設 設計書 — ℚ[x]/(x³−2) = ℚ(∛2) を本物の商環＋実体として建てる

日付: 2026-07-09 ／ 種別: **設計ドキュメントのみ**（実装は次ラウンド）
分類: **[実／昇格(a)]** — 既存の抽象商環機構（`polyCRing`・`quotCRing`・
`quotField_of_bezout`・`SimpleExtData`、全て Field268 抽象止まり）を
**実 ℚ（`ratRing`/`ratIUTField`）で具体化**し、一般次数の実数体
ℚ[x]/(f) の最初の本物のインスタンス **ℚ(∛2)（実三次数体）** を得る。
A1 台帳「実数体 K=ℚ[x]/(f) を実際の商環として構成」（現状 0.5 =
`QuadraticField.lean` の carrier ℚ×ℚ 対・次数 2 のみ）の頭打ちを破る。

---

## 0. 既存機構の実/模型判定（read 済み・設計の前提）

| 部品 | 場所 | 判定 | 根拠 |
|---|---|---|---|
| `polyCRing R` / `Poly R` / `polyC` | `IUT/SimpleExtension.lean` M269F-2/3 | **実** | psRing の有限台部分環として全環法則を Subtype.ext で証明済み。R は任意 `CRing` なので `ratRing` をそのまま入れられる |
| `quotCRing S E` / `idealRel` / `quotOf` / `quot_exact_ideal` | `IUT/EisTowerRings.lean` M109（`idealRel` は `IUT/EisensteinRing.lean`） | **実** | Quot ベースの一般単項イデアル商環。任意 CRing で使える |
| `quotField_of_bezout` | `IUT/SimpleExtension.lean` M269F-4 | **実** | Bezout ⟹ 非零元に逆元（∃ 形・choice-free）。一般 S・E で証明済み |
| `simpleExtRing` / `simpleExtC` / `simpleExtC_injective` / `simpleExt_nontrivial` / `simpleExt_field` / `SimpleExtData.build` | `IUT/SimpleExtension.lean` M269F-5〜10 | **実だが Field268 抽象止まり** | K : `Field268` はパラメータのまま。**ℚ での実例化はゼロ**（`Field268` に `ratRing` を入れたファイルは 9 ファイル中 0）。honest 仮説 `SimpleExtData.bezout` が deferred |
| `field_division_exists` / `field_division_unique` / `poly_mul_g_bounded_zero268` / `mul_eq_zero_left268` / `psMul_g_top_coeff268` | `IUT/PolyFieldDivision.lean` M268F | **実** | 除法定理は `(R : CRing) (invf) (hinv)` を裸で受けるので `ratRing`+`qInv`+`qMul_inv` が直接刺さる。剰余の一意性・整域正則性も同型 |
| `evalSum` / `evalHom_add` / `evalHom_mul` / `evalHom_stable` / `evalHomId` | `IUT/EvaluationHom.lean` M274F | **実** | 打ち切り点明示の評価準同型。ι=id・K=E=ratRing でそのまま使える（`evalHom_id_mul`） |
| `rootAdj_root` / `rootAdj_is_root` / `rootAdj_root_not_in_base` | `IUT/RootAdjunction.lean` M275F | **実** | ρ=[X] が f の根・deg≥2 で ρ∉K 像。Field268 パラメータのまま → ℚ 実例化で α=∛2 の言明が即出る |
| `ratRing` / `qInv` / `qMul_inv` / `quot_exact_rat` | `IUT/Rationals.lean` M115F | **実** | PreRat/Quot 表現。`prInv` は `if hz : x.num = 0`（Int の DecidableEq）で choice-free |
| `ratIUTField : IUTField` | `IUT/Field.lean` M264F-5 | **実** | `mul_inv_cancel`・`zero_ne_one` 証明済み → `Field268` への梱包は 3 行 |

**結論**: 必要部品は全て本物で揃っており、欠けているのはただ一つ——
`SimpleExtData.bezout`（f のイデアル極大性）の**実 ℚ・実 f での証明**。
これが本設計の本丸（§2）。位置づけは**昇格(a)**: M269F ヘッダが自ら
deferred と申告した「素の既約性から拡張ユークリッド互除法で Bezout を
構成する重い後続」を、f = x³−2 で実際に果たす。

---

## 1. 最終目標の Lean statement 候補

新規モジュール（実装ラウンドで 1〜3 ファイルに分割可、§4 の DAG 参照）。
記法: `Q := ratRing`、`P := polyCRing ratRing`。

```lean
-- (G0) ℚ の Field268 梱包（既存 ratIUTField の詰め替え・3 行）
def ratField268 : Field268 :=
  ⟨ratRing, qInv, fun a ha => ratIUTField.mul_inv_cancel a ha⟩

-- (G1) 法多項式 f3 = x³ − 2 ∈ PS ratRing（係数列表現）
def qTwo : QRat := ratOfInt.map 2
def cbrtTwoPS : PS ratRing :=
  psAdd ratRing (psMono ratRing 3) (psC ratRing (ratRing.neg qTwo))
-- 係数確定（if 展開の rfl 級補題群）:
--   cbrtTwoPS 0 = neg 2, cbrtTwoPS 1 = 0, cbrtTwoPS 2 = 0, cbrtTwoPS 3 = 1
theorem cbrtTwo_bound : IsPolyBounded ratRing cbrtTwoPS 4
theorem cbrtTwo_lead  : cbrtTwoPS 3 ≠ ratRing.zero   -- 1 ≠ 0（ratIUTField.one_ne_zero）

-- Poly ratRing の元としての f3（= SimpleExtData 経由の simpleExtModulus と一致）
def cbrtTwoModulus : Poly ratRing :=
  simpleExtModulus ratField268 cbrtTwoPS 3 cbrtTwo_bound

-- (G2) 本丸: Bezout（イデアル (f3) の極大性）
theorem cbrtTwo_bezout :
    ∀ a : Poly ratRing,
      ¬ idealRel P cbrtTwoModulus a P.zero →
      ∃ u v : Poly ratRing,
        P.add (P.mul u cbrtTwoModulus) (P.mul v a) = P.one

-- (G3) 実三次数体 ℚ(∛2) — carrier は本物の商環
--      (quotCRing (polyCRing ratRing) cbrtTwoModulus).carrier
def cbrtTwoData : SimpleExtData ratField268 :=
  { modulus := cbrtTwoPS, deg := 3, bound := cbrtTwo_bound,
    lead := cbrtTwo_lead, deg_pos := by omega,
    base_nontrivial := ratIUTField.one_ne_zero,   -- 型合わせ調整あり
    bezout := cbrtTwo_bezout }                    -- ← honest 仮説を本物で充填

def cbrtTwoRing : CRing := simpleExtRing ratField268 cbrtTwoPS 3 cbrtTwo_bound
def cbrtTwoField : SimpleFieldExt ratField268 := cbrtTwoData.build ratField268
-- 射影定理（監査向け見出し）:
theorem cbrtTwo_has_inverses :
    ∀ x : cbrtTwoRing.carrier, x ≠ cbrtTwoRing.zero →
      ∃ y, cbrtTwoRing.mul x y = cbrtTwoRing.one
theorem cbrtTwo_nontrivial : cbrtTwoRing.one ≠ cbrtTwoRing.zero
theorem cbrtTwo_emb_injective : {…}  -- ℚ ↪ ℚ(∛2) 単射（simpleExtC_injective 実例化）

-- (G4) ∛2 の実在: α := [X] とその言明（RootAdjunction M275F の実例化）
def cbrtTwoAlpha : cbrtTwoRing.carrier :=
  rootAdj_root ratField268 cbrtTwoPS 3 cbrtTwo_bound
theorem cbrtTwo_alpha_cubed :   -- α³ = emb(2)（rootAdj_is_root: f3(α)=0 の整理）
    cbrtTwoRing.mul cbrtTwoAlpha (cbrtTwoRing.mul cbrtTwoAlpha cbrtTwoAlpha)
      = (simpleExtC ratField268 cbrtTwoPS 3 cbrtTwo_bound).map qTwo
theorem cbrtTwo_alpha_not_rational :  -- α ∉ ℚ 像（rootAdj_root_not_in_base、deg 3 ≥ 2）
    ∀ c : QRat, cbrtTwoAlpha ≠ (simpleExtC …).map c
```

体の形は既存規約どおり **∃ 形**（`SimpleFieldExt.has_inverses`）。全域
`inv` 付き `IUTField` への昇格は Prop の ∃ からの witness 抽出 =
Classical.choice を要するため本設計の対象外（§5 の後続に道筋のみ記す）。

---

## 2. hBez をどう証明するか（最大の難所）

### 2.1 候補比較

**(i) 一般拡張ユークリッド互除法**（次数の整礎再帰で任意の f・a に
gcd と Bezout 係数を構成し、「f 既約 ⟹ gcd は単元 or f の同伴」で 1 に潰す）
- 必要物: 次数の完全な簿記（bound でなく真の deg。有限台からの deg 抽出は
  係数の零判定を全域で要し、抽象体では非可述——ℚ では可述だが装置が重い）、
  gcd の整除性、「f の約元は単元 or 同伴」の因数分解解析、同伴性の処理。
- 評価: core Lean で書けなくはないが、**新規補題 15〜20 本級**の重量。
  一般 f への道としては正しいが、A1 の頭打ちを破る第一歩には過大。

**(ii) 次数 3 固定の有限深度ユークリッド鎖**（採用）
- deg f3 = 3 は、剰余の次数が 3 → ≤2 → ≤1 → 0 と**最大 3 回の除法で
  必ず停止**することを意味する。再帰・整礎性・deg 抽出装置が一切不要で、
  各段は `field_division_exists`（既存・実）の 1 回呼び出し + 有限の
  場合分け。既約性の使用箇所は「割り切れた葉」2 箇所に局在し、どちらも
  「f3 の一次因子 ⟹ 有理根」1 本の補題（§3）に還元される。
- 評価: **core Lean で現実的なのはこちら**。新規補題 8〜10 本、全て
  既存イディオム（rsum 計算・psRing 環法則・Quot.ind + Decidable.em）の
  組み合わせ。(i) は将来の一般 f 用後続として §5 に明記する。

### 2.2 採用案の構造（鎖の設計）

中間述語（PS レベル・bound 持ち回り）:

```lean
def BezB (x y : PS ratRing) : Prop :=
  ∃ (u v : PS ratRing) (Nu Nv : Nat),
    IsPolyBounded ratRing u Nu ∧ IsPolyBounded ratRing v Nv ∧
    psAdd ratRing (psMul ratRing u x) (psMul ratRing v y) = psOne ratRing
```

（等式は PS = 関数の等式。除法の出力 `∀ j, …` は funext で持ち上げ、
以後の代数は **psRing の CRing 法則**（mul_assoc/mul_comm/left_distrib、
全て関数レベル等式で証明済み）で行う——rsum の手計算を避ける鍵。）

**核補題 2 本**（再利用で鎖全体を賄う）:

1. `bez_const`: y が非零定数（`IsPolyBounded y 1`・`y 0 ≠ 0`）なら任意 x で
   `BezB x y`。witness u := 0、v := psC (qInv (y 0))。
   一行: (psC c⁻¹)·y = psC(c⁻¹·c) = 1（y = psC (y 0) を bound-1 から確定、
   psC の乗法性は `polyC`/`psConstHom` 既存）。
2. `bez_descend`: `w = psAdd (psMul q g) rr` かつ `IsPolyBounded q Nq` かつ
   `BezB g rr` ⟹ `BezB w g`。
   一行: u·g + v·rr = 1 に rr = w − q·g を代入し
   **u' := v、v' := u + neg (v·q)** で u'·w + v'·g = 1（psRing の分配・結合で
   純代数）。bound は `simpleExt_add_bounded`/`simpleExt_mul_bounded`（既存）。

**主定理 `cbrtTwo_bezout` の場合分け**（各除法は `field_division_exists
ratRing qInv (ratIUTField.mul_inv_cancel …)` の実例化。bound の引数合わせ
のみ注意——署名は `IsPolyBounded w (N+m)`）:

```
入力 a（bound Na を a.property から ∃ 除去で取得; Prop ゴールなので合法）
段0: a ÷ f3 (m=3, N:=Na)            → a = q·f3 + r,  IsPolyBounded r 3
場合分け r 2, r 1, r 0 の零判定（§2.3 の qratZeroOrNe で choice-free）:
├─ r2≠0（deg r=2）: f3 ÷ r (m=2, N:=2) → f3 = q₁·r + r₁, bound r₁ 2
│   ├─ r₁1≠0（deg r₁=1）: r ÷ r₁ (m=1, N:=2) → r = q₂·r₁ + r₂, bound r₂ 1
│   │   ├─ r₂0≠0: bez_const → BezB r₁ r₂ →(descend ×2)→ BezB f3 r
│   │   └─ r₂0=0: r = q₂·r₁ 完全割り ⟹ f3 = (q₁·q₂ + 1)·r₁ で
│   │             f3 が一次因子 r₁ を持つ → §3 の葉補題 → ∃t,t³=2 → 矛盾
│   ├─ r₁1=0・r₁0≠0: r₁ 非零定数: bez_const → BezB r r₁ →(descend)→ BezB f3 r
│   └─ r₁1=0・r₁0=0: f3 = q₁·r 完全割り ⟹ 頂点係数論法（§2.4）で
│                    q₁ は一次（q₁2=0・q₁1≠0）→ 葉補題（w:=r, g:=q₁）→ 矛盾
├─ r2=0・r1≠0（deg r=1）: f3 ÷ r (m=1, N:=3) → f3 = q₁·r + r₁, r₁ 定数
│   ├─ r₁0≠0: bez_const → BezB f3 r
│   └─ r₁0=0: f3 = q₁·r で一次因子 r → 葉補題 → 矛盾
├─ r2=r1=0・r0≠0: r 非零定数: bez_const → BezB f3 r（直接）
└─ r2=r1=r0=0: r = psZero（bound 3 + 3 係数零で funext）⟹ a = q·f3
              ⟹ idealRel P F3 a 0（witness q を Poly 化・Subtype.ext）
              ⟹ 前提 ¬idealRel と矛盾
最後: BezB f3 r → bez_descend (a = q·f3 + r) → BezB a f3
      → add_comm で並べ替え・Poly へ梱包（funext + Subtype.ext、
        val (polyMul …) = psMul … は定義的 rfl）→ ゴール
```

### 2.3 QRat の零判定（choice-free の要）

抽象体では「x = 0 ∨ x ≠ 0」は排中律（`Field.lean` の正直申告どおり）。
**実 ℚ では構成的に取れる**——これ自体が小さな昇格:

```lean
theorem qratZeroOrNe : ∀ x : QRat, x = ratRing.zero ∨ x ≠ ratRing.zero
-- Quot.ind で代表 r を取り Decidable.em (r.num = 0)（Int の DecidableEq）:
--   num=0 → Quot.sound (r.num·1 = 0·r.den)、num≠0 → quot_exact_rat で反駁
```

`Rationals.lean` の `prInv`（`if hz : x.num = 0`）・`ratRel_inv` の
`Decidable.em` と同じイディオム。新規 axiom なし。

### 2.4 完全割りの葉での次数降下（頂点係数論法）

f3 = q₁·r（r 二次・r2≠0、q₁ bound 3）から q₁ が一次であることの抽出:
- `psMul_g_top_coeff268`（既存 M268F-6a）で (q₁·r)₄ = q₁2·r2 = f3ps 4 = 0、
  `mul_eq_zero_left268`（既存・invf=qInv）で **q₁2 = 0**。
- 同様に (q₁·r)₃ = q₁1·r2 = f3ps 3 = 1 ⟹ **q₁1 ≠ 0**（さもなくば 0=1、
  `ratIUTField.one_ne_zero` に反する）。
- あとは psMul の可換で f3 = r·q₁ とし、葉補題（§3）に g:=q₁ で渡す。

---

## 3. 既約性の使い方（有理根なし ⟹ 三次で既約）

数学: x³−2 は有理根を持たない（∛2∉ℚ）。三次多項式は可約なら必ず一次
因子を持つので、§2.2 の鎖では「一次因子が出た瞬間に有理根が出る」形で
既約性を消費する。**「三次で根なし ⟹ 既約」を一般命題として証明する
必要はなく**、鎖の 2 種類の葉（一次因子 r₁ / 一次余因子 q₁）だけ潰せば
よい。両葉は次の 1 本に還元される:

```lean
-- 葉補題: f3 の一次因子は有理立方根を生む（矛盾はここでは出さない）
theorem cbrt_linear_factor_root
    (w g : PS ratRing) (Nw : Nat)
    (hw : IsPolyBounded ratRing w Nw)
    (hg : IsPolyBounded ratRing g 2) (hg1 : g 1 ≠ ratRing.zero)
    (heq : cbrtTwoPS = psMul ratRing w g) :
    ∃ t : QRat, ratRing.mul t (ratRing.mul t t) = qTwo
```

Lean 化ステップ（全て M274F の既存評価装置で機械的）:
1. 根 t := neg ((g 0)·qInv (g 1))。`evalSum (evalHomId ratRing) t g 2 = 0`:
   rsum 2 項展開 g0·1 + g1·t、`qMul_inv`（g1≠0）で g1·(g0/g1) = g0、
   add_neg で消える。
2. `evalSum … cbrtTwoPS 4 = t³ − 2`: rsum 4 項の if 展開（係数確定補題）。
3. wlog で w の bound を Nw+2 に持ち上げ（`isPolyBounded_mono`、
   Nw+2+3 ≥ 4 を常に確保）、`evalHom_id_mul`（M274F-9c）:
   ev(w·g) at (Nw'+2+1) = ev w · ev g = ev w · 0 = 0。
   `evalHom_stable`（M274F-3）で ev f3 の打ち切り点 4 と Nw'+3 を同定。
4. t³ − 2 = 0 ⟹ t³ = 2（`CRing.eq_of_sub_eq_zero` 系）。

**矛盾の供給源（外部インターフェース）**: 親が別スライスで実証中の

```lean
-- 期待署名（形が異なる場合はアダプタ補題 1 本を DAG に追加）
theorem no_rat_cube_two : ∀ t : QRat, ratRing.mul t (ratRing.mul t t) ≠ qTwo
```

を **`cbrtTwo_bezout` 本体だけ**が消費する（葉補題は ∃t を「生産」する
だけにして依存を切る）。親スライスが Int 形（n³ ≠ 2·d³ 等）で上がる
場合は Quot.ind + `quot_exact_rat` + 分母の正値でアダプタを書く（S 級）。
未着ならば `cbrtTwo_bezout` を no_rat_cube_two を仮説引数に取る形で先行
実装し、着地後に充填する（正直申告付き・§4 の N0）。

---

## 4. 順序付き実装チェックリスト（DAG）

sorry は書かない。各項目は「型＋一行スケッチ」。**Wave 内は並列可・
Wave 間は直列**。tier は CLAUDE.md のモデル配分規則に整合。

**Wave 0（4 本並列可・独立）**
- **N0**〔外部・進行中〕`no_rat_cube_two`: 親の別スライス。本設計は署名
  合意のみ（§3）。
- **N1**〔S/M〕基礎データ: `ratField268`（詰め替え rfl 級）、`qTwo`、
  `cbrtTwoPS`、係数確定 4 本（if 展開）、`cbrtTwo_bound`（i≥4 で両項消える）、
  `cbrtTwo_lead`（1≠0）。
- **N2**〔M〕`qratZeroOrNe`: Quot.ind + Decidable.em(num=0) + Quot.sound /
  quot_exact_rat（§2.3）。
- **N3**〔S/M〕PS 汎用小補題: `isPolyBounded_mono`（N≤M で伝播・omega）、
  `bound_drop`（bound (n+1) ∧ 係数 n = 0 → bound n・場合分け）、
  `const_poly_eq_psC`（bound 1 → h = psC (h 0)・funext + if）、
  `psC_mul_left`（psMul (psC c) h = c を各係数に掛けたもの・
  rsum_single_middle 型、既存 `psMul_psC` の左版）、
  `poly_pointwise_eq`（∀j 等式 → funext → Subtype.ext の梱包 3 行）。

**Wave 1（3 本並列可・Wave 0 のみに依存）**
- **N4**〔M・本設計の計算的難所〕`cbrt_linear_factor_root`（§3）:
  依存 N1・N3。EvaluationHom の evalSum/evalHom_id_mul/evalHom_stable の
  実例化 + rsum 4 項展開。
- **N5**〔M〕`BezB`・`bez_const`・`bez_descend`（§2.2）: 依存 N3。
  psRing 環法則の純代数 + bound 伝播（simpleExt_add/mul_bounded 既存）。
- **N6**〔M〕`cbrt_cofactor_linear`（§2.4 の頂点係数論法）: 依存 N1・N2。
  psMul_g_top_coeff268 + mul_eq_zero_left268 の実例化 2 発。

**Wave 2（直列・1 本）**
- **N7**〔L=fable（詰まり時）または M=opus 主導〕`cbrtTwo_bezout`（§2.2 の
  組み立て）: 依存 N1〜N6（+ N0 または仮説引数）。
  field_division_exists を 3 箇所で実例化し、qratZeroOrNe の入れ子場合
  分け（最大 3 重）で 8 分岐を各 2〜10 行に潰す。r=0 分岐の idealRel
  構成（neg_zero/add_zero 整形）と最終 Poly 梱包（poly_pointwise_eq）も
  ここ。**分量的に最大の 1 ファイル**。
- **N7'**〔S・N7 と同時に着手可〕`idealRel_zero_iff` 整形補題:
  `idealRel P E a P.zero ↔ ∃ h, a = P.mul h E`（neg_zero・add_zero）。

**Wave 3（2 本並列可・capstone）**
- **N8**〔S〕`cbrtTwoData`/`cbrtTwoRing`/`cbrtTwoField`/射影 3 定理（G3）:
  SimpleExtData.build への充填のみ・新規証明ほぼゼロ。
- **N9**〔M〕`cbrtTwoAlpha`/`cbrtTwo_alpha_cubed`/`cbrtTwo_alpha_not_rational`
  （G4）: rootAdj_is_root の rootAdjEval（Σ_{k≤3} emb(f_k)·ρ^k = 0）を
  「ρ³ = emb 2」へ整理する rsum 4 項展開 + 移項 1 本、
  rootAdj_root_not_in_base は deg 3 ≥ 2 の実例化。

検収基準（全 Wave 共通）: `#print axioms` = `[propext, Quot.sound]` のみ・
sorry 皆無・新規 Classical.choice 皆無・禁止タクティク不使用。
共有ファイル（IUT.lean 等）の更新は親が統合時に実施。

---

## 5. 正直な限定の予測（A1 をどこまで動かしうるか・保守的）

**動くもの**: A1「実数体 K=ℚ[x]/(f) を実際の商環として構成」に対し、
carrier が文字どおり `(quotCRing (polyCRing ratRing) f3).carrier` である
実三次数体が、体性（∃ 形逆元）・ℚ の単射埋め込み・α³=2・α∉ℚ 込みで
立つ。現状 0.5 の根拠（ℚ×ℚ 対 = 商環を経由しない次数 2 の直積模型）を
質的に超える。**予測: 0.5 → 0.7 前後**（独立監査次第。0.5 据え置きも
あり得るが、「実際の商環として」という文言には初めて正面から答える）。

**動かない・残る限定（§4 規約により消さない）**:
1. **単一 f = x³−2 のみ**。一般既約 f への Bezout は未達（一般拡張
   ユークリッド互除法 + 一般次数簿記 + 「約元は単元 or 同伴」= §2.1(i)
   が名前付き後続）。A1 満点には一般 f（少なくとも既約性を仮説に取る
   一般定理 + 複数実例）が要ると見るべき。
2. **逆元は ∃ 形**。全域 inv 付き `IUTField` インスタンス化は、
   `field_division_exists` の Σ 型（構造体返し）リファクタ =
   「除法**関数**」の構成が前提（証明は既に witness 構成的なので数学的
   障害はないが、別スライスの重さ）。これも名前付き後続。
3. **次数 3 の完全抽出はしない**: 1, α, α² の一次独立（ℚ 上 3 次元）は
   `rootAdj_root_not_in_base`（α∉ℚ）止まり。基底・次数理論は後続。
4. **N0 依存**: `no_rat_cube_two` が親スライスから供給されるまでは
   `cbrtTwo_bezout` は同命題を仮説引数に持つ（着地後に充填し限定を消す）。

**波及（本設計の副産物・complete_pct 外の正直な記載）**: `ratField268`・
`qratZeroOrNe`・BezB イディオムは、E6（ℚ(ζ_l) 一般族）や A3（一般
K[x]/(f) 数体の塔）が同じ形の Bezout を要するときの再利用資産になる。
