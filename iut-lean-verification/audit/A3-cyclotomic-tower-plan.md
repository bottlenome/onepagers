# A3 円分塔設計書 — 実プロファイナイト Galois 群 Gal(ℚ(ζ_{p^∞})/ℚ) を円分塔の逆極限で建てる

日付: 2026-07-09 ／ 種別: **設計ドキュメントのみ**（実装コード無し・共有ファイル不更新）
分類: **[実／本物建設(b) の設計]** — A3 台帳（weight 12・現 status 0.5、
満点条件「有限 Galois 群の逆極限を本物のプロファイナイト群として構成し実 G_K に接続」）
の頭打ちを破る Phase III 本丸の段階分解。CLAUDE.md 規則により直接実装せず、
本ドキュメントで DAG・型スケッチ・tier 配分まで詳細化してから実装枠（opus）を割り当てる。
**complete_pct 影響: 本ドキュメント自体は 0（設計のみ）**。実装マイルストーン到達時の
保守的予測は §5（M1 で A3 0.5→0.6 級、M3 で 0.7 級、独立監査が最終判定）。

---

## 0. 既存資産の監査と設計を規定する 3 つの発見

前提とした既存 API（全て read 済み・実/模型判定込み）:

| 資産 | 実体 | A3 での役割 |
|---|---|---|
| `IUT/Profinite.lean` `InverseSystem`/`limitGrp`/`limit_universal` | **実**（代数的逆極限・普遍性完全証明） | 逆極限エンジン（そのまま使える・型変更不要） |
| `IUT/ProfinitePi1.lean` `ProfinitePi1Tower`/`profPi1System`/`profPi1Limit`/`profPi1_is_profinite` | **実**（塔→逆系→逆極限＋副有限位相。ただし実例は自明塔のみ） | **塔の受け皿（§3 発見 1）** |
| `IUT/FieldAutGroup.lean` `FieldAut`/`fieldAutGroup`/`FieldExtension`/`galoisSubgroup`/`galoisGroupGrp` | **実**（体自己同型群・Gal(L/K)⊆Aut(L)） | 各段の Galois 群。**base/top は `IUTField`（全域 inv）を要求（発見 2）** |
| `IUT/QuadraticField.lean` `qdf_galoisGroup_order_two` | **実**（非自明 Gal の完成手本: 共役 σ の全数え上げ・`FieldAut.ext`+`left_inv` で invFun を確定するイディオム） | R3 の証明イディオムの写経元 |
| `IUT/Cq3Base.lean` `cq0PS`(Φ₃)/`cq0_no_rat_root`・`IUT/Cq3Irreducible.lean` `cqi_irreducible` | **実**（Φ₃ の既約性 `pibIrreducible`、IsPoly 約元修正済み） | 塔の初段 n=1 の既約性入力（完成済み） |
| **A1 一般 f エンジン**（並行建設・完成前提）: `IUT/GenExtField.lean` `gefField`、Wave 2+ `GenExtFieldNF` の `gefNFIUTField : IUTField`/`gefNF268 : Field268`/NF 担体/`gefNFMonBasis` | Wave 1 は**実**・Wave 2+ は**建設中** | 各段の体 ℚ[x]/(Φ_{p^n}) の実体化（★A1 依存、§1） |
| `IUT/EvaluationHom.lean` `evalSum`/`evalHom_add`/`evalHom_mul` | **実**（有界打ち切り明示の評価準同型） | 代入準同型 y↦y(x̄^a) の部品（R3） |
| `IUT/PolyFieldDivision.lean` `field_division_exists` 等・`IUT/RootAdjunction.lean` `rootAdj_is_root` | **実** | 因数定理・[Φ]=0 の手本（R1/R2） |
| `IUT/PadicValuationQ.lean` `pvqVal`/`pvq_val_mul`/`pvq_val_p`・`IUT/RatZeroDecide.lean` `rzd_zero_or_ne` | **実**（実 v_p: ℚ^×→ℤ・加法性・ℚ 零判定） | Eisenstein 既約性鎖（E 系列）の土台 |
| `IUT/CyclotomicPrimePower.lean` `cppPhi` | **実**（φ(p^k)=p^{k−1}(p−1) の ℕ 算術） | 次数簿記の再利用 |
| `IUT/LocalCFT.lean` `Zp`/`padicSystem` | **実**（ℤ_p = lim ℤ/p^n、ただし**加法**群） | M4 の比較対象（(ℤ/p^n)^× 逆系は**新規**が要る・§4） |

**発見 1（最重要・工数を大幅削減）**: `ProfinitePi1Tower`（M287F）が既に
「Nat 添字の `FieldExtension` 塔＋制限準同型 `restr` ＋逆系則」→ `profPi1Limit`
（逆極限＋副有限位相・開核・近傍基）を**完成済みの本物**として持つ。その正直申告 2 が
「制限準同型は witness データとして受け取る（構成は分離正規拡大機構待ち）」、
正直申告 4 が「非自明塔の実例なし（自明塔のみ）」。**A3 の novelty はこの witness を
本物の構成で discharge し、非自明な実例塔（円分塔）を差し込むことに尽きる**。
逆系・逆極限・位相は 1 行も書き直さなくてよい。

**発見 2（型制約）**: `FieldExtension.base/top : IUTField`・`FieldAut K (K : IUTField)`。
一方 A1 Wave 1 の `gefField : SimpleFieldExt`（`ring : CRing`・逆元は ∃ 形）は
`IUTField` でない。ゆえに **塔の各段を `galoisGroupGrp` に載せるには A1 Wave 2+ の
全域 inv 付き `gefNFIUTField : IUTField` が必須**。本設計はこれを「完成前提」とし、
依存箇所に ★A1 を付す（§6 リスク欄に要求インターフェイス一覧）。

**発見 3（塔の埋め込みは「係数の p 倍引き伸ばし」で書ける）**: 奇素数 p の冪では
円分多項式が **Φ_{p^{n+1}}(X) = Φ_{p^n}(X^p)** を満たす。係数列（`PS ratRing`）の
言葉では X ↦ X^p 代入＝**stretch 作用素**（係数を p 間隔に配る）であり、
埋め込み ι_n : ℚ(ζ_{p^n}) ↪ ℚ(ζ_{p^{n+1}}) は **NF 担体上の stretch そのもの**になる
（次数 < φ(p^n) の多項式の stretch は次数 < p·φ(p^n) = φ(p^{n+1}) — **簡約不要**で
well-defined）。抽象の「部分体を保つ σ の制限」を、具体的な係数演算に完全に落とせる。

---

## 1. 塔の各段 K_n = ℚ(ζ_{p^n}) = ℚ[x]/(Φ_{p^n})（T0・K 系列）

### 1.1 T0 `IUT/CyclotomicTowerPoly.lean` — stretch と Φ_{p^n} のデータ（★A1 非依存）

```lean
-- stretch 作用素（X ↦ X^p 代入の係数列版）
def ctpStretch (p : Nat) (f : PS ratRing) : PS ratRing :=
  fun j => if j % p = 0 then f (j / p) else ratRing.zero

-- 有界性: f が N で有界なら stretch は p*(N−1)+1 で有界
theorem ctpStretch_bounded (p : Nat) (hp : 1 ≤ p) {f : PS ratRing} {N : Nat}
    (hf : IsPolyBounded ratRing f N) :
    IsPolyBounded ratRing (ctpStretch p f) (p * (N - 1) + 1)
-- 一行: stretch j ≠ 0 ⟹ p ∣ j ∧ j/p < N ⟹ j ≤ p(N−1)。omega。

-- 加法との両立（成分ごと・自明）
theorem ctpStretch_add (p : Nat) (f g : PS ratRing) :
    ctpStretch p (psAdd ratRing f g)
      = psAdd ratRing (ctpStretch p f) (ctpStretch p g)

-- **乗法との両立（T0 の山場）**: 代入 X↦X^p は環準同型
theorem ctpStretch_mul (p : Nat) (hp : 1 ≤ p) (f g : PS ratRing)
    {N M : Nat} (hf : IsPolyBounded ratRing f N) (hg : IsPolyBounded ratRing g M) :
    ctpStretch p (psMul ratRing f g)
      = psMul ratRing (ctpStretch p f) (ctpStretch p g)
-- スケッチ: 右辺の第 j 係数 = Σ_{k≤j} (stretch f)_k (stretch g)_{j−k}。
-- p∤j なら各項で k, j−k の一方が p 非倍数で 0（j = k+(j−k) の mod p 算術）。
-- j = p·m なら非零項は k = p·i のみ、reindex して Σ_{i≤m} f_i g_{m−i} = (f·g)_m。
-- 「p 倍添字だけ残る rsum の間引き補題」を 1 本立てる（rsum_triangle／
-- evalHom_cauchy_mul と同族の確立イディオム・新インスタンス）。

-- Φ_p = 1 + X + … + X^{p−1}（幾何和）と Φ_{p^n} の再帰定義
def ctpGeom (p : Nat) : PS ratRing := fun j => if j < p then ratRing.one else ratRing.zero
def ctpPhi (p : Nat) : Nat → PS ratRing
  | 0     => ctpGeom p            -- 番兵（使わない）
  | 1     => ctpGeom p
  | n + 1 => ctpStretch p (ctpPhi p n)

-- 次数簿記（M386F cppPhi を再利用）: 有界性・先頭係数 1
theorem ctpPhi_bound (p n : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) :
    IsPolyBounded ratRing (ctpPhi p n) (cppPhi p n + 1)
theorem ctpPhi_lead (p n : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) :
    ctpPhi p n (cppPhi p n) = ratRing.one     -- ⟹ ≠ 0

-- **核の恒等式**（R2 の燃料）: X^{p^n} − 1 = Φ_{p^n} · (X^{p^{n−1}} − 1)
def ctpXPowSubOne (m : Nat) : PS ratRing   -- X^m − 1（psSingle − psC）
theorem ctp_pow_sub_one (p n : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n) :
    ctpXPowSubOne (p ^ n)
      = psMul ratRing (ctpPhi p n) (ctpXPowSubOne (p ^ (n - 1)))
-- スケッチ: n=1 は幾何和の telescoping（(X−1)·Σ X^i = X^p − 1、直接 Cauchy 計算）。
-- n+1 は n の式の両辺 stretch（ctpStretch_mul と stretch(X^m−1) = X^{pm}−1）。

-- p = 3 初段の接続（既存資産へ）: Φ_3 = cq0PS（係数ごと・rfl 級 3 本）
theorem ctp_phi3_eq : ctpPhi 3 1 = cq0PS
```

### 1.2 既約性入力 — Φ_{p^n} の `pibIrreducible`（E 系列、§2.5 に詳細）

`gefNFIUTField` は `hirr : pibIrreducible ratRing f`（IsPoly 約元修正済み・
`Cq3Irreducible` の正直申告に整合）を入力に取る。

- **n = 1（p = 3）**: `cqi_irreducible` で**完成済み**（`ctp_phi3_eq` で輸送）。
- **n ≥ 2**: 新規。一般解は **Gauss 付値版 Eisenstein 判定法**（E 系列・§2.5）。
  実装順序を塞がないため、K/S/R/T 系列は `hirr` を**名前付き honest 仮説
  パラメータ**として受け、E 系列完成時に discharge する（`SimpleExtData.bezout`
  が deferred → `gef_bezout` で充填された前例と同型の運用。§4 正直申告に明記し、
  discharge 前は「仮説付き」と報告する——満点主張はしない）。

### 1.3 K `IUT/CyclotomicTowerField.lean` — 各段の実体と Gal（★A1 依存）

```lean
-- 各段の体（A1 Wave 2+ エンジンの実例化）
def ctwField (p n : Nat) (hp : 2 ≤ p) (hn : 1 ≤ n)
    (hirr : pibIrreducible ratRing (ctpPhi p n)) : IUTField :=
  gefNFIUTField (ctpPhi p n) (cppPhi p n) (ctpPhi_bound …) (ctpPhi_lead' …)
    (cpp_phi_pos …) hirr                                   -- ★A1

-- 拡大 ℚ ⊂ K_n（FieldExtension。incl は NF 定数埋め込み＝次数 0 多項式）
def ctwExtQ (p n : Nat) … : FieldExtension where
  base := ratIUTField
  top  := ctwField p n …
  incl := gefNFConst …          -- ★A1（無ければ 5 行で新設: psC の NF 梱包）
  incl_add/incl_mul/incl_one    -- 定数×定数は次数 0 で簡約不要 ⟹ rfl 級

-- 各段の実 Galois 群（M271F をそのまま適用・新規証明ゼロ）
def ctwGal (p n : Nat) … : Grp := galoisGroupGrp (ctwExtQ p n …)
```

`qdf_galoisGroup_order_two` と同様、これで Gal(K_n/ℚ) は**本物の群**。
n=1, p=3 では位数 2（Φ₃ 版は既存 `qdfField` 系と同型な別実装になる——§6 正直申告）。

---

## 2. 制限準同型 res_n : Gal(K_{n+1}/ℚ) → Gal(K_n/ℚ)（S・R 系列 = A3 の novelty 核）

コードベースに存在しない新規部品。「σ を部分体 ι(K_n) に制限する」を、抽象の
部分体安定性でなく**円分の具体構造 σ(x̄) = x̄^a** に落として構成する。段階分解:

### 2.1 S `IUT/CyclotomicTowerEmbed.lean` — 塔の埋め込み ι_n（★A1・T0 依存）

```lean
-- NF 担体上の stretch（発見 3: 次数 < φ(p^n) ⟹ stretch 次数 < φ(p^{n+1})、簡約不要）
def ctwIota (p n : Nat) … : (ctwField p n …).carrier → (ctwField p (n+1) …).carrier

-- 環準同型性（山場は乗法）: NF 積 = 「掛けて Φ_{p^n} で簡約」なので、
--   stretch(reduce_{Φ_n}(a·b)) = reduce_{Φ_{n+1}}(stretch a · stretch b)
-- を余りの一意性で示す:
theorem ctw_rem_unique …   -- q₁Φ+r₁ = q₂Φ+r₂ ∧ deg rᵢ < deg Φ ⟹ r₁ = r₂
-- （(q₁−q₂)Φ = r₂−r₁ の次数比較。psMul_g_top_coeff268／
--   poly_mul_g_bounded_zero268 の確立イディオム）
theorem ctwIota_mul …      -- ctpStretch_mul + Φ_{n+1} = stretch Φ_n + ctw_rem_unique
theorem ctwIota_injective … -- 係数ごと（stretch は単射）: Subtype.ext + funext
theorem ctwIota_incl …     -- ι_n ∘ inclQ_n = inclQ_{n+1}（定数は j=0 で stretch 不変）
```

### 2.2 R1 `IUT/CyclotomicRootBound.lean` — 体上の根の個数 ≤ 次数（★A1(268)・汎用）

コードベース未整備の一般補題（`PolyFieldDivision` ヘッダが「後続」と予告済み）。
一般 `Field268` E 上で:

```lean
-- 因数定理: f(α) = 0 ⟹ f = (X−α)·g（field_division_exists で X−α による除算、
-- 余り＝定数＝f(α)（evalSum の除算恒等式への適用）＝0）
theorem crb_factor (E : Field268) …

-- 根の個数上界: deg f = d・f ≠ 0 のとき、相異なる根は d 個以下
theorem crb_root_bound (E : Field268) (f : PS E.ring) (d : Nat) …
    (r : Fin (d + 1) → E.ring.carrier)
    (hroot : ∀ i, evalSum (evalHomId E.ring) (r i) f (d + 1) = E.ring.zero)
    (hinj : ∀ i j, i ≠ j → r i ≠ r j) : False
-- スケッチ: d の帰納。crb_factor で (X−α_0) を剥がし、残る根は
-- 「体は零因子なし」（mul_inv_cancel から 3 行）で g の根に落ちる。
```

E := `gefNF268 (Φ_{p^{n+1}})` ★A1 に適用する。R1 自体は円分に依存しない**一般
体論の本物建設(b)**（分裂体・分離性など後続の柱 A 資産としても再利用可）。

### 2.3 R2 `IUT/CyclotomicMuCyclic.lean` — μ_{p^{n+1}}(K_{n+1}) = ⟨x̄⟩（T0・K・R1 依存）

x̄ := 変数 x の類（NF では単項式、`rootAdj_root` の NF 版）。

```lean
-- (R2-1) x̄^{p^{n+1}} = 1: ctp_pow_sub_one を商に落とす（[Φ_{n+1}] = 0、
--        rootAdj_is_root / rootAdj_modulus_class_zero のイディオム）
theorem ctw_x_pow_one …
-- (R2-2) x̄^{p^n} ≠ 1: X^{p^n} − 1 は次数 p^n < φ(p^{n+1}) = p^n(p−1)（p ≥ 3！）
--        なので既に NF・定数項 −1 ≠ 0 ⟹ 非零。**奇素数限定の理由**（§6）。
theorem ctw_x_pow_ne_one …
-- (R2-3) 冪 x̄^0, …, x̄^{p^{n+1}−1} は相異なる:
--        x̄^a = x̄^b (a<b) ⟹ x̄^{b−a} = 1 ⟹ 指数の Bezout で
--        x̄^{gcd(b−a, p^{n+1})} = 1、gcd = p^k (k ≤ n) ⟹ x̄^{p^n} = 1 と矛盾。
theorem ctw_x_powers_distinct …
-- (R2-4) 巡回性: y^{p^{n+1}} = 1 ⟹ y はある x̄^a。
--        p^{n+1} 個の相異冪 + y が全冪と異なると根が p^{n+1}+1 個 ⟹ R1 と矛盾。
-- (R2-5) **構成的抽出**（choice 回避の要）: NF 担体の Boolean 等値判定
--        ctwEqb（係数 φ(p^{n+1}) 本の rzd_zero_or_ne の有限連言 ★A1）で
--        a を下から走査する全域関数
def ctwFindPow … (y : carrier) : Nat      -- 走査; 見つからなければ 0（R2-4 が保証）
theorem ctwFindPow_spec … (hy : y^{p^{n+1}} = 1) : y = x̄ ^ (ctwFindPow y)
```

### 2.4 R3 `IUT/CyclotomicRestriction.lean` — res_n 本体（**novelty の頂点**・R2/S/K 依存）

```lean
-- (R3-1) Galois 指標: σ(x̄) も 1 の p^{n+1} 乗根（σ は環準同型: map_mul/map_one）
def ctwChar (σ : FieldAut (ctwField p (n+1) …)) : Nat := ctwFindPow (σ.toFun x̄)
theorem ctwChar_spec … : σ.toFun x̄ = x̄ ^ (ctwChar σ)
-- (R3-2) a = ctwChar σ は p と互いに素: σ⁻¹ 側の b で x̄^{ab} = x̄ ⟹
--        x̄^{ab−1} = 1 ⟹（R2-3 の順序論法）p^{n+1} ∣ ab−1 ⟹ p ∤ a
theorem ctwChar_coprime …
-- (R3-3) **決定補題**（本設計の主力・以後 4 回使う）: ℚ を固定する σ,τ が
--        σ(x̄) = τ(x̄) なら σ = τ。NF 元の展開 y = Σ c_j x̄^j
--        （gefNFMonBasis ★A1 または evalSum 恒等式 gefNF_repr を新設）から
--        σ(y) = Σ incl(c_j)·σ(x̄)^j。invFun 側は FieldAut.ext + left_inv
--        （qdf_galois_order_two 末尾のイディオムを写経）。
theorem ctw_aut_ext …
-- (R3-4) Φ_{p^n}(x̄_n^a) = 0（p ∤ a）: ctp_pow_sub_one を x̄_n^a で評価
--        （evalHom_mul）。左辺 0・第 2 因子 (x̄_n^a)^{p^{n−1}} − 1 ≠ 0
--        （R2-2/R2-3 の n 段版 + p∤a）・体の零因子なし ⟹ Φ 因子 = 0。
theorem ctw_phi_at_power_zero …
-- (R3-5) 代入準同型（gefNF の普遍性の実例）: y ↦ evalSum incl (x̄_n^a) y.val。
--        NF 担体は真の多項式なので写像は無条件 well-defined。乗法保存は
--        「簡約差 q·Φ の評価 = eval(q)·Φ(x̄^a) = 0」で R3-4 に帰着。
def ctwSub (a : Nat) … : (ctwField p n …).carrier → (ctwField p n …).carrier
-- (R3-6) **res_n の定義**: toFun := ctwSub (ctwChar σ)、
--        invFun := ctwSub (ctwChar σ⁻¹)。左右逆・ℚ 固定・FieldAut 全 field を
--        R3-3 で閉じる（合成は x̄_n ↦ x̄_n^{ab} = x̄_n、ab ≡ 1 mod p^{n+1} ⟹ mod p^n）。
def ctwRes … : (galoisGroupGrp (ctwExtQ p (n+1) …)).carrier
             → (galoisGroupGrp (ctwExtQ p n …)).carrier
-- (R3-7) 群準同型 + 「制限」の意味論
def ctwResHom … : Hom (ctwGal p (n+1) …) (ctwGal p n …)
   -- map_mul: 両辺とも x̄_n ↦ x̄_n^{a(σ)a(τ)}（R3-3 決定補題）
theorem ctw_res_compat … :   -- ι_n ∘ (ctwRes σ) = σ ∘ ι_n（「本当に制限である」）
```

`ctw_res_compat` が「σ∘incl が部分体を保ち、その制限が res(σ)」という課題文の
核の主張の Lean 形。stretch/evalSum の交換（σ(y(x̄^p)) = (res σ y)(x̄^p)）で示す。

### 2.5 E 系列 — Gauss 付値 Eisenstein 判定（★A1 非依存・R 系列と並列）

**Gauss の補題（内容の可約性）を経由しない**、実 v_p（`PadicValuationQ`）直上の
最小添字論法で `pibIrreducible` を出す（ℤ[x] への往復・content 理論が不要になり、
既存資産 `pvq_val_mul`・`rzd_zero_or_ne` に直結する）:

- **E1** `IUT/PadicUltrametricQ.lean`: 超距離 `pvq_val_add_ge_min`
  （v(x+y) ≥ min(v x, v y)、非零 3 元）＋等号条件（v x < v y ⟹ v(x+y) = v x）。
  代表の Int 算術（`pvq_val_wd` と同じ交差積簿記）。[opus]
- **E2** `IUT/GaussValuationQ.lean`: 多項式の Gauss 付値
  `egvMin f N : Int`（非零係数の v_p 最小値・rzd で走査・先頭係数非零が非空性 witness）と
  **最小添字乗法補題**: i₀, j₀ を g, h の「v が最小値を取る最小添字」とすると
  v((g·h)_{i₀+j₀}) = egvMin g + egvMin h（Cauchy 和で対角項が真に支配・E1 の等号条件）。[opus・詰まったら fable]
- **E3** `IUT/EisensteinCriterionQ.lean`: **Eisenstein ⟹ pibIrreducible**。
  f = d·c（IsPoly 両側）に対し次数加法（`psMul_g_top_coeff268`）で
  deg d + deg c = deg f。deg d = 0 ⟹ 単元（`pdv_deg_zero_unit`）、
  deg d = deg f ⟹ 余因子が単元 ⟹ associate。中間次数なら正規化後の
  最小添字 i₀ + j₀ = deg f を強制（中間係数 v ≥ 1）⟹ i₀ = deg d, j₀ = deg c
  ⟹ 定数項で v(f_0) = v(d_0) + v(c_0) ≥ 2、v(f_0) = 1 と矛盾。[fable 1 枠で詳細化→opus]
- **E4** `IUT/CyclotomicEisenstein.lean`: **Φ_{p^n}(X+1) が p-Eisenstein** ＋
  shift X↦X+1 の環自己同型（逆 shift X↦X−1）による既約性の輸送。
  freshman's dream ((X+1)^{p^k} ≡ X^{p^k} + 1 の係数 v_p ≥ 1、二項係数 C(p^k, j) の
  p 整除の ℕ 算術）を `ctp_pow_sub_one` の shift 版に適用。定数項 Φ_{p^n}(1) = p
  （v = 1、`pvq_val_p`）。[fable 詳細化→opus 実装・E 系列の最重量]

E 系列は x³−2 の `cti_irreducible` にも再適用可能な**一般判定器**（(b) 本物建設）。

---

## 3. 逆系と逆極限（T1 系列 — 受け皿は完成済み）

```lean
-- (T1-1) 多段制限: i ≤ j に対する反復合成（j−i の再帰）。
--        restr_self は定義から、restr_comp は「合成 = x̄ ↦ x̄^{a の積}」を
--        R3-3 決定補題で一点比較（fold 補題 1 本）。
def ctwRestr (p : Nat) … {i j : Nat} (h : i ≤ j) :
    Hom (ctwGal p (j+1) …) (ctwGal p (i+1) …)

-- (T1-2) **円分塔を ProfinitePi1Tower に差し込む**（p = 3 を第一実例に）
def ctwTower (p : Nat) … : ProfinitePi1Tower where
  K := ratIUTField
  ext := fun n => ctwExtQ p (n + 1) …     -- L_n = ℚ(ζ_{p^{n+1}})
  restr := ctwRestr p …
  restr_self := …  ;  restr_comp := …

-- (T1-3) 逆極限 = 実プロファイナイト Gal(ℚ(ζ_{p^∞})/ℚ)（全て既存機構が無償で供給）
def ctwProfinite (p : Nat) … : Grp := profPi1Limit (ctwTower p …)
-- profPi1_is_profinite (ctwTower …) : 開射影核＋近傍基（M287F-6e、証明済み定理の適用）
-- limit_universal          : 普遍性（M13-6、適用のみ）
```

これで M287F の正直申告 2（witness 制限）と 4（自明塔のみ）が円分塔について
discharge され、**「有限 Galois 群の逆極限」が非自明な本物の実例を持つ**。

### 3.1 M4（optional）: ℤ_p^× への接続 — 指標同型

- σ_a の**構成**（res と同じ機構の再利用）: p ∤ a に対し `ctwSub a` は R3-4/R3-3 で
  自己同型 ⟹ **Gal(K_n/ℚ) の元を φ(p^n) 個明示構成**。R3-1 と併せ
  `ctwGal p n ≅ (ℤ/p^n)^×`（単射 = 決定補題・全射 = σ_a）。
- (ℤ/p^n)^× の逆系は**新規**（`zmod`/`padicSystem` は加法群。単元群 `zmodUnits` と
  その `InverseSystem` を小規模新設）。レベル同型が `ctwRestr` と可換 ⟹
  逆極限の同型 `ctwProfinite p ≅ lim (ℤ/p^n)^× (= ℤ_p^×)` は `limit_universal` の
  錐比較で得る。ここまで到達すると「逆極限 ≅ ℤ_p^×」の課題文の姿が完全に閉じる。

---

## 4. 段階的マイルストーン（保守的予測・独立監査が最終判定）

| 里程 | 内容 | 依存 | A3 status 予測 |
|---|---|---|---|
| **M1** | **有限 2 段塔 ℚ ⊂ ℚ(ζ_3) ⊂ ℚ(ζ_9)**（p=3, n=1,2）: T0＋K(n≤2)＋S＋R1＋R2(n=1)＋R3(n=1) の実例化。res_1 : Gal(ℚ(ζ_9)/ℚ) → Gal(ℚ(ζ_3)/ℚ) が**初の本物の制限準同型** | ★A1 Wave 2+・Φ_9 既約性（E 系列 or 当面 honest 仮説） | Φ_9 discharge 済みなら **0.5→0.6**（監査示唆「非自明拡大の塔を制限準同型で連結」の最初の 1 コマ）。hΦ9 が仮説のままなら **0.55 止まり**と正直申告 |
| **M2** | 一般 n 段（p=3 固定）: R2/R3 の n 量化＋E 系列完成（Eisenstein で全 Φ_{3^n} discharge） | M1・E1–E4 | **0.6→0.65**（塔の全段が仮説なしで本物） |
| **M3** | **逆極限**: T1 で `ProfinitePi1Tower` に差し込み、`ctwProfinite 3` = 実プロファイナイト Gal(ℚ(ζ_{3^∞})/ℚ)（開核・近傍基・普遍性込み） | M2 | **0.65→0.7**（満点条件前半「有限 Galois 群の逆極限を本物のプロファイナイト群として構成」を円分部分で達成） |
| **M4** | 指標同型 Gal(K_n/ℚ) ≅ (ℤ/p^n)^×（σ_a 全射込み）と極限の ℤ_p^× 同定 | M3 | **0.7→0.75 級**（「≅ ℤ_p^×」の完全な形。これ以上は円分塔単独では動かない見込み・§6） |

M1 を near-term に切り出す根拠: R2/R3 の一般 n 証明はそのまま n=1 に特殊化でき、
数値が小さい（φ(9)=6・根走査 9 個・a 走査 9 個）ため決定補題・走査関数の
イディオムを最小コストで確立できる。逆に「まず n=1 だけの bespoke 証明」を書く
short-cut は Φ_9 の bespoke 既約性（2·4/3·3 次因子の排除）が Eisenstein より
高くつくため**採らない**（別コース 99% でなく本コース: 一般 n の忠実な部分ケース
として n=1 を実例化する）。

---

## 5. DAG と tier 配分

```
Wave 1（並列 3–4 枠・★A1 Wave 2+ の完成待ちと独立に走れる）
  T0  stretch＋Φ塔＋恒等式        [M: opus]
  E1  超距離 v_p                  [M: opus]
  E2  Gauss 付値・最小添字補題     [M: opus（詰まりは fable スポット）]
  R1  根の個数 ≤ 次数              [M: opus]（Field268 一般・E ではなく K268 が対象
                                    なので gefNF268 到着前は一般 E で書けて独立）

Wave 2（★A1 Wave 2+（gefNFIUTField 等）到着後）
  K   各段の体・拡大・Gal          [S–M: sonnet/opus（エンジン適用が主・新規証明少）] ★A1
  S   ι_n 埋め込み（stretch NF）   [M: opus。ctw_rem_unique は fable レビュー 1 点] ★A1・T0
  E3  Eisenstein ⟹ pibIrreducible [L→M: fable 詳細化 1 枠 → opus 実装]・E1 E2

Wave 3
  R2  μ 巡回性・x̄ の位数・走査     [M: opus（R2-5 の choice 回避構成は本設計で確定済み）]
                                   ・T0 K R1 ★A1(rzd/NF)
  E4  Φ_{p^n}(X+1) Eisenstein＋shift輸送 [L→M: fable 詳細化 → opus]・E3

Wave 4
  R3  ctwChar/決定補題/ctwSub/ctwRes/Hom [L: fable（novelty 核。本設計で段分解済みなので
      opus 先行→HELP スポットのみ fable でも可）]・R2 S K

Wave 5
  T1  ctwRestr 反復＋ProfinitePi1Tower 差し込み＋limit [S: sonnet（受け皿完成済み・束ね）]
  M4  σ_a・zmodUnits 逆系・指標同型 [M: opus]（optional・R3 後ならいつでも）
```

- 直列の背骨: T0 → S → R2 → R3 → T1。E 系列（E1→E2→E3→E4）は独立の並行鎖で、
  合流点は「K の hirr 引数の discharge」のみ。5 並列は Wave 1 で T0/E1/E2/R1 ＋
  A1 側 1 枠、以降も実装 opus 複数＋fable 詳細化 1＋sonnet 束ね 1 で埋まる。
- **★A1 Wave 2+ 完了待ちの段**: K・S・R2(R2-5 の rzd/NF 等値判定)・R3・T1・M4。
  待ち時間は T0/E 系列/R1 で埋める（すべて ★A1 非依存）。
- A1 側への**要求インターフェイス**（親が A1 実装と調整）:
  (i) NF 担体（次数 < nf の実多項式・Subtype）と `gefNFIUTField`/`gefNF268`、
  (ii) NF 乗法の特徴付け `gefNF_mul_spec`（mul a b ≡ psMul a.val b.val mod Φ、
  次数境界つき——S の ctw_rem_unique 接続点）、(iii) NF 定数埋め込みと
  単項式 `gefNFMon`（あれば R3-3 決定補題が gefNFMonBasis 経由で短縮）、
  (iv) 係数 rzd による等値判定が閉じる形（担体が関数型なら有限本の係数比較補題）。
  欠けるものは各モジュールが橋渡し補題として自前で足す（リスク: S/R3 に各 +1 段）。

---

## 6. 正直な限定（§4 規約により消さない・弱めない）

1. **円分部分に留まる**: 建つのは Gal(ℚ(ζ_{p^∞})/ℚ) ≅ ℤ_p^×（可換！）であり、
   **実絶対 Galois 群 G_ℚ（全代数拡大・非可換）ではない**。A3 満点条件の
   「実 G_K に接続」は部分達成（G_ℚ の可換商の、さらに 1 素数分の切片）。
   M4 完遂でも A3 = 1 にはしない（0.75 級が上限の見込み・独立監査が最終判定）。
2. **ℚ 上のみ・奇素数 1 個固定**（第一実例 p = 3）: 一般数体 K 上の円分塔・
   複数素数の合成（ẑ^× 方向）・p = 2（R2-2 の次数論法 p^n < φ(p^{n+1}) が
   崩れる）は対象外。
3. **既約性の discharge 前は仮説付き**: Φ_{p^n}（n ≥ 2）の `pibIrreducible` は
   E 系列完成まで名前付き honest 仮説。仮説が残る間のラウンド報告は
   「res_n は Φ 既約性を仮説とする条件付き構成」と明記する。
4. **制限の全射性は M4 まで無い**: M1–M3 の res_n は構成された群準同型＋
   `ctw_res_compat`（制限の意味論）までで、全射性（= σ_a 構成）は M4。
   従って M3 時点の逆極限は「Gal 塔の逆極限」ではあるが各射影の全射性は未証明。
5. **★A1 依存**: `FieldExtension`/`FieldAut` が `IUTField`（全域 inv）を要求する
   ため、A1 Wave 2+（`gefNFIUTField`）が遅延・変更されると K 以降が滑る。
   その場合の代替（CRing 版 Aut の新設）は共有型の重複を生むため採らず、待つ。
6. **位相は既存の代数的副有限位相**: `limitTopology`（M13/M265F/M287F）の
   「開射影核＝近傍基」流儀であり、一般位相空間論としてのコンパクト性等は
   既存資産の正直申告に従う（本設計で新たに弱めるものは無い）。
7. **ℚ(ζ_3) の実装重複**: 本塔の K_1 は `gefNF` 版であり、既存の `cq3Field`
   （ℚ×ℚ ガウス型）・`gfiCq3Field`（Quot 商環版）とは**同型な別コピー**
   （`qdf` の正直申告 (2) と同種）。同型輸送は本設計の対象外の後続。
8. 本ドキュメントは設計であり complete_pct を動かさない。各マイルストーンの
   数値は保守的予測であって、確定は独立監査（reaudit-A 系）が行う。
