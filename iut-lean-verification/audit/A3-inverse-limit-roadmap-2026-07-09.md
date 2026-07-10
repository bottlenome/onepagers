# A3 逆極限ロードマップ — 実 2 段円分塔（res₁ 完成）から一般 n 塔・逆極限・実 profinite G への詳細化ラウンド III

日付: 2026-07-10（ファイル名は起票ラウンド 2026-07-09 の継続）／ 種別: **設計ドキュメントのみ**
（実装コード無し・共有ファイル不更新）
分類: **[実／本物建設(b) の設計]** — `audit/A3-cyclotomic-tower-plan.md`（前々段・M2–M4 の大設計）と
`audit/A3-cyclotomic-tower-detail-2026-07-09.md`（前段・M1 の詳細化）の**次々段**。
台帳確認: `target_ledger.json` A3 = { weight 12, status **0.6** }（本日実測・
`reaudit-A3-res39-2026-07-09.md` で監査確定済み）。柱 A complete_pct = 38。
**complete_pct 影響: 本ドキュメント自体は 0（設計のみ）**。実装マイルストーンの
保守的予測は §5（最終判定は独立監査）。

前段からの**差分**（本ドキュメントの存在理由）: M1（2 段塔＋res₁）は**完成・監査確定**した。
残欠は監査が名指しした 4 つ——(i) 無限塔・逆極限 profinite G 未達、(ii) res 全射性未証明、
(iii) `ProfinitePi1Tower.restr` witness へ未接続（塔詰め未実施）、(iv) p=3・一般論未形式化。
本ドキュメントは (i)(ii)(iii) を、前々段設計 §4 の **M2（一般 n 段）・M3（逆極限）・M4（指標同型）**
に対応させて opus 実装枠に渡せる粒度へ分解する。進行中の `CyclotomicGal9`（CG9・
Gal(ℚ(ζ₉)/ℚ) 位数 6 決定）は**完成前提**とし、要求インターフェイスを §1.0 に明記する。

---

## 0. 既存資産の再監査（本日 read 済み・シグネチャ実在確認）

| 資産 | 実在シグネチャ（確認済み） | 本設計での役割 |
|---|---|---|
| 受け皿（塔） | `ProfinitePi1Tower`: `K : IUTField`・`ext : Nat → FieldExtension`・**`restr : ∀ {i j : Nat}, i ≤ j → Hom (galoisGroupGrp (ext j)) (galoisGroupGrp (ext i))`（witness）**・`restr_self`・`restr_comp`（`ProfinitePi1.lean`） | M3 の discharge 対象。**Nat 添字・全レベル要求**（有限段では詰められない・§4.0） |
| 受け皿（逆系） | `InverseSystem`: `Idx : Type`・`le`（前順序＋directed）・`G : Idx → Grp`・`t : le i j → Hom (G j) (G i)`・`t_self`/`t_comp`（`Profinite.lean:150`）。`limitGrp`・`limitProj`・`limit_universal` | **発見 A（§4.1）: Idx は任意型**——`Fin k` の有限逆系が正当に書ける |
| 受け皿（位相） | `limitTopology (S : InverseSystem)`・`projKernel_isOpen (S) (i : S.Idx)`・`projKernel_nbhd (S) (i₀ : S.Idx)`・`projKernelSubgroup`・`subgroup_isOpen_iff_contains_kernel`（`Topology.lean`/`ProfiniteTopology.lean`）——**全て S 一般** | 有限逆系にも Nat 塔にも無償適用 |
| 準同型 | `Hom G H`（`map`・`map_mul`）・`Hom.comp`・`Hom.map_one/map_inv/map_pow`・`profPi1IdHom`（`FundamentalGroup.lean`・`ProfinitePi1.lean`） | 反復制限 `ctwRestr` の部品 |
| res₁ 完成 | `cr39ResHom : Hom (galoisGroupGrp p9iExt9) (galoisGroupGrp cnfExt3)`・`cr39Res σ = if cr39Char σ % 3 = 1 then fieldAutId else cg3Conj`・`cr39Char σ = cm9Find (σ.toFun cm9Zeta)`・`cr39_char_spec`・`cr39_char_not_dvd3`・`cr39_compat`（`CyclotomicRes39.lean`） | **型が `restr` の 1 コマ（i=0, j=1）と正確に一致**。§4.2 で橋越しに再利用 |
| Gal(ζ₃) 完全決定 | `cg3Conj`・`cg3_aut_ext`（決定補題）・`cg3_decompose`・`cg3_galois_order_two`・`cg3Conj_ne_id`（`CyclotomicGal3.lean`） | 全射性 §1 の二分法 |
| ζ₉ 側 μ | `cm9Zeta`・`cm9Pow`・`cm9_factor`（x⁹−1 = Φ₉·(x³−1)）・`cm9_order`・`cm9_powers_distinct`・`cm9Find`/`cm9Find_spec`・`cm9_nf_unique`（`CyclotomicMu9(.Roots).lean`） | §1 の指標逆読み・§3 の一般 μ の写経元 |
| Eisenstein 判定器 | `eis_irreducible (f n p hp hb hn) (hlead : egvValQ p hp (f n) = 0) (hln) (hmid : ∀ i < n, f i ≠ 0 → 1 ≤ egvValQ …) (hconst : egvValQ … (f 0) = 1) (hc0) : pibIrreducible ratRing f`（`EisensteinCriterionQ.lean:227`） | **f 一般・完成済み**。E5（§2）はこの入力を一般 n で作るだけ |
| シフト機構 | `p9eShift f N`（f 一般）・`p9i_shift_bounded`/`p9i_shift_deg`（**f 一般**）・`p9i_shift_factor`/`p9i_irreducible` の輸送論法（Φ₉ 固定だが構造は f 一般・§2.3 で抽出）・`chs`（二項係数・`Fermat.lean:36`）（`Phi9Shift.lean`/`Phi9Irreducible.lean`） | E5 の輸送部 |
| 付値 | `egvValQ p hp : QRat → Int`・`egvValQ_mul`・`egvValQ_mk_ne`・`pum_val_add_ge_min`・`pvq_val_p`・`pvqNatVal_spec`（`GaussValuationQ.lean`/`PadicUltrametricQ.lean`/`PadicValuationQ.lean`） | E5 の 3-整性簿記（§2.2） |
| 体エンジン | `gefNFIUTField`/`gefNF268`/`gefFieldExtension`/`gefIncl`（**f 一般**・`GenExtTower.lean`）・`gefNFMon`/`gefNFPow`/`gefAlphaPowVal`/`gefBoundedRecon`（`GenExtBasisAlpha.lean`）・`pfdRed`/`pfdRed_char`/`pfdRed_of_bounded`（`PolyDivModFn.lean`）・`gnfCong`/`gnfCong_trans`（`GenExtFieldNF.lean`） | 一般段の体は既約性さえあれば 1 行（§2.4）。決定補題一般化の燃料（§3.3） |
| 評価 | `evalSum ι α f N`・`evalHom_add/mul/stable`・`psConstHom`（`EvaluationHom.lean`） | 一般代入自己同型 ctwSub（§3.4）と E5-3 |
| 根の上界 | `prc_roots_le_degree (K : Field268) …`（**K 一般**・`PolyRootCount.lean`） | 一般 μ の全射性（§3.2） |

**進行中（完成前提）**: `CyclotomicGal9.lean`（CG9）。本設計が仮定する**要求インターフェイス**は §1.0。

本ラウンドの設計を規定する **4 つの発見**:

- **発見 A（有限逆系は正当）**: `InverseSystem.Idx` は任意型なので、`Fin 2`/`Fin 3` 添字の
  **有限逆系**（各射 = 本物の res）が定義でき、`limitGrp`・`limitTopology`・`projKernel_isOpen`・
  `projKernel_nbhd` が**そのまま**適用される。これは scout §4 で却下した degenerate 定数塔
  （n ≥ 2 で同じ体を無限に並べる）とは別物——射が全部本物で「無限の水増し」が無い。
  ただし `ProfinitePi1Tower`（Nat 添字）の restr witness の discharge には**ならない**（§4.1 で正直に区別）。
- **発見 B（nf = 2 短絡の破れの正確な地点）**: CE39 の乗法性は「K₁ の積の Φ₃ 簡約余因子が
  **定数** q = psC(u₁v₁)（deg(uv) ≤ 2 = deg Φ₃）」に依存した。次段 ι₂ : K₂(nf=6) ↪ K₃(nf=18)
  では K₂ 内の積が deg ≤ 10・余因子 deg ≤ 4 の**非定数**になるため、この短絡は使えない。
  **ここが前々段設計 T0（stretch の環準同型性）が初めて必須になる地点**（§3.1）。
- **発見 C（Pascal の壁は回避できる）**: Φ_{3ⁿ}(x+1) の Eisenstein 入力は、二項係数表を
  一切使わず **freshman's dream の立方帰納**（(u+3B)³ 展開・係数 1,3,3,1 のみ）で一般 n
  一括に出せる（§2.2）。一般 n 版が n=3 の具体表版より**安い**。
- **発見 D（μ の因数分解は stretch で無償）**: `cm9_factor` の一般形
  x^{3^{n}}−1 = Φ_{3^{n}}·(x^{3^{n−1}}−1) は stretch 帰納（基底は x³−1 = Φ₃·(x−1) の
  4 係数 Cauchy 照合）で得られ、レベルごとの 10 係数照合の再演は不要（§3.0 の cts_pow_sub_one）。

---

## 1. 問い 1: res₁ の全射性（cr39_surjective）——2 段塔の Gal 構造完全把握の最後のピース

### 1.0 CG9 への要求インターフェイス（親が CG9 実装と整合させる・本設計の仮定）

cs39（下記）が CG9 から必要とするのは最小で次の 2 点（名前は仮・実名に合わせて読み替え）:

1. **σ₂ の実在**: `cg9Sigma2 : FieldAut p9iPhi9Field` と
   `cg9Sigma2_zeta : cg9Sigma2.toFun cm9Zeta = cm9Pow 2` と
   `cg9Sigma2_mem : (galoisSubgroup p9iExt9).mem cg9Sigma2`。
   （CG9 が σ_a を a ∈ {1,2,4,5,7,8} で全数え上げするならその a=2 実例で良い。
   **全射性には a ≡ 2 (mod 3) の 1 本があれば足りる**——位数 6 の完全決定は不要。）
2. （§3.3 の一般化写経元として）決定補題 `cg9_aut_ext`（ℚ 固定・σ(x̄₉) 一致 ⟹ σ = τ）。
   res₂（§3.5）はこれと CG9 の σ_a 全数え上げ（`cg9_galois_order_six` 級）を使う。

### 1.1 新規ファイル `IUT/CyclotomicSurj39.lean`（prefix `cs39`・依存: CR39・CG3・CG9）

```lean
-- (1) 指標の逆読み: σ(x̄₉) = x̄₉^a（a < 9）なら cr39Char σ = a。
--     cr39_char_spec: σ(x̄₉) = cm9Pow (cr39Char σ)。cm9Pow a = cm9Pow (cr39Char σ) と
--     cm9_powers_distinct（a, cr39Char σ < 9・cr39_char_lt）の対偶で一致。choice 不要。
theorem cs39_char_of_image (σ : FieldAut p9iPhi9Field) (a : Nat) (ha : a < 9)
    (hz : σ.toFun cm9Zeta = cm9Pow a) : cr39Char σ = a

-- (2) 単位元は単位元へ: Hom.map_one で無償（明示補題は展開の便宜のみ）
theorem cs39_res_one : cr39ResHom.map (galoisGroupGrp p9iExt9).one
    = (galoisGroupGrp cnfExt3).one := cr39ResHom.map_one

-- (3) σ₂ は共役へ: cr39Char cg9Sigma2 = 2（(1)）⟹ 2 % 3 = 2 ≠ 1 ⟹
--     cr39Res cg9Sigma2 = cg3Conj（if_neg・rfl 級）
theorem cs39_res_sigma2 :
    (cr39ResHom.map ⟨cg9Sigma2, cg9Sigma2_mem⟩).val = cg3Conj

-- (4) 非自明元の同定: cg3_galois_order_two の g は ⟨cg3Conj, cg3Conj_mem⟩ に等しい。
--     二分 ∀h を h := ⟨cg3Conj,…⟩ に適用し、h = one 枝を cg3Conj_ne_id で潰す
theorem cs39_conj_is_g …

-- (5) capstone: 全射性（本丸）
theorem cr39_surjective :
    ∀ τ : (galoisGroupGrp cnfExt3).carrier,
      ∃ σ : (galoisGroupGrp p9iExt9).carrier, cr39ResHom.map σ = τ
-- 証明: cg3_galois_order_two の二分で τ = one（→ σ := one・(2)）か
--       τ = g = ⟨cg3Conj,…⟩（→ σ := ⟨cg9Sigma2,…⟩・(3)(4)・Subtype.ext）
```

工数: 150–250 行。tier **S–M**（sonnet 可・(1) の distinct 対偶で詰まれば opus）。
仮説 0 本（CG9 完成が前提条件なだけで、honest 仮説パラメータは持たない）。

### 1.2 単段での A3 status 前進見積り（保守）

監査残欠 (ii) の解消であり「2 段塔の Gal 構造完全把握」（Gal(ζ₉) 位数 6 = CG9・
Gal(ζ₃) 位数 2・res₁ compat＋全射 ⟹ 短完全列 1 → ker → Gal₉ → Gal₃ → 1 の実質）を閉じる。
ただし監査 §5 は 0.65+ の条件を「逆極限・無限塔・塔詰め」と明言しており、
**cs39 単段では A3 0.6 → 0.6 据え置き〜0.62 級**（CG9 の position 込みで監査判定）。
柱 A% は +0.02×12 = +0.24 → 38.2 で**丸め据え置き 38 の可能性大**——これを正直に報告する。
それでも着手価値が高い理由: (a) 工数極小、(b) M4（σ_a・指標同型）の必須部品の先行、
(c) 残欠リストを 4 → 3 に減らし後続監査の 0.65 判定の下地になる。

---

## 2. 問い 2: 一般 n 塔の体 ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ})——既約性の一般証明（E5）

### 2.1 Pascal の壁の評価（結論: 壁は迂回できる・一般 n が n=3 具体表より安い）

**具体表 route（n = 3・ℚ(ζ₂₇)・次数 18）の見積り**: Φ₂₇ = x¹⁸ + x⁹ + 1 は 3 単項式なので
シフト像の係数は `p9e_shift_coeff` の rsum が 3 項に潰れ、係数_j = C(18,j) + C(9,j) + [j=0]。
必要なのは chs の行 9・行 18 の数値確定（行 9 = 行 6 × 行 3 の Cauchy 積・行 18 = 行 9² の
Vandermonde、`p9e_pow_coeff` の続き）と、中間係数 17 個の v₃ ≥ 1 の `pvqNatVal_spec` 数値検証
（例 j=1: 18+9 = 27 = 3³、j=9: 48620+1 = 48621 = 3²·5402.33… ではなく 3·16207——各自明分解）。
原理的障害なし・**物量 700–1000 行**。だが n = 4（次数 54）以降は非現実的で、
**∀n には決して届かない**——別コースである。

**一般 route（推奨・発見 C）**: Φ_{3ⁿ}(x) = Φ₃(x^{3^{n−1}}) = y² + y + 1（y := x^{3^{n−1}}）
なので、シフト像は y := (x+1)^{3^{n−1}} での y² + y + 1。freshman's dream
(x+1)^{3^m} = x^{3^m} + 1 + 3·B_m（B_m は 3-整・定数項 0）が立てば、z := x^{3^{n−1}} と置いて

    Φ_{3ⁿ}(x+1) = (z+1+3B)² + (z+1+3B) + 1 = z² + 3·(z + 1 + C),
    C := 2B(z+1) + 3B² + B（3-整・定数項 0）

⟹ 先頭 x^{2·3^{n−1}} の係数 1（v=0）・中間係数は全て 3×(3-整) で v ≥ 1・定数項 3(1+C₀) = 3
（v = ちょうど 1）。**二項係数表は一切不要**——freshman's dream 自体が立方帰納
(u + 3B)³ = u³ + 3(u²·B·3-整式…) で回り、必要な数係数は 1,3,3,1 のみ。

### 2.2 新規ファイル `IUT/EisensteinTowerInput.lean`（prefix `eit`・依存: GaussValuationQ・PadicUltrametricQ・Phi9Shift・CyclotomicStretch(§3.0)）

```lean
-- (E5-1) 3-整性述語と閉包（超距離・付値乗法性の直線合成）
def eit3Int (f : PS ratRing) : Prop :=
  ∀ j, f j ≠ ratRing.zero → 0 ≤ egvValQ 3 isPrime_three (f j)
theorem eit3Int_add …   -- pum_val_add_ge_min（の商版）+ rzd 零分岐
theorem eit3Int_mul …   -- Cauchy 和: 各項 v(ab) = v a + v b ≥ 0（egvValQ_mul）
                        -- + 和の v ≥ min の rsum 帰納（★E5 の実装上の泥はここ。
                        --   「rsum の v ≥ c 帰納」を 1 本の補助補題にする）
theorem eit3Int_natC …  -- 自然数定数（p9i_val_rofNat: v₃ = pvqNatVal ≥ 0）

-- (E5-2) freshman's dream（m 帰納・witness はデータで持つ = choice 回避）
structure EitFD (m : Nat) where
  B : PS ratRing
  int3 : eit3Int B
  const0 : B 0 = ratRing.zero
  bnd : IsPolyBounded ratRing B (3 ^ m)         -- 次数簿記（3^m 有界で足りる）
  eq : rpow (psRing ratRing) p9eXp1 (3 ^ m)
        = psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ m))
            (psOne ratRing)) (eitSmul3 B)        -- eitSmul3 = 係数 3 倍（psC 3 の psMul）
def eitFD : (m : Nat) → EitFD m
-- 基底 m=0: (x+1)¹ = x + 1 + 3·0（B := psZero・係数照合）
-- 段 m+1: rpow _ p9eXp1 (3^(m+1)) = (rpow _ p9eXp1 (3^m))³（rpow の指数積・3^(m+1) = 3^m·3）。
--   帰納の eq を代入し (u + 3B)³（u := X^{3^m} + 1）を psRing の環算術で展開:
--   u³ = X^{3^{m+1}} + 1 + 3(X^{2·3^m} + X^{3^m})（1,3,3,1 の (u₀+1)³ 形・u₀ := psSingle 3^m）、
--   残りは 3·(u²B·3 + uB²·9/3 + …) —— B_{m+1} := X^{2·3^m} + X^{3^m}
--     + 3u²B/3 の整理…（正確な閉形は実装時に named subterm で機械的に。閉包は E5-1）
-- ※ rpow の指数法則 rpow x (a*b) = rpow (rpow x a) b が無ければ eit で新設（Nat 帰納・10 行級）

-- (E5-3) シフト像の恒等式（3 単項式の evalSum 崩し）
theorem eit_shift_phi (n : Nat) (hn : 1 ≤ n) :
    ∀ j, p9eShift (ctsPhi n) (2 * 3 ^ (n-1) + 1) j
      = (psAdd _ (psAdd _ (psMul _ Y Y) Y) (psOne _)) j
        where Y := rpow (psRing ratRing) p9eXp1 (3 ^ (n-1))
-- ctsPhi n は 3 単項式（係数 1 が j ∈ {0, 3^{n-1}, 2·3^{n-1}} のみ・§3.0）なので
-- p9e_shift_coeff の rsum が 3 項に潰れる（p9e_rsum_collapse の一般化 1 本）

-- (E5-4) Eisenstein 入力の組み立てと (E5-5) 一般既約性
theorem eitPhi_shift_mid …    -- 中間係数 v ≥ 1（E5-2/E5-3 + eit3Int_mul + pvq_val_p）
theorem eitPhi_shift_const …  -- 定数項 = rofNat 3（v = 1・p9i_val_rofNat）
theorem eitPhi_shift_lead …   -- 先頭 = 1（p9i_shift_deg は f 一般・そのまま）
theorem eitPhi_irreducible (n : Nat) (hn : 1 ≤ n) :
    pibIrreducible ratRing (ctsPhi n)
-- eis_irreducible（実在・f 一般）+ est_transport（§2.3）の直線合成
```

工数: 600–900 行（E5-2 の環算術整理と E5-1 の rsum 帰納が主）。
tier **M（opus）・E5-2 で詰まった場合のみ fable スポット**。
n = 3 の先行実装の価値: **低**（一般版が同等以下の工数で ∀n を返し、n=3 は
`eitPhi_irreducible 3` の 1 行実例化で落ちる）。E5 が万一難航した場合の fallback
として §2.1 の具体表 route を記録するが、その着手は §2 規約により事前確認する。

### 2.3 新規ファイル `IUT/EisensteinShiftTransport.lean`（prefix `est`・依存: Phi9Irreducible）

`p9i_shift_factor`/`p9i_irreducible` の輸送論法（シフト像の既約性 ⟹ 元の既約性）は
Φ₉ 固定で書かれているが、使用部品（`p9i_shift_bounded`/`p9i_shift_deg`/`evalHom_mul`/
`evalHom_stable`/`plo_lead_oracle_Q`/`pdv_deg_zero_unit`/`pdv_mul_top_ne`/`pdbAssoc` 枝）は
**全て f 一般**。f を引数化した実質クローン:

```lean
theorem est_transport (f : PS ratRing) (n : Nat)
    (hb : IsPolyBounded ratRing f (n + 1)) (hl : f n ≠ ratRing.zero) (hn : 1 ≤ n)
    (hsh : pibIrreducible ratRing (p9eShift f (n + 1))) :
    pibIrreducible ratRing f
-- p9i_irreducible の証明体を f/n 引数で写経（p9eShifted への係数照合 p9e_shift_eq は
-- 不要になる——シフト像をそのまま主語にするため、Φ₉ 版より短くなる）
```

工数: 200–300 行。tier **S–M**（確立イディオムのクローン）。E5 と独立に先行可。

---

## 3. 問い 3: 一般段の埋め込み ι_n と res_n——stretch 一般補題の洗い出し

### 3.0 新規ファイル `IUT/CyclotomicStretch.lean`（prefix `cts`・依存: CyclotomicPolyData・Cq3Base・GenExtFieldNF・★A1 非依存）

前々段設計 T0 の p = 3 固定版。**ι₂ 以降・E5・一般 μ の三方が要る共通足場**
（承認済み足場 (c) でなく、一般 n 塔という名前付き実ターゲットへの本物建設 (b) の一部）:

```lean
-- (T0-1) stretch（X ↦ X³ 代入の係数列版）と有界性
def ctsStretch (f : PS ratRing) : PS ratRing :=
  fun j => if j % 3 = 0 then f (j / 3) else ratRing.zero
theorem ctsStretch_bounded {f N} (hf : IsPolyBounded ratRing f N) :
    IsPolyBounded ratRing (ctsStretch f) (3 * (N - 1) + 1)   -- omega 級

-- (T0-2) 加法・定数・単項式との両立（係数ごと・if 分岐）
theorem ctsStretch_add / ctsStretch_neg / ctsStretch_psC / ctsStretch_single …
theorem cts_xm1 (m : Nat) :   -- stretch(X^m − 1) = X^{3m} − 1（座標照合）
    ctsStretch (ctsXm1 m) = ctsXm1 (3 * m)

-- (T0-3) ★山場: stretch の乗法性（rsum 間引き補題 1 本に集約）
theorem cts_rsum_thin (h : Nat → QRat) (m : Nat)
    (hz : ∀ k, k % 3 ≠ 0 → h k = ratRing.zero) :
    rsum ratRing h (3 * m + 1) = rsum ratRing (fun i => h (3 * i)) (m + 1)
theorem ctsStretch_mul (f g : PS ratRing) :
    ctsStretch (psMul ratRing f g)
      = psMul ratRing (ctsStretch f) (ctsStretch g)
-- j % 3 ≠ 0: Cauchy 各項で k・j−k の一方が 3 非倍数 ⟹ 0（mod 3 算術・omega）。
-- j = 3m: 非零項は k = 3i のみ ⟹ cts_rsum_thin で Σ_{i≤m} f_i·g_{m−i} = (f·g)_m。
-- ※ IsPolyBounded 仮定は不要（係数ごとの主張・打切は Cauchy 和の定義内で閉じる）——
--   前々段設計の hf hg 付き主張より強く、使い回しが楽になる（実装時に要検証・
--   もし psMul の打切定義で詰まるなら有界仮定付きに落とす）

-- (T0-4) Φ 塔（基底を cq0PS そのものにして n=1 橋を rfl 化）
def ctsPhi : Nat → PS ratRing
  | 0 => cq0PS                    -- 番兵（使わない）
  | 1 => cq0PS                    -- Φ₃（既存 Cq3Base と定義一致 ⟹ 橋不要）
  | n + 2 => ctsStretch (ctsPhi (n + 1))
theorem ctsPhi_two_eq : ctsPhi 2 = cpdPhi9        -- funext・j % 3 場合分け（7 点照合）
theorem ctsPhi_bound (n) (hn : 1 ≤ n) :
    IsPolyBounded ratRing (ctsPhi n) (2 * 3 ^ (n - 1) + 1)
theorem ctsPhi_lead (n) (hn : 1 ≤ n) : ctsPhi n (2 * 3 ^ (n - 1)) = ratRing.one
theorem ctsPhi_three_coeffs (n) …   -- 係数 1 は j ∈ {0, 3^{n-1}, 2·3^{n-1}} のみ（E5-3 の燃料）
-- ※ 3^n の冪算術は omega 不可 ⟹ Nat.pow_succ/Nat.pow_le_pow_right 級の手動補題を同ファイルで

-- (T0-5) 核の恒等式（発見 D・stretch 帰納・基底は 4 係数 Cauchy 照合）
theorem cts_pow_sub_one (n : Nat) (hn : 1 ≤ n) :
    ctsXm1 (3 ^ n) = psMul ratRing (ctsPhi n) (ctsXm1 (3 ^ (n - 1)))
-- 基底 n=1: x³−1 = Φ₃·(x−1)。段: 両辺 ctsStretch（ctsStretch_mul + cts_xm1）

-- (T0-6) 合同輸送（ι_n の map_mul の燃料・発見 B の解決）
theorem cts_cong {n : Nat} {u v : PS ratRing}
    (h : gnfCong (ctsPhi n) u v) :
    gnfCong (ctsPhi (n + 1)) (ctsStretch u) (ctsStretch v)
-- witness q ↦ ctsStretch q（u − v = q·Φ_n ⟹ stretch 両辺・T0-2/T0-3）

-- (T0-7) 評価との交換（E5-3 で使うなら。同じ間引き補題）
theorem cts_eval_stretch (ι) (α) (f N) :
    evalSum ι α (ctsStretch f) (3 * N) = evalSum ι (rpow _ α 3) f N
-- ※ E5-3 を ctsPhi_three_coeffs の直接崩しで書くなら T0-7 は不要——実装時にどちらか片方
```

工数: 400–600 行。tier **M（opus）**。`cts_rsum_thin`/`ctsStretch_mul` で詰まった場合のみ
fable スポット（前々段設計が「T0 の山場」と事前登録済み）。

### 3.1 一般 ι_n `IUT/CyclotomicEmbedTower.lean`（prefix `cte`・依存: cts・eit(hirr)・GenExtTower）

**最初から n 引数で書く**（ce927 という n=2 bespoke を作ってから一般化する順序は採らない。
CM9→CM27 と違い数値表が無いので、一般化を妨げる具体計算が存在しない。CE39 は
「nf=2 短絡の実例」として残るが、cte は CE39 の写経でなく cts_cong 経由の新イディオム）:

```lean
-- 各段の体・拡大（E5 完成後は仮説 0 本の 1 行実例化）
def cteField (n : Nat) (hn : 1 ≤ n) : IUTField :=
  gefNFIUTField (ctsPhi n) (2 * 3 ^ (n-1)) (ctsPhi_bound …) (ctsPhi_lead' …) … (eitPhi_irreducible n hn)
def cteExt (n : Nat) (hn : 1 ≤ n) : FieldExtension := gefFieldExtension (ctsPhi n) …

-- 担体写像（deg < 2·3^{n-1} ⟹ stretch deg ≤ 3·(2·3^{n-1} − 1) < 2·3^n ⟹ 簡約不要）
def cteMap (n) (u : GefNF (ctsPhi n) (2·3^{n-1})) : GefNF (ctsPhi (n+1)) (2·3^n) :=
  ⟨ctsStretch u.val, ctsStretch_bounded … を 2·3^n へ緩めたもの⟩
-- 乗法性（発見 B の解決コマ）: u·v = pfdRed …。gefNF 乗法の gnfCong witness
-- （gnfCong (ctsPhi n) (u.val·v.val) ((u·v).val)）を cts_cong で持ち上げ、
-- ctsStretch_mul で左辺 = (stretch u)·(stretch v)、NF 一意性（pfdRed_char）で確定
theorem cteMap_mul / cteMap_add / cteMap_one / cte_incl_compat / cteMap_inj …
def cteIota (n) : RingHom (cteField n).toCRing (cteField (n+1)).toCRing …
-- 橋（§4.2 で使う）: cteField 1 の f = ctsPhi 1 = cq0PS は定義一致（rfl）、
-- cteField 2 は ctsPhi_two_eq（funext 等式）越しに p9iPhi9Field と同定（小補題 1 本・
-- 引数の Prop は proof-irrelevant なので f の subst のみ）
```

工数: 400–600 行。tier **M（opus）**。

### 3.2 一般 μ `IUT/CyclotomicMuTower.lean`（prefix `ctm`・依存: cts・cte・PolyRootCount）

CM9/CM9Roots の n 一般化（数値 9 を 3^n に置換・写経比率高）:

```lean
theorem ctm_zeta_pow (n) : ζ_n ^ (3^n) = 1        -- cts_pow_sub_one を商に落とす（cm9_x9_cong_one の写経）
theorem ctm_zeta_pow_sub_ne (n) : ζ_n ^ (3^{n-1}) ≠ 1   -- deg 3^{n-1} < 2·3^{n-1} で NF・定数項 −1
theorem ctm_order (n) …                            -- 位数 = 3 の冪 + 前項 ⟹ ちょうど 3^n（gcd/omega）
theorem ctm_powers_distinct (n) …                  -- cm9_powers_distinct の一般化（同じ順序論法）
theorem ctm_root_in_powers (n) …                   -- prc_roots_le_degree（K 一般・実在）で 3^n+1 根矛盾
def ctmFind (n) (y) : Nat / theorem ctmFind_spec … -- fuel 3^n の走査（cm9FindGo の fuel 引数化）
theorem ctm_nf_unique (n) …                        -- cm9_nf_unique の一般化（pfdRed_char 直結）
```

工数: 500–700 行。tier **M（opus）**（choice 回避構成は CM9 で確立済み・新イディオム無し）。

### 3.3 一般決定補題 `IUT/CyclotomicAutExt.lean`（prefix `cae`・依存: cte・GenExtBasisAlpha）

cg3_decompose（2 項）の n 項一般化。`gefBoundedRecon`（v = pmbLinComb v n・実在）と
`gefAlphaPowVal`（α^i = X^i・実在）で NF 元を y = Σ_{i<nf} incl(y_i)·x̄^i に分解し、
σ の map_add/map_mul 連鎖（rsum 上の帰納 1 本）で:

```lean
theorem cae_decompose (n) (y) : y = Σ_{i < 2·3^{n-1}} incl (y.val i) · x̄^i   -- 有限和は rsum/再帰で
theorem cae_endo_ext (n) (φ ψ : K_n の環自己準同型データ)   -- invFun 不要版（§3.4 の左右逆で使う）
    (hφQ hψQ : ℚ 固定) (h : φ x̄ = ψ x̄) : ∀ y, φ y = ψ y
theorem cae_aut_ext (n) (σ τ : FieldAut (cteField n)) (hσ hτ : mem) 
    (h : σ.toFun x̄ = τ.toFun x̄) : σ = τ    -- cg3_aut_ext の一般化（invFun は left_inv 経由）
```

工数: 300–450 行。tier **M（opus）**。

### 3.4 一般代入自己同型 = σ_a `IUT/CyclotomicSubAut.lean`（prefix `csa`・依存: ctm・cae・EvaluationHom）

**本ロードマップ最重要の 1 部品**。前々段設計 R3-4/R3-5/R3-6 の実装形。
res_n 一般・res 全射性一般・M4 指標同型の**三者が共有**する:

```lean
-- (R3-4) Φ_n(ζ_n^a) = 0（3∤a）: cts_pow_sub_one を ζ^a で評価（evalHom_mul）。
--   (ζ^a)^{3^n} = 1・(ζ^a)^{3^{n-1}} ≠ 1（ctm の位数論法 + 3∤a）・体の零因子なし
theorem csa_phi_at_pow_zero (n a) (ha : ¬ 3 ∣ a) : Φ_n(ζ_n^a) = 0
-- (R3-5) 代入写像（評価で定義・商をくぐらない・全域）
def csaSub (n a : Nat) (y : (cteField n).carrier) : (cteField n).carrier :=
  evalSum (cteInclHom n) (ctmPow n a) y.val (2 * 3 ^ (n-1))
--   cteInclHom : RingHom ratRing (cteField n).toCRing は gefIncl の RingHom 梱包（小部品・S 級）
theorem csaSub_add / csaSub_mul …
--   mul: u·v = pfdRed（gnfCong witness q）⟹ eval(uv) = eval(q)·Φ_n(ζ^a) + eval(NF) の
--   第 1 項が csa_phi_at_pow_zero で消える（evalHom_add/mul の直線合成）
theorem csaSub_zeta (n a) : csaSub n a ζ_n = ζ_n ^ a     -- 単項式の評価
-- (R3-6) 自己同型化: b := a の mod 3^n 逆元（gcd Bezout の Nat 算術・構成的に書ける——
--   拡張 Euclid の fuel 再帰 or a^{φ(3^n)−1} mod 3^n の冪走査。choice 不使用）
def csaAut (n a : Nat) (ha : ¬ 3 ∣ a) : FieldAut (cteField n) :=
  { toFun := csaSub n a, invFun := csaSub n b,
    left_inv/right_inv := cae_endo_ext で ζ 一点比較（ζ^{ab} = ζ・ab ≡ 1 mod 3^n）, … }
theorem csaAut_mem (n a ha) : (galoisSubgroup (cteExt n)).mem (csaAut n a ha)
```

工数: 500–800 行。tier **M–L**: opus 先行・`csaSub_mul` か左右逆の簿記で詰まった
スポットのみ fable（本ドキュメントで段分解済みのため fable 前置は不要と判断）。

### 3.5 一般 res_n `IUT/CyclotomicResTower.lean`（prefix `ctr`・依存: csa・ctm・cae）

CR39 の一般化。CR39 は「下段 Gal が完全決定済み」という n=1 特有の短絡
（res(σ) := id or cg3Conj の 2 分岐）を使ったが、一般 n では csaAut がその役を担う:

```lean
def ctrChar (n) (σ : FieldAut (cteField (n+1))) : Nat := ctmFind (n+1) (σ.toFun ζ_{n+1})
theorem ctrChar_not_dvd3 …                        -- cr39_char_not_dvd3 の写経（σ 単射・位数論法）
def ctrRes (n) (σ) : FieldAut (cteField n) := csaAut n (ctrChar n σ % 3 ^ n) …
--   3∤(a % 3^n) は 3∤a と 3 ∣ 3^n から omega 級（n ≥ 1）
theorem ctr_compat (n) (σ) (hσ) : ∀ x, cteMap n ((ctrRes n σ).toFun x) = σ.toFun (cteMap n x)
--   生成元: σ(ι x̄_n) = σ(ζ_{n+1}³) = ζ_{n+1}^{3a}、ι((ctrRes σ) x̄_n) = ι(ζ_n^{a mod 3^n})
--   = ζ_{n+1}^{3·(a mod 3^n)}、3a ≡ 3(a mod 3^n) (mod 3^{n+1}) の周期補題（cm9_pow_period の一般化）
--   全点: cae_decompose + 環準同型性 + ℚ 固定（cr39_compat の写経）
def ctrResHom (n) : Hom (galoisGroupGrp (cteExt (n+1))) (galoisGroupGrp (cteExt n))
--   map_mul: cae_aut_ext + cteMap_inj + compat 3 連鎖（cr39_res_comp の写経）
theorem ctr_surjective (n) : ∀ τ, ∃ σ, (ctrResHom n).map σ = τ
--   ★一般 n では全射性が M4 を待たず出る: τ の指標 a := ctmFind n (τ x̄_n)（cae_aut_ext で
--   τ = csaAut n a）に対し σ := csaAut (n+1) a'（a' := a か a + 3^n の 3∤ 調整）が原像。
--   これは §1 の cs39 の一般化であり、cs39 はこの忠実な n=1 実例（写経元）になる
```

工数: 500–700 行。tier **M（opus）**（CR39 という完成した写経元があるため）。

---

## 4. 問い 4: 逆系と逆極限——有限段先行と無限塔の分離

### 4.0 分離の原則（何が有限段で得られ、何に ∀n が要るか）

`ProfinitePi1Tower` は **`ext : Nat → FieldExtension` の全レベル**を要求する。よって
witness `restr` の discharge（監査残欠 (iii)）には**無限塔が必須**であり、有限段で
詰める唯一の方法は「n ≥ N で定数」の degenerate 延長——これは scout §4・前段 §2.2 で
**却下済み・本ラウンドも継続却下**する。∀n に要るのは正確に
(1) Φ_{3ⁿ} 既約の一般証明（§2 E5）、(2) 一般 ι_n・μ・res_n（§3）の 2 系列で、他は既存機構。

一方**発見 A** により、有限段の**逆系**（塔でなく）は正当に本物化できる:

### 4.1 有限 3 段逆系 `IUT/CyclotomicSystem3.lean`（prefix `csy`・依存: CR39・ctr(n=2 実例) or cr927 相当）

```lean
-- Idx = Fin 3（0 ↦ ℚ(ζ₃)・1 ↦ ℚ(ζ₉)・2 ↦ ℚ(ζ₂₇)）・le は val ≤ val・directed は max
def csyG : Fin 3 → Grp
  | ⟨0,_⟩ => galoisGroupGrp cnfExt3 | ⟨1,_⟩ => galoisGroupGrp p9iExt9
  | ⟨2,_⟩ => galoisGroupGrp (cteExt 3)     -- 橋補題で ζ₂₇ 段（§3.1）
def csySystem : InverseSystem where
  Idx := Fin 3; le := fun i j => i.val ≤ j.val; …
  t := fun {i j} h => match i, j with     -- 6 通りの明示 match（i.val > j.val は omega で排除）
    | ⟨0,_⟩,⟨0,_⟩ => profPi1IdHom _ | ⟨0,_⟩,⟨1,_⟩ => cr39ResHom
    | ⟨0,_⟩,⟨2,_⟩ => Hom.comp cr39ResHom (ctrResHom 2 の橋渡し版)   -- 合成を定義に採る
    | ⟨1,_⟩,⟨1,_⟩ => profPi1IdHom _ | ⟨1,_⟩,⟨2,_⟩ => res₂ | ⟨2,_⟩,⟨2,_⟩ => profPi1IdHom _ | …
  t_self := Fin 場合分けで rfl 級
  t_comp := 10 通りの場合分け（id 吸収は rfl・0≤1≤2 の連鎖は t(0≤2) を合成で定義したので rfl）
def csyLimit : Grp := limitGrp csySystem
theorem csy_kernel_open (i : Fin 3) :
    (limitTopology csySystem).IsOpen (projKernelSubgroup csySystem i).mem :=
  projKernel_isOpen csySystem i                    -- S 一般定理の無償適用
theorem csy_nbhd_base … := projKernel_nbhd csySystem …
```

**正直な位置づけ（過大主張しない）**: これは `InverseSystem.t` に本物の非自明遷移射が
初めて入る実例（従来の実例は自明塔と可換 ẑ）だが、極限は有限群（≅ Gal(ζ₂₇)）であり
「profinite G_K」ではなく、`ProfinitePi1Tower.restr`（残欠 (iii)）の discharge にも
**ならない**。complete_pct 単体寄与は小さく、**§2 規約の自問では「枠埋め束ね」に近い**
——着手は ζ₂₇ 段＋res₂ 完成ラウンドの sonnet 余枠に限り、事前にユーザー確認する。
無限塔（4.2）が近いなら省略してよい（4.2 が csy を包含する）。

### 4.2 本丸 M3: Nat 塔の discharge `IUT/CyclotomicTowerLimit.lean`（prefix `ctl`・依存: cte/ctm/csa/ctr 全部＋ProfinitePi1）

`cr39ResHom` を `ProfinitePi1Tower.restr` witness に嵌める具体手順:

1. **塔の宣言**: `ctlExt (n : Nat) : FieldExtension := cteExt (n + 1)`（L_n = ℚ(ζ_{3^{n+1}})。
   全 n で本物・E5 が既約性を供給）。橋補題 `cteExt 1 = cnfExt3`（ctsPhi 1 = cq0PS は
   定義一致 rfl・他引数は Prop）と `cteExt 2 = p9iExt9`（`ctsPhi_two_eq` の f-subst 1 本）で、
   CR39/CG3/CG9/cs39 の成果が第 0–1 層の定理としてそのまま輸送される（各 1 小補題）。
   一般 `ctrResHom n` があるため **cr39ResHom 自体の再利用は「n=1 実例との一致確認」**
   （`ctl_res0_eq_cr39 : 橋越しに ctrResHom 1 = cr39ResHom`・検算定理）に格下げされる——
   これが最も安全な嵌め方（cast を跨いだ定義の共有をしない）。
2. **反復制限（cast 簿記の本体）**: 単段 `S n := ctrResHom (n+1) : Hom (G (n+1)) (G n)` から
   ```lean
   -- 差分 d の再帰は cast-free（i + 0 = i・i + (d+1) = (i+d) + 1 が definitional）
   def ctlRestrAux (i : Nat) : (d : Nat) → Hom (ctlGal (i + d)) (ctlGal i)
     | 0     => profPi1IdHom _
     | d + 1 => Hom.comp (ctlRestrAux i d) (S (i + d))
   theorem ctlRestrAux_comp (i d₁ d₂) :   -- aux レベルの推移律（d₂ 帰納・cast-free）
       ∀ x, (ctlRestrAux i d₁).map ((ctlRestrAux (i + d₁) d₂).map x)
         = (ctlRestrAux i (d₁ + d₂)).map x
   -- i ≤ j への橋: j = i + (j − i)（Nat.add_sub_cancel' 級）の subst 1 回のみ
   def ctlRestr {i j : Nat} (h : i ≤ j) : Hom (ctlGal j) (ctlGal i) := …
   ```
   `restr_self` は d = 0 帰着（i − i = 0 の rewrite 後 rfl）、`restr_comp` は
   `ctlRestrAux_comp` の subst 輸送。**cast 簿記が本モジュール最大の泥**——
   subst を「j 側 1 箇所」に固定する上記の形で最小化する。詰まったら fable スポット。
3. **塔詰めと極限（束ね・新規証明ゼロ）**:
   ```lean
   def ctlTower : ProfinitePi1Tower :=
     { K := ratIUTField, ext := ctlExt, restr := ctlRestr,
       restr_self := …, restr_comp := … }               -- ★witness の初 discharge
   def ctlProfinite : Grp := profPi1Limit ctlTower       -- 実 profinite Gal(ℚ(ζ_{3^∞})/ℚ)
   theorem ctl_is_profinite := profPi1_is_profinite ctlTower   -- 開核＋近傍基（適用のみ）
   -- 射影の全射性は M4 の一般 σ_a 整合族で別途（正直な限定・§6）
   ```

工数: 2. が 300–500 行・1.・3. が 150–250 行。tier: 2. **M（opus・fable スポット予約）**、
1.+3. **S（sonnet）**。

### 4.3 M4（後続・optional だが §3.4 完成後は安い）: 指標同型と ℤ₃^×

- `csaAut` が σ_a そのものなので、レベル同型 Gal(K_n/ℚ) ≅ (ℤ/3ⁿ)^× は
  単射（cae_aut_ext）＋全射（csaAut）＋指標乗法性（ctrChar の積公式）で閉じる。
- (ℤ/3ⁿ)^× の逆系 `zmodUnits` は新設（`zmodSystem` は加法群）。極限同型
  `ctlProfinite ≅ lim (ℤ/3ⁿ)^×` は `limit_universal` の錐比較。
- 併せて**射影の全射性**（整合族の持ち上げ・有限レベルの全射 ctr_surjective の帰納極限）
  まで到達すると A3 の円分部分は打ち止め（0.75 級・前々段設計 §6-1 の上限）。

---

## 5. 問い 5: 最小 complete_pct 前進ステップ——候補の自問と優先順位

台帳: A3 = weight 12・status **0.6**（本日実測）。柱 A complete_pct 38。
各候補に「この一手は実 IUT 完全証明率を上げるか？」:

| 候補 | 実 IUT を進めるか | status 見積り（保守・監査確定） | 工数・tier | 判定 |
|---|---|---|---|---|
| **(a) cs39: res₁ 全射性**（§1） | **Yes**——残欠 (ii) の解消・2 段塔 Gal 構造の完全把握（実質の短完全列）・M4 部品の先行 | 0.6→**0.6 据え置き〜0.62**（柱 A% は 38.2 で丸め据え置きの可能性大と正直申告） | 極小 150–250 行 [**S–M**]・CG9 完成待ちのみ | **即時着手（CG9 完了次第）** |
| **(b) cts+est+E5: stretch 一般＋Φ_{3ⁿ} 一般既約**（§2・§3.0） | **Yes**——∀n の体を解禁する唯一の欠落を、一般判定器（他の既約性にも再利用）で閉じる本物建設 (b)。発見 C により n=3 具体表より安い | 単体では体のみで小幅（0.62 級）。**価値は (c)(d) の解禁** | cts 400–600 [**M**]＋est 200–300 [**S–M**]＋E5 600–900 [**M**・fable スポット] | **(a) と並行で即時着手** |
| **(c) 一般段機構: cte/ctm/cae/csa/ctr**（§3.1–3.5） | **Yes（M2）**——一般 ι_n・μ・σ_a・res_n。res 全射性の一般形も同梱 | M2 相当: 0.6→**0.65**（全段が仮説なしで本物・前々段設計 §4 と整合） | 5 ファイル計 2200–3300 行 [**M** 中心・csa のみ M–L] | 第 2 波（(b) 完成後・csa→ctr は直列、cte/ctm/cae は並列可） |
| **(d) ctl: Nat 塔詰め＋逆極限**（§4.2） | **Yes（M3 本丸）**——残欠 (i)(iii) の discharge。「有限 Galois 群の逆極限を本物の profinite 群として構成」を円分部分で達成 | 0.65→**0.7**（前々段設計 M3 と整合） | 450–750 行 [M＋S・cast 簿記に fable スポット] | 第 3 波（(c) 完了後） |
| (e) csy: 有限 Fin-3 逆系（§4.1） | 弱い Yes（実遷移射の InverseSystem 初通電）だが小・(d) が包含 | 据え置き見込み | 150–250 行 [S] | **枠埋め限定・着手前にユーザー確認**（§2 規約）。(d) が近いなら省略 |
| (f) ζ₂₇ の bespoke 実装（一般 n を経ない具体表・具体 res₂） | No に近い（∀n に届かない別コース・発見 C で一般の方が安い） | — | — | **却下**（一般 (b)(c) の n=2,3 実例化で代替） |
| (g) degenerate 定数塔での塔詰め | **No**（§3 規約の水増し） | — | — | **却下継続**（scout §4・前段・本設計 §4.0 で三度目） |

**結論——最小 complete_pct 前進ステップ（優先順位つき）**:

1. **cs39（res₁ 全射性）** [S–M・CG9 待ち]: 単段の status 寄与は小さいが工数極小・
   残欠 1 本消し・M4 部品。**単段で A3 を動かす量は 0〜+0.02 と保守申告**。
2. **cts（stretch 一般補題）** [M]: ι₂ 以降・E5・一般 μ の三方が要る共通足場。
   名前付き実ターゲット（cte/eit/ctm）への (b) 本物建設。
3. **est＋E5（一般 Eisenstein）** [S–M＋M・fable スポット]: ∀n の既約性。
   ここまでで「無限塔の材料」が揃う。
4. **cte→{ctm, cae}→csa→ctr（一般段機構 M2）** [M×4＋M–L×1]: 完了時 **A3 0.6→0.65** を
   申告し独立監査へ。
5. **ctl（塔詰め＋逆極限 M3）** [M＋S]: 完了時 **A3 0.65→0.7** を申告し独立監査へ。
   ここで監査残欠 (i)(iii) が discharge される。
6. （後続）M4 指標同型・射影全射性: 0.7→0.75 級。

5 並列の編成案（tier 混合・CLAUDE.md 配分規則準拠）:
- **ラウンド 1**: cs39 [sonnet→詰まれば opus]＋cts [opus]＋est [sonnet]＋E5-1/E5-2 [opus]＋
  E5-3〜5 [opus]（E5 内は E5-1/2 と E5-3 が独立・E5-4/5 は合流）。fable は起動せず
  スポット待機（cts_rsum_thin・E5-2 の環算術のみ）。
- **ラウンド 2**: cte [opus]＋ctm [opus]＋cae [opus]＋csa [opus・fable スポット]＋
  検算/監査準備 or cs39 回収 [sonnet]。
- **ラウンド 3**: ctr [opus]＋ctl-2（反復制限）[opus・fable スポット]＋ctl-1/3 束ね [sonnet]
  ＋監査 [独立枠]＋余枠は csy（事前確認の上）か他柱。

---

## 6. 実装規約（全新規ファイル共通・前段 §5 を継承・opus への指示に含める）

- **ヘッダ二軸**: 分類 [実]・complete_pct 影響を 1 行明記（本設計を引用）。
  ctr・ctl のみ「A3 complete_pct 前進候補（監査確定待ち）」、cts/est/eit/cte/ctm/cae/csa は
  「M2/M3 の必要部品（単体では未設定・ctr/ctl 到達時に親が更新）」。
- **禁止タクティク**: simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp 不使用。新規 Classical.choice 禁止（`#print axioms` =
  propext, Quot.sound 維持。E5-2 の witness は **構造体データ**で持つ——∃ から取り出さない。
  csa の mod 逆元も fuel 走査で構成的に）。
- **新規ファイルのみ**・共有ファイル（IUT.lean/build.sh/dashboard/graph 系/target_ledger）
  不更新（親が統合時に一括・`tools/gen_graph.py` 再生成も親）。
- **3^n 算術**: omega は冪を扱えない。`Nat.pow_succ`・`Nat.pos_pow`・単調性の小補題を
  cts に集約し全ファイルで輸入する（各所で再証明しない）。
- 正直な限定を各ヘッダに**追記のみ**: (i) p = 3・ℚ 上固定、(ii) 建つのは可換な
  Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^× の円分切片であり**実絶対 Galois 群 G_ℚ ではない**
  （前々段設計 §6-1 の継承・M4 完遂でも A3 = 1 にしない）、(iii) M3 時点で射影の
  全射性は未証明（M4）、(iv) csy（作る場合）は有限逆系であり profinite G_K でも
  ProfinitePi1Tower の discharge でもない、(v) 分離性・正規性の一般論は未形式化のまま
  （res は円分の指標構造で直接構成——一般論の代替ではない）。

## 7. 正直な限定（本設計自身のもの・§4 規約により消さない）

1. 本ドキュメントは設計であり complete_pct を動かさない。status 数値は全て保守的
   見積りで、確定は独立監査（reaudit-A 系・AUDIT_RUBRIC 準拠）。
2. CG9 は**完成前提**であり、§1.0 のインターフェイスが実名と食い違えば cs39 は
   親が調整する（食い違いは cs39 の 1 ファイルに閉じる設計にしてある）。
3. E5-2（freshman's dream の立方帰納）の環算術整理と、ctl-2（反復制限の cast 簿記）を
   本設計の 2 大リスクと評価する（fable スポット枠を各 1 予約）。E5 が万一予算超過なら、
   §2.1 の n=3 具体表 route を fallback とするが、その場合 ∀n は閉じず M2 は
   「n ≤ 3 の忠実な部分ケース」と正直申告して 0.65 は主張しない。
4. ctsStretch_mul の「有界仮定なし」主張（§3.0 の注記）は psMul の打切定義次第で
   有界仮定付きに弱める可能性がある（どちらでも cte/E5 の用途には足りる）。
5. 一般 ctr の全射性（§3.5）は csaAut に依存するため、cs39（n=1 の全射性）とは
   証明経路が異なる。cs39 は「CG9 の完全決定を使う n=1 短絡」であり、一般化の
   写経元としては ctr_surjective の方が本線——cs39 を書いた後も ctr_surjective は
   独立に必要（重複でなく、n=1 検算 `ctl_res0` 系で整合を確認する）。
