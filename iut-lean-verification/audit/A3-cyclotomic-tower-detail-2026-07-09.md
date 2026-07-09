# A3 円分塔 詳細化ラウンド II — 最小 complete_pct 前進ステップの特定と opus 実装スケッチ

日付: 2026-07-09 ／ 種別: **設計ドキュメントのみ**（実装コード無し・共有ファイル不更新）
分類: **[実／本物建設(b) の設計]** — `audit/A3-cyclotomic-tower-plan.md`（前段設計）と
`audit/A3-machinery-scout-2026-07-09.md`（棚卸し）の**次段の詳細化**。
台帳確認: `target_ledger.json` A3 = { weight 12, status 0.5 }（実測・本日確認）。
**complete_pct 影響: 本ドキュメント自体は 0（設計のみ）**。実装マイルストーンの
保守的予測は §4（最終判定は独立監査）。

前段設計からの**差分**（本ドキュメントの存在理由）:
前段設計は一般 p・一般 n の壮大な DAG（T0/K/S/R/E/T1）を描いたが、その後
**A1 側の状況が変わった**——F6（`GenExtFieldInv`）が完成し `gefNFIUTField : IUTField`
（全域 inv・choice-free）が**実在**する。また R1（`PolyRootCount.lean`
`prc_roots_le_degree`）と Φ 系データ（`CyclotomicPolyData.lean` `cpdPhiP`/`cpd_factor`/
`cpdPhi9`）も完成済み。本ドキュメントはこの新しい足場の上で、**「一般 n の機械を
待たずに、いま本物に実装できる最小の前進」**を nf = 2, 6（p = 3, n = 1, 2）の
**忠実な部分ケース**として切り出し、opus 実装枠に渡せる粒度まで分解する。
（§3 規約: 「本コースを 3% 進む > 別コースを 99%」。以下の全モジュールは
一般 n 版（前段設計 T0/R/S 系列）の**特殊化として再利用可能な形**で設計する——
別コースではなく本コースの最初の 2 段である。）

---

## 0. 既存資産の再監査（本日 read 済み・全て実在確認）

| 資産 | 実在シグネチャ（確認済み） | 本設計での役割 |
|---|---|---|
| **F6 完成** | `gefNFIUTField (f : PS ratRing) (nf : Nat) (hb : IsPolyBounded ratRing f (nf+1)) (hl : f nf ≠ ratRing.zero) (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) : IUTField`・`gefNF268 … : Field268`（`IUT/GenExtFieldInv.lean`） | **円分体を IUTField として作る唯一のエンジン**。前段設計の ★A1 依存が解消した |
| F5 | `GefNF f nf := {g // IsPolyBounded ratRing g nf}`・`gefNFRing`（乗法 = `pfdRed f nf nf (a·b)`）・合同代数 `gnfCong`/`gnfCong_*`（`GenExtFieldNF.lean`） | NF 担体・乗法の合同計算エンジン |
| F3 | `pfdRed g m N w`・`pfdRed_bound`・**`pfdRed_char`**（剰余の一意特徴付け）・**`pfdRed_of_bounded`**（deg < m なら簡約不要）（`PolyDivModFn.lean`） | 環準同型性証明の主力（「簡約差 = h·Φ」を潰す） |
| F9 | `gefNFMon f nf i (hi : i < nf) : GefNF f nf`（単項式 X^i）・`gefNFPow`・`gefBoundedRecon`（v = pmbLinComb v n）・`gefSmulCoeff`・`gefSMS`（`GenExtBasisAlpha.lean`）。**F9-7（`gefFieldExtension` ℚ↪gefNFIUTField）は「F6 待ち」のまま未実装** | 生成元 α = X̄・冪基底・展開。F9-7 の discharge が本設計 CNF-2 |
| R1 完成 | `prc_roots_le_degree (K : Field268) : ∀ n p, IsPolyBounded p (n+1) → p n ≠ 0 → ∀ S, (∀ r ∈ S, prcIsRoot K p r) → prcDistinct S → S.length ≤ n`・`prcIsRoot`・`prc_root_of_eval`（`PolyRootCount.lean`） | **根の個数上界は既に本物**。K := `gefNF268 …` に適用可 |
| Φ データ | `cpdPhiP p`・`cpdPhiP_coeff/bound/lead`・**`cpd_factor : cpdXpMinus1 p = psMul cpdXMinus1 (cpdPhiP p)`**・`cpdPhi3_eq : cpdPhiP 3 = cq0PS`・**`cpdPhi9`（x⁶+x³+1）・`cpdPhi9_bound`**（`CyclotomicPolyData.lean`） | 法多項式の実データ。**Φ_9 の先頭係数補題と既約性のみ未着手** |
| Φ₃ 既約 | `cqi_irreducible : pibIrreducible ratRing cq0PS`（IsPoly 約元の忠実な定義・`Cq3Irreducible.lean`）・`cq0_bound : IsPolyBounded ratRing cq0PS 3`・`cq0_lead : cq0PS 2 ≠ ratRing.zero`（`Cq3Base.lean`） | **ℚ(ζ₃) の gefNF 体化の入力は全部揃っている**（§1.1） |
| Galois 機構 | `FieldAut K`（明示 invFun）・`FieldAut.ext`・`fieldAutGroup`・`FieldExtension`（base/top : IUTField・incl 環準同型）・`galoisSubgroup`/`galoisGroupGrp`（`FieldAutGroup.lean`） | 各段の Gal。型制約（IUTField 要求）は F6 で満たせる |
| 手本 | `qdf_decompose`/`qdf_apply`/`qdf_galois_order_two`/`qdf_galoisGroup_order_two`（`QuadraticField.lean`） | 「σ は生成元の像で決まる」＋ invFun 確定の完成イディオム（写経元） |
| 受け皿 | `ProfinitePi1Tower`（`restr : ∀ {i j}, i ≤ j → Hom (galoisGroupGrp (ext j)) (galoisGroupGrp (ext i))` は **witness**）・`profPi1Limit`・`profPi1_is_profinite`（`ProfinitePi1.lean`）・`Hom G H`（map・map_mul、`FundamentalGroup.lean`） | 塔差し込みは束ねのみ（本設計 W-C 完了後） |
| 付値 | `pvqAux/pvqNatVal`・`pvqNatVal_spec`（v_p(p^k·n') = k）・`pvq_natval_mul`・`prime_pow_extract`・`pvqVal : PreRat → Int`・`pvq_val_wd/mul/p`（`PadicValuationQ.lean`）・`pvqVal_zero_of_not_dvd`（`PadicAbsValueQ.lean`）・`rzd_zero_or_ne`・`rzd_eq_zero_iff`（`RatZeroDecide.lean`） | E 系列（Eisenstein）の土台。**超距離・QRat 持ち上げ・Gauss 付値は未整備**（§1.2） |
| 評価準同型 | `evalSum {K E : CRing} (ι : RingHom K E) (α : E.carrier) (f : PS K) (n : Nat) : E.carrier`・`evalHom_add/mul/stable`・`evalHomId`・**`psConstHom (R) : RingHom R (psRing R)`**（`EvaluationHom.lean`/`PowerSeries.lean`） | **E := psRing ratRing でも使える**——シフト x↦x+1・stretch x↦x³ を evalSum で書ける（§1.2/§2.2 の鍵） |
| 除法・整域 | `field_division_exists`・`mul_eq_zero_left268`・`psMul_g_top_coeff268`・`psMul_single_coeff268`・`pdv_deg_zero_unit`・`pdb_dvd_deg_le`（M268F/M272F） | 次数簿記・零因子なし |

**結論（差分の要約）**: 前段設計で「★A1 待ち」だった K 系列（各段の体化・Gal）は
**待ちが解けた**。壁は 2 つに減った: **(壁 1) Φ_9 の `pibIrreducible`**（E 系列）と
**(壁 2) res の構成**（R 系列）。そして壁 2 のうち **n = 1 段（Gal(ℚ(ζ₃)/ℚ) の
完全決定）は仮説ゼロで今すぐ本物に建てられる**（§2.1）。

---

## 1. 問い 1: 円分体インスタンス

### 1.1 ℚ(ζ₃) = ℚ[x]/(Φ₃) は**即日実装可能**（入力が全部揃っている）

`gefNFIUTField` の 6 引数と現物の対応（型まで一致することを確認済み）:

| 引数 | 現物 | 所在 |
|---|---|---|
| `f` | `cq0PS`（= x²+x+1、`cpdPhi3_eq` で `cpdPhiP 3` と一致） | `Cq3Base` |
| `nf` | `2` | — |
| `hb : IsPolyBounded ratRing cq0PS 3` | `cq0_bound` | `Cq3Base` |
| `hl : cq0PS 2 ≠ ratRing.zero` | `cq0_lead` | `Cq3Base` |
| `hn : 1 ≤ 2` | `by omega` 級 | — |
| `hirr : pibIrreducible ratRing cq0PS` | `cqi_irreducible` | `Cq3Irreducible` |

よって新規ファイル **CNF**（§5 W-A1）で

```lean
def cnfPhi3Field : IUTField :=
  gefNFIUTField cq0PS 2 cq0_bound cq0_lead cnf_one_le_two cqi_irreducible
def cnfPhi3F268 : Field268 :=
  gefNF268 cq0PS 2 cq0_bound cq0_lead cnf_one_le_two cqi_irreducible
```

が 1 行ずつで立つ。続いて **F9-7 の discharge**（一般 f の定数埋め込み——
`GenExtBasisAlpha.lean` 正直申告が「F6 待ち」と保留していたもの）:

```lean
-- 定数埋め込み（一般 f・nf ≥ 1 で psC c は nf 有界: j ≥ nf ≥ 1 ⟹ psC c j = 0）
def gefNFConst (f : PS ratRing) (nf : Nat) (hn : 1 ≤ nf) (c : QRat) : GefNF f nf :=
  ⟨psC ratRing c, fun j hj => if_neg (by omega)⟩

-- ℚ ⊂ ℚ[x]/(f) の FieldExtension（一般 f 版・cnfExt3 はその実例化）
def gefNFExtQ (f nf hb hl hn hirr) : FieldExtension where
  base := ratIUTField
  top  := gefNFIUTField f nf hb hl hn hirr
  incl := gefNFConst f nf hn
  incl_add := …   -- Subtype.ext + funext + psC の係数場合分け（rfl 級）
  incl_mul := …   -- NF 積 = pfdRed f nf nf (psC a · psC b)。psConstHom.map_mul で
                  -- psC a · psC b = psC (a·b)（deg 0 < nf）⟹ pfdRed_of_bounded で簡約不要
  incl_one := …   -- one = ⟨psOne,…⟩・psC 1 = psOne（係数ごと）
def cnfExt3 : FieldExtension := gefNFExtQ cq0PS 2 cq0_bound cq0_lead … cqi_irreducible
def cnfGal3 : Grp := galoisGroupGrp cnfExt3
```

山場は `incl_mul` 1 本（`pfdRed_of_bounded` 適用・10 行級）。tier **S–M**。
補助として `gefNFConst_inj`（0 次係数読み出しで単射——`FieldExtension` に単射性
公理が無い分の呼び出し側証明。scout §2-1 の指摘の discharge）も同ファイルで出す。

### 1.2 ℚ(ζ₉): Φ_9 の既約性が唯一の欠落——Eisenstein（x↦x+1）の最小経路

`cpdPhi9`（x⁶+x³+1）・`cpdPhi9_bound` は実在。先頭係数 `cpdPhi9 6 = 1 ≠ 0` は
if 分岐 3 本の小補題。**欠けているのは `pibIrreducible ratRing cpdPhi9` のみ**で、
これが立てば `cnfPhi9Field := gefNFIUTField cpdPhi9 6 …` が 1 行で立つ。

**問いへの回答: 「Eisenstein 判定を x↦x+1 代用で使えるか」——使える。ただし
一般 E4（freshman's dream・一般 p^n）は不要**で、Φ_9 は次数 6 の**具体多項式**
なのでシフト像を明示係数で持てる:

    Φ_9(x+1) = (x+1)⁶ + (x+1)³ + 1 = x⁶ + 6x⁵ + 15x⁴ + 21x³ + 18x² + 9x + 3

係数 (3, 9, 18, 21, 15, 6, 1)。p = 3 で Eisenstein: v₃(3) = 1・中間係数
9,18,21,15,6 はすべて 3 の倍数（v₃ ≥ 1）・先頭 1 は v₃ = 0。✓（手計算検算済み）

core Lean での現実的な最小経路を 4 段に分解する（前段設計 E 系列の**軽量化版**。
E1/E2/E3 は一般判定器としてそのまま前段設計の資産になる）:

- **E1 `IUT/PadicUltrametricQ.lean`**（prefix `pum`・★A1 非依存・[opus]）:
  超距離の **Int 整除形**での最小セット。QRat の商をくぐる前に
  `pvqNatVal` の整除特徴付けを立てる:
  ```lean
  theorem pum_pow_dvd_of_le (p : Nat) (hp : IsPrime p) (n k : Nat) (hn : 1 ≤ n)
      (h : k ≤ pvqNatVal p n) : p ^ k ∣ n
  theorem pum_le_of_pow_dvd (p : Nat) (hp : IsPrime p) (n k : Nat) (hn : 1 ≤ n)
      (h : p ^ k ∣ n) : k ≤ pvqNatVal p n
  -- 証明: prime_pow_extract で n = p^a·n'（p∤n'）に分解し pvqNatVal_spec で
  -- pvqNatVal = a。順方向は p^k ∣ p^a·n'。逆方向は k > a なら p ∣ n' で矛盾。
  theorem pum_natval_add_ge (p …) (m n : Nat) (hm hn : 1 ≤ …) (hmn : 1 ≤ m + n)
      (h : k ≤ pvqNatVal p m) (h' : k ≤ pvqNatVal p n) : k ≤ pvqNatVal p (m + n)
  -- p^k ∣ m ∧ p^k ∣ n ⟹ p^k ∣ m+n（Nat.dvd_add）＋ pum_le_of_pow_dvd
  ```
  および PreRat 加法（分子 = num₁·den₂ + num₂·den₁）への持ち上げ
  `pum_val_add_ge_min`（v(x+y) ≥ min(v x, v y)、x,y,x+y の分子非零仮定つき）と
  等号条件 `pum_val_add_eq`（v x < v y ⟹ v(x+y) = v x——「v(x+y) ≥ v x かつ
  v(y) = v((x+y) − x) ≥ min にならぬよう対偶」の標準 3 行論法を交差積簿記で）。
  Int の符号は natAbs 経由で `Int.natAbs_add_le` 型の分岐が要る——ここが E1 の
  実装上の泥。**Int 上の別動線**（`(p:Int)^k ∣ a` を主語にし natAbs 橋
  `pum_int_dvd_iff_natAbs` 1 本で Nat に落とす）を推奨する。

- **E2 `IUT/GaussValuationQ.lean`**（prefix `egv`・[opus・詰まりは fable スポット]）:
  1. **QRat 付値の商持ち上げ**（前段設計に無かった明示ステップ・必須）:
     `pvqVal` は PreRat 上で、`pvq_val_wd` は**分子非零**の代表間でのみ well-defined。
     零類は代表間で分子 0 が保存される（`rzd_eq_zero_iff` の両向き）ので
     ```lean
     def egvValQ (p : Nat) (hp : IsPrime p) : QRat → Int :=
       Quot.lift (fun r => if r.num = 0 then 0 else pvqVal p r) (…wd…)
     -- wd: 両方零なら 0 = 0、両方非零なら pvq_val_wd、片方零は ratRel が排除
     theorem egvValQ_mul …  -- pvq_val_mul の商版（非零 2 元）
     theorem egvValQ_p : egvValQ p hp (qOfInt p) = 1   -- pvq_val_p の商版
     ```
  2. **最小添字補題**（Eisenstein の核）: g, h : PS ratRing・IsPoly・非零、
     i₀ := 「v(g_i) が最小値を取る**最小の**添字」（明示 witness として受け取る:
     `(hgmin : ∀ i, g i ≠ 0 → egvValQ (g i₀) ≤ egvValQ (g i))`・
     `(hglt : ∀ i, i < i₀ → g i ≠ 0 → egvValQ (g i₀) < egvValQ (g i))` の 2 仮定
     ——「min の存在」の抽出走査を書かずに済む形で E3 から渡す）に対し
     ```lean
     theorem egv_min_index_mul :
         egvValQ ((g·h) (i₀+j₀)) = egvValQ (g i₀) + egvValQ (h j₀)
     -- Cauchy 和 Σ_{k≤i₀+j₀} g_k·h_{i₀+j₀−k}。k = i₀ の対角項の v は和、
     -- k < i₀ の項は v(g_k) が真に大きい（hglt）、k > i₀ の項は h 側添字 < j₀ で
     -- v(h_…) が大きいか等しく g 側 ≥ で総和的に真に大きい…に見えるが、
     -- **正確には**: 対角以外の各項 v > v(g_{i₀})+v(h_{j₀}) を示し、
     -- pum_val_add_eq（強い方が勝つ超距離等号）を rsum の帰納で回す。
     -- 零係数項は「v = +∞」扱い——項が psC 0 なら和から消える分岐を
     -- rzd_zero_or_ne で処理（Int に ∞ を持ち込まない）。
     ```
     ここが E 系列の最重量（前段設計どおり）。**fable スポット許可枠**。

- **E3 `IUT/EisensteinCriterionQ.lean`**（prefix `eis`・[opus（本ドキュメントで
  詳細化済みのため fable 前置は不要へ格下げ）]）:
  ```lean
  theorem eis_irreducible (f : PS ratRing) (n : Nat) (p : Nat) (hp : IsPrime p)
      (hb : IsPolyBounded ratRing f (n + 1)) (hn : 1 ≤ n)
      (hlead : egvValQ p hp (f n) = 0)              -- 先頭 v = 0（モニック緩和）
      (hmid : ∀ i, i < n → f i ≠ ratRing.zero → 1 ≤ egvValQ p hp (f i))
      (hconst : egvValQ p hp (f 0) = 1) (hc0 : f 0 ≠ ratRing.zero) :
      pibIrreducible ratRing f
  ```
  骨子（前段設計 E3 の具体化・全部品実在）: f = c·d（IsPoly 両側）を仮定。
  `plo_lead_oracle_Q` で c, d の先頭位置 nc, nd を取り、`psMul_g_top_coeff268` で
  nc + nd = n・先頭係数の積分解。nd = 0 ⟹ `pdv_deg_zero_unit` で単元（左枝）。
  nd = n ⟹ 余因子 c が次数 0 ⟹ 単元 ⟹ `pdbAssoc`（右枝、`Cq3Irreducible` の
  nd=2 枝の写経）。**中間次数 1 ≤ nd ≤ n−1 の排除が Eisenstein の本体**:
  d, c それぞれの「v 最小・最小添字」i₀, j₀ を**下から走査で構成**
  （`rzd_zero_or_ne` の有限連言・添字 ≤ nd の有限走査関数——choice 不使用）。
  egv_min_index_mul で v(f_{i₀+j₀}) = v(d_{i₀}) + v(c_{j₀})。
  一方 v(f) の側は hmid/hconst/hlead で「v(f_k) = 0 は k = n のみ」。
  v(d_{i₀}) + v(c_{j₀}) = egvMin d + egvMin c ≤ v(d_nd) + v(c_nc) = v(f_n) = 0、
  かつ ≥ 0 になる保証は無いが**等式 v(f_{i₀+j₀}) ≥ 1（i₀+j₀ < n のとき）**と
  合わせ i₀ + j₀ = n を強制 ⟹ i₀ = nd, j₀ = nc ⟹ 全下位係数で
  v(d_i) > v(d_{nd})・v(c_j) > v(c_{nc})、特に定数項
  v(f_0) = v(d_0) + v(c_0) ≥ (v(d_{nd})+1) + (v(c_{nc})+1) = 2 > 1 = v(f_0) で矛盾。
  ※ 有理係数のまま回すので **v(d_i) < 0 もあり得るが論法は min の位置しか
  使わない**（Gauss の補題・ℤ[x] 往復・content は最後まで不要）。

- **E4′ `IUT/Phi9Eisenstein.lean`**（prefix `p9e`・**一般 E4 の代替（軽量・具体）**
  ・[opus]）:
  1. シフト準同型は**新規演算子を作らず** `evalSum` を E := `psRing ratRing` で使う:
     ```lean
     def p9eXp1 : PS ratRing := psAdd ratRing (psSingle ratRing ratRing.one 1)
       (psC ratRing ratRing.one)                          -- x+1
     def p9eShift (f : PS ratRing) (N : Nat) : PS ratRing :=
       evalSum (psConstHom ratRing) p9eXp1 f N            -- f(x+1)（打切 N）
     ```
     乗法性・加法性は `evalHom_mul`/`evalHom_add` が**そのまま供給**（新規証明ゼロ）。
  2. **(x+1)^k の明示係数（Pascal 行・k ≤ 6）**: `rpow (psRing ratRing) p9eXp1 k` の
     j 次係数 = C(k,j) を k = 0..6 の 7 本の小補題で確定（`psMul_single_coeff268` と
     rsum の一点集中・数値は 1,6,15,20,15,6,1 等の QRat 数値等式——
     `Binomial2.lean` に既存の二項部品があれば流用、無ければ直接数値）。
  3. `p9eShifted`（係数 (3,9,18,21,15,6,1) の明示多項式）と
     `p9e_shift_eq : ∀ j, p9eShift cpdPhi9 7 j = p9eShifted j`（係数 8 本の照合）。
  4. **Eisenstein 入力の数値検証**: v₃(3) = 1（`pvq_val_p` の商版）、
     v₃(9) = 2・v₃(18) = 2・v₃(21) = 1・v₃(15) = 1・v₃(6) = 1（各
     `pvqNatVal_spec` の具体 k, n' 代入: 9 = 3²·1, 18 = 3²·2, 21 = 3·7, …）、
     v₃(1) = 0。⟹ `eis_irreducible` 適用で `pibIrreducible ratRing p9eShifted`。
  5. **輸送（逆シフト不要の片道論法）**: `pibIrreducible ratRing cpdPhi9` を示す。
     Φ_9 = c·d（IsPoly）とすると shift の乗法性で
     p9eShifted = (p9eShift c)·(p9eShift d)。次数保存補題
     ```lean
     theorem p9e_shift_lead (f : PS ratRing) (N : Nat)
         (hf : IsPolyBounded ratRing f (N + 1)) :
         (p9eShift f (N + 1)) N = f N ∧ IsPolyBounded ratRing (p9eShift f (N+1)) (N+1)
     -- rpow p9eXp1 i は (i+1) 有界・先頭係数 1（i 帰納 + psMul_g_top_coeff268）。
     -- 三角性: N 次係数に効くのは i = N の項のみ。
     ```
     で deg(p9eShift d) = deg d。p9eShifted の既約性から p9eShift d が単元 or
     同伴 ⟹ 次数 0 or n ⟹ **d 自身が**次数 0（`pdv_deg_zero_unit` で単元）or
     次数 n（余因子 c が次数 0 ⟹ Φ_9 ∣ d を `Cq3Irreducible` nd=2 枝の写経で
     構成し `pdbAssoc`）。**逆方向シフト x↦x−1 と合成恒等式は一切不要**。
  6. 仕上げ: `p9e_phi9_lead : cpdPhi9 6 ≠ ratRing.zero`（if 分岐 3 本）と
     ```lean
     theorem p9e_irreducible : pibIrreducible ratRing cpdPhi9
     def cnfPhi9Field : IUTField := gefNFIUTField cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead … p9e_irreducible
     def cnfExt9 : FieldExtension := gefNFExtQ cpdPhi9 6 …
     ```

**判定**: 現実的。総工数は E1+E2+E3+E4′ で新規 4 ファイル・概算 1200–1800 行
（E2 の超距離帰納が最大変数）。**ただし壁 1 は壁 2 と独立**なので、
Φ_9 既約性は**独立サブタスク**として並行させ、W-A（§2.1）は待たずに進める。
E 系列が万一難航した場合の正直な代替: ℚ(ζ₃)/ℚ の 1 段（W-A）＋ res の n=1
イディオム確立までで止め、A3 は「条件付き 2 段目」と正直申告する（§4）。

---

## 2. 問い 2: 制限準同型 res の壁の分解——いま仮説なしで証明できる部分

### 2.0 壁の正確な Lean 型

目標は `ProfinitePi1Tower.restr` の witness を初めて本物で discharge する 1 コマ:

```lean
def cr39Res : Hom (galoisGroupGrp cnfExt9) (galoisGroupGrp cnfExt3)
-- carrier: {σ : FieldAut cnfPhi9Field // ∀ k, σ.toFun (gefNFConst … k) = gefNFConst … k}
--        → 同型（cnfExt3 側）
theorem cr39_res_compat (σ …) : ∀ y, cr39Iota.toFun ((cr39Res.map σ).val.toFun? …) …
-- ι ∘ res(σ) = σ ∘ ι（「本当に制限である」の意味論）
```

scout §2 が列挙した 4 欠落の現況（本設計での対応）:

| 欠落 | 対応 | 状態 |
|---|---|---|
| (1) incl の単射性 | `gefNFConst_inj`（0 次係数読み出し） | W-A1 で即 discharge |
| (2) 部分体保存 σ(ι(K₁)) ⊆ ι(K₁) | 抽象正規性でなく**円分の指標** σ(x̄₉) = x̄₉^a に落とす（本節） | W-A2 で n=1 イディオム確立 → W-C |
| (3) res(σ) の明示 invFun | res(σ⁻¹) を invFun に据え決定補題で左右逆 | W-C（cg3 の位数 2 なら**対合**で自動） |
| (4) 群準同型性 | 決定補題での一点比較（σ(x̄) の像だけ見る） | W-C |

### 2.1 いま仮説ゼロで証明できる部分（本設計の主推奨 W-A2）: Gal(ℚ(ζ₃)/ℚ) の完全決定

**主張**: `cnfGal3` は位数ちょうど 2——元は id と共役 σ₁ : x̄ ↦ −1−x̄ のみ。
（(ℤ/3)^× ≅ ℤ/2 の実現。x̄² の NF 簡約が −1−x̄ なので「ζ↦ζ²」と同じもの。）
入力は全て実在資産（F6・R1・cqi_irreducible）で、**honest 仮説パラメータは 0 本**。

新規ファイル **CG3 `IUT/CyclotomicGal3.lean`**（prefix `cg3`）の段分解:

```lean
-- (G1) 生成元と基本計算（全て具体係数・pfdRed_of_bounded / pfdRed_char で確定）
def cg3Alpha : (cnfPhi3Field).carrier := gefNFMon cq0PS 2 1 (by omega)   -- x̄
def cg3Beta  : (cnfPhi3Field).carrier := ⟨…⟩   -- −1−x（明示係数 j=0 ↦ −1, j=1 ↦ −1）
theorem cg3_alpha_sq : (cnfPhi3Field).mul cg3Alpha cg3Alpha = cg3Beta
-- x·x = x²、pfdRed cq0PS 2 2 (x²) = −1−x。witness: x² − (−1−x) = 1·Φ₃ ⟹ pfdRed_char
theorem cg3_phi_alpha : Φ₃(α) = 0 と cg3_phi_beta : Φ₃(β) = 0
-- α²+α+1 = (−1−α)+α+1 = 0（cg3_alpha_sq から環算術のみ）。β 側も同様
theorem cg3_alpha_ne_beta : cg3Alpha ≠ cg3Beta   -- 1 次係数 1 ≠ −1（rzd 級）

-- (G2) 共役 σ₁ の構成（substitution 準同型の n=1 実例 = 前段設計 R3-5 の初出）
def cg3ConjFun : carrier → carrier := fun y => ⟨fun j =>
  if j = 0 then ratRing.add (y.val 0) (ratRing.neg (y.val 1))
  else if j = 1 then ratRing.neg (y.val 1) else ratRing.zero, …⟩
-- 意味論: y₀ + y₁x ↦ y₀ + y₁(−1−x) = (y₀−y₁) + (−y₁)x。deg ≤ 1 なので簡約不要
theorem cg3Conj_add : map_add（成分ごと・線形。環算術 10 行級）
theorem cg3Conj_mul : map_mul   -- ★G2 の山場・前段設計 ctw_rem_unique イディオムの初出
-- u·v（NF 積）= pfdRed(u.val·v.val)。u.val·v.val = q·Φ₃ + r（q は**定数**——
--   deg(uv) ≤ 2 = deg Φ₃ なので q = psC (u₁v₁)、r = uv − u₁v₁Φ₃ を明示式で持てる）。
-- σ₁ を PS 上の代入 ev_β = evalSum (psConstHom ratRing) (−1−x) · 2 と同一視し
--   （cg3ConjFun_eq_evalSum: 係数 2 本の照合）、evalHom_add/mul で
--   ev_β(uv) = ev_β(q)·ev_β(Φ₃) + ev_β(r)、ev_β(Φ₃) = Φ₃（β²+β+1 = x²+x+1 の
--   PS 計算・具体係数）⟹ 差が (ev_β q)·Φ₃ ⟹ gnfCong ⟹ pfdRed_char で
--   σ₁(uv) = σ₁(u)·σ₁(v)。全部品実在（gnfCong_* は GenExtFieldNF から輸入）
def cg3Conj : FieldAut cnfPhi3Field :=
  { toFun := cg3ConjFun, invFun := cg3ConjFun,     -- 対合（σ₁² = id は係数計算）
    left_inv := cg3Conj_invol, right_inv := cg3Conj_invol, … }
theorem cg3Conj_mem : (galoisSubgroup cnfExt3).mem cg3Conj   -- 定数は j=1 係数 0 で不動

-- (G3) 決定補題（前段設計 R3-3 の n=1 初出・res の 4 用途の原型）
theorem cg3_decompose (y : carrier) :
    y = add (incl (y.val 0)) (mul (incl (y.val 1)) cg3Alpha)
-- qdf_decompose の写経: psC y₀ + (psC y₁)·x は deg ≤ 1 ⟹ 簡約不要 ⟹ 係数照合
theorem cg3_aut_ext (σ τ : FieldAut cnfPhi3Field)
    (hσ : mem σ) (hτ : mem τ) (h : σ.toFun cg3Alpha = τ.toFun cg3Alpha) : σ = τ
-- toFun: cg3_decompose + map_add/map_mul + 定数固定で全点一致。
-- invFun: FieldAut.ext + funext + left_inv/right_inv（qdf_galois_order_two 末尾の写経）

-- (G4) σ(α) は Φ₃ の根 ⟹ α か β（R1 の初適用）
theorem cg3_sigma_alpha_root (σ …) : prcIsRoot cnfPhi3F268 (Φ₃ を PS carrier 係数に
  持ち上げた cg3PhiTop) (σ.toFun cg3Alpha)
-- Φ₃(σα) = σ(Φ₃(α)) = σ(0) = 0（map_add/map_mul/定数固定・evalSum 展開）
-- ※ 技術注意: prcIsRoot は「係数 ∈ K の多項式」を取るので Φ₃ の係数 1,1,1 を
--   incl で K 側へ持ち上げた cg3PhiTop : PS (cnfPhi3F268.ring) を定義して使う
theorem cg3_root_dichotomy (r : carrier) (hr : prcIsRoot … r) : r = cg3Alpha ∨ r = cg3Beta
-- 排中せず: r ≠ α ∧ r ≠ β と仮定すると [r, α, β] が相異なる 3 根 ⟹
-- prc_roots_le_degree cnfPhi3F268 2 cg3PhiTop … で length 3 ≤ 2 の矛盾。
-- r = α / r = β の判定は carrier の係数 2 本の rzd_zero_or_ne 場合分けで構成的に

-- (G5) capstone: 位数ちょうど 2（qdf_galoisGroup_order_two と同形の主張）
theorem cg3_galois_order_two :
    ∃ g : (galoisGroupGrp cnfExt3).carrier, g ≠ one ∧ ∀ h, h = one ∨ h = g
-- g := ⟨cg3Conj, cg3Conj_mem⟩。h は cg3_sigma_alpha_root → cg3_root_dichotomy →
-- cg3_aut_ext（σα = α なら id と一致・σα = β なら cg3Conj と一致）
```

**これが「いま仮説なしで証明できる部分」の切り出し**である。G2 の代入準同型
イディオムと G3 の決定補題は、そのまま前段設計 R3-5/R3-3 の一般 n 版の
**忠実な n = 1 インスタンス**であり、W-C（res 本体）の 4 箇所で再利用される。
既存 `qdf_galois_order_two`（ℚ×ℚ 直積担体）との違い＝**存在意義**: gefNF 担体は
ζ_9・一般 n にそのままスケールする**唯一の担体**であり（qdf は 2 次固定）、
G2/G3 は qdf には無い「剰余簡約越しの環準同型性・n 項分解」を初めて閉じる。

### 2.2 残る壁（W-C・Φ_9 完成後）: 2 段塔の res_1 の段分解

前段設計 §2 の R2/R3 を **p=3, n=1 の具体 2 段**に固定した縮約（一般 stretch
`ctpStretch_mul` を**回避**できることが新しい発見）:

- **CE39 `IUT/CyclotomicEmbed39.lean`**（ι : K₁ ↪ K₂、x̄₃ ↦ x̄₉³）:
  担体写像は (a + bx) ↦ (a + bx³)（明示係数・deg 1 ↦ deg 3 < 6 で簡約不要）。
  乗法性: u·v の Φ₃ 簡約は余因子が**定数** q = psC(u₁v₁)（deg uv ≤ 2）なので、
  「stretch の乗法性」は (a+bx³)(c+dx³) = ac+(ad+bc)x³+bd x⁶ の**具体 3 係数計算**と
  q·Φ₃ ↦ q·Φ_9（定数×多項式・`gefSmulCoeff`）だけで済む。一般 T0 不要。
  仕上げ: `ce39_phi9_eq_phi3_cubed`（Φ₃(x³) = Φ_9 の係数照合・7 本）と
  `ce39_incl_compat`（ι ∘ incl₃ = incl₉、定数は不動）。
- **CM9 `IUT/CyclotomicMu9.lean`**（μ_9(K₂) = ⟨x̄₉⟩）:
  `cm9_factor : x⁹−1 = Φ_9·(x³−1)`（**具体 10 係数の Cauchy 照合**——一般
  `ctp_pow_sub_one` の代替。もしくは `cpd_factor` の p=9 版 (x−1)Φ̃ と組む案も
  あるが x⁹−1 = Φ_9·(x³−1) 直接照合が最短）⟹ 商で x̄₉⁹ = 1。
  x̄₉³ ≠ 1: x³−1 は deg 3 < 6 で NF・定数項 −1 ≠ 0。位数 9・冪 9 個相異
  （位数は 9 の約数で 3 でない ⟹ 9。指数の Nat.gcd 算術・omega 級）。
  y⁹ = 1 ⟹ y ∈ 冪: 9 個の相異冪 + y で 10 根 ⟹ `prc_roots_le_degree`
  （K := `gefNF268 cpdPhi9 6 …`、p := X⁹−1 の持ち上げ、n := 9）と矛盾。
  構成的抽出 `cm9Find`（a < 9 の下から走査・NF 係数 6 本の rzd 等値判定）。
- **CR39 `IUT/CyclotomicRes39.lean`**（res 本体）:
  指標 a := `cm9Find (σ.toFun x̄₉)`（σ(x̄₉)⁹ = 1 は map_mul の 9 連鎖）、
  3∤a（σ⁻¹ 側の b と ab ≡ 1 mod 9）。**res(σ) := (a mod 3 = 1 なら id、
  さもなくば cg3Conj)**——K₁ 側は G5 で自己同型が 2 個と**既に完全決定**して
  いるので、一般 R3-5 の代入準同型を K₁ 側で再構成する必要すらない。
  compat: σ(ι(x̄₃)) = σ(x̄₉³) = x̄₉^{3a}、x̄₉⁶ = −1−x̄₉³（Φ_9(x̄₉) = 0 の直接帰結）
  ⟹ a≡1: = ι(x̄₃)・a≡2: = ι(−1−x̄₃) = ι(cg3Conj x̄₃)（3a mod 9 ∈ {3,6} の 2 分岐）。
  群準同型性: a(στ) ≡ a(σ)a(τ) mod 9（cm9Find の一意性 = 冪の相異性）⟹ mod 3
  でも積 ⟹ ℤ/2 の積表と cg3 側 2×2 表の照合（4 ケース・決定補題）。
  最後に 2 段塔を `ProfinitePi1Tower` に詰める場合は「n ≥ 2 で定数」でなく
  **A3 本丸は無限塔**なので、M1 時点では塔詰めを行わず `cr39Res` 単体＋
  compat を成果として報告する（定数延長で塔化して 0.05 を拾う誘惑は
  §3 規約の水増しに当たるため**採らない**。scout §4 の定数塔却下と同判断）。

---

## 3. 問い 3: 最小 complete_pct 前進ステップの特定と優先順位

台帳: A3 = weight 12・status 0.5（`target_ledger.json` 実測）。柱 A complete_pct 36
（`graph-meta.json`・「決定的欠落: 非自明有限体拡大が 1 つも構成されておらず
全 Galois 塔が trivialExtension 詰め」）。候補の自問（「この一手は実 IUT 完全
証明率を上げるか？」）:

| 候補 | 実 IUT を進めるか | 見積り（保守・監査が確定） | 判定 |
|---|---|---|---|
| **(a) W-A: cnf + cg3**（ℚ(ζ₃) の gefNF 体化・ℚ↪K₁ 拡大・Gal 位数 2 の完全決定） | **Yes**——「非自明有限体拡大が 1 つも構成されていない」欠落の初 discharge を**スケールする担体**（gefNF）上で行い、res に必須の決定補題・代入イディオムを本物で確立。qdf の再演でなく R3 系の初出 | A3 0.5→**0.52–0.55**（単段のみ・res 未達なので小幅。ただし後続の必須経路） | **最優先・即時着手可（仮説 0）** |
| **(b) W-B: E1–E3 + E4′ → ℚ(ζ₉) 構成** | **Yes**——Φ_9 既約性は 2 段目の唯一の欠落。E1–E3 は一般判定器（x³−2 の別証明にも再利用）で本物建設(b) | 単体では A3 微動（体があるだけでは塔でない）: 0.55 前後。**価値は W-C の解禁** | **最優先と並行**（W-A と独立・4 ファイル並列可） |
| **(c) W-C: ce39/cm9/cr39 = res_1 本物構成** | **Yes（本丸）**——scout が「唯一かつ最大のボトルネック」と断じた witness restr の初 discharge | **A3 0.5→0.6**（前段設計 M1 と整合。Φ_9 discharge 済みが条件。hΦ9 が仮説なら 0.55 止まりと正直申告） | 第 2 波（W-A・W-B 完了後） |
| (d) 定数化する二次塔（scout §4 の近道） | **No**（§3 規約の degenerate。連鎖する非自明拡大でない） | — | **却下（前回どおり）** |
| (e) cg3 の capstone 束ね・qdf からの同型輸送 | No（complete_pct 不動の骨格整備） | — | 着手しない（要ユーザー確認事項にすらしない） |

**結論——最小 complete_pct 前進ステップ（優先順位つき）**:

1. **W-A1 (CNF)**: `cnfPhi3Field`/`gefNFExtQ`/`cnfExt3`/`gefNFConst_inj`。
   仮説 0・既存部品の直線合成 + `pfdRed_of_bounded` 1 山。F9-7 の discharge を兼ねる。
   [tier **S–M**: sonnet でも可・incl_mul で詰まれば opus]
2. **W-A2 (CG3)**: G1–G5。**本ラウンドの実質的な complete_pct 前進の最小単位**
   （非自明 Galois 群の完全決定を、塔にスケールする担体上で初めて本物化）。
   [tier **M**: opus。G2 の map_mul で詰まった場合のみ fable スポット]
3. **W-B (E1/E2/E4′ 並列 → E3)**: E1 [opus]・E2 [opus・fable スポット許可]・
   E4′ の 1–4 項（シフト・Pascal 行・係数照合・数値 v₃——E3 に非依存で先行可）
   [opus]。E3 は E1/E2 到着後 [opus]。
4. **W-C (CE39→CM9→CR39)**: res_1。完了時に A3 0.5→0.6 を申告し独立監査へ。
   [CE39/CM9: opus。CR39: opus 先行・詰まりのみ fable]

5 並列の初回ラウンド編成案: CNF [sonnet] + CG3 [opus] + E1 [opus] + E2 [opus] +
E4′(1–4) [opus]。（次ラウンド: E3 [opus] + CE39 [opus] + CM9 [opus] +
CG3/E2 の詰まり回収 [fable ≤1 枠] + 監査準備 [sonnet]。）

---

## 4. マイルストーンと status 予測（保守・独立監査が最終判定）

| 里程 | 内容 | A3 status 予測 | complete_pct 注記 |
|---|---|---|---|
| **M0.5**（W-A） | ℚ(ζ₃) gefNF 体化 + Gal 完全決定（位数 2・元の列挙） | 0.5→**0.52–0.55** | 柱 A は小数点以下の前進見込み（丸めで据え置きの可能性を正直申告） |
| **M0.7**（W-B） | Φ_9 既約（Eisenstein 一般判定器込み）+ ℚ(ζ₉) 体化 | 0.55 前後 | E1–E3 は一般資産（他の既約性にも再利用） |
| **M1**（W-C） | res_1 : Gal(ℚ(ζ₉)/ℚ) → Gal(ℚ(ζ₃)/ℚ) 本物構成 + compat | **0.5→0.6** | 前段設計 M1 と同値。witness restr の初 discharge |
| M2–M4 | 一般 n 塔・逆極限・(ℤ/3^n)^× 同型 | 0.6→0.75 級 | 前段設計 §4 のまま（本ドキュメントの射程外） |

---

## 5. 実装規約（全新規ファイル共通・opus への指示に含める）

- **ヘッダ二軸**: 分類 [実]・complete_pct 影響を 1 行明記（本設計を引用）。
  W-A2 のみ「A3 の complete_pct 前進候補（監査確定待ち）」、他は「未設定
  （W-C 到達時に親が更新）」。
- **禁止タクティク**: simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp 不使用（既存イディオム: show + rw + omega + cases +
  induction + funext + Subtype.ext + refine/exact）。新規 Classical.choice 禁止
  （`#print axioms` = propext, Quot.sound を維持）。数値は QRat の明示計算
  （`rzd_*`・`cbp_one_ne_zero` 系）で閉じる。
- **新規ファイルのみ**・共有ファイル（IUT.lean/build.sh/dashboard/graph 系/
  target_ledger）不更新（親が統合時に一括）。
- 正直な限定を各ヘッダに**追記のみ**（消去・弱化禁止）。特に:
  (i) p = 3・ℚ 上・2 段までの部分ケースであること、(ii) M1 時点で res の
  全射性は未証明（M4 の σ_a 待ち）、(iii) K₁ は既存 cq3Field/qdfField(−3)/
  gfiCq3Field と**同型な第 4 の担体**であり同型輸送は対象外、(iv) E3 は
  「先頭 v = 0・定数項 v = 1」の正規化形での判定器であること（一般の
  スカラー正規化は呼び出し側 E4′ が具体係数で満たす）。

## 6. 正直な限定（本設計自身のもの・§4 規約により消さない）

1. 本ドキュメントは設計であり complete_pct を動かさない。status 予測は
   全て保守的見積りで、確定は独立監査（reaudit-A 系・AUDIT_RUBRIC 準拠）。
2. W-A 完了時点では「塔」は未成立（1 段 + Gal 決定のみ）。ラウンド報告では
   「res は未構成・M1 前」と明記する。
3. E2 の超距離最小添字補題は本設計でも最重量と評価（fable スポット枠を予約）。
   万一 E 系列が予算超過なら、Φ_9 既約性を**名前付き honest 仮説**として
   W-C を条件付きで先行する選択肢はあるが、その場合 A3 は 0.55 を超えない
   と正直申告する（前段設計 §4 正直申告 3 と同運用）。
4. §2.2 の「stretch 一般補題回避」は nf = 2（余因子が定数）に依存する短絡で、
   一般 n 段（M2）では前段設計 T0（`ctpStretch_mul`）が改めて必要になる。
   これは手抜きでなく「n = 1,2 の忠実な部分ケースを最短で本物化し、一般化は
   イディオム確立後」という §3 規約準拠の順序である。
