# B5 積公式 ∏_v |x|_v = 1（ℚ 上）— 最終組み立て段の詳細設計

- 種別: **設計ドキュメント（詳細化ラウンド成果物・コードなし）**
- 対象モジュール（実装予定）: `IUT/B5ProductFormulaQ.lean`（prefix `b5`）
- 分類（実装時ヘッダに転記）: **[実]** / complete_pct 影響: **あり**（B5「大域類体論/積公式(実)」の積公式側 0→0.5。実 v_p・実 |·|_∞・実素因数分解の上での本物の大域整合性）
- 制約: Lean 4.30.0 core・mathlib 禁止・sorry/新規 choice 禁止・許可タクティクは cases/obtain/induction/rw/show/refine/exact/apply/intro/funext/omega

---

## 0. 前提資産と interface 仮定

### 0.1 既存資産（確認済み・実在の名前）

| 名前 | 場所 | 型・内容 |
|---|---|---|
| `PreRat` / `ratRel` / `QRat` | `IUT/Rationals.lean` | `QRat = Quot ratRel`、`ratRel x y := x.num * y.den = y.num * x.den` |
| `prMul` / `prAbs` / `intToPreRat` / `preRat_ext` | 同上 | 代表演算。`prAbs x = ⟨intAbs x.num, x.den, _⟩` |
| `qMul` / `qInv` / `qAbs` / `ratRing` | 同上 | `ratRing.mul = qMul`・`ratRing.one = Quot.mk ratRel prOne`（定義的に一致、rfl） |
| `qMul_inv` | `Rationals.lean:697` | `x.num ≠ 0 → qMul (Quot.mk ratRel x) (qInv (Quot.mk ratRel x)) = Quot.mk ratRel prOne` — **最終段のキャンセルの要** |
| `quot_exact_rat` | `Rationals.lean:467` | `Quot.mk ratRel x = Quot.mk ratRel y → ratRel x y`（choice なし分離性） |
| `intAbs` / `intAbs_of_nonneg` / `intAbs_of_nonpos` / `intAbs_mul` | 同上 | Int 値絶対値 |
| `pvqNatVal : Nat → Nat → Nat` / `pvqVal : Nat → PreRat → Int` | `IUT/PadicValuationQ.lean` | `pvqVal p x = ↑(pvqNatVal p x.num.natAbs) − ↑(pvqNatVal p x.den.natAbs)` |
| `pvq_val_mul` / `pvq_val_p` / `pvq_natval_mul` / `natAbs_pos_of_ne` / `natAbs_den_pos` | 同上 | 加法性・健全性・非零 natAbs ≥ 1 |
| `arpAbs : ratIUTField.carrier → ratIUTField.carrier`（= `qAbs`） | `IUT/ArchAbsValueQ.lean` | `ratIUTField.carrier = QRat`（定義的） |
| `IsPrime` / `prime_pow_extract` / `euclid` | `IUT/Fermat.lean:182` / `IUT/NatPrimeParts.lean` | `IsPrime p := 2 ≤ p ∧ ∀ k, k ∣ p → k = 1 ∨ k = p` |
| `ratIUTField` / `IUTField.mul_ne_zero` 等 | `IUT/Field.lean` | ℚ は IUTField（逆元・整域性つき） |

### 0.2 並行 4 スライスの interface 仮定（シグネチャ規約）

型まで確定していないため、本設計は以下の**規約**を仮定する。ズレたら本節の対応表を親が更新してから実装に入ること。

- `PrimeFactorization.lean` (pfc):
  - `pfcFactors : Nat → List Nat`
  - `listProd : List Nat → Nat`（`listProd [] = 1`、`listProd (q :: L) = q * listProd L` が定義等式で取れること）
  - `pfc_prod_factors : ∀ n, 1 ≤ n → listProd (pfcFactors n) = n`
  - `pfc_vp_count : ∀ p n, IsPrime p → 1 ≤ n → pvqNatVal p n = List.count p (pfcFactors n)`
- `PadicAbsValueQ.lean` (pav):
  - `pavAbs : Nat → PreRat → QRat`（代表レベル、pvqVal と同じ流儀）で `pavAbs p x = p^{−pvqVal p x}`
  - `pav_mul : IsPrime p → x.num ≠ 0 → y.num ≠ 0 → pavAbs p (prMul x y) = qMul (pavAbs p x) (pavAbs p y)`
  - `pav_trivial : IsPrime p → ¬ (↑p ∣ x.num * x.den) → pavAbs p x = ratRing.one`（W1 でのみ使用）
- `FiniteSupportPrimeProduct.lean` (fsp):
  - `fspProd : (Nat → QRat) → List Nat → QRat`
  - `fsp_prod_mul_pointwise : fspProd (fun p => qMul (f p) (g p)) S = qMul (fspProd f S) (fspProd g S)`
  - `fsp_prod_append` / `fsp_prod_extend`（W1 でのみ使用）
- `ArchValueInteger.lean` (avi): `arpAbs (Quot.mk ratRel x) = |num|/den` の実等式。
  **注意（§2.6）: 本設計の A1 はこの実等式を経由せず自力で閉じられる**（avi は使えれば使う、無くても FINAL は成立）。avi への依存はクリティカルパスから外す。

### 0.3 スライスへの **interface 追加要求**（親が調整・不足なら b5 側で自前証明）

| # | 要求 | 理由 | 代替（スライスが出せない場合） |
|---|---|---|---|
| I-1 | `pfc_mem_prime : q ∈ pfcFactors n → IsPrime q` | S2（台の全要素が素数）に必須。pav 補題・pfc_vp_count の素数仮定を S 上で満たすため | pfc の構成（prime_factor_exists 由来）から容易のはず。出なければ b5 実装をブロック（自前導出は不可能） |
| I-2 | count の統一: `pfc_vp_count` の count が **core の `List.count`**（`Nat`, `instBEqNat`）であること | R1/R2/F4 は count の cons 展開に依存 | pfc が独自 count を使うなら橋渡し補題 `b5_count_bridge : pfcCount q L = List.count q L`（両者 induction で一致）を b5 冒頭に追加 |
| I-3 | fsp の定義等式 export: `fsp_nil : fspProd f [] = ratRing.one`・`fsp_cons : fspProd f (q :: S) = qMul (f q) (fspProd f S)` | F1/F2/F4 は list induction で fspProd を段ごとに開く必要がある | fspProd が structural recursion なら rfl。export されなければ b5 から `fspProd` を直接 unfold（`show` で定義形に落とす） |
| I-4 | `listProd` の cons/nil 定義等式 export（rfl 想定） | R2 の cons 段 | 同上 |
| I-5 | **`pav_cleared`（下記 P1）を pav スライス側で export**（最善）または pavAbs の場合分け定義等式（`pvqVal p x ≥ 0` 側 / `< 0` 側の代表の形）を export | P1 は pavAbs の内部表現（負冪をどの PreRat で表すか）に触れる唯一の補題 | b5 側で pavAbs を unfold して P1 を証明（§3 P1 のスケッチ参照）。**親は pav スライス担当に P1 の statement を先に共有すること** |

---

## 1. 最終定理の正確な statement

### 1.1 補助定義（b5 モジュール内）

```lean
/-- 自然数の ℚ への埋め込み n ↦ n/1。 -/
def b5N (n : Nat) : QRat := Quot.mk ratRel (intToPreRat (n : Int))

/-- 重複除去（Nat の DecidableEq、choice なし）。 -/
def b5Dedup : List Nat → List Nat
  | [] => []
  | q :: L => if q ∈ b5Dedup L then b5Dedup L else q :: b5Dedup L

/-- 積公式の有限台: num・den を割る素数のリスト（重複なし）。 -/
def b5Support (x : PreRat) : List Nat :=
  b5Dedup (pfcFactors x.num.natAbs ++ pfcFactors x.den.natAbs)
```

- `b5Dedup` の if 条件 `q ∈ b5Dedup L` は `Nat` の DecidableEq から決定可能（core の `List.instDecidableMemOfLawfulBEq` 系、choice なし）。インスタンス解決が渋ければ `(b5Dedup L).contains q = true` に置換（L1 の証明が contains↔Mem の橋渡し 1 本増えるだけ）。
- **設計判断**: `b5Support` は「重複なし」を **述語や Nodup 型ではなく count で管理**する（L2: 要素なら count = 1）。許可タクティクに simp が無い環境では、帰納法 + `rw [if_pos/if_neg]` + omega で閉じる count 形式が最も軽い。

### 1.2 最終定理

```lean
/-- **B5 積公式（ℚ、実）** — 非零有理数 x に対し
    |x|_∞ · ∏_{p ∈ Supp(x)} |x|_p = 1。
    台 Supp(x) = num·den を割る素数全体（それ以外の p では |x|_p = 1、W1 参照）。 -/
theorem b5_product_formula (x : PreRat) (hx : x.num ≠ 0) :
    ratRing.mul (arpAbs (Quot.mk ratRel x))
      (fspProd (fun p => pavAbs p x) (b5Support x))
    = ratRing.one
```

- `ratRing.mul = qMul`・`ratRing.one = Quot.mk ratRel prOne` は定義的（rfl）。証明内部は `qMul` 表記で進め、statement は capstone として `ratRing.*` に揃える。
- `arpAbs` の引数型 `ratIUTField.carrier` は `QRat` に definitionally equal（`Field.lean:151` で `toCRing := ratRing`, `carrier := QRat`）なので `Quot.mk ratRel x` がそのまま通る。
- 非零性は PreRat 代表の `x.num ≠ 0` で表す（pvqVal/pvq_val_mul と同じ「ℚ^× の choice なし忠実版」の流儀。QRat 全域でのゼロ判定選言は排中律を要するため対象外 — 既存の正直申告と整合）。

---

## 2. 証明 DAG — 核イディオム「両側 cleared form」

### 2.1 核となる設計判断（新イディオム）

素朴には「|x|_∞ = a/b、∏_p |x|_p = b/a、掛けて 1」だが、**b/a を直接作ると (i) 負冪 p^{−v}（v : Int）の表現、(ii) 逆元の有限積との交換（∏ (f p)⁻¹ = (∏ f p)⁻¹、各項非零の管理）という 2 つの重い補題群が要る**。これを両方回避するのが本設計の核:

> **cleared form イディオム**: 分母を払った乗法等式だけで組む。
> - アルキメデス側: `A · β = α` （A = |x|_∞, α = b5N a, β = b5N b, a = |num|, b = den）
> - p 進側: `P · α = β` （P = ∏_p |x|_p）
> - 合成: `(A·P)·α = A·(P·α) = A·β = α`、最後に `qMul_inv`（既存・witness 形）で α を 1 回だけキャンセルして `A·P = 1`。
>
> 逆元が登場するのはこの最終キャンセルの 1 箇所のみ。負冪 v : Int は pavAbs の内部（P1 の 1 補題）に完全に閉じ込め、DAG の残り全部は **Nat 冪 p^(pvqNatVal …) だけ**で走る。

p 進側 cleared form の中身は恒等式
`p^{−(v_p(a)−v_p(b))} · p^{v_p(a)} = p^{v_p(b)}`（P1、各素数ごと）と、
`∏_{p∈S} p^{v_p(n)} = n`（R2/R3、count による組み替え）の 2 段。

### 2.2 DAG 全景（→ は「が使われる」）

```
[core Nat/Int/List]      [pfc slice]              [pav slice]        [fsp slice]
      │                    │                          │                  │
  N1 b5N_mul           I-1 pfc_mem_prime         P1 pav_cleared      I-3 fsp_nil/cons
  N2 b5N_one           pfc_vp_count                  │               F3 fsp_prod_mul_pointwise
  N4 intAbs_eq_natAbs  pfc_prod_factors              │                  │
      │                listProd 定義等式(I-4)        │               F1 fsp_prod_one
  L1 dedup_mem              │                        │               F2 fsp_prod_congr
  L2 dedup_count            │                        │               F4 prod_indicator ←(L3,N2)
  L3 count_zero_not_mem     │                        │                  │
      │                     │                        │                  │
      ├──> R1 pow_count_cons┤                        │                  │
      │         │           │                        │                  │
      └──> R2 prod_pow_count = listProd  ←──(N1,N2,F1,F2,F3,F4,R1)      │
                │           │                        │                  │
           R3 prod_pow_val = b5N n  ←──(R2, pfc_vp_count, pfc_prod_factors)
                │                                    │
  S1 support_mem / S2 support_prime / S3 support_count  ←──(L1,L2,I-1)
                │                                    │
           Q1 prod_num = b5N a ・ Q2 prod_den = b5N b  ←──(R3,S1–S3)
                │                                    │
           G1 padic_cleared: P·α = β  ←──(Q1,Q2,P1,F2,F3,S2)
                │
  A1 arch_cleared: A·β = α  ←──(N4, prAbs, Quot.sound)   [avi 不要・使えれば短縮]
                │
        FINAL b5_product_formula  ←──(G1, A1, qMul_inv, ratRing 結合/可換/単位)
                │
        (optional) W1 support 拡大不変性 ←──(fsp_prod_extend, pav_trivial, I-6)
```

### 2.3 依存順のステップ列挙（どの補題 → どの補題）

1. **N 層**（依存: core のみ）: N1, N2, N4。
2. **L 層**（依存: core List）: L3 → L1 → L2。
3. **F 層**（依存: fsp の定義等式 I-3）: F1, F2；F4 は L3・N2・F1・F2 を使う。
4. **R1**（依存: core `List.count_cons`, `Nat.pow_succ`）。
5. **R2**（依存: R1, N1, N2, F1–F4, listProd 定義等式）— **本設計の最重量級**。
6. **R3**（依存: R2, `pfc_vp_count`, `pfc_prod_factors`）。
7. **S 層**（依存: L1, L2, `List.mem_append`, I-1）: S1 → S2, S3。
8. **Q1, Q2**（依存: R3, S1–S3, `natAbs_pos_of_ne`, `natAbs_den_pos`）。
9. **P1**（依存: pav の定義 or I-5 export、`Nat.pow_add`, Quot.sound）。
10. **G1**（依存: Q1, Q2, P1, F2, F3, S2）。
11. **A1**（依存: N4, `prAbs`, `preRat_ext`/Quot.sound）。
12. **FINAL**（依存: G1, A1, `qMul_inv`, ratRing の mul_assoc/mul_comm/one_mul）。
13. **W1**（optional、依存: `fsp_prod_extend`, `pav_trivial`, I-6）。

---

## 3. 中間補題 stub（型 + 一行証明スケッチ）— 実装チェックリスト

以下が親の実装順序付きチェックリスト。各項目は `型` と `証明スケッチ` のみ（sorry は書かない。実装時に上から順に、依存スライスの着地を待って埋める）。

### ☐ Step 1 — N 層（スライス不要、即着手可）

- **N1** `b5N_mul (m n : Nat) : b5N (m * n) = qMul (b5N m) (b5N n)`
  — スケッチ: `congrArg (Quot.mk ratRel)` + `preRat_ext`；分子 `(↑(m*n) : Int) = ↑m * ↑n` は `Int.ofNat_mul`（無ければ omega では閉じないので `Int.natCast_mul`；core 4.30 に存在）、分母 `1 = 1*1` は `Int.one_mul` の rw。
- **N2** `b5N_one : b5N 1 = ratRing.one`
  — スケッチ: `rfl`（`intToPreRat 1 = prOne` は成分 rfl）。rfl で落ちなければ `preRat_ext rfl rfl` + congrArg。
- **N4** `intAbs_eq_natAbs (a : Int) : intAbs a = (a.natAbs : Int)`
  — スケッチ: `cases Int.lt_or_le a 0`；負側 `intAbs_of_nonpos` + omega、非負側 `intAbs_of_nonneg` + omega（`Int.natAbs` の cast は omega が読める）。

### ☐ Step 2 — L 層（スライス不要、即着手可）

- **L3** `b5_count_zero_of_not_mem (q : Nat) (S : List Nat) (h : q ∉ S) : List.count q S = 0`
  — スケッチ: S の induction；cons 段で `List.count_cons` を rw し、頭 ≠ q（h から）で if を `if_neg`、IH。core に `List.count_eq_zero` があればそれで即。
- **L1** `b5_dedup_mem (q : Nat) (L : List Nat) : q ∈ b5Dedup L ↔ q ∈ L`
  — スケッチ: L の induction；cons 段は `b5Dedup` の if を `cases Decidable.em (head ∈ b5Dedup tail)` ならぬ decidable インスタンスの `if h : _` 場合分け（`rw [if_pos h] / [if_neg h]`）、`List.mem_cons` の往復 + IH。
- **L2** `b5_dedup_count (q : Nat) (L : List Nat) (hq : q ∈ L) : List.count q (b5Dedup L) = 1`
  — スケッチ: L の induction；cons 段、if の両分岐で `List.count_cons` + L1 + L3（「dedup に q が既にいる/いない」×「q = 頭か否か」の 4 通りを omega で束ねる）。

### ☐ Step 3 — F 層（fsp スライス着地後）

- **F1** `b5_fsp_one (S : List Nat) : fspProd (fun _ => ratRing.one) S = ratRing.one`
  — スケッチ: S の induction；`fsp_nil` / `fsp_cons`（I-3）+ `ratRing.one_mul`。
- **F2** `b5_fsp_congr {f g : Nat → QRat} (S : List Nat) (h : ∀ p, p ∈ S → f p = g p) : fspProd f S = fspProd g S`
  — スケッチ: S の induction；`fsp_cons` を両辺 rw、頭は `h _ (List.mem_cons_self ..)`、尾は IH に `fun p hp => h p (List.mem_cons_of_mem _ hp)`。
- **F4** `b5_prod_indicator (q : Nat) (S : List Nat) (h1 : List.count q S = 1) : fspProd (fun p => if p = q then b5N p else ratRing.one) S = b5N q`
  — スケッチ: S の induction；cons 段 `cases Decidable.em (head = q)`：
    (i) head = q なら count 等式から `List.count q tail = 0`（`count_cons` + omega）→ q ∉ tail（L3 の逆向き: count = 0 → ∉、これは membership → count ≥ 1 の対偶；core `List.count_pos_iff_mem` 相当が無ければ小補題 L3' を追加）→ 尾の各 p ∈ tail で p ≠ q → F2 で尾を定数 one に → F1 → `mul_one`（`ratRing.mul_comm` + `one_mul` で合成）。
    (ii) head ≠ q なら頭因子 `if_neg` で one → `one_mul` → IH（count 保存は `count_cons` + omega）。

### ☐ Step 4 — R1（core のみ、即着手可）

- **R1** `b5_pow_count_cons (p q : Nat) (L : List Nat) : p ^ List.count p (q :: L) = (if p = q then p else 1) * p ^ List.count p L`
  — スケッチ: `cases Decidable.em (p = q)`；等しい側は `count_cons` の if が発火して指数 +1、`Nat.pow_succ`（`p^(k+1) = p^k * p`）+ `Nat.mul_comm`；異なる側は count 不変で `Nat.one_mul`。**BEq 注意**: core の `List.count_cons` は `if head == p` 形。`Nat.beq_eq`／`beq_iff_eq` で Prop 等式へ橋渡ししてから rw（§4-6）。

### ☐ Step 5 — R2（核・最重量。F 層 + N 層 + listProd 定義等式）

- **R2** `b5_prod_pow_count (L S : List Nat) (hsub : ∀ r, r ∈ L → r ∈ S) (hcnt : ∀ q, q ∈ L → List.count q S = 1) : fspProd (fun p => b5N (p ^ List.count p L)) S = b5N (listProd L)`
  — スケッチ: **L の induction（S は固定）**。
    nil: 各 p で count = 0、`Nat.pow_zero` + N2 で因子は one → F2 → F1；右辺 `listProd [] = 1` → N2。
    cons q L': 各 p ∈ S で R1 + N1 + 「`b5N (if p = q then p else 1) = if p = q then b5N p else ratRing.one`」（cases で両分岐 rfl/N2）により
    `b5N (p ^ count p (q::L')) = qMul (if p = q then b5N p else ratRing.one) (b5N (p ^ count p L'))` — これを F2 で積の中へ、F3 で積を分割、左は F4（`hcnt q (mem_cons_self)`）で `b5N q`、右は IH（hsub/hcnt を尾へ制限）で `b5N (listProd L')`、最後に N1 逆向き + `listProd (q::L') = q * listProd L'`（I-4、rfl 想定）。
  - **ポイント**: S 側には素数性も nodup も要らない。「L ⊆ S」と「L の各元の S 内 count = 1」だけ。q ∈ L に対してのみ count 条件を要求する形にしておくと S3 がそのまま刺さる。

### ☐ Step 6 — R3（pfc スライス着地後）

- **R3** `b5_prod_pow_val (n : Nat) (hn : 1 ≤ n) (S : List Nat) (hpr : ∀ p, p ∈ S → IsPrime p) (hsub : ∀ r, r ∈ pfcFactors n → r ∈ S) (hcnt : ∀ q, q ∈ pfcFactors n → List.count q S = 1) : fspProd (fun p => b5N (p ^ pvqNatVal p n)) S = b5N n`
  — スケッチ: F2 で各 p ∈ S の指数を `pfc_vp_count p n (hpr p _) hn` により `List.count p (pfcFactors n)` へ書換 → R2 → `pfc_prod_factors n hn` で `listProd (pfcFactors n) = n`。

### ☐ Step 7 — S 層（pfc + I-1 着地後）

- **S1** `b5_support_mem (x : PreRat) (q : Nat) : q ∈ b5Support x ↔ (q ∈ pfcFactors x.num.natAbs ∨ q ∈ pfcFactors x.den.natAbs)`
  — スケッチ: L1 + `List.mem_append`。
- **S2** `b5_support_prime (x : PreRat) : ∀ p, p ∈ b5Support x → IsPrime p`
  — スケッチ: S1 → cases → `pfc_mem_prime`（I-1）。
- **S3** `b5_support_count (x : PreRat) (q : Nat) (h : q ∈ pfcFactors x.num.natAbs ∨ q ∈ pfcFactors x.den.natAbs) : List.count q (b5Support x) = 1`
  — スケッチ: `List.mem_append` の逆向きで q ∈ (++ ) → L2。

### ☐ Step 8 — Q 層

- **Q1** `b5_prod_num (x : PreRat) (hx : x.num ≠ 0) : fspProd (fun p => b5N (p ^ pvqNatVal p x.num.natAbs)) (b5Support x) = b5N x.num.natAbs`
  — スケッチ: R3 に `n := x.num.natAbs`（`1 ≤ n` は `natAbs_pos_of_ne hx`）、hpr = S2、hsub/hcnt は S1/S3 の左枝。
- **Q2** `b5_prod_den (x : PreRat) : fspProd (fun p => b5N (p ^ pvqNatVal p x.den.natAbs)) (b5Support x) = b5N x.den.natAbs`
  — スケッチ: 同上、`1 ≤ b` は `natAbs_den_pos x`、右枝。

### ☐ Step 9 — P1（pav スライス着地後・I-5 を先に調整）

- **P1** `pav_cleared (p : Nat) (hp : IsPrime p) (x : PreRat) (hx : x.num ≠ 0) : qMul (pavAbs p x) (b5N (p ^ pvqNatVal p x.num.natAbs)) = b5N (p ^ pvqNatVal p x.den.natAbs)`
  — 数学: `|x|_p = p^{v_p(b) − v_p(a)}` なので両辺は `p^{v_p(b)}`。
  — スケッチ（pav 側で export できない場合の b5 側導出）: `pvqVal p x = ↑va − ↑vb`（va := pvqNatVal p a, vb := pvqNatVal p b、定義展開）に対し `cases Int.lt_or_le (pvqVal p x) 0`：
    (i) v < 0（va < vb）: pavAbs は `b5N (p ^ (vb − va))` 系の代表 → 積の代表は `⟨↑(p^(vb−va)) * ↑(p^va), 1*1⟩` → `Quot.sound`；交差積は `Nat.pow_add`（`(vb−va)+va = vb` は omega）で閉じる。
    (ii) 0 ≤ v（vb ≤ va）: pavAbs は `1/p^(va−vb)` の代表 `⟨1, ↑(p^(va−vb))⟩` → 積 `⟨↑(p^va), ↑(p^(va−vb))⟩ ~ ⟨↑(p^vb), 1⟩`；交差積 `p^va * 1 = p^vb * p^(va−vb)` は `Nat.pow_add`（`vb+(va−vb) = va` は omega）。
    Nat↔Int の冪 cast は `Int.natCast_mul` + `Nat.pow_add` を Nat 側で済ませてから cast する（Int 側の pow を持ち込まない）。
  - **調整事項**: pavAbs の実際の場合分け（`0 ≤ v` の境界がどちらの枝か、`Int.toNat` を使うか `natAbs` か）に合わせて (i)(ii) の展開補題名を差し替える。**pav スライスが P1 そのものを export するのが最善**（I-5）。

### ☐ Step 10 — G1（p 進側 cleared form）

- **G1** `b5_padic_cleared (x : PreRat) (hx : x.num ≠ 0) : qMul (fspProd (fun p => pavAbs p x) (b5Support x)) (b5N x.num.natAbs) = b5N x.den.natAbs`
  — スケッチ: `rw [← Q1 x hx]` で `b5N a` を積に開く → `rw [← fsp_prod_mul_pointwise]`（F3 逆向き）で 1 本の積 `fspProd (fun p => qMul (pavAbs p x) (b5N (p ^ pvqNatVal p a)))` へ → F2 で各 p ∈ S に `P1 p (S2 …) x hx` を適用し `fun p => b5N (p ^ pvqNatVal p b)` へ → Q2。

### ☐ Step 11 — A1（アルキメデス側 cleared form、avi 非依存）

- **A1** `b5_arch_cleared (x : PreRat) : qMul (arpAbs (Quot.mk ratRel x)) (b5N x.den.natAbs) = b5N x.num.natAbs`
  — スケッチ: 左辺代表 = `prMul (prAbs x) (intToPreRat ↑(x.den.natAbs))` = `⟨intAbs x.num * ↑(den.natAbs), x.den * 1⟩`。`Quot.sound`：交差積 `intAbs x.num * ↑(den.natAbs) * 1 = ↑(num.natAbs) * (x.den * 1)` を N4（`intAbs = ↑natAbs`）と `↑(x.den.natAbs) = x.den`（den_pos + omega）で書換え、`Int.mul_one`・`Int.mul_comm` で一致。
  — 代替: avi の実等式 `arpAbs (mk x) = qMul (b5N a) (qInv (b5N b))` が着地していれば、それ + `qMul_inv`（rep `intToPreRat ↑b`, 分子 ≠ 0）+ 結合律で 3 行。**どちらでも良いが、A1 直接版は avi をクリティカルパスから外せる**。

### ☐ Step 12 — FINAL

- **FINAL** `b5_product_formula`（§1.2 の statement）
  — スケッチ: `A := arpAbs (Quot.mk ratRel x)`, `P := fspProd … (b5Support x)`, `α := b5N x.num.natAbs`, `β := b5N x.den.natAbs` とおく。
    1. `h1 : qMul (qMul A P) α = α` — `mul_assoc` で `qMul A (qMul P α)` へ → G1 → A1。
    2. `hinv : qMul α (qInv α) = ratRing.one` — `qMul_inv (intToPreRat ↑a)`、分子 `(↑a : Int) ≠ 0` は `natAbs_pos_of_ne hx` + omega。
    3. `qMul A P = qMul (qMul A P) (qMul α (qInv α))`（hinv + `mul_one`; `mul_one` は `mul_comm`+`one_mul`）` = qMul (qMul (qMul A P) α) (qInv α)`（`mul_assoc`）` = qMul α (qInv α)`（h1）` = ratRing.one`（hinv）。
    すべて `rw` 連鎖（ratRing.mul_assoc / mul_comm / one_mul / qMul_inv）で閉じ、新規 choice なし。

### ☐ Step 13 — （optional・phase 2）W1 台の拡大不変性

- **W1** `b5_support_ext (x : PreRat) (hx : x.num ≠ 0) (T : List Nat) (hpr : ∀ p, p ∈ T → IsPrime p) (hsub : ∀ q, q ∈ b5Support x → q ∈ T) : fspProd (fun p => pavAbs p x) T = fspProd (fun p => pavAbs p x) (b5Support x)`
  — スケッチ: `fsp_prod_extend` + 「p ∈ T \ Supp なら pavAbs p x = 1」（`pav_trivial`；p ∉ Supp → p ∤ num·den は **pfc の完全性 `IsPrime q → q ∣ n → q ∈ pfcFactors n` が必要 = interface 追加 I-6**）。FINAL には不要なので後回し。積公式の「台の取り方に依らない」頑健性 corollary として価値があるが、complete_pct への寄与は FINAL で確定するため phase 2。

### ☐ Step 14 — 親の統合作業

IUT.lean への import 追加・`tools/gen_graph.py` の PILLAR に `B5ProductFormulaQ` を B 柱で追記・`graph-meta.json` の B5 complete_note 更新（§5 の文言）・`python3 tools/gen_graph.py` 再生成・dashboard 二軸表更新。

---

## 4. 想定される詰まり所と回避策

1. **負冪 p^{−v}（v : Int）の表現**: Int 冪や「負なら逆数」の一般論を作ると qInv の乗法性・非零性管理が芋づる式に必要になる。**回避**: cleared form イディオム（§2.1）。負冪は P1 の内部（pavAbs の定義展開）にのみ現れ、そこでは `Nat.pow_add` + omega（`vb + (va−vb) = va` 等の指数演算）だけで閉じる。DAG の他の全補題は Nat 冪のみ。
2. **num 側と den 側の素数の合併と重複**: `pfcFactors a ++ pfcFactors b` は重複だらけ（同じ素数が両側に、また多重度分だけ）。**回避**: `b5Dedup` + count 管理（L1/L2）。R2 は「S nodup」全体を要求せず「L の各元 q について count q S = 1」だけを要求する形にしたので、S3 がそのまま供給できる。Nodup 帰納型を新設しない（count = 1 は omega と好相性）。
3. **重複素数（多重度）の扱い**: `pfcFactors n` は多重度つきリスト（例: 12 → [2,2,3]）。指数への組み替えは R2 の「count による regrouping」で処理する — ∏_{p∈S} p^{count p L} を L の帰納で 1 因子ずつ剥がす。多重度を先にまとめる（ソートや groupBy）必要は無い。
4. **count の BEq/Eq ずれ**: core `List.count` は `BEq` ベース（`a == b`）で、`count_cons` の if 条件も `==`。素の `rw [if_pos h]` は `h : (head == q) = true` を要求する。**回避**: R1/F4/L2 内で `Nat.beq_eq`（または `beq_iff_eq`）で Prop 等式と往復する小補題を最初に 1 本置く（`b5_beq (a b : Nat) : (a == b) = true ↔ a = b`）。core 4.30 のどの名前が生きているかは実装時に `Nat.beq_eq` → `beq_iff_eq` → 手証明（`cases`/omega は不可なので `Nat.decEq` 展開か `Nat.eq_of_beq_eq_true`）の順で当てる。
5. **スライス間の count 不一致**（pfc が独自 count の場合）: 橋渡し `b5_count_bridge` を b5 冒頭に置く（I-2）。両実装とも構造的再帰なら双方 induction + rfl/omega で 10 行以内。
6. **fspProd の畳み込み方向**: fspProd が foldl か foldr か、単位元をどちら側に掛けるかで `fsp_cons` の形が変わる。**回避**: b5 は fspProd を一切 unfold せず、I-3 の定義等式（fsp_nil/fsp_cons）と F1–F4 だけを使う。fsp スライスの実装がどちらでも、定義等式さえ export されれば b5 は無変更。
7. **pavAbs の代表形依存（P1）**: pavAbs が `Int.toNat` を使うか、境界（v = 0）をどちらの枝に入れるかで P1 の場合分けが変わる。**回避**: I-5 で pav スライスに P1 そのものの export を要求するのが第一。だめなら pavAbs の場合分け定義等式（`pav_of_nonneg`/`pav_of_neg` 相当）を要求。それも無ければ b5 で unfold（最悪ケース、pavAbs の定義変更に脆くなるため非推奨と明記）。
8. **`↑(x.den.natAbs) = x.den` の cast**（A1・P1）: den_pos から omega で閉じる（omega は `Int.natAbs`・`Int.ofNat` を読める）。`Int.natAbs_of_nonneg` が使えればそれでも可。
9. **タクティク制約（simp なし）**: if の簡約は全て `rw [if_pos h] / rw [if_neg h]`（Decidable インスタンスの一致に注意 — 定義に使った instance と証明で使う instance が同じになるよう、`if h : q ∈ …` の依存 if は避けて命題 if + `Decidable.em` 場合分けに統一する。b5Dedup の定義中の if も同様に非依存 if にする）。
10. **`arpAbs` の型が `ratIUTField.carrier`**: QRat と definitionally equal だが、`show` で明示的に型を読み替える箇所（A1・FINAL）が必要になることがある。`show qMul (qAbs (Quot.mk ratRel x)) … = …` の形で qAbs に落としてから進める（`arpAbs = qAbs` は rfl）。
11. **R2 の帰納で hsub/hcnt の受け渡し**: L の帰納は S を固定して回す（S も一緒に一般化しない）。hsub/hcnt は `fun r hr => hsub r (List.mem_cons_of_mem _ hr)` で尾へ制限。`List.mem_cons_self` / `List.mem_cons_of_mem` は core にある。

---

## 5. 正直な限定の予測（B5 台帳 0 → 0.5 に留まる理由）

実装完了時、`graph-meta.json` の B5 と実装モジュールヘッダに以下を明記する（**消去・弱化禁止**）:

1. **B5 台帳項目は「大域類体論/積公式(実)」の複合項目**であり、本成果はその**積公式側のみ**。大域類体論の本体 — 大域相互写像 Gal(K^ab/K) ≃ イデール類群の連結成分商、イデール類群 C_K の構成、局所-大域整合（局所 Artin 写像の束が大域で積 = 1 になる相互律）— は一切手つかず。積公式は相互律の「ノルム 1 条件」の可換図式の最下段にすぎない。ゆえに **0 → 0.5（積公式(実)完了・類体論本体未着手）**が正直な上限。
2. **K = ℚ のみ**: 一般数体 K の積公式（∏_v |x|_v^{[K_v:ℚ_v]} = 1、正規化冪込み）ではない。実素点 1 個・複素素点なし・分岐なしの最易ケース。
3. **非零性は代表 witness 形**（`x : PreRat`, `x.num ≠ 0`）: QRat 全域のゼロ判定選言は排中律を要するため、ℚ^× の choice なし忠実版として代表上で述べる（pvqVal・qMul_inv と同じ既存の正直申告を継承）。
4. **有限台は明示リスト**: 「ほとんど全ての v で |x|_v = 1、無限積が収束」という places 全体にわたる積の形式化ではなく、`b5Support x`（num·den の素因子）上の有限リスト積 + （W1 実装時）台の拡大不変性、という有限的定式化。places の型（全素点の型としての束）は未構成。
5. **値は ℚ 内**: |·|_∞ も |·|_p も ℚ≥0 値（ℝ 未構成のため）。積公式は等式なので ℚ 内で完結し損失はないが、log を取った次数式（deg = Σ log|·| = 0、Arakelov 次数との接続）へは進めない。

以上の限定は「Lean 定義そのものの地図」としてヘッダに転記し、完了報告では complete_pct への寄与を「B5: 0 → 0.5（積公式(実)、ℚ・witness 形・有限台）」と表記する。
