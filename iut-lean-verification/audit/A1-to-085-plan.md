# A1 0.80→0.85 詳細設計 — 全域 inv 付き実体 ℚ[x]/(f) と {1,α,…,α^{n−1}} 基底・次数理論

作成: 2026-07-09（詳細化ラウンド・tier L）。実装コードなし（本書は設計のみ・次段 opus が実装）。

- **分類**: [実] の詳細設計。目標は前回 A1 監査（`audit/reaudit-A-genf-2026-07-09.md`）が 0.85 の残欠として名指しした
  (ii) **全域 inv 付き体（∃形でない）** と (iii) **{1,α,…,α^{n−1}} 基底・次数 = [K:ℚ] 理論** の両方を、
  実 ℚ[x]/(f)（一般既約 f・`gefField` 系）上で本物に建てる道の分解。
- **complete_pct 影響**: 実装完了＋独立再監査で A1 0.80→0.85 を狙う（監査自身の 0.85 条件
  「全域 inv 付き IUTField インスタンス＋{1,α,…}基底・次数=[K:ℚ] 理論」と一致）。
  丸め上 A1=0.85 で柱 A 36.4→36.8 → **37**（柱%前進）。最終判定は独立監査。

---

## 0. 設計の核心判断（最初に結論）

### 0.1 構成性の判定結果（(A) の前提精査）

| 既存部品 | witness | 判定 |
|---|---|---|
| `field_division_exists`（M268F-5） | q, r を N 帰納の各段で明示構成 | **Σ'化可能**（分岐なし・Nat 構造再帰のみ。関数 `def` に書き直せる） |
| `pgbExtGcdAuxB` / `pgbBezoutQ`（PGB-3/5） | s,t,gg を fuel 帰納で明示構成 | **Σ'化可能・ただし分岐が問題**: 各段の分岐が `hlead_oracle` の **Prop 値 Or**（`plo_lead_oracle_Q` は `Quot.ind`＋`Decidable.em` で Prop 専用）。Type 値関数にするには **Bool 値の零判定**（下記 F1）への置換が必要 |
| `plo_lead_oracle_Q`（PLO-1） | `Decidable.em (r.num = 0)` | Prop Or のまま。**Bool 版 `qIsZero := Quot.lift (fun r => r.num == 0) …` が choice-free に定義可能**（`qInv` が既に同型の `Quot.lift` 前例。respects 証明は `den_pos` から即） |
| `gef_bezout` / `quotField_of_bezout` | ∃ u v（Prop） | 上流を Σ'化すれば同構成を関数化できる |

**結論 1**: 拡張ユークリッド全体は「∃ 定理の写経」で **choice-free な Type 値関数**（除法関数・Euclid 関数）に昇格できる。
唯一の新規部品は Bool 零判定 `qIsZero`（Quot.lift・実 ℚ 固有・choice 不要）。

### 0.2 ただし「既存 Quot 担体上の全域 inv」は choice なしでは不可能（正直申告・消さない）

`(gefField f nf …).ring.carrier = Quot (idealRel (polyCRing ratRing) f̂)` 上の全域関数
`inv : carrier → carrier` は、`Quot.lift` により **`Poly ratRing → Poly ratRing` の関数**を経由するしかない。ところが

1. `Poly R = {g : PS R // IsPoly R g}`、`IsPoly R g = ∃ N, IsPolyBounded R g N` — 次数上界は **Prop の ∃** に隠れている。
2. 除法・Euclid の実行には代表 g の**数値上界 N（fuel）**が必要（頂点消去は上から降りる）。Prop ∃ から Type への witness 抽出は choice。
3. `Nat.find`/`Acc.rec` 型の choice-free 救済も不可: 述語 `IsPolyBounded g N` は **∀i≥N の無限全称で決定不能**（探索の停止判定ができない）。
4. 本質的にも、inv([g]) の各係数は g の**非有界個の係数**に依存し、上界データなしのアルゴリズムは存在しない。

よって **「gef_bezout の u,v の inv:=[v] 関数化」は Quot 担体の上では choice なしで不成立**。∃ 形（`has_inverses`）は
この担体の正直な限界であり、M269F の正直申告は正しい。**これを消さずに**、次の 0.3 で本物の解決を与える。

### 0.3 解決: 正規形（normal form; NF）担体 — 上界を「固定パラメータ」にして ∃ を消す

ブロッカーは「∃N」のみ。ならば **次数 < nf の剰余代表**を担体にすればよい:

```
GefNF (f nf …) := { g : PS ratRing // IsPolyBounded ratRing g nf }
```

- 上界 nf は**型のパラメータ（データ）**であり全要素で一様 → 関数定義に抽出問題が発生しない。
- 剰余の一意性（`field_division_unique`・M268F-7）により、商 ℚ[x]/(f) の各類はちょうど 1 つの NF 代表を持つ
  → `GefNF → (gefField …).ring.carrier`（`Quot.mk`）は**単射環準同型**、かつ ∃ 形で全射（除法定理）。
- NF 担体上では加法は各点、**乗法は「掛けて f で割った剰余」**（除法**関数** F3 使用）、**inv は Euclid 関数 F4** — 全て全域関数。
- これは計算機代数の標準表現（ℚ(∛2) を 3 組 (a,b,c) で持つのと同じ）であり、代理でも模型でもなく
  **実 ℚ[x]/(f) の忠実な第二表示**。既存 Quot 表示とは同型対（F7）で結ぶ。

**設計方針**: (A) 全域 inv 付き `gefNFIUTField : IUTField` / `gefNF268 : Field268` を NF 担体上に建て、
Quot 表示との同型（単射準同型＋∃全射）を本物に証明する。(B) 基底・次数理論も NF 担体を主語にする
（座標写像 `repr x i := x.val i` が**リフト不要の直接関数**になり、TowerLawBasis の全フィールドが埋まる）。
Quot 表示側には span・一次独立の **Prop 形の系**を同型経由で出す（そこで初めて課題文の
「f∣p ∧ deg p<n ⟹ p=0」論法＝`poly_mul_g_bounded_zero268` が使われる）。

---

## 1. (A) 全域 inv 付き体の道 — モジュール分解と型スケッチ

### F1 `IUT/PolyLeadFindQ.lean` — Bool 零判定と先頭係数探索関数（Type 値）

```lean
-- (a) Bool 零判定（qInv と同じ Quot.lift イディオム・choice-free）
def qIsZero : QRat → Bool :=
  Quot.lift (fun r => r.num == 0)
    (fun r s h => …)   -- ratRel r s ∧ r.num=0 → s.num=0（s.den_pos>0、逆も対称）→ beq 一致
theorem qIsZero_iff (x : QRat) : qIsZero x = true ↔ x = ratRing.zero
  -- Quot.ind + rzd_eq_zero_iff（N2-3）へ帰着

-- (b) 先頭係数探索（plo_lead_oracle_Q の Type 値版・上から下への有限走査）
def ploFind (p : PS ratRing) : Nat → Option Nat
  | 0 => none
  | m+1 => if qIsZero (p m) then ploFind p m else some m
theorem ploFind_none (p n) (hb : IsPolyBounded ratRing p n)
    (h : ploFind p n = none) : ∀ i, p i = ratRing.zero      -- n 帰納・qIsZero_iff
theorem ploFind_some (p n) (hb : IsPolyBounded ratRing p n) {d}
    (h : ploFind p n = some d) : p d ≠ ratRing.zero ∧ IsPolyBounded ratRing p (d+1)
theorem ploFind_zero (n) : ploFind (psZero ratRing) n = none  -- inv_zero 用
```
一行スケッチ: respects は交差積 `r.num * s.den = s.num * r.den` と `den_pos` の omega。走査は
`plo_lead_oracle_Q` の証明と同じ n 帰納を `if` 分岐（Bool・Type 値可）で書き直すだけ。

### F3 `IUT/PolyDivModFn.lean` — 除法関数（`field_division_exists` の写経Σ'化）と剰余の特徴付け

```lean
-- (a) 除法関数（M268F-5 の witness をそのまま def に）
def pfdDivMod (g : PS ratRing) (m : Nat) : Nat → PS ratRing → PS ratRing × PS ratRing
  | 0,     w => (psZero ratRing, w)
  | N+1, w =>
      let c := ratRing.mul (w (N+m)) (qInv (g m))
      let w' := psAdd _ w (psNeg _ (psMul _ (psSingle _ c N) g))
      let (q', r') := pfdDivMod g m N w'
      (psAdd _ q' (psSingle _ c N), r')
-- (b) 仕様（M268F-5 と同一命題・同一帰納で証明）
theorem pfdDivMod_spec (g m hg hlead) : ∀ N w, IsPolyBounded _ w (N+m) →
    IsPolyBounded _ (pfdDivMod g m N w).1 (N+1) ∧
    IsPolyBounded _ (pfdDivMod g m N w).2 m ∧
    ∀ j, w j = psAdd _ (psMul _ (pfdDivMod g m N w).1 g) (pfdDivMod g m N w).2 j
-- (c) 剰余（f mod 用の略記; f 側は nf 固定なので fuel は静的に取れる）
def pfdRed (f nf) (N : Nat) (w : PS ratRing) : PS ratRing := (pfdDivMod f nf N w).2
-- (d) **剰余の特徴付け（NF 環法則の共通エンジン・本設計の要）**:
--     w ≡ v (mod f, 余因子 IsPoly) ∧ v が nf 有界 ⟹ pfdRed w = v
theorem pfdRed_char (f nf hb hl) (N w v)
    (hw : IsPolyBounded _ w (N + nf)) (hv : IsPolyBounded _ v nf)
    (hcong : ∃ h, IsPoly ratRing h ∧ ∀ j, psAdd _ w (psNeg _ v) j = psMul _ h f j) :
    ∀ j, pfdRed f nf N w j = v j
  -- spec の w = q·f + r と hcong から r − v = (h−q)·f、r−v は nf 有界、
  -- poly_mul_g_bounded_zero268 で h−q = 0 ⟹ r = v（M268F-7 と同じ論法）
theorem pfdRed_of_bounded : IsPolyBounded _ w nf → pfdRed f nf N w = w   -- char の v:=w 特例
```
注意: (d) の hcong 内の IsPoly は Prop ∃ でよい（結論が Prop なので中で obtain 可）。
**(d) 一本が one_mul / mul_assoc / distrib / inv_cancel を全部駆動する**（§F5）。

### F4 `IUT/PolyEuclidFn.lean` — 拡張ユークリッド関数（`pgbExtGcdAuxB` の写経Σ'化）

**設計上の要点（詰まりやすい点を先回り）**: 出力の s, t は後段で `pfdRed` にかける（inv を nf 有界へ落とす）ため
fuel が要る。よって **数値上界 Ns, Nt をデータとして一緒に返す**（PGB-3 が Prop で持ち回る IsPoly を数値化して返すだけ。
bound の合成は `Na+1`（商）と `+`・`max` の Nat 算術）。

```lean
structure PefOut where
  s t gg : PS ratRing
  mg Ns Nt : Nat
def pefGcd (f g : PS ratRing) :
    Nat →  -- fuel
    PS ratRing → PS ratRing →              -- a b
    PS ratRing → PS ratRing → PS ratRing → PS ratRing →  -- sa ta sb tb
    Nat → Nat → Nat → Nat → Nat → Nat →    -- Na mb Nsa Nta Nsb Ntb（全部データ）
    PefOut
  | 0, _, b, _, _, sb, tb, _, mb, _, _, Nsb, Ntb => ⟨sb, tb, b, mb, Nsb, Ntb⟩  -- 到達しないダミー
  | fuel+1, a, b, sa, ta, sb, tb, Na, mb, Nsa, Nta, Nsb, Ntb =>
      let (q, r) := pfdDivMod b mb Na a
      match ploFind r mb with
      | none    => ⟨sb, tb, b, mb, Nsb, Ntb⟩
      | some dr => pefGcd f g fuel b r sb tb
          (psAdd _ sa (psNeg _ (psMul _ q sb))) (psAdd _ ta (psNeg _ (psMul _ q tb)))
          (mb+1) dr Nsb Ntb (Nsa + (Na+1) + Nsb) (Nta + (Na+1) + Ntb)
theorem pefGcd_spec … :   -- PGB-3 の結論そのもの（∃ を pefGcd の射影に置換した形）
    (out.gg) = psAdd _ (psMul _ out.s f) (psMul _ out.t g) ∧
    IsPolyBounded _ out.gg (out.mg+1) ∧ out.gg out.mg ≠ ratRing.zero ∧
    pdbDvd ratRing out.gg a ∧ pdbDvd ratRing out.gg b ∧
    IsPolyBounded _ out.s out.Ns ∧ IsPolyBounded _ out.t out.Nt
  -- fuel 帰納・pgbExtGcdAuxB の証明本文を pfdDivMod_spec / ploFind_none / ploFind_some で写経
def pefBezout (f a : PS ratRing) (Nf Na mb : Nat) : PefOut :=
  pefGcd f a (mb+1) f a (psOne _) (psZero _) (psZero _) (psOne _) Nf mb 1 0 0 1
theorem pefBezout_spec …  -- PGB-4 対応（初期係数 1,0,0,1・fuel = mb+1）
```
一行スケッチ: 関数本体は PGB-3 の各段 witness の転記。spec は同じ fuel 帰納（fuel=0 は `mb < fuel` 前提で vacuous、
ダミー枝は仕様対象外）。**割り切れの余因子上界も返す必要はない**（pdbDvd の ∃ で足りる——後段で Prop 使用のみ）。

### F5 `IUT/GenExtFieldNF.lean` — NF 担体の可換環（乗法 = 掛けて簡約）

パラメータは GEF と同一: `(f : PS ratRing) (nf : Nat) (hb : IsPolyBounded _ f (nf+1)) (hl : f nf ≠ 0)
(hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f)`（環までは hirr 不要）。

```lean
def GefNF := { g : PS ratRing // IsPolyBounded ratRing g nf }
def gefNFRing … : CRing where
  carrier := GefNF …
  add  a b := ⟨psAdd _ a.val b.val, 各点⟩         -- (a+b) j = 0+0（simpleExt_add_bounded は 2nf で過大・直接各点）
  neg  a   := ⟨psNeg _ a.val, 各点⟩
  zero := ⟨psZero _, …⟩ ; one := ⟨psOne _, hn から⟩
  mul  a b := ⟨pfdRed f nf nf (psMul _ a.val b.val),   -- 積は 2nf=nf+nf 有界 → fuel N:=nf で spec 発火
              (pfdDivMod_spec …).2.1⟩
  加法系法則 := Subtype.ext ∘ psRing 降下（polyCRing と同型のボイラープレート）
  mul_comm := congrArg pfdRed ∘ psMul 可換
  one_mul  := pfdRed_of_bounded（1·a = a は nf 有界）
  mul_assoc / left_distrib := pfdRed_char で「両辺 ≡ a·b·c（resp. ab+ac）mod f・両辺 nf 有界」
    -- 例 assoc: red(red(ab)·c) − abc = (−q₁·c)·f（q₁ は ab の商・IsPoly）、
    --          red(a·red(bc)) − abc = (−a·q₂)·f。両者を pfdRed_char で同じ v に落とすか、
    --          直接 red(red(ab)·c) = red(abc) = red(a·red(bc)) の 2 段（char を w:=red(ab)·c, v:=red(abc) 形で）
def gefNF_zero_ne_one : … one ≠ zero   -- 係数 0 で 1 ≠ 0（rzd_ne_zero_of_num_ne）
```

### F6 `IUT/GenExtFieldInv.lean` — 全域 inv と体インスタンス（(A) の頂点）

```lean
def gefNFInv … (x : GefNF …) : GefNF … :=
  match ploFind x.val nf with
  | none   => zero                          -- 規約 inv 0 = 0
  | some d =>
      let o := pefBezout f x.val (nf+1) (d+1) d   -- gg = s·f + t·x
      -- gg は単元（§下記 Prop 側で保証）だが関数側は無条件に正規化して返す:
      ⟨pfdRed f nf o.Nt (psMul _ (psC _ (qInv (o.gg o.mg))) o.t), …⟩
      -- gg 単元時 gg o.mg = 定数 c。非単元枝は spec 対象外（x≠0 では起こらない）
theorem gefNF_mul_inv_cancel … : ∀ x, x ≠ zero → mul x (gefNFInv x) = one
  -- (i) x ≠ 0 ⟹ ploFind = some d（ploFind_none の対偶）
  -- (ii) f ∤ x.val: f∣x なら pdb_dvd_deg_le で nf ≤ d、だが d < nf（x nf 有界・x d ≠ 0）で矛盾
  -- (iii) pefBezout_spec + pib_gcd_unit_of_not_dvd + pib_unit_eq_psC ⟹ gg = psC c, c ≠ 0
  --       （このとき o.mg = 0 かつ gg o.mg = c: gg mg ≠ 0・gg = psC c から mg=0 を強制）
  -- (iv) GEF-2(v) と同じ単元正規化 inline（pbz_scale_comb・psConstHom.map_mul・mul_inv_cancel）で
  --       (c⁻¹s)·f + (c⁻¹t)·x = 1 ⟹ x·(c⁻¹t) − 1 = (−c⁻¹s)·f
  -- (v) mul x (inv x) = red(x·red(c⁻¹t)) = red(x·c⁻¹t) = 1 —— pfdRed_char 2 発（≡ 伝播と v:=psOne・hn）
theorem gefNF_inv_zero … : gefNFInv zero = zero        -- ploFind_zero
def gefNFIUTField … : IUTField := { toCRing := gefNFRing …, inv := gefNFInv …,
  mul_inv_cancel := gefNF_mul_inv_cancel …, inv_zero := …, zero_ne_one := (gefNF_zero_ne_one …).symm ∘ … }
def gefNF268 … : Field268 := ⟨(gefNFIUTField …).toCRing, gefNFInv …, gefNF_mul_inv_cancel …⟩
```
`gefNF268 : Field268` は **課題文の `gefField268` に相当**（Field268 = ring+invf+mul_inv_cancel の雛形を充填）。
さらに強い `IUTField` まで届く（inv_zero・zero_ne_one 込み）。

### F7 `IUT/GenExtFieldIso.lean` — Quot 表示との同型（NF が「同じ体」であることの本物の証明）

```lean
def gefNFtoQuot … : RingHom (gefNFRing …) (gefField f nf hb hl hn hirr).ring where
  map x := Quot.mk _ ⟨x.val, ⟨nf, x.property⟩⟩
  map_add := rfl 系（quotOf と同じ） ; map_one := rfl
  map_mul := Quot.sound ⟨q̂, …⟩   -- red(xy) − xy = (−q)·f、q は pfdDivMod_spec の商を Poly 化
theorem gefNFtoQuot_injective …   -- [x]=[y] → quot_exact_ideal → x−y = w·f（w Poly）
  -- → x−y は nf 有界 → poly_mul_g_bounded_zero268 で w=0 → x=y（Subtype.ext+funext）
theorem gefNFtoQuot_surjective_ex … : ∀ z, ∃ x : GefNF …, gefNFtoQuot.map x = z
  -- Quot.ind で代表 a、a.property の ∃N を obtain（Prop 内なので可）、
  -- field_division_exists で a = q·f + r、[a]=[r]（Quot.sound ⟨q⟩）、x := ⟨r, hr⟩
theorem gefField_has_total_inv_upto_iso …   -- 見出し: Quot 表示の体は全域 inv 付き体と単射+∃全射同型
```
∃全射は Prop なので choice 不要。**逆向きの関数（切断）を作らないのが choice 回避の要**（0.2 の非存在と整合）。

---

## 2. (B) 基底・次数理論の道 — {1, α, …, α^{n−1}} は ℚ-基底・[K:ℚ] = n = deg f

### F8 `IUT/GenExtBasisMonomial.lean` — ℚ-加群構造と単項式基底（NF 担体・環乗法に非依存 → 早期並列可）

smul は `psC c` との積のみで簡約不要（`psMul_single_coeff268` の k=0 で `(psC c · g) j = c·g_j`、nf 有界保存）。
**F5 の環に依存しない**ので Wave 1 から並列実装できる。

```lean
def gefNFModule … : TowerLawModule ratIUTField where
  carrier := GefNF … ; add/zero/neg := F5 と同じ各点演算（または自前再掲・親が統合時に一本化）
  smul c x := ⟨psMul _ (psC _ c) x.val, psMul_single_coeff268 系で nf 有界⟩
  加群公理 := psC 環準同型（psConstHom）＋ psRing 法則から routine
def gefNFMon … (i : Fin nf) : GefNF … := ⟨psSingle _ ratRing.one i.val, i.isLt から⟩
-- 核: 係数読み出し補題（span と indep の両方を一撃で出す）
theorem gefNF_sum_coeff … (c : Fin nf → QRat) (j : Nat) :
    (towerLawSum (gefNFModule …) nf (fun i => smul (c i) (gefNFMon i))).val j
      = if h : j < nf then c ⟨j, h⟩ else ratRing.zero
  -- nf 帰納 + psMul_single_coeff268（psC·single の係数 = 対角）+ rsum 簿記
def gefNFMonBasis … : TowerLawBasis ratIUTField (gefNFModule …) where
  dim := nf ; vec := gefNFMon … ;
  repr x i := x.val i.val                   -- ★ リフト不要の直接関数（NF 設計の配当）
  spans x := Subtype.ext (funext (fun j => gefNF_sum_coeff の場合分け ∘ x.property))
  indep c h i := gefNF_sum_coeff … と h の j:=i.val 係数比較
```

### F9 `IUT/GenExtBasisAlpha.lean` — α = [x] の冪 = 単項式、{1,α,…} 基底・次数・TowerLaw 接続

```lean
def gefAlpha … : GefNF … := ⟨pfdRed f nf 1 (psSingle _ ratRing.one 1), …⟩  -- [x]（nf=1 でも定義可）
def gefNFPow … : GefNF … → Nat → GefNF …    -- x^0 = one, x^(k+1) = mul (x^k) x（gefNFRing の冪）
theorem gefAlpha_pow_eq_mon … (i : Fin nf) : gefNFPow (gefAlpha …) i.val = gefNFMon i
  -- i 帰納: i=0 は one = single 1 0（funext）; i+1 < nf なら
  --   red(X)=X（nf≥2 のとき pfdRed_of_bounded; nf=1 は base case のみ）、
  --   single·single = single(i+1)（psMul_single_coeff268）、i+1<nf 有界なので red = id（pfdRed_of_bounded）
def gefPowBasis … : TowerLawBasis ratIUTField (gefNFModule …)
  -- vec i := gefNFPow (gefAlpha …) i.val に gefAlpha_pow_eq_mon で gefNFMonBasis を書き換えて構成
  -- ★ これが監査文言どおりの主語 {1, α, …, α^{n−1}}
theorem gef_degree_eq … : towerLawDegree (gefPowBasis f nf …) = nf   -- 定義展開（[K:ℚ] = n = deg f）
-- TowerLaw への流し込み（塔の 1 段目として再利用可能に）
def gefFieldExtension … : FieldExtension :=
  { base := ratIUTField, top := gefNFIUTField …,
    incl := fun c => ⟨psC _ c, …⟩,
    incl_add/mul/one := psConstHom + 「定数×定数は nf 未満なので red = id」（pfdRed_of_bounded） }
def gefBasisLK … : TowerLawBasis ratIUTField
    (towerLawRestrict (gefFieldExtension …) (towerLawRegModule (gefNFIUTField …)))
  -- 制限正則加群の smul c x = NF乗法(incl c, x) = red(psC c·x) = psC c·x（積は nf 有界・red=id）
  -- ⟹ gefNFModule の smul と全点一致 → gefPowBasis を書き換えで移送
-- これで TowerData の basisLK スロット（M281F-6a）に実既約 f の実基底が入る（塔法則の実入力・A3 用）
```

### Quot 表示側への系（監査ナラティブ用・Prop 形）

`GenExtFieldIso`（F7）の単射性の証明の中身が、課題文がスケッチした一次独立論法そのもの:
**Σcᵢαⁱ = 0（商で）⟹ 対応する多項式（deg<n）∈(f) ⟹ `quot_exact_ideal` で = w·f ⟹
`poly_mul_g_bounded_zero268`（deg<n・f の先頭 ≠ 0）で w=0 ⟹ 零多項式 ⟹ 全 cᵢ=0**。
F9 の末尾に Prop 形の系 2 本を置く（関数 repr は作らない・0.2 の限界に従う）:
`gefQuot_spans_ex : ∀ z, ∃ c : Fin nf → QRat, z = Σᵢ [cᵢ]·[x]^i` と
`gefQuot_indep : Σᵢ [cᵢ]·[x]^i = 0 → ∀ i, cᵢ = 0`（前者は除法 ∃・後者は上記論法。同型移送でも直接でも可）。

---

## 3. 実装 DAG（順序・並列・tier 割当）

```
Wave 1（3 並列・全部 opus=M）
  F1  PolyLeadFindQ      qIsZero + ploFind + spec        依存: Rationals/RatZeroDecide
  F3  PolyDivModFn       pfdDivMod + spec + pfdRed_char  依存: PolyFieldDivision
  F8  GenExtBasisMonomial 加群 + 単項式基底              依存: TowerLaw/Field/PolyFieldDivision（F5 非依存!）
Wave 2（2 並列）
  F4  PolyEuclidFn       pefGcd/pefBezout + spec         依存: F1, F3     [opus=M・★fable HELP 第1候補]
  F5  GenExtFieldNF      NF 可換環（red 乗法）           依存: F3         [opus=M・★fable HELP 第2候補]
Wave 3（3 並列・全部 opus=M）
  F6  GenExtFieldInv     inv + IUTField/Field268         依存: F4, F5, pib（既存）
  F7  GenExtFieldIso     Quot 同型 + ∃全射               依存: F5（+ 既存 GenExtField）
  F9  GenExtBasisAlpha   α冪基底 + 次数 + TowerLaw 接続  依存: F5, F8（gefBasisLK のみ F6 待ち→後述）
Wave 4（1-2 本）
  F10 GenExtFieldTotal   capstone（新規証明ゼロの束ね: 「∀既約f, 全域inv付き実体+基底+次数」+
                          x³−2/Φ₃ の 2 実例を NF で再輸出）                 [sonnet=S]
  親  IUT.lean/build.sh/dashboard/graph-meta 統合・gen_graph 再生成・独立 A 再監査発注
```

- **fable の使い所（本詳細化で先回り済み・実装は全部 opus 可の見込み）**:
  - F4: Type 値 fuel 再帰＋依存 spec の写経で `match` の等式論証（`match h : ploFind …`）に詰まったら fable。
    設計上の罠（s,t の数値上界をデータで返す・fuel=0 ダミー枝は spec 対象外）は本書で解消済み。
  - F5: `mul_assoc` の pfdRed_char 2 段適用（≡ の余因子簿記）に詰まったら fable。char の v を
    `red(abc)`（fuel 2nf... 正確には N:=2nf で abc は 3nf=2nf+nf 有界）に取り両辺から挟むのが推奨経路。
- 依存注意: F9 の `gefBasisLK` だけ `gefNFIUTField`（F6）を参照する。F9 実装は「基底本体（F5+F8 のみ依存）→
  gefBasisLK（F6 完了後に追記 or Wave 4 へ回す）」の 2 段に切ってよい。
- 全モジュール共通規約: sorry 皆無・新規 Classical.choice 皆無（`#print axioms` = propext, Quot.sound のみ）・
  禁止タクティク不使用・新規ファイルのみ（共有ファイルは親が統合）・ヘッダに [実]／complete_pct 影響を明記。

---

## 4. 正直な限定の予測（0.85 に届くか・保守的に）

**届く見込みの根拠**: 前回監査が自ら書いた 0.85 条件は
「全域 inv 付き IUTField インスタンス（∃→Σ' 構成的リファクタ）＋{1,α,…}基底・次数=[K:ℚ] 理論」。
本設計はその両方を一般既約 f で、choice-free・実 ℚ[x]/(f) 上に建てる（F6 の `gefNFIUTField` と F9 の
`gefPowBasis`/`gef_degree_eq`）。

**保守的リスク（監査が値切り得る点・先に正直申告する）**:
1. **担体の差**: 全域 inv は NF 表示上であり、既存 Quot 表示の `has_inverses` は ∃ 形のまま
   （0.2 の choice-free 非存在による。消さない・弱めない）。緩和: F7 の単射準同型＋∃全射で
   「同じ体の第二表示」であることを本物に証明し、非存在理由（0.2）を実装ヘッダにも明記する。
   監査が「Quot 担体そのものの全域 inv」を要求するなら choice なしでは満点不可能であり、
   その場合も本設計が choice-free の到達上限である。
2. **次数の well-defined 性**: `towerLawDegree` は基底 witness 依存（M281F の honest 仮説 1 と同じ）。
   「任意の 2 基底が同じ要素数」（次元の一意性）は未証明のまま残る。
3. 0.85 でも 1 に届かない理由（残る本物の欠落・§4 準拠で列挙）:
   一般既約性判定（Eisenstein 等）なし＝f ごと手証明のまま／基礎体は ℚ 固定＝塔の反復
   （K[x]/(f) を新基礎体に）は未実装（ただし §5 のとおり本設計が鍵を外す）／Galois 群・共役・分離性は
   この上に未接続／∃全射（F7）は関数切断でない。
4. **最終判定は独立監査**。本書の 0.85 は目標値であり、実装完了後に独立 A 再監査
   （`reaudit-A-*` 系・#print axioms 検証込み）を発注して確定する。丸め: A1=0.85 なら
   柱 A = 36.4+0.4 = 36.8 → 表示 37（A1=0.82 が閾値・0.85 はそれを超える）。

---

## 5. A3（円分塔）への波及 — 再利用資産か？ → **鍵そのもの**

- **全域 inv（Field268 化）**: 塔の次段 K[x]/(g)（K = ℚ[x]/(f)）を建てるには K が `Field268`
  （除法定理・Euclid の入力）である必要がある。`gefNF268` がまさにそれ。さらに拡張ユークリッドの
  停止に要る `hlead_oracle`（係数の零判定）は、NF 担体では **`qIsZero` の nf 回走査で決定可能**
  （Quot 担体では不可能だった）——つまり NF 設計は A3 の塔反復の最大ブロッカー
  （「基礎体の零判定」）を同時に外す。F1 の一般化（`Field268`+Bool 零判定を持つ体のクラス）は
  A3 詳細化ラウンドの入口タスク。
- **基底・次数**: `gefBasisLK`（F9）は TowerData の `basisLK` スロット（M281F-6a）に直接刺さる形で
  設計してあり、円分塔の各段 [K_{n+1}:K_n] と塔法則 [M:ℚ]=Π の実入力になる。各段で同じ
  {1,α,…,α^{deg−1}} 基底構成（F8/F9 のイディオム）を再利用する。

---

## 6. 返り値要約（親向け）

- 成果物: 本書 `audit/A1-to-085-plan.md` 1 個のみ（コード・共有ファイル不変更）。
- (A) は「Quot 担体では choice なしで全域 inv 不可能（∃N が Prop・IsPolyBounded 非決定）」を確定させた上で、
  正規形担体 `{g // IsPolyBounded g nf}` への表示替え＋除法/Euclid の Σ'写経（F1→F3→F4→F5→F6）で
  choice-free の全域 inv `gefNFIUTField : IUTField` / `gefNF268 : Field268` に到達する。
- (B) は NF 担体上で repr がリフト不要の直接関数になり、`gefNF_sum_coeff` 一本から
  TowerLawBasis（{1,α,…,α^{n−1}}・dim = nf = deg f）が閉じる（F8→F9）。Quot 側は Prop 形の系。
- 実装は 4 Wave・opus 7 本 + sonnet 1 本、fable は F4/F5 の詰まり解決のみ。
