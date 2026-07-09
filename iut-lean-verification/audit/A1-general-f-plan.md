# A1 一般既約 f 設計書 — ℚ[x]/(f) を一般の既約多項式 f で実体化する

日付: 2026-07-09 ／ 種別: **設計ドキュメントのみ**（実装は次ラウンド・コード無し）
分類: **[実／昇格(a) の設計]** — A1 台帳（現 0.7・正直な限定「単一 f = x³−2 のみ」）
の頭打ちを破る一般 f エンジンの詳細設計。同時に A3 実 Galois 塔
（ℚ(ζ_{p^n}) 等の円分体）の**前提供給エンジン**（法多項式＋既約性 → 実体）を用意する。
**complete_pct 影響: 本ドキュメント自体は 0（設計のみ）**。実装完遂時に A1 の
「単一 f」限定が「一般 f（既約性は仮説）」へ昇格し、新規の具体 f（Φ₃ 等）を
1 個でも実証すれば A1 0.7→0.8 級（§6、保守的見積り）。

前提とした既存 API（全て read 済み・本物）:
`IUT/PolyBezoutQ.lean`（pbzBezout / pbzBezout_one_of_unit / pbzDvd / pbzRatField）、
`IUT/RatZeroDecide.lean`（rzd_zero_or_ne）、
`IUT/SimpleExtension.lean`（SimpleExtData / .build / quotField_of_bezout / idealRel /
simpleExtModulus / IsPoly / IsPolyBounded / simpleExt_add/neg/mul_bounded）、
`IUT/CbrtBezoutChain.lean`（単一 f=x³−2 の完成例 cbc_bezout・cbc_idealRel_zero_iff）、
`IUT/PolyFieldDivision.lean`（field_division_exists / psMul_g_top_coeff268 /
mul_eq_zero_left268 / poly_mul_g_bounded_zero268）、
`IUT/PolyPSUtil.lean`（ppu_bound_drop / ppu_const_eq_psC / ppu_poly_ext /
ppu_psZero_of_coeffs / ppu_bounded_mono）、`IUT/CbrtBezB.lean`（cbz_descend の簿記手本）。

---

## 0. 設計を規定する重要発見 — `pbzDvd` は冪級数的整除であり degree 論法に使えない

`pbzDvd R d a := ∃ c : PS R, a = psMul R c d`（M270F-3）の cofactor c は
**無界の冪級数**でよい。これは K[X] の整除ではなく K[[X]] の整除である。
反例（実 ℚ で成立）: w := 全係数 1 の列、g := X − 1（g 0 = −1, g 1 = 1）とすると

  (psMul w g) 0 = w₀·g₀ = −1、 (psMul w g) j = w_{j−1}·1 + w_j·(−1) = 0 (j ≥ 1)

ゆえに psMul w g = psC (−1)、つまり **pbzDvd (X−1) (−1)**（さらに −1 倍して
「X−1 が 1 を割る」）が PS ℚ で成立する。一般に f 0 ≠ 0 なら f は K[[X]] の
単元であり、pbzDvd の意味ではほぼ全てを割る。従って:

- **「gg ∣ f ⟹ deg gg ≤ deg f」は pbzDvd では偽**。次数論法・既約性論法には
  **cofactor の有界性（IsPoly）を明示した整除** `pdvDvd`（§2）が必須。
- `pbzBezout`（M270F-6）の結論の `pbzDvd R gg f ∧ pbzDvd R gg a` は情報を
  落としている。再帰の実際の cofactor は各段 `pbz_dvd_comb` で q·cb + cr と
  更新され**常に有界**（q は除法から有界・cb,cr は帰納法）だが、∃ に畳んだ
  時点で有界性は回収不能（同じ整除事実が有界 cofactor では偽になり得るため
  事後修復も不可能）。ゆえに **有界性を conclusions に持つ強化クローン
  `pgbExtGcdAuxB` / `pgbBezoutB`（§3.1）が必要**。既存 `pbzExtGcdAux` の
  再帰構造はそのまま写経し、有界性の伝播だけを各段に足す（CBC の `cbzBezB` が
  u,v の有界性を追跡したのと同じ精神。CBC はこの罠を `¬∃q, IsPoly q ∧ …` の
  形で既に回避済み——本設計はその一般化）。
- 既存 `PolyBezoutQ.lean` は**変更しない**（共有・完成済み）。強化版は新規
  ファイルに置き、既存の部品補題（pbz_comb_sub / pbz_dvd_comb /
  pbz_scale_comb / pbzDivStep）はそのまま import して再利用する。

もう 1 点の方針: 本エンジンは **ℚ 専用にせず一般 `Field268` K ＋係数零判定
オラクル hdec** で建てる（追加コストほぼゼロ）。ℚ は `rzd_zero_or_ne` で hdec を
討って具体化する。これにより A3 の**塔**（前段の商体を新たな基礎体にする相対拡大）
への道が開く（§6）。なお `pbzRatField.ring = ratIUTField.toCRing` と `ratRing` の
defeq は CBC が既に併用している確立事実（`ct0Field := pbzRatField` と
`Poly ratRing` の混用が rfl で通っている）。

---

## 1. hlead_oracle の ℚ 充填 — `plo_lead_oracle_Q`

`pbzBezout` / `pbzBezoutQ` に残る唯一の honest 仮説 `hlead_oracle` を本物にする。
一般形（hdec から）と ℚ 具体化の 2 段で書く。

```lean
-- (PLO-1) 一般形: 係数零判定 hdec があれば先頭係数探索オラクルが取れる
theorem plo_lead_oracle (R : CRing)
    (hdec : ∀ x : R.carrier, x = R.zero ∨ x ≠ R.zero) :
    ∀ (p : PS R) (n : Nat), IsPolyBounded R p n →
      (∀ i, p i = R.zero) ∨
      (∃ d, p d ≠ R.zero ∧ IsPolyBounded R p (d + 1))

-- (PLO-2) ℚ 具体化: rzd_zero_or_ne で hdec を討つ（hlead_oracle の完全解消）
theorem plo_lead_oracle_Q :
    ∀ (p : PS ratRing) (n : Nat), IsPolyBounded ratRing p n →
      (∀ i, p i = ratRing.zero) ∨
      (∃ d, p d ≠ ratRing.zero ∧ IsPolyBounded ratRing p (d + 1)) :=
  plo_lead_oracle ratRing rzd_zero_or_ne
```

**証明スケッチ（PLO-1・n を fuel とする下向き有限探索）**: `induction n` —
`n = 0` は `IsPolyBounded p 0` が ∀i, p i = 0 そのもの（左選言）。`n = k+1` は
`hdec (p k)` で二分: 非零なら d := k で右選言（有界性は仮定そのまま）; 零なら
`ppu_bound_drop` で `IsPolyBounded p k` に降ろして帰納法の仮定を適用。
choice-free（hdec は仮説・ℚ では `Int.decEq` 由来）・全部品既存・約 40 行。
tier S〜M の軽スライス。

---

## 2. 既約性の定式化 — `pdvIrreducible`（有界整除の除数二分形）

§0 により整除・単元・同伴は全て**有界 cofactor** で述べる。新述語（`PolyDvdDeg.lean`）:

```lean
-- (PDV-1) 多項式整除（cofactor が有界 = 本物の K[X] 整除）
def pdvDvd (R : CRing) (d a : PS R) : Prop :=
  ∃ c : PS R, IsPoly R c ∧ a = psMul R c d

-- (PDV-2) 単元 = 非零定数（K[X]^× の忠実な記述）
def pdvIsUnit (R : CRing) (d : PS R) : Prop :=
  ∃ c : R.carrier, c ≠ R.zero ∧ d = psC R c

-- (PDV-3) f の同伴 = f の非零定数倍
def pdvAssoc (R : CRing) (f d : PS R) : Prop :=
  ∃ c : R.carrier, c ≠ R.zero ∧ d = psMul R (psC R c) f

-- (PDV-4) 既約性: 非定数、かつ先頭係数付き有界除数は単元 or 同伴
def pdvIrreducible (R : CRing) (f : PS R) (n : Nat) : Prop :=
  1 ≤ n ∧
  ∀ (d : PS R) (md : Nat), IsPolyBounded R d (md + 1) → d md ≠ R.zero →
    pdvDvd R d f → pdvIsUnit R d ∨ pdvAssoc R f d
```

選定理由（Bezout DAG への忠実さ）:
- **除数二分形**を主とする。§3 の DAG では強化 Bezout が gcd gg を
  「有界 (mg+1)・先頭 gg mg ≠ 0・pdvDvd gg f」の形で produce するので、
  PDV-4 に**そのまま代入できる**（除数の正規形と一致）。分解形
  「f = g·h ⟹ g 単元 ∨ h 単元」は数学的に同値だが、DAG 側で除数→分解の
  変換（cofactor の先頭係数抽出 = §4 の degree 補題）を挟む分だけ遠い。
  同値補題 `pdv_irr_iff_factor` は任意（§4 の degree 補題の系・優先度低）。
- 除数を「有界＋先頭非零」の正規形で受けるのは、gg の生産形と一致するのに
  加え、**単元の判定が「md = 0」と同値**（`ppu_const_eq_psC` で d = psC (d 0)、
  d 0 ≠ 0）になり具体 f の既約性証明（md による場合分け 0 < md < n）が
  書きやすいため。
- 抽象 `Field268`/`CRing` 上のまま定義する（ℚ 固有物は入れない）。具体 f の
  既約性証明（x³−2 の写経・Φ_p の Eisenstein）は本設計外の named 後続（§6）。

---

## 3. 本丸: 一般 hBez の DAG

目標（PS 版の頂点。K は一般 `Field268`、ℚ は specialization）:

```lean
-- (PGB-4) 一般 hBez（PS 版頂点）
theorem pgb_bezout_of_irreducible (K : Field268)
    (hdec : ∀ x : K.ring.carrier, x = K.ring.zero ∨ x ≠ K.ring.zero)
    (f : PS K.ring) (n : Nat)
    (hb : IsPolyBounded K.ring f (n + 1)) (hl : f n ≠ K.ring.zero)
    (hirr : pdvIrreducible K.ring f n)
    (a : PS K.ring) (Na : Nat) (ha : IsPolyBounded K.ring a Na)
    (hnd : ¬ pdvDvd K.ring f a) :
    ∃ u v : PS K.ring, IsPoly K.ring u ∧ IsPoly K.ring v ∧
      psAdd K.ring (psMul K.ring u f) (psMul K.ring v a) = psOne K.ring
```

### 3.1 前段: 強化 Bezout クローン `pgbBezoutB`（§0 の帰結・別ファイル）

`pbzExtGcdAux` の写経に、(i) 組合せ係数 s,t の有界性、(ii) 整除 cofactor の
有界性（pbzDvd → pdvDvd）を conclusions として追加したもの:

```lean
-- (PGB-1) 強化拡張ユークリッド（pbzExtGcdAux の bound-tracking 版）
theorem pgbExtGcdAuxB (R : CRing) (invf) (hinv) (hlead_oracle) (f g : PS R) :
    ∀ (fuel : Nat) (a b sa ta sb tb : PS R) (Na mb : Nat),
      IsPolyBounded R a Na → IsPolyBounded R b (mb + 1) → b mb ≠ R.zero →
      mb < fuel →
      IsPoly R sa → IsPoly R ta → IsPoly R sb → IsPoly R tb →
      a = psAdd R (psMul R sa f) (psMul R ta g) →
      b = psAdd R (psMul R sb f) (psMul R tb g) →
      ∃ (s t gg : PS R) (mg : Nat),
        IsPoly R s ∧ IsPoly R t ∧
        gg = psAdd R (psMul R s f) (psMul R t g) ∧
        IsPolyBounded R gg (mg + 1) ∧ gg mg ≠ R.zero ∧
        pdvDvd R gg a ∧ pdvDvd R gg b

-- (PGB-2) 頂点（初期対 f = 1·f + 0·g, g = 0·f + 1·g、fuel = mg0 + 1）
theorem pgbBezoutB (R)(invf)(hinv)(hlead_oracle)(f g)(Nf mg0)
    (hf : IsPolyBounded R f Nf)(hg : IsPolyBounded R g (mg0 + 1))
    (hgl : g mg0 ≠ R.zero) :
    ∃ s t gg mg, IsPoly R s ∧ IsPoly R t ∧
      gg = psAdd R (psMul R s f) (psMul R t g) ∧
      IsPolyBounded R gg (mg + 1) ∧ gg mg ≠ R.zero ∧
      pdvDvd R gg f ∧ pdvDvd R gg g
```

追加簿記は全て既存部品で閉じる: s,t の更新 sa − q·sb は
`simpleExt_add_bounded`＋`simpleExt_neg_bounded`＋`simpleExt_mul_bounded`
（q は `field_division_exists` から有界 (Na+1)）; 整除 cofactor の更新
q·cb + cr（`pbz_dvd_comb`）も同 3 補題; 基底 case（r = 0 葉）の cofactor は
q（有界）と psOne（有界 1）。IsPoly は ∃ 形なので上界の算術を書かずに済む。
証明手順・分岐構造は `pbzExtGcdAux` と完全同型（写経＋各分岐に obtain/refine
数行の追加）。既存 `pbzBezout` は温存し**呼ばない**（conclusions が弱いため）。

### 3.2 DAG 本体（pgb_bezout_of_irreducible の 5 段）

```
[0] hlead := plo_lead_oracle K.ring hdec                       （§1）
[1] pgbBezoutB (f := a, g := f, mg0 := n; hgl := hl)
      ⟹ s t gg mg: IsPoly s ∧ IsPoly t ∧ gg = s·a + t·f
                    ∧ gg 有界(mg+1) ∧ gg mg ≠ 0
                    ∧ pdvDvd gg a ∧ pdvDvd gg f
[2] hirr.2 gg mg ⟨有界⟩ ⟨先頭非零⟩ ⟨pdvDvd gg f⟩
      ⟹ pdvIsUnit gg ∨ pdvAssoc f gg                        （二分）
[3a] 単元枝: gg = psC c, c ≠ 0
      ⟹ pgb_one_of_unit_B（下記）で u := psC(invf c)·t, v := psC(invf c)·s、
        u·f + v·a = 1 ∧ IsPoly u ∧ IsPoly v                  （完了）
[3b] 同伴枝: gg = psC c · f  ⟹  pdvDvd f gg（cofactor psC c・有界 1）
      ⟹ pdvDvd_trans : pdvDvd f gg → pdvDvd gg a → pdvDvd f a
      ⟹ hnd と矛盾                                            （完了）
```

補助補題の型（[3a][3b] の脚）:

```lean
-- (PGB-3) 単元正規化の有界版（pbzBezout_one_of_unit の IsPoly 追跡クローン・
--         等式部は pbz_scale_comb 再利用・約 25 行）
theorem pgb_one_of_unit_B (R)(invf)(hinv)(f g s t gg : PS R)
    (hs : IsPoly R s) (ht : IsPoly R t) (c : R.carrier) (hc : c ≠ R.zero)
    (hcomb : gg = psAdd R (psMul R s f) (psMul R t g))
    (hunit : gg = psC R c) :
    ∃ u v : PS R, IsPoly R u ∧ IsPoly R v ∧
      psAdd R (psMul R u f) (psMul R v g) = psOne R

-- (PDV-5) 有界整除の推移律（cofactor の積・simpleExt_mul_bounded）
theorem pdvDvd_trans (R : CRing) {f g a : PS R}
    (h1 : pdvDvd R f g) (h2 : pdvDvd R g a) : pdvDvd R f a

-- (PDV-6) 同伴 ⟹ f が gg を割る（cofactor = psC c・有界 1）
theorem pdv_dvd_of_assoc (R : CRing) {f gg : PS R}
    (h : pdvAssoc R f gg) : pdvDvd R f gg
```

注意（[1] の引数順）: `pgbBezoutB` の除数側 g には**先頭係数非零が既知の f**
を渡す（hgl := hl）。被除数側 a は上界 Na だけでよい。得られる組合せは
gg = s·a + t·f なので [3a] では f 側係数が t・a 側係数が s（入替えて提示）。

### 3.3 Poly（Subtype）梱包と `SimpleExtData.bezout` 型への着地

CBC-3 `cbc_idealRel_zero_iff` は ct0 固定だったが証明は法多項式に依存しない。
一般 F で書き直す（写経・約 15 行）:

```lean
-- (PGB-5) idealRel の零右辺整形（一般法多項式版）
theorem pgb_idealRel_zero_iff (R : CRing) (F a : Poly R) :
    idealRel (polyCRing R) F a (polyCRing R).zero
      ↔ ∃ h : Poly R, a = (polyCRing R).mul h F

-- (PGB-6) Poly 版頂点 = SimpleExtData.bezout の型そのもの
theorem pgb_bezout_poly (K : Field268) (hdec)
    (f : PS K.ring) (n : Nat) (hb : IsPolyBounded K.ring f (n + 1))
    (hl : f n ≠ K.ring.zero) (hirr : pdvIrreducible K.ring f n) :
    ∀ a : Poly K.ring,
      ¬ idealRel (polyCRing K.ring) (simpleExtModulus K f n hb) a
        (polyCRing K.ring).zero →
      ∃ u v : Poly K.ring,
        (polyCRing K.ring).add
          ((polyCRing K.ring).mul u (simpleExtModulus K f n hb))
          ((polyCRing K.ring).mul v a) = (polyCRing K.ring).one
```

翻訳は CBC-5 `cbc_bezout` の写経: ¬idealRel を (PGB-5) 経由で
¬pdvDvd f a.val（`∃ h : Poly` ⟷ `∃ c, IsPoly c ∧ …` の pack/unpack、
`ppu_poly_ext`・val(polyMul)=psMul は defeq）へ翻訳 → (PGB-4) → witness u,v を
IsPoly ごと Subtype へ梱包。

---

## 4. 一般 SimpleExtData 構成器 — `genExtData` / `genField`

```lean
-- (GEN-1) 一般構成器（K : Field268・hdec・既約性は仮説）
def genExtData (K : Field268)
    (hdec : ∀ x : K.ring.carrier, x = K.ring.zero ∨ x ≠ K.ring.zero)
    (hK1 : K.ring.one ≠ K.ring.zero)
    (f : PS K.ring) (n : Nat)
    (hb : IsPolyBounded K.ring f (n + 1)) (hl : f n ≠ K.ring.zero)
    (hn : 1 ≤ n) (hirr : pdvIrreducible K.ring f n) :
    SimpleExtData K where
  modulus := f
  deg := n
  bound := hb
  lead := hl
  deg_pos := hn
  base_nontrivial := hK1
  bezout := pgb_bezout_poly K hdec f n hb hl hirr

def genField (K)(hdec)(hK1)(f n hb hl hn hirr) : SimpleFieldExt K :=
  (genExtData K hdec hK1 f n hb hl hn hirr).build K

-- (GEN-2) ℚ 具体化（プロンプト指定形。hdec := rzd_zero_or_ne、
--         hK1 := ratIUTField.one_ne_zero、K := pbzRatField）
def genExtDataQ (f : PS ratRing) (n : Nat)
    (hb : IsPolyBounded ratRing f (n + 1)) (hl : f n ≠ ratRing.zero)
    (hn : 1 ≤ n) (hirr : pdvIrreducible ratRing f n) :
    SimpleExtData pbzRatField
def genFieldQ (f n hb hl hn hirr) : SimpleFieldExt pbzRatField
```

（`pbzRatField.ring = ratIUTField.toCRing ≡ ratRing` の defeq は CBC 実績。
万一 rfl で通らなければ `show`/`Eq.mpr` 一行の詰め替え——実装時の check 項目。）

### 4.1 次数簿記補題群（具体 f の既約性証明と PDV の整備に必要な脚）

hBez DAG 自体（§3）は下記を**要求しない**（gg の有界＋先頭非零が recursion
から直接出るため）が、具体 f で `pdvIrreducible` を**証明する**段（x³−2 の
一般化・Φ_p 等）と PDV 層の完結には次が要る:

```lean
-- (PDV-7) 積の sharp な上界: deg ≤ N, M ⟹ 積の deg ≤ N+M
--   （simpleExt_mul_bounded は (N+1)+(M+1) で 1 過剰。同じ添字計算で sharp 化）
theorem pdv_mul_bounded_sharp (R : CRing) {g h : PS R} {N M : Nat}
    (hg : IsPolyBounded R g (N + 1)) (hh : IsPolyBounded R h (M + 1)) :
    IsPolyBounded R (psMul R g h) (N + M + 1)

-- (PDV-8) 積の先頭係数（psMul_g_top_coeff268 の言い換え・既存で実質済み）
--   w 有界(M+1)・g 有界(m+1) ⟹ (w·g)(M+m) = w M · g m

-- (PDV-9) cofactor の正規化（除数の degree 上界の本体）:
--   f = c·d, c IsPoly, f 有界(n+1), f n ≠ 0, d 有界(md+1), d md ≠ 0 ⟹
--   md ≤ n ∧ ∃ 正規形: IsPolyBounded c (n−md+1) ∧ c (n−md) ≠ 0 ∧ md + (n−md) = n
theorem pdv_cofactor_lead (K : Field268) (hdec) {f c d : PS K.ring}
    {n md Nc : Nat} (hf : IsPolyBounded K.ring f (n + 1))
    (hfl : f n ≠ K.ring.zero) (hc : IsPolyBounded K.ring c Nc)
    (hd : IsPolyBounded K.ring d (md + 1)) (hdl : d md ≠ K.ring.zero)
    (heq : f = psMul K.ring c d) :
    md ≤ n ∧ IsPolyBounded K.ring c (n - md + 1) ∧ c (n - md) ≠ K.ring.zero
```

(PDV-9) の証明戦略: `plo_lead_oracle` を c に適用。c 全零なら f = 0 で hfl に
矛盾。c の先頭 dc（有界 dc+1・c dc ≠ 0）を取り、(PDV-8) で
(c·d)(dc+md) = c dc · d md ≠ 0（体の零因子なし = `mul_eq_zero_left268` の対偶）。
f 有界(n+1) と併せ dc + md ≤ n。逆向きは (PDV-7) で c·d 有界(dc+md+1)、
f n ≠ 0 から n ≤ dc + md。よって dc = n − md。`cco_cofactor_linear`
（n=3, md=2 固定）の一般化に相当。

- 用途 1（具体 f の既約性）: pdvIrreducible の除数 d（md, 先頭非零）に対し
  (PDV-9) で md ≤ n・余因子の次数 n−md を確定 → md = 0 は単元枝・md = n は
  余因子が定数（同伴枝・`ppu_const_eq_psC`）→ 残る 0 < md < n を f 固有の
  数論（x³−2 なら有理根なし = 既存 crt_two_not_cube 系の再編、Φ_p なら
  Eisenstein）で反駁する、が標準テンプレートになる。
- 用途 2（任意）: `pdv_irr_iff_factor`（除数二分形 ⟷ 分解形の同値）。

---

## 5. 並列スライス割当（5 並列の埋め方・DAG 対応）

新規ファイル 5 本（全て新規・共有ファイル不触・親が統合時に IUT.lean /
gen_graph PILLAR / graph-meta を一括更新）:

| # | ファイル | 内容（§ 対応） | tier / model | 依存 | 並列 |
|---|---|---|---|---|---|
| 1 | `IUT/PolyLeadOracle.lean` | PLO-1/2（§1） | S〜M / opus | RatZeroDecide, PolyPSUtil | **R1 並列** |
| 2 | `IUT/PolyDvdDeg.lean` | PDV-1〜9（§2, §4.1） | M / opus | SimpleExtension, PolyFieldDivision（PDV-9 のみ #1 の plo_lead_oracle も） | **R1 並列**（PDV-9 だけ #1 完了後に追記 or R1 は一般 hdec を仮説で受けて自立） |
| 3 | `IUT/PolyBezoutBounded.lean` | PGB-1/2/3（§3.1）強化クローン | M / opus（詰まれば L/fable 引継） | PolyBezoutQ, SimpleExtension, #2（pdvDvd） | R2（#2 の def 確定後） |
| 4 | `IUT/GeneralIrredBezout.lean` | PGB-4/5/6（§3.2–3.3 DAG 組立） | M〜L / opus 主・fable は HELP のみ | #1, #2, #3 | R3 直列 |
| 5 | `IUT/GeneralSimpleExt.lean` | GEN-1/2（§4 構成器・capstone） | S / sonnet | #4 | R3（#4 と同一ラウンド後半 or R4） |

- プロンプトのスライス対応: **(a) plo_lead_oracle_Q = #1**（DAG [0]）、
  **(b) 整除/次数補題 = #2**（DAG [3b] の脚 PDV-5/6 と、既約性証明用 PDV-7/8/9）、
  **(c) 既約 ⟹ 単元 or 同伴の二分 = #4 の [2]–[3b]**（二分そのものは
  pdvIrreducible の適用なので #4 に属し、#2 は述語と脚だけ供給）。
- R1 で #1 ∥ #2 は完全独立（#2 の PDV-9 は hdec を引数に取るので #1 の成果を
  待たずに書ける——plo_lead_oracle の呼び出しだけ #4 で行う設計も可）。
  R1 の残枠は A3 先行（Φ₃ = x²+x+1 の係数列・有界・先頭非零の定義層、
  tier S）や既存柱の独立残件で埋める（水増し capstone では埋めない）。
- #3 は写経量が多い（pbzExtGcdAux 全体の bound-tracking 化・推定 250 行級）が
  イディオムは確立済み（cbz_descend の簿記）。opus で着手し、分岐の簿記で
  詰まった箇所のみ fable にスポット委譲。
- #4 が真の新結線（既約性の適用・同伴枝の矛盾・Poly 梱包）。#5 は record
  詰めのみで新規証明ゼロ（sonnet）。

---

## 6. A1・A3 への波及と正直な限定（保守的見積り）

### A1（実数体 ℚ[x]/(f)・現 0.7）

- 本設計の完遂で「**単一 f = x³−2 のみ**」の限定が「**一般 f・ただし既約性
  `pdvIrreducible` は仮説**」へ昇格する。hlead_oracle は完全解消（ℚ で本物）。
  エンジンのみ（新規の具体 f 無し）なら **0.7 → 0.75 級**が正直な線:
  既約性が仮説である限り「一般 f の実体」を無条件には主張できない。
- 具体 f を最低 1 個追加実証（Φ₃ = x² + x + 1 が最軽量: 0 < md < n の反駁は
  「x² + x + 1 の有理根なし」= 判別式負の有限計算）すれば **0.8 級**。
  x³−2 も本エンジン経由で再導出（CBC の鎖 → pdvIrreducible ct0PS 3 への
  移植）すれば設計の一貫性が閉じる（優先度は新規 f より下）。
- **0.9 に届かない残り**（named・本設計外）:
  (i) **全域 inv**: has_inverses は依然 ∃ 形。ただし本設計で道が開ける——
  商体の零判定 `genExt_zero_dec`（[a] = 0 ⟺ f ∣ a は `field_division_exists` の
  剰余 r の全係数零判定 = hdec の有限回適用で**choice-free に決定可能**）を
  積めば、∃ 逆元 + 零判定から全域 inv 関数の構成が視野に入る（Quot の代表
  レベルで inv を定義する重い後続・別スライス）。
  (ii) **基底・次数**: {1, x, …, x^{n−1}} の一次独立・[K(α):K] = n の線形代数は
  未着手。(iii) 任意 f の既約性**判定**は対象外（仮説で受けるのが本設計の限定）。

### A3（実 Galois 塔・円分体）

- 本エンジンは A3 の**前提供給装置**: 法多項式 f と `pdvIrreducible` を渡せば
  実体 K[x]/(f) が出る。円分体 ℚ(ζ_{p^n}) には
  (i) Φ_{p^n} の係数列（PS ratRing・有界・先頭 1）の構成——x^{p^{n−1}(p−1)} + …
  の有限和、tier S〜M で独立に積める、
  (ii) Φ_{p^n} の既約性——**Eisenstein 判定（x ↦ x+1 シフト後 p-Eisenstein）**が
  named の重い後続（二項係数の p 整除・shift 準同型の構成）。既存 eisRing 層は
  模型なので流用せず、実 ℤ 係数の Eisenstein を新設する必要がある（toy 主語
  禁止）。
- **塔**（ℚ(ζ_p) ⊂ ℚ(ζ_{p²}) ⊂ …）には前段の商体を新たな `Field268` として
  渡す必要があり、そのためには (α) has_inverses の全域 inv 化（上記
  `genExt_zero_dec` 経由）と (β) 商体上の hdec（同じく genExt_zero_dec）が要る。
  本設計が K を一般 `Field268`+hdec で受けるのはこの相対拡大への布石であり、
  genExt_zero_dec が閉じれば**同一エンジンの反復適用**で塔が建つ、が A3 の
  設計上のクリティカルパス。complete_pct への A3 計上は円分 f の既約性実証
  （(ii)）が入るまで **0 のまま**と申告するのが正直。

### 正直な限定（§4 規約・消さない）

1. `pdvIrreducible` は**仮説**——本設計は「既約 ⟹ 体」のエンジンであり
   既約性の証明装置ではない。2. 逆元は ∃ 形のまま（全域 inv は named 後続）。
3. 基底・次数・最小多項式は未着手。4. `pbzDvd`（無界）と `pdvDvd`（有界）の
   差は本質（§0 の反例）であり、既存 PolyBezoutQ の正直申告は変更しない。
5. 円分 Φ_{p^n} は係数構成すら未着手（本設計は受け口のみ）。
