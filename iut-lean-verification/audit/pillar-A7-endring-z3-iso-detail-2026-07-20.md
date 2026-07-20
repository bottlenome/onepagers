# A7 End(ℤ₃(1)) ≅ ℤ₃ 環同型スライス詳細化（tmer 指数表示 → 実 z3 環同型の到達可能性）— 2026-07-20

**分類: [設計のみ / design-only]・tier-L 詳細化・complete_pct 0 前進（Lean コードなし・共有ファイル変更なし）・§4 規約遵守（既存の正直な限定を消さない・弱めない・過大主張しない）**

- 対象: 柱A **A7**（実円分剛性・現 s_A7=0.57・weight 12）。直近の A7f =
  `IUT/TateModuleEndoRing.lean`（tmer）は End(ℤ₃(1)) の環演算を**指数族表示の上で**確立したが、
  正直な限定 (1)(2) で「**A2 の実 ℤ₃ 環 z3 との環同型接続は未形式化**・End の抽象環束ねも未」を
  明示的に残した。本書はその名指し後続ターゲット——**End(ℤ₃(1)) ≅ ℤ₃（実 `z3` オブジェクト）
  の本物の環同型**——の到達可能性を disproof-first で検査する。
- 先例テンプレート: `audit/pillar-A6-monotheta-kill-detail-2026-07-11.md`（同型の disproof-first
  検査で「研究」判定を覆した）。

---

## 0. TL;DR

**判定: 到達可能（research-blocked ではない）・choice-free・opus 1 枠 1 ファイル。**
しかも依頼文の「少なくとも単射環準同型」より強く、**明示逆写像つきの両側環同型**
（`z3vRingEquivData trzEndRing z3` 型・∃ すら不要の関数レベル逆写像）が構成できる。理由の骨子:

1. **順方向** φ : End(T) → z3 は `φ(f).val n := Quot.mk (tmeChar f n : Int)` の 1 行で定義でき、
   整合性は既証明の `tme_char_compat`（mod 3^{i+1}——z3 の level i が要求する mod 3^i より**強い**）
   から従う。逆極限の「組み立て」に新しい完備化・極限構成は一切不要——指数族は**すでに**整合族
   である（§2 攻撃 1）。
2. **逆方向**の唯一の見かけ上の障害「Quot 類から代表元を選ぶ = choice では？」は不成立:
   `Quot.lift (fun a : Int => (a % m).toNat)` による**choice-free 代表元抽出は
   `IUT/Finiteness.lean` の `zmod_finite`（M17-5a・296 行）に一字一句同じイディオムで既存**。
   逆写像は `tmiPowHom`（tmi TMI-1b・既存）にこの代表元族を食わせるだけ（§2 攻撃 3）。
3. 乗法の照合（合成 = 指数積 vs z3 の zpMul = 代表元積）は `tmer_char_comp` がそのまま供給し、
   加法は `tmer_char_add`、単位は `tmer_char_id`（§2 攻撃 4）。全て mod 3^{n+1} ⊇ mod 3^n。
4. 精度 1 段のズレ（tmeChar level n は mod 3^{n+1}・z3 level n は mod 3^n）は単射性を壊さない
   ——level n+1 成分＋ `tme_char_compat` の 1 段シフトで mod 3^{n+1} 一致が回収できる（§2 攻撃 2）。

**マイルストーン**: 新規 1 ファイル `IUT/TateModuleEndRingZ3Iso.lean`（prefix `trz`・衝突なし
grep 確認済）・TRZ-0〜5・推定 400–600 行・新規イディオム実質 0。
**予測 s_A7**: 中央 **0.58（+0.01）**・上振れ 0.59・下振れ 0.57 据え置き。柱A 表示（現 57・
Σ_A=56.86）は**動かない見込み**（+0.12〜0.24 では 57.5 に届かない）——表示 mover ではなく、
tmi/tme/tmer が 3 ファイル連続で名指ししてきた正直限定の**正面 discharge**として積む一手（§4）。

---

## 1. 正確なギャップ（何が有り・何が無いか）

### 1.1 tmer が持っているもの（指数表示上の環演算・A7 計上済 0.57）

`IUT/TateModuleEndoRing.lean`（tmer）は T = ℤ₃(1) = `tmzLimit` の End の環演算を
**指数族 `tmeChar : Hom tmzLimit tmzLimit → Nat → Nat`（level n で mod 3^{n+1}）の上で**確立:

- `tmer_char_comp`（87 行）— 合成 = 指数族の積: `tmeChar (Hom.comp f g) n % 3^{n+1} = tmeChar f n * tmeChar g n % 3^{n+1}`。
- `tmer_char_add`（205 行）— 点ごと積 `tmerAdd`（196 行）= 指数族の和。
- `tmer_char_id`（143 行）/ `tmer_char_zero`（169 行）— `tmerId`/`tmerZero` = 指数 1/0。
- `tmer_comp_comm`（130 行）— 合成の指数可換性（End は可換）。
- capstone `TmerEndoRingData`/`tmerEndoRingData`（247/264 行）。

土台（全て既存・消費のみ）: `tmeChar`/`tme_endo_pow`/`tme_char_compat`/`tme_endo_ext`
（`IUT/TateModuleEndo.lean` TME-5・311/316/358/388 行）＝ End 完全分類、
`tmiPowHom`/`tmi_pow_char`/`TmiExpFam`（`IUT/TateModuleIndeterminacy.lean` TMI-1・77/86/104 行）
＝ 整合指数族 → End の逆構成。

**tmer の正直な限定（本書の検査対象）**: (1)「**A2 の実 ℤ₃ 環 z3 との環同型接続は依然未形式化**
……後続の昇格ターゲットとして依然名指しのまま残す」・(2)「End(T) を抽象環として full ring axioms
で束ねる capstone は作らない」。同旨の名指しは tme 限定 (4)・tmi 限定 (4) にも 3 連続で残る。

### 1.2 実 ℤ₃ オブジェクトの正体（写像先・A2 計上済）

- **`z3 : CRing := zpRing 3`**（`IUT/Zp3ValuationRing.lean` 55 行・@[reducible]）。
- `zpRing p : CRing`（`IUT/Ring.lean` 178 行・M38-5）: carrier = `(Zp p).carrier`、
  加法 = `(Zp p).mul`（逆極限群 M27）、乗法 = `zpMul p`（`IUT/PrincipalUnits.lean` 61 行・
  成分ごと `zmodMul`）、**全環公理証明済み**（結合・可換・分配・単位）。
- `Zp p = limitGrp (padicSystem p)`（`IUT/LocalCFT.lean` 90 行）: **level n の成分は
  `zmod (p^n)`** = ℤ の商 `Quot (modCong (p^n))`（`IUT/Profinite.lean` 262/254 行・
  rel = `(n:Int) ∣ a − b`）。遷移 `zmodTrans`（265 行）は **Quot.mk a ↦ Quot.mk a**
  （代表元保存・rfl 級）。
- z3 は A2 の付値環理論の主語（`z3vMax`/`z3vResidue ≅ 𝔽₃` = `z3v_res_iso`・
  `IUT/Zp3ValuationRing.lean` 241–375 行）であり、「実 ℤ₃ 環オブジェクト」の資格は確立済み。
- **環同型の器も既存**: `z3vRingEquivData (R S : CRing)`（同 364 行）は名前に反して
  **汎用**（toFun/invFun : RingHom・left_inv/right_inv）。新構造体は不要。

### 1.3 ギャップの正体（4 点・全て有限個の翻訳）

| # | ギャップ | 内容 |
|---|---|---|
| G1 | **表現の不一致** | tmeChar は Nat 族（level n・mod 3^{n+1}）、z3 は Int-Quot 族（level n・mod 3^n）。両者を結ぶ写像が無い |
| G2 | **添字 1 段ズレ** | tmz の level n は μ_{3^{n+1}}（mod 3^{n+1}）、padicSystem の level n は mod 3^n（level 0 は自明群 mod 1） |
| G3 | **End が環として未束ね** | `Hom tmzLimit tmzLimit` は CRing インスタンスでない（tmer 限定 (2)）。RingHom の定義域になれない |
| G4 | **逆写像** | z3 元 → End の構成（tmiPowHom はあるが、Quot 類 → Nat 指数の抽出が要る） |

---

## 2. Disproof-first 検査（敵対的攻撃 8 本）

### 2.1 攻撃 1（依頼文の指定攻撃）: 指数族は整合 ℤ₃ 元に組み上がるか——極限・完備化障害は？

**判定: 障害なし——組み立ては定義 1 行で、整合性は既証明が過剰供給している。**
順方向を `trzToZ3(f).val n := Quot.mk (modCong (3^n)).rel ((tmeChar f n : Nat) : Int)` と
定義すると、`padicSystem 3` の整合性（i ≤ j で `zmodTrans` 像一致）が要求するのは
**3^i ∣ tmeChar f j − tmeChar f i（Int）** のみ。既証明 `tme_char_compat`
（`IUT/TateModuleEndo.lean` 358 行）は `tmeChar f j % 3^{i+1} = tmeChar f i % 3^{i+1}`（Nat）
——**要求より 1 段強い** mod 3^{i+1} 合同を与える。`zmodTrans` は代表元保存
（`Profinite.lean` 266 行: `Quot.lift (fun a => Quot.mk (modCong m).rel a) …`）なので、
整合性証明は「Nat mod 等式 → Int ∣ 差」の翻訳 1 個（§3 TRZ-0）に帰着する。
新しい極限構成・完備化・Cauchy 列・choice は**一切登場しない**——`tmeZetaLim` を f で送った
族の整合性（= f の連続性の代数版）として tme が既に支払ったコストの再利用である。

### 2.2 攻撃 2: 1 段の精度損失（G2）で単射性が死なないか？

**判定: 死なない（1 段シフトで回収）。** φ f = φ g は level n で
3^n ∣ χ_f n − χ_g n しか与えず、`tme_endo_ext`（388 行）が要求する
「∀n, χ_f n ≡ χ_g n mod **3^{n+1}**」に一見届かない。しかし level n+1 成分の一致
3^{n+1} ∣ χ_f (n+1) − χ_g (n+1) と `tme_char_compat (n ≤ n+1)` の
χ_• (n+1) ≡ χ_• n（mod 3^{n+1}）を合成すれば χ_f n ≡ χ_g n（mod 3^{n+1}）が全 n で出る。
消費: `tme_endo_ext`・`tme_char_compat`・Int/Nat 翻訳のみ。**逆向きの罠**
（φ を level n ↦ χ_f (n−1) とシフト定義して mod をピッタリ合わせる案）も可能だが、
n=0 の場外処理が増えるだけで利点がない——非シフト定義＋本攻撃のシフト論法を推奨。

### 2.3 攻撃 3（最重要）: 逆写像は Quot 類からの代表元選択 = choice 障害では？

**判定: 障害なし——choice-free 抽出はリポジトリ既存イディオムである。**
`IUT/Finiteness.lean` の `zmod_finite`（M17-5a・296 行）が文字通り
`Quot.lift (fun a => (a % ((n:Nat):Int)).toNat) (fun a b hab => … emod_eq_of_dvd hab)` で
zmod n → Nat の**関数**（well-defined・選択公理不使用・core Int 補題のみ:
`Int.emod_nonneg`/`Int.emod_lt_of_pos`/`Int.mul_ediv_add_emod`）を構成済み。
well-definedness の両方向の橋 `emod_eq_of_dvd`（262 行）/ `dvd_of_emod_eq`（275 行）も既存。
したがって

- `trzRep : (zmod m).carrier → Nat`（Quot.lift・閉じた式）は新規 20 行級、
- 逆写像 `trzFromZ3 (x : z3.carrier) : Hom tmzLimit tmzLimit := tmiPowHom ⟨fun n => trzRep (x.val (n+1)), compat⟩`
  は**本物の関数**（Prop-∃ に隠す必要すらない）。compat（`TmiExpFam.compat` の
  a j % 3^{i+1} = a i % 3^{i+1}）は x.property（i+1 ≤ j+1）＋ `dvd_of_emod_eq` 系翻訳から出る。

往復も閉じる: **ψ∘φ = id** は `tmi_pow_char`（104 行: tmeChar (tmiPowHom F) n ≡ F.a n
mod 3^{n+1}）＋「trzRep (Quot.mk χ_f (n+1)) = χ_f (n+1) % 3^{n+1}」（Nat cast・
`Int.ofNat_emod` 級）＋ `tme_char_compat` ＋ `tme_endo_ext`。**φ∘ψ = id** は level n で
roundtrip 補題 `Quot.mk (trzRep q) = q`（`Int.mul_ediv_add_emod` から 3^{n+1} ∣ a − (a%3^{n+1})）
＋ x.property の 1 段押し下げ。どちらも既存イディオムの直列。

### 2.4 攻撃 4: 乗法は本当に一致するか——合成 = 指数積 vs z3 の zpMul？

**判定: 一致（tmer が正確にこの形で供給済み）。** z3 の乗法は成分ごと
`zmodMul`（`IUT/PrincipalUnits.lean` 42 行）で、代表元上 `Quot.mk a · Quot.mk b = Quot.mk (a*b)`
は Quot.lift の定義展開（rfl 級）。よって map_mul の level n 側は
3^n ∣ χ_{f∘g} n − χ_f n · χ_g n を要求し、`tmer_char_comp`（mod 3^{n+1}）が過剰供給する。
加法側 map_add は `(Zp 3).mul` = 成分 zmod 加法（`Quot.mk (a+b)`・rfl 級）に対し
`tmer_char_add` が、map_one は `zpOne 3`（対角 1 族）に対し `tmer_char_id` が同様に供給。
Nat→Int キャストの積・和分配（`Int.ofNat_mul`/`Int.ofNat_add`）は core。
mul の左右の向き（`Hom.comp g f` = g∘f・`IUT/FundamentalGroup.lean` 146 行）は
`tmer_comp_comm` により無害。**指数積 ≠ ℤ₃ 乗法となる余地は無い**——両者とも
「代表元の Nat/Int 積 mod 3 冪」という同一の算術に落ちている。

### 2.5 攻撃 5: End の CRing 束ね（G3）に新数学は要らないか？

**判定: 要らない（唯一の非自明公理 mul_comm は既払い）。** `trzEndRing : CRing` の各成分:

- carrier = `Hom tmzLimit tmzLimit`、add = `tmerAdd`、zero = `tmerZero`、mul = `Hom.comp`、
  one = `tmerId`（全て既存）。neg = 新規 `trzNeg f := y ↦ tmzLimit.inv (f.map y)`
  （map_mul は可換群の inv-of-product・`tmer_limit_comm`（189 行）＋群律 5 行）。
- Hom の等式は `cra_hom_ext`（`IUT/CyclotomicRigidityAut.lean` 70 行・map_mul は Prop ゆえ
  cases で潰れる）で funext に帰着——add_assoc/zero_add/neg_add/add_comm は成分ごと群律、
  mul_assoc/one_mul は `Hom.comp` の定義展開で rfl 級。
- **mul_comm（可換環の核心）**: `tme_endo_ext` ＋ `tmer_comp_comm` の合成——両方既証明。
- **left_distrib**: f∘(g+h) = f∘g + f∘h は各点で `f.map_mul` そのもの（指数すら不要）。
  逆側分配は可換性から `CRing.right_distrib`（`IUT/Ring.lean` 51 行）で自動。

tmer 限定 (2) の discharge がここで同時に達成される。

### 2.6 攻撃 6: import 循環・二重計上 firewall

**判定: 問題なし。** 新ファイルの import は `IUT.TateModuleEndoRing`（tmer 経由で
tme/tmz/cci/zpu）＋ `IUT.TateModuleIndeterminacy`（tmiPowHom）＋ `IUT.Zp3ValuationRing`
（z3・z3vRingEquivData; その鎖 Ring/LocalCFT/PrincipalUnits/Finiteness/Profinite は
tmz 鎖を import しない——独立枝の合流であり循環なし。`Q3Mu3Completeness` 等が両鎖を
既に同居させている先例あり）。firewall: `tmer_char_comp`/`tmer_char_add`/`tmer_char_id`/
`tmer_char_zero`/`tmer_comp_comm`/`tme_endo_ext`/`tme_char_compat`/`tmi_pow_char`/
`tmiPowHom`/`emod_eq_of_dvd`/`dvd_of_emod_eq` は**消費のみ・再証明ゼロ**。

### 2.7 攻撃 7: これは tmer の再ラベルでは？（監査ディスカウント検査）

**判定: 再ラベルではない——が、割引は見込む。** 主語が異なる:
tmer の主語は「指数表示が環演算を保つ」（合同定理 5 本・z3 は登場しない）。
新スライスの主語は **(i) End(T) の抽象可換環としての束ね（tmer 限定 (2) の discharge）**、
**(ii) A2 の実付値環オブジェクト z3 への両側環同型（tmer 限定 (1)・tme 限定 (4)・
tmi 限定 (4) が 3 ファイル連続で名指しした successor target の discharge）**。
End(ℤ₃(1)) ≅ ℤ₃ という [IUTchI] の基本事実が、**柱 A7 の End 側と柱 A2 の環側という
別建設の実対象同士の同定**として閉じるのは新言明である。一方、証明実質は翻訳・簿記が
主（新イディオム 0）ゆえ、crc 先例（transport +0.03 未満）・tmer 先例（+0.01）に照らし
控えめ査定を見込む（§4）。

### 2.8 攻撃 8: 「正直な限定」を消すことにならないか（§4 規約）

**判定: ならない（討ち取り型 discharge）。** tmer 限定 (1)(2) は「未形式化・後続ターゲット」
という**ギャップ申告**であり、定義を弱めて閉じるのではなく名指しされた本物を建てて閉じる
（規約の认める唯一の閉じ方）。継承必須の限定は残る: mono-theta（tmer 限定 (3)）・
p=3/位相/幾何（限定 (4)）は新ファイルにそのまま並置する（§3 末尾）。

### 2.9 総合判定

**到達可能・choice-free・研究要素なし。** 4 ギャップ（G1–G4）は全て「既存資産の翻訳＋束ね」
で閉じ、唯一の懸念だった Quot 代表元抽出は Finiteness.lean の既存イディオム（§2.3）で決着。
禁止タクティク不要・∃ も不要（逆写像は関数）・新規 axiom 0（propext/Quot.sound のみ）。

---

## 3. マイルストーン梯子（新規 1 ファイル・prefix `trz`・全 choice-free）

新ファイル `IUT/TateModuleEndRingZ3Iso.lean`（prefix `trz`・衝突なし grep 確認済み）。
import: `IUT.TateModuleEndoRing`・`IUT.TateModuleIndeterminacy`・`IUT.Zp3ValuationRing`。
共有ファイル変更なし（親が統合）。

| 段 | 内容 | 消費資産 | 難度 |
|---|---|---|---|
| **TRZ-0** | 代表元抽出と mod 橋: `trzRep : (zmod m).carrier → Nat`（Quot.lift `(a % m).toNat`）、`trzRep_lt`・roundtrip `trzRep_mk : Quot.mk (trzRep q) = q`・Nat mod 等式 ⟺ Int ∣ 差の双方向橋（`emod_eq_of_dvd`/`dvd_of_emod_eq` 消費＋Nat cast 版 2 本） | `Finiteness.lean` 262/275/296 行イディオム・core Int（`Int.mul_ediv_add_emod`/`Int.emod_nonneg`/`Int.emod_lt_of_pos`/`Int.ofNat_emod`） | 低〜中（本 file 唯一の簿記スポット） |
| **TRZ-1** | **End 環束ね** `trzNeg`（点ごと逆元 endo）＋ `trzEndRing : CRing`（add=tmerAdd・mul=Hom.comp・mul_comm は `tme_endo_ext`+`tmer_comp_comm`・left_distrib は各点 `f.map_mul`）。**tmer 限定 (2) discharge** | `cra_hom_ext`・`tmer_limit_comm`・tmer 定義群・`tme_endo_ext` | 中の下 |
| **TRZ-2** | **順方向環準同型** `trzToZ3 : RingHom trzEndRing z3`（val n = Quot.mk (χ_f n)・整合は `tme_char_compat`＋TRZ-0 橋・map_add/mul/one は `tmer_char_add`/`tmer_char_comp`/`tmer_char_id`＋TRZ-0 橋） | tmer 合同定理 3 本・`tme_char_compat` | 中 |
| **TRZ-3** | **単射** `trz_inj`: φ f = φ g → f = g（level n+1 成分＋ `tme_char_compat` シフト＋ `tme_endo_ext`・§2.2 の論法） | `tme_endo_ext`・`tme_char_compat` | 中の下 |
| **TRZ-4** | **明示逆写像** `trzFromZ3 : z3.carrier → Hom tmzLimit tmzLimit` := `tmiPowHom` ∘ 代表元族（compat は x.property＋TRZ-0）＋往復 `trz_left_inv`（`tmi_pow_char`＋`tme_endo_ext`）・`trz_right_inv`（`trzRep_mk`＋x.property 押し下げ・§2.3） | `tmiPowHom`・`tmi_pow_char`・TRZ-0 | 中（★核・簿記最重） |
| **TRZ-5** | **capstone**: `trz_ring_iso : z3vRingEquivData trzEndRing z3`（汎用構造体を再利用・新構造体なし）＋ scope 補題（正直限定の機械可読束ね） | `z3vRingEquivData`（Zp3ValuationRing 364 行）・TRZ-1〜4 | 低（束ね） |

新規イディオム: **実質 0**（TRZ-0 は Finiteness の写経＋Nat cast 化・他は消費と glue）。
禁止タクティク不要。3^ℓ は `zpu_pow_pos`/`zpu_pow_dvd`/`zpu_one_lt` 経由（生 omega 渡し禁止を
遵守可能）。推定規模 400–600 行・**opus 1 枠 1 ラウンド**（fable は HELP 予備のみ）。

### 正直な限定（新ファイルに必ず書く・消さない・弱めない）

1. **mono-theta 円分剛性は本スライスの外**: 環同型は不定性を**殺さない**（Aut 側 ≅ ℤ₃^× の
   CHARACTERIZE の環版完成であって KILL ではない）。kill は mod-9 実装済み（q9mb・crk）＋
   mod-27 設計のみ（`audit/level27-kill-scope-2026-07-11.md`）、full ℤ₃^× kill は依然 0。
2. **p = 3 固定・円分切片・位相未形式化・幾何側不在**（tmz/tme/tmi/tmer の限定 (3)(4)(5) 継承）。
   `trzToZ3` の連続性（limitTopology 間）は主張しない。
3. z3 は A2 の実付値環だが、**本スライスは Q₃ 体・付値の同変性までは束ねない**（環同型のみ。
   Gal 作用が φ を通じて χ の像に行くことは tmi_act_char の帰結として別途 1 行言及に留める）。
4. tmer/tme/tmi の他の正直限定は一切消さない・弱めない——tmer 限定 (1)(2) だけが
   「本物を建てたことによる discharge」として閉じる（§2.8）。

---

## 4. 保守的 honest forecast と A7 帽子

**verdict: 到達可能。** 予測（過大主張しない・独立監査が確定）:

- **中央 s_A7 0.57 → 0.58（+0.01）**: 3 ファイル連続で名指しされた successor target の正面
  discharge・A2 実対象とのクロス柱同定・End の抽象環束ねという新言明はあるが、証明実質は
  翻訳/簿記/束ね（新イディオム 0）ゆえ tmer 先例（+0.01）と同格が敵対的相場。
- **上振れ 0.59（+0.02）**: 監査が「明示逆写像つき両側環同型（∃ なし・choice-free）＋
  限定 3 本同時 discharge」を crc の transport tier（+0.03 未満）相当と見た場合。
- **下振れ 0.57 据え置き**: 「tmer の主張の再パッケージ・数学的新規性ゼロ」査定。この場合でも
  tmer 限定 (1)(2)・tme 限定 (4)・tmi 限定 (4) の文言が「未形式化」から「trz で形式化済み」へ
  更新される実体は残る。
- **柱A 表示への波及: なし（正直明記）**。Σ_A 現 56.86（表示 57）に対し w12 × (+0.01〜0.02) =
  +0.12〜0.24 → 56.98〜57.10 で表示 57 のまま。本スライスは表示 mover ではない。
- **A7 帽子（変わらず）**: full ℤ₃^× kill（実 wild 円分塔・[EtTh] 本体）と実 G_{ℚ₃}/幾何
  cyclotome が 0 のあいだ、A7 は **≤ 0.60〜0.62 帯**に留まる（level-27 接続 +0.01〜0.03 と
  本スライスを足しても 0.60 前後が天井）。A7=1 には依然遠い——本スライスは
  「End/Aut/環同型の CHARACTERIZE 側を完成させ、以後の A7 前進は kill 側のみ」という
  **区切り**を作る一手である。

**やってはいけないこと（overclaim 禁止リスト）**: 「ℤ₃^× 不定性に進展」と書かない（環同型は
CHARACTERIZE 側）／「End(ℤ₃(1)) ≅ ℤ₃ 完全証明」を幾何・一般 p へ外挿しない（p=3 円分切片）／
tmer/tme/tmi の限定 (1)(2)(4) 以外を「解消」と書かない／連続性・位相同型を主張しない。

---

## 5. 推奨 first slice と de-risk

- **first slice（opus 1 枠）**: TRZ-0〜5 を単一ファイルで一括実装（依存が直列で薄く、分割の
  利得が小さい）。行数が 600 を超えそうなら TRZ-0/1（環束ね）と TRZ-2〜5（同型）の 2 分割で
  2 枠直列。tier 配分は §7.5 準拠で **M=opus**（確立イディオムの新インスタンス）——fable は
  詰まり HELP のみ。
- **de-risk 項目（実装前 10 分・scratchpad 使い捨てコンパイル）**: TRZ-0 の Nat cast 橋 2 本
  （「Nat A,B: (3^ℓ:Int) ∣ (A:Int)−(B:Int) ↔ A % 3^ℓ = B % 3^ℓ」）だけを先に単体コンパイルする。
  本設計で唯一 omega の generalize イディオム（`Finiteness.lean` 280–288 行型）に依存する箇所
  であり、ここが通れば残りは全て既証明の消費と rfl 級展開。
- **失敗時 fallback**: 万一 TRZ-4 の往復簿記が膨らむ場合、右往復（φ∘ψ = id）を先に落とし、
  「RingHom + 単射 + 明示 section」の弱形で一旦着地（それでも tmer 限定 (1) の過半は
  discharge・左往復は次ラウンド）——ただし §0 の解析では両往復とも既存イディオムで閉じる
  見込みが高く、fallback 発動確率は低い。
