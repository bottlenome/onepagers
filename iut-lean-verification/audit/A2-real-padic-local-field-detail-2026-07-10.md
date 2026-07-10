# A2 詳細化 — 実 p 進局所体 K_v: 実 ℤ₃・ℚ₃ の choice-free 本物構成（A2 0.5 → 0.65 級）

日付: 2026-07-10 ／ 種別: **設計ドキュメントのみ**（実装コード無し・共有ファイル不更新）
分類: **[実／昇格(a)+本物建設(b) の設計]** — 既存の実 p 進**付値**機構（pvq/pum/egv・本物）と
完備化**機構**（M301F–M316F・機構は実だが実例は自明付値のみ）の境界を精査し、
**実 ℚ₃ = 実 p 進局所体 K_v の choice-free 本物構成の最小経路**を opus 実装枠に渡せる
粒度へ段階分解する詳細化ラウンド。
台帳確認: `target_ledger.json` A2 = { weight 8, status **0.5** }（本日実測）。
柱A Σ(w·s) = 6.8+4.0+9.0+7.0+0+7.7+4.2+6.0+0 = **44.7**/100 → complete_pct 45
（`tools/compute_complete_pct.py` の round・`graph-meta.json` A=45 と整合確認済み）。
**complete_pct 影響: 本ドキュメント自体は 0（設計のみ）**。実装マイルストーンの
status 見積りは §6（保守値・最終確定は独立監査・AUDIT_RUBRIC 準拠）。

---

## 0. 既存資産の再監査（本日 read/grep 済み・シグネチャ実在確認）

### 0.1 ★中心的発見: 実 ℤ_p は既に存在する（逆極限環として・choice-free）

依頼文の予想「(A) 逆極限が有力・ℤ₃ は zps の環版を新設」に対する実測の修正:
**ℤ_p = lim ℤ/pⁿ は加法群・可換環・単数群・p 除算・Teichmüller 込みで既に本物に建っている**。
A2 の欠落は「ℤ₃ を作ること」ではなく、(i) **局所体パッケージ**（付値・極大イデアル・剰余体・
完備性）が ℤ₃ の上に載っていないこと、(ii) **体 ℚ₃ そのもの（K_v の主語）が皆無**なこと、
(iii) 実 ℚ 上の実付値機構（pvq）と ℤ₃ が**未接続**なこと、の 3 点である。
graph-meta の「実p進局所体K_vも皆無」はこの (ii) を指す（環 ℤ_p は柱B 文脈で建設済みだが
「局所体 K_v」としては未パッケージ・A2 実例未計上）。

| 資産 | 実在シグネチャ（ファイル:行・本日確認） | A2 での役割 |
|---|---|---|
| **ℤ_p 加法群** | `Zp p := limitGrp (padicSystem p)`（`LocalCFT.lean:90`・`padicSystem p = natSystem (fun n => zmod (p^n)) …`:83）・`Zp_compact`:93・`toZp`:109・`toZp_injective`:143（p≥2） | **A2a の主語そのもの**。担体は整合族 subtype（`Profinite.lean:167` `limitGrp`）＝依頼文の「(A) 逆極限」は**この形で実装済み** |
| **ℤ_p 可換環** | `zpRing p : CRing`（`Ring.lean:178`・add=(Zp p).mul・mul=`zpMul`）・`toZpRing : RingHom intRing (zpRing p)`:204・`projRing p n : RingHom (zpRing p) (zmodRing (p^n))`:217 | **「環版 limitRing の新設」は不要**——成分ごと乗法 `zpMul`（`PrincipalUnits.lean:61`・整合性証明込み）で直接環化済み。汎用 limitRing インフラの新設は共有インフラ改変であり不採用（§7.2） |
| **単数群 ℤ_p^×** | `IsZpUnit p x := ∃a, x.val 1 = [a] ∧ ¬p∣a`（`ZpUnits.lean:38`・**レベル1判定**）・`zpUnitInv`:117（**明示逆元・choice-free**・x^{p−2}·幾何級数逆元）・`zpUnitInv_mul`:124・`zpUnits p hp : Grp`:159・`zpUnits_decomposition`:186（μ×U^{(1)} 分解）・`teich`（`Teichmuller.lean:215`） | A2a の「O∖m は単元」の witness。**逆元は既に関数**（∃ 取り出し不要） |
| **p 除算** | `zpDivP p hp x : (Zp p).carrier`（`PadicDivision.lean:76`・**全域・choice-free**）・`zpDivP_mul_cancel`:89（p∣x なら p·(x/p)=x）・`zpDivP_cancel`:119・**`zp_dvd_p_iff`:138（∃e, x=p·e ⟺ x.val 1 = [0]・可除性のレベル1判定）** | A2a の因数分解 x = 3^v·u の再帰の心臓部 |
| **p 正則性** | `zp_p_regular`（`LubinTateZp.lean:123`・p·d=0 ⟹ d=0） | 3^k 正則性（反復）→ ℚ₃ の非退化・局所化単射性（§4） |
| **実 p 進付値（ℚ 側・本物）** | `pvqNatVal p n`（`PadicValuationQ.lean:70`・fuel 走査）・`pvqNatVal_spec`:107（n=p^k·n'・p∤n' ⟹ v=k）・`pvqVal`:162・`pvq_val_mul`:205・`pvq_val_p`:229。`PadicUltrametricQ`（pum・超距離）・`GaussValuationQ`（egv）・`PadicAbsValueQ`（pavAbs） | A2b の橋 `z3c_val_compat`（v₃ on ℤ ＝ ℤ₃ 内の exact 付値）の左辺。**実付値機構は本物**——欠けているのは完備化体との接続のみ |
| **完備化機構（Cauchy 路線・機構は実・実例は自明）** | M301F `valRingValuation K`（`ValuationRing.lean:109`・IUTField 上の総付値 v:K→Option Int）→ M306F `LocalFieldCompletion`（Cauchy/零列 setoid）→ M311F `LocalFieldRing`（K̂ の CRing 化・honest「K̂ の inv 全域化・完備性込みの収束は後続」）→ M316F `FieldCompletion`（**自明付値のみ** `fldCompTrivField`:328 で IUTField・一般付値は「非零判定が排中律を要する」と honest 明記） | §1 の比較対象 (B)。**実 (ℚ,v₃) インスタンスは未**（valRingValuation の実例は trivialValuation のみ）＝「機構は実だが実例が自明/退化」の実体 |
| **局所化** | `ringLocRing R S : CRing`（`RingLocalization.lean:431`）・`ringLocMap`:490（環準同型）・`ringLocRel`:147（∃t∈S, t(rs')=t(r's)）・`ringLocRf R f := R[1/f]`:595・`ringLoc_unit_of_S`（witness 形逆元）・honest 2「全域 inv は台の等号判定を要し採らない」 | **A2c の ℚ₃ = ℤ₃[1/3] の受け皿**（実例代入のみ・機構再証明不要） |
| **剰余体機構** | `primeSpecIdeal R`（`PrimeSpectrum.lean:73`・mem/zero/add/smul）・`resFieldMaximal R`（`ResidueField.lean:115`・**witness 形極大性** x∉m → ∃r s, s∈m ∧ r·x+s=1）・`resFieldQuot`:233・`resFieldProj`:301・`resField_quot_isField`:344（∃ 形可逆） | A2a の剰余体 ℤ₃/3ℤ₃。極大性 witness は **r=zpUnitInv・s=0** で即納（§2.4） |
| **今セッションの単数側逆極限** | `zpuGrp ℓ hℓ`＝(ℤ/3^ℓ)^×（Nat subtype 担体）・`zpuInv`（Hensel 逆元関数）・`zpsSystem`/`zpsLimit`＝ℤ₃^×・`zps_proj_surjective`（`Zmod3PowUnitsSystem.lean`） | **担体表現が別系統**（Nat subtype vs Quot Int）。A2 は Quot Int 系（Zp/zpRing）で閉じるため **zps/zpu との同型橋は A2 の範囲外**（後続 interop・§7.6）。`InverseSystem`/`limitGrp`/`natSystem` 機構は Zp が既に消費済み |
| **K^× 代理（昇格ターゲット）** | `unitsModel U := prodGrp intGrp U`（`LocalCFT.lean:153`・**K^× の抽象直積代理**）・`FullReciprocity.lean:64` `prodGrp intGrp (zpUnits p hp)`（ℚ_p^× 型の代理・「ℚ_p^× = p^ℤ×ℤ_p^× の明示同型は未形式化」と honest） | A2c-2 で**実 ℚ₃^× に昇格**する §2(a) 対象 |
| その他 | `isPrime_three`（`Fermat.lean:243`）・`zpPow`（`RootsOfUnity.lean:38`）・`SGA1Completion.lean` は**ガロア圏の抽象完成（充満忠実性）であり体の完備化と無関係**（名前のみ類似・A2 資産でない） | 素数性 witness・冪簿記 |

### 0.2 既存 IUTField 実例の確認（総当たり grep）

`IUTField where` 実例: ratIUTField・cq3Field（ℚ(ζ₃)）・gaussQField・gefNFIUTField（一般 ℚ[x]/(f)）・
fldCompTrivField（自明付値・DecidableEq 仮定付き）。**全て標数 0**。有限体 𝔽_p の IUTField も、
p 進体 ℚ_p の体オブジェクトも**存在しない**（後者が A2 の本丸、前者は A2a の剰余体で初納品）。

---

## 1. 問い 1（★核心）: 構成法の判定 — (A) 逆極限 vs (B) Cauchy 商

**結論: (A) 逆極限を採る（確定・裏取り済み）**。ただし依頼文の想定と違い「ℤ₃ を逆極限で
新設する」のではなく「**既設の逆極限環 zpRing 3 を局所体パッケージへ昇格させ、体 ℚ₃ は
その 3 冪局所化で作る**」。以下、choice-free 性・本物性・工数の三軸で厳密比較する。

### 1.1 (B) Cauchy 列 mod 零列 — どこまで choice-free に閉じるか（厳密評価）

1. **実 (ℚ, v₃) のインスタンス化自体は可能**（中工数）: `valRingValuation ratIUTField` は
   総関数 v : ℚ → Option Int を要求する。PadicValuationQ の honest note は「Quot 上の
   ゼロ判定選言が排中律を要する」と書くが、これは**選言（Or）としての取り出し**の話であり、
   `Int.decEq` は計算可能インスタンスなので **項レベル ite による Quot.lift**
   `fun x => if x.num = 0 then none else some (pvqVal 3 x)`（well-defined 性は
   `pvq_val_wd` + 「ratRel は num=0 を保つ」）で総関数 v は choice-free に作れる
   （zpuInv の項レベル ite 前例・禁止タクティク by_cases とは別物）。
   よって M311F `locRingCompletionRing` への代入で「Cauchy 商としての ℚ̂₃ : CRing」までは
   (B) でも到達**可能**ではある。
2. **しかし体化（total inv）は (B) では原理的に閉じない**: 非零判定「Cauchy 列が零列で
   ない」は ∀n∃N∀m（Π⁰₂ 型）の否定であり、決定関数が存在しない。M316F 自身が
   「非零判定（零列か否か）が排中律を要するため一般付値の total inv は行わない」と
   honest 明記し、自明付値のみ体化した。**v₃ は自明付値ではないので M316F の体化は
   一切適用できない**。∃ 形逆元（`fldComp_mul_inv_cancel_gen`・安定値 witness 付き）止まり。
3. **完備性が (B) では未解決のまま**: K̂ 自身の完備性は「二重完備化」（M316F honest・骨組み）。
   A2 のタイトルは「完備化」であり、ここが閉じないのは致命的。
4. **既存 ℤ₃ 資産と断絶**: (B) の ℚ̂₃ は zpRing 3・zpUnits・teich・zpDivP・LT 系の巨大な
   実資産と別の担体になり、接続には結局 (A)↔(B) 同型（大工事）が要る。

### 1.2 (A) 逆極限 — choice-free で閉じる範囲（厳密評価）

1. **ℤ₃ = lim ℤ/3ⁿ は既に本物・choice-free**（zpRing 3・§0.1）。担体は整合族 subtype、
   演算は成分ごと。新規構成ゼロ。
2. **完備性が choice-free に本物証明できる**（(B) との決定的差）: 逆極限モデルでは
   Cauchy 列の極限を**レベルごとに構成できる**——modulus M : Nat → Nat 付き Cauchy 列
   （∀n ∀i,j≥M(n), (x i).val n = (x j).val n）に対し、極限は
   `lim.val n := (x (M' n)).val n`（M' は M の単調化）という**閉じた式**。∃ 形 Cauchy
   （∀n∃N…）からの modulus 抽出は可算選択を要するため、**modulus 持ち Cauchy 列の完備性**
   として述べるのが choice-free の忠実版（RReal の regular 列イディオムと同精神・§3.2）。
3. **付値・単数・剰余体の材料が全部ある**: レベル 1 判定（IsZpUnit・zp_dvd_p_iff）・
   明示逆元（zpUnitInv）・p 除算（zpDivP）・p 正則性（zp_p_regular）。
4. **ℚ₃ = ℤ₃[1/3]** は `ringLocRf (zpRing 3) 3` の**実例代入**（機構再証明不要）。
   分母が 3 冪に限られるため分母簿記が決定可能で、Frac(ℤ₃) 案より軽い（§7.4）。

### 1.3 判定表

| 軸 | (A) 逆極限（採用） | (B) Cauchy 商 |
|---|---|---|
| ℤ₃ 環 | **既設**（zpRing 3・choice-free） | 新規インスタンス化（中工数） |
| 体 ℚ₃ の inv | ∃ 形（正の witness 付き・明示構成）。total は不可（§3.1・両案共通の原理的限界） | ∃ 形（安定値 witness）。同上 |
| **完備性** | **modulus 形で choice-free に本物証明可**（レベルごと極限構成） | 二重完備化・未解決（M316F honest） |
| 既存資産との接続 | zpUnits/zpDivP/teich/LT を直接消費 | 断絶（別担体） |
| 工数 | 新規 3–4 ファイル・全て確立イディオム | 新規 4–5 ファイル＋体化・完備性は原理的に閉じない |

(B) は**捨てない**: 実 (ℚ,v₃) の valRingValuation インスタンス化＋「K̂(ℚ,v₃) ≅ ℚ₃」比較定理は、
M301F–M316F 機構の「実例が自明」限定を discharge する後続候補（A2d・範囲外・§7.5）として保存。

---

## 2. A2a: ℤ₃ の局所体パッケージ — `IUT/Zp3ValuationRing.lean`（prefix `z3v`）

依存: `IUT.Ring`（zpRing）・`IUT.ZpUnits`・`IUT.PadicDivision`・`IUT.ResidueField`・`IUT.Fermat`
（isPrime_three）。tier **M（opus）**。全て choice-free（新規 Classical.choice 禁止）。

### 2.1 主語の固定と非退化

```lean
@[reducible] def z3 : CRing := zpRing 3            -- 実 ℤ₃（既設の逆極限環・p=3 固定）
theorem z3_zero_ne_one : z3.zero ≠ z3.one
-- レベル 1 で分離: 等しいなら quot_exact intGrp (modCong 3) で 3 ∣ 1 − 0、omega で矛盾。
-- toZp_injective 3 (by omega) の写経でも可。
```

### 2.2 付値の関係形（★設計判断: 付値は「関数」でなく「関係」で持つ）

ℤ₃ の元 x の付値 v(x) を **Nat 値関数にしない**（v(0)=∞ で総関数化に Option/ダミーが要り、
かつ任意 x の v 計算は非零判定＝非可判定を含む）。代わりに**レベル述語**で持つ:

```lean
def z3vGe (x : z3.carrier) (n : Nat) : Prop :=        -- v(x) ≥ n ⟺ x ≡ 0 mod 3ⁿ
  x.val n = (zmod (3 ^ n)).one                        -- zmod の one = 加法単位 [0]
def z3vExact (x : z3.carrier) (n : Nat) : Prop := z3vGe x n ∧ ¬ z3vGe x (n + 1)
theorem z3vGe_antitone : m ≤ n → z3vGe x n → z3vGe x m      -- 整合族の遷移で即
theorem z3vGe_zero_all : ∀ n, z3vGe z3.zero n
theorem z3vGe_add : z3vGe x n → z3vGe y n → z3vGe (z3.add x y) n   -- 成分計算
```

これは M301F の超距離公理を**選言形すら経由せず**レベルごとの等式に落とした、逆極限
モデル固有の忠実版（超距離 v(x+y)≥min は z3vGe_add がその内容）。

### 2.3 因数分解 x = 3^v·u（★本ファイルの中核・Hensel 帰納の写経）

```lean
theorem z3v_unit_of_lev1 (x) (h : ¬ z3vGe x 1) : IsZpUnit 3 x
-- x.val 1 を Quot.ind で [a] に開き、3∣a なら Quot.sound で x.val 1 = [0] と矛盾。
theorem z3v_extract : ∀ (n : Nat) (x : z3.carrier), ¬ z3vGe x (n + 1) →
    ∃ (v : Nat) (u : z3.carrier), v ≤ n ∧ IsZpUnit 3 u ∧
      x = z3.mul (zpPow 3 (toZp3 3) v) u ∧ z3vExact x v
-- n の強帰納。項レベル判定 `x.val 1 = [0]?`（レベル1のゼロ判定は
-- Quot.lift (fun a => a % 3 == 0) の Bool 化 or `zp_dvd_p_iff` の右辺の Decidable 化）:
--   ・非零枝: v=0, u=x（z3v_unit_of_lev1）。
--   ・零枝: zp_dvd_p_iff で x = 3·e（e := zpDivP 3 _ x・関数！ ∃ 取り出し不要）、
--     補題 z3v_shift: (3·e).val (k+1) の零性 ⟺ e.val k の零性（zpDivP_cancel の簿記）で
--     ¬ z3vGe e n を得て帰納。witness は再帰構成＝choice-free。
theorem z3v_exact_mul : z3vExact x a → z3vExact y b → z3vExact (z3.mul x y) (a + b)
-- extract で x=3^a u, y=3^b w に開き、uw は isZpUnit_mul、3^{a+b}·単数 の exact 付値
-- （単数のレベル1非零 + zp_p_regular の反復 z3v_pow_regular）で閉じる。
theorem z3v_domain_pos : ¬ z3vGe x (n+1) → ¬ z3vGe y (m+1) → ¬ z3vGe (z3.mul x y) (n+m+1)
-- 整域性の「正の witness 形」（v(xy) = v(x)+v(y) ≤ n+m の系）。
-- 否定形 x≠0→y≠0→xy≠0 は witness 抽出に Markov を要するため採らない（§3.1）。
```

### 2.4 極大イデアル 3ℤ₃・局所環性・剰余体 𝔽₃

```lean
def z3vMax : primeSpecIdeal z3 where          -- m = ker(proj 1) = 3ℤ₃ = {v ≥ 1}
  mem x := z3vGe x 1
  zero_mem := …  ; add_mem := z3vGe_add … ; smul_mem := …   -- 全て成分計算
def z3vMaximal : resFieldMaximal z3 where
  toprimeSpecIdeal := z3vMax
  proper := …                                  -- 1.val 1 = [1] ≠ [0]（3∤1）
  maximal_witness := fun x hx =>
    ⟨zpUnitInv 3 isPrime_three x (z3v_unit_of_lev1 x hx), z3.zero,
     z3vGe_zero_all 1, by rw [add_zero 化] ; exact zpUnitInv_mul …⟩
-- ★witness 形極大性が r = 明示逆元・s = 0 で「即納」——M295F 機構への初の非自明実例代入。
def z3vResidue : CRing := resFieldQuot z3vMax          -- ℤ₃/3ℤ₃
def z3vResToF3   : RingHom z3vResidue (zmodRing 3)     -- Quot.lift (fun x => x.val 1)
def z3vF3ToRes   : RingHom (zmodRing 3) z3vResidue     -- Quot.lift (fun a => [toZp a])
theorem z3v_res_iso : 左右逆（両合成が恒等）            -- MuUnitsIsoData 型レコードで束ねる
-- well-defined: 差が m₃ ⟺ レベル1一致 ⟺ 3 ∣ 代表差（quot_exact / Quot.sound の往復）。
```

**成果の意味（本物性）**: 「ℤ₃ は極大イデアル 3ℤ₃・剰余体 𝔽₃ を持つ局所環で、単数群は
O∖m、任意の非零 witness 付き元は 3^v·単数」＝ **DVR の実内容が実 ℤ₃ の上で閉じる**。
M301F の抽象 valRingValuation の「具体的な離散付値の構成は後続」を初 discharge する実例。

### 2.5 併設ファイル: 𝔽₃ の体化 — `IUT/F3Field.lean`（prefix `f3`・依存: Ring のみ・tier S〜M）

```lean
def f3Field : IUTField where          -- 台 = zmodRing 3・コードベース初の有限 IUTField
  …(zmodRing 3 の環部)…
  inv := fun x => x                   -- ★総 inv = 恒等！ 3∤a ⟹ a² ≡ 1 (mod 3)
  mul_inv_cancel := …                 -- 代表 a を Quot.ind で開き a%3 ∈ {1,2} の
                                      -- Int emod 簿記（a²−1 = (a−1)(a+1)・3∣ どちらか）
  inv_zero := rfl ; zero_ne_one := …  -- 3∤1
```
x⁻¹ = x は p=3 特有（(ℤ/3)^× = {±1}・位数 2）で総 inv が**判定不要で書ける**。剰余体が
本物の IUTField になる＝A2a の剰余体・柱B の局所体剰余体の共用部品。A2a と独立に並列可。

---

## 3. choice-free 性の厳密な線引き（正直申告・実装ヘッダに転記すべき内容）

### 3.1 total inv は（どちらの構成でも）choice-free 不可能 — 恒久的 honest 限定

ℚ₃ の元 x の逆元計算は v(x)（最初の非零レベル）の特定を要する。仮定 x ≠ 0 は
¬(∀n, x.val n = [0]) という**否定形**であり、そこから witness n を取り出すのは
Markov 原理（≒排中律の断片）で、Lean の choice-free 断片では**関数として書けない**
（構成的数学の標準事実: ℚ_p は構成的には離散体でない）。よって:
- **IUTField（total inv）としての ℚ₃ は本設計では主張しない**（Classical.choice 解禁は
  規則違反で却下・§7.3）。
- choice-free の忠実版は「**正の非零 witness（∃n, x.val n ≠ [0]・apartness x # 0）を
  渡された元の逆元を明示構成する ∃ 形**」であり、これは pvqVal の「非零代表上の付値が
  choice なし忠実版」・RingLocalization honest 2「witness 形が本来の姿」・A1 旧 Quot 表示の
  ∃ 形逆元と同じ正直ラインである。**この限定は消去・弱化しない**。

### 3.2 完備性は modulus 形なら choice-free（(A) 採用の決め手）

- **本物で閉じる**: modulus 付き Cauchy 列（M : Nat → Nat 明示）の極限の存在・収束・
  一意性（§4 A2b）。極限はレベルごとの閉じた式で、選択ゼロ。
- **閉じない（正直に後続）**: ∃ 形 Cauchy（∀n∃N…）からの modulus 抽出（可算選択）・
  位相空間論としての「全ての Cauchy フィルターが収束」。位相そのものは
  `limitTopology (padicSystem 3)`（既設・コンパクト性 Zp_compact も既設）が実体。

### 3.3 その他の限定（過大主張防止・実装ヘッダ必載）

p = 3 固定（一般素数 p は zpRing p 一般で書ける部分はなるべく p 一般で書く——zpUnits 系は
既に p 一般なので z3v も可能な限り `(p) (hp : IsPrime p)` 一般で書き、ℚ₃ 実例は p=3 で
非空虚検算する）。基礎体は ℚ のみ（一般数体 K の K_v は A1 の一般体 × 本設計の合成・後続）。
ℚ₃ 上の位相・G_{ℚ₃}・分岐理論は範囲外（B1 の射程）。

---

## 4. A2b: ℤ₃ の完備性 — `IUT/Zp3Complete.lean`（prefix `z3c`）

依存: A2a（z3vGe）＋ `IUT.PadicValuationQ`。tier **M（opus）**。

```lean
def z3cIsModCauchy (x : Nat → z3.carrier) (M : Nat → Nat) : Prop :=
  ∀ n i j, M n ≤ i → M n ≤ j → (x i).val n = (x j).val n
def z3cModUp (M : Nat → Nat) : Nat → Nat            -- 単調化 M' n := max (M n) (M' (n−1))
def z3cLim (x) (M) (h : z3cIsModCauchy x M) : z3.carrier :=
  ⟨fun n => (x (z3cModUp M n)).val n, …⟩
-- 整合性: i ≤ j に対し t (x (M' j)).val j = (x (M' j)).val i（族 x_{M' j} の整合性）
--         = (x (M' i)).val i（M' i ≤ M' j と Cauchy 性）。閉じた式・choice ゼロ。
theorem z3c_converges : ∀ n i, z3cModUp M n ≤ i → z3vGe (z3.add (x i) (z3.neg (z3cLim …))) n
-- 「v(xᵢ − lim) ≥ n」＝収束のレベル形。減算の成分簿記のみ。
theorem z3c_lim_unique : (∀ n, ∃ N, ∀ i ≥ N, z3vGe (xᵢ − l) n) → 同 l' → l = l'
-- 分離性（Subtype.ext + レベルごとの一致）。∃ は仮定側なので取り出し不要（Prop 消費）。
theorem z3c_int_dense : ∀ (x : z3.carrier) (n : Nat), ∃ a : Int, z3vGe (x − toZp a) n
-- 「ℤ は ℤ₃ で稠密」＝ℤ₃ が ℤ の完備化であることの残り半分。witness は x.val n の代表。
theorem z3c_val_compat (a : Int) (ha : a ≠ 0) :
    z3vExact ((toZpRing 3).map a) (pvqNatVal 3 a.natAbs)
-- ★実 ℚ 側の実付値（pvq・本物）と ℤ₃ 内の付値の一致。pvqNatVal_spec で a = ±3^k·n'
-- （3∤n'）に開き、z3v_exact_mul + 単数性 isZpUnit_teich 型の簿記で閉じる。
-- ——依頼文の「既存の p 進付値機構（本物）と完備化体（模型）の境界」を接着する定理。
```

**成果の意味**: A2 タイトルの「完備化」が初めて定理になる——「ℤ₃ は（modulus 形で）完備、
ℤ が稠密、ℚ 側の実 v₃ と両立」。これで ℤ₃ は「ℤ の 3 進完備化」という**関係ごと**本物。

---

## 5. A2c: 体 ℚ₃ — `IUT/Q3LocalField.lean`（prefix `q3f`）

依存: A2a ＋ `IUT.RingLocalization`。tier **M（opus）**。

```lean
def q3fThree : z3.carrier := (toZpRing 3).map 3
def q3Ring : CRing := ringLocRf z3 q3fThree                    -- ★ℚ₃ = ℤ₃[1/3]・実例代入
theorem q3f_zero_ne_one : q3Ring.zero ≠ q3Ring.one
-- ringLocRel (1,1) (0,1) なら ∃k, 3^k·1 = 0——z3v_pow_regular（zp_p_regular 反復）と
-- z3_zero_ne_one で矛盾。局所化の非退化は 3 冪の正則性そのもの。
theorem q3f_embed_inj : (ringLocMap z3 (ringLocPowers z3 q3fThree)).map の単射性
-- 同上（t·(a−b)=0, t=3^k ⟹ a=b）。ℤ₃ ↪ ℚ₃。
theorem q3f_three_unit : ∃ y, q3Ring.mul [3/1] y = q3Ring.one   -- ringLoc_unit_of_S 適用
theorem q3f_uniformizer : z3vExact q3fThree 1 ∧ ¬ IsZpUnit 3 q3fThree
-- 「3 は ℤ₃ の素元・ℚ₃ で可逆」＝uniformizer の実内容。
theorem q3f_has_inverses :                                      -- ★∃ 形体性（§3.1 の忠実版）
    ∀ (a : z3.carrier) (n k : Nat), ¬ z3vGe a (k + 1) →
      ∃ y, q3Ring.mul (mk (a, 3^n)) y = q3Ring.one
-- z3v_extract で a = 3^v·u（v≤k・u 単数）→ y := mk (3^n · zpUnitInv u, 3^v)。
-- 検算: (3^v u·3^n u⁻¹) / (3^n·3^v) = 3^{v+n}/3^{n+v} = 1（ringLocRel・witness t=1）。
def q3fValRel (x : q3Ring.carrier) (κ : Int) : Prop :=          -- 付値の関係形（ℤ 値）
    ∃ a n v, x = mk (a, 3^n) ∧ z3vExact a v ∧ κ = (v : Int) - n
theorem q3f_val_wd : q3fValRel x κ → q3fValRel x κ' → κ = κ'    -- 代表非依存
-- 交差積 3^m a = 3^n b に z3v_exact_mul と 3 の exact=1 を当て v+m = w+n。
theorem q3f_val_mul : q3fValRel x κ → q3fValRel y λ → q3fValRel (x·y) (κ+λ)
theorem q3f_ring_of_val : q3fValRel x κ → 0 ≤ κ → ∃ c : z3.carrier, x = mk (c, 3^0)
-- O = {v≥0} = ℤ₃ の像（⊇ 側は zpDivP の n 回反復で分子から 3^n を剥がす）。
```

### 5.1 A2c-2（同ラウンド並列可・別ファイル `IUT/Q3UnitsGroup.lean`・prefix `q3u`・tier M）

`FullReciprocity.lean:64` の代理 `prodGrp intGrp (zpUnits 3 …)`（K^× の抽象直積）を
実 ℚ₃^× へ昇格する §2(a): 準同型 `(k, u) ↦ [3^k·u]`（k<0 は分母側）が単射
（q3f_val_wd で v=k を分離・単数部は q3f_embed_inj）かつ積保存であることを示し、
「ℚ₃^× ⊇ 3^ℤ × ℤ₃^×（実現形）」を初めて実体上で与える。全射性は像の特徴付け
（非零 witness 付き元は全て 3^κ·単数形＝q3f_has_inverses の副産物）として ∃ 形で。
**A8（Tate 曲線 K^×/q^ℤ を実 ℚ₃^× 上で・v(q)≥1 の実 q）と B2（相互写像の主語）の
ブロッカー解消はこのファイルが直接の接点**。

### 5.2 A2c-3（範囲外・後続に明記）: ℚ ↪ ℚ₃

den = ±3^w·d'（3∤d'）分解＋d' の単数逆元で `ratRing → q3Ring` の環準同型は書けるが、
ratRel 上の well-defined 簿記が重く 0.65 到達に不要のため後続（A2 0.65→0.7 の主部品）。

---

## 6. 段階分解・status 寄与・柱A% 効果（保守見積り・確定は独立監査）

依存 DAG と並列プラン（5 並列規則との整合）:

```
f3 (𝔽₃ 体化・独立)      ┐
z3v (A2a・中核)  ────────┼──→ z3c (A2b)   ┐ 並列
                         └──→ q3f (A2c)   ┤
                              q3u (A2c-2) ┘ (q3f と同時起動可・q3f の mk 簿記を共有するなら直列)
```

ラウンド 1: **z3v（opus）+ f3（sonnet〜opus）並列**。ラウンド 2: **z3c（opus）+ q3f（opus）
+ q3u（opus）並列**（q3u は q3f 完了待ちにするなら z3c とだけ並列＋残枠は他柱 tier-S）。

| 段階 | 内容 | A2 status（保守） | 柱A Σ(w·s) | 柱A% |
|---|---|---|---|---|
| 現状 | 機構実・実例自明（M301F–M316F）・ℤ_p 環は柱B 文脈に散在 | 0.50 | 44.7 | 45 |
| A2a+f3 | 実 ℤ₃ の局所体パッケージ（付値関係・3^v·u 分解・極大イデアル・剰余体 𝔽₃ 同型・𝔽₃ IUTField） | **0.55** | 45.1 | **45（据え置き）** |
| +A2b | 完備性（modulus 形・choice-free）・ℤ 稠密・実 pvq 付値との一致 | **0.60** | 45.5 | **46 は丸め境界ちょうど（下記注意）** |
| +A2c(+c-2) | **体 ℚ₃ = ℤ₃[1/3] 実構成**・∃ 形体性・uniformizer・ℤ 値付値・O=ℤ₃・K^× 昇格 | **0.65** | 45.9 | **46（安全圏）** |

**丸め境界の正直な注意**: Σ=45.5 は `round()`（banker's）で 46 になるが、浮動小数の
和の順序次第で 45.499… に落ち得る**不安定な境界**。よって**柱A 45→46 の報告は A2c 監査
確定後に行う**のが正直（A2a のみのラウンドは「complete_pct 柱% 据え置き（status は
0.5→0.55 前進）」と明記する）。0.65 の上限根拠（敵対的監査を先取り）: total inv 不可
（§3.1・恒久 honest）・p=3/基礎体ℚ 固定・ℚ₃ の位相/Galois 側 G_{ℚ₃} 未構成・
∃形 Cauchy 完備性未達・ℚ↪ℚ₃ 未接続（A2c-3）。**0.7 以上は A2c-3＋(A2d: M311F 機構との
比較定理 or 位相)を要する**。

各実装ヘッダには規則 §1 の二軸（[実／昇格(a)] または [実／本物建設(b)]・complete_pct 影響）と
§3 の honest 限定を必載。監査は AUDIT_RUBRIC 準拠（bash build.sh EXIT=0・no sorry・
新規全対象 `#print axioms` = [propext, Quot.sound]・新規 Classical.choice 皆無・
禁止タクティク不使用——z3v_extract の項レベル ite は zpuInv 前例で許容範囲）。

---

## 7. 却下案・境界判断（degenerate 回避の記録）

1. **(B) Cauchy 商を主経路にする**: §1.1 で却下（完備性・体化が閉じず、既存 ℤ₃ 資産と断絶）。
2. **汎用 limitRing（InverseSystem の環版）の新設**: 不要——zpRing が成分ごと乗法で既に
   環化済み。共有インフラ（Profinite.lean）の改変はリスクのみで complete_pct を動かさない。
3. **Classical.choice を解禁して IUTField ℚ₃ を作る**: 規則違反（新規 choice 禁止）で却下。
   ∃ 形＋正の witness が構成的に忠実な体性（§3.1）。
4. **Frac(ℤ₃)（分数体）で ℚ₃ を作る**: 数学的には ℤ₃[1/3] と同型だが、分母が「任意の非零
   witness 付き元」になり witness 簿記が全演算に伝播して重い。m=(3) の DVR では 3 冪分母で
   十分（任意の非零元 = 3^v·単数・単数は分母に不要）。局所化案が厳密に軽い。
5. **正規形担体（Option (Int × 単数)) で total inv を狙う**: 乗法・逆元は閉じるが**加法が
   書けない**——v が等しい 2 元の和 3^k(u+w) は u+w の付値特定（非可判定）を要する。却下。
   （＝total inv 不可能性 §3.1 の担体取り替えによる回避も不成立、という裏取り。）
6. **zps/zpu（Nat subtype 系 ℤ₃^×）との同型橋を A2 に含める**: 担体表現の interop であり
   A2 の completeness/体性を進めない。後続（cli 系が要求した時点）に送る。
7. **fldCompTrivField（自明付値の K̂）を「ℚ₃ の実例」と称する**: 自明付値では K̂=K で
   p 進内容ゼロ＝toy 主語。却下（§3 規則）。

---

## 8. HELP スポット（実装枠が詰まったら fable に回す点・予告）

- z3v_extract の再帰での「x = 3·e への witness 伝播」（z3v_shift の Quot 二重簿記）。
- resFieldQuot ↔ zmodRing 3 の双方向 RingHom の well-defined（quot_exact の往復の向き）。
- ringLocRel の witness t の正規化（t = 3^k 形の取り扱い・ringLocRel_iff_sub との往復）。
- f3 の a%3 ∈ {1,2} 分岐の Int emod 簿記（omega 到達形に落とす整形）。
