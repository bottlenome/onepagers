# 柱A 次の最小 complete_pct 前進ステップ — 実円分機構（cmr/cgar/cra/tmz・ctl/cli/zps）の最有効活用先のスコープ設計

日付: 2026-07-10 ／ 種別: **設計ドキュメントのみ**（実装コード無し・共有ファイル不更新）
分類: **[実／昇格(a) の設計]** — 今セッション完成の実円分機構＋実円分剛性（A7 0→0.35）を
土台に、A2/A4/A6/A8 のどれが「実 IUT 完全証明率を最も上げる 1 手」かを実測比較し、
選定した **A6（mono-anabelian 復元・w14）** の最小前進ステップを opus 実装枠に渡せる
粒度（新規ファイル・prefix・主要シグネチャ・依存・tier・段階順）へ分解する。
**complete_pct 影響: 本ドキュメント自体は 0（設計のみ）**。実装マイルストーンの
status 見積りは §6（保守値・最終確定は独立監査・AUDIT_RUBRIC 準拠）。

---

## 0. 現状の実測（本日 read/grep 済み）

### 0.1 台帳（`target_ledger.json`・本日実測）

A1=0.85(w8)・A2=0.5(w8)・A3=0.75(w12)・A4=0.5(w14)・A5=0(w10)・A6=0.5(w14)・
A7=**0.35**(w12・本日独立監査確定)・A8=0.5(w12)・A9=0(w10)。
Σ(w·s) = 6.8+4+9+7+0+7+4.2+6+0 = **44.0**/100 → 柱A complete_pct **44**
（`tools/compute_complete_pct.py` の round(Σ(w·s)/Σw·100)・graph-meta.json と整合確認済み）。

**丸めの位置が重要**: Σ=44.0 ちょうどのため、**Σ を +0.5 以上動かす最小の一手で柱A% が
44→45 に前進する**。w14 項目なら status +0.05 で +0.7、w8 項目でも +0.1 で +0.8。

### 0.2 今セッション完成の実機構（全て本物・choice-free・`#print axioms`=[propext,Quot.sound]）

| 資産 | 実在シグネチャ（本日確認） | 本設計での意味 |
|---|---|---|
| 実円分塔 | `cteField ℓ hℓ`=ℚ(ζ_{3^ℓ})=ℚ[x]/(Φ_{3^ℓ})・`cteIota`（x̄↦x̄³）・`ctmZeta/ctmFind/ctmFind_spec`・`cae_aut_ext`・`csaAut`・`ctrResHom/ctr_surjective` | 実体・実 μ 素材・実 Gal |
| 実逆極限 G | `ctlProfinite`=lim Gal(ℚ(ζ_{3^{n+1}})/ℚ)（`CyclotomicTowerLimit.lean`・ProfinitePi1Tower witness 初 discharge 済み） | 実 profinite Galois 群 |
| 指標同型 | `cciIsoData`（各段 Gal≅(ℤ/3^ℓ)^×）・`cliChar/cli_res_char/cliIsoData`（極限 Gal≅ℤ₃^×）・`zpuGrp/zpuInv`・`zpsLimit`=ℤ₃^× | χ の双方向同型・mod 簿記 |
| 実円分剛性 A7 | `cmrMu ℓ hℓ : CycMuGroup`（実 μ_{3^ℓ}⊂ℚ(ζ_{3^ℓ})・log=ctmFind）・`cgarAct : CycGKAction (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ)`（実 Gal の実作用）・`cgar_exp_eq`（cycRigExp=ctr_charG）・`cgar_nontrivial`（χ(σ₂)=2≠1）・`cgar_rigidity`・`cgarRecChar ℓ hℓ : cycRecCharacter (galoisGroupGrp (cteExt ℓ hℓ)) (3^ℓ)`（M334F 入力の実 witness・CGAR-6）・`cra_*`（Gal≅Aut(μ)・cra_indeterminacy）・`tmzLimit`=ℤ₃(1)（実 μ 塔逆極限・`tmz_act_char`・`tmz_iota_cube`） | **cgarRecChar は既に M334F `cycRecCharacter` 型で供給済み**——A6 復元機構の入口に実 χ が刺さっている |

### 0.3 A6 側の既存資産（本日精読・何が本物で何が退化か）

| モジュール | 本物の部分 | 退化/外部仮定（complete_note「実例が自明/退化」の実体） |
|---|---|---|
| `CyclotomeRecovery.lean`（M334F・cycRec） | χ:G_K→(ℤ/n)^× から μ̂=(ℤ/n, χ 捻り) を復元・剛性同型・変 n 両立 `cycRecCharTrans`・capstone (K^×,v,χ)→(体+円分体) | (i) 実例 `cycRecGaloisCyclotome` は **trivial χ≡1**（M334F-9 正直申告「非自明 χ を与える実 Galois 降下は柱A/E 後続」——**cgarRecChar で入力は昇格済みだが消費者側の実インスタンスは未**）。(ii) **`cycRecGeoCompatible`（復元 μ̂ ≅ 真の幾何 μ_n の G_K-同変一致）は外部仮説として受領のみ・「決して導出しない」**（`cycRec_geo_recovery_hypothesis` :224） |
| `AbsTopFieldRecover.lean`（M329F・absF） | 乗法+付値→加法→環→元の体の復元ループ（本物・実 K 上） | χ の台は抽象 `CycGKAction`・実例は trivial 付値 |
| `AbsTopFieldFromCyclotome.lean`（M409F）・`AbsTopFullRecovery.lean`（M414F） | χ 同定橋・AbsTopI/II/III 統合 capstone（本物の束ね） | π₁^ét からの抽出は外部仮説 `atmPi1ReconHypothesis`・実例は G_ℚ trivial |
| `CyclotomeIdentification.lean`（M443F・cid） | `cidIso M N`（位数の等しい任意の 2 CycMuGroup 間の明示同型・左右逆）・**`cid_galois_equivariant`**（両側の作用の mod-n 指数が一致すれば cmuMap は G-同変） | A 側 Zp p の ζ の **hζl・hdist は外部仮定**・E.n=l も外部 |
| `KummerCharReal.lean`（M349F・kcr） | κ_α(σ)=σ(α)/α 実コサイクル | 準同型性は `htriv` 外部仮説・n 乗根存在も外部（A7 詳細化 §4 で A6/E4 境界と判定済み） |

---

## 1. 候補 A6: mono-anabelian 復元（w14・0.5→?）——**円分剛性の自然な次消費者（本命）**

### 1.1 grep 裏取り: どこが模型・どこを本物置換できるか

- 復元機構そのもの（M334F/M329F/M409F/M414F）は「機構は実」——復元式・剛性同型・
  capstone は本物の定理。**退化しているのは実例と外部仮説の 2 点**:
  1. **実例が trivial χ≡1**（`cycRecGaloisCyclotome`）: 復元 μ̂ の作用が恒等になる
     退化ケースのみ。非自明 χ での実インスタンスが無い。
  2. **`cycRecGeoCompatible` が外部仮説**: 「復元 μ̂ が真の幾何的 μ_n と G_K-同変に
     一致する」——mono-anabelian 復元の**核心命題**が仮説受領のまま（M334F 自身が
     「決して導出しない」と正直申告）。
- **今セッションの機構がこの両方を一挙に閉じる部品を既に持つ**:
  - 非自明 χ = `cgarRecChar`（既に `cycRecCharacter` 型・χ(σ₂)=2≠1）。
  - 真の幾何側 witness = `cmrMu`（実 μ_{3^ℓ}⊂ℚ(ζ_{3^ℓ})）＋ `cgarAct`（実 Gal の実作用）。
  - 同変同定の道具 = M443F `cidIso`＋`cid_galois_equivariant`（**再証明不要・供給するだけ**）。
    hchar 前提（両側指数の mod-n 一致）は `cgar_exp_eq`＋log 計算で落ちる。
- すなわち: **「実 χ から復元した μ̂(χ) が、実円分体の中の実 μ_{3^ℓ} と G-同変同型」**という
  mono-anabelian 円分体復元の忠実な部分ケース（AbsTopIII の cyclotome 復元ステップの実内容）が、
  **新イディオムゼロの組み立て**で定理になる。`cycRecGeoCompatible` は仮説でなく
  **定理として discharge** される（μ⊂K̄ でなく μ⊂ℚ(ζ) 自身という正直な限定つき・§8）。

### 1.2 cid（hζl/hdist）discharge 案の却下（正直な線引き）

A7 詳細化 §0.1 が後続候補に挙げた「cmrMu で M443F cid の外部仮定 hζl/hdist を discharge」は
**本ラウンドでは不成立**と判定する: cid の A 側は `ζ : (Zp p).carrier`（実 ℤ_p の元）に
ハードコードされており、p=3 では μ_{3^ℓ}(ℚ₃)=1（Teichmüller 根の位数は p−1=2）——
**実 ℤ₃ に位数 3^ℓ の実 ζ は存在しない**。実 discharge には p≡1 (mod 3^ℓ) の素数と
Hensel/Teichmüller 持ち上げの実装（重い・別ターゲット）が必要。degenerate な仮定充填で
「閉じた」ことにするのは §3 toy 主語禁止に反するため却下。cmrMu が供給できるのは
**E 側**（`E : CycMuGroup, E.n=l`）のみで、それは §6 の crr 設計に吸収する。

### 1.3 相対 Kummer 案（A7 詳細化 §4 の後続候補 (b)）との比較

相対 Kummer κ: Gal(ℚ(ζ_{3^{ℓ+1}})/ℚ(ζ_{3^ℓ}))→μ₃ は本物の A6 寄与だが、**新機構
「相対 Galois 部分群」**（ι の像を各点固定する実部分群・その群構造・M349F htriv/hfix の
部分ケース discharge）をゼロから要する（400 行級＋新イディオム 1）。一方 §1.1 の
geo-discharge は**全部品が既存**で同工数帯・リスク小・「復元の核心仮説を定理化」という
status 直撃点を突く。**相対 Kummer は A6 第 2 波に回す**（本設計 §6.4 に後続として名指し）。

- 工数: 350–500 行（1 ファイル）＋任意の塔整合 400–600 行（第 2 ファイル）。tier **M（opus）**。
- status 見積り（保守）: 0.5 → **0.55**（+塔整合で 0.6）。柱A%: **44→45（+1）**。
- 依存: cgar・cmr・cid・cycRec・（塔整合は cli・tmz・ctl）。全て存在確認済み。

## 2. 候補 A4: 実 π₁^ét（w14・0.5→?）——**二重計上リスクで次点**

- 既存資産: `ProfinitePi1.lean`（M287F・lim Gal(Lᵢ/K) の逆極限＋副有限位相・実例は
  **自明塔 lim Gal(ℚ/ℚ)=1**）・`GaloisPi1Iso.lean`（M286F・Gal≅π₁ 像は **2 根被覆のみ**）・
  `GrothendieckGalois`（π₁=Aut(F)・profPi1_toPiEt は骨組み）。
- **ctlProfinite は既に ProfinitePi1Tower.restr/restr_self/restr_comp witness を discharge 済み**
  （2026-07-10 A3 M3 ラウンド・graph-meta A3 注記に明記・**A3 0.65→0.7 の監査根拠として
  消費済み**）。つまり「ctlProfinite を M287F の非自明実例として接続する」だけの一手は、
  独立監査に **A3 成果の A6/A4 への再ラベル（二重計上）**と判定される可能性が高い。
- A4 を正直に動かす最小の一手は**被覆圏側**: 円分被覆 Spec ℚ(ζ_{3^ℓ})→Spec ℚ の
  ファイバー（Φ_{3^ℓ} の根の集合）への Gal 作用の推移性＝**Φ_{3^ℓ} の全 φ(3^ℓ) 根が
  ℚ(ζ_{3^ℓ}) 内で ζ^a（gcd(a,3)=1）として尽くされる**こと（Φ_{3^ℓ}(ζ^a)=0 の実証明——
  X^{3^ℓ}−1=(X^{3^{ℓ−1}}−1)·Φ_{3^ℓ} の多項式分解の新イディオムが必要）＋連結ファイバー
  関手 F との一致 profPi1_toPiEt の非自明化。工数 600–900 行・fable スポット 1
  （根の分解イディオム）。status 0.5→0.55 見込みだが上記リスクで**割引**。
- 判定: **次点**。A6 完了後、「Aut(F)≅ctlProfinite の円分部分ケース」として独立の
  被覆圏成果に切り出すのが正順（双曲的曲線 π₁ は依然遠い——honest）。

## 3. 候補 A8: Tate 曲線の実被覆・cuspidalization（w12・0.5→?）——**A2 ブロッカーで保留**

- 既存資産: `TateCurve.lean`（M309F・E_q=K^×/q^ℤ 実商群・**K は抽象 IUTField**）・
  `TateTorsion.lean`（M314F・E_q[n] 実部分群・μ_n⊆E_q[n]・**位数言明 M314F-5 は付値 v を
  外部入力**）・TateCover 系（被覆圏の Galois 圏化・A-3β 済み）。
- 円分剛性の接続先は明確: K:=`cteField ℓ hℓ`（実 ℚ(ζ_{3^ℓ})）・q:=3 で **E_q の実
  インスタンス**を建て、`cmrMu` が μ_{3^ℓ}⊆E_q[3^ℓ] の実体を、`cgarAct` が捻れ点への
  実 Galois 作用を供給する——1→μ_{3^ℓ}→E_q[3^ℓ]→ℤ/3^ℓ→1 の μ 側が実で立つ。
- **ブロッカー 2 点**: (i) q=3 の非捻れ性（3^n≠1）は ℚ 部分体算術で落ちる見込みだが、
  M314F-5 の**位数ちょうど言明は実離散付値 v を要求**——実 ℚ(ζ_{3^ℓ}) 上の 3 進付値
  （λ=ζ−1 の Eisenstein 付値）は**未構成**（A2/柱B の残欠がそのまま刺さる）。
  (ii) q^{1/3^ℓ} 方向（ℤ/3^ℓ 商側）は体拡大の新設が必要で重い。cuspidalization は
  さらに先（被覆の関手性・基点込み）。
- 判定: **保留**。μ 側だけの実インスタンス（400–600 行・M）は可能だが、位数・完全列が
  半分外部仮定のまま残り、監査で 0.5→0.55 に届くか不確実。**A2（実付値/実局所体）が
  先に立つと一挙に本物化する**——順序依存。

## 4. 候補 A2: 実 p 進局所体 K_v（w8・0.5→?）——**独立・重い・weight 最小**

- 既存資産: `Zp p := limitGrp (padicSystem p)`（実 ℤ_p **加法群**・LocalCFT.lean:90）・
  `ZpDomain.lean`（witness 付き零因子なし・付値分解 x=p^k·u・choice-free）・
  `ZpUnits/ZpUnitDecomp`・今セッションの `zpuGrp`（(ℤ/3^ℓ)^× Hensel 逆元）・`zpsLimit`（ℤ₃^×）。
  完備化機構（M306F/M311F/M316F）は「実だが実例は自明付値」。
- 最小の実ステップ: ℤ₃ の CRing 化（成分ごと乗法・padicSystem の環準同型性）→
  実 ℚ₃=Frac(ℤ₃) の IUTField 化（witness 付き整域性 ZpDomain を利用・分数体機構
  FractionField.lean と接続）→ 3 進付値 v₃ の実装。工数 800 行級×2 段・M×2。
- zpu/zps の流用度: zpsT の「指数読み替え遷移」イディオムと Hensel 逆元 `zpuInv` は
  ℤ₃^×（乗法）側の部品としてそのまま効くが、**環化・分数体・付値の本体は新規建設(b)**。
- status 0.5→0.65 見込み（+1.2→45.2→45・+1）だが**工数最大・weight 最小（8）**。
  ただし A6-AbsTopIII の実付値入力・A8 の位数言明・柱B の実例という**下流 3 件の
  ブロッカー解消**という戦略価値は大きい——**A6 の次ラウンド以降の本命候補**として名指し。

---

## 5. 総合判定（比較表）

| 候補 | w | 今回機構の活用度 | 最小実ステップ | 工数/tier | status 見積(保守) | 柱A% | リスク |
|---|---|---|---|---|---|---|---|
| **A6** | 14 | **★直接消費者**（cgarRecChar が M334F 入力に接続済み・cmrMu/cgarAct が幾何側 witness・cidIso/cid_galois_equivariant 再利用） | `cycRecGeoCompatible` の実 discharge＋μ̂(実χ)≅実μ_{3^ℓ} の G-同変同型 | 350–500 [M] | 0.5→**0.55** | **44→45 (+1)** | ほぼ無し（新イディオム 0） |
| A4 | 14 | 中（ctlProfinite の witness discharge は A3 監査で消費済み） | Aut(F)≅ctlProfinite の円分部分ケース（Φ の根分解） | 600–900 [M+fable1] | 0.5→0.55（割引あり） | +1 or 0 | **A3 二重計上判定**・根分解の新イディオム |
| A8 | 12 | 中（cmr/cgar が μ 側捻れを供給） | E_q over 実 ℚ(ζ_{3^ℓ})・q=3 の実インスタンス＋実 μ 捻れ | 400–600 [M] | 0.5→0.55 不確実 | +1 or 0 | **実付値不在**（M314F-5 が外部仮定のまま）・A2 順序依存 |
| A2 | 8 | 弱–中（zpu/zps は乗法側部品のみ） | ℤ₃ CRing 化→実 ℚ₃ IUTField→v₃ | 800×2 [M×2] | 0.5→0.65 | +1 | 工数最大・weight 最小（戦略価値は下流 3 件の解消） |

**結論: A6 を選定**。理由: (1) 今セッションの円分剛性・実 χ・実 μ の**設計時から意図された
消費者**であり（CGAR-6 が cycRecCharacter 型で供給済み）、全部品が存在する唯一の候補。
(2) M334F が「決して導出しない」と正直申告した mono-anabelian の核心仮説
`cycRecGeoCompatible` を**定理に変える**——「実 IUT 完全証明率を上げるか？」の自問に
最も明確に Yes（復元機構の主語が実になる）。(3) Σ=44.0 ちょうどの丸め位置により
w14×(+0.05)=+0.7 で確実に柱A 44→45。(4) 新イディオム 0・fable 不要・二重計上リスク無し
（A7 監査は cgarRecChar を「入力供給」までしか計上していない——消費側の実化は未計上）。

**次点以降の順序（本設計の勧告）**: A6a(crr) → A6b(crrt・任意) → A2（実 ℚ₃・下流 3 件の
ブロッカー解消）→ A8（実付値を得てから）→ A4（被覆圏側の独立成果として）。

---

## 6. 選定項目の分解 — A6a「実 mono-anabelian 円分体復元」（opus 実装枠へ）

### 6.1 新規ファイル 1（本体・必須）: `IUT/CyclotomeRecoveryReal.lean`（prefix `crr`・本日 grep で未使用確認済み）

依存: `CyclotomicGKActionReal`（cgar）・`CyclotomicMuGroupReal`（cmr）・
`CyclotomeIdentification`（cid・cmuMap/cidIso/cid_galois_equivariant）・
`CyclotomeRecovery`（cycRec）・`CyclotomicRigidity`（cycMuStd/CycGKAction）・
`CyclotomicCharIso`（cci）・`PrincipalUnits`（zmodMul）。

```lean
/- CRR-0: zmod 簿記（既存に無いことを本日 grep 確認・各 ~15 行） -/
theorem crr_zmodMul_add (n : Nat) (c x y : (zmod n).carrier) :
    zmodMul n c ((zmod n).mul x y)
      = (zmod n).mul (zmodMul n c x) (zmodMul n c y)
  -- zmod の群演算は加法。Quot.ind ×2 + Int.mul_add + Quot.sound（witness は差の因数）
theorem crr_zmodMul_one (n : Nat) (c : (zmod n).carrier) :
    zmodMul n c (Quot.mk (modCong n).rel 1) = c        -- Int.mul_one

/- CRR-1: χ 捻りの CycGKAction 化（M334F cycRecGKModule は raw 関数——Hom 化が新規） -/
def crrAction (GK : Grp) (n : Nat) (hn : 1 ≤ n) (χ : cycRecCharacter GK n) :
    CycGKAction GK (cycMuStd n hn) where
  act := fun g => { map := fun x => zmodMul n (χ.chi g) x,
                    map_mul := crr_zmodMul_add n (χ.chi g) }
  act_one := …   -- cycRec_action_one（χ(1)=1・既存）
  act_mul := …   -- cycRec_action_mul（χ 準同型・既存）

/- CRR-2: 実 χ での指数計算（hchar 前提の供給・本ファイル最大の簿記） -/
theorem crr_exp_eq (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ) :
    cycRigExp _ (cycMuStd (3^ℓ) (zpu_pow_pos ℓ)) (crrAction _ _ _ (cgarRecChar ℓ hℓ)) σ
      % 3^ℓ
      = cycRigExp _ (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ % 3^ℓ
  -- LHS: exp = log(χ(σ)·class 1) = log(χ(σ))（crr_zmodMul_one）。cgarRecChar.chi =
  --   cycRigChar(cgarAct) = class(ctr_charG : Int)（cgar_char_eq・既存）、cycMuStd.log =
  --   (·%n).toNat ⟹ LHS = ctr_charG % 3^ℓ（ctr_charG_lt で <3^ℓ・Int/Nat cast 簿記）。
  -- RHS: cgar_exp_eq（既存）で = ctr_charG % 3^ℓ。合流。

/- CRR-3: 実 χ の復元円分体（M334F-9 trivial 実例の実主語版・消さずに併設） -/
def crrRecovered (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    cycRecGKModule (galoisGroupGrp (cteExt ℓ hℓ)) :=
  cycRec_mu_from_chi _ (3^ℓ) (cgarRecChar ℓ hℓ)
theorem crr_recovered_nontrivial (ℓ hℓ) :
    (crrRecovered ℓ hℓ).act (cgarSigma2 ℓ hℓ) (Quot.mk _ 1) ≠ Quot.mk _ 1
  -- 復元作用が σ₂ で class 2 ≠ class 1（cgar_sigma2_exp・ctm/zmod 分離は既存
  --   cci_indexG 系 or 2<3^ℓ の直接簿記）——trivial χ≡1 実例（恒等作用）との対比を実現

/- CRR-4: ★復元 μ̂ ≅ 実 μ_{3^ℓ} の G-同変同型（cid 再利用・A6a のヘッドライン前半） -/
def crrIso (ℓ hℓ) : Hom (cycMuStd (3^ℓ) _).μ (cmrMu ℓ hℓ).μ :=
  cidIso (cycMuStd (3^ℓ) _) (cmrMu ℓ hℓ) rfl        -- 両側 .n = 3^ℓ は rfl 級
theorem crr_iso_leftinv / crr_iso_rightinv            -- cid_iso_leftinv/rightinv の実主語適用
theorem crr_iso_equivariant (ℓ hℓ) (σ) (x) :
    (crrIso ℓ hℓ).map ((crrAction _ _ _ (cgarRecChar ℓ hℓ)).act σ |>.map x)
      = ((cgarAct ℓ hℓ).act σ).map ((crrIso ℓ hℓ).map x) :=
  cid_galois_equivariant _ _ _ rfl _ _ (crr_exp_eq ℓ hℓ) σ x
  -- ★M443F の一般定理に実主語（実 Gal・実 μ・実 χ）を代入するだけ——再証明しない

/- CRR-5: ★cycRecGeoCompatible の実 discharge（A6a のヘッドライン本丸） -/
def crrGeoAct (ℓ hℓ) : (galoisGroupGrp (cteExt ℓ hℓ)).carrier
    → (zmod (3^ℓ)).carrier → (zmod (3^ℓ)).carrier :=
  fun σ x => cmuMap (cmrMu ℓ hℓ) (cycMuStd (3^ℓ) _)
    (((cgarAct ℓ hℓ).act σ).map ((crrIso ℓ hℓ).map x))
  -- 実 Galois 作用（体自己同型の実 μ への制限）を同定で読んだもの＝「真の幾何作用」side
theorem crr_geo_compatible (ℓ hℓ) :
    cycRecGeoCompatible (galoisGroupGrp (cteExt ℓ hℓ)) (3^ℓ)
      (cgarRecChar ℓ hℓ) (crrGeoAct ℓ hℓ)
  -- ∀ σ x, crrGeoAct σ x = zmodMul (χ.chi σ) x。crr_iso_equivariant で作用を χ 捻り側へ
  --   移送し、crr_iso_leftinv で往復を消す。M334F が「決して導出しない」とした仮説の、
  --   実円分体を幾何側とする忠実な部分ケースでの**定理化**（§8 の正直な限定つき）
theorem crr_geo_recovery (ℓ hℓ) (σ) (x) :
    crrGeoAct ℓ hℓ σ x = (crrRecovered ℓ hℓ).act σ x :=
  cycRec_geo_recovery_hypothesis _ _ _ _ (crr_geo_compatible ℓ hℓ) σ x
  -- 既存の仮説依存定理が本物の入力で発火する瞬間（仮説スロットに定理を差す）

/- CRR-6: capstone（束ね・新規証明ゼロ） -/
structure CrrRealCyclotomeData (ℓ : Nat) (hℓ : 1 ≤ ℓ) where
  recovered : cycRecGKModule (galoisGroupGrp (cteExt ℓ hℓ))   -- 復元 μ̂（実 χ から）
  nontrivial : …                                              -- CRR-3
  iso_equivariant : …                                         -- CRR-4
  geo_discharge : cycRecGeoCompatible _ _ (cgarRecChar ℓ hℓ) (crrGeoAct ℓ hℓ)  -- CRR-5
def crrRealCyclotomeData (ℓ hℓ) : CrrRealCyclotomeData ℓ hℓ
theorem crr_scope : …    -- 正直な限定の宣言（§8 の (i)-(iii) を Prop 註記 or ドキュメントで）
```

- **工数: 350–500 行**。tier **M（opus）**。新イディオム 0（cid の一般定理への実主語代入＋
  zmod/Int cast 簿記のみ）。fable 不要。
- 詰まりどころと予防線: (i) `(cycMuStd (3^ℓ) hh).n = (cmrMu ℓ hℓ).n` の rfl——両者とも
  定義フィールド n := 3^ℓ で defeq 見込み。通らなければ付替補題 1 本（+15 行）。
  (ii) CRR-2 の Int↔Nat cast（cycMuStd.log の toNat と ctr_charG : Nat の突き合わせ）——
  `Int.toNat_of_nonneg`/`Int.emod_nonneg` の既存イディオム（cycMuStd 本体の証明が写経元）。
- **complete_pct 単体寄与: A6 0.5→0.55 を独立監査に諮る**（ヘッダに「A6a 本体・監査確定待ち」
  と明記）。柱A Σ 44.0→44.7 → **44→45（+1）**。

### 6.2 新規ファイル 2（任意・第 2 波）: `IUT/CyclotomeRecoveryTowerReal.lean`（prefix `crrt`・未使用確認済み）

依存: crr・`CyclotomicLimitIso`（cli_res_char）・`CyclotomicTowerLimit`（ctlRestr）・
`TateModuleZ3`（tmzT/tmzLimit）・`CyclotomeRecovery`（cycRecCharTrans/zmodTrans）。

```lean
/- CRRT-1: 実 χ の塔整合——復元指標の変 n 両立が実制限に一致 -/
theorem crrt_char_restr {i j : Nat} (h : i ≤ j) (σ : (ctlGal j).carrier) :
    (cycRecCharTrans (zpu_pow_dvd …) (cgarRecChar (j+1) _)).chi σ
      = (cgarRecChar (i+1) _).chi ((ctlRestr h).map σ)
  -- cli_res_char（χ_i(res σ)=χ_j(σ)%3^{i+1}・既存）＋zmodTrans の mod 簿記で合流
/- CRRT-2: 復元塔 ≅ 実 ℤ₃(1) 塔の段間可換正方形 -/
theorem crrt_iso_trans_square {i j} (h : i ≤ j) (x) :
    (tmzT h).map ((crrIso (j+1) _).map x)
      = (crrIso (i+1) _).map ((zmodTrans …).map x)
  -- 両辺とも「指数を 3^{i+1} で読む」——tmz_find_pow（既存）＋cycMuStd/zmodTrans の
  --   mod 簿記。★詰まった場合のみ fable スポット 1（tmz_act_compat と同型の差分帰納）
/- CRRT-3: capstone — 実 profinite G の指標データ（cliChar）だけから復元した
   μ̂ 塔が、実 ℤ₃(1)=tmzLimit の各段と G-同変・遷移整合に同定される
   （mono-anabelian ℤ₃(1) 復元の忠実な部分ケース） -/
structure CrrtTowerData where … / def crrtTowerData : CrrtTowerData
```

- **工数: 400–600 行**。tier **M（opus）・CRRT-2 に fable スポット 1 予約**。
- **complete_pct 寄与: A6 0.55→0.6 を諮る**（Σ 44.7→45.4 → 柱A% **45 据え置き**——
  status は動くが柱%は横這い。§5 規則によりその旨を正直に報告する前提で投入）。

### 6.3 ラウンド編成（CLAUDE.md tier 配分・5 並列規則準拠）

1. **ラウンド 1**: crr [opus] 1 本（A6 枠は依存の都合で 1 本——残り枠は他柱の
   complete_pct 前進案件で埋める。水増し capstone で埋めない）。完了時 **A6a 独立監査**
   （0.55・柱A 44→45 見込み）。
2. **ラウンド 2（任意）**: crrt [opus・fable スポット待機]。完了時 A6 再監査（0.6 級・
   柱A% 据え置きを正直申告）。
3. 並行推奨（別項目・本設計の勧告）: A2 実 ℚ₃ の詳細化ラウンド（fable 1 枠）を先行させ、
   A8/A6-AbsTopIII のブロッカー解消を仕込む。

### 6.4 後続ターゲットの名指し（本ラウンドに含めない・§2(c) 起票時に参照）

- **相対 Kummer**（A7 詳細化 §4）: 相対 Galois 部分群 Gal(ℚ(ζ_{3^{ℓ+1}})/ℚ(ζ_{3^ℓ})) の
  実構成＋κ_α:G→μ₃——M349F htriv/hfix の部分ケース discharge（A6 第 2 波・400 行級）。
- **AbsTopIII 実付値インスタンス**: 実 ℚ(ζ_{3^ℓ}) 上の 3 進（λ=ζ−1 Eisenstein）付値の
  実構成→ M329F/M334F capstone の非自明付値実例（A2 完了後）。
- **cid hζl/hdist の実 discharge**: p≡1 (mod 3^ℓ) の Teichmüller 持ち上げ（Hensel 実装後）。

## 7. 実装規約（crr/crrt 共通・A7 詳細化 §6 を継承・opus への指示に含める）

- ヘッダ二軸: 分類 [実／昇格(a)]・complete_pct 影響（crr は「A6a 本体・監査確定待ち」、
  crrt は「A6b・柱% 横這い見込みを明記」）。**置換対象を名指し**: M334F-9 trivial χ 実例・
  M334F-7 外部仮説 `cycRecGeoCompatible`（「決して導出しない」:217-231）・complete_note
  「A6=0.5(機構は実だが実例が自明/退化)」。
- 既存モジュール改変禁止・正直申告は消さない弱めない（trivial 実例 `cycRecGaloisCyclotome`
  も外部仮説枠 `cycRec_geo_recovery_hypothesis` も残す——crr は実 witness を**併設供給**）。
- 禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用・**新規 Classical.choice 禁止**（`#print axioms`=[propext,Quot.sound]）。
  witness は全てデータ（cmuMap=log 読み替え・χ=cgarRecChar・∃ は Prop ゴール内のみ）。
- 3^ℓ 算術は zpu_pow_pos/zpu_pow_dvd 経由（omega に冪を渡さない）。
- 新規ファイルのみ・共有ファイル（IUT.lean/build.sh/dashboard/graph 系/target_ledger）不更新
  （親が統合・gen_graph.py 再生成も親）。

## 8. 正直な限定（本設計自身のもの・消さない・弱めない）

1. 本ドキュメントは設計であり complete_pct を動かさない。status 数値は保守的見積りで、
   確定は独立監査（AUDIT_RUBRIC 準拠）。
2. **「幾何側」の正直な線引き**: crr が discharge する `cycRecGeoCompatible` の幾何作用は
   **実円分体 ℚ(ζ_{3^ℓ}) 自身の中の実 μ_{3^ℓ} への実 Galois 作用**（cgarAct の同定読み）
   であり、分離閉包 K̄ の μ_n(K̄) でも π₁^ét の幾何的 cyclotome（Λ）でもない。
   「真の幾何 μ⊆K^sep との同型」の完全形は依然後続（M334F の申告文言は消さず、
   「忠実な部分ケースで定理化」と併記する）。
3. **χ の位相性は未**: cgarRecChar は実 Galois 群の実指標だが、π₁^ét **位相群の連続指標**
   としての抽出（M334F 正直申告の本丸）は本ラウンドでも閉じない。円分切片
   Gal(ℚ(ζ_{3^ℓ})/ℚ)・p=3・基礎体 ℚ 固定。
4. **A6 上限**: crr+crrt 到達でも A6 ≤ 0.6 目安——AbsTopIII の非自明付値実例・
   π₁ からの (K^×,v,χ) 抽出アルゴリズム・Kummer 部（theta Kummer との接続）・
   数体全体の mono-anabelian 復元は全て未達のため、1 に近づけない。
5. リスク: (a) cycMuStd と cmrMu の .n defeq（fallback: 付替補題 +15 行）、
   (b) CRR-2 の Int/Nat cast 簿記（写経元あり）、(c) CRRT-2 の遷移正方形
   （fable スポット 1 予約・fallback: crrt を CRRT-1 のみの 0.55→0.58 級申告に縮小）。
