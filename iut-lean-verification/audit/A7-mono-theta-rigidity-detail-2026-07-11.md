# A7 詳細化ラウンド（設計のみ・実装なし）: mono-theta 円分剛性 — テータ環境による不定性の KILL は今可能か

- 日付: 2026-07-11
- 対象: pillars.A **A7「実円分剛性 cyclotomic rigidity」**（weight 12・status 0.40）
- 前提資産: A8 実テータ群 `IUT/Q3ThetaGroup.lean`（q3th・0.65 算入済）・A5 `IUT/Q3TemperedThetaClass.lean`（q3nt・0.20 算入済）
- 方法: def/theorem 本体精読（ヘッダ主張不使用）・敵対的既定＝「A8/A7 既算入分の relabel」
- 結論先出し: **実装可能な real ステップあり（新規ファイル `IUT/Q3MonoThetaRigidity.lean`・prefix `q3mr`・tier M=opus）**。
  ただし level 2/μ₂ 切片ゆえ「ℤ₃^× 不定性の KILL」は**部分的にしか**実現しない（§2/§4 で正直に線引き）。
  A7 0.40 → 見込み 0.43（敵対的下限 0.41・据置リスクあり）→ 柱A 表示 52→**53**（s≥0.41 で成立・§5）。

---

## §1 現状実測 — A7 が持つもの・テータ環境が新たに与えるもの

### 1.1 A7 の現在地（characterize-not-kill）

前回監査 `audit/reaudit-A7-tatemodule-endo-indet-2026-07-10.md` の据置理由（本体精読で再確認）:

> 「mono-theta 円分剛性（不定性を殺す幾何的剛性・A7 が最終的に指す IUT 荷重）は依然ちょうど 0。
> 本件は不定性を CHARACTERIZE するのみで KILL しない」

| 資産 | prefix | 内容（本体実測） | 剛性の型 |
|---|---|---|---|
| `TateModuleEndo.lean` | tme | 抽象 Hom f:T→T（T=ℤ₃(1)=tmzLimit）の自動降下・End 完全分類（`tme_endo_ext`） | 特徴付け |
| `TateModuleIndeterminacy.lean` | tmi | **Aut(T) ≅ 実 ℤ₃^×**（`tmi_aut_classify`+`tmi_units_inj`）・同変性は空（`tmi_endo_gal_commute`: 全 f が Gal 可換） | 特徴付け（不定性＝ちょうど ℤ₃^×・殺さない） |
| `CyclotomicRigidityAut.lean` | cra | レベル単位剛性・`cra_indeterminacy`＝(ℤ/3^ℓ)^× 残存宣言 | 特徴付け |
| `CyclotomicGKActionReal.lean` | cgar | 実 Gal(ℚ(ζ_{3^{n+1}})/ℚ) の μ_{3^{n+1}} 実作用・χ 一意性（`cgar_rigidity`） | 作用の同定 |
| （A6 隣接）crl/crc | | cyclotome 復元＝**ℤ₃^× torsor**（`CyclotomeRecoveryCanonicity`） | torsor（殺さない） |

共通の構図: **不定性群 ℤ₃^×（レベルでは (ℤ/3^ℓ)^×）を正確に同定するが、それを 1 に潰す機構はゼロ**。
[EtTh] の mono-theta 剛性（テータ環境の自己同型は内部 cyclotome に恒等で作用する）が A7 の IUT 荷重であり、それは現状 0。

### 1.2 テータ環境（q3th・A8=0.65 算入済）が新たに置いた土台

`IUT/Q3ThetaGroup.lean` 本体精読の実測:

| 対象 | 内容 | mono-theta 剛性への含意 |
|---|---|---|
| `q3thGrp = C_M(g_τ)` | 実テータ群（所属 qᵃw²=1 ⟺ a=−j ∧ u₀∈μ₂・`q3th_mem_iff`） | 剛性の主語となる実対象 |
| `q3th_comm_eq_weil` | [g,g'] = (e(g,g'),0,1)・e=DERIVED Weil ペアリング | **交換子＝cyclotome 値**（剛性機構の入力） |
| `q3th_weil_g3_gm1` / `q3th_weil_nondeg` | e([3],[−1]) = (0,q3tNegOne) = 実 −1 ∈ μ₂ ⊂ ℤ₃^×・≠1 | 内部 cyclotome の**特定の**生成元（−1）が交換子として指名される |
| `q3th_ker_central` / `q3th_ker_scalar` | 純スカラー (c,0,1) は中心・核は ℚ₃^××q^ℤ | 内部 cyclotome の担体＝中心スカラー |
| `q3th_proj_surj_klein` | 射影は Klein=E₉[2] に全射（witness 明示） | 交換子の「幾何座標」側 |
| `q3th_weil_lift_indep` | e は (a,w) が**等しければ**等しい（c 非依存のみ・自明 rewrite） | **Klein 降下は未証明**（q^ℤ シフト非依存性はゼロ）← ここが新規余地 |

**A8 が持っていないもの（＝二重計上にならない新規余地）**: q3th には**自己同型／自己準同型に関する定理が 1 本もない**。
ヘッダ §4-6 も「A7 mono-theta 剛性も主張しない（setup のみ）」と明記し、A8 監査（reaudit-A8-theta-group-2026-07-11.md）も
剛性を一切算入していない。また e の Klein 像のみへの依存（w→w·qᵏ の非依存性）は未証明——`q3th_weil_lift_indep` は
(a,w) 完全一致を仮定する自明 rewrite であり、q^ℤ-lift をまたぐ降下は**所属条件（a=−j・u₀²=1）を実消費する非自明な新内容**。

### 1.3 q3nt（A5=0.20 算入済）にある「distinguished cyclotome」

- `q3ntZ := q3thScalar ((0:Int), q3tNegOne)`（Q3TemperedThetaClass.lean:293）— 内部 cyclotome 生成元は**すでに名前を持つ**。
- `q3nt_cyclotome_real`: Φ((0,0,1)) = q3ntZ — 代理 cyclotome の実像同定。`q3nt_symplectic_real`: 交換子＝(−1)^ω。
- いずれも**値の同定・bridge**であり、自己同型剛性（KILL）は q3nt にもゼロ。q3ntZ の再利用は定義 1 行の重複に留める（§2.4）。

### 1.4 surrogate 側の mono-theta（対照・柱A 算入済の模型）

- `TemperedThetaCommutator.lean`（M384F）: ℤ³ Heisenberg thetaGrp・中心＝μ_l 離散モデル。
- `TemperedThetaOuterAction.lean`（M389F）: **M389F-3a「交換子はスケール捻りで不変 [σx,σy]=[x,y]」**——これは
  「交換子は幾何座標のみに依存」という mono-theta 機構の**代理の影**。ただし主語は裸 ℤ³（座標が nose で一致する世界）で、
  実テータ群の q^ℤ-lift・μ₂ torsion の簿記（本設計の核・§2.2）は存在しない。

---

## §2 中心判定 — 最小の real mono-theta 剛性ステップ

### 2.1 候補 (a): 実 Galois 作用を q3thGrp に載せて Galois 同変剛性 → **却下（空虚・接続不能）**

- `tmzActHom`（TateModuleZ3.lean:300）は **Gal(ℚ(ζ_{3^∞})/ℚ) の T=ℤ₃(1)（3 冪円分塔）への作用**。
  q3thGrp の台は (ℚ₃^××ℤ)×ℚ₃^× で、**ℚ₃^× = 3^ℤ×ℤ₃^× の torsion は μ₂ のみ**。μ_{3^n} は ℚ₃^× に入らず、
  tmzActHom の作用先（cmrGrp 塔）と q3th の台は**交わらない**。成分ごとに移植できる作用が存在しない。
- 仮に「G_{ℚ₃} の実作用」を考えても、現形式化は E₉ の **ℚ₃-有理点のみ**を持つ（q3tGrp=QpUnits 3）。ℚ₃-有理対象への
  Galois 作用は恒等であり、「Galois と可換な自己同型は cyclotome に自明に作用」は**仮定が全自己同型に退化して空虚**。
  μ₂={±1}⊂ℚ₃ ゆえ「交換子値が Galois 固定」も自動（有理数だから）。
- 判定: **(a) は現資産では空虚**。非空虚化には ℚ̄₃-点（少なくとも ℚ₃(ζ₃)^×）が要る＝§3 の名指し前提条件。

### 2.2 候補 (b)+(c) の再編成 → **採用核: 「交換子は Klein 像のみで決まる」⇒ テータ両立自己準同型の内部 cyclotome 恒等**

[EtTh] の mono-theta 剛性の証明機構は「交換子値は E[2] 像だけで決まる。テータ環境の自己同型が E[2] 上恒等なら
交換子値（＝内部 cyclotome の生成系）を動かせない。ゆえに内部 cyclotome への作用は恒等＝捻り不能」。
この機構は q3th の上で**そのまま実定理化できる**。実計算で裏取り済（本設計で手計算検証）:

**鍵補題（Klein 決定性）**: g₁,g₂,g' ∈ q3thGrp・proj(g₁.2)=proj(g₂.2)（同じ Klein 像）⟹ e(g₁,g')=e(g₂,g')。

*証明の実体*（q3tGrp = ℤ×ℤ₃^× 成分計算・tateZpow 簿記）: proj 相等 ⟹ w₂=w₁·qᵏ（`quotientProjN_ker` 型で k 抽出）
⟹ j₂=j₁+2k・u₀ 同一・所属より a₂=−j₂=a₁−2k。差分因子は
e(g₂,g')·e(g₁,g')⁻¹ = w'^{−2k}·q^{−k a'} = ((−2k j') + (−2k a'), u₀'^{−2k}) = (−2k(j'+a'), (u₀'²)^{−k}) = (0,1)=1、
ここで **a'=−j'（g' の所属）と u₀'²=1（g' の μ₂ 所属）を両方実消費**する。
一般の M 元では**偽**（反例 witness §2.3）——すなわちこの補題は「テータ構造が剛性を生む」ことの実定理であり、
群論的一般論からは出ない。

**主定理（mono-theta 剛性・level 2）**: φ : q3thCar → q3thCar が
(i) 所属限定準同型 hHom: ∀ g g'∈q3thGrp, φ(g·g') = φg·φg'、(ii) 所属保存 hMem: mem g → mem (φ g)、
(iii) Klein 上恒等 hKlein: mem g → proj((φ g).2) = proj(g.2)、
を満たすなら ∀ g,g'∈q3thGrp: **φ(q3thComm g g') = q3thComm g g'**。

*証明*: φ(comm g g') = comm(φg)(φg')（hHom＋φ(1)=1（消去律）＋φ(inv)=inv∘φ）
= ((e(φg,φg'),0),1)（`q3th_comm_eq_weil` 消費）= ((e(g,g'),0),1)（鍵補題×2・hMem/hKlein）= comm g g'。

**系（内部 cyclotome の恒等＝KILL）**: q3mrZeta := q3thScalar((0,q3tNegOne))（＝q3ntZ と同一元・−1 スカラー）は
q3mrZeta = comm(g_{[3]}, g_{[−1]})（`q3th_weil_g3_gm1` 消費）ゆえ **φ(q3mrZeta) = q3mrZeta**。
内部 cyclotome μ₂ = {1, q3mrZeta} への誘導作用は**恒等のみ**——テータ構造と両立する自己準同型の
cyclotome 捻り群は {id}。tmi の「Aut(T)≅ℤ₃^× まるごと生き残る」（torsor）との対照が Lean 上の実定理で立つ。

### 2.3 反空虚性の防御（敵対監査が撃つ 2 点への先回り）

**攻撃 1「自己同型は唯一の位数 2 元を自動固定する（安い別証明がある）」**:
- 部分的に正しい: φ が**全単射**なら φ(−1)=−1 は「ℚ₃^× の 2-torsion は {±1}・ℤ 部分 torsion-free」から安く出る。
- 防御: 主定理は**自己準同型**（単射仮定なし）で述べる。endo では φ(q3mrZeta) ∈ {1, q3mrZeta} が先験で、
  **潰し（→1）を排除するのは Klein 決定性＋非退化値 e([3],[−1])=−1 のみ**。安い別証明は存在しない。
  さらに定理の実体は結論単体でなく**全交換子の保存**（機構そのもの）であり、こちらは全単射でも自明でない。
- 併置 witness（実装必須）: **q3mr_klein_fails_on_M** — g₁=((1,0),1)∈q3thGrp・g₂=((1,1),1)∉q3thGrp は同 Klein 像
  （w がともに 1）だが e(g₁,g_{[−1]})=1 ≠ (0,−1)=e(g₂,g_{[−1]})。所属仮定が load-bearing であることの反例定理。
- 非空虚な適用例: 内部自己同型 conj_h（h∈q3thGrp）は (i)(ii)(iii) を全部満たす（w 成分可換ゆえ Klein 恒等）。仮定クラスは非空。

**攻撃 2「level 2 では殺すべき群が最初から自明（(ℤ/2)^×=1・ℤ₃^×→Aut(μ₂) は自明）」**:
- **正しい。ここは認める**（§4 に明記）。ℤ₃^× の μ₂ への作用は u 奇数ゆえ (−1)ᵘ=−1 で恒等。
  ゆえに本ステップは「Aut(ℤ₃(1))=ℤ₃^× の KILL」**そのものではない**。実現するのは
  (α) [EtTh] 剛性**機構**（交換子＝Klein 決定 ⇒ 内部 cyclotome 恒等）の実テータ群上の忠実インスタンス、
  (β) endo 水準の非自明な KILL（cyclotome 潰し endo の排除・攻撃 1 参照）、の 2 点。
  (ℤ/3^n)^× を殺すには μ_{3^n} 水準のテータ環境が要る（§3 の前提条件）。

### 2.4 二重計上境界（厳密・監査向け）

| 対 | 既算入 | q3mr の新規 | 再計上でないことの根拠 |
|---|---|---|---|
| **A8 (q3th)** | 群の建設・交換子=Weil・値 −1・非退化・Klein 全射・(a,w) 完全一致 lift 非依存 | **Klein 決定性（qᵏ-shift 降下・所属実消費）・endo 剛性・cyclotome 恒等・M 上反例** | q3th に自己同型定理ゼロ（本体 grep 確認）。ヘッダ §4-6「A7 mono-theta 剛性も主張しない」。q3th 定理は**消費のみ・再証明ゼロ** |
| **A7 (tme/tmi)** | End/Aut(T=ℤ₃(1)) の完全分類（3 冪円分塔上） | 主語が別（テータ群の endo）・不定性の**排除**定理 | tmi は import しない・対照は散文＋status 根拠のみ。characterize（tmi）と kill（q3mr）は論理的に別命題 |
| **A6 (crl/crc)** | 3-cyclotome 復元＝ℤ₃^× torsor | 触れない | import なし・μ₂ ≠ 3-cyclotome |
| **A5 (q3nt)** | Φ/Ψ bridge・q3ntZ 命名・symplectic 値一致 | q3mrZeta は**定義 1 行の重複**（q3nt を import しない設計・重複は正直申告） | q3nt 定理は不消費・値一致の再演なし |
| **M389F（代理）** | ℤ³ Heisenberg 上の [σx,σy]=[x,y]（座標 nose 一致の世界） | 実 q^ℤ-lift をまたぐ降下＋μ₂ torsion 簿記（代理に存在しない内容） | 比較準同型は作らない・transport ゼロ |

**もし新規分が「q3th_comm_eq_weil の系」に見えるなら**: 鍵補題は q3th_comm_eq_weil からは出ない
（同定理は交換子の**値の式**を与えるだけで、その式の qᵏ-shift 不変性は所属条件 2 本を要する別計算）。§2.3 の
M 上反例定理が「系ではない」ことの機械可検証な証拠になる。

---

## §3 結論 — 採用する 1 ステップ

**実装する**（re-counts A8/A7 ではない・§2.4）。ただし主張は「mono-theta 剛性の level-2/μ₂ 忠実インスタンス＋endo 水準 KILL」に限定し、「ℤ₃^× 不定性の完全 KILL」とは**言わない**。

- **ファイル**: `IUT/Q3MonoThetaRigidity.lean`（新規 1 本・prefix `q3mr`・衝突なし grep 済）
- **import**: `IUT.Q3ThetaGroup` のみ（tmi/q3nt/crl は import しない——二重計上防壁）
- **tier**: **M（opus）**。確立イディオム（q3tGrp 成分計算・tateZpow 簿記・q3th スタイル）＋本設計の証明スケッチ済。
  詰まった箇所のみ fable スポット。推定 400–500 行。
- **定理列（choice-free・全計算 witness 明示）**:
  1. `q3mr_proj_eq_shift`: proj x = proj y（in q3tCurve 2）⟹ ∃k, y = x·qᵏ（`quotientProjN_ker`＋Hom の inv 簿記）
  2. `q3mr_weil_klein_left` (★): mem g₁ → mem g₂ → mem g' → proj g₁.2=proj g₂.2 → e(g₁,g')=e(g₂,g')
     （§2.2 の実計算: 差分 = (−2k(j'+a'), (u₀'²)^{−k}) = 1・所属 2 条件消費）
  3. `q3mr_weil_klein_right` (★): 第 2 引数版（同型の計算）
  4. `q3mr_hom_one` / `q3mr_hom_inv`: 所属限定 hom の単位・逆元保存（消去律・所属閉性消費）
  5. `q3mr_rigidity` (★★): §2.2 の主定理（endo・Klein 恒等 ⇒ 全交換子保存）
  6. `q3mrZeta` 定義＋`q3mr_zeta_eq_comm`: q3mrZeta = comm(g_{[3]},g_{[−1]})（`q3th_weil_g3_gm1` 消費）＋`q3mr_zeta_mem`
  7. `q3mr_cyclotome_fixed` (★★★): φ(q3mrZeta) = q3mrZeta — **内部 cyclotome への捻りゼロ**（mono-theta 剛性の実現形）
  8. `q3mr_mu2_killed` (★★): 内部 μ₂={1,q3mrZeta} 上の誘導作用は恒等（endo クラス全体で）——「kill」の言明形
  9. `q3mr_klein_fails_on_M` (★): M 上反例（§2.3・所属仮定の load-bearing 証明）
  10. `q3mr_inner_example`: 内部自己同型が仮定クラスに入る（非空性 witness・小）
  - capstone 束ねは**作らない**（水増し回避・言明 8 が結論そのもの）
- **選択公理**: 新規 Classical.choice ゼロ設計。k の抽出（定理 1）は ∃ を Prop ゴール内で破壊するのみ・
  witness 関数化しない（Klein 降下ペアリング**関数**は作らず関係式形に留める——Quot からの関数化が
  choice か全域拡張を要するため。正直限定として記す）。全 ★ 対象 #print axioms = [propext, Quot.sound] 目標。

**pivot が必要になる条件**（実装前チェック）: 定理 2 の差分計算が q3tGrp の zpow 簿記で 1 に閉じることは
本設計で成分検算済（(0,1) に正規化）。閉じない事態は想定しないが、万一 `quotientProjN_ker` の形が proj 相等
からの k 抽出に不足する場合は q3t 側補題 1 本（proj x=proj y ⟺ x⁻¹y∈qᶻ）を同ファイル内に足す（新規・依存追加なし）。

---

## §4 正直な線引き（un-real の明示・消さない）

1. **殺した群は「テータ両立 endo の内部 μ₂ への作用」であり、Aut(ℤ₃(1))=ℤ₃^× ではない**。μ₂ は 3 と素な
   cyclotome で、tmi の ℤ₃^× 不定性（3-冪円分塔上）はこの定理の後も**まるごと残存**する。ℤ₃^×→Aut(μ₂) が
   算術的に自明（u 奇数）である事実は隠さない。
2. **全単射 φ に限れば系 7 は安く出る**（唯一の位数 2 元）。非安価な内容は endo 版＋Klein 決定性＋全交換子保存
   （機構）であり、その線で status を主張する。
3. **level 2/p=3/q=9 単一切片**。μ_{3^n} 水準の mono-theta 剛性（＝(ℤ/3^n)^× を殺す本丸）の**名指し前提条件**:
   実 ℚ₃(ζ₃)（分岐 2 次拡大）の単数群 or E_q[3] の実担体（μ₃⊄ℚ₃ ゆえ現 q3tGrp では建設不能）。これは
   将来の (b) 本物建設ターゲットとして残す。
4. **Galois 同変性はゼロ**（§2.1 の通り現資産では空虚——載せない。空虚な同変仮定を足して「Galois 剛性」を
   名乗る水増しはしない）。
5. **Klein 降下ペアリングの関数化はしない**（関係式形のみ・choice 回避）。実テータ関数・π₁-同定・cuspidalization
   本体は依然 0（q3th/q3cu の正直限定を不変更で保持）。
6. crl/crc の「復元は ℤ₃^× torsor」・tmi の「同変性条件は空」は**消さない・弱めない**（q3mr は別主語の追加）。

---

## §5 status 見込み・柱A% 算術（検算済）

`target_ledger.json` 実測（2026-07-11 時点）:

| A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8 | A9 |
|---|---|---|---|---|---|---|---|---|
| 8×0.85 | 8×0.65 | 12×0.75 | 14×0.55 | 10×0.20 | 14×0.58 | **12×0.40** | 12×0.65 | 10×0.10 |

- **Σ_A = 52.42**（検算一致）・A7 抜き定数 = 52.42 − 12×0.40 = **47.62**・Σ_A = 47.62 + 12·s_A7
- 表示 53 の条件: Σ_A > 52.5（Python banker's `round(52.5)=52` ゆえ**厳密超過**が必要）
  ⟹ s_A7 > (52.5 − 47.62)/12 = **0.40667** ⟹ 台帳粒度 0.01 で **s_A7 ≥ 0.41**
- 検算: s=0.41 → Σ=52.54 → round **53** ✓ ／ s=0.43 → 52.78 → **53** ／ s=0.45 → 53.02 → **53** ／ 据置 0.40 → 52.42 → **52**

**見込み**: 設計自己予測 **0.43**（named blocker「mono-theta 剛性ちょうど 0」を、機構の忠実 level-2 インスタンス
＋endo 水準 KILL で非零化。_status_scale の 0.5「忠実な部分ケース」には μ₂/ℤ₃(1) 不一致（§4-1）ゆえ届かない）。
敵対的下限 0.41–0.42（§2.3 攻撃 2 の割引）。**据置（0.40）リスクは実在**——監査が「殺した群が自明な切片は
部分ケースと認めない」と裁定する場合。その場合 柱A 表示は 52 のまま（正直に「complete_pct 0 前進」と報告する）。

---

## §6 実装計画

| 枠 | tier/model | 内容 | 依存 |
|---|---|---|---|
| 実装 | **M (opus)** | `IUT/Q3MonoThetaRigidity.lean`（§3 の定理 1–10・400–500 行・choice-free） | `IUT.Q3ThetaGroup` のみ |
| 詰まり時 | L (fable) スポット | 定理 2 の zpow 簿記が閉じない場合のみ | — |
| 監査 | M (opus)・独立敵対 | AUDIT_RUBRIC 準拠・§2.3 の 2 攻撃と §2.4 の境界を必ず撃たせる | 本体のみ渡す |

- 統合時（親）: `target_ledger.json` A7 status・`graph-meta.json`（complete_note prepend・complete_pct は監査確定値）・
  `tools/gen_graph.py` 再生成・`dashboard.md` 二軸表・`tools/gen_graph.py` の `PILLAR` 辞書に q3mr→A 追記。
- 将来の名指しターゲット（本ラウンド外・(b) 本物建設）: 実 ℚ₃(ζ₃)^×（分岐拡大単数群）→ level-3 テータ環境
  → (ℤ/3)^× を殺す mono-theta 剛性 → tmi 不定性の真の KILL 開始。これが A7 0.5 超えの経路。
