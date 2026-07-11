# 詳細化ラウンド: level-3 kill 後の最高レバレッジ次手 — 比較橋 vs F-wild — 2026-07-11

**種別**: 設計文書のみ（Lean 実装なし）。**対象**: level-3 mono-theta kill キャンペーン（R1→R4・A7=0.47 確定）が残した 2 つの正直な上限——(1) 機構レベル止まり（tmzLimit への比較橋なし）・(2) mod-3 成分のみ（pro-3 bulk と n≥2 は F-wild 残存）——に対する次の一手として、**候補 A（比較橋）** と **候補 B（F-wild 塔）** を def/theorem 本体の読解で査定し 1 つを推奨する。**判定は本体のみ・敵対的既定=模型**。

---

## 0. 結論先出し（TL;DR）

1. **推奨: 候補 A（比較橋）**。1 モジュール（`IUT/Q3Mu3TmzBridge.lean`・prefix `q3mb`・tier M）・1 ラウンドで建ち、監査上限 #1（機構レベル）を正面 discharge して kill を「tmi の実 ℤ₃^× 対象の (ℤ/3)^× 商に作用する」水準へ昇格する。部品は**全て実在確認済み**（§2.2 の対応表）。新イディオム実質ゼロ（離散対数 `ctmFind`・冪簿記・成分計算の既確立 3 系統）。
2. **status 算術の重要な訂正（§5）**: 再監査 reaudit-A7-level3-kill-2026-07-11.md の「54 表示には A7≥0.54 が要る」は**算術誤り**。`compute_complete_pct.py` は `round()` を使い、Σ_A = 47.62 + 12·s ゆえ **s=0.49 で 53.50→表示 54** になる（実測 47.62+12×0.49 = 53.50000... → round = 54）。frontier 文書の「0.50 なら 54」が正しい側。つまり比較橋は、監査が 0.49 以上を与えれば**表示を 53→54 に動かし得る**（敵対的下振れ 0.48 なら 53 据え置き——両様を正直に見込む）。
3. **候補 B の未解決問題は設計レベルで割れた（§3）**: frontier が「genuinely open」と旗を立てた**暴分岐単数群の choice-free 逆元**は、λ-adic 幾何級数（重い・M160–M184 資産の単数群化が必要）**ではなく**、**相対 Kummer 共役ノルムのイディオム**で閉形式に解ける: R1 が μ₃ ⊂ O_{L₂} を**実に**建てたことにより、wild 段 M = ℚ₃(ζ₉) = L₂[Y]/(Y³−ζ₃) は L₂ 上 **Kummer 巡回 3 次**であり、相対 Galois σ:(a,b,c)↦(a, ζ₃b, ζ₃²c) は座標スケーリングの閉形式・逆元は x⁻¹ = σ(x)·σ²(x)·N(x)⁻¹（N は 3 次ノルム形式・N(x)⁻¹ は R1 の `q3rqInv` を消費）。幾何級数・Markov・choice は一切不要。
4. ただし B は「逆元が割れても」**最初の表示前進まで 2–3 ラウンド・full kill まで依然 12–18 モジュール**であり、最難関は逆元から **μ₉ 完全性（wild 版 mem_iff の急所・tier L）** に移る。B の初弾は A の後のラウンドで着工するのが正しい順序（A の橋モジュールが F-wild (iv)〔橋の塔版〕の**テンプレート**にもなる）。
5. 二重計上境界: 比較橋は tmi（特徴付け）・crl（A6 復元 Ξ）のどちらの再ラベルでもない——grep 実測で **q3rq を import する円分側モジュールはゼロ**・q3m3r は tmi を import していない（従来の firewall）。橋はその firewall を**新規の同一視＋輸送定理**で意図的に越える初のモジュールであり、消費のみ（tmiFromUnits・q3m3r_cyclotome_fixed・q3mc_mu3_complete）で再証明ゼロ。

---

## 1. 現状 — level-3 kill が達成したもの・2 つの上限・橋が繋ぐべき実対象

### 1.1 達成（本体確認済み・再監査 0.47 確定）

- **R4 `q3m3r_cyclotome_fixed`** (Q3Mu3Rigidity.lean:305): テータ両立自己準同型（所属限定 hom＋所属保存＋E₂₇[3] 上恒等）は内部 cyclotome 生成元 `q3m3rZeta`（=comm(g₃,g_ζ)・値 ζ₃⁻¹∈μ₃⊂U₂）を恒等固定する。
- **R4 `q3m3r_aut_mu3_nontrivial`** (:337): 実共役 `q3rqConj`（√−3↦−√−3）は μ₃ 上の反転 ζ₃↦ζ₃²≠ζ₃＝Aut(μ₃)≅ℤ/2 は非自明。よって剛性の {id} 固定は**本物の非恒等自己同型を排除**する——初の非自明 3-冪 kill。
- 支持: `q3m3_weil_nondeg`（μ₃ 値 Weil 非退化）・`q3m3r_weil_fails_on_M`（membership load-bearing）・全 14 対象 axioms = [propext, Quot.sound]。

### 1.2 二つの正直な上限（再監査が status 0.50 未満とした正確な理由）

1. **機構レベル**: 剛性の主語は**テータ環境の内部 μ₃**（q3m3 の交換子像・L₂^×=q3rqLx 内）であって、tmi の実不定性対象 `zpsLimit`（実 ℤ₃^×）が作用する実 `tmzLimit`（ℤ₃(1)）ではない。**比較橋が無い**——q3m3r は tmi を import せず（grep 裏取り済み）、「level-3 テータ cyclotome（q3m3 内部 μ₃）≅ tmz の mod-3 層」の同一視はコードベースのどこにも存在しない（§1.3 で再確認）。
2. **mod-3 のみ**: 殺したのは Aut(μ₃)≅(ℤ/3)^×≅ℤ/2 成分だけ。ℤ₃^× = lim (ℤ/3ⁿ)^× の pro-3 bulk（1+3ℤ₃）と n≥2 レベルは F-wild（実 wild 円分塔 ℚ₃(ζ_{3ⁿ})・暴分岐 e=2·3^{n−1}）までまるごと SURVIVES。

### 1.3 橋が繋ぐべき実対象（本体確認）

| 側 | 対象 | 実体 |
|---|---|---|
| テータ側（局所） | 実 μ₃ ⊂ U₂ = O_{ℚ₃(ζ₃)}^× | `q3rqZeta`=(−h,h)（h=2⁻¹∈ℤ₃ 閉形式）・`q3tlZeta3U : q3rqU.carrier`（q3tl:80）・完全性 `q3mc_mu3_complete`（u³=1⟹u∈μ₃）・実共役 `q3rqConj` の反転作用 |
| テータ側（内部） | 内部 cyclotome `q3m3rZeta` | 値 = `q3rqU.inv q3tlZeta3U`（ζ₃⁻¹）・剛性 `q3m3r_cyclotome_fixed` で恒等固定 |
| tmz 側（mod-3 層） | `tmzG 0 = cmrGrp 1` = μ₃ ⊂ ℚ(ζ₃)（大域実円分体） | 離散対数 `ctmFind 1`・生成元 `cmrZeta 1`・実 Galois 作用 `cgarAct 1`（σ y = ζ^{χ(σ)·find y}・`cgar_rigidity`）・非自明元 `cgarSigma2 1`（χ=2・`cgar_sigma2_exp`）・射影 `limitProj tmzSystem 0`・明示極限元 `tmeZetaLim`（.val 0 = cmrZeta 1） |
| tmi 側（不定性の主語） | `zpsLimit`（実 ℤ₃^×）→ Aut(tmzLimit) | `tmiFromUnits u` = 成分冪 y_n ↦ y_n^{(u.val n).val}（tmi:227）・`tmi_aut_classify`: 任意の同型はちょうど 1 つの u から来る |

grep 実測（二重計上の事前確認）: `Q3RamifiedQuadratic` を import するのはキャンペーン 5 ファイルのみで、そのどれも `TateModuleZ3`/`CyclotomicMuTower`/`tmzLimit` に触れない。逆方向も `q3rq` への言及ゼロ。**局所 μ₃ ↔ 大域 μ₃ の同一視は未建設**＝橋は genuinely new。

### 1.4 F-wild が要るもの（frontier §3 の named foundation・変更なし）

(i) ℚ₃(ζ_{3ⁿ})（n≥2）の整数環＋**単数群 Grp**、(ii) μ_{3ⁿ} 完全性の各レベル版、(iii) レベル 3ⁿ テータ群族と剛性、(iv) テータ内部 cyclotome 塔 ↔ tmzLimit の比較準同型（＝候補 A の塔版）、(v) 逆極限集約。frontier は (i) の**暴分岐単数の choice-free 逆元**を「genuinely open design problem」と旗を立てた——§3 で正面査定する。

---

## 2. 候補 A — 比較橋（level-3 kill → tmi の (ℤ/3)^× 商）の評価

### 2.1 中心判定: 実 G-同変同一視は建つか — **建つ（tier M・1 モジュール）**

**数学的内容**: テータ側 μ₃（局所・O_{ℚ₃(ζ₃)}=ℤ₃[√−3] の実単数群 U₂ 内）と tmz 側 μ₃（大域・実円分体 ℚ(ζ₃) 内・`tmzG 0`）の、**選ばれた実生成元同士を突き合わせる群同一視** β: tmzG 0 → U₂（像 = μ₃）、および両側の**実自己同型**（大域: `cgarAct 1` の実体自己同型 σ₂・局所: 実環自己同型 `q3rqConj`）に関する同変性。

**choice-free 構成（決定的な点）**: β の定義に選択は要らない——tmz 側には離散対数 `ctmFind 1` が既にあり（`ctmFind_spec` で仕様証明済み・cmr:616/687）、

```
q3mbU (y : (tmzG 0).carrier) : q3rqU.carrier := Grp.pow q3rqU q3tlZeta3U (ctmFind 1 h y.val)
```

は閉じた式。逆向き（U₂ の μ₃ 元→ tmzG 0）を函数にするには z3.carrier の等号判定が要り Markov に触れるため**作らない**——単射性＋像の μ₃ 特徴付け（`q3mc_mu3_complete` 消費）の消去形で「同一視」を述べる（QpUnits/L₂^× 提示と同じ正直さ）。

**同変性が本物である理由**: 両側の作用が**実自己同型**である。大域側 σ₂=`cgarSigma2 1` は実体 ℚ(ζ₃) の実代入自己同型で σ₂y = y²（`cgar_rigidity`＋`cgar_sigma2_exp`: χ(σ₂)=2）。局所側 `q3rqConj` は実環 ℤ₃[√−3] の実環自己同型で ζ₃↦ζ₃²（q3m3r_aut_mu3_nontrivial で既証明）。β の同変性 β(σ₂y) = q3rqConj(β y) は両辺 = ζ^{2·find y} の指数計算で閉じる。Bool/Fin ラベルの身代わりは一切現れない——主語は実担体の実元。

**敵対的自問（「位数 3 の群は全部同型・空虚では？」）への答え**: 空虚でない理由は 3 つ。(i) β 単独ではなく**同変性**（両側の実 Galois/共役作用の互換）込みで初めて「cyclotome の同一視」になる——これは χ mod 3 と conj の突き合わせという算術的内容を持つ。(ii) 橋の**目的地**は同型の存在ではなく §2.3 の輸送定理——tmi の実不定性対象 `zpsLimit` の実作用 `tmiFromUnits` を、この同一視を通してテータ内部 μ₃ 上の要求に翻訳し、剛性で殺す。同型の存在だけなら安いが、**輸送して殺す**ところに実消費（tmiFromUnits の本体＝成分冪・q3m3r_cyclotome_fixed・q3mc）がある。(iii) 生成元突き合わせには ℤ/2 の曖昧さ（ζ↦ζ vs ζ↦ζ²）が本質的に残るが、**kill の言明はこの曖昧さで不変**（Aut(μ₃) 可換ゆえ、β を反転で取り替えても冪写像の輸送指数は不変: β'(y)=β(y)² なら β'(y^{u₀})=(β'(y))^{u₀}）——これを補題 `q3mb_flip_invariant` で機械証明し、正直な限定に「同一視は生成元指定つき・ℤ/2 曖昧・kill は曖昧さ不変」と明記する。

### 2.2 Lean スケッチ（`IUT/Q3Mu3TmzBridge.lean`・prefix `q3mb`・tier M）

**deps**: `IUT.Q3Mu3Rigidity`（剛性・q3m3rZeta）・`IUT.Q3Mu3Completeness`（μ₃ 完全性）・`IUT.TateModuleIndeterminacy`（tmiFromUnits・**初の意図的 firewall 越え**）・`IUT.TateModuleZ3`・`IUT.CyclotomicGKActionReal`・`IUT.Zmod3PowUnitsSystem`。新規 axiom なし・choice-free・禁止タクティク不使用。

| # | 定理/定義 | 内容 | 部品（全て実在確認済み） |
|---|---|---|---|
| 1 | `q3mb_conj_norm` | N(q3rqConj x)=N(x)（conj を U₂ へ持ち上げる） | 成分計算（neg·neg）・tier S |
| 2 | `q3mbConjU : q3rqU.carrier → q3rqU.carrier`＋`q3mb_conjU_mul` | 実共役の単数群化 | q3rq_conj_mul＋#1 |
| 3 | `q3mb_zeta_pow_mod` | Grp.pow q3rqU ζU (e % 3) = pow ζU e | q3tl_zeta3U 立方（q3tl:84） |
| 4 | **`q3mbU`／`q3mbHom : Hom (tmzG 0) q3rqU`（★橋）** | y ↦ ζU^{find y}・map_mul | `tmz_mul_find`（ℓ=1）＋#3 |
| 5 | `q3mb_inj` | β 単射（find<3 の 3 元・ζ≠1・ζ²≠1・ζ≠ζ²） | q3rq_zeta_ne_one 系＋h≠−h |
| 6 | `q3mb_image_mu3`／`q3mb_onto_mu3` | 像 ⊆ μ₃、および u³=1 ⟹ ∃y, β y = u（∃ は Prop 内） | **q3mc_mu3_complete 消費** |
| 7 | **`q3mb_equivariant`（★同変性）** | β(σy) = pow (β y) χ(σ)（∀σ∈ctlGal 0）＋ β(σ₂y) = q3mbConjU(β y) | cgar_rigidity・cgar_sigma2_exp・conj ζ=ζ² |
| 8 | `q3mb_flip_invariant` | 生成元反転で輸送指数不変（§2.1(iii)） | 可換冪計算 |
| 9 | `q3mbInt : (tmzG 0).carrier → q3m3Car` | 内部版橋: y ↦ (((0, pow (inv ζU) (find y)), 0), 1)（内部生成元 q3m3rZeta と整合） | #4 の内部読み替え |
| 10 | **`q3mb_transport`（★輸送）** | β∘(tmiFromUnits u の level-0 成分) = (β の u₀ 乗)。すなわち q3mbInt(((tmiFromUnits u).map t).val 0) = 「q3mbInt(t.val 0) の u₀ 冪」（u₀=(u.val 0).val） | tmiFromUnits 本体（成分冪）＋#4 |
| 11 | **`q3mb_kill_mod3`（★★★ display-moving 主定理）** | u : zpsLimit・φ テータ両立（hHom/hMem/hE3）が「橋輸送で tmiFromUnits u を内部 μ₃ 上に実現」（∀t, φ(q3mbInt(t.val 0)) = q3mbInt(((tmiFromUnits u).map t).val 0)）ならば **(u.val 0).val = 1** | 証明: t=tmeZetaLim（明示・choice-free）で左辺 = φ(q3m3rZeta)=q3m3rZeta（**q3m3r_cyclotome_fixed 消費**）・右辺 = ζ_int^{u₀}・u₀∈{1,2}（単数）・u₀=2 なら ζ_int=ζ_int²（h≠−h に矛盾） |
| 12 | `q3mb_admissible_iff` | 逆向き: u₀=1 なら φ=id が実現 ⟹ **「テータ実現可能 ⟺ u₀=1」の消去形 iff** | pow_one 計算 |
| 13 | `Q3Mu3TmzBridgeData`／`q3mbData`／`q3mb_exists` | capstone | — |

規模: 550–900 行。tier M（opus）——新イディオムなし（離散対数・冪簿記・成分計算の既確立 3 系統の融合）。詰まり得る箇所は #5 の 9 分岐簿記と #11 の内部成分読みだけで、必要なら fable スポット 1 点。

**#11+#12 が言えるようになる言明（過大主張しない正確な形)**: 「実 ℤ₃(1)=tmzLimit の任意の自己同型は実単元 u∈ℤ₃^× から来る（tmi_aut_classify・消費のみ）。その mod-3 読み u₀ が 1 でない（＝(ℤ/3)^× の非自明元に落ちる）なら、その作用の mod-3 層を橋で読んだテータ内部 μ₃ 上の捻りは、**いかなるテータ両立自己準同型でも実現不可能**（level-3 mono-theta 剛性）。すなわちテータ剛性は tmi の実不定性 ℤ₃^× の **(ℤ/3)^× 商を、実対象の上で殺す**。」——再監査上限 #1（機構レベル・比較橋なし）の正面 discharge。

### 2.3 二重計上境界（vs tmi・vs crl・vs q3m3r）

- **vs tmi（A7・ℤ₃^× の特徴付け）**: tmi は Aut(ℤ₃(1))≅zpsLimit を**特徴付ける**（CHARACTERIZE・全レベル・極限）。橋は tmiFromUnits／tmi_aut_classify を**消費のみ**（再証明ゼロ・言明の複製ゼロ）。NEW は「局所テータ μ₃ ↔ tmz mod-3 層の同変同一視」＋「輸送＋実現不可能性」で、tmi のどの定理とも主語が異なる。tmi の正直限定 (1)「CHARACTERIZE であって KILL しない」は**消さない**——橋の kill は mod-3 商・テータ両立クラス限定であり、tmi の宣言（full ℤ₃^× が Galois 同変性だけでは絞れない）はそのまま真。
- **vs crl（A6・復元側 T̂≅T の Ξ）**: crl の辺は「復元 zmod 塔 ↔ 実 μ 塔」（両方 tmz 系・大域・全レベル）。橋の辺は「**局所テータ環境の μ₃** ↔ 実 μ 塔の mod-3 層」——別の辺・別の主語。A6 は一切主張しない（graph-meta の A6 note 不変更）。
- **vs q3m3r（R4）**: 剛性は消費のみ。橋は q3m3r の正直限定 5「tmzLimit への比較橋は含めない」を**後続モジュールとして** discharge するのであって、q3m3r の限定文自体は消さない（追記のみ: 「→ q3mb で discharge」）。

### 2.4 正直な限定（橋モジュールのヘッダに書くべきもの）

1. **mod-3 層（level 0）のみ**。tmzLimit 全体との橋（塔版・F-wild (iv)）ではない。1+3ℤ₃・n≥2 は依然 SURVIVES——tmi の残存宣言は不変更。
2. 同一視は**群レベル・生成元指定つき**（ℤ/2 曖昧・kill は曖昧さ不変を機械証明）。実埋め込み ℚ(ζ₃)↪ℚ₃(ζ₃)（体・環レベルの局所大域比較・分解群理論）は形式化しない。
3. テータ側の Galois は位数 2 の実共役 `q3rqConj` のみ（実 G_{ℚ₃} 不在——R1 限定 7 継承）。
4. q=27 忠実部分ケース・endo 定式化・実テータ関数/π₁/大域 Galois 0（R2b–R4 の限定を全部継承）。

### 2.5 動かす台帳項目と見込み

**A7 をさらに動かす**（A6 ではない）。再監査が 0.50 を拒んだ 2 理由のうち #1（機構レベル・橋なし）を正面 discharge。#2（mod-3 のみ）は残る。敵対的見込み: **A7 0.47 → 0.49–0.51**（下振れ 0.48）。§5 の算術により **0.49 以上で表示 53→54**。

---

## 3. 候補 B — F-wild 塔の評価: 暴分岐単数逆元は割れるか

### 3.1 既存資産の実測（本体確認）

- **towerLevel（M109・EisTowerRings.lean:289）**: LT 塔 O_{n+1} = O_n[[Y]]/(π Y + Y^p − λ) の**環骨格は全レベル実在**（Quot 提示・塔関係式 f(λ')=ι(λ)・捻れ [π^{n+1}]λ_{n+1}=0）。p=3 で数学的には 3-冪円分塔。**しかし正直申告どおり**: 単数群 Grp 化ゼロ・μ の内部実在ゼロ（ζ₃ すら未構成）・n≥2 の座標忠実性は M122 が「次層」と明記（M122 は level 0 の Weierstrass 割り算まで）。この経路で単数逆元を作るには n≥2 の座標理論が先に要り、**この経路は依然遠い**。
- **付値簿記**: M222F/M226F は塔遷移像の exact 付値 v(ι(λₙ))=p まで到達（分岐入力 v(π)≥p は明示仮定）。単数群には未接続。

### 3.2 中心査定: 「暴分岐単数の choice-free 逆元」は open か — **設計レベルで割れた（相対 Kummer 共役ノルム）**

frontier §3 は「暴分岐では共役ノルム閉形式が消え、λ-adic 幾何級数逆元が必要（open）」とした。**この前提が過剰に悲観的だった**ことを指摘する。鍵は R1 の成果そのもの:

> **μ₃ ⊂ O_{L₂} が実在する**（q3rqZeta・q3rq_zeta_cube）。ゆえに wild 第一段 M = ℚ₃(ζ₉) は L₂ 上の **Kummer 巡回 3 次拡大** M = L₂[Y]/(Y³ − ζ₃)（ζ₉³=ζ₃・O_M = O_{L₂}[ζ₉]、O_{L₂}-基底 {1, ζ₉, ζ₉²}——ζ₉⁴=ζ₃ζ₉, ζ₉⁵=ζ₃ζ₉² で閉じる）であり、相対 Galois σ: Y↦ζ₃Y は**座標スケーリングの閉形式** σ(a,b,c) = (a, ζ₃b, ζ₃²c)。

これで逆元は R1 と同じ共役ノルム型で閉じる:

- **台**: `q3kCar := q3rqCar × q3rqCar × q3rqCar`、積は Y³=d（d=q3rqZeta）の巡回畳み込み `(a,b,c)(a',b',c') = (aa'+d(bc'+cb'), ab'+ba'+dcc', ac'+bb'+ca')`。環法則は q3rq の写経（3 成分版・O_{L₂} 係数）。
- **相対ノルム**: N(x) := x·σ(x)·σ²(x)。σ が環準同型であること（ζ₃³=1 の成分計算・ζ⁴=ζ）と N の σ-不変性から、N(x) の Y-成分は (ζ₃−1)·(成分)=0 型の方程式に落ち、**(ζ₃−1) の正則性**（N_{L₂/ℚ₃}(ζ₃−1)=3——実測: ζ₃−1=(−h−1,h)・N=(3h)²+3h²=12h²=3——と 3-正則性 `q3mc_three_mul_zero` の対版）で消える ⟹ **N(x) = (n, 0, 0)・n ∈ O_{L₂} が定理**。R1 が機械的多項式恒等式を x·x̄=(N,0) の環準同型ルートで回避したのと同じ構図の 3 次版。
- **逆元（★ 閉形式・choice-free）**: `q3kInv x = σ(x)·σ²(x)·(q3rqInv n h)`——**R1 の q3rqInv を消費**。単数判定は `IsZpUnit 3 (q3rqNorm n)`（総ノルム O_M→O_{L₂}→ℤ₃ のレベル 1 剰余）＝既存判定と同形。幾何級数・λ-adic 収束・Markov・choice は**一切不要**。
- **反復性（F-wild 全体への含意）**: 各段 M_{n+1}/M_n も μ₃ ⊂ L₂ ⊆ M_n ゆえ Kummer Y³=ζ_{3ⁿ} であり、**「CRing R＋単数 d＋（必要なら μ₃）上の巡回 3 次捻り代数」を汎用モジュール 1 本**にすれば塔全体の環＋単数群が同じ部品で昇れる。frontier の (i) はこの分だけ規模が縮む。

**結論: 「wild-unit choice-free inverse」は open problem ではなくなった**（設計解あり・実装は tier M/L の物量）。ただし本査定は設計レベルであり、σ-環準同型性と N∈O_{L₂} の成分計算量（3 成分×q3rq 対＝実質 6 座標）は R1 の「8 項簿記」の約 2–3 倍の物量と見込む。

### 3.3 残る最難関と真の規模（正直申告）

逆元が割れた結果、**最難関は μ₉ 完全性に移る**: level-9 テータの mem_iff の急所「U₃ 内 u⁹=1 ⟹ u∈μ₉」。R2a（q3mc）の枝分析は 2 成分×立方だったが、今度は **3 成分（O_{L₂} 係数）× 9 乗**で、剰余体 𝔽₃ 上の分岐簿記（π₉=ζ₉−1・e=6）が絡む。q3mc のレベルシフト帰納は移植可能と見るが、枝の数と witness 消去の物量は未 de-risk——**専用詳細化（fable 1 枠）が必須**。その他: L₂^×↪M^× の分岐 3 実現（λ と π₉³ の単数差の明示）・q=3⁹ の指数簿記（v_π(q)=54）・一般 n の汎用 Kummer 段・橋の塔版・極限集約。

**真の規模（改訂見積り）**: 初弾 `Q3KummerCubic.lean`（環＋σ＋N＋逆元＋U₃＋実 ζ₉＝(0,1,0)・位数 9）は 900–1400 行・tier M/L・**1 ラウンドで建つ**。level-9 kill まで 6–8 モジュール・2–3 ラウンド。full ℤ₃^× kill（一般 n＋極限＋橋塔）は依然 **12–18 モジュール・3–5 ラウンド以上**（frontier の見積りを維持——(i) が軽くなった分は (ii) μ_{3ⁿ} 完全性の重さで相殺）。**表示への効き**: B の初弾単体は complete_pct 丸め値 0 前進（foundation）を正直申告することになる。

---

## 4. 結論・推奨

**推奨 = 候補 A（比較橋）を次ラウンドで実装する。**

| 項目 | 内容 |
|---|---|
| ファイル/prefix | `IUT/Q3Mu3TmzBridge.lean`／`q3mb`（1 モジュール・550–900 行） |
| tier/model | **M（opus）**・詰まったら fable スポット 1 点（§2.2 #5/#11 想定） |
| 分類 | [実／昇格(a)]——R4 の kill を「機構レベル」から「tmi の実 ℤ₃^× 対象の (ℤ/3)^× 商への kill」へ昇格（再監査上限 #1 の正面 discharge） |
| status 見込み | A7 0.47 → **0.49–0.51**（敵対的下振れ 0.48）。0.49 以上で柱 A 表示 53→**54**（§5） |
| 二重計上 | なし（§2.3——tmi/crl/q3m3r は消費のみ・辺が全て新規） |

**理由**: (i) A は監査が名指しした上限 #1 をちょうど 1 モジュールで discharge し、B は最初の表示前進まで 2–3 ラウンド。(ii) A の部品は全て実在確認済みでリスク最小、B は μ₉ 完全性という未 de-risk の tier-L 山を含む。(iii) A の橋イディオム（μ 層の同変同一視＋輸送）は F-wild (iv)（橋の塔版）の**テンプレート**であり、A→B の順に無駄がない。(iv) §5 の算術訂正により A は表示を動かし得る唯一の 1 ラウンド手。

**B は「blocked」ではない**（§3.2 で逆元は割れた）——A の次のラウンドから `Q3KummerCubic`（opus）＋μ₉ 完全性詳細化（fable）で着工するのが正順。ピボット（他柱）・consolidate は不要: 本コースを実際に進める tractable な手が 2 本ある。

---

## 5. status 算術（実測・訂正あり）

`target_ledger.json` 実測: 柱 A 総 weight=100・A7 weight=12・status=0.47・**A7 以外の定数 = 47.62**（Σ w·s = 47.62 + 12s。監査記載の定数 47.62 は正確 ✓・現 Σ_A = 53.26 → 表示 53 ✓）。

**訂正（重要）**: `compute_complete_pct.py` は `round(num/den*100)`。実測:

| A7 status | Σ_A | 表示 |
|---|---|---|
| 0.47（現在） | 53.26 | **53** |
| 0.48 | 53.38 | 53 |
| **0.49** | **53.50** | **54**（実測 round(53.50000…)=54） |
| 0.50 | 53.62 | 54 |
| 0.54 | 54.10 | 54 |

再監査 reaudit-A7-level3-kill-2026-07-11.md の「0.46–0.50 は全て 53 表示・54 には A7≥0.54 が要る」および graph-meta.json の同文は**算術誤り**（frontier 文書の「0.50 なら 54」が正しい）。次ラウンドの報告でこの訂正を明記し、graph-meta の note は**追記で**訂正する（過去監査の status 値 0.47 自体は不変更——誤っていたのは表示閾値の注記のみ）。

**各候補の効き（正直）**:
- **候補 A**: A7 0.49–0.51 なら柱 A **53→54**（+1 表示）。敵対的監査が「mod-3 層のみ・体埋め込みなし」を重く見て 0.48 に留めれば **53 据え置き**——その場合も上限 #1 の discharge は次段（F-wild）の status 天井を引き上げる。他項目は動かさない（A6 不主張）。
- **候補 B 初弾**: A7 据え置き見込み（foundation・0 前進申告）。表示 53 のまま。full F-wild 完了（0.60–0.70）で 54.8–56.0 → 55–56——3–5 ラウンド以上先。
- 正直な総括: **どちらも今ラウンドの表示は 53 のままの可能性が高い**が、A のみ 54 到達の現実的確率を持つ（監査 0.49 の攻防）。

---

## 6. 実装計画（次統合ラウンド・5 並列の埋め方）

| 枠 | タスク | tier/model | complete_pct への関係 |
|---|---|---|---|
| 1 | **`Q3Mu3TmzBridge.lean`（q3mb・§2.2 の 13 項）** | **M / opus** | **A7 0.47→0.49–0.51（display-moving 候補）** |
| 2 | `Q3KummerCubic.lean` 前半（巡回 3 次捻り代数の環法則＋σ 環準同型・§3.2） | M / opus | F-wild (i) foundation（0 前進申告） |
| 3 | μ₉ 完全性の詳細化ラウンド（§3.3 の最難関の段階分解・設計のみ） | **L / fable** | F-wild (ii) の de-risk |
| 4 | 他柱の独立実仕事（柱 B/C/E の complete_pct 残地・親が選定） | M / opus | 他柱 |
| 5 | ドキュメント同期（graph-meta 注記の算術訂正の追記・q3m3r 限定 5 への「→q3mb」追記・dashboard 整合） | S / sonnet | 表示整合（水増しなし・§5 訂正の反映） |

直列依存: 枠 1 は独立で即着工可（部品全て実在）。枠 2 は枠 3 の設計を待たない（環＋逆元は §3.2 で分解済み・μ₉ 完全性だけが枠 3 待ち）。統合時に親が IUT.lean/build.sh/graph を一括更新・`gen_graph.py` 再実行。ラウンド報告は「A7 の status 前進を主指標・表示は 53 か 54 かは監査 0.49 の攻防」と正直に書く。

**ブロッカー報告**: なし。両候補とも blocked ではない。唯一の未 de-risk 山は F-wild の μ₉ 完全性（枠 3 で先に設計する）。

---
*作成: 詳細化ラウンド（設計のみ・Lean 実装なし）。判定は全て対象 .lean の def/theorem 本体の読解による（q3m3r 全文・tmz 全文・tmi 全文・q3rq 本体・q3mc ヘッダ＋定理列・q3tl 該当行・crl ヘッダ＋定義列・cgar/cmr/ctmFind の該当 def・M109 towerLevel 本体・M122/M226F ヘッダ・target_ledger.json/compute_complete_pct.py/graph-meta.json 実測・reaudit-A7-level3-kill-2026-07-11.md・frontier-z3x-kill-mu3n-theta-detail-2026-07-11.md）。grep 裏取り: q3rq を import する円分側モジュール 0 件＝橋は genuinely new。*
