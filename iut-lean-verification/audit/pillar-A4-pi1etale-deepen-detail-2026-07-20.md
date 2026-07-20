# A4 実 π₁^ét 深化スライス詳細化（0.56 の次の実増分の到達可能性）— 2026-07-20

**分類: [設計のみ / design-only]・tier-L 詳細化・complete_pct 0 前進（Lean コードなし・共有ファイル変更なし）・§4 規約遵守（既存の正直な限定を消さない・弱めない・過大主張しない）**

- 対象: 柱A **A4**「実 π₁^ét（双曲的曲線/Spec の実プロファイナイト基本群）」
  （**weight 14 = 柱A 最大重み**・現 s_A4 = **0.56**・`target_ledger.json` 実測）。
- 手法: `audit/pillar-A6-monotheta-kill-detail-2026-07-11.md` と同じ **disproof-first
  到達可能性検査**。候補 3 方向 (a) 算術完全列 1→π₁^geom→π₁^arith→G→1 と実外 Galois
  作用／(b) SGA1 punctured/双曲的完全列／(c) 具体的双曲的曲線（tripod・once-punctured E）
  の π₁^ét——を敵対的に検査し、対象不一致・A3/A5/A7/A9 二重計上・choice 障害を攻撃する。
- 結論の先出し: **候補 (a) は到達可能（research-blocked ではない）**。A4 監査 2 本
  （`reaudit-A4-pi1-etale-tate-2026-07-11.md` §5・`reaudit-q9td-twodir-a4-2026-07-11.md`
  §4.2）が **blocker として名指しした「G_{ℚ₃} 外作用ゼロ」**は、その後に完成した
  A7b `tmzActHom`（実 profinite Gal の ℤ₃(1) への実作用・`IUT/TateModuleZ3.lean`）と
  A3 `ctlProfinite`/`cliChar`（実 profinite Galois 塔極限と指標）により、**既存資産の
  接続＋atp 既確立イディオムの再インスタンスだけで discharge 可能**に変わっている。
  候補 (b) は research-blocked、候補 (c) は A9 計上と衝突（本書で正直に却下）。

---

## 0. TL;DR

| 問い | 答え |
|---|---|
| 次の実増分は到達可能か | **YES（候補 (a)・research-blocked でない）** |
| 本命 | **AP: 実算術 π₁^ét 完全列スライス**（新規 1 ファイル `IUT/Q3EtaleArithPi1.lean`・prefix `q3ap`・opus 1 枠）。Π^arith := (ℤ₃(1) × ℤ₃) ⋊ Gal(ℚ(ζ_{3^∞})/ℚ)——**両側とも実 profinite**（geom = q9td 二方向 π₁ 対象・G = A3 `ctlProfinite`）——の半直積建設・完全列 1→π₁^geom→Π^arith→G→1・**外 Galois 定理 s(σ)·ι(z)·s(σ)⁻¹ = ι(σ·z)**・**実曲線 E_{3⁹}[9] 作用の χ 同変性**（q9td μ 方向作用が Galois で χ 捻れすることを実曲線上で可視化） |
| s_A4 見込み（保守） | 0.56 → 中央値 **0.58（+0.02）**・敵対的下限 0.57（+0.01）・楽観 0.59。w=14 ゆえ +0.02 で Σ_A 寄与 **+0.28 表示ポイント** |
| 柱A 表示 | Σ_A 実測 56.56（表示 57）→ +0.02 で 56.84 → **表示 57 据え置き**（表示 58 には Δs_A4 ≥ 0.067 が必要＝単独では届かない）。**表示 mover を主張しない**で正直に報告する |
| research-blocked（正直申告） | (i) **候補 (b) SGA1 punctured 完全列**——スキーム・エタールサイト・punctured 曲線対象が皆無（punctured 側は tempered=A5 の主語で q9nt が担当済み）。(ii) **full ẑ×ẑ(1) と非分裂 T₃E 拡大**（Kummer コサイクル σ(3^{1/3})/3^{1/3} は実 ℚ₃(ζ₂₇,3^{1/3}) 建設が前提・named future target）。(iii) **実局所 G_{ℚ₃} そのもの**（リポジトリの実 Galois は ℚ 上円分切片のみ・tmz (iii) 継承） |
| 却下（二重計上防止） | 候補 (c) tripod π₁^ét は **A9 の BLW 梯子**（kmu が 2026-07-20 に A9 +0.02 で計上済み・F₂=BLW-1 は A9 named future）——A4 で建てると二重計上。once-punctured E の非可換 π₁ は A5（q9nt 計上済み）の主語 |

---

## 1. 正確なギャップ（何が有り・何が無いか）

### 1.1 A4 が現在持っているもの（0.56 の内訳・全て本体確認済み）

| 資産 | ファイル / 主対象 | 内容 | 計上 |
|---|---|---|---|
| A4a | `IUT/Q3TatePi1Etale.lean`（q3pe） | π₁^ét 格子スライス `q3pePi1 l = ℤ_l`（真の逆極限 `limitGrp (padicSystem l)`）の実 Tate 被覆塔 E_{q^{l^k}}(ℚ₃) への作用 `q3peLimitAct`・段間自然性 `q3pe_limit_act_natural`・逆極限忠実性 `q3pe_limit_faithful`・ファイバー＝軌道 `q3pe_fiber_orbit` | 0.55 の主因 |
| A4b | `IUT/Q3TatePi1Comparison.lean`（q3pc） | 普遍性 `q3pc_pi1_universal`・完備化両立・surrogate 昇格 `q3pcSurrogateAct`（裸 ẑ が実曲線に作用） | 同上 |
| A4c | `IUT/Q3Etale9TwoDir.lean`（q9td） | **二方向 π₁^ét 作用**: 格子指標 `q9tdLatChar : Hom (q3pePi1 3) (zmod 9)`・μ 指標 `q9tdMuChar : Hom tmzLimit (zmod 9)`（:464/:471）・二方向 GAction `q9tdLatAct`/`q9tdMuAct`・E[9]≅(ℤ/9)² 分解 `q9td_e9_decomp`・実曲線実現 `q9td_lat_realize`/`q9td_mu_realize`（φ(act p) = [3]/[ζ₉] 平行移動） | 0.55→0.56 |
| 基盤 | `IUT/ProfinitePi1.lean`・`IUT/GrothendieckGalois.lean`・`IUT/GaloisPi1Iso.lean` | lim Gal 機構・π₁=Aut(F)・副有限位相（progress 側） | 既算入 |

### 1.2 blocker の名指し状況（両監査の一致点）

- q3pe/q3pc ヘッダ正直限定 (3)（`Q3TatePi1Etale.lean:28-29`）:
  「μ 方向 ℤ₃(1) との積・Weil ペアリング・**G_{ℚ₃} 外作用は本ステップで一切構成しない**」。
  μ 方向の積は q9td が discharge 済み。**外 Galois 作用と Weil スライスが未 discharge の
  named 残欠**。
- `reaudit-A4-pi1-etale-tate-2026-07-11.md` §5 の 0.6 到達 blocker (i)–(vi) のうち
  「G_{ℚ₃} 外作用」該当分、および `reaudit-q9td-twodir-a4-2026-07-11.md` §4.2 下げ要因 5:
  「位相/エタールサイト/**G_{ℚ₃}**/anabelian 逆再構成ゼロ」。
- すなわち「算術列の不在」は threshold-shopping でなく **両監査が blocker として名指しした
  named defect** であり、q9td（μ 方向 named-defect discharge で +0.01）と同型の正当な標的。

### 1.3 その後に建った資産（ギャップを閉じる材料・全て監査済み or foundation）

| 資産 | 実体 | 帰属 |
|---|---|---|
| `ctlProfinite`（`IUT/CyclotomicTowerLimit.lean`） | 実 profinite Gal(ℚ(ζ_{3^∞})/ℚ) = lim Gal(ℚ(ζ_{3^{n+1}})/ℚ)（実体自己同型群の逆極限・witness 初 discharge） | A3 |
| `cliChar`/`cliTo`/`cliFrom`/`CliIsoData`（`IUT/CyclotomicLimitIso.lean`） | 極限指標同型 Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^×（各段 `cciToUnits`/`cciFromUnits`） | A3 |
| `cgarAct`（`IUT/CyclotomicGKActionReal.lean`） | 実 Gal(ℚ(ζ_{3^ℓ})/ℚ) の実 μ_{3^ℓ} への体自己同型制限作用・非自明 χ | A7a |
| **`tmzActHom`・`tmz_act_char`・`tmzGModule`**（`IUT/TateModuleZ3.lean:300/318/344`） | **実 profinite Gal の T=ℤ₃(1)=tmzLimit への実作用**・作用は χ 冪 ((tmzActHom s) y).val n = ζ^{χ_n(s)·find(y_n)}・act_one/act_mul（G-加群公理） | A7b |
| `q3tpGalAct`（`IUT/Q3TemperedPi1.lean:136`） | ctlProfinite の tempered 直積 tmzLimit×ℤ への作用（μ に tmzActHom・deck 固定） | A5b |
| `atpGroup`（`IUT/ArithTemperedPi1.lean`・M429F） | **代理**算術 tempered 半直積 tpeGroup ⋊_χ ℤ・完全列・外 Galois 定理——ただし正直限定「算術商は**実 G_K（非可換副有限）でなく**円分指標像のモデル ℤ・(ℤ/n)^× 値実 χ の作用には**副有限シクロトームが必要で後続**」（:65-69） | 柱A（tempered 系） |
| `tmz_find_pow`/`tmz_mul_find`/`q3mb_find_pow`/`cra_find_zeta` | 離散対数 ctmFind の準同型・冪則・find(ζ)=1（q9td/q3mb/q9mb で消費実績） | A7 系 |

### 1.4 ギャップの正体（本書の問い）

A4 は「π₁^geom スライス（格子×μ）が実曲線に作用する」まで持ち、A7b は「実 Gal が μ 方向
ℤ₃(1) に χ で作用する」まで持つ。**両者を束ねる算術基本群——完全列
1 → π₁^geom → Π^arith → G → 1 の実 Lean 群・切断・外 Galois 定理（共役 = Galois 作用）・
その E[9] 実曲線作用への同変性——はコードベースのどこにも存在しない**（grep 実測:
étale 側対象を台とする半直積群はゼロ。半直積は tempered 系 8 ファイルのみで、算術商が実
profinite なものは皆無）。[IUTchI] §2 が入力とする Π_X → G_K の形の実インスタンスが A4 の
次の一手である。

---

## 2. Disproof-first 検査

### 2.1 攻撃 1（最重要）: 部品は同じ Lean 対象の上に居るか（対象不一致の攻撃）

**判定: YES——接続は文字通り型が合う。** 実測:

| 役割 | 供給側 | 消費形 | 一致? |
|---|---|---|---|
| π₁^geom μ 方向 | `tmzLimit`（TMZ・A7） | `q9tdMuChar : Hom tmzLimit (zmod 9)`（q9td:471・A4） | **同一 def** |
| π₁^geom 格子方向 | `q3pePi1 3 = Zp 3`（q3pe・A4） | `q9tdLatChar : Hom (q3pePi1 3) (zmod 9)`（q9td:464） | **同一 def** |
| Galois 作用 | `tmzActHom : ctlProfinite.carrier → Hom tmzLimit tmzLimit`（TMZ:300） | 半直積の捻り・外 Galois 定理の右辺 | **そのまま型が合う** |
| 指標 | `cliChar n : Hom (ctlGal n) (zpsG n)`（cli） | n=1 で χ₉ : Gal 段 → (ℤ/9)^× | 同一 def |
| 実曲線 | `q9tlCurve = E_{3⁹}`・`q9td_mu_realize` | 同変性の着地先 | 同一 def |

核心の計算が既存定理で閉じることの検証（設計時手計算済み）:
`q9tdMuChar.map ((tmzActHom σ).map s)` は定義展開で `mk (ctmFind 2 ((tmzActHom σ s).val 1).val)`、
`tmz_act_char σ s 1`（TMZ:318）で `(tmzActHom σ s).val 1 = pow ζ₉ (χ₁(σ)·find(s₁))`、
`tmz_find_pow`（ℓ=2）で `find = (χ₁(σ)·find(s₁)) % 9`、`Quot.sound` と「mk(k·a) = (mk a) の
k 回冪」（zmod 加法群の npow・帰納 1 本）で

> **q3ap_mu_equivariant**: `q9tdMuChar((tmzActHom σ) s) = tateNpow (zmod 9) (q9tdMuChar s) χ₉(σ)`
> （χ₉(σ) := ((cliChar 1).map (σ.val 1)).val）

が落ちる。新機構・choice・翻訳層は不要。`q3mb_find_pow`（`Q3Mu3TmzBridge.lean:204`・
find∘pow = (k·find)%3^ℓ）が ℓ=1 で同型の証明を既に完遂しており、ℓ=2 はその写経。

### 2.2 攻撃 2: 半直積 Π^arith は TmzGModule の形式的ラッパに過ぎないのでは？

**判定: ラッパで尽きない新言明が 3 点あるが、glue 割引は見込む。**

- **新規 1（A4 主語の新対象）**: 完全列 1 → π₁^geom → Π^arith → G → 1 と
  **外 Galois 定理 s(σ)·ι(z)·s(σ)⁻¹ = ι(tw σ z)**。TmzGModule（A7b）は「T が G-加群」という
  加群言明であり、拡大群・切断・共役実現・正規性はどこにもない。[IUTchI] §2 / SGA1 IX の
  算術基本群の定義的性質そのもので、A4 title（Spec/曲線の算術 π₁^ét）の直撃。
- **新規 2（実曲線への着地・本モジュール最強内容）**: `q3ap_mu_equivariant` を
  `q9td_mu_realize` に通した **実曲線同変性**——
  φ(q9tdMuAct(σ·s) p) = φ(p)·[ζ₉]^{χ₉(σ)·χ_μ(s)}、すなわち「**Galois で捻った π₁ 元の
  E_{3⁹} 上の μ 平行移動は元の平行移動の χ₉(σ) 乗**」。TmzGModule には曲線が無く、q9td には
  Galois が無い。共役形の系「s(σ)ι(z)s(σ)⁻¹ の E[9] 作用 = z の作用の χ 捻り」まで束ねると、
  算術 π₁ がファイバーに作用する描像の最初の実インスタンスになる。
- **新規 3（Weil スライス・任意檗）**: 指標座標上の実 μ₉ 値ペアリング
  ω((s,γ),(s',γ')) := ζ₉^{χ_μ(s)·χ_lat(γ') − χ_μ(s')·χ_lat(γ)} と、その **Galois 同変性
  ω(σx, σx') = ω(x,x')^{χ₉(σ)}**（∧²T ≅ ℤ₃(1) の mod-9 影・q3pe 限定 (3) の
  「Weil ペアリング」残欠に対応）。双線形性は座標定義の帰結（credit 低）だが χ 同変性は
  q3ap_mu_equivariant の実消費で非自明。theta 側 `q9mt_weil`（A7 foundation）とは主語が別
  （こちらは π₁ 指標座標上・q9mtGrp 非依存）で import しない。
- **割引すべき点（正直に）**: 半直積の群公理・完全列・共役公式の証明テンプレートは
  `atpGroup`（M429F）が抽象証明のイディオムを確立済み——新イディオム発明は 0。
  A6 crk 相場（既存資産 glue = +0.01〜0.02）を下限に、新対象（実 profinite 拡大群）＋
  実曲線同変性の分を上乗せする査定が妥当（§4）。

### 2.3 攻撃 3: A3／A7／A5 の再計上（二重計上）ではないか？

**判定: 主語で切れる。firewall を新ファイルヘッダに明記する。**

- **vs A3**（ctlProfinite・cli）: 消費のみ・再証明 0。A3 の主語は Galois 群そのもの／指標同型。
  Π^arith は「曲線側 π₁ の G による拡大」で A3 に存在しない。
- **vs A7**（tmzActHom・tmz_act_char・cgar）: 消費のみ。A7b の主語は「T=ℤ₃(1) の G-加群構造」。
  A4 の新主語は「算術 π₁ 拡大群＋その実曲線 E[9] 作用の同変性」。判定基準（q9td 監査 2.5 の
  再利用）: 各旗艦定理から Π^arith／q9td 指標を消去すると命題が消滅する。
- **vs A5**（q3tpGalAct・atpGroup）: 最も危険な攻撃。`q3tpGalAct`（A5b）は「ctlProfinite が
  tempered 直積 tmzLimit×**ℤ（離散）** に作用する」**単なる Hom 族**であり、(i) 拡大群・
  完全列・共役定理が無い、(ii) 台が tempered（離散 deck）で étale（`q3pePi1 3 = Zp 3` 副有限）
  でない、(iii) 曲線作用への同変性が無い。atpGroup は半直積だが**算術商が代理 ℤ・χ が
  {±1} 符号**で、その正直限定（:65-69）自身が「実 G_K（非可換副有限）・(ℤ/n)^× 値実 χ は
  後続」と本スライスを named future target として指名している——**M429F 正直限定の正面
  discharge = §2(a) 昇格**。firewall: 新ファイルは Q3TemperedPi1／ArithTemperedPi1 を
  import しない・A5 status を主張しない。
- **vs A4 自身（q9td の再ラベル）**: q9td の主語は「二方向作用の存在・忠実性・直交性」。
  Galois は q9td に一切登場しない（grep: q9td は ctlProfinite/tmzActHom を参照しない）。

### 2.4 攻撃 4: choice 障害・witness は閉形式か？

**判定: choice-free で閉じる。** (i) 半直積の群公理は `tmzGModule.act_one/act_mul`＋Hom の
map_mul から抽象的に落ちる（atp 先例・座標総当たり不要）。tw σ の可逆性は
act_mul σ σ⁻¹ ＋ act_one で閉形式。(ii) 外 Galois 非自明性の witness は両方閉形式:
G 側は **σ₂ 整合族** = `cliFrom.map u₂`（u₂ = 定数 2 の zpsLimit 整合族・zpsT は剰余ゆえ
2↦2 で整合・単元性は `zpuInvL`）、χ₉(σ₂)=2；T 側は **ζ 生成元整合族**
tζ := ⟨fun n => cmrZeta (n+1)⟩（整合性は `cra_find_zeta`（find ζ = 1）＋ tmzT の指数読み替え
で ζ↦ζ）。すると q3ap_mu_equivariant で χ₉(σ₂)·1 = 2 ≠ 1 = find(tζ)₁、よって
tw σ₂ tζ ≠ tζ が mk 2 ≠ mk 1（3∤1 で Quot 相異・q9td の相異イディオム）で落ちる。
(iii) ∃ は Prop ゴール内のみ。

### 2.5 攻撃 5: 候補 (b)(c) はなぜ却下か（正直な verdict）

- **(b) SGA1 punctured/双曲的完全列: research-blocked。** リポジトリにスキーム・エタール
  サイト・punctured 曲線対象が存在しない（q3pe 恒久限定 (4)）。punctured 側の非可換 π₁ は
  tempered＝**A5 の主語**で、q9nt（2026-07-20 計上）が wild level-9 実現を担当済み。
  tpeGroup の副有限完備化を「π₁^ét of punctured」と呼ぶ路線は、台が代理 Heisenberg ゆえ
  complete_pct を動かさない（toy 主語規約 §3 に抵触）。**梯子に載せない。**
- **(c) tripod／once-punctured E の π₁^ét: A9/A5 と衝突。** tripod の実被覆は A9 kmu
  （BLW-2・2026-07-20 に A9 +0.02 計上）の梯子であり、その塔化・F₂ 商は A9 の named future
  （BLW-1）。A4 で同じ対象を建てると帰属が割れる。**A9 に譲る**（本書は A4 の増分として
  数えない）。

### 2.6 disproof-first 総合判定

**候補 (a) は到達可能。** 「G_{ℚ₃} 外作用ゼロ」という両監査 blocker は、q9td 時点では
真だったが、A7b tmzActHom（実 profinite Gal の実作用）と A3 cli（実指標）が揃った現在は
**接続 1 ファイルの距離**にある——A6 crk・A5 q9nt と同型の「後続実装による判定失効」。
残る本質的未達（非分裂 T₃E・実局所 G_{ℚ₃}・スキーム位相）は §4 の帽子として正直に残す。

---

## 3. マイルストーン梯子（新規 1 ファイル・prefix `q3ap`・全 choice-free）

新ファイル `IUT/Q3EtaleArithPi1.lean`（450–650 行見込み）。import:
`IUT.TateModuleZ3`・`IUT.CyclotomicLimitIso`・`IUT.Q3Etale9TwoDir`（＝経由で
Q3TatePi1Etale/Q3TateCurveL9）。**Q3TemperedPi1・ArithTemperedPi1・Q3Mu9ThetaGroup は
import しない**（A5/A7 firewall）。共有ファイル変更なし。

| 段 | 内容 | 消費資産 | 難度 |
|---|---|---|---|
| **AP-0** | 幾何スライス `q3apGeom := prodGrp tmzLimit (q3pePi1 3)`・Galois 捻り `q3apTw σ : Hom q3apGeom q3apGeom = (tmzActHom σ) × id`・作用則 tw(1)=id・tw(στ)=tw σ∘tw τ・可逆性（act_mul＋act_one の抽象系） | `tmzGModule`（TMZ:344） | 低 |
| **AP-1** | 半直積 **Π^arith = q3apArith**: 台 q3apGeom.carrier × ctlProfinite.carrier・積 (z,σ)(z',σ') = (z · tw σ z', σσ')・群公理（atp イディオムの写経・抽象証明） | AP-0・atp 先例（import せず手法のみ） | 中の下 |
| **AP-2（★核）** | 算術完全列: ι 単射・pr 全射・ker(pr)=im(ι)・正規性・分裂切断 s(σ)=(1,σ)・**外 Galois 定理 s(σ)·ι(z)·s(σ)⁻¹ = ι(q3apTw σ z)**・**非自明性**（witness σ₂ 整合族 × ζ 生成元族 tζ・§2.4） | AP-0/1・`cliFrom`・`zpuInvL`・`cra_find_zeta` | 中 |
| **AP-3（★★ headline）** | **実曲線同変性 mod 9**: `q3ap_mu_equivariant`（q9tdMuChar∘tw σ = χ₉(σ) 冪・§2.1 の計算）・格子不変 `q3ap_lat_invariant`（tw は第 2 成分 id ゆえ rfl 級）・**実現形** φ(q9tdMuAct(tw σ s) p) = φ(p)·[ζ₉]^{χ₉(σ)·χ_μ(s)}（`q9td_mu_realize` 消費）・共役形の系（s(σ)ι(z)s(σ)⁻¹ の E[9] 作用 = χ 捻り） | `tmz_act_char`・`tmz_find_pow`・`q3mb_find_pow` 写経・`q9td_mu_realize` | 中 |
| **AP-4（任意檗）** | Weil スライス: 指標座標 μ₉ 値ペアリング ω と **Galois 同変性 ω(σx,σx') = ω(x,x')^{χ₉(σ)}**（q3pe 限定 (3)「Weil ペアリング」残欠の mod-9 discharge・双線形性は定義的と正直申告） | AP-3・`ctmPow` 算術 | 低〜中 |
| **AP-5** | capstone `Q3EtaleArithPi1Data`（完全列・外 Galois・曲線同変・非自明 witness を束ねる）/ witness / exists・正直限定の並置 | — | 低（束ね） |

新規イディオム: **0**（半直積公理は atp 写経・指標算術は q3mb/q9td 写経・witness は
定数族/生成元族の閉形式）。禁止タクティク不要。AP-4 が重ければ落として AP-0〜3+5 で
成立する（AP-4 は独立檗）。

---

## 4. 保守的 status forecast と、持ち越す A4 の帽子・限定

**verdict: 到達可能（research-blocked ではない）。**

**s_A4 予測（過大主張しない・独立監査が確定）**: 現 0.56 →
- 中央値 **0.58（+0.02）**: 両監査が名指しした blocker（G 外作用ゼロ）の正面 discharge＋
  A4 title の中核対象（算術 π₁^ét 拡大）の初実インスタンス＋実曲線同変性、という点で
  q9td（packaging・+0.01）より大きく、q3pe/q3pc（対象層まるごと新設・+0.05）より小さい。
  半直積テンプレが atp 既確立・作用本体が tmzActHom 消費である glue 性格が上限を抑える。
- 敵対的下限 **+0.01（0.57）**: 「TmzGModule の群ラッパ＋指標算術クローン」と査定された
  場合。その場合も q3pe 限定 (3) の残欠 2 件（G 外作用・Weil）の文言が実 discharge に
  更新される実体は残る。
- 楽観 **+0.03（0.59）**: AP-4 Weil 同変性まで含め「二方向＋外 Galois＋pairing」の
  [IUTchI] §2 入力形が揃ったと評価された場合。0.6 は主張しない（下記帽子が残るため）。
- **表示**: Σ_A 実測 = 8·0.85+8·0.69+12·0.75+14·0.56+10·0.27+14·0.61+12·0.57+12·0.66
  +10·0.14 = **56.56**（表示 57・graph-meta 記載の Σ_A=56.56 と一致確認済み）。
  +0.02 で 56.84 → **表示 57 据え置き**。表示 58 には Δs_A4 ≥ 0.067 または他柱との合算が
  必要——**表示 mover を主張しない**。

**消さない・弱めない帽子（新ファイルに必ず並置）**:
1. **分裂・次数付きスライスである**: q3apGeom = ℤ₃(1)×ℤ₃ は T₃(E_q) の**次数付き
   （graded）**であり、本物の T₃E は非分裂拡大 0→ℤ₃(1)→T₃E→ℤ₃→0（Kummer 類 q）。
   格子方向への trivial 作用は「商への作用」としてのみ正確。mod-9 では q=3⁹ の
   9 乗トリック（q^{1/9}=3∈ℚ₃・q9tl）により分裂が忠実だが、**level 27 以深の Kummer
   コサイクル（σ(3^{1/3})/3^{1/3}）は未構成**——named future target（実 ℚ₃(ζ₂₇,3^{1/3})
   の建設が前提）。「非分裂拡大を構成した」とは書かない。
2. **G は Gal(ℚ(ζ_{3^∞})/ℚ)（ℚ 上円分切片）**であって実局所 G_{ℚ₃} でも実 G_K
   （非可換副有限全体）でもない（tmz (iii)・ctl (iv) 継承）。曲線は ℚ₃/M 上・Galois は
   ℚ 上という主語のずれは、古典的同型 Gal(ℚ₃(ζ_{3^∞})/ℚ₃) ≅ Gal(ℚ(ζ_{3^∞})/ℚ)
   （3 完全分岐）が**未形式化**である旨を明記して正直に残す。
3. **Galois は曲線の点には作用しない**: 同変性は π₁ 作用・指標のレベルであり、
   E_{3⁹}(M) の担体への実 Gal(M/ℚ₃) 作用（実局所 Galois 自己同型）は未構成
   （A5 詳細化 2026-07-20 §2.5-3 と同じ named future・A3/A7 と調整）。
4. pro-3・単一曲線 E_{3⁹}・q=3⁹ 忠実部分ケース・K-点群提示（A2/A8 恒久限定）・
   位相/スキーム/エタールサイト皆無・anabelian 逆再構成ゼロ・full ẑ×ẑ(1) 未達——
   q3pe/q3pc/q9td の正直限定を全て継承・並置。atpGroup・q3tpGalAct・M188F surrogate の
   ヘッダ本文は書き換えない（昇格は「新ファイルでの主語替え供給」のみ）。
5. AP-4 の双線形性は座標定義の帰結であり「Weil ペアリングを構成した」とは書かない
   （χ 同変な μ₉ 値スライスまで）。

**overclaim 禁止リスト**: 「算術基本群 Π_X を構成した」と書かない（次数付き pro-3
円分切片の算術拡大スライス）／「G_K 作用」と書かない（円分切片 G）／
crt・tmz・q9td・atp の正直限定の消去・弱化／A3・A5・A7 status の再主張。

---

## 5. 推奨第一実装スライスと de-risk-first

- **第一スライス（opus 1 枠）**: **AP-0〜AP-3＋AP-5**（`IUT/Q3EtaleArithPi1.lean`・
  AP-4 は余力があれば同ファイル内で追加・無ければ落として後続檗）。
  理由: (i) A4 は柱A 最大重み 14 で +0.02 でも表示ポイント +0.28 相当の実増分、
  (ii) 新イディオム 0（atp 写経＋tmzGModule 消費＋q3mb/q9td 指標算術写経）、
  (iii) 両監査の named blocker の正面 discharge で threshold-shopping 疑義がない。
- **de-risk-first 項目（実装前 30–45 分・scratch 1 本）**: 次の 3 点だけ先にコンパイルして
  確定する——
  1. **ζ 生成元整合族 tζ**: ⟨fun n => cmrZeta (n+1), 整合証明⟩ : tmzLimit.carrier が
     `cra_find_zeta`＋tmzT 展開で通ること（通れば非自明性 witness が確定）。
  2. **σ₂ 整合族**: 定数 2 の zpsLimit 族（zpsT 剰余で 2↦2・zpuInvL 単元）→ `cliFrom.map`
     で ctlProfinite の実元になること。
  3. **mk(k·a) = (mk a)^k（zmod 9 の npow）**と `tmz_find_pow` ℓ=2 適用の噛み合わせ
     （q3ap_mu_equivariant の 1 行核）。
  この 3 点が通れば残りは atp 型の抽象群公理と rfl 級の成分計算で機械的に落ちる。
  詰まった場合のみ HELP スポットで fable を呼ぶ（想定詰まりは半直積 assoc の
  Subtype/funext 順序のみ・atp 先例で既知）。
- **並列枠への注意**: 本スライスは q9td・tmz・cli に read 依存するのみで、A5/A6/A9 の
  進行中ファイルと独立——同一ラウンドで他柱 opus 枠と並列可能。統合時の共有ファイル更新
  （IUT.lean・build.sh・gen_graph.py PILLAR・graph-meta/dashboard・target_ledger）は親が
  一括。status 確定は独立敵対監査後（本書の見込み値を先に書き込まない）。

---

*設計: tier-L 詳細化ラウンド 2026-07-20。本書は設計のみで complete_pct を動かさない。
§1–§3 の全主張は実ファイル精読（Q3TatePi1Etale・Q3TatePi1Comparison・Q3Etale9TwoDir・
TateModuleZ3・CyclotomicTowerLimit・CyclotomicLimitIso・CyclotomicGKActionReal・
Q3TateCurveL9・ArithTemperedPi1・Q3TemperedPi1・Q3Mu3TmzBridge・ProfinitePi1）と監査記録
（reaudit-A4-pi1-etale-tate・reaudit-q9td-twodir-a4・reaudit-A5c-cover-tower・
pillar-A5-tempered-pi1-deepen-detail-2026-07-20）に基づく。q3ap_mu_equivariant の
指標計算・witness 整合族の閉形式は設計時に手計算済み。*
