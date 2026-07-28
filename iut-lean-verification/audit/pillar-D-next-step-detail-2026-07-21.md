# 柱D 次段詳細化（disproof-first）— 2026-07-21 詳細化ラウンド

- 種別: **設計文書のみ**（Phase-III 本丸の直接実装禁止規則に従う。本ラウンドで .lean は一切作成・変更しない）
- 対象: 柱D「定理3.11／多輻 (multiradial)」— complete_pct **18%**（全柱最低・Cor 3.12 の本体）
- 方針: 各項目について**まず到達不能の証明を試み**、反証に失敗した場合のみ REACHABLE と判定する。
- 台帳: D1 0.5 / D2 0.5 / D3 0.5 / **D4 0 / D5 0 / D6 0 / D7 0（係争点・恒久 0）/ D8 0**

---

## 0. 要約（結論先出し）

1. **柱D の「実 deg_ℝ」層は全面的に logp 型の自由パラメータ簿記である**（§2 の空虚性所見）。
   `logVolLocal logq k n = n · logq k` の `logq : Nat → RReal` は M351F ProductFormula の
   `logp` と同型の**仮説ゼロ自由パラメータ**であり、M312F 以降の「テータパイロット体積」
   「ガウスパイロット体積」「crux」「Szpiro」「ABC」の全定理は `logq ≡ 0` でも成立する
   線形恒等式である。D1–D3 の 0.5 は ℤ_p 側・形式テータ側の実対象が支えており、
   deg_ℝ 層は支えていない（監査上の注意）。
2. **M382F MultiradialIndet の (Ind1)(Ind2) 不変性は定義的空虚**（`mindSignVal ≡ 0`）。
   「不変性定理」は作用を恒等写像に定義した上での自明式であり、実群が実対象に作用する
   内容を一切持たない。
3. **D7 には即時の罠がある**: 形式化された crux `cruxRealIneq` は `w ≡ 1` を代入すると
   **3 行で証明できる**（両辺閉形式が一致・`rLe_refl`）。D7 を「達成」するいかなる
   インスタンス化・言い換えも定義的閉鎖であり禁止（§4）。
4. 到達可能性判定: **D4 = BLOCKED**（ℚ₃ の拡大体機構と大域楕円曲線が不在）、
   **D5 = BLOCKED-mostly**（p 進級数の収束評価が不在・形式レベルは既建設）、
   **D6 = REACHABLE（忠実な実部分ケース・上限 ~0.5）**、**D8 = REACHABLE（副・忠実な
   実整数部分ケース）**。
5. 推奨: **D6 を主目標**とする段階計画（§5）。fallback は D8 実整数 radical 路線（§6）。

---

## 1. 現状調査 — モジュール分類表（実／模型／toy／自由パラメータ簿記）

分類凡例:
- **[実]** … 本物の数学的対象（実 ℤ_p・実 ℚ₃^×・実 Haar 測度・実形式冪級数・実 Galois 群）が主語
- **[実(狭)]** … 実だが忠実な部分ケース（K=ℚ_p 固定・主項のみ等）
- **[簿記]** … RReal(setoid ℝ) の算術自体は本物だが、**中身（log q_v・重み w）が自由パラメータ**で、
  「体積」「次数」「高さ」「導手」が導出されない装飾名の層（M351F logp と同族。§2 参照）
- **[模型]** … Int/QDiv 等の充足デモ模型（`m202fVol` 型）
- **[toy]** … Bool/Bool³ 軌道等を定理の主語にした層

| モジュール | ID | 分類 | 根拠（実 Lean 定義から） |
|---|---|---|---|
| LogShell.lean | M201F | 模型 | ヘッダ自認「realVolumeTheory: Region=ℝ・vol=id の**充足デモ模型**」 |
| LogShellReal.lean | M321F | 実(狭) | 実 ℤ_p 上 m^d=p^dℤ_p（`logShellMem`）・O_v-加群閉性は本物。log は主項 θ_d のみ・K=ℚ_p 固定 |
| LogShellContainment.lean | M387F | 実(狭) | ℤ_p 上のフィルトレーション包含格子 |
| LogKummerReal.lean | M327F | 実(狭) | graded log θ_d の準同型・核=U^(d+1)・全射（主項レベルで本物） |
| LogLinkReal.lean | M337F | 実(狭)＋簿記 | 写像側（U^(d)→ℤ/p）は本物。「体積輸送」側は自由 `logq` 上の線形式 |
| LogLinkShellCompat.lean | M392F | 実(狭) | ℤ_p 上の log-link ⇄ 殻格子両立 |
| LogLinkIndeterminacy.lean | M367F | 簿記 | deg_ℝ 可換図（自由 logq 上の realAdd 結合律） |
| LogLinkIndetNonzero / FullIndetGroup / ContinuousIndet / FullContinuous | M442F/447F/452F/M4xx | 簿記 | 「log(l)·μ 不定性」の 1 パラメータ族を自由 logq 体積に加算する線形算術 |
| ThetaLinkReal.lean | M328F | 実(狭)＋簿記 | Θ(q,u_j)=u^{j²}（M318F 形式 Laurent 単項式・本物）と Θ^{2l}=q^{j²}（反復冪・本物）。次数変換は自由 logq |
| ThetaLinkTransport.lean | M244F | 模型 | crux の単一 Prop 化（QDiv・m202fVol 由来） |
| ThetaLinkTemperedPi1.lean | M434F | 実(狭) | 実算術 tempered π₁ 上の theta-link 群準同型（柱A frontier・本物） |
| ThetaLinkTwoTheater.lean | M439F | 実(狭) | 2 劇場ラベル付きコピー間の link（†0→†1・本物の群準同型） |
| ThetaLinkPolyIso.lean | M444F | 実(狭) | **link は環準同型でない**（tlp_link_not_ring_hom）— 柱D的に最重要の実定理群 |
| FrobenioidThetaLink.lean | M449F | 実(狭) | Θ-link の函手化・環構造を保たないことの圏レベル持ち上げ |
| Indeterminacies.lean | M202F | 模型 | `@[reducible] def m202fVol : VolumeTheory where Region := Int … vol := id` を (Ind3)/実現可能性の主語に使用（下記引用） |
| IndAction.lean | M241F | toy | `unitOrbitImg … : Bool → QDiv`・`Ix := Bool` |
| IndActionLabel.lean | M254F | toy | `Ix := Bool × Bool`（Bool² 軌道） |
| IndActionFull.lean | M259F | toy | `Ix := Bool × Bool × Bool`（**Bool³ 軌道**・下記引用） |
| IndeterminacyRealAction.lean | M332F | 簿記 | Bool³ の作用主語を「実 deg_ℝ」= 自由 logq 線形式へ載せ替え |
| IndeterminacyFull.lean | M342F | 簿記 | 同上（(Ind3) 膨張 = +m·logq v の加算） |
| MultiradialIndet.lean | M382F | **空虚**（§2.2） | `mindSignVal (_ : Bool) : Int := 0`・作用が定義的に恒等 |
| TateModuleIndeterminacy.lean | TMI | **実** | Aut(ℤ₃(1)) ≅ 実 ℤ₃^×（tmzLimit/zpsLimit・柱A7e。**D6 の最重要資産**） |
| MultiradialRep.lean | M372F | 簿記 | 「多輻表現」= Σj²·logq v という 1 実数値への「降下」 |
| Multiradial.lean / Multiradial311 / MultiradialInput / RealMultiradialInput / Premises311(Real) | M5/M210F/M215F/M228F/M97/M134 | 模型 | Int/実数 witness 骨格・充足モデル |
| MultiradialCompare / MultiradialLatticeCompare / ThetaLinkMultiradial / MultiradialLogLinkTransport / LogVolMultiradialTransport / PilotComparisonMultiradial / PilotBoundMultiradialFull / LogVolumePilotBound | M362F〜M437F | 簿記 | いずれも自由 logq 上の閉形式張り替え・±m シフト・×2l スケールの線形算術 |
| PillarDFoundation / PillarDInterface / PillarDBetaLocalization | M214F/M220F/M233F | 模型 | capstone 束ね |
| GaussPilotRep / GaussPilotWeighted / GaussPilot311 | M141F/M158F | 模型 | `gaussSkeleton logTheta := −Σj²` の充足模型 |
| ThetaPilotRealVolume / GaussPilotRealVolume / LogVolume / LogVolumeArch | M319F/M324F/M312F/M317F | 簿記 | `thPilotValueDeg logq v j = j²·logq v`・`gPilotValueDeg = w(k)k²·logq v`（自由 logq・自由 w） |
| CruxInequalityReal.lean | M347F | 簿記 | crux の「形」= 自由パラメータ不等式（§2.3, §4） |
| SzpiroReduction.lean | M352F | 簿記 | 「高さ」「導手」= 同一単項式 `n·logq v` の係数違い（Σj² vs Σw(k)k²）。楕円曲線・数体は不在 |
| ABCConsequence.lean | M357F | 簿記＋実(初等) | 指数有界の初等算術は本物だが、radical は「上界模型 a·b·c」・実→ℕ 橋は明示仮説 |
| HodgeTheater.lean | M2 | 実(組合せ) | F_l ⋊ {±1} のラベル組合せ論としては本物・**だが Hodge 劇場の実データ（prime-strip・実捻れ点・実 π₁）は皆無** |
| MeasureLogVolume.lean | M341F | **実** | log-vol = −log_p μ を **M336F 実 Haar 測度から導出**（`mlv_from_measure`）— 柱D で数少ない「導出された体積」 |

### 引用（toy/模型の具体的検証・依頼にあった Bool³ の確認）

`IUT/IndActionFull.lean:223`:
```lean
  Ix := Bool × Bool × Bool
```
同 108 行:「**(Ind1)×(Ind2)×(Ind3) 同時作用の像**（`Bool × Bool × Bool`）」、219 行:
「像は `Bool × Bool × Bool` の 8 点軌道」。→ **Bool³ 軌道が不定性の主語**であることを実コードで確認。

`IUT/Indeterminacies.lean:142-152`:
```lean
@[reducible] def m202fVol : VolumeTheory where
  Region := Int
  ...
  vol := id
```
(Ind3) `UpperCompat` の非対称 witness（157-161 行）と `ind311_refines`（201-218 行）の主語は
この Int 模型である。→ **(Ind1)(Ind2)(Ind3) の「構造化」は m202fVol 上の型遊びであり、実対象上の
不定性は D6 = 0 のまま**という台帳評定は正しい。

---

## 2. 空虚性所見（M351F logp 型・今回の最重要 finding）

### 2.1 柱D の deg_ℝ 層全体が自由パラメータ `logq` の線形簿記

`IUT/LogVolume.lean:236-237`:
```lean
def logVolLocal (logq : Nat → RReal) (k : Nat) (n : Int) : RReal :=
  rmul (intToReal n) (logq k)
```
`IUT/ThetaPilotRealVolume.lean:95` / `IUT/GaussPilotRealVolume.lean:117-118`:
```lean
def thPilotValueDeg (logq : Nat → RReal) (v : Nat) (j : Int) : RReal := ...  -- j²·logq v
def gPilotValueDeg (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (k : Nat) : RReal :=
  logVolLocal logq v ((w k * (k * k) : Nat) : Int)                           -- w(k)k²·logq v
```

- `logq : Nat → RReal` は**どこからも導出されない**（局所体の q パラメータ・Haar 測度・付値と
  無接続）。`logq ≡ 0` を代入すると M312F/M319F/M324F/M342F/M347F/M352F/M372F/M382F/M407F/
  M412F/M417F/M427F/M432F/M437F/M442F〜M452F の**全「体積」定理の両辺が ≈0 に退化**し、全て成立
  し続ける。これは M351F ProductFormula の `logp` 循環（「`logp := fun _ => realZero` でも成立」
  — 同ファイル 15-20 行に自認あり）と**同一の欠陥族**である。
- 重み `w : Nat → Nat` も自由。「ガウスパイロット」は実際のガウス因子（実テータ値の q-次数簿記）
  から導出されず、任意重み付き平方和 `wssq w l = Σ_{k≤l} w(k)k²` である。
- **帰結（監査上の注意）**: D1/D2/D3 の 0.5 を支えるのは ℤ_p 側（`logShellMem`・graded log・
  U^(d) 核/全射）と形式テータ側（u^{j²}・Θ^{2l}=q^{j²}）の実定理であり、deg_ℝ 層の定理群は
  **complete_pct の根拠に算入してはならない**。deg_ℝ 層を経由して D4–D8 を「前進」させる計画は
  すべて水増しになる。
- **修復方向**（義務ではないが推奨・§5 D-6-0）: `logq` を **M341F の測度導出値**（`mlvBall d = d`
  = −log_p μ の指数・有理数値）に置換し、「log p を単位とする ℚ 値 log-volume」で言明し直す。
  解析的 log p の実構成（超越値）は不要になり、体積が**導出量**になる。

### 2.2 M382F MultiradialIndet — 不変性が定義的空虚

`IUT/MultiradialIndet.lean:147, 158-159, 163`:
```lean
def mindSignVal (_ : Bool) : Int := 0
def mindInd1Act (logq …) (s : Bool) (V : RReal) : RReal := mindValAct logq v (mindSignVal s) V
def mindUnitVal (_ : Bool) : Int := 0
```
(Ind1)(Ind2) の「作用」は**付値シフト 0 の加算＝恒等写像**として定義されており、「不変性定理」
`mind_ind1_invariant` / `mind_ind2_invariant`（172-180 行）は V+0≈V の自明式。さらに群作用律
`mind_comp_mul`（229-235 行）の証明は作用の構造でなく「両辺とも V を保つ」ことから導かれる。
**実群（ℤ₃^×・Aut(G)）が実対象（実 log-shell・実 Tate 加群）に作用して初めて (Ind1)(Ind2) と
呼べる**。D6 は 0 のままが正しく、M382F を D6 の根拠にしてはならない。

### 2.3 「高さ」「導手」「Szpiro」「ABC」の装飾名

M352F の `szpHeightDeg = logVolLocal logq v (Σj²)`・`szpConductorDeg = logVolLocal logq v (Σw(k)k²)`
は**同一の自由単項式 n·logq v の整数係数違い**であり、楕円曲線・数体・実際の高さ関数・実際の
導手はどこにも存在しない。還元定理（推移律）は本物の論理だが、主語は空である。M357F の radical
も「上界模型 a·b·c」で、実 radical（素因数の積）ではない。→ D8 = 0 は正当。

---

## 3. D 項目別の到達可能性判定（disproof-first）

### D4 実ホッジ劇場／実 log-theta-lattice（w16, 0.00）— **BLOCKED**

**言明が要求する実対象**: (i) 大域数体 F と F 上の実楕円曲線 E（悪還元付き）、(ii) 各素点の
prime-strip（実 π₁ ＋ 実 Frobenioid）、(iii) 実 l-捻れ点集合への二対称性 F_l^±±・F_l^* の実作用
（ラベルは E[l](F̄) の実点でなければならない）、(iv) 劇場間 link で結んだ格子。

**在庫**: ラベル組合せ論（M2・実組合せ）、実 Tate 曲線 E_q(ℚ₃)=ℚ₃^×/q^ℤ（A8a `q3tCurve`・実付値
v(q)=m）、**E₉(ℚ₃)[2] の Klein 4 群のみ**（A8b）、2 劇場ラベル付きコピー＋環非保存 link
（M439F/M444F/M449F）、実算術 tempered π₁（M429F/M434F）。

**不能の証明（成功）**: IUT の走行仮定は l ≥ 5 の奇素数。ところが E_q(ℚ₃)[l]（l 奇）の点は
ζ_l, q^{1/l} ∉ ℚ₃ ゆえ **ℚ₃ の有限次拡大体の中にしか存在しない**。リポジトリには ℚ₃ の拡大体
機構（分岐/不分岐拡大の実構成）が無い（A8b 正直な限定 2 が自認:「奇素数 l の E_q[l] は ℚ₃
有理でない——拡大体機構（未建設）の後続」）。また大域側の実楕円曲線（Weierstrass 係数付き
E/ℚ とその導手）も皆無。**ラベルに実捻れ点を載せられない以上、「実ホッジ劇場」は主語を
持てない**。ラベル骨格＋簿記でのそれらしい束ねは §2 型の水増しになる。
→ **BLOCKED on**: (α) ℚ₃ の拡大体機構（柱A A2/A8 後続）、(β) 大域実楕円曲線。着手禁止。

### D5 実多輻表現（w14, 0.00）— **BLOCKED-mostly**

**要求する実対象**: 定理3.11 (i) の (a) 対数殻テンソルパケット I^Q（複数ラベル j にわたる
実 ⊕_j m^{d_j}）、(b) splitting monoid、(c) 数体 M_MOD——これらを**実 π₁/実 Galois の作用込みで**
持ち、その値（パイロット次数）が**実テータ値の実付値から導出**されること。

**在庫**: 形式テータ Θ(q,u)（M88・本物の形式冪級数）、Θ(q,1)=0（M308F・本物）、
テータ値 = Laurent 単項式 u^{j²}・Θ^{2l}=q^{j²}（M318F/M328F・形式レベルで本物）、
実 ℤ₃ 側の殻・graded log（M321F/M327F）。

**不能の証明（ほぼ成功）**: 「多輻表現の値」を本物にするには Θ を実際の q ∈ ℚ₃（例 q=9）で
**評価**して実付値を取る必要があるが、Θ は q の**無限和**であり、リポジトリには p 進完備性に
おける級数収束・評価の機構が無い（M308F は係数ごとの形式的消滅までで止めたと自認）。また
表現の「多輻性」は相異なる劇場の実環構造間の両立であり D4 に依存する。形式 q-次数レベル
（u^{j²} の指数簿記）は**既に建設済み**なので、そこに留まる追加は骨格水増しにしかならない。
→ **BLOCKED on**: p 進級数評価（＋D4）。部分的な例外は D6 経由（下記）の実作用のみ。

### D6 実不定性 Ind1/Ind2/Ind3（w12, 0.00）— **REACHABLE（忠実な実部分ケース・上限 ~0.5）**

**要求する実対象**: (Ind1) 局所 Galois 群の自己同型（の像）による poly-同型不定性、
(Ind2) 各因子への Ô^×_v コピーの作用、(Ind3) log-Kummer 対応の上半両立（殻包含の一方向性）。

**不能の証明の試み（失敗 → REACHABLE）**:
- (Ind2) の実主語は「実単数群が実対数殻に作用する」こと。**両方在庫にある**: 実 ℤ₃^×
  （`zpUnits`/`zpsLimit`・逆元込みの実アーベル群）と実殻 m^d（`logShellMem`）、しかも
  `logShell_smul_mem`（M321F-2c）が O_v スカラー閉性を既に本物で証明している。作用の群律・
  各段安定性・graded 商 m^d/m^{d+1} ≅ ℤ/p 上の剰余倍作用・**非自明性**（u=−1 が動かす witness）
  は全て現有部品の実算術で閉じる。反証不能。
- (Ind1) の完全版は Aut(G_{ℚ₃}) を要し G_{ℚ₃} 全体は未建設（A2 後続）——**完全版は不能**。
  しかし §3 規則の「本物の忠実な部分ケース」として、**実 Tate 加群 ℤ₃(1) の実自己同型群
  Aut(ℤ₃(1)) ≅ ℤ₃^×（TMI・既に実）**と、実円分塔 μ_{3^n} の実 Galois 作用（`csaAut`・A3）が
  在庫にある。シクロトーム側自己同型が捻れラベル・殻付値に及ぼす作用（付値保存を**定理として**
  証明する——M382F のように定義 0 にしない）は現有部品で閉じる。反証不能。
- (Ind3) の核心は**完全 p 進 log**（主項でない収束級数）に依存し、これは重い（分母 1/k は
  ℚ₃ 係数を要し、逆極限上の収束評価が要る）。ただし ℚ₃ の体表示 `q3f`（実付値 `q3fValRel` 込み）
  は在庫にあるため、**有限精度打ち切り log_N ＋ 付値誤差評価**という忠実な部分ケースは
  不能と断定できない（tier L・HELP スポット）。
→ **判定: REACHABLE**。ここだけが「実群 × 実対象」の両方が既に在庫にある D 項目である。

### D8 Cor 3.12 → Szpiro → ABC 還元（実）（w8, 0.00）— **REACHABLE（副・実整数部分ケース）**

**要求する実対象**: 実高さ・実導手（本来は E/ℚ の Faltings 高さ・導手）。完全版は D4 と同じ
理由で不能。しかし**整数 ABC の実言明**（互いに素な a+b=c と**実 radical** rad(abc) = 素因数の
積）は初等であり、リポジトリには**実素因数分解 `pfcFactors`（B5 で監査済み・本物）**が既にある。
`b5Support`（重複除去済み素因子リスト）から実 rad(n) を定義し、M357F の「radical 上界模型
a·b·c」と「実→ℕ 橋仮説」を**実 rad(n) の実定理**（べき不変性 rad(xᵐ)=rad(x)・rad(n) ∣ n・
乗法性 gcd 条件下）に置換できる。反証不能 → REACHABLE。ただし w8（最小 weight）で、IUT 本体
（劇場・多輻）には触れないため**副目標**とする。見込み D8 0→0.3（「実整数 ABC 言明＋実 radical
での還元」＝忠実部分ケース未満、Frey/楕円曲線側が空のため 0.5 に届かない可能性が高い）。

---

## 4. D7 の例外と罠（必読・恒久遵守）

D7「多輻不等式 crux Dβ-ω」は**数学的係争点そのもの**であり、決着まで status 0 固定が台帳規約。
今回の調査で、**現行形式化には D7 を「定義的に閉じてしまう」具体的な罠がある**ことを確認した:

`IUT/GaussPilotRealVolume.lean:193-195`:
```lean
def GaussPilotCruxHyp (logq : Nat → RReal) (v : Nat) (w : Nat → Nat) (l : Nat) : Prop :=
  rLe (thPilotTotalVol logq v l) (gPilotTotalVol logq v w (l + 1))
```
両辺の閉形式は `Σ_{j=1}^{l} j² · logq v` と `Σ_{k=0}^{l} w(k)k² · logq v`（`thPilot_total_closed`・
`gPilot_total_wssq`）。**`w ≡ 1` を代入すると `wssq w l = sumSq l` で両辺が realEq になり、
`rLe_refl` ＋ `rLe_congr` の 3 行で `cruxRealIneq logq v (fun _ => 1) l` が「証明」できる**。
同様に `w(k) ≥ 1`（k≥1）と `logq v ≥ 0` を仮定すれば単調性で一般に「証明」できる。

これは crux が解けたことを意味しない。**形式化された「crux」が係争点を全く符号化していない**
（自由 w と自由 logq の比較式に退化している）ことを意味する。本物の crux は:
- 両辺が**相異なるホッジ劇場**に住む量であり（同一の logq v 上の 2 つの数ではない）、
- テータパイロット次数が**実テータ値の実付値から導出**され（自由係数 j² の宣言ではなく）、
- ガウス側が theta-link・log-Kummer 対応（**全段収束 log**）・3 不定性の**実作用**を通って
  比較可能になる、
という構成全体（≒ D4+D5+D6 の実物）を経て初めて**言明できる**。ゆえに:

1. **禁止**: `GaussPilotCruxHyp`/`cruxRealIneq`/`indF_cruxHyp` を任意の w・logq で
   インスタンス化して閉じるモジュール、crux と同値な言い換えを「新定理」として導入する
   モジュール、`w` に具体値を仕込んだ「充足デモ」。これらはすべて D7 の定義的閉鎖であり、
   発見次第 revert 対象。
2. **正当な D7 の試みの最低要件**（現時点では全て不在）: 実 2 劇場の環構造非両立（M444F は
   その入口・本物）の上で、導出されたパイロット次数（§5 D-6-0 の測度導出 ℚ 値）を
   log-Kummer 全段（完全 log）で輸送し、(Ind1–3) の実作用の hull を取った上での不等式言明。
   これが揃って初めて「証明を試みる対象」が Lean に存在する。**それでも証明の成否は数学の
   係争の裁定であり、本プロジェクトの管轄外**。status は 0 のまま。
3. M347F/M352F/M357F の「crux は外部仮説（Iff.rfl）」という自己申告は正直だが、§2.3 の通り
   主語が空なので、**「crux の形の精密化」を D7 どころか D4/D5 の前進として数えることも
   禁止**する。

---

## 5. 推奨: D6 段階計画（実不定性・忠実な実部分ケース）

**選定理由**: D6 だけが「実群」と「実被作用対象」の両方を在庫に持つ（§3）。また D6 の実作用は
将来の D5（表現＝不定性商への降下）・D4（劇場の対称性）の必須部品であり、本コース上にある。
M382F の空虚作用（§2.2）の**昇格 (a)** に該当し、完全証明ファースト規則 §2(a) を満たす。

### D-6-0（前提整地・tier M・新規 1 ファイル）: 測度導出 log-volume への張り替え

- **消費する実対象**: M341F `mlvBall`（−log_p μ・実 Haar 測度から導出）、M336F `haarBall`。
- **目標言明**: `pilotDegQ : … → Rat`（log p 単位の ℚ 値パイロット次数）を `mlvBall`（と付値）
  から**導出**して定義し、`thPilotValueDeg`/`gPilotValueDeg` との関係を「logq を単位重みに
  特殊化したとき一致」(`realEq`) で証明。以後の D6 言明はこの導出量で行う。
- **効果**: §2.1 の自由 logq 空虚性を D6 の新規部分から遮断する（既存 deg_ℝ 層は消さない・
  正直申告として併記）。complete_pct 直接寄与は小（D1–D3 の質の是正）だが、これ無しでは
  D6 の「体積への作用」言明が再び簿記化する。
- **status 予測**: 単独では動かさない（整地）。難度 M。

### D-6-1（本丸 1・tier M・新規 1 ファイル）: 実 (Ind2) — 実 ℤ₃^× の実 log-shell への作用

- **消費する実対象**: `zpUnits p hp`（実 ℤ_p^×・M36）、`Zp p`/`zpMul`、`logShellMem`（M321F）、
  `zmod p`、`unitFiltration`（M31）。
- **目標 Lean 言明**（精密形）:
  - `def ind2Act (p hp) (u : (zpUnits p hp).carrier) (x : (Zp p).carrier) : (Zp p).carrier`
    （u.val による zpMul）
  - `theorem ind2Act_mem : logShellMem p d x → logShellMem p d (ind2Act u x)`（殻安定・
    `logShell_smul_mem` の単数特殊化）
  - `theorem ind2Act_one / ind2Act_mul`（**群作用律**・M382F と違い実乗法で証明）
  - `theorem ind2Act_graded : (m^d/m^{d+1} 上の誘導作用) = 剰余 ū ∈ (ℤ/p)^× による乗法`
  - `theorem ind2Act_nontrivial : ∃ u x, logShellMem p 1 x ∧ ind2Act u x ≠ x`（u=−1, x=p で
    実 witness——**空虚性の否定を機械検証**）
  - `theorem ind2Act_val_preserve : 殻レベル（付値）を変えない`（単数の付値 0 を**定理として**）
- **status 予測**: D6 0 → 0.25（独立監査条件。実群×実対象×非自明作用の初達成）。

### D-6-2（本丸 2・tier M・新規 1 ファイル）: 実 (Ind1) — Aut(ℤ₃(1)) ≅ ℤ₃^× の実作用

- **消費する実対象**: TMI `tmzLimit`（実 ℤ₃(1)）・`Aut(ℤ₃(1)) ≅ zpsLimit`（既に実・A7e）、
  実 μ_{3^n}（`cm9`/`ctm`・A3）、実 Galois `csaAut`・制限塔 `ctrResHom`（A3 M2/M3）。
- **目標 Lean 言明**: Aut(ℤ₃(1)) の実元 σ_a が (i) 円分塔の各段 μ_{3^n} にラベル a 倍で作用し
  制限塔と可換（`ctr_compat` と接続）、(ii) 捻れラベル j ↦ a·j が D6-1 の殻 graded 作用と両立、
  (iii) 付値を保存（**定理**）。非自明 witness（a=2 が μ₉ の生成元を動かす——実円分体内の実計算）。
- **正直な限定**: これは Aut(G_{ℚ₃}) 全体でなく**シクロトーム部分への忠実な実部分ケース**
  （G_{ℚ₃} 未建設のため）。ヘッダに明記し、0.4 超の主張をしない。
- **status 予測**: D6 0.25 → 0.4。

### D-6-3（HELP スポット・tier L・新規 1 ファイル）: 実 (Ind3) — 有限精度 p 進 log と上半両立

- **消費する実対象**: `q3f`（実 ℚ₃ 体表示・実付値 `q3fValRel`）、`unitFiltration`、
  `logShellMem`、M327F graded log。
- **目標 Lean 言明**: 打ち切り対数 `logN(1+t) = Σ_{k=1}^{N} (−1)^{k+1} t^k/k`（ℚ₃ 値・実分数）
  について (i) `v(logN(u) − (u−1)) ≥ 2d − v₃(N!)` 型の実付値誤差評価、(ii) `logN(U^(d)) ⊆ m^d`
  （主項でなく**打ち切り全体**の着地・p=3, d≥1 で 3d>… の実評価）、(iii) その帰結として
  (Ind3) 上半両立「log 像の殻は包含 ⊆ のみで両立（等号不成立の実 witness）」を**実 ℚ₃ 上で**。
- **これが D6 の 0.5 到達条件**（(Ind3) が m202fVol 型 le-関係でなく実殻包含になる）。
- **stall 時の扱い**: (i)(ii) が重ければ D-6-3 を中断し、D6 は 0.4 で正直申告
  （「(Ind3) は実対象上未達・完全 log が blocker」）。**主項 log での見かけ Ind3 を作らない**。

### D-6-4（capstone・tier S・新規 1 ファイル）: 束ねと正直申告同期

- D-6-1〜3 を `Ind6RealData` に束ね、M202F/M241F/M254F/M259F/M382F の toy/空虚層への
  参照を「昇格済み（実版は …）・旧層は消さず併設」と相互注記。graph-meta/dashboard の
  二軸更新は親が統合時に実施。

### 予測まとめ

| 段 | tier | 新規ファイル | D6 status 予測 | blocker |
|---|---|---|---|---|
| D-6-0 | M | 1 | ±0（整地） | なし |
| D-6-1 | M | 1 | 0→0.25 | なし（在庫で閉じる） |
| D-6-2 | M | 1 | 0.25→0.4 | なし（TMI/A3 在庫） |
| D-6-3 | L | 1 | 0.4→0.5 | 収束評価が stall し得る（stall なら 0.4 で申告） |
| D-6-4 | S | 1 | — | D-6-1〜3 依存 |

柱D complete_pct への影響見込み: D6 0→0.5 で **18% → 約 23%**（w12/Σw=100・独立監査確定が条件）。

---

## 6. Fallback: D8 実整数 radical 路線（主計画 stall 時・tier M）

D-6-1/2 が予想外に stall した場合のみ起動。
- **D-8-1（tier M）**: 実 radical。`pfcFactors`（B5・監査済み実素因数分解）と `b5Dedup` から
  `rad : Nat → Nat` を定義し、`rad_dvd : rad n ∣ n`・`rad_pow : rad (x^m) = rad x`・
  `rad_mul_coprime` を実証明。M357F の「radical 上界模型 a·b·c」を実 rad に置換した
  `abcTripleReal`（互いに素 a+b=c・実 rad(abc)）と、実整数 ABC 言明
  `c ≤ K · rad(abc)^{…}` の**言明の実化**（証明はしない・予想本体）。
- **D-8-2（tier M）**: M357F の実→ℕ 橋仮説を「実 rad の実定理」で置換した漸近フェルマー還元の
  再証明（`rad_pow` が M357F の「べき乗不変＝還元の心臓部」を仮説から定理へ昇格）。
- **status 予測**: D8 0→0.3（楕円曲線側が空のため 0.5 未達の可能性を予告）。
- **注意**: これは crux にも劇場にも触れない外周であり、主計画より優先してはならない。

---

## 7. 着手禁止リスト（本ラウンドの負の結論・水増し防止）

1. **D4/D5 の直接着手**（§3 の blocker が解けるまで）。ラベル骨格＋deg_ℝ 簿記での「劇場風」
   モジュールは complete_pct 0 前進の骨格追加であり §2 規則により事前確認必須。
2. **deg_ℝ 簿記層（自由 logq/w）の上の追加補題**すべて（LogLink*/Multiradial* 系の横展開）。
   §2.1 により complete_pct を動かさない。
3. **crux 関連 Prop のインスタンス化・同値言い換え**（§4）。
4. Bool 軌道・m202fVol を主語とする一切の新規（§3 規則そのもの）。
5. D6 実装時、M382F の語彙（mind*）を**主語として再利用しない**こと（作用が 0 定義の層と
  混線し監査が汚染される）。

---

## 8. blocker 登録（他柱への要請）

- **(α) ℚ₃ の有限次拡大体機構**（不分岐 ℚ₉・分岐 ℚ₃(ζ₃)/ℚ₃(3^{1/l})）: D4（奇 l 捻れ）・
  D6 完全版 (Ind1)・D5 の評価の前提。柱A A2/A8 の後続として起票を推奨。
- **(β) p 進級数の収束・評価機構**（逆極限位相での Cauchy 性）: D5（実テータ値）・D-6-3
  （完全 log）の前提。柱A/C の後続として起票を推奨。
- **(γ) 大域実楕円曲線 E/ℚ**（Weierstrass 係数・判別式・導手）: D4 大域側・D8 満点の前提。

以上。本ラウンドは設計のみで complete_pct 0 前進（正直申告）。次ラウンドの実装割当は
D-6-0/D-6-1 の並列（opus×2）＋ D-6-2（opus）を推奨し、D-6-3 のみ fable 枠とする。
