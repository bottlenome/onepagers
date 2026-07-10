# A5 実 tempered π₁^temp 詳細化ラウンド設計 — 実 Tate 被覆のデッキ群 ℤ（2026-07-10）

**種別**: 詳細化ラウンド（設計ドキュメントのみ・Lean 実装なし）
**対象**: 柱A A5「実 tempered π₁^temp」（w10・**status 0**——柱A で A9 と並ぶ最後の status 0）
**土台**: 今セッション完成の実 Tate 曲線一式 — `Q3TateCurve.lean`（q3t: 実 E_q(ℚ₃)=ℚ₃^×/q^ℤ・
q3tProj 全射 Hom・q3tSubgroup=q^ℤ・q3t_q_pow_ne_one・q3t_qpow_val）・`Q3UnitsGroup.lean`（q3u:
実 ℚ₃^×＝3^ℤ×ℤ₃^×↪ℚ₃）・A7 の実 ℤ₃(1)=tmzLimit・実 Gal 作用 tmzActHom
**目的**: A5 の既存代理（ẑ×ℤ・tateModel 抽象 G_K）のうち、**離散 ℤ デッキ部分を実 Tate 曲線の
実被覆で本物化**する最小 complete_pct 前進ステップを、opus 実装枠に渡せる粒度まで分解する。

---

## 0. 結論サマリ

| 項目 | 内容 |
|---|---|
| 選定ステップ | **A5a**: 実 Tate 被覆 ℚ₃^× → E_q(ℚ₃) のデッキ群 q^ℤ ≅ ℤ（核＝ちょうど q^ℤ・自由推移的ファイバー作用・**M333F/M364F の外部仮説 `discRig_infiniteOrder_hypothesis` を実主語上の定理として discharge**）＋ **A5b**: pro-3 tempered 模型 π₁^{temp,(3)} = 実 ℤ₃(1) × ℤ（両成分とも実・完全列・実 Gal(ℚ(ζ_{3^∞})/ℚ) 作用） |
| 新規ファイル | `IUT/Q3TateDeck.lean`（prefix `q3td`）→ `IUT/Q3TemperedPi1.lean`（prefix `q3tp`・q3td 依存）。第三候補 `IUT/Q3TateCoverTower.lean`（prefix `q3tc`・q3td 依存・並列可） |
| tier | **全て M（opus）**。新イディオム不要（prodGrp 成分算術・Quot.sound/quot_exact・tateZpow 帰納・cciIsoData 型の双方向写像——すべて確立イディオムの写経）。fable 実装枠不要 |
| A5 status 見込み | 0 → **0.1**（A5a 単独・保守）→ **0.15**（A5a+A5b）→ 上限 **0.2**（A5c まで。§7 参照・独立監査確定が条件） |
| 柱A% | Σ_A 46.74 → A5=0.1 で 47.74 ⇒ **47 → 48**。丸め境界は A5 ≥ 0.076（§7.2）。A5a 単独で届く見込みだが余裕が薄いため **A5a+A5b の 2 本を推奨**（A8a/A8b 前例と同じ保険設計） |
| 中心判定（§2） | 実 Tate 被覆のデッキ群 ℤ は tempered π₁ の離散部分の**本物の忠実な算術的実現（K-点の影・位相なし）**——「別コースの toy」ではなく本コースの実部分ケース。ただし Berkovich/rigid 位相・punctured 曲線の非可換 θ 構造は範囲外（§6） |

---

## 1. 現状実測 — 既存 A5 資産の実／代理判定（精読結果）

| モジュール | 分類 | 実測内容 | 本設計との関係 |
|---|---|---|---|
| `TemperedPi1.lean`（M364F） | **代理（主語）／機構は実** | π₁^temp を **Ẑ×ℤ 直積模型**で構成。完全列 1→Ẑ→π₁^temp→ℤ→1・非可除性・非有界指数は完全証明。**しかし離散部 `tmpDiscretePart = intGrp` は裸の ℤ で、どの実曲線・実被覆にも接続されていない**。存在定理 `tmp_exists` は一般 IUTField K の q に対し **`tmp_infiniteOrder_hypothesis`（=`discRig_infiniteOrder_hypothesis`・「決して導出しない」明記の外部仮説）に条件付き** | **A5a の直接昇格対象**。graph-meta「tempered π₁はẑ×ℤ代理」の実体はこれ |
| `DiscreteRigidity.lean`（M333F） | 実（機構）／仮説条件付き | 周期準同型 n↦qⁿ の単射性を `discRig_infiniteOrder_hypothesis (G) (g) : ∀ n:Int, tateZpow G g n = G.one → n = 0` の**外部仮説**の下で導出。仮説は Grp 一般の Prop | **A5a が実主語 q3tGrp・q3tQ m で仮説そのものを定理化**（§3.4） |
| `TemperedTower.lean`（M374F） | 実（機構）／主語は裸の ℤ | デッキ群塔 ℤ/l^n・逆極限 ℤ_l。実曲線の被覆塔としての実現なし | A5c の接続先（実 E_{q^{l^n}}(ℚ₃) の塔で実例化） |
| `ThetaCovering.lean`（M369F） | 実（機構）／主語は裸の ℤ | 部分格子 lℤ⊆ℤ・tcvDeckGroup l = zmod l・被覆準同型 | A5c が消費（tcvDeckGroup を実被覆のデッキ群として実現） |
| `TemperedPi1Etale.lean`（M424F）・`TemperedThetaCommutator`（M384F）・`TemperedThetaOuterAction`（M389F）・`ArithTemperedPi1.lean`（M429F） | **実（群論）／実曲線未接続** | 離散 Heisenberg thetaGrp ⋊ ℤ（tpeGroup）・算術化 atpGroup=tpeGroup⋊_χℤ。群演算・完全列・交換子＝シクロトーム着地は本物の群論。**しかし主語は抽象格子 ℤ³ で、シクロトーム c は実 μ に未接続・G_K 商は ℤ 模型（自己申告済み）・実曲線の被覆空間としての幾何的実現は「外部/後続」と明記** | punctured 曲線の非可換 tempered 構造。今回**触らない**（実 θ が柱E 依存・§6）。消さず併設 |
| `TateCoverGroup.lean`（M188F）〜`TateSurrogateCapstone.lean`（M206F）A-3β 4 部作 | **代理（自己申告）** | 「デッキ ℤ・G_K=ℤ は玩具モデル」「π₁ の提示は幾何からの入力（tateModel）であり実際の Tate 曲線から計算された不変量でない」とヘッダに明記。被覆圏の Galois 圏化・Aut(F)=ẑ 復元は抽象群一般の定理の適用 | A5c（後続 phase）の実代入先。今回は圏側に触らない |
| `TateModuleZ3.lean`（tmz・A7b 帰属） | **実** | ℤ₃(1)=lim μ_{3^{n+1}}（実円分体内の実 μ・遷移=実 cube 写像）・実 Gal 作用 tmzActHom（ctlProfinite=実 Gal(ℚ(ζ_{3^∞})/ℚ)） | **A5b の profinite 側の実部品**（pro-3 部分） |
| `Q3TateCurve.lean`（q3t・A8a・本日確定） | **実** | E_q(ℚ₃)=ℚ₃^×/q^ℤ・q3tProj 全射・q^ℤ 正規・q3t_q_pow_ne_one（外部付値仮定なし）・quotientProjN_ker（核＝ちょうど q^ℤ） | **A5a の土台**。被覆側の全部品が既に本物 |

**判定**: A5 資産は「機構・群論は実、しかし tempered π₁ の主語（どの曲線の何の被覆のデッキか）が
全て裸の ℤ か抽象模型」という構図。status 0 の正体は**実曲線に接続された tempered 対象が 1 つも
無い**こと。本日 A8a で実 E_q(ℚ₃) と実被覆 q3tProj が入ったため、接続の材料は全て揃っている。

---

## 2. 中心判定 — 実 Tate 被覆のデッキ群 ℤ は tempered π₁ の離散部分の本物か

**判定: Yes（忠実な算術的実現・離散部分に限る・位相なし）**。根拠と正確なスコープ:

1. **数学的事実**: Tate の一意化定理により、局所体 K 上の Tate 曲線 E_q は K-点で
   **完全列 1 → q^ℤ → K^× → E_q(K) → 1 が厳密に成立**する（H¹(G_K, q^ℤ)=0 側の議論を
   経ずに、E_q(K)=K^×/q^ℤ が定義そのもの）。解析側では普遍被覆 𝔾_m^an → E_q^an の
   デッキ変換群がちょうど q^ℤ ≅ ℤ であり、tempered π₁^temp(E_q) の**離散商 π₁^temp ↠ ℤ は
   この被覆のデッキ群**である（André・Mochizuki [SemiAnbd]）。compact な E_q では
   π₁^temp ≅ ẑ(1) × ℤ（可換）で、M364F の直積模型は**群構造としては正しい**——欠けていたのは
   両成分の実主語だけである。
2. **Lean 構成が捉えるもの**: `q3tProj : ℚ₃^× → E_q(ℚ₃)` は本物の全射群準同型・核＝ちょうど
   q^ℤ（quotientProjN_ker・∃形でなく iff）・q^ℤ ≅ ℤ は m≥1 で本物の単射（第1成分 m·t の
   実算術・外部仮説なし）・デッキ作用 t·x = qᵗ·x は射影を保ち（被覆変換）・自由（qᵗx=x→t=0）・
   ファイバー上推移的（proj x=proj y ↔ ∃t, qᵗx=y）。これは**上記完全列の K-点の影を
   丸ごと形式化**したものであり、離散部分については「本物の忠実な部分ケース」の要件
   （実主語・非退化・外部仮説ゼロ）を満たす。
3. **本物でない部分（正直な限定・§6 で線引き）**: tempered π₁ の**定義**は Berkovich/rigid
   解析化の被覆理論に基づく。位相・解析構造は形式化されないため、本構成は「位相被覆の
   デッキ群」ではなく「その群論的・算術的な影（K-点の格子商）」である。また実現されるのは
   離散**商**のみで、tempered 群そのもの（profinite 部分との拡大・punctured 曲線では
   非可換 θ 構造）ではない。よって A5a は 0.5（実対象の忠実な部分ケース＝target 全体の
   部分ケース）には届かず、**0 → 0.1 のオーダーの「実 IUT 本コースの最初の実歩」**と見積もる。
4. **§3（toy 主語禁止）適合**: 主語は実 ℚ₃^×（3^ℤ×ℤ₃^× 群提示・q3uEmbed で実 ℚ₃ 内へ
   単射同定済み）・実 q=3^m・実 E_q(ℚ₃)。Bool 軌道や surrogate 群を主語にした「別コースの
   完成」ではない。

---

## 3. A5a 設計 — `IUT/Q3TateDeck.lean`（prefix `q3td`・tier M）

**分類ヘッダ（実装時に記載）**: [実／昇格(a)]。M364F `tmpDiscretePart`（裸の ℤ・実曲線
未接続）と M333F の外部仮説 `discRig_infiniteOrder_hypothesis`（「決して導出しない」明記）を、
実 Tate 被覆 ℚ₃^× → E_q(ℚ₃) のデッキ群として本物化・定理化する。
complete_pct 影響: A5 0→0.1（見込み・独立監査確定が条件）・柱A 47→48。

依存: `IUT.Q3TateCurve`・`IUT.TateCurve`・`IUT.DiscreteRigidity`・`IUT.GaloisCategory`（GAction）。
規模見積もり: 約 280–330 行・9 節。

### 3.1 zpow の第1成分公式（q3t_npow_fst の Int 拡張・部品）

```lean
/-- 一般元の npow 第1成分（q3t_npow_fst の g 一般化・帰納）。 -/
theorem q3td_npow_fst (g : q3tGrp.carrier) : ∀ n : Nat,
    (tateNpow q3tGrp g n).1 = g.1 * (n : Int)
-- 証明: q3t_npow_fst と同型の帰納（intGrp 加法・Int.mul_add）。

/-- **q3td-1（★）: zpow 第1成分公式** (tateZpow q3tGrp (q3tQ m) t).1 = m·t。 -/
theorem q3td_zpow_fst (m : Nat) (t : Int) :
    (tateZpow q3tGrp (q3tQ m) t).1 = (m : Int) * t
-- 証明: cases t。ofNat n は q3td_npow_fst。negSucc n は
-- (q3tGrp.inv (q3tQ m)).1 = -(m:Int)（prodGrp inv の成分計算・rfl 近傍）を経由し
-- (-m)·(n+1) = m·negSucc n を omega で。
```

### 3.2 周期準同型 ℤ → ℚ₃^× とその単射性（q^ℤ ≅ ℤ の実体）

```lean
/-- **q3td-2a: 実周期準同型** t ↦ qᵗ（M333F discRig_periodHom の実 Grp 版）。 -/
def q3tdPeriodHom (m : Nat) : Hom intGrp q3tGrp where
  map := tateZpow q3tGrp (q3tQ m)
  map_mul := tateZpow_add q3tGrp (q3tQ m)   -- intGrp.mul = +

/-- **q3td-2b（★）: 単射性＝ q^ℤ ≅ ℤ（実同型・外部仮説なし）**。 -/
theorem q3td_period_inj (m : Nat) (hm : 1 ≤ m) :
    (q3tdPeriodHom m).Injective
-- 証明: q3td_zpow_fst で m·s = m·t、m≥1 から s=t（omega は m 変数の線形等式で可）。

/-- **q3td-2c: 像＝ちょうど q^ℤ**（tateQPowersSubgroup の mem は定義的に ∃t, qᵗ=x）。 -/
theorem q3td_image (m : Nat) (x : q3tGrp.carrier) :
    (q3tSubgroup m).mem x ↔ ∃ t : Int, (q3tdPeriodHom m).map t = x := Iff.rfl
```

単射＋像特徴付けで「q^ℤ ≅ ℤ の本物の同型」を主張する（cciIsoData 型の双方向逆写像は
指数抽出 `x.1 / m` の Int 除算補題（core に `Int.mul_ediv_cancel_left` が無い場合 omega は
変数除算を扱えない）が難所になり得るため、**見出し実例 m=1 では明示逆写像
`q3tdExp x := x.1`・`q3td_exp_zpow`/`q3td_zpow_exp` の双方向をフル証明**し、一般 m は
単射＋∃形像で主張する。フォールバック方針として実装者に指示・正直な限定に記載）。

### 3.3 核＝ちょうど q^ℤ（被覆の完全列 1 → q^ℤ → ℚ₃^× → E_q(ℚ₃) → 1）

```lean
/-- **q3td-3（★）: 実 Tate 被覆の完全列** — ker(q3tProj) = im(q3tdPeriodHom)（iff 形）。 -/
theorem q3td_ker (m : Nat) (x : q3tGrp.carrier) :
    (q3tProj m).map x = (q3tCurve m).one ↔ ∃ t, (q3tdPeriodHom m).map t = x :=
  (quotientProjN_ker q3tGrp (q3tSubgroup m) (q3t_normal _) x).trans (q3td_image m x)
```

全射性は `q3tProj_surjective`（既存）と合わせて、完全列の全成分が揃う。

### 3.4 外部仮説の定理化（本ラウンドの旗艦 discharge）

```lean
/-- **q3td-4（★★）: M333F/M364F の外部仮説を実主語上の定理として discharge** —
    discRig_infiniteOrder_hypothesis q3tGrp (q3tQ m)（∀ t, qᵗ=1 → t=0）。
    M333F は「本層では決して自前で導出しない」と明記した仮説。実 ℚ₃^× の
    第1成分算術（q3td_zpow_fst・1.1=0・m·t=0→t=0）で無条件に閉じる。 -/
theorem q3td_infinite_order (m : Nat) (hm : 1 ≤ m) :
    discRig_infiniteOrder_hypothesis q3tGrp (q3tQ m)
```

これにより M364F `temperedPi1Data`/`tmp_exists` の条件節（hInf）が、実主語では
**入力不要**になる（A5b で消費）。既存の仮説定義・条件付き定理は消さない（§4 規約）。

### 3.5 デッキ作用（自由・推移的・被覆変換）

```lean
/-- **q3td-5a: デッキ作用** t·x = qᵗ·x（ℤ が実 ℚ₃^× に作用）。 -/
def q3tdDeck (m : Nat) : GAction intGrp where
  carrier := q3tGrp.carrier
  act := fun t x => q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) x
  act_one := ...   -- q⁰=1・one_mul
  act_mul := ...   -- tateZpow_add・mul_assoc

/-- **q3td-5b（★）: デッキ変換は被覆変換**（射影を保つ＝id_{E_q} を覆う）。 -/
theorem q3td_deck_over_proj (m : Nat) (t : Int) (x : q3tGrp.carrier) :
    (q3tProj m).map ((q3tdDeck m).act t x) = (q3tProj m).map x
-- 証明: q3t_period の zpow 一般化（Quot.sound・x⁻¹·(qᵗx)=qᵗ ∈ q^ℤ を可換整理・⟨t,rfl⟩）。

/-- **q3td-5c（★）: 自由性** qᵗ·x = x → t = 0（m≥1・第1成分算術のみ）。 -/
theorem q3td_deck_free (m : Nat) (hm : 1 ≤ m) (t : Int) (x : q3tGrp.carrier) :
    (q3tdDeck m).act t x = x → t = 0
-- 証明: 第1成分 m·t + x.1 = x.1 → m·t=0 → t=0（逆元消去すら不要・omega）。

/-- **q3td-5d（★）: ファイバー推移性** proj x = proj y → ∃ t, qᵗ·x = y。 -/
theorem q3td_deck_transitive (m : Nat) (x y : q3tGrp.carrier)
    (h : (q3tProj m).map x = (q3tProj m).map y) : ∃ t, (q3tdDeck m).act t x = y
-- 証明: quot_exact q3tGrp (normalCong ...) h → mem(x⁻¹y) → ⟨t, ht: qᵗ=x⁻¹y⟩ →
--       qᵗ·x = (x⁻¹y)·x = y（可換整理）。∃ の除去は Prop ゴール内で choice-free。

/-- **q3td-5e: ファイバー＝軌道**（5b+5d の iff 束ね）— Galois 被覆の核心。 -/
theorem q3td_fiber_orbit (m : Nat) (x y : q3tGrp.carrier) :
    (q3tProj m).map x = (q3tProj m).map y ↔ ∃ t, (q3tdDeck m).act t x = y
```

### 3.6 capstone

```lean
/-- **q3td-6: 実 Tate 被覆デッキデータ** — 実被覆 ℚ₃^×→E_q(ℚ₃)（全射・核＝q^ℤ）・
    デッキ群 ℤ（周期準同型の単射・∃形像）・自由推移的被覆変換作用・無限位数定理
    （外部仮説 discharge）を束ねる。tempered π₁ の離散部分の初の非退化実実現。 -/
structure Q3TateDeckData where
  m : Nat
  hm : 1 ≤ m
  proj_surj : ∀ x, ∃ a, (q3tProj m).map a = x
  ker_eq : ∀ x, (q3tProj m).map x = (q3tCurve m).one ↔ ∃ t, (q3tdPeriodHom m).map t = x
  deck_inj : (q3tdPeriodHom m).Injective
  deck_over : ∀ t x, (q3tProj m).map ((q3tdDeck m).act t x) = (q3tProj m).map x
  deck_free : ∀ t x, (q3tdDeck m).act t x = x → t = 0
  fiber_orbit : ∀ x y, (q3tProj m).map x = (q3tProj m).map y ↔ ∃ t, (q3tdDeck m).act t x = y
  infinite_order : discRig_infiniteOrder_hypothesis q3tGrp (q3tQ m)

def q3tdData : Q3TateDeckData    -- m=1（q=3）見出し実例
theorem q3tdDeck_exists : Nonempty Q3TateDeckData
```

**正直な限定（q3td ヘッダに記載・消さない）**: (1) 位相・解析構造なし——tempered π₁ の定義
（Berkovich 被覆理論）そのものではなく K-点の群論的影。(2) 実現は離散**商** ℤ のみ——tempered
群本体・profinite 部分との拡大は A5b、punctured/θ は範囲外（§6）。(3) 担体は群提示
3^ℤ×ℤ₃^×（A2/A8 恒久限定の継承）。(4) p=3・q∈3^ℤ 固定。(5) 一般 m の指数抽出逆写像は
∃形（m=1 のみ双方向明示）。(6) 既存 M333F/M364F の仮説付き機構は消さず併設。

---

## 4. A5b 設計 — `IUT/Q3TemperedPi1.lean`（prefix `q3tp`・tier M・q3td 依存）

**分類ヘッダ**: [実／昇格(a)]。M364F `tmpTemperedGroup = ẑ×ℤ` 代理の**両成分**を実部品に置換した
pro-3 tempered 模型を建設: profinite 側は**実 ℤ₃(1) = tmzLimit**（A7b・実円分体内の実 μ の
逆極限・遷移=実 cube）、離散側は **A5a の実デッキ群**（q3tdPeriodHom で実 q^ℤ と同定）。
complete_pct 影響: A5 0.1→0.15（見込み）。

依存: `IUT.Q3TateDeck`・`IUT.TemperedPi1`・`IUT.TateModuleZ3`・`IUT.CyclotomicTowerLimit`。
規模見積もり: 約 280–350 行。

### 4.1 pro-3 tempered 群と完全列

```lean
/-- **q3tp-1（★）: pro-3 tempered 模型** π₁^{temp,(3)}(E_q) = ℤ₃(1) × ℤ —
    M364F ẑ×ℤ の ẑ を実 ℤ₃(1)（実円分 μ の逆極限）に置換した実成分版。
    compact Tate 曲線の tempered π₁ は可換（≅ ẑ(1)×ℤ）なので直積は群構造として忠実。 -/
def q3tpGroup : Grp := prodGrp tmzLimit intGrp

def q3tpIncl : Hom tmzLimit q3tpGroup      -- z ↦ (z, 0)
def q3tpProj : Hom q3tpGroup intGrp        -- (z, n) ↦ n
theorem q3tp_extension_exact : ...          -- 1 → ℤ₃(1) → π₁^{(3)} → ℤ → 1
-- 証明: tmp_incl_injective / tmp_proj_surjective / tmp_extension_exact と同型の成分計算。
```

### 4.2 離散商の実実現（A5a の消費・本モジュールの核）

```lean
/-- **q3tp-2（★★）: 離散商 ℤ ＝ 実 Tate 被覆のデッキ群** — q3tpProj の値域 ℤ は
    q3tdPeriodHom（単射・像＝ker(q3tProj)）を通じて実 q^ℤ ⊂ 実 ℚ₃^× と同定される。
    合成 q3tpGroup → ℤ → ℚ₃^× が単射×準同型で、像＝実被覆の核。 -/
def q3tpDeckRealize (m : Nat) : Hom q3tpGroup q3tGrp   -- (z,n) ↦ qⁿ（q3tdPeriodHom ∘ q3tpProj）
theorem q3tp_deck_realize_ker (m : Nat) (hm : 1 ≤ m) (x : q3tpGroup.carrier) :
    (q3tProj m).map ((q3tpDeckRealize m).map x) = (q3tCurve m).one   -- 像⊆核
theorem q3tp_deck_faithful (m : Nat) (hm : 1 ≤ m) :
    ∀ a b : Int, (q3tdPeriodHom m).map a = (q3tdPeriodHom m).map b → a = b
```

### 4.3 M364F 条件付き存在の無条件化（実主語）

```lean
/-- **q3tp-3（★）: 実主語では tempered データが無条件に存在** — M364F tmp_exists の
    hInf 条件節を q3td_infinite_order で充填。 -/
theorem q3tp_exists_unconditional (m : Nat) (hm : 1 ≤ m) : ...
```

（注: M364F `TemperedPi1Data K` は `K : IUTField` パラメータのため q3Ring では直接
インスタンス化できない——q3Ring に IUTField は付かない（A2 恒久限定・choice-free 裏取り済み）。
よって **Grp 主語の新 structure `Q3TemperedPi1Data` を立て、M364F の各フィールドを実部品で
埋める**。既存 TemperedPi1Data は消さない。）

### 4.4 実 Galois 作用（tmzActHom の消費）

```lean
/-- **q3tp-4（★）: 実 Gal(ℚ(ζ_{3^∞})/ℚ) の作用** — profinite 部分 ℤ₃(1) には実作用
    tmzActHom s（A7b・χ 冪）、離散デッキ部分には自明作用（算術 π₁ の標準形:
    deck/値群方向固定・μ 方向 χ 倍——M429F atpTw と同じ形）。成分ごとの積で
    q3tpGroup 全体の実自己準同型。 -/
def q3tpGalAct (s : ctlProfinite.carrier) : Hom q3tpGroup q3tpGroup
theorem q3tp_gal_act_hom / q3tp_gal_act_deck_trivial / q3tp_gal_act_mu_char : ...
```

### 4.5 tempered 核の継承と capstone

`tmp_discrete_vs_profinite`・`theta_deck_not_finite`（非可除・非有界指数）は主語が intGrp の
まま再利用可能（離散部の非副有限性＝tempered の核心）。capstone `Q3TemperedPi1Data` は
実 E_q・実被覆・実デッキ同定・実 ℤ₃(1)・完全列・実 Gal 作用・非有界指数・無条件存在を束ねる。

**正直な限定（q3tp ヘッダ・消さない）**: (1) profinite 側は **pro-3 部分のみ**（本物の
ẑ(1)=lim_n μ_n 全体は全 n 円分塔が必要・後続）。(2) compact E_q の可換 tempered のみ——
IUT 本丸の punctured 曲線の**非可換** θ 拡大（tpeGroup の実化）は範囲外。(3) ℤ₃(1) は円分側
（Tate 加群の μ 成分）で、幾何的 T₃(E_q) の q^{1/3^n} 成分（w=q^{1/2} の A8b 系列の一般化）
との 2 成分拡大は未構成。(4) Gal は円分切片 Gal(ℚ(ζ_{3^∞})/ℚ)（実 G_{ℚ₃} でない）。
(5) 位相なし・p=3。

---

## 5. A5c 設計 — `IUT/Q3TateCoverTower.lean`（prefix `q3tc`・tier M・q3td 依存・A5b と並列可）

**分類ヘッダ**: [実／昇格(a)]。M374F `ttwDeckTower`（裸の ℤ/l^n）と M369F `tcvDeckGroup` を
実曲線の有限中間被覆で実現する: **E_{q^n}(ℚ₃) → E_q(ℚ₃) は実 degree-n 被覆でデッキ群 ℤ/n**。
鍵は恒等式 **q3tQ (m·n) = (q3tQ m)ⁿ**（成分計算で証明可能）——中間被覆 ℚ₃^×/(qⁿ)^ℤ が
**既存の q3tCurve (m·n) そのもの**として現れ、新しい商構成が不要になる。
complete_pct 影響: A5 0.15→0.2（見込み・上限）。

### 5.1 主要部品

```lean
theorem q3tc_q_pow (m n : Nat) : q3tQ (m * n) = tateNpow q3tGrp (q3tQ m) n
-- 証明: Prod ext。第1成分 q3t_npow_fst（m·n）・第2成分 q3t_npow_snd_of（単数部=1）。

/-- Grp 一般の新補題（TateCurve.lean 系イディオム・唯一のやや新しい代数部品）:
    (gⁿ)ᵗ = g^{n·t}。tateZpow_add の帰納で ~40 行。 -/
theorem tateZpow_npow (G : Grp) (g : G.carrier) (n : Nat) (t : Int) :
    tateZpow G (tateNpow G g n) t = tateZpow G g ((n : Int) * t)

theorem q3tc_nested (m n : Nat) (x) :
    (q3tSubgroup (m * n)).mem x → (q3tSubgroup m).mem x   -- (qⁿ)^ℤ ⊆ q^ℤ

/-- **q3tc-1（★）: 実中間被覆** E_{qⁿ}(ℚ₃) = q3tCurve (m·n) → q3tCurve m = E_q(ℚ₃)。
    Quot.lift で q3tProj m を降下（well-def は q3tc_nested + Quot.sound）。 -/
def q3tcHom (m n : Nat) : Hom (q3tCurve (m * n)) (q3tCurve m)
theorem q3tc_surjective / q3tc_ker : ...   -- 核＝q^ℤ/(qⁿ)^ℤ の像（∃ j 形）

/-- **q3tc-2（★）: 有限デッキ作用 ℤ/n** — [j]·[x] = [q^j·x]（j mod n で well-def:
    qⁿ の類は q3tCurve(m·n) で自明＝q3tc_q_pow）。自由・ファイバー推移的（q3td の降下）。
    tcvDeckGroup n = zmod n（M369F）の初の実曲線実例。 -/
def q3tcDeckFin (m n : Nat) : GAction (zmod n)   -- carrier := (q3tCurve (m*n)).carrier

/-- **q3tc-3: 実被覆塔** E_{q^{l^k}}(ℚ₃) = q3tCurve (m·l^k) の入れ子塔・遷移
    q3tcHom の合成・デッキ群塔 ℤ/l^k ＝ M374F ttwDeckTower l k の実例化。 -/
theorem q3tc_tower_nested / q3tc_tower_deck : ...
```

**正直な限定**: TateCoverCat/Galois 圏（M191F/M195F）への実対象登録（実ファイバー
{[q^j]} ≅ ℤ/n を tateLevelCover n と同定）は本ファイルでは**行わない**（圏側の主語替えは
別ラウンド・A5d 後続として明記）。塔の逆極限 ℤ_l との接続は M374F 既存機構の消費に留める。

---

## 6. 境界の正直な線引き（本ラウンドで本物化**しない**もの）

| 項目 | 状態 | 理由・後続 |
|---|---|---|
| Berkovich/rigid 解析化・位相被覆理論 | **範囲外（恒久的に重い）** | tempered π₁ の定義本体。位相・解析構造の形式化は現機構（Grp/CRing・choice-free）の外。A5 の 1.0 はこれ無しには到達しない——**A5 上限は当面 0.35–0.4 程度**と見積もる（§7.3） |
| punctured E_q の非可換 θ 拡大（tpeGroup/atpGroup の実化） | 範囲外（後続 A5d 候補） | Heisenberg シクロトーム c を実 μ（tmzLimit）に、deck を q3td に接続する構想は自然だが、実 θ 関数（柱E）と cuspidal 幾何（A8c=0）に依存。fable 詳細化ラウンドを先行させるべき本丸 |
| ẑ(1) 全体（全 n の μ 逆極限） | 範囲外 | 実円分塔は 3-冪のみ（A3/A7 の p=3 固定）。pro-3 で正直に主張 |
| 幾何的 Tate 加群 T₃(E_q)（q^{1/3^n} 成分込みの 2 成分拡大） | 範囲外 | A8b の w=q^{1/2} の 3-冪塔一般化が先（A8 後続） |
| tempered 遠アーベル復元（slim・[SemiAnbd]） | 範囲外 | M364F の外部仮説のまま（消さない）。compact E_q 模型は可換＝非 slim を正直に継承 |
| 実 π₁^ét（A4）との依存 | **独立に進行可能** | A5a/b/c は A4 の成果物を消費しない（デッキ側は離散・profinite 側は A7b の実 μ 逆極限を消費）。逆に A5b の実 ℤ₃(1)×ℤ は将来 A4 の実 π₁^ét(E_q)=T(E_q) 構成の部品になる |
| TateCover 系（M188F–M206F）の主語替え | 範囲外（A5d 後続） | 圏・fiber functor の実対象化は q3tc の後で独立ラウンド化 |

---

## 7. status 寄与・柱A% 効果・候補比較・実装計画

### 7.1 段階分解と見積もり（保守・独立監査確定が条件）

| 段階 | 内容 | A5 status | 根拠 |
|---|---|---|---|
| **A5a**（q3td） | 実デッキ群 ℤ＝実被覆の核・自由推移作用・外部仮説 discharge | 0 → **0.1** | 初の非退化実対象（実主語・仮説ゼロ）。ただし離散商のみ・位相なしで 0.5（忠実な部分ケース＝構造全体の実例）には遠い |
| **A5b**（q3tp） | pro-3 tempered 模型・両成分実・完全列・実 Gal 作用・無条件存在 | 0.1 → **0.15** | tempered「群」として両成分が実になる質的前進。pro-3 限定・可換 compact 限定で 0.2 未満 |
| **A5c**（q3tc） | 実有限中間被覆 E_{qⁿ}→E_q・デッキ ℤ/n・実被覆塔 | 0.15 → **0.2（上限）** | M374F/M369F の塔が実曲線に着地。θ/位相/punctured 皆無のため 0.2 で cap |

**A5a 単独で A5 0→0.1 に届くか（設問 5 への正答）**: 届く見込み——「実対象なし(0)」を
脱する要件（実主語・非退化・外部仮説なし・#print axioms クリーン）を満たす。ただし監査が
「離散商 1 成分のみ」を理由に 0.05 と裁定するリスクはあり、その場合柱A は 47 のまま
（47.24・丸め届かず）。**リスクヘッジとして A5a+A5b の 2 本立てを推奨**（A8a/A8b と同じ構図）。

### 7.2 柱A% 算術（target_ledger.json 実測・総 weight 100）

現在 Σ_A = 46.74（A1 .85·8 + A2 .65·8 + A3 .75·12 + A4 .5·14 + A5 0 + A6 .55·14 +
A7 .35·12 + A8 .57·12 + A9 0）。丸め 47。

| A5 | Σ_A | 表示 |
|---|---|---|
| 0.05 | 47.24 | 47（据え置き） |
| **0.1** | **47.74** | **48** ✅（丸め境界 A5≥0.076） |
| 0.15 | 48.24 | 48 |
| 0.2 | 48.74 | 49（監査が満額なら） |

### 7.3 候補比較（採用理由）

| 候補 | 判定 | 理由 |
|---|---|---|
| **(採用) A5a 実デッキ群 ℤ** | ✅ | 今セッションの実 E_q(ℚ₃) を直接消費・ブロッカーなし・全部品既存・M333F/M364F の名指し外部仮説を定理化する旗艦 discharge・tier M で足りる |
| tpeGroup（Heisenberg θ 拡大）の実化 | ❌ 今回見送り | 実 θ・cuspidal 幾何（柱E・A8c=0）依存。fable 詳細化が先（degenerate でなく時期尚早） |
| M188F tateModel の G_K を実 ctlProfinite に置換 | △ 後続（A5d） | 算術商側の昇格として有効だが、G_K が円分切片のみの現状では「デッキの実化」より寄与が薄い。q3tp-4 の実 Gal 作用で部分先取り |
| ẑ 全体の実化 | ❌ | 全 n 円分塔が必要（p=3 恒久限定と衝突）。pro-3 で正直に進むのが §3 適合 |
| 骨格側の追加補題（Ẑ×ℤ 上） | ❌ §2 禁止 | complete_pct を動かさない水増し |

### 7.4 実装ラウンド計画（親向け）

- **直列依存**: q3td → {q3tp, q3tc}（後 2 者は相互独立・並列可）。
- **tier/model**: 3 本とも **M（opus）**。fable は不要（新イディオムは tateZpow_npow 程度で
  既存帰納イディオムの写経圏内）。詰まったら HELP スポットのみ fable。
- **choice-free 規律**: 全証明で新規 Classical.choice 禁止・∃ の除去は Prop ゴール内のみ・
  各 public 対象の #print axioms = [propext, Quot.sound] を実装者が自己申告→独立監査が再実行。
- **監査観点（先回りで指示）**: (i) q3td_infinite_order が本当に仮定ゼロか（hm のみ可）、
  (ii) q3tdDeck の自由性・推移性が m=1 実例で非空虚に検算されているか、(iii) 既存
  M364F/M333F の仮説・正直な限定が消されていないか、(iv) q3tp の「pro-3 限定」「可換
  compact 限定」がヘッダ・docstring 双方に残っているか。
- **共有ファイル**（IUT.lean・build.sh・graph-meta.json・dashboard.md・gen_graph.py PILLAR
  辞書への q3td/q3tp/q3tc 追記）は親が統合時に一括更新（サブエージェント運用規約）。

---

## 8. まとめ（設問への回答）

1. **実 Tate 被覆とデッキ群 ℤ**: 全部品が既存（q3tProj・quotientProjN_ker・q3t_npow_fst）。
   新規は zpow 第1成分公式と GAction 束ねのみ。q^ℤ ≅ ℤ は単射＋像特徴付けで本物（m=1 は
   双方向明示逆写像まで）。
2. **tempered π₁ の構造**: 離散 ℤ 商は A5a で実 q^ℤ に置換。profinite 側は tmzLimit
   （実 ℤ₃(1)）と接続**できる**（A5b・prodGrp・実 Gal 作用 tmzActHom 込み）——ただし pro-3
   限定・可換 compact 限定を正直に主張。
3. **被覆の圏論的側面**: 実中間被覆 E_{qⁿ}→E_q（q3tc）でデッキ ℤ/n・被覆塔まで実現可能。
   Galois 圏（M195F）への実対象登録は A5d 後続に切り出し（今回は過大主張しない）。
4. **境界**: Berkovich/θ/punctured/ẑ 全体/遠アーベル復元は範囲外（§6 表）。A4 とは独立。
5. **最小ステップ**: A5a 単独で A5 0→0.1（柱A 47→48・丸め境界 0.076 を超える）見込み。
   監査下振れリスクに備え A5a+A5b 推奨。3 本フル成立で A5=0.2 上限・柱A 49 の可能性。

**中心判定の明記**: 実 Tate 被覆 ℚ₃^× → E_q(ℚ₃) のデッキ群 q^ℤ ≅ ℤ は、tempered
π₁^temp(E_q) の離散部分の**本物の忠実な算術的実現である（K-点の影・位相なし・離散商に限る）**。
toy 模型の「別コース完成」ではなく、実 IUT 本コース上の A5 初の実歩と判定する。
