# A8 実 Tate 曲線 詳細化ラウンド設計 — E_q(ℚ₃) の実構成（2026-07-10）

**種別**: 詳細化ラウンド（設計ドキュメントのみ・Lean 実装なし）
**対象**: 柱A A8「楕円曲線/Tate 曲線の実被覆・cuspidalization」（w12・status 0.5）
**土台**: 今セッション完成の実 p 進機構 — `Q3LocalField.lean`（実 ℚ₃=ℤ₃[1/3]・q3f）・
`Q3UnitsGroup.lean`（実 ℚ₃^×＝3^ℤ×ℤ₃^×↪ℚ₃・q3u）・`Zp3ValuationRing.lean`（z3v）
**目的**: A8 の既存模型/退化 witness を実 ℚ₃ 上の本物へ昇格する最小 complete_pct
前進ステップを、opus 実装枠に渡せる粒度まで分解する。

---

## 0. 結論サマリ

| 項目 | 内容 |
|---|---|
| 選定ステップ | **A8a**: 実 Tate 曲線 E_q(ℚ₃) = (3^ℤ×ℤ₃^×)/q^ℤ（q=3^m・**実付値 v(q)=m≥1**・q の実無限位数）＋ **A8b**: 実 2-捻れ E₉[2]（実 w=3 で w²=q=9・**実位数ちょうど 2**・実 μ₂={±1}・Klein 4 群 ⊆ E₉[2]） |
| 新規ファイル | `IUT/Q3TateCurve.lean`（prefix `q3t`）→ `IUT/Q3TateTorsion.lean`（prefix `q3tt`・q3t 依存） |
| tier | **両方 M（opus）**。新イディオム不要（quotientGroupN 適用・prodGrp 成分算術・q3u/q3f 補題の再利用のみ）。fable 枠不要 |
| A8 status 見込み | 0.5 → **0.6**（A8a 単独では 0.55 止まり＝柱A% 丸め境界で 47 未保証。A8b まで入れて確保。独立監査確定が条件） |
| 柱A% | Σ_A 45.9 → 47.1 ⇒ **46 → 47**（A8a+A8b 両方成立時） |
| A8c cuspidalization | **今回 0**（モジュール皆無・実 π₁^ét/実 G_{ℚ₃} 依存で後続。§6 で正直に線引き） |

---

## 1. 現状実測 — 既存 A8 資産の実／模型判定（精読結果）

| モジュール | 分類 | 実測内容 | A8 残欠との関係 |
|---|---|---|---|
| `TateCurve.lean`（M309F・q3t の直接昇格対象） | **実（機構）／witness 退化** | E_q=K^×/q^ℤ を**一般 IUTField K** 上の本物の商群として構成。tateZpow 整数冪・q^ℤ 部分群・周期性 [u]=[qu] は完全証明。**ただし存在 witness `tateCurveDataOne` は q=1（自明周期）**、無限位数 `tate_qpow_ne_one` は「v(q)=some m≠0 の付値」を**外部仮定**（honest note: 「正 valuation の witness は未達」「trivialValuation は rank 0」） | graph-meta「実Tate曲線K^×/q^ℤ済み」の実体はこれ。「A8=0.5(機構は実だが実例が自明/退化)」の主因 |
| `TateTorsion.lean`（M314F） | **実（機構）／条件付き** | E_q[n] 部分群・μ_n⊆E_q[n]・位数ちょうど言明（M314F-5）は完全証明だが、**q^{1/n}=w は witness で受け取り**・**位数言明の付値 v は外部入力**（honest note 明記） | A8b の昇格対象 |
| `EllipticCurve.lean`（M304F）・`EllipticJInvariant.lean`（M310F） | **実** | Weierstrass 曲線・j 不変量の代数核（体一般・実例 ℚ）。Tate 曲線との同型（a₄(q),a₆(q) 級数）は未接続 | 今回は触らない（後続） |
| `TateQuotient.lean`（M91） | 骨格（柱E 帰属） | 中心元 q を持つ一般群の q^ℤ 商（Nat 冪対称関係） | propext-lift の核抽出イディオムの参考のみ |
| `TateCoverGroup/Cat/Galois/FiberFunctor/SurrogateCapstone`（M188F/191F/195F/200F/206F） | **代理（A-3β プログラム）** | tempered π₁ の具体提示（デッキ ℤ・`tateModel` の**抽象 G_K**・ẑ）と被覆圏の Galois 圏化。スキーム論的エタール被覆の**代理**と自己申告 | 今回は消さない・触らない（実 π₁^ét は A4/A5 の本丸） |
| `TateModuleZ3.lean`（tmz） | 実（**A7b 帰属**） | ℤ₃(1)=lim μ_{3^{n+1}}（円分側）。幾何的 T_l(E) ではない（honest note (ii)） | §5 で境界判定 |
| cuspidalization | **皆無** | `grep -i cusp IUT/` = 0 件。モジュール自体が存在しない | §6 |

**ブロッカー履歴**: `audit/A-next-leverage-scope-2026-07-10.md` §3 は A8 を「**A2 ブロッカーで保留**」
（実離散付値の不在・M314F-5 が外部仮定のまま）と判定し、「**A2（実付値/実局所体）が先に立つと
一挙に本物化する**」「A8（実付値を得てから）」と順序付けた。A2 は本日 0.65 で独立監査確定
（`reaudit-A2-real-padic-local-field-2026-07-10.md`）し、`Q3UnitsGroup.lean` ヘッダは
「**A8（Tate 曲線 K^×/q^ℤ を実 ℚ₃^× 上で・v(q)≥1 の実 q）…のブロッカー解消はこのファイルが
直接の接点**」と明記している。**本設計はその接点を実際に消費する**。

---

## 2. 設計原理 — なぜ q3u 群提示経由か（問い 1・2 への答え）

### 2.1 直接路は choice-free 不能（正直な理由・却下）

M309F の `tateMultGroup K` は `K : IUTField` の **total inv** を要求する。しかし
`q3Ring : CRing` は体でない（A2 監査確定の恒久障害: ℚ_p は構成的には離散体でなく、
x≠0 からの逆元計算は Markov 原理を要する。忠実版は ∃形 `q3f_has_inverses`）。したがって

- `tateMultGroup q3Ring` は型が合わない（IUTField インスタンス皆無＝A2 監査の choice-free 裏取り事項）。
- `{x : q3Ring.carrier // x ≠ 0}` を Grp 化する路も **inv フィールドが埋まらず choice-free 不能**。

この限定は消さない・弱めない（§4 規約）。「実 ℚ₃^×」の忠実な choice-free 実現は
A2c-2 が構成した**群提示 3^ℤ×ℤ₃^×** である:

```
QpUnits 3 isPrime_three = prodGrp intGrp (zpUnits 3 isPrime_three)   -- 本物の Grp
q3uEmbed : (QpUnits 3 …).carrier → q3Ring.carrier                    -- (k,u) ↦ [3^k·u]
q3u_embed_hom / q3u_embed_inj                                        -- 単射乗法準同型
q3u_image_char                                                       -- 像 = 非零 witness 付き元全体（∃形）
```

### 2.2 採用路: E_q = (3^ℤ×ℤ₃^×)/q^ℤ、実 q = 3^m（v(q)=m≥1）

q^ℤ 側の機構は **M309F が Grp 一般で既に本物**（`tateZpow`/`tateNpow` は `(G : Grp)` 引数、
`tateQPowersSubgroup : (G : Grp) → g → Subgroup G`、商は `quotientGroupN`）。
IUTField 特化なのは `tateMultGroup`/`tateQPowers_isNormal` だけで、後者は可換性しか
使っていない。よって

- **q = q3tQ m := ((m:Int), 1) ∈ ℤ × ℤ₃^×**（m≥1）。q3uEmbed で実 ℚ₃ の元 3^m に写る。
  q=3（m=1）が見出し実例。q^ℤ = 3^ℤ 側の部分群 ⟨(m,1)⟩ = mℤ×{1}（問い 2 の実現形そのもの）。
- **v(q)=m≥1 は実付値で証明**: `q3fValRel (q3uEmbed (q3tQ m)) m`（`q3f_uniformizer`
  の z3vExact 3 1 と `q3f_val_mul` から）。M309F honest note の「正 valuation witness 未達」
  を**実 ℤ 値付値 q3fValRel で discharge** する初の実例。
- **q の無限位数は本物**: `tateNpow (QpUnits 3 …) (q3tQ m) n` の第 1 成分は m·n≠0（omega）。
  外部付値仮定なしの実証明（さらに実付値公式 v(qⁿ)=m·n も付ける、§3.2 q3t-6）。
- **周期性 [u]=[qu] を実 ℚ₃ の中で読む**: `q3u_embed_hom` により
  q3uEmbed(q·x) = q3Ring.mul (3^m の像) (q3uEmbed x)、すなわち商での同一視は
  実 ℚ₃ の元 u と 3^m·u の同一視である（§3.2 q3t-5）。

### 2.3 主語の正直な限定（消さない・引き継ぐ）

- E_q の担体は**群提示 3^ℤ×ℤ₃^×**（q3uEmbed で ℚ₃ 内の部分群と単射同定・像の全射性は
  `q3u_image_char` の ∃形まで）。「文字通りの {x:ℚ₃ // x≠0} の商」ではない——A2 の
  ∃形体性と同一ラインの恒久限定として header に明記する。
- p=3 固定・q ∈ 3^ℤ（単数部込みの一般 q=3^m·u₀ は自然な一般化だが今回は u₀=1。
  header に後続と明記）。
- 既存 `TateCurve.lean`/`tateCurveDataOne`/TateCover 系は**消さず併設**（§2(a) 昇格の規約）。

---

## 3. A8a: `IUT/Q3TateCurve.lean`（prefix `q3t`・tier M=opus・想定 400–500 行）

**分類ヘッダ（必須記載）**: [実／昇格(a)] — M309F `TateCurve.lean` の退化 witness
（q=1・付値外部仮定）を、実 ℚ₃^×（q3u 群提示）上の実 q=3^m（実付値 v(q)=m≥1・実無限位数）
へ昇格。complete_pct 影響: A8 0.5→0.55（本ファイル）・A8b と合わせ 0.6 見込み。

**依存**: `import IUT.Q3UnitsGroup`（→ Q3LocalField→Zp3ValuationRing・FullReciprocity）、
`import IUT.TateCurve`（→ QuotientGroup・ValuationRing）。全て既存・共有ファイル不変更。

### 3.1 部品表と Lean スケッチ

```lean
-- q3t-0: 主語の固定
@[reducible] def q3tGrp : Grp := QpUnits 3 isPrime_three   -- = prodGrp intGrp (zpUnits 3 …)

-- q3t-1: 可換性（intGrp の加法可換 × zpMul_comm を Subtype.ext/成分で）
theorem q3t_comm (x y : q3tGrp.carrier) : q3tGrp.mul x y = q3tGrp.mul y x

-- q3t-2: 可換群では任意部分群が正規（M309F tateQPowers_isNormal の Grp 一般化・可換性のみ使用）
theorem q3t_normal (H : Subgroup q3tGrp) : IsNormalSubgroup q3tGrp H

-- q3t-3: 実 Tate パラメータ q = 3^m（m ≥ 1）と実付値証明書
def q3tQ (m : Nat) : q3tGrp.carrier := ((m : Int), (zpUnits 3 isPrime_three).one)
theorem q3t_q_embed : q3uEmbed (q3tQ 1) = (ringLocMap z3 q3S).map q3fThree
  -- [3^1·1 / 3^0] = ι(3)。z3.mul_one の書き換え＋ Quot.sound（q3u_frac_eq 流用可）
theorem q3t_q_val (m : Nat) : q3fValRel (q3uEmbed (q3tQ m)) (m : Int)
  -- witness ⟨3^m·1, 0, m, …⟩・z3vExact は q3_pow_exact m ＋ mul_one。κ = m − 0

-- q3t-4: ★ 実 Tate 曲線 E_q(ℚ₃) と射影
def q3tSubgroup (m : Nat) : Subgroup q3tGrp := tateQPowersSubgroup q3tGrp (q3tQ m)
def q3tCurve (m : Nat) : Grp := quotientGroupN q3tGrp (q3tSubgroup m) (q3t_normal _)
def q3tProj (m : Nat) : Hom q3tGrp (q3tCurve m) := quotientProjN … -- 全射 quotientProjN_surjective
theorem q3tCurve_abelian (m : Nat) : ∀ x y, (q3tCurve m).mul x y = (q3tCurve m).mul y x

-- q3t-5: ★ 周期性 — 商上の [x]=[qx] と、その実 ℚ₃ 内での読み（q3u_embed_hom の実消費）
theorem q3t_period (m : Nat) (x : q3tGrp.carrier) :
    (q3tProj m).map x = (q3tProj m).map (q3tGrp.mul (q3tQ m) x)
  -- M309F-5 tate_point_period と同一の証明（Quot.sound ＋ tate_gen_mem・可換整理）
theorem q3t_period_real (m : Nat) (x : q3tGrp.carrier) :
    q3uEmbed (q3tGrp.mul (q3tQ m) x) = q3Ring.mul (q3uEmbed (q3tQ m)) (q3uEmbed x)
  -- q3u_embed_hom そのもの。「E_q の同一視 = 実 ℚ₃ の u ↦ 3^m·u」の証明書

-- q3t-6: ★ q の実無限位数（M309F honest note の discharge・外部付値仮定なし）
theorem q3t_q_pow_ne_one (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    tateNpow q3tGrp (q3tQ m) n ≠ q3tGrp.one
  -- 第 1 成分 = (m·n : Int) ≠ 0。tateNpow の成分計算補題 q3t_npow_fst を帰納で立て omega
theorem q3t_qpow_val (m n : Nat) :
    q3fValRel (q3uEmbed (tateNpow q3tGrp (q3tQ m) n)) ((m : Int) * n)
  -- 実付値公式 v(qⁿ)=m·n（M309F-6 tate_qpow_val の実 ℚ₃ 版）。q3f_val_mul ＋帰納

-- q3t-7: 実 −1 ∈ ℤ₃^×（q3tt の μ₂ と共用の部品・非自明点の分離にも使用）
def q3tNegOne : (zpUnits 3 isPrime_three).carrier :=
  ⟨(toZpRing 3).map (-1), …⟩   -- IsZpUnit: レベル 1 剰余 [−1]・¬3∣(−1)（omega）
theorem q3tNegOne_sq : (zpUnits 3 …).mul q3tNegOne q3tNegOne = (zpUnits 3 …).one
  -- (toZpRing 3).map_mul → map((−1)·(−1)) = map 1 = one（Subtype.ext）
theorem q3t_negone_ne_one : q3tNegOne ≠ (zpUnits 3 …).one
  -- レベル 1 で −1≢1 (mod 3)：等式から congrArg (·.val 1)・quot_exact intGrp (modCong 3)・omega

-- q3t-8: 曲線上の非自明点（退化 witness の質的超克）
theorem q3t_point_ne_one (m : Nat) (hm : 1 ≤ m) :
    (q3tProj m).map ((0 : Int), q3tNegOne) ≠ (q3tCurve m).one
  -- quotientProjN_ker で膜所属へ還元：⟨(m,1)⟩ の元は第 2 成分 one（tateZpow の成分補題）、
  -- q3tNegOne ≠ one（q3t-7）で矛盾

-- q3t-9: capstone（新規証明なし・束ねのみ）
structure Q3TateCurveData where
  m : Nat
  hm : 1 ≤ m
  q : q3tGrp.carrier            -- = q3tQ m
  q_val : q3fValRel (q3uEmbed q) (m : Int)          -- 実付値 v(q)=m≥1
  curve : Grp                                        -- = q3tCurve m
  abelian : …
  q_infinite : ∀ n, 1 ≤ n → tateNpow q3tGrp q n ≠ q3tGrp.one
  period : ∀ x, …                                    -- q3t-5
def q3tData : Q3TateCurveData := ⟨1, …⟩              -- 見出し実例 q = 3
```

### 3.2 実装ノート（opus への注意）

- `tateZpow`/`tateNpow`/`tateQPowersSubgroup` は Grp 一般なのでそのまま消費できる。
  `tateQPowers_isNormal`（IUTField 特化）だけは q3t-2 で可換 Grp 版を書く（数行）。
- prodGrp の冪の成分計算 `q3t_npow_fst : (tateNpow q3tGrp (q3tQ m) n).1 = (m:Int)*n`
  と `q3t_npow_snd : ….2 = one` を先に帰納で立てると q3t-6/q3t-8 が一行化する。
- `ringLocMap z3 q3S : RingHom z3 (ringLocRing z3 q3S)`（RingLocalization.lean:490）。
  `ringLocRf z3 q3fThree` は `ringLocRing z3 (ringLocPowers z3 q3fThree)` の略記
  （:595）なので型は整合。q3t-3 の等式は `q3u_frac_eq` の p=1,q=0,p'=1,q'=0 か直接
  Quot.sound で閉じる。
- 禁止タクティク（simp/decide/by_cases/rcases/ring/…）不使用・新規 Classical.choice
  禁止・#print axioms 自己確認（[propext, Quot.sound] のみ）は既存 A2 ラウンドと同一規約。

### 3.3 A8a の正直な限定（header 必載・消さない）

1. 担体は群提示 3^ℤ×ℤ₃^×（q3uEmbed 単射同定・像の全射性は ∃形 `q3u_image_char` まで。
   {x:ℚ₃//x≠0} の商は total inv 不可のため choice-free 不能——A2 の恒久限定を継承）。
2. p=3 固定・q=3^m（単数部付き一般 q・一般素数 p は後続）。
3. Weierstrass 模型（M304F）との同型（a₄(q),a₆(q) q-級数）・rigid 幾何・位相は皆無。
4. Θ の E_q 上の実現は柱E 後続（M309F-7 の骨組み申告を継承）。
5. TateCover 系（代理 π₁）とは未接続（実 π₁^ét は A4/A5）。cuspidalization 皆無（§6）。

---

## 4. A8b: `IUT/Q3TateTorsion.lean`（prefix `q3tt`・tier M=opus・想定 400–550 行＋stretch 150–250 行）

**分類ヘッダ**: [実／昇格(a)] — M314F `TateTorsion.lean` の 2 つの外部仮定
（q^{1/n}=w の witness 受け取り・位数言明の付値外部入力）を、実 ℚ₃ 上の
**実 witness（w=3, w²=q=9・体拡大なしで ℚ₃ 内に実在）**と**実位数証明**で discharge。
実 μ₂={±1}⊂ℤ₃^× と合わせ、**Klein 4 群 ⊆ E₉[2] を実構成**する。

**依存**: `import IUT.Q3TateCurve`。**q=q3tQ 2（=9・v(q)=2）で n=2 捻れ**が主語。

### 4.1 部品表と Lean スケッチ

```lean
-- q3tt-1: ★ 実 2 乗根 witness — w=3, w²=q=9（M314F「w は witness で受け取る」の実 discharge）
theorem q3tt_w_sq : q3tGrp.mul (q3tQ 1) (q3tQ 1) = q3tQ 2
  -- 第 1 成分 1+1=2・第 2 成分 one·one=one（成分計算・ほぼ rfl＋one_mul）

-- q3tt-2: ★ [w]=[3] の位数ちょうど 2（M314F-5 の外部付値仮定を実算術で置換）
theorem q3tt_w_torsion : (q3tCurve 2).mul ([w]) ([w]) = (q3tCurve 2).one   -- [w]²=[q]=1
theorem q3tt_w_order (k : Nat) :
    tateNpow (q3tCurve 2) ((q3tProj 2).map (q3tQ 1)) k = (q3tCurve 2).one → 2 ∣ k
  -- quotientProjN_ker（M267F-3d・両方向既存）で (k,1)∈⟨(2,1)⟩ へ還元 →
  -- ∃t, tateZpow q3tGrp (q3tQ 2) t = ((k:Int), one) を obtain（Prop ゴールなので choice 不要）→
  -- 第 1 成分 2t=k（tateZpow の成分補題・q3t_npow_fst の Int 版）→ 2∣k（omega）
  -- ※射影と冪の可換 (q3tProj m).map (tateNpow … x k) = tateNpow … ([x]) k を先に帰納で

-- q3tt-3: ★ 実 μ₂ = {±1} ⊂ ℤ₃^× の 2 捻れ（μ_n⊆E_q[n] の非自明実例）
def q3ttMuPoint : (q3tCurve 2).carrier := (q3tProj 2).map ((0 : Int), q3tNegOne)
theorem q3tt_mu_torsion : (q3tCurve 2).mul q3ttMuPoint q3ttMuPoint = (q3tCurve 2).one
  -- 成分: (0+0, (−1)·(−1)) = (0, 1)（q3tNegOne_sq）→ 単位元の類
theorem q3tt_mu_ne_one : q3ttMuPoint ≠ (q3tCurve 2).one
  -- quotientProjN_ker：⟨(2,1)⟩ の元は第 2 成分 one・q3t_negone_ne_one で矛盾

-- q3tt-4: ★ 類の分離補題（4 点の相互区別を一手で閉じる簿記）
theorem q3tt_class_eq_iff (k k' : Int) (u u' : (zpUnits 3 …).carrier) :
    (q3tProj 2).map (k, u) = (q3tProj 2).map (k', u') ↔ ((2:Int) ∣ (k' - k)) ∧ u = u'
  -- ker 特徴付け＋逆元/積の成分計算。⟨(2,1)⟩ の第 2 成分が常に one であることが核

-- q3tt-5: ★ Klein 4 群 {[1],[3],[−1],[−3]} ⊆ E₉[2]（実 (ℤ/2)² の実現・4 点相異）
theorem q3tt_klein_distinct : … -- q3tt-4 で 6 組の相異（2∤1・−1≠1 は q3t_negone_ne_one）
theorem q3tt_klein_closed : …   -- 4 点集合が積で閉じる（成分算術・q3tNegOne_sq）
structure Q3TateTorsionData where …  -- capstone: q=9・v(q)=2 実・w=3 実・位数 2 実・μ₂ 実
def q3ttData : Q3TateTorsionData := …

-- q3tt-6（★stretch・任意）: μ₂(ℤ₃^×) の完全性 u²=1 → u=1 ∨ u=−1
theorem q3tt_mu2_complete (u : z3.carrier) (hu : zpMul 3 u u = zpOne 3) :
    u = (toZpRing 3).map 1 ∨ u = (toZpRing 3).map (-1)
  -- 各レベル n: 3ⁿ∣(u−1)(u+1)・3 は u−1,u+1 の両方を割れない（差 2・¬3∣2）→
  -- レベル 1 の三分律（a%3 の omega 三分岐・Int の場合分けは or-除去で by_cases 回避）で
  -- u≡1 (mod 3) か u≡−1 (mod 3) に分岐 → 各分岐で全レベル 3ⁿ∣u∓1（素冪 Euclid 反復・
  -- not_dvd_ipow の同型イディオム）→ Zp の成分ごと等式で u=±1
-- 成立すれば E₉(ℚ₃)[2] = Klein 4 群「ちょうど」（M314F honest note
-- 「直積分解 E_q[n]=μ_n×⟨q^{1/n}⟩ の完全性は骨組み」の n=2 実 discharge）
```

### 4.2 stretch の扱い（正直規約）

q3tt-6 は素冪 Euclid の反復とレベル横断の整合で中規模（150–250 行）・**リスク中**。
詰まったら**落として良い**——その場合 header の正直な限定に「E₉[2] ⊇ Klein 4 群まで・
等号（μ₂ の完全性）は未達」と書く（**等号を主張しない**）。成立すれば「完全性の初の
実インスタンス」として 0.6 判定を固める材料になる。stretch の詰まり解決だけを
fable HELP スポットに回してよい（tier 規約 L の適用範囲内）。

### 4.3 A8b の正直な限定（header 必載）

1. **l=2 のみ**。奇素数 l の E_q[l] は数学的に ℚ₃ 有理でない（ζ_l∉ℚ₃（l≠2）・
   q^{1/l}∉ℚ₃）——IUT の l≥5 奇捻れは ℚ₃ の拡大体機構（未建設）の後続。これは
   「本コースの忠実な部分ケース」（§3 規約: 別コース 99% より本コース 3%）。
2. Galois 作用（G_{ℚ₃} の E_q[n] への作用）は皆無（実 G_{ℚ₃} 自体が A2 後続）。
3. M314F の一般機構（IUTField 上）は消さず併設。q3tt は q3tGrp 上に部分群を建て直す
   （tateTorSubgroup は IUTField 特化のため。Grp 一般化の小リファクタは実装者の裁量・
   ただし既存ファイルは変更しない＝新ファイル内に一般補題を置く）。

---

## 5. 問い 3 判定: Tate 加群 T_l(E_q) と ℤ₃(1)（tmz）の接続 — **今回は範囲外（境界明示）**

- T_l(E_q) の逆極限は各段で q^{1/l^n}・ζ_{l^n} を要するが、**どちらも ℚ₃ に living しない**
  （l=2: √3∉ℚ₃。l=3=p: q^{1/3}∉ℚ₃・ζ₃∉ℚ₃——x²+x+1≡(x−1)² mod 3 で Hensel 不成立の分岐拡大）。
  必要なのは **q3Ring 上の体拡大機構**（gefField は ℚ 上のみ）で、これは未建設の大物。
- tmz（`TateModuleZ3.lean`・ℤ₃(1)=lim μ_{3^{n+1}}）は **A7b 帰属**であり、各段の μ は
  ℚ(ζ_{3^{n+1}}) 住まい。ℚ₃ とは **ℚ↪ℚ₃（A2c-3）すら未接続**なので、
  0→ℤ_l(1)→T_l(E_q)→ℤ_l→0 の μ 側同定は A2c-3 完了後の別ラウンド。
- **判定**: A8 の今回範囲に含めない。境界線は「有限レベル n 捻れの ℚ₃ 有理部分＝A8b（今回）／
  逆極限 T_l と μ 側の tmz 同定＝A8 後続（A2c-3・拡大体機構が前提）」。設計に書いて正直に残す。

## 6. 問い 4 判定: cuspidalization — **今回 0（正直な線引き）**

- 実測: cuspidalization を主語にしたモジュールは**皆無**（grep 0 件）。存在するのは
  TateCover 系 = A-3β **代理**プログラム（`tateModel` の抽象 G_K・デッキ ℤ・ẑ）のみで、
  E∖{O} の**実** π₁^ét・基点・被覆の関手性は実体がない。
- 実 cuspidalization（cusp を復元する π₁ の cuspidal 惰性部分）は
  実 π₁^ét（A4/A5 本丸）＋実 G_{ℚ₃}（A2 後続）の両方に依存し、本ラウンドの最小範囲外。
- **本ラウンドの status 寄与は cuspidalization については 0** と報告に明記する
  （A8 のタイトルに含まれる語だが、0.6 の判定根拠は曲線・捻れの実体化のみに置く）。

---

## 7. 候補比較（採否と理由）

| # | 候補 | 内容 | 判定 |
|---|---|---|---|
| 1 | **ℚ₃/q3u 路（A8a+A8b）** | E_q=(3^ℤ×ℤ₃^×)/q^ℤ・実 v(q)=m≥1・実位数・実 2 捻れ | **採用**。監査が名指しした退化 witness／外部付値仮定を正面から discharge。全部品が既存（新イディオム 0）・q3u ヘッダの宣言済みブロッカー接点を消費 |
| 2 | 円分体路（E_q over `cteField ℓ`・q=3・cmrMu で μ_{3^ℓ}⊆E_q[3^ℓ]・cgarAct 実 Galois 作用） | cteField は total inv 持ち（gefNFIUTField）で M309F/M314F が**そのまま**実例化でき、μ 側は豊富 | **後続に温存**。ℚ(ζ_{3^ℓ}) 上の 3 進（λ=ζ−1 Eisenstein）実付値が未構成のため位数言明が外部仮定のまま（leverage-scope §3 の「0.5→0.55 不確実」判定を踏襲）。A8-次ラウンドの本命（実付値を円分体へ拡張してから） |
| 3 | {x:q3Ring//x≠0} の直接商 | 文字通りの ℚ₃^×/q^ℤ | **却下**（choice-free 不能・§2.1。∃形限定として正直申告） |
| 4 | T_l(E_q) 逆極限・tmz 接続 | l 進 Tate 加群 | **範囲外**（§5。拡大体機構・A2c-3 が前提） |
| 5 | TateCover 系の再束ね・capstone 追加 | 代理プログラムの整備 | **却下**（complete_pct を動かさない骨格追加＝§2 水増し） |

---

## 8. status 寄与・柱A% 算術（保守・監査確定前提）

現状 Σ_A = 8·0.85 + 8·0.65 + 12·0.75 + 14·0.5 + 10·0 + 14·0.55 + 12·0.35 + 12·0.5 + 10·0
= **45.9**（表示 46）。A8 は w12。

| シナリオ | A8 | Σ_A | 柱A% 表示 |
|---|---|---|---|
| A8a のみ成立 | 0.5→0.55 | 46.5 | **46 か 47（丸め境界・保証なし）** |
| A8a+A8b（core）成立 | 0.5→**0.6** | **47.1** | **47** ✓ |
| ＋q3tt-6 stretch 成立 | 0.6（判定を固める） | 47.1 | 47 |

**0.6 の根拠（何が実になるか）**: (i) 監査の名指し残欠「実例が自明/退化」（q=1 witness）が
実 q=3^m・実付値 v(q)=m≥1 で解消、(ii) M309F・M314F が外部仮定と正直申告した
付値・q^{1/n} witness の両方が実 ℚ₃ の中で discharge、(iii) 位数ちょうど・μ₂・Klein 4 群
という**非自明な実捻れ構造**が初めて立つ。

**0.6 を超えない根拠（cap・過大主張しない）**: 担体が群提示（∃形限定）・p=3・q∈3^ℤ・
l=2 のみ（奇 l 不能）・Galois 作用皆無・Weierstrass/Θ 未接続・TateCover 系は代理のまま・
**cuspidalization 0**・T_l 皆無。タイトルの「被覆・cuspidalization」半分が丸ごと残るため、
敵対的監査なら 0.55 判定もあり得る——報告では「0.6 は独立監査確定が条件」と明記する。

---

## 9. 実装ラウンド構成（親への引き渡し）

| wave | 枠 | tier/model | タスク | 依存 |
|---|---|---|---|---|
| 1 | 1 | **M / opus** | `Q3TateCurve.lean`（§3 の q3t-0〜9・単独ファイル） | 既存のみ（Q3UnitsGroup・TateCurve） |
| 2 | 1 | **M / opus** | `Q3TateTorsion.lean`（§4 の q3tt-1〜5 core・q3tt-6 stretch は任意） | wave 1 |
| 2′ | − | L / fable（スポットのみ） | q3tt-6 が詰まった場合の HELP（落として fallback 申告でも可） | − |
| 3 | 1 | S–M / sonnet or opus | 独立再監査（build EXIT 0・no sorry・全 public 対象 #print axioms=[propext,Quot.sound]・新規 Classical.choice 0・正直限定の header 検査）→ A8 status 判定 | wave 1–2 |

- サブエージェントは**新規ファイルのみ**作成。IUT.lean・build.sh・dashboard.md・graph 系・
  `target_ledger.json`・`graph-meta.json` の更新（A8 0.6・柱A 47・complete_note 追記・
  `tools/gen_graph.py` 再実行）は**親が統合時に一括**。
- `gen_graph.py` の PILLAR 辞書に `Q3TateCurve`/`Q3TateTorsion` → A を追記（親）。
- 残り並列枠は本設計の範囲外（他柱・A6/A2c-3 系で充当。水増し禁止規則を優先）。

### 監査チェックリスト（wave 3 用）

- [ ] q3tCurve が `quotientGroupN` の実適用であること（新規商構成の再発明でないこと）
- [ ] q3t_q_val / q3t_qpow_val が `q3fValRel`（実 ℤ 値付値）を主語にしていること
- [ ] q3t_q_pow_ne_one が付値の**外部仮定なし**で閉じていること（M309F honest note との差分）
- [ ] q3tt_w_sq / q3tt_w_order が M314F の witness/付値外部仮定の**実 discharge** になっていること
- [ ] q3tNegOne の IsZpUnit・q3t_negone_ne_one が choice-free（レベル 1 算術）であること
- [ ] 既存 TateCurve/TateTorsion/TateCover 系の正直申告が**一切消去・弱化されていない**こと
- [ ] header に §3.3・§4.3 の限定（群提示 ∃形・p=3・l=2・cuspidalization 0）が明記されていること
