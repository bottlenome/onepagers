# 独立再監査: A8 実 Tate 曲線 E_q(ℚ₃) — 退化 witness / 外部付値仮定の discharge 検証（2026-07-10）

**監査者**: 独立・敵対的監査者（親の自己申告を非共有・自走検証）
**対象**: 柱A A8「楕円曲線/Tate 曲線の実被覆・cuspidalization」（前回 status 0.5・weight 12）
**契機**: 今セッション新規実装 `IUT/Q3TateCurve.lean`（q3t・310 行）＋`IUT/Q3TateTorsion.lean`（q3tt・355 行）。
設計 `audit/A8-real-tate-curve-detail-2026-07-10.md` 見込み 0.5→0.6（上限 0.6）。

## 判定（結論）

**A8 status 0.5 → 0.57**（設計見込み 0.6 を敵対的に 0.03 ノッチ下・**0.6 を超えない**）。
**柱A%: 46 → 47**（Σ_A = 45.9 + (0.57−0.5)×12 = 46.74 → round 47・46.5 の不安定境界を回避）。

理由: 前回 0.5 の named 欠陥（存在 witness が q=1 の自明周期・torsion 位数と無限位数が外部付値仮定）を、
**実 q=3^m（実付値 v(q)=m≥1・実無限位数）・実 2 乗根 w=3・実位数ちょうど 2・Klein 4 群 ⊆ E₉[2]**
で本物・choice-free に discharge したことを自走検証で確認。§2(a) の昇格であり水増しでない。
ただし A8 title の cuspidalization は 0・cover 系は代理・Galois 作用皆無・μ₂ 完全性未・
単一 (p=3, l=2, q=3^m) 切片なので 0.6 の design cap には届かせない。

## 自走検証の証跡

### 1. フルビルド（自分の手で）
- `export PATH="/root/lean4/bin:$PATH"; bash build.sh` → **EXIT=0**・`OK: all theorems verified, no sorry.`
- `grep sorry/admit` は両ファイルの正直ヘッダ行（「sorry 皆無」の宣言）のみ・実体の sorry/admit 皆無。
- build.sh の #print axioms 一括に A8 対象（q3tCurve・q3t_q_pow_ne_one・q3t_point_ne_one・
  q3tt_w_order・q3tt_klein_closed・q3ttData）が含まれ全て `[propext, Quot.sound]`。

### 2. 独立 #print axioms（build.sh 掲載外も含む全 31 A8 対象を自分で列挙実行）
`lake env lean` で A8a 16 対象＋A8b 15 対象＝**31 対象すべて `[propext, Quot.sound]`**。
新規 Classical.choice 混入 **皆無**。特に監査重点の位数・klein・class 分離で choice が隠れていないこと:
- `q3t_q_pow_ne_one`（無限位数）・`q3tt_w_order`（位数 2）・`q3tt_class_eq_iff`（類分離）・
  `q3tt_klein_distinct`（4 点相異）・`q3tt_klein_closed`（積閉）・`q3tt_klein_torsion`（2-捻れ）
  すべて `[propext, Quot.sound]` を目視確認。omega/congrArg/Quot.sound のみで choice 不使用。

## 核心判定: 退化 witness / 外部付値仮定の discharge は本物か（見せかけの仮定置換でないか）

**本物である。** Lean 定義精読で以下を確認:

### (a) 実 Tate 曲線が本物（模型でない）
- `q3tGrp := QpUnits 3 isPrime_three = prodGrp intGrp (zpUnits 3 …)`＝担体 ℤ×ℤ₃^× の
  **成分ごと積の本物の Grp**（FundamentalGroup.lean:444 prodGrp・componentwise mul）。
- `q3uEmbed : (k,u) ↦ [3^k·u] : ℚ₃^× → q3Ring` は **実 ℚ₃ 内への単射乗法準同型**
  （`q3u_embed_hom`＋`q3u_embed_inj` を精読——inj は付値分離で第1成分 k を、3 冪正則性で
  第2成分 u を復元する実証明。q3Ring=ringLocRf z3 3＝実 ℤ₃[1/3]=実 ℚ₃・模型でない）。
- `q3tCurve m := quotientGroupN q3tGrp (q3tSubgroup m) …`＝M267F の**本物の商群機構**
  （quotientProjN_ker の普遍性=核ちょうど N まで本物）に実 ℚ₃^×・実 q=3^m を代入した実例。
  ⇒ **「実 ℚ₃^× を実 q^ℤ で割った本物の商群」であり toy 主語でない**。

### (b) 退化 witness q=1 の discharge が本物
- `q3fValRel`（Q3LocalField.lean:248）は**関数でなく関係**の忠実付値: x=mk(a,3ⁿ)∧z3vExact a v∧κ=v−n。
  well-defined（q3f_val_wd）・加法性（q3f_val_mul）を実証明済み。z3vExact（Zp3ValuationRing.lean:68）は
  「レベル n 成分 0 かつレベル n+1 成分≠0」の**真の厳密付値**（自明述語でない）。
- `q3t_q_val m : q3fValRel (q3uEmbed (q3tQ m)) m`＝v(3^m)=m を、`q3_pow_exact`（3^m の厳密付値=m・
  非空虚）と `q3u_unit_exact0`（単数の付値=0）の積で実証明。⇒ M309F の「正 valuation witness 未達」を
  **実 ℤ 値付値で discharge する初の実例**。
- `q3t_q_pow_ne_one m n (1≤m)(1≤n) : qⁿ≠1`＝tateNpow の第1成分 `q3t_npow_fst: (qⁿ).1 = m·n`
  （prodGrp 成分帰納）を使い **m·n≠0（omega）** のみで矛盾。**外部付値仮定を一切使わない群成分算術**。
  無限位数は free ℤ 成分（intGrp）から本物に出る。⇒ **見せかけでない実 discharge**。

### (c) 外部付値仮定（torsion 位数）の discharge が本物
- `q3tt_w_sq : (q3tQ 1)·(q3tQ 1) = q3tQ 2`＝w=3, w²=q=9 を第1成分 1+1=2・第2成分 1·1=1 の
  **成分算術で実証明**（体拡大なし・w=3 が ℚ₃ 内に実在）。M314F「w を witness で受け取る」を実 discharge。
- `q3tt_w_order k : [w]ᵏ=1 → 2∣k`＝射影核 `quotientProjN_ker`（本物の普遍性）で [w]ᵏ=1 を
  qⁿ∈q₉^ℤ へ還元し、第1成分 `2·t = 1·k`（q3t_zpow_fst/q3t_npow_fst）から **omega で 2∣k**。
  **付値 v を外部入力しない**——「ちょうど 2」は q₉=q3tQ 2 の第1成分 2 から実算術で出る。
  ⇒ M314F `tateTorQrootOrder` の外部付値入力を**実算術で置換した本物**。

## torsion / Klein が本物か

- `q3tt_w_sq`（w=3, w²=9 が ℚ₃ 内・体拡大なし）: 本物（上記 (c)）。
- `q3tt_w_order`（実位数ちょうど 2）: 本物（上記 (c)・choice-free）。
- `q3tt_klein_*`（Klein 4 群 {[1],[3],[−1],[−3]} ⊆ E₉[2]）:
  - `q3tt_class_eq_iff`＝[k,u]=[k',u'] ⟺ 2∣(k'−k)∧u=u'（付値方向×単数方向の直交）を
    射影核＋成分特徴付け `q3t_mem_pair_iff` で実証明。
  - `q3tt_klein_distinct`＝4 点相異（6 組）を class_eq_iff の否定＋`q3t_negone_ne_one`（−1≢1 mod 3・
    レベル1 剰余で実証明）で一様に。**4 点相異は本物**。
  - `q3tt_klein_closed`＝積閉（±1 の積は ±1・q3tNegOne_sq 使用）・`q3tt_klein_torsion`＝各点 2-捻れ。
  ⇒ Klein 4 群の**包含・相異・積閉・2-捻れすべて本物**。

## 過大主張検出（正直な限定の妥当性）

- **Klein は ⊆ のみ・= E₉[2] を主張していない**: grep で `= E₉[2]`/`完全`/`全体` の等式主張なし。
  header §3.3 point 3（q3tt）が「μ₂ の完全性（u²=1⟹u=±1）は stretch/後続・等号を主張しない・
  Klein は包含まで」と明記。**過大主張なし**。
- **cuspidalization は今回 0**: `grep -ric cuspidal IUT/*.lean` は q3t/q3tt の**正直な限定行（「皆無」宣言）
  各 1 件のみ**でモジュール実体は皆無。A8 title に含むが未達を確認。
- **Weierstrass 未接続**: grep で q3t/q3tt の Weierstrass 言及は「皆無」の限定行のみ。
- 担体は群提示 3^ℤ×ℤ₃^×（∃形・total inv 不可・{x:ℚ₃//x≠0} literal 商でない）: header 明記・A2 継承の恒久限定。
- p=3 固定・q∈3^ℤ・l=2 のみ・T_l/幾何 Tate 加群 未接続・cover 系代理のまま: すべて header 明記で過大主張なし。

## 残る限定（0.6 を超えない理由・0.57 に留める理由）

1. **cuspidalization = 0**（A8 title の半分・モジュール皆無）。
2. **real cover = 代理のまま**（TateCover 系 M188F/191F/195F/200F/206F は surrogate π₁・実 E_q と未接続）。
3. **Galois 作用皆無**（G_{ℚ₃} の E_q[n] 作用なし・実 G_{ℚ₃} は A2 後続）。
4. **μ₂ 完全性未証明**（Klein は ⊆ のみ・2-torsion 構造も完全決定でない）。
5. **単一切片**（p=3・l=2・q=3^m・u₀=1）・幾何 Tate 加群 T_l 未接続・Weierstrass 未接続。

→ named 欠陥 2 件の discharge は 100% 本物で **据え置き（0.5）は過小**だが、A8 の広い残欠
（cuspidalization・cover・Galois・完全 torsion・一般 p/l）を踏まえ **design cap 0.6 に 0.03 の margin**
を残す。0.55 は Σ=46.5 で banker's rounding が 46 に落ち genuine promotion を柱%に反映しないため不採。

## complete_pct への反映

- `target_ledger.json`: A8 status 0.5 → **0.57**。`_current_numerator` に本ラウンドの dated entry を追記。
- `tools/compute_complete_pct.py` 自走 → 柱A = **47**（B18/C41/D18/E42 不変）。
- `graph-meta.json`: pillars.A.complete_pct 46 → **47**・complete_note の A8「退化」記述を実態へ更新・_last_round 更新。
- `tools/gen_graph.py` → graph.json 再生成。
- `dashboard.md` 二軸表の柱A% 46→47 同期。

## 丸めの扱い（正直に）

Σ_A(w·s) = 45.9 → **46.74**（A8 +0.84）。`round()`（banker's）で **47**。
0.55 だと Σ=46.5→round 46（banker's で 46 に落ちる不安定境界）ゆえ genuine promotion が柱%に出ない。
0.57 は Σ=46.74 で 46.5 境界から安全側・47 へクリーンに繰り上がる。0.6/0.57 いずれも柱% 47（クロス/非クロスが唯一のレバー）。
本物の discharge ゆえクロスさせるのが正直、cap 未達ゆえ 0.57 に留める。
