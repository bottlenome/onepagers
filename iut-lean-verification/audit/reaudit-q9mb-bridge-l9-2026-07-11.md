# 独立敵対的再監査: level-9 比較橋 Q3Mu9TmzBridge（q9mb）— 2026-07-11

**監査者**: 独立敵対的監査（本コードを書いていない・既定 SKEPTICAL）。
**対象**: `IUT/Q3Mu9TmzBridge.lean`（prefix `q9mb`・650 行・commit 7d2850b）。
**位置づけ**: level-9 テータ kill キャンペーン（q9ps→q9tl→q9mt→q9mr→q9mb）の **consumer=display-mover**。
直前 5 モジュールの kill 連鎖は unconsumed foundation として **0前進で正しく保持**されていたが、
本橋 q9mb がそれらを消費して firewall（テータ側 q9mr/q9mt/q3k ↔ 円分側 tmz/tmi/cgar）を越え、
tmi の実 ℤ₃^×=`zpsLimit` の (ℤ/9)^× 商を殺す。**ゆえに本監査が now-consumed 連鎖を纏めて計上し s_A7 を SET する。**
**方法**: def/theorem 本体の読解＋`lake build`＋`#print axioms` 自己列挙＋grep＋compute_complete_pct.py 実測。

---

## Part 1 — 正確性検証（先に厳密に）

### 1. `q9mb_kill_mod9` は非空虚に (u.val 1).val=1 を強制する — ✅ YES

- 主語 `u : zpsLimit.carrier` は **実 ℤ₃^×**（`tmiFromUnits` が実作用する同一 `zpsLimit`）。level-1 成分 `(u.val 1)` は (ℤ/9)^× の実元（`.property.1: <9`）。
- 仮説 `hHom/hMem/hE9` は q9mr theta-両立剛性の genuine 条件（`q9mr_cyclotome_fixed` と同一シグネチャ）。`hreal` は「橋輸送で `tmiFromUnits u` を内部 μ₉ 上に実現」する実現条件。
- **非空虚性の裏取り**: `q9mb_admissible_iff`（531–551）の前方向が、u₁=1 のとき **φ=id** を明示構成し hHom(rfl)/hMem/hE9(rfl)/hreal を全て充足する（`hid: ((tmiFromUnits u).map t).val 1 = t.val 1` を `q9mb_level1`＋u₁=1 の pow-by-1 で証明）。すなわち仮説集合は u₁=1 でちょうど充足可能＝**真の二分（vacuous ∀ でない）**。
- **forcing の中身**（504–525）: `t=tmeZetaLim`（明示 choice-free witness）で `hreal` を評価。`q9mb_int_zeta` で左辺の被作用対象が `q9mr_zeta9`（=ζ₉⁻¹・原始 9 乗根）になり、`q9mr_cyclotome_fixed φ … = q9mr_zeta9`（剛性消費）で左辺固定。右辺は `q9mb_transport` で `(ζ₉U⁻¹)^{u₁}`（`.1.1.2` 成分抽出）。`inv` を噛ませて `ζ₉U = (ζ₉U)^{u₁}`、`q9mb_pow_one` で `(ζ₉U)^1 = (ζ₉U)^{u₁}`、**ζ₉U 位数ちょうど 9 の単射性 `q9mb_pow_inj`（1<9, u₁<9）** で `1 = u₁`。循環なし・剛性は本物の消費点。
- `q9mr_cyclotome_fixed`（Q3Mu9Rigidity.lean:305）を精読: `q9mr_rigidity` を交換子生成元 g₃, g_ζ に適用し `q9mr_zeta_eq_comm` で書換えた genuine な帰結（honest 仮説でない）。
- **判定**: 非空虚・非循環・剛性を本物消費。u₁=1 の真の dichotomy。**YES**。

### 2. σU 同変は genuine な新規内容（level-3 の再ラベルでない） — ✅ YES

- `q9mb_normBase_sigma`（362）: N(σx)=N(x) を `q3k_norm_eq`（N=x·σx·σ²x）＋`q3k_sigma3_id`（σ³=id）＋可換再配列で実証明（`q3k_embed_inj` 経由・Bool/Fin ラベルでなく実 O_M の実ノルム保存）。これが `q9mbSigmaU`（372）を well-defined にする生命線。
- `q9mb_equivariant_sigmaU`（429）: β₉(σ₄y)=σU(β₉y)。`q9mb_equivariant`（χ 冪）＋`q9mb_sigma4_exp`（χ(σ₄)=4）で右辺を `(ζ₉U^{find y})^4` にし、`q9mb_sigmaU_pow`＋`q9mb_sigmaU_zeta`（σU(ζ₉U)=ζ₉U⁴＝`q9mr_sigma_zeta9` 消費）で σU 側と一致。
- **level-3 との対比**: q3mb の `q3mb_equivariant_conj` は反転共役（ζ₃↦ζ₃²・位数 2・μ₃ 上非恒等）。σU=`q3kSigma` の単数群化は Y↦ζ₃Y・**位数 3**・μ₃ 対角を各点固定・ζ₉↦ζ₉⁴。すなわち **level-3 では μ₃ 上恒等ゆえ不可視だった NEW な位数 3 自己同型**であり、再ラベルでない。新層 ker(Aut(μ₉)→Aut(μ₃)) の局所大域突き合わせ。
- **判定**: **YES**（genuinely new・q9mr_aut_mu9_new_layer と整合）。

### 3. `q9mb_kill_new_layer` は {4,7}=(1+3ℤ₃)/(1+9ℤ₃) を機械可読に同定・過大主張なし — ✅ YES

- `q9mb_new_layer_chars`（558）: 4,7 は共に mod3=1・<9・¬3∣・≠1＝**核 ker(Aut(μ₉)→Aut(μ₃)) の非自明元**＝((1+3ℤ₃)/(1+9ℤ₃))∖{1}。
- `q9mb_kill_new_layer`（570）: kill の帰結 (u.val 1).val=1 の下で `≠4 ∧ ≠7`。定理文と Lean コメントが「**増分は核層 {4,7} のみ**・(ℤ/9)^× 全体でも 1+9ℤ₃（n≥3 層）でもない——これらは依然 SURVIVES（正直限定 5）」と明示＝過大主張なし。

### 4. firewall / consumption は real — ✅ YES

- β₉=`q9mbHom`（211）: `Hom (tmzG 1) q3kU`。`tmzG 1 = cmrGrp 2` は実 ℚ(ζ₉)=cteField 2 内の実 μ₉。写像は `q3kU.pow q9tlZeta9U (ctmFind 2 …)`（choice-free 離散対数）。map_mul は `tmz_mul_find 2`＋ζ₉U⁹=1。
- `q9mb_onto_mu9`（311）は `q9c_mu9_complete`（Q3Mu9Completeness.lean:1311・実 9 分類・塔分解＋Y-捻り）を 9 分岐 Or で消費。
- `tmiFromUnits`（TateModuleIndeterminacy.lean:227）を精読: 実 ℤ₃^× の各成分 (u.val n).val を指数とする成分冪 `tmiPowHom`＝実 Aut(ℤ₃(1))。level-1 成分は `(cmrGrp 2).pow (t.val 1) (u.val 1).val`（`q9mb_level1` が rfl）＝surrogate でない実対象。

### 5. 軸チェック — ✅ CLEAN

`lake build IUT.Q3Mu9TmzBridge` EXIT=0。監査者が `lake env lean` で列挙:

```
q9mbHom, q9mb_equivariant_sigmaU, q9mb_normBase_sigma, q9mb_kill_mod9,
q9mb_kill_new_layer, q9mb_admissible_iff, q9mb_onto_mu9, q9mb_transport, q9mb_exists
  → 全て [propext, Quot.sound]
```

禁止タクティク grep（simp/decide/by_cases/rcases/ring/nlinarith/sorry/admit）: **コード本体ヒット 0**（唯一の "sorry" ヒットはヘッダ日本語コメント「sorry 皆無」）。omega 98 箇所は純 Int/Nat（付値・指数・剰余）で許容。

### 6. q3mb（level-3 橋）との二重計上なし — ✅ YES

- q3mb は `(u.val 0).val=1`（index 0=mod-3 層・主語 `q3rqU`・`q3m3Car`）を殺す。q9mb は `(u.val 1).val=1`（index 1=mod-9 層・主語 `q3kU`・`q9mtCar`）を殺す＝**異なる層・異なる主語・異なる消費完全性（q3mc vs q9c）**。
- tmi の ℤ₃^× 特徴付け（`tmiFromUnits`）は消費のみ・再証明ゼロ。(ℤ/9)^× kill が (ℤ/3)^× kill を論理的に含む点は増分として主張されていない（コメントで明示）。

**Part 1 総合判定**: kill_mod9 非空虚 = **YES**、σU genuine = **YES**、firewall real = **YES**、axioms clean = **YES**、二重計上なし = **YES**。

---

## Part 2 — s_A7 の決定（本監査の metric SET）

### 2.1 算術（compute_complete_pct.py・round-half-to-even・実測）

柱 A の総重量はちょうど 100 ゆえ **Σ_A(%) = 47.62 + 12·s_A7**（A7 以外の Σ(w·s)=47.62・A7 weight=12）。

| s_A7 | Σ_A | 表示（round-half-even） |
|---|---|---|
| 0.49（旧） | 53.50 | 54 |
| 0.54 | 54.10 | 54 |
| 0.56（**採用**） | **54.34** | **54** |
| 0.57 | 54.46 | 54 |
| 0.573 | 54.496 | 54 |
| **0.574** | **54.508** | **55** |
| 0.58 | 54.58 | 55 |

**表示 55 の閾値 = s_A7 ≥ 0.574**（Σ>54.5・厳密には s>0.5733・54.5 ちょうどは偶数側 54 に落ちる）。

### 2.2 上げ要因（upward pressure）

1. **pro-3 bulk 1+3ℤ₃ への初の一咬み**。level-3 の正直限定が「1+3ℤ₃ はまるごと SURVIVES」と宣言した (1+3ℤ₃)/(1+9ℤ₃) 層を初めて剥がす。level-3 が殺したのは素数-to-3 の ℤ/2 成分＝算術的に易しい側であり、pro-3 側は IUT の本丸。**質的フロンティア越え**。
2. **genuinely new mathematics の消費**: μ₉ 完全性 `q9c_mu9_complete`（実 9 分類・クローンでない実定理）・wild 分割 3=π₉⁶·u₆・実テータ交換子からの初の原始 9 乗根 Weil 値 ζ₉⁻¹。
3. **σU 局所大域同変**（level-3 に無い NEW な位数 3 自己同型）・**機構→対象昇格**（tmi の実 (ℤ/9)^× 商へ輸送・level-3 橋の precedent と同型の upgrade）。

### 2.3 下げ要因（downward pressure・0.574 未達で cap する）

1. **殺すのは第 1 層 {4,7} のみ**。n≥3（1+9ℤ₃ の全層）は SURVIVES＝可算無限塔の 1 graded piece。mod-9 層のみで塔/極限（F-wild (v)）でない。
2. **kill 機構の約 8 割が level-3 テンプレのクローン**（q9mt/q9mr の E[9] 決定性・endo 剛性・cyclotome 固定は定数替え）。
3. 忠実部分ケースの 2 乗（q=3⁹・[EtTh] q^{1/l} でない）・**endo 定式化**・実テータ関数/π₁/G_{ℚ₃} ゼロ。
4. 群レベル同定（Aut(μ₉)=位数 6 曖昧）・**u₁=1 強制は「level-9 テータ両立クラス」相対**・tmi の残存 full-ℤ₃^× 宣言は不変更。

### 2.4 決定: **s_A7 = 0.56 ⟹ 表示 54（据え置き）**

**justification**: level-3 kill+橋の全キャンペーンが 0.42→0.49（**+0.07**）だった precedent と同規模の **+0.07（0.49→0.56）** を採る。
- 同規模を正当化する根拠: pro-3 初咬みの質的前進＋新数学（q9c/u₆/原始 9 乗根）の消費＋σU 新規＋機構→対象昇格。単なる「橋イディオムの 2 回目」に留まらない実質を持つ。
- precedent を**超えさせない**根拠: 機構の 8 割クローン・単層・endo・G_{ℚ₃} 不在・tmi 残存宣言不変更は level-3 と同じく効く cap。表示 55（s≥0.574）は **全 level-3 キャンペーンの純増（+0.07）を上回る +0.084 超**を要し、8 割クローン campaign では正当化不能。

0.55/0.57 も表示 54 で不変だが、全連鎖 landing の質（全 9 対象 clean・非空虚 kill・σU 新規・firewall real）を過小評価せず、設計 forecast の中央 0.55–0.56 の上側 **0.56** を採る。
- **0.58 に inflate しない**（campaign を「55 達成＝成功」に見せるため数字を作らない）。
- **0.54 に deflate もしない**（merit で決定・pro-3 初咬みと新数学消費は過小評価しない）。

これは設計文書 `audit/level9-theta-kill-detail-2026-07-11.md` §5 の中央推定「0.55–0.56 ⟹ 表示 54 据え置き（55 到達は上振れ側・本キャンペーン単独では確率半々未満）」と一致する **honest な central case**。表示 54 は失敗ではなく forecast の中央結果。

### 2.5 台帳・メタ整合

- `target_ledger.json` A7 status: 0.49 → **0.56**、`_current_numerator` に本決定を追記。
- `compute_complete_pct.py` 出力: `{"A": 54, "B": 18, "C": 41, "D": 18, "E": 42}`。
- `graph-meta.json` pillars.A.complete_pct = **54**（= compute 出力の A・整合確認済）、`complete_note` に本決定を追記。
- **柱A%は 54 据え置き**（status は 0.49→0.56 と前進するが表示は横這い・正直に明記）。

---

## 結論（3 行）

- **Part 1**: kill_mod9 非空虚=YES・σU genuine=YES・firewall real=YES・axioms=[propext,Quot.sound] clean・二重計上なし。正確性に refute 事由なし。
- **Part 2**: **s_A7 = 0.56 ⟹ 表示 54（据え置き）**。上げ=pro-3 初咬み＋新数学(q9c/u₆/ζ₉⁻¹)消費＋σU 新規；下げ=単層{4,7}のみ(1+9ℤ₃全層 SURVIVES)＋8割クローン＋endo/G_{ℚ₃}不在。0.574 未達。
- 表示 54 は honest な central case（設計 forecast と一致）。inflate も deflate もせず merit で決定。
