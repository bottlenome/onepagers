# 独立敵対的再監査: kill#1 foundation — q9ps 実 wild 分割要石 + q9yp Y-冪パック — 2026-07-11

**監査者**: 独立敵対的監査（コードを書いていない・既定 SKEPTICAL）。
**対象**:
1. `IUT/Q3KummerPiSplit.lean`（prefix `q9ps`・527 行・commit 7d09ec7）— wild 分割恒等式 **3 = π₉⁶·u₆**（実 M=q3k 上）・level-9 テータ kill の [実] 分類要石。
2. `IUT/Q3KummerYPow.lean`（prefix `q9yp`・275 行・commit 1e9936d）— Y-冪（ζ₉-冪）単項式正規形パック＋位数ちょうど 9 補助。
両者 **[実／本物の先行建設(b)] FOUNDATION・complete_pct 0前進**を申告。

**判定要旨（先出し）**:
- **q9ps [実] 検証（本監査の核心）: [実] STANDS（PASS）**。3 = π₉⁶·u₆ は**証明**されており**posit されていない**。§2.2 の警告「3:=(6,任意単数) と置くと模型＝[実] 剥奪」の該当なし。
- **q9yp: 真正（PASS）**。Yᵏ は実 q3kMul で計算・Yᵏ≠1 は非空虚。
- **axiom: 全対象 [propext, Quot.sound] のみ**。禁止タクティクなし。
- **二重計上なし**。q9ps/q9yp は既存（q3k/q9ci）の再ラベルでない。
- **台帳判定: 0前進確定**。target_ledger.json 不変・A=54 据え置き。compute_complete_pct.py 出力 `{"A":54,...}` 再確認済み。

---

## 1. q9ps 実 wild 分割検証（★ 本監査の crux — 証明か posit か）

§2.2 （`audit/level9-theta-kill-detail-2026-07-11.md`）は明示的に警告する:
> これを省略して 3:=(6,任意単数) と置くと提示は抽象群の再ラベル＝模型であり、敵対的監査は [実] を剥奪する。

すなわち本監査の唯一最重要の問いは: **q9ps は 3=π₉⁶·u₆ を実恒等式から導いているか、それとも u₆ を自由パラメータとして posit しているか**。4 点を .lean 本体の読解で確認した。

### 1.1 `q9ps_pi9_cube`: (Y−1)³ = λ·w は実計算（PASS）

- `q9psPi9 := q3kAdd q3kZeta9 (q3kNeg q3kOne)`（=Y−1・座標 (−1,1,0)・`q9ps_pi9_coords` で座標確定）。
- 証明本体（219–307 行）は `q3k_ext` で 3 座標に分解し、各座標で**汎用の立方展開補題** `q9ci_cube_0/1/2 (x)` を x=(−1,1,0) に実適用する。q9ci_cube_0/1/2（`Q3KummerCubeIdent.lean` 349–394 行）は `(q3kMul (q3kMul x x) x).i = [a³+ζb³+ζ²c³+6ζabc 型の座標多項式]` を**任意 x で**成り立つ実定理（axiom でない）。
- 各座標で `q9ps_neg1_cube`・`q9ps_c0b/c0c/c0t6`・`q9ps_S1`・`q9ps_S2`・`q9ps_coord0`・`q9ps_lamsq'`・`q9ps_three_eq` 等の実 q3rq 成分補題に還元。coord1 で λ²=−3（`q9ps_lamsq'`）＋S₁=1 から 3、coord2 で −3、coord0 で λ(ζ₃+1)=ζ₃−1。**代入・座標計算のみで posit なし**。
- RHS は `q3kMul (q3kEmbed q3rqLambda) q9psW`。w=q9psW は座標 (ζ₃+1,−λ,λ) の**明示的な実元**（自由記号でない）。

### 1.2 `q9ps_w_norm`: N(w) = −1 は実ノルム定義から計算（PASS）

- `q3kNormBase`（`Q3KummerCubic.lean` 682–686 行）は**本物の 3 次ノルム多項式** N=a³+ζ₃b³+ζ₃²c³−3ζ₃abc（assert でない）。さらに `q3k_norm_eq`（810 行）が N(x)=x·σx·σ²x=embed(N) を実 Galois 共役積として証明済み＝ノルムは飾りでなく実共役ノルム。
- `q9ps_w_norm`（312–363 行）は q3kNormBase q9psW を w=(ζ₃+1,−λ,λ) で全展開し、hA:(ζ₃+1)³=−1・hBC:ζ(−λ)³+ζ²λ³=−(3·3)・hD:3ζ(ζ₃+1)(−λ)λ=−(3·3) の 3 実補題で組む。算術 N=−1+(−9)−(−9)=**−1**（検算一致）。**assert でなく実計算**。
- −1 が真の ℤ₃-単数: `q9ps_norm_neg_one`（q3rqNorm(−1)=1 の実 z3 計算）＋`q9ps_w_unit`（IsZpUnit 3 1・witness ⟨1,rfl,not_dvd_one⟩）。w は実単数として確定。

### 1.3 u₆ = −(w⁻¹)² は実閉形式（自由パラメータでない）（PASS）

- `q9psWinv := q3kInv q9psW q9ps_w_unit`。`q3kInv`（869–870 行）は**閉形式** (σx·σ²x)·N⁻¹＝共役ノルム逆元。単数証明 hx を要求し、自由記号でない。`q3k_inv_mul`（872 行）が w·w⁻¹=1 を q3k_norm_eq 経由で実証明。
- `q9psU6 := q3kNeg (q3kMul q9psWinv q9psWinv)` = −(w⁻¹)²。`q9ps_u6_unit` で実単数性を継承。**u₆ は本物の構成物**。

### 1.4 `q9ps_three_eq_pi6_u6` / `q9ps_three_split`: 3_M=π₉⁶·u₆ は実恒等式（posit でない）（PASS — [実] 生命線）

- 主張は `q3kMul q9psPi6 q9psU6 = q3kEmbed q3rqThreeElt`。**右辺 3_M は q3kEmbed(q3rqThreeElt)＝実基底元 3=(3,0) の埋め込み (3,0,0)**（`q3rqThreeElt` 定義 729 行・`q3kEmbed` 689 行）。**posit された組 (6,u₆) ではない**。
- 証明本体（467–484 行）は:
  1. `q9ps_pi9_cube` で両 π₉³ 因子を λ·w に書き換え。
  2. `mul_mul_mul_comm` で (λw)(λw) を (λλ)(ww) に並べ替え、`mul_neg`。
  3. 再び並べ替えて (ww)(w⁻¹w⁻¹) を作り、`hwinv:w·w⁻¹=1`（`q9ps_w_inv_mul`）で 1 に消去。
  4. 残る −(embed λ·embed λ) を `q9ps_LL`（=q3k_embed_mul）で −embed(λ²)、`q9ps_embed_neg` で embed(−λ²)、最後に `q3rq_three_eq_neg_lambda_sq`（3=−λ²・実証明 744 行）で embed(3) に到達。
- すなわち 3_M = π₉⁶·u₆ は **(Y−1)³=λw・w·w⁻¹=1・3=−λ² の 3 実補題から機械的に導出**される。**u₆ を自由に置いて 3 と定義する posit は一切ない**。

**結論（q9ps [実]）**: §2.2 の模型化警告に**該当しない**。u₆ は −(w⁻¹)² の実閉形式単数、3_M は実基底 3 の埋め込み、恒等式は実補題からの導出。**[実／本物の先行建設(b)] 分類は維持（STANDS）**。[実] 剥奪の必要なし・§3 違反なし。

---

## 2. q9yp 検証（PASS）

- **Yᵏ は実 q3kMul で計算**: `q9ypY2 := q3kMul q3kZeta9 q3kZeta9`… `q9ypY8 := q3kMul q9ypY7 q3kZeta9`（左結合連鎖・fake でない）。
- **単項式正規形は実還元**: `q9yp_y2`=q3k_zeta9_sq（実座標計算 931 行）・`q9yp_y4/y5/y7/y8` は「·Y」1 段ヘルパ `q9yp_mulY_100/010/001`（各 q3k_ext で座標証明）に還元・`q9yp_y3`=q3k_zeta9_cube（Y³=embed ζ₃）・`q9yp_y6`=embed ζ₃²。
- **位数ちょうど 9 補助 Yᵏ≠1 は非空虚**: k∈{1,2,4,5,7,8} は非零スロット矛盾（congrArg で成分抽出→q3rq_half_ne_zero 等の実不等号）、k=3,6 は embed 単射（q3k_embed_inj）＋ζ₃/ζ₃²≠1（q3rq_zeta_ne_one/q3rq_zeta_sq_ne_one）。**vacuous でない実証明**。

---

## 3. axiom 出力（PASS）

`lake env lean` で以下を実行（全対象・IUT namespace）:

```
'IUT.q9ps_pi9_cube'        : [propext, Quot.sound]
'IUT.q9ps_w_norm'          : [propext, Quot.sound]
'IUT.q9ps_three_eq_pi6_u6' : [propext, Quot.sound]
'IUT.q9ps_three_split'     : [propext, Quot.sound]
'IUT.q9ps_u6_unit'         : [propext, Quot.sound]
'IUT.q9ps_exists'          : [propext, Quot.sound]
'IUT.q9ps_w_unit'          : [propext, Quot.sound]
'IUT.q9yp_y4'              : [propext, Quot.sound]
'IUT.q9yp_y6'              : [propext, Quot.sound]
'IUT.q9yp_y3_ne_one'       : [propext, Quot.sound]
'IUT.q9yp_y6_ne_one'       : [propext, Quot.sound]
'IUT.q9yp_exists'          : [propext, Quot.sound]
'IUT.q9yp_y2_ne_one'       : [propext, Quot.sound]
```

**全対象ちょうど [propext, Quot.sound]**。sorryAx なし・新規 Classical.choice なし。
`lake build IUT.Q3KummerPiSplit IUT.Q3KummerYPow` EXIT=0。
禁止タクティク grep（sorry/admit/simp/decide/by_cases/rcases/ring/nlinarith）: **ヒットは日本語コメント「sorry 皆無」のみ**＝コード本体に禁止タクティクなし（omega は q9ps_w_unit/neg_one_unit の純 Nat `not_dvd_one 3 (by omega)` のみ・OK）。

---

## 4. 二重計上チェック（PASS）

- `q9ps_three_split`/`q9ps_pi9_cube` は **Q3KummerPiSplit.lean のみ**に出現（他ファイル 0）。wild 分割恒等式 3=π₉⁶·u₆ は q3k/q9ci に存在しない新規内容。q9ci_cube_0/1/2 は**汎用の立方展開補題として消費のみ**（q9ps が再証明していない）。
- `def q9ypY*`/`q9yp_y4_ne_one` は **Q3KummerYPow.lean のみ**に出現。Y-冪単項式正規形は新規（q3k_zeta9_sq/cube を消費して連鎖を延長）。
- 主語は実 q3kCar（6 ℤ₃ 座標・O_M）・q3rq 係数の実 3 次代数。m202fVol 型・Bool 軌道・surrogate 群を**一切使用せず**（toy 主語なし）。**hollow capstone でない**（q9ps_data/q9yp_data は実定理の束ね）。

---

## 5. 台帳判定（0前進・A=54 据え置き）

- q9ps/q9yp は **foundation であり、実 kill に消費されていない**。level-9 kill 本体（q9mt テータ群 / q9mr 剛性 / q9mb 橋）は**未建設**（`IUT/Q3Mu9{Theta,Rigidity,TmzBridge}*.lean` 不在）。§5「foundation は実 kill に CONSUMED されて初めて信用・表示 mover は橋 q9mb」に従い、本 2 モジュールは complete_pct を動かさない。
- `target_ledger.json` の A 項目（A1–A9）は μ₉ wild 分割 / Y-冪を追跡せず、本物化しない。**status 変更なし・target_ledger.json 不変**。
- `python3 tools/compute_complete_pct.py` → **`{"A": 54, "B": 18, "C": 41, "D": 18, "E": 42}`**（A=54 据え置き再確認）。
- graph-meta.json pillar-A `complete_pct=54` 不変。**`complete_note` に本監査の結果（kill#1 が real+axiom-clean で 0前進・q9ps [実] は genuine splitting で維持）を追記のみ**（消去・弱化なし）。

**過大主張なし**。本ラウンドは「complete_pct 0前進（骨格でなく本物基盤の先行建設・実 kill 未消費）」。

---

## 判定 3 行（親向け）

- **q9ps**: genuine wild splitting → **[実] STANDS（YES）**。3=π₉⁶·u₆ は (Y−1)³=λw・N(w)=−1・w·w⁻¹=1・3=−λ² の実補題から**導出**、u₆=−(w⁻¹)² は実閉形式単数、3_M=q3kEmbed(3) は実基底埋め込み。posit でない・§2.2 模型化なし・§3 違反なし。
- **q9yp**: genuine（**YES**）。Yᵏ 実 q3kMul・Yᵏ≠1 非空虚。
- **台帳**: **0前進**。target_ledger.json 不変・A=54・compute_complete_pct.py `{"A":54,...}` 再確認・graph-meta A=54 不変（complete_note 追記のみ）。

---
*監査手法: 全て対象 .lean の def/theorem 本体読解による。読解対象: Q3KummerPiSplit.lean 全 527 行・Q3KummerYPow.lean 全 275 行・Q3KummerCubic.lean（q3kNormBase 682/q3kEmbed 689/q3k_norm_eq 810/q3kInv 869/q3k_inv_mul 872/q3k_embed_mul 818/q3kZeta9 929/q3k_zeta9_sq 931 本体）・Q3RamifiedQuadratic.lean（q3rqLambda 726/q3rqThreeElt 729/q3rq_lambda_sq 732/q3rq_three_eq_neg_lambda_sq 744 本体）・Q3KummerCubeIdent.lean（q9ci_cube_0/1/2 349–394）・audit/level9-theta-kill-detail-2026-07-11.md §2.2・target_ledger.json 全文・tools/compute_complete_pct.py 全文。axiom は lake env lean で実測・compute は python3 実測。*
