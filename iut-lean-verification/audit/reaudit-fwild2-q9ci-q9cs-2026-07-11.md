# 独立敵対的再監査: F-wild #2 基盤 2 モジュール (q9ci + q9cs)

- 監査日: 2026-07-11
- 監査者: 独立敵対的監査（本コードを書いていない・既定スタンス=懐疑）
- 対象:
  - `IUT/Q3KummerCubeIdent.lean`（prefix `q9ci`・756 行・commit f194b0b）
  - `IUT/Q3KummerDescentSpike.lean`（prefix `q9cs`・558 行・commit 308cc84）
- 申告分類: 両者 **[実／本物の先行建設(b)] FOUNDATION・complete_pct 0 前進**
- 監査目的: (i) 真の REAL 先行建設か（§2/§3 の水増しでないか）・(ii) axiom-clean か・
  (iii) 二重計上でないか・(iv) 正直な 0 前進が正しいかの裁定。

---

## 0. 結論（先出し）

| 項目 | 判定 |
|---|---|
| q9ci が genuine real 先行建設か | **YES**（本物の恒等式＋正則性・toy 主語なし） |
| q9cs が genuine real 先行建設か | **YES**（忠実 Int 影の上の本物の降下簿記・toy 主語なし） |
| q9cs の Int 影の忠実性 | **忠実**（q3rqMul の D=−3 座標式と定義一致・下記 §2） |
| axiom-check（両モジュール主要対象） | **全て [propext, Quot.sound]**（Classical.choice/sorryAx 皆無） |
| 禁止タクティク | **なし**（sorry/simp/decide/ring/nlinarith 等は日本語コメント内のみ・omega は純 Int/Nat 線形のみ） |
| 二重計上（q3mc/q3rq リラベル・hollow capstone） | **なし**（新規対象・新規言明） |
| 台帳裁定 | **0 前進確定**（pillar A=54 据え置き・target_ledger.json 無改変） |

lake build: `lake build IUT.Q3KummerCubeIdent IUT.Q3KummerDescentSpike` → **EXIT 0 / no sorry**
（既存モジュールの unusedVariables 警告のみ・両新規ファイルに警告なし）。

---

## 1. 読んだもの（def 本体＋定理本体）

両ファイルとも署名だけでなく証明本体を全読。加えて依存元の実定義を精読:

- `IUT/Q3KummerCubic.lean`: `q3kMul`(:99)＝O_M=ℚ₃(ζ₉) のねじれ畳み込み乗法（Y³=ζ₃=d）・
  `q3kMul_0/_1/_2`(:108/113/118)＝rfl 展開・`q3kNormBase`(:682)＝a³+ζ₃b³+ζ₃²c³−3ζ₃abc・
  `q3k_M_eq`/`q3k_A_eq`(:59/62)＝q3rqMul/Add=環演算の rfl。
- `IUT/Q3RamifiedQuadratic.lean`: `q3rqMul`(:135)・`q3rqD=z3.neg q3rqThree`(:71)＝−3・
  `q3rqZeta`(:534)=(−h,h)・`q3rqLambda`(:726)=(0,1)・`q3rqThreeElt`(:729)=(3,0)。
- `IUT/Q3Mu3Completeness.lean`: `q3mc_three_mul_zero`(:239)・`q3mc_cube_snd`(:342)＝
  (a,b)³ の第2成分=3·((a²−b²)b)・`q3mc_mul_val1`(:382)。
- `IUT/Q3TateCuspidalization.lean`: `q3cu_ppow_dvd`(:126)＝素冪 Euclid 反復（euclid_int＋
  isPrime_three の n 段帰納）。
- `IUT/RootsOfUnity.lean`: `euclid_int`(:63)。

---

## 2. q9cs Int 影の忠実性検証（★ 最重点・不忠実なら spike は空虚）

実定義（Q3RamifiedQuadratic.lean:135–137）:

```
q3rqMul (x y) = ( z3.add (z3.mul x.1 y.1) (z3.mul q3rqD (z3.mul x.2 y.2)),
                  z3.add (z3.mul x.1 y.2) (z3.mul x.2 y.1) )
```

`q3rqD = z3.neg q3rqThree = −3`（:71）。したがって
- 第1座標 = x1·y1 + (−3)·(x2·y2) = **x1·y1 − 3·(x2·y2)**
- 第2座標 = x1·y2 + x2·y1

q9cs の影定義（Q3KummerDescentSpike.lean:175/178）:
- `q9csMulFst x1 x2 y1 y2 = x1 * y1 - 3 * (x2 * y2)` ← 第1座標と**完全一致（D=−3 符号正）**
- `q9csMulSnd x1 x2 y1 y2 = x1 * y2 + x2 * y1` ← 第2座標と**完全一致**

さらに影が飾りでなく本物に接着していることを、忠実性補題そのものが証明している:
- `q9cs_rq_mul_fst_valn`(:509): q3rqMul の第1座標のレベル n rep が q9csMulFst に等しい。
  `q9cs_D_valn`(D の rep=−3)を使い、`+(−3)·` と `−3·` の差を `Quot.sound`（差=3^n·0）で吸収。
- `q9cs_rq_mul_snd_valn`(:532): 第2座標=q9csMulSnd（定義一致・add/mul val-n 補題の合成）。
両者 axioms=[propext, Quot.sound]。**影は実 q3rqMul に rep レベルで実接着**。

**符号の敵対的検算**: もし D を +3 と取り違えていれば q9csMulFst の主要項 (a1²−3a2²) が
(a1²+3a2²) となり、単数 peel `q9cs_unit_peel`（3∤a1 ⟹ 3∤(a1²−3a2²)、euclid_int 経由）も
`q9cs_sq_fst_even/odd` の 3-content 計算も全て破綻する。実際の符号は −3 で一貫し、build 通過。
**⇒ 影は忠実。spike は空虚でない。**

なお正直限定 #4（d=ζ₃ を任意 Int 対 d1,d2 として抽象化）は忠実性を壊さない: 降下で d は
既に可除な因子への左乗（`q9cs_dvd_mull d1 …`）としてのみ現れ、主要項 (a1²−3a2²)·b1 に d は
不在。n∣x ⟹ n∣d·x は任意 d で成立するため、d 抽象化は 3-content 簿記の忠実な過剰近似。

---

## 3. q9ci 各成果の非空虚性検証

### A1 立方恒等式（q9ci_cube_0/_1/_2, :349/370/390）
主張は `(q3kMul (q3kMul x x) x).1 / .2.1 / .2.2 = 明示展開`。証明は `q3kMul_0/_1/_2` 
（実乗法の rfl 展開）で座標を開き、抽象 CRing 展開補題 `q9ci_cube0/1/2_raw` を q3rqRing に
specialize。raw 補題は分配律・結合律・可換律の実 rw 連鎖（:99–345）で、6ζ₃abc・3(…) を反復和で
honest に明示。**主語は実 q3kMul（O_M の元 x のねじれ立方）・vacuous でも fake でもない。**

### A2 正則性パック
- `q9ci_three_reg_L2`(:412): 各座標を `q3mc_three_mul_zero` に帰着（実）。
- `q9ci_nine_reg`(:431): 3 を 2 回・結合律。
- `q9ci_lambda_reg`(:441): λ(p,q)=(−3q,p)・第1成分=z.1・第2成分は 3 正則へ帰着。
- `q9ci_unit_reg_L2/_M`(:463/473): 逆元乗算（q3rqInv/q3kInv 消費）。
- `q9ci_zeta_norm3`(:483): (ζ₃²−1)(ζ₃−1)=3 を円分関係 1+ζ₃+ζ₃²=0（q3k_zeta_sum_zero）と
  実 rw で証明。
- `q9ci_zeta_sub_one_reg`(:512): 上を掛けて 3z=0 に帰着。
- `q9ci_cofactor_raw`(:586): (Y−1)(Y²+Y+1)=Y³−1 を実 CRing telescope（q9ci_tele:569）で証明。
- `q9ci_pi9_reg`(:602): cofactor で Y³−1=embed(ζ₃−1)（q3k_zeta9_cube）、embed(ζ₃−1) 正則
  （q9ci_embed_reg_M＋q9ci_zeta_sub_one_reg）へ帰着。**申告の帰着経路と一致・空虚でない。**

### A3 立方根なし（q9ci_no_cbrt_zeta/_zetaSq, :628/661）
`q3mc_cube_snd`（立方第2成分=3·(…)≡0 mod 3）と、ζ₃ の第2成分=q3rqHalf（単数・2 倍で 1）の
矛盾を、val-1 rep（q3mc_mul_val1）＋quot_exact＋omega で導出。3k≡half を 2 倍し 1≡6k≡0 mod 3 の
矛盾。**実 2 成分因数分解と実 rep を使う本物の議論・vacuous でない。**

### A4 ノルム整合（q9ci_norm_sub, :707）
`q3kNormBase x = (x³).1 − 9ζ₃abc` を、q9ci_cube_0（E0=a³+ζ₃b³+ζ₃²c³+6ζ₃abc）を rw し、
q3kThree·(ζ₃abc)=3·(ζ₃abc) 展開（q9ci_three_mul）＋加法相殺（q9ci_add_neg_cancel）で証明。
**q3kNormBase（実ノルム）と E0（実立方）の本物の整合。**

---

## 4. q9cs 降下の非空虚性検証（結論を仮定に隠していないか）

- `q9cs_unit_peel`(:129): 3^t∣(a1²−3a2²)·x, 3∤a1 ⟹ 3^t∣x。`q3cu_ppow_dvd`（実素冪 Euclid）＋
  `q9cs_unit_sq`（euclid_int）を実消費。load-bearing・非自明。
- `q9cs_descent_even`(:223): 仮定=k=2m 不変量(3^m∣b1,b2,c1,c2)＋3∤a1＋E1'/E2' 第1座標の
  mod 3^{m+1} 合同(hE1/hE2)。結論=3^{m+1}∣b1 ∧ 3^{m+1}∣c1。証明は主要項 (a1²−3a2²)·b1 以外の
  全単項式が 3^{m+1} を持つこと（平方 3-content 補題＋IH）を実 Int 可除計算で示し、`hE1' := hE1`
  で E1' の定義展開が hE1 と defeq であることを型検査に通し（＝申告の多項式が真に q9csE1fst の
  展開）、差の閉じた Int 恒等式（heq・omega）で主要項を抽出、unit_peel で締める。
  **hE 仮定は honest な降下不変量（本物では x³=1 の Y/Y² 成分方程式から出る・正直限定 #1 で
  明示）であり、結論 3^{m+1}∣b1 を偽装していない。** 仮定は充足可能（b=c=0 等）で空虚偽でない。
- `q9cs_descent_odd`(:330): 交互の「奇段」。主要項が第2座標 (a1²−3a2²)·b2/·c2 に移る。同構造。
- `q9cs_descent_all`(:435): 帰納 glue。base m=0（3^0=1・自明）、m=0→1 は奇段 m=0、
  m≥1→m+1 は偶段＋奇段合成。**Module B6 の帰納 glue の実証・re-export でない。**

---

## 5. 二重計上チェック

- **q9ci は q3mc/q3rq のリラベルでない**: q3mc は平方/level-3 の第2成分因数分解まで。q9ci は
  **立方**展開（E0/E1/E2・O_M=q3k 上）・正則性パック・立方根なし・ノルム整合＝次数 3 の新対象・
  新規言明。既存結果の束ね直し（hollow capstone）でない。
- **q9cs は q3mc の re-export でない**: q3mc は μ₃(level-3) 完全性。q9cs は level-9 の
  **同時 b,c パリティ降下**（新座標多項式 E1'/E2'・偶奇交互構造）＋忠実性橋。新規言明。
- 忠実性橋（q9cs_rq_mul_fst/snd_valn）が実 q3rqMul に接着＝spike は本物を主語にしている。

---

## 6. 台帳裁定（§5 準拠）

**どの tracked pillar-A 項目も本物には進めない**:

- q9ci は「何も kill しない」（正直限定 1）。恒等式＋正則性のみ。A4/A5/A6/A7 等の実対象
  （π₁^ét・tempered・mono-anabelian 復元・mono-theta 剛性）を構成しない。
- q9cs は Int 可除簿記であり **実 Galois コホモロジー（B6 の主語）を構成しない**。x³=1 の
  O_M 等式・Galois 作用は明示的に範囲外（正直限定 #1）。したがって B6（status 0・weight 10）を
  0.5 の「忠実な部分ケース」へ上げる資格はまだない（level-9 kill に CONSUMED されていない）。

§5「foundation は実 kill に CONSUMED されて初めて complete_pct 信用を得る」に照らし、
両モジュールは kill を消費されていない先行建設ゆえ **0 前進が正しい正直な帰結**（失敗でない）。
新規の加重台帳項目を捏造して foundation に信用を与えることは §5 で禁止・行わない。

**決定**:
- `target_ledger.json` を **無改変**。
- pillar A complete_pct を **54 据え置き**。
- `graph-meta.json` の pillar-A `complete_note` に F-wild #2 の着地（実・axiom-clean・0 前進）と、
  spike の de-risk 成果（B6 の残リスク=交互パリティ降下の Lean encode 物量が単段＋交互合成まで
  焼却・tier-L→tier-M へ格下げ・数学リスク消滅）を正直に追記。

検算: `python3 tools/compute_complete_pct.py` → `{"A": 54, "B": 18, "C": 41, "D": 18, "E": 42}`
（A=54 維持・graph-meta A=54 と整合）。

---

## 7. axiom-check 実出力（監査者が自ら実行）

```
'IUT.q9ci_cube_0'          depends on axioms: [propext, Quot.sound]
'IUT.q9ci_cube_1'          depends on axioms: [propext, Quot.sound]
'IUT.q9ci_cube_2'          depends on axioms: [propext, Quot.sound]
'IUT.q9ci_pi9_reg'         depends on axioms: [propext, Quot.sound]
'IUT.q9ci_no_cbrt_zeta'    depends on axioms: [propext, Quot.sound]
'IUT.q9ci_no_cbrt_zetaSq'  depends on axioms: [propext, Quot.sound]
'IUT.q9ci_norm_sub'        depends on axioms: [propext, Quot.sound]
'IUT.q9ci_three_reg_L2'    depends on axioms: [propext, Quot.sound]
'IUT.q9ci_zeta_norm3'      depends on axioms: [propext, Quot.sound]
'IUT.q9cs_descent_even'    depends on axioms: [propext, Quot.sound]
'IUT.q9cs_descent_odd'     depends on axioms: [propext, Quot.sound]
'IUT.q9cs_descent_all'     depends on axioms: [propext, Quot.sound]
'IUT.q9cs_unit_peel'       depends on axioms: [propext, Quot.sound]
'IUT.q9cs_rq_mul_fst_valn' depends on axioms: [propext, Quot.sound]
'IUT.q9cs_rq_mul_snd_valn' depends on axioms: [propext, Quot.sound]
```

禁止タクティク grep（両ファイル）: ヒットは日本語コメント内の宣言文（「sorry 皆無」
「禁止タクティク不使用」）のみ・コード本体に sorry/admit/simp/decide/by_cases/rcases/ring/
nlinarith なし。omega は純 Int/Nat 線形ゴール（heq 恒等式・可除 witness）にのみ使用＝許容。

## 8. 総合判定

両モジュールは **genuine REAL 先行建設(b)**・axiom-clean・忠実・二重計上なし。
§2/§3 の水増し（骨格/模型/代理を主語にした「完成」）に該当せず。§4 の正直限定は真実かつ完全。
kill を消費していないため **complete_pct 0 前進が正しい**（pillar A=54 据え置き・水増しでない）。
spike は Module B6 の残 tier-L リスク（降下の Lean encode 物量）を焼却し tier-M へ格下げ＝
後続 level-9 kill が表示を動かす消費入力を先に本物で建てた、健全な foundation ラウンド。
