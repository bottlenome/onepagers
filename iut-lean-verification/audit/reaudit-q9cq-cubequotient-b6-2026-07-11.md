# 独立敵対監査: Q3CubeQuotientReal（q9cq）— 柱B B6 深掘り（実局所体立方剰余群 rank≥2 下界）2026-07-11

**監査人**: 独立敵対監査（本コードを書いていない・default SKEPTICAL）
**対象**: `IUT/Q3CubeQuotientReal.lean`（prefix `q9cq`・217 行・commit **8e860dd**）
**申告分類**: **[実／(a) 昇格]**・forecast B6 0.15→0.20
**前提**: 柱B 表示 26（厳密 Σ_B=26.5→banker's 26）。B6 weight=10・現 status 0.15（q9kd の ⟨[ζ₃]⟩ rank≥1 由来）。
**姿勢**: 全ての格上げは実 .lean 証明本体から正当化する。過大主張は FLAG する。**現在 Σ_B が 26.5＝.5 下丸め位置にあり任意の正の増分で表示が 27 へ動く不安定境界のため、「表示を動かすために status を与える」ことを厳に避け、merit のみで s_B6 を決める。**

---

## TL;DR（監査判定）

| 検査 | 結果 |
|---|---|
| 真水 genuine 且つ非空虚か | **YES** — [λ] 付値クラス非立方＋独立性組立は実担体上の実言明で非空虚 |
| 非立方の核は消費（再証明せず）か | **YES** — ζ₃ は q9kd_class_nontrivial、ζ₃² は q9ci_no_cbrt_zetaSq を消費 |
| ★rank-4 過大主張なしか | **YES** — 定理化は rank≥2 下界のみ・(ℤ/3)⁴/|81| はコメント・商群オブジェクト未建設 |
| 軸 [propext,Quot.sound] か | **静的 YES**（本環境 lean 未導入・#print axioms 実行不能→静的検査で choice-free 確認） |
| 二重計上なしか | **YES** — q9kd（rank≥1・付値/独立性なし）・抽象 Kummer（別主語）と非重複 |
| **s_B6 決定** | **0.18**（forecast 0.20 を 1 ノッチ下げ・薄い真水を敵対的に反映） |
| **表示** | **26 → 27**（Σ_B=26.8→round 27） |

---

## 1. 真水（genuinely new）の実在性・非空虚性 — 【YES】

本モジュールの新規主張は **付値方向 [λ] の非立方性 ＋ [λ]/[ζ₃] の 𝔽₃-独立性の組み立てのみ**（ヘッダ L19-20 の自己申告と一致・非立方の核は消費）。

### 1.1 `q9cq_cube_fst`（L61-64）— 成分立方の付値補題
`(q3rqLx.mul (q3rqLx.mul g g) g).1 = 3 * g.1`。証明 `key: ∀n,(n+n)+n=3*n`（omega）を `exact key g.1`。q3rqLx=prodGrp intGrp q3rqU・intGrp.mul=(+) より第1成分は defeq で `(g.1+g.1)+g.1`＝3·g.1。無条件・choice-free・正しい。

### 1.2 `q9cq_lambda_nontrivial`（L78-86）— **真水①**
`¬∃g, g³=[λ]`（[λ]=(1,e_U)）。証明: (g³).1=[λ].1=1 を q9cq_cube_fst で 3·g.1=1 に書換、`∀n,3n=1→False`（omega）。**q9kd は付値方向を一切持たず、これは第2成分（単数部）外の初の real クラス＝genuine な新規。** 非空虚（[λ] は q3rqLx.carrier の実元・実存在の否定を主張）。1 行 omega＝最も易しい次元だが本物。

### 1.3 `q9cq_val_nontrivial`（L110-120）＋ val1/val2（L123-130）— 真水①の一般形
`3∤i ⟹ ¬∃g,g³=(i,u)`（∀u:U₂）。第2成分 u に無関係に付値だけで殺す・choice-free・正しい。

### 1.4 `q9cq_lambda_zeta_indep`（L157-178）— **真水②（組立）**
`Q9cqIndep` は (i,ζ₃^j)（i,j∈{0,1,2}, (i,j)≠(0,0)）の **8 個**の非立方性の連言。監査で 8 元を数え上げ確認: (1,e)(2,e)(0,ζ)(1,ζ)(2,ζ)(0,ζ²)(1,ζ²)(2,ζ²)＝{0,1,2}²∖{(0,0)} と完全一致（過不足なし）。証明は val1/val2（i≠0・付値・新規）と zeta/zetaSq_noncube（i=0・消費）の束ね。**exponent-3 群では全非自明元≠恒等⟺核自明⟺(ℤ/3)²単射**ゆえ honest rank≥2 下界として数学的に正しい。非空虚。

**判定**: 真水は薄い（自由 ℤ 因子＝最易次元の 1 行付値＋消費補題の機械的 8 way 組立）が、**実在し非空虚で、q9kd に不在の genuine な前進**。

---

## 2. 消費（cores consumed, not re-proved）— 【YES】

- `q9cq_zeta_noncube`（L136-138）`:= q9kd_class_nontrivial`。q9kd_class_nontrivial（Q3KummerDualityReal L340-350）の型は `¬∃g, g³=((0:Int),⟨q3rqZeta,q3rq_zeta_unit⟩)` で q9cq_zetaClass=((0:Int),q9cq_zetaUnit)（q9cq_zetaUnit=⟨q3rqZeta,q3rq_zeta_unit⟩）と**完全一致**＝term 直代入の純消費・再証明ゼロ。
- `q9cq_zetaSq_noncube`（L143-151）: 第2成分へ射影（congrArg Prod.snd → Subtype.val）し `q9ci_no_cbrt_zetaSq g.2.val hval` を適用。q9ci_no_cbrt_zetaSq（Q3KummerCubeIdent L661）`∀v, v³≠q3rqZetaSq` を消費。第1成分 0=3·g.1 は制約せず単数部 u³=ζ₃² が q9ci に矛盾＝正しい消費。

**判定**: 非立方性の核（ζ₃/ζ₃² が非3乗）は q9kd/q9ci から消費。真水は付値方向＋組立に限定される（ヘッダ自己申告と一致）。

---

## 3. ★正直性検査（rank-4 過大主張なし）— 【YES・最重点】

- **定理化されるのは rank≥2 下界のみ**: `q9cq_rank_ge_two`（L186-189）=⟨q9cq_lambda_nontrivial, q9cq_lambda_zeta_indep⟩＝非立方述語の連言。rank≥2 の honest 下界。
- **(ℤ/3)⁴・|quotient|=81 は定理化されていない**: ヘッダ named target（L33-37）と正直な限定1（L40-41）で**コメントのみ**。grep で rank 4 を主張する theorem は不在。
- **商群オブジェクト未建設**: `Q9cqIndep` は `¬∃g,g³=x` の**述語 Prop**（L157-165）。Quotient/Quot による商群構成なし。`Q3CubeQuotientData`（L194-205）も述語を束ねる structure＝predicate form のみ。
- 「≅(ℤ/3)²」の表現はドキュメント文字列（L30,182）に現れるが、実定理 q9cq_rank_ge_two は非立方述語の連言＝honest 下界形であり、群同型を証明済みとして主張していない。μ₂ が自明（−1 は立方）である事実も定理化せず註記のみ（L45,128）。

**判定**: **過大主張なし。** 欠落する主単数 2 次元＋上界 exhaustion（判別器/v_M＝2〜3 ラウンド案件）は正直な限定として明記され、消去・弱化されていない（§4 規約遵守）。FLAG 事項なし。

---

## 4. 軸（axioms）— 【静的 YES】

- **本監査環境に lean/lake/elan 未導入（which/~/.elan 空）→ `lake build`・`#print axioms` 実行不能。**
- 静的検査: 対象ファイルの証明本体で使用されるタクティク/項は `omega`（純 Int/Nat 付値・指数）・`congrArg`・`Prod.fst`/`Prod.snd`・`Subtype.val`・`exact`・`intro`・`obtain`・`rfl` のみ（grep 列挙で確認）＝**全 choice-free**。
- **禁止タクティク 0**: `sorry/admit/native_decide/decide/simp/ring/nlinarith/linarith/by_cases/rcases/Classical/choice/axiom` はコメント（「sorry 皆無」等）を除き実コードにヒットなし。
- 消費核 `q9kd_class_nontrivial`・`q9ci_no_cbrt_zetaSq` は既往の B6/柱A 監査で `[propext,Quot.sound]` 確認済（推移閉包に新規 Classical.choice なし）。
- commit 8e860dd で target 未変更（git status clean）を確認。

**判定**: 静的に `[propext,Quot.sound]` 相当（新規 choice 皆無）。toolchain 復旧時に #print axioms で機械確認すべき（A2c-3 監査と同じ環境制約・precedent 準拠）。

---

## 5. 二重計上（double-counting）— 【なし】

- **vs q9kd（Q3KummerDualityReal）**: q9kd は `q9kd_class_nontrivial`＝⟨[ζ₃]⟩ の単一クラス非3乗（rank≥1）のみ。**付値クラス [λ] も 𝔽₃-独立性も持たない**。新規＝[λ]非立方＋独立性（rank≥1→rank≥2）で非重複。
- **vs KummerTheory(M320F)/KummerExact(M345F)**: 抽象体 K の K^×/(K^×)ⁿ（tateMultGroup・IUTField・Hilbert 90）＝主語別。**実局所体 L₂=ℤ₃[√−3]=q3rqLx の具体立方剰余群を計算した初モジュール。**
- **vs q9ci（Q3KummerCubeIdent）**: q9ci は非立方の核（消費対象）で重複証明でなく消費。
- scope 監査（pillar-B6-cube-quotient-scope-2026-07-11.md §4）の独立主張を、監査人が q9kd_class_nontrivial（L340）・q9ci_no_cbrt_zetaSq（L661）・q3rqLx=prodGrp intGrp q3rqU（q3rq L505）を自ら精読して再確認。

**判定**: genuinely new・二重計上なし。

---

## 6. s_B6 の敵対的決定 — **0.18**

### 6.1 算術
Σ_B den=100。B6 weight=10。
- 0.15→0.18（+0.03）: Σ_B=26.5+10·0.03=**26.8→round 27**。**表示 26→27**。
- 0.15→0.20（forecast・+0.05）: Σ_B=27.0→27。表示 27。
- 0.15→0.25（+0.10）: Σ_B=27.5→28（過大・不可）。
- 据置 0.15: Σ_B=26.5→26。

**不安定境界の注記**: 現 Σ_B=26.5 は banker's で 26（下丸め）。任意の正の増分で Σ_B>26.5 となり表示は 27 へ跳ぶ（0.16 でも Σ=26.6→27）。ゆえに「表示を動かすため」ではなく merit のみで status を決める。

### 6.2 merit 判定
**上げ材料**: (i) 実局所体 L₂ の**初**の具体立方剰余群計算。(ii) rank≥1→rank≥2 の**構造前進**（4 のうち 2 次元を明示部分群として確定）。(iii) 付値クラス [λ] という第2成分外の**初の real クラス**（q9kd に不在）。(iv) honest 下界形で**過大主張ゼロ**。(v) genuinely new・非空虚。

**下げ材料（forecast 0.20 を 1 ノッチ下げる根拠）**: (i) **真水が薄い**——新規数学は自由 ℤ 因子の付値方向（最易次元・1 行 omega）＋消費補題の 8 way 機械的組立のみ。(ii) 非立方の**核は q9ci/q9kd 消費**（労働の大半は消費）。(iii) **rank≥2 下界のみ**（4 のうち 2 次元・full rank 4 未達）。(iv) **述語形**（商群オブジェクト未建設）。(v) 体 **L₂ 1 個**。(vi) q9kd の完全 Kummer 双対構築が 0→0.15 を得たのに対し本モジュールは軽量（~200 行・消費＋1 行付値＋束ね）ゆえ、+0.05（q9kd 全体の 1/3）は寛大。**+0.03（0.18）が、genuine な rank≥2 前進を認めつつ薄い真水を敵対的に反映する honest な値。**

- **0.20 に膨らませない**: campaign を「成功」に見せるため／表示を確実に動かすための inflate をしない。真水が自由 ℤ 方向 1 行＋消費束ねである以上 0.20 は過大。
- **0.15 据置（deflate）にもしない**: rank≥1→rank≥2 は q9kd に不在の genuine な構造前進であり、初の実局所体立方剰余群・初の付値 real クラスを過小評価しない。

**結論: s_B6 = 0.18・Σ_B=26.8→表示 26→27（+1）。** compute_complete_pct.py 出力 `{"B":27}` 確認（Fraction 版・float 由来の丸め崩れなし）。

---

## 7. 実施した台帳・グラフ更新

- `target_ledger.json`: B6 status 0.15→**0.18**。
- `graph-meta.json`: 柱B complete_pct 26→**27**・complete_note に本監査結果を追記。
- `python3 tools/compute_complete_pct.py` → `{"A":55,"B":27,"C":41,"D":18,"E":42}`。**graph-meta 柱B(27) == compute 出力(27) 一致確認**。
- 他柱は不変（未編集）。Lean/IUT.lean/build.sh/gen_graph.py/graph.json/dashboard.md も不変（監査制約遵守）。

*読んだ .lean 本体*: `IUT/Q3CubeQuotientReal.lean`（全 217 行）・`IUT/Q3KummerDualityReal.lean`（q9kd_class_nontrivial L340-350）・`IUT/Q3KummerCubeIdent.lean`（q9ci_no_cbrt_zeta L628 / q9ci_no_cbrt_zetaSq L661-）・`IUT/Q3RamifiedQuadratic.lean`（q3rqLx=prodGrp intGrp q3rqU L505・q3rqU L488・q3rqLambda L726）。参照: `audit/pillar-B6-cube-quotient-scope-2026-07-11.md`・`tools/compute_complete_pct.py`（Fraction+banker's）・`graph-meta.json` 柱B。
