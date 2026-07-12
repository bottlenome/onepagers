# 独立敵対監査: IUT/Q3KummerCubic.lean（F-wild R1・実巡回 3 次 Kummer 拡大 M=ℚ₃(ζ₉)）

- 監査日: 2026-07-11
- 監査対象: `IUT/Q3KummerCubic.lean`（prefix `q3k`・1032 行・commit d9e49a7）
- 監査者: 独立敵対監査（本モジュール非関与・既定スタンス＝懐疑）
- 主張分類（著者）: **[実／本物の先行建設(b)] FOUNDATION**、complete_pct **0 前進**（正直申告）
- 評決: **genuine real 先行建設（水増しでない）／axiom-clean／0 前進の申告は正しい（A 据え置き 54）**

---

## 0. 結論（先出し）

1. 本モジュールは §2(b)「本物の先行建設」に該当する**真正な実数学**である。§3 toy 主語違反・§2 リラベル/束ね直し違反・水増しは**認められない**。
2. #print axioms は主要 12 対象すべて厳密に `[propext, Quot.sound]`。`Classical.choice`／`sorryAx` **皆無**。禁止タクティク**不使用**。
3. しかし本モジュールは**何も kill しない**（付値・位相・G_{ℚ₃}・剛性・不定性消去いずれも 0）。`target_ledger.json` の A 項目（A2/A3/A7/A8）のいずれも本物には進めない。
4. ゆえに CLAUDE.md §5「foundation は実 kill に CONSUMED されて初めて信用を得る」に従い、**complete_pct 0 前進を確定**。`target_ledger.json` は**無改訂**（新規 weighted item も作らない＝foundation への信用捏造を回避）、A は **54 据え置き**。`graph-meta.json` の pillar-A `complete_note` にのみ**正直な 0 前進記録を追記**した。

---

## 1. 読んだもの（def・theorem 本体を全行精読）

`Q3KummerCubic.lean` を signature でなく**証明本体**まで全読した。核心の検証:

### 1.1 台と乗法（§3 主語の実在性）
- `q3kCar := q3rqCar × q3rqCar × q3rqCar`（三つ組 (a,b,c) ↔ a+bY+cY²）。
- 係数環 `q3rqCar` を依存ファイル `Q3RamifiedQuadratic.lean` で裏取り: `q3rqCar := z3.carrier × z3.carrier` で **z3 = zpRing 3 = 実 ℤ₃（逆極限）**。すなわち主語は**実 O_{L₂}=ℤ₃[√−3]** の上の 3 次代数であり、m202fVol 型・Bool 軌道・surrogate 群を**主語にしていない**。§3 適合。
- `q3kMul` はねじれ畳み込み（Y³=ζ₃=`q3rqZeta`・Y⁴→ζ₃Y）を係数環の実 mul/add で書いた本物。`q3rqZeta = (−h, h)`（h=`q3rqHalf`=実 2⁻¹∈ℤ₃）で実 ζ₃。

### 1.2 `q3k_mul_assoc`（★ 重い結合律・axiom されていないか）
- 3 成分それぞれを 9 項の標準形へ `right_distrib`/`left_distrib`/`mul_assoc`/`mul_comm` で展開し、`q3k_perm0/perm1/perm2`（9 項和の再配置補題・各々 `q3k_perm_chain` の実証明に帰着）で一致させる**明示 rw 連鎖の本証明**。`sorry`/`admit`/`rfl 誤魔化し`は無い。d=ζ₃ は抽象環元として扱われ、途中で ζ₃ の特殊値に依存しない（結合律は係数環公理のみで閉じる）。→ 真正。

### 1.3 σ（相対 Galois）
- `q3kSigma`（Y↦ζ₃Y）。`q3k_sigma_mul`（σ(xy)=σx·σy）は ζ₃·ζ₃²=1（`q3k_z_zsqR1`）・ζ₃²·ζ₃=1（`q3k_zsq_zR1`）・ζ₃²·ζ₃²=ζ₃（`q3k_zsq_zsqR`）等の**実 ζ 冪還元**を消費した本証明。フェイクでない。
- `q3k_sigma3_id`（σ³=id・位数ちょうど 3）は ζ₃³=1（`q3k_z3R`=`q3rq_zeta_cube`）を消費。位数 3 は本物。

### 1.4 `q3k_norm_eq`（★★ 荷重ノルム恒等式・Y,Y² 消去が本物か）
- `q3k_norm_eq : x·(σx·σ²x) = embed(a³+ζ₃b³+ζ₃²c³−3ζ₃abc)` は `q3k_w_eq`（σx·σ²x=w 閉形式）と `q3k_x_wt`（x·w=embed N）に分解。
- **Y 成分消去 `q3k_xwt_1`・Y² 成分消去 `q3k_xwt_2`** は `q3k_cancel6a`/`q3k_cancel6b`（6 項相殺）で 0 になる本証明。
- 荷重の要 **1+ζ₃+ζ₃²=0（`q3k_zeta_sum_zero`）** は `q3k_sum3`→`q3k_bc`/`q3k_bc2`/`q3k_bc3` を経て `q3k_w_eq` に**実際に消費**されている（vacuous でない）。定数成分は `q3k_norm_collect`＋`q3k_three_K` で −3ζ₃abc を正しく集約。→ 荷重恒等式は真正。

### 1.5 `q3k_inv_mul`（閉形式共役ノルム逆元・体エンジン不使用か）
- `q3kInv x hx := (σx·σ²x)·embed(q3rqInv (N x) hx)`。**`q3rqInv` を実消費**。
- `q3rqInv` を依存ファイルで裏取り: `q3rqInv x hx := (x.1·zpUnitInv 3 …, (−x.2)·zpUnitInv 3 …)` で **zpUnitInv（実 Hensel 単数逆元・choice-free）** を使う閉形式。`q3rqUnitMem x := IsZpUnit 3 (q3rqNorm x)`＝ノルムが ℤ₃ 単数のときのみ定義。→ **体エンジンの total inverse ではない**。
- `q3kUnitMem x := q3rqUnitMem (q3kNormBase x)` で単数（N∈ℤ₃^×）に**確かに制限**。`q3kU : Grp` は subtype `{x // q3kUnitMem x}` 上に構成（`inv_mul` は `q3k_inv_mul'`）。→ §4 正直限定 1（M は体でない・逆元は単数限定）は**真実**。

### 1.6 ζ₉ の位数ちょうど 9
- `q3k_zeta9_pow9`（Y⁹=1）は `q3k_zeta9_cube`（Y³=ζ₃）→`embed_mul`×2→ζ₃³=1（`q3rq_zeta_cube`）の本証明。
- `q3k_zeta9_ne_one`（Y≠1）・`q3k_zeta9_cube_ne_one`（Y³=ζ₃≠1）で **9 の約数 1,3 での早期還帰を排除**＝位数ちょうど 9。非空虚。

### 1.7 capstone
- `Q3KummerCubicData`／`q3kData`／`q3k_exists` は上記**本ファイルで新規に証明した**定理（sigma_mul・sigma3_id・norm_eq・inv_closed・zeta9_cube(_ne_one)）を束ねる。既存結果の再束ねでなく、**新対象 M についての新定理の束ね**＝§2 が禁じる「新しい capstone 束ね（既存結果の水増し）」ではない。中身は hollow でない。

---

## 2. #print axioms 自走結果（監査者実行）

`IUT.Q3KummerCubic` を import した scratch を `lake env lean` で実行:

```
'IUT.q3kData'              depends on axioms: [propext, Quot.sound]
'IUT.q3k_norm_eq'         depends on axioms: [propext, Quot.sound]
'IUT.q3k_inv_mul'         depends on axioms: [propext, Quot.sound]
'IUT.q3k_zeta9_pow9'      depends on axioms: [propext, Quot.sound]
'IUT.q3k_mul_assoc'       depends on axioms: [propext, Quot.sound]
'IUT.q3k_sigma_mul'       depends on axioms: [propext, Quot.sound]
'IUT.q3kU'                depends on axioms: [propext, Quot.sound]
'IUT.q3k_zeta9_ne_one'    depends on axioms: [propext, Quot.sound]
'IUT.q3k_zeta9_cube_ne_one' depends on axioms: [propext, Quot.sound]
'IUT.q3kRing'             depends on axioms: [propext, Quot.sound]
'IUT.q3k_exists'          depends on axioms: [propext, Quot.sound]
'IUT.q3k_normBase_mul'    depends on axioms: [propext, Quot.sound]
```

全対象**厳密に `[propext, Quot.sound]`**。`Classical.choice`／`sorryAx` 皆無。`lake build IUT.Q3KummerCubic` は EXIT=0（no sorry）。

**禁止タクティク grep**（`sorry|admit|simp|decide|by_cases|rcases|ring|nlinarith|omega|linarith|native_decide|Classical.choice|choice`）: コード本体ヒット 0。`ring` の 2 ヒットは**タクティクでなく構造体フィールド名**（`ring : CRing`／`ring := q3kRing`）、他は日本語コメント。禁止タクティク不使用を確認。

---

## 3. 二重計上・水増しチェック

- **q3rq のリラベルか?** No。`q3kCar` は `q3rqCar³`（三つ組）で Y³=ζ₃ のねじれ乗法を持つ**次数 3 の新対象**。q3rq を係数環として消費するだけで、rename でない。
- **既存結果の capstone 束ね直しか?** No。capstone が束ねる定理は全て本ファイルで新規証明された新対象 M についての命題。
- **§3 toy 主語違反か?** No。主語は実 z3=zpRing 3 上の実 q3rq 係数 3 次代数。
- → 水増し・§2/§3 違反は**認められない**。genuine real 先行建設。

---

## 4. 台帳裁定（ledger adjudication）

現行 `target_ledger.json`（A 項目 status）から `tools/compute_complete_pct.py` → **{"A":54,...}**。

本モジュールが本物に進める A 項目を敵対的に探索:

| 項目 | 内容 | 本モジュールの寄与 | 判定 |
|---|---|---|---|
| A2 (w8, 0.65) | 実 p 進局所体 K_v（完備化） | M は O_M と M^× のみ・体でない・付値/位相/完備化なし（正直限定 1,4） | 進めない |
| A3 (w12, 0.75) | 実 G_K=有限 Gal の逆極限 | 相対 σ（位数 3）のみ・G_{ℚ₃}/逆極限なし（正直限定 3） | 進めない |
| A7 (w12, 0.49) | 実円分剛性 | **何も kill せず・剛性内容 0・ℤ₃^× 不定性を一切殺さない**（正直限定 2） | 進めない |
| A8 (w12, 0.65) | Tate 曲線の実被覆 | 無関係 | 進めない |

本モジュールは「level-9 kill / pro-3 bulk」という named 実ターゲットの**土台**であって、その kill そのものは後続ラウンド。CLAUDE.md §5 が明記する通り **foundation は実 kill に CONSUMED されて初めて complete_pct の信用を得る**。現時点で consume する kill は存在しない。

**裁定**: 著者の 0 前進申告は**正しい**。
- `target_ledger.json`: **無改訂**（status 不変・新規 weighted item も作らない＝foundation への信用捏造を回避）。
- 改訂後 `compute_complete_pct.py` 再実行 → **{"A":54,...}**（不変）を確認。
- `graph-meta.json` pillar-A `complete_pct`: **54 据え置き**（改訂なし）。`complete_note` に**本監査の 0 前進記録を追記**（F-wild opener が real+axiom-clean で landing・complete_pct 0 movement・実ターゲットは後続 level-9 kill）。追記後 graph-meta の A complete_pct=54 と `compute_complete_pct.py` の A=54 が**一致**することを確認。

---

## 5. 監査者が編集したファイル（制約遵守）

- `graph-meta.json`: pillar-A `complete_note` に 2026-07-11 の 0 前進記録を**追記のみ**（`complete_pct`/`status` 不変・他 pillar 不変）。
- `audit/reaudit-q3k-fwild-opener-2026-07-11.md`: 本記録を新規作成。
- `target_ledger.json`: **無改訂**（意図的）。
- Lean ファイル・IUT.lean・build.sh・gen_graph.py・graph.json・dashboard.md: **未編集**（制約遵守・graph.json は親が再生成）。

## 6. 総評

沈黙すべき点は無い。本モジュールは**本物の実巡回 3 次 Kummer 拡大**を実 O_{L₂} の上に axiom-clean に建てた真正な先行建設であり、著者の分類 [実／本物の先行建設(b)] と正直限定 7 項は全て**真実**。同時に、それが**何も kill しない foundation** であるという事実も真実であり、**complete_pct 0 前進**は誇張でも失敗でもなく正しい帰結である。信用は後続の level-9 kill が本モジュールを消費した時に与える。
