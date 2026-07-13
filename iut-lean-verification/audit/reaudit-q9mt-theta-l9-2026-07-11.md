# 独立敵対監査: q9mt（level-9 実テータ群・μ₉ 値 Weil ペアリング・q9c 消費者）

- **対象**: `IUT/Q3Mu9ThetaGroup.lean`（prefix `q9mt`・674 行・commit 62cc7ba）
- **申告**: `[実／本物の先行建設(b)] FOUNDATION・complete_pct 0前進`
- **監査日**: 2026-07-11
- **監査者立場**: 独立・敵対的・既定 SKEPTICAL・コードは書いていない
- **結論（先出し）**: 申告は正直。q9c_mu9_complete の消費は**本物**、Weil 非退化値は**本物の原始 9 乗根**、witness は**本物のテータ群元**、全対象 axiom-clean `[propext, Quot.sound]`、禁止タクティク 0、double-counting なし。**0前進・A=54 据え置き**が妥当。target_ledger.json 不変。

---

## 1. ★ q9c 消費の本物性（本監査の crux）

`q9mt_mem_val0_mu9 (g) (hmem : q9mtMem g) (ha : g.1.2 = 0) : q3kMu9 g.2.2.val` を全文精読。

証明チェーン（すべて実導出・vacuous でない）:
1. `hmem : q9mtMem g` は **genuine な所属仮説**（`q9mtMem g := qᵃ·w⁹ = 1` の実 M^× 内等式）。仮説を偽と仮定して空虚に閉じてはいない。
2. `q9mt_mem_iff.mp hmem` で成分特徴付け `(6a+v_w=0 ∧ (u₆⁹)ᵃ·u_w⁹ = 1)` を得る（mem_iff は付値成分 54a+9v_w=0⟺6a+v_w=0 と単数成分の Prod.mk.injEq 分割で厳密に証明・完全性不使用）。
3. `ha : a=0` を h2 に代入。`tateZpow q3kU q9tlQ.2 0 = q3kU.one`（tateZpow_zero）＋ one_mul で `h2' : tateZpow q3kU g.2.2 9 = q3kU.one`（＝ u_w⁹=1）を**実導出**。
4. `q9mt_ninth_gen q3kU g.2.2`（塔分解 9=6+3, 6=3+3・tateZpow_add 2 回＋q9mt_cube_gen で各立方を開く汎用 Grp 補題）で 9 乗を 9 重積 `(((u·u)·u)·((u·u)·u))·((u·u)·u)` へ開き `h9`（q3kU subtype 上）を得る。
5. `hval := congrArg Subtype.val h9` で carrier（q3kCar）へ落とす。

**shape 一致の検証（隠れ cheat の有無）**: `q9c_mu9_complete` の実シグネチャ（Q3Mu9Completeness.lean:1311）は
```
(hu9 : q3kMul (q3kMul (q3kMul (q3kMul u u) u) (q3kMul (q3kMul u u) u))
    (q3kMul (q3kMul u u) u) = q3kOne) : q3kMu9 u
```
`hval` の宣言型は u = `g.2.2.val` を代入した
`q3kMul (q3kMul (q3kMul (q3kMul u u) u) (q3kMul (q3kMul u u) u)) (q3kMul (q3kMul u u) u) = q3kOne`
と**構造的に完全一致**（(((u·u)·u)·((u·u)·u))·((u·u)·u)）。呼び出し `q9c_mu9_complete g.2.2.val hval` は `lake build` 成功が示すとおり**定義的に typecheck**（congrArg Subtype.val が q3kU.mul の .val を q3kMul へ、q3kU.one.val を q3kOne へ定義的に還元。ここに defeq の偽装が入れば build が落ちる）。9 重積 ⇄ tateZpow 変換 1 本で q9c 側に追加要求なし、という設計 §2.4 の主張どおり。

→ **q9c 消費は本物・非空虚・shape 一致で cheat なし。**

## 2. ★★ Weil 非退化の本物性（原始 9 乗根か ζ₃ 誤標か）

- `q9mtWeil g g' := w'ᵃ · w^{−a'}`（交換子スカラー成分・q9mt_commutator で [g,g']=(e₉,0,1) を実証明）。asserted でなく交換子計算から落ちる。
- `q9mt_weil_g3_gz : e₉([3],[ζ₉]) = (0, q3kU.inv q9tlZeta9U)`。a₃=−1・a_ζ=0 で e₉ = ζ₉^{a₃}·3^{−a_ζ} = ζ₉^{−1}·3⁰ = ζ₉^{−1} を実 `tateZpow`（tateZpow_negOne・tateZpow_zero）で計算。
- `q9mt_weil_nondeg : e₉([3],[ζ₉]) ≠ 1`。ζ₉⁻¹=1 ⟹ ζ₉=1（Grp.inv_inv/inv_one）⟹ q3kZeta9=q3kOne（congrArg Subtype.val）を `q3k_zeta9_ne_one` で矛盾。

**原始性の裏取り**: ζ₉ = q9tlZeta9U は q3kZeta9 = (0,1,0)（=Y）を包む。Y³ = q3k_embed ζ₃ で `q3k_zeta9_cube_ne_one`（Y³≠1）かつ `q3k_zeta9_pow9`（Y⁹=1）。位数は 9 を割り 1・3 でない ⟹ **ちょうど 9＝真の原始 9 乗根**（ζ₃ 誤標ではない）。曲線側でも q9tl_zeta9_tor が [ζ₉] の位数ちょうど 9 を実証。

**敵対的注記（正直に記載）**: `q9mt_weil_nondeg` の**証明本体が示すのは ≠1 のみ**（ζ₃ も ≠1 を満たす）。「原始 9 乗根」の質は本定理の証明内容ではなく外部の order-9 事実（q3k_zeta9_cube_ne_one・q9tl_zeta9_tor）に依存する。値自体は確かに ζ₉⁻¹（order 9）なので誤標ではないが、非退化定理単体は μ₃/μ₉ を区別しない——この限定はヘッダ「原始 9 乗根」主張の担保が別補題側にあることを意味する。過大主張ではないが束ねの構造として明記する。

→ **Weil 非退化値は本物の原始 9 乗根。**

## 3. witness の本物性

- `q9mtG3 = ((1,−1),3)`・`q9mt_g3_mem`: mem_iff.mpr で 6·(−1)+6=0（omega）∧ (u₆⁹)^{−1}·(u₆)⁹=1（tateZpow_negOne＋q3kU.inv_mul・u_q=u₆⁹ で定義的に閉じる）。
- `q9mtGZeta = ((1,0),ζ₉)`・`q9mt_gz_mem`: 6·0+0=0 ∧ (u₆⁹)⁰·ζ₉⁹=1（tateZpow_zero＋Subtype.ext＋q9tl_zpow9 で Y⁹=1）。
- 両証明とも実仮説から実等式を導く（vacuous でない）。

→ **両 witness は本物のテータ群元。**

## 4. axioms・禁止タクティク

`lake env lean` で列挙実行（監査者自身）:
```
q9mt_mem_val0_mu9 : [propext, Quot.sound]
q9mt_weil_g3_gz   : [propext, Quot.sound]
q9mt_weil_nondeg  : [propext, Quot.sound]
q9mt_nonabelian   : [propext, Quot.sound]
q9mt_mem_iff      : [propext, Quot.sound]
q9mt_exists       : [propext, Quot.sound]
q9mt_g3_mem       : [propext, Quot.sound]
q9mt_gz_mem       : [propext, Quot.sound]
q9mt_commutator   : [propext, Quot.sound]
```
全対象 exactly `[propext, Quot.sound]`・新規 Classical.choice 皆無。

禁止タクティク grep（sorry/admit/simp/decide/by_cases/rcases/nlinarith/ring）: **唯一のヒットは 49 行目の日本語コメント「sorry 皆無」**でタクティク使用でない。omega は 21 箇所すべて純 Int/Nat（付値方程式 54a+9v=0⟺6a+v=0・添字算術 e1+e2+e3・(-9)+9 等）で許容範囲。`lake build IUT.Q3Mu9ThetaGroup` EXIT=0・no sorry。

## 5. double-counting・capstone

q9mt は q=q9tlQ=3⁹・g_τ 中央指数 −9（9 乗）・所属条件 qᵃw⁹=1（9 乗）・Weil 値 μ₉・q9c_mu9_complete 消費——**q3m3（level-3・μ₃・−3・q9c 非消費）の再ラベルでない新規 level-9 対象**。q3m3/q9tl/q9c/q9ps/q3k は消費のみ（再証明せず）。capstone `q9mt_data`/`q9mt_exists` は 13 フィールド全て実証明済み定理を束ねる——hollow でない。

## 6. 台帳判定

- q9mt は**テータ機構の建設**であって kill ではない（kill/表示は後続 q9mr 剛性＋q9mb 橋）。本モジュール単体は何も殺さず、どの表示も動かさない。
- **complete_pct 0前進**が正しい。`target_ledger.json` **不変**・**A status 群不変**。
- `compute_complete_pct.py` 再実行: `{"A": 54, "B": 18, "C": 41, "D": 18, "E": 42}`——A=54 維持。
- `graph-meta.json` pillar-A `complete_note` に本監査の正直注記を追記（complete_pct=54 のまま）。過大主張・水増しなし。

---

**総合判定**: q9c 消費＝本物（yes）・Weil 非退化＝本物の原始 9 乗根（yes・ただし定理本体は ≠1 のみで原始性は外部補題担保と明記）・axioms 全 `[propext, Quot.sound]`・0前進・A=54 据え置き。**申告と実 Lean 定義は整合。**
