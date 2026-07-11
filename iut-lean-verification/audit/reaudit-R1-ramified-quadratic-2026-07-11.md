# 独立敵対監査: R1 実分岐 2 次局所拡大 ℚ₃(ζ₃) — Q3RamifiedQuadratic.lean (q3rq)

- 日付: 2026-07-11
- 対象柱項目: A7 実円分剛性 cyclotomic rigidity（weight 12・監査前 status 0.42）
- 監査モード: 独立・敵対的（既定=model/surrogate・立証責任は "real" 側）
- 判定入力: AUDIT_RUBRIC.md ＋ Lean ソース本体（ヘッダ主張は無視）＋依存 z3/ZpUnits/q3th/q3mr/cq3

## 判定サマリ

**classification = real（本物の先行建設 (b)）**。ただし A7 の rigidity 本体（不定性 kill）は
R3/R4 で到達する **FOUNDATION** であり、本ラウンド単体の complete_pct 前進は最小。

- **A7 status: 0.42 → 0.43（+0.01・foundation credit の最小ノッチ）**
- **柱 A complete_pct: 53 据え置き**（Σ_A = 47.62 + 12×0.43 = 52.78 → round 53。
  0.42 の 52.66 と同一丸め値ゆえ表示は両値で不変。境界を跨がない。）

### 一段落の justification

分岐局所拡大 ℚ₃(ζ₃)=ℚ₃(√−3) は **genuinely real かつ field-engine-free** である:
主対象 q3rqRing の担体は実 ℤ₃=zpRing 3（逆極限環）の対 z3.carrier × z3.carrier であり
Nat/Bool/Fin の身代わりでない。乗法は Gauss 則（D=−3）で環公理は明示 rw 計算で証明され、
Brahmagupta ノルム乗法性 q3rq_norm_mul は共役 ring-hom 経由の本物の定理。核心の逆元
q3rqInv=(a·N⁻¹,−b·N⁻¹) は N⁻¹=zpUnitInv（Fermat＋幾何級数・choice-free）を消費し
q3rq_inv_mul で逆元性を証明——**Field268/gefNF/Bezout/IUTField を一切 import/使用せず**
（grep 確認・cq3/IUTField はヘッダ限定コメントのみ）、A2 恒久限定（ℚ₃ に total inverse なし）
を単数（ノルム∈ℤ₃^×）のみに閉じた逆元で正面回避せず迂回する。ζ₃=(−h,h)（h=2⁻¹=zpUnitInv・
閉形式）は ζ₃³=1（本物の Gauss 乗法）かつ **位数ちょうど 3**（q3rq_zeta_ne_one かつ
q3rq_zeta_sq_ne_one）で、μ₃(ℚ₃)={1} ゆえ実 ζ₃ は genuinely 拡大を要求する（toy でない・
**コードベース初の実局所環内 order-3 根**）。分岐 e=2 は λ²=(−3,0)・ℚ₃^×↪L₂^× 単射・
v_λ∘embed=2·v₃ で実現。大域 cq3（ℚ(ζ₃)）の再利用でない（CyclotomicField3 不 import・
base=z3=ℤ₃ で ratRing でない＝genuinely LOCAL 版）。**過大主張なし**（体でない・kill 未達・
e=2 整数レベル・Galois/実テータ/π₁ ゼロの正直限定が全て健在）。
0.43 を採る（0.42 hold でなく）のは、A7 が named prerequisite とした「実 ℚ₃(ζ₃) 分岐 2 次
拡大」を本物・field-engine-free に discharge した real-building(b) を fractional に認めるため。
0.44 以上を採らないのは kill（A7 の rigidity 本体＝ℤ₃^× 不定性消去）が本ファイルで 0 前進
（1+3ℤ₃ 残存・mod-3 も R4 後）ゆえ。両値とも表示 53 で不変。

## build.sh tail

```
'IUT.q3rqRing' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_inv_mul' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_zeta_cube' depends on axioms: [propext, Quot.sound]
'IUT.q3rqEmbed' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_ramification' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```
bash build.sh EXIT=0・no sorry。

## 監査者自作 #print axioms（16 load-bearing 対象・verbatim）

scratch: `import IUT.Q3RamifiedQuadratic` で以下を実行（lake env lean）:

```
'IUT.q3rqRing' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_norm_mul' depends on axioms: [propext, Quot.sound]
'IUT.q3rqInv' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_inv_mul' depends on axioms: [propext, Quot.sound]
'IUT.q3rqU' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_two_half' depends on axioms: [propext, Quot.sound]
'IUT.q3rqZeta' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_zeta_cube' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_zeta_ne_one' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_zeta_sq_ne_one' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_mu3_closed' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_lambda_sq' depends on axioms: [propext, Quot.sound]
'IUT.q3rqEmbed' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_embed_inj' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_ramification' depends on axioms: [propext, Quot.sound]
'IUT.q3rq_exists' depends on axioms: [propext, Quot.sound]
```

全 16 対象 = [propext, Quot.sound] のみ。**Classical.choice / sorryAx 皆無**。
scratch と stray IUT/*.olean は削除済み。

## Rubric 構造化出力（q3rq）

- **classification**: real
- **principal_object**: O_{ℚ₃(ζ₃)}=ℤ₃[√−3] 実可換環 q3rqRing（担体 z3.carrier×z3.carrier・
  z3=zpRing 3=実 ℤ₃ 逆極限）＋単数群 U₂=O_{L₂}^×（q3rqU:Grp）＋実 ζ₃（位数3・μ₃⊂U₂）。
- **is_it_a_stand_in**: no。担体は実 ℤ₃ の対で Nat/Bool/Fin の濃度合わせでない。乗法は
  実 Gauss 則、逆元は実 zpUnitInv（choice-free）、ζ₃ は実 h=2⁻¹ の閉形式。
- **self_declared_external**: なし（核となる実対象 O_L/U₂/ζ₃ を外部/後続/模型と自認しない。
  後続とされるのは kill＝rigidity 本体であって本ファイルの主対象でない）。
- **moves_complete_pct**: 実質 ~0（foundation・A7 の rigidity 本体を動かさない）。
  real-building(b) を認め fractional に 0.42→0.43 のみ。表示 53 は不変。
- **evidence**: q3rqRing(def:147)・q3rq_norm_mul(thm:330)・q3rqInv(def:364・zpUnitInv 消費)・
  q3rq_inv_mul(thm:375)・q3rqU(def:488)・q3rqZeta(def:534)・q3rq_zeta_cube(thm:614)・
  q3rq_zeta_ne_one(thm:644)・q3rq_zeta_sq_ne_one(thm:650・位数ちょうど3)・
  q3rq_mu3_closed(thm:707)・q3rq_lambda_sq(thm:732・e=2)・q3rqEmbed(def:801)・
  q3rq_embed_inj(thm:815)・q3rq_ramification(thm:829・v_λ=2·v₃)。

## 主要プローブ結果

1. **実可換環か**: yes。carrier=z3.carrier×z3.carrier（実 ℤ₃ 対）。mul_assoc/left_distrib
   等は z3 の環公理からの明示 rw 計算（sorry でない）。q3rq_norm_mul は共役 ring-hom
   x·x̄=(N,0)＋mul_mul_mul_comm 経由の本物の Brahmagupta。
2. **★逆元は閉形式・field-engine-free か（最重要プローブ）**: yes。q3rqInv=(a·N⁻¹,−b·N⁻¹)、
   N⁻¹=zpUnitInv 3 isPrime_three (q3rqNorm x) hx。ZpUnits 精読で zpUnitInv=x^{p−2}·(x^{p−1})⁻¹
   （幾何級数 zpGeomInv・代表元抽出なし＝choice 回避）を確認。q3rqInv/q3rq_inv_mul とも
   Field268/gefNF/Bezout/IUTField を一切使わず（import 6 本＝Zp3ValuationRing/ZpUnits/
   Q3TateCurve/QuadraticNorm/FormalGroupExists/LTIterate・grep で本体使用も 0）。
   拡大に IUTField インスタンスなし・total inverse なし＝A2 障害を単数閉じた逆元で迂回。
3. **ζ₃ は order-3 実か**: yes。ζ₃=(−h,h)・h=2⁻¹=zpUnitInv（閉形式）。ζ₃³=1（q3rq_zeta_cube・
   本物の Gauss 乗法）・ζ₃≠1（第2成分 h≠0）・ζ₃²≠1（第2成分 −h≠0）＝位数ちょうど 3。
   μ₃ 乗法閉（q3rq_mu3_closed・9 通り帰着）。μ₃(ℚ₃)={1} との対比で拡大を genuinely 要求。
4. **e=2 実現か**: yes。λ=(0,1)・λ²=(−3,0)（q3rq_lambda_sq）・3=−λ²。埋め込み (j,u)↦(2j,φu)
   単射（q3rq_embed_inj）・v_λ∘embed=2·v₃（q3rq_ramification=rfl）。
5. **大域 cq3 の再利用でないか**: yes（局所版）。import に CyclotomicField3 なし・base=z3(ℤ₃)。
   cq3/IUTField はヘッダの正直限定コメント（兄弟担体・A2 継承）のみに出現。
6. **過大主張チェック**: 問題なし。体主張なし（O_L/L^× のみ・total inverse なし）・kill 主張なし
   （foundation・ℤ₃^× 不定性 0 kill）・theta 群/rigidity 主張なし（R3/R4）・tmz 橋なし。
   正直限定 7 項（O_L 非体・kill 未達・e=2 整数レベル・R4 後 mod-3 のみ・1+3ℤ₃ 残存・
   tmzLimit 比較準同型なし・Galois/実テータ/π₁ ゼロ）が全て健在。

## 結果 Σ_A / 柱 A

- A7 status: 0.42 → 0.43
- Σ_A = 47.62 + 12×0.43 = 52.78 → round 53（compute_complete_pct.py 出力 {"A":53}）
- 柱 A complete_pct: 53（不変・境界跨がず）
- graph-meta.json pillars.A.complete_pct=53・complete_note に R1 note prepend 済み
- python3 tools/gen_graph.py 再生成済み（modules=623）
- dashboard.md 二軸表 pillar-A セルに R1 note prepend 済み（53% 不変）

## overclaim / re-use / hidden-choice

なし。field-engine（Field268/gefNF/Bezout/IUTField）不使用・cq3 大域体の再利用なし・
新規 Classical.choice/sorryAx 皆無（16 対象自作 #print axioms で確認）。
