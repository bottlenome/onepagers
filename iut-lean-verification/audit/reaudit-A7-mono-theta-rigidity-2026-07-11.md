# 再監査記録: A7 実 mono-theta 円分剛性 MECHANISM (q3mr)

- 日付: 2026-07-11
- 対象モジュール: `IUT/Q3MonoThetaRigidity.lean` (prefix `q3mr`)
- 依存精読: `IUT/Q3ThetaGroup.lean` (q3th, A8・既計上 0.65), `IUT/TateModuleIndeterminacy.lean` (tmi, A7・既計上), `IUT/TateModuleEndo.lean` (tme), `IUT/CyclotomicRigidityAut.lean` (cra)
- 監査方式: 独立・敵対的（既定=model/surrogate/re-label・立証責任は「real/NEW」側）
- 台帳: A7 weight=12・監査前 status=0.40。Σ_A = 47.62 + 12·s_A7（他項目定数 47.62）

## 結論（先出し）

**A7 status: 0.40 → 0.42（+0.02）。柱A complete_pct: 52 → 53。**

q3mr は [EtTh] mono-theta 円分剛性の MECHANISM を、実テータ群 q3thGrp（A8・実
E₉=ℚ₃^×/q^ℤ 上）の上で忠実な level-2 インスタンスとして realize する。A8 の交換子値
（q3th_comm_eq_weil）でも tmi の ℤ₃^× 特徴付けでもない NEW な内容（Klein 決定性・endo 版
KILL 機構・内部 cyclotome 恒等固定）で、level-2/μ₂ でも非空虚。ただし殺す群は μ₂（3 と素）で
tmi の ℤ₃^× 不定性はまるごと SURVIVES ゆえ実 ℤ₃^× kill は依然 0。機構の忠実部分ケースゆえ
設計自己予測 0.43 を敵対的に 1 ノッチ下げた 0.42。

## rubric 分類（q3mr）

- `classification`: **real**（A7 へ算入・moves_complete_pct: yes）
- `principal_object`: 実テータ群 q3thGrp（=C_M(g_τ)・実 ℚ₃^×=q3tGrp 成分・実 E₉=ℚ₃^×/q^ℤ）上の
  membership-限定自己準同型と、その交換子（実 Weil ペアリング）保存＝mono-theta 剛性機構。
- `is_it_a_stand_in`: **no**。主対象は A8 で既に real 認定された実テータ群（Bool/Nat/Fin 身代わりでない）。
  q3mr の rigidity は実 ℚ₃^× 成分計算（tateZpow 簿記）で完全証明。
- `self_declared_external`: μ₂ が Aut(ℤ₃(1))=ℤ₃^× でないこと・tmi の ℤ₃^× SURVIVES・Galois 作用 0・
  実テータ関数/π₁-同定 0 を正直に明記（消していない・下記「正直な限定」参照）。
- `moves_complete_pct`: **yes（modest）**。characterize-only（tme/tmi/cra）へ endo 水準の KILL 機構を追加。
- `evidence`: q3mr_weil_klein_left (l.125)・q3mr_rigidity (l.239)・q3mr_cyclotome_fixed (l.283)・
  q3mr_klein_fails_on_M (l.315)。

## build.sh 末尾（EXIT 0・no sorry）

```
'IUT.q3mr_weil_klein_left' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_rigidity' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_cyclotome_fixed' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_mu2_killed' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_klein_fails_on_M' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```

## #print axioms（監査者自作 scratch `import IUT.Q3MonoThetaRigidity`・全 11 load-bearing 対象・verbatim）

```
'IUT.q3mr_weil_klein_left' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_weil_klein_right' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_proj_eq_shift' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_hom_one' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_hom_inv' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_rigidity' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_zeta_eq_comm' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_cyclotome_fixed' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_mu2_killed' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_klein_fails_on_M' depends on axioms: [propext, Quot.sound]
'IUT.q3mr_inner_example' depends on axioms: [propext, Quot.sound]
```

全 11 対象 = `[propext, Quot.sound]` のみ。**Classical.choice / sorryAx 皆無**（あれば失格）。
scratch (`Q3mrCheck.lean`) と生成 olean は削除済（git clean）。

## DECISIVE 探針 1: 二重計上 / re-label（vs A8 q3th・vs A7 tmi）

### import 事実
q3mr の import は `import IUT.Q3ThetaGroup` **1 本のみ**（l.55）。tmi/q3nt/crl は import しない。
grep で `tmi`/`crl`/`q3nt`/`TateModuleIndeterminacy`/`CyclotomicRig` は**コメント（正直な限定
記述）にのみ**出現し、コード（def/theorem 本体）には無し。⇒ literal な A8/tmi 再輸出ではない。

### q3mr_weil_klein_left は q3th_comm_eq_weil の系か？（NEW vs A8）
- q3th_comm_eq_weil は「[g,g']=(e(g,g'),0,1)」＝**交換子の値の式**（A8 で計上済）。
- q3mr_weil_klein_left は「g1,g2,g'∈q3thGrp かつ proj(g1.2)=proj(g2.2)（同 Klein 像）⟹
  e(g1,g')=e(g2,g')」＝**Klein 同値での Weil ペアリング不変性**（q^ℤ-lift 独立性）。本体（l.129-164）は
  q3mr_proj_eq_shift で g2.2=g1.2·qᵏ を取り、所属 2 条件 `a'=−j'`（ha1/ha2）と `w'²=q^{−a'}`（hsq）を
  **実消費**して補正因子 B·D=1 を閉じる。値の式の rewrite ではなく、所属を消費する別命題。
- **機械可検証な load-bearing 証拠**: q3mr_klein_fails_on_M（l.315）が
  g₁=((1,0),1)∈q3thGrp・g₂=((1,1),1)∉q3thGrp（a=1≠−0）が**同 Klein 像**（proj w=1 が rfl で一致）を持つのに
  e(g₁,g₋₁)=1 ≠ (0,−1)=e(g₂,g₋₁) を証明。⇒ 所属なしでは Klein 同値はペアリングを決定しない＝
  q3mr_weil_klein_left は q3th_comm_eq_weil の系でない。**NEW vs A8 確定**。

### vs tmi（NEW vs A7 既存）
tmi の主語は End/Aut(ℤ₃(1))=zpsLimit（実 ℤ₃^×・3-冪円分塔 tmzLimit）の分類＝**別対象**。
q3mr は実 ℚ₃^× から建てた q3thGrp のテータ群 rigidity。tmi を import せず・tmi の定理を再述しない。
主語が disjoint。**re-label でない確定**。

## DECISIVE 探針 2: endo-not-bijective / level-2 縮退（非空虚性）

### endo 版であることの確認
q3mr_rigidity（l.239-243）の仮説は hHom（membership-限定 hom）・hMem（所属保存）・hKlein
（Klein 像上恒等）**のみ**。injective/bijective 仮定は無い。ヘッダの「全単射なら系は安く出る（唯一の位数 2 元）・
非安価は endo 版」（l.41-42）と整合。⇒ 「唯一の位数 2 元」型の安い議論に退化していない。

### collapsing map の排除は smallness でなく機構による
証明（l.244-264）: φ(comm g g')=comm(φg,φg')〔hHom+hom_one/inv〕=(e(φg,φg'),0,1)〔q3th_comm_eq_weil〕
=(e(g,g'),0,1)〔q3mr_weil_klein_left/right・hMem/hKlein〕=comm g g'。cyclotome-collapsing endo
（φ(ζ)=1）を排除するのは、群が小さいからではなく **Klein 決定性＋非退化 e([3],[−1])=−1≠1**。

### 非空虚性
q3mr_cyclotome_fixed は ζ=q3mrZeta=comm(g₃,g₋₁)（l.270-290）を厳密固定。ζ の Klein 像を持つ member は
{((c,−2k),(2k,−1)) : c∈ℚ₃^×, k∈ℤ}＝大集合。φ はこの大集合の中で ζ（c=1,k=0）を厳密に pin する。
q3mr_inner_example（l.379）が内部自己同型 conj_h を仮説クラスの witness として提供（クラス非空）。
⇒ level-2/μ₂ でも「殺すものが無い」空虚ではない。**level-2 縮退攻撃は endo 定式化＋false-on-M 証拠で survives**。

## 探針 3: overclaim / 正直な限定（消していない）

コード＋ヘッダ（l.34-51）に以下の正直な限定が存在し、コードは overclaim しない:
1. 殺した群は μ₂（3 と素）で Aut(ℤ₃(1))=ℤ₃^× でない。tmi の ℤ₃^× 不定性は本定理後もまるごと SURVIVES
   （full ℤ₃^× KILL でない・IUT 荷重の kill は 0）。ℤ₃^×→Aut(μ₂) が算術的に自明（u 奇⇒(−1)ᵘ=−1）を隠さない。
2. 全単射なら系 7 は安く出る・非安価は endo 版（q3mr_rigidity は bijective に弱めていない）。
3. level 2/p=3/q=9/μ₂ 単一切片。
4. Galois 作用ゼロ。
5. Klein 降下ペアリングの関数化はしない（∃k は Prop 内破壊のみ・choice 回避）。実テータ関数・π₁-同定は依然 0。
6. 二重計上境界: q3th 定理は消費のみ・再証明ゼロ。tmi/q3nt/crl 不 import。

tmi/q3th の既存正直限定は削除されていない（tmi の「CHARACTERIZE not KILL」・q3th の「実テータ関数 0」保持）。

## status 決定と根拠

- **0.42 を採る理由**: (i) 機構は本物（実対象 q3thGrp 上の real 定理）(ii) NEW vs A8（Klein 決定性・
  false-on-M 検証）・NEW vs tmi（別対象・不 import）(iii) endo 版で非空虚（collapsing map を機構で排除）。
  characterize-only（tme/tmi/cra）を質的に超える［EtTh］rigidity 機構の初 realize。
- **0.43（設計）を採らない理由**: 殺すのは μ₂（3 と素）で、IUT が要する実 ℤ₃^× 不定性の kill は依然 0＝
  機構の忠実部分ケースであって本丸でない。敵対的に 1 ノッチ下げる。
- **0.40 据え置きを採らない理由**: false-on-M 検証つき Klein 決定性＋endo KILL 機構は
  「不定性を CHARACTERIZE のみ」から「機構による endo 水準 KILL」への質的前進で、過小評価は不当。

## 結果の数値

- Σ_A = 47.62 + 12·0.42 = 52.66 → round **53**。
- `python3 tools/compute_complete_pct.py` 出力: `{"A": 53, "B": 18, "C": 41, "D": 18, "E": 42}`。
- 更新: target_ledger.json A7 status=0.42・graph-meta.json pillars.A complete_pct=53（A7 note prepend）・
  dashboard.md 二軸表 柱A complete=53%（A7 note prepend）・tools/gen_graph.py 再実行で graph.json 再生成。

## overclaim / 二重計上 / hidden-choice の総括

- overclaim: なし（μ₂/ℤ₃^× survives/no Galois/relation-not-function を明記）。
- 二重計上: なし（q3th のみ import・消費のみ・比較準同型を作らない・tmi/q3nt 不 import）。
- hidden-choice: なし（全 11 対象 [propext, Quot.sound]・∃ は Prop 内破壊のみ・witness 関数化せず）。
