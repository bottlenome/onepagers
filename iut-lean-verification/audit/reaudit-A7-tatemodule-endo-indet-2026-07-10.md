# 独立再監査 A7（深化） — 実 Tate 加群 T=ℤ₃(1) の End 完全分類・自己同型不定性の正確な特徴付け

日付: 2026-07-10 ／ 監査者: 独立・敵対的（親の自己申告・設計 doc 非共有・自走検証）
対象項目: `target_ledger.json` 柱A **A7**（weight 12）
対象ソース: `IUT/TateModuleEndo.lean`（A7d・prefix tme）／`IUT/TateModuleIndeterminacy.lean`（A7e・prefix tmi）
前回 status: **0.35**（reaudit-A7-real-cyclotomic-rigidity-2026-07-10.md・据置理由=(1)剛性がレベル単位・初等 (2)cra_indeterminacy が (ℤ/3^ℓ)^× 不定性の残存宣言止まり）
**判定: A7 0.35 → 0.40**（design 見込み 0.42–0.45 を敵対的に据える）
**柱A%: 48 据え置き**（Σ_A = 47.74 → 48.34・いずれも banker's round 48）

---

## 0. 検証方法（自走・親の申告に依拠せず）

- `export PATH="/root/lean4/bin:$PATH"` で **`bash build.sh` フル実行**。
- A7d/A7e の Lean 定義本体を全文精読（ヘッダ主張は無視・def/structure/theorem 実体のみで判定）。
- 主対象が身代わりでないことの裏取りとして依存実基盤（tmzLimit=limitGrp tmzSystem・tmzG n=cmrGrp(n+1)=実 μ_{3^{n+1}}・zpsLimit=limitGrp zpsSystem・zpuGrp/zpuInv・Compatible/limitGrp・cliChar）を精読。
- **load-bearing 18 対象の #print axioms を自作 scratch（IUT/Ax.lean）で独立実行**（build.sh の列挙に依存しない）・実行後 scratch/olean 削除。

### 検証結果（自走証跡）

- **`bash build.sh` → `OK: all theorems verified, no sorry.`**（成功行確認・EXIT 0）。
- **自作 #print axioms（18/18 = [propext, Quot.sound] のみ）**:

```
'IUT.tme_ker_pow' depends on axioms: [propext, Quot.sound]
'IUT.tme_ker_preserved' depends on axioms: [propext, Quot.sound]
'IUT.tmeRootFam_compat' depends on axioms: [propext, Quot.sound]
'IUT.tme_endo_pow' depends on axioms: [propext, Quot.sound]
'IUT.tme_char_compat' depends on axioms: [propext, Quot.sound]
'IUT.tme_endo_ext' depends on axioms: [propext, Quot.sound]
'IUT.tmeEndoData' depends on axioms: [propext, Quot.sound]
'IUT.tmi_endo_gal_commute' depends on axioms: [propext, Quot.sound]
'IUT.tmiFromUnits' depends on axioms: [propext, Quot.sound]
'IUT.tmi_from_units_iso' depends on axioms: [propext, Quot.sound]
'IUT.tmi_aut_classify' depends on axioms: [propext, Quot.sound]
'IUT.tmi_units_inj' depends on axioms: [propext, Quot.sound]
'IUT.tmi_act_char' depends on axioms: [propext, Quot.sound]
'IUT.tmi_unit_of_iso' depends on axioms: [propext, Quot.sound]
'IUT.tmiIndeterminacyData' depends on axioms: [propext, Quot.sound]
'IUT.tmi_pow_char' depends on axioms: [propext, Quot.sound]
'IUT.tmzLimit' depends on axioms: [propext, Quot.sound]
'IUT.zpsLimit' depends on axioms: [propext, Quot.sound]
```

**Classical.choice / sorryAx は 18 対象すべての推移的閉包に皆無。**

---

## 1. 構造化ルーブリック出力

### A7d = `IUT/TateModuleEndo.lean`（tme）
- **classification**: real
- **principal_object**: 実 Tate 加群 T = ℤ₃(1) = `tmzLimit` = `limitGrp tmzSystem`（実 μ_{3^{n+1}}=`cmrGrp(n+1)` 塔の真の逆極限）の**任意の抽象群自己準同型 f:T→T の完全分類**（`tme_endo_pow`／`tme_char_compat`／`tme_endo_ext`）。
- **is_it_a_stand_in**: no。`limitGrp` の担体は Compatible 整合族 subtype（成分積でない真の逆極限・Profinite.lean:163-190 精読）、`tmzG n=cmrGrp(n+1)` は実円分体 ℚ(ζ_{3^{n+1}})=ℚ[x]/(Φ) 内の実 3^ℓ 乗根群（A3/A7b 監査確定の実対象）。Nat/Bool/Fin の身代わりでない。
- **self_declared_external**: なし（`_model_scope` で核対象を外部と自認していない）。honest 限定は「mono-theta 剛性は 0」「p=3 円分切片」「自動連続性は代数版」「End≅ℤ₃ 環同型は未接続」で、これは核対象でなく scope の明示。
- **moves_complete_pct**: yes（実対象上の新規極限レベル定理・下記 §2）。
- **evidence**: `tme_ker_pow`(194)／`tmeRootFam`(137)＋`tmeRootFam_compat`(144)／`tme_ker_preserved`(226)／`tme_endo_pow`(316)／`tme_char_compat`(358)／`tme_endo_ext`(388)／`tmeEndoData`(420)。

### A7e = `IUT/TateModuleIndeterminacy.lean`（tmi）
- **classification**: real
- **principal_object**: T=ℤ₃(1) の**自己同型群 Aut(T) が実 ℤ₃^×=`zpsLimit`（実 (ℤ/3^{n+1})^× 逆極限）に消去形で同定**（`tmi_aut_classify`＋`tmi_units_inj`）＋同変性条件の空性（`tmi_endo_gal_commute`）。
- **is_it_a_stand_in**: no。`zpsLimit=limitGrp zpsSystem`・`zpsG n=zpuGrp(n+1)`＝(ℤ/3^{n+1})^×、逆元は choice-free Hensel 再帰 `zpuInv`（Zmod3PowUnits.lean:62 精読・関数・∃仮説でない）。真の ℤ₃^× 逆極限。
- **self_declared_external**: なし。honest 限定「不定性を KILL せず CHARACTERIZE のみ」「cra_indeterminacy は消さず並置」「位相/環同型は未」は scope 明示で核対象の外部化でない。
- **moves_complete_pct**: yes（実 ℤ₃^× への正確な同定＝前回残存宣言ディスカウントの解消）。
- **evidence**: `tmiFromUnits`(227)／`tmi_from_units_iso`(238)／`tmi_aut_classify`(276)／`tmi_units_inj`(305)／`tmi_endo_gal_commute`(130)／`tmi_act_char`(149)／`tmi_unit_of_iso`(207)／`tmiIndeterminacyData`(358)。

---

## 2. 前回 2 ディスカウントに正面から答えているか（本監査の主判定）

### 2.1 「剛性がレベル単位・初等」→ A7d は**極限レベル・非初等**（genuinely 解消）
- `tme_ker_pow`: level n 自明な y は T 内の 3^{n+1} 乗。**witness `tmeRootFam` は Nat 除算の閉じた式**（ζ_{k+1}^{find(y_{k+n+1})/3^{n+1}}）で `sorry`/`Classical.choice`/∃仮説でない。flagged hard core `tmeRootFam_compat`（整合族性）は `tme_div_mod_helper`（div/mod 実簿記）＋`tme_find_dvd`（TME-1 可除性）＋`tmz_find_pow`＋`cra_pow_reduce` で**実証明**（精読で穴なし確認）。
- `tme_ker_preserved`: **任意の抽象 Hom f:T→T が ker proj_n を保つ**。証明は tme_ker_pow で y=z^{3^{n+1}}→f y=(f z)^{3^{n+1}}→成分 n で位数 3^{n+1} 消去（cra_pow_ord）。位相・連続性仮定なしの抽象 Hom が自動降下する＝**「自動連続性」の代数版**。
- **非再輸出の確認**: `tme_endo_pow` は `tme_level_map`（→tme_ker_congr→tme_ker_preserved→tme_ker_pow＝可除性フィルトレーション）で抽象 Hom をレベルに降ろした**後で** `cra_endo_pow` を消費する。cra_endo_pow はレベル単位の初等剛性だが、それを適用できる `tmeLevel f n` を genuine な群自己準同型として構成する段（自動降下）が新規の極限内容で、これがなければレベル分類に到達できない。**主役は T 側の降下であり、cra の再輸出ではない。→ 前回ディスカウント(1)を genuinely 解消。**

### 2.2 「不定性は残存宣言止まり」→ A7e は**Aut≅実 ℤ₃^× を正確に特徴付け**（genuinely 解消）
- `tmi_aut_classify`: 両側可逆 f はちょうど 1 つの実単元 u∈`zpsLimit` から来る。**witness u は各段 tmeChar f n%3^{n+1} の閉じた式**（¬3∣は tmi_unit_of_iso・整合は tme_char_compat）。∃ は Prop ゴール内のみ・choice 不使用。
- `tmi_units_inj`: tmiFromUnits u=tmiFromUnits v ⟹ u=v（ζ 生成元で cci_indexG）。→ 両者で **Aut(ℤ₃(1)) ≅ 実 ℤ₃^× の消去形同型**を pin。
- `tmi_endo_gal_commute`: 任意 f と実 Galois 作用 tmzActHom s が可換。両者 Hom ゆえ tme で成分冪・Nat.mul_comm。**同変性条件が End(T) を一切絞らない＝不定性がちょうど ℤ₃^× であることの正確な意味**（非空虚な内容）。`tmi_act_char` で Gal 作用の指数族＝χ=cliChar と同定。
- `cra_indeterminacy` は**消さず並置**（tmi ヘッダ・§4 規約遵守を確認）。→ 前回の「残存宣言止まり」を、正確な特徴付けの積み増しで **genuinely 解消**。

### 2.3 二重計上チェック
- 使用対象 tmzLimit（A7b）・zpsLimit/cliChar（A3-M4）・cgarAct（A7c）は既算入。だが load-bearing な新規定理は**すべて T の End/Aut に関する新内容**（可除性フィルトレーション・自動降下・End 完全分類・Aut≅ℤ₃^×・同変性空性）で、zps/cli は同定ターゲット/χ としての**正当な再利用**（タスク明示許容）。A5(q3tp) は不使用。**二重計上なし。**

### 2.4 過大主張チェック
- 不定性を KILL しない（CHARACTERIZE のみ・mono-theta 剛性 0）を honest に明記。位相・full G_{ℚ₃}・一般 p・ẑ(1)・End≅A2 z3 環同型のいずれも主張せず。**過大主張なし・honest 限定完備。**

---

## 3. status 判定（0.40）と根拠

**0.35 → 0.40。** 前回据置の 2 ディスカウントは両方 genuinely・choice-free・非空虚・非二重計上に解消（§2）。これは 0 前進でも token でもない実質前進。前回、この 2 ディスカウントが design 0.4 を 0.35 に引いた（1 ノッチ 0.05）ため、その genuine 回復＋極限レベル深化分で 0.40。

**design 0.42–0.45 を採らず 0.40 に据える（＝柱A を 49 に上げない）敵対的理由**:
1. **mono-theta 円分剛性（不定性を殺す幾何的剛性・A7 が最終的に指す IUT 荷重）は依然ちょうど 0**。本件は不定性を CHARACTERIZE するのみで KILL しない——`_status_scale` の 0.5「実対象の忠実な部分ケース」は mono-theta 剛性の部分ケースを要し、本件はその特徴付け（並行対象）で該当しない。
2. **内容は soft algebra**（torsion 可除性フィルトレーション＋可換群冪写像＋Hensel 逆元）で、自動連続性も torsion 塔上の可除性経由の軽い議論。深い剛性ではない。
3. **同一 p=3 円分切片対象の深化**であって G_ℚ・局所 G_{ℚ₃}・K̄/幾何 cyclotome へ未拡張。

0.42 は「両条件が real・非空虚・clean・ディスカウント解消なら defensible」という基準を満たすが、characterize-not-kill が本質で mono-theta=0 が不変ゆえ敵対的に 1 段据える。0.38 未満を採らないのは 2 ディスカウントの genuine 解消を過小評価しないため。**→ 0.40。**

---

## 4. 反映

- `target_ledger.json`: 柱A A7 status 0.35 → **0.40**。
- `python3 tools/compute_complete_pct.py` → `{"A": 48, ...}`（Σ_A=48.34・banker's round 48）。
- `graph-meta.json`: 柱A `complete_pct` 48 据え置き・`complete_note` に本 A7 深化ラウンド注記を prepend。
- `python3 tools/gen_graph.py` で `graph.json` 再生成（pillars=A:203 …）。
- `dashboard.md` 二軸表 柱A: 48% 据え置き＋A7 深化注記を prepend。

**柱A% 新値: 48（据え置き・status は 0.35→0.40 だが Σ_A=48.34 で round 48・正直に横這い）。**
