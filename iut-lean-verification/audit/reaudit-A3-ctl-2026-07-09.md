# 独立再監査 A3 — 逆極限 M3（円分塔 → profinite Gal(ℚ(ζ_{3^∞})/ℚ) 組み立て・restr witness 初 discharge）

- 日付: 2026-07-10（起票ラウンド名 2026-07-09 の継続）
- 監査者: 独立・敵対的監査（opus・実 Lean 定義のみ・実装者の自己申告は判定に用いない）
- 対象柱: A（遠アーベル / 実 π₁^ét）・項目 A3（実絶対 Galois 群 G_K = 有限 Galois 群の逆極限・weight 12）
- 前回: A3 = 0.65（`reaudit-A3-m2-2026-07-09.md`・一般 n の有限 Gal 群＋全遷移射 res_n＋compat＋全射性は揃うが**逆極限オブジェクト未組み立て**を 0.65 上限の唯一の主因と明記）
- **判定: A3 0.65 → 0.7**（設計 §4 M3 予測と一致）。**柱A% 38.6→39.2 の丸めで 39 据え置き**（status は上がるが柱%は横這い。過大主張しない）。complete_pct 主指標（柱%）は今回動かない。

---

## 0. 自走検証の証跡（自己申告に依らず監査者が実行）

### 0.1 フルビルド
```
export PATH="/root/lean4/bin:$PATH"; bash build.sh
→ EXIT=0
→ "OK: all theorems verified, no sorry."
```
生成モジュール数 591（前回 590 から +1 = CyclotomicTowerLimit.lean）。

### 0.2 #print axioms（新規 M3 対象・全て [propext, Quot.sound]）
build.sh 末尾の axiom 監査出力を目視確認。本ラウンドの新規 A3 対象は例外なく
`depends on axioms: [propext, Quot.sound]`:
```
'IUT.ctlTower'        depends on axioms: [propext, Quot.sound]
'IUT.ctlProfinite'    depends on axioms: [propext, Quot.sound]
'IUT.ctl_is_profinite' depends on axioms: [propext, Quot.sound]
```
`Classical.choice` 依存はコード全体で既存の 2 件のみ（`bi_implies_mono_classical`・
`theta_labels`＝M1-2 の意図的 choice 使用点）。**M3 の cast 簿記・反復合成
（`Hom.comp`）・`profPi1Limit` 束ねはいずれも新規 Classical.choice ゼロ混入**。
`IUT/CyclotomicTowerLimit.lean` 内に `sorry`／`admit`／`native_decide` 皆無を grep で確認。

---

## 1. ctlTower が本物・非自明・非空虚か（最重要・監査者が Lean 定義を精読）

### (A) `ctlExt`／`ctlGal`：塔の各段は実円分体 ℚ(ζ_{3^{n+1}})（∀n・本物）— **本物**
`ctlExt n := cteExt (n+1) (by omega)`。`cteExt`（`CyclotomicEmbedTower.lean`）は
`gefFieldExtension (ctsPhi n) (2·3^{n-1}) … (eitPhi_irreducible n hn)`——A1 の一般体
エンジンを Φ_{3ⁿ} で実例化した**実 IUTField 拡大**（既約性は前回監査で本物確認済み
`eitPhi_irreducible`・trivialExtension でない・base=実ℚ）。したがって塔の各段
`ctlGal n = galoisGroupGrp (cteExt (n+1))` は**実 Gal(ℚ(ζ_{3^{n+1}})/ℚ)**。K は
`ratIUTField`（コード共通の実 ℚ）。**自明塔でない実非自明円分塔**であることを確認。

### (B) `ctlStep`／`ctlRestr`：restr は本物の非自明制限（反復合成）か — **本物**
- `ctlStep n := ctrResHom (n+1) (by omega)`。`ctrResHom`（`CyclotomicResTower.lean`
  L436）は `Hom`（群準同型）で、`map = ⟨ctrRes …, ctrRes_mem …⟩`（実制限
  σ_{a mod 3ⁿ}）、**`map_mul = ctr_res_comp`**（L412・生成元一致 `cae_aut_ext`＋
  単射 `cteMap_inj`＋compat 3 連鎖で証明・fudge でない）。前回監査で本物確認済み。
  ＝**恒等/自明射でない実 Galois 制限**。
- `ctlRestrAux i (d+1) = Hom.comp (ctlRestrAux i d) (ctlStep (i+d))`、
  `ctlRestrAux i 0 = profPi1IdHom`（d=0 の同一段のみ恒等・正しい）。
  `ctlRestr {i j} (h:i≤j) = ctlRestrD i j (j-i) (Nat.add_sub_cancel' h)`。
  ＝**実制限の反復合成**（i<j で非自明）。空虚な恒等埋めではない。

### (C) `restr_self`／`restr_comp` witness は本物に証明されているか — **本物（cast を誤魔化していない）**
- `ctl_restr_self`（L110）: `ctl_restr_selfD` へ帰着し `subst hd; rfl`。d=0（同一段）で
  `profPi1IdHom` の恒等作用＝**proof-irrelevance のみ**（sorry/admit なし）。
- `ctl_restr_comp`（L172）: `ctl_restr_compK`（subst 1 回）→ `ctl_restr_comp_aux`
  （L144・差分 e の**帰納**）。核は `ctl_restr_step`（L130・単段 peel）で、最上段の
  `ctlStep m` を剥がして帰納仮説に落とす。**結合律 cast も transport も使わず**、
  `ctlRestrD_congr`（proof-irrelevance で差分値一致⇒制限一致）と `ctl_restr_stepD`
  （`subst; rfl`）だけで閉じる。監査者が各補題の証明本体を精読し、`sorry`／不正な
  `defeq` 濫用／`admit` が無いことを確認。帰納は e に関して正しく回っている
  （zero 枝＝`ctl_restr_self`、succ 枝＝両側 peel で ih に帰着）。**空虚でない実証明**。

### (D) `ctlProfinite := profPi1Limit ctlTower` は実際にこの非自明塔の逆極限か — **本物**
- `profPi1Limit T := limitGrp (profPi1System T)`（`ProfinitePi1.lean` L124）。
  `profPi1System T := natSystem (fun n => galoisGroupGrp (T.ext n)) (fun h => T.restr h) …`
  ＝塔の**制限準同型 T.restr を推移射 t** に持つ逆系。
- **決定的確認**: `limitGrp S`（`Profinite.lean` L167）の担体は
  `{ s : ∀ i, (S.G i).carrier // Compatible S s }`、`Compatible S s := ∀ {i j} (h),
  (S.t h).map (s j) = s i`。すなわち**担体条件が遷移射 S.t h = ctlRestr h を実際に
  使う**（積 Πではなく真の逆極限）。よって `profPi1Limit ctlTower` は ctlTower の
  非自明制限の下での整合族の群＝**この非自明円分塔の真の逆極限** lim Gal(ℚ(ζ_{3^{n+1}})/ℚ)
  = Gal(ℚ(ζ_{3^∞})/ℚ)。ctlTower を実引数に取っていることを確認。
- `ctl_is_profinite`（L202）は `profPi1_is_profinite ctlTower` の**実適用**（各射影核が
  開部分群＋開部分群系が 1 の近傍基）。ctlTower を実引数に取る。

### (E) 従来との差の裏取り（grep）— **ctlTower が初の非自明 discharge**
コード全体の `ProfinitePi1Tower` 具体インスタンス（`: ProfinitePi1Tower where`）は:
- `profPi1_trivialTower`（`ProfinitePi1.lean` L259）: ext=trivialExtension・restr=id・
  restr_self/comp=`rfl`＝**自明塔** lim Gal(ℚ/ℚ)=1。
- `algCloProfTower (T : AlgCloTower)`（`AlgClosureColimit.lean` L377）: restr/restr_self/
  restr_comp は**すべて引数 T のフィールド**（T.restr…）。`AlgCloTower`（L110）は
  restr/restr_self/restr_comp を**structure フィールド（＝仮説 witness）**として持つ抽象塔。
  具体 `AlgCloTower` 実例は `algCloTrivialTower`（L554・restr=id・rfl）のみ。
- `ctlTower`（`CyclotomicTowerLimit.lean` L185）: ext=∀n 実円分体・restr=実制限反復合成・
  **restr_self/restr_comp を本物に証明**。

⇒ `ctlTower` は**非自明∀n 円分塔で restr witness を本物に埋めた初のインスタンス**。
前回監査残欠 (i)「逆極限オブジェクト未組み立て・ProfinitePi1Tower.restr 未接続」は
**実際に解消されている**（見せかけの自明塔でない）。

---

## 2. 正直な限定の妥当性（過大主張がないか・grep で裏取り）

ヘッダ記載の限定 (i)–(iv) はいずれも**正しく**、過大主張は認められない:

- **(i) p=3・ℚ 上の円分塔の忠実な部分ケース** — 正しい。
- **(ii) 射影の全射性（整合族の持ち上げ／Mittag-Leffler）は未証明** — 監査でも裏取り。
  `ctlProfinite → ctlGal n` の射影が全射である（＝極限が各段を覆う・恒等以外の整合族が
  存在する）ことは本ファイルに無い。`ctr_surjective`（各有限段の遷移射の全射性）は
  proven だが、**それを極限へ持ち上げる論法（Mittag-Leffler）は未形式化**。よって
  極限の非退化（`ctlProfinite` が恒等族以外を持つこと）は機械証明されていない。
  ＝**0.7 に留め 0.7 を超えない主因**。
- **(iii) レベル同型 Gal(L_n/ℚ)≅(ℤ/3^{n+1})^× と極限同型 ≅ℤ₃^×（M4）は未** — 裏取り。
- **(iv) 円分切片であって実 G_ℚ そのものではない** — 正しい。`ctlProfinite` は
  G_ℚ の可解商（Kronecker–Weber 部分に対応する副有限商 Gal(ℚ(ζ_{3^∞})/ℚ)）であって、
  絶対 Galois 群 G_ℚ ではない。A3 の literal target「絶対 Galois 群 G_K」には未到達。

これらは各ファイルヘッダに明記され、削除・弱化されていない（§4 規約遵守）。

---

## 3. 判定の根拠（0.7 が妥当・0.7 を超えない・据え置きでない）

前回 0.65 の上限理由は**唯一**「逆極限オブジェクト未組み立て（残欠 i）」だった。今回、

1. **A3 の literal target「有限 Galois 群の逆極限＝実プロファイナイト群」オブジェクトが、
   実非自明円分塔の上に本物・非空虚・choice-free で組み上がった**（restr witness の初
   discharge・profinite 位相込み）。前回明示された唯一の cap 理由の discharge。
2. `profPi1Limit`／`profPi1_is_profinite` は一般 `ProfinitePi1Tower` に対する本物の建設で、
   それを**具体の非自明塔に初めて実インスタンス化**した（自明塔から実円分塔への飛躍）。

status スケール（0.5=忠実な部分ケース／0.7=部分ケースを質的に超えるが満点未満）に照らし、
「一般 n の全遷移系を持つが極限は未組み立て（0.65）」から「実非自明塔の逆極限
プロファイナイト群を本物に組み立てた（profinite 位相込み）」への飛躍は 0.65 を明確に
上回り、設計 §4 M3 予測 0.7 と一致する。

一方、**0.7 を超えない**理由は明確:
- 射影全射性（Mittag-Leffler）未証明＝極限の非退化が未形式化。
- レベル/極限の群同型 ≅ℤ₃^×（M4）未達。
- 円分切片であって実 G_ℚ ではない（A3 の literal target「絶対 Galois 群」未到達）。

0.68 等の更に保守的値も検討したが、(a) 前回の唯一の cap 理由が本物・非空虚に解消され、
(b) 一般 M3 建設の初の非自明インスタンス化という質的段階であり、(c) 設計予測 0.7 と
一致することから、**0.7 が適正**。据え置き 0.65 は今回の質的飛躍（逆極限オブジェクトの
本物組み立て）を反映せず不正直。過大評価（>0.7）は上記 3 未達で不可。**0.7 を確定**。

## 4. complete_pct への反映・丸めの正直な扱い

- ledger: A3 status 0.65 → **0.7**（weight 12 不変）。
- `python3 tools/compute_complete_pct.py` → **A: 39（据え置き）**。
  柱A Σ(w·s)/Σw = 39.2/100（前回 38.6/100）。round(38.6)=39・round(39.2)=39 で
  **丸めの結果、柱A% は 39 のまま動かない**。**status は 0.65→0.7 と上がるが柱%は横這い**。
  正直に「complete_pct（柱%）0 前進（status 昇格・丸め閾を越えず）」と記す。
- graph-meta.json: `pillars.A.complete_pct` は 39 のまま（ledger 由来値と厳密一致・
  `complete_pct_guard.sh` の graph-meta=台帳一致を満たす）。`complete_note`／`_last_round`
  を M3 ラウンドで更新。
- graph.json 再生成（`tools/gen_graph.py`・modules=591 edges=1116）。graph.json は
  構造データのみで pct を埋め込まない。
- dashboard.md 二軸表 A 行: % は 39% 据え置き・M3 ラウンド記述を追記（status 昇格＋柱%
  横這いを明記）。他柱（B18/C41/D18/E42）不変。総合 ≈32%（5 柱平均 A39/B18/C41/D18/E42）不変。

コード（IUT/*.lean）は不変更。共有ファイルは監査確定分（ledger／graph-meta／graph.json／
dashboard／本監査 doc）のみ更新。
