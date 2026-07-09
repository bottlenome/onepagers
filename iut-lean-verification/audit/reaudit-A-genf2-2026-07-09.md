# 柱A 再監査（A1 全域 inv・冪基底・体拡大 実装後）2026-07-09

- 監査者: 独立エージェント1名（opus・敵対的・実 Lean 定義のみ・自己申告非共有・自ら `bash build.sh` フル実行＋`#print axioms` を実行・**自ら gefNFIUTField を具体実例化して検証**）
- 契機: 前回 A1 監査（`audit/reaudit-A-genf-2026-07-09.md`）が **0.85 は過大**とした 2 つの名指し限定——(1) 逆元は∃形（全域 inv なし）・(2) {1,α,…}基底/次数=[K:ℚ] 理論なし——を解消したと主張する新規実装（F6 `GenExtFieldInv`・F9 `GenExtBasisAlpha`・F7 `GenExtTower` ＋支持部品 F1/F3/F4/F5/F8）の再評定
- 基準: `AUDIT_RUBRIC.md` / `target_ledger.json` / 前回監査（0.80・「total-inv/基底の近接を含意するが無い」ゆえ 0.85 過大）

## 結果: **A1 0.80→0.85**（A 柱 complete_pct **36→37**）

| id | 前回 | 今回 | 判定 |
|---|---|---|---|
| **A1** | **0.80** | **0.85** | **前進**（前回名指しの 2 限定を**両方本物に解消**・非空虚を実例化で確認） |
| A2–A9 | — | 変化なし | 据置（新規 F6/F7/F9 は実 ℚ[x]/(f) の体構成のみ・Galois/π₁/局所体に無関与） |

A 柱 % = round(Σ(weight×status)) は **36.4→36.8 で丸め上 37**（前回は 36.0→36.4 で丸め 36 据置だったため、今回は丸め閾値を越えて柱%が実際に動く）。`python3 tools/compute_complete_pct.py` = `{"A": 37, ...}` を監査者自身が確認。

## 監査者自走の検証証跡（自己申告非依存）

### (a) フルビルド + 公理チェック（自分の手で）
`export PATH="/root/lean4/bin:$PATH"; bash build.sh` を**フル実行 → EXIT=0**・`OK: all theorems verified, no sorry.`。build.sh の `#print axioms` 出力で、本ラウンドの全新規主対象が **`[propext, Quot.sound]` のみ**であることを監査者が目視:

```
'IUT.gefNF_mul_inv_cancel' depends on axioms: [propext, Quot.sound]
'IUT.gefNFIUTField'        depends on axioms: [propext, Quot.sound]
'IUT.gefNF268'            depends on axioms: [propext, Quot.sound]
'IUT.gefAlpha_pow_eq_mon' depends on axioms: [propext, Quot.sound]
'IUT.gefPow_indep'        depends on axioms: [propext, Quot.sound]
'IUT.gefPow_spans'        depends on axioms: [propext, Quot.sound]
'IUT.gefPowBasis'         depends on axioms: [propext, Quot.sound]
'IUT.gef_degree_eq'       depends on axioms: [propext, Quot.sound]
'IUT.gefFieldExtension'   depends on axioms: [propext, Quot.sound]
'IUT.gefRegBasis'         depends on axioms: [propext, Quot.sound]
'IUT.gefTowerDegree'      depends on axioms: [propext, Quot.sound]
```

`Classical`/`sorry`/`admit`/`axiom` の grep は F6/F7/F9/F5/F1/F3/F4/F8/GenFieldInstances の**コメント行のみ**にヒット（証明本体ゼロ）。新規 Classical.choice の混入なし。

### (b) 具体実例化（監査者が自分で書いた検証ファイルで非空虚を確認）
監査者が独自の Lean ファイルを書いて `lake env lean` で通した（LEAN_EXIT=0・全 `[propext, Quot.sound]`）:
- `gefNFIUTField ct0PS 3 ct0_bound ct0_lead _ cti_irreducible : IUTField` ＝ **次数3の実体 ℚ[x]/(x³−2)**（全域 inv 付き）
- `gefNFIUTField cq0PS 2 cq0_bound cq0_lead _ cqi_irreducible : IUTField` ＝ **次数2の実体 ℚ[x]/(x²+x+1)**（全域 inv 付き）
- `towerLawDegree (gefPowBasis ct0PS 3 …) = 3` / `… (gefPowBasis cq0PS 2 …) = 2`（rfl・**異なる次数**）
- `gefRegBasis ct0PS 3 …` が `TowerData.basisLK` スロット型に嵌り `towerLawDegree = 3`
- `(gefFieldExtension ct0PS 3 …).base = ratIUTField`（rfl・**基礎体は本物の ℚ**）

→ 主張された ∀ 構成は**空虚でない**。前回 gefField（∃形）で満たした仮説束（cti_irreducible 等）が、そのまま新しい全域 inv 体 gefNFIUTField・冪基底・体拡大を産む。

## 核心判定（各項・監査者が証明本体を読了）

### (2) F6 全域逆元は本物（前回名指し限定(1)を解消）
- `gefNFInv` は正規形担体 `GefNF f nf := {g // IsPolyBounded ratRing g nf}`（**choice-free な subtype**・Quot でなく∃抽出も無い）上の**全域関数**。中身 `gefNFInvRaw` は `ploFind`（Bool 零判定に基づく Type 値探索・choice-free）で先頭係数位置 d を取り、`pefBezout`（拡張ユークリッド関数）の Bezout 係数 t を単元 gg=psC c で正規化した剰余 `pfdRed f nf (c⁻¹·t)`。x=0 枝は `ploFind=none → 0`。**∃ を Classical.choice で選んでいない**。
- `gefNF_mul_inv_cancel : ∀ x, x ≠ 0 → mul x (inv x) = one` は本物で、**inv(0)=0 の縮退で誤魔化していない**: 証明は (i) x≠0⟹ploFind=some d、(ii) d<nf かつ f∤x.val（`pdb_dvd_deg_le`）、(iii) 既約性 hirr から Bezout gcd が単元 gg=psC c（`pib_gcd_unit_of_not_dvd`＋`pib_unit_eq_psC`）、(iv) 単元正規化で (c⁻¹s)f+(c⁻¹t)x=1、(v) 合同代数 `gnfCong` の伝播＋`pfdRed_char`（＝`field_division_unique` に帰着する剰余一意特徴付け）で red(x·c⁻¹t)=1。x≠0 の仮説を**実際に使う**（縮退枝でない）。inv(0)=0 は別途 `gefNF_inv_zero`（`ploFind_zero` 経由）。
- `gefNFIUTField : IUTField` の inv/mul_inv_cancel/inv_zero/zero_ne_one 全フィールドが上記の本物で埋まる。`IUTField` 構造は inv・mul_inv_cancel・inv_zero・zero_ne_one を**必須**とする本物の体（Field.lean:44）。`gefNF268 : Field268` も同 inv で充填。**前回の「∃形逆元」限定は NF 表示上で実際に解消**（旧 Quot 表示 M269F の has_inverses は∃形のまま——後述の正直な限定として保持）。

### (3) F9 基底・次数は本物（前回名指し限定(2)を解消）
- `gefPow_indep` は{1,α,…,α^{n−1}}の ℚ-線形結合=0 ⟹ 全係数0を**実際に閉じている**: α^i=X^i（`gefAlpha_pow_eq_mon`・i 帰納・`pfdRed_of_bounded` で簡約不要）で単項式線形結合に落とし、`pmbLinComb_zero_iff`（座標読み出しの零判定）で係数消滅。**仮説で誤魔化していない**（TowerLawBasis.indep フィールドは実証明 gefPow_indep が埋める）。
- `gefPow_spans` は任意の NF 担体元＝冪の線形結合（座標＝担体元の係数・`pmbLinComb_coeff`）。
- `gefPowBasis : TowerLawBasis` の spans/indep は上記実証明。dim=nf・vec=α の冪（`vec : Fin nf → carrier`）ゆえ、`gef_degree_eq : towerLawDegree = nf` の rfl は**自明な rfl 詐欺でなく基底要素数 dim に結びついた**次数（dim フィールドが基底ベクトル族の添字集合 Fin nf の濃度）。
- `gefAlpha_pow_eq_mon : α^i = X^i` は本物（`gefAlphaPowVal` の i 帰納・単項式積公式 `psMul_single_coeff268`）。

### (4) F7 capstone は空虚でない（体拡大の主語で確定）
- `gefFieldExtension.incl = gefIncl`（定数埋め込み psC c）で、incl_add/incl_mul/incl_one が**証明済み**（`psConstHom` 環準同型＋mul は psC·psC が次数0で `pfdRed_of_bounded` 簡約恒等）。`FieldExtension` は incl_add/mul/one を必須とする本物（FieldAutGroup.lean:176）。base=ratIUTField（実 ℚ）・top=gefNFIUTField（実 K）。
- `gefRegBasis` は `TowerLawBasis ext.base (towerLawRestrict ext (towerLawRegModule ext.top))` ＝ **`TowerData.basisLK` の型そのもの**に嵌る（監査者が自作ファイルで basisLK スロット型として型検査を確認）。別加群でお茶を濁していない。
- smul 一致 `gefRestrictSmul_eq`（制限正則加群の smul c x = K.mul(psC c) x = pfdRed(psMul(psC c) x) と F9 gefNFModule の smul=psMul(psC c) x が `pfdRed_of_bounded` で命題的一致）は本物に閉じており、これを介して F9 の span/indep を制限正則加群へ `towerLawSum_congr`/`gefSumTransfer` で移送。

## 支持部品の本物性（監査者スポットチェック）
- `pfdRed_char`（剰余の一意特徴付け）は `field_division_unique`（除法の一意性）に帰着＝本物。`pfdRed_of_bounded` はその v:=w 特例。
- `gefNFRing`（F5・乗法=掛けて f で簡約）の mul_assoc/left_distrib は合同代数 `gnfCong`（refl/symm/trans/加法/左右乗法/剰余）で両辺を同じ剰余へ落として本物に閉じる。
- `GefNF` は subtype（choice-free）で、上界 nf は型パラメータ＝∃N 抽出問題が生じない設計。

## 残る正直な限定（満点1には遠い）
1. **基礎体 ℚ 固定**（ratRing・qInv・ratIUTField.mul_inv_cancel）。一般 Field268 上への写経は未。
2. **既約性は f ごと手証明**（cti_irreducible/cqi_irreducible）。Eisenstein 等の一般判定なし。
3. **旧 Quot 表示（M269F/GEF）の has_inverses は∃形のまま**（choice-free 非存在）。全域 inv は NF 第二表示 `GefNF` 上でのみ。**この限定は消していない**（§4 正直申告の保持）。
4. **次元 well-defined 性 未証明**（`towerLawDegree` は基底 witness 依存の定義値・M281F の honest 仮説と同精神）。異なる基底で次数不変は未。
5. **塔反復未達**: basisLK スロットへの接続と [K:ℚ]=n までで、K[x]/(g) を K 上に積む塔法則の乗法性への流し込み（実 G_K への道）は後段。
6. コミット済みコードには gefNFIUTField の**具体実例化ファイルが無い**（gefField は GenFieldInstances で実例化済だが新 gefNFIUTField は未）。非空虚は監査者が実例化して確認したが、committed witness としては gefField のみ。軽微。

## 判定の根拠（0.85 が妥当・0.9 以上でない理由）
前回監査の 0.85 阻却理由は「total-inv の近接・基底/次数の近接を含意するが**無い**」だった。今回、**その 2 点が両方とも本物に建った**（全域 inv 付き IUTField/Field268 実インスタンス・spans/indep 実証明の冪基底・[K:ℚ]=n・体拡大 ℚ↪K の basisLK スロット）＝前回が 0.85 のマイルストーンとして名指しした内容にちょうど到達。よって **0.80→0.85**。一方、上記残る限定 1–5（基礎体 ℚ 固定・既約性手証明・次元 well-defined 性・塔反復・旧表示∃形の併存）が残るため **1 には遠く 0.9 でもない**——0.85 は「実対象上で当該部品がほぼ完成だが複数の正直な限定が残る」水準として妥当。過大主張しない。

## complete_pct への反映
- `target_ledger.json` A1 status 0.80→0.85（`_current_numerator` に経緯追記）。JSON valid 確認。
- `python3 tools/compute_complete_pct.py` = `{"A": 37, "B": 18, "C": 41, "D": 18, "E": 42}`（A のみ 36→37 前進）。
- `graph-meta.json` A.complete_pct 36→37・complete_note/_last_round を成果に整合更新（ledger 由来と一致）。
- `python3 tools/gen_graph.py` で graph.json 再生成（modules=569 edges=1044・valid 確認）。
- 注記: `.claude/hooks/complete_pct_guard.sh` はリポジトリに**存在しない**（`.claude/hooks/` ディレクトリ自体なし）。graph-meta の complete_pct(37) は compute_complete_pct.py の ledger 由来値と一致させた。
- コード（IUT/*.lean）は不変更（監査確定分の ledger/graph-meta/graph.json/audit doc のみ更新）。
