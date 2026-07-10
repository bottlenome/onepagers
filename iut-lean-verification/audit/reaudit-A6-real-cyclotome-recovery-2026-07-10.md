# 独立再監査: A6 実 mono-anabelian 円分体復元（2026-07-10）

- 監査者: 独立・敵対的監査（opus・柱A・自己申告非共有・実 Lean 定義のみ）
- 対象項目: `target_ledger.json` 柱A **A6**「mono-anabelian 復元（π₁ から体/環を復元・実）」weight 14
- 前回 status: **0.5**
- 契機: 今セッションで `IUT/CyclotomeRecoveryReal.lean`（crr）が新規実装され、M334F `CyclotomeRecovery` の
  trivial-χ 実例＋外部仮説 `cycRecGeoCompatible` を実非自明 χ・実 μ・実 Gal 作用で discharge したとの主張。
  設計 `audit/A-next-leverage-scope-2026-07-10.md` §6.1 は A6 0.5→0.55 を見込む。

## 判定（監査者独自）

**A6 status 0.5 → 0.55（+0.05）。柱A complete_pct 44 → 45**（Σ(w·s)=44.0+0.05×14=44.7→丸め45）。
上限 0.6 に対し 0.55。過大でない。K̄/幾何 cyclotome・π₁ 連続指標本丸には遠い。

## 各項の自走検証と判定

### 1. フルビルド・axiom・sorry（自走）
- `export PATH="/root/lean4/bin:$PATH" && bash build.sh` → **EXIT=0・"OK: all theorems verified, no sorry."**
- 監査者自身が `lake env lean` で `#print axioms` を独立に走らせ（build.sh の一覧に依存しない）、
  次の全対象が **`[propext, Quot.sound]` のみ**であることを確認:
  crrAction / crr_exp_eq / crrRecovered / crr_recovered_nontrivial / crrIso / crr_iso_equivariant /
  crrGeoAct / crr_geo_compatible / crr_geo_recovery / crrRealCyclotomeData / crr_scope、
  および実主語 cgarAct / cgarRecChar / cmrMu / cid_galois_equivariant。
- **新規 Classical.choice 混入なし**（crr 全体・下流実主語とも propext/Quot.sound のみ）。禁止タクティク未使用。

### 2. 昇格が本物か（最重要）——外部仮説の実 discharge
- M334F `CyclotomeRecovery.lean:217-219` で `cycRecGeoCompatible GK n χ geoAct :=`
  `∀ g x, geoAct g x = zmodMul n (χ.chi g) x` が **Prop の外部仮説**として定義され、
  `cycRec_geo_recovery_hypothesis`（:224-229）は `(hyp : cycRecGeoCompatible …)` を受け取り
  `hyp g x` を返すのみ＝**本体で決して導出しない**ことをヘッダ :35-37 が明記。grep で裏取り済み。
- crr `crr_geo_compatible`（crr:223-233）は **同一の型** `cycRecGeoCompatible (galoisGroupGrp (cteExt ℓ hℓ))
  (3^ℓ) (cgarRecChar ℓ hℓ) (crrGeoAct ℓ hℓ)` を**定理として完全証明**。
  仮説スロットを別の仮説で埋めた見せかけではない: `crrGeoAct`（crr:211-215）は
  `fun σ x => cmuMap (cmrMu)(cycMuStd) (((cgarAct).act σ).map ((crrIso).map x))` として**完全に構成**され、
  証明は `crr_iso_equivariant`（作用の移送）＋`crr_iso_leftinv`（crrIso 往復消去）で閉じる。
  **結論: 型として本物の discharge。新規仮説の持ち込みなし。**

### 3. 非自明 χ の復元が本物か
- `crr_recovered_nontrivial`（crr:150-173）は `(crrRecovered).act (cgarSigma2) (class 1) ≠ class 1` を証明。
  `crrRecovered` は `cgarRecChar`（実 χ）由来。χ(σ₂)=`cgar_sigma2_exp`=2、class 2 ≠ class 1 を
  `quot_exact`＋3^ℓ∤1（`cgar_two_lt`）で分離。**本物の非自明性**。
- `crrAction`（crr:89-100）は `χ.chi g` を捻りに使い、`crr_exp_eq` は `cgarRecChar` の χ(σ) が
  実 Gal 作用 `cgarAct` の円分指数と mod 3^ℓ 一致することを示す（実 χ を使用）。
- 実主語裏取り: `cgarAct`（CGAR:83-88）は `cgarRestrict`＝**実体自己同型 σ.val.toFun の μ_{3^ℓ} への制限**、
  `cgarSigma2`＝`cciFromUnits ⟨2,…⟩`＝**ζ→ζ² を送る実 Galois 自己同型**、
  `cgarRecChar`＝`cycRecCharOfAction … cgarAct`＝その実作用から抽出した実円分指標。すべて実主語。

### 4. 同変同型が本物か
- `crr_iso_equivariant`（crr:194-204）は M443F `cid_galois_equivariant`（一般定理・
  CyclotomeIdentification.lean:303、hchar 仮定下で cmuMap が G-同変）へ
  **実主語（galoisGroupGrp・cycMuStd/cmrMu・crrAction/cgarAct）を代入**し、hchar を `crr_exp_eq` で供給。
  再証明でなく実例化だが、実主語が本物ゆえ昇格として有効。
- `crrIso`＝`cidIso (cycMuStd 3^ℓ)(cmrMu) rfl`（双方向逆写像つき）。`cmrMu` は
  μ_{3^ℓ}={y∈ℚ(ζ_{3^ℓ}):y^{3^ℓ}=1}（CyclotomicMuGroupReal:62・実部分群・ℤ/n 模型でない）＝**実 μ**。
- `crr_exp_eq`（crr:109-135）は fudge でない: LHS を `zmodMul_one`（χ(σ)·class1=χ(σ)）で潰し、
  cycMuStd.log=(·%n).toNat と `crr_nat_mod_toNat`（Int/Nat cast 簿記）で mod 合流、
  `Nat.mod_eq_of_lt` で両側 mod。**cast/mod の正当な簿記のみ**。

### 5. 正直な限定の妥当性（過大主張検出）
- ヘッダ §8（crr:37-43）の限定を grep 裏取り:
  (i) 幾何側は K̄ の μ_n でなく **ℚ(ζ_{3^ℓ}) 自身の μ_{3^ℓ}**（`cmrMu`）— 分離閉包 μ_n(K̄) でも π₁ 幾何 cyclotome でもない。
  (ii) **χ の π₁^ét 位相連続指標抽出は未**（`cycRigChar` 経由で受ける・後続）。
  (iii) **p=3・Gal(ℚ(ζ_{3^ℓ})/ℚ) 固定**（G_ℚ の可解商・実 G_K/局所体でない）・A6 上限 0.6。
  いずれも消去・弱化されておらず、`crr_scope`（crr:278-284）にも保持。過大主張なし。

## 核心判定: 「外部仮説 cycRecGeoCompatible の discharge が本物か」

**本物の discharge だが、幾何内容は薄い。** 型としては真に満たしており（crrGeoAct 完全構成・
crr_geo_compatible 完全証明・新規仮説なし・axiom clean）、M334F が明示的に「決して導出しない」と
した仮説を実非自明 χ・実 μ・実 Gal 作用で定理化している点は本物の前進。

ただし敵対的に見ると、`crrGeoAct`（真の幾何作用 side）と χ=`cgarRecChar` は**同一の実 Gal 作用
`cgarAct` 由来**であり（χ は作用の円分指数として抽出）、discharge の実質は
「巡回群 μ 上の実 Gal 作用＝その作用から取った指標での冪」という **M322F 円分剛性の再表現**である。
これは π₁^ét の群論的データから独立に復元した cyclotome が真の幾何 μ_n(K̄) と G-同型になるという
**mono-anabelian の IUT 本丸ではない**。`crr_exp_eq` が近ほぼ簿記的に成り立つのも、χ が同じ作用から
定義されているため。

## 丸めの扱いと最終値
- 前進の実体は3点: (a) trivial χ≡1 実例 → 実非自明 χ（σ₂→2）、(b) 実 μ_{3^ℓ}⊂実 ℚ(ζ)、
  (c) G-同変同型、加えて (d) 外部仮説の形式 discharge。(a)(b)(c) は明確に本物・axiom clean。
  (d) は形式有効だが内容薄。総合して **+0.05（0.5→0.55）** が妥当（薄い discharge を理由に 0.6 未満に留置）。
- Σ(w·s) 柱A = 44.0 + 0.05×14 = 44.7 → **丸め 45**。`compute_complete_pct.py` 出力 `{A:45,...}` と一致。

## complete_pct への反映（本監査で更新した共有ファイル）
- `target_ledger.json`: A6 status 0.5 → 0.55。
- `graph-meta.json`: pillars.A.complete_pct 44 → 45、complete_note に A6 ラウンド追記（0.55 上限の薄い discharge 明記）、_last_round 更新。台帳計算値と厳密一致（`complete_pct_guard.sh` EXIT=0 で裏取り）。
- `graph.json`: `tools/gen_graph.py` で再生成。
- `dashboard.md`: 二軸表 A 行 44%→45%・A6 ラウンド注記追加、5柱平均 A44→A45（全体 ≈33% 据え置き）。
- `IUT/*.lean` は不変更（監査は数字のみ触る）。
