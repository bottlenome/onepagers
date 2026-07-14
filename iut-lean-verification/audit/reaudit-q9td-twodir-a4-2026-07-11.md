# 独立再監査記録 — A4「実 π₁^ét: E_{3⁹}[9] の二方向 π₁^ét 作用（robust-55 試行・s_A4 SET）」 (2026-07-11)

- 監査者: 独立敵対的監査エージェント (opus, Claude Code)。当該コードは監査者が書いていない。既定スタンス = SKEPTICAL。
- 対象: `IUT/Q3Etale9TwoDir.lean`（prefix `q9td`・623 行・commit 60a66c8・宣言 [実／(a) 昇格]）。
- 主張: A4 監査（`reaudit-A4-pi1-etale-tate-2026-07-11.md`・status 0.55）が §5 で名指し defer した **μ 方向 π₁ 接続（ℤ₃(1)=A7 は二重計上回避で意図的に不構成）** を discharge する。
- 依存精読（主語が本物かの裏取り）: `IUT/Q3TatePi1Etale.lean`(q3pePi1)・`IUT/TateModuleZ3.lean`(tmzLimit)・`IUT/Q3TateCurveL9.lean`(q9tl)・`IUT/Q3Mu9Completeness.lean`(q9c)・`IUT/LocalCFT.lean`(Zp/padicSystem)・`IUT/CyclotomicMuGroupReal.lean`(cmrGrp)・`IUT/CyclotomicMuTower.lean`(ctmFind)。
- 判定不使用: ヘッダの `[実／(a) 昇格]` 主張・実装者要約・目標値。判定は def/structure/theorem の本体のみ。

---

## 0. 結論（先出し）

- **crux 判定: genuine new A4 π₁^ét 内容（A7 再計上でない）＝ YES。** ただし深度は modest。
- **s_A4 = 0.55 → 0.56（+0.01・敵対的 merit 決定）。**
- **柱A complete_pct = 54 → 55（robust・Σ_A=54.64・tie でない）。** compute_complete_pct.py 出力 `{"A":55}` と graph-meta A=55 一致確認。
- 全軸 clean（build EXIT=0・全対象 #print axioms=[propext,Quot.sound]・禁止タクティク 0）。

---

## 1. ビルドと軸（監査者自身の実行）

- `lake build IUT.Q3Etale9TwoDir` → `Build completed successfully (215 jobs). EXIT=0`。
- scratch `IUT/AuditQ9tdScratch.lean` を自作し `lake env lean` で以下を列挙（実行後削除・git clean 確認済）:

```
'IUT.q9td_e9_decomp' depends on axioms: [propext, Quot.sound]
'IUT.q9td_act_faithful_lattice' depends on axioms: [propext, Quot.sound]
'IUT.q9td_act_faithful_mu' depends on axioms: [propext, Quot.sound]
'IUT.q9td_two_dir_orthogonal' depends on axioms: [propext, Quot.sound]
'IUT.q9td_lat_realize' depends on axioms: [propext, Quot.sound]
'IUT.q9td_mu_realize' depends on axioms: [propext, Quot.sound]
'IUT.q9td_exists' depends on axioms: [propext, Quot.sound]
'IUT.q9td_phi_injective' depends on axioms: [propext, Quot.sound]
'IUT.q9td_phi_surjective' depends on axioms: [propext, Quot.sound]
'IUT.q9tdLatAct' depends on axioms: [propext, Quot.sound]
'IUT.q9tdMuAct' depends on axioms: [propext, Quot.sound]
'IUT.q9td_lat_nontrivial' depends on axioms: [propext, Quot.sound]
```

**全て `[propext, Quot.sound]` のみ。Classical.choice / sorryAx は一つも無し。**
- 禁止タクティク grep: `sorry/simp/decide/by_cases/rcases/ring/nlinarith/native_decide/admit/axiom` ヒット 0（唯一の "sorry" 文字列はヘッダの日本語コメント「sorry 皆無」のみ）。`omega` 24 箇所は純 Int/Nat の付値・指数ゴール（§A 群冪算術ラッパ／§B 付値簿記）。

## 2. THE CRUX — genuine new A4 π₁ 内容か、discounted A7 再計上か

### 2.1 格子方向は実 A4a π₁^ét オブジェクトを使うか（YES）
- `q9tdLatChar : Hom (q3pePi1 3) (zmod 9)`、`map := fun γ => γ.val 2`。
- `q3pePi1 3 = ttwInverseLimit 3 = Zp 3 = limitGrp (padicSystem 3)`（LocalCFT.lean:90・TemperedTower.lean:86）＝**実 ℤ_3 逆極限 π₁^ét オブジェクト**（A4a で 0.5→0.55 の際に既に本物と認定済み・整合族担体の真の逆極限群・Nat/Bool/Fin 身代わりでない）。γ.val 2 は第 2 段成分 ∈ ℤ/3²=ℤ/9。
- `q9tdLatAct : GAction (q3pePi1 3)`、act γ p = (χ_lat(γ)·p.1, p.2)。act_one/act_mul は χ_lat の準同型性から本証明。**主語は π₁^ét であり A7 の cyclotome/tmi でない。**単一の格子方向作用は A4a 逆極限オブジェクトへの新規適用（新規作用だが対象は既算入 q3pePi1）。

### 2.2 μ 方向は tmzLimit=ℤ₃(1) を [ζ₉] 方向に genuine 接続するか（YES＝named defect の実 discharge）
- `q9tdMuChar : Hom tmzLimit (zmod 9)`、`map := fun s => mk (ctmFind 2 _ (s.val 1).val)`。map_mul は `tmz_mul_find`（離散対数の準同型性）＋`q9td_ar_modsum`（mod-9 整合）で本証明。
- `tmzLimit = limitGrp tmzSystem`（TateModuleZ3.lean:171）、`tmzG n = cmrGrp (n+1)`＝**実円分 μ_{3^{n+1}}=ℚ(ζ_{3^{n+1}}) 内の実 3^{n+1} 乗根群**の塔逆極限＝**実 ℤ₃(1)**。s.val 1 は第 1 段成分 ∈ μ_9、ctmFind はその離散対数（choice-free 走査）。
- `q9tdMuAct : GAction tmzLimit`、act s p = (p.1, χ_μ(s)·p.2)＝**ℤ₃(1) が E[9] の [ζ₉] 座標に作用**。
- A4 監査 `reaudit-A4-pi1-etale-tate-2026-07-11.md` §5 の 0.55 上限理由 (i) が明記: 「μ 方向 ℤ₃(1)=A7 は二重計上回避で意図的に不構成」。本モジュールはこの **named deferred defect を実接続で discharge**する。名指し defect の discharge は閾値漁り（threshold-shopping）でなく creditable。

### 2.3 E[9]≅(ℤ/9)² は消費 scaffold か（YES・ヘッドラインでない）
- `q9td_e9_decomp = ⟨q9td_phi_injective, q9td_phi_surjective⟩`。存在は `q9c_mu9_complete`（実 μ₉ 9 分類）を、一意性は q9tl 付値（第1成分＝格子方向分離）＋位数 9（§A q9td_order9）を消費。§B（~280 行・q9td_zv0..8 の μ₉ 正規形値・付値簿記）は A7 campaign 資産 q9tl/q9c を **INPUT** として消費する scaffold で、**A7 level-9 kill の再計上ではない**（分解は π₁ 作用が乗る土台の完全化）。モジュールは §C（π₁ 二方向作用）をヘッドラインとし §E capstone Q3Etale9TwoDirData の 7 フィールドのうち faithful_lat/faithful_mu/orthogonal/lat_realize/mu_realize が NEW A4。

### 2.4 実現（realize）＝toy でない実曲線作用か（YES）
- `q9td_lat_realize`: φ(act_lat γ p) = [3]^{χ_lat γ} · φ(p)。`q9td_mu_realize`: φ(act_μ s p) = φ(p) · [ζ₉]^{χ_μ s}。両者 q9td_cpow_hom（冪写像の準同型性）＋実曲線可換性で本証明。**φ が模型作用を実 Tate 曲線 E_{3⁹}=q9tlCurve 上の [3]/[ζ₉] 冪平行移動へ intertwine**＝作用は形式的 toy でなく実曲線作用。

### 2.5 CRUX 判定
- 格子方向は明白に A4 主語（q3pePi1 3）＝A7 純再計上は成立不能。μ 方向は A7 campaign オブジェクト tmzLimit を消費するが、それを π₁^ét の E[9] 作用（A4 主語）として packaging＋named defect discharge＝A4 固有。realize が実曲線作用を裏取り。**⟹ genuine new A4 π₁^ét 内容と判定。0 discount は不採**（landed 内容の過小評価になる）。ただし深度は modest（§3）。

## 3. 忠実性・直交性・実現の敵対的検査

- **忠実性（modest だが非空虚）**: `q9td_act_faithful_lattice`／`_mu` は「全 E[9] 元固定 ⟹ χ=(zmod 9).one」。証明は p=(1,1) で評価し mul_one で落とす。これは **ℤ/9 商上の作用の忠実性**であって ℤ_l 全体の単射ではない（ker=9ℤ_l を honest 申告）。非空虚（∀ p 仮説を p=(1,1) で実消費）だが弱い＝character が mod 9 で非自明を検出するのみ。`q9td_lat_nontrivial`（(toZp 3).map 1 の χ_lat 像 ≠ 1）で非空虚を追加検算。
- **直交性（rfl 自明）**: `q9td_two_dir_orthogonal = ⟨rfl, rfl, rfl⟩`。可換性＋各作用の他座標保存は**座標分離の定義的帰結**（格子作用は第1座標のみ・μ 作用は第2座標のみを触る設計）。real statement だが深い定理でない＝設計選択の顕在化。honest（消去/弱化なし）だが credit 深度に寄与しない。
- **実現（本モジュール最強内容）**: §2.4 の通り実曲線平行移動へ intertwine＝genuine。

## 4. s_A4 決定（Part 2・敵対的）

### 4.1 算術
- A 総重量 = 100（Σweight）。現状 A4=0.55 で Σ_A = 8·0.85+8·0.67+12·0.75+**14·0.55**+10·0.2+14·0.58+12·0.56+12·0.65+10·0.1 = 54.5（丁度タイ）→ compute（exact Fraction＋banker 丸め）→ 54。
- A4 0.55→0.56: Σ_A = 54.5 + 14·0.01 = **54.64 → round = 55（tie でなく robust・banker 丸め非依存）**。
- A4 据え置き/0 discount: Σ_A = 54.5 → 54。
- ゆえ +0.01 の genuine 付与で表示は **robust 55**。ただし表示帰結でなく merit で決定する。

### 4.2 s_A4 = 0.56 の justification
**上げ要因**:
1. A4 監査が §5(i) で名指し defer した μ 方向 ℤ₃(1) 接続を実 discharge（threshold-shopping でなく named-defect の landing）。
2. 実逆極限 2 オブジェクト（q3pePi1=ℤ_3・tmzLimit=ℤ₃(1)）上の π₁^ét 二方向作用＋実曲線 [3]/[ζ₉] 平行移動としての realize（toy でない）。

**下げ要因（+0.02/+0.03 に届かない・0.56 上限）**:
1. 直交性は ⟨rfl,rfl,rfl⟩＝座標分離の定義的自明（深い定理でない）。
2. 忠実性は mod-9 商のみ（ker=9ℤ_l honest・full π₁ 単射でない）。
3. モジュール bulk（§B ~280 行 E[9] 分解）は A7 資産 q9tl/q9c 消費の A7-adjacent scaffold＝NEW A4 の正味体積は §C/§D の π₁ 作用+realize に集中し相対的に小さい。
4. 単一曲線 E_{3⁹}・q=3⁹ 忠実部分ケース・l 進格子+μ スライスのみ（full ẑ×ẑ(1) でない）。
5. 位相/エタールサイト/G_{ℚ₃}/anabelian 逆再構成ゼロ。A4 title「実 π₁^ét」の完全形に程遠い。

**規模の較正**: 前回 A4 0.5→0.55 は逆極限オブジェクト本体＋忠実自然作用＋普遍性＋surrogate 昇格の +0.05 大玉。今回は**単一 named-defect（μ 方向）discharge＋二方向作用の packaging** ゆえ質的により小さく、half-notch（0.05）未満の **+0.01** が妥当。
- **0 にしない**: 格子方向は明白に A4 主語・μ discharge は landed・realize が実曲線作用を裏取り＝A7 純再計上でない。
- **0.02+ に inflate しない**: rfl 直交・mod-9 忠実・A7-adjacent scaffold bulk が深度を cap。robust 55 を作るために 0.56 を採ったのでなく、merit の帰結として +0.01 が 0.56 で、それが偶々 robust 55 を生む（Σ=54.64 は tie でなく float/banker 依存なし）。

### 4.3 集計
- ledger A4 status: 0.55 → **0.56**。
- `python3 tools/compute_complete_pct.py` → `{"A": 55, "B": 21, "C": 41, "D": 18, "E": 42}`。
- graph-meta.json pillars.A complete_pct=55 に更新・complete_note に本ラウンド追記。**compute 出力 A=55 と graph-meta A=55 一致確認済。**
- 他柱 (B/C/D/E) は不変更。dashboard/gen_graph は本監査の編集対象外（親統合）。

---

## 5. 過大主張チェック

- def/theorem 本体に「全 π₁^ét ẑ×ẑ(1)」「一般双曲的曲線/Spec」「位相/スキーム/エタールサイト」「anabelian 逆再構成」「G_{ℚ₃}」「E[9] = full torsion classification without inputs」の主張なし。忠実性は mod-9 商 honest・直交性は座標分解 real statement・分解は q9tl/q9c 消費と明記・q=3⁹ 部分ケース明記。ヘッダ「正直な限定」4 項（単一曲線・名指し二方向のみ・q=3⁹ 部分ケース・座標分解直交）は実スコープと一致（消去/弱化なし）。**過大主張なし。**
