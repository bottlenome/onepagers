# 独立再監査記録 — A5c「実中間被覆・被覆塔 E_{qⁿ}→E_q・有限デッキ ℤ/n」 (2026-07-10)

- 監査者: 独立敵対的監査エージェント (opus, Claude Code)
- 対象: `IUT/Q3TateCoverTower.lean`（A5c・prefix q3tc・NEW）
- 依存精読（主語が本物かの裏取り）: `IUT/Q3TateCurve.lean`(q3t・A8 監査済 実 E_q)・`IUT/TemperedTower.lean`(M374F ttwDeckTower=裸 zmod)・`IUT/ThetaCovering.lean`(M369F tcvDeckGroup=裸 ℤ/l)・`IUT/GaloisCategory.lean`(GAction)・`IUT/Profinite.lean`(zmod/modCong/quot_exact)・`IUT/QuotientGroup.lean`(quotientProjN_ker)・prior A5 audit `reaudit-A5-tempered-pi1-2026-07-10.md`
- 既定スタンス: 模型/再消費（立証責任は「新規実対象追加」主張側）。ヘッダの `[実／昇格]` 主張・design doc・実装者要約・dashboard 自己分類・目標値は判定に不使用。判定は def/structure/theorem の本体のみ。
- **判定: A5 status 0.1 → 0.15**。柱A complete_pct **48 → 49**（`compute_complete_pct.py` 機械計算・下記）。

---

## 1. ビルド (build.sh tail)

`cd iut-lean-verification && export PATH="/root/lean4/bin:$PATH" && bash build.sh 2>&1 | tail -45` の末尾（A5c 対象を含む）:

```
'IUT.q3tc_q_pow' depends on axioms: [propext, Quot.sound]
'IUT.q3tcHom' depends on axioms: [propext, Quot.sound]
'IUT.q3tc_ker' depends on axioms: [propext, Quot.sound]
'IUT.q3tcDeckFin' depends on axioms: [propext, Quot.sound]
'IUT.q3tcCoverTower_exists' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```

EXIT=0、成功行 `OK: all theorems verified, no sorry.` 確認。

## 2. 監査者自身の #print axioms (IUT/AuditA5c.lean を自作・実行後削除)

`lake env lean IUT/AuditA5c.lean` の出力 (verbatim・全 14 load-bearing 対象):

```
'IUT.q3tc_q_pow' depends on axioms: [propext, Quot.sound]
'IUT.q3tcHom' depends on axioms: [propext, Quot.sound]
'IUT.q3tc_surjective' depends on axioms: [propext, Quot.sound]
'IUT.q3tc_ker' depends on axioms: [propext, Quot.sound]
'IUT.q3tcDeckFin' depends on axioms: [propext, Quot.sound]
'IUT.q3tc_deck_over' depends on axioms: [propext, Quot.sound]
'IUT.q3tc_tower_nested' depends on axioms: [propext, Quot.sound]
'IUT.q3tcTowerDeck' depends on axioms: [propext, Quot.sound]
'IUT.q3tc_tower_deck' depends on axioms: [propext, Quot.sound]
'IUT.q3tcCoverTower_exists' depends on axioms: [propext, Quot.sound]
'IUT.tateZpow_npow' depends on axioms: [propext, Quot.sound]
'IUT.q3tc_nested' depends on axioms: [propext, Quot.sound]
'IUT.q3tcShift_wd' depends on axioms: [propext, Quot.sound]
'IUT.q3tcData' depends on axioms: [propext, Quot.sound]
```

**全て `[propext, Quot.sound]` のみ。Classical.choice / sorryAx は一つも無し。** scratch (`IUT/AuditA5c.lean`) と stray olean は削除済 (`git status --short` 空＝clean)。

## 3. 身代わり / 過大主張 / 二重計上 プローブ (本体判定)

### 3.1 q3tcHom は本物の次数 n 中間被覆射か
- `q3tcHom (m n) : Hom (q3tCurve (m*n)) (q3tCurve m)`。source `q3tCurve (m*n)` = ℚ₃^×/(q3tQ(m·n))^ℤ、target `q3tCurve m` = ℚ₃^×/(q3tQ m)^ℤ。
- 恒等式 `q3tc_q_pow : q3tQ (m*n) = tateNpow q3tGrp (q3tQ m) n`（3^{mn}=(3^m)ⁿ）を本体確認: `Prod.ext`——第1成分 `q3t_npow_fst m n`＋`Int.natCast_mul`（実成分算術）、第2成分 `q3t_npow_snd_of`（単数部=1）。sorry/choice/∃仮説なし。よって source は ℚ₃^×/(qⁿ)^ℤ で中間被覆 E_{qⁿ}=既存 q3tCurve(m·n) と一致（新商構成不要）。
- `map = Quot.lift (fun a => (q3tProj m).map a) (fun a b hab => Quot.sound (q3tc_nested m n (a⁻¹b) hab))`。well-def は `q3tc_nested`（(qⁿ)^ℤ ⊆ q^ℤ を tateZpow_npow＋q3tc_q_pow で本証明）＋Quot.sound の**実 descent**（sorry/choice でない）。`map_mul` は q3tProj の map_mul 降下で本証明。
- `q3tc_surjective`（q3tProj 全射の降下）・`q3tc_ker`（quotientProjN_ker への帰着＝核ちょうど q^ℤ）も本体確認。**genuine な次数 n 中間被覆射**。

### 3.2 q3tcDeckFin : GAction (zmod n) は非空虚な実有限デッキ作用か
- `carrier := (q3tCurve (m*n)).carrier`＝**実曲線 E_{qⁿ} の carrier**（Nat/Bool/Fin 身代わりでない）。
- `act jc x = Quot.lift (fun j => q3tcShift m n (tateZpow q3tGrp (q3tQ m) j) x) (q3tcShift_wd …) jc`。jc : zmod n = ℤ/modCong n（実 ℤ の実商群）。作用 [j]·[x]=[qʲx]。
- **j mod n well-def** `q3tcShift_wd`: n∣(j−j') なら q^{−j+j'}=(qⁿ)^{−k}∈(qⁿ)^ℤ=q3tSubgroup(m·n)＝E_{qⁿ} で自明（tateZpow_npow＋q3tc_q_pow で本証明・omega）。実 mod-n well-def。
- `act_one`（[0]·x=x・tateZpow_zero＋q3tcShift_one）・`act_mul`（[i+j]·x=[i]·([j]·x)・tateZpow_add＋q3tcShift_mul）**両方本証明**。GAction 構造として非空虚・実担体上の実作用。
- **薄さ（0.15 上限の主因の1つ）**: 忠実性/自由性（0<j<n で [j] が非自明作用＝ℤ/n が真に位数 n）は**未証明**。A5a は `q3td_deck_free`／`q3td_deck_transitive` を証明していたのに対し、A5c の有限デッキは well-def GAction 止まりで非退化認証が A5a より薄い。構造は実だが「真に order-n の被覆変換群」の完全認証には至らない。

### 3.3 q3tcTowerDeck は M374F 裸 ℤ/l^k の実曲線上実現か
- `ttwDeckTower l n := zmod (l^n)`（TemperedTower.lean:43・裸 ℤ/l^n・M374F は逆系を組むのみで実曲線に未接続＝本文精読で裏取り）。M369F `tcvDeckGroup l = quotientGroupN intGrp …`（裸 ℤ/l・intGrp の商・実曲線に未接続）も同様。
- `q3tcTowerDeck (m l k) : GAction (ttwDeckTower l k) := q3tcDeckFin m (l^k)`。ttwDeckTower l k が**定義的に** zmod(l^k) ゆえ型検査が通り、裸 M374F 群が実曲線 E_{q^{l^k}} に**作用する**。`q3tc_tower_deck : (q3tcTowerDeck m l k).carrier = (q3tCurve (m·l^k)).carrier := rfl` で担体が実曲線と確認。塔入れ子 `q3tc_tower_nested`（(q^{l^{k+1}})^ℤ⊆(q^{l^k})^ℤ・q3tc_nested 特化）も本証明。**§2(a) surrogate→実 昇格が genuine に成立**（裸群の主語替えでなく、裸群が実対象に作用する形の実現）。

### 3.4 二重計上チェック（本監査の最重点）
- 既算入 0.1 の内訳（prior audit）: A5a=単一デッキ ℤ（普遍射影 ℚ₃^×→E_q・q3tdDeck:GAction intGrp）＋A5b=pro-3 ℤ₃(1)×ℤ。**A5a/A5b には (a) 中間曲線 E_{qⁿ} も (b) 曲線間の被覆射も (c) 有限デッキ群も皆無**。
- A5c の新規実対象: (a) 実中間曲線 E_{qⁿ}=q3tCurve(m·n)（E_q でも ℚ₃^× でもない別の実 Tate 曲線）・(b) 実射 q3tcHom（2 曲線間・全射・核特徴付け）・(c) 実有限デッキ作用 ℤ/n on E_{qⁿ}。**いずれも A5a/A5b に存在しない**。
- 「同じデッキ ℤ の再スライスか」への回答: ℤ/n は既算入の周期格子 ℤ の有限商であり、中間被覆は同一塔の有限段であるため**部分的に同系統**だが、有限段の実対象（別曲線・曲線間射・有限群作用）としては**新規**。単一普遍デッキ ℤ を超える「有限層」の初出現＝質的追加であり単純再消費でない。ただし増分は 0.05（half-notch）に留めるのが妥当（下記 §5）。

### 3.5 過大主張チェック
- def/theorem 本体のどこにも「位相的被覆」「全 tempered π₁」「非可換 θ」「Galois 圏/TateCoverCat 登録」「新規 ℤ_l 実現」の主張なし。q3tcHom は Grp の Hom（圏登録でない）・deck_over は E_q 上恒等被覆のみ・q3tcTowerDeck は M374F ttwDeckTower の消費（新規逆極限でない）。
- ヘッダの正直な限定 5 項（圏登録 defer(A5d)・逆極限 ℤ_l は M374F 消費・位相/解析なし・p=3 固定・裸 M374F/M369F 併設）が**実スコープと一致**（消去/弱化なし）。**過大主張なし**。

---

## 4. 構造化ルーブリック出力

### A5c (Q3TateCoverTower)
- **classification**: real (partial)
- **principal_object**: 実 Tate 曲線間の有限中間被覆 E_{qⁿ}(ℚ₃)=q3tCurve(m·n) → E_q=q3tCurve m（実射 q3tcHom）＋その実有限デッキ群 ℤ/n（GAction on 実 E_{qⁿ}）＋M374F/M369F 裸 ℤ/l^k の実曲線上実現。
- **is_it_a_stand_in**: no。主語 q3tGrp=実 ℚ₃^×・q3tQ=実 3^m・q3tCurve=実商群（A8 監査済）・zmod n=実 ℤ/n（intGrp の実商）。carrier は実曲線 carrier。Nat/Bool/Fin 濃度合わせでない。
- **self_declared_external**: 併設の M374F(ttwDeckTower・逆系)/M369F(tcvDeckGroup)/圏側 TateCoverCat 登録は残置・defer（§2(a) 昇格規約・限定(1)(2)(5)）。本モジュール core は外部自認なし。
- **moves_complete_pct**: yes（新規実対象＝中間被覆射＋有限デッキ作用＋surrogate 実現）。ただし増分は小（有限段の実現・忠実性未証明）。
- **evidence**: tateZpow_npow(:80)・q3tc_q_pow(:93)・q3tc_nested(:101)・q3tcHom(:114)・q3tc_surjective(:126)・q3tc_ker(:135)・q3tcShift_wd(:195)・q3tcDeckFin(:219)・q3tc_deck_over(:240)・q3tc_tower_nested(:262)・q3tcTowerDeck(:272)・q3tc_tower_deck(:277)・Q3TateCoverTowerData/q3tcData/q3tcCoverTower_exists(:285,:306,:317)。

---

## 5. status 決定と根拠

**A5 = 0.15**（0.1 → 0.15）。

- **0.1 を脱する理由**: A5a/A5b（既算入 0.1）に存在しなかった **(a) 実 2 曲線間の中間被覆射 q3tcHom（全射・核特徴付け・恒等式 q3tc_q_pow で中間曲線同定）** と **(b) 実有限デッキ作用 ℤ/n on 実 E_{qⁿ}** と **(c) M374F 裸 ℤ/l^k・M369F 裸 ℤ/l の初の実曲線上実現（§2(a) 昇格）** が genuine な新規実対象として入り、全 axiom clean で landing。単一普遍デッキ ℤ を超える「有限層（covers, not just the single universal deck ℤ）」の初出＝質的追加であり単純再消費でない。
- **0.5 に遠い理由（全 A5 target の忠実な部分ケースでない・上限が 0.15 の理由）**: (1) 有限デッキ q3tcDeckFin は well-def GAction だが**忠実性/自由性未証明**（A5a の deck_free/transitive より認証が薄く「真に order-n」未確立）・(2) 位相/被覆空間論ゼロ（K 点の群論的 quotient のみ・Berkovich/rigid でない）・(3) Galois 圏/TateCoverCat 実登録なし（限定(1)・A5d defer）・(4) 逆極限 ℤ_l 新規実現なし（M374F ttwDeckTower の消費・限定(2)）・(5) 依然可換・compact E_q（IUT 本丸 punctured 曲線の非可換 θ-Heisenberg は範囲外）・(6) p=3/q=3^m 固定。
- **0.1 据え置きでない理由**: 中間被覆射＋有限デッキ群という新規実対象が clean landing した前進を過小評価しないため（有限段の実現は A5a の単一 ℤ には無い質的追加）。
- **0.2 でない理由**: 増分の実質は「既算入 ℤ 塔の有限段の実対象化」であり、忠実性未証明・圏未登録・逆極限未実現・非可換未達で、half-notch（0.05）を超える質的飛躍ではない。

## 6. 集計

- ledger `target_ledger.json` pillars.A A5 status: 0.1 → **0.15**。
- Σ_A = Σ(weight×status) = A1 8×0.85 + A2 8×0.65 + A3 12×0.75 + A4 14×0.5 + **A5 10×0.15** + A6 14×0.55 + A7 12×0.4 + A8 12×0.57 + A9 0 = 48.84（分母 Σweight=100）→ round(48.84)= **49**。
- `python3 tools/compute_complete_pct.py` → `{"A": 49, "B": 18, "C": 41, "D": 18, "E": 42}`。柱A **48 → 49**。
- `graph-meta.json` pillars.A complete_pct=49 に更新・complete_note に本ラウンド前置。progress_pct=99 据え置き（新規実モジュール 1 本追加だが骨格被覆は既に飽和域）。`tools/gen_graph.py` 再生成済（modules=613)。`dashboard.md` 二軸表 A 行を 49% に同期・全体平均 A49/B18/C41/D18/E42。
