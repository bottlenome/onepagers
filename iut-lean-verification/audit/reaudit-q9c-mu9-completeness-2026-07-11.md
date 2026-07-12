# 独立敵対再監査: q9c μ₉ 完全性（IUT/Q3Mu9Completeness.lean）

- 日付: 2026-07-11
- 監査者スタンス: INDEPENDENT ADVERSARIAL AUDITOR（本コードの著者でない・既定 SKEPTICAL）
- 対象: `IUT/Q3Mu9Completeness.lean`（prefix `q9c`, 1387 行, commit 7566676）
- 申告分類: **[実／本物の先行建設(b)] FOUNDATION, complete_pct 0前進**
- 位置づけ: F-wild level-9 テータ kill 全体が唯一この結果を消費する load-bearing モジュール。よって通常より厳しく証明構造を精査した。

## 結論（VERDICT）

| 検査項目 | 判定 |
|---|---|
| 本物・非空虚な μ₉/μ₃(M) 完全性か | **YES（REAFFIRM）** |
| B6 降下は仮定でなく導出か（急所） | **DERIVED（仮定していない）** |
| q3mc 正確に2回消費・再証明なしか | **YES（B1/B7 のみ・再証明なし）** |
| axiom-clean（[propext, Quot.sound] のみ）か | **YES（8定理すべて）** |
| 禁止タクティク不使用か | **YES（grep 0）** |
| 二重計上（q3mc 再ラベル/hollow capstone） | **なし** |
| 台帳判定 | **0前進（A 据え置き 54）** |

全 1387 行を精読。ビルド `lake build IUT.Q3Mu9Completeness` は exit 0。

---

## 1. 非空虚性（statement が弱化/自明でないこと）

### q3kMu9 の定義（line 1299–1308）
真の9元選言であることを確認した。ζ₉^{3i+j} を i∈{0,1,2} について
- (ζ₃^i,0,0): `q3kOne` / `(q3rqZeta,0,0)` / `(q3rqZetaSq,0,0)`
- (0,ζ₃^i,0): `(0,q3rqOne,0)` / `(0,q3rqZeta,0)` / `(0,q3rqZetaSq,0)`
- (0,0,ζ₃^i): `(0,0,q3rqOne)` / `(0,0,q3rqZeta)` / `(0,0,q3rqZetaSq)`

の9元をちょうど列挙。弱化述語（`True`・単なる冪等・座標一つだけ）ではない。

### q9c_mu9_complete の署名（line 1311–1314）
```
theorem q9c_mu9_complete (u : q3kCar)
  (hu9 : q3kMul (q3kMul (q3kMul (q3kMul u u) u) (q3kMul (q3kMul u u) u))
      (q3kMul (q3kMul u u) u) = q3kOne) : q3kMu9 u
```
仮定は u⁹=(u³)³=q3kOne を carrier レベルで明示展開したもの。**spurious な単数仮定はない**（§6.2 の要求どおり carrier レベル）。結論は完全な `q3kMu9 u`。

### q9c_m_mu3_complete の署名（line 1176–1178）
```
theorem q9c_m_mu3_complete (x : q3kCar) (hu : q3kMul (q3kMul x x) x = q3kOne) :
  x = q3kOne ∨ x = (q3rqZeta,0,0) ∨ x = (q3rqZetaSq,0,0)
```
仮定は x³=q3kOne の carrier レベル（「x は既に単数」等の混入仮定なし）、結論は完全な3元対角 μ₃(M)。**subtle cheat（単数を仮定に入れる／弱い結論）は無い**。

---

## 2. B6 降下が「仮定で消し去られていない」ことの検証（最重要・急所）

μ₉ 結果は b=c=0 が降下から来ることに全依存する。q9c_bc_zero（line 1160）と核 q9c_bc_val（line 1067）を精読し、降下入力が**未証明仮定として q9c_bc_zero に置かれていない**こと、**循環的に b=c=0 を仮定していない**ことを確認した。

導出の連鎖（すべて x³=1 から前向きに導出）:
1. **E1′=E2′=0**: `q9c_E1_zero`/`q9c_E2_zero`（line 353–372）が `(x³).2.1 = 3·E1′` 等（`q9ci_cube_1/_2`）＋3正則 `q9ci_three_reg_L2` で、x³=q3kOne から環レベルの E1′=E2′=q3rqZero を導く。
2. **座標割り切れへの変換**: q9c_bc_val 内（line 1103–1110）で `congrArg Prod.fst/snd (q9c_E1_zero x hu)` 等を `q9cs_zero_rep_dvd` に通し、E-多項式 rep の 3^{m+1} 割り切れ hd_E1f/hd_E1s/hd_E2f/hd_E2s を得る。**これらは q9c_bc_zero の仮定ではなく、hu(x³=1) から内部で導出**。
3. **忠実性橋**: E-多項式 `q9csE1fst` 等が環元 E1′ の座標に一致することは `q9c_e1fst_valn`/`_e1snd_valn`/`_e2fst_valn`/`_e2snd_valn`（line 598–896）で、`q9cs_rq_mul_fst/snd_valn`（乗法忠実）＋`q9cs_add_valn`（加法忠実）の合成として証明済み。Int レベル多項式が環 E′ を秘密裏にすり替えていない。
4. **3∤a1（降下の駆動力）**: `q9c_a_unit`（line 902）が N(x)=1 の第1座標 level-1 = a³≡1 mod3 を強制し 3∤a1 を導く。q9c_bc_val 内では hanz からレベル m+1 rep へ射影補題 `q9c_val_proj_gen`（line 377・逆極限 coherence `w.property` を実際に使用）で伝播（hna, line 1088–1094）。
5. **降下ステップ**: `q9cs_descent_even`/`_odd`（依存モジュール）は署名を確認——level-m の b,c 座標割り切れ＋E-多項式の 3^{m+1} 割り切れ＋3∤a1 から level-(m+1) 割り切れを結論する実 content-lifting（Hensel 型）。`ha:¬3∣a1` は本質的に使用される（単数 a が b,c の content を押し上げる）。空虚でない。
6. **∩3ⁿℤ₃=0 終盤**: `q9c_zero_of_allval`（line 1058）が全レベル [0] から `Subtype.ext`＋`funext` で z3.zero を得る。逆極限の交わりが 0 という本物のエンドゲーム。

帰納法（line 1076–1157）の基底 n=0 は mod 1 で自明 [0]、m=0 は odd 単段、m=succ q は even→odd 合成。循環なし。

**判定: B6 の入力合同は x³=1 から genuinely 導出されている。REFUTE 条件（入力を秘密裏に仮定）に該当せず。**

---

## 3. q3mc 消費が正確に2回・再証明なし

grep 実測で `q3mc_mu3_complete` の出現は target 内 2 箇所のみ:
- **line 284（B1, q9c_norm_one 内）**: N(x)³=1 から N(x)∈μ₃ を得る（ノルムが μ₃）。
- **line 1208（B7, q9c_m_mu3_complete 内）**: b=c=0 で x=embed(x.1) に還元後、x.1³=1 から x.1∈μ₃(L₂) を得る端点（a³=1）。

q9c は q3mc の定理を再証明も再言明もしていない（q3rqMu3/q3mc_mu3_complete は依存 `IUT.Q3Mu3Completeness` の real 定理を import 消費）。

**B8 塔分解（line 1310）**: `q9c_cube_mul`（(xy)³=x³y³）＋`q9c_m_mu3_complete`（w=u³ に適用）＋実 Y⁻¹=ζ₃²Y² 捻り（`q9cYinv`（line 1223）・`q9c_Yinv3`：(Y⁻¹)³=embed ζ₃²）を用い、u·Y⁻¹ / u·Y を μ₃(M) に落として9元に振り分ける。9乗展開の brute force は無い。u³=ζ₃/ζ₃² 枝で Y-捻りにより μ₃·Y / μ₃·Y² の6元を回収。

---

## 4. Axioms・禁止タクティク

`#print axioms`（lake env lean で実行）:
```
q9c_mu9_complete    : [propext, Quot.sound]
q9c_m_mu3_complete  : [propext, Quot.sound]
q9c_bc_zero         : [propext, Quot.sound]
q9c_norm_one        : [propext, Quot.sound]
q9c_not_b_unit      : [propext, Quot.sound]
q9c_a_unit          : [propext, Quot.sound]
q9c_abc_zero        : [propext, Quot.sound]
q9c_exists          : [propext, Quot.sound]
```
全て **ちょうど [propext, Quot.sound]**（Classical.choice/sorryAx なし）。

禁止タクティク grep（コメント・日本語行を除外）: **0 ヒット**。sorry/admit/decide/native_decide/simp/ring/nlinarith/linarith/by_cases/rcases なし。`omega` は 30 箇所すべて純線形 Int/Nat ゴール（割り切れ・rep 差の 3ⁿ∣ 判定）に限定。§5 choice-hazard 処方に準拠: Or 破壊は `obtain`（line 299, 1208, 1315 等）、3∣ 分岐は `Decidable` インスタンスの `cases`（line 1183, 1192）、∨ 上での omega 使用なし。

---

## 5. 二重計上（double-counting）

q9c は **q3kCar**（立方代数 O_M = O_{L₂}[Y]/(Y³−ζ₃) ＝ q3rqCar³, 6 個の ℤ₃ 座標）上の **level-9 μ₉**。q3mc は **q3rqCar**（2 座標）上の **level-3 μ₃**。対象・レベルとも別物であり、q3mc の再ラベルではない。capstone `q9c_data`/`q9c_exists`（line 1379–1385）は本ファイルで新規証明した `q9c_m_mu3_complete`・`q9c_mu9_complete` を束ねるもので、hollow re-export ではない。

---

## 6. 台帳判定（Ledger Adjudication）

`target_ledger.json` の pillar-A 項目は A1–A9（実数体・実 p 進局所体・実 G_K・実 π₁^ét・実 π₁^temp・mono-anabelian 復元・実円分剛性・楕円/Tate 被覆・Belyi）の固定分母。**μ₉ 完全性を追跡する項目は存在しない**。q9c 単体はテータ群・Weil pairing・剛性を含まず何も kill しない（ヘッダ正直限定2 と一致）。§5「foundation は実 kill に CONSUMED されて初めて信用」に従い、level-9 テータ kill（q9mt/q9mr/q9mb）が未建設である以上、いずれの追跡項目の status も本物には進められない。

- **target_ledger.json**: 変更なし。
- `python3 tools/compute_complete_pct.py` → `{"A": 54, "B": 18, "C": 41, "D": 18, "E": 42}`（A=54 維持）。
- **graph-meta.json** pillar-A `complete_note` に本再監査の正直注記を追記のみ（旧値・旧注記の改変/弱化なし・§4 準拠）。progress_pct(99)/complete_pct(54)/status は不変。

**0前進 確定。表示を動かすのは本結果を消費する後続 level-9 テータ kill。**

---

## 監査で読んだもの

- `IUT/Q3Mu9Completeness.lean` 全 1387 行（B1–B9 全証明本体）
- 依存署名: `IUT/Q3Mu3Completeness.lean`（q3mc_mu3_complete）, `IUT/Q3RamifiedQuadratic.lean`（q3rqMu3）, `IUT/Q3KummerDescentSpike.lean`（q9cs_descent_even/odd）
- `target_ledger.json`（pillars.A 項目・weight）, `tools/compute_complete_pct.py`（出力）, `graph-meta.json`（pillar-A note）
- ビルド exit 0・`#print axioms`・禁止タクティク grep を自ら実行
