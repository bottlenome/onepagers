# 独立再監査 A7 — 実円分剛性 cyclotomic rigidity（実 G_K 加群上）

日付: 2026-07-10 ／ 監査者: 独立・敵対的（親の自己申告を非共有・自走検証）
対象項目: `target_ledger.json` 柱A **A7**（weight 12）
前回 status: **0**（既存 `CyclotomicRigidity`（M322F）が「抽象 GK＋ℤ/n 模型 `cycMuStd`＋trivial χ≡1」の代理のため）
**判定: A7 0 → 0.35**（設計見込み 0.4 に対し 1 ノッチ下・敵対的ディスカウント）
**柱A%: 40 → 44**（Σ(w·s) = 39.8 + 0.35×12 = 44.0 → round 44）

---

## 0. 検証方法（自走・親の申告に依拠せず）

- `export PATH="/root/lean4/bin:$PATH"` で **`bash build.sh` フル実行**。
- 4 新規ファイル（`CyclotomicMuGroupReal`・`CyclotomicGKActionReal`・`CyclotomicRigidityAut`・`TateModuleZ3`）の Lean 定義を全文精読。
- 4 ファイルの**全 public def/theorem（63 個）を抽出**し、自作の `#print axioms` スクリプトで独立に公理検査（親の build.sh が列挙する 12 個に限定しない）。
- 昇格元（M322F `CycMuGroup`/`CycGKAction`/`cycRig_rigidity`・honest note :70-73）と、依拠する実基盤（`galoisGroupGrp`・`FieldAut`・`csaAut`/`cciFromUnits`・`cteField`/`cteExt`・`limitGrp`/`Compatible`・`cteIota`/`ctr_map_pow`）を精読して昇格の実体性を裏取り。

### 検証結果（自走証跡）

- **`bash build.sh` EXIT=0・`OK: all theorems verified, no sorry.`**（scratchpad/build_out.txt）。
- **63/63 の A7 対象が `[propext, Quot.sound]` 以下**（`cra_hom_ext`=`[Quot.sound]`、`cra_pow_mul_dist`=公理なし、残 61=`[propext, Quot.sound]`）。**新規 Classical.choice 混入は皆無**。build 全体で Choice を持つのは既存無関係モジュール（gsets 圏・GaloisTower）のみで、A7 4 ファイルの推移的閉包には現れない。
- `python3 tools/compute_complete_pct.py`（監査前）= `{"A": 40, ...}`。柱A weights 総和=100・Σ(w·s)=39.8。

---

## 1. 昇格が本物か（§2(a) 昇格の核・最重点）

### 1.1 `cmrMu`（実 μ_{3^ℓ}）— **本物（ℤ/n 模型でない）**

- 担体 `cmrCarrier ℓ hℓ = { y : (cteField ℓ hℓ).carrier // rpow (cteField ℓ hℓ).toCRing y (3^ℓ) = one }` ＝**実円分体 ℚ(ζ_{3^ℓ})=ℚ[x]/(Φ_{3^ℓ}) の中の実 3^ℓ 乗根の部分群**。`cteField` は A3 監査で確定済みの実 `gefNFIUTField (ctsPhi n) …`（実 ℚ 上の商環体・次数 2·3^{ℓ-1}）。ℤ/n 模型（`cycMuStd`=zmod n）でも抽象巡回群でもない。
- 群構造は本物: 積＝体の積（閉性 `rpow_one_mul_closed`）・逆元＝`y^{3^ℓ-1}`（`cmr_inv_root`：(y^{3^ℓ-1})^{3^ℓ}=1 を rpow 反復で証明・choice-free データ）・生成元 ζ=`ctmZeta`（=x̄・root 性は `ctr_pow_rpow`+`ctm_zeta_pow`）・離散対数 log=`ctmFind`（fuel 走査の**関数**）。
- `cmrMu` は M322F 抽象 `CycMuGroup` の**全 9 フィールド**（μ/comm/ζ/n/hn/ord/log/log_lt/pow_log/distinct）を実補題で充填。→ M322F の全定理（χ・準同型・剛性）が実 μ_{3^ℓ} を主語に回る。**判定: 実インスタンスへの昇格＝本物。**

### 1.2 `cgarAct`（実 Gal 作用）— **本物（模型でない）**

- GK＝`galoisGroupGrp (cteExt ℓ hℓ)`。精読で確認: `galoisGroupGrp` = `galoisSubgroup`（K を各点固定する `FieldAut` 全体・one_mem/mul_mem/inv_mem 実証明）の `subgroupGrp`。`FieldAut` は**全単射環準同型**（map_add/map_mul/map_one＋明示逆 invFun・left_inv/right_inv・choice-free）。`cteExt` は base=実ℚ・top=ℚ(ζ_{3^ℓ}) の実拡大。→ **実 Gal(ℚ(ζ_{3^ℓ})/ℚ) そのもの。**
- `cgarRestrict σ` = σ の μ への制限（`map = fun y => ⟨σ.val.toFun y.val, …⟩`・根の保存は `ctr_rpow_hom_gen`+`map_one`・乗法保存 `σ.map_mul`）＝**体自己同型の実制限**。`cgarAct` は M322F `CycGKAction` の act/act_one/act_mul を充填（act_one/act_mul は fieldAutId/fieldAutComp の defeq を `Subtype.ext rfl` で確定）。**判定: 実作用への昇格＝本物。**

### 1.3 `cgar_nontrivial`（非自明 χ）— **本物（trivial χ 模型を実 discharge）**

- `cgarSigma2 = cciFromUnits ⟨2,…⟩`。精読で確認: `cciFromUnits a` = `⟨cciAut a, cciAut_mem a⟩`、`cciAut a = csaAut a (zpuInvL a) …`＝**実体自己同型 σ_a**（toFun=`csaSub`＝商環上の代入 X↦X^a・map_mul 実証明 `csaSub_mul`・逆元 witness `zpuInvL` は choice-free）で `σ_a(ζ)=ζ^a`（`csaAut_zeta`/`cci_aut_zeta`）。
- `cgar_sigma2_exp`: χ(σ₂)=2（`cci_charG_csaAut`：char(σ_a)=a を `ctr_charG_spec`+`cci_indexG` で実証明）。`cgar_one_exp`: χ(1)=1（`cgar_charG_id`：id(ζ)=ζ=ζ^1）。`cgar_nontrivial`: 2≠1（`omega`）。
- ここで `ctr_charG ℓ hℓ σ := ctmFind ℓ hℓ (σ.toFun (ctmZeta ℓ hℓ))`＝σ(ζ) の ζ 冪指数の実抽出。`cgar_exp_eq` は M322F の抽象 `cycRigExp`=実 `ctr_charG` を `rfl` で合流（defeq がビルドで通ることを確認）。
- **判定: M322F の honest note :70-73「非自明な χ（σ(ζ)=ζ^a, a≠1）を与える実 Galois 自己同型の μ_n への降下は後続」を、実 σ₂(ζ)=ζ² で実際に discharge。trivial χ≡1 模型のままではない＝本物の昇格。**（旧実例 `cycRigGaloisExample`・`cycTrivialAction` は消さず、`cgarRigidityData` が実主語版として並置。）

## 2. 剛性定理が本物・非空虚か（A7c）

- `cra_endo_pow`: **任意**の群自己準同型 e（Galois 仮定なし）が e(y)=ζ^{χ(e)·log y}。証明は y=ζ^{log y}→`Hom.map_pow`→e(ζ)=ζ^{χ(e)}→`cycRig_pow_mul`。e(ζ)∈μ は担体 subtype で自動＝本物。**ただし**巡回群 μ_{3^ℓ} では「自己準同型＝冪写像」はほぼ自明な群論（生成元の像で決まる）で、深い剛性ではない。
- `cra_gal_inj`（`cae_aut_ext` 経由の単射）＋`cra_gal_realize`（可逆 e に対し σ=`cciFromUnits⟨χ(e)%3^ℓ,…⟩` が実現・witness choice-free・∃ は Prop ゴール内のみ）＝**Gal≅Aut(μ_{3^ℓ}) の消去形**。本物だが、これは「円分体の自己同型群＝(ℤ/3^ℓ)^×」という古典・初等の内容。
- `cra_char_canonical`: χ が原始根の取り替えに非依存（内在性）。本物。
- `cra_indeterminacy`: **(ℤ/3^ℓ)^× 不定性を定理として明示**（全冪写像 y↦y^a が Galois 作用と可換・`Hom.map_pow`）。**正直な限定が消されず・弱められず定理化されている**ことを確認。これは IUT 本丸（mono-theta 環境が殺す不定性）が**未達であることの当のモジュール自身による証明**でもある。**判定: 剛性は本物・非空虚だが初等（古典円分指標論）であり、IUT 荷重を担う mono-theta 剛性ではない。**

## 3. Tate 加群が本物か（A7b）

- `tmzLimit = limitGrp tmzSystem`、`tmzSystem = natSystem tmzG tmzT …`。`limitGrp` は精読で確認: 担体＝`Compatible`（遷移射 t と両立する整合族）の subtype ＝**真の逆極限**（成分積でない）。`tmzG n = cmrGrp (n+1)`＝実 μ 塔。**判定: 実 μ 塔の逆極限＝本物。**
- `tmz_proj_surjective`: 各段射影の全射（witness=定数指数族・閉じた式・choice-free）＝**非退化**。
- `tmz_iota_cube`: ι(t y)=y³。`cteIota`＝実 RingHom（map=`cteMap`＝x̄↦x̄³ stretch・map_add/mul/one 実証明）、`ctr_map_pow`：ι(ζ_n^k)=ζ_{n+1}^{3k}。→ **遷移が実 3 乗写像であることの忠実性証明書＝本物。**
- `tmz_act_char`: 作用=χ 冪（`cgar_rigidity` の成分適用）。`tmz_act_compat`（作用×遷移の可換正方形）は `cli_char_restr`（既存・実証明）の再利用で choice-free に閉じる。χ≅ℤ₃^× は `cliIsoData`（A3-M4 監査で確定済み実双方向同型）を capstone `tmzTateData` に束ねるのみ＝正当な再利用。
- **判定: T=ℤ₃(1) 逆極限・作用の χ 記述・忠実性は本物。**

## 4. 正直な限定の妥当性（過大主張の検出）

ヘッダ記載の限定を精読・grep 裏取り。**過大主張なし**:
- **円分切片限定**: G は Gal(ℚ(ζ_{3^ℓ})/ℚ)・Gal(ℚ(ζ_{3^∞})/ℚ)（G_ℚ の可解商・Kronecker–Weber 部分）であって実 G_ℚ・局所 G_{K_v} でない。**p=3・ℚ 固定**。
- **μ は円分体自身の中の μ_{3^ℓ}**: 分離閉包 K̄ の μ_n(K̄) でも π₁ の幾何的 cyclotome でもない。各段の μ は別々の体に住み K̄ を持たない。
- **T=ℤ₃(1) の限定**: 逆極限＋G 作用＋χ 記述まで。ℤ₃ スカラー（位相 ℤ₃-加群）構造は非形式化・幾何的 Tate 加群でない・遷移は指数読み替え（ι∘t=cube で担保）。
- **mono-theta 円分剛性（[EtTh]・ẑ^× 不定性を殺す幾何的円分剛性）は scope 外**。`cra_indeterminacy` が (ℤ/3^ℓ)^× 不定性の**残存を定理化**＝IUT 本丸との距離を自ら明示。
- 既存 surrogate（M322F `cycRigGaloisExample`・`cycTrivialAction`・M334F 入力）は消していない（`cgarRigidityData`/`cgarRecChar` は実主語版の並置）。

**IUT 本丸との距離**: 本 4 ファイルが閉じたのは「純群論＋実 Gal 作用の**古典**円分剛性」（Gal=Aut(μ)・χ 内在性・ℤ₃(1) 逆極限）であって、「mono-theta 環境が (ℤ/3^ℓ)^× 不定性を殺す」IUT の当の円分剛性ではない。A7=1 には遠い。

## 5. 判定と根拠（0.35）

**status 0 → 0.35**（設計 0.4 に対し 1 ノッチ下）。

昇格の実体（0 からの大きな前進）:
- 実 μ_{3^ℓ}（実円分体の実部分群）× 実 Gal(ℚ(ζ_{3^ℓ})/ℚ) の実作用 × **非自明 χ(σ₂)=2**（trivial χ 模型の実 discharge）× 剛性定理群（任意自己準同型の冪分類・Gal≅Aut(μ)・χ canonical）× 実 ℤ₃(1) 逆極限（作用=χ 冪・ι∘t=cube 忠実性）。全 63 対象 [propext, Quot.sound] 以下・新規 choice 皆無・sorry なし。全て実 A3 塔（cteField/galoisGroupGrp/cci/ctl/cli — 監査確定済み実対象）の上に立つ。

0.5 未満に留める（＝**敵対的に 0.4 から 1 ノッチ引く**）理由:
1. **剛性の内容が初等・古典**（巡回群の自己準同型＝冪写像・Aut(μ_n)≅(ℤ/n)^×・χ 内在性）であって、IUT が要する mono-theta 円分剛性ではない。
2. **モジュール自身が `cra_indeterminacy` で (ℤ/3^ℓ)^× 不定性の残存を定理化**＝IUT 荷重を担う剛性（不定性の消去）は 0。台帳 A7（weight 12）が最終的に指すのは mono-theta 剛性であり、古典円分剛性はその前提/並行対象で「target の忠実な部分ケース」（0.5 の定義）とは言い切れない。
3. **円分切片・p=3・K̄/幾何 cyclotome 不在・G_ℚ/局所体 未達**。
4. `_status_scale` の 0.5＝「実対象の忠実な部分ケース（狭い but 本物）」に対し、本件は「実対象・複数定理は本物だが、IUT 本丸の剛性機構が provably 不在で、剛性内容が初等」→ 0.5 と 0 の中間で**0.5 寄りに置かない**のが正直。

**0.45 は超えない**（タスク上限・mono-theta/幾何 cyclotome/G_ℚ 未達）。0.4 を採らないのは上記 1–2 の敵対的ディスカウント。0.3 を採らないのは 3 成分（cmr+cgar・cra・tmz）が全て実装・検証され非自明 χ が本物に立った前進を過小評価しないため。**→ 0.35。**

## 6. 反映

- `target_ledger.json`: A7 status 0 → **0.35**。`_status_scale` は既に中間値を許容（0.7 例）ため 0.35 も枠内。`_current_numerator` に本監査行を追記。
- `python3 tools/compute_complete_pct.py` → `{"A": 44, ...}`（Σ(w·s)=44.0・round 44）。
- `graph-meta.json`: 柱A `complete_pct` 40 → **44**、`complete_note` の「円分剛性は抽象GK+ℤ/n模型」を「A7=0.35（実 μ×実 Gal×非自明 χ×古典剛性×実 ℤ₃(1)・mono-theta 剛性は未）」へ実態更新、`_last_round` 更新、`status` blurb に A7 ラウンド注記。
- `python3 tools/gen_graph.py` で `graph.json` 再生成。
- `dashboard.md` 二軸表 柱A 40%→44%＋注記・5柱平均の A 値を同期。

**柱A% 新値: 44**（40→44・+4）。
