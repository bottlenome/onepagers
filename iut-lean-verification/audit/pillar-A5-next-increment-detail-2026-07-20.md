# A5 実 tempered π₁ 次期増分詳細化（0.27 の次の実増分の到達可能性）— 2026-07-20

**分類: [設計のみ / design-only]・tier-L 詳細化・complete_pct 0 前進（Lean コードなし・共有ファイル変更なし）・§4 規約遵守（既存の正直な限定を消さない・弱めない・過大主張しない）**

- 対象: 柱A **A5**「実 tempered π₁^temp」（weight 10・現 s_A5 = **0.27**・`target_ledger.json` 実測。
  0.27 の内訳 = 前世代 0.23 + q3tpd(N1) 位相稠密性 + q9nt(N2) wild level-9 実現・監査合算 +0.04）。
- 手法: 前回 A5 詳細（`audit/pillar-A5-tempered-pi1-deepen-detail-2026-07-20.md`）と同じ
  **disproof-first 到達可能性検査**。前回が research-blocked と裁定した各条項を敵対的に再検査し、
  **前提が失効した条項**と**依然ブロックされる条項**を峻別する。
- 結論の先出し: 前回詳細 §2.5-3 が「実 Gal(M/ℚ₃) 自己同型の建設が前提・A7 と主語が絡む・
  梯子に載せない」と裁定した **atpGroup 型半直積（tempered テータ類への実外 Galois 作用）の前提が、
  その後の A7 資産で失効した**。実 Gal(M/L₂) 生成元 σ=`q3kSigma`（Y↦ζ₃Y・環自己同型・σ³=id・
  `IUT/Q3KummerCubic.lean:504`）、その単数群化 σU=`q9mbSigmaU`（`IUT/Q3Mu9TmzBridge.lean:372`）、
  σU(ζ₉U)=ζ₉U⁴（`q9mb_sigmaU_zeta`）、位数 3 の実 Galois 群対象 `q9kdG`
  （`IUT/Q3KummerDualityReal.lean:144`）が**全て実装済み**であり、q9nt の実現 Φ₉/Ψ₉ への
  実 Galois 半直積・χ₉(σ)=4 捻りの実現が**既存資産の消費のみで建つ**。
  q9nt 自身（「奇レベル恒久ブロック」の失効）と同型の判定失効である。

---

## 0. TL;DR

| 問い | 答え |
|---|---|
| 次の実増分は到達可能か | **YES（research-blocked ではない・choice-free）** |
| 本命 | **N3: 実外 Galois 作用の tempered テータ類実現**（`IUT/Q3TemperedThetaGaloisL9.lean`・prefix `q9ng`・opus 1 枠）。実 Gal(M/L₂)=⟨σ⟩ の componentwise 自己同型 σ₉ を q9mtM 上に建て、**σ₉(Z₉)=Z₉⁴（実円分指標 χ₉(σ)=4 のテータシクロトーム実装）**・**μ₉ Weil 形式の Galois 同変性 e₉(σ₉g,σ₉g')=σU(e₉(g,g'))**・**半直積 q9mtM⋊⟨σ⟩ と外 Galois 定理 s(σ)·Ψ₉(ι(0,0,1))·s(σ)⁻¹=Ψ₉(ι(0,0,4))** を証明する。M429F `atpTw e` の骨格（(a,b,c,n)↦(a,eb,ec,n)）が e=4∈(ℤ/9)^× の**実 Galois 値**で初めて実現する。保守見込み **+0.02〜+0.03** |
| 副 | **N4: 実算術 tempered 完全列＋比較射**（`IUT/Q3TemperedArithSeq.lean`・prefix `q3ta`・sonnet/opus 1 枠・N3 と独立並列可）。Π^temp,arith=(ℤ₃(1)×ℤ)⋊ctlProfinite（q3ap の tempered デッキ版）＋**拡大の射としての比較 Π^temp→Π^ét**（q3tpEtComp の算術昇格）＋外 Galois 非自明性（q3aw の σ₂×tζ witness 消費）。クローン割引重く **+0.005〜+0.01**。§2 規約上の注意付き（§2.4） |
| 合算の保守 forecast | s_A5 0.27 → **0.29〜0.31**（敵対的下限 0.28）。Σ_A=57.40 ゆえ Δ≥+0.011 で表示 57→58 の可能性があるが、**表示 mover を事前主張しない**（監査確定後のみ） |
| research-blocked（正直申告） | (i) **tempered π₁ の定義そのもの**（Berkovich/rigid）——A5 恒久上限 0.35–0.4 不変。(ii) **level-27 tempered テータ**——q27tl/q27mt（A6 キャンペーン後続）未着で前提欠落。(iii) **full Gal(M/ℚ₃)≅(ℤ/9)^×**——L₂/ℚ₃ 層（ζ₃↦ζ₃² の M への持ち上げ）は未建設・σ-only（⟨4⟩={1,4,7}・指数 2 部分群）に留まる。(iv) **テータ部分群 q9mtGrp を保つ Galois 作用**——一様化子捻り cσ=σ(π₉)/π₉ の単数恒等式が消去律依存（§2.2） |

---

## 1. 正確なギャップ（何が有り・何が無いか）

### 1.1 A5 が現在持っているもの（0.27 の内訳・全て本体確認済み）

| 資産 | ファイル / 主定理 | 内容 |
|---|---|---|
| A5a–A5d′ | q3td/q3tp/q3tc/q3nt/q3tpec | 前回詳細 §1.1 の通り（0.23 世代） |
| N1 (q3tpd) | `IUT/Q3TemperedEtDensity.lean` | 比較射像の**位相的稠密＋真部分**（étale 側 limitTopology・228 行） |
| N2 (q9nt) | `IUT/Q3TemperedThetaClassL9.lean` | Φ₉:thetaGrp→q9mtM・Ψ₉:tpeGroup→q9mtM・シクロトーム位数ちょうど 9（`q9nt_cyclotome_order9`）・μ₉ シンプレクティック `q9nt_symplectic_real`・deck×θ≠1・**χ 捻り可視 `q9nt_chi_visible`**・正直核 `q9nt_psi_level9_collapse` |

### 1.2 タスク指定の候補 4 方向と現状の欠落（grep/精読実測）

**(a) tempered 算術完全列** 1→π₁^{temp,geom}→Π^temp→G→1（q3ap の tempered 版）。
q3ap（`IUT/Q3EtaleArithPi1.lean`・A4 計上 0.59）は Π^arith=(tmzLimit×q3pePi1 3)⋊ctlProfinite を
持つが、**tempered デッキ（離散 ℤ）版の半直積は存在しない**。素材は全て在る:
`q3tpGalAct`（`Q3TemperedPi1.lean:136`・μ 方向 tmzActHom・デッキ固定・act_one=`q3tp_gal_act_one`
既証明、act_mul は `tmzGModule.act_mul` の成分適用 2 行）、比較射 `q3tpEtComp`
（`Q3TemperedPi1Deepen.lean:137`・(z,n)↦(z, toZp n)）。**欠落**: 半直積そのもの・
完全列・外 Galois 定理・そして質的に新しいのは**拡大の射としての比較**
Π^temp⋊G → Π^arith⋊G（同変性 q3tpEtComp∘(q3tpGalAct σ) = (q3apTw σ)∘q3tpEtComp は
μ 成分双方 tmzActHom σ・デッキ/格子成分双方固定ゆえ成分ごと rfl 級）。

**(b) tempered テータ類への実外 Galois 作用（本命）**。前回詳細 §2.5-3 の文言:
「χ を外部自己同型として実現するには実 Gal(M/ℚ₃)≅(ℤ/9)^× の自己同型（ζ₉↦ζ₉^k）の
実建設が前提」——この前提の充足状況が変わった（§2.1）。**欠落**（grep 実測・§2.3 で裏取り）:
σU の消費者は q9mb 自身のみ・q9mtM への Galois 作用/半直積はコードベースに存在しない・
q9kdG の消費者は相互律連鎖（q9qc/Artin 系）のみでテータ実現には未接続。

**(c) level-27 tempered テータ（q9nt の 1 段上）**。前提となる実 μ₂₇ テータ群 q27mt・
実 E_{3²⁷} 曲線 q27tl は**未実装**（実装済みは環 opener q27k=`Q3KummerNonic.lean` と
降下 spike q27cs のみ・`audit/pillar-A6-level27-first-slice-detail-2026-07-20.md` §0 実測）。
A6 キャンペーンの q27ci→q27ps→q27tl→q27mt が閉じるまで**着手不能**——今ラウンドは defer。

**(d) tempered π₁ のテータ商構造の深化**。(b) がその実体（χ 捻りの「可視性」（非不変性）
から「実 Galois 共役としての実装」への昇格）。q9mtGrp（部分群）を保つ作用は §2.2 の
crux に依存し今回スコープ外（正直申告して ambient q9mtM 上で建てる）。

---

## 2. Disproof-first 検査

### 2.1 攻撃 1（本命 N3 の核心）: 「半直積実現は実 Gal(M/ℚ₃) 未建設でブロック」は今も真か？

**判定: σ-only スコープについて失効（FALSE になった）。** 前回詳細（2026-07-20 朝）執筆時点の
裁定は「実 Gal(M/ℚ₃) 自己同型の建設は新規建設であり credit が A3/A7 と絡む」だった。
実測では、A7 キャンペーン（q9mr/q9mb・独立監査済み）が以下を**実対象として**建てている:

| 資産 | 実体 | 所在 |
|---|---|---|
| `q3kSigma` | 実 Gal(M/L₂) 生成元 σ: Y↦ζ₃Y（**環準同型** `q3k_sigma_mul`・**σ³=id** `q3k_sigma3_id`・L₂ 定数固定 `q9mr_sigma_fixes_mu3`） | `Q3KummerCubic.lean:504–560` |
| `q9mr_sigma_zeta9` | **σ(ζ₉)=ζ₉⁴**（=q9ypY4）・σ(ζ₉)≠ζ₉ | `Q3Mu9Rigidity.lean:327/338` |
| `q9mbSigmaU` | σ の**単数群化** σU:U₃→U₃（ノルム保存 `q9mb_normBase_sigma` で well-defined・乗法 `q9mb_sigmaU_mul`・**σU(ζ₉U)=ζ₉U⁴** `q9mb_sigmaU_zeta`） | `Q3Mu9TmzBridge.lean:362–409` |
| `q9mbSigma4`/`q9mb_sigma4_exp` | 大域 χ=4 の実 Galois 元と **χ(σ₄)=4**・局所大域同変 `q9mb_equivariant_sigmaU` | 同 :415–440 |
| `q9kdG` | **実 Gal(M/L₂)=⟨σ⟩ : Grp**（位数 3・Cayley 表・全群公理証明済み） | `Q3KummerDualityReal.lean:144` |

つまり「ζ₉↦ζ₉^k の実自己同型」は k=4（と 4²=7）について**既に在り**、群対象 ⟨σ⟩ まで在る。
これらは A7 の cyclotomic rigidity 文脈（Aut(μ₉)→Aut(μ₃) 新層・β₉ 局所大域突き合わせ）で
計上済みであり、**消費する側の A5 実現（Ψ₉ 像への作用・半直積）は誰の仕事でもない空白**
（grep 実測: `q9mbSigmaU` の消費者は `Q3Mu9TmzBridge.lean` 自身のみ・`q9mtM` の消費者は
q9mr/q9mt/q9nt のみで Galois 半直積ゼロ・`q9kdG` の消費者は相互律連鎖のみ）。
q9nt・A6 crk と同型の「実装済み資産による判定失効」と裁定する。

**残る正直な限定**: ⟨σ⟩=Gal(M/L₂) は**位数 3・χ₉ 像 {1,4,7}⊂(ℤ/9)^× の指数 2 部分群**。
full Gal(M/ℚ₃)（位数 6・−1 捻り込み）には L₂/ℚ₃ 層（λ↦−λ/ζ₃↦ζ₃² の M=L₂[Y]/(Y³−ζ₃) への
持ち上げ——ターゲット提示が Y³=ζ₃² に変わるため単純クローンでない）が要る。named future。
なお q3nt_chi_invisible / q9nt_chi_visible の捻り e=−1（atpChi）とは異なる部分群であり、
**q9nt の χ 可視化の再証明・置換ではない**（−1∉{1,4,7}・別の実指標値）。

### 2.2 攻撃 2（敵対的自己検査）: componentwise 作用はテータ部分群を壊すのでは？

**判定: YES 壊れる——だから ambient で建て、部分群保存は主張しない（正直設計）。**
本設計の急所を先に自白する。q9tlMx=ℤ(v_π)×U₃ の componentwise 作用
σ̃M(n,u):=(n, σU u) は群準同型だが、これは**体の Galois 作用の「次数付き分裂スライス」**である:
真の作用は x=π₉ⁿu に対し σ(x)=σ(π₉)ⁿσ(u)=π₉ⁿ·cσⁿ·σ(u)（cσ:=σ(π₉)/π₉）で、
**cσ = 1+Y+Y²+ζ₃**（手計算: σπ₉=ζ₃Y−1=Y⁴−1=(Y−1)(Y³+Y²+Y+1)・Y³=ζ₃）という
明示単数の捻りを持つ。帰結:

- σ̃M は **q9tl3=(6,u₆)・q9tlQ=(54,u₆⁹) を固定しない**（σ(u₆)≠u₆——q9ps の要石
  3=π₉⁶·u₆（`Q3KummerPiSplit.lean:452`）に σ を当てると π₉⁶cσ⁶σ(u₆)=3 となり
  cσ⁶σ(u₆)=u₆ が真の関係）。ゆえに componentwise σ₉ は**中心化条件 q9mtMem
  （qᵃw⁹=1・`Q3Mu9ThetaGroup.lean:366`）を保存しない**。
- 保存させる「正しい」捻り作用 σ̃(n,u)=(n, cσⁿ·σU u) は建設可能だが、その正当化
  **cσ⁶·σU(u₆)=u₆** は π₉⁶ の消去律（q3kRing の domain 性——未整備）または cσ⁶ の
  閉形式 6 乗計算（禁止タクティク環境で高リスク）を要する。**crux として named future に置く**。

**それでも N3 が成立する理由（設計上の逃げ道・全て検算済み）**:
半直積とその旗艦は **ambient q9mtM（Heisenberg 担体全体）上で閉じ、部分群 q9mtGrp を要さない**。

1. σ₉ := componentwise σ̃M は **q9mtM の群自己準同型**（cocycle 積
   (c,a,w)(c′,a′,w′)=(cc′w′ᵃ, a+a′, ww′) は q9tlMx-hom＋zpow 保存（`hom_map_zpow`）で
   同変・Int スロット固定）。σ₉³=id（σ³=id の成分持ち上げ）で自己同型。
2. **σ₉(Z₉)=Z₉⁴**: Z₉=scalar(0,ζ₉U⁻¹)・σU(ζ₉U⁻¹)=(σU ζ₉U)⁻¹=ζ₉U⁻⁴（`q9mb_sigmaU_zeta`）・
   Z₉⁴=scalar((0,ζ₉U⁻¹)⁴)（`q9nt_Z9_zpow`）——スカラー準同型の自然性で on the nose。
   非自明性 σ₉(Z₉)≠Z₉ ⟸ Z₉³≠1（`q9nt_Z9_npow_ne 3`）。
3. **σ₉(Y)=Y⁴ on the nose**: Y=q9mtGZeta=((1,0),(0,ζ₉U))・a=0 ゆえ Yᵏ の cocycle は
   スカラー蓄積ゼロ（Yᵏ=((1,0),(0,ζ₉Uᵏ))・小補題 1 本）・σ₉Y=((1,0),(0,ζ₉U⁴))=Y⁴ ✓。
4. **σ₉(X)=uδ·X**（X=q9mtG3・uδ:=((one,0),(0,δU))・δU:=σU(u₆)·u₆⁻¹）: 左乗算で
   成分検算済み（uδ·X=((one,−1),(6,δu₆))=σ₉X ✓・cocycle の w^a 項は a=0 側で消える）。
   X 方向が単数平行移動 uδ だけずれる——これが分裂スライスの正直核であり、
   q3ap 正直限定 (ii)（graded split slice）と同族の帽子として並置する。
5. **Weil 同変性は membership 不要**: q9mtWeil g g′ = zpow g′.w (g.a) · zpow g.w (−g′.a)
   （`Q3Mu9ThetaGroup.lean:525`・担体全体で定義）ゆえ
   e₉(σ₉g,σ₉g′)=σ̃M(e₉(g,g′)) は hom_map_zpow＋map_mul の 2 行。
6. 半直積 q9mtM⋊⟨σ⟩（q9kdG・act: e↦id, s↦σ₉, s2↦σ₉²・act_mul は Cayley 9 場合×σ₉³=id）
   と外 Galois 定理は q3ap の確立イディオムの写経。

### 2.3 攻撃 3: N3 は A7（σU）/A4（半直積イディオム）の再ラベルでは？ 二重計上 firewall

**判定: 再ラベルでない。境界は q9nt 監査の判定基準がそのまま使える。**

- **vs A7（q9mb/q9mr）**: A7 側の主語は「Aut(μ₉)→Aut(μ₃) 新層の実現」「β₉ 橋の局所大域
  同変」——テータ群・Φ₉/Ψ₉ は登場しない。q9ng の旗艦（σ₉∘Φ₉ の χ 捻り実現・Weil 同変・
  外 Galois 共役の Ψ₉ 像上の値）は **Φ₉/Ψ₉ を消去すると命題が消滅**する。σU/q9kdG の
  定理は消費のみ（再証明 0 本）。**A7 status は主張しない**。
- **vs A4（q3ap/q3aw）**: 半直積＋外 Galois 定理の**イディオム**はクローン（割引対象として
  自己申告）。しかし G が異なり（実局所 Gal(M/L₂) vs 大域円分切片）、ターゲットが異なり
  （非可換 μ₉ テータ Heisenberg vs 可換 (ℤ/9)² スライス）、Weil 同変の主語も異なる
  （q9mtWeil＝テータ交換子のスカラー成分 vs M339F determinant 形式）。q3aw の定理を
  1 本も再証明しない。**A4 status は主張しない**。
- **vs A5 自身（q9nt）**: q9nt ヘッダ正直限定 3 が「実 Gal(M/ℚ₃)…の建設は named future
  target・A7 と主語が絡む」と**明示 defer した項目の（σ-only スコープでの）正面 discharge**。
  q3nt ロードマップの「(i) A7: Ψ 像への実 Gal 作用→mono-theta 剛性の実入口」が、
  A7 資産完成後の今、**A5 の実現主語側の仕事**として落ちてきた形。
- 敵対的相場: 「イディオム 2 度目のクローン +0.01–0.02」を下限に、質的新規
  （**A5 実現への初の実 Galois 作用**・atpTw e の実値 e=4 実現・q9nt 限定 3 の部分 discharge）
  で半ノッチ上乗せ → **+0.02〜+0.03**（§4）。

### 2.4 攻撃 4（副 N4）: tempered 算術完全列は complete_pct 0 の骨格束ねでは？

**判定: 小さいが実増分——ただし §2 規約の注意付きで従とする。** 敵対的査定
「q3ap のデッキ成分を intGrp に差し替えただけ＋q3tpGalAct の再パッケージ」は半分正しい。
残り半分（新規内容）: (i) **拡大の射としての比較** q3taComp: Π^temp⋊G→Π^arith⋊G
（q3tpEtComp の算術昇格・ι/pr/s との可換 3 角形・単射・**非全射**（q3tpEtWitness 持ち上げ））
はコードベースに存在せず、「Π^tp ⊂ Π†（稠密・真）」（[IUTchI] §2 の tempered⊂étale 算術版）の
算術レベル初出。(ii) 幾何部が**非副有限**（`theta_deck_not_finite` 継承）な G 拡大は初
（q3ap は両側 profinite）。(iii) 外 Galois 非自明性は q3aw witness σ₂×tζ の消費で実値。
それでも主構成が q3ap クローンである事実は動かず **+0.005〜+0.01**（敵対的下限 0）。
5 並列の枠が余る場合のみ着手し、ラウンド報告で「クローン主体・小増分」と正直申告する。
監査が 0 査定なら次回から同種スライスを止める（§2 規約の自己執行）。

### 2.5 research-blocked なもの（正直に列挙・梯子に載せない）

1. **tempered π₁ の定義そのもの**（Berkovich/rigid 解析被覆・位相 π₁）: N3/N4 の後も
   **A5 恒久上限 0.35–0.4 は不変**（`audit/A5-real-tempered-pi1-detail-2026-07-10.md` §6）。
2. **level-27 tempered テータ（候補 c）**: q27tl/q27mt が A6 キャンペーン（q27ci→q27ps 経由・
   `pillar-A6-level27-first-slice-detail-2026-07-20.md` §0）で未着。前提欠落——今回 defer。
   q27mt が着地したラウンドで q9nt→q27nt の写経（+0.01 級）が自動的に候補化する。
3. **full Gal(M/ℚ₃)（位数 6）**: L₂/ℚ₃ 共役の M への持ち上げは提示変更（Y³=ζ₃²）を伴う
   非クローン建設。named future（これが閉じると χ₉ 像が (ℤ/9)^× 全体になり、q9nt の
   e=−1 捻りと σ の e=4 捻りが単一の実 Galois 群に統合される）。
4. **テータ部分群 q9mtGrp を保つ Galois 作用**: §2.2 の crux（cσ⁶·σU(u₆)=u₆・消去律依存）。
   これ憖閉じると σ₉ が q9mtGrp の自己同型に落ち、mono-theta 剛性（A7）の実 Galois 入口が
   開く。named future として q9ng ヘッダに明記する。
5. **full ẑ(1)・全素数 l**: p=3 恒久スコープ。従来通り着手しない。

---

## 3. マイルストーン梯子（到達可能・2 ファイル・全 choice-free）

### N3（本命・opus 1 枠）: `IUT/Q3TemperedThetaGaloisL9.lean`（prefix `q9ng`・450–650 行）

import: `IUT.Q3TemperedThetaClassL9`・`IUT.Q3Mu9TmzBridge`・`IUT.Q3KummerDualityReal`。
共有ファイル変更なし。

| 段 | 内容 | 消費資産 | 難度 |
|---|---|---|---|
| q9ng-0 | σU の Hom 化（`q9mb_sigmaU_mul`/`_one` の束ね）・σ̃M:Hom q9tlMx q9tlMx（(n,u)↦(n,σU u)）・σ̃M³=id（`q3k_sigma3_id` の subtype/成分持ち上げ） | q9mb §8・q3k §4 | 低 |
| q9ng-1 | **σ₉:Hom q9mtM q9mtM**（componentwise・map_mul は cocycle 3 成分＝σ̃M hom＋hom_map_zpow）・σ₉³=id・自己同型（逆 σ₉²） | σ̃M | 低〜中 |
| q9ng-2（★） | **σ₉(Z₉)=Z₉⁴**（`q9mb_sigmaU_zeta`＋`q9nt_Z9_zpow`）・σ₉(Z₉)≠Z₉（`q9nt_Z9_npow_ne 3`）・一般 σ₉(Z₉ᶜ)=Z₉^{4c}（要 zpow 合成補題 q9ng_zpow_mul: (xᵐ)ⁿ=x^{mn}・唯一のやや新しい一般補題・標準帰納） | q9nt-0 系 | 中 |
| q9ng-3（★） | Yᵏ 閉形式（a=0 平行移動はスカラー蓄積ゼロ・小帰納）・**σ₉(Y)=Y⁴ on the nose**・**χ 捻りの実現**: σ₉(Φ₉(0,b,c))=Φ₉(0,4b,4c)——M429F atpTw e の骨格が実 Galois 値 e=4 で実現（q9nt_chi_visible の「可視」から「実装」への昇格） | q9nt Φ₉・q9ng_zpow_mul | 中 |
| q9ng-4（★★ 旗艦 1） | **μ₉ Weil 形式の Galois 同変性**: e₉(σ₉g,σ₉g′)=σ̃M(e₉(g,g′))（2 行）・Φ₉ 像上: [σ₉Φ₉v,σ₉Φ₉w]=Z₉^{4·ω(v,w)}（`q9nt_symplectic_real`＋q9ng-2——q3aw_weil_galois の tempered テータ版・χ₉(σ)=4） | q9mtWeil・q9nt-5 | 中 |
| q9ng-5（★★ 旗艦 2） | **半直積 q9ngArith = q9mtM ⋊ q9kdG**（act: e↦id/s↦σ₉/s2↦σ₉²・act_mul=Cayley 9 場合×σ₉³=id・群公理は q3ap AP-1 イディオム写経）・完全列（ι 単射・pr 全射・exact・正規性）・外 Galois 定理 s(g)·ι(x)·s(g)⁻¹=ι(σ₉ᵏ x) | q9kdG・q3ap イディオム | 中 |
| q9ng-6（★★★ headline） | **実外 Galois 共役はテータシクロトームを χ₉(σ)=4 倍に捻る**: s(.s)·ι(Ψ₉(ι(0,0,1)))·s(.s)⁻¹ = ι(Ψ₉(ι(0,0,4))) ≠ ι(Ψ₉(ι(0,0,1)))（外 Galois 定理＋q9ng-2＋ι 単射＋Z₉³≠1）——q9nt 正直限定 3 の σ-only discharge・大域 χ(σ₄)=4（`q9mb_sigma4_exp`）との整合注記 | q9ng-2/5 | 低（束ね） |
| q9ng-7 | 正直核: **σ₉(X)=uδ·X**（δU=σU(u₆)·u₆⁻¹・X 方向は単数平行移動でずれる＝分裂スライスの帽子）・**q9mtGrp 保存は主張しない**（§2.2 crux を named future として明記）・capstone struct/data/exists | q9tl3・q3kU.inv | 低〜中 |

新規イディオム: **q9ng_zpow_mul 1 本のみ**（標準的二重帰納・発明でない）。
残りは成分計算・transport・確立イディオムの写経。

### N4（副・sonnet/opus 1 枠・N3 と独立並列可）: `IUT/Q3TemperedArithSeq.lean`（prefix `q3ta`・250–400 行）

import: `IUT.Q3TemperedPi1Deepen`・`IUT.Q3EtaleArithPi1Weil`。§2.4 の注意付き。

| 段 | 内容 | 消費資産 | 難度 |
|---|---|---|---|
| q3ta-0 | q3tpGalAct の act_mul（`tmzGModule.act_mul` 成分適用・2 行）・半直積 Π^temp,arith=(tmzLimit×intGrp)⋊ctlProfinite（q3ap AP-1 写経） | q3tp-3・q3ap | 低 |
| q3ta-1 | 完全列・外 Galois 定理・幾何部非副有限の継承注記（両側 profinite でない初の実 G 拡大） | q3ap AP-2 | 低 |
| q3ta-2（★） | **拡大の射 q3taComp: Π^temp,arith→Π^arith**（(x,σ)↦(q3tpEtComp x,σ)・同変性は成分 rfl 級）・ι/pr/s 可換 3 角形・単射・**非全射**（q3tpEtWitness） | q3tpec | 中 |
| q3ta-3（★） | 外 Galois 非自明性: s(σ₂)·ι(tζ,0)·s(σ₂)⁻¹≠ι(tζ,0)（`q3aw_galois_moves_tzeta` 消費）・capstone | q3aw §E | 低 |

---

## 4. 保守的 status forecast と、持ち越す A5 の帽子・限定

**verdict: 到達可能（research-blocked ではない）。**

**s_A5 予測（過大主張しない・独立敵対監査が確定）**: 現 0.27 →
- N3 単独: 中央値 **+0.02〜+0.03**（半直積イディオムはクローンだが「A5 実現への初の
  実 Galois 作用・χ₉(σ)=4 の実値実装・q9nt 限定 3 の部分 discharge」で相場の上に半ノッチ）。
  敵対的下限 +0.01（「σU の輸送に過ぎない」査定——ただし §2.3 の消滅テストで反論可能）。
- N4 単独: 中央値 **+0.005〜+0.01**・敵対的下限 0（§2.4 で正直申告済み）。
- 合算中央値 **0.29〜0.31**・敵対的下限 **0.28**。前世代 soft 天井 0.28 は本判定失効
  （§2.1）により更新され、新 soft 天井 **~0.31–0.32**（残る主資産が §2.5 の blocked 群のみ
  になるため）。**恒久上限 0.35–0.4 は不変**。
- **柱A 表示**: Σ_A（ledger 実測）= 8·0.85+8·0.69+12·0.75+14·0.59+10·0.27+14·0.61
  +12·0.58+12·0.66+10·0.17 = **57.40** → 表示 57。Δs_A5≥+0.011 で Σ_A>57.5 となり
  表示 58 の可能性があるが、**監査確定前に表示 mover を主張しない**（q9nt ラウンドの
  慣行を踏襲し、報告では「監査が +0.02 以上を確定した場合のみ 58」と条件付きで書く）。

**消さない・弱めない帽子（新ファイルに必ず並置）**:
1. **A5 恒久上限 0.35–0.4**（Berkovich/rigid 位相なし・tempered π₁ の「定義」は依然外部）。
2. **σ-only Galois**: 作用は Gal(M/L₂)=⟨σ⟩（位数 3・χ₉ 像 {1,4,7}・指数 2 部分群）のみ。
   full Gal(M/ℚ₃)・実 G_{ℚ₃} は未建設（q9mb 正直限定 3 の継承・named future）。
3. **分裂スライスの帽子**: σ̃M は一様化子捻り cσ を捨てた componentwise 作用であり、
   「体 M^× の Galois 作用そのもの」ではない（q3ap (ii) と同族）。X 方向は uδ 平行移動で
   ずれる（q9ng-7 正直核）。**q9mtGrp（テータ部分群）の保存は主張しない**（cσ crux・§2.2）。
4. q9nt の正直限定（level-9 崩壊・full ẑ(1) 未達・実テータ関数 0・cuspidalization 0・
   q=3⁹ 忠実部分ケース）・q9mb/q3k/q9tl の正直限定を全て継承・並置。
5. N4 の「稠密・真」は代数的（単射・非全射）＋幾何部の q3tpd 位相文の継承であり、
   Π 全体の位相は主張しない。

**overclaim 禁止リスト**: 「tempered π₁ への G_K 作用を実現した」と書かない（σ-only・
分裂スライス）／「テータ群の Galois 剛性」と書かない（q9mtGrp 保存なし・剛性は A7 の主語）／
q9nt・q9mb・q3ap・q3aw の正直限定の消去・弱化／A4・A7 status の再主張。

---

## 5. 推奨第一実装スライスと de-risk-first

- **第一スライス（opus 1 枠）**: **N3 = `IUT/Q3TemperedThetaGaloisL9.lean`（q9ng）**。
  理由: (i) A5 の残存最大の質的空白（実 Galois × テータ実現）に直撃し増分最大、
  (ii) 新イディオムは q9ng_zpow_mul 1 本のみ・地上事実（σU(ζ₉U)=ζ₉U⁴・Z₉ 位数 9・
  Weil=交換子スカラー・q9kdG 群公理）は全て監査済み資産、(iii) σ₉(Y)=Y⁴・σ₉(X)=uδ·X・
  σ₉(Z₉)=Z₉⁴ は本設計で成分手計算済み。tier は M（opus）——半直積・transport とも
  確立イディオムで、tier-L 発明を要さない。
- **de-risk-first 項目（実装前 30 分・scratch 1 本）**: 次の 4 点だけを先にコンパイルして
  確定する: (1) σ̃M の Hom 化と σ₉ の map_mul（cocycle 3 成分・w′ᵃ 項の hom_map_zpow 通過）、
  (2) q9ng_zpow_mul の帰納骨格、(3) σ₉(Y)=Y⁴ の rfl 度（q9mb_sigmaU_zeta の subtype 層が
  どこまで definitional か）、(4) σ₉(X)=uδ·X の成分一致（q3kU.inv 経由の δU が
  素直に書けるか）。(4) が重ければ q9ng-7 の等式を「σ₉(X)·X⁻¹ はスカラー成分 one・
  a 成分 0 の単数平行移動」という成分形に弱めて出荷する（正直核の内容は不変）。
  詰まった場合のみ HELP スポットとして fable を呼ぶ。
- **並列枠**: N4（q3ta）は N3 と**ファイル・依存とも独立**で同一ラウンド並列可
  （sonnet で足りる見込み・§2.4 の正直申告をヘッダに義務付け）。残り枠は他柱
  （A4 Kummer コサイクル・A6 q27ci 等）を優先し、A5 で水増ししない。
- 統合時の共有ファイル更新（IUT.lean・build.sh・gen_graph.py PILLAR・graph-meta/dashboard・
  target_ledger）は親が一括。status 確定は独立敵対監査後（本書の見込み値を先に書き込まない）。

---

*設計: tier-L 詳細化ラウンド 2026-07-20（同日 2 本目・0.27 世代）。本書は設計のみで
complete_pct を動かさない。§1–§3 の全主張は実ファイル精読（Q3TemperedThetaClassL9・
Q3TemperedPi1/Deepen・Q3TemperedEtDensity・Q3Mu9ThetaGroup・Q3Mu9TmzBridge・Q3Mu9Rigidity・
Q3KummerCubic・Q3KummerDualityReal・Q3KummerPiSplit・Q3TateCurveL9・Q3EtaleArithPi1/Weil・
ArithTemperedPi1・Q3KummerNonic）と grep 実測（σU/q9mtM/q9kdG の消費者空白）に基づく。
σ₉ の cocycle 同変・σ₉(Y)=Y⁴・σ₉(X)=uδ·X・σ₉(Z₉)=Z₉⁴・Weil 同変は設計時に成分手計算済み。
cσ=1+Y+Y²+ζ₃（σπ₉=π₉·cσ）の crux とその消去律依存は §2.2 に正直に記録した。*
