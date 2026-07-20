# A5 実 tempered π₁ 深化スライス詳細化（0.23 の次の実増分の到達可能性）— 2026-07-20

**分類: [設計のみ / design-only]・tier-L 詳細化・complete_pct 0 前進（Lean コードなし・共有ファイル変更なし）・§4 規約（既存の正直な限定を消さない・弱めない・過大主張しない）**

- 対象: 柱A **A5**「実 tempered π₁^temp」（weight 10・現 s_A5 = **0.23**・`target_ledger.json` 実測）。
- 手法: `audit/pillar-A6-monotheta-kill-detail-2026-07-11.md` と同じ **disproof-first 到達可能性検査**。
  既存の「正直な限定」の各条項を敵対的に再検査し、**前提が失効した条項**（＝実は到達可能に
  変わった条項）と**依然 research-blocked な条項**を峻別する。
- 結論の先出し: **到達可能なマイルストーンが 2 本ある（research-blocked ではない）**。
  (1) A5d′ 監査（`reaudit-5parallel-crosspillar-2026-07-11.md` §A5）が名指しした
  「density を位相的閉包へ（limitTopology 接続）」は M15 位相資産で **choice-free に閉じる**。
  (2) q3nt 正直限定 1 の「奇レベル実現は ζ_l∉ℚ₃ で恒久ブロック」は、その**後**に建った
  L₂/M 生態系（q3rq→q3tl→q3k→q9tl→**q9mt**）により **3-冪レベル（l=9）については失効**して
  おり、**wild level-9 の tempered テータ実現 Ψ₉**（q3nt の level-9 版＋χ 可視化）が
  既存資産の消費のみで建つ。A6 crk と同型の「実装済み資産による判定失効」である。

---

## 0. TL;DR

| 問い | 答え |
|---|---|
| 次の実増分は到達可能か | **YES（2 本・どちらも research-blocked でない）** |
| 本命 | **N2: wild level-9 tempered テータ実現**（`IUT/Q3TemperedThetaClassL9.lean`・prefix `q9nt`・opus 1 枠）。q3nt（A5d・0.20→0.23 の主要因の片割れ）の「実現は level 2（μ₂ 影）のみ・χ 不可視」を **mod-9・μ₉・χ 可視**へ昇格。保守見込み **+0.02〜+0.03** |
| 副 | **N1: 位相的稠密性**（`IUT/Q3TemperedEtDensity.lean`・prefix `q3tpd`・opus 1 枠）。A5d′（q3tpec）正直限定 (3)「位相的稠密性は主張しない」を M15 `cylinder_nbhd_basis` で正面 discharge。監査が名指しした次の一手。保守見込み **+0.01〜+0.02** |
| 合算の保守 forecast | s_A5 0.23 → **0.26〜0.28**（敵対的下限 0.25）。柱A 表示は **56 据え置き**（Σ_A=55.96+10·Δ・表示 57 には Δ≥0.06 が必要＝単独ラウンドでは届かない前提で正直に報告する） |
| research-blocked（正直申告） | (i) **tempered π₁ の「定義」そのもの**（Berkovich/rigid 被覆理論・位相）——A5 恒久上限 0.35–0.4 の根拠・本 2 スライスでも外れない。(ii) **full ẑ(1)（全素数 l）**——p=3 恒久スコープと衝突。(iii) **atpGroup の半直積まるごとの実現**（実 Gal(M/ℚ₃) 自己同型の建設が前提・A7 と主語が絡む・後続） |

---

## 1. 正確なギャップ（何が有り・何が無いか）

### 1.1 A5 が現在持っているもの（0.23 の内訳・全て本体確認済み）

| 資産 | ファイル / 主定理 | 内容 | 計上 |
|---|---|---|---|
| A5a | `IUT/Q3TateDeck.lean`（q3td） | 実 Tate 被覆 ℚ₃^×→E_q(ℚ₃)・デッキ ℤ・実周期準同型 `q3tdPeriodHom`（単射・像=ker）・無限位数の無条件 discharge | 0.10 帯 |
| A5b | `IUT/Q3TemperedPi1.lean`（q3tp） | 実 pro-3 tempered 群 `q3tpGroup = prodGrp tmzLimit intGrp`・完全列 `q3tp_extension_exact`・実 Gal 円分切片作用 `q3tpGalAct`・無条件存在 `q3tp_exists_unconditional` | 0.15 |
| A5c | `IUT/Q3TateCoverTower.lean`（q3tc） | 実中間被覆 E_{qⁿ}→E_q（`q3tcHom`・`q3tc_q_pow`）・有限デッキ `q3tcDeckFin`・実被覆塔 | 0.15 |
| A5d | `IUT/Q3TemperedThetaClass.lean`（q3nt） | 代理 Heisenberg/tpeGroup の実 level-2 テータ群内実現 `q3ntPhi`/`q3ntPsi`・代理 ω=実 μ₂ Weil `q3nt_symplectic_real`・deck×θ=実 −1 `q3nt_deck_theta_ne_one`・v(q)=2 復元 `q3nt_vq_two`・**正直核 `q3nt_psi_level2_collapse`／`q3nt_chi_invisible`** | 0.20（+0.05） |
| A5d′ | `IUT/Q3TemperedPi1Deepen.lean`（q3tpec） | 実比較射 `q3tpEtComp : π₁^{temp,(3)} → ℤ₃(1)×ℤ₃`・忠実 `q3tpEtComp_injective`・各有限段全射 `q3tpEt_finite_level_surjective`・**全体非全射 `q3tpEtComp_not_surjective`**（witness ω=(3ⁿ−1)/2・`q3tpEtWitness`） | 0.23（+0.03） |

### 1.2 「より深い tempered π₁ 言明」の候補 3 方向と、それぞれの現状の欠落

**(G1) 完備化としての π₁^ét との関係の完成**。q3tpec は「各有限商 ℤ/3ⁿ で全射」＝稠密の
**代数的影**までで止まり、ヘッダ正直限定 (3) が明示する:「**位相的稠密性（閉包＝全体）は
主張しない**（Zp の位相は M15/M25 にあるが本ファイルでは接続しない）」。一方リポジトリには
`IUT/Topology.lean`（M15）の `limitTopology`（`Zp 3 = limitGrp (padicSystem 3)` にそのまま
適用可能・`IUT/LocalCFT.lean:90`）・`prodTopology`・**近傍基定理 `cylinder_nbhd_basis`**
（Topology.lean:237・choice-free）が既に在る。欠落は「toZp 像は limitTopology で稠密」
「比較射像は直積位相で稠密**かつ**真部分（dense proper subgroup）」の 2 定理**のみ**。
grep 実測: tempered 系ファイルに位相 import はゼロ・稠密定理は存在しない。

**(G2) tempered π₁ のテータ商構造（非可換部分）の深化**。q3nt は代理 tempered π₁
（thetaGrp=ℤ³ Heisenberg・tpeGroup=⋊ℤ・atpGroup=χ捻り）を実 level-2 テータ群 `q3thGrp` 内に
実現したが、正直限定 1 が線を引いた:
> 「実現は level 2（μ₂ 影）: …代理シクロトーム ℤ の実現は mod 2 のみ。ℤ 全体（ẑ(1)）の実現は
> 奇レベル拡大体機構（**後続・ζ_l∉ℚ₃ で恒久ブロック**）。χ 捻り（M429F）は level 2 で不可視
> （q3nt_chi_invisible）」

この「恒久ブロック」の前提が**その後のラウンドで失効した**（§2.1）。欠落は
「代理 tempered テータ骨格の **wild level-9（μ₉）実現**」＝ Ψ₉ : tpeGroup → q9mtM、
シクロトーム生成元 (0,0,1) ↦ 実 ζ₉⁻¹（位数ちょうど 9）、および **χ 捻りの可視化**
（q3nt_chi_invisible の正反対の定理が level 9 で成立する）。

**(G3) tempered π₁ への外 Galois 作用の深化**。現状は `q3tpGalAct`（円分切片
Gal(ℚ(ζ_{3^∞})/ℚ) が μ 方向に χ 冪・デッキ方向固定・A5b）のみ。テータ実現像への Galois 作用は
q3nt ロードマップが **A7 後続**と名指し（「(i) A7: q3thGrp/Ψ 像への実 Gal 作用→mono-theta
剛性の実入口」）。M = ℚ₃(ζ₉)（q3k の実体）へは円分指標 mod 9 の作用が数学的には見えているが、
実 Gal(M/ℚ₃) 自己同型（ζ₉↦ζ₉^k・Y の像の実書き下し）の建設は新規建設であり、credit が
A3/A7 と絡む。**本ラウンドの梯子には載せない**（§2.4）。

---

## 2. Disproof-first 検査

### 2.1 攻撃 1（本命 N2 の核心）: 「奇レベルは ζ_l∉ℚ₃ で恒久ブロック」は今も真か？

**判定: 3-冪レベルについて失効（FALSE になった）。** q3nt（2026-07-11 実装）の正直限定 1 が
書かれた時点では、リポジトリの実局所対象は ℚ₃ 系（q3tGrp）のみで、ζ₃∉ℚ₃ ゆえ奇レベルの
実 μ_l 値テータは建たなかった。その**後**、A7 の ℤ₃^× kill キャンペーン（R1→R4→level-9）が
以下を**実対象として**建てた（各々独立監査済み・[propext, Quot.sound]）:

| 資産 | 実体 | 監査 |
|---|---|---|
| `IUT/Q3RamifiedQuadratic.lean`（q3rq） | 実分岐 2 次拡大 L₂=ℚ₃(ζ₃)・**実 ζ₃ 位数ちょうど 3**・field-engine-free 逆元 | `reaudit-R1-…`: **real(b)**・A7 +0.01 |
| `IUT/Q3TateCurveL2.lean`（q3tl） | 実 E₂₇ = L₂^×/27^ℤ・[ζ₃]/[3] 位数 3 | R2b foundation |
| `IUT/Q3TateCurveL9.lean`（q9tl） | 実 E_{3⁹} = M^×/q^ℤ（M^× = `q9tlMx` = ℤ(v_π)×U₃・q=3⁹）・**[ζ₉]/[3] 位数ちょうど 9**（`q9tl_zeta9_tor`/`q9tl_3_tor`） | foundation・0 前進申告 |
| `IUT/Q3Mu9ThetaGroup.lean`（**q9mt**） | **wild level-9 実テータ群** `q9mtGrp` = C_{M₉}(g_τ)（`q9mtM` 台 (M^××ℤ)×M^×・cocycle 積は q3th と同形）・**μ₉ 値 Weil `q9mtWeil`**・`q9mt_comm_eq_weil`・**非退化 `q9mt_weil_nondeg`: e₉([3],[ζ₉])=ζ₉⁻¹≠1**・witness `q9mtG3`/`q9mtGZeta` ∈ q9mtGrp（`q9mt_g3_mem`/`q9mt_gz_mem`） | `reaudit-q9mt-theta-l9-…`: 申告どおり **0 前進（foundation）**・A 据え置き |

つまり q3nt が「代理 tempered 骨格を実現する先」として欠いていた **μ₉ 値の実テータ群が、
今は在る**——しかも q9mt は complete_pct **0 計上（foundation）**であり、これを消費する
A5 実現は二重計上でない。grep 実測: `q9mtM`/`q9mtGrp` の消費者は A7 kill 連鎖
（q9mr・q9mb・crk）のみで、**tpeGroup/thetaGrp から q9mtM への準同型はコードベースに存在しない**
——q3nt が q3thM に対してやったことの level-9 版は、まだ誰の仕事でもない空白である。
A6 crk と同型の判定失効（「研究」判定が後続実装で前提を失った）と裁定する。

### 2.2 攻撃 2: N2 は q3nt のクローンに過ぎず、新規 A5 内容ゼロでは？

**判定: クローン割引は見込むが、クローンで尽きない新規内容が 2 点ある。**

- **同形部分（クローン・割引対象）**: Φ₉/Ψ₉ の構成テンプレート（Y^b·X^a·Z^c）・braiding は
  `q3nt_braid`（**一般 Grp で証明済み**・Q3TemperedThetaClass.lean:245・そのまま消費可・
  新イディオム発明ゼロ）・部分群 zpow 閉性（`q3nt_mem_zpow` の q9mtGrp 版クローン）。
  地上事実は全て q9mt 済み: [X,Y]=scalar(ζ₉⁻¹) は `q9mt_commutator`＋`q9mt_weil_g3_gz` の系
  （成分検算: X·Y=(ζ₉⁻¹,−1,3ζ₉)=scalar(ζ₉⁻¹)·(Y·X)・本設計で手計算済み）、scalar 中心性は
  cocycle 積 (c,a,w)(c′,a′,w′)=(cc′w′ᵃ,a+a′,ww′) と M^× 可換性（`q9tlComm`）から 1 行。
- **新規 1（質的・q3nt に無い）**: **シクロトーム実現の深さが mod 2 → mod 9**。
  q3nt の Z=−1 は位数 2（代理 ℤ の μ₂ 影）だったのに対し、Z₉=scalar(ζ₉⁻¹) は
  **位数ちょうど 9**（`q3k_zeta9_pow9`＋q9yp の Yᵏ≠1・q9tl 消費実績あり）。代理 ℤ の実現が
  初めて 2-冪でない・しかも **wild**（分岐 e=6 の M 上）な円分値に届く。正直核は
  `q9nt_psi_level9_collapse`: Ψ₉(ι(0,0,9))=1（Z₉⁹=1）へ更新（消さずに深化）。
- **新規 2（質的・q3nt が正反対を証明した命題）**: **χ 捻りの可視化**。q3nt は
  `q3nt_chi_invisible`（捻り (a,b,c,n)↦(a,−b,−c,n) で Ψ 不変・(−1)^{−k}=(−1)^k）を
  **正直限定として定理化**した。level 9 では同じ捻りが Z₉^c ↦ Z₉^{−c} を与え、
  ζ₉² ≠ 1 ゆえ **Ψ₉∘tw ≠ Ψ₉**（witness ι(0,0,1)・1 定理）。M429F `atpChi`（算術捻り代理・
  `IUT/ArithTemperedPi1.lean`）の主張する「算術作用は tempered テータに非自明に効く」が
  実値で**初めて見える**。これは q3nt 監査の割引理由 3「mod-2/μ₂ 影のみ」への正面回答であり、
  単なる 2 度目のクローンではない。

敵対的相場: level27-kill 先例「2 度目のクローンに +0.01–0.02」を下限に、割引理由の
正面 discharge（q3nt 監査 §5 の割引 3 を解消・割引 1「値一致 bridge 性」は残存）を勘案して
**+0.02〜+0.03**（§4）。

### 2.3 攻撃 3: N2 の二重計上 firewall（vs A7・A8・A4）

**判定: 境界は q3nt 監査で確立済みの判定基準がそのまま使える。**

- **vs A8（q3th）**: 触らない（q9nt は q3thM でなく q9mtM に実現する・q3th ファイル不変更）。
- **vs A7（q9mr/q9mb/crk・level-9 kill 計上済み）**: A7 側の主語は「テータ両立 **endo** の
  cyclotome 固定」（q9mr）と「kill の tmi/torsor への輸送」（q9mb/crk）。q9nt の主語は
  「**代理 tempered π₁（thetaGrp/tpeGroup/atpChi）の q9mtM 内実現準同型 Φ₉/Ψ₉**」で、
  endo も tmi も登場しない。逆方向の依存もない（q9mr/q9mb は tpeGroup を import しない・
  grep 実測）。判定基準（q3nt 監査 4.2 DECISIVE の再利用）: **各旗艦から Φ₉/Ψ₉ を消去すると
  命題が消滅する**こと・q9mt の定理は消費のみ（再証明 0 本）・**A7/A8 status は主張しない**。
- **vs q9mt 自身（foundation）**: q9mt は 0 計上（監査確定）。foundation の消費は q3nt が
  q3th（A8 計上済み）を消費した場合より**さらに**クリーン。
- **vs A4**: π₁^ét 系対象（q3pe/q3pc）は一切登場しない。無関係。

### 2.4 攻撃 4（副 N1）: 位相的稠密性は本当に choice-free で閉じるか？ A4 の再ラベルでは？

**判定: 閉じる・再ラベルでない。**

- **構成可能性**: 稠密性の言明は「∀ U open in `limitTopology (padicSystem 3)`, ∀ x∈U,
  ∃ a:Int, U ((toZp 3).map a)」。証明は `cylinder_nbhd_basis`（M15-6・choice-free・
  帰納は GenOpen 上）でレベル k を取り、x.val k : (zmod (3^k)).carrier を **Prop ゴール内で**
  `Quot.ind` して整数代表 a を得る（`q3tpEt_finite_level_surjective` と同じイディオム）。
  (toZp a).val k = mk a は定義計算。∃ は Prop 内・witness は代表元＝choice-free。
  直積版（比較射像の π₁^ét = tmzLimit×Zp 3 内での稠密性）には「開長方形近傍基」補題
  `q3tpd_prod_nbhd_basis`（`prodTopology` の GenOpen 帰納・`cylinder_nbhd_basis` と同構造・
  inter ケースは `isOpen_inter` で閉じる）が 1 本要る——これが本スライス唯一のやや新しい
  一般補題（発明ではなく M15-6 の直積版写経）。μ 成分は恒等（`q3tpEtComp_mu`）ゆえ
  長方形の μ 側は x.1 自身で当たる。
- **headline**: `q3tpd_dense_proper` —— 比較射像は **位相的に稠密**（閉包＝全体の
  各点近傍定式化）**かつ真部分**（`q3tpEtComp_not_surjective` の消費）。「tempered π₁ は
  étale π₁ の**真の稠密部分群**」が代数的影でなく本物の位相文になる。
- **A4/A3 再ラベル攻撃**: M15/M265F の位相資産は柱A の progress 側で古くから存在するが、
  **tempered 側の対象への接続はゼロ**（grep: q3tp*/q3nt* に Topology import なし）。
  新言明の主語は `q3tpEtComp` の像（A5 の対象）であり、q3tpec ヘッダ限定 (3) の named defer の
  discharge。A4 の π₁^ét 作用定理群（q3pe/q3pc）には稠密性は存在しない。
- **監査正当性の傍証**: A5 監査自身が「次: density を位相的閉包へ（limitTopology 接続）」と
  書いた（reaudit-5parallel §A5 末尾）——監査 sanctioned の一手。

### 2.5 攻撃 5: research-blocked なもの（正直に列挙・梯子に載せない）

1. **tempered π₁ の定義そのもの**（Berkovich/rigid 解析被覆・位相 π₁）: N1 の位相は
   **étale 側（副有限）位相**であって tempered 位相ではない。A5 恒久上限 **0.35–0.4**
   （`audit/A5-real-tempered-pi1-detail-2026-07-10.md` §6・q3nt ヘッダ限定 2）は本 2 スライスの
   後も**不変**。ここを動かすには rigid 幾何の形式化という別次元の建設が要る——research-blocked。
2. **full ẑ(1)（全素数）**: A5b 限定 (1)（pro-3 のみ）は p=3 恒久スコープの帰結。
   Π_l ℤ_l(1) の建設は骨格量産になりやすく、§2 規約により**着手しない**。
3. **atpGroup（χ 半直積）まるごとの実現**: χ を**外部自己同型**として実現するには
   実 Gal(M/ℚ₃)≅(ℤ/9)^× の自己同型（ζ₉↦ζ₉^k）の実建設が前提。M=ℚ₃(ζ₉) ゆえ数学的には
   円分指標 mod 9 で見えているが、建設 credit が A3/A7 と絡む（q3nt ロードマップは
   「Ψ 像への実 Gal 作用」を A7 名指し）。N2 では χ を「捻り写像に対する Ψ₉ の**非不変性**」
   （可視化定理・Ψ₉ が主語）までに限定し、半直積実現は named future target として残す。
4. **q3tpGroup（A5b 分裂直積）の主語ごと置換**: compact E_q の tempered π₁ は実際に可換
   なので A5b は正直——置換すべきは punctured 側であり、それが正に N2 の路線（実現）。
   別途「fiber product π₁^temp ≅ π₁^ét ×_{ℤ₃} ℤ」の普遍性 packaging は可能だが、
   新規数学ゼロの束ねで **complete_pct 0 前進の骨格追加**になる恐れが高い——§2 規約により
   梯子に載せず、やるなら着手前にユーザー確認する。

---

## 3. マイルストーン梯子（IF reachable → 到達可能・2 ファイル・全 choice-free）

### N2（本命・opus 1 枠）: `IUT/Q3TemperedThetaClassL9.lean`（prefix `q9nt`・500–700 行）

import: `IUT.Q3Mu9ThetaGroup`・`IUT.Q3TemperedThetaClass`（braiding/一般補題の消費）・
`IUT.TemperedPi1Etale`・`IUT.ArithTemperedPi1`・`IUT.Q3KummerYPow`。共有ファイル変更なし。

| 段 | 内容 | 消費資産 | 難度 |
|---|---|---|---|
| q9nt-0 | Z₉ := q9mt スカラー ((0, q3kU.inv q9tlZeta9U), 0, 1) の中心性（cocycle 成分 1 行）・**Z₉⁹=1**（scalar 冪=成分冪＋`q3k_zeta9_pow9` subtype 化）・**Z₉ᵏ≠1 (0<k<9)**（q9yp の Yᵏ≠1 消費） | q9mt cocycle・q3k/q9yp | 低 |
| q9nt-1 | 基本関係 X·Y = Z₉·(Y·X)（X=`q9mtG3`・Y=`q9mtGZeta`・1 回の成分計算・`q9mt_weil_g3_gz` と整合）・q9mtGrp の zpow 閉性（`q3nt_mem_zpow` の写経） | `q9mt_commutator`・`q9mt_g3_mem`/`q9mt_gz_mem` | 低 |
| q9nt-2 | **Φ₉ : thetaGrp → q9mtM**（v ↦ Yᵇ·Xᵃ·Z₉ᶜ・map_mul は **`q3nt_braid` をそのまま消費**）・像⊆q9mtGrp・**シクロトーム実現 (0,0,1)↦Z₉ の位数ちょうど 9**（mod-2→mod-9 昇格の headline） | `q3nt_braid`（一般 Grp・再証明ゼロ） | 中の下 |
| q9nt-3 | **Ψ₉ : tpeGroup → q9mtM**（((a,b,c),n) ↦ Yᵇ·X^{a+n}·Z₉ᶜ）・Ψ₉∘tpeIncl=Φ₉・Ψ₉(tpeSection n)=Xⁿ | tpeIncl/tpeSection・q3nt cocycle 検算の写経 | 中 |
| q9nt-4（★旗艦 1） | **代理 ω＝実 μ₉ Weil**: [Φ₉v,Φ₉w] = Z₉^{ω(v,w)}（`theta_comm` transport）・**deck×θ = 実 ζ₉^{−nb} ≠ 1**（`tpe_deck_theta_commutator` transport・q3nt_deck_theta_ne_one の μ₉ 版） | `theta_comm`・`q9mt_comm_eq_weil` | 中 |
| q9nt-5（★旗艦 2・q3nt に無い） | **χ 可視化**: 捻り tw:(a,b,c,n)↦(a,−b,−c,n)（M429F `atpChi` 系）に対し **Ψ₉∘tw ≠ Ψ₉**（witness ι(0,0,1)・Z₉≠Z₉⁻¹⟸ζ₉²≠1）——`q3nt_chi_invisible` の正反対が wild レベルで成立 | q9nt-0 の Z₉ᵏ≠1 | 低 |
| q9nt-6 | **v(q) の wild 復元**: (Ψ₉(s n)).w = q9tl3ⁿ（v_π=6n）・その **9 乗 = qⁿ**（`q9tl_ninth_elt`）・v_π(q)=54=9·6 | `q9tl_ninth_elt` | 低 |
| q9nt-7 | 正直核＋capstone: `q9nt_psi_level9_collapse`（Ψ₉(ι(0,0,9))=1）・deck 融合 ker 記述・`Q3TemperedThetaL9Data`/witness/exists | — | 低（束ね） |

新規イディオム: **0**（braiding は q3nt 既証明の一般 Grp 補題・残りは成分計算と transport）。

### N1（副・opus 1 枠・N2 と独立並列可）: `IUT/Q3TemperedEtDensity.lean`（prefix `q3tpd`・250–400 行）

import: `IUT.Q3TemperedPi1Deepen`・`IUT.Topology`。共有ファイル変更なし。

| 段 | 内容 | 消費資産 | 難度 |
|---|---|---|---|
| q3tpd-0 | toZp 稠密性: ∀ U open (limitTopology (padicSystem 3)), ∀x∈U, ∃a, U(toZp a)（`cylinder_nbhd_basis`＋Quot.ind） | M15-6 | 低〜中 |
| q3tpd-1 | 直積開長方形近傍基 `q3tpd_prod_nbhd_basis`（prodTopology の GenOpen 帰納・唯一のやや新しい一般補題） | `prodTopology`・`genOpen` 帰納 | 中 |
| q3tpd-2（★） | **比較射像の位相的稠密性**（π₁^ét = tmzLimit×Zp 3・直積 limitTopology）＋ **`q3tpd_dense_proper`**: 稠密かつ真部分（`q3tpEtComp_not_surjective` 消費）——「tempered ⊊ étale・しかも稠密」の完全な位相文 | q3tpec 全部・M15 | 中 |
| q3tpd-3 | capstone・q3tpec 限定 (3) の discharge 注記（既存ヘッダは触らない・新ファイル側に記載） | — | 低 |

### N3（任意 filler・tier-S・§2 確認条件付き）

fiber-product packaging（π₁^temp ≅ π₁^ét ×_{ℤ₃} ℤ）は complete_pct 0 前進の骨格束ねに
なりうるため、**着手前にユーザー確認**（§2.5-4）。5 並列の枠埋めには他柱を優先する。

---

## 4. 保守的 status forecast と、持ち越す A5 の帽子・限定

**verdict: 到達可能（research-blocked ではない）。**

**s_A5 予測（過大主張しない・独立監査が確定）**: 現 0.23 →
- N2 単独: 中央値 **+0.02〜+0.03**（q3nt +0.05 の先例に対し、テンプレートはクローンだが
  「mod-9 wild シクロトーム＋χ 可視化」が q3nt 監査割引 3 を正面 discharge する分、
  level27 クローン相場 +0.01–0.02 の上に半ノッチ）。敵対的下限 +0.01（「q3nt の主語で
  レベルだけ替えた」査定）。
- N1 単独: 中央値 **+0.01〜+0.02**（監査が名指しした named next・ただし位相は étale 側で
  tempered 位相でない、の割引込み）。敵対的下限 +0.01。
- 合算中央値 **0.26〜0.28**・敵対的下限 **0.25**。A5 監査が示唆した現世代の soft 天井 0.28 と
  整合（それを超える主張はしない）。
- **柱A 表示**: Σ_A（ledger 実測）= 8·0.85+8·0.69+12·0.75+14·0.56+10·0.23+14·0.61+12·0.57
  +12·0.66+10·0.12 = **55.96** → 表示 56。Δs_A5=+0.05 でも Σ_A=56.46 → **56 据え置き**
  （表示 57 は Σ_A>56.5 ⟺ Δ≥0.06 が必要）。**表示 mover を主張しない**で正直に報告する。

**消さない・弱めない帽子（新ファイルに必ず並置）**:
1. **A5 恒久上限 0.35–0.4**（Berkovich/rigid 位相なし・tempered π₁ の「定義」は依然外部）——
   N1 の位相は étale 側 limitTopology であり tempered 位相でない。上限は動かない。
2. q3nt 正直限定の**更新形**: 「実現は level 2 のみ」→「level 2（μ₂・ℚ₃ 上）と level 9
   （μ₉・M=ℚ₃(ζ₉) 上・wild）で成立。**full ẑ(1)・全素数 l は依然未達**。Ψ₉ も非単射
   （mod-9 崩壊）」。旧限定は消さず、q9nt 側に深化形を書く。
3. pro-3 恒久限定（A5b (1)）・K-point の影（群提示担体・A2 継承）・実テータ関数 0・
   cuspidalization 本体 0・q=3^m/3⁹ 忠実部分ケース（[EtTh] の q^{1/l} 添加そのものでない・
   q9tl 限定 2 継承）——全て継承・並置。
4. **稠密性の正直文**: q3tpd の「稠密」は「開集合ごとの交わり（各点近傍定式化）」であり、
   閉包演算子・完備性・コンパクト性の一般論は主張しない（M15 の正直申告を継承）。
5. χ 可視化は「捻りに対する Ψ₉ の非不変性」であり、**atpGroup 半直積の実現ではない**
   （実 Gal(M/ℚ₃) 自己同型は named future target・A7 と調整）。

**やってはいけないこと（overclaim 禁止リスト）**: 「tempered π₁ を実現した」と書かない
（実現したのは代理骨格の mod-9 影）／「位相的に完成」と書かない（étale 側位相のみ）／
q3nt・q9mt・q3tpec の正直限定の消去・弱化／A7・A8 status の再主張。

---

## 5. 推奨第一実装スライスと de-risk-first

- **第一スライス（opus 1 枠）**: **N2 = `IUT/Q3TemperedThetaClassL9.lean`（q9nt）**。
  理由: (i) A5 の重み中心（テータ商構造）に直撃し増分が最大、(ii) 新イディオム 0
  （`q3nt_braid` 一般版の消費のみ）、(iii) 地上事実（[X,Y]=scalar(ζ₉⁻¹)・中心性・witness 所属）
  は q9mt 監査で検証済み。q3nt 実装（同 opus 級・550–700 行）が 1 ラウンドで通った先例に載る。
- **de-risk-first 項目（実装前 30 分・scratch 1 本）**: q9mtM の cocycle 順序規約の下で
  **X·Y = Z₉·(Y·X) と Z₉ 中心性と Z₉⁹=1 の 3 事実だけ**を先にコンパイルして確定する
  （q3nt で「X を左に置く順序では準同型にならない」が判明した前例の再発防止。
  ここが通れば残りは全て q3nt の写経＋transport で機械的に落ちる）。詰まった場合のみ
  HELP スポットとして fable を呼ぶ（braiding は既証明ゆえ想定詰まりは規約順序のみ）。
- **並列枠**: N1（q3tpd・opus）は N2 と**ファイル・依存とも独立**であり同一ラウンドで
  並列可能。N1 側の de-risk は `q3tpd_prod_nbhd_basis` の sUnion ケース（GenOpen 帰納の
  motive 設計）——`cylinder_nbhd_basis` の証明（Topology.lean:237-259）を写経の型にする。
- 統合時の共有ファイル更新（IUT.lean・build.sh・gen_graph.py PILLAR・graph-meta/dashboard・
  target_ledger）は親が一括。status 確定は独立敵対監査後（本書の見込み値を先に書き込まない）。

---

*設計: tier-L 詳細化ラウンド 2026-07-20。本書は設計のみで complete_pct を動かさない。
§1–§3 の全主張は実ファイル精読（Q3TemperedPi1/Deepen・Q3TemperedThetaClass・Q3Mu9ThetaGroup・
Q3TateCurveL9・Q3RamifiedQuadratic・Topology・LocalCFT・ArithTemperedPi1）と監査記録
（reaudit-A5-tempered-theta-class・reaudit-5parallel-crosspillar §A5・reaudit-q9mt-theta-l9・
reaudit-R1-ramified-quadratic）に基づく。X·Y=Z₉·(Y·X) の成分検算・Ψ₉ cocycle 一致・
χ 可視 witness は設計時に手計算済み。*
