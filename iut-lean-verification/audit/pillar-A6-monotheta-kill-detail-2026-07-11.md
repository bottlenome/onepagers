# A6 mono-theta KILL スライス詳細化（crt torsor への theta-kill 橋の到達可能性）— 2026-07-11

**分類: [設計のみ / design-only]・tier-L 詳細化ラウンド・complete_pct 0 前進（Lean コードなし・共有ファイル変更なし）・§4 規約（既存の正直な限定を消さない・弱めない・過大主張しない）**

- 対象: 柱A **A6**（実 mono-anabelian cyclotome 復元・現 s=0.60）。A6 監査群が繰り返し
  「最大レバー」と名指しした **mono-theta 円分剛性（[EtTh]）による ℤ₃^× 不定性の一部 KILL**
  ——すなわち crt の「characterized torsor」を「rigidified」へ昇格する一手——について、
  従前の「研究（柱E/D 後続）」判定を disproof-first で再検査する。
- 先例: `pillar-B2-T3-M2-M3-completeness-detail-2026-07-11.md` が B2 T3-M3「research-blocked」
  判定を disproof-first 検査（choice 障害の厳密検証・付録 A）で覆した。本書は同じ手順を
  A6 の KILL スライスに適用する。
- 結論の先出し: **橋は実在し到達可能（research-blocked ではない）**。level-9 の theta-kill
  連鎖（q9mr/q9mb）は **crt torsor の構造群そのもの（`zpsLimit`・`tmiFromUnits`）の上で**
  既に言明されており、A6 の残作業は新研究ではなく **1 ファイルの接続橋（opus 実装可）**である。

---

## 1. 正確なギャップ（何が有り・何が無いか）

### 1.1 crt が持っているもの（CHARACTERIZE・A6 計上済 0.60）

`IUT/CyclotomeRecoveryTorsor.lean`（crt）は、復元円分体 T̂=`crlLimit` と実 T=ℤ₃(1)=`tmzLimit`
の同一視空間 Isom_G(T̂,T) を**基点自由な ℤ₃^× torsor** として完全証明した:

- `crt_from_units_mul` — 実現写像 u ↦ `tmiFromUnits u` の群準同型性（CRT-0）。
- `crt_ratio_exists` — 任意の 2 つの両側可逆同一視 Φ₁,Φ₂ : Hom crlLimit tmzLimit に対し
  **w : zpsLimit.carrier** で Φ₂ = (tmiFromUnits w)∘Φ₁ となるものが存在（CRT-3a）。
- `crt_ratio_unique` — その w は一意（CRT-3b・`tmi_units_inj` 消費）。

crt ヘッダの正直な線引き (1) は明示的:「**mono-theta 円分剛性（[EtTh]）は依然 0——本ステップは
ℤ₃^× 不定性を殺さない**（CHARACTERIZE, not KILL）。不定性を消すテータ環境は柱E/D 後続」。
これが本書の検査対象の verdict である。

### 1.2 theta 側が既に持っているもの（KILL・ただし A7 計上）

level-9 kill 連鎖は**実装済み・独立監査済み**（A7 側 display-mover として計上済）:

| モジュール | 主定理 | 内容 |
|---|---|---|
| `IUT/Q3MonoThetaRigidity.lean`（q3mr） | `q3mr_cyclotome_fixed` | level-2/μ₂: テータ両立 endo は内部 cyclotome を捻れない（MECHANISM） |
| `IUT/Q3Mu9Rigidity.lean`（q9mr） | `q9mr_cyclotome_fixed`・`q9mr_aut_mu9_new_layer` | level-9/μ₉: 原始 9 乗根 ζ₉⁻¹ の恒等固定・新層 ker(Aut(μ₉)→Aut(μ₃))={1,4,7} の kill 機構 |
| `IUT/Q3Mu9TmzBridge.lean`（q9mb） | `q9mb_kill_mod9`（★★★）・`q9mb_admissible_iff`・`q9mb_kill_new_layer` | **橋 β₉ : Hom (tmzG 1) q3kU で theta-kill を tmi の実 ℤ₃^× へ輸送し、(u.val 1).val = 1 を強制**（(ℤ/9)^× 商 kill） |

### 1.3 ギャップの正体（本書の問い）

crt は「Isom_G(T̂,T) はちょうど ℤ₃^×-torsor」と言い、q9mb は「theta 両立クラスでは
u ≡ 1 (mod 9) が強制される」と言う。**両者を接続する定理——「theta 剛性は crt torsor の
構造群を ℤ₃^× から ker(ℤ₃^× → (ℤ/9)^×) ≅ 1+9ℤ₃ へ縮小する（torsor reduction）」——は
コードベースに存在しない**。prior A6 監査はこの一手を「研究（柱E/D）」と分類していた。
問い: これは本当に研究か、それとも既存資産の接続（橋）か。

---

## 2. Disproof-first 検査: 橋は実在するか（対象不一致の攻撃）

### 2.1 攻撃 1（最重要）: kill と torsor は同じ対象の上に居るか？

**判定: YES——文字通り同一の Lean 対象である。** 実測（def/theorem 本体の読解）:

| 役割 | crt 側（A6 torsor） | q9mb 側（theta-kill） | 一致? |
|---|---|---|---|
| 不定性の群 | `zpsLimit`（実 ℤ₃^×・`IUT/Zmod3PowUnitsSystem.lean` の `limitGrp zpsSystem`） | `q9mb_kill_mod9 (u : zpsLimit.carrier) …` | **同一 def** |
| 実現写像 | `tmiFromUnits : zpsLimit.carrier → Hom tmzLimit tmzLimit`（`IUT/TateModuleIndeterminacy.lean` TMI-5a） | `hreal : ∀ t, φ (q9mbInt (t.val 1)) = q9mbInt (((tmiFromUnits u).map t).val 1)` | **同一 def** |
| 作用先 | `tmzLimit`（実 ℤ₃(1)・crt の同一視の終域） | `t : tmzLimit.carrier`（hreal の量化域） | **同一 def** |
| kill の結論 | —（無し・crt 限定 (1)） | `(u.val 1).val = 1`（level-1 成分＝(ℤ/9)^× 成分） | 接続点 |

crt の torsor 比（ratio）は `w : zpsLimit.carrier` として取り出され（`crt_ratio_exists`）、
q9mb の kill は任意の `u : zpsLimit.carrier` に theta 実現仮定（hHom/hMem/hE9/hreal）を課すと
`(u.val 1).val = 1` を返す。**したがって「kill を torsor の比 w に適用する」ことは型として
そのまま合法**であり、対象の翻訳・比較準同型・新機構は一切要らない。

これは level-3 の先例と同じ構図: q3mb 監査（reaudit-A7-tmz-bridge-2026-07-11.md）が
「kill が tmi の実対象上・非空虚——u : zpsLimit.carrier（tmiFromUnits が作用する実 ℤ₃^×・
同一 zpsLimit）」と確認したのと同じ同一性が、crt の torsor 比にもそのまま当たる。

### 2.2 攻撃 2: tmz vs crt の tmzLimit/zpsLimit は別インスタンスではないか？

**判定: NO（同一）。** crt は `IUT.CyclotomeRecoveryCanonicity`（crc）→ crl → tmi 経由で
`tmzLimit`/`zpsLimit`/`tmiFromUnits` を import し、q9mb は `IUT.TateModuleIndeterminacy` を
直接 import する。両者とも `namespace IUT` 直下の同一 def を参照する（grep 実測・別名定義なし）。
q9mb の橋 β₉ は `tmzG 1 = cmrGrp 2`（tmzLimit の level-1 成分群＝実 μ₉）を theta 側実
U₃=`q3kU` に結んでおり、`q9mb_level1` が `tmiFromUnits u` の level-1 成分を rfl で展開する。
つまり **theta-kill は tmzLimit の「成分」を経由して zpsLimit の「成分条件」に着地しており、
crt の torsor が量化するのと同じ極限対象の同じ成分**である。

### 2.3 攻撃 3: import 循環・firewall 違反は無いか？

**判定: 無い。** crt の import 鎖（crc→crl→tmi→tme/tmz/zps/cli）と q9mb の import 鎖
（q9mr/q9c/q9yp/q9tl/tmi/tmz/tme/cgar/cra/cci/brau）は合流するが循環しない。新規橋ファイルが
`import IUT.CyclotomeRecoveryTorsor` と `import IUT.Q3Mu9TmzBridge` を並べても DAG は保たれる。
二重計上 firewall: 新ファイルは `q9mb_kill_mod9`/`q9mb_admissible_iff`/`crt_ratio_exists`/
`crt_ratio_unique`/`crc_canonical` を**消費のみ・再証明ゼロ**とする（q3mb/q9mb と同じ規約）。

### 2.4 攻撃 4: これは q9mb（A7 計上済）の再ラベルに過ぎないのでは？

**判定: 再ラベルではないが、監査ディスカウントは見込むべき。** 区別は主語で付く
（crt §4.2 の二重計上境界と同じ判定基準）:

- q9mb（A7 計上）の主語: `u : zpsLimit.carrier` と theta endo φ——**固定 T 上の
  自己同型の不定性**の kill。復元側 T̂=`crlLimit` は登場しない（q9mb は crl/crc/crt を
  import しない）。
- 新スライス（A6 主張）の主語: **同一視 Φ : Hom crlLimit tmzLimit の空間**（T̂ を台に含む）
  とその **torsor 構造群の縮小**——「任意の 2 つの theta-admissible な同一視の比は
  1+9ℤ₃（mod-9 で 1）に落ちる」。これは crt にも q9mb にも無い言明であり、A6 の
  「復元の rigidification」そのもの（[IUTchI] Example 1.8 / [EtTh] の cyclotomic rigidity が
  復元同一視の不定性を絞るという使われ方の忠実 mod-9 切片）。

ただし証明本体は既存定理の合成（glue）が主で、新規イディオムはゼロ。監査先例
（crc: A7 transport ゆえ full credit しない・+0.03 止まり／level27-kill-scope: 2 度目の
クローンに +0.01–0.02）に照らし、**s_A6 予測は控えめに置く**（§4）。

### 2.5 攻撃 5: kill は hreal（theta 実現可能性）条件付きであり空虚では？

**判定: 空虚ではない（q9mb で決着済み）が、限定は継承する。** `q9mb_admissible_iff` が
「(u.val 1).val = 1 ⟺ theta 両立 φ による橋輸送実現が存在」の **iff** を与えるので、
「theta-admissible」述語は消去形で well-defined であり、φ=id witness により基点
（Ξ=`crlIso`・crc 座標 u=1）が admissible であることも安価に出る。非空虚性の機械可検証
証拠は q9mb 側で確立済み（`q9mr_klein_fails_on_M`/`q9mr_weil_fails_on_M` 型の load-bearing
証明・`q9mr_inner_example` の非空 witness）。継承すべき正直な限定: **kill は「level-9 theta
両立クラス」相対**であり、この相対性は新ファイルでも消さない・弱めない（q9mb 正直限定 5）。

### 2.6 disproof-first 総合判定

**橋は実在する。対象不一致は無い。** prior A6 監査の「mono-theta kill は研究（柱E/D）」は、
q9mr/q9mb 実装**以前**の状況判断であり、q9mb が `zpsLimit`/`tmiFromUnits` の上に kill を
着地させた時点で前提が変わった——B2 T3 の「research-blocked → 到達可能」反転と同型の状況。
残作業は **crt の比 w に q9mb の kill を通す接続補題群＝1 ファイル**である。

---

## 3. マイルストーン梯子（新規ファイル 1 個・prefix `crk` 案・全 choice-free）

新ファイル `IUT/CyclotomeRecoveryThetaKill.lean`（仮）: import は
`IUT.CyclotomeRecoveryTorsor` + `IUT.Q3Mu9TmzBridge` のみ。共有ファイル変更なし。

| 段 | 内容 | 消費資産 | 難度 |
|---|---|---|---|
| **CRK-0** | zpsLimit の level-1 成分算術: `(zpsLimit.mul u v).val 1` の成分展開（limitGrp ゆえ成分ごと・ほぼ rfl/show）、one の成分=1、部分群述語 S(u) := `(u.val 1).val = 1` の mul/inv/one 閉性（(ℤ/9)^× で 1·1=1・1⁻¹=1） | zps 群律・`zpuInvL` | 低（sonnet 可） |
| **CRK-1** | theta-admissible 述語 `CrkAdm Φ` := ∃u, (crc 座標 eq) ∧ (u.val 1).val=1（`crc_canonical_unique` で well-defined）＋基点 admissibility: Ξ=`crlIso` の座標は zpsLimit.one（`tmiFromUnits one = id` は成分 pow y 1 = y・mul_one）で admissible | `crc_canonical`・`crc_canonical_unique`・`q9mb_admissible_iff` | 低〜中 |
| **CRK-2（★核）** | **比の kill**: 両側可逆な Φ₁,Φ₂ : Hom crlLimit tmzLimit と theta 両立 φ（hHom/hMem/hE9）が、`crt_ratio_exists`/`crt_ratio_unique` の一意比 w を橋輸送で実現（hreal on w）するならば `(w.val 1).val = 1`。証明 = crt_ratio_exists で w を取り、crt_ratio_unique で hreal の w と同定し、`q9mb_kill_mod9 w φ …` を適用する glue | `crt_ratio_exists`・`crt_ratio_unique`・`q9mb_kill_mod9` | 中の下（opus） |
| **CRK-3（★★ headline）** | **torsor reduction**: theta-admissible な同一視全体は部分群 S = {u : (u.val 1).val=1}（≅ 1+9ℤ₃ の mod-9 描像・S∋u ⟹ u₀=1 も従う: u₀ = u₁ mod 3）の**基点自由 torsor**——比の存在（座標 w=u₂·u₁⁻¹ の成分計算で w₁ = 1·1⁻¹ = 1）＋一意（crt_ratio_unique 透過）。主語は Φ : Hom crlLimit tmzLimit（A6 主語・§2.4 境界適合） | CRK-0/1/2・`crt_from_units_mul`・`crt_div_unit` | 中（opus） |
| **CRK-4** | 消去形の帰結＋capstone: 「crt の ℤ₃^× torsor は theta 剛性の下で構造群が S へ縮小し、新層 {4,7}＝(1+3ℤ₃)/(1+9ℤ₃) の非自明元および mod-9 非 1 類 {2,4,5,7,8} が比から排除される」（`q9mb_kill_new_layer` 型の機械可読形）＋ `CrkReductionData`/witness/`crk_scope` | `q9mb_kill_new_layer` | 低（束ね） |

新規イディオム: **0**（成分展開・群律透過・既存 kill の消費のみ）。禁止タクティク不要。
∃ は Prop ゴール内のみ・witness は crc 座標の群積（crt と同じ閉式）で choice-free。
推定規模 300–450 行・**opus 1 枠 1 ラウンド**（fable 不要・詰まりが出た場合のみ HELP）。

### 正直な限定（新ファイルに必ず書く・消さない・弱めない）

1. **縮小は mod-9 スライスのみ**: 縮小後も S ≅（mod-9 で）1+9ℤ₃ の torsor が**まるごと残存
   （SURVIVES）**する。rigidified ≠ canonical trivialization——同一視は mod 9 で pin される
   だけで一点には落ちない。full ℤ₃^× kill は実 wild 円分塔（named future target・
   level-27 は設計済み fallback `level27-kill-scope-2026-07-11.md` の q27* 連鎖で第 2 層
   {1,10,19} まで拡張可能）。
2. **theta 両立クラス相対**（q9mb 正直限定 5 の継承): 縮小は「level-9 theta 実現可能な比」に
   対する言明。tmi の残存宣言（Galois 同変性だけでは絞れない）は不変更。
3. crt 限定 (2)(3)(4)（π₁ 連続 χ 未・幾何 cyclotome 不在・p=3/G 固定）は全て継承・並置。
   crr/crl/crc の「A6 ≤ 0.65（K̄/幾何 cyclotome・π₁ 連続 χ が未のあいだ）」帽子も**維持**
   ——本スライスは帽子の内側での前進であり帽子を外さない。
4. q=3⁹ 忠実部分ケース・endo 定式化・実テータ関数/π₁ 同定/大域 Galois 0（q9mr/q9mb 継承）。

---

## 4. 正直な verdict と s_A6 予測

**verdict: 到達可能（research-blocked ではない）。** 最短経路 = 上記 CRK-0〜4 の
**opus 1 ファイル 1 ラウンド**。理由の要約:

- kill（q9mb_kill_mod9）と torsor（crt_ratio_exists/unique）は**同一の Lean 対象
  `zpsLimit`/`tmiFromUnits`/`tmzLimit` の上に既に居る**（§2.1–2.2・対象不一致なし）。
- 接続は既存定理の合成で閉じ、新機構・新イディオム・choice 障害はゼロ（§3）。
- prior 監査の「研究」判定は q9mr/q9mb 以前の状況に対するものであり、失効している。

**s_A6 予測（過大主張しない・独立監査が確定）**: 現 0.60 →
- 中央値 **0.61–0.62**: A6 主語（Isom_G(T̂,T) の torsor reduction・crt 限定 (1) の
  「KILL は柱E/D 後続」を mod-9 スライスで正面 discharge）は crt/q9mb のどちらにも無い
  新言明である一方、証明実質は transport/glue ゆえ crc 先例（+0.03 の transport 割引）
  より小さい +0.01–0.02 が敵対的相場。
- 敵対的下限 **0.60 据え置き**も想定内（「q9mb の A7 計上との差分が主語の置換のみ」と
  査定された場合）。その場合でも crt 正直限定 (1) の文言が「mono-theta 剛性 0」から
  「mod-9 スライスは接続済み・残りは 1+9ℤ₃」へ更新される実体は残り、A6 の 0.65 帽子への
  次の一手（level-27 接続・π₁ 連続 χ）の土台になる。
- 柱A 表示への波及は微小（Σ_A への寄与 14×0.01–0.02 = 0.14–0.28）。表示 mover は
  期待しない（表示目的なら level27-kill 経路が本命のまま）。

**やってはいけないこと（överclaim 禁止リスト）**: 「ℤ₃^× 不定性を殺した」と書かない
（殺したのは (ℤ/9)^× 商の比のみ）／「復元が canonical になった」と書かない（mod-9 pin のみ）
／crt・q9mb・tmi の正直申告の消去・弱化・crt の CHARACTERIZE 言明の書き換え（新ファイルは
並置＋接続のみ）／A7 側 status の再主張（kill 本体は A7 計上済・新規主張は A6 のみ）。
