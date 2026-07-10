# A7 深化詳細化 — 実 ℤ₃(1) の自己準同型剛性と (ℤ/3^ℓ)^×→ℤ₃^× 不定性の「正確な特徴付け」（A7 0.35 → 0.42–0.45 級）

日付: 2026-07-10 ／ 種別: **設計ドキュメントのみ**（実装コード無し・共有ファイル不更新）
分類: **[実／本物建設(b)＋昇格(a) の設計]** — 既存 A7 実資産（cmr/cgar/cra/tmz・独立再監査で
status 0.35 確定）の上に、**実 Tate 加群 T=ℤ₃(1)=`tmzLimit` の自己準同型の完全分類
（自動 ℤ₃-線型性）と、Aut(ℤ₃(1)) ≅ 実 ℤ₃^×（`zpsLimit`）＝円分剛性の不定性の正確な
特徴付け**を本物に積む深化ステップを、opus 実装枠に渡せる粒度へ段階分解する。
台帳確認（本日実測）: `target_ledger.json` A7 = { weight 12, status **0.35** }・
柱A Σ(w·s) = **47.74**/100 → complete_pct 48（`graph-meta.json` と整合）。
**complete_pct 影響: 本ドキュメント自体は 0（設計のみ）**。実装後の保守的見込みは §5
（最終判定は独立監査・AUDIT_RUBRIC 準拠・敵対的既定=模型）。

**本設計の中心的発見（§1-§2 で裏取り）**: A7 を 0.35 に留めた監査ディスカウント
（reaudit-A7 §5: 「剛性内容が初等・レベル単位」「`cra_indeterminacy` は不定性の
*残存*を 1 本の可換定理で言うのみ」）は、**逆極限レベルの新しい実定理**——
「T=ℤ₃(1) の *任意の抽象群自己準同型* は自動的に整合冪族（=ℤ₃ 元）で尽くされる」
（自動連続性/線型性・核=`ker proj_n = T^{3^{n+1}}` の可除性フィルトレーションが証明の
本体）——で正面から解消できる。これはレベル単位の初等剛性（生成元の像で決まる）とは
異なり、**極限対象では自明でない本物の定理**であり、その系として IUT が mono-theta
剛性で殺す当の **ẑ^× 不定性（p=3 切片: ℤ₃^×）を「残存する」でなく「正確にこれである」
と実対象 `zpsLimit`（実 ℤ₃^×）で特徴付け**られる。

---

## §1 現状実測 — A7 既存資産（定義・定理の**本体**で判定・本日全文精読）

### 1.1 資産表

| モジュール | 判定（本体根拠） | 何を証明しているか | 残る正直な限定 |
|---|---|---|---|
| `IUT/CyclotomicMuGroupReal.lean`（cmr） | **実**。`cmrCarrier` は実円分体 `cteField`=ℚ[x]/(Φ_{3^ℓ}) の担体の subtype（rpow y 3^ℓ=1）——ℤ/n 模型でない。log=`ctmFind`（fuel 走査の関数・choice-free） | 実 μ_{3^ℓ}⊂ℚ(ζ_{3^ℓ}) の `CycMuGroup` 実インスタンス `cmrMu` | μ は円分体自身の中（K̄ の μ_n(K̄) でない）・p=3 |
| `IUT/CyclotomicGKActionReal.lean`（cgar） | **実**。`cgarRestrict` の map は `σ.val.toFun`＝実体自己同型の制限（:71-74）。`cgarAct` の act_one/act_mul は fieldAutId/fieldAutComp の defeq（`Subtype.ext rfl`）。`cgarSigma2`=`cciFromUnits ⟨2,…⟩`＝実代入自己同型 | 実 Gal(ℚ(ζ_{3^ℓ})/ℚ) の実 μ への実作用・非自明 χ(σ₂)=2≠1（`cgar_nontrivial`）・実主語剛性 `cgar_rigidity` | G は円分切片（G_ℚ・G_{ℚ₃} でない）・χ の位相連続性なし |
| `IUT/CyclotomicRigidityAut.lean`（cra） | **実だが初等（監査ディスカウントの当箇所）**。`cra_endo_pow`（:132-148）の本体は y=ζ^{log y}→`Hom.map_pow`→冪法則＝巡回群の「自己準同型は生成元の像で決まる」。`cra_indeterminacy`（:319-325）の本体は `Hom.map_pow` 1 行＝「全冪写像が作用と可換」という*残存宣言*のみ | 自己準同型の冪分類・Gal≅Aut(μ_{3^ℓ})（消去形）・χ の生成元非依存・不定性の残存定理 | **レベル ℓ 単位のみ**（極限対象 T の End/Aut は未分類）・不定性は「残る」と言うだけで「正確に何か」を極限実対象で特定していない・mono-theta 剛性は 0 |
| `IUT/TateModuleZ3.lean`（tmz） | **実**。`tmzLimit`=`limitGrp tmzSystem`＝整合族 subtype（`Profinite.lean:167-168`・真の逆極限）。遷移の忠実性は `tmz_iota_cube`（実 RingHom ι で cube・:217-233）。`tmzActHom` は成分ごと実 `cgarAct`（:300-311）・`tmz_act_compat` は `cli_char_restr` 再利用の本物証明 | T=ℤ₃(1) の構成・G=Gal(ℚ(ζ_{3^∞})/ℚ) 作用・作用=χ 冪（`tmz_act_char`）・射影全射 | **T の自己準同型は 1 本も分類されていない**（G-加群としての剛性は「作用が χ 冪」まで）・ℤ₃ スカラー構造なし・位相なし・幾何的 Tate 加群でない |
| `IUT/CyclotomicLimitIso.lean`（cli）・`CyclotomicCharIso.lean`（cci）・`CyclotomicTowerLimit.lean`（ctl） | **実**（A3 監査で既算入）。`cliChar n`=`cciToUnits (n+1)`・`cli_char_restr`（χ の compat 正方形）・`ctlProfinite`＝実 profinite Gal(ℚ(ζ_{3^∞})/ℚ) | χ: Gal≅(ℤ/3^{n+1})^×・極限 ℤ₃^×=`zpsLimit` | **A3 で既算入——A7 深化の「新規性」には数えない（再消費禁止）** |
| `IUT/Q3TemperedPi1.lean`（q3tp・A5） | **実**（A5 監査で既算入）。`q3tpGalAct` は tmzActHom 経由の実作用 | ℤ₃(1)×ℤ への実 Gal 作用 | A5 資産。A7 側の新 Galois 内容なし（A5 監査自身が明記） |
| `IUT/CyclotomeRecoveryReal.lean`（crr・A6） | **実だが薄い discharge**。`crrGeoAct`（:211-215）は*定義上* `cgarAct` を `crrIso` で読み戻したもの——`crr_geo_compatible` は同変性（`cid_galois_equivariant` の実主語代入）＋往復消去の計算 | M334F 外部仮説 `cycRecGeoCompatible` の実 discharge・復元 μ̂≅実 μ の G-同変同型 | **レベル ℓ 単位**・幾何側=ℚ(ζ) 自身の μ・「χ が同定を決める」canonicity は同変同型 1 本の存在まで（一意性・不定性込みの特徴付けは無い）。A6 資産 |
| `IUT/CyclotomicRigidity.lean`（M322F）・`CyclotomeRecovery.lean`（M334F） | **代理/模型（維持）**。抽象 GK＋ℤ/n 模型・trivial χ 実例 | 抽象枠（実インスタンスで回る設計） | 正直申告ごと**消さず並置**（§4 規約） |

### 1.2 A7 を 0.35 に留めているものの特定（reaudit-A7 §5 の 4 理由に対応）

1. **剛性内容の初等性**: `cra_endo_pow`/`cra_gal_realize` はレベル ℓ の巡回群では
   「生成元の像で決まる」古典・初等の内容（監査が明示的に 0.4→0.35 へ割り引いた当の理由）。
   **極限対象 `tmzLimit` では同じ主張は自明でない**——抽象群準同型 f: T→T は先験的には
   成分ごとに降下せず、「降下する」こと自体が可除性フィルトレーション
   （ker proj_n = T^{3^{n+1}}）を要する本物の定理。ここが**未着手**。
2. **不定性の扱いが「残存宣言」止まり**: `cra_indeterminacy` は「冪写像は作用と可換」
   （`Hom.map_pow` 1 行）で不定性の*実在*を言うのみ。IUT の議論（[EtTh]・[IUTchII] の
   ẑ^× 不定性）が指すのは**「純 Galois 加群としての cyclotome の同定の曖昧さは正確に
   ẑ^×（p 成分: ℤ_p^×）である」という特徴付け**であり、その p=3 実版
   （End(ℤ₃(1))=ℤ₃・Aut=ℤ₃^×・同変性条件は End 上で空）が**未証明**。
3. 円分切片・p=3・K̄/幾何 cyclotome 不在——本ステップでは解消しない（§4 で正直に線引き）。
4. mono-theta 剛性（不定性の*消去*）は 0 のまま——本ステップでも 0（§4）。

**0.45 へ動かすために足す実内容の結論**: (1)(2) を極限レベルで閉じる、すなわち
**「実 ℤ₃(1) の任意の抽象自己準同型の自動分類」＋「Aut(ℤ₃(1)) ≅ 実 ℤ₃^×=`zpsLimit` の
正確な同定」＋「Galois 同変性条件が End 上で空＝不定性はちょうど ℤ₃^×」**。

---

## §2 中心判定 — 最小の本物の新内容は何か（3 候補の評価）

判定基準: (α) 実対象（`tmzLimit`/`cmrMu`）を主語に**新しい**数学を証明するか
（A3/A5 既算入対象の再消費でないか）、(β) 監査ディスカウント理由 §1.2-(1)(2) を
正面から解消するか、(γ) opus 枠で実装可能か（既存イディオムの射程内か）。

### 候補 C1（★採用）: 不定性の正確な特徴付け＝実 ℤ₃(1) の End/Aut 完全分類

**主張**: (i) **可除性フィルトレーション** — y ∈ T が level n で自明（y.val n = 1）⟺
y は T 内の 3^{n+1} 乗（∃z, z^{3^{n+1}}=y・witness は閉じた式）。
(ii) **自動降下・自動線型性** — 任意の抽象群準同型 f: T→T は (i) により
ker proj_n を保ち、各レベルへ降下して冪写像に分類される: (f y)ₙ = (yₙ)^{aₙ}、
指数族 aₙ は mod-整合（＝ℤ₃ の元の指数表示）。**End(ℤ₃(1)) = ℤ₃（自動連続性の代数版）**。
(iii) **Aut(ℤ₃(1)) ≅ `zpsLimit`（実 ℤ₃^×・A3 で実構成済みの実対象への同定）** —
可逆 ⟺ 単元指数族、分類は双方向（実現＋一意性）。
(iv) **不定性の正確性** — 任意の f ∈ End(T) は実 Galois 作用 `tmzActHom` と可換
（同変性条件が空）⟹ **G-同変自己同型群 = Aut(T) = ℤ₃^× ちょうど**。`cra_indeterminacy`
（残存宣言）を「不定性は正確に実 ℤ₃^× である」へ引き上げる。Galois 作用自身の指数族が
χ（`cliChar`）に一致することも定理化（作用は Aut の中で χ の像として座る）。

- (α) **Yes**: (i)(ii) は `tmzLimit` 上の**新定理**（tmz は End を 1 本も分類していない）。
  極限の抽象準同型の降下は初等でない（可除性が証明の本体・ℤ_p の自動連続性の代数化）。
  cli/zps は「Aut の同定先」として使うが、証明の主役は T 側の新内容（再消費でない）。
- (β) **Yes**: §1.2-(1)（初等性→極限剛性へ）と (2)（残存宣言→正確な特徴付けへ）を
  両方正面から解消。監査の 2 大ディスカウント理由への直接回答。
- (γ) **Yes**: witness は全て閉じた式（`tmzWitnessFam` 既存・Nat 除算 e/3^{n+1}）。
  指数簿記は `tmz_find_pow`/`cci_indexG`/`ctm_pow_mod`/`Nat.mul_mod_mul_right` の
  確立イディオムの射程内（§3 に完全スケッチ）。1 箇所（可除性 witness の整合）に
  fable HELP スポットを予約。
- 種別: **本物建設(b)**（実 T 上の新定理）＋**昇格(a) 要素**（`cra_indeterminacy` の
  残存宣言を極限実対象上の正確な特徴付けへ置換——旧定理は消さない）。

**副次案「distinguished generator の固定」は不採用**: ζ を人工的に固定して不定性を
「消した」ことにするのは mono-anabelian の趣旨（生成元非依存・`cra_char_canonical`）に
逆行する反則であり、監査は overclaim と判定する。正直な形は「特徴付け」であって「固定」ではない。

### 候補 C2: G-加群同型としての剛性（μ 同定の Galois 可換性を tmzLimit 上で）

crr が既にレベル ℓ で `crr_iso_equivariant`（cid の実主語代入）を持ち、極限版は
cid イディオムの再適用＋整合簿記が主体になる。**新内容が「同変同型 1 本の存在」に
留まり**、監査ディスカウント理由 (1)(2) を解消しない（同定の*一意性・曖昧さの範囲*を
言わなければ crr の薄さと同じ批判を受ける）。一意性まで言うなら結局 C1 の End 分類が
必要——**C1 に包含**（C1 の (iv) が同変同型の曖昧さ=ℤ₃^× を与える）。単独では不採用。

### 候補 C3: cyclotome の一意性/canonicity（χ が同定を決める・crr の薄さの補強）

レベル ℓ では `cra_endo_pow`＋`cra_indeterminacy`＋`cid_galois_equivariant` の組合せで
ほぼ既知（「χ 捻り同型は単元冪の差を除いて一意」はレベルでは cra の系）。主語が
`cycMuStd`/crr 側に寄るため **A6 の status に流れるリスク**が高く、A7（cyclotome の
G-加群剛性そのもの）の weight 12 を動かす主張として弱い。不採用（C1 完了後の A6 側
後続候補として名指しのみ: crrIso の一意性 up to `zpsLimit`——C1 の系で 60 行級）。

**結論: C1 を採用**。2 ファイル（A7d+A7e）に分割し、A5a/A5b・A8a/A8b 前例と同じ
「丸め境界の保険」構成とする（§5: 表示 49 の境界が A7 ≥ 0.4134 のため、単発 0.40 着地
だと 48 のまま——2 本目で 0.42–0.45 を狙う）。

---

## §3 選定ステップ — A7d `TateModuleEndo.lean`（tme）＋ A7e `TateModuleIndeterminacy.lean`（tmi）

prefix 衝突チェック（本日 grep 済み）: `tme`・`tmi` とも未使用（`ctmr_` は別識別子・衝突なし）。

依存 DAG:

```
tmz（既存 T=ℤ₃(1)）──→ tme（End 分類 = A7d）──→ tmi（Aut≅ℤ₃^×・不定性の正確性 = A7e）
         cra（レベル分類・既存）──↗          cli/zps（同定先・既存）──↗
```

### 3.1 A7d — `IUT/TateModuleEndo.lean`（prefix `tme`・依存: TateModuleZ3・CyclotomicRigidityAut・CyclotomicCharIso・Zmod3PowUnits）

ヘッダ分類: **[実／本物建設(b)]**。complete_pct 影響: A7d 単体では申告せず、A7e 到達で
親が独立監査に諮る（A7d 単独完了時のフォールバック申告は §5）。

```lean
/- TME-0: 極限群の冪は成分ごと（小補題・k 帰納） -/
theorem tme_pow_level (y : tmzLimit.carrier) (k n : Nat) :
    (tmzLimit.pow y k).val n = (tmzG n).pow (y.val n) k
  -- k 帰納・limitGrp.mul は成分ごと（Profinite.lean:169 の定義で rfl 級）

/- TME-1: 核の可除性の指数側 — level n 自明なら上段の find は 3^{n+1} で割れる -/
theorem tme_find_dvd (n k : Nat) (y : tmzLimit.carrier) (hy : y.val n = (tmzG n).one) :
    3 ^ (n + 1) ∣ ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val)
  -- y.property (n ≤ k+n+1) で y.val n = tmzT(y.val (k+n+1)) = ζ_{n+1}^{find(…) % 3^{n+1}}、
  -- one = ζ^0（ctmPow _ 0 = one の小補題・無ければ +10 行）→ cci_indexG で find % 3^{n+1} = 0
  -- → Nat.dvd_of_mod_eq_zero

/- TME-2: ★可除性フィルトレーションの witness（本ファイルの数学的本体・fable スポット予約） -/
def tmeRootFam (n : Nat) (y : tmzLimit.carrier) (k : Nat) : (tmzG k).carrier :=
  (cmrGrp (k + 1) (by omega)).pow (cmrZeta (k + 1) (by omega))
    (ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val) / 3 ^ (n + 1))
theorem tmeRootFam_compat (n : Nat) (y : tmzLimit.carrier)
    (hy : y.val n = (tmzG n).one) : Compatible tmzSystem (tmeRootFam n y)
  -- e_k := find(y_{k+n+1}) / 3^{n+1}。i ≤ j に対し e_j % 3^{i+1} = e_i を示す:
  --   y.property (i+n+1 ≤ j+n+1) ＋ tmz_find_pow ＋ cci_indexG で
  --   find(y_{j+n+1}) % 3^{(i+1)+(n+1)} = find(y_{i+n+1})、
  --   TME-1 の可除性で find = e·3^{n+1}（Nat.div_mul_cancel）、
  --   3^{(i+1)+(n+1)} = 3^{i+1}·3^{n+1}（Nat.pow_add）、
  --   (e_j·3^{n+1}) % (3^{i+1}·3^{n+1}) = (e_j % 3^{i+1})·3^{n+1}（Nat.mul_mod_mul_right）、
  --   3^{n+1} > 0 で約分（Nat.eq_of_mul_eq_mul_right）。
  --   あとは tmzT の定義＋tmz_find_pow＋ctm_pow_mod で ζ 側へ翻訳（tmz_t_comp と同型の簿記）
theorem tme_ker_pow (n : Nat) (y : tmzLimit.carrier) (hy : y.val n = (tmzG n).one) :
    ∃ z : tmzLimit.carrier, tmzLimit.pow z (3 ^ (n + 1)) = y
  -- witness z := ⟨tmeRootFam n y, tmeRootFam_compat n y hy⟩（閉じた式・∃ は Prop ゴール内）。
  -- 成分 k: tme_pow_level → pow (ζ^{e_k}) 3^{n+1} = ζ^{e_k·3^{n+1}} = ζ^{find(y_{k+n+1})}
  -- （cycRig_pow_mul＋Nat.div_mul_cancel）= tmzT(y_{k+n+1}) = y.val k（y.property）

/- TME-3: ★核の保存（自動降下の鍵） — 任意の抽象 Hom は ker proj_n を保つ -/
theorem tme_ker_preserved (f : Hom tmzLimit tmzLimit) (n : Nat) (y : tmzLimit.carrier)
    (hy : y.val n = (tmzG n).one) : (f.map y).val n = (tmzG n).one
  -- obtain ⟨z, hz⟩ := tme_ker_pow n y hy; f y = f(z^{3^{n+1}}) = (f z)^{3^{n+1}}（Hom.map_pow）
  -- 成分 n: tme_pow_level → ((f z).val n)^{3^{n+1}} = one（cra_pow_ord (n+1)）

/- TME-4: 降下（witness 経由の choice-free レベル写像） -/
def tmeLift (n : Nat) (u : (tmzG n).carrier) : tmzLimit.carrier :=
  ⟨tmzWitnessFam n u, tmzWitnessFam_compat n u⟩          -- 既存の閉じた式 witness
theorem tme_lift_diff_ker (n : Nat) (y : tmzLimit.carrier) :
    (tmzLimit.mul y (tmzLimit.inv (tmeLift n (y.val n)))).val n = (tmzG n).one
  -- y と「y_n を通る標準 witness」の差は ker proj_n（成分 n で ζ^{find} = y_n・逆元消去）
def tmeLevel (f : Hom tmzLimit tmzLimit) (n : Nat) : Hom (tmzG n) (tmzG n) where
  map := fun u => (f.map (tmeLift n u)).val n
  map_mul := …
  -- tmeLift n (uv) と (tmeLift n u)·(tmeLift n v) の差 d は ker proj_n
  -- （成分 n の指数: tmz_mul_find で (find u + find v) % 3^{n+1} 一致・ctm_pow_mod）
  -- → f.map_mul＋tme_ker_preserved で (f d).val n = 1 → 成分 n で乗法保存
theorem tme_level_map (f : Hom tmzLimit tmzLimit) (n : Nat) (y : tmzLimit.carrier) :
    (f.map y).val n = (tmeLevel f n).map (y.val n)
  -- y = (tmeLift n y_n)·d（d ∈ ker proj_n・tme_lift_diff_ker）＋ tme_ker_preserved

/- TME-5: ★End(ℤ₃(1)) の完全分類（自動 ℤ₃-線型性・A7d ヘッドライン） -/
def tmeChar (f : Hom tmzLimit tmzLimit) (n : Nat) : Nat :=
  craEndoChar (n + 1) (by omega) (tmeLevel f n)            -- choice-free（ctmFind 走査）
theorem tme_endo_pow (f : Hom tmzLimit tmzLimit) (y : tmzLimit.carrier) (n : Nat) :
    (f.map y).val n = (cmrGrp (n + 1) (by omega)).pow (y.val n) (tmeChar f n)
  -- tme_level_map ＋ cra_endo_pow（レベル分類の消費）＋ cra_pow_log で y_n^{a} 形へ
theorem tme_char_compat {i j : Nat} (h : i ≤ j) (f : Hom tmzLimit tmzLimit) :
    tmeChar f j % 3 ^ (i + 1) = tmeChar f i % 3 ^ (i + 1)
  -- y := tmeLift j ζ_{j+1} に tme_endo_pow を level j と level i で適用し、
  -- (f y).property (i ≤ j) の整合＋tmz_find_pow＋cci_indexG で合流
  -- （cli_char_restr の差分帰納は不要——f y 自身の整合族性が直接使える）
theorem tme_endo_ext (f g : Hom tmzLimit tmzLimit)
    (h : ∀ n, tmeChar f n % 3 ^ (n + 1) = tmeChar g n % 3 ^ (n + 1)) : f = g
  -- cra_hom_ext（輸入）＋ Subtype.ext/funext ＋ tme_endo_pow ＋ cra_pow_reduce
structure TmeEndoData where                                 -- capstone（新規証明ゼロ）
  ker_pow : ∀ n y, y.val n = (tmzG n).one → ∃ z, tmzLimit.pow z (3 ^ (n + 1)) = y
  ker_preserved : ∀ f n y, y.val n = (tmzG n).one → ((f : Hom tmzLimit tmzLimit).map y).val n = (tmzG n).one
  endo_pow : ∀ f y n, (Hom.map f y).val n = (cmrGrp (n+1) _).pow (y.val n) (tmeChar f n)
  char_compat : ∀ {i j} (h : i ≤ j) f, tmeChar f j % 3 ^ (i+1) = tmeChar f i % 3 ^ (i+1)
def tmeEndoData : TmeEndoData
```

主要 public 定理名（監査対象）: `tme_pow_level`・`tme_find_dvd`・`tmeRootFam_compat`・
`tme_ker_pow`・`tme_ker_preserved`・`tme_lift_diff_ker`・`tmeLevel`・`tme_level_map`・
`tmeChar`・`tme_endo_pow`・`tme_char_compat`・`tme_endo_ext`・`tmeEndoData`。

工数: **500–650 行**。tier **M（opus）**・**fable HELP スポット 1 を TME-2
（`tmeRootFam_compat` の div/mod 簿記）に予約**（詰まった場合のみ・イディオム自体は
`tmz_t_comp`/`cli_char_restr` に写経元あり）。

### 3.2 A7e — `IUT/TateModuleIndeterminacy.lean`（prefix `tmi`・依存: TateModuleEndo・Zmod3PowUnitsSystem・CyclotomicLimitIso）

ヘッダ分類: **[実／本物建設(b)＋昇格(a)]**（`cra_indeterminacy` の残存宣言を極限実対象の
正確な特徴付けへ昇格・旧定理は消さない）。

```lean
/- TMI-1: 整合冪族 → T の自己準同型（データ） -/
structure TmiExpFam where
  a : Nat → Nat
  compat : ∀ {i j : Nat}, i ≤ j → a j % 3 ^ (i + 1) = a i % 3 ^ (i + 1)
def tmiPowHom (F : TmiExpFam) : Hom tmzLimit tmzLimit where
  map := fun y => ⟨fun n => (cmrGrp (n+1) _).pow (y.val n) (F.a n), …⟩
  -- 整合: tmz_find_pow＋ctm_pow_mod＋Nat.mul_mod＋F.compat（tmz_act_compat の指数簿記の写経）
  map_mul := …                                             -- cra_pow_mul_dist 成分ごと
theorem tmi_pow_char (F : TmiExpFam) (n : Nat) :
    tmeChar (tmiPowHom F) n % 3 ^ (n + 1) = F.a n % 3 ^ (n + 1)
  -- 分類と構成の往復（tme_endo_pow＋cci_indexG）

/- TMI-2: ★同変性条件は End(T) 上で空（不定性の総和・cra_indeterminacy の極限昇格） -/
theorem tmi_endo_gal_commute (f : Hom tmzLimit tmzLimit) (s : ctlProfinite.carrier)
    (y : tmzLimit.carrier) :
    f.map ((tmzActHom s).map y) = (tmzActHom s).map (f.map y)
  -- 成分 n: 両辺とも y_n の冪（tme_endo_pow＋tmz_act_char）・指数は Nat.mul の可換で一致
  -- （＝「任意の自己準同型が Galois 同変」——同変性は End を一切絞らない、が正確な主張）

/- TMI-3: Galois 作用の指数族は χ（作用は End の中で χ の像として座る） -/
theorem tmi_act_char (s : ctlProfinite.carrier) (n : Nat) :
    tmeChar (tmzActHom s) n % 3 ^ (n + 1) = ((cliChar n).map (s.val n)).val % 3 ^ (n + 1)
  -- tme_endo_pow を tmz_act_char と突き合わせ（cci_indexG）

/- TMI-4: 可逆 ⟺ 単元指数族・逆写像の整合（単元逆の mod 一意性） -/
theorem tmi_inv_congr {i j : Nat} (h : i ≤ j) (a : Nat) (ha : ¬ 3 ∣ a) :
    zpuInvL (j + 1) a % 3 ^ (i + 1) = zpuInvL (i + 1) a % 3 ^ (i + 1)
  -- b·(a·b') ≡ b ≡ b'·(a·b) の mod 簿記（zpuInvL_one 二枚・zpu_mod_mul）
theorem tmi_unit_of_iso (f g : Hom tmzLimit tmzLimit)
    (hl : ∀ y, g.map (f.map y) = y) (hr : ∀ y, f.map (g.map y) = y) (n : Nat) :
    ¬ 3 ∣ tmeChar f n
  -- tmeLevel へ降ろし cra_unit_of_iso（tme_level_map で左右逆がレベルへ降下）

/- TMI-5: ★Aut(ℤ₃(1)) ≅ 実 ℤ₃^×（zpsLimit・A7e ヘッドライン） -/
def tmiFromUnits (u : zpsLimit.carrier) : Hom tmzLimit tmzLimit :=
  tmiPowHom ⟨fun n => (u.val n).val, …⟩                    -- 整合は u.property（zpsT）から
theorem tmi_from_units_iso (u : zpsLimit.carrier) :
    (∀ y, (tmiFromUnits (zpsLimit.inv u)).map ((tmiFromUnits u).map y) = y) ∧
    (∀ y, (tmiFromUnits u).map ((tmiFromUnits (zpsLimit.inv u)).map y) = y)
  -- zpsLimit の実逆元（成分 zpuGrp.inv）＋ cra_pow_reduce/zpuInvL_one・tmi_inv_congr
theorem tmi_aut_classify (f g : Hom tmzLimit tmzLimit)
    (hl : ∀ y, g.map (f.map y) = y) (hr : ∀ y, f.map (g.map y) = y) :
    ∃ u : zpsLimit.carrier, ∀ y, f.map y = (tmiFromUnits u).map y
  -- witness u := ⟨fun n => ⟨tmeChar f n % 3^{n+1}, Nat.mod_lt, zpu_mod_nd3 (tmi_unit_of_iso)⟩,
  --              tme_char_compat から zps 整合⟩（閉じた式・∃ は Prop ゴール内のみ）
theorem tmi_units_inj (u v : zpsLimit.carrier)
    (h : ∀ y, (tmiFromUnits u).map y = (tmiFromUnits v).map y) : u = v
  -- 生成元族 tmeLift n ζ で読み cci_indexG・成分ごと Subtype.ext

/- TMI-6: capstone — 不定性の正確な特徴付け（正直: 消去ではない） -/
structure TmiIndeterminacyData where
  endo : TmeEndoData                                       -- End(T) の完全分類（tme）
  gal_commute : ∀ f s y, (Hom.map f) ((tmzActHom s).map y) = (tmzActHom s).map (Hom.map f y)
  act_char : ∀ s n, tmeChar (tmzActHom s) n % 3 ^ (n+1) = ((cliChar n).map (s.val n)).val % 3 ^ (n+1)
  aut_realize : ∀ u : zpsLimit.carrier, (左右逆の ∧ 形 = tmi_from_units_iso)
  aut_classify : (tmi_aut_classify の ∀∃ 形)
  aut_inj : (tmi_units_inj の形)
def tmiIndeterminacyData : TmiIndeterminacyData
```

主要 public 定理名（監査対象）: `TmiExpFam`・`tmiPowHom`・`tmi_pow_char`・
`tmi_endo_gal_commute`・`tmi_act_char`・`tmi_inv_congr`・`tmi_unit_of_iso`・
`tmiFromUnits`・`tmi_from_units_iso`・`tmi_aut_classify`・`tmi_units_inj`・
`tmiIndeterminacyData`。

工数: **400–550 行**。tier **M（opus）**（新イディオム無し——tme の分類＋zps/cli の
実対象へ突き合わせる簿記が主体）。

### 3.3 choice-free 戦略（両ファイル共通・実装規約）

- **新規 `Classical.choice` 禁止**（`#print axioms` = [propext, Quot.sound] 維持）。
  witness は全てデータ: 可除性の根 = `tmeRootFam`（Nat 除算の閉じた式）・リフト =
  `tmzWitnessFam`（既存）・指数抽出 = `ctmFind`/`craEndoChar`（fuel 走査）・単元逆 =
  `zpuInvL`。**∃ は Prop ゴール内のみ**（`tme_ker_pow`・`tmi_aut_classify`）。
  「End(T) ≅ 指数族」の全単射を関数として総体化することは choice なしでは不可能な形に
  しない——分類は「∀f ∃族（witness 明示）＋一意性」の消去形で述べる。
- 禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。3^ℓ を omega に渡さない（`zpu_pow_pos`/`zpu_pow_dvd`/
  `Nat.pow_add`/`Nat.mul_mod_mul_right` 経由——`Nat.mul_mod_mul_right` が core に無い
  場合のみ自前補題 +15 行）。
- 既存モジュール（tmz/cra/crr/M322F/M334F）は**一切改変しない**。`cra_indeterminacy` は
  消さず、tmi ヘッダで「レベル残存宣言 → 極限の正確な特徴付けへの昇格・消去ではない」と
  名指しする。

---

## §4 正直な線引き — 本ステップが本物に**しない**もの（overclaim 禁止・監査への申告）

1. **mono-theta 円分剛性（[EtTh]）は依然 0**: 本ステップは ẑ^×（p=3: ℤ₃^×）不定性を
   **殺さない**。「不定性は正確に実 ℤ₃^× である」と特徴付けるだけであり、テータ環境が
   この不定性を消す仕組み（IUT 本丸・柱 E/D 後続）は範囲外。A7=1 には依然遠い。
2. **p = 3 固定・円分切片限定**: G は Gal(ℚ(ζ_{3^∞})/ℚ)（G_ℚ の可解商）。実 G_{ℚ₃}・
   実 G_ℚ・一般素数 p は含めない（cgar/ctl の正直申告を弱めず継承）。
3. **位相は形式化しない**: 「自動連続性」は可除性フィルトレーション経由の**代数版**
   （ker proj_n の保存）であり、`limitTopology` に対する連続写像の定理としては述べない
   （後続候補: `Topology.lean` の実位相で tmiPowHom の連続性——本ステップ範囲外）。
4. **End(ℤ₃(1)) ≅ ℤ₃ の「ℤ₃」は指数族表示**: 分類先は `TmiExpFam`（整合 Nat 族）と
   単元部分の `zpsLimit`（実 ℤ₃^×）であり、**A2 の実 ℤ₃ 環オブジェクト（z3）との環同型
   接続は未形式化**（End の環構造・合成=積も未・後続の昇格ターゲットとして名指し）。
5. **幾何側は不在のまま**: μ 塔は各段別々の実円分体に住む（K̄ なし）。楕円曲線の
   幾何的 Tate 加群・π₁ の幾何的 cyclotome ではない（tmz の限定を継承）。
6. 既存の正直な限定（M322F :70-73・cra (i)-(iv)・tmz (i)-(iv)・crr (i)-(iii)）は
   **一切消さない・弱めない**。本ステップは並置＋昇格のみ。

---

## §5 status 見込み・柱A% 算術（本日 `tools/compute_complete_pct.py` の丸め仕様で検算済み）

台帳実測: 柱 A weights 総和 = 100・Σ(w·s) = **47.74**
（A1 6.8 + A2 5.2 + A3 9.0 + A4 7.0 + A5 1.0 + A6 7.7 + A7 4.2 + A8 6.84 + A9 0）。
A7（weight 12）を s へ動かすと Σ_A = 43.54 + 12s。丸めは Python `round`＝**銀行丸め**
（`round(48.5) = 48` に注意——48.5 ちょうどでは 49 にならない）:

| A7 status | Σ_A | round | 表示 |
|---|---|---|---|
| 0.35（現在） | 47.74 | 48 | 48 |
| 0.40 | 48.34 | 48 | 48（**動かない**） |
| 0.41 | 48.46 | 48 | 48 |
| 0.4133 | 48.4996 | 48 | 48 |
| **0.4134** | **48.5008** | **49** | **49（境界）** |
| 0.42 | 48.58 | 49 | 49 |
| 0.45 | 48.94 | 49 | 49 |

**正確な丸め境界: Σ_A > 48.5 ⟺ 12·s > 4.96 ⟺ s > 0.41333…、すなわち A7 ≥ 0.4134**
（銀行丸めのため 48.5 ちょうど＝s=0.41333… は 48 のまま）。実務上 status は 2 桁刻みで
運用しているため **A7 ≥ 0.42 が表示 49 の実効条件**。タスク指示の概算
（0.4→48.34→48・0.42→48.58→49）と一致することを検算した。

保守的見込み（**最終確定は独立監査**・敵対的既定=模型・過大主張しない）:

| 到達点 | 申告見込み | 根拠 / リスク |
|---|---|---|
| A7d のみ（tme） | 0.35 → **0.38–0.40**（表示 48 のまま） | End 分類は新実定理だが Aut≅実 ℤ₃^× の同定・不定性の正確性が未——監査は「分類の半分」と見る可能性が高い |
| A7d+A7e（tme+tmi） | 0.35 → **0.42–0.45**（表示 49 見込み） | §1.2-(1)(2) の両ディスカウントへの直接回答＋実対象 `zpsLimit` への同定。**ただし監査が「依然 mono-theta 0・円分切片」を重く見て 0.40 に置けば表示 48 のまま**——この下振れは正直に想定内とする |

上限メモ: 本ステップ完了でも **0.45 を超える申告はしない**（§4-(1)(2)(5) が残る限り
「忠実な部分ケース 0.5」に届かない、が前回監査の運用）。

---

## §6 実装計画（親向け）

- **直列依存**: tme → tmi（tmi は tmeChar/tme_endo_pow を消費）。並列化不可の 2 段。
  各ラウンドの残り並列枠は他柱の complete_pct 前進案件で埋める（完全証明ファースト規則
  §5 準拠・水増しの capstone/クローンで埋めない）。
- **tier/model 配分**（CLAUDE.md tier 規則準拠）:
  - ラウンド 1: **tme [M=opus] 1 本**。fable は TME-2（`tmeRootFam_compat` の div/mod
    簿記）で opus が 2 回失敗した場合の HELP スポットのみ（新イディオム発明ではなく
    詰まり解決の限定投入）。
  - ラウンド 2: **tmi [M=opus] 1 本**（新イディオム無し・fable 不要見込み）。
  - 完了時に独立再監査 1 本（監査者はいつも通り自走で `bash build.sh`＋全 public 対象の
    `#print axioms` 列挙・敵対的判定）。
- **サブエージェント規約**: 新規ファイルのみ作成。共有ファイルは親が統合時に一括更新——
  `IUT.lean`（import 2 行: TateModuleEndo・TateModuleIndeterminacy）・`build.sh`
  （検証対象の追記）・`tools/gen_graph.py` の `PILLAR` 辞書（両ファイル → "A"）・
  `python3 tools/gen_graph.py` 再生成。`target_ledger.json` A7 status・
  `graph-meta.json` complete_pct/complete_note・`dashboard.md` 二軸表は**独立監査の
  確定値で**更新（実装者は触らない）。
- **ヘッダ必須事項**（両ファイル）: 二軸分類（tme: [実／本物建設(b)]・tmi: [実／
  本物建設(b)＋昇格(a)]）・complete_pct 影響 1 行・置換/昇格対象の名指し
  （`cra_indeterminacy` の残存宣言→極限特徴付け・消去ではない旨）・正直な限定 §4 の
  (1)–(6) を転記。
- **フォールバック**: TME-2 が fable 投入でも閉じない場合、A7d を「核保存
  `tme_ker_preserved` を n=0 特殊ケース＋一般 n は ∃-仮説受け」の縮退形に**しない**
  （それは骨格化＝水増し）。代わりに A7d を分割凍結し、ユーザーへ報告して指示を仰ぐ
  （CLAUDE.md §2 の停止規則）。

---

### 付記: 本設計自身の正直な申告

本ドキュメントは設計であり complete_pct を 0 前進させる（動かさない）。§5 の数値は
実装＋独立監査を経て初めて動く。判定はすべて敵対的既定（=模型）から出発する
AUDIT_RUBRIC 準拠の再監査が下し、本設計の見込みを下回る（0.40 着地・表示 48 のまま）
可能性は現実的にある——その場合も「A7 は前進したが表示は動かず」と正直に報告する。
