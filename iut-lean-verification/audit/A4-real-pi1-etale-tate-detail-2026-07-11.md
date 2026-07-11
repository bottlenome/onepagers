# A4「実 π₁^ét」詳細化 — A5c 実被覆塔のデッキ逆極限を実 Tate 曲線 E_q(ℚ₃) の実 pro-l π₁^ét 切片へ組み上げる最小ステップ設計

日付: 2026-07-11 ／ 種別: **設計ドキュメントのみ**（実装コード無し・共有ファイル不更新）
分類: **[実／昇格(a)+本物建設(b) の設計]** — 昨日完成の A5c 実中間被覆塔
（`Q3TateCoverTower.lean`・独立監査確定 A5 0.15）を中心テコに、柱A 最大 weight 残項目
**A4（実 π₁^ét・w14・status 0.5）** の最小 complete_pct 前進ステップを opus 実装枠へ
渡せる粒度に分解する。**complete_pct 影響: 本ドキュメント自体は 0（設計のみ）**。
status 見積りは §5（保守値・最終確定は独立監査・AUDIT_RUBRIC 準拠）。

判定は全て def/theorem **本体の精読**による（ヘッダ主張は使わない・敵対的既定=模型）。
本日精読: `Q3TateCoverTower.lean`（全 319 行）・`Q3TateCurve.lean`・`Q3TateDeck.lean`・
`TemperedTower.lean`・`Profinite.lean`（InverseSystem/limitGrp/limit_universal）・
`ProfinitePi1.lean`・`GaloisCategory.lean`（GAction/levelAction/level_transition_equivariant）・
`GaloisPi1Iso.lean`・`TateCoverGroup/Cat/Galois/FiberFunctor` ヘッダ＋主要 def・
`LocalCFT.lean`（padicSystem/Zp/toZp）・`target_ledger.json`・`tools/compute_complete_pct.py`・
`graph-meta.json` 柱A complete_note・`audit/A-next-leverage-scope-2026-07-10.md`（旧 A4 判定）。

---

## §1 現状実測 — A4 資産の実測表と「0.5 で止まっている理由」

### 1.1 既存 A4 資産（本体判定）

| モジュール | 本体判定 | 何を証明しているか | 正直な限定（0.5 の実体） |
|---|---|---|---|
| `Profinite.lean` (M13) | **実（汎用機構）** | `InverseSystem`/`limitGrp`/`limitProj`/`limit_universal`（逆極限の普遍性・完全証明・choice-free）、実例 `zhat = lim ℤ/n` | 主語は抽象 Grp。ẑ は本物の逆極限だが**どの実曲線・実体の π₁ でもない** |
| `GaloisCategory.lean` (M14) | **実（汎用機構）** | `GAction`・`equivariant_is_right_mul`（Aut(普遍ファイバー)≅G）・`levelAction`（極限群の有限レベル作用）・`level_transition_equivariant`（作用＝自然変換） | levelAction の作用先は抽象 `(S.G i).carrier`（群自身）。**実被覆のファイバーに作用する実例ゼロ** |
| `GrothendieckGalois.lean` (M277F) | 実（機構）＋退化実例 | π₁^ét=Aut(F)（ファイバー関手の自己同型群）の建設 | 実例は分裂/自明ケース。「pro-有限位相・逆極限としての構造は未」と自己申告（M287F が半分充填） |
| `ProfinitePi1.lean` (M287F) | 実（機構）＋**自明実例** | `ProfinitePi1Tower`→`profPi1Limit = lim Gal(Lᵢ/K)`＋副有限位相（開核・近傍基）・`profPi1_toPiEt` 骨組み | restr は witness データ。実例は**自明塔 lim Gal(ℚ/ℚ)=1** のみ（:259-264 本体確認）。非自明 witness は ctlProfinite が discharge 済みだが**A3 0.7 の監査根拠として計上済み**（再ラベル＝二重計上不可・A-next-leverage-scope §2 判定） |
| `GaloisPi1Iso.lean` (M286F) | 実＋狭い実例 | Gal(L/K)→Sym(根) モノドロミー・忠実性⟹単射・第一同型定理・全モノドロミー | 全モノドロミーは **2 根被覆のみ**。一般連結被覆の忠実性は仮説受領 |
| `TateCoverGroup/Cat/Galois/FiberFunctor/SurrogateCapstone` (M188F/191F/195F/200F) | **代理（surrogate）** | `tateProfinite := zhat`（:151 本体確認・**裸の ẑ**）が抽象 `tateLevelCover n`（担体=zmod n の剰余ファイバー）に作用。Galois 圏公理 G1–G6 充足・Aut(F)≅ẑ 復元 | π₁ の主語が **どの実曲線の被覆群でもない**。CLAUDE.md §2(a) が昇格例として名指しする「Tate surrogate→実 π₁^ét」の当の surrogate |
| （隣接・A5 計上済み）`Q3TateDeck`/`Q3TateCoverTower` | **実**（A5a/A5c で計上済み） | 実被覆 ℚ₃^×→E_q のデッキ ℤ（自由・推移）・実中間被覆 q3tcHom・実有限デッキ q3tcDeckFin・実塔 | **逆極限側は未実現**（A5c 正直な限定(2)「塔の逆極限 ℤ_l との接続は M374F 既存機構の消費に留める（実逆極限の幾何的実現は後続）」＝監査も「(4) 逆極限 ℤ_l は新規実現なし」と明記） |
| （隣接）`TemperedTower.lean` (M374F) | 実（群論のみ） | `ttwDeckTower l k = zmod(l^k)` の逆系＝`padicSystem l`・逆極限 `ttwInverseLimit l = Zp l`・`toZp` 単射 | **裸の ℤ/l^k・裸の ℤ_l**。本体（:23-100）は intGrp の商と極限のみで、被覆・曲線は一切登場しない（E_{q^{l^n}} はコメント上の名前だけ） |

### 1.2 A4 が 0.5 で止まっている正確な理由（complete_note「機構は実だが実例が自明/退化」の実体）

1. **非自明な実インスタンスの不在**: profinite π₁ 機構（limitGrp・副有限位相・Aut(F)・
   levelAction）は全て本物だが、それが「実際の幾何対象の実際の被覆のデッキ群の逆極限」
   として発火した実例が**一つも無い**（自明塔 lim Gal(ℚ/ℚ)=1・抽象 ẑ 代理・2 根被覆）。
2. **AUDIT_RUBRIC の基準**「Galois 群/π₁^ét = 実際の環自己同型/**被覆の群 or その逆極限**」
   を満たす対象が、有限レベル（A5c の q3tcDeckFin・A5 計上）までしか存在せず、
   **逆極限レベルの π₁ 対象**（＝A4 の主語そのもの）が実曲線上に立っていない。
3. 旧判定（A-next-leverage-scope §2・2026-07-10）の A4 ルート「円分被覆 Spec ℚ(ζ)→Spec ℚ の
   ファイバー推移性」は Φ の根分解の新イディオム（600–900 行・fable 1）＋ A3 二重計上リスクで
   次点止まりだった。**当時存在しなかった A5c 実被覆塔が、より軽い本命ルートを開いた**（§2）。

---

## §2 中心判定 — A5c 塔の有限デッキ群の逆極限は「実 π₁^ét(E_q) の断片」か

### 2.1 数学的判定（正直に）

A5c が実装した中間被覆 E_{qⁿ}(ℚ₃) = ℚ₃^×/(qⁿ)^ℤ → E_q(ℚ₃) = ℚ₃^×/q^ℤ は、Tate
一意化の下で**本物の巡回 n-同種（degree n の有限エタール被覆）の ℚ₃-点への制限**であり、
その核 q^ℤ/(qⁿ)^ℤ ≅ ℤ/n（q3tc_ker で特徴付け済み）は定数群スキーム ℤ/n の点群に
一致する。したがって塔 {E_{q^{l^k}} → E_q}_k のデッキ群 ℤ/l^k の逆極限 ℤ_l は、
数学的には **π₁(E_q) の q-格子方向の pro-l 商**（π₁^temp = ℤ₃(1)×ℤ の離散部 ℤ の pro-l
完備化・π₁^ét の格子側切片）である。**判定: 本物の断片である**——ただし次の正直な留保つき:

- 形式化が見ているのは **K-点の群としての被覆**（全射群準同型＋有限デッキ作用）であり、
  スキーム・エタールサイト・位相は無い。「被覆の群の逆極限」という RUBRIC の群論的読みでは
  実、「エタール位相のファイバー関手の自己同型群」という完全形では影。
- 断片は **pro-l・格子方向のみ**。π₁^ét(E_q,ℚ̄₃) ≅ ẑ×ẑ(1) の μ 方向（ℤ₃(1)=tmzLimit・
  A7 計上済み）とは本ステップでは接続しない（二重計上回避のため意図的に触らない）。

### 2.2 ただし「逆極限を再輸出するだけ」では動かない — 何が genuinely 新規か

既算入の資産（敵対的に列挙・graph-meta A5c 監査注記と突合済み）:

- A5c: q3tc_q_pow・q3tcHom（E_{qⁿ}→E_q・m と m·n の間のみ）・q3tc_surjective/q3tc_ker・
  q3tcDeckFin（有限デッキ・**忠実性は未証明と監査が明記**）・q3tc_deck_over（片方向のみ）・
  q3tc_tower_nested・q3tcTowerDeck（= q3tcDeckFin の名前替え・carrier=実曲線の rfl 確認）。
- A5a: q3tdDeck（普遍被覆 ℚ₃^×→E_q のデッキ ℤ・自由・推移）。
- M374F: 裸の padicSystem l・Zp l・toZp・toZp_injective。

**未実現（＝本ステップの新規実内容）**——A5c 正直な限定 (2) が明示 defer した「実逆極限の
幾何的実現」そのもの:

| # | 新規対象 | なぜ A4 か |
|---|---|---|
| N1 | **塔の隣接段の実被覆** E_{q^{l^{k+1}}} → E_{q^{l^k}}（q3tcHom は m→m·n の 2 段のみで、塔内部の段間射は def として存在しない。q3tc_tower_nested は膜（membership 含意）だけ） | 実被覆の**余過滤塔**（cofiltered tower）を曲線間の射として完備にする＝π₁ を取る対象の完成 |
| N2 | **デッキ遷移の幾何的実現**（等変正方形）: 段間実被覆が ℤ/l^{k+1} 作用を ℤ/l^k 作用（zmodTrans 経由）へ運ぶ | padicSystem l（裸の逆系）が「**実被覆の塔のデッキ群の逆系**」であることの初の証明。M14-6 `level_transition_equivariant` の実曲線初実例 |
| N3 | **逆極限群 ℤ_l の実塔への作用**（各段の実曲線に射影経由で作用・段間自然性） | **π₁^ét 対象そのもの**が実曲線族に「ファイバー関手の自然変換」として作用する初実例＝M14-5 `levelAction` の実昇格 |
| N4 | **忠実性**（有限段: [qʲ]=[1]⟹n∣j、極限: 全段自明作用⟹γ=1） | A5c 監査の明示ディスカウント(1)「忠実性/自由性未証明＝ℤ/n が真に位数 n を実現する非退化性は未確立」の正面 discharge。RUBRIC「身代わりでない」（ℤ_l が実際に作用の群として非退化）の認証 |
| N5 | **ファイバー＝軌道**（q3tcHom のファイバー ⟺ ℤ/n 軌道の iff。A5c は deck_over 片方向のみ） | 中間被覆が **Galois 被覆**であることの完成（q3td_fiber_orbit の有限デッキ版・新規） |
| N6 | **普遍性・比較**: 極限の普遍性の π₁ 対象への実装＋離散デッキ ℤ（A5a）→ ℤ_l の完備化が実塔の作用と両立（「π₁^ét 切片＝π₁^top 切片の pro-l 完備化」比較定理の実現） | π₁^ét の**普遍的特徴付け**＝A4 主語の対象性 |
| N7 | **Tate surrogate の主語替え**: 裸の `tateProfinite = ẑ` が `ttwProfiniteToLadic`（Ẑ↠ℤ_l・M374F 既存）経由で**実曲線に作用**する GAction | CLAUDE.md §2(a) 名指しの昇格例「Tate surrogate→実 π₁^ét」の literal な第一歩（圏登録 A5d とは別・作用レベル） |

### 2.3 候補比較（最小の実新規内容）

| 候補 | 内容 | 新規実対象 | A4/A5 帰属 | 工数/tier | リスク |
|---|---|---|---|---|---|
| **C1（選定）** | N1–N5＋capstone（π₁ 対象の建設＝実塔＋実逆極限作用＋忠実性＋Galois 性） | 逆極限レベルの実 π₁ 断片（初） | **A4**（主語＝profinite π₁ 対象。A5 の主語＝tempered 拡大 ℤ₃(1)×ℤ とは別） | 380–480 行 [M/opus] | 低（全て既存イディオムの組合せ・§3.4） |
| **C2（選定・保険）** | N6–N7＋普遍性 capstone（比較定理＋surrogate 主語替え） | π₁ 対象の普遍的特徴付け＋surrogate 昇格 | **A4**（昇格(a) の名指し例） | 250–350 行 [M/opus] | 低（rfl 級が多い） |
| C3（却下） | 円分被覆 Spec ℚ(ζ_{3^ℓ})→Spec ℚ のファイバー推移性（旧 A-next-leverage §2 案） | Φ_{3^ℓ} 根分解 | A4 だが重い | 600–900 行 [M+fable] | 新イディオム・A3 二重計上懸念 |
| C4（却下） | ℤ_l を tmzLimit=ℤ₃(1)（A7）と接続し π₁^ét 全体 ẑ(1)×ẑ へ | μ 方向との積 | A4/A7 跨り | 中 | **A7 再消費が主成分**になる（tmz は既算入）＝二重計上判定リスク大。後続へ |
| C5（却下） | profPi1_trivialTower を ctlProfinite で置換 | 無し（witness 差し替え） | — | 小 | **A3 二重計上**（A-next-leverage §2 で判定済み・据え置き） |

**選定: C1＋C2 の 2 ファイル対**（丸め保険・A5a/A5b・A7d/A7e 前例に従う）。いずれも
昇格(a)（Tate surrogate・裸 ℤ_l の主語替え）＋本物建設(b)（逆極限作用・忠実性・Galois 性は
ゼロから）で、A5 既算入対象は「作用される曲線・有限デッキ」としての正当な再利用に限る。
**ヘッドライン定理は全て π₁ 対象（極限群とその普遍的・忠実な作用）が主語**——A5 の主語
（tempered 拡大 1→ℤ₃(1)→π₁^{(3)}→ℤ→1）とは別対象であり、A5c 監査が「後続」と明示した
枠を埋める正順。

---

## §3 選定ステップ — A4a `Q3TatePi1Etale.lean`（q3pe）＋ A4b `Q3TatePi1Comparison.lean`（q3pc）

### 3.1 ファイル 1（A4a・必須）: `IUT/Q3TatePi1Etale.lean`（prefix `q3pe`・grep で未使用確認済み）

依存: `Q3TateCoverTower`（q3tc）・`Q3TateCurve`（q3t）・`TemperedTower`（ttw・経由で
LocalCFT の padicSystem/Zp）・`GaloisCategory`（GAction）・`Profinite`（quot_exact）。
~420 行・tier **M（opus）**・fable 不要（新イディオム無し・全て写経元あり）。

```lean
/- q3pe-1: 塔の隣接段の実被覆（N1）— q3tcHom と同じ Quot.lift 降下だが
   添字を m·l^{k+1} → m·l^k に直接取り、Nat 添字キャストを完全回避する。
   well-def は q3tc_tower_nested（既にこの添字で証明済み・:262-267）そのもの -/
def q3peStep (m l k : Nat) : Hom (q3tCurve (m * l ^ (k + 1))) (q3tCurve (m * l ^ k)) where
  map := Quot.lift (fun a => (q3tProj (m * l ^ k)).map a)
    (fun a b hab => Quot.sound (q3tc_tower_nested m l k _ hab))
  map_mul := …            -- q3tcHom (:117-123) の写経
theorem q3pe_step_surjective (m l k) : ∀ y, ∃ x, (q3peStep m l k).map x = y
theorem q3pe_step_ker (m l k) (a) :
    (q3peStep m l k).map ((q3tProj (m * l ^ (k+1))).map a) = (q3tCurve (m * l ^ k)).one
      ↔ (q3tSubgroup (m * l ^ k)).mem a      -- quotientProjN_ker 帰着（q3tc_ker 写経）

/- q3pe-2: デッキ遷移の幾何的実現（N2・★）— 段間実被覆はデッキ作用を運ぶ。
   ttwTransition（zmodTrans: mk j ↦ mk j・ttw_transition_reduce=rfl）の実曲線上実現＝
   M14-6 level_transition_equivariant の実被覆初実例。代表元では両辺
   [q^j·a]（q = q3tQ m は両レベル共通）で rfl 級 -/
theorem q3pe_step_deck (m l k : Nat) (j : Int) (x : (q3tCurve (m * l ^ (k+1))).carrier) :
    (q3peStep m l k).map ((q3tcDeckFin m (l ^ (k+1))).act (Quot.mk (modCong (l^(k+1))).rel j) x)
      = (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l^k)).rel j) ((q3peStep m l k).map x)
  -- Quot.ind で x=[a]。両辺 = (q3tProj (m*l^k)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) a)
  -- ※ mk j の遷移: (ttwTransition l k).map (mk j) = mk j は rfl（ttw_transition_reduce）
  --   ゆえこの一本で「zmodTrans が実被覆で実現される」を主張できる

/- q3pe-3: π₁ 対象＝逆極限 ℤ_l の実塔への作用（N3・★★ ヘッドライン）-/
def q3pePi1 (l : Nat) : Grp := ttwInverseLimit l          -- = Zp l = limitGrp (padicSystem l)
def q3peLimitAct (m l k : Nat) : GAction (q3pePi1 l) where
  carrier := (q3tCurve (m * l ^ k)).carrier               -- 実曲線 E_{q^{l^k}}(ℚ₃)
  act := fun γ x => (q3tcDeckFin m (l ^ k)).act (γ.val k) x
  act_one := …    -- (limitGrp …).one.val k = mk 0・(q3tcDeckFin …).act_one
  act_mul := …    -- limitGrp の mul は成分ごと（Profinite.lean:169）・(q3tcDeckFin …).act_mul
theorem q3pe_limit_act_natural (m l k : Nat) (γ) (x) :
    (q3peStep m l k).map ((q3peLimitAct m l (k+1)).act γ x)
      = (q3peLimitAct m l k).act γ ((q3peStep m l k).map x)
  -- γ.val k = (zmodTrans …).map (γ.val (k+1))（γ.property (Nat.le_succ k)）＋
  --   Quot.ind (γ.val (k+1)) で代表 j に落として q3pe_step_deck。
  --   ＝「π₁ の作用は実被覆塔のファイバー関手の自然変換」（M14-6 の実主語版）
theorem q3pe_deck_over (m l k) (γ) (z) :   -- 極限作用も被覆変換（E_q 上に恒等を覆う）
    (q3tcHom m (l ^ k)).map ((q3peLimitAct m l k).act γ z) = (q3tcHom m (l ^ k)).map z
  -- Quot.ind (γ.val k) → q3tc_deck_over

/- q3pe-4: 忠実性（N4・★ A5c 監査ディスカウント(1) の正面 discharge）-/
theorem q3pe_fin_faithful (m n : Nat) (hm : 1 ≤ m) (j : Int)
    (h : (q3tcDeckFin m n).act (Quot.mk (modCong n).rel j) ((q3tCurve (m*n)).one)
           = (q3tCurve (m*n)).one) :
    ((n : Nat) : Int) ∣ j
  -- act(mk j)[1]=[qʲ]。quotientProjN_ker（添字 m·n）で qʲ ∈ ⟨q3tQ(m·n)⟩＝∃t,(q^{mn})ᵗ=qʲ。
  -- 第1成分: q3td_zpow_fst (m*n) t と q3td_zpow_fst m j で (m·n)·t = m·j
  --  （Int.natCast_mul）。m≥1 の左簡約（Int.eq_of_mul_eq_mul_left）で n·t = j ⟹ n ∣ j。
  --  写経元: q3td_infinite_order（:117-125）＋ q3tcShift_wd（逆向きの新規半分）
theorem q3pe_fin_act_inj (m n) (hm) (j j' : Int)      -- 作用の単射版（mk j = mk j' へ）
theorem q3pe_limit_faithful (m l : Nat) (hm : 1 ≤ m) (γ : (q3pePi1 l).carrier)
    (h : ∀ k, (q3peLimitAct m l k).act γ ((q3tCurve (m * l ^ k)).one)
           = (q3tCurve (m * l ^ k)).one) :
    γ = (q3pePi1 l).one
  -- Subtype.ext＋funext k。γ.val k を Quot.ind で mk j に、q3pe_fin_faithful で l^k ∣ j、
  -- Quot.sound（j−0 の整除）で mk j = mk 0。choice-free（witness 不要・全て閉形式）
  -- ＝ RUBRIC「身代わりでない」: ℤ_l は実作用の群として非退化＝実塔の対称性を実際に区別する

/- q3pe-5: ファイバー＝軌道（N5・★ 中間被覆の Galois 性の完成）-/
theorem q3pe_fiber_orbit (m n : Nat) (x y : (q3tCurve (m*n)).carrier) :
    (q3tcHom m n).map x = (q3tcHom m n).map y
      ↔ ∃ j : Int, (q3tcDeckFin m n).act (Quot.mk (modCong n).rel j) x = y
  -- →: Quot.ind ×2・quot_exact（normalCong）で a⁻¹b ∈ q3tSubgroup m＝∃t,qᵗ=a⁻¹b、
  --    act(mk t)[a]=[qᵗa]=[b]（可換整理・q3td_deck_transitive :171-179 の写経）。
  -- ←: q3tc_deck_over（既存）。A5c は ← のみだった——iff で Galois 被覆が閉じる

/- q3pe-6: capstone -/
structure Q3TatePi1EtaleData where
  m : Nat ;  l : Nat ;  hm : 1 ≤ m ;  hl : 2 ≤ l
  pi1 : Grp                                    -- π₁ 断片
  pi1_eq : pi1 = q3pePi1 l                     -- ＝実被覆塔のデッキ逆極限 lim ℤ/l^k
  step_surj : ∀ k y, ∃ x, (q3peStep m l k).map x = y            -- 実余過滤塔
  step_deck : ∀ k j x, …                        -- q3pe_step_deck（遷移の幾何実現）
  act_natural : ∀ k γ x, …                      -- q3pe_limit_act_natural
  faithful : ∀ γ, (∀ k, …) → γ = pi1.one 相当   -- q3pe_limit_faithful
  fiber_orbit : ∀ k x y, …                      -- q3pe_fiber_orbit（n := l^k）
def q3peData : Q3TatePi1EtaleData      -- m=1, l=2（q=3・q3tcData と整合する見出し実例）
theorem q3pePi1_exists : Nonempty Q3TatePi1EtaleData := ⟨q3peData⟩
```

### 3.2 ファイル 2（A4b・保険/普遍性）: `IUT/Q3TatePi1Comparison.lean`（prefix `q3pc`・未使用確認済み）

依存: `Q3TatePi1Etale`・`Q3TateDeck`（q3td）・`TemperedTower`（ttwDiscreteComplete/
ttwProfiniteToLadic）・`TateCoverGroup`（tateProfinite）・`Profinite`（limit_universal）。
~300 行・tier **M（opus）**。

```lean
/- q3pc-1: 普遍被覆との比較（N6 前半・★）— 普遍デッキ ℤ（A5a）は各有限段の
   実デッキ ℤ/l^k と実被覆 q3tProj を通じて等変（代表計算で rfl 級）-/
theorem q3pc_universal_cover_equivariant (m l k : Nat) (t : Int) (x : q3tGrp.carrier) :
    (q3tProj (m * l ^ k)).map ((q3tdDeck m).act t x)
      = (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l^k)).rel t)
          ((q3tProj (m * l ^ k)).map x)
  -- 両辺 = [qᵗ·x]（q3tdDeck の act と q3tcShift は同じ tateZpow q3tGrp (q3tQ m)）
/- q3pc-2: 完備化 ℤ→ℤ_l の作用両立（N6 後半・★）— π₁^top 断片 ℤ の像は
   π₁^ét 断片 ℤ_l の中で同じ幾何作用を与える（比較定理の実現）-/
theorem q3pc_completion_act (m l k : Nat) (t : Int) (x) :
    (q3peLimitAct m l k).act ((ttwDiscreteComplete l).map t) x
      = (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l^k)).rel t) x
  -- (toZp l t).val k = mk t は定義計算（LocalCFT :109-110）
  -- ＋ ttw_discrete_complete_injective（既存・再消費）で ℤ ↪ ℤ_l が忠実に載る旨を capstone に併記
/- q3pc-3: π₁ 対象の普遍性（limit_universal の π₁ 実装・witness は閉形式）-/
theorem q3pc_pi1_universal (l : Nat) (H : Grp) (c : ∀ k, Hom H (zmod (l ^ k)))
    (hc : ∀ {i j} (h : i ≤ j) (x),
      (zmodTrans (pow_dvd_mono l h)).map ((c j).map x) = (c i).map x) :
    ∃ u : Hom H (q3pePi1 l),
      (∀ k x, (ttwLimitProj l k).map (u.map x) = (c k).map x) ∧ （一意性）
  := limit_universal (padicSystem l) H c hc   -- 特化＝既存機構の π₁ 主語への発火
theorem q3pc_pi1_act_via_cone (…) :           -- 分解 u の実塔作用 = 錐成分の作用（新規・数行）
    (q3peLimitAct m l k).act (u.map h) x = (q3tcDeckFin m (l^k)).act ((c k).map h) x
/- q3pc-4: Tate surrogate の主語替え（N7・★ 昇格(a) の名指し例）— 裸の ẑ=tateProfinite が
   Ẑ↠ℤ_l（ttwProfiniteToLadic・M374F 既存）経由で実曲線 E_{q^{l^k}}(ℚ₃) に作用する -/
def q3pcSurrogateAct (m l k : Nat) : GAction tateProfinite where
  carrier := (q3tCurve (m * l ^ k)).carrier
  act := fun σ x => (q3peLimitAct m l k).act ((ttwProfiniteToLadic l).map σ) x
  act_one/act_mul := …    -- ttwProfiniteToLadic は Hom（map_one/map_mul 既存）
theorem q3pc_surrogate_natural (…)  -- 段間自然性（q3pe_limit_act_natural に帰着）
theorem q3pc_surrogate_nontrivial (m l k hm hk) : ∃ σ x,
    (q3pcSurrogateAct m l k).act σ x ≠ x     -- σ = toZhat 1 の像・x=[1]・q3pe_fin_faithful で分離
/- q3pc-5: capstone Q3Pi1ComparisonData / q3pcData / q3pcComparison_exists -/
```

### 3.3 choice-free 戦略（両ファイル共通）

- 新規 `Classical.choice` ゼロ。逆極限機構（`limitGrp`/`limitProj`/`limit_universal`）は
  Profinite.lean で choice-free 済み——witness は全て閉形式（整合族は `fun k => …` の
  直接構成・分解 u は `limit_universal` の構成的 witness）。
- ∃ 形は Prop ゴール内のみ（q3pe_fiber_orbit の t は quot_exact から obtain・
  q3pc_surrogate_nontrivial の witness は明示元 toZhat 1・[1]）。
- 忠実性の核は第1成分の Int 算術（Int.eq_of_mul_eq_mul_left・omega は線形式のみ）。
  3^ℓ/l^k 冪算術は既存 pow_dvd_mono 経由（omega に冪を渡さない）。
- 禁止タクティク（simp/decide/by_cases/rcases/ring 等）不使用。目標
  `#print axioms` = [propext, Quot.sound]。

### 3.4 詰まりどころと予防線（tier M で閉じる根拠）

1. **Nat 添字キャスト**: q3peStep を q3tcHom の合成でなく **m·l^{k+1} 添字で直接
   Quot.lift** することで、m·l^{k+1} = (m·l^k)·l の型レベル書換を完全回避
   （q3tc_tower_nested が既にこの添字対で証明済みなのが決め手）。
2. q3pe_step_deck / q3pc-1/2 は代表元計算で両辺が同一項に畳まれる rfl 級
   （show で正規形を明示する q3tc の流儀を写経）。
3. q3pe_fin_faithful の第1成分算術: `q3td_zpow_fst` は q3tQ の任意添字で使える
   （q3tQ (m*n) の第1成分 = ((m*n : Nat) : Int)・Int.natCast_mul で m·n へ）。
   写経元 q3td_infinite_order・q3tcShift_wd。
4. 失敗時の縮退順序: q3pc（ファイル 2）が詰まれば q3pc-3/4 を落として q3pc-1/2 のみで
   提出（A4a 単独でも §5 の 0.55 candidacy は主張可能・保険が薄くなるだけ）。
   q3pe_limit_faithful が詰まれば有限段 q3pe_fin_faithful までで提出し「極限忠実性は
   後続」と正直申告（この場合 0.53–0.54 級見込み＝柱A 49 据え置きを覚悟）。

---

## §4 正直な線引き（本ステップが実にしないもの・過大主張禁止・消さない/弱めない）

1. **依然 p=3・q=3^m 固定・単一 l の pro-l 切片のみ**。ẑ 全体（Π_l ℤ_l）の組み上げ・
   一般素数・一般 Tate パラメータ（単数部つき q）は未達。
2. **Tate 曲線のみ・しかも compact E_q**。A4 title の「双曲的曲線/Spec」には遠い——
   IUT 本丸の once-punctured 楕円曲線の非可換 tempered π₁（θ-Heisenberg）は範囲外。
   可換な格子方向の切片である。
3. **π₁^ét の格子方向スライスのみ**: μ 方向 ℤ₃(1)（=tmzLimit・A7 計上済み）との積
   ẑ(1)×ẑ・Weil ペアリング・G_{ℚ₃} の外作用（arithmetic π₁ 拡大
   1→π₁^geo→π₁^arith→G_{ℚ₃}→1）は本ステップで一切構成しない（意図的・二重計上回避）。
4. **位相・スキーム・エタールサイト皆無**: 「被覆」は K-点群の全射準同型であり、
   スキームの有限エタール射・Berkovich/rigid 被覆理論そのものではない（A5a/A5c の
   恒久限定(3)(4) を継承）。担体は群提示 3^ℤ×ℤ₃^×（A2/A8 恒久限定の継承）。
5. **Aut(F) 復元・遠アーベルは未接続**: GrothendieckGalois の π₁=Aut(F)・M286F の
   モノドロミー同型を本実例に適用すること、および TateCoverCat/GaloisCatData への
   実対象登録（A5c 正直な限定(1) の A5d 後続）は行わない。π₁ からの逆再構成
   （anabelian 方向）はゼロのまま。
6. **既存の正直申告は全て残す**: M374F の外部仮説（ttw_full_tower_hypothesis・
   Slim）・A5c ヘッダ限定 5 項・tateProfinite 系 surrogate 本体・profPi1_trivialTower は
   消さず併設（§2(a) 昇格の規約）。q3pc-4 は surrogate を**主語替えの供給**で昇格するの
   であって、M188F/M195F の自己申告を書き換えない。
7. **A4 は 0.55 でもなお 0.5 帯**: 上記 1–5 が残る限り「忠実な部分ケース(0.5) を
   質的に一歩超える最初の非自明実インスタンス」以上を主張しない。監査が「これは A5 の
   深化であり A4 の主語に達しない」と判定する可能性は §5 に織り込む。

---

## §5 status 見込み・柱A% 算術（丸め境界の厳密計算）

`target_ledger.json` 本日実測: A1=0.85(w8)・A2=0.65(w8)・A3=0.75(w12)・**A4=0.5(w14)**・
A5=0.15(w10)・A6=0.55(w14)・A7=0.40(w12)・A8=0.57(w12)・A9=0(w10)。Σw=100。

**A4 以外の定数項**（自ら加算検算）:
6.8 + 5.2 + 9.0 + 1.5 + 7.7 + 4.8 + 6.84 + 0 = **41.84**。
∴ **Σ_A = 41.84 + 14·s_A4**。現状 s=0.5 → Σ_A = 48.84 → round(48.84) = **49**（現表示と一致・検算済み）。

`tools/compute_complete_pct.py` は Python `round()`（**banker's rounding**: x.5 は偶数へ。
round(49.5)=50——50 は偶数なので **49.5 ちょうどでも 50 に丸まる**。対して round(48.5)=48）。
∴ 表示 50 の条件は **Σ_A ≥ 49.5 ⟺ 14·s_A4 ≥ 7.66 ⟺ s_A4 ≥ 7.66/14 = 0.547142857…**。

| 監査結果 s_A4 | Σ_A = 41.84+14s | round | 柱A 表示 |
|---|---|---|---|
| 0.50（据え置き） | 48.84 | 49 | 49（横這い） |
| 0.52 | 49.12 | 49 | 49 |
| 0.53 | 49.26 | 49 | 49 |
| 0.54 | 49.40 | 49 | 49 |
| **0.55（設計見込み）** | **49.54** | **50** | **50（+1）** |
| 0.57 | 49.82 | 50 | 50 |

**正直な見込み**: A4a+A4b 完了時に **0.55 を独立監査に諮る**（丸め境界 0.5471… を
0.0029 上回るだけの際どい位置）。監査が「逆極限作用は実装されたが K-点群論の影・
格子スライスのみ」を重く見て 0.52–0.54 に据えれば**柱A 49 据え置き**であり、その場合は
§5 規則に従い「complete_pct 前進・柱% 横這い」と正直に報告する。0.55 の根拠は
(i) A4 初の非自明実インスタンス（自明塔・抽象 ẑ・2 根被覆を質的に超える）、
(ii) A5c 監査の名指しディスカウント（忠実性未証明・逆極限未実現）の正面 discharge、
(iii) CLAUDE.md §2(a) 名指し昇格例「Tate surrogate→実 π₁^ét」の第一歩、の 3 点。
過大側（0.6 級）は §4 の 1–5 により主張しない。

---

## §6 実装計画（親向け）

| 枠 | ファイル | prefix | tier/model | 行数 | 依存 | 直列/並列 |
|---|---|---|---|---|---|---|
| 1 | `IUT/Q3TatePi1Etale.lean`（A4a） | q3pe | **M / opus** | ~420 | q3tc・q3t・ttw・GaloisCategory・Profinite（全既存） | 先行 |
| 2 | `IUT/Q3TatePi1Comparison.lean`（A4b） | q3pc | **M / opus** | ~300 | **A4a**・q3td・ttw・TateCoverGroup・Profinite | A4a 完了後に直列 |

- **fable 不要**（新イディオム無し・全定理に写経元を §3 で名指し済み）。詰まった場合のみ
  HELP スポットとして fable を q3pe_limit_faithful（Subtype/funext/Quot.ind の三段）1 点に限定。
- 残り並列枠は他柱の complete_pct 案件で埋める（本設計のスコープ外・水増し capstone で
  埋めない——CLAUDE.md §2 遵守）。
- サブエージェントは新規 2 ファイルのみ作成。**共有ファイル更新は親が統合時に一括**:
  1. `IUT.lean` に import 2 行（Q3TateCoverTower の後ろ）。
  2. `build.sh`（登録方式に従い追記）。
  3. `tools/gen_graph.py` の PILLAR 辞書に `"Q3TatePi1Etale": "A", "Q3TatePi1Comparison": "A"` を追記 → `python3 tools/gen_graph.py` 再生成。
  4. `target_ledger.json` A4 status・`graph-meta.json` pillars.A（complete_pct/complete_note）・
     `dashboard.md` 二軸表は**独立監査確定後に**更新（自己申告禁止・AUDIT_RUBRIC 準拠。
     `.complete_pct_baseline.json` 相当の確定はユーザー人手署名）。
- 検証手順（実装枠に指示）: `bash build.sh` フル EXIT=0・no sorry・主要対象
  （q3peStep/q3pe_step_deck/q3peLimitAct/q3pe_limit_act_natural/q3pe_fin_faithful/
  q3pe_limit_faithful/q3pe_fiber_orbit/q3peData/q3pc_universal_cover_equivariant/
  q3pc_completion_act/q3pc_pi1_universal/q3pcSurrogateAct/q3pc_surrogate_nontrivial）の
  `#print axioms` = [propext, Quot.sound] を列挙確認。
- 完了後に**独立 A4 再監査**を起票（入力は AUDIT_RUBRIC＋対象 .lean のみ・本設計書と
  ヘッダ主張は監査に渡さない）。監査には「A5 二重計上でないこと」（§2.2 の新規表 N1–N7 と
  A5c 監査注記の defer 文言の突合）を敵対的に検証させる。
- ラウンド報告: 柱別二軸表＋「A4 0.5→(監査値)・Σ_A=41.84+14s・表示 49 or 50」を主指標で。

---

## 付録: 本設計自身の正直な限定

- 本ドキュメントは設計であり complete_pct を動かさない（動かすのは実装＋独立監査）。
- §3 の Lean スケッチは本日精読した実在シグネチャ（q3tc_tower_nested の添字形・
  limitGrp の成分 mul・toZp の val 定義・ttw_transition_reduce=rfl 等）に基づくが、
  defeq の細部（特に (limitGrp …).one.val k の畳み込み）は実装時に show で固定すること。
- 最大の非技術リスクは**監査帰属**（A4 でなく A5 深化と判定される可能性）。§2.3・§5 に
  織り込み済み——その場合も A5 側の正当な前進（忠実性 discharge）として無駄にはならないが、
  柱A 表示は動かない。
