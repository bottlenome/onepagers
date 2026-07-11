# A8 cuspidalization 詳細化ラウンド設計 — 実 [2]-同種と E₉(ℚ₃)∖E₉[2] → E₉(ℚ₃)∖{O}（2026-07-11）

**種別**: 詳細化ラウンド（設計ドキュメントのみ・Lean 実装なし）
**対象**: 柱A A8「楕円曲線/Tate 曲線の実被覆・cuspidalization」（w12・status 0.57）
**契機**: A8 再監査（`reaudit-A8-real-tate-curve-2026-07-10.md`）が 0.6 未達の**筆頭理由**に
「**cuspidalization = 0**（A8 title の半分・モジュール皆無）」を名指し。本設計はその半分に
**現行インフラで到達可能な本物の第一歩があるか**を敵対的に判定する。

---

## 0. 結論サマリ

| 項目 | 内容 |
|---|---|
| 判定 | **tractable な実第一歩あり**（ただし「cuspidal 惰性群」そのものは**ブロック**——§2(a) で precisely 線引き） |
| 選定ステップ | **A8c: 楕円 cuspidalization（[AbsTopII] §3）の幾何的基体** — 実 [2]-同種 sq: E₉(ℚ₃)→E₉(ℚ₃)（x↦x²）・**核＝ちょうど Klein 4 群**（μ₂ 完全性 u²=1⟹u=±1 を新規実証明・q3tt 正直限定 3 の discharge）・実開曲線 E₉∖E₉[2] → E₉∖{O}（楕円 cuspidalization の 2 本の射の実現）・ファイバー＝捻れ平行移動軌道・**[2] の ℚ₃ 点非全射性の実 witness**（E(ℚ₃)/2E(ℚ₃)≠0 の影） |
| 新規ファイル | `IUT/Q3TateCuspidalization.lean`（prefix `q3cu`・1 ファイルのみ・想定 550–650 行） |
| tier | **M（opus）**。μ₂ 完全性（q3cu-3・約 200 行）が詰まった場合のみ fable HELP スポット |
| A8 status 見込み | 0.57 → **0.62**（独立監査確定が条件・§5） |
| 柱A% | Σ_A 50.96 → **51.56** ⇒ 表示 **51 → 52**（丸め境界 51.5 を検算済み・§5） |
| ブロックのまま残るもの | **cuspidal 惰性群そのもの（非自明惰性）＝0**。名指し前提条件: 実テータ被覆＝実直線束/テータ関数機構（柱E EtaleTheta の幾何的実現）または スキーム水準の分岐被覆・π₁^ét（§2(a)） |

---

## 1. A8 cuspidalization の定義と現状

### 1.1 cuspidalization が実第一歩に要求するもの

Mochizuki [AbsTopII] §3 の cuspidalization は「**コンパクト曲線の π₁ ＋ cusp データから、
開曲線（punctured 曲線）の π₁ を群論的に再構成する**」技法。Tate 曲線 E_q では主語は
once-punctured E_q∖{O}。要求される構造は 3 層:

1. **幾何的基体**: 開曲線 E∖{O}（と E∖E[N]）そのもの・その間の被覆
   — 楕円 cuspidalization は具体的に **2 本の射** {E∖E[N] ⊆ E∖{O}（開埋め込み）,
   [N]: E∖E[N] → E∖{O}（N 倍同種の制限・有限エタール）} を使う（[AbsTopII] §3 の
   楕円 cuspidalization 図式）。cusp 集合は下流 {O}・上流 E[N]。
2. **cuspidal 惰性**: π₁(E∖{O}) ↠ π₁(E) の核＝cusp まわりの惰性 ẑ(1) の正規閉包。
   種数 1・1 点抜きでは惰性生成元 c は基本関係 [a,b]·c = 1 により**交換子 [a,b]⁻¹**。
3. **群論的再構成アルゴリズム**: 1–2 を使い π₁(E∖{O}) を復元する函手的手続き。

### 1.2 現状実測（grep・本体精読）

`grep -rniE "cusp|puncture|inertia|tripod|…" IUT/*.lean` の全ヒットを精読した結果:

| 資産 | 実体 | cuspidalization との関係 |
|---|---|---|
| cuspidalization を主語にしたモジュール | **皆無**（q3t/q3tt/blc の「皆無」正直限定行のみ） | A8 再監査の「cuspidalization=0」を再確認 |
| `Q3TateCurve.lean`(q3t)/`Q3TateTorsion.lean`(q3tt) | 実 E_q(ℚ₃)=（3^ℤ×ℤ₃^×)/q^ℤ・実 2-捻れ **Klein 4 群 ⊆ E₉[2]**（包含のみ・μ₂ 完全性は正直限定 3 で未達） | **cusp 候補（捻れ点）は既に実在**。だが開曲線・同種・核の等号は皆無 |
| `Q3TateDeck.lean`(q3td)/`Q3TateCoverTower.lean`(q3tc)/`Q3TatePi1Etale.lean`(q3pe) | 実デッキ ℤ（自由性 q3td_deck_free 済）・実中間被覆 E_{qⁿ}→E_q（**コンパクト曲線間**・レベル替え商写像・デッキ＝q 平行移動）・逆極限 ℤ_l 作用 | **すべてコンパクト E_q の被覆**。開曲線は一切登場しない（q3pe 正直限定 (2) が明記: once-punctured の非可換 tempered π₁ は範囲外） |
| `TemperedThetaCommutator.lean`(M384F)/`TemperedPi1Etale`(M424F)/`ArithTemperedPi1.lean`(M429F) | 離散 Heisenberg 群 thetaGrp = H(ℤ)・tpeGroup = thetaGrp⋊ℤ・atpGroup（**実群として**交換子＝シンプレクティック形式・中心＝シクロトーム着地を完全証明） | **punctured π₁ の抽象群提示**。ただし全ヘッダが「幾何的実現＝外部/後続」と正直申告——thetaGrp が**実 E_q(ℚ₃)∖{O} の実被覆のデッキ群として**実現された事実はゼロ。すなわち現状の「punctured π₁」は本物の群だが主語接続なしの**模型的立ち位置** |
| `BelyiCubicReal.lean`(blc・A9) | 実 Belyi 多項式 f=3X²−2X³ の分岐軌跡＝{0,1,∞}（下流）完全証明 | tripod の cusp 3 点は実在。ただし blc §4.2 限定 3 が「Belyi cuspidalization ではない・tripod π₁ ゼロ」と明記・§4.3 が A8 と主語素 disjoint を宣言 |

**0.57 に据え置いている理由**（再監査の残欠 5 項）: (1) cuspidalization=0、(2) cover 系の
圏側は代理のまま、(3) Galois 作用皆無、(4) **μ₂ 完全性未証明（Klein は ⊆ のみ）**、(5) 単一切片。
本設計の A8c は **(1) の幾何的基体half と (4) を同時に正面 discharge** する（(1) の惰性 half は
ブロックと正直申告・§2(a)）。

---

## 2. 候補評価（敵対的・本体判定）

### (a) puncture の惰性群を実群として — **ブロック（原理的・precisely）**

**判定: BLOCKED。これは実装力の問題ではなく現行インフラの構造的不可能。**

- 種数 1・1 点抜きの cuspidal 惰性生成元 c は基本関係により**交換子 [a,b]⁻¹**（§1.1）。
  よって c は**あらゆるアーベル商で死ぬ**: π₁^ab(E∖{O}) ≅ π₁^ab(E)（H₁ は点抜きで不変）。
  帰結: **E∖{O} のすべてのアーベル被覆は cusp で不分岐＝E の被覆に延長する**。
- 現行インフラの実被覆は**すべて可換群 ℚ₃^×（3^ℤ×ℤ₃^×）の商写像・その制限**であり、
  デッキ群は例外なくアーベル（q3td の ℤ・q3tc の ℤ/n・q3pe の ℤ_l・本設計 q3cu の Klein 4 も）。
  ⇒ **現行インフラで構成可能ないかなる実被覆上でも惰性は自明にしか作用できない**。
  非自明惰性を担う最小の実対象は非可換（テータ/Heisenberg）被覆だが、点レベルでは
  Tate 型被覆のデッキはすべて「定数倍」で可換——EtTh の非可換性は**直線束の全空間／
  テータ関数への作用**（コサイクル）に宿り、K 点集合には決して現れない。
- **名指し前提条件**: (i) 実直線束＋Mumford テータ群 1→μ₂→G(L)→E[2]→1（柱E の
  EtaleTheta 幾何的実現・M384F/M429F ヘッダが「外部/後続」と自認するギャップそのもの）、
  または (ii) スキーム水準のエタールサイト・分岐被覆理論。どちらも大物・未建設。
- 抽象拡大 1→I→G→ℤ/n→1 を裸で建てて「punctured π₁」と呼ぶのは §3 toy 主語禁止の
  典型違反（惰性が実被覆の何も区別しない）。**却下＝ブロック明記**。

### (b) tripod P¹∖{0,1,∞} の実 cusp（A9 blc 経由） — 実・tractable だが **A8 の主語でない**

blc の因子分解（f=X²(3−2X)・f−1=(X−1)²(−(2X+1))・f(1/u)u³=3u−2）から、上流 cusp 集合
f⁻¹({0,1,∞}) = {0, 3/2, 1, −1/2, ∞}（5 実 cusp・e = 2,1,2,1,3・**各ファイバーで Σe=3=deg**）と
開制限「x が上流 cusp 外 ⟹ f(x) が下流 cusp 外」は零因子なし環の積零分解で完全証明可能
（新イディオム不要・tier M）。これは Belyi cuspidalization の幾何入力として本物。
**しかし**: (i) 主語は Belyi 写像＝**A9 のコース**（blc §4.3 が A8 と disjoint を宣言済み・
A8 に付け替えると帰属の水増し）、(ii) ℚ 点レベルでは一般ファイバーの非分岐性（3 点相異）が
体の非閉性で言えず「cusp 簿記のみ」に留まる。**A9 の次ラウンド本命として温存・A8 では不採用**。

### (c) punctured 曲線のデッキ群を実自由拡大として — 抽象形は却下・実形は薄すぎ

- 抽象形（A5c の ℤ/n × 惰性因子の拡大を建てて punctured π₁ と呼ぶ）: (a) と同罪の
  toy 主語（惰性が何にも作用しない）。**却下**。
- 実形（tempered 被覆 ℚ₃^×∖q^ℤ → E_q∖{O} への制限）: 実だが、自由性は q3td_deck_free で
  既出・新内容は「q^ℤ 軌道が補集合を保つ」制限簿記のみ・**惰性ゼロ**（コンパクト被覆の
  制限ゆえ cusp で何も起きない）。単独モジュールでは §2 骨格水増しの敵対的判定を免れない。
  **単独では不採用**（(e) 内の任意小節 q3cu-8 として吸収可・落として良い）。

### (d) 幾何的 Tate 加群 T_2(E_q)（q^{1/2^n} 方向） — **ブロック（既判定の再確認)**

各段で q^{1/2^n} が要る: q=9 で q^{1/2}=3∈ℚ₃ は実在（q3tt_w_sq）だが **q^{1/4}=√3∉ℚ₃**
（v(√3)=1/2 が ℤ 値付値と矛盾）。以降の塔は q3Ring 上の体拡大機構（未建設の大物）が前提。
さらに θ-拡大類（非可換）は柱E。`A8-real-tate-curve-detail-2026-07-10.md` §5 の判定を維持。
**ブロック明記・不採用**。

### (e) ★採用: 楕円 cuspidalization の幾何的基体 — 実 [2]-同種と E₉∖E₉[2] → E₉∖{O}

[AbsTopII] §3 の**楕円 cuspidalization**は N 捻れ被覆 [N]: E∖E[N] → E∖{O} を入力にする
（§1.1-1）。その幾何的基体を N=2・E₉(ℚ₃) 上で**丸ごと実構成**できる:

1. **実 [2]-同種 sq: E₉ → E₉**（[x]↦[x²]）。well-def は「部分群は平方で閉じる」
   （x=q^t ⟹ x²=q^{2t}）・hom は可換性。**リポジトリ初の実同種**（A5c/A4 の被覆は
   レベル替え商写像＝別物・§4.2）。sq x = x·x（proj が hom）なので **ker(sq) = E₉[2]
   （2-捻れ全体）が on the nose** で成立。
2. **核の成分特徴付け**: sq[k,u]=O ⟺ u²=1（q3t_mem_pair_iff m=2: 2∣2k は常に真）。
3. **μ₂ 完全性（新規実補題・本設計の要）**: u∈ℤ₃^×・u²=1 ⟹ u=1 ∨ u=−1。
   IsZpUnit のレベル 1 witness a（∃形で既に手元・choice 不要）の 3 分律で分岐し、
   各レベル n で 3ⁿ∣(j−1)(j+1)・3 は j∓1 の片方しか割らない（j≡a mod 3 の整合）
   ⟹ 素冪 Euclid 反復（euclid_int の帰納・新小補題 q3cu_ppow_dvd）で 3ⁿ∣j∓1。
   ⟹ **ker(sq) = Klein 4 群 ちょうど**（q3tt 正直限定 3「⊆ のみ」の discharge）。
   さらに q=9 では q^{1/2}=3∈ℚ₃・μ₂⊂ℚ₃ ゆえ **幾何的 E[2]≅(ℤ/2)² が全部 ℚ₃ 有理**
   ——K 点の影が cusp レベルで忠実な、選び抜かれた本コース部分ケース。
4. **開曲線と 2 本の射**: E₉∖{O}・E₉∖E₉[2] を実 subtype で定義し、
   (i) 包含 E∖E[2] ⊆ E∖{O}（O∈ker）、(ii) sq の制限 E∖E[2] → E∖{O}
   （x∉ker ⟹ sq x ≠ O は定義そのもの）——**楕円 cuspidalization 図式の 2 本の射の実現**。
5. **被覆構造**: ファイバー＝核剰余類（sq x = sq y ⟺ ∃a∈Klein, a·x=y）・Klein 平行移動は
   開部分を保ち（a∈ker, x∉ker ⟹ a·x∉ker）自由に作用・上流 cusp 4 点は相異
   （q3tt_klein_distinct 消費）。
6. **[2] の ℚ₃ 点非全射性の実 witness**: ∀x, sq x ≠ q3ttW1（[1,1] のパリティ矛盾・omega）。
   E(ℚ₃)/2E(ℚ₃) ≠ 0（Kummer 降下の影）の**初の実定理**——「K 点の影では [N] は
   全射でない」を隠さず定理として顕示する正直装置を兼ねる。

**判定: 実・tractable・cuspidalization の主語**（開曲線・捻れ cusp・同種被覆が主語で、
コンパクト被覆塔の再ラベルでない）。**採用**。

---

## 3. 結論 — 選定ステップの実装粒度

### 3.1 ファイル・部品表

**`IUT/Q3TateCuspidalization.lean`**（prefix `q3cu`・tier **M=opus**・想定 550–650 行）
**分類ヘッダ**: [実／昇格(a)+本物建設(b)] — q3tt の「Klein ⊆ E₉[2] のみ・μ₂ 完全性未達」を
等号へ昇格(a)し、楕円 cuspidalization（[AbsTopII] §3）の幾何的基体（実 [2]-同種・実開曲線・
2 本の射・核剰余類被覆・非全射 witness）をゼロから建設(b)。complete_pct 影響: A8 0.57→0.62
見込み（独立監査確定が条件）。
**依存**: `import IUT.Q3TateTorsion`（→ Q3TateCurve→Q3UnitsGroup）・`IUT.RootsOfUnity`
（euclid_int）。共有ファイル不変更・新規 1 ファイルのみ。

```lean
-- q3cu-0: ★ 実 [2]-同種 sq: E₉(ℚ₃) → E₉(ℚ₃)（リポジトリ初の実同種）
def q3cuSq : Hom (q3tCurve 2) (q3tCurve 2)
  -- map := Quot.lift (fun a => (q3tProj 2).map (q3tGrp.mul a a)) …
  -- well-def: a⁻¹b ∈ q^ℤ ⟹ (a²)⁻¹b² = (a⁻¹b)² ∈ q^ℤ（可換性＋tateZpow_add）
theorem q3cu_sq_eq_square (x) : q3cuSq.map x = (q3tCurve 2).mul x x
  -- ⟹ ker(q3cuSq) = E₉[2]（2-捻れ全体）が on the nose

-- q3cu-1: 核の成分特徴付け
theorem q3cu_ker_iff (k : Int) (u) :
    q3cuSq.map ((q3tProj 2).map (k, u)) = (q3tCurve 2).one
      ↔ (zpUnits 3 isPrime_three).mul u u = (zpUnits 3 isPrime_three).one
  -- q3t_mem_pair_iff（m=2・2∣2k は omega）＋成分計算

-- q3cu-2: 素冪 Euclid 反復（新小補題・euclid_int の帰納）
theorem q3cu_ppow_dvd (n : Nat) {x y : Int}
    (h : ((3:Nat)^n : Int) ∣ x * y) (hy : ¬ ((3:Nat) : Int) ∣ y) :
    ((3:Nat)^n : Int) ∣ x

-- q3cu-3: ★★ μ₂ 完全性（q3tt 正直限定 3 の discharge・本設計の要・約 200 行）
theorem q3cu_mu2_complete (u : (zpUnits 3 isPrime_three).carrier)
    (hu : (zpUnits 3 isPrime_three).mul u u = (zpUnits 3 isPrime_three).one) :
    u = (zpUnits 3 isPrime_three).one ∨ u = q3tNegOne
  -- IsZpUnit のレベル1 witness a（∃形・obtain で choice 不要）→ a%3 の omega 3分律
  -- （3∣a は単数性と矛盾）→ 各分岐: funext n・Quot.ind で代表 j・整合 j≡a mod 3・
  -- 3ⁿ∣(j−1)(j+1)＋3∤(j±1) → q3cu_ppow_dvd → Quot.sound

-- q3cu-4: ★★ 核＝ちょうど Klein 4 群（上流 cusp 集合の完全決定）
theorem q3cu_ker_eq_klein (x : (q3tCurve 2).carrier) :
    q3cuSq.map x = (q3tCurve 2).one ↔ q3ttKleinMem x
  -- →: Quot.ind＋q3cu_ker_iff＋q3cu_mu2_complete。←: q3tt_klein_torsion＋q3cu_sq_eq_square

-- q3cu-5: ★ 実開曲線と楕円 cuspidalization 図式の 2 本の射
def q3cuPunct : Type := { x : (q3tCurve 2).carrier // x ≠ (q3tCurve 2).one }   -- E₉∖{O}
def q3cuOpen  : Type := { x : (q3tCurve 2).carrier // q3cuSq.map x ≠ (q3tCurve 2).one } -- E₉∖E₉[2]
theorem q3cu_open_sub (x : q3cuOpen) : x.val ≠ (q3tCurve 2).one         -- 包含 E∖E[2] ⊆ E∖{O}
def q3cuOpenMap : q3cuOpen → q3cuPunct := fun x => ⟨q3cuSq.map x.val, x.property⟩ -- [2] の制限

-- q3cu-6: ★ 被覆構造（ファイバー＝Klein 剰余類・開部分を保つ自由デッキ）
theorem q3cu_fiber_coset (x y) : q3cuSq.map x = q3cuSq.map y
      ↔ ∃ a, q3ttKleinMem a ∧ (q3tCurve 2).mul a x = y
theorem q3cu_deck_open (a x) (ha : q3ttKleinMem a)
    (hx : q3cuSq.map x ≠ (q3tCurve 2).one) : q3cuSq.map ((q3tCurve 2).mul a x) ≠ …
theorem q3cu_deck_free (a x) (h : (q3tCurve 2).mul a x = x) : a = (q3tCurve 2).one

-- q3cu-7: ★ [2] の ℚ₃ 点非全射性（E(ℚ₃)/2E(ℚ₃)≠0 の影・正直装置を兼ねる実定理）
theorem q3cu_not_surjective : ∀ x, q3cuSq.map x ≠ q3ttW1
  -- Quot.ind→[2k,u²]=[1,1] → q3tt_class_eq_iff → 2∣(1−2k) → omega

-- q3cu-8（任意・落として良い）: tempered 被覆の puncture 整合（候補(c)の実形の吸収）
theorem q3cu_temp_puncture (x) : (q3tSubgroup 2).mem x
      ↔ (q3tSubgroup 2).mem (q3tGrp.mul (q3tQ 2) x)   -- q^ℤ 軌道は puncture ファイバーを保つ

-- q3cu-9: capstone（新規証明なし・束ねのみ）
structure Q3CuspidalizationData where
  ker_eq_klein : … ; open_map : … ; fiber_coset : … ; deck_free : … ;
  cusps_distinct : …（q3tt_klein_distinct 消費）; not_surj : …
def q3cuData : Q3CuspidalizationData ; theorem q3cuCusp_exists : Nonempty _
```

**choice-free 戦略**: 全補題が成分算術＋quotientProjN_ker＋既存 q3tt 補題＋euclid_int 帰納。
∨ ゴール（q3cu-3）は Prop なので Quot.ind/obtain 可・witness は IsZpUnit の ∃ 形から取る。
新規 Classical.choice 皆無・#print axioms = [propext, Quot.sound] 目標・禁止タクティク不使用。

### 3.2 なぜ「再カウント」でなく「本物の建設」か

複数の**新しい実主語**が立つ: 実同種 sq（初）・実開曲線 E∖{O}, E∖E[2]（初）・
核＝Klein の**等号**（初・q3tt は ⊆ 止まり）・非全射 witness（初・降下理論の影）。
A8 の既存資産は消費（q3tt_klein_distinct/class_eq_iff・q3t_mem_pair_iff）するが、
これらを cusp 集合として読み直す新定理群であり値一致の再確認は置かない。

---

## 4. 正直な線引き（header 必載・消さない・弱めない）

1. **cuspidal 惰性群 = 0 のまま**。[2]-被覆は E∖{O} 上不分岐（エタール）であり、
   本モジュールのどの群も cusp 惰性を担わない。非自明惰性の最小担体は非可換テータ被覆で、
   **名指し前提条件 = 実直線束/Mumford テータ群（柱E EtaleTheta の幾何的実現）または
   スキーム水準の分岐被覆**（§2(a) の原理的ブロック。本モジュールは解消を主張しない）。
2. **π₁ 再構成アルゴリズム（cuspidalization 本体・§1.1-3）= 0**。建てるのは幾何的基体
   （§1.1-1）＋cusp 集合の完全決定のみ。「cuspidalization を実装した」とは主張しない。
3. **K 点の影**: スキーム・エタールサイト・位相なし。「開曲線」は subtype・「被覆」は
   核剰余類ファイバーの写像（恒久限定の継承）。[2] は ℚ₃ 点で**非全射**（q3cu-7 で
   定理として顕示・幾何的次数 4 との差は正直申告）。
4. **単一切片**: p=3・q=9（m=2）・N=2 のみ。奇 N・一般 q・一般 p は後続
   （N=2/q=9 は E[2] 全有理という本コースの忠実部分ケース・§3 規約）。
5. **二重計上の排除（監査向け・明示）**:
   - **vs A8a/A8b（q3t/q3tt）**: q3tt は Klein「⊆」まで。本モジュールの等号（q3cu-4）・
     同種・開曲線・非全射は全て新規。q3tt の正直限定 3 は**弱化でなく証明による置換**
     （既存ファイルは不変更・限定文はヘッダで「q3cu-3 で discharge 済み」と参照追記のみ親が判断）。
   - **vs A5a/A5c/A4（q3td/q3tc/q3pe）**: あちらはレベル替え商写像 E_{qⁿ}→E_q・デッキ＝
     q 冪平行移動・コンパクト曲線。こちらは**自己同種 x↦x²・デッキ＝捻れ平行移動・開曲線**。
     写像も群も主語も disjoint。A5/A4 の status には触れない。
   - **vs A9（blc）**: 多項式・P¹ は一切登場しない。
   - **vs A2/A6/A7**: q3cu-3 は ℤ₃^× の補題だが、輸出先は cusp 集合の決定（A8c 帰属）。
     ℤ₃(1) の End/Aut 剛性（A7）・復元（A6）とは主語素 disjoint。

---

## 5. status 見込み・柱A% 算術（検算済み）

`target_ledger.json` 実測（2026-07-11 時点）:
Σ_A = 8·0.85 + 8·0.65 + 12·0.75 + 14·0.55 + 10·0.15 + 14·0.58 + 12·0.4 + **12·0.57** + 10·0.1
= 6.8+5.2+9.0+7.7+1.5+8.12+4.8+**6.84**+1.0 = **50.96**（表示 51・graph-meta と整合）。
A8 以外 8 項の定数 = 50.96 − 6.84 = **44.12**。Σ_A = 44.12 + 12·s_A8。

表示 52 の条件: `compute_complete_pct.py` は Python `round()`（banker's）。
**Σ_A ≥ 51.5 で 52**（round(51.5)=52・52 は偶数ゆえ境界そのものでも 52 に上がる）。
s_A8 ≥ (51.5 − 44.12)/12 = 7.38/12 = **0.6150**。

| s_A8 | Σ_A | 表示 |
|---|---|---|
| 0.57（現状） | 50.96 | 51 |
| 0.60（監査ノッチ下シナリオ） | 51.32 | **51（境界未達）** |
| 0.61 | 51.44 | 51 |
| **0.62（見込み）** | **51.56** | **52** ✓ |

**0.62 の根拠**: (i) 再監査の筆頭残欠「cuspidalization=0」が幾何的基体レベルで 0→ε
（楕円 cuspidalization 図式の 2 本の射＋cusp 集合完全決定が実で立つ）、(ii) 残欠 (4)
μ₂ 完全性の正面 discharge（Klein「⊆」→「=」）、(iii) 新規の実算術内容（非全射 witness）。
**0.62 を超えない根拠**: 惰性 0・再構成 0・K 点の影・単一切片・Galois 作用皆無・圏側代理の
まま——title の残り半分の核心（惰性・π₁ 復元）はブロックのまま（§4-1,2）。
**リスクの正直申告**: 敵対的監査が「基体のみ・惰性ゼロ」を重く見て 0.60–0.61 に留めれば
表示は 51 のまま（境界クロスせず）。q3cu-3（μ₂ 完全性）が落ちた場合の fallback
（ker ⊇ Klein のみ）は 0.59–0.60 相当となり境界未達——**q3cu-3 が本ラウンドの成否を握る**。

---

## 6. 実装計画（親向け）

| wave | 枠 | tier/model | タスク | 依存 |
|---|---|---|---|---|
| 1 | 1 | **M / opus** | `Q3TateCuspidalization.lean`（§3.1 q3cu-0〜9・q3cu-8 は任意） | 既存のみ（Q3TateTorsion・RootsOfUnity） |
| 1′ | − | L / fable（スポットのみ） | q3cu-3 μ₂ 完全性が詰まった場合の HELP（レベル横断整合・Quot.ind 段取り） | − |
| 2 | 1 | S–M / sonnet or opus | 独立再監査（AUDIT_RUBRIC 準拠・ソースのみ渡す・build EXIT 0・no sorry・全 public 対象 #print axioms=[propext,Quot.sound]・新規 Classical.choice 0・§4 限定のヘッダ検査・**q3cu-4 が q3tt_klein_torsion の再輸出でないこと**） | wave 1 |

- サブエージェントは**新規 1 ファイルのみ**作成。共有ファイル更新は親が統合時に一括:
  `IUT.lean` import 追記・`build.sh` #print axioms 対象追加・`tools/gen_graph.py` の
  PILLAR 辞書に `Q3TateCuspidalization` → A 追記・`gen_graph.py` 再実行・
  `target_ledger.json`（A8 0.62・監査確定後）・`graph-meta.json`
  （pillars.A.complete_pct 51→52・complete_note に本ラウンド dated entry）・
  `dashboard.md` 二軸表同期。
- 残り並列枠は本設計の範囲外（候補 (b) tripod cusp 簿記は **A9 次ラウンド**の本命として
  別設計に回す。水増し禁止規則優先）。

### 監査チェックリスト（wave 2 用）

- [ ] q3cuSq が Quot.lift の実同種（新規商構成の再発明・値一致定理でない）こと
- [ ] q3cu_mu2_complete が choice-free（IsZpUnit ∃witness＋omega 3分律＋euclid 帰納）で、
      u が**任意の** ℤ₃^× 元（整数対角像に限定されていない）こと
- [ ] q3cu_ker_eq_klein の → 方向が本物（mu2_complete 消費）で ← が q3tt 再輸出のみでないこと
- [ ] 開曲線 subtype が実際に q3cuOpenMap の定義域/終域として使われている（飾りでない）こと
- [ ] q3cu_not_surjective が成立している（非全射の正直装置が消えていない）こと
- [ ] q3tt/q3t/M384F 等の既存正直申告が一切消去・弱化されていないこと
- [ ] ヘッダに §4 の 5 項（惰性 0・再構成 0・K 点の影・単一切片・二重計上排除）が明記されていること
