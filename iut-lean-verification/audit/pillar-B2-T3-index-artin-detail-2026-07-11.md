# B2・T3（上界: index(U_{L₂} : N(U_M)) ≤ 3 / Gal ≅ 余核 同型化）詳細化設計 — 2026-07-11

**分類: [設計のみ / design-only]・tier-L 詳細化ラウンド・complete_pct 0 前進（Lean コードなし・共有ファイル変更なし）**

- 対象: 柱 B・B2（実局所類体論・相互律）の残り主要質量 **T3 = 上界／全射性**。
  現状 s_B2 = 0.36（q9qc: Gal(M/L₂) ↪ U_{L₂}/N(U_M) の literal Grp 商対象への単射まで確定・下界側完了）。
- 本書の成果は (i) T3 の codebase 実対象での正確な再定式化、(ii) **disproof-first 有限検査の実行と結果**（graded ノルムの level ごと全射性の数値確認・障害ゼロ）、(iii) 実 Lean 到達可能なマイルストーン梯子 T3-M1〜M4、(iv) 完備性ステップ（最難所）の到達可能性判定。
- §4 規約: 本書は既存モジュールの正直な限定を一切消さない・弱めない。到達可能性を過大主張しない（各所に「監査次第」「リスク」を明記）。

---

## 1. T3 の正確な再定式化（codebase の実対象で）

### 1.1 番号付けの注意（最初に固定する・混同すると設計が壊れる）

L₂ = ℚ₃(ζ₃) の一様化子は λ = √−3（λ² = −3）、M = ℚ₃(ζ₉) の一様化子は π₉ = ζ₉−1、
e(M/L₂) = 3・e(M/ℚ₃) = 6。codebase の embed: O_{L₂} → O_M（q3kEmbed）の下で

- **λ-番号（L₂ 固有）**: U_{L₂}^{(j)} := 1 + λ^j O_{L₂}
- **π₉-番号（embed 側・codebase の q9nfUfilt）**: embed(U_{L₂}^{(j)}) = { u ∈ embed(O_{L₂}) : q9nfUfilt (3j) (q3kEmbed u) }

つまり **λ-level j ⟺ π₉-level 3j**。依頼文の「U_{L₂}^(3) ⊆ N(U_M)」は **λ-番号**であり、
codebase の q9nfUfilt では **level 9** に対応する（q9gn_norm_U2 の「N(U^(2)) ⊆ U^(9)」の 9 と同じ場所）。
既存の実測: embed(ζ₃) ∈ U^(3)∖U^(4)（λ-level 1・q9nf_zeta_U3/not_U4）、4 = 1+3 ∈ U^(6)∖U^(7)（λ-level 2・q9nf_retarget_witness/sharp）。

### 1.2 T3 の主命題（codebase 語彙）

> **T3-core**: ∀ u : q3rqCar, q3rqUnitMem u → q9nfUfilt 9 (q3kEmbed u) →
> ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = u
>
> （「λ-level 3 以深のすべての L₂ 主単数は M/L₂ ノルムである」= U_{L₂}^{(3)} ⊆ N(U_M)）

これが確立されると index(U_{L₂} : N(U_M)) ≤ 3 は次の**有限側の帳簿**で落ちる
（U_{L₂}/U^{(3)}_λ は位数 18 = 2·3·3 の有限群であり、各 graded 断面の「ノルムで打てる／打てない」が既知資産で決まる）:

| 断面 | 代表 | ノルムで打てるか | 既存資産 |
|---|---|---|---|
| gr⁰（Teichmüller ±1・位数 2） | −1 | **可**: N(−1_M) = −1（奇数次） | q9ps_neg_one_normBase |
| gr¹_λ（≅𝔽₃） | ζ₃ 型 | **可**: N(1+π₉a) の先頭項 (ζ₃−1)N(a)・graded 全射（§2 E 検査で確認） | q9gn_norm_U1_sharp・q9nf_zeta_is_norm |
| gr²_λ（≅𝔽₃・break level） | 4 = 1+3 | **不可**（graded 写像が零・余核の住処） | q9gn_norm_U2・q9lr（4∉N 下界・既確定） |
| U^{(3)}_λ 以深 | — | **T3-core（本書の対象）** | 未 |

したがって余核 U_{L₂}/N(U_M) は ⟨[4]⟩ で生成され位数 ≤ 3、既存の下界（q9qc_gal_embeds:
像 = 位数 3 部分群 ⟨[4]⟩ への単射）と合わせて **位数ちょうど 3・q9qcGalHom は全射 ⟹
Gal(M/L₂) ≅ q9qcCoker（本物の LCFT 単数同型）** に昇格する。これが T3-M4 の最終形。

なお値群側（T1）は N(π₉) = ζ₃−1（q9wr_normBase_pi9・λ-level 1 の一様化子）で既に全射であり、
T3 で残るのは純粋に単数側 U_{L₂}/N(U_M) の上界のみである。

### 1.3 正直な限定（本設計のスコープ外・§4 規約で維持）

- q9qc の限定 1 を継承: 対象は**整単数余核** U_{L₂}/N(U_M) であって分数元込みの
  L₂^×/N(M^×) の完全配線（cap (b)）ではない。T3-M4 完了後もこの限定は残る（残 s_B2 に計上）。
- 単一拡大 M/L₂/ℚ₃ のみ。Artin 写像の Frobenius 正規化・一般局所体はスコープ外。

---

## 2. 核心難点と disproof-first 有限検査（実行結果）

### 2.1 核心難点の同定

T3-core は「ノルム方程式 N(x) = u の逐次解法」であり、次の 3 つが積み重なる:

1. **Herbrand shift**: 依頼文の「graded ノルム gr^i(U_M) → gr^i(U_{L₂}) は全射か」を
   **同番号のまま読むと問いが不正**。分岐 break は t = 2（下=上・v_M(σπ₉ − π₉) = v_M(ζ₉(ζ₃−1)) = 3、
   i_G(σ) − 1 = 2）であり、Serre 型の対応は target λ-level j ≥ 3 に対し **source π₉-level
   ψ(j) = t + 3(j − t) − ... = 3j − 4**（j=3↦5, j=4↦8, j=5↦11, …）。正しい graded 写像は
   g_j : gr^{3j−4}(U_M) → gr^j_λ(U_{L₂}), a mod π₉ ↦ [(N(1+π₉^{3j−4}a) − 1)/λ^j] mod λ。
   codebase 既存の q9nf_norm_filt「N(U^(i)) ⊆ U^(i+1)」は**粗い包含**であって sharp な挙動ではない。
2. **各 level の全射性**: g_j が 𝔽₃ 上全射（実は全単射）か。1 つでも非全射 level があれば
   index > 3 となり LCFT 描像が崩れる——これが本ラウンドの **disproof-first ゲート**。
3. **無限積の収束（完備性）**: 各 level を 1 段ずつ潰す補正列 x_n の無限積の極限を
   **choice-free** に構成し N(lim) = u を厳密等式で閉じる。これが最難所（§5 で判定）。

### 2.2 有限検査の方法

ℤ[ζ₉]（Φ₉ = x⁶+x³+1 による厳密整数演算・p 進打ち切りなし）で σ: ζ₉↦ζ₉⁴、
N(z) = z·σz·σ²z を直接計算し、ℤ[ζ₃] 内の λ-付値と先頭剰余（𝔽₃）を厳密に読む。
スクリプトは付録 A（再現可能・依存なし・数秒）。

### 2.3 検査結果（**ゲート = PASS・障害ゼロ**）

**(A) break level j=2 の零性**（既存 q9gn_norm_U2 の照合）:
N(1+aπ₉²)−1 の λ-val は a=1 で 3、a=2 で 4 —— gr² 写像は零。✓（余核が gr² に住む描像と整合）

**(B) level ごと graded 全射性（本丸）** — j = 3..8、source i = 3j−4:

| j (λ-level) | i = 3j−4 | a=1 → (val, res) | a=2 → (val, res) | 正確 level | 𝔽₃ 全単射 |
|---|---|---|---|---|---|
| 3 | 5  | (3, 1) | (3, 2) | ✓ | ✓ |
| 4 | 8  | (4, 2) | (4, 1) | ✓ | ✓ |
| 5 | 11 | (5, 1) | (5, 2) | ✓ | ✓ |
| 6 | 14 | (6, 2) | (6, 1) | ✓ | ✓ |
| 7 | 17 | (7, 1) | (7, 2) | ✓ | ✓ |
| 8 | 20 | (8, 2) | (8, 1) | ✓ | ✓ |

**全 level で正確な値・𝔽₃ 全単射**。しかも先頭剰余が j の偶奇で ±1 交代しており、これは
§3 の λ-再帰（1 段ごとに res_M(w) = −1 が掛かる）の予言と**正確に一致**する。

**(C) 悉皆検査（3 level 一括の強い形）**: U_M^{(5)} の 3⁹ = 19683 元全てのノルムを厳密計算し
mod λ⁶（= mod 27）で分類 → **U^{(3)}_λ/U^{(6)}_λ の全 27 類を完全被覆**（image == target: True）。
逐次近似 3 段分が一括で成立していることの直接検証。

**(D) 負の対照（下界との整合）**: 全単数のノルム像 mod λ³ は 18 類中ちょうど **6 類**
（= {±1, ±ζ₃, ±ζ₃²} 型）で**余核位数ちょうど 3**、かつ **4 はどの単数のノルムとも mod λ³ で
一致しない**（既存 crux 4∉N・q9lr と整合。もし 4 が打たれていたら下界側と矛盾するところ、矛盾なし）。

**(E) gr¹ 全射性**（T3-M4 の帳簿に必要）: N(1+aπ₉)−1 は λ-val ちょうど 1・剰余 a↦−a の全単射。✓

**結論**: 反証は出なかった。**index = 3 の LCFT 描像どおり**であり、per-level 全射性は
「研究リスク」ではなく「実装対象」に降格した。残る本質リスクは §2.1-(3) の完備性のみ。

---

## 3. 新イディオムの設計: λ-再帰による閉形式 graded 逆写像

per-level 全射性を「level ごとの有限計算の無限族」としてではなく、**一様な閉形式**で
Lean 化できることが本設計の主発見である。鍵は 3 つの既存資産の合成:

1. **Tr の閉形式**（q9nf_tr_embed）: Tr(t) = embed(3·t₀)。
2. **π₉³ の分解**（q9ps_pi9_cube）: π₉³ = embed(λ)·w、w は実単数・**res_M(w) = 2 = −1**
   （resL(ζ₃+1) = 1+1 = 2・resL(±λ) = 0、q9rf 資産で 3 行）。
3. **level-2 剰余公式**（q9gn_resL_t1）: resL((π₉²s)₀) = res_M(s)。

**λ-再帰**（新補題・Tr の O_{L₂}-線形性 Tr(embed(c)·t) = c·Tr(t) が必要——座標計算 1 本）:

> π₉^{i+3}·a = embed(λ)·(π₉^i·(w·a)) ⟹ **Tr(π₉^{i+3}a) = λ·Tr(π₉^i·(w·a))**

これにより g_{j+1}(a) = (w̄)·g_j 型の再帰が走り、**基底 j=3** は

> Tr(π₉⁵a) = λ·Tr(π₉²·(wa)) = λ·embed(3·(π₉²(wa))₀) = −λ³·embed 側先頭、
> 先頭剰余 = −resL((π₉²(wa))₀) = −res_M(wa) = −w̄·ā = ā（w̄ = −1）

と**完全に既存イディオムの合成で閉じる**。他項が深いことも既存の一様下界で足りる:
i = 3j−4 (j≥3) のとき E₂ ∈ (π₉^{2i})（q9nf_e2_dvd）で 2i = 6j−8 ≥ 3j+1 ⟺ j ≥ 3 ✓、
ノルム 3 次項 ∈ (π₉^{3i})（q9nf_normterm_dvd）で 3i = 9j−12 ≥ 3j+1 ⟺ j ≥ 3 ✓。
（q9nf の正直限定 2「trace 下界は π₉⁶ のみ・i≤5 制限」は本経路では**回避される**——
Tr を可除性で見積もらず、λ-再帰で正確な λ-level に**等式として**持ち込むため。）

もう 1 つの新小物: **𝔽₃ からの構成的切断**。逐次近似の各段で剰余類から代表 a ∈ {0,1,2} を
**データとして**取り出す必要がある。𝔽₃ = zmod 3 は Int の Quot だが、r ↦ r % 3 は
類上定数なので Quot.lift で**choice-free な切断 𝔽₃ → Int が定義できる**（可算選択不要）。

---

## 4. マイルストーン梯子（T3-M1 〜 T3-M4）

### T3-M1: per-level graded 全射性（閉形式・λ-再帰）

- **主張スケッチ**: ∀ j ≥ 3, ∀ u, q3rqUnitMem u → q9nfUfilt (3j) (q3kEmbed u) →
  ∃ a : q3kCar（構成的・§3 の切断で剰余から陽に）,
  q9nfUfilt (3(j+1)) (q3kEmbed (u ·_{L₂} (N(1+π₉^{3j−4}a))⁻¹))。
  （乗法形。逆元は q3rqUnitMem からの q3rq 側逆元・既存機構。）
- **消費**: q9nf_norm_expand・q9nf_tr_embed・q9nf_e2_dvd・q9nf_normterm_dvd・
  q9ps_pi9_cube・q9ps_w_unit・q9gn_resL_t1・q9rf_resL_*・q9rf_div3（剰余→可除の witness）。
- **新イディオム**: Tr の O_{L₂}-線形性（1 本）・λ-再帰補題・𝔽₃ 構成的切断（Quot.lift %3）・
  j 上の帰納で先頭剰余公式 g_j(a) = ±ā を運ぶ枠。
- **難度**: **1〜2 ラウンド（opus・本設計済みのため）**。
- **s_B2 予測**: 0.36 → **0.39–0.40**（graded 上界機構の実 Lean 化・監査次第）。

### T3-M2: 逐次近似の有限深度降下

- **主張スケッチ**: ∀ u（λ-level 3 以深の単数）, ∀ n, ∃ x_n ∈ U_M^{(5)}（π₉^{3j−4} 型因子の
  有限積・陽な再帰構成）, q9nfUfilt (9+3n) (q3kEmbed (u · (N x_n)⁻¹))。
- **消費**: T3-M1（帰納の各段）・q9nf_ufilt_mul・q3k_normBase_mul・q3kInv/q3rq 逆元帳簿。
- **新イディオム**: なし（M1 の帰納合成のみ）。全て choice-free（x_n は陽な有限積）。
- **難度**: **1 ラウンド（opus）**。
- **s_B2 予測**: → **0.42**。**正直申告必須**: M2 まででは「任意精度でノルムに近い」だけであり
  「u はノルムである」（T3-core）は**主張できない**。ヘッダにこの限定を明記すること。

### T3-M3: 完備性・無限積の組み立て（最難所）

- **主張スケッチ**: (x_n) の π₉-進極限 x ∈ O_M を choice-free に構成し、
  N の連続性と O_M の分離性で **N(x) = u（厳密等式）** を閉じる ⟹ T3-core。
- **サブ段（実装順）**:
  - **M3a 可除性ブリッジ**: π₉^{6k} ∣ z ⟺ 3^k ∣ z（O_M 内・3 = π₉⁶u₆ の双方向・易）＋
    「3^k ∣ z ⟺ z の 6 個の z3-座標すべてが 3^k 可除」（3^k 倍が座標ごとのスカラー作用・中）＋
    **z3 の level-k 可除性判定** 3^k ∣ c ⟺ c.val k = 0（zp_dvd_p_iff の level-1 から k への
    一般化・zpDivP の k 回帰納・**本 M3 で最も新しい機械**）。
  - **M3b O_M 完備性コンストラクタ**: π₉-modulus-Cauchy 列（modulus 陽・M2 の列は
    modulus M(n) = n が陽に取れる）→ M3a で 6 本の z3 modulus-Cauchy 座標列 →
    **z3cLim を座標ごとに適用**（Zp3Complete の資産がそのまま働く）→ 収束（z3c_converges
    座標版）＋分離性（∀n 3^n∣t ⟹ t = 0——z3 は逆極限なので Subtype.ext + funext で易）。
  - **M3c N の連続性**: N(x)−N(y) ∈ (x−y)（望遠鏡分解 xσxσ²x − yσyσ²y の 3 項各々が
    (x−y) 可除・q9nf_dvd_sigma 消費）⟹ v(N x − N x_n) ≥ v(x − x_n) ⟹
    N(x) ≡ u mod π₉^∀ ⟹ 分離性で等式。x の単数性は res_M(x) = 1 ≠ 0 ⟹ 単数
    （q9rf_local の証明内部にある順方向を独立補題に抽出・小）。
- **消費**: z3cIsModCauchy・z3cModUp・**z3cLim・z3c_converges・z3c_sub_eq**（Zp3Complete）・
  zpDivP/zp_dvd_p_iff（PadicDivision）・q9ps_three_split・q9nf_dvd_sigma・q9rf_local（内部）。
- **新イディオム**: z3 level-k 可除性判定（M3a）・座標ごと完備性コンストラクタ（M3b）。
  いずれも**既存パターンの k-一般化／6 重化**であり、未知の数学は含まない。
- **難度**: **2〜3 ラウンド（設計 = 本書済み・実装 opus・詰まりのみ fable スポット）**。
  リスク: M3a の level-k 判定が帳簿的に重い可能性（zpDivP の商の val 整合）。fallback:
  可除性 witness（q9wrDvd の c）を陽に持ち回る形で座標判定を迂回する設計も可（等価・やや冗長）。
- **s_B2 予測**: → **0.48–0.52**（T3-core 確立・上界の解析的本体）。

### T3-M4: index ≤ 3 の結論と Gal ≅ q9qcCoker 同型

- **主張スケッチ**: (i) ∀ u ∈ U_{L₂}, ∃ x ∈ U_M, ∃ c ∈ {0,1,2},
  u ≡ 4^c · N(x) （q9rcCongMod の言葉で [u] = [4]^c）——§1.2 の表の帳簿
  （gr⁰: ±1・gr¹: q9gn_norm_U1_sharp ベースの 1 段降下（E 検査で全射確認済）・
  gr²: 4^c で吸収（q9nf_retarget_witness/sharp が「4 が gr² を生成」の実体）・
  U^{(3)}_λ: T3-core）。
  (ii) ⟹ q9qcCoker の全元は q9qcGalHom の像 ⟹ **q9qcGalHom 全単射**・逆 Hom 構成 ⟹
  **Gal(M/L₂) ≅ U_{L₂}/N(U_M)（本物の Grp 同型・LCFT 単数同型定理の実例）**。
- **消費**: T3-M3・q9qc 全資産・q9rc/q9rg（[4] の位数 3）・q9ps_neg_one_normBase・
  q9gn_norm_U1_sharp・q9nf_retarget_witness/sharp。
- **難度**: **1〜2 ラウンド（opus・M3 完了後）**。
- **s_B2 予測**: → **0.55–0.62**（残り: cap(b) 分数元 M^× の配線・Artin 正規化・一般化。
  これらは T3 の外・別途詳細化が必要）。

### 予測サマリ

| 段 | 内容 | 難度 | s_B2 予測（監査次第） |
|---|---|---|---|
| T3-M1 | per-level graded 全射性（λ-再帰・閉形式） | 1–2 ラウンド opus | 0.36 → 0.39–0.40 |
| T3-M2 | 有限深度逐次近似 | 1 ラウンド opus | → 0.42 |
| T3-M3 | 完備性・N(x)=u 厳密化 | 2–3 ラウンド opus（+fable スポット） | → 0.48–0.52 |
| T3-M4 | index ≤ 3・Gal ≅ 余核 | 1–2 ラウンド opus | → 0.55–0.62 |

---

## 5. 正直な verdict

1. **T3 は research-blocked ではない**。恐れられていた 2 つの障害は両方とも解体された:
   - *per-level 全射性*: 有限検査で全 level 無障害（§2.3 B/C）、かつ λ-再帰（§3）により
     **無限族でなく閉形式＋帰納**で Lean 化できる。未知の数学は残っていない。
   - *完備性*: 「実逆極限ノルム解コンストラクタ」は**ゼロから建てる必要がない**。
     O_M = z3⁶（座標）なので、Zp3Complete の modulus-Cauchy 機構（z3cLim・choice-free）の
     **座標ごと適用 + level-k 可除性判定**に還元される（§4 M3a/M3b）。これは重い（2–3 ラウンド）が
     既存パターンの一般化であり、新規 choice も新規公理も要らない。
2. **最短の次 opus 一手 = T3-M1**（本設計をそのまま実装・消費リストと新補題 3 本が §3/§4 に明示済み）。
   s_B2 0.36 → 0.39–0.40。M1 は M3 と独立に着手可能で、失敗リスクが最も低い。
3. **過大主張の禁止事項**（実装ラウンドのヘッダに転記すること):
   - M1/M2 の段階では「u はノルム」を主張しない（有限深度近似のみ）。
   - M3 完了までは s_B2 の 0.42 超えを主張しない。
   - M4 完了後も cap(b)（分数元 M^×・full L₂^×/N(M^×)）と Artin 正規化は**未達のまま残る**と
     正直申告する（q9qc 限定 1 の継承）。
4. 予測値はすべて独立監査次第。M3 が 3 ラウンドに滑るリスクを見込んでおく。

---

## 付録 A: disproof-first 有限検査スクリプト（再現用・依存なし・厳密整数演算）

```python
# Z[zeta9] mod Phi9 = x^6+x^3+1 (exact), sigma: x->x^4, N(z)=z*sz*s2z
def pmul(a,b):
    c=[0]*11
    for i in range(6):
        if a[i]:
            for j in range(6): c[i+j]+=a[i]*b[j]
    for k in range(10,5,-1):
        v=c[k]
        if v: c[k]=0; c[k-6]-=v; c[k-3]-=v
    return tuple(c[:6])
padd=lambda a,b: tuple(x+y for x,y in zip(a,b))
ONE=(1,0,0,0,0,0); PI=(-1,1,0,0,0,0)
SIG=[(1,0,0,0,0,0),(0,0,0,0,1,0),(0,0,-1,0,0,-1),(0,0,0,1,0,0),(0,-1,0,0,-1,0),(0,0,1,0,0,0)]
def sigma(a):
    r=(0,)*6
    for k in range(6):
        if a[k]: r=padd(r,tuple(a[k]*t for t in SIG[k]))
    return r
def N(z):
    n=pmul(pmul(z,sigma(z)),sigma(sigma(z)))
    assert n[1]==n[2]==n[4]==n[5]==0
    return (n[0],n[3])                    # a+b*zeta3
lmul=lambda u,v:(u[0]*v[0]-u[1]*v[1], u[0]*v[1]+u[1]*v[0]-u[1]*v[1])
LAM=(1,2)                                 # lambda=1+2*zeta3, lambda^2=-3
def lam_val(t):                           # (lambda-val, leading residue in F3)
    v=0
    while (t[0]+t[1])%3==0:
        m=lmul(t,LAM); t=(-m[0]//3,-m[1]//3); v+=1
    return v,(t[0]+t[1])%3
def pip(k):
    r=ONE
    for _ in range(k): r=pmul(r,PI)
    return r
# (B) per-level: j>=3, source i=3j-4
for j in range(3,9):
    i=3*j-4
    for a in (1,2):
        u=N(padd(ONE,tuple(a*t for t in pip(i))))
        print(j,i,a,lam_val((u[0]-1,u[1])))   # expect (j, nonzero), bijective in a
# (C) exhaustive: N(U_M^(5)) covers all 27 classes of U^(3)/U^(6) mod 27
import itertools
hit=set()
P=[pip(5+k) for k in range(9)]
for cs in itertools.product((0,1,2),repeat=9):
    z=ONE
    for k,ak in enumerate(cs):
        if ak: z=padd(z,tuple(ak*t for t in P[k]))
    u=N(z); hit.add((u[0]%27,u[1]%27))
print(len(hit))                            # == 27
```

実行結果（本ラウンドで実施・§2.3 に転記）: (A) break 零性 ✓、(B) j=3..8 全 level で
正確 λ-level・𝔽₃ 全単射 ✓、(C) 27/27 完全被覆 ✓、(D) 余核位数ちょうど 3・4 非ノルム ✓、
(E) gr¹ 全射 ✓。**障害ゼロ・ゲート PASS**。
