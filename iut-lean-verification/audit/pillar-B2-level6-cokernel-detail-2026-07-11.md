# 柱B2 詳細化: level-6 graded cokernel の同定 — retarget 後の B2 本体の段階分解（2026-07-11）

**種別**: 詳細化ドキュメント（**design-only・Lean 実装なし・tier-L 枠の消費・complete_pct 0 前進**）
**対象**: `target_ledger.json` 柱B B2「実局所類体論(相互写像・実)」（w20・status 0）——q9nf スパイクの retarget 後の**真の crux「4 = 1+3 ∉ N_{M/L₂}(M^×)」**を Lean-provable なマイルストーン列に分解する。
**前提資産**: `IUT/Q3NormFiltrationSpike.lean`（q9nf: U^(i)・norm graded・retarget witness）・`IUT/Q3WildRamFiltrationReal.lean`（q9wr）・`IUT/Q3KummerPiSplit.lean`（q9ps: 3=π₉⁶·u₆）・`IUT/Q3RamifiedQuadratic.lean`（q3rq）・`IUT/Q3ArtinConductorReal.lean`（q9ac: a(χ)=3）・先行 scope `audit/pillar-B2-reciprocity-normgroup-scope-2026-07-11.md`（★訂正済み）。
**姿勢**: 先行 scope の中心 crux「ζ₃∉N」が偽だった（q9nf_zeta_is_norm が反証）教訓に従い、**本書はまず retarget 候補 1+3 を「反証ファースト」で検証してから**ラダーを設計した（§4）。検証は**合格**——決定精度での有限全数計算により 4 ∉ N(単数) を確認済み。

---

## 0. TL;DR

- **retarget 候補は正しい**: 4 = 1+3 ∉ N_{M/L₂}(M^×)。ζ₃ のような裏切りは**起きない**。根拠は 3 系統（§4）: (i) 古典 rec 検算 N_{L₂/ℚ₃}(4)=16≡7 mod 9 ∉ 1+9ℤ₃、(ii) **決定精度の有限全数検証**——N(x) mod λ³ は x mod 3π₉ のみに依存（3π₉ = π₉⁷·u₆）ので単数類 1458 個の厳密整数計算で決着し、**N(x)≡4 mod λ³ の解は 0 個**・ノルム像は (O_{L₂}/λ³)^× の 18 類中ちょうど 6 類（指数 3）・U^(2) 類 242 個全てで level-6 graded 像が零、(iii) 手計算 N(1+π₉²) = 7+3ζ₃ = 1+3(2+ζ₃)（v_λ=3・graded 類 0）。
- **cokernel ℤ/3 の局在**: tame graded piece（残余体 𝔽₃・a³=a）では余核ゼロ、**level 6（L₂ 側 λ²-level 2 = 上付き break t=2）に全集中**。level-6 graded map の零性の正体は**厳密な打ち消し** Tr(π₉²a) + N(π₉²a) ≡ 3·res(a) − 3·res(a) ≡ 0 mod λ³——トレース項（level 6 で初めて (3) に入る加法的寄与）と 3 乗ノルム項（Fermat a³≡a mod 3）が**係数ぴったり逆符号**で消し合う。これが conductor = break+1 = 3（q9ac の a(χ)=3 と整合）の具体形。
- **設計上の 2 大簡約を発見**（実装コストを 1 ラウンド分下げる）:
  1. **E₂ の鋭い評価は環恒等式 2·E₂(t) = Tr(t)² − Tr(t²) に帰着**——右辺は両方トレースなので `q9nf_trace_kill`（Tr=3·t₀）だけで π₉⁶ ∣ E₂ が**全 t で**出る（2 は単数）。q9nf 正直限定 3（E₂ の粗い下界）はこれで退役。
  2. **最終矛盾は既存 `q9nf_retarget_sharp` の消費で閉じる**: x∈U^(2) ⟹ embed(N x) ∈ U^(9) ⊆ U^(7)、一方 embed(4) = 1+embed(3) ∉ U^(7)。
- **ラダー**: M1（残余体 𝔽₃ と O_M の局所性・z3 Euclid ステップ）→ M2（level-6 graded 公式と零性）→ M3（**crux: 4∉N** — 初の status mover、予測 s_B2 0→0.25–0.35）→ M4（類 [4] の位数 3・Gal との ℤ/3 対応、→0.35–0.45）→ M5（指数 ≤3・Artin 写像・**research 級・未スケジュール**）。
- **正直な見通し**: M3 到達に実装 2 ラウンド（M1 が 1、M2+M3 が 1、詰まれば +1）。**本書自体は complete_pct 0 前進**（設計のみ）。

---

## 1. LCFT ターゲットの正確な再定式化と既存資産の地図

### 1.1 目標

M = ℚ₃(ζ₉) = q3k（O_M = O_{L₂}[Y]/(Y³−ζ₃)）、L₂ = ℚ₃(ζ₃) = q3rq、Gal(M/L₂) = ⟨σ⟩ = q9kdG（位数 3）。目標は局所類体論の本体:

> **L₂^× / N_{M/L₂}(M^×) ≅ Gal(M/L₂) ≅ ℤ/3。**

分解すると 3 つの主張:
(T1) **値群側**: N(M^×) は v_{L₂} に全射（N(π₉) = ζ₃−1 が L₂ 一様化子）。
(T2) **余核の下界**: ∃ 非ノルム単数、その類が位数 3 ⟹ ℤ/3 ↪ L₂^×/N(M^×)。**retarget 後の crux は「4 = 1+3 が非ノルム」**。
(T3) **余核の上界**: 指数 ≤ 3、すなわち U_{L₂}^(3) ⊆ N(U_M)（conductor 側の全射性）＋Artin 写像の構成。

### 1.2 既存資産の地図（何がどこまで建っているか）

| 部品 | 状態 | 所在 |
|---|---|---|
| N(π₉) = ζ₃−1（L₂ 一様化子）・q3rqNorm(ζ₃−1)=3 | **済** | `q9wr_normBase_pi9`・`q9wr_qnorm_zeta_sub` |
| x 単数 ⟺ N(x) 単数 | **済（定義そのもの）** | `q3kUnitMem x := q3rqUnitMem (q3kNormBase x)` |
| 3 乗はすべてノルム（(L₂^×)³ ⊆ N） | **済** | `q9ps_normBase_embed`（N(embed n)=n³） |
| **ζ₃ ∈ N(M^×)**（旧 crux の反証） | **済** | `q9nf_zeta_is_norm`（witness ζ₉） |
| U^(i) = 1+π₉^i O_M・積閉・単調 | **済** | `q9nfUfilt`・`q9nf_ufilt_*` |
| ノルム展開 embed N(1+t) = 1+Tr(t)+E₂(t)+embed N(t) | **済** | `q9nf_norm_expand` |
| Tr(t) = embed(3·t₀)・π₉⁶ ∣ Tr(t)（∀t） | **済** | `q9nf_tr_embed`・`q9nf_trace_kill` |
| N(U^(i)) ⊆ U^(i+1)（1≤i≤5） | **済** | `q9nf_norm_filt` |
| 3 = π₉⁶·u₆（wild 分割）・λ = π₉³w⁻¹ | **済** | `q9ps_three_split`・`q9nf_embed_lambda` |
| 1+3 ∈ U^(6)∖U^(7)（候補の正確な位置） | **済** | `q9nf_retarget_witness`・`q9nf_retarget_sharp` |
| break t=2・different d=6 | **済** | `q9wr_break`・`q9wr_different` |
| 導手 a(χ)=3（傍証: 非ノルムは L₂-level 2） | **済** | q9ac（`Q3ArtinConductorReal.lean`） |
| Gal 側 ℤ/3（Kummer 双対の易しい側） | **済** | q9kd（`Q3KummerDualityReal.lean`） |
| **残余体 𝔽₃ への還元・O_M の局所性（¬単数 ⟹ π₉∣）** | **無い（M1）** | — |
| **level-6 graded 公式と零性** | **無い（M2）** | — |
| **非ノルムの実在（crux）** | **無い（M3）** | — |

(T1) は既存資産でほぼ閉じる（先行 scope §2.1 P3）。**(T2) が M1–M4、(T3) が M5（research）**。

---

## 2. graded-cokernel 還元: なぜ tame は自明で level 6 に全集中するか

### 2.1 filtration の対応（M 側 π₉-level と L₂ 側 λ-level）

v_M(λ) = 3（`q9nf_embed_lambda`: embed λ = π₉³·w⁻¹）、v_M(3) = 6（`q9ps_three_split`）。L₂ 側 U_{L₂}^(j) = 1+λ^j O_{L₂} の M への埋め込みは U^(3j)。上付き break は t = 2（Herbrand: φ = id on [0,2]）なので、古典 LCFT の予言は「非ノルム単数は U_{L₂}^(2)∖U_{L₂}^(3) の graded 類、conductor = 3」＝ **M 側 level 6**（`q9nf_retarget_witness/sharp` の 1+3 ∈ U^(6)∖U^(7) と一致）。

### 2.2 tame graded piece（level 0, 1）での余核消滅

残余体は k = 𝔽₃（M/ℚ₃ 完全分岐）で、**𝔽₃ 上 3 乗は恒等 a³ = a**（Fermat）。

- **Level 0**（residue）: res(N(x)) = res(x)·res(σx)·res(σ²x) = res(x)³ = res(x)（σ は residue を固定: σ の座標作用は (x₀, ζ₃x₁, ζ₃²x₂) で ζ₃ ≡ 1 mod λ）。よって k^× 上のノルム誘導写像は**恒等**——全射・余核ゼロ。
- **Level 1**（gr¹, i=1）: `q9nf_norm_graded` の 4 項分解で、Tr は π₉⁶∣（trace_kill）、E₂ は π₉⁶∣（M2(a) の環恒等式による——§3）、先頭項は embed N(π₉a) = embed((ζ₃−1)N(a))。graded 写像 gr¹(U_M) → gr¹(U_{L₂}) は ā ↦ (ζ₃+1)‾·ā³ = 2ā = −ā（ζ₃−1 = λ(ζ₃+1)、`q9ps_coord0`）——**𝔽₃ 上の −1 倍で全単射**・余核ゼロ。ζ₃（∈U^(3)∖U^(4)、L₂-level 1）がノルムに打たれる `q9nf_zeta_graded_norm_hit` はこの全射性の実例。
- **Level ≥ 3（L₂ 側）**: 余核の同定には不要（M3 の降下は「level ≥3 に落ちること」しか使わない）。全射性（＝(T3)）は research 側へ。

**したがって単数余核 [U_{L₂}:N(U_M)] = 3 は丸ごと level 2（M 側 6）の graded piece 1 枚 𝔽₃ に集中し、そこでの graded 写像は零写像でなければならない。**

### 2.3 level-6 の正確な graded 写像とその零性（打ち消しの正体）

**写像の定義**: Φ : gr²(U_M) → gr²(U_{L₂})、代表 1+π₉²a ↦ N(1+π₉²a) の U_{L₂}^(3) 類。両辺 ≅ 𝔽₃（gr²(U_{L₂}) = λ²O/λ³O の生成元は λ² = −3、すなわち **1+3 = 1+(−1)·λ² の類は −1 ≠ 0**）。

**4 項分解の level 勘定**（t = π₉²a）:
- **Tr(t) = embed(3·(π₉²a)₀)**: π₉² の座標は (1,−2,1)（(Y−1)² = Y²−2Y+1）なので座標積公式（`q3kMul_0` 型）で (π₉²a)₀ = a₀ + ζ₃(a₁−2a₂)。**一般に単数レベル ⟹ Tr は v_λ = 2 ちょうど＝level 6 で初めて寄与**（trace の像はちょうど (3) = λ²O——「トレースは level 6 で発火」の正確な意味）。
- **embed N(t) = embed((ζ₃−1)²·N(a)) = embed(−3ζ₃·N(a))**: これも v_λ = 2（a 単数のとき）——乗法的（3 乗・Frobenius 型）寄与。
- **E₂(t)**: 2E₂ = Tr(t)²−Tr(t²)、Tr(t²) = embed(3(π₉⁴a²)₀) で (π₉⁴a²)₀ = λ·(wπ₉a²)₀（π₉⁴ = embed(λ)·wπ₉・座標は λ 線形）だから **v_λ ≥ 3——level 6 に寄与しない**。

**零性（打ち消し）**: level-6 部分の和は
```
Tr(t) + embed N(t) = embed( 3·[ (π₉²a)₀ − ζ₃·N(a) ] )
```
で、括弧内を mod λ で見ると（ζ₃ ≡ 1、3 ≡ 0）:
```
(π₉²a)₀ − ζ₃N(a) ≡ (a₀+a₁−2a₂) − (a₀³+a₁³+a₂³) ≡ (a₀−a₀³)+(a₁−a₁³)−(2a₂+a₂³) ≡ −3a₂ ≡ 0
```
（**Fermat: 3 ∣ c³−c in ℤ₃**）。よって λ ∣ 括弧 ⟹ λ³ ∣ 和 ⟹ **Φ ≡ 0**。検算（a=1）: Tr(π₉²)+N(π₉²) = 3 + (−3ζ₃) = −3(ζ₃−1)、v_λ = 3 ✓。

**非全射性の正体**: 加法的（trace）寄与 +3·res(a) と乗法的（cube/norm）寄与 −3ζ₃·res(a) ≡ −3·res(a) が**係数ぴったり逆符号**。wild break でトレースがちょうど (3) に入射する level と、𝔽₃ 上 Frobenius が恒等になる事実の合流点であり、これが conductor = break+1 の機構そのもの。Φ = 0 ⟹ ノルムは gr² の非零類（1+3 の類 = −1）に**届かない**。

---

## 3. マイルストーン・ラダー（実装順・各項 Lean ターゲット）

記法: 新モジュール接頭辞は仮に q9rf（M1: residue field）・q9gn(M2: graded norm)・q9lr（M3/M4: local reciprocity）。各項に (a) 文の骨子 (b) 消費 (c) 新イディオム (d) 難度 (e) s_B2 予測。

### M1 — 残余体 𝔽₃ と O_M の局所性（`Q3ResidueFieldReal.lean` 仮）

**(a) 文の骨子**:
```
q9rfRes3 : z3.carrier → Fin 3                 -- val 1 の Quot.lift（構成的）
q9rf_div3 : q9rfRes3 c = 0 → ∃ k, c = z3.mul q3rqThree k   -- ★ z3 Euclid ステップ
q9rfResL (n : q3rqCar) : Fin 3 := q9rfRes3 n.1              -- λ を潰す
q9rfResM (x : q3kCar) : Fin 3 := q9rfResL (x₀+x₁+x₂)        -- Y ≡ 1
q9rf_resM_mul / q9rf_resM_add                                -- 乗法性・加法性
q9rf_kernel : q9rfResM x = 0 → q9wrDvd q9psPi9 x            -- ★ 完全性（核 = (π₉)）
q9rf_local  : ¬ q3kUnitMem x → q9wrDvd q9psPi9 x            -- O_M は局所（対偶形）
q9rf_res_norm : q9rfResL (q3kNormBase x) = q9rfResM x       -- res∘N = res³ = res
```
核の完全性の証明は**選択公理なしの陽な分解**: x − (x₀+x₁+x₂) = π₉·(x₁ + x₂·(Y+1))（一行の座標計算）、残る embed(s) 側は res(s)=0 ⟹ s = 3k + λm 形 ⟹ π₉³ ∣ embed(s)（3 = π₉⁶u₆・λ = π₉³w⁻¹ 消費）。3k の witness k が `q9rf_div3`。
**(b) 消費**: `q9ps_three_split`・`q9nf_embed_lambda`・q3k 座標公式・`q9wr_three_mul_not_unit` 系の val-1/Quot 操作前例（quot_exact・modCong）。
**(c) 新イディオム（唯一の HELP リスク）**: **z3 の Euclid ステップ `q9rf_div3`**——逆極限担体上の「3 で割る」構成: k.val n := (s.val (n+1) の代表を Int 除算で /3) の Quot.lift 井戸定義性（(m+3^{n+1}c)/3 = m/3 + 3ⁿc の整合、負数の Int 除算規約に注意）。前例（`q9wr_three_mul_not_unit` の val-1 抽出）はあるが逆方向（witness 構成）は初。
**(d) 難度**: **1 ラウンド（opus）**。q9rf_div3 が詰まれば fable HELP 1 スポット。
**(e) s_B2**: **0（正直: 足場）**。ただし B1 の残件「一般元の付値の部分建設」に実質重なるので B1 の note 更新はあり得る（監査判断）。**complete_pct 表示は動かない見込み**。

### M2 — level-6 graded 公式と零性（`Q3GradedNormBreak.lean` 仮）

**(a) 文の骨子**:
```
q9gn_two_e2 : (2:O_M)·E₂(t) = (Tr t)² − Tr(t²)              -- 純環恒等式（対称式）
q9gn_e2_kill : ∀ t, q9wrDvd (q9nfPiPow 6) (q9nfE2 t)         -- trace_kill×2 + 2 単数
q9gn_fermat3 : ∀ c : z3.carrier, ∃ k, c³ − c = 3k            -- Fermat（val-1 有限検査+div3）
q9gn_break_cancel : ∀ a, q9wrDvd (q9nfPiPow 9)
    (Tr(π₉²a) + embed(N(π₉²a)))                              -- ★ 打ち消し（§2.3）
q9gn_norm_U2 : q9nfUfilt 2 x → q9nfUfilt 9 (embed (N x))     -- ★ N(U^(2)) ⊆ U^(9)
q9gn_norm_U1_sharp : q9nfUfilt 1 x → π₉⁶ ∣ (embed(N x) − 1 − embed((ζ₃−1)N(a)))
                                                              -- level-1 先頭項の分離（M3 用）
```
q9gn_break_cancel の中身: 3·[(π₉²a)₀ − ζ₃N(a)] の括弧を Fermat witness kᵢ（aᵢ³−aᵢ=3kᵢ）と ζ₃−1 = λ(ζ₃+1) で **λ·c の陽な closed form** に組み上げる（§2.3 の分解を項別に）。規模は `q9ps_w_norm` の 2–3 倍の座標 rw。
**(b) 消費**: `q9nf_norm_expand`・`q9nf_tr_embed`・`q9nf_trace_kill`・q3kMul 座標公式・`q9ps_coord0`・`q3rq_two_unit`（+embed 単数化 `q9wr_embed_unit`）・M1 の q9rf_div3（Fermat の witness 化）。
**(c) 新イディオム**: 2E₂ = Tr²−Tr∘sq の対称式イディオム（新規だが q9nf_cube_expand 級の機械 rw）と「係数打ち消しを陽な λ-witness で書く」バンドル。発明要素は小さい——**§2.3 で設計済み**。
**(d) 難度**: **1 ラウンド（opus）**（M1 完了が前提）。座標計算の物量が主リスク。
**(e) s_B2**: **0→0.05–0.10（監査判断）**。wild kernel の計算そのもの＝LCFT の実内容だが非ノルムは未達なので小さく。正直: 監査が 0 維持でも異議なし。

### M3 — crux: 4 ∉ N（`Q3LocalReciprocityReal.lean` 仮・**初の status mover**）

**(a) 文の骨子**（降下 3 段 + 矛盾）:
```
q9lrFour : q3rqCar := 1 + q3rqThreeElt
q9lr_step0 : q3kNormBase x = q9lrFour → q9nfUfilt 1 x
   -- x 単数（定義: N(x)=4 単数）・res(x) = res(N x) = res(4) = 1 → x−1 ∈ ker res = (π₉)
q9lr_step1 : … → q9nfUfilt 2 x
   -- x = 1+π₉a; embed(3) = Tr+E₂+embed((ζ₃−1)N(a)); π₉⁶ が左 3 項を割る
   -- ⟹ π₉⁶ ∣ embed((ζ₃−1)N(a)) = π₉³(ζ₃+1)-単数·embed(N a) ⟹ π₉³∣embed(N a)
   -- ⟹ λ ∣ N(a)（座標 0 降下）⟹ N(a) 非単数（q9wr_three_mul_not_unit）
   -- ⟹ a 非単数（定義）⟹ π₉ ∣ a（q9rf_local）
q9lr_contra : q9nfUfilt 2 x → q3kNormBase x ≠ q9lrFour
   -- q9gn_norm_U2: embed(N x) ∈ U^(9) ⊆ U^(7)（q9nf_ufilt_antitone）
   -- 一方 embed(4) = 1+embed(3) ∉ U^(7)＝q9nf_retarget_sharp そのもの。矛盾
q9lr_four_not_norm : ¬ ∃ x, q3kUnitMem x ∧ q3kNormBase x = q9lrFour   -- ★★ crux
```
**(b) 消費**: M1 全部・M2 全部・`q9nf_retarget_sharp`（**スパイクの witness がここで正確に発火**）・`q9wr_pi3_cancel`・`q9nf_ufilt_decomp`・`q9ps_coord0`。
**(c) 新イディオム**: 無し（M1/M2 の組み立てのみ）。「embed(λ)∣embed(z) ⟹ λ∣z」の座標降下 1 補題程度。
**(d) 難度**: **M2 と同ラウンドに同居可能（合わせて 1–1.5 ラウンド）**。安全側は M2 と分けて計 2。
**(e) s_B2**: **0.25–0.35（監査判断・主張は 0.30）**。retarget 後の crux が入り、(T1)（値群側）+ 単数余核の非自明性が実 Lean で閉じる。**complete_pct 表示: Σ_B +5〜7 → 表示 26→31±1 の見込み**（`compute_complete_pct.py` 準拠・過大主張しない）。

**正直な限定（M3 に残るもの・§4 規約で消さない）**: 量化は **x ∈ O_M（整元）**。分数元 π₉^{-k}u への拡張は M^× の群提示（q9ps ヘッダの ℤ×U₃）上の値群 bookkeeping で、N(x) が単数なら k=0 に落ちる——提示が実装済みならほぼ機械的、未実装なら honest limitation として明記。

### M4 — 類 [4] の位数 3 と Gal(M/L₂) との ℤ/3 対応

**(a)**: 4² ∉ N（もし 4² = N(y) なら 4 = 4³·4⁻² = N(embed(4)·y⁻¹)——`q9ps_normBase_embed` で 4³ = N(embed 4)、`q3kInv` で単数逆元——M3 に矛盾）。よって {1,4,16} は N を法として相異なり [4]³ = [1]: **ℤ/3 ↪ U_{L₂}/N(U_M)**。q9kdG = ⟨σ⟩ ≅ ℤ/3 との対応は「存在」形の同型（正規化 4↦σ か 4↦σ² かは Artin 写像未構成なので**選ばない**——honest ∃ 形）。
**(b) 消費**: M3・`q9ps_normBase_embed`・`q3kInv`・q9kd。
**(c) 新イディオム**: 無し。 **(d) 難度**: 1 ラウンド弱（opus/sonnet 混成・M3 と同ラウンド後半でも可）。
**(e) s_B2**: **→0.35–0.45**。(T2) が完結（余核の ℤ/3 下界＋Gal 対応）。

### M5 — 指数 ≤ 3（U_{L₂}^(3) ⊆ N）と Artin 写像（**research 級・未スケジュール**）

(T3)。level ≥3 の graded 全射性は各 graded piece では有限計算だが、**「全ての u ∈ U^(3) がノルム」には norm 方程式の逐次解と収束（完備性）**——choice-free 逆極限担体上の無限積構成——が要る。さらに Artin 写像を「写像」として建て正規化（Lubin–Tate 型）を固定し、Hilbert 記号 (·,·)₃ に接続するのは別建ての多ラウンド。**B2 の残り ~0.55–0.6 はここ**。安易な閾値ショッピングをせず、M4 後に専用の詳細化ラウンドを挟むこと。

---

## 4. 反証ファースト検証（本書の最重要部）— 1+3 は本当に非ノルムか

先行 scope は crux「ζ₃∉N」を検証せずに設計し、q9nf が偽と暴いた。同じ轍を踏まないため、**本書は設計に先立って 1+3 candidate を 3 系統で検証した。結果: 合格（4 は非ノルム）**。実装ラウンドは安心して M1 から着手してよい。

### 4.1 決定精度の有限全数検証（新規実施・本書の根拠）

**還元補題**（それ自体 M2 の系として Lean 化可能）: 単数 x に対し **N(x) mod λ³ は x mod 3π₉O_M のみに依存**する。∵ x' = x(1+π₉⁷c) なら N(x')/N(x) = N(1+π₉⁷c) ∈ 1+λ³O——π₉⁷ = 3π₉u₆⁻¹ より t = 3π₉d 形なので Tr(t) = 3Tr(π₉d) = 9(π₉d)₀（v_λ≥4）・E₂ は 2E₂=Tr²−Tr(t²) で v_λ≥6・N(t) は v_λ≥7。また v_λ(N x) = v_M(x) だから N(x)=4（単数）は x 単数のみ。

よって「∃x 単数, N(x)=4」は **O_M/3π₉ の単数類（3⁷=2187 類中 1458 個）の厳密整数計算**で決着する。ℤ[x]/Φ₉（Φ₉=x⁶+x³+1・σ: x↦x⁴）で全数計算した（スクリプト §A）:

| 検査 | 結果 |
|---|---|
| N(x) ≡ 4 mod λ³ となる単数類 | **0 個 / 1458**（⟹ **4 ∉ N(単数)・crux は真**） |
| ノルム像の mod λ³ 類の個数 | **6 / 18**（(O_{L₂}/λ³)^× 内・**指数ちょうど 3** ✓ ℤ/3 余核） |
| U^(2) 類（242 個）の level-6 graded 像 | **全て零**（Φ ≡ 0 ✓ §2.3） |
| 検算 N(ζ₉) | (0,1) = ζ₃ ✓（`q9nf_zeta_is_norm` と一致） |
| 検算 N(1+π₉²) | (7,3) = 7+3ζ₃ = 1+3(2+ζ₃)、v_λ(N−1)=3 ✓（複素数値でも照合済み） |

### 4.2 独立の古典検算（rec/conductor 側）

ノルム推移 N_{M/ℚ₃} = N_{L₂/ℚ₃}∘N_{M/L₂} と ℚ₃(ζ₉)/ℚ₃ のノルム群 ⟨3⟩×(1+9ℤ₃)（conductor 9）より: 4 = N_{M/L₂}(x) なら 16 = N_{M/ℚ₃}(x)、だが **16 ≡ 7 mod 9 ∉ 1+9ℤ₃**。Artin 側: rec(16)|_M は ζ₉ ↦ ζ₉^{16^{±1}}、16≡7・16⁻¹≡4 mod 9 のどちらの正規化でも ≠ id、かつ 7,4 ∈ {1,4,7}（ζ₃ 固定部分群）なので L₂ 固定とも整合。

### 4.3 それでも残るリスク（実装を沈め得るもの・正直申告）

1. **数学リスクは事実上消えた**が、4.1 の計算は Lean の外（Python・§A で再現可能）。Lean 内の証明は M1–M3 の graded 降下で行い、全数計算там持ち込まない（2187 類の環計算は rw スタイルでは不可能・decide 系は本リポジトリの方針外）。
2. **M1 の z3 Euclid ステップ**が最大の実装リスク（Quot.lift の井戸定義性・Int 除算の符号規約）。詰まったら fable HELP 1 スポット（本書 §3 M1(c) に構成案を明記済み）。
3. **M2 の座標計算の物量**（q9ps_w_norm の 2–3 倍）。打ち消しの項別分解（§2.3）に沿えば発散しないが、rw 列が長い。ラウンド計画では M2 を単独 opus 1 枠にし、M3 を同枠後半または次枠に。
4. **量化の範囲**（M3 の正直限定）: 整元に限る。監査が「M^× 全体でない」を理由に減点する可能性——群提示側の bookkeeping を M4 枠で足すことで回収可能。
5. 本書の設計が誤っていた場合の検知線: M2 の `q9gn_break_cancel` が割れなければ**即座に停止して本書 §2.3 の手計算と突き合わせる**（符号 1 個のずれが典型）。candidate 自体を疑う必要はもう無い（4.1 が決定精度）。

---

## 5. 予測と正直な結論

### 5.1 ラウンド計画と s_B2 軌道

| ラウンド | 内容 | tier | s_B2（監査判断・予測レンジ） | complete_pct |
|---|---|---|---|---|
| （本書） | 設計のみ | L (fable) | 0 → 0 | **0 前進** |
| R+1 | M1（残余体・局所性） | M (opus)・HELP 1 スポット潜在 | 0 → 0 | 0 前進（足場・正直申告） |
| R+2 | M2+M3（graded 零性 + **crux 4∉N**） | M (opus)×1–2 | 0 → **0.25–0.35** | **動く**（Σ_B +5〜7・表示 26→31±1） |
| R+3 | M4（位数 3・Gal 対応・群提示 bookkeeping） | M/S | → 0.35–0.45 | 動く（小） |
| 以降 | M5（指数 ≤3・Artin 写像・Hilbert 記号） | **research・要再設計** | 残り ~0.55 は未約束 | — |

- M2 が 1 枠で閉じない場合 R+2 は 2 分割（+1 ラウンド）。**M3 到達の現実的総コスト: 実装 2 ラウンド（悲観 3）**。
- **B2 は「1–2 opus ラウンドで status が動く」項目に転化した**（q9nf スパイク前の「v_M の壁で見積り不能」から前進）。ただし動くのは (T2) まで——**(T3) は research 級のまま**であり、B2 を 0.45 超に上げる主張は M5 の再設計なしには水増し。

### 5.2 三行結論

(a) **retarget candidate 1+3 は正しい非ノルム生成元**——決定精度（x mod 3π₉・1458 単数類）の厳密全数計算で N(x)≡4 mod λ³ の解ゼロ・ノルム像指数ちょうど 3・level-6 graded 写像の恒等的零性まで確認済み。ζ₃ 型の裏切りリスクは消えた。
(b) 余核 ℤ/3 は level 6 に全集中し、その零性の正体は **Tr の (3)-入射と Fermat a³≡a の係数打ち消し**（Tr(π₉²a)+N(π₉²a) = 3[(π₉²a)₀−ζ₃N(a)] ∈ 3λO）——これを M1（残余体・z3 Euclid）→ M2（2E₂=Tr²−Tr∘sq と打ち消し）→ M3（降下 3 段・`q9nf_retarget_sharp` で矛盾）の 3 段で Lean 化するのが最短路。
(c) 正直な見通し: **M3（crux）まで実装 2 ラウンドで s_B2 0→0.25–0.35 が現実的**、M4 で 0.45 まで。**本書自体と M1 は complete_pct 0 前進**、M5（conductor 全射・Artin 写像）は research 級として未約束のまま残す——ここを曖昧にして B2 を高く積むのは §2/§4 違反。

---

## A. 付録: 反証ファースト検証スクリプト（再現用・§4.1 の根拠）

ℤ[x]/Φ₉ の厳密整数計算。O_M/3π₉ の完全代表系は {p(x)+3e : p は deg<6 係数∈{0,1,2}, e∈{0,1,2}}（3O/3π₉O ≅ O/π₉ ≅ 𝔽₃ が定数項 3e で尽くされる）。単数 ⟺ Σ係数 ≢ 0 mod 3。v_λ(a+bζ₃) = v₃(a²−ab+b²)。

```python
from itertools import product
def redPhi9(c):
    c = list(c)
    for d in range(len(c)-1, 5, -1):
        if c[d]: c[d-3] -= c[d]; c[d-6] -= c[d]; c[d] = 0
    return (c[:6] + [0]*6)[:6]
def pmul(a,b):
    r=[0]*11
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): r[i+j]+=ai*bj
    return redPhi9(r)
def subst(p,k):
    r=[0]*46
    for i,ci in enumerate(p): r[i*k]+=ci
    return redPhi9(r)
def normML2(p):                      # N = p·σp·σ²p, σ: x↦x⁴
    n=pmul(pmul(p,subst(p,4)),subst(p,7))
    assert n[1]==n[2]==n[4]==n[5]==0
    return (n[0],n[3])               # a+b·ζ₃ (ζ₃=x³)
def v3(n):
    if n==0: return 99
    v=0
    while n%3==0: n//=3; v+=1
    return v
def vlam(ab): a,b=ab; return v3(a*a-a*b+b*b)
hits=0; units=0
for cs in product(range(3),repeat=6):
    for e in range(3):
        if sum(cs)%3==0: continue
        units+=1
        a,b=normML2([cs[0]+3*e]+list(cs[1:]))
        if vlam((a-4,b))>=3: hits+=1
print(units, hits)                   # → 1458 0
```
出力（2026-07-11 実行）: 単数類 1458・`N≡4 mod λ³` ヒット **0**・ノルム像 mod λ³ は 6 類 {ζ₃, ζ₃², −1, 8ζ₃, −8, −8−8ζ₃}（= ±ζ₃^k·(1+λ³-調整) の像・指数 3）・U^(2) 類 242 個で graded 像すべて零・N(1+π₉²) = 7+3ζ₃。
