# 独立再監査 A3 — ℚ(ζ₃)/ℚ の gefNF 体化 + Gal 完全決定（cnf / cg3）

日付: 2026-07-09 ／ 監査者: 独立・敵対的（opus・親の自己申告非共有・実 Lean 定義のみ）
対象柱: **A3**（実絶対 Galois 群 G_K = 有限 Galois 群の逆極限）weight 12
契機: 新規 `IUT/CyclotomicField3.lean`（cnf）・`IUT/CyclotomicGal3.lean`（cg3）
の本物性再評定。設計予測（`audit/A3-cyclotomic-tower-detail-2026-07-09.md` §4）は
W-A で A3 0.5→0.52–0.55（小幅・丸めで据え置きの可能性明記）。

## 判定（結論先出し）

**A3 status 0.5 → 0.55**（中間値・`_status_scale` の「0.5 の忠実な部分ケースを
質的に超えるが満点未達」に該当）。**ただし柱 A の complete_pct は 37 で据え置き**
（raw 36.8→37.4・round は 37 のまま。38 になるのは A3 ≥ 0.58 のとき）。
status は上げるが柱%は丸めで動かない、を正直に反映する。

根拠の核心: **コード全体で初めて非自明有限体拡大 ℚ ⊂ ℚ(ζ₃)（base = 実 ℚ・
trivialExtension ではない）が構成され、その Gal が位数ちょうど 2 と完全決定
（∀ σ は id か σ₁・仮説 0 本）された。** これは従来の柱 A の名指し欠落
「非自明有限体拡大が 1 つも構成されておらず全 Galois 塔が trivialExtension 詰め」
の**初 discharge**。だが A3 の本丸（無限塔・制限準同型 res・逆極限 G_K）は
**完全に未構成**（2 段目 ℚ(ζ₉) すら未達）ゆえ 0.6 には届かず、0.55 が上限。

## 自走検証（自分の手で実行）

- `export PATH="/root/lean4/bin:$PATH"; bash build.sh` を**フル実行**。
  **EXIT=0**・`OK: all theorems verified, no sorry.`
- 全 A3 対象の `#print axioms` を目視: 以下すべて **`[propext, Quot.sound]`**
  （新規 Classical.choice 混入なし）:
  `cnfPhi3Field` / `cnfExt3` / `gefNFConst_inj` / `cg3_galois_order_two` /
  `cg3ConjFun_mul` / `cg3_root_dichotomy` / `cg3_aut_ext`。
  併せて依存足場 `gefNFIUTField` / `gefNF268` / `gefFieldExtension` /
  `prc_roots_le_degree` / `pfdRed_of_bounded` / `pum_val_add_*` / `p9e_shift_*`
  も全て `[propext, Quot.sound]`。ビルドログ中の Classical.choice 出現は
  すべて A3 と無関係の既存モジュール（theta_labels・gsets・GaloisTower 等）で、
  A3 対象には一切かからない。

## 各項の本物性判定

### 1. `cg3_galois_order_two` は本物・非空虚か → **本物**

- 主張形は `∃ g, g ≠ one ∧ ∀ h, h = one ∨ h = g`。∀ h は
  `(galoisGroupGrp cnfExt3).carrier`＝**ℚ を各点固定する全 FieldAut** を走る
  真の全射（完全列挙）で、仮説で範囲を絞っていない。
- g = ⟨cg3Conj, cg3Conj_mem⟩ ≠ one: `cg3Conj_ne_id` は縮退でなく
  `cg3Conj(α)=β`・β.val 1 = −1・α.val 1 = 1 に落ち、最終的に
  `cg3q_neg_one_ne_one`（代表交差積 (−1)·1 = 1·1 に `quot_exact_rat`+`omega`）
  という**実事実 −1 ≠ 1**へ帰着。空虚でない。
- 全射性は本物: `cg3_sigma_alpha_root`（σ(α) は Φ₃ の根＝σ(Φ₃(α))=σ(0)=0 を
  map_add/map_mul/map_one/map_zero で展開）→ `cg3_root_dichotomy`（根は α か β
  ——R1 `prc_roots_le_degree` を **実適用**し [r,α,β] の 3 相異根で 3 ≤ 2 の矛盾）
  → `cg3_aut_ext`（σ,τ が α で一致⟹全点一致・`cg3_decompose` で
  y = ι(y₀)+ι(y₁)·α に分解し map_add/map_mul + ℚ 各点固定で確定、invFun も
  left/right_inv で確定）。仮説で誤魔化していない。
- R1 の非退化前提 `cg3PhiTop 2 ≠ 0`（K₁ 内で 1_K ≠ 0）は `gnf_zero_ne_one`
  で本物に供給。

### 2. `cg3Conj` は本物の体自己同型か → **本物**

- `FieldAut` は明示 invFun 付きの全単射環準同型（map_add/map_mul/map_one/
  left_inv/right_inv）。cg3Conj は invFun = 自身（対合 `cg3ConjFun_invol`）で
  left_inv=right_inv を充足。map_add は成分線形で本物。
- **map_mul（山場）は fudge していない**: `cg3ConjFun_mul` は係数公式
  `cg3_mul_val0/1` と QRat 恒等 `cg3q_conj0/1` で閉じる。係数公式
  `cg3_mul_coeffs` は `pfdRed_char`（剰余の一意特徴付け＝`field_division_unique`
  に帰着）を使い、簡約差 w−v の witness を **h = psC(a₁·b₁)**（＝先頭係数積 × Φ₃）
  と明示して x̄² ≡ −1−x̄ を**本物に実現**。剰余簡約越しの環準同型性が実証されている。
- `cg3Conj_mem`（ℚ 各点固定）: `cnfExt3.incl k` の 1 次係数が 0 なので
  σ₁ が定数を動かさない、を係数計算で証明。Gal(ℚ(ζ₃)/ℚ) の元であることが本物。

### 3. cnf は本物の非自明有限体拡大か → **本物**

- `cnfPhi3Field = gefNFIUTField cq0PS 2 …`＝実 ℚ 上の Φ₃=x²+x+1 による
  2 次商体（F6 の全域 inv 付き実体エンジンの実例化）。入力は全て実在資産
  （`cq0_bound`/`cq0_lead`/`cqi_irreducible`）で honest 仮説 0 本。
- `cnfExt3 = gefFieldExtension …`: **base = ratIUTField（実 ℚ）**・
  top = 上記 2 次体・incl = 定数埋め込み `gefIncl`。incl_mul は psConstHom +
  `pfdRed_of_bounded` で本物に証明。**trivialExtension 詰めではない**（base ≠ top・
  incl は恒等でない定数埋め込み）。
- `gefNFConst_inj`（定数埋め込みの単射性）も 0 次係数読み出しで本物。

### 4. 正直な限定の妥当性 → **妥当・過大主張なし**

ヘッダ記載の限定 (i) p=3・ℚ・1 段のみ、(ii) res 未構成・全射性/分離性/正規性の
一般論未形式化、(iii) K₁ は既存 cq3Field/qdfField(−3)/gfiCq3Field と同型な第4担体
（同型輸送は対象外）——**すべて正しい**。特に監査者が独立確認した事実:
- **塔・res・逆極限 G_K は本当に無い**: `cnfPhi9Field`/`cnfExt9`/`cr39Res`/
  `ProfinitePi1Tower` への差し込みは grep で不在。制限準同型 Hom も未構成。
- A3 の本丸（無限塔＋制限準同型＋逆極限プロファイナイト群）には**まだ遠い**。
  今回入ったのは逆極限の**構成部品を 1 個**（単一有限 Gal）だけ、しかも塔構造なし。

### 5. pum / p9e は Φ_9 既約性の土台のみ → **確認・A3 を今は動かさない**

- `PadicUltrametricQ.lean`（p 進超距離 `pum_val_add_ge_min`/`pum_val_add_eq`）・
  `Phi9Shift.lean`（Φ_9 シフト像 `p9e_shift_eq`・次数保存 `p9e_shift_lead`・
  先頭係数 `p9e_phi9_lead`）は実在・ビルド通過。
- しかし `eis_irreducible`（Eisenstein 判定器）・`p9e_irreducible`
  （Φ_9 既約性）・`cnfPhi9Field`（ℚ(ζ₉)）は**いずれも不在**。2 段目は未達。
- Phi9Shift.lean 自身のヘッダが「承認済み足場(c)・本ファイル単体では
  complete_pct 0 前進」と正直申告。これらは A3 を今は動かさない足場。

## 本物性の核心判定

「非自明有限体拡大が 1 つも構成されていない・全 Galois 塔が trivialExtension 詰め」
という従来の A 柱の欠落に対し、**ℚ(ζ₃)/ℚ という実 2 次拡大＋その Gal の完全決定
（位数ちょうど 2・∀ 自己同型の列挙・仮説 0）が初めて本物で入った**。これは
- スケールする担体（gefNF・ζ_9/一般 n に拡張可能）上で行われ、
- 既存 `qdf_galois_order_two`（ℚ×ℚ 直積担体・2 次固定）の再演でなく、
  剰余簡約越しの環準同型性（map_mul）と根の二分法（R1 初適用）を初めて閉じた、
本物の質的前進。

**だが** A3 の定義（G_K = 有限 Galois 群の**逆極限**）の本丸構造——無限塔・
制限準同型・逆極限——は完全に未着手で、2 段目すら未構成。ゆえに満点にも 0.6
にも届かない。

## complete_pct への反映と丸めの扱い

- 台帳 A3 status 0.5 → **0.55**（`_status_scale` 中間値・質的超過だが満点未達）。
- `tools/compute_complete_pct.py`: 柱 A raw = 36.8 → 37.4。**round = 37 で据え置き**
  （38 になるのは A3 ≥ 0.58 のとき。0.55 では丸め上動かない）。
- graph-meta `pillars.A.complete_pct` は **37 のまま**（ledger 由来 round 値と厳密一致）。
  `progress_pct`（骨格被覆率 99）不変。`complete_note` は
  「非自明有限体拡大の初 discharge・Gal 完全決定・ただし塔/res/逆極限は未」に更新。
- **正直な結論**: status は 0.5→0.55 に上げるが、柱 A の headline % は 37 で不動。
  これは水増しでも過小でもなく、丸めの正直な扱い。

## 残る限定（A3 が 0.55 で止まる理由）

1. 単一有限 Gal のみ。塔（連鎖する非自明拡大）が無い。
2. 制限準同型 res が未構成（`ProfinitePi1Tower.restr` witness 未 discharge）。
3. 逆極限 G_K が無い（プロファイナイト群としての実現ゼロ）。
4. 2 段目 ℚ(ζ₉) 未構成（Φ_9 既約性 = Eisenstein 判定器が未完）。
5. 全射性/分離性/正規性の一般論・一般 n の (ℤ/3ⁿ)^× 同型は未形式化。
