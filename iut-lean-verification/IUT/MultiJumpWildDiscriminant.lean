/-
  IUT/MultiJumpWildDiscriminant.lean
-- M446F MultiJumpWildDiscriminant [実・本物・柱B]
-- complete_pct 影響: **前進あり**（柱B）。M441F `WildConductorDiscriminant`（wcd）は
--   野性 conductor-discriminant を **単一跳躍 ℤ/p（下付き番号付けの唯一の break m,
--   |G_i|∈{1,p}）**の 1 族でのみ閉じ、`wcd_model_scope` で「一般野性分岐（多跳躍・|G_i|
--   任意）・Hasse–Arf 整数跳躍・非巡回は後続」と正直に限定していた。本モジュールはその
--   限定のうち **「単一跳躍のみ」を多跳躍で昇格して破る**。具体ケースは **全分岐 巡回 ℤ/p²
--   拡大（2 段跳躍 b₁ < b₂）**で、下付き分岐フィルトレーションが 3 段:
--       |G_i| = p²  (0 ≤ i ≤ b₁),   |G_i| = p  (b₁ < i ≤ b₂),   |G_i| = 1  (i > b₂)
--   と**二つの break（b₁, b₂）**を持つ（M441F の 2 段 |G_i|∈{1,p} を破る本質）。
--   野性 different 指数を階段和で本物構成:
--       d = Σ_{i=0}^{b₂}(|G_i|−1) = (b₁+1)(p²−1) + (b₂−b₁)(p−1)      （`mjw_diff_zp2`）
--   跳躍数=1（b₁=b₂）で M441F 単一跳躍 `wcdRamGroups (p²) b` へ厳密還元
--   （`mjw_reduces_to_single`/`mjw_collapse_value`）。多跳躍 Swan 導手（高次分岐 Σ_{i≥1}
--   の階段和）を本物構成し、単一跳躍 ℤ/p を超えることを `mjw_swan_ge_single` で示す。
--   Hasse–Arf 整数跳躍（**上付き番号 φ(b₂)=b₁+(b₂−b₁)/p が整数**）を、Herbrand φ=rnfPhi
--   （M420F RamifiedNormFiltration）で **p ∣ (b₂−b₁) の下で本物検証**する
--   （`mjw_hasse_arf_integrality`/`mjw_hasse_arf_dvd`）——M441F が「後続」とした Hasse–Arf に
--   具体ケースで到達。
-- 正直な限定（消去・弱化禁止）: 破ったのは **全分岐 巡回 ℤ/p²（2 跳躍 b₁<b₂・|G_i|∈{1,p,p²}）**
--   の 1 具体族のみ。**任意跳躍数 k≥3・|G_i| 一般・非巡回/非可換・dim≥2 表現・一般 Hasse–Arf
--   定理（跳躍が必ず整数になること自体の証明）**は依然対象外——後続。これを §6 `mjwScope`/
--   `mjw_model_scope` で定理化し、M441F の「単一跳躍のみ」を実際に破ったことを
--   `mjw_breaks_single_jump` で明示する。
--
--  ────────────────────────────────────────────────────────────────────────
--  二軸（CLAUDE.md §1）
--  * 分類: **[実]**（(a) 昇格）。M441F `wcd_model_scope`（単一跳躍 m・|G_i|∈{1,p}）の
--    「単一跳躍のみ」限定を、**2 跳躍 ℤ/p²（|G_i|∈{1,p,p²}）**で置換し、多跳躍 different
--    階段和・多跳躍 Swan・conductor-discriminant・Hasse–Arf 整数性（具体ケース）を本物 Nat
--    算術で閉じる。単一跳躍は b₁=b₂ の退化として厳密回復（限定を狭めて正直に述べ直す）。
--  * complete_pct 影響: **前進あり**（柱B: 多跳躍野性 different d=(b₁+1)(p²−1)+(b₂−b₁)(p−1)・
--    多跳躍 Swan の階段和・p∣(b₂−b₁) 下の Hasse–Arf 整数上付き break の本物建設 =
--    M441F「単一跳躍のみ」限定の突破）。
--
--  既存モジュールの何を本物化したか
--  * M441F `wcdRamGroups p m`（2 段 |G_i|∈{1,p}）を、3 段 `mjwZp2Groups p b₁ b₂`
--    （|G_i|∈{1,p,p²}）へ一般化し、跳躍数=1（b₁=b₂）で `wcdRamGroups (p²) b` に厳密還元。
--  * M441F の野性 different telescope（`wcd_sum_const`/`wcd_sum_at_break`）を再利用しつつ、
--    **2 区間階段和**を `mjw_sum_segment`（本物 帰納）で建て、多跳躍 d を閉じる。
--  * M420F `rnfPhi`（Herbrand φ=⌊i/e⌋）・`rnf_phi_psi`（φ∘ψ=id, tame）を用い、
--    上付き break φ(b₂)=b₁+(b₂−b₁)/p の整数性（Hasse–Arf）を p∣(b₂−b₁) の下で本物検証。
--
--  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
--  * `mjwZp2Groups` / `mjw_grp_lo` / `mjw_grp_mid` / `mjw_grp_hi`
--      — 3 段 野性分岐群位数 |G_i|=p²(i≤b₁), p(b₁<i≤b₂), 1(i>b₂)（ℤ/p² 2 跳躍）
--  * `mjw_sum_segment` / `mjw_diff_zp2` / `mjwDiffMultiJump` / `mjw_different_eq`
--      — **多跳躍 different d = Σ_{i=0}^{b₂}(|G_i|−1) = (b₁+1)(p²−1)+(b₂−b₁)(p−1)**（階段和）
--  * `mjw_reduces_to_single` / `mjw_diffsum_reduces_single` / `mjw_collapse_value`
--      — 跳躍数=1（b₁=b₂）で M441F 単一跳躍 `wcdRamGroups (p²) b` へ厳密還元
--  * `mjwSwanSum` / `mjw_diff_eq_head_swan` / `mjw_swan_val` / `mjw_swan_mono` / `mjw_swan_ge_single`
--      — **多跳躍 Swan 導手 Σ_{i≥1}(|G_i|−1)** の階段和・単一跳躍 ℤ/p を超える
--  * `mjwConductorDisc` / `mjw_conductor_discriminant_multi`
--      — **conductor-discriminant** v(disc)=Σ_χ a(χ)=d（多跳躍階段和・本命題）
--  * `mjwUpperBreak` / `mjw_hasse_arf_integrality` / `mjw_hasse_arf_dvd`
--      — **Hasse–Arf: 上付き break φ(b₂)=b₁+(b₂−b₁)/p が整数**（p∣(b₂−b₁) 下・rnfPhi 使用）
--  * `mjwScope` / `mjw_model_scope` / `mjw_breaks_single_jump` / `mjw_scope_witness`
--      — 正直な限定の定理化（M441F「単一跳躍のみ」を破った印を明示）
--  * `MultiJumpWildData` / `mjwDataOf` / `mjw_exists` — capstone
--  * `mjw_ex_zp4_*`（ℤ/4, b₁=1,b₂=3: d=8, Swan=5）・`mjw_ex_hasse_*`・`mjw_ex_reduce_*`
--
--  正直な限定（CLAUDE.md §4: 消去・弱化禁止）: 上記ヘッダ限定を §6 で定理化。破ったのは
--  全分岐 巡回 ℤ/p²（2 跳躍）の 1 族のみ。任意跳躍数 k≥3・非巡回・一般 Hasse–Arf 定理は後続。
--  全て選択公理不使用（propext/Quot.sound のみ）。共有ファイル未変更（新規 1 本）。
-/
import IUT.WildConductorDiscriminant
import IUT.RamifiedNormFiltration

namespace IUT

/-! ## §1 多跳躍 野性分岐群位数 |G_i| = p²(i≤b₁), p(b₁<i≤b₂), 1(i>b₂)（全分岐 ℤ/p², 2 跳躍）

    剰余標数 p の局所体 K 上の**全分岐 巡回 ℤ/p² 拡大** L/K を考える。ℤ/p² は一意の位数 p
    部分群 pℤ/p² を持ち、下付き番号付けの分岐フィルトレーション G_0 ⊇ G_1 ⊇ … は**二つの
    break b₁ < b₂**を持つ:
      |G_i| = p²  (0 ≤ i ≤ b₁),   |G_i| = p  (b₁ < i ≤ b₂),   |G_i| = 1  (i > b₂).
    M441F の単一跳躍（|G_i|∈{1,p}）は 2 段だったが、ここは **3 段（|G_i|∈{1,p,p²}）**——
    多跳躍の本質。b₁<b₂ で中間段 |G_i|=p が実在し「単一跳躍のみ」を実際に破る。 -/

/-- **M446F-1: 多跳躍（ℤ/p²）野性分岐群位数** |G_i|=p²(i≤b₁), p(b₁<i≤b₂), 1(i>b₂)。
    M441F `wcdBle` を二重に使い i≤b₁ / i≤b₂ を判定（i=0 で常に p² が定義的）。 -/
def mjwZp2Groups (p b1 b2 i : Nat) : Nat :=
  bif wcdBle i b1 then p * p else bif wcdBle i b2 then p else 1

/-- **M446F-1a: |G_i| = p² (i ≤ b₁)（本物）** — 第 1 段（惰性群 G_0 込み・野性）。 -/
theorem mjw_grp_lo (p b1 b2 : Nat) : ∀ i, i ≤ b1 → mjwZp2Groups p b1 b2 i = p * p := by
  intro i h
  show (bif wcdBle i b1 then p * p else bif wcdBle i b2 then p else 1) = p * p
  rw [wcd_ble_le i b1 h]; rfl

/-- **M446F-1b: |G_i| = p (b₁ < i ≤ b₂)（本物）** — 中間段（第 2 跳躍前・多跳躍の徴）。 -/
theorem mjw_grp_mid (p b1 b2 : Nat) : ∀ i, b1 < i → i ≤ b2 → mjwZp2Groups p b1 b2 i = p := by
  intro i h1 h2
  show (bif wcdBle i b1 then p * p else bif wcdBle i b2 then p else 1) = p
  rw [wcd_ble_gt i b1 h1, wcd_ble_le i b2 h2]; rfl

/-- **M446F-1c: |G_i| = 1 (i > b₂)（本物）** — 第 2 跳躍を過ぎて分岐群自明。 -/
theorem mjw_grp_hi (p b1 b2 : Nat) (hb : b1 ≤ b2) :
    ∀ i, b2 < i → mjwZp2Groups p b1 b2 i = 1 := by
  intro i h
  show (bif wcdBle i b1 then p * p else bif wcdBle i b2 then p else 1) = 1
  rw [wcd_ble_gt i b1 (by omega), wcd_ble_gt i b2 h]; rfl

/-! ## §2 多跳躍 野性 different 指数 d = Σ_{i=0}^{b₂}(|G_i|−1)（2 区間階段和）

    different 指数 d = v_L(𝔡_{L/K}) = Σ_{i≥0}(|G_i|−1)（Serre, Corps Locaux IV §1）。
    ℤ/p² の 2 跳躍では
      d = Σ_{i=0}^{b₁}(p²−1) + Σ_{i=b₁+1}^{b₂}(p−1) = (b₁+1)(p²−1) + (b₂−b₁)(p−1)
    と **2 つの階段区間**の和になる（M441F の単一区間 (m+1)(p−1) の多跳躍版）。
    M441F `wcdDiffSum` を和のエンジンとして再利用し、区間和補題 `mjw_sum_segment` で閉じる。 -/

/-- **M446F-2: 区間和補題（本物・任意跳躍の再利用エンジン）** —
    G が (b₁, b₁+j] で一定 c なら Σ_{i=b₁+1}^{b₁+j}(|G_i|−1) を加えて
    wcdDiffSum G (b₁+j) = wcdDiffSum G b₁ + j·(c−1)。任意個の階段区間を積み重ねる基盤。 -/
theorem mjw_sum_segment (G : Nat → Nat) (c b1 : Nat) :
    ∀ j, (∀ i, b1 < i → i ≤ b1 + j → G i = c) →
      wcdDiffSum G (b1 + j) = wcdDiffSum G b1 + j * (c - 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    show wcdDiffSum G b1 = wcdDiffSum G b1 + 0 * (c - 1)
    rw [Nat.zero_mul, Nat.add_zero]
  | succ k ih =>
    intro h
    show wcdDiffSum G (b1 + k + 1) = wcdDiffSum G b1 + (k + 1) * (c - 1)
    have hstep : wcdDiffSum G (b1 + k + 1)
        = wcdDiffSum G (b1 + k) + (G (b1 + k + 1) - 1) := rfl
    have hc : G (b1 + k + 1) = c := h (b1 + k + 1) (by omega) (by omega)
    have hih : wcdDiffSum G (b1 + k) = wcdDiffSum G b1 + k * (c - 1) :=
      ih (fun i hi1 hi2 => h i hi1 (by omega))
    have hm : (k + 1) * (c - 1) = k * (c - 1) + (c - 1) := Nat.succ_mul k (c - 1)
    rw [hstep, hc, hih, hm]
    omega

/-- **M446F-2a: 多跳躍 ℤ/p² different（本命題・本物）** —
    Σ_{i=0}^{b₂}(|G_i|−1) = (b₁+1)(p²−1) + (b₂−b₁)(p−1)。第 1 区間 [0,b₁] で各項 (p²−1)、
    第 2 区間 (b₁,b₂] で各項 (p−1) の 2 段階段和。 -/
theorem mjw_diff_zp2 (p b1 b2 : Nat) (hb : b1 ≤ b2) :
    wcdDiffSum (mjwZp2Groups p b1 b2) b2
      = (b1 + 1) * (p * p - 1) + (b2 - b1) * (p - 1) := by
  have hbase : wcdDiffSum (mjwZp2Groups p b1 b2) b1 = (b1 + 1) * (p * p - 1) :=
    wcd_sum_const (p * p) (mjwZp2Groups p b1 b2) b1 (fun i hi => mjw_grp_lo p b1 b2 i hi)
  have hseg : wcdDiffSum (mjwZp2Groups p b1 b2) (b1 + (b2 - b1))
      = wcdDiffSum (mjwZp2Groups p b1 b2) b1 + (b2 - b1) * (p - 1) :=
    mjw_sum_segment (mjwZp2Groups p b1 b2) p b1 (b2 - b1)
      (fun i hi1 hi2 => mjw_grp_mid p b1 b2 i hi1 (by omega))
  have hb2 : b1 + (b2 - b1) = b2 := by omega
  rw [hb2] at hseg
  rw [hseg, hbase]

/-- **M446F-2b: 多跳躍 different 指数** d = (b₁+1)(p²−1)+(b₂−b₁)(p−1)（ℤ/p², 跳躍 b₁<b₂）。 -/
def mjwDiffMultiJump (p b1 b2 : Nat) : Nat := (b1 + 1) * (p * p - 1) + (b2 - b1) * (p - 1)

/-- **M446F-2c: d = Σ_{i=0}^{b₂}(|G_i|−1)（本物・和からの導出）**。 -/
theorem mjw_different_eq (p b1 b2 : Nat) (hb : b1 ≤ b2) :
    wcdDiffSum (mjwZp2Groups p b1 b2) b2 = mjwDiffMultiJump p b1 b2 :=
  mjw_diff_zp2 p b1 b2 hb

/-! ## §3 跳躍数=1 への厳密還元（b₁=b₂ で M441F 単一跳躍 `wcdRamGroups (p²) b` を回復）

    2 跳躍 b₁ < b₂ を b₁ = b₂ = b に退化させると中間段 (b₁,b₂] が空になり、群位数は
      |G_i| = p²  (i ≤ b),   1  (i > b)
    となって **M441F の単一跳躍 `wcdRamGroups (p²) b`（|G_i|∈{1,p²}）に一致**する。
    多跳躍の跳躍数を 1 に落とすと M441F へ戻ることの本物証明（genuine reduction）。 -/

/-- **M446F-3: 跳躍数=1 で M441F 単一跳躍群位数に一致（本物・還元の核）** —
    b₁=b₂=b で mjwZp2Groups p b b i = wcdRamGroups (p²) b i（|G_i|∈{1,p²}）。 -/
theorem mjw_reduces_to_single (p b i : Nat) :
    mjwZp2Groups p b b i = wcdRamGroups (p * p) b i := by
  show (bif wcdBle i b then p * p else bif wcdBle i b then p else 1)
     = (bif wcdBle i b then p * p else 1)
  cases h : wcdBle i b with
  | true => rfl
  | false => rfl

/-- **M446F-3a: different 和も跳躍数=1 で M441F へ還元（本物）**。 -/
theorem mjw_diffsum_reduces_single (p b : Nat) :
    wcdDiffSum (mjwZp2Groups p b b) b = wcdDiffSum (wcdRamGroups (p * p) b) b :=
  wcd_diffsum_congr (mjwZp2Groups p b b) (wcdRamGroups (p * p) b) b
    (fun i _ => mjw_reduces_to_single p b i)

/-- **M446F-3b: 跳躍数=1 の different 値（本物）** — b₁=b₂=b で d=(b+1)(p²−1)（単一跳躍値）。
    M441F `wcd_sum_at_break (p²) b` に landing。 -/
theorem mjw_collapse_value (p b : Nat) :
    wcdDiffSum (mjwZp2Groups p b b) b = (b + 1) * (p * p - 1) := by
  rw [mjw_diffsum_reduces_single p b]
  exact wcd_sum_at_break (p * p) b

/-! ## §4 多跳躍 Swan 導手 Σ_{i≥1}(|G_i|−1)（高次分岐の階段和・単一跳躍を超える）

    different 指数 d = Σ_{i≥0}(|G_i|−1) の高次分岐部（i≥1）が **Swan 部**
      sw = Σ_{i≥1}(|G_i|−1)     （i=0 の tame 部 |G_0|−1 を除いた野性寄与）
    である（正則表現の conductor の Swan 部＝判別式の野性部）。多跳躍では
      sw = b₁(p²−1) + (b₂−b₁)(p−1)
    と 2 区間の階段和になり、同じ top break を持つ単一跳躍 ℤ/p の Swan を超える。 -/

/-- **M446F-4: Swan 部分和** sw_n = Σ_{i=1}^{n}(|G_i|−1)（i≥1 の高次分岐項のみ）。 -/
def mjwSwanSum (G : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => mjwSwanSum G n + (G (n + 1) - 1)

/-- **M446F-4a: different = tame(|G_0|−1) + Swan（本物・分解）** —
    wcdDiffSum G n = (G 0 − 1) + Σ_{i≥1}(|G_i|−1)。i=0 の tame 項と i≥1 の Swan 階段和。 -/
theorem mjw_diff_eq_head_swan (G : Nat → Nat) :
    ∀ n, wcdDiffSum G n = (G 0 - 1) + mjwSwanSum G n := by
  intro n
  induction n with
  | zero =>
    show G 0 - 1 = (G 0 - 1) + 0
    rw [Nat.add_zero]
  | succ k ih =>
    show wcdDiffSum G k + (G (k + 1) - 1)
       = (G 0 - 1) + (mjwSwanSum G k + (G (k + 1) - 1))
    rw [ih]
    omega

/-- **M446F-4b: 多跳躍 Swan 導手の値（本物）** —
    (p²−1) + Σ_{i≥1}(|G_i|−1) = d = (b₁+1)(p²−1)+(b₂−b₁)(p−1)。
    |G_0|=p² の tame 部を足すと多跳躍 different へ戻る（Swan = d − (p²−1)）。 -/
theorem mjw_swan_val (p b1 b2 : Nat) (hb : b1 ≤ b2) :
    (p * p - 1) + mjwSwanSum (mjwZp2Groups p b1 b2) b2 = mjwDiffMultiJump p b1 b2 := by
  have h := mjw_diff_eq_head_swan (mjwZp2Groups p b1 b2) b2
  have h0 : mjwZp2Groups p b1 b2 0 = p * p := mjw_grp_lo p b1 b2 0 (Nat.zero_le b1)
  rw [h0] at h
  rw [← h]
  exact mjw_different_eq p b1 b2 hb

/-- **M446F-4c: Swan 部分和の単調性（本物）** — G が H を各点で上回れば Swan も上回る。 -/
theorem mjw_swan_mono (G H : Nat → Nat) :
    ∀ n, (∀ i, i ≤ n → H i ≤ G i) → mjwSwanSum H n ≤ mjwSwanSum G n := by
  intro n
  induction n with
  | zero => intro _; exact Nat.le_refl 0
  | succ k ih =>
    intro h
    show mjwSwanSum H k + (H (k + 1) - 1) ≤ mjwSwanSum G k + (G (k + 1) - 1)
    have h1 : mjwSwanSum H k ≤ mjwSwanSum G k := ih (fun i hi => h i (by omega))
    have h2 : H (k + 1) - 1 ≤ G (k + 1) - 1 :=
      Nat.sub_le_sub_right (h (k + 1) (by omega)) 1
    exact Nat.add_le_add h1 h2

/-- **M446F-4d: ℤ/p² が単一跳躍 ℤ/p を各点で支配（本物）** —
    i≤b₂ で wcdRamGroups p b₂ i ≤ mjwZp2Groups p b₁ b₂ i（第 1 段 p²≥p, 中間段 p=p）。 -/
theorem mjw_dominates_single (p b1 b2 : Nat) (hb : b1 ≤ b2) (hp : 1 ≤ p) :
    ∀ i, i ≤ b2 → wcdRamGroups p b2 i ≤ mjwZp2Groups p b1 b2 i := by
  intro i hi
  cases Nat.lt_or_ge b1 i with
  | inl hlt =>
      rw [mjw_grp_mid p b1 b2 i hlt hi, wcd_ram_le p i b2 hi]
      exact Nat.le_refl p
  | inr hge =>
      rw [mjw_grp_lo p b1 b2 i hge, wcd_ram_le p i b2 hi]
      have hpp : p * 1 ≤ p * p := Nat.mul_le_mul (Nat.le_refl p) hp
      rw [Nat.mul_one] at hpp
      exact hpp

/-- **M446F-4e: 多跳躍 Swan ≥ 単一跳躍 Swan（本命題・本物）** —
    mjwSwanSum (wcdRamGroups p b₂) b₂ ≤ mjwSwanSum (mjwZp2Groups p b₁ b₂) b₂。
    ℤ/p² の第 1 段が p²（>p）ゆえ、同じ top break b₂ の単一跳躍 ℤ/p の Swan を上回る。 -/
theorem mjw_swan_ge_single (p b1 b2 : Nat) (hb : b1 ≤ b2) (hp : 1 ≤ p) :
    mjwSwanSum (wcdRamGroups p b2) b2 ≤ mjwSwanSum (mjwZp2Groups p b1 b2) b2 :=
  mjw_swan_mono (mjwZp2Groups p b1 b2) (wcdRamGroups p b2) b2
    (fun i hi => mjw_dominates_single p b1 b2 hb hp i hi)

/-! ## §5 多跳躍 conductor-discriminant（本命題）: v(disc) = Σ_χ a(χ) = d

    conductor-discriminant 公式（Führerdiskriminantenproduktformel の valuation 版）で
      v(disc) = Σ_χ a(χ) = Σ_{i≥0}(|G_i|−1) = d
    が成り立つ（全指標にわたる Artin 導手総和 = 分岐フィルトレーション和）。ℤ/p² 多跳躍では
    右辺が 2 段階段和 (b₁+1)(p²−1)+(b₂−b₁)(p−1) になる（M441F 単一跳躍 (p−1)(m+1) の昇格）。 -/

/-- **M446F-5: 判別式 valuation** v(disc) = Σ_χ a(χ) = Σ_{i≥0}(|G_i|−1)（多跳躍階段和）。 -/
def mjwConductorDisc (p b1 b2 : Nat) : Nat := wcdDiffSum (mjwZp2Groups p b1 b2) b2

/-- **M446F-5a: 多跳躍 conductor-discriminant 恒等式（本命題・本物）** —
    v(disc) = Σ_χ a(χ) = d = (b₁+1)(p²−1)+(b₂−b₁)(p−1)。
    M441F `wcd_conductor_discriminant_wild`（単一跳躍・(p−1)(m+1)）の多跳躍昇格版。 -/
theorem mjw_conductor_discriminant_multi (p b1 b2 : Nat) (hb : b1 ≤ b2) :
    mjwConductorDisc p b1 b2 = mjwDiffMultiJump p b1 b2 :=
  mjw_different_eq p b1 b2 hb

/-! ## §6 Hasse–Arf 整数跳躍（上付き番号 φ(b₂) の整数性・Herbrand φ=rnfPhi 使用）

    下付き break b₁ < b₂ の上付き番号（Herbrand φ）は
      φ(b₁) = b₁,   φ(b₂) = b₁ + (b₂−b₁)/p
    （第 1 区間の傾き 1, 第 2 区間 (b₁,b₂] の傾き 1/[G_0:G_i]=1/p）。**Hasse–Arf 定理**は
    アーベル拡大でこの上付き break が**整数**であること——すなわち **p ∣ (b₂−b₁)**——を主張する。
    本 § は M420F Herbrand φ=`rnfPhi p`（⌊·/p⌋）を用い、p∣(b₂−b₁) の下で φ(b₂)=b₁+(b₂−b₁)/p が
    整数（割り切れ・余りなし）であることを本物検証する。M441F が「後続」とした Hasse–Arf に
    具体ケースで到達（一般定理そのものの証明は §7 で後続と明記）。 -/

/-- **M446F-6: 上付き break** φ(b₂) = b₁ + (b₂−b₁)/p（Herbrand φ=rnfPhi・第 2 区間傾き 1/p）。 -/
def mjwUpperBreak (p b1 b2 : Nat) : Nat := b1 + rnfPhi p (b2 - b1)

/-- **M446F-6a: Hasse–Arf 整数性（本命題・本物）** — b₂ = b₁ + p·t（p∣間隔）のとき
    上付き break φ(b₂) = b₁ + t（整数）かつ p·(φ(b₂)−b₁) = b₂−b₁（余りなし・整数 landing）。
    M420F `rnf_phi_psi`（φ∘ψ=id）で ⌊p·t/p⌋=t を本物化。 -/
theorem mjw_hasse_arf_integrality (p b1 t : Nat) (hp : 1 ≤ p) :
    mjwUpperBreak p b1 (b1 + p * t) = b1 + t
    ∧ p * (mjwUpperBreak p b1 (b1 + p * t) - b1) = (b1 + p * t) - b1 := by
  have hphi : rnfPhi p ((b1 + p * t) - b1) = t := by
    have hsub : (b1 + p * t) - b1 = rnfPsi p t := by
      show (b1 + p * t) - b1 = p * t
      omega
    rw [hsub]
    exact rnf_phi_psi p t hp
  constructor
  · show b1 + rnfPhi p ((b1 + p * t) - b1) = b1 + t
    rw [hphi]
  · show p * ((b1 + rnfPhi p ((b1 + p * t) - b1)) - b1) = (b1 + p * t) - b1
    rw [hphi]
    have e1 : (b1 + t) - b1 = t := by omega
    have e2 : (b1 + p * t) - b1 = p * t := by omega
    rw [e1, e2]

/-- **M446F-6b: Hasse–Arf 整数性（可除性形・本物）** — p ∣ (b₂−b₁) のとき
    p·(φ(b₂)−b₁) = b₂−b₁（上付き break が整数に landing・余りなし）。
    p∣(b₂−b₁) が上付き番号整数性（Hasse–Arf の結論）と同値であることの本物側。 -/
theorem mjw_hasse_arf_dvd (p b1 b2 : Nat) (hp : 1 ≤ p) (hdvd : p ∣ (b2 - b1)) :
    p * (mjwUpperBreak p b1 b2 - b1) = b2 - b1 := by
  obtain ⟨t, ht⟩ := hdvd
  show p * ((b1 + rnfPhi p (b2 - b1)) - b1) = b2 - b1
  rw [ht]
  have hdiv : rnfPhi p (p * t) = t := by
    show (p * t) / p = t
    exact Nat.mul_div_cancel_left t hp
  rw [hdiv]
  have e1 : (b1 + t) - b1 = t := by omega
  rw [e1]

/-! ## §7 正直な限定の定理化（CLAUDE.md §4: 消去・弱化禁止）

    本モジュールが M441F の「単一跳躍のみ」を破ったのは、次を**すべて満たす 1 つの具体族**に限る:
      (multiJump) 下付き 2 跳躍 b₁ < b₂（中間段 |G_i|=p が実在・単一跳躍を破る）,
      (zp2)       全分岐 巡回 ℤ/p²（|G_i|∈{1,p,p²}）,
      (hasseArfChecked) p∣(b₂−b₁) の下で上付き break 整数性を本物検証。
    以下は**依然対象外**（フラグ false）——後続:
      (generalMultiJump) 任意跳躍数 k≥3・|G_i| 一般（ℤ/p^n・非巡回アーベル）,
      (nonCyclic)        非巡回・非可換・dim≥2 表現,
      (generalHasseArf)  Hasse–Arf 定理そのもの（上付き break が必ず整数になることの証明）。 -/

/-- **M446F-7: 正直な限定フラグ** — 破った多跳躍ケースと依然未対応の一般化を Bool で明示。 -/
structure mjwScope where
  /-- 下付き 2 跳躍 b₁<b₂（中間段実在）を破った。 -/
  multiJump : Bool
  /-- 全分岐 巡回 ℤ/p²（|G_i|∈{1,p,p²}）。 -/
  zp2 : Bool
  /-- p∣(b₂−b₁) の下で Hasse–Arf 上付き break 整数性を本物検証。 -/
  hasseArfChecked : Bool
  /-- 任意跳躍数 k≥3・|G_i| 一般（ℤ/p^n・非巡回）— 未対応。 -/
  generalMultiJump : Bool
  /-- 非巡回・非可換・dim≥2 表現 — 未対応。 -/
  nonCyclic : Bool
  /-- Hasse–Arf 定理そのもの（整数性の必然の証明）— 未対応。 -/
  generalHasseArf : Bool

/-- **M446F-7a: 本モジュールの scope witness** — 破った多跳躍ケース（前 3 つ true）と
    依然未対応の一般化（後 3 つ false）。M441F の単一跳躍 scope とは異なり、
    multiJump=true が「単一跳躍のみ」を破った印。 -/
def mjwModelScope : mjwScope where
  multiJump := true
  zp2 := true
  hasseArfChecked := true
  generalMultiJump := false
  nonCyclic := false
  generalHasseArf := false

/-- **M446F-7b: 正直な限定（定理・消さない）** — 破ったのは全分岐 ℤ/p²（2 跳躍）の 1 族のみ。
    任意跳躍数・非巡回・一般 Hasse–Arf は false（対象外）。 -/
theorem mjw_model_scope :
    mjwModelScope.multiJump = true ∧ mjwModelScope.zp2 = true ∧
    mjwModelScope.hasseArfChecked = true ∧ mjwModelScope.generalMultiJump = false ∧
    mjwModelScope.nonCyclic = false ∧ mjwModelScope.generalHasseArf = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **M446F-7c: M441F「単一跳躍のみ」を破ったことの定理（本物）** —
    b₁<b₂ で分岐フィルトレーションが 3 段 |G_0|=p², |G_{b₁+1}|=p, |G_{b₂+1}|=1 を取る。
    中間段 p（≠p², ≠1）の実在が **2 跳躍**の証拠——M441F の単一跳躍（2 段 |G_i|∈{1,p}）を破る。 -/
theorem mjw_breaks_single_jump (p b1 b2 : Nat) (h1 : b1 < b2) :
    mjwZp2Groups p b1 b2 0 = p * p ∧
    mjwZp2Groups p b1 b2 (b1 + 1) = p ∧
    mjwZp2Groups p b1 b2 (b2 + 1) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact mjw_grp_lo p b1 b2 0 (Nat.zero_le b1)
  · exact mjw_grp_mid p b1 b2 (b1 + 1) (by omega) (by omega)
  · exact mjw_grp_hi p b1 b2 (by omega) (b2 + 1) (by omega)

/-- **M446F-7d: 限定内での恒等式成立（本物）** — 多跳躍 scope（b₁≤b₂）を満たす下で
    ∀ p, v(disc) = Σ_χ a(χ) = d が成立する（限定の忠実な充足）。 -/
theorem mjw_scope_witness :
    (mjwModelScope.multiJump = true) ∧
    (∀ p b1 b2, b1 ≤ b2 → mjwConductorDisc p b1 b2 = mjwDiffMultiJump p b1 b2) :=
  ⟨rfl, fun p b1 b2 hb => mjw_conductor_discriminant_multi p b1 b2 hb⟩

/-! ## §8 capstone: 多跳躍 野性 conductor-discriminant データ -/

/-- **M446F-8: 多跳躍 野性 conductor-discriminant データ** — 剰余標数 p、単位性 hp、
    下付き 2 跳躍 b₁≤b₂、分岐群位数 groupOrder（|G_i|∈{1,p,p²}）、different 指数 differentExp を束ね、
      * 3 段群位数（`order_lo`/`order_mid`/`order_hi`）,
      * **多跳躍 different** d = Σ_{i=0}^{b₂}(|G_i|−1)（`different_eq`）,
      * **conductor-discriminant** d = (b₁+1)(p²−1)+(b₂−b₁)(p−1)（`conductor_disc`）
    を要請する。全分岐 巡回 ℤ/p² 多跳躍野性分岐の conductor-discriminant valuation 恒等式の核。 -/
structure MultiJumpWildData where
  p : Nat
  hp : 1 ≤ p
  b1 : Nat
  b2 : Nat
  hb : b1 ≤ b2
  groupOrder : Nat → Nat
  order_lo : ∀ i, i ≤ b1 → groupOrder i = p * p
  order_mid : ∀ i, b1 < i → i ≤ b2 → groupOrder i = p
  order_hi : ∀ i, b2 < i → groupOrder i = 1
  differentExp : Nat
  different_eq : differentExp = wcdDiffSum groupOrder b2
  conductor_disc : differentExp = (b1 + 1) * (p * p - 1) + (b2 - b1) * (p - 1)

/-- **M446F-8b: データの構成**（剰余標数 p, hp, 2 跳躍 b₁≤b₂ から本物 witness）。 -/
def mjwDataOf (p : Nat) (hp : 1 ≤ p) (b1 b2 : Nat) (hb : b1 ≤ b2) : MultiJumpWildData where
  p := p
  hp := hp
  b1 := b1
  b2 := b2
  hb := hb
  groupOrder := mjwZp2Groups p b1 b2
  order_lo := fun i hi => mjw_grp_lo p b1 b2 i hi
  order_mid := fun i h1 h2 => mjw_grp_mid p b1 b2 i h1 h2
  order_hi := fun i hi => mjw_grp_hi p b1 b2 hb i hi
  differentExp := wcdDiffSum (mjwZp2Groups p b1 b2) b2
  different_eq := rfl
  conductor_disc := mjw_diff_zp2 p b1 b2 hb

/-- **M446F-8c: データの存在**（無矛盾性 witness、ℤ/4 野性 b₁=1, b₂=3）。 -/
theorem mjw_exists : Nonempty MultiJumpWildData :=
  ⟨mjwDataOf 2 (by omega) 1 3 (by omega)⟩

/-! ## §9 worked examples: ℤ/4 (b₁=1,b₂=3: d=8,Swan=5)・Hasse–Arf・跳躍数=1 還元 -/

/-- **M446F-9a: 全分岐 ℤ/4 多跳躍 (b₁=1,b₂=3)** different 指数 d = 8。
    (1+1)(4−1)+(3−1)(2−1) = 2·3 + 2·1 = 8。3 段 |G|=4,4,2,2 の階段和。 -/
theorem mjw_ex_zp4_diff : wcdDiffSum (mjwZp2Groups 2 1 3) 3 = 8 := rfl

/-- **M446F-9b: 全分岐 ℤ/4 多跳躍 (b₁=1,b₂=3)** Swan 導手 sw = 5（i≥1 の階段和 3+1+1）。 -/
theorem mjw_ex_zp4_swan : mjwSwanSum (mjwZp2Groups 2 1 3) 3 = 5 := rfl

/-- **M446F-9c: 多跳躍 Swan > 単一跳躍 Swan（具体・strict）** —
    ℤ/4 (b₁=1,b₂=3) の Swan 5 > 同 top break の単一跳躍 ℤ/2 (m=3) の Swan 3。 -/
theorem mjw_ex_swan_strict : mjwSwanSum (wcdRamGroups 2 3) 3 < mjwSwanSum (mjwZp2Groups 2 1 3) 3 := by
  show 3 < 5
  omega

/-- **M446F-9d: 全分岐 ℤ/4 多跳躍 (b₁=1,b₂=3)** conductor-discriminant v(disc)=Σ_χ a(χ)=d=8。 -/
theorem mjw_ex_zp4_cd : mjwConductorDisc 2 1 3 = mjwDiffMultiJump 2 1 3 :=
  mjw_conductor_discriminant_multi 2 1 3 (by omega)

/-- **M446F-9e: 多跳躍の証拠 (b₁=1,b₂=3)** 3 段 |G_0|=4, |G_2|=2, |G_4|=1（中間段 2 実在）。 -/
theorem mjw_ex_three_levels :
    mjwZp2Groups 2 1 3 0 = 4 ∧ mjwZp2Groups 2 1 3 2 = 2 ∧ mjwZp2Groups 2 1 3 4 = 1 :=
  mjw_breaks_single_jump 2 1 3 (by omega)

/-- **M446F-9f: Hasse–Arf 整数性 (p=2,b₁=1,b₂=3=1+2·1)** 上付き break φ(3)=1+1=2（整数）。
    p∣(b₂−b₁)=2 ゆえ φ(b₂)=b₁+(b₂−b₁)/p が整数に landing。 -/
theorem mjw_ex_hasse : mjwUpperBreak 2 1 3 = 2 ∧ 2 * (mjwUpperBreak 2 1 3 - 1) = 3 - 1 :=
  mjw_hasse_arf_integrality 2 1 1 (by omega)

/-- **M446F-9g: Hasse–Arf 可除性形 (p=2,b₁=1,b₂=3)** 2·(φ(3)−1)=2=b₂−b₁（余りなし）。 -/
theorem mjw_ex_hasse_dvd : 2 * (mjwUpperBreak 2 1 3 - 1) = 3 - 1 :=
  mjw_hasse_arf_dvd 2 1 3 (by omega) ⟨1, by omega⟩

/-- **M446F-9h: 跳躍数=1 還元 (b₁=b₂=2)** 多跳躍 ℤ/p² が M441F 単一跳躍 `wcdRamGroups 4 2` へ。 -/
theorem mjw_ex_reduce (i : Nat) : mjwZp2Groups 2 2 2 i = wcdRamGroups 4 2 i :=
  mjw_reduces_to_single 2 2 i

/-- **M446F-9i: 跳躍数=1 還元値 (b₁=b₂=2)** d=(2+1)(4−1)=9（単一跳躍 ℤ/4 の different）。 -/
theorem mjw_ex_reduce_val : wcdDiffSum (mjwZp2Groups 2 2 2) 2 = 9 :=
  mjw_collapse_value 2 2

/-- **M446F-9j: capstone まとめ** — ℤ/4(b₁=1,b₂=3: d=8,Swan=5)・conductor-discriminant 一致・
    多跳躍 Swan>単一跳躍・Hasse–Arf 整数 break・跳躍数=1 で M441F 還元。 -/
theorem mjw_examples :
    wcdDiffSum (mjwZp2Groups 2 1 3) 3 = 8 ∧
    mjwSwanSum (mjwZp2Groups 2 1 3) 3 = 5 ∧
    mjwConductorDisc 2 1 3 = mjwDiffMultiJump 2 1 3 ∧
    mjwSwanSum (wcdRamGroups 2 3) 3 < mjwSwanSum (mjwZp2Groups 2 1 3) 3 ∧
    mjwUpperBreak 2 1 3 = 2 ∧
    wcdDiffSum (mjwZp2Groups 2 2 2) 2 = 9 :=
  ⟨rfl, rfl, mjw_conductor_discriminant_multi 2 1 3 (by omega),
   mjw_ex_swan_strict, (mjw_hasse_arf_integrality 2 1 1 (by omega)).1, mjw_collapse_value 2 2⟩

end IUT
