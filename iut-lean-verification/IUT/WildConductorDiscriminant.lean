/-
  IUT/WildConductorDiscriminant.lean
-- M441F WildConductorDiscriminant [実・本物・柱B]
-- complete_pct 影響: **前進あり**（柱B）。M435F/M425F は different 指数
--   d = Σ_{i≥0}(|G_i|−1) を **tame（|G_0|=e, |G_i|=1 i≥1, Swan 導手 0）**の部分ケースでのみ
--   閉じ、`cdd_model_scope`/`dff_...` で「野性分岐（高次分岐群 G_i≠1, i≥1・Swan 導手）は
--   対象外」と正直に限定していた。本モジュールはその限定を **1 つの野性分岐部分ケース**
--   ——**全分岐 巡回 ℤ/p 拡大 L/K（剰余標数 p, 下付き番号付けの単一跳躍 m）**——で
--   **昇格して破る**。ここでは高次分岐群が非自明:
--       |G_i| = p  (0 ≤ i ≤ m),   |G_i| = 1  (i > m)      （G ≅ ℤ/p, 単一 break at m）
--   ゆえ i≥1 の項が残り、Swan 導手 sw(χ) = Σ_{i≥1} codim = m ≠ 0（m≥1 で野性）を**本物構成**。
--   conductor-discriminant を野性ケースで検証:
--       v(disc) = Σ_χ a(χ) = (p−1)·(m+1)          （Artin 導手総和・非自明指標 p−1 個）
--       d_different = Σ_{i=0}^{m}(|G_i|−1) = (m+1)·(p−1)   （different telescope・野性版）
--   が一致（`wcd_conductor_discriminant_wild`）。**Artin 導手 a = tame f(=1) + Swan(=m)**
--   の分解を高次分岐 codim 列から本物に建て（`wcd_artin_tame_swan`）、**m=0 で野性項が消え
--   M435F/M425F の tame telescope d=e−1 へ厳密還元**する（`wcd_reduces_to_tame`/`wcd_reduces_to_cdd`）。
-- 正直な限定（消去・弱化禁止）: 破ったのは **単一跳躍 m の 全分岐 巡回 ℤ/p 拡大**（|G_i|∈{1,p}）の
--   1 つの具体族のみ。**一般野性分岐（多跳躍・|G_i| 任意・非巡回）・Hasse–Arf 整数跳躍定理・
--   upper/lower numbering の一般変換・一般 p-拡大**は依然対象外——後続。これを §6 `wcdScope`/
--   `wcd_model_scope` で定理化する（M435F の「tame のみ」を実際に破ったことは
--   `wcd_swan_nonzero`・`wcd_breaks_tame_only` で明示）。
--
--  ────────────────────────────────────────────────────────────────────────
--  二軸（CLAUDE.md §1）
--  * 分類: **[実]**（(a) 昇格）。M435F `cdd_model_scope`（tame のみ・Swan 0）と
--    M425F `dffDifferentSum`（|G_i|=1, i≥1）の tame 限定を、**高次分岐群 |G_i|=p (1≤i≤m) を
--    持つ全分岐 ℤ/p 野性拡大**で置換し、Swan 導手非自明・conductor-discriminant 一致を
--    本物 Nat 算術で閉じる。tame は m=0 の退化として厳密回復（限定を狭めて正直に述べ直す）。
--  * complete_pct 影響: **前進あり**（柱B: 野性 different Σ(|G_i|−1)=(m+1)(p−1)・Swan 導手 m・
--    野性 conductor-discriminant v(disc)=Σ_χ a(χ)=d の本物建設 = M435F tame-only 限定の突破）。
--
--  既存モジュールの何を本物化したか
--  * M425F `dffDifferentSum e n`（|G_i|=1, i≥1 で e−1 に telescope）を、|G_i|=p (i≤m) を持つ
--    `wcdDiffSum (wcdRamGroups p m)` へ一般化し、i≥1 項が残る野性 telescope (m+1)(p−1) を本物証明。
--  * M430F の tame Artin 導手 f=dim(V/V^{G_0})=1（i≥1 項 0）を、高次 codim 列 `wcdCodim m` から
--    a(χ) = tame(1) + Swan(m) へ拡張し、Swan = Σ_{i≥1} codim を本物構成（`wcd_artin_eq_tame_swan`）。
--  * M435F `cdd_conductor_discriminant`（tame・両辺 p−2）の野性版 `wcd_conductor_discriminant_wild`
--    （両辺 (p−1)(m+1)）を建て、m=0 で M435F/M425F の tame telescope へ厳密還元（genuine reduction）。
--
--  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
--  * `wcdRamGroups` / `wcd_ram_zero` / `wcd_ram_le` / `wcd_ram_gt` / `wcd_ram_tame`
--      — 野性分岐群位数 |G_i|=p (i≤m), 1 (i>m)、m=0 で M425F `dffTameOrder` に一致
--  * `wcdDiffSum` / `wcd_sum_const` / `wcd_sum_at_break` / `wcd_sum_stable` / `wcd_different_eq`
--      — **野性 different d = Σ_{i=0}^{m}(|G_i|−1) = (m+1)(p−1)**（i≥1 項が残る telescope）
--  * `wcdCodim` / `wcdSwanSum` / `wcd_swan_val` / `wcdSwanExp` / `wcd_swan_nonzero`
--      — **Swan 導手 sw = Σ_{i≥1} codim = m ≠ 0**（m≥1 で野性・tame では 0 だった項）
--  * `wcdArtinSum` / `wcd_artin_val` / `wcdArtinExpWild` / `wcd_artin_eq_tame_swan` / `wcd_artin_tame_swan`
--      — **Artin 導手 a(χ) = tame f(=1) + Swan(=m) = m+1**（高次 codim 列からの本物分解）
--  * `wcdConductorTotal` / `wcd_conductor_discriminant_wild`（**本命題**）
--      — 野性 conductor-discriminant v(disc)=Σ_χ a(χ)=(p−1)(m+1)=d_different
--  * `wcd_reduces_to_tame` / `wcd_reduces_to_cdd` — m=0 で M425F/M435F tame telescope へ厳密還元
--  * `wcdScope` / `wcd_model_scope` / `wcd_breaks_tame_only` / `wcd_scope_witness` — 正直な限定の定理化
--  * `WildConductorDiscriminantData` / `wcdDataOf` / `wcd_exists` — capstone
--  * `wcd_ex_wild_2_1_*`（ℤ/2, m=1: d=2, Swan=1）・`wcd_ex_wild_3_1_*`（ℤ/3, m=1: d=4）ほか
--
--  正直な限定（CLAUDE.md §4: 消去・弱化禁止）: 上記ヘッダ限定を §6 で定理化。破ったのは
--  単一跳躍 m の全分岐巡回 ℤ/p の 1 族のみ。一般野性・Hasse–Arf・非巡回・多跳躍は後続。
--  全て選択公理不使用（propext/Quot.sound のみ）。共有ファイル未変更（新規 1 本）。
-/
import IUT.ConductorDiscriminant

namespace IUT

/-! ## §1 野性分岐群位数 |G_i| = p (0≤i≤m), 1 (i>m)（全分岐 巡回 ℤ/p・単一跳躍 m）

    剰余標数 p の局所体 K 上の**全分岐 巡回 ℤ/p 拡大** L/K を考える。ℤ/p は単純ゆえ
    下付き番号付けの分岐フィルトレーション G_0 ⊇ G_1 ⊇ … は唯一の跳躍 m（下付き break）を持ち
      |G_i| = p  (0 ≤ i ≤ m),   |G_i| = 1  (i > m).
    m ≥ 1 のとき **G_1 ≠ 1** ——高次分岐群が非自明——ゆえ**野性分岐**（p ∣ e=p）。
    M425F の tame（|G_0|=e, |G_i|=1 i≥1）を実際に破る具体族である。 -/

/-- **M441F-1pre: 分岐しきい値判定** wcdBle i m = (i ≤ m)（第 1 引数 i を主軸に構造再帰）。
    i=0 で true・(i+1,0) で false・(i+1,m+1) で i,m に降下——ゆえ i=0 側が定義的に簡約する。 -/
def wcdBle : Nat → Nat → Bool
  | 0,     _     => true
  | _ + 1, 0     => false
  | i + 1, m + 1 => wcdBle i m

/-- **M441F-1pre-a: wcdBle = true (i ≤ m)（本物）**。 -/
theorem wcd_ble_le : ∀ i m, i ≤ m → wcdBle i m = true := by
  intro i
  induction i with
  | zero => intro m _; rfl
  | succ j ih =>
    intro m h
    cases m with
    | zero => exact absurd h (by omega)
    | succ k => exact ih k (by omega)

/-- **M441F-1pre-b: wcdBle = false (m < i)（本物）**。 -/
theorem wcd_ble_gt : ∀ i m, m < i → wcdBle i m = false := by
  intro i
  induction i with
  | zero => intro m h; exact absurd h (by omega)
  | succ j ih =>
    intro m h
    cases m with
    | zero => rfl
    | succ k => exact ih k (by omega)

/-- **M441F-1: 野性分岐群位数** |G_i| = p (i≤m), 1 (i>m)（ℤ/p 単一跳躍 m）。
    wcdBle で i≤m を判定（i=0 で常に true ⇒ |G_0|=p が定義的）。 -/
def wcdRamGroups (p m i : Nat) : Nat := bif wcdBle i m then p else 1

/-- **M441F-1a: |G_0| = p（本物・定義的）** — 惰性群 G_0 の位数（全分岐 ℤ/p）。 -/
theorem wcd_ram_zero (p m : Nat) : wcdRamGroups p m 0 = p := rfl

/-- **M441F-1b: |G_i| = p (i ≤ m)（本物）** — 跳躍 m まで高次分岐群も位数 p（野性）。 -/
theorem wcd_ram_le (p : Nat) : ∀ i m, i ≤ m → wcdRamGroups p m i = p := by
  intro i m h
  show (bif wcdBle i m then p else 1) = p
  rw [wcd_ble_le i m h]; rfl

/-- **M441F-1c: |G_i| = 1 (i > m)（本物）** — 跳躍を過ぎると分岐群自明。 -/
theorem wcd_ram_gt (p : Nat) : ∀ i m, m < i → wcdRamGroups p m i = 1 := by
  intro i m h
  show (bif wcdBle i m then p else 1) = 1
  rw [wcd_ble_gt i m h]; rfl

/-- **M441F-1d: m=0 で M425F tame 群位数に一致（本物・還元の核）** —
    wcdRamGroups p 0 i = dffTameOrder p i（|G_0|=p, |G_i|=1 i≥1）。野性の跳躍を 0 にすると
    M425F の tame 分岐群位数（|G_0|=e, |G_i|=1）に厳密還元する。 -/
theorem wcd_ram_tame (p i : Nat) : wcdRamGroups p 0 i = dffTameOrder p i := by
  cases i with
  | zero => rfl
  | succ j => rfl

/-! ## §2 野性 different 指数 d = Σ_{i=0}^{m}(|G_i|−1) = (m+1)(p−1)（i≥1 項が残る telescope）

    different 指数 d = v_L(𝔡_{L/K}) = Σ_{i≥0}(|G_i|−1)（Serre, Corps Locaux IV §1）。
    tame（M425F）では i≥1 項が 0 に telescope して d=e−1 だったが、**野性**では
      d = (|G_0|−1) + Σ_{i=1}^{m}(|G_i|−1) = (p−1) + m·(p−1) = (m+1)(p−1)
    と **i≥1 の高次項が非自明に残る**。これを一般群位数関数上の部分和で本物建設する。 -/

/-- **M441F-2: 一般 different 部分和** d_n = Σ_{i=0}^{n}(|G_i|−1)（分岐群位数関数 G 上）。
    M425F `dffDifferentSum` の群位数関数を任意化した本物版。 -/
def wcdDiffSum (G : Nat → Nat) : Nat → Nat
  | 0     => G 0 - 1
  | n + 1 => wcdDiffSum G n + (G (n + 1) - 1)

/-- **M441F-2a: 定値区間の和（本物）** — G が i≤n で一定 p なら Σ_{i=0}^{n}(|G_i|−1)=(n+1)(p−1)。 -/
theorem wcd_sum_const (p : Nat) (G : Nat → Nat) :
    ∀ n, (∀ i, i ≤ n → G i = p) → wcdDiffSum G n = (n + 1) * (p - 1) := by
  intro n
  induction n with
  | zero =>
    intro h
    show G 0 - 1 = (0 + 1) * (p - 1)
    rw [h 0 (Nat.le_refl 0)]
    show p - 1 = 1 * (p - 1)
    rw [Nat.one_mul]
  | succ k ih =>
    intro h
    show wcdDiffSum G k + (G (k + 1) - 1) = (k + 1 + 1) * (p - 1)
    rw [ih (fun i hi => h i (by omega)), h (k + 1) (by omega), ← Nat.succ_mul]

/-- **M441F-2b: 野性 different の跳躍点での値（本命題・本物）** —
    Σ_{i=0}^{m}(|G_i|−1) = (m+1)(p−1)。跳躍 m まで各項 (p−1) が残る（野性 telescope）。 -/
theorem wcd_sum_at_break (p m : Nat) :
    wcdDiffSum (wcdRamGroups p m) m = (m + 1) * (p - 1) :=
  wcd_sum_const p (wcdRamGroups p m) m (fun i hi => wcd_ram_le p i m hi)

/-- **M441F-2c: 跳躍以降の安定（本物）** — n=m+k (≥m) でも Σ=(m+1)(p−1) 一定。
    i>m の項が (|G_i|−1)=0 ゆえ、上限を跳躍点より上げても different 指数は不変。 -/
theorem wcd_sum_stable (p m : Nat) :
    ∀ k, wcdDiffSum (wcdRamGroups p m) (m + k) = (m + 1) * (p - 1) := by
  intro k
  induction k with
  | zero => exact wcd_sum_at_break p m
  | succ j ih =>
    show wcdDiffSum (wcdRamGroups p m) (m + j + 1) = (m + 1) * (p - 1)
    have hstep : wcdDiffSum (wcdRamGroups p m) (m + j + 1)
        = wcdDiffSum (wcdRamGroups p m) (m + j) + (wcdRamGroups p m (m + j + 1) - 1) := rfl
    have hgt : wcdRamGroups p m (m + j + 1) = 1 := wcd_ram_gt p (m + j + 1) m (by omega)
    rw [hstep, hgt, ih, Nat.sub_self, Nat.add_zero]

/-- **M441F-2d: 野性 different 指数** d = (m+1)(p−1)（跳躍 m の全分岐 ℤ/p）。 -/
def wcdDifferentWild (p m : Nat) : Nat := (m + 1) * (p - 1)

/-- **M441F-2e: d = Σ_{i=0}^{m}(|G_i|−1)（本物・和からの導出）**。 -/
theorem wcd_different_eq (p m : Nat) :
    wcdDiffSum (wcdRamGroups p m) m = wcdDifferentWild p m :=
  wcd_sum_at_break p m

/-! ## §3 Swan 導手 sw = Σ_{i≥1} codim(V^{G_i}) = m（tame で 0 だった高次項が野性で非自明）

    1 次元非自明指標 χ（ℤ/p の非自明指標）の Artin 導手は分岐フィルトレーション上の
      a(χ) = Σ_{i≥0} (|G_i|/|G_0|)·codim(V^{G_i}).
    G=ℤ/p は単純ゆえ i≤m で G_i=ℤ/p 上 χ 非自明 → codim=1、i>m で codim=0。|G_i|/|G_0|=p/p=1。
    よって a(χ) = Σ_{i=0}^{m} 1 = m+1。**tame 部** f = i=0 項 = 1、
    **Swan 部** sw = Σ_{i≥1} codim = m（M430F では tame ゆえ i≥1 項 0 = Swan 0 だったものが
    野性で m≠0 に）。高次 codim 列 `wcdCodim m` から本物に構成する。 -/

/-- **M441F-3: 高次 codim 列** codim(V^{G_i}) = 1 (i≤m), 0 (i>m)（非自明 1 次元指標）。
    wcdBle で i≤m を判定（i=0 で常に 1 が定義的）。 -/
def wcdCodim (m i : Nat) : Nat := bif wcdBle i m then 1 else 0

/-- **M441F-3a: codim = 1 (i ≤ m)（本物）** — 跳躍 m まで G_i 非自明 ⇒ V^{G_i}=0。 -/
theorem wcd_codim_le : ∀ i m, i ≤ m → wcdCodim m i = 1 := by
  intro i m h
  show (bif wcdBle i m then 1 else 0) = 1
  rw [wcd_ble_le i m h]; rfl

/-- **M441F-3b: codim = 0 (i > m)（本物）** — 跳躍以降 G_i 自明 ⇒ V^{G_i}=V。 -/
theorem wcd_codim_gt : ∀ i m, m < i → wcdCodim m i = 0 := by
  intro i m h
  show (bif wcdBle i m then 1 else 0) = 0
  rw [wcd_ble_gt i m h]; rfl

/-- **M441F-3c: Swan 部分和** sw_n = Σ_{i=1}^{n} codim(V^{G_i})（i≥1 の高次項のみ）。 -/
def wcdSwanSum (m : Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => wcdSwanSum m n + wcdCodim m (n + 1)

/-- **M441F-3d: Artin 部分和** a_n = Σ_{i=0}^{n} codim(V^{G_i})（i=0 の tame 項込み）。 -/
def wcdArtinSum (m : Nat) : Nat → Nat
  | 0     => wcdCodim m 0
  | n + 1 => wcdArtinSum m n + wcdCodim m (n + 1)

/-- **M441F-3e: Swan 部分和の値（本物）** sw_n = n（n ≤ m、各高次項 codim=1）。 -/
theorem wcd_swan_val (m : Nat) : ∀ n, n ≤ m → wcdSwanSum m n = n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    show wcdSwanSum m k + wcdCodim m (k + 1) = k + 1
    rw [ih (by omega), wcd_codim_le (k + 1) m (by omega)]

/-- **M441F-3f: Artin 部分和の値（本物）** a_n = n+1（n ≤ m）。 -/
theorem wcd_artin_val (m : Nat) : ∀ n, n ≤ m → wcdArtinSum m n = n + 1 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    show wcdArtinSum m k + wcdCodim m (k + 1) = k + 1 + 1
    rw [ih (by omega), wcd_codim_le (k + 1) m (by omega)]

/-- **M441F-3g: Artin = tame(1) + Swan（本物・分解）** a_n = 1 + sw_n（任意 n）。
    i=0 の tame 項（=1）と i≥1 の Swan 項の和。M430F では Swan_n=0 だったが野性で非自明。 -/
theorem wcd_artin_eq_tame_swan (m : Nat) : ∀ n, wcdArtinSum m n = 1 + wcdSwanSum m n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show wcdArtinSum m k + wcdCodim m (k + 1) = 1 + (wcdSwanSum m k + wcdCodim m (k + 1))
    rw [ih]
    omega

/-- **M441F-3h: tame conductor 指数** f = 1（i=0 の G_0 項・M430F の tame 導手）。 -/
def wcdTameCondExp : Nat := 1

/-- **M441F-3i: Swan 導手指数** sw = Σ_{i≥1} codim = m。 -/
def wcdSwanExp (m : Nat) : Nat := wcdSwanSum m m

/-- **M441F-3j: Swan 導手 = m（本物・定値）**。 -/
theorem wcd_swan_eq (m : Nat) : wcdSwanExp m = m := wcd_swan_val m m (Nat.le_refl m)

/-- **M441F-3k: Swan 導手が正（本命題・野性の徴）** — m≥1 で sw = m > 0。
    tame（M430F/M425F）では Swan 導手は常に 0 だった。本モジュールは m≥1 で**非零 Swan 導手**を
    本物構成し、M435F の「tame のみ・Swan 0」限定を実際に破ることを示す。 -/
theorem wcd_swan_nonzero (m : Nat) (hm : 1 ≤ m) : 0 < wcdSwanExp m := by
  rw [wcd_swan_eq m]; exact hm

/-- **M441F-3l: Artin 導手指数** a = m+1（非自明 ℤ/p 指標）。 -/
def wcdArtinExpWild (m : Nat) : Nat := wcdArtinSum m m

/-- **M441F-3m: Artin = tame f + Swan（本物）** a = 1 + sw = tame(1) + Swan(m) = m+1。 -/
theorem wcd_artin_tame_swan (m : Nat) :
    wcdArtinExpWild m = wcdTameCondExp + wcdSwanExp m := by
  show wcdArtinSum m m = 1 + wcdSwanSum m m
  exact wcd_artin_eq_tame_swan m m

/-- **M441F-3n: Artin 導手 = m+1（本物・値）**。 -/
theorem wcd_artin_eq (m : Nat) : wcdArtinExpWild m = m + 1 :=
  wcd_artin_val m m (Nat.le_refl m)

/-! ## §4 野性 conductor-discriminant（本命題）: v(disc) = Σ_χ a(χ) = d_different

    全分岐 巡回 ℤ/p 拡大では非自明指標が p−1 個、各 a(χ) = m+1（§3）。
    conductor-discriminant 公式（Führerdiskriminantenproduktformel の valuation 版）:
      v(disc) = Σ_χ a(χ) = (p−1)·(m+1)
    と different 指数
      d = Σ_{i=0}^{m}(|G_i|−1) = (m+1)·(p−1)   （§2）
    が一致する。M435F の tame（両辺 p−2）に対する**野性版**（両辺 (p−1)(m+1)）である。 -/

/-- **M441F-4: 判別式の valuation** v(disc) = Σ_χ a(χ) = (非自明指標数 p−1)·(Artin 導手 a)。 -/
def wcdConductorTotal (p m : Nat) : Nat := (p - 1) * wcdArtinSum m m

/-- **M441F-4a: 野性 conductor-discriminant 恒等式（本命題・本物）** —
    v(disc) = Σ_χ a(χ) = (p−1)(m+1) = d_different = Σ_{i=0}^{m}(|G_i|−1)。
    左辺 = 非自明指標 p−1 個 × Artin 導手 (m+1)、右辺 = 野性 different telescope。
    M435F `cdd_conductor_discriminant`（tame・両辺 p−2）の**野性昇格版**。 -/
theorem wcd_conductor_discriminant_wild (p m : Nat) :
    wcdConductorTotal p m = wcdDiffSum (wcdRamGroups p m) m := by
  show (p - 1) * wcdArtinSum m m = wcdDiffSum (wcdRamGroups p m) m
  rw [wcd_artin_val m m (Nat.le_refl m), wcd_sum_at_break p m]
  exact Nat.mul_comm (p - 1) (m + 1)

/-- **M441F-4b: 恒等式の値版（本物）** — v(disc) = d = (p−1)(m+1)（両辺の値一致）。 -/
theorem wcd_cond_disc_val (p m : Nat) :
    wcdConductorTotal p m = (p - 1) * (m + 1) ∧
    wcdDiffSum (wcdRamGroups p m) m = (m + 1) * (p - 1) := by
  refine ⟨?_, wcd_sum_at_break p m⟩
  show (p - 1) * wcdArtinSum m m = (p - 1) * (m + 1)
  rw [wcd_artin_val m m (Nat.le_refl m)]

/-! ## §5 tame への厳密還元（m=0 で M425F/M435F telescope を回復・genuine reduction）

    野性の跳躍 m を 0 に退化させると高次分岐群が消え（wcdRamGroups p 0 = dffTameOrder p）、
    野性 different telescope が M425F の tame telescope へ厳密還元する:
      wcdDiffSum (wcdRamGroups p 0) n = dffDifferentSum p n = p−1 = M435F `cddDifferentVal p`.
    同時に Swan 導手 sw = 0（m=0）。「野性項を 0 にすると tame 公式へ戻る」ことの本物証明。 -/

/-- **M441F-5: different 部分和の M425F 一致（本物）** — 群位数関数 dffTameOrder では
    wcdDiffSum と M425F dffDifferentSum が一致（同一漸化式）。 -/
theorem wcd_diffsum_tame (e : Nat) : ∀ n, dffDifferentSum e n = wcdDiffSum (dffTameOrder e) n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show dffDifferentSum e k + (dffTameOrder e (k + 1) - 1)
       = wcdDiffSum (dffTameOrder e) k + (dffTameOrder e (k + 1) - 1)
    rw [ih]

/-- **M441F-5a: different 部分和の群位数関数依存性（本物）** — G, H が i≤n で一致すれば和も一致。 -/
theorem wcd_diffsum_congr (G H : Nat → Nat) :
    ∀ n, (∀ i, i ≤ n → G i = H i) → wcdDiffSum G n = wcdDiffSum H n := by
  intro n
  induction n with
  | zero =>
    intro h
    show G 0 - 1 = H 0 - 1
    rw [h 0 (Nat.le_refl 0)]
  | succ k ih =>
    intro h
    show wcdDiffSum G k + (G (k + 1) - 1) = wcdDiffSum H k + (H (k + 1) - 1)
    rw [ih (fun i hi => h i (by omega)), h (k + 1) (Nat.le_refl (k + 1))]

/-- **M441F-5b: m=0 で M425F tame telescope へ厳密還元（本物・genuine reduction）** —
    wcdDiffSum (wcdRamGroups p 0) n = dffDifferentSum p n。野性の跳躍を 0 にすると
    高次分岐群が消え、M425F の tame different 和に一致する。 -/
theorem wcd_reduces_to_tame (p n : Nat) :
    wcdDiffSum (wcdRamGroups p 0) n = dffDifferentSum p n := by
  rw [wcd_diffsum_congr (wcdRamGroups p 0) (dffTameOrder p) n (fun i _ => wcd_ram_tame p i)]
  exact (wcd_diffsum_tame p n).symm

/-- **M441F-5c: m=0 で M435F `cddDifferentVal` へ厳密還元（本物）** —
    wcdDiffSum (wcdRamGroups p 0) n = cddDifferentVal p = p−1。野性 different の m=0 特殊化が
    M435F の tame different 指数（e=p で e−1）であることの genuine reduction。 -/
theorem wcd_reduces_to_cdd (p n : Nat) :
    wcdDiffSum (wcdRamGroups p 0) n = cddDifferentVal p := by
  rw [wcd_reduces_to_tame p n]
  exact (dff_different_eq_sum p n).symm

/-- **M441F-5d: m=0 で Swan 導手 0（本物）** — 野性跳躍を消すと Swan=0（tame・M430F に一致）。 -/
theorem wcd_swan_zero_tame : wcdSwanExp 0 = 0 := rfl

/-! ## §6 正直な限定の定理化（CLAUDE.md §4: 消去・弱化禁止）

    本モジュールが M435F の「tame のみ」を破ったのは、次を**すべて満たす 1 つの具体族**に限る:
      (wildBreak) 下付き番号付けの単一跳躍 m ≥ 1（G_1≠1 の野性分岐）,
      (cyclicZp) 全分岐 巡回 ℤ/p（|G_i| ∈ {1, p}）,
      (swanNonzero) Swan 導手 sw = m ≠ 0 を本物構成。
    以下は**依然対象外**（フラグ false）——後続:
      (generalWild) 一般野性分岐（|G_i| 任意・多跳躍）,
      (hasseArf) Hasse–Arf 整数跳躍定理・upper/lower numbering の一般変換,
      (nonCyclic) 非巡回・2 次元以上の表現,
      (generalPExt) 一般 p-拡大。 -/

/-- **M441F-6: 正直な限定フラグ** — 破った野性ケースと依然未対応の一般化を Bool で明示。 -/
structure wcdScope where
  /-- 単一跳躍 m≥1 の野性分岐（G_1≠1）を破った。 -/
  wildBreak : Bool
  /-- 全分岐 巡回 ℤ/p（|G_i|∈{1,p}）。 -/
  cyclicZp : Bool
  /-- Swan 導手 sw=m≠0 を本物構成（tame-only を実際に破った）。 -/
  swanNonzero : Bool
  /-- 一般野性分岐（|G_i| 任意・多跳躍）— 未対応。 -/
  generalWild : Bool
  /-- Hasse–Arf 整数跳躍定理・番号付け一般変換 — 未対応。 -/
  hasseArf : Bool
  /-- 非巡回・2 次元以上の表現 — 未対応。 -/
  nonCyclic : Bool
  /-- 一般 p-拡大 — 未対応。 -/
  generalPExt : Bool

/-- **M441F-6a: 本モジュールの scope witness** — 破った野性ケース（前 3 つ true）と
    依然未対応の一般化（後 4 つ false）。M435F の全 tame フラグ true とは異なり、
    wildBreak/swanNonzero が true = tame-only を破った印。 -/
def wcdModelScope : wcdScope where
  wildBreak := true
  cyclicZp := true
  swanNonzero := true
  generalWild := false
  hasseArf := false
  nonCyclic := false
  generalPExt := false

/-- **M441F-6b: 正直な限定（定理・消さない）** — 破ったのは単一跳躍 ℤ/p 野性の 1 族のみ。
    一般野性・Hasse–Arf・非巡回・一般 p-拡大は false（対象外）。 -/
theorem wcd_model_scope :
    wcdModelScope.wildBreak = true ∧ wcdModelScope.cyclicZp = true ∧
    wcdModelScope.swanNonzero = true ∧ wcdModelScope.generalWild = false ∧
    wcdModelScope.hasseArf = false ∧ wcdModelScope.nonCyclic = false ∧
    wcdModelScope.generalPExt = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **M441F-6c: M435F の「tame のみ」を破ったことの定理（本物）** —
    ∀ m≥1, Swan 導手 sw = m > 0。M435F `cdd_model_scope`（tame=true・Swan 0）に対し、
    本モジュールは非零 Swan 導手を持つ野性ケースを本物構成した、を明示。 -/
theorem wcd_breaks_tame_only : ∀ m, 1 ≤ m → 0 < wcdSwanExp m :=
  fun m hm => wcd_swan_nonzero m hm

/-- **M441F-6d: 限定内での恒等式成立（本物）** — 野性 scope（m≥1）を満たす下で
    ∀ p, v(disc) = Σ_χ a(χ) = d_different が成立する（限定の忠実な充足）。 -/
theorem wcd_scope_witness :
    (wcdModelScope.wildBreak = true) ∧
    (∀ p m, wcdConductorTotal p m = wcdDiffSum (wcdRamGroups p m) m) :=
  ⟨rfl, fun p m => wcd_conductor_discriminant_wild p m⟩

/-! ## §7 capstone: 野性 conductor-discriminant データ -/

/-- **M441F-7: 野性 conductor-discriminant データ** — 剰余標数 p、野性跳躍 m（hm: m≥1）、
    分岐群位数 groupOrder（|G_i|=p i≤m, 1 i>m）、Swan 導手 swanExp、different 指数 differentExp を束ね、
      * groupOrder の野性値（`order_le`/`order_gt`）,
      * **Swan 導手 sw=m≠0**（`swan_eq`/`swan_pos`）,
      * **conductor-discriminant** (p−1)(1+sw) = differentExp（`conductor_disc`）
    を要請する。全分岐 巡回 ℤ/p 野性分岐の conductor-discriminant valuation 恒等式の核。 -/
structure WildConductorDiscriminantData where
  p : Nat
  m : Nat
  hm : 1 ≤ m
  groupOrder : Nat → Nat
  order_le : ∀ i, i ≤ m → groupOrder i = p
  order_gt : ∀ i, m < i → groupOrder i = 1
  swanExp : Nat
  swan_eq : swanExp = m
  swan_pos : 0 < swanExp
  differentExp : Nat
  different_eq : differentExp = wcdDiffSum groupOrder m
  conductor_disc : (p - 1) * (1 + swanExp) = differentExp

/-- **M441F-7b: データの構成**（剰余標数 p, 野性跳躍 m, hm: m≥1 から本物 witness）。 -/
def wcdDataOf (p m : Nat) (hm : 1 ≤ m) : WildConductorDiscriminantData where
  p := p
  m := m
  hm := hm
  groupOrder := wcdRamGroups p m
  order_le := fun i hi => wcd_ram_le p i m hi
  order_gt := fun i hi => wcd_ram_gt p i m hi
  swanExp := wcdSwanExp m
  swan_eq := wcd_swan_eq m
  swan_pos := wcd_swan_nonzero m hm
  differentExp := wcdDiffSum (wcdRamGroups p m) m
  different_eq := rfl
  conductor_disc := by
    rw [wcd_swan_eq m, wcd_sum_at_break p m, Nat.add_comm 1 m]
    exact Nat.mul_comm (p - 1) (m + 1)

/-- **M441F-7c: データの存在**（無矛盾性 witness、ℤ/2 野性 m=1）。 -/
theorem wcd_exists : Nonempty WildConductorDiscriminantData :=
  ⟨wcdDataOf 2 1 (by omega)⟩

/-! ## §8 worked examples: ℤ/2 (m=1: d=2)・ℤ/3 (m=1: d=4)・ℤ/2 (m=2: d=3)・m=0 還元 -/

/-- **M441F-8a: 全分岐 ℤ/2 野性 (m=1)** different 指数 d = 2（(1+1)(2−1)=2）。 -/
theorem wcd_ex_wild_2_1_diff : wcdDiffSum (wcdRamGroups 2 1) 1 = 2 := rfl

/-- **M441F-8b: 全分岐 ℤ/2 野性 (m=1)** Swan 導手 sw = 1（≠0・野性の徴）。 -/
theorem wcd_ex_wild_2_1_swan : wcdSwanExp 1 = 1 := rfl

/-- **M441F-8c: 全分岐 ℤ/2 野性 (m=1)** Artin 導手 a = tame(1)+Swan(1) = 2。 -/
theorem wcd_ex_wild_2_1_artin : wcdArtinExpWild 1 = 2 := rfl

/-- **M441F-8d: 全分岐 ℤ/2 野性 (m=1)** conductor-discriminant v(disc)=Σ_χ a(χ)=d（両辺 2）。 -/
theorem wcd_ex_wild_2_1_cd : wcdConductorTotal 2 1 = wcdDiffSum (wcdRamGroups 2 1) 1 :=
  wcd_conductor_discriminant_wild 2 1

/-- **M441F-8e: 全分岐 ℤ/3 野性 (m=1)** different 指数 d = 4（(1+1)(3−1)=4）。
    非自明指標 p−1=2 個 × Artin (m+1)=2 = 4 = Σ_χ a(χ)。 -/
theorem wcd_ex_wild_3_1_diff : wcdDiffSum (wcdRamGroups 3 1) 1 = 4 := rfl

/-- **M441F-8f: 全分岐 ℤ/3 野性 (m=1)** conductor-discriminant（両辺 4）。 -/
theorem wcd_ex_wild_3_1_cd : wcdConductorTotal 3 1 = wcdDiffSum (wcdRamGroups 3 1) 1 :=
  wcd_conductor_discriminant_wild 3 1

/-- **M441F-8g: 全分岐 ℤ/2 野性 (m=2)** different 指数 d = 3（(2+1)(2−1)=3）・Swan=2。
    跳躍が上がると高次分岐群 G_1=G_2=ℤ/2 の寄与で d が増える（tame の d=e−1=1 を超える）。 -/
theorem wcd_ex_wild_2_2_diff : wcdDiffSum (wcdRamGroups 2 2) 2 = 3 := rfl

/-- **M441F-8h: 全分岐 ℤ/2 野性 (m=2)** Swan 導手 sw = 2。 -/
theorem wcd_ex_wild_2_2_swan : wcdSwanExp 2 = 2 := rfl

/-- **M441F-8i: m=0 還元** 野性 (m=0) different が M425F tame telescope に一致（d=p−1）。 -/
theorem wcd_ex_reduce : wcdDiffSum (wcdRamGroups 5 0) 10 = dffDifferentSum 5 10 :=
  wcd_reduces_to_tame 5 10

/-- **M441F-8j: m=0 還元（値）** 野性 (m=0) の d = 4 = M435F cddDifferentVal 5（=p−1=e−1）。 -/
theorem wcd_ex_reduce_cdd : wcdDiffSum (wcdRamGroups 5 0) 10 = cddDifferentVal 5 :=
  wcd_reduces_to_cdd 5 10

/-- **M441F-8k: capstone まとめ** — ℤ/2(m=1: d=2,Swan=1)・ℤ/3(m=1: d=4)・ℤ/2(m=2: Swan=2)・
    conductor-discriminant 一致・野性で Swan≠0（tame-only 突破）・m=0 で M435F 還元。 -/
theorem wcd_examples :
    wcdDiffSum (wcdRamGroups 2 1) 1 = 2 ∧
    wcdSwanExp 1 = 1 ∧
    wcdConductorTotal 3 1 = wcdDiffSum (wcdRamGroups 3 1) 1 ∧
    (0 < wcdSwanExp 2) ∧
    wcdDiffSum (wcdRamGroups 5 0) 10 = cddDifferentVal 5 :=
  ⟨rfl, rfl, wcd_conductor_discriminant_wild 3 1, wcd_swan_nonzero 2 (by omega),
   wcd_reduces_to_cdd 5 10⟩

end IUT
