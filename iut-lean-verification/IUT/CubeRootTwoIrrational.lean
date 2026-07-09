/-
  IUT/CubeRootTwoIrrational.lean — crt: ∛2 ∉ ℚ の実証明（x³ = 2 は有理数解を持たない）

  ── 主要成果の分類: **[実]**（本物の Int／本物の ℚ = QRat 上の完全証明。模型・代理・
     toy 主語は一切なし）。

  complete_pct 影響: **本ラウンドでは complete_pct は未設定（動かさない）**。本ファイルは
  「ℚ[x]/(x³−2) を実数体（3 次代数体）として建てる」ための既約性の最下層 ——
  「x³ − 2 が ℚ 上に根を持たない」= 「2 は ℚ の三乗元でない」を、本物の有理数体 QRat
  （M115F, Rationals.lean）と本物の Int 上でゼロから完全証明する **(b) 本物の先行建設**。
  代数体の実構成（柱C ℝ 基盤／柱A 数体）への必要足場であり、後続で最小多項式・単純拡大
  （既存 SimpleExtension / MinimalPolynomial）と接続して 3 次体 ℚ(∛2) を建てる。

  * crt-1 even_of_cube_even   — x³ が偶なら x が偶（Nat.pow_mod による mod 2 論法）
  * crt-2 crt_core            — 核 Nat 版: a³ = 2·b³ ⟹ b = 0（2 進無限降下・強帰納法）
  * crt-3 crt_no_int_cube_eq  — 核 Int 版: q ≠ 0 ⟹ p³ ≠ 2·q³（natAbs で Nat 版へ帰着）
  * crt-4 crt_no_rat_cube     — ℚ 版: 任意の r : QRat で r³ ≠ 2（本物の QRat 上）
  * crt-5 crt_two_not_cube    — 系: 2 は ℚ の三乗元でない（体公理／既約性向けの形）

  手法: **2 進付値の mod 3 は使わず、無限降下（強帰納法 Nat.strongRecOn）**で確実に完成。
  偶奇判定は `Nat.pow_mod`（a³ % 2 = (a%2)³ % 2）と `Nat.mul_pow`（(2c)³ = 8c³）のみ。
  Int → Nat は `Int.natAbs_pow`／`Int.natAbs_mul`／`Int.natAbs_eq_zero`。ℚ → Int は
  Rationals.lean の `quot_exact_rat`（分離性）で交差積 num³ = 2·den³ に落とす。

  正直な限定（何が本物で何が未達か）:
  - **本物**: crt_core・crt_no_int_cube_eq・crt_no_rat_cube はすべて本物の Int／QRat 上の
    完全証明（sorry 皆無・新規 Classical.choice 皆無）。QRat は M115F の本物の有理数体。
  - 本ファイルは「2 が三乗元でない」= x³−2 の**有理根の非存在**のみ。x³−2 の ℚ 上での
    完全な既約性（1 次因子分解の非存在は本ファイルで尽きるが、一般の因数分解不能性の
    形式化）や、剰余環 ℚ[x]/(x³−2) の体構成そのものは後続（既存 SimpleExtension 等と接続）。

  全て選択公理不使用（新規 choice を証明本体に導入しない。propext / Quot.sound のみ）。
-/
import IUT.Rationals

namespace IUT

/-! ## crt-1: x³ が偶なら x が偶（mod 2 の論法） -/

/-- **crt-1: 立方の偶奇** — `x³ % 2 = 0` ならば `x % 2 = 0`。
    `Nat.pow_mod` で `x³ % 2 = (x % 2)³ % 2` に還元し、`x % 2 ∈ {0,1}` を場合分け。
    `x % 2 = 1` の側は `1³ % 2 = 1 ≠ 0` で矛盾（choice なしの Or 分解）。 -/
theorem even_of_cube_even (x : Nat) (h : x ^ 3 % 2 = 0) : x % 2 = 0 := by
  have hp : x ^ 3 % 2 = (x % 2) ^ 3 % 2 := Nat.pow_mod x 3 2
  rw [h] at hp
  have hcase : x % 2 = 0 ∨ x % 2 = 1 := by omega
  cases hcase with
  | inl h0 => exact h0
  | inr h1 =>
    rw [h1] at hp
    rw [show (1 : Nat) ^ 3 % 2 = 1 from rfl] at hp
    omega

/-! ## crt-2: 核（Nat 版）— 無限降下 -/

/-- **crt-2: 核 Nat 版** — `a³ = 2·b³` ならば `b = 0`。
    2 進無限降下を強帰納法 `Nat.strongRecOn` で実装:
    `a³ = 2b³ ⟹ a 偶 ⟹ a = 2c ⟹ 8c³ = 2b³ ⟹ b³ = 4c³ ⟹ b 偶 ⟹ b = 2d ⟹ c³ = 2d³`
    で `c < a` の帰納法へ。従って `d = 0`、`b = 2d = 0`。 -/
theorem crt_core : ∀ a b : Nat, a ^ 3 = 2 * b ^ 3 → b = 0 := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a IH =>
    intro b h
    cases Nat.eq_zero_or_pos a with
    | inl ha0 =>
      -- 基底 a = 0: 0 = 2·b³ ⟹ b³ = 0 ⟹ b·b·b = 0 ⟹ b = 0（choice なしの mul_eq_zero）
      rw [ha0, show (0 : Nat) ^ 3 = 0 from rfl] at h
      have hb3z : b ^ 3 = 0 := by omega
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
        Nat.mul_eq_zero, Nat.mul_eq_zero] at hb3z
      omega
    | inr hapos =>
      -- a は偶
      have ha2 : a % 2 = 0 := by
        apply even_of_cube_even
        omega
      -- a = 2c
      obtain ⟨c, hac⟩ : ∃ c, a = 2 * c := ⟨a / 2, by omega⟩
      -- (2c)³ = 8c³
      rw [hac, Nat.mul_pow, show (2 : Nat) ^ 3 = 8 from rfl] at h
      -- 8c³ = 2b³ ⟹ b³ = 4c³
      have hb3 : b ^ 3 = 4 * c ^ 3 := by omega
      -- b は偶
      have hb2 : b % 2 = 0 := by
        apply even_of_cube_even
        omega
      obtain ⟨d, hbd⟩ : ∃ d, b = 2 * d := ⟨b / 2, by omega⟩
      -- (2d)³ = 8d³ かつ = 4c³ ⟹ c³ = 2d³
      rw [hbd, Nat.mul_pow, show (2 : Nat) ^ 3 = 8 from rfl] at hb3
      have hcd : c ^ 3 = 2 * d ^ 3 := by omega
      -- a = 2c かつ a > 0 なので c < a、帰納法
      have hca : c < a := by omega
      have hd0 : d = 0 := IH c hca d hcd
      rw [hbd, hd0]

/-! ## crt-3: 核（Int 版） -/

/-- **crt-3: 核 Int 版** — `q ≠ 0` ならば `p³ ≠ 2·q³`。
    両辺の `natAbs` を取り `Int.natAbs_pow`／`Int.natAbs_mul` で Nat 版 `crt_core` へ帰着。 -/
theorem crt_no_int_cube_eq (p q : Int) (hq : q ≠ 0) : p ^ 3 ≠ 2 * q ^ 3 := by
  intro h
  apply hq
  have hn : (p ^ 3).natAbs = (2 * q ^ 3).natAbs := congrArg Int.natAbs h
  rw [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_pow,
    show (2 : Int).natAbs = 2 from rfl] at hn
  have hqz : q.natAbs = 0 := crt_core p.natAbs q.natAbs hn
  exact Int.natAbs_eq_zero.mp hqz

/-! ## crt-4: ℚ 版（本物の QRat 上） -/

/-- ℚ の 2（M115F の `ratRing` の乗法単位を 2 倍した本物の有理数 2 = 2/1）。 -/
def ratOfTwo : QRat := Quot.mk ratRel ⟨2, 1, by omega⟩

/-- 積を 3 乗へ整える補助（Int）。 -/
theorem crt_int_cube (t : Int) : t * t * t = t ^ 3 := by
  rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

/-- **crt-4: ℚ 版** — 任意の有理数 `r : QRat` に対し `r³ ≠ 2`
    （`ratRing.mul (ratRing.mul r r) r ≠ ratOfTwo`）。
    代表 `r = x.num/x.den` に落とし、分離性 `quot_exact_rat` で交差積
    `x.num³ = 2·x.den³` を得て `crt_no_int_cube_eq`（`x.den ≠ 0`）で否定。 -/
theorem crt_no_rat_cube (r : QRat) :
    ratRing.mul (ratRing.mul r r) r ≠ ratOfTwo := by
  induction r using Quot.ind with
  | _ x =>
    intro h
    -- h : mk (prMul (prMul x x) x) = ratOfTwo（定義展開）
    have hr : ratRel (prMul (prMul x x) x) ⟨2, 1, by omega⟩ := quot_exact_rat h
    -- ratRel を展開: (x.num*x.num*x.num) * 1 = 2 * (x.den*x.den*x.den)
    have hr2 : x.num * x.num * x.num * 1 = 2 * (x.den * x.den * x.den) := hr
    rw [Int.mul_one, crt_int_cube x.num, crt_int_cube x.den] at hr2
    exact crt_no_int_cube_eq x.num x.den (by
      intro hz
      have hp := x.den_pos
      rw [hz] at hp
      exact absurd hp (by omega)) hr2

/-! ## crt-5: 系 — 2 は ℚ の三乗元でない -/

/-- **crt-5: 既約性の基礎** — 2 は ℚ の三乗元でない
    （x³ − 2 は ℚ 上に根を持たない ⟹ ℚ[x]/(x³−2) が体を成す最下層の入力）。 -/
theorem crt_two_not_cube :
    ¬ ∃ r : QRat, ratRing.mul (ratRing.mul r r) r = ratOfTwo := by
  intro hex
  obtain ⟨r, hr⟩ := hex
  exact crt_no_rat_cube r hr

end IUT
