/-
  IUT/Zp3Complete.lean — A2b（柱A2: 実 p 進局所体 — 実 ℤ₃ の完備性）

  ── 主要成果の分類: **[実／本物建設(b)]**。既存の実 ℤ₃ = lim ℤ/3ⁿ（M27 逆極限環・
     A2a Zp3ValuationRing の付値関係 z3vGe）と実 ℚ 側 p 進付値 pvq（PadicValuationQ・
     本物の v₃ : ℚ^× → ℤ）の上に、「ℤ₃ は ℤ の 3 進完備化」という**関係ごと**の
     本物の内容——modulus 形の完備性（Cauchy 列の極限の存在・収束・一意性）・
     ℤ の稠密性・実 v₃ との一致——をゼロから建設する。toy 主語なし。主語は実 zpRing 3。

  complete_pct 影響: **A2 A2b を前進**（設計見込み A2 0.55→0.60）。A2 タイトルの
    「完備化」が初めて定理になる: modulus 付き Cauchy 列 (x, M) の極限が閉じた式
    （レベルごと (x (M' n)).val n）で choice-free に構成でき、レベルごとに収束する。
    さらに z3c_val_compat が「既存の p 進付値機構（本物 pvq）と完備化体（実 ℤ₃）の境界」を
    接着する: 整数 a の実 v₃(|a|) = ℤ₃ 内での 3 進付値 z3vExact(toZp a)。

  * z3c-1 `z3cIsModCauchy` / `z3cModUp`   — modulus 付き Cauchy 列と modulus の単調化
  * z3c-2 `z3cModUp_ge` / `z3cModUp_mono` — 単調化 modulus の基本性質（choice-free）
  * z3c-3 `z3cLim`                        — **極限（整合族＝ℤ₃ の元・レベルごと閉じた式）**
  * z3c-4 `z3c_converges`                 — **★極限収束（レベルごと v(xᵢ − lim) ≥ n）**
  * z3c-5 `z3c_sub_eq` / `z3c_lim_unique` — 分離性による極限の一意性
  * z3c-6 `z3c_int_dense`                 — **ℤ は ℤ₃ で稠密**（witness = x.val n の代表）
  * z3c-7 `z3c_val_compat`                — **★実 v₃(|a|) = z3vExact(toZp a)（付値機構と
                                            完備化体の境界接着）**

  正直な限定（§3 準拠・消さない）:
  - **完備性は modulus 形のみが本物**: modulus M : Nat → Nat を入力データとして持つ
    Cauchy 列 (x, M) の極限・収束・一意性は閉じた式で choice ゼロ（§3.2 (A) 採用）。
    ∃ 形 Cauchy（∀n∃N…）からの modulus 抽出は可算選択（≒排中律断片）で choice-free に
    書けないため**後続**とし、本ファイルでは主張しない。この限定は消去・弱化しない。
  - **位相的完備性そのもの**（全 Cauchy フィルターの収束）は範囲外。位相の実体は既設
    `limitTopology (padicSystem 3)`（コンパクト性 Zp_compact も既設）。
  - **p = 3 固定**（付値関係・Cauchy 機構は zpRing p 一般でも書けるが、実 pvq との接着
    z3c_val_compat と実例は p=3 で確立）。基礎体は ℚ のみ（一般数体 K_v は後続）。
  - 実 ℤ₃・実 pvq は既存（新設せず消費）。既存 surrogate は消さない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
-/
import IUT.Zp3ValuationRing
import IUT.PadicValuationQ

namespace IUT

/-! ## z3c-1: modulus 付き Cauchy 列 -/

/-- **z3c-1a: modulus 付き Cauchy 列** — 各レベル n に対し、添字が modulus M n 以上の
    2 項のレベル n 成分が一致する（設計 §4 のレベル一致形。z3vGe (xᵢ−xⱼ) n と同値）。
    modulus M は入力データ（∃ 形 Cauchy の可算選択を回避する choice-free 版）。 -/
def z3cIsModCauchy (x : Nat → z3.carrier) (M : Nat → Nat) : Prop :=
  ∀ n i j, M n ≤ i → M n ≤ j → (x i).val n = (x j).val n

/-- **z3c-1b: modulus の単調化** M' n := max (M n) (M' (n−1))。極限の整合性証明に
    「n レベルは M' n 以降で確定・M' は単調」を保証する（閉じた再帰・choice ゼロ）。 -/
def z3cModUp (M : Nat → Nat) : Nat → Nat
  | 0 => M 0
  | n + 1 => Nat.max (M (n + 1)) (z3cModUp M n)

/-! ## z3c-2: 単調化 modulus の基本性質 -/

/-- **z3c-2a: M n ≤ M' n**（各レベルで元の modulus を上回る）。 -/
theorem z3cModUp_ge (M : Nat → Nat) (n : Nat) : M n ≤ z3cModUp M n := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ n => exact Nat.le_max_left _ _

/-- 単調化 M' の 1 段昇り。 -/
theorem z3cModUp_step (M : Nat → Nat) (n : Nat) :
    z3cModUp M n ≤ z3cModUp M (n + 1) := Nat.le_max_right _ _

/-- **z3c-2b: M' は単調**（i ≤ j なら M' i ≤ M' j）。 -/
theorem z3cModUp_mono (M : Nat → Nat) {i j : Nat} (h : i ≤ j) :
    z3cModUp M i ≤ z3cModUp M j := by
  induction j with
  | zero =>
    have hi : i = 0 := Nat.le_zero.mp h
    exact Nat.le_of_eq (congrArg (z3cModUp M) hi)
  | succ j ih =>
    cases Nat.lt_or_ge i (j + 1) with
    | inl hlt =>
      have hij : i ≤ j := Nat.lt_succ_iff.mp hlt
      exact Nat.le_trans (ih hij) (z3cModUp_step M j)
    | inr hge =>
      have heq : i = j + 1 := Nat.le_antisymm h hge
      exact Nat.le_of_eq (congrArg (z3cModUp M) heq)

/-! ## z3c-3: 極限（整合族＝ℤ₃ の元・レベルごと閉じた式） -/

/-- **z3c-3（★中核）: modulus 付き Cauchy 列の極限** — レベル n 成分を
    (x (M' n)).val n（閉じた式・choice ゼロ）で与える。これが整合族（＝実 ℤ₃ の元）
    であることは、i ≤ j に対し (x (M' j)) の整合性で n=i 成分を落とし、i レベルの
    Cauchy 性（M' i, M' j がともに M i 以上）で (x (M' j)).val i = (x (M' i)).val i を
    得て閉じる（成分計算のみ・新規 choice なし）。 -/
def z3cLim (x : Nat → z3.carrier) (M : Nat → Nat) (h : z3cIsModCauchy x M) :
    z3.carrier :=
  ⟨fun n => (x (z3cModUp M n)).val n, by
    intro i j hij
    have hprop := (x (z3cModUp M j)).property hij
    have hcau := h i (z3cModUp M j) (z3cModUp M i)
      (Nat.le_trans (z3cModUp_ge M i) (z3cModUp_mono M hij)) (z3cModUp_ge M i)
    show ((padicSystem 3).t hij).map ((x (z3cModUp M j)).val j)
       = (x (z3cModUp M i)).val i
    rw [hprop]
    exact hcau⟩

/-! ## z3c-4: 極限収束（レベルごと） -/

/-- **z3c-4（★）: 極限収束** — 添字 i が M' n 以上なら v(xᵢ − lim) ≥ n。
    レベル n で (x i).val n = (x (M' n)).val n = lim.val n（Cauchy 性・M n ≤ M' n ≤ i）
    となり、差の成分が mul c (inv c) = 0 に潰れる。減算の成分簿記のみ・choice ゼロ。 -/
theorem z3c_converges (x : Nat → z3.carrier) (M : Nat → Nat)
    (h : z3cIsModCauchy x M) :
    ∀ n i, z3cModUp M n ≤ i →
      z3vGe 3 (z3.add (x i) (z3.neg (z3cLim x M h))) n := by
  intro n i hi
  have key : (x i).val n = (x (z3cModUp M n)).val n :=
    h n i (z3cModUp M n) (Nat.le_trans (z3cModUp_ge M n) hi) (z3cModUp_ge M n)
  show (zmod (3 ^ n)).mul ((x i).val n)
      ((zmod (3 ^ n)).inv ((x (z3cModUp M n)).val n))
    = Quot.mk (modCong (3 ^ n)).rel 0
  rw [key]
  exact Grp.mul_inv (zmod (3 ^ n)) ((x (z3cModUp M n)).val n)

/-! ## z3c-5: 極限の一意性（分離性） -/

/-- **z3c-5a: 差の付値 ≥ n はレベル n 成分の一致を与える** — v(a − b) ≥ n ↔ aₙ = bₙ の
    forward。mul aₙ (inv bₙ) = one と mul bₙ (inv bₙ) = one を右簡約。 -/
theorem z3c_sub_eq {a b : z3.carrier} {n : Nat}
    (h : z3vGe 3 (z3.add a (z3.neg b)) n) : a.val n = b.val n := by
  have h' : (zmod (3 ^ n)).mul (a.val n) ((zmod (3 ^ n)).inv (b.val n))
      = (zmod (3 ^ n)).one := h
  have hb : (zmod (3 ^ n)).mul (b.val n) ((zmod (3 ^ n)).inv (b.val n))
      = (zmod (3 ^ n)).one := Grp.mul_inv (zmod (3 ^ n)) (b.val n)
  exact Grp.mul_right_cancel (zmod (3 ^ n)) (Eq.trans h' hb.symm)

/-- **z3c-5b: 極限の一意性** — 同じ列に収束する 2 元は一致（分離性 = ℤ₃ が Hausdorff）。
    ∃ 形の収束仮定は Prop 消費（obtain）のみで、極限構成に choice を持ち込まない。 -/
theorem z3c_lim_unique (x : Nat → z3.carrier) (l l' : z3.carrier)
    (hl : ∀ n, ∃ N, ∀ i, N ≤ i → z3vGe 3 (z3.add (x i) (z3.neg l)) n)
    (hl' : ∀ n, ∃ N, ∀ i, N ≤ i → z3vGe 3 (z3.add (x i) (z3.neg l')) n) :
    l = l' := by
  apply Subtype.ext
  funext n
  obtain ⟨N, hN⟩ := hl n
  obtain ⟨N', hN'⟩ := hl' n
  have h1 := z3c_sub_eq (hN (Nat.max N N') (Nat.le_max_left N N'))
  have h2 := z3c_sub_eq (hN' (Nat.max N N') (Nat.le_max_right N N'))
  show l.val n = l'.val n
  rw [← h1]
  exact h2

/-! ## z3c-6: ℤ は ℤ₃ で稠密 -/

/-- **z3c-6: ℤ の稠密性** — 任意の x ∈ ℤ₃ と精度 n に対し、v(x − toZp a) ≥ n となる
    整数 a が存在する（witness = x.val n の任意の代表）。これで ℤ₃ は「ℤ の 3 進完備化」の
    残り半分（ℤ の像が稠密）を満たす。choice ゼロ（Quot.exists_rep は Prop 消費）。 -/
theorem z3c_int_dense (x : z3.carrier) (n : Nat) :
    ∃ a : Int, z3vGe 3 (z3.add x (z3.neg ((toZp 3).map a))) n := by
  obtain ⟨a, ha⟩ := Quot.exists_rep (x.val n)
  refine ⟨a, ?_⟩
  have hc : ((toZp 3).map a).val n = x.val n := ha
  show (zmod (3 ^ n)).mul (x.val n) ((zmod (3 ^ n)).inv (((toZp 3).map a).val n))
    = Quot.mk (modCong (3 ^ n)).rel 0
  rw [hc]
  exact Grp.mul_inv (zmod (3 ^ n)) (x.val n)

/-! ## z3c-7: 実 v₃ との一致（付値機構と完備化体の境界接着） -/

/-- **z3c-7（★）: 実 pvq 付値と ℤ₃ 内付値の一致** — 非零整数 a に対し、実 ℚ 側の
    本物の 3 進付値 v₃(|a|) = pvqNatVal 3 a.natAbs が、実 ℤ₃ 内での 3 進付値
    z3vExact(toZp a) と一致する。a.natAbs = 3^k·m'（3∤m'）に prime_pow_extract で開き、
    pvqNatVal_spec で左辺 = k、右辺は toZp a のレベル成分の 3^k 整除（成立）と
    3^(k+1) 非整除（3∤m' から矛盾）を Int↔Nat 整除の橋渡しで示す。
    ——依頼文の「既存の p 進付値機構（本物 pvq）と完備化体（実 ℤ₃）の境界」を接着する定理。 -/
theorem z3c_val_compat (a : Int) (ha : a ≠ 0) :
    z3vExact 3 ((toZpRing 3).map a) (pvqNatVal 3 a.natAbs) := by
  have hp : IsPrime 3 := isPrime_three
  have hpos : 1 ≤ a.natAbs := natAbs_pos_of_ne ha
  obtain ⟨k, m', hfact, hqm'⟩ := prime_pow_extract 3 hp a.natAbs hpos
  have hm'pos : 1 ≤ m' := by
    cases Nat.eq_zero_or_pos m' with
    | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hfact; omega
    | inr hp' => exact hp'
  have hval : pvqNatVal 3 a.natAbs = k := by
    rw [hfact]; exact pvqNatVal_spec 3 (by omega) k m' hqm' hm'pos
  rw [hval]
  refine ⟨?_, ?_⟩
  · -- 3^k ∣ a （成立側）
    show ((toZpRing 3).map a).val k = Quot.mk (modCong (3 ^ k)).rel 0
    show Quot.mk (modCong (3 ^ k)).rel a = Quot.mk (modCong (3 ^ k)).rel 0
    apply Quot.sound
    show ((3 ^ k : Nat) : Int) ∣ a - 0
    have hdnat : (3 ^ k) ∣ a.natAbs := ⟨m', hfact⟩
    have hd2 : ((3 ^ k : Nat) : Int) ∣ (a.natAbs : Int) :=
      Int.ofNat_dvd.mpr hdnat
    have hd3 : ((3 ^ k : Nat) : Int) ∣ a := Int.dvd_natAbs.mp hd2
    obtain ⟨c, hc⟩ := hd3
    exact ⟨c, by omega⟩
  · -- ¬ 3^(k+1) ∣ a （非整除側）
    intro hcon
    have hcon' : Quot.mk (modCong (3 ^ (k + 1))).rel a
        = Quot.mk (modCong (3 ^ (k + 1))).rel 0 := hcon
    have hrel := quot_exact intGrp (modCong (3 ^ (k + 1))) hcon'
    have hdInt : ((3 ^ (k + 1) : Nat) : Int) ∣ a := by
      obtain ⟨c, hc⟩ := hrel
      exact ⟨c, by omega⟩
    have hdNatAbs : ((3 ^ (k + 1) : Nat) : Int) ∣ (a.natAbs : Int) :=
      Int.dvd_natAbs.mpr hdInt
    have hdNat : (3 ^ (k + 1)) ∣ a.natAbs := Int.ofNat_dvd.mp hdNatAbs
    rw [hfact] at hdNat
    rw [Nat.pow_succ] at hdNat
    have h3 : (3 : Nat) ∣ m' :=
      (Nat.mul_dvd_mul_iff_left (Nat.pow_pos (show 0 < 3 by omega))).mp hdNat
    exact hqm' h3

end IUT
