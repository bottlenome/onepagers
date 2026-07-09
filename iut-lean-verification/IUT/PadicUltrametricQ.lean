/-
  IUT/PadicUltrametricQ.lean — p 進超距離不等式の土台（Nat/Int 整除形 → PreRat 持ち上げ）

  分類: [実] / 本物建設(b)。
  complete_pct 影響: A3（Φ_9 の Eisenstein 既約性 → ℚ(ζ_9) 構成）への
    承認済み足場（設計書 audit/A3-cyclotomic-tower-detail-2026-07-09.md §1.2 E1）。
    実 p 進付値 v_p : ℚ^× → ℤ（PadicValuationQ の本物構成）の上に、
    超距離（非アルキメデス）不等式 v_p(x+y) ≥ min(v_p x, v_p y) と
    強三角等号 v_p(x) < v_p(y) ⟹ v_p(x+y) = v_p(x) を本物証明する。
    一般 p 進超距離判定器であり、Eisenstein 判定（E3）だけでなく他の
    既約性・付値論にも再利用できる。本ファイル単体では complete_pct 未設定
    （E3/E4′ で Φ_9 まで繋いだ時点で実 IUT 完全証明率に反映）。

  設計書 §1.2 E1 の推奨どおり **Int 上の別動線**を採る:
  超距離の核は自然数の「p^k ∣ n ⟺ k ≤ v_p(n)」整除特徴付けにあり、
  有理数（PreRat 代表）の符号付き分子は natAbs 橋 `pum_int_dvd_iff_natAbs`
  1 本で Nat の整除に落とす。これにより Int 符号分岐の泥を最小化する。

  * Nat/Int 整除形（設計 E1 最小セット）:
    - `pum_pow_dvd_pow`   — k ≤ a なら p^k ∣ p^a。
    - `pum_pow_dvd_of_le` — k ≤ v_p(n) なら p^k ∣ n（n ≥ 1）。
    - `pum_le_of_pow_dvd` — p^k ∣ n なら k ≤ v_p(n)（逆向き、p∤n' で矛盾）。
    - `pum_natval_add_ge` — k ≤ v_p(m) ∧ k ≤ v_p(n) ⟹ k ≤ v_p(m+n)。
  * Int 橋・積:
    - `pum_int_dvd_iff_natAbs` — (p^k:ℤ) ∣ a ⟺ p^k ∣ |a|。
    - `pum_int_natval_mul` — v_p(|a·b|) = v_p(|a|)+v_p(|b|)（a,b ≠ 0）。
  * PreRat 持ち上げ（設計 §1.2 後半、到達済み）:
    - `pum_add_num_lb` — 加法の分子 num₁den₂+num₂den₁ の下界補題。
    - `pum_val_add_ge` — 任意の下界 k ≤ v_p x ∧ k ≤ v_p y ⟹ k ≤ v_p(x+y)
      （min 形と同値な「全 k」形。非零分子 3 つ仮定）。
    - `pum_val_add_ge_min` — v_p(x+y) ≥ min(v_p x, v_p y)（超距離不等式）。
    - `pum_val_add_eq` — v_p x < v_p y ⟹ v_p(x+y) = v_p x（強三角等号）。

  正直な限定（到達範囲）:
  - Nat/Int 版・PreRat 持ち上げ（ge_min・強三角等号）まで**全て到達**した。
    設計書は「PreRat 持ち上げが予算内で難しければ Nat/Int 版で止めてよい」と
    していたが、`prAdd_assoc`/`prNeg_add_rel`/`ratRel_add_left` 等の既存代表演算
    補題を再利用して x = (x+y)+(−y) の ratRel 分解を作ることで、強三角等号まで
    本物で閉じられた（多項式恒等式を手展開せず ring も使わずに達成）。
  - 付値は非零元のみ（v_p(0) = +∞ は ℤ に収まらない）。`pum_val_add_eq` は
    x, y, x+y の分子非零を仮定する（付値が定義される定義域内での主張）。
  - well-defined 移送（`pum_val_add_eq` 内）は既存 `pvq_val_wd`（choice 不使用・
    非零代表）に委譲。ratRel 商 QRat 全域への Quot.lift は §1.2 E2 の担当。

  全て選択公理不使用（propext, Quot.sound のみ）・sorry なし。§2(b) 本物建設。
-/
import IUT.PadicAbsValueQ

namespace IUT

/-! ## Nat 整除形の超距離土台（設計 E1 最小セット） -/

/-- **冪の整除単調性** — k ≤ a なら p^k ∣ p^a（p^a = p^k · p^(a−k)）。 -/
theorem pum_pow_dvd_pow (p k a : Nat) (h : k ≤ a) : p ^ k ∣ p ^ a := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  refine ⟨p ^ d, ?_⟩
  rw [← hd, Nat.pow_add]

/-- **順方向** — k ≤ v_p(n) なら p^k ∣ n（n ≥ 1）。
    prime_pow_extract で n = p^a·n'（p∤n'）と分解し pvqNatVal_spec で v_p(n)=a。
    k ≤ a から p^k ∣ p^a ∣ p^a·n' = n。 -/
theorem pum_pow_dvd_of_le (p : Nat) (hp : IsPrime p) (n k : Nat) (hn : 1 ≤ n)
    (h : k ≤ pvqNatVal p n) : p ^ k ∣ n := by
  have hp2 : 2 ≤ p := hp.1
  obtain ⟨a, n', hne, hn'⟩ := prime_pow_extract p hp n hn
  have hn'pos : 1 ≤ n' := by
    cases Nat.eq_zero_or_pos n' with
    | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hne; omega
    | inr hpos => exact hpos
  have hval : pvqNatVal p n = a := by
    rw [hne]; exact pvqNatVal_spec p hp2 a n' hn' hn'pos
  have hka : k ≤ a := by rw [hval] at h; exact h
  rw [hne]
  exact Nat.dvd_trans (pum_pow_dvd_pow p k a hka) (Nat.dvd_mul_right (p ^ a) n')

/-- **逆方向** — p^k ∣ n なら k ≤ v_p(n)（n ≥ 1）。
    v_p(n)=a とし k > a を仮定すると p^(a+1) ∣ p^a·n' から p^a を約分して
    p ∣ n' を得るが p∤n' に矛盾。 -/
theorem pum_le_of_pow_dvd (p : Nat) (hp : IsPrime p) (n k : Nat) (hn : 1 ≤ n)
    (h : p ^ k ∣ n) : k ≤ pvqNatVal p n := by
  have hp2 : 2 ≤ p := hp.1
  obtain ⟨a, n', hne, hn'⟩ := prime_pow_extract p hp n hn
  have hn'pos : 1 ≤ n' := by
    cases Nat.eq_zero_or_pos n' with
    | inl h0 => exfalso; rw [h0, Nat.mul_zero] at hne; omega
    | inr hpos => exact hpos
  have hval : pvqNatVal p n = a := by
    rw [hne]; exact pvqNatVal_spec p hp2 a n' hn' hn'pos
  rw [hval]
  cases Nat.lt_or_ge a k with
  | inr hge => exact hge
  | inl hlt =>
    exfalso
    have hak : a + 1 ≤ k := hlt
    have hd1 : p ^ (a + 1) ∣ p ^ k := pum_pow_dvd_pow p (a + 1) k hak
    have hd2 : p ^ (a + 1) ∣ n := Nat.dvd_trans hd1 h
    rw [hne] at hd2
    obtain ⟨t, ht⟩ := hd2
    rw [Nat.pow_succ, Nat.mul_assoc] at ht
    have hpapos : 0 < p ^ a := Nat.pow_pos (by omega)
    have hn'eq : n' = p * t := Nat.eq_of_mul_eq_mul_left hpapos ht
    exact hn' ⟨t, hn'eq⟩

/-- **加法の超距離（Nat 版）** — k ≤ v_p(m) ∧ k ≤ v_p(n) ⟹ k ≤ v_p(m+n)。
    p^k ∣ m ∧ p^k ∣ n ⟹ p^k ∣ (m+n)（Nat.dvd_add）＋ 逆方向。 -/
theorem pum_natval_add_ge (p : Nat) (hp : IsPrime p) (m n k : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : 1 ≤ m + n)
    (h : k ≤ pvqNatVal p m) (h' : k ≤ pvqNatVal p n) :
    k ≤ pvqNatVal p (m + n) := by
  have hdm : p ^ k ∣ m := pum_pow_dvd_of_le p hp m k hm h
  have hdn : p ^ k ∣ n := pum_pow_dvd_of_le p hp n k hn h'
  have hdmn : p ^ k ∣ (m + n) := Nat.dvd_add hdm hdn
  exact pum_le_of_pow_dvd p hp (m + n) k hmn hdmn

/-! ## Int 橋（設計推奨の別動線）: 符号を natAbs で潰す -/

/-- **natAbs 橋** — (p^k : ℤ) ∣ a ⟺ p^k ∣ |a|。
    Int.natAbs_dvd_natAbs と natCast の natAbs = 自身で往復。 -/
theorem pum_int_dvd_iff_natAbs (p k : Nat) (a : Int) :
    ((p ^ k : Nat) : Int) ∣ a ↔ (p ^ k) ∣ a.natAbs := by
  constructor
  · intro h
    have h2 : ((p ^ k : Nat) : Int).natAbs ∣ a.natAbs :=
      Int.natAbs_dvd_natAbs.mpr h
    rw [Int.natAbs_natCast] at h2
    exact h2
  · intro h
    have h2 : ((p ^ k : Nat) : Int).natAbs ∣ a.natAbs := by
      rw [Int.natAbs_natCast]; exact h
    exact Int.natAbs_dvd_natAbs.mp h2

/-- **Int 積の付値加法性** — a,b ≠ 0 で v_p(|a·b|) = v_p(|a|)+v_p(|b|)。
    Int.natAbs_mul で |a·b| = |a|·|b| に開き pvq_natval_mul。 -/
theorem pum_int_natval_mul (p : Nat) (hp : IsPrime p) (a b : Int)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    pvqNatVal p (a * b).natAbs
      = pvqNatVal p a.natAbs + pvqNatVal p b.natAbs := by
  have hap : 1 ≤ a.natAbs := natAbs_pos_of_ne ha
  have hbp : 1 ≤ b.natAbs := natAbs_pos_of_ne hb
  have hmul : (a * b).natAbs = a.natAbs * b.natAbs := Int.natAbs_mul a b
  rw [hmul]
  exact pvq_natval_mul p hp a.natAbs b.natAbs hap hbp

/-! ## PreRat 加法への持ち上げ -/

/-- **加法分子の下界補題** — j が交差積 num₁den₂ と num₂den₁ の両付値以下なら
    j ≤ v_p(|(x+y).num|)。両交差積を p^j で割り Int で足して natAbs へ戻す。 -/
theorem pum_add_num_lb (p : Nat) (hp : IsPrime p) (x y : PreRat)
    (hx : x.num ≠ 0) (hy : y.num ≠ 0) (hxy : (prAdd x y).num ≠ 0) (j : Nat)
    (h1 : j ≤ pvqNatVal p x.num.natAbs + pvqNatVal p y.den.natAbs)
    (h2 : j ≤ pvqNatVal p y.num.natAbs + pvqNatVal p x.den.natAbs) :
    j ≤ pvqNatVal p (prAdd x y).num.natAbs := by
  have hBne : x.den ≠ 0 := by have := x.den_pos; omega
  have hDne : y.den ≠ 0 := by have := y.den_pos; omega
  -- 第 1 項 x.num·y.den の付値と整除
  have hv1 : pvqNatVal p (x.num * y.den).natAbs
           = pvqNatVal p x.num.natAbs + pvqNatVal p y.den.natAbs :=
    pum_int_natval_mul p hp x.num y.den hx hDne
  have ht1pos : 1 ≤ (x.num * y.den).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_pos (natAbs_pos_of_ne hx) (natAbs_pos_of_ne hDne)
  have hd1n : p ^ j ∣ (x.num * y.den).natAbs :=
    pum_pow_dvd_of_le p hp (x.num * y.den).natAbs j ht1pos (by rw [hv1]; exact h1)
  -- 第 2 項 y.num·x.den の付値と整除
  have hv2 : pvqNatVal p (y.num * x.den).natAbs
           = pvqNatVal p y.num.natAbs + pvqNatVal p x.den.natAbs :=
    pum_int_natval_mul p hp y.num x.den hy hBne
  have ht2pos : 1 ≤ (y.num * x.den).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_pos (natAbs_pos_of_ne hy) (natAbs_pos_of_ne hBne)
  have hd2n : p ^ j ∣ (y.num * x.den).natAbs :=
    pum_pow_dvd_of_le p hp (y.num * x.den).natAbs j ht2pos (by rw [hv2]; exact h2)
  -- Int へ持ち上げて和を取り natAbs へ戻す
  have hd1i : ((p ^ j : Nat) : Int) ∣ (x.num * y.den) :=
    (pum_int_dvd_iff_natAbs p j (x.num * y.den)).mpr hd1n
  have hd2i : ((p ^ j : Nat) : Int) ∣ (y.num * x.den) :=
    (pum_int_dvd_iff_natAbs p j (y.num * x.den)).mpr hd2n
  have hsum : ((p ^ j : Nat) : Int) ∣ (x.num * y.den + y.num * x.den) :=
    Int.dvd_add hd1i hd2i
  have hnumeq : (prAdd x y).num = x.num * y.den + y.num * x.den := rfl
  have hdsum : ((p ^ j : Nat) : Int) ∣ (prAdd x y).num := by
    rw [hnumeq]; exact hsum
  have hdn : p ^ j ∣ (prAdd x y).num.natAbs :=
    (pum_int_dvd_iff_natAbs p j (prAdd x y).num).mp hdsum
  have hnpos : 1 ≤ (prAdd x y).num.natAbs := natAbs_pos_of_ne hxy
  exact pum_le_of_pow_dvd p hp (prAdd x y).num.natAbs j hnpos hdn

/-- **超距離（全 k 形）** — k ≤ v_p x ∧ k ≤ v_p y ⟹ k ≤ v_p(x+y)。
    交差積のどちらの付値が小さいかで場合分けし、その方を下界 j に取って
    pum_add_num_lb を発火、分母付値 v_p(den·den)=v_p den+v_p den を差し引く。 -/
theorem pum_val_add_ge (p : Nat) (hp : IsPrime p) (x y : PreRat)
    (hx : x.num ≠ 0) (hy : y.num ≠ 0) (hxy : (prAdd x y).num ≠ 0)
    (k : Int) (hkx : k ≤ pvqVal p x) (hky : k ≤ pvqVal p y) :
    k ≤ pvqVal p (prAdd x y) := by
  have hBne : x.den ≠ 0 := by have := x.den_pos; omega
  have hDne : y.den ≠ 0 := by have := y.den_pos; omega
  -- 分母の付値: v_p(|(x+y).den|) = v_p(|x.den|) + v_p(|y.den|)
  have hden : pvqNatVal p (prAdd x y).den.natAbs
            = pvqNatVal p x.den.natAbs + pvqNatVal p y.den.natAbs := by
    show pvqNatVal p (x.den * y.den).natAbs = _
    exact pum_int_natval_mul p hp x.den y.den hBne hDne
  have hvx : pvqVal p x
    = (pvqNatVal p x.num.natAbs : Int) - (pvqNatVal p x.den.natAbs : Int) := rfl
  have hvy : pvqVal p y
    = (pvqNatVal p y.num.natAbs : Int) - (pvqNatVal p y.den.natAbs : Int) := rfl
  have hvxy : pvqVal p (prAdd x y)
    = (pvqNatVal p (prAdd x y).num.natAbs : Int)
      - (pvqNatVal p (prAdd x y).den.natAbs : Int) := rfl
  cases Nat.le_total (pvqNatVal p x.num.natAbs + pvqNatVal p y.den.natAbs)
                     (pvqNatVal p y.num.natAbs + pvqNatVal p x.den.natAbs) with
  | inl hle =>
    have hlb := pum_add_num_lb p hp x y hx hy hxy
        (pvqNatVal p x.num.natAbs + pvqNatVal p y.den.natAbs) (Nat.le_refl _) hle
    rw [hvxy, hden]
    rw [hvx] at hkx
    omega
  | inr hle =>
    have hlb := pum_add_num_lb p hp x y hx hy hxy
        (pvqNatVal p y.num.natAbs + pvqNatVal p x.den.natAbs) hle (Nat.le_refl _)
    rw [hvxy, hden]
    rw [hvy] at hky
    omega

/-- **超距離不等式** — v_p(x+y) ≥ min(v_p x, v_p y)（非零分子 3 つ）。
    全 k 形に k := min を代入（Int.min_le_left/right）。 -/
theorem pum_val_add_ge_min (p : Nat) (hp : IsPrime p) (x y : PreRat)
    (hx : x.num ≠ 0) (hy : y.num ≠ 0) (hxy : (prAdd x y).num ≠ 0) :
    pvqVal p (prAdd x y) ≥ min (pvqVal p x) (pvqVal p y) :=
  pum_val_add_ge p hp x y hx hy hxy (min (pvqVal p x) (pvqVal p y))
    (Int.min_le_left _ _) (Int.min_le_right _ _)

/-! ## 強三角等号: v_p x < v_p y ⟹ v_p(x+y) = v_p x -/

/-- **反元の付値不変** — v_p(−y) = v_p(y)（分子は natAbs 同一、分母不変）。 -/
theorem pum_val_neg (p : Nat) (y : PreRat) :
    pvqVal p (prNeg y) = pvqVal p y := by
  show (pvqNatVal p (prNeg y).num.natAbs : Int)
       - (pvqNatVal p (prNeg y).den.natAbs : Int)
     = (pvqNatVal p y.num.natAbs : Int) - (pvqNatVal p y.den.natAbs : Int)
  have hn : (prNeg y).num.natAbs = y.num.natAbs := by
    show (-y.num).natAbs = y.num.natAbs
    exact Int.natAbs_neg y.num
  have hd : (prNeg y).den.natAbs = y.den.natAbs := rfl
  rw [hn, hd]

/-- **(x+y)+(−y) は x に ratRel 同値** — prAdd_assoc・prNeg_add_rel・
    ratRel_add_left の合成（多項式恒等式の手展開・ring 不使用）。 -/
theorem pum_rel_add_sub (x y : PreRat) :
    ratRel (prAdd (prAdd x y) (prNeg y)) x := by
  have e1 : prAdd (prAdd x y) (prNeg y) = prAdd x (prAdd y (prNeg y)) :=
    prAdd_assoc x y (prNeg y)
  have e2 : prAdd y (prNeg y) = prAdd (prNeg y) y := prAdd_comm y (prNeg y)
  have e3 : ratRel (prAdd (prNeg y) y) prZero := prNeg_add_rel y
  have e4 : ratRel (prAdd y (prNeg y)) prZero := by rw [e2]; exact e3
  have e5 : ratRel (prAdd x (prAdd y (prNeg y))) (prAdd x prZero) :=
    ratRel_add_left x e4
  have e6 : prAdd x prZero = x := by rw [prAdd_comm x prZero]; exact prZero_add x
  rw [e1]
  rw [e6] at e5
  exact e5

/-- **強三角等号** — v_p x < v_p y ⟹ v_p(x+y) = v_p x（非零分子 3 つ）。
    下界は全 k 形（k := v_p x）。上界は x = (x+y)+(−y) の ratRel を pvq_val_wd で
    移送し v_p((x+y)+(−y)) = v_p x、これに超距離を効かせて v_p(x+y) ≤ v_p x。 -/
theorem pum_val_add_eq (p : Nat) (hp : IsPrime p) (x y : PreRat)
    (hx : x.num ≠ 0) (hy : y.num ≠ 0) (hxy : (prAdd x y).num ≠ 0)
    (h : pvqVal p x < pvqVal p y) :
    pvqVal p (prAdd x y) = pvqVal p x := by
  -- 下界: v_p x ≤ v_p(x+y)
  have hge : pvqVal p x ≤ pvqVal p (prAdd x y) :=
    pum_val_add_ge p hp x y hx hy hxy (pvqVal p x) (Int.le_refl _) (Int.le_of_lt h)
  -- 反元の非零・付値
  have hnegy : (prNeg y).num ≠ 0 := by
    show -y.num ≠ 0
    intro h0; exact hy (by omega)
  have hvneg : pvqVal p (prNeg y) = pvqVal p y := pum_val_neg p y
  -- (x+y)+(−y) ~ x と非零
  have hrel : ratRel (prAdd (prAdd x y) (prNeg y)) x := pum_rel_add_sub x y
  have hcne : (prAdd (prAdd x y) (prNeg y)).num ≠ 0 := by
    intro h0
    have hr : (prAdd (prAdd x y) (prNeg y)).num * x.den
            = x.num * (prAdd (prAdd x y) (prNeg y)).den := hrel
    rw [h0, Int.zero_mul] at hr
    have hcd : 0 < (prAdd (prAdd x y) (prNeg y)).den :=
      (prAdd (prAdd x y) (prNeg y)).den_pos
    have hz : x.num * (prAdd (prAdd x y) (prNeg y)).den = 0 := hr.symm
    cases Int.mul_eq_zero.mp hz with
    | inl hh => exact hx hh
    | inr hh => omega
  -- 付値移送: v_p((x+y)+(−y)) = v_p x
  have hceq : pvqVal p (prAdd (prAdd x y) (prNeg y)) = pvqVal p x :=
    pvq_val_wd p hp (prAdd (prAdd x y) (prNeg y)) x hcne hx hrel
  -- 上界: v_p(x+y) と v_p y の大小で場合分け
  cases Int.le_total (pvqVal p (prAdd x y)) (pvqVal p y) with
  | inl hle =>
    have hup : pvqVal p (prAdd x y)
             ≤ pvqVal p (prAdd (prAdd x y) (prNeg y)) :=
      pum_val_add_ge p hp (prAdd x y) (prNeg y) hxy hnegy hcne
        (pvqVal p (prAdd x y)) (Int.le_refl _) (by rw [hvneg]; exact hle)
    rw [hceq] at hup
    omega
  | inr hle =>
    have hup : pvqVal p y ≤ pvqVal p (prAdd (prAdd x y) (prNeg y)) :=
      pum_val_add_ge p hp (prAdd x y) (prNeg y) hxy hnegy hcne
        (pvqVal p y) hle (by rw [hvneg]; exact Int.le_refl _)
    rw [hceq] at hup
    omega

end IUT
