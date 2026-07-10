/-
  IUT/GaussValuationQ.lean — E2: 商 ℚ 上の p 進付値と Eisenstein の最小添字補題

  分類: [実] / 本物建設(b)。
  complete_pct 影響: A3（Φ_9 の Eisenstein 既約性 → ℚ(ζ_9) 構成）への
    承認済み足場（設計書 audit/A3-cyclotomic-tower-detail-2026-07-09.md §1.2 E2）。
    E1（PadicUltrametricQ）で本物構成した超距離不等式
      v_p(x+y) ≥ min(v_p x, v_p y) と 強三角等号 v_p x < v_p y ⟹ v_p(x+y)=v_p x
    を、商体 ℚ = QRat（= Quot ratRel）**全域の実付値 egvValQ** に持ち上げ、
    その上で Eisenstein 判定器 E3 の律速部品である**最小添字補題**
      v_p((g·h)_{i₀+j₀}) = v_p(g_{i₀}) + v_p(h_{j₀})
    を Cauchy 積の超距離帰納で本物証明する。本ファイル単体では complete_pct
    未設定（E3/E4′ で Φ_9 まで繋いだ時点で実 IUT 完全証明率に反映）。

  * (1) 商持ち上げ:
    - `egvValQ` — QRat → ℤ の実 p 進付値（Quot.lift・零類は 0、非零類は pvqVal）。
      wd は E1 系の `pvq_val_wd`（choice 不使用）に委譲。ratRel は片零・片非零を
      排除するので零判定が代表間で well-defined。
    - `egvValQ_mk_zero` / `egvValQ_mk_ne` — 代表計算（零類 / 非零類）。
    - `egvValQ_neg` — v_p(−x) = v_p(x)（pum_val_neg の商版）。
    - `egv_mul_ne_zero` — 非零 2 元の積は非零。
    - `egvValQ_mul` — 加法性 v_p(xy)=v_p(x)+v_p(y)（非零 2 元、pvq_val_mul の商版）。
    - `egvValQ_p` — v_p(p) = 1（pvq_val_p の商版）。
  * (2) 超距離の商版:
    - `egvValQ_add_ge`（全 k 形）/ `egvValQ_add_ge_min`（min 形）/
      `egvValQ_add_eq`（強三角等号）— E1 の pum_val_add_* を egvValQ に持ち上げ。
    - `egv_add_ne_zero_lt` — v_p x < v_p y なら x+y ≠ 0（付値の相異から）。
  * (3) 最小添字補題（Eisenstein の核）:
    - `egvSumAbove` — 各項が「零 or 付値 > V」なら有限和は「零 or 付値 > V」。
    - `egvSumDominant` — 対角に 1 個だけ付値 = V の支配項、他は「零 or > V」なら
      有限和の付値は V（超距離: 強い方＝小さい付値が勝つ、rsum の帰納）。
    - `egv_min_index_mul` — Cauchy 積 (g·h)_{i₀+j₀} の付値 = v(g_{i₀})+v(h_{j₀})。
      対角項 k=i₀ が付値 = 和、対角以外は真に大 or 零（零係数項は
      `rzd_zero_or_ne` で和から除外、Int に +∞ を持ち込まない）。

  正直な限定（到達範囲）:
  - 付値 egvValQ は QRat 全域で total（零類は便宜上 0）だが、加法性・超距離の
    各定理は**非零元のみ**（v_p(0) = +∞ は ℤ に収まらない）で成立する形。
    egvValQ_mul / egvValQ_add_* / egvValQ_p は非零仮定を明示する。
  - 最小添字は「min の存在探索」を書かず、E3 から明示 witness（i₀・j₀ と
    hgmin/hglt/hhmin/hhlt の 4 連言）を受け取る設計（choice 不使用）。IsPoly
    有界性は本補題では不要（有限 Cauchy 和のみに依存）なので仮定に含めない。
  - v_p(p)=1 は `Quot.mk ratRel (intToPreRat (p:Int))`（= ℚ の元 p）上で述べる
    （専用の qOfInt 名は既存資産に無いため直接記述）。

  全て選択公理不使用（propext, Quot.sound のみ）・sorry なし。§2(b) 本物建設。
-/
import IUT.PadicUltrametricQ
import IUT.RatZeroDecide
import IUT.PowerSeries

namespace IUT

/-! ## (1) QRat 上の実 p 進付値（商持ち上げ） -/

/-- **E2-(1): ℚ 上の p 進付値** — QRat = Quot ratRel の全域に、零類は 0、
    非零類は代表の `pvqVal` を割り当てる（Quot.lift）。wd: ratRel a b の下で
    「両零 → 0=0」「両非零 → pvq_val_wd」、片零は ratRel（a.num·b.den=b.num·a.den・
    正分母）が排除する。 -/
def egvValQ (p : Nat) (hp : IsPrime p) : QRat → Int :=
  Quot.lift (fun r => if r.num = 0 then (0 : Int) else pvqVal p r)
    (by
      intro a b hr
      show (if a.num = 0 then (0 : Int) else pvqVal p a)
        = (if b.num = 0 then (0 : Int) else pvqVal p b)
      have he : a.num * b.den = b.num * a.den := hr
      have hapos : 0 < a.den := a.den_pos
      have hbpos : 0 < b.den := b.den_pos
      cases Decidable.em (a.num = 0) with
      | inl ha0 =>
        have hb0 : b.num = 0 := by
          rw [ha0, Int.zero_mul] at he
          cases Int.mul_eq_zero.mp he.symm with
          | inl h => exact h
          | inr h => omega
        rw [if_pos ha0, if_pos hb0]
      | inr ha0 =>
        have hb0 : b.num ≠ 0 := by
          intro h0
          rw [h0, Int.zero_mul] at he
          cases Int.mul_eq_zero.mp he with
          | inl h => exact ha0 h
          | inr h => omega
        rw [if_neg ha0, if_neg hb0]
        exact pvq_val_wd p hp a b ha0 hb0 hr)

/-- 零類の代表計算 — 代表 num = 0 なら egvValQ = 0。 -/
theorem egvValQ_mk_zero (p : Nat) (hp : IsPrime p) (r : PreRat) (h : r.num = 0) :
    egvValQ p hp (Quot.mk ratRel r) = 0 := by
  show (if r.num = 0 then (0 : Int) else pvqVal p r) = 0
  rw [if_pos h]

/-- 非零類の代表計算 — 代表 num ≠ 0 なら egvValQ = pvqVal。 -/
theorem egvValQ_mk_ne (p : Nat) (hp : IsPrime p) (r : PreRat) (h : r.num ≠ 0) :
    egvValQ p hp (Quot.mk ratRel r) = pvqVal p r := by
  show (if r.num = 0 then (0 : Int) else pvqVal p r) = pvqVal p r
  rw [if_neg h]

/-- **反元の付値不変** — v_p(−x) = v_p(x)（pum_val_neg の商版、零類も含む）。 -/
theorem egvValQ_neg (p : Nat) (hp : IsPrime p) (x : QRat) :
    egvValQ p hp (ratRing.neg x) = egvValQ p hp x := by
  induction x using Quot.ind
  rename_i a
  cases Decidable.em (a.num = 0) with
  | inl h0 =>
    have hn0 : (prNeg a).num = 0 := by
      show -a.num = 0
      omega
    show egvValQ p hp (Quot.mk ratRel (prNeg a)) = egvValQ p hp (Quot.mk ratRel a)
    rw [egvValQ_mk_zero p hp (prNeg a) hn0, egvValQ_mk_zero p hp a h0]
  | inr h0 =>
    have hn0 : (prNeg a).num ≠ 0 := by
      show -a.num ≠ 0
      intro h
      exact h0 (by omega)
    show egvValQ p hp (Quot.mk ratRel (prNeg a)) = egvValQ p hp (Quot.mk ratRel a)
    rw [egvValQ_mk_ne p hp (prNeg a) hn0, egvValQ_mk_ne p hp a h0]
    exact pum_val_neg p a

/-- **非零 2 元の積は非零** — 代表 num の積 a.num·b.num が非零。 -/
theorem egv_mul_ne_zero (x y : QRat) (hx : x ≠ ratRing.zero)
    (hy : y ≠ ratRing.zero) :
    ratRing.mul x y ≠ ratRing.zero := by
  revert hx hy
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  intro hx hy
  have ha : a.num ≠ 0 := fun h => hx ((rzd_eq_zero_iff a).mpr h)
  have hb : b.num ≠ 0 := fun h => hy ((rzd_eq_zero_iff b).mpr h)
  intro hz
  have hz' : Quot.mk ratRel (prMul a b) = ratRing.zero := hz
  have hnum : a.num * b.num = 0 := (rzd_eq_zero_iff (prMul a b)).mp hz'
  cases Int.mul_eq_zero.mp hnum with
  | inl h => exact ha h
  | inr h => exact hb h

/-- **加法性** — 非零 x,y で v_p(xy) = v_p(x)+v_p(y)（pvq_val_mul の商版）。 -/
theorem egvValQ_mul (p : Nat) (hp : IsPrime p) (x y : QRat)
    (hx : x ≠ ratRing.zero) (hy : y ≠ ratRing.zero) :
    egvValQ p hp (ratRing.mul x y) = egvValQ p hp x + egvValQ p hp y := by
  revert hx hy
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  intro hx hy
  have ha : a.num ≠ 0 := fun h => hx ((rzd_eq_zero_iff a).mpr h)
  have hb : b.num ≠ 0 := fun h => hy ((rzd_eq_zero_iff b).mpr h)
  have hab : (prMul a b).num ≠ 0 := by
    show a.num * b.num ≠ 0
    intro h
    cases Int.mul_eq_zero.mp h with
    | inl h => exact ha h
    | inr h => exact hb h
  show egvValQ p hp (Quot.mk ratRel (prMul a b))
    = egvValQ p hp (Quot.mk ratRel a) + egvValQ p hp (Quot.mk ratRel b)
  rw [egvValQ_mk_ne p hp (prMul a b) hab, egvValQ_mk_ne p hp a ha,
    egvValQ_mk_ne p hp b hb]
  exact pvq_val_mul p hp a b ha hb

/-- **健全性** — v_p(p) = 1（pvq_val_p の商版、ℚ の元 p = p/1 上）。 -/
theorem egvValQ_p (p : Nat) (hp : IsPrime p) :
    egvValQ p hp (Quot.mk ratRel (intToPreRat (p : Int))) = 1 := by
  have hne : (intToPreRat (p : Int)).num ≠ 0 := by
    show (p : Int) ≠ 0
    have hp2 : 2 ≤ p := hp.1
    intro hpz
    omega
  rw [egvValQ_mk_ne p hp (intToPreRat (p : Int)) hne]
  exact pvq_val_p p hp

/-! ## (2) 超距離の商版 -/

/-- **超距離（全 k 形）** — 非零 x,y,x+y で k ≤ v_p x ∧ k ≤ v_p y ⟹ k ≤ v_p(x+y)。
    E1 の pum_val_add_ge を egvValQ へ持ち上げ。 -/
theorem egvValQ_add_ge (p : Nat) (hp : IsPrime p) (x y : QRat)
    (hx : x ≠ ratRing.zero) (hy : y ≠ ratRing.zero)
    (hxy : ratRing.add x y ≠ ratRing.zero) (k : Int)
    (hkx : k ≤ egvValQ p hp x) (hky : k ≤ egvValQ p hp y) :
    k ≤ egvValQ p hp (ratRing.add x y) := by
  revert hx hy hxy hkx hky
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  intro hx hy hxy hkx hky
  have ha : a.num ≠ 0 := fun h => hx ((rzd_eq_zero_iff a).mpr h)
  have hb : b.num ≠ 0 := fun h => hy ((rzd_eq_zero_iff b).mpr h)
  have hab : (prAdd a b).num ≠ 0 :=
    fun h => hxy ((rzd_eq_zero_iff (prAdd a b)).mpr h)
  rw [egvValQ_mk_ne p hp a ha] at hkx
  rw [egvValQ_mk_ne p hp b hb] at hky
  show k ≤ egvValQ p hp (Quot.mk ratRel (prAdd a b))
  rw [egvValQ_mk_ne p hp (prAdd a b) hab]
  exact pum_val_add_ge p hp a b ha hb hab k hkx hky

/-- **超距離不等式** — v_p(x+y) ≥ min(v_p x, v_p y)（非零 x,y,x+y）。 -/
theorem egvValQ_add_ge_min (p : Nat) (hp : IsPrime p) (x y : QRat)
    (hx : x ≠ ratRing.zero) (hy : y ≠ ratRing.zero)
    (hxy : ratRing.add x y ≠ ratRing.zero) :
    egvValQ p hp (ratRing.add x y)
      ≥ min (egvValQ p hp x) (egvValQ p hp y) :=
  egvValQ_add_ge p hp x y hx hy hxy
    (min (egvValQ p hp x) (egvValQ p hp y))
    (Int.min_le_left _ _) (Int.min_le_right _ _)

/-- **強三角等号** — 非零 x,y,x+y で v_p x < v_p y ⟹ v_p(x+y) = v_p x
    （pum_val_add_eq の商版）。 -/
theorem egvValQ_add_eq (p : Nat) (hp : IsPrime p) (x y : QRat)
    (hx : x ≠ ratRing.zero) (hy : y ≠ ratRing.zero)
    (hxy : ratRing.add x y ≠ ratRing.zero)
    (h : egvValQ p hp x < egvValQ p hp y) :
    egvValQ p hp (ratRing.add x y) = egvValQ p hp x := by
  revert hx hy hxy h
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  intro hx hy hxy h
  have ha : a.num ≠ 0 := fun h0 => hx ((rzd_eq_zero_iff a).mpr h0)
  have hb : b.num ≠ 0 := fun h0 => hy ((rzd_eq_zero_iff b).mpr h0)
  have hab : (prAdd a b).num ≠ 0 :=
    fun h0 => hxy ((rzd_eq_zero_iff (prAdd a b)).mpr h0)
  rw [egvValQ_mk_ne p hp a ha, egvValQ_mk_ne p hp b hb] at h
  show egvValQ p hp (Quot.mk ratRel (prAdd a b)) = egvValQ p hp (Quot.mk ratRel a)
  rw [egvValQ_mk_ne p hp (prAdd a b) hab, egvValQ_mk_ne p hp a ha]
  exact pum_val_add_eq p hp a b ha hb hab h

/-- **付値相異 ⟹ 和は非零** — v_p x < v_p y なら x+y ≠ 0。
    もし x+y = 0 なら y = −x で v_p y = v_p(−x) = v_p x に反する。 -/
theorem egv_add_ne_zero_lt (p : Nat) (hp : IsPrime p) (x y : QRat)
    (h : egvValQ p hp x < egvValQ p hp y) :
    ratRing.add x y ≠ ratRing.zero := by
  intro hz
  have e1 : ratRing.add (ratRing.neg x) (ratRing.add x y)
          = ratRing.add (ratRing.add (ratRing.neg x) x) y :=
    (ratRing.add_assoc (ratRing.neg x) x y).symm
  rw [ratRing.neg_add, ratRing.zero_add] at e1
  rw [hz, ratRing.add_zero] at e1
  rw [← e1, egvValQ_neg] at h
  omega

/-! ## (3) 最小添字補題（Eisenstein の核） -/

/-- **各項が「零 or 付値 > V」なら有限和も「零 or 付値 > V」** — rsum の帰納。
    非零同士の和が消える（cancellation）可能性は `rzd_zero_or_ne` で分岐する。 -/
theorem egvSumAbove (p : Nat) (hp : IsPrime p) (t : Nat → QRat) (V : Int) :
    ∀ N, (∀ k, k < N →
        t k = ratRing.zero ∨ (t k ≠ ratRing.zero ∧ V < egvValQ p hp (t k))) →
      rsum ratRing t N = ratRing.zero ∨
        (rsum ratRing t N ≠ ratRing.zero ∧ V < egvValQ p hp (rsum ratRing t N)) := by
  intro N
  induction N with
  | zero =>
    intro _
    exact Or.inl rfl
  | succ M ih =>
    intro hprem
    have hM := hprem M (by omega)
    have hpar := ih (fun k hk => hprem k (by omega))
    show (ratRing.add (rsum ratRing t M) (t M) = ratRing.zero) ∨
      (ratRing.add (rsum ratRing t M) (t M) ≠ ratRing.zero ∧
        V < egvValQ p hp (ratRing.add (rsum ratRing t M) (t M)))
    cases hpar with
    | inl hAz =>
      cases hM with
      | inl hBz =>
        apply Or.inl
        rw [hAz, hBz]
        exact ratRing.zero_add ratRing.zero
      | inr hBpos =>
        obtain ⟨hBne, hBval⟩ := hBpos
        apply Or.inr
        have hEq : ratRing.add (rsum ratRing t M) (t M) = t M := by
          rw [hAz]
          exact ratRing.zero_add (t M)
        rw [hEq]
        exact ⟨hBne, hBval⟩
    | inr hApos =>
      obtain ⟨hAne, hAval⟩ := hApos
      cases hM with
      | inl hBz =>
        apply Or.inr
        have hEq : ratRing.add (rsum ratRing t M) (t M) = rsum ratRing t M := by
          rw [hBz]
          exact ratRing.add_zero (rsum ratRing t M)
        rw [hEq]
        exact ⟨hAne, hAval⟩
      | inr hBpos =>
        obtain ⟨hBne, hBval⟩ := hBpos
        cases rzd_zero_or_ne (ratRing.add (rsum ratRing t M) (t M)) with
        | inl hsz => exact Or.inl hsz
        | inr hsne =>
          apply Or.inr
          refine ⟨hsne, ?_⟩
          have hge := egvValQ_add_ge p hp (rsum ratRing t M) (t M) hAne hBne hsne
            (V + 1) (by omega) (by omega)
          omega

/-- **支配項をもつ有限和の付値** — 添字 d の項だけ付値 = V、他は「零 or > V」なら
    有限和の付値は V（かつ非零）。超距離「小さい付値が勝つ」を rsum の帰納で回す。 -/
theorem egvSumDominant (p : Nat) (hp : IsPrime p) (t : Nat → QRat) (V : Int)
    (d : Nat) :
    ∀ N, d < N → t d ≠ ratRing.zero → egvValQ p hp (t d) = V →
      (∀ k, k < N → k ≠ d →
        t k = ratRing.zero ∨ (t k ≠ ratRing.zero ∧ V < egvValQ p hp (t k))) →
      rsum ratRing t N ≠ ratRing.zero ∧ egvValQ p hp (rsum ratRing t N) = V := by
  intro N
  induction N with
  | zero =>
    intro hd _ _ _
    exact absurd hd (Nat.not_lt_zero d)
  | succ M ih =>
    intro hd htd hval hprem
    cases Nat.lt_or_ge d M with
    | inl hdM =>
      have hMne : M ≠ d := by omega
      have hMcase := hprem M (by omega) hMne
      have hih := ih hdM htd hval (fun k hk hkd => hprem k (by omega) hkd)
      obtain ⟨hAne, hAval⟩ := hih
      show ratRing.add (rsum ratRing t M) (t M) ≠ ratRing.zero ∧
        egvValQ p hp (ratRing.add (rsum ratRing t M) (t M)) = V
      cases hMcase with
      | inl hMzero =>
        have hEq : ratRing.add (rsum ratRing t M) (t M) = rsum ratRing t M := by
          rw [hMzero]
          exact ratRing.add_zero (rsum ratRing t M)
        rw [hEq]
        exact ⟨hAne, hAval⟩
      | inr hMpos =>
        obtain ⟨hMne', hMval⟩ := hMpos
        have hlt : egvValQ p hp (rsum ratRing t M) < egvValQ p hp (t M) := by
          rw [hAval]
          exact hMval
        have hsumne :=
          egv_add_ne_zero_lt p hp (rsum ratRing t M) (t M) hlt
        have heq :=
          egvValQ_add_eq p hp (rsum ratRing t M) (t M) hAne hMne' hsumne hlt
        rw [heq]
        exact ⟨hsumne, hAval⟩
    | inr hdge =>
      have hdeq : d = M := by omega
      subst hdeq
      have habove : ∀ k, k < d →
          t k = ratRing.zero ∨ (t k ≠ ratRing.zero ∧ V < egvValQ p hp (t k)) :=
        fun k hk => hprem k (by omega) (by omega)
      have hpar := egvSumAbove p hp t V d habove
      show ratRing.add (rsum ratRing t d) (t d) ≠ ratRing.zero ∧
        egvValQ p hp (ratRing.add (rsum ratRing t d) (t d)) = V
      cases hpar with
      | inl hAzero =>
        have hEq : ratRing.add (rsum ratRing t d) (t d) = t d := by
          rw [hAzero]
          exact ratRing.zero_add (t d)
        rw [hEq]
        exact ⟨htd, hval⟩
      | inr hApos =>
        obtain ⟨hAne, hAval⟩ := hApos
        have hlt : egvValQ p hp (t d) < egvValQ p hp (rsum ratRing t d) := by
          rw [hval]
          exact hAval
        have hcomm : ratRing.add (rsum ratRing t d) (t d)
                   = ratRing.add (t d) (rsum ratRing t d) :=
          ratRing.add_comm _ _
        have hsumne :=
          egv_add_ne_zero_lt p hp (t d) (rsum ratRing t d) hlt
        have heq :=
          egvValQ_add_eq p hp (t d) (rsum ratRing t d) htd hAne hsumne hlt
        rw [hcomm, heq, hval]
        exact ⟨hsumne, rfl⟩

/-- **最小添字補題（Eisenstein の核）** — g, h : PS ratRing に対し、
    i₀ が「v(g_i) の最小値をとる最小添字」・j₀ が h 側同様（明示 witness）ならば
      v_p((g·h)_{i₀+j₀}) = v_p(g_{i₀}) + v_p(h_{j₀})。
    Cauchy 積 Σ_{k≤i₀+j₀} g_k·h_{i₀+j₀−k} の対角項 k=i₀ が付値 = 和、
    対角以外は各項が「零（零係数）or 付値が真に大」で `egvSumDominant` が閉じる。 -/
theorem egv_min_index_mul (p : Nat) (hp : IsPrime p) (g h : PS ratRing)
    (i₀ j₀ : Nat)
    (hgi0 : g i₀ ≠ ratRing.zero) (hhj0 : h j₀ ≠ ratRing.zero)
    (hgmin : ∀ i, g i ≠ ratRing.zero →
      egvValQ p hp (g i₀) ≤ egvValQ p hp (g i))
    (hglt : ∀ i, i < i₀ → g i ≠ ratRing.zero →
      egvValQ p hp (g i₀) < egvValQ p hp (g i))
    (hhmin : ∀ j, h j ≠ ratRing.zero →
      egvValQ p hp (h j₀) ≤ egvValQ p hp (h j))
    (hhlt : ∀ j, j < j₀ → h j ≠ ratRing.zero →
      egvValQ p hp (h j₀) < egvValQ p hp (h j)) :
    egvValQ p hp (psMul ratRing g h (i₀ + j₀))
      = egvValQ p hp (g i₀) + egvValQ p hp (h j₀) := by
  have hdN : i₀ < i₀ + j₀ + 1 := by omega
  have hidx0 : i₀ + j₀ - i₀ = j₀ := by omega
  -- 対角項 k = i₀: 付値 = 和、非零
  have htd_ne : ratRing.mul (g i₀) (h (i₀ + j₀ - i₀)) ≠ ratRing.zero := by
    rw [hidx0]
    exact egv_mul_ne_zero (g i₀) (h j₀) hgi0 hhj0
  have htd_val : egvValQ p hp (ratRing.mul (g i₀) (h (i₀ + j₀ - i₀)))
      = egvValQ p hp (g i₀) + egvValQ p hp (h j₀) := by
    rw [hidx0]
    exact egvValQ_mul p hp (g i₀) (h j₀) hgi0 hhj0
  -- 対角以外の各項: 零 or 付値 > V
  have hother : ∀ k, k < i₀ + j₀ + 1 → k ≠ i₀ →
      ratRing.mul (g k) (h (i₀ + j₀ - k)) = ratRing.zero ∨
      (ratRing.mul (g k) (h (i₀ + j₀ - k)) ≠ ratRing.zero ∧
        egvValQ p hp (g i₀) + egvValQ p hp (h j₀)
          < egvValQ p hp (ratRing.mul (g k) (h (i₀ + j₀ - k)))) := by
    intro k hk hki0
    cases rzd_zero_or_ne (g k) with
    | inl hgz =>
      apply Or.inl
      rw [hgz]
      exact ratRing.zero_mul (h (i₀ + j₀ - k))
    | inr hgn =>
      cases rzd_zero_or_ne (h (i₀ + j₀ - k)) with
      | inl hhz =>
        apply Or.inl
        rw [hhz]
        exact ratRing.mul_zero (g k)
      | inr hhn =>
        apply Or.inr
        have htk_ne : ratRing.mul (g k) (h (i₀ + j₀ - k)) ≠ ratRing.zero :=
          egv_mul_ne_zero (g k) (h (i₀ + j₀ - k)) hgn hhn
        refine ⟨htk_ne, ?_⟩
        have htk_val : egvValQ p hp (ratRing.mul (g k) (h (i₀ + j₀ - k)))
            = egvValQ p hp (g k) + egvValQ p hp (h (i₀ + j₀ - k)) :=
          egvValQ_mul p hp (g k) (h (i₀ + j₀ - k)) hgn hhn
        rw [htk_val]
        cases Nat.lt_or_ge k i₀ with
        | inl hklt =>
          have hgstrict : egvValQ p hp (g i₀) < egvValQ p hp (g k) :=
            hglt k hklt hgn
          have hhge : egvValQ p hp (h j₀) ≤ egvValQ p hp (h (i₀ + j₀ - k)) :=
            hhmin (i₀ + j₀ - k) hhn
          omega
        | inr hkge =>
          have hidx : i₀ + j₀ - k < j₀ := by omega
          have hgge : egvValQ p hp (g i₀) ≤ egvValQ p hp (g k) :=
            hgmin k hgn
          have hhstrict : egvValQ p hp (h j₀) < egvValQ p hp (h (i₀ + j₀ - k)) :=
            hhlt (i₀ + j₀ - k) hidx hhn
          omega
  -- 支配項補題を対角 i₀ に適用
  have hmain := egvSumDominant p hp
    (fun k => ratRing.mul (g k) (h (i₀ + j₀ - k)))
    (egvValQ p hp (g i₀) + egvValQ p hp (h j₀))
    i₀ (i₀ + j₀ + 1) hdN htd_ne htd_val hother
  show egvValQ p hp (psMul ratRing g h (i₀ + j₀))
    = egvValQ p hp (g i₀) + egvValQ p hp (h j₀)
  exact hmain.2

end IUT
