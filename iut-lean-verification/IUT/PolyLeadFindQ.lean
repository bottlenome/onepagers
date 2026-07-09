/-
  IUT/PolyLeadFindQ.lean — F1（A1 0.80→0.85 詳細設計 §1 F1）:
    ℚ の Bool 零判定 `qIsZero` と Type 値先頭係数探索 `ploFind`

  ── 分類 **[実]**（本物の先行建設・承認済み足場(c)）。sorry 皆無・
  新規 Classical.choice 皆無（`#print axioms` = [propext, Quot.sound]）。

  **complete_pct 影響**: この段では complete_pct を直接動かさない（未設定）。
  本モジュールは A1 0.80→0.85 の**名前付き実ターゲット** `gefNFIUTField`
  （全域 inv 付き実体 ℚ[x]/(f)）への承認済み足場: 全域 inv 関数化の土台
  （Type 値・choice-free）を成す。設計 `audit/A1-to-085-plan.md` §1 F1・§3。
  後続計画: F3 除法関数 → F4 拡張ユークリッド関数 → F5/F6 NF 担体上の全域 inv。

  なぜ本物か:
   - `qIsZero` は既存 `qInv`（M115F-6c）と**同型の `Quot.lift` イディオム**で
     実 ℚ = `QRat` 上に直接建てる Bool 零判定。respects は交差積
     `r.num·s.den = s.num·r.den` と `den_pos`（分母 > 0）から
     `r.num=0 ↔ s.num=0`（`Int.mul_eq_zero`）で閉じる。代理群・toy 模型を
     主語にしない（実 ℚ の代表 num の `Int.decEq`＝choice-free で場合分け）。
   - `ploFind` は `plo_lead_oracle_Q`（Prop 値 Or・排中律版）の**Type 値版**:
     上から下への有限走査で `Option Nat` を返す全域関数。Quot 担体上の
     拡張ユークリッドを choice なしで停止させるための本物の探索関数。

  * F1-1 `plf_num_zero_iff` — 交差積 + 正分母から `r.num=0 ↔ s.num=0`
  * F1-2 `qIsZero` / `qIsZero_iff` — Bool 零判定（choice-free）と特徴付け
  * F1-3 `ploFind` / `ploFind_succ` — 先頭係数探索（Type 値・有限走査）
  * F1-4 `ploFind_none` — 走査 none ⟹ 全係数 0
  * F1-5 `ploFind_some` — 走査 some d ⟹ p d ≠ 0 かつ d+1 有界
  * F1-6 `ploFind_zero` — 零多項式では走査 none（inv_zero 用）

  全て選択公理不使用・禁止タクティク不使用・新規ファイルのみ。
-/
import IUT.RatZeroDecide
import IUT.SimpleExtension

namespace IUT

/-! ## F1-1: 交差積からの零判定同値 -/

/-- **F1-1: 零判定の well-defined 性の核** — 交差積 `ratRel r s` と正分母
    （`den_pos`）から `r.num = 0 ↔ s.num = 0`。`Int.mul_eq_zero` で分母因子を
    排除する（分母は正ゆえ非零）。 -/
theorem plf_num_zero_iff {r s : PreRat} (h : ratRel r s) :
    r.num = 0 ↔ s.num = 0 := by
  have h' : r.num * s.den = s.num * r.den := h
  apply Iff.intro
  · intro hr
    rw [hr, Int.zero_mul] at h'
    cases Int.mul_eq_zero.mp h'.symm with
    | inl h1 => exact h1
    | inr h1 => have := r.den_pos; omega
  · intro hs
    rw [hs, Int.zero_mul] at h'
    cases Int.mul_eq_zero.mp h' with
    | inl h1 => exact h1
    | inr h1 => have := s.den_pos; omega

/-! ## F1-2: Bool 零判定（qInv と同じ Quot.lift イディオム・choice-free） -/

/-- **F1-2a: ℚ の Bool 零判定** — `qInv`（M115F-6c）と同型の `Quot.lift`。
    代表の `Int.decEq`（`if r.num = 0`）で Bool を返す（choice-free）。
    respects は `plf_num_zero_iff`。 -/
def qIsZero : QRat → Bool :=
  Quot.lift (fun r => if r.num = 0 then true else false)
    (fun r s h => by
      show (if r.num = 0 then true else false) = (if s.num = 0 then true else false)
      have hiff := plf_num_zero_iff h
      cases Decidable.em (r.num = 0) with
      | inl hr => rw [if_pos hr, if_pos (hiff.mp hr)]
      | inr hr => rw [if_neg hr, if_neg (fun hs => hr (hiff.mpr hs))])

/-- **F1-2b: 零判定の特徴付け** — `qIsZero x = true ↔ x = 0`。
    `Quot.ind` で代表 r に落とし、`rzd_eq_zero_iff`（N2-3）で
    `x = 0 ⟺ r.num = 0` に帰着。 -/
theorem qIsZero_iff (x : QRat) : qIsZero x = true ↔ x = ratRing.zero := by
  induction x using Quot.ind
  rename_i r
  show (if r.num = 0 then true else false) = true ↔ Quot.mk ratRel r = ratRing.zero
  rw [rzd_eq_zero_iff r]
  cases Decidable.em (r.num = 0) with
  | inl hr => rw [if_pos hr]; exact Iff.intro (fun _ => hr) (fun _ => rfl)
  | inr hr =>
    rw [if_neg hr]
    exact Iff.intro (fun h => Bool.noConfusion h) (fun h => absurd h hr)

/-! ## F1-3: 先頭係数探索（Type 値・上から下への有限走査） -/

/-- **F1-3a: 先頭係数探索** — 上から下へ走査し、最初の非零係数の位置を返す
    （なければ none）。`plo_lead_oracle_Q` の Prop 値 Or を Bool 分岐で
    Type 値化した本物の探索関数。 -/
def ploFind (p : PS ratRing) : Nat → Option Nat
  | 0 => none
  | m + 1 => if qIsZero (p m) then ploFind p m else some m

/-- 0 段の展開。 -/
theorem ploFind_zero_eq (p : PS ratRing) : ploFind p 0 = none := rfl

/-- 後続段の展開（構造帰納の分岐そのもの）。 -/
theorem ploFind_succ (p : PS ratRing) (m : Nat) :
    ploFind p (m + 1) = if qIsZero (p m) then ploFind p m else some m := rfl

/-! ## F1-4/5: 走査結果の仕様 -/

/-- **F1-4: 走査 none ⟹ 全係数 0** — 上界 n の有界性と走査結果 none から、
    p の全係数が 0。n 帰納: 各段で `qIsZero (p m) = true`（さもなくば
    `some m ≠ none`）ゆえ `p m = 0`（`qIsZero_iff`）、下段へ有界性を伝播。 -/
theorem ploFind_none (p : PS ratRing) (n : Nat) (hb : IsPolyBounded ratRing p n)
    (h : ploFind p n = none) : ∀ i, p i = ratRing.zero := by
  revert hb h
  induction n with
  | zero => intro hb _ i; exact hb i (Nat.zero_le i)
  | succ m ih =>
    intro hb h
    rw [ploFind_succ] at h
    cases hq : qIsZero (p m) with
    | true =>
      rw [if_pos hq] at h
      have hpm : p m = ratRing.zero := (qIsZero_iff (p m)).mp hq
      have hb' : IsPolyBounded ratRing p m := by
        intro i hi
        cases Nat.lt_or_ge i (m + 1) with
        | inl _ => have he : i = m := by omega
                   rw [he]; exact hpm
        | inr hge => exact hb i hge
      exact ih hb' h
    | false =>
      rw [if_neg (by rw [hq]; exact (fun hc => Bool.noConfusion hc))] at h
      exact absurd h (fun hc => by injection hc)

/-- **F1-5: 走査 some d ⟹ p d ≠ 0 かつ d+1 有界** — 走査が d で止まる
    （= その位置の係数が非零）ので `p d ≠ 0`、それより上（d 以上の未走査域と
    上界域）は 0 ゆえ `IsPolyBounded p (d+1)`。 -/
theorem ploFind_some (p : PS ratRing) (n : Nat) (hb : IsPolyBounded ratRing p n)
    {d : Nat} (h : ploFind p n = some d) :
    p d ≠ ratRing.zero ∧ IsPolyBounded ratRing p (d + 1) := by
  revert hb h
  induction n with
  | zero =>
    intro _ h
    rw [ploFind_zero_eq] at h
    exact absurd h (fun hc => by injection hc)
  | succ m ih =>
    intro hb h
    rw [ploFind_succ] at h
    cases hq : qIsZero (p m) with
    | true =>
      rw [if_pos hq] at h
      have hpm : p m = ratRing.zero := (qIsZero_iff (p m)).mp hq
      have hb' : IsPolyBounded ratRing p m := by
        intro i hi
        cases Nat.lt_or_ge i (m + 1) with
        | inl _ => have he : i = m := by omega
                   rw [he]; exact hpm
        | inr hge => exact hb i hge
      exact ih hb' h
    | false =>
      rw [if_neg (by rw [hq]; exact (fun hc => Bool.noConfusion hc))] at h
      have hmd : m = d := Option.some.inj h
      have hpm_ne : p m ≠ ratRing.zero := by
        intro hz
        have ht : qIsZero (p m) = true := (qIsZero_iff (p m)).mpr hz
        rw [hq] at ht
        exact Bool.noConfusion ht
      apply And.intro
      · rw [← hmd]; exact hpm_ne
      · rw [← hmd]; exact hb

/-- **F1-6: 零多項式では走査 none** — 各段で `qIsZero 0 = true`（`qIsZero_iff`）
    ゆえ 0 まで降りて none（`gefNFInv` の `inv 0 = 0` 用）。 -/
theorem ploFind_zero (n : Nat) : ploFind (psZero ratRing) n = none := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [ploFind_succ]
    have hz : qIsZero (psZero ratRing m) = true := by
      show qIsZero ratRing.zero = true
      exact (qIsZero_iff ratRing.zero).mpr rfl
    rw [if_pos hz]
    exact ih

end IUT
