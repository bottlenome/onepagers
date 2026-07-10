/-
  IUT/EisensteinTowerInput.lean — A3 一般 n 円分塔の Eisenstein 入力（E5）:
  ∀n の Φ_{3ⁿ} 既約性 `eitPhi_irreducible` を本物に証明する。

  設計 audit/A3-inverse-limit-roadmap-2026-07-09.md §2.2（E5-1〜E5-5）の実装。
  柱A3「一般 n 円分塔 ℚ ⊂ ℚ(ζ₃) ⊂ … ⊂ ℚ(ζ_{3ⁿ})」の各段の法多項式
  Φ_{3ⁿ} = 1 + X^{3^{n-1}} + X^{2·3^{n-1}} が、**任意の n** で ℚ[X] の
  多項式約元上で既約であることを、Eisenstein 判定器（`eis_irreducible`）と
  シフト輸送（`est_transport`）へ、freshman's dream の立方帰納で組んだ
  Eisenstein 入力を投入して閉じる。

  ── 分類 **[実／本物建設(b)]**（骨格でなく実 ℚ[X] = `PS ratRing` 上の
  本物の多項式・付値。sorry 皆無・新規 Classical.choice 皆無・模型ゼロ）。

  **complete_pct 影響**: A3 一般 n 円分塔——**∀n の Φ_{3ⁿ} 既約性**を本物に
  証明し、任意段 ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ}) の体化を可能にする（M2 一般段
  機構の基盤）。本ファイル単体では complete_pct 未設定（M2 完成時に親が反映）。

  内容:
   * (E5-1) `eit3Int` — 3-整性述語 v₃(f_j) ≥ 0、閉包 add/mul/base（超距離商版 +
     Cauchy 和の v≥0 帰納 `eitSumGe`）。
   * (E5-2) `eit_cube` — (x+y)³ = x³+y³+3(x²y+xy²)（二項展開・freshman の核）。
     `eitFreshman` — **freshman's dream**: rpow(x+1)(3^m) = X^{3^m}+1+3·B（B は
     3-整、witness は ∃ で保持＝choice 回避）。m の立方帰納（(u+3B)³ 展開・
     係数 1,3,3,1 のみ）。
   * (E5-3〜E5-5) シフト像の 3 整同値 `eit_shift_triform` → Eisenstein 入力
     組み立て → `eitPhi_irreducible (n) (hn : 1 ≤ n) : pibIrreducible ratRing (ctsPhi n)`
     （= `eis_irreducible`（シフト像）+ `est_transport` の直線合成）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   - **p = 3 固定・ℚ 上固定**。stretch 塔 Φ_{3ⁿ} のみ（一般素数 p の X^p 版は
     含めない）。
   - **既約性のみ**。各段 ℚ(ζ_{3ⁿ}) の体化（gefNFIUTField 実例化）・Galois
     構造・res・塔・逆極限は本ファイルの射程外（M2 以降）。
   - freshman's dream `eitFreshman` の witness B は構造データでなく ∃ で保持し、
     Prop 証明内で ∃-除去のみ使う（新規 Classical.choice を導入しない）。

  全て選択公理不使用（propext/Quot.sound のみ）。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.CyclotomicStretch
import IUT.EisensteinShiftTransport
import IUT.Freshman

namespace IUT

/-! ## EIT-0: rpow 指数法則（local・重い import 回避のため再証明） -/

/-- **EIT-0a: rpow の加法法則** — a^{k+l} = a^k · a^l。 -/
theorem eit_rpow_add (R : CRing) (a : R.carrier) (k l : Nat) :
    rpow R a (k + l) = R.mul (rpow R a k) (rpow R a l) := by
  induction l with
  | zero =>
    show rpow R a k = R.mul (rpow R a k) R.one
    rw [R.mul_comm, R.one_mul]
  | succ l ih =>
    show R.mul (rpow R a (k + l)) a = R.mul (rpow R a k) (R.mul (rpow R a l) a)
    rw [ih, R.mul_assoc]

/-- **EIT-0b: rpow の反復法則** — (a^k)^l = a^{k·l}。 -/
theorem eit_rpow_rpow (R : CRing) (t : R.carrier) (k l : Nat) :
    rpow R (rpow R t k) l = rpow R t (k * l) := by
  induction l with
  | zero => rw [Nat.mul_zero]; rfl
  | succ l ih =>
    show R.mul (rpow R (rpow R t k) l) (rpow R t k) = rpow R t (k * (l + 1))
    rw [ih, Nat.mul_succ]
    exact (eit_rpow_add R t (k * l) k).symm

/-! ## EIT-1 (E5-1): 3-整性述語と閉包 -/

/-- **EIT-1a (E5-1): 3-整性述語** — 係数列 f の各非零係数の 3 進付値が ≥ 0。 -/
def eit3Int (f : PS ratRing) : Prop :=
  ∀ j, f j ≠ ratRing.zero → 0 ≤ egvValQ 3 isPrime_three (f j)

/-- **EIT-1b: Cauchy 和の v ≥ c 帰納（★E5 の実装上の泥）** — 各項が
    「零 or 付値 ≥ c」なら有限和も「零 or 付値 ≥ c」。非零同士の相殺は
    `rzd_zero_or_ne` で分岐、非strict 超距離 `egvValQ_add_ge` で閉じる。 -/
theorem eitSumGe (t : Nat → QRat) (c : Int) :
    ∀ N, (∀ k, k < N →
        t k = ratRing.zero ∨ (t k ≠ ratRing.zero ∧ c ≤ egvValQ 3 isPrime_three (t k))) →
      rsum ratRing t N = ratRing.zero ∨
        (rsum ratRing t N ≠ ratRing.zero ∧ c ≤ egvValQ 3 isPrime_three (rsum ratRing t N)) := by
  intro N
  induction N with
  | zero => intro _; exact Or.inl rfl
  | succ M ih =>
    intro hprem
    have hM := hprem M (by omega)
    have hpar := ih (fun k hk => hprem k (by omega))
    show (ratRing.add (rsum ratRing t M) (t M) = ratRing.zero) ∨
      (ratRing.add (rsum ratRing t M) (t M) ≠ ratRing.zero ∧
        c ≤ egvValQ 3 isPrime_three (ratRing.add (rsum ratRing t M) (t M)))
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
          rw [hAz]; exact ratRing.zero_add (t M)
        rw [hEq]; exact ⟨hBne, hBval⟩
    | inr hApos =>
      obtain ⟨hAne, hAval⟩ := hApos
      cases hM with
      | inl hBz =>
        apply Or.inr
        have hEq : ratRing.add (rsum ratRing t M) (t M) = rsum ratRing t M := by
          rw [hBz]; exact ratRing.add_zero (rsum ratRing t M)
        rw [hEq]; exact ⟨hAne, hAval⟩
      | inr hBpos =>
        obtain ⟨hBne, hBval⟩ := hBpos
        cases rzd_zero_or_ne (ratRing.add (rsum ratRing t M) (t M)) with
        | inl hsz => exact Or.inl hsz
        | inr hsne =>
          apply Or.inr
          refine ⟨hsne, ?_⟩
          exact egvValQ_add_ge 3 isPrime_three (rsum ratRing t M) (t M) hAne hBne hsne
            c hAval hBval

/-- **EIT-1c: 零多項式は 3-整**。 -/
theorem eit3Int_zero : eit3Int (psZero ratRing) := by
  intro j hj
  exact absurd rfl hj

/-- **EIT-1d: 加法閉包**。 -/
theorem eit3Int_add (f g : PS ratRing) (hf : eit3Int f) (hg : eit3Int g) :
    eit3Int (psAdd ratRing f g) := by
  intro j hj
  show 0 ≤ egvValQ 3 isPrime_three (ratRing.add (f j) (g j))
  cases rzd_zero_or_ne (f j) with
  | inl hfz =>
    rw [hfz, ratRing.zero_add]
    apply hg j
    show g j ≠ ratRing.zero
    intro hgz
    apply hj
    show ratRing.add (f j) (g j) = ratRing.zero
    rw [hfz, hgz]; exact ratRing.zero_add ratRing.zero
  | inr hfn =>
    cases rzd_zero_or_ne (g j) with
    | inl hgz =>
      rw [hgz, ratRing.add_zero]
      exact hf j hfn
    | inr hgn =>
      have hne : ratRing.add (f j) (g j) ≠ ratRing.zero := by
        show psAdd ratRing f g j ≠ ratRing.zero
        exact hj
      exact egvValQ_add_ge 3 isPrime_three (f j) (g j) hfn hgn hne 0 (hf j hfn) (hg j hgn)

/-- **EIT-1e: 乗法閉包** — Cauchy 和の各項 v(f_k·g_{j-k}) = v(f_k)+v(g_{j-k}) ≥ 0、
    和も `eitSumGe`（c = 0）で v ≥ 0。 -/
theorem eit3Int_mul (f g : PS ratRing) (hf : eit3Int f) (hg : eit3Int g) :
    eit3Int (psMul ratRing f g) := by
  intro j hj
  show 0 ≤ egvValQ 3 isPrime_three
    (rsum ratRing (fun k => ratRing.mul (f k) (g (j - k))) (j + 1))
  have hterms : ∀ k, k < j + 1 →
      (fun k => ratRing.mul (f k) (g (j - k))) k = ratRing.zero ∨
      ((fun k => ratRing.mul (f k) (g (j - k))) k ≠ ratRing.zero ∧
        0 ≤ egvValQ 3 isPrime_three ((fun k => ratRing.mul (f k) (g (j - k))) k)) := by
    intro k _
    show ratRing.mul (f k) (g (j - k)) = ratRing.zero ∨
      (ratRing.mul (f k) (g (j - k)) ≠ ratRing.zero ∧
        0 ≤ egvValQ 3 isPrime_three (ratRing.mul (f k) (g (j - k))))
    cases rzd_zero_or_ne (f k) with
    | inl hfz =>
      apply Or.inl; rw [hfz]; exact ratRing.zero_mul (g (j - k))
    | inr hfn =>
      cases rzd_zero_or_ne (g (j - k)) with
      | inl hgz =>
        apply Or.inl; rw [hgz]; exact ratRing.mul_zero (f k)
      | inr hgn =>
        apply Or.inr
        have hne : ratRing.mul (f k) (g (j - k)) ≠ ratRing.zero :=
          egv_mul_ne_zero (f k) (g (j - k)) hfn hgn
        refine ⟨hne, ?_⟩
        rw [egvValQ_mul 3 isPrime_three (f k) (g (j - k)) hfn hgn]
        have h1 := hf k hfn
        have h2 := hg (j - k) hgn
        omega
  cases eitSumGe (fun k => ratRing.mul (f k) (g (j - k))) 0 (j + 1) hterms with
  | inl hz =>
    exfalso; apply hj
    show rsum ratRing (fun k => ratRing.mul (f k) (g (j - k))) (j + 1) = ratRing.zero
    exact hz
  | inr hpos => exact hpos.2

/-- **EIT-1f: psOne は 3-整**（定数 1・v₃ = 0）。 -/
theorem eit3Int_psOne : eit3Int (psOne ratRing) := by
  intro j hj
  cases Nat.decEq j 0 with
  | isTrue h =>
    have hval : psOne ratRing j = ratRing.one := if_pos h
    rw [hval, ← rofNat_one ratRing, p9i_val_rofNat 1 (by omega)]
    omega
  | isFalse h =>
    exfalso; apply hj
    show psOne ratRing j = ratRing.zero
    exact if_neg h

/-- **EIT-1g: 単項式 X^a は 3-整**（係数 1・v₃ = 0）。 -/
theorem eit3Int_single_one (a : Nat) : eit3Int (psSingle ratRing ratRing.one a) := by
  intro j hj
  cases Nat.decEq j a with
  | isTrue h =>
    have hval : psSingle ratRing ratRing.one a j = ratRing.one := if_pos h
    rw [hval, ← rofNat_one ratRing, p9i_val_rofNat 1 (by omega)]
    omega
  | isFalse h =>
    exfalso; apply hj
    show psSingle ratRing ratRing.one a j = ratRing.zero
    exact if_neg h

/-- **EIT-1h: 自然数定数 psC(rofNat n) は 3-整**（v₃(rofNat n) = pvqNatVal ≥ 0）。 -/
theorem eit3Int_psC_rofNat (n : Nat) : eit3Int (psC ratRing (rofNat ratRing n)) := by
  intro j hj
  cases Nat.decEq j 0 with
  | isTrue h =>
    have hval : psC ratRing (rofNat ratRing n) j = rofNat ratRing n := if_pos h
    rw [hval] at hj ⊢
    cases n with
    | zero => exact absurd rfl hj
    | succ m => rw [p9i_val_rofNat (m + 1) (by omega)]; omega
  | isFalse h =>
    exfalso; apply hj
    show psC ratRing (rofNat ratRing n) j = ratRing.zero
    exact if_neg h

/-! ## EIT-2 (E5-2): freshman's dream の核 — 立方展開 -/

/-- **EIT-2a: 4 項アーベル並べ替え** — ((A+B)+C)+D = (D+A)+(C+B)。 -/
theorem eit_add4 (R : CRing) (A B C D : R.carrier) :
    R.add (R.add (R.add A B) C) D = R.add (R.add D A) (R.add C B) := by
  rw [R.add_comm (R.add (R.add A B) C) D, ← R.add_assoc D (R.add A B) C,
    ← R.add_assoc D A B, R.add_assoc (R.add D A) B C, R.add_comm B C]

/-- **EIT-2b: 立方の二項展開の中間項** — x²y + xy²。 -/
def eitCubeWit (x y : PS ratRing) : PS ratRing :=
  psAdd ratRing (psMul ratRing (psMul ratRing x x) y) (psMul ratRing x (psMul ratRing y y))

/-- **EIT-2c (二項定理・立方版): (x+y)³ = x³ + y³ + 3·(x²y + xy²)**。
    `binomial2`（一般二項定理）を指数 3 で展開し、係数 (1,3,3,1) を確定して整理。 -/
theorem eit_cube (x y : PS ratRing) :
    rpow (psRing ratRing) (psAdd ratRing x y) 3
      = psAdd ratRing (psAdd ratRing (rpow (psRing ratRing) x 3) (rpow (psRing ratRing) y 3))
          (psMul ratRing (psC ratRing (rofNat ratRing 3)) (eitCubeWit x y)) := by
  have hb := binomial2 (psRing ratRing) x y 3
  have e3 : rofNat (psRing ratRing) 3 = psC ratRing (rofNat ratRing 3) :=
    rofNat_ps_eq_psC ratRing 3
  have hx1 : rpow (psRing ratRing) x 1 = x := (psRing ratRing).one_mul x
  have hy1 : rpow (psRing ratRing) y 1 = y := (psRing ratRing).one_mul y
  have hx2 : rpow (psRing ratRing) x 2 = psMul ratRing x x := by
    show psMul ratRing (rpow (psRing ratRing) x 1) x = psMul ratRing x x
    rw [hx1]
  have hy2 : rpow (psRing ratRing) y 2 = psMul ratRing y y := by
    show psMul ratRing (rpow (psRing ratRing) y 1) y = psMul ratRing y y
    rw [hy1]
  show rpow (psRing ratRing) ((psRing ratRing).add x y) 3 = _
  rw [hb]
  show psAdd ratRing (psAdd ratRing (psAdd ratRing (psAdd ratRing (psZero ratRing)
      (psMul ratRing (rofNat (psRing ratRing) (chs 3 0))
        (psMul ratRing (rpow (psRing ratRing) x 0) (rpow (psRing ratRing) y 3))))
      (psMul ratRing (rofNat (psRing ratRing) (chs 3 1))
        (psMul ratRing (rpow (psRing ratRing) x 1) (rpow (psRing ratRing) y 2))))
      (psMul ratRing (rofNat (psRing ratRing) (chs 3 2))
        (psMul ratRing (rpow (psRing ratRing) x 2) (rpow (psRing ratRing) y 1))))
      (psMul ratRing (rofNat (psRing ratRing) (chs 3 3))
        (psMul ratRing (rpow (psRing ratRing) x 3) (rpow (psRing ratRing) y 0)))
    = psAdd ratRing (psAdd ratRing (rpow (psRing ratRing) x 3) (rpow (psRing ratRing) y 3))
          (psMul ratRing (psC ratRing (rofNat ratRing 3)) (eitCubeWit x y))
  rw [show chs 3 0 = 1 from rfl, show chs 3 1 = 3 from rfl, show chs 3 2 = 3 from rfl,
    show chs 3 3 = 1 from rfl, hx1, hy1, hx2, hy2, rofNat_one (psRing ratRing), e3]
  have hT0 : psMul ratRing (psRing ratRing).one
      (psMul ratRing (rpow (psRing ratRing) x 0) (rpow (psRing ratRing) y 3))
      = rpow (psRing ratRing) y 3 :=
    ((psRing ratRing).one_mul _).trans ((psRing ratRing).one_mul (rpow (psRing ratRing) y 3))
  have hT3 : psMul ratRing (psRing ratRing).one
      (psMul ratRing (rpow (psRing ratRing) x 3) (rpow (psRing ratRing) y 0))
      = rpow (psRing ratRing) x 3 :=
    ((psRing ratRing).one_mul _).trans (CRing.mul_one (psRing ratRing) (rpow (psRing ratRing) x 3))
  rw [hT0, hT3, show psAdd ratRing (psZero ratRing) (rpow (psRing ratRing) y 3)
      = rpow (psRing ratRing) y 3 from (psRing ratRing).zero_add (rpow (psRing ratRing) y 3)]
  show psAdd ratRing (psAdd ratRing (psAdd ratRing (rpow (psRing ratRing) y 3)
      (psMul ratRing (psC ratRing (rofNat ratRing 3)) (psMul ratRing x (psMul ratRing y y))))
      (psMul ratRing (psC ratRing (rofNat ratRing 3)) (psMul ratRing (psMul ratRing x x) y)))
      (rpow (psRing ratRing) x 3)
    = psAdd ratRing (psAdd ratRing (rpow (psRing ratRing) x 3) (rpow (psRing ratRing) y 3))
        (psMul ratRing (psC ratRing (rofNat ratRing 3)) (eitCubeWit x y))
  unfold eitCubeWit
  rw [show psMul ratRing (psC ratRing (rofNat ratRing 3))
        (psAdd ratRing (psMul ratRing (psMul ratRing x x) y) (psMul ratRing x (psMul ratRing y y)))
      = psAdd ratRing (psMul ratRing (psC ratRing (rofNat ratRing 3)) (psMul ratRing (psMul ratRing x x) y))
          (psMul ratRing (psC ratRing (rofNat ratRing 3)) (psMul ratRing x (psMul ratRing y y)))
      from (psRing ratRing).left_distrib (psC ratRing (rofNat ratRing 3))
        (psMul ratRing (psMul ratRing x x) y) (psMul ratRing x (psMul ratRing y y))]
  exact eit_add4 (psRing ratRing) (rpow (psRing ratRing) y 3)
    (psMul ratRing (psC ratRing (rofNat ratRing 3)) (psMul ratRing x (psMul ratRing y y)))
    (psMul ratRing (psC ratRing (rofNat ratRing 3)) (psMul ratRing (psMul ratRing x x) y))
    (rpow (psRing ratRing) x 3)

/-! ## EIT-3: 環演算のブリッジ補題（psMul/psAdd 形の環公理・rw 一致用） -/

theorem eitOneMul (a : PS ratRing) : psMul ratRing (psOne ratRing) a = a :=
  (psRing ratRing).one_mul a
theorem eitMulOne (a : PS ratRing) : psMul ratRing a (psOne ratRing) = a :=
  CRing.mul_one (psRing ratRing) a
theorem eitMulZero (a : PS ratRing) : psMul ratRing a (psZero ratRing) = psZero ratRing :=
  CRing.mul_zero (psRing ratRing) a
theorem eitMulAssoc (a b c : PS ratRing) :
    psMul ratRing (psMul ratRing a b) c = psMul ratRing a (psMul ratRing b c) :=
  (psRing ratRing).mul_assoc a b c
theorem eitAddAssoc (a b c : PS ratRing) :
    psAdd ratRing (psAdd ratRing a b) c = psAdd ratRing a (psAdd ratRing b c) :=
  (psRing ratRing).add_assoc a b c
theorem eitLeftDistrib (a b c : PS ratRing) :
    psMul ratRing a (psAdd ratRing b c) = psAdd ratRing (psMul ratRing a b) (psMul ratRing a c) :=
  (psRing ratRing).left_distrib a b c
theorem eitAddComm (a b : PS ratRing) : psAdd ratRing a b = psAdd ratRing b a :=
  (psRing ratRing).add_comm a b
theorem eitZeroAdd (a : PS ratRing) : psAdd ratRing (psZero ratRing) a = a :=
  (psRing ratRing).zero_add a
theorem eitAddZero (a : PS ratRing) : psAdd ratRing a (psZero ratRing) = a :=
  CRing.add_zero (psRing ratRing) a
theorem eitRpowMulDist (a b : PS ratRing) (k : Nat) :
    rpow (psRing ratRing) (psMul ratRing a b) k
      = psMul ratRing (rpow (psRing ratRing) a k) (rpow (psRing ratRing) b k) :=
  rpow_mul_dist (psRing ratRing) a b k

/-- **EIT-3b: (S+B)+A = S+(A+B)**（アーベル並べ替え）。 -/
theorem eit_add_assoc_comm (a b c : PS ratRing) :
    psAdd ratRing (psAdd ratRing a b) c = psAdd ratRing a (psAdd ratRing c b) := by
  rw [eitAddAssoc, eitAddComm b c]

/-- **EIT-3c: 1 の冪 = 1**。 -/
theorem eit_rpow_one_base : ∀ k, rpow (psRing ratRing) (psOne ratRing) k = psOne ratRing := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show psMul ratRing (rpow (psRing ratRing) (psOne ratRing) k) (psOne ratRing) = psOne ratRing
    rw [ih, eitMulOne]

/-- **EIT-3d: 3-整列の冪は 3-整**。 -/
theorem eit3Int_rpow (D : PS ratRing) (hD : eit3Int D) :
    ∀ k, eit3Int (rpow (psRing ratRing) D k) := by
  intro k
  induction k with
  | zero => exact eit3Int_psOne
  | succ k ih =>
    show eit3Int (psMul ratRing (rpow (psRing ratRing) D k) D)
    exact eit3Int_mul _ _ ih hD

/-! ## EIT-4 (E5-2): freshman's dream — 3 進合同と立方帰納 -/

/-- **EIT-4a: 定数 3**（3·(−) の乗数）。 -/
def eitC3 : PS ratRing := psC ratRing (rofNat ratRing 3)

theorem eit3Int_eitC3 : eit3Int eitC3 := eit3Int_psC_rofNat 3

/-- **EIT-4b: 3 進合同** — P ≡ Q (mod 3): P = Q + 3·D（D は 3-整）。 -/
def eitCong3 (P Q : PS ratRing) : Prop :=
  ∃ D, eit3Int D ∧ P = psAdd ratRing Q (psMul ratRing eitC3 D)

/-- **EIT-4c: 合同の推移律**。 -/
theorem eitCong3_trans {P Q S : PS ratRing} (h1 : eitCong3 P Q) (h2 : eitCong3 Q S) :
    eitCong3 P S := by
  obtain ⟨D1, hD1, hPQ⟩ := h1
  obtain ⟨D2, hD2, hQS⟩ := h2
  refine ⟨psAdd ratRing D1 D2, eit3Int_add _ _ hD1 hD2, ?_⟩
  rw [hPQ, hQS, eitLeftDistrib eitC3 D1 D2]
  exact eit_add_assoc_comm S (psMul ratRing eitC3 D2) (psMul ratRing eitC3 D1)

/-- **EIT-4d: 立方の合同保存（★freshman の核）** — P ≡ Q (mod 3)・Q 3-整なら
    P³ ≡ Q³ (mod 3)。(Q+3D)³ = Q³ + 3·D'（D' 3-整）を `eit_cube` の展開で得る。 -/
theorem eitCong3_cube {P Q : PS ratRing} (hQ : eit3Int Q) (h : eitCong3 P Q) :
    eitCong3 (rpow (psRing ratRing) P 3) (rpow (psRing ratRing) Q 3) := by
  obtain ⟨D, hD, hPQ⟩ := h
  refine ⟨psAdd ratRing (psMul ratRing (psMul ratRing eitC3 eitC3) (rpow (psRing ratRing) D 3))
      (eitCubeWit Q (psMul ratRing eitC3 D)), ?_, ?_⟩
  · apply eit3Int_add
    · exact eit3Int_mul _ _ (eit3Int_mul _ _ eit3Int_eitC3 eit3Int_eitC3) (eit3Int_rpow D hD 3)
    · unfold eitCubeWit
      apply eit3Int_add
      · exact eit3Int_mul _ _ (eit3Int_mul _ _ hQ hQ) (eit3Int_mul _ _ eit3Int_eitC3 hD)
      · exact eit3Int_mul _ _ hQ
          (eit3Int_mul _ _ (eit3Int_mul _ _ eit3Int_eitC3 hD) (eit3Int_mul _ _ eit3Int_eitC3 hD))
  · rw [hPQ, eit_cube Q (psMul ratRing eitC3 D)]
    have h2 : rpow (psRing ratRing) (psMul ratRing eitC3 D) 3
        = psMul ratRing eitC3 (psMul ratRing (psMul ratRing eitC3 eitC3) (rpow (psRing ratRing) D 3)) := by
      rw [eitRpowMulDist eitC3 D 3]
      have hpe : rpow (psRing ratRing) eitC3 3 = psMul ratRing eitC3 (psMul ratRing eitC3 eitC3) := by
        show psMul ratRing (psMul ratRing (psMul ratRing (psOne ratRing) eitC3) eitC3) eitC3
          = psMul ratRing eitC3 (psMul ratRing eitC3 eitC3)
        rw [eitOneMul, eitMulAssoc]
      rw [hpe, eitMulAssoc eitC3 (psMul ratRing eitC3 eitC3) (rpow (psRing ratRing) D 3)]
    show psAdd ratRing (psAdd ratRing (rpow (psRing ratRing) Q 3)
        (rpow (psRing ratRing) (psMul ratRing eitC3 D) 3))
        (psMul ratRing (psC ratRing (rofNat ratRing 3)) (eitCubeWit Q (psMul ratRing eitC3 D)))
      = psAdd ratRing (rpow (psRing ratRing) Q 3)
          (psMul ratRing eitC3 (psAdd ratRing
            (psMul ratRing (psMul ratRing eitC3 eitC3) (rpow (psRing ratRing) D 3))
            (eitCubeWit Q (psMul ratRing eitC3 D))))
    rw [h2, eitLeftDistrib eitC3 (psMul ratRing (psMul ratRing eitC3 eitC3) (rpow (psRing ratRing) D 3))
        (eitCubeWit Q (psMul ratRing eitC3 D))]
    exact eitAddAssoc (rpow (psRing ratRing) Q 3)
      (psMul ratRing eitC3 (psMul ratRing (psMul ratRing eitC3 eitC3) (rpow (psRing ratRing) D 3)))
      (psMul ratRing eitC3 (eitCubeWit Q (psMul ratRing eitC3 D)))

/-- **EIT-4e: 単項式の立方** — (X^a)³ = X^{3a}。 -/
theorem eit_single_cube (a : Nat) :
    rpow (psRing ratRing) (psSingle ratRing ratRing.one a) 3
      = psSingle ratRing ratRing.one (3 * a) := by
  show psMul ratRing (psMul ratRing (psMul ratRing (psOne ratRing)
      (psSingle ratRing ratRing.one a)) (psSingle ratRing ratRing.one a))
      (psSingle ratRing ratRing.one a)
    = psSingle ratRing ratRing.one (3 * a)
  rw [eitOneMul, psSingle_mul_single ratRing ratRing.one ratRing.one a a,
    ratRing.one_mul ratRing.one,
    psSingle_mul_single ratRing ratRing.one ratRing.one (a + a) a,
    ratRing.one_mul ratRing.one, show a + a + a = 3 * a from by omega]

/-- **EIT-4f (E5-2 本丸): freshman's dream** — (x+1)^{3^m} ≡ X^{3^m}+1 (mod 3)。
    m の立方帰納（base: (x+1)¹ = x+1；step: `eitCong3_cube` で立方を上げ、
    単項式立方 `eit_single_cube` で X^{3^{m+1}} を出し推移律で合成）。 -/
theorem eitFreshman : ∀ m, eitCong3 (rpow (psRing ratRing) p9eXp1 (3 ^ m))
    (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ m)) (psOne ratRing)) := by
  intro m
  induction m with
  | zero =>
    refine ⟨psZero ratRing, eit3Int_zero, ?_⟩
    show rpow (psRing ratRing) p9eXp1 1
      = psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one 1) (psOne ratRing))
          (psMul ratRing eitC3 (psZero ratRing))
    rw [eitMulZero, eitAddZero]
    show psMul ratRing (psOne ratRing) p9eXp1
      = psAdd ratRing (psSingle ratRing ratRing.one 1) (psOne ratRing)
    exact eitOneMul p9eXp1
  | succ m ih =>
    have hQ : eit3Int (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ m)) (psOne ratRing)) :=
      eit3Int_add _ _ (eit3Int_single_one (3 ^ m)) eit3Int_psOne
    have hcube := eitCong3_cube hQ ih
    have hL : rpow (psRing ratRing) (rpow (psRing ratRing) p9eXp1 (3 ^ m)) 3
        = rpow (psRing ratRing) p9eXp1 (3 ^ (m + 1)) := by
      rw [eit_rpow_rpow (psRing ratRing) p9eXp1 (3 ^ m) 3,
        show 3 ^ m * 3 = 3 ^ (m + 1) from (Nat.pow_succ 3 m).symm]
    rw [hL] at hcube
    have hmono : eitCong3
        (rpow (psRing ratRing) (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ m)) (psOne ratRing)) 3)
        (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ (m + 1))) (psOne ratRing)) := by
      refine ⟨eitCubeWit (psSingle ratRing ratRing.one (3 ^ m)) (psOne ratRing), ?_, ?_⟩
      · unfold eitCubeWit
        apply eit3Int_add
        · exact eit3Int_mul _ _
            (eit3Int_mul _ _ (eit3Int_single_one (3 ^ m)) (eit3Int_single_one (3 ^ m)))
            eit3Int_psOne
        · exact eit3Int_mul _ _ (eit3Int_single_one (3 ^ m))
            (eit3Int_mul _ _ eit3Int_psOne eit3Int_psOne)
      · rw [eit_cube (psSingle ratRing ratRing.one (3 ^ m)) (psOne ratRing),
          eit_single_cube (3 ^ m),
          show 3 * 3 ^ m = 3 ^ (m + 1) from by rw [Nat.pow_succ]; omega,
          eit_rpow_one_base 3]
        rfl
    exact eitCong3_trans hcube hmono

/-! ## EIT-5 (E5-3〜E5-5): シフト像の Eisenstein 入力と一般既約性 -/

/-- **EIT-5a: 立方二項展開（一般環）**。 -/
theorem eit_binsq (R : CRing) (a c : R.carrier) :
    R.mul (R.add a c) (R.add a c)
      = R.add (R.add (R.add (R.mul a a) (R.mul a c)) (R.mul a c)) (R.mul c c) := by
  rw [R.left_distrib (R.add a c) a c, R.right_distrib a c a, R.right_distrib a c c,
    R.mul_comm c a, R.add_assoc (R.add (R.mul a a) (R.mul a c)) (R.mul a c) (R.mul c c)]

/-- **EIT-5a': c·(1 + 2a + c) = (c + (ac + ac)) + c²**。 -/
theorem eit_ctri (R : CRing) (a c : R.carrier) :
    R.mul c (R.add (R.add R.one (R.add a a)) c)
      = R.add (R.add c (R.add (R.mul a c) (R.mul a c))) (R.mul c c) := by
  rw [R.left_distrib c (R.add R.one (R.add a a)) c, R.left_distrib c R.one (R.add a a),
    CRing.mul_one R c, R.left_distrib c a a, R.mul_comm c a]

/-- **EIT-5a'': 7 原子アーベル並べ替え**。 -/
theorem eit_six (R : CRing) (o a c aa ac : R.carrier) :
    R.add (R.add o (R.add a c)) (R.add (R.add aa ac) ac)
      = R.add (R.add (R.add o a) aa) (R.add c (R.add ac ac)) := by
  rw [← R.add_assoc o a c,
    ← R.add_assoc (R.add (R.add o a) c) (R.add aa ac) ac,
    ← R.add_assoc (R.add (R.add o a) c) aa ac, ← R.add_assoc c ac ac,
    ← R.add_assoc (R.add (R.add o a) aa) (R.add c ac) ac,
    ← R.add_assoc (R.add (R.add o a) aa) c ac,
    R.add_assoc (R.add o a) c aa, R.add_comm c aa, ← R.add_assoc (R.add o a) aa c]

/-- **EIT-5a''': 1 + (a+c) + (a+c)² = (1+a+a²) + c·(1+2a+c)**。 -/
theorem eit_tri (R : CRing) (a c : R.carrier) :
    R.add (R.add R.one (R.add a c)) (R.mul (R.add a c) (R.add a c))
      = R.add (R.add (R.add R.one a) (R.mul a a))
          (R.mul c (R.add (R.add R.one (R.add a a)) c)) := by
  rw [eit_binsq, eit_ctri,
    ← R.add_assoc (R.add R.one (R.add a c))
      (R.add (R.add (R.mul a a) (R.mul a c)) (R.mul a c)) (R.mul c c),
    ← R.add_assoc (R.add (R.add R.one a) (R.mul a a))
      (R.add c (R.add (R.mul a c) (R.mul a c))) (R.mul c c),
    eit_six R R.one a c (R.mul a a) (R.mul a c)]

/-- **EIT-5b: 二乗二項展開（psMul 形ブリッジ）**。 -/
theorem eitBinsq (a c : PS ratRing) :
    psMul ratRing (psAdd ratRing a c) (psAdd ratRing a c)
      = psAdd ratRing (psAdd ratRing (psAdd ratRing (psMul ratRing a a) (psMul ratRing a c))
          (psMul ratRing a c)) (psMul ratRing c c) :=
  eit_binsq (psRing ratRing) a c

/-- **EIT-5c: (X^K + 1)² = X^{2K} + X^K + X^K + 1**。 -/
theorem eit_asq (K : Nat) :
    psMul ratRing (psAdd ratRing (psSingle ratRing ratRing.one K) (psOne ratRing))
        (psAdd ratRing (psSingle ratRing ratRing.one K) (psOne ratRing))
      = psAdd ratRing (psAdd ratRing (psAdd ratRing
          (psSingle ratRing ratRing.one (K + K)) (psSingle ratRing ratRing.one K))
          (psSingle ratRing ratRing.one K)) (psOne ratRing) := by
  rw [eitBinsq (psSingle ratRing ratRing.one K) (psOne ratRing),
    eitMulOne (psSingle ratRing ratRing.one K), eitMulOne (psOne ratRing),
    psSingle_mul_single ratRing ratRing.one ratRing.one K K, ratRing.one_mul ratRing.one]

/-- **EIT-5d: 1+1+1 = 3**（環スカラー）。 -/
theorem eit_three :
    ratRing.add (ratRing.add ratRing.one ratRing.one) ratRing.one = rofNat ratRing 3 := by
  show ratRing.add (ratRing.add ratRing.one ratRing.one) ratRing.one
    = ratRing.add (ratRing.add (ratRing.add ratRing.zero ratRing.one) ratRing.one) ratRing.one
  rw [ratRing.zero_add]

/-- **EIT-5e: 1 + a + a² = X^{2K} + 3·a**（a = X^K+1・定数/中間の 3-整除の核）。 -/
theorem eit_1aa2 (K : Nat) (hK : 1 ≤ K) :
    psAdd ratRing (psAdd ratRing (psOne ratRing)
        (psAdd ratRing (psSingle ratRing ratRing.one K) (psOne ratRing)))
        (psMul ratRing (psAdd ratRing (psSingle ratRing ratRing.one K) (psOne ratRing))
          (psAdd ratRing (psSingle ratRing ratRing.one K) (psOne ratRing)))
      = psAdd ratRing (psSingle ratRing ratRing.one (K + K))
          (psMul ratRing eitC3 (psAdd ratRing (psSingle ratRing ratRing.one K) (psOne ratRing))) := by
  rw [eit_asq K]
  funext j
  show ratRing.add (ratRing.add (psOne ratRing j)
      (ratRing.add (psSingle ratRing ratRing.one K j) (psOne ratRing j)))
      (ratRing.add (ratRing.add (ratRing.add (psSingle ratRing ratRing.one (K + K) j)
        (psSingle ratRing ratRing.one K j)) (psSingle ratRing ratRing.one K j)) (psOne ratRing j))
    = ratRing.add (psSingle ratRing ratRing.one (K + K) j)
        (psMul ratRing eitC3 (psAdd ratRing (psSingle ratRing ratRing.one K) (psOne ratRing)) j)
  rw [show psMul ratRing eitC3 (psAdd ratRing (psSingle ratRing ratRing.one K) (psOne ratRing)) j
      = ratRing.mul (rofNat ratRing 3) (ratRing.add (psSingle ratRing ratRing.one K j) (psOne ratRing j))
      from psC_mul_coeff ratRing (rofNat ratRing 3)
        (psAdd ratRing (psSingle ratRing ratRing.one K) (psOne ratRing)) j]
  cases Nat.decEq j 0 with
  | isTrue hj0 =>
    rw [hj0, show psOne ratRing 0 = ratRing.one from if_pos rfl,
      show psSingle ratRing ratRing.one K 0 = ratRing.zero from if_neg (by omega),
      show psSingle ratRing ratRing.one (K + K) 0 = ratRing.zero from if_neg (by omega),
      ratRing.zero_add, ratRing.add_zero, ratRing.add_zero, ratRing.zero_add,
      CRing.mul_one ratRing (rofNat ratRing 3), ratRing.zero_add]
    exact eit_three
  | isFalse hj0 =>
    cases Nat.decEq j K with
    | isTrue hjK =>
      rw [hjK, show psOne ratRing K = ratRing.zero from if_neg (by omega),
        show psSingle ratRing ratRing.one K K = ratRing.one from if_pos rfl,
        show psSingle ratRing ratRing.one (K + K) K = ratRing.zero from if_neg (by omega),
        show ratRing.add ratRing.one ratRing.zero = ratRing.one from ratRing.add_zero ratRing.one,
        show ratRing.add ratRing.zero ratRing.one = ratRing.one from ratRing.zero_add ratRing.one,
        show ratRing.add (ratRing.add ratRing.one ratRing.one) ratRing.zero
          = ratRing.add ratRing.one ratRing.one from ratRing.add_zero (ratRing.add ratRing.one ratRing.one),
        CRing.mul_one ratRing (rofNat ratRing 3),
        show ratRing.add ratRing.zero (rofNat ratRing 3) = rofNat ratRing 3
          from ratRing.zero_add (rofNat ratRing 3),
        ← ratRing.add_assoc ratRing.one ratRing.one ratRing.one]
      exact eit_three
    | isFalse hjK =>
      cases Nat.decEq j (K + K) with
      | isTrue hjKK =>
        rw [hjKK, show psOne ratRing (K + K) = ratRing.zero from if_neg (by omega),
          show psSingle ratRing ratRing.one K (K + K) = ratRing.zero from if_neg (by omega),
          show psSingle ratRing ratRing.one (K + K) (K + K) = ratRing.one from if_pos rfl,
          ratRing.add_zero, ratRing.add_zero, ratRing.add_zero, ratRing.zero_add,
          ratRing.mul_zero, ratRing.add_zero]
      | isFalse hjKK =>
        rw [show psOne ratRing j = ratRing.zero from if_neg (by omega),
          show psSingle ratRing ratRing.one K j = ratRing.zero from if_neg (by omega),
          show psSingle ratRing ratRing.one (K + K) j = ratRing.zero from if_neg (by omega),
          ratRing.add_zero, ratRing.add_zero, ratRing.add_zero, ratRing.zero_add,
          ratRing.mul_zero, ratRing.add_zero]

/-- **EIT-5f: eit_tri の psMul 形ブリッジ**。 -/
theorem eitTri (a c : PS ratRing) :
    psAdd ratRing (psAdd ratRing (psOne ratRing) (psAdd ratRing a c))
        (psMul ratRing (psAdd ratRing a c) (psAdd ratRing a c))
      = psAdd ratRing (psAdd ratRing (psAdd ratRing (psOne ratRing) a) (psMul ratRing a a))
          (psMul ratRing c (psAdd ratRing (psAdd ratRing (psOne ratRing) (psAdd ratRing a a)) c)) :=
  eit_tri (psRing ratRing) a c

/-! Φ_{3ⁿ} の係数（0, 3^{n-1}, 2·3^{n-1} で 1） -/

theorem eit_ctsPhi_c0 : ∀ n, ctsPhi (n + 1) 0 = ratRing.one := by
  intro n
  induction n with
  | zero => exact cq0PS_coeff0
  | succ n ih =>
    show ctsStretch (ctsPhi (n + 1)) 0 = ratRing.one
    show (if 0 % 3 = 0 then ctsPhi (n + 1) (0 / 3) else ratRing.zero) = ratRing.one
    rw [if_pos (show 0 % 3 = 0 from rfl)]
    exact ih

theorem eit_ctsPhi_cK : ∀ n, ctsPhi (n + 1) (3 ^ n) = ratRing.one := by
  intro n
  induction n with
  | zero => exact cq0PS_coeff1
  | succ n ih =>
    show ctsStretch (ctsPhi (n + 1)) (3 ^ (n + 1)) = ratRing.one
    show (if 3 ^ (n + 1) % 3 = 0 then ctsPhi (n + 1) (3 ^ (n + 1) / 3) else ratRing.zero) = ratRing.one
    rw [if_pos (show 3 ^ (n + 1) % 3 = 0 by rw [cts_pow3_succ n]; omega),
      show 3 ^ (n + 1) / 3 = 3 ^ n by rw [cts_pow3_succ n]; omega]
    exact ih

theorem eit_ctsPhi_eq (n : Nat) :
    ctsPhi (n + 1)
      = psAdd ratRing (psAdd ratRing (psOne ratRing) (psSingle ratRing ratRing.one (3 ^ n)))
          (psSingle ratRing ratRing.one (2 * 3 ^ n)) := by
  funext j
  show ctsPhi (n + 1) j
    = ratRing.add (ratRing.add (psOne ratRing j) (psSingle ratRing ratRing.one (3 ^ n) j))
        (psSingle ratRing ratRing.one (2 * 3 ^ n) j)
  have hpos : 0 < 3 ^ n := Nat.pow_pos (by omega)
  cases Nat.decEq j 0 with
  | isTrue hj0 =>
    rw [hj0, eit_ctsPhi_c0 n, show psOne ratRing 0 = ratRing.one from if_pos rfl,
      show psSingle ratRing ratRing.one (3 ^ n) 0 = ratRing.zero from if_neg (by omega),
      show psSingle ratRing ratRing.one (2 * 3 ^ n) 0 = ratRing.zero from if_neg (by omega),
      ratRing.add_zero, ratRing.add_zero]
  | isFalse hj0 =>
    cases Nat.decEq j (3 ^ n) with
    | isTrue hjK =>
      rw [hjK, eit_ctsPhi_cK n, show psOne ratRing (3 ^ n) = ratRing.zero from if_neg (by omega),
        show psSingle ratRing ratRing.one (3 ^ n) (3 ^ n) = ratRing.one from if_pos rfl,
        show psSingle ratRing ratRing.one (2 * 3 ^ n) (3 ^ n) = ratRing.zero from if_neg (by omega),
        ratRing.zero_add, ratRing.add_zero]
    | isFalse hjK =>
      cases Nat.decEq j (2 * 3 ^ n) with
      | isTrue hj2 =>
        rw [hj2, ctsPhi_lead_succ n,
          show psOne ratRing (2 * 3 ^ n) = ratRing.zero from if_neg (by omega),
          show psSingle ratRing ratRing.one (3 ^ n) (2 * 3 ^ n) = ratRing.zero from if_neg (by omega),
          show psSingle ratRing ratRing.one (2 * 3 ^ n) (2 * 3 ^ n) = ratRing.one from if_pos rfl,
          ratRing.zero_add, ratRing.zero_add]
      | isFalse hj2 =>
        rw [ctsPhi_vanish_succ n j hj0 hjK hj2,
          show psOne ratRing j = ratRing.zero from if_neg hj0,
          show psSingle ratRing ratRing.one (3 ^ n) j = ratRing.zero from if_neg hjK,
          show psSingle ratRing ratRing.one (2 * 3 ^ n) j = ratRing.zero from if_neg hj2,
          ratRing.add_zero, ratRing.add_zero]

/-! シフト（加法性・単項式像） -/

theorem eit_shift_add (f g : PS ratRing) (M : Nat) :
    p9eShift (psAdd ratRing f g) M = psAdd ratRing (p9eShift f M) (p9eShift g M) :=
  evalHom_add (psConstHom ratRing) p9eXp1 f g M

theorem eit_shift_mono (m M : Nat) (hm : m < M) :
    p9eShift (psSingle ratRing ratRing.one m) M = rpow (psRing ratRing) p9eXp1 m := by
  funext j
  rw [p9e_shift_coeff (psSingle ratRing ratRing.one m) M j,
    rsum_single ratRing
      (fun i => ratRing.mul (psSingle ratRing ratRing.one m i) (rofNat ratRing (chs i j))) m M hm
      (fun q _ hqm => by
        show ratRing.mul (psSingle ratRing ratRing.one m q) (rofNat ratRing (chs q j)) = ratRing.zero
        rw [show psSingle ratRing ratRing.one m q = ratRing.zero from if_neg hqm]
        exact ratRing.zero_mul _),
    p9e_pow_coeff m j]
  show ratRing.mul (psSingle ratRing ratRing.one m m) (rofNat ratRing (chs m j)) = rofNat ratRing (chs m j)
  rw [show psSingle ratRing ratRing.one m m = ratRing.one from if_pos rfl, ratRing.one_mul]

/-- **EIT-5g: シフト像 = 1 + y + y²**（y = (x+1)^{3ⁿ}）。 -/
theorem eit_hShiftEq (n : Nat) :
    p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1)
      = psAdd ratRing (psAdd ratRing (psOne ratRing) (rpow (psRing ratRing) p9eXp1 (3 ^ n)))
          (psMul ratRing (rpow (psRing ratRing) p9eXp1 (3 ^ n)) (rpow (psRing ratRing) p9eXp1 (3 ^ n))) := by
  have hs0 : p9eShift (psOne ratRing) (2 * 3 ^ n + 1) = psOne ratRing :=
    eit_shift_mono 0 (2 * 3 ^ n + 1) (by omega)
  have hsK : p9eShift (psSingle ratRing ratRing.one (3 ^ n)) (2 * 3 ^ n + 1)
      = rpow (psRing ratRing) p9eXp1 (3 ^ n) :=
    eit_shift_mono (3 ^ n) (2 * 3 ^ n + 1) (by omega)
  have hs2K : p9eShift (psSingle ratRing ratRing.one (2 * 3 ^ n)) (2 * 3 ^ n + 1)
      = rpow (psRing ratRing) p9eXp1 (2 * 3 ^ n) :=
    eit_shift_mono (2 * 3 ^ n) (2 * 3 ^ n + 1) (by omega)
  have h2K : rpow (psRing ratRing) p9eXp1 (2 * 3 ^ n)
      = psMul ratRing (rpow (psRing ratRing) p9eXp1 (3 ^ n)) (rpow (psRing ratRing) p9eXp1 (3 ^ n)) := by
    rw [show 2 * 3 ^ n = 3 ^ n + 3 ^ n from by omega,
      eit_rpow_add (psRing ratRing) p9eXp1 (3 ^ n) (3 ^ n)]
    rfl
  rw [eit_ctsPhi_eq n, eit_shift_add, eit_shift_add, hs0, hsK, hs2K, h2K]

/-- **EIT-5h: 1 + y + y² = X^{2·3ⁿ} + 3·W**（W は 3-整・freshman + eit_tri + eit_1aa2）。 -/
theorem eit_triform (n : Nat) :
    ∃ W, eit3Int W ∧
      psAdd ratRing (psAdd ratRing (psOne ratRing) (rpow (psRing ratRing) p9eXp1 (3 ^ n)))
        (psMul ratRing (rpow (psRing ratRing) p9eXp1 (3 ^ n)) (rpow (psRing ratRing) p9eXp1 (3 ^ n)))
      = psAdd ratRing (psSingle ratRing ratRing.one (2 * 3 ^ n)) (psMul ratRing eitC3 W) := by
  obtain ⟨B, hB, hyeq⟩ := eitFreshman n
  refine ⟨psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
      (psMul ratRing B (psAdd ratRing (psAdd ratRing (psOne ratRing)
        (psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
          (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))))
        (psMul ratRing eitC3 B))), ?_, ?_⟩
  · apply eit3Int_add
    · exact eit3Int_add _ _ (eit3Int_single_one (3 ^ n)) eit3Int_psOne
    · apply eit3Int_mul _ _ hB
      apply eit3Int_add
      · apply eit3Int_add
        · exact eit3Int_psOne
        · exact eit3Int_add _ _
            (eit3Int_add _ _ (eit3Int_single_one (3 ^ n)) eit3Int_psOne)
            (eit3Int_add _ _ (eit3Int_single_one (3 ^ n)) eit3Int_psOne)
      · exact eit3Int_mul _ _ eit3Int_eitC3 hB
  · rw [hyeq]
    show psAdd ratRing (psAdd ratRing (psOne ratRing)
          (psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
            (psMul ratRing eitC3 B)))
        (psMul ratRing (psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
            (psMul ratRing eitC3 B))
          (psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
            (psMul ratRing eitC3 B)))
      = psAdd ratRing (psSingle ratRing ratRing.one (2 * 3 ^ n))
          (psMul ratRing eitC3 (psAdd ratRing
            (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
            (psMul ratRing B (psAdd ratRing (psAdd ratRing (psOne ratRing)
              (psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
                (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))))
              (psMul ratRing eitC3 B)))))
    rw [eitTri (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
        (psMul ratRing eitC3 B),
      eit_1aa2 (3 ^ n) (Nat.pow_pos (by omega)),
      eitMulAssoc eitC3 B
        (psAdd ratRing (psAdd ratRing (psOne ratRing)
          (psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
            (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))))
          (psMul ratRing eitC3 B)),
      eitAddAssoc,
      ← eitLeftDistrib eitC3 (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
        (psMul ratRing B (psAdd ratRing (psAdd ratRing (psOne ratRing)
          (psAdd ratRing (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))
            (psAdd ratRing (psSingle ratRing ratRing.one (3 ^ n)) (psOne ratRing))))
          (psMul ratRing eitC3 B))),
      show 3 ^ n + 3 ^ n = 2 * 3 ^ n from by omega]

/-- **EIT-5i (E5-5 本丸): Φ_{3^{n+1}} は多項式約元上で既約**（後続 succ 版）。 -/
theorem eitPhi_irreducible_succ (n : Nat) : pibIrreducible ratRing (ctsPhi (n + 1)) := by
  have hpos : 0 < 3 ^ n := Nat.pow_pos (by omega)
  have hone : ratRing.one ≠ ratRing.zero := by
    rw [← rofNat_one ratRing]; exact p9i_rofNat_ne 1 (by omega)
  have hbound : IsPolyBounded ratRing (ctsPhi (n + 1)) (2 * 3 ^ n + 1) := ctsPhi_bound_succ n
  have hleadphi : ctsPhi (n + 1) (2 * 3 ^ n) = ratRing.one := ctsPhi_lead_succ n
  have hleadne : ctsPhi (n + 1) (2 * 3 ^ n) ≠ ratRing.zero := by rw [hleadphi]; exact hone
  have hdeg := p9i_shift_deg (ctsPhi (n + 1)) (2 * 3 ^ n) (2 * 3 ^ n + 1) hbound (by omega)
  have hSE := eit_hShiftEq n
  obtain ⟨W, hW, hTF⟩ := eit_triform n
  have hform : p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1)
      = psAdd ratRing (psSingle ratRing ratRing.one (2 * 3 ^ n)) (psMul ratRing eitC3 W) :=
    hSE.trans hTF
  have hy0 : rpow (psRing ratRing) p9eXp1 (3 ^ n) 0 = ratRing.one := by
    rw [p9e_pow_coeff (3 ^ n) 0, chs_zero (3 ^ n)]; exact rofNat_one ratRing
  have hyy0 : psMul ratRing (rpow (psRing ratRing) p9eXp1 (3 ^ n))
      (rpow (psRing ratRing) p9eXp1 (3 ^ n)) 0 = ratRing.one := by
    show ratRing.add ratRing.zero (ratRing.mul (rpow (psRing ratRing) p9eXp1 (3 ^ n) 0)
        (rpow (psRing ratRing) p9eXp1 (3 ^ n) (0 - 0))) = ratRing.one
    rw [ratRing.zero_add, show (0 : Nat) - 0 = 0 from rfl, hy0, ratRing.one_mul]
  have hconstval : p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1) 0 = rofNat ratRing 3 := by
    rw [hSE]
    show ratRing.add (ratRing.add (psOne ratRing 0) (rpow (psRing ratRing) p9eXp1 (3 ^ n) 0))
        (psMul ratRing (rpow (psRing ratRing) p9eXp1 (3 ^ n))
          (rpow (psRing ratRing) p9eXp1 (3 ^ n)) 0) = rofNat ratRing 3
    rw [show psOne ratRing 0 = ratRing.one from if_pos rfl, hy0, hyy0]
    exact eit_three
  have h3one : pvqNatVal 3 3 = 1 := pvqNatVal_spec 3 (by omega) 1 1 p9i_not3dvd1 (by omega)
  have h1zero : pvqNatVal 3 1 = 0 := pvqNatVal_spec 3 (by omega) 0 1 p9i_not3dvd1 (by omega)
  -- Eisenstein 入力
  have hlead' : egvValQ 3 isPrime_three (p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1) (2 * 3 ^ n)) = 0 := by
    rw [hdeg.1, hleadphi, ← rofNat_one ratRing, p9i_val_rofNat 1 (by omega)]; omega
  have hln' : p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1) (2 * 3 ^ n) ≠ ratRing.zero := by
    rw [hdeg.1, hleadphi]; exact hone
  have hconst' : egvValQ 3 isPrime_three (p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1) 0) = 1 := by
    rw [hconstval, p9i_val_rofNat 3 (by omega)]; omega
  have hc0' : p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1) 0 ≠ ratRing.zero := by
    rw [hconstval]; exact p9i_rofNat_ne 3 (by omega)
  have hmid' : ∀ i, i < 2 * 3 ^ n →
      p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1) i ≠ ratRing.zero →
      1 ≤ egvValQ 3 isPrime_three (p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1) i) := by
    intro i hi hine
    have hval : p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1) i = ratRing.mul (rofNat ratRing 3) (W i) := by
      rw [hform]
      show ratRing.add (psSingle ratRing ratRing.one (2 * 3 ^ n) i) (psMul ratRing eitC3 W i)
        = ratRing.mul (rofNat ratRing 3) (W i)
      rw [show psSingle ratRing ratRing.one (2 * 3 ^ n) i = ratRing.zero from if_neg (by omega),
        ratRing.zero_add]
      exact psC_mul_coeff ratRing (rofNat ratRing 3) W i
    rw [hval] at hine ⊢
    have hWi : W i ≠ ratRing.zero := by
      intro h0; apply hine; rw [h0]; exact ratRing.mul_zero _
    have h3ne : rofNat ratRing 3 ≠ ratRing.zero := p9i_rofNat_ne 3 (by omega)
    rw [egvValQ_mul 3 isPrime_three (rofNat ratRing 3) (W i) h3ne hWi, p9i_val_rofNat 3 (by omega)]
    have hWval := hW i hWi
    omega
  have hsh : pibIrreducible ratRing (p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1)) :=
    eis_irreducible (p9eShift (ctsPhi (n + 1)) (2 * 3 ^ n + 1)) (2 * 3 ^ n) 3 isPrime_three
      hdeg.2 (by omega) hlead' hln' hmid' hconst' hc0'
  exact est_transport (ctsPhi (n + 1)) (2 * 3 ^ n) hbound hleadne (by omega) hsh

/-- **EIT-5j (E5-5): 一般 n の Φ_{3ⁿ} 既約性** — 任意段 ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ}) の
    法多項式が ℚ[X] の多項式約元上で既約（1 ≤ n）。 -/
theorem eitPhi_irreducible (n : Nat) (hn : 1 ≤ n) : pibIrreducible ratRing (ctsPhi n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact eitPhi_irreducible_succ m

end IUT
