/-
# M193F: Λₙ 塔の生成元 λₙ と位数・付値（柱B B-1・並行部品）

M109（塔の環骨格 towerLevel・tower_shape・tower_torsion）と M151F
（λ-adic 付値の階段 lam_pow_val_exact・lam_pow_strict）の直上に立ち、
**Λₙ (n ≥ 2) の塔の生成元 λₙ を明示し、その λ-adic 付値が正確に 1
（＝ λₙ は各塔レベルで一意化元 uniformizer・極大イデアルの生成元）**
であることを全レベルで閉じる。issue #36（B-1 残件）の
「塔の生成元 λₙ は未形式化」申告のうち **生成元の同定と位数（付値 1）**
の部分を解消する。

  * M193F-1 `rpow_one` — 環冪の一段補題 a^1 = a（one_mul、一般環）
  * M193F-2 `towerGen` — **塔の生成元 λₙ := (towerLevel p n).lam の明示**
  * M193F-3 `towerGen_regular` / `towerGen_not_unit` — λₙ は正則かつ
    非単元（M144 tower_lam_regular・M111 tower_lam_not_unit の言い換え）
  * M193F-4 `towerGen_val_ge_one` — **λₙ ∈ (λₙ)**（付値 ≥ 1、
    M151F-4a を a^1 = a で λₙ 自身へ）
  * M193F-5 `towerGen_not_val_two` — **λₙ ∉ (λₙ²)**（付値 ≱ 2、
    M151F-5 lam_pow_strict の j=1 版、厳密降下）
  * M193F-6 `towerGen_val_exact` — **λₙ ∈ (λₙ^k) ↔ k ≤ 1**
    （M151F-6 lam_pow_val_exact の j=1 版）: 生成元の付値は
    正確に 1 = **λₙ は各レベルで一意化元**
  * M193F-7 `LambdaTowerGenData` / `lambdaTowerGenData` /
    `lambdaTowerGen_exists` — 総括レコードと witness・存在

意義: M151F は λₙ の**冪** λₙ^j に対する付値の井戸定義性を与えたが、
本層はそれを塔の**生成元** λₙ 自身へ特殊化し、「λₙ は各塔レベル
（n ≥ 2 を含む全 n）で極大イデアルの生成元＝一意化元（付値 1）」
という B-1 の生成元同定を明示的に切り出す。tower_shape の Eisenstein
関係式 πₙλₙ + λₙ^p = ι(λₙ₋₁) と合わせ、λₙ は次数 p^n(p−1) の分岐
塔の各段の一意化元である。

正直な限定: 本層が閉じるのは **生成元 λₙ の同定とその付値＝位数
（正確に 1・一意化元性）** の斜片のみ。一般の [c]-倍作用の形式群
加法 F(λₙ, ·) 経由の構成、および n ≥ 2 の生成元の完全な構造論
（λₙ の最小多項式・剰余体拡大次数・Galois 軌道の塔版）は
M105〜M107 機構の O_n 版として次層に残る（issue #36 の残余）。
全て選択公理不使用（M151F から propext, Quot.sound を継承、
新規 Classical.choice なし）。サブエージェント並行部品。
-/
import IUT.LambdaValuation

namespace IUT

/-! ## M193F-1: 環冪の一段補題 a^1 = a -/

/-- **定理 (M193F-1): a^1 = a**（一般環）。rpow の succ 展開
    a^1 = a^0·a = 1·a を one_mul で畳む。生成元 λₙ を rpow λₙ 1 と
    同一視し M151F の冪版補題を λₙ 自身へ持ち込む糊。 -/
theorem rpow_one (R : CRing) (a : R.carrier) : rpow R a 1 = a := by
  show R.mul R.one a = a
  exact R.one_mul a

/-! ## M193F-2: 塔の生成元 λₙ の明示 -/

/-- **M193F-2: 塔の生成元** λₙ := (towerLevel p n).lam。各塔レベル
    O_{n+1} = towerLevel p n の一意化元を生成元として明示する。 -/
def towerGen (p : Nat) (n : Nat) : (towerLevel p n).ring.carrier :=
  (towerLevel p n).lam

/-! ## M193F-3: λₙ は正則かつ非単元 -/

/-- **定理 (M193F-3a): λₙ は正則**（M144 tower_lam_regular）。 -/
theorem towerGen_regular (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    IsRegularElem (towerLevel p n).ring (towerGen p n) :=
  tower_lam_regular p hp n

/-- **定理 (M193F-3b): λₙ は非単元** — λₙ·v ≠ 1（∀ v）
    （M111 tower_lam_not_unit）。極大イデアルの生成元であることの
    片翼。 -/
theorem towerGen_not_unit (p : Nat) (hp : 2 ≤ p) (n : Nat)
    (v : (towerLevel p n).ring.carrier) :
    (towerLevel p n).ring.mul (towerGen p n) v ≠ (towerLevel p n).ring.one :=
  tower_lam_not_unit p hp n v

/-! ## M193F-4: 付値 ≥ 1 — λₙ ∈ (λₙ) -/

/-- **定理 (M193F-4): λₙ ∈ (λₙ)**（付値 ≥ 1）。M151F-4a
    `lam_pow_self_val`（λ^1 は値 ≥ 1）を a^1 = a で λₙ 自身へ。
    生成元は自明に自らの生成する極大イデアルに属する。 -/
theorem towerGen_val_ge_one (p : Nat) (n : Nat) :
    IsValAtLeast (towerLevel p n).ring (towerGen p n) (towerGen p n) 1 := by
  have h := lam_pow_self_val (towerLevel p n).ring (towerGen p n) 1
  rw [rpow_one] at h
  exact h

/-! ## M193F-5: 付値 ≱ 2 — λₙ ∉ (λₙ²) -/

/-- **定理 (M193F-5): λₙ ∉ (λₙ²)**（付値 ≱ 2、厳密降下）。M151F-5
    `lam_pow_strict`（λ 正則・非単元なら λ^1 ∉ (λ^{1+1})）を
    a^1 = a で λₙ 自身へ。**λₙ の付値は 2 に届かない** ので
    位数（付値）は正確に 1 = λₙ は真の一意化元（π のような
    より深い元ではない）。 -/
theorem towerGen_not_val_two (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    ¬ IsValAtLeast (towerLevel p n).ring (towerGen p n) (towerGen p n) 2 := by
  have h := lam_pow_strict (towerLevel p n).ring
    (tower_lam_regular p hp n) (tower_lam_not_unit p hp n) 1
  rw [rpow_one] at h
  exact h

/-! ## M193F-6: 排他性 — 生成元の付値は正確に 1 -/

/-- **定理 (M193F-6): λₙ ∈ (λₙ^k) ↔ k ≤ 1**（生成元の付値＝位数は
    正確に 1）。M151F-6 `lam_pow_val_exact` の j=1 版を a^1 = a で
    λₙ 自身へ。**λₙ は各塔レベル（n ≥ 2 を含む）で極大イデアルの
    生成元＝一意化元 uniformizer**: 所属レベルの最大値がちょうど 1。 -/
theorem towerGen_val_exact (p : Nat) (hp : 2 ≤ p) (n : Nat) (k : Nat) :
    IsValAtLeast (towerLevel p n).ring (towerGen p n) (towerGen p n) k
      ↔ k ≤ 1 := by
  have h := lam_pow_val_exact (towerLevel p n).ring
    (tower_lam_regular p hp n) (tower_lam_not_unit p hp n) 1 k
  rw [rpow_one] at h
  exact h

/-! ## M193F-7: 総括 -/

/-- **M193F-7a: 総括** — Λₙ 塔の生成元 λₙ と位数（付値 1・一意化元性）
    のデータ: 生成元の明示・正則性・非単元性・付値 ≥ 1・付値 ≱ 2・
    排他性（付値正確に 1）。 -/
structure LambdaTowerGenData (p : Nat) (hp : 2 ≤ p) where
  /-- 塔の生成元 λₙ := (towerLevel p n).lam。 -/
  gen : ∀ n, (towerLevel p n).ring.carrier
  /-- λₙ は正則。 -/
  gen_regular : ∀ n, IsRegularElem (towerLevel p n).ring (gen n)
  /-- λₙ は非単元（極大イデアルの生成元）。 -/
  gen_not_unit : ∀ n (v : (towerLevel p n).ring.carrier),
    (towerLevel p n).ring.mul (gen n) v ≠ (towerLevel p n).ring.one
  /-- λₙ ∈ (λₙ)（付値 ≥ 1）。 -/
  gen_val_ge_one : ∀ n,
    IsValAtLeast (towerLevel p n).ring (gen n) (gen n) 1
  /-- λₙ ∉ (λₙ²)（付値 ≱ 2・厳密降下）。 -/
  gen_not_val_two : ∀ n,
    ¬ IsValAtLeast (towerLevel p n).ring (gen n) (gen n) 2
  /-- 排他性: λₙ ∈ (λₙ^k) ↔ k ≤ 1（付値正確に 1・一意化元）。 -/
  gen_val_exact : ∀ n k,
    IsValAtLeast (towerLevel p n).ring (gen n) (gen n) k ↔ k ≤ 1

/-- **M193F-7b: witness** — towerGen が生成元データを成す
    （純レコード、選択公理不使用）。 -/
def lambdaTowerGenData (p : Nat) (hp : 2 ≤ p) : LambdaTowerGenData p hp where
  gen := towerGen p
  gen_regular := towerGen_regular p hp
  gen_not_unit := towerGen_not_unit p hp
  gen_val_ge_one := towerGen_val_ge_one p
  gen_not_val_two := towerGen_not_val_two p hp
  gen_val_exact := towerGen_val_exact p hp

/-- **M193F-7c: 存在定理（ヘッドライン）** — Λₙ 塔は各レベルで
    一意化元 λₙ（付値正確に 1・極大イデアルの生成元）を持つ。
    柱B B-1（塔の生成元 λₙ の同定と位数）の一歩。 -/
theorem lambdaTowerGen_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaTowerGenData p hp) :=
  ⟨lambdaTowerGenData p hp⟩

end IUT
