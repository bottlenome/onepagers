/-
# M203F: Λₙ 塔の遷移と付値の層間整合（柱B B-1 Slice B・並行部品）

M193F（塔の生成元 λₙ の同定・付値正確に 1）と M109（塔の環骨格
towerHom・tower_shape・tower_torsion）・M151F（λ-adic 付値の階段
IsValAtLeast）の直上に立ち、**塔の推移射 towerHom による生成元 λₙ の
層間遷移**と、その遷移が**上位レベルの極大イデアルへ落ちる（付値 ≥ 1・
順序＝濾過の保存）**ことを閉じる。issue #36（B-1 残件）の
「塔の生成元の層間整合（遷移の記述）」の斜片を解消する。

  * M203F-1 `ringF_val_ge_one` — 一般環の補題: f_π(λ) = π·λ + λ^p は
    イデアル (λ) に属する（付値 ≥ 1）。証人 π + λ^{p−1}、
    右分配律 + rpow の succ 展開（1 ≤ p）
  * M203F-2 `towerGen_transition` — **遷移の記述**: 推移射は生成元
    λₙ を上位レベルの f_π(λ_{n+1}) へ送る（tower_shape の言い換え、
    towerGen による生成元表示）
  * M203F-3 `towerGen_transition_val` — **順序保存（本丸）**: 生成元
    λₙ の遷移像 ι(λₙ) = f_π(λ_{n+1}) は上位レベルで付値 ≥ 1
    （＝上位レベルの極大イデアル (λ_{n+1}) に属する）。M203F-1 を
    塔レベルへ食わせる: 塔の推移射は一意化元を極大イデアルへ写す
    **局所準同型（濾過保存）**
  * M203F-4 `towerGen_torsion` — 捻れの生成元表示: [π^{n+1}]λₙ = 0
    （M109-7c tower_torsion の towerGen 言い換え）
  * M203F-5 `LambdaTowerTransData` / `lambdaTowerTransData` /
    `lambdaTowerTrans_exists` — 総括レコードと witness・存在

意義: M193F は各レベル単体での生成元 λₙ の付値（正確に 1・一意化元性）
を切り出したが、本層はそれを**層間の遷移**へ持ち上げる:
推移射 towerHom は λₙ を f_π(λ_{n+1})（＝ tower_shape の右辺）へ送り、
その像が上位レベルの極大イデアル (λ_{n+1}) に属する。すなわち
**塔の推移射は各段の一意化元を次段の極大イデアルへ写す濾過保存写像**
であり、λ-adic 付値の塔（M151F）が層間で整合的に持ち上がる。
tower_shape の Eisenstein 関係式 π_{n+1}λ_{n+1} + λ_{n+1}^p = ι(λₙ) が、
右辺 ι(λₙ) の付値 ≥ 1 を左辺の分解から直接与える。

正直な限定: 本層 Slice B が閉じるのは **遷移の記述（像 = f_π(λ_{n+1})）
と順序保存（像 ∈ (λ_{n+1})・付値 ≥ 1）** の斜片のみ。像の付値が
正確に幾つか（ι(λₙ) の付値 = p か否か・分岐指数 e の実現）は
上位レベルの λ_{n+1} 正則性を要する精密化として次層に残る。
一般の [c]-倍作用の形式群加法 F(λₙ, ·) 経由の構成、および n ≥ 2 の
生成元の完全な構造論（最小多項式・剰余体拡大・Galois 軌道の塔版）は
M105〜M107 機構の O_n 版として次層（issue #36 の残余）。
全て選択公理不使用（M193F/M151F から propext, Quot.sound を継承、
新規 Classical.choice なし）。サブエージェント並行部品。
-/
import IUT.LambdaTowerGen
import IUT.EisTowerRings

namespace IUT

/-! ## M203F-1: 一般環の補題 — f_π(λ) は (λ) に属する（付値 ≥ 1） -/

/-- **定理 (M203F-1): f_π(λ) ∈ (λ)**（一般環、1 ≤ p）。
    f_π(λ) = π·λ + λ^p = (π + λ^{p−1})·λ。証人 h = π + λ^{p−1}、
    λ^p = λ^{p−1}·λ（rpow の succ 展開・(p−1)+1 = p）と右分配律で畳む。
    塔の関係式 tower_shape の右辺 ι(λₙ) の付値下界を与える糊。 -/
theorem ringF_val_ge_one (p : Nat) (hp : 1 ≤ p) (R : CRing)
    (pi lam : R.carrier) :
    IsValAtLeast R lam (ringF p R pi lam) 1 := by
  have hpe : R.mul (rpow R lam (p - 1)) lam = rpow R lam p := by
    have h : (p - 1) + 1 = p := Nat.sub_add_cancel hp
    show rpow R lam ((p - 1) + 1) = rpow R lam p
    rw [h]
  refine ⟨R.add pi (rpow R lam (p - 1)), ?_⟩
  show R.add (R.mul pi lam) (rpow R lam p)
      = R.mul (R.add pi (rpow R lam (p - 1))) (rpow R lam 1)
  rw [rpow_one, CRing.right_distrib, hpe]

/-! ## M203F-2: 遷移の記述 — 推移射は λₙ を f_π(λ_{n+1}) へ送る -/

/-- **定理 (M203F-2): 遷移の記述** — 塔の推移射 towerHom は生成元
    λₙ を上位レベルの f_π(λ_{n+1}) = π_{n+1}λ_{n+1} + λ_{n+1}^p へ送る。
    M109-6d tower_shape（f(λ_{n+1}) = ι(λₙ)）の対称・towerGen 表示。 -/
theorem towerGen_transition (p : Nat) (n : Nat) :
    (towerHom p n).map (towerGen p n)
      = ringF p (towerLevel p (n + 1)).ring (towerLevel p (n + 1)).pi
          (towerGen p (n + 1)) :=
  (tower_shape p n).symm

/-! ## M203F-3: 順序保存（本丸）— 遷移像は上位の極大イデアルに属する -/

/-- **定理 (M203F-3): 順序保存（本丸）** — 生成元 λₙ の遷移像
    ι(λₙ) = f_π(λ_{n+1}) は上位レベル O_{n+2} で付値 ≥ 1、すなわち
    上位レベルの極大イデアル (λ_{n+1}) に属する。M203F-1 を塔レベル
    R = (towerLevel p (n+1)).ring、λ = λ_{n+1} へ食わせる。
    **塔の推移射 towerHom は各段の一意化元 λₙ を次段の極大イデアル
    へ写す濾過保存（局所準同型）**であり、λ-adic 付値の塔が層間で
    整合的に持ち上がる。 -/
theorem towerGen_transition_val (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerHom p n).map (towerGen p n)) 1 := by
  rw [towerGen_transition p n]
  exact ringF_val_ge_one p (by omega) (towerLevel p (n + 1)).ring
    (towerLevel p (n + 1)).pi (towerGen p (n + 1))

/-! ## M203F-4: 捻れの生成元表示 -/

/-- **定理 (M203F-4): [π^{n+1}]λₙ = 0**（生成元表示）。
    M109-7c tower_torsion の towerGen 言い換え: 生成元 λₙ は
    f_π の n+1 回反復で消える π^{n+1}-捻れ点。 -/
theorem towerGen_torsion (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    ringFIter p (towerLevel p n).ring (towerLevel p n).pi (n + 1)
      (towerGen p n)
      = (towerLevel p n).ring.zero :=
  tower_torsion p hp n

/-! ## M203F-5: 総括 -/

/-- **M203F-5a: 総括** — Λₙ 塔の遷移と付値の層間整合データ:
    生成元の明示・遷移の記述（像 = f_π(λ_{n+1})）・順序保存
    （像 ∈ (λ_{n+1})）・捻れ（π^{n+1}-torsion）・付値正確に 1。 -/
structure LambdaTowerTransData (p : Nat) (hp : 2 ≤ p) where
  /-- 塔の生成元 λₙ := (towerLevel p n).lam。 -/
  gen : ∀ n, (towerLevel p n).ring.carrier
  /-- 遷移の記述: 推移射は λₙ を f_π(λ_{n+1}) へ送る。 -/
  transition : ∀ n, (towerHom p n).map (gen n)
    = ringF p (towerLevel p (n + 1)).ring (towerLevel p (n + 1)).pi
        (gen (n + 1))
  /-- 順序保存: 遷移像は上位の極大イデアル (λ_{n+1}) に属する（付値 ≥ 1）。 -/
  transition_val : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      ((towerHom p n).map (gen n)) 1
  /-- 捻れ: [π^{n+1}]λₙ = 0。 -/
  torsion : ∀ n, ringFIter p (towerLevel p n).ring (towerLevel p n).pi (n + 1)
    (gen n) = (towerLevel p n).ring.zero
  /-- 付値正確に 1: λₙ ∈ (λₙ^k) ↔ k ≤ 1（各レベルの一意化元性）。 -/
  val_exact : ∀ n k,
    IsValAtLeast (towerLevel p n).ring (gen n) (gen n) k ↔ k ≤ 1

/-- **M203F-5b: witness** — towerGen が遷移データを成す
    （純レコード、選択公理不使用）。 -/
def lambdaTowerTransData (p : Nat) (hp : 2 ≤ p) : LambdaTowerTransData p hp where
  gen := towerGen p
  transition := towerGen_transition p
  transition_val := towerGen_transition_val p hp
  torsion := towerGen_torsion p hp
  val_exact := towerGen_val_exact p hp

/-- **M203F-5c: 存在定理（ヘッドライン）** — Λₙ 塔の推移射は各段の
    一意化元 λₙ を次段の極大イデアルへ写す（遷移の記述 + 濾過保存）。
    柱B B-1（塔の生成元の層間整合）の一歩。 -/
theorem lambdaTowerTrans_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaTowerTransData p hp) :=
  ⟨lambdaTowerTransData p hp⟩

end IUT
