/-
# M222F: 塔の分岐指数と π の付値（柱B B-1・並行部品）

M211F（塔遷移 ι(λₙ) の厳密付値へ向けた二項還元）の直上に立つ。
M211F は遷移像 ι(λₙ) = f_π(λ_{n+1}) の付値 ≥ 2 を **唯一の未形式入力
`π_{n+1} ∈ (λ_{n+1})`（上位レベルの π が極大イデアルに属する・分岐入力）**
へ隔離した（M211F-6b `towerGen_transition_val_ge_two_of_pi` が条件付き）。

本層はその隔離された入力を、**塔全レベルで無条件に確立する**:

    π_n ∈ (λ_n)（各塔レベルで π は一意化元の生成する極大イデアルに属する）

を n の帰納で閉じ、M211F の条件を **discharge** する。骨子:

  * **基底 n = 0**: M82F-5c `eis_lambda_pow`（λ_0^{p−1} = −π_0）より
    π_0 = −λ_0^{p−1} ∈ (λ_0^{p−1}) ⊆ (λ_0)（M151F-3b の単調降下、
    1 ≤ p−1）。分岐指数 e = p−1 の基底 Eisenstein 関係式が直接与える
  * **帰納段 n → n+1**: π_{n+1} = ι(π_n)（塔の推移射 towerHom による
    π の像）。帰納法の仮定 π_n = h·λ_n を推移射で運び
    ι(π_n) = ι(h)·ι(λ_n)、そして ι(λ_n) ∈ (λ_{n+1})（M203F-3
    `towerGen_transition_val`）より積の付値の加法性（M161-2
    `isValAtLeast_mul`）で ι(π_n) ∈ (λ_{n+1})。**塔の局所準同型性
    （π を π へ、極大イデアルを極大イデアルへ写す）が入力を伝播**

  * M222F-1 `tower_pi_val_ge_one` — **本丸**: ∀ n, π_n ∈ (λ_n)。
    M211F の隔離入力の無条件確立
  * M222F-2 `base_pi_val_exact` — 基底の厳密分岐: v(π_0) = p−1、すなわち
    π_0 ∈ (λ_0^k) ⇔ k ≤ p−1（λ_0^{p−1} = −π_0・付値の反元不変・
    M151F-6 lam_pow_val_exact）。**基底の分岐指数 e = p−1 を正確に確定**
  * M222F-3 `towerGen_transition_val_ge_two` — **M211F の無条件 discharge**:
    ι(λₙ) ∈ (λ_{n+1}²)（付値 ≥ 2）を条件なしで確立
    （M211F-6b に M222F-1 の入力を食わせる）。M203F の付値 ≥ 1 が
    無条件で付値 ≥ 2 へ上がる
  * M222F-4 `LambdaTowerRamifData` / `lambdaTowerRamifData` /
    `lambdaTowerRamif_exists` — 総括レコードと witness・存在

意義: M211F は遷移像の付値 ≥ 2 を「π_{n+1} ∈ (λ_{n+1})」という上位
レベルの分岐入力に還元して隔離したが、その入力自体が **未証明の
仮定として残っていた**。本層は塔の推移射が π を π へ写す局所準同型
であること（+ 基底の Eisenstein 分岐）から **π_n ∈ (λ_n) を全レベルで
無条件に確立**し、M211F の条件付き付値 ≥ 2 を **無条件へ格上げ**する。
これにより「遷移像 ι(λₙ) は上位の極大イデアルの 2 乗に沈む」が
仮定なしに成り立ち、分岐指数 e = p の実現に向けた鎖の一段が閉じる。

正直な限定: 本層が無条件に閉じるのは **π_n ∈ (λ_n)（各レベルの π が
極大イデアルに属する・付値 ≥ 1）と、それによる遷移像の付値 ≥ 2** まで。
基底 n = 0 では v(π_0) = p−1 を **正確に**確定するが（e = p−1）、上位
レベルの v(π_{n+1}) の**正確な**値（分岐帰納 v(π_{n+1}) = p·v(π_n) の
完全な等式・分岐指数 e = p のちょうどの実現）は、遷移像 ι(λₙ) の
**厳密**付値 = p（下界 ≥ 2 の上界側 = 支配項による厳密同定）と
π_{n+1} の付値の厳密下界 ≥ p−1 を要し、これは次層に残る。塔版の
Eisenstein 関係式 λ_{n+1}^{p−1} = −π_{n+1} は本塔では成立しない
（π_{n+1} = ι(π_n) は下位の π の持ち上げであり新しい一意化元関係を
持たない）ため、付値 ≥ 1 の伝播は本層の局所準同型論法で、正確値は
剰余体拡大次数の塔版を経由する別道が要る。全て選択公理不使用
（M211F/M203F/M161/M151F から propext, Quot.sound を継承、新規
Classical.choice なし）。サブエージェント並行部品。
-/
import IUT.LambdaTowerExactVal

namespace IUT

/-! ## M222F-1: 本丸 — π_n ∈ (λ_n) を全レベルで無条件確立 -/

/-- **定理 (M222F-1, 本丸): ∀ n, π_n ∈ (λ_n)** — 各塔レベルの π
    （= (towerLevel p n).pi）は一意化元 λ_n の生成する極大イデアルに
    属する（付値 ≥ 1）。**M211F が隔離した分岐入力の無条件確立**。

    基底 n=0: M82F-5c `eis_lambda_pow`（λ_0^{p−1} = −π_0）より
    π_0 = −λ_0^{p−1} = (−1)·λ_0^{p−1} ∈ (λ_0^{p−1})、そして 1 ≤ p−1
    ゆえ M151F-3b `isValAtLeast_mono` で (λ_0) へ降下。
    帰納段 n→n+1: π_{n+1} = ι(π_n)。IH で π_n = h·λ_n、推移射で運び
    ι(π_n) = ι(h)·ι(λ_n)、ι(λ_n) ∈ (λ_{n+1})（M203F-3）と
    ι(h) ∈ (λ_{n+1}^0)（M151F-2）を M161-2 `isValAtLeast_mul` に
    食わせ ι(π_n) ∈ (λ_{n+1}^{0+1}) = (λ_{n+1})。 -/
theorem tower_pi_val_ge_one (p : Nat) (hp : 2 ≤ p) : ∀ n,
    IsValAtLeast (towerLevel p n).ring (towerGen p n) (towerLevel p n).pi 1 := by
  intro n
  induction n with
  | zero =>
    -- 基底: π_0 = −λ_0^{p−1} ∈ (λ_0^{p−1}) ⊆ (λ_0)
    show IsValAtLeast (eisRing p) (eisLambda p)
      ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) 1
    have hpe : rpow (eisRing p) (eisLambda p) (p - 1)
        = (eisRing p).neg ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) :=
      eis_lambda_pow p hp
    have hpi0 : (eisOf p).map ((toZp p).map ((p : Nat) : Int))
        = (eisRing p).neg (rpow (eisRing p) (eisLambda p) (p - 1)) := by
      rw [hpe]
      exact (CRing.neg_neg (eisRing p)
        ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))).symm
    have hval : IsValAtLeast (eisRing p) (eisLambda p)
        ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) (p - 1) := by
      refine ⟨(eisRing p).neg (eisRing p).one, ?_⟩
      rw [hpi0]
      show (eisRing p).neg (rpow (eisRing p) (eisLambda p) (p - 1))
        = (eisRing p).mul ((eisRing p).neg (eisRing p).one)
            (rpow (eisRing p) (eisLambda p) (p - 1))
      rw [CRing.neg_mul (eisRing p) (eisRing p).one
          (rpow (eisRing p) (eisLambda p) (p - 1)),
        (eisRing p).one_mul (rpow (eisRing p) (eisLambda p) (p - 1))]
    exact isValAtLeast_mono (eisRing p) (eisLambda p)
      ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) (p - 1) 1
      (by omega) hval
  | succ n ih =>
    -- 帰納段: π_{n+1} = ι(π_n) = ι(h)·ι(λ_n) ∈ (λ_{n+1})
    obtain ⟨h, hh⟩ := ih
    have hpi : (towerLevel p (n + 1)).pi
        = (towerLevel p (n + 1)).ring.mul ((towerHom p n).map h)
            ((towerHom p n).map (towerGen p n)) := by
      show (towerHom p n).map (towerLevel p n).pi
          = (towerLevel p (n + 1)).ring.mul ((towerHom p n).map h)
              ((towerHom p n).map (towerGen p n))
      rw [hh, (towerHom p n).map_mul, rpow_one]
    rw [hpi]
    have hz : IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
        ((towerHom p n).map h) 0 :=
      isValAtLeast_zero (towerLevel p (n + 1)).ring (towerGen p (n + 1))
        ((towerHom p n).map h)
    have ha : IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
        ((towerHom p n).map (towerGen p n)) 1 :=
      towerGen_transition_val p hp n
    exact isValAtLeast_mul hz ha

/-! ## M222F-2: 基底の厳密分岐 v(π_0) = p−1 -/

/-- **定理 (M222F-2): 基底の厳密分岐指数** — π_0 ∈ (λ_0^k) ⇔ k ≤ p−1、
    すなわち **v(π_0) = p−1**（基底 Eisenstein 拡大の分岐指数 e = p−1）。
    λ_0^{p−1} = −π_0（M82F-5c）で付値は反元で不変、λ_0^{p−1} の付値の
    厳密性（M151F-6 `lam_pow_val_exact`、λ_0 正則・非単元）が
    π_0 の所属レベルをちょうど p−1 に切り出す。 -/
theorem base_pi_val_exact (p : Nat) (hp : 2 ≤ p) (k : Nat) :
    IsValAtLeast (eisRing p) (eisLambda p)
        ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) k
      ↔ k ≤ p - 1 := by
  have hpe : rpow (eisRing p) (eisLambda p) (p - 1)
      = (eisRing p).neg ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) :=
    eis_lambda_pow p hp
  have hpi0 : (eisOf p).map ((toZp p).map ((p : Nat) : Int))
      = (eisRing p).neg (rpow (eisRing p) (eisLambda p) (p - 1)) := by
    rw [hpe]
    exact (CRing.neg_neg (eisRing p)
      ((eisOf p).map ((toZp p).map ((p : Nat) : Int)))).symm
  constructor
  · intro hmem
    -- λ_0^{p−1} = −π_0 ∈ (λ_0^k)
    have h2 : IsValAtLeast (eisRing p) (eisLambda p)
        (rpow (eisRing p) (eisLambda p) (p - 1)) k := by
      rw [hpe]
      exact isValAtLeast_neg hmem
    exact (lam_pow_val_exact (eisRing p) (tower_lam_regular p hp 0)
      (tower_lam_not_unit p hp 0) (p - 1) k).mp h2
  · intro hk
    have h2 : IsValAtLeast (eisRing p) (eisLambda p)
        (rpow (eisRing p) (eisLambda p) (p - 1)) k :=
      (lam_pow_val_exact (eisRing p) (tower_lam_regular p hp 0)
        (tower_lam_not_unit p hp 0) (p - 1) k).mpr hk
    rw [hpi0]
    exact isValAtLeast_neg h2

/-! ## M222F-3: M211F の無条件 discharge — ι(λₙ) ∈ (λ_{n+1}²) -/

/-- **定理 (M222F-3): 遷移像の無条件付値 ≥ 2** — 遷移像
    ι(λₙ) = f_π(λ_{n+1}) は上位レベルで付値 ≥ 2（＝ (λ_{n+1}²) に属する）、
    **仮定なしで**。M211F-6b `towerGen_transition_val_ge_two_of_pi`
    （条件付き）に、M222F-1 で無条件確立した分岐入力
    π_{n+1} ∈ (λ_{n+1}) を食わせて condition を discharge。
    M203F の付値 ≥ 1 が無条件で付値 ≥ 2 へ上がる。 -/
theorem towerGen_transition_val_ge_two (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerHom p n).map (towerGen p n)) 2 :=
  towerGen_transition_val_ge_two_of_pi p hp n (tower_pi_val_ge_one p hp (n + 1))

/-! ## M222F-4: 総括 -/

/-- **M222F-4a: 総括** — 塔の分岐指数と π の付値のデータ:
    π_n ∈ (λ_n)（無条件・全レベル）・基底の厳密分岐 v(π_0) = p−1・
    遷移像の無条件付値 ≥ 2（M211F の discharge）。 -/
structure LambdaTowerRamifData (p : Nat) (hp : 2 ≤ p) where
  /-- 塔の生成元 λ_n := (towerLevel p n).lam。 -/
  gen : ∀ n, (towerLevel p n).ring.carrier
  /-- 分岐入力の無条件確立: π_n ∈ (λ_n)（全レベル・付値 ≥ 1）。 -/
  pi_val_ge_one : ∀ n,
    IsValAtLeast (towerLevel p n).ring (gen n) (towerLevel p n).pi 1
  /-- 基底の厳密分岐: v(π_0) = p−1（π_0 ∈ (λ_0^k) ⇔ k ≤ p−1）。 -/
  base_val_exact : ∀ k,
    IsValAtLeast (eisRing p) (eisLambda p)
        ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) k
      ↔ k ≤ p - 1
  /-- M211F の無条件 discharge: ι(λₙ) ∈ (λ_{n+1}²)（付値 ≥ 2）。 -/
  transition_val_ge_two : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      ((towerHom p n).map (gen n)) 2

/-- **M222F-4b: witness** — towerGen が分岐データを成す
    （純レコード、選択公理不使用）。 -/
def lambdaTowerRamifData (p : Nat) (hp : 2 ≤ p) : LambdaTowerRamifData p hp where
  gen := towerGen p
  pi_val_ge_one := tower_pi_val_ge_one p hp
  base_val_exact := base_pi_val_exact p hp
  transition_val_ge_two := towerGen_transition_val_ge_two p hp

/-- **M222F-4c: 存在定理（ヘッドライン）** — Λₙ 塔の各段で π_n は
    一意化元の生成する極大イデアルに属する（分岐入力 π_n ∈ (λ_n) の
    無条件確立）。これにより M211F が隔離した条件が discharge され、
    遷移像 ι(λₙ) の付値 ≥ 2 が無条件に成り立つ。基底の分岐指数
    e = p−1 は正確に確定。柱B B-1（塔の分岐）の一段。 -/
theorem lambdaTowerRamif_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaTowerRamifData p hp) :=
  ⟨lambdaTowerRamifData p hp⟩

end IUT
