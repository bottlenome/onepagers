/-
# M239F: 塔の π の付値の幾何的下界 v(π_{n+1}) ≥ 2^{n+1}(p−1)
        （柱B B-1・M235F 正直申告の parenthetical 主張の形式化）

M235F `IUT/LambdaTowerPiValBound.lean` の直上に立つ。

背景（M235F の正直な限定）:
  * M235F-1 `tower_pi_doubling` は遷移射の**付値倍化**
    （a ∈ (λ_n^k) なら ι(a) ∈ (λ_{n+1}^{k·2})）を無条件に確立した。
  * M235F-2 `tower_pi_val_ge_p` はそれを基点 v(π_0) ≥ p−1 から回して
    **v(π_{n+1}) ≥ p** を無条件確立したが、これは倍化が本来与える
    より強い幾何的成長を **isValAtLeast_mono で p まで潰した**形の
    ステートメントである。M235F の正直申告は
    「本層の倍化は v(π_{n+1}) ≥ 2·v(π_n) の下界（実際は
    v(π_{n+1}) ≥ 2^{n+1}(p−1)）」と、この**幾何的下界を parenthetical に
    言及するのみで形式化していなかった**。

本層はこの parenthetical 主張を実定理へ昇格する。すなわち、
付値倍化（M235F-1）を基点 v(π_0) ≥ p−1（M222F-2）から回すと、
各段で付値が**ちょうど 2 倍**に押し上がるため、

  * v(π_1) ≥ 2·(p−1) = 2^1·(p−1)、
  * v(π_{n+2}) ≥ 2·v(π_{n+1}) ≥ 2·(2^{n+1}(p−1)) = 2^{n+2}(p−1)

と、**塔を昇るごとに π の付値は少なくとも 2 のべきで成長する**。
これは M235F-2 の一様下界 ≥ p を厳密に含む（2^{n+1}(p−1) ≥ p、p ≥ 2）
真に強い成長則であり、**塔の分岐が上位レベルほど深くなる（deeply
ramified tower）**という定量的骨格を無条件に与える。

内容:
  * M239F-1 `tower_pi_val_geom` — **幾何的下界（本丸）**:
    ∀ n, v(π_{n+1}) ≥ 2^{n+1}(p−1)。付値倍化（M235F-1）を基点
    v(π_0) ≥ p−1（M222F-2）から n について帰納で回す。
  * M239F-2 `tower_pi_val_geom_ge_p` — **M235F-2 の再導出**:
    幾何的下界から一様下界 v(π_{n+1}) ≥ p を回収（2^{n+1}(p−1) ≥ p、
    p ≥ 2）。幾何的下界が M235F-2 を真に含むことの確認。
  * M239F-3 `LambdaTowerPiValGeomData` / `lambdaTowerPiValGeomData` /
    `lambdaTowerPiValGeom_exists` — 総括レコードと witness・存在。

意義: M235F が倍化から取り出せる情報を「≥ p」へ潰していたのに対し、
本層は倍化の**幾何的成長を保ったままの下界** v(π_{n+1}) ≥ 2^{n+1}(p−1)
を形式化する。これにより塔の分岐深度が上位レベルで（少なくとも 2 の
べきで）増大することが無条件に確定し、M235F-2 はその系として回収される。

正直な限定:
  * 本層が与えるのは付値の**下界**（幾何的成長）のみであり、上界
    （等号 v(π_{n+1}) = p·v(π_n) の完全な分岐帰納・分岐指数 e の
    ちょうどの実現）は依然与えない。塔版 Eisenstein 関係式が本塔で
    成立せず、剰余体次数 f と分岐指数 e の ef=[L:K] 簿記を要するため
    （M235F/M226F/M222F の正直申告と整合、次層に残る）。
  * 幾何的下界の指数 2^{n+1}(p−1) は倍化 ι(λ_n) ∈ (λ_{n+1}²) の
    「係数 2」に由来する構造的な下界であり、真の分岐指数（各段で
    e = p が期待される）そのものではない（下界であって等号ではない）。
  * 基点 n=0 の v(π_0) = p−1（分岐指数 e = p−1）は M222F-2 が正確に
    確定する別枝であり、本層は上位レベル（n ≥ 0 で π_{n+1}）の下界のみ
    を扱う。

全て選択公理不使用（M235F/M222F/M151F/EisDomain から propext,
Quot.sound を継承、新規 Classical.choice なし）。サブエージェント
並行部品（tier M）。
-/
import IUT.LambdaTowerPiValBound
import IUT.EisDomain

namespace IUT

/-! ## M239F-1: 幾何的下界（本丸）— v(π_{n+1}) ≥ 2^{n+1}(p−1) -/

/-- **定理 (M239F-1, 本丸): 塔の π の付値の幾何的下界** — ∀ n、上位
    レベルの π、すなわち π_{n+1} = (towerLevel p (n+1)).pi は付値
    ≥ 2^{n+1}(p−1)（π_{n+1} ∈ (λ_{n+1}^{2^{n+1}(p−1)})）、**仮定なしで**。
    付値倍化 M235F-1 `tower_pi_doubling` を基点 v(π_0) ≥ p−1
    （M222F-2 `base_pi_val_exact`）から回す:
    基底 v(π_1) ≥ (p−1)·2 = 2^1(p−1)、帰納段
    v(π_{n+2}) ≥ (2^{n+1}(p−1))·2 = 2^{n+2}(p−1)。M235F-2 が
    `isValAtLeast_mono` で p まで潰していた倍化の幾何的成長を、
    下界のまま保った形。 -/
theorem tower_pi_val_geom (p : Nat) (hp : 2 ≤ p) : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      (towerLevel p (n + 1)).pi (2 ^ (n + 1) * (p - 1)) := by
  intro n
  induction n with
  | zero =>
    -- v(π_0) ≥ p−1、倍化で v(π_1) ≥ (p−1)·2 = 2^1(p−1)
    have h0 : IsValAtLeast (towerLevel p 0).ring (towerGen p 0)
        (towerLevel p 0).pi (p - 1) := by
      show IsValAtLeast (eisRing p) (eisLambda p)
        ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) (p - 1)
      exact (base_pi_val_exact p hp (p - 1)).mpr (Nat.le_refl (p - 1))
    have hd := tower_pi_doubling p hp 0 h0
    have eq0 : (p - 1) * 2 = 2 ^ (0 + 1) * (p - 1) := by
      rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_comm]
    rw [eq0] at hd
    exact hd
  | succ n ih =>
    -- v(π_{n+1}) ≥ 2^{n+1}(p−1)、倍化で v(π_{n+2}) ≥ (…)·2 = 2^{n+2}(p−1)
    have hd := tower_pi_doubling p hp (n + 1) ih
    have eq : (2 ^ (n + 1) * (p - 1)) * 2 = 2 ^ (n + 1 + 1) * (p - 1) := by
      rw [Nat.pow_succ 2 (n + 1), Nat.mul_assoc, Nat.mul_comm (p - 1) 2,
        ← Nat.mul_assoc]
    rw [eq] at hd
    exact hd

/-! ## M239F-2: M235F-2 の再導出 — 幾何的下界から一様下界 ≥ p -/

/-- **定理 (M239F-2): 幾何的下界からの一様下界の回収** — ∀ n、
    v(π_{n+1}) ≥ p。幾何的下界 M239F-1 の指数は 2^{n+1}(p−1) ≥ p
    （p ≥ 2 で 2 ≤ 2^{n+1}、`two_le_pow`、かつ 2(p−1) ≥ p）なので、
    `isValAtLeast_mono` で p まで降ろせる。M235F-2 `tower_pi_val_ge_p`
    が幾何的下界 M239F-1 の**系として回収される**ことの確認（幾何的
    下界が M235F-2 を真に含む）。 -/
theorem tower_pi_val_geom_ge_p (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      (towerLevel p (n + 1)).pi p := by
  have hgeom := tower_pi_val_geom p hp n
  have hle : p ≤ 2 ^ (n + 1) * (p - 1) := by
    have hm : 2 ≤ 2 ^ (n + 1) := two_le_pow 2 (by omega) (n + 1) (by omega)
    have h2 : 2 * (p - 1) ≤ 2 ^ (n + 1) * (p - 1) :=
      Nat.mul_le_mul hm (Nat.le_refl (p - 1))
    omega
  exact isValAtLeast_mono (towerLevel p (n + 1)).ring (towerGen p (n + 1))
    (towerLevel p (n + 1)).pi (2 ^ (n + 1) * (p - 1)) p hle hgeom

/-! ## M239F-3: 総括 -/

/-- **M239F-3a: 総括** — 塔の π の付値の幾何的下界データ:
    幾何的下界 v(π_{n+1}) ≥ 2^{n+1}(p−1) と、その系としての一様下界
    v(π_{n+1}) ≥ p。 -/
structure LambdaTowerPiValGeomData (p : Nat) (hp : 2 ≤ p) where
  /-- 塔の生成元 λₙ := (towerLevel p n).lam。 -/
  gen : ∀ n, (towerLevel p n).ring.carrier
  /-- 幾何的下界: v(π_{n+1}) ≥ 2^{n+1}(p−1)（全 n・仮定なし）。 -/
  pi_val_geom : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      (towerLevel p (n + 1)).pi (2 ^ (n + 1) * (p - 1))
  /-- 系としての一様下界: v(π_{n+1}) ≥ p（M235F-2 の回収）。 -/
  pi_val_ge_p : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (gen (n + 1))
      (towerLevel p (n + 1)).pi p

/-- **M239F-3b: witness** — towerGen が幾何的下界データを成す
    （純レコード、選択公理不使用）。 -/
def lambdaTowerPiValGeomData (p : Nat) (hp : 2 ≤ p) :
    LambdaTowerPiValGeomData p hp where
  gen := towerGen p
  pi_val_geom := tower_pi_val_geom p hp
  pi_val_ge_p := tower_pi_val_geom_ge_p p hp

/-- **M239F-3c: 存在定理（ヘッドライン）** — Λₙ 塔の上位レベルの π は、
    **仮定なしで** 付値の幾何的下界 v(π_{n+1}) ≥ 2^{n+1}(p−1) を持つ。
    遷移射 towerHom の付値倍化（ι(λ_n) ∈ (λ_{n+1}²) に由来）を基点
    v(π_0) ≥ p−1 から回すことで、塔を昇るごとに分岐深度が少なくとも
    2 のべきで増大する（deeply ramified tower）ことを定量化する。
    M235F-2 の一様下界 ≥ p はその系。柱B B-1（塔の分岐深度）の一段。 -/
theorem lambdaTowerPiValGeom_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaTowerPiValGeomData p hp) :=
  ⟨lambdaTowerPiValGeomData p hp⟩

end IUT
