/-
# M243F: λ-塔分岐 exact 付値の総括 capstone（柱B B-1・束ね capstone）

M222F `IUT/LambdaTowerRamif.lean`・M226F `IUT/LambdaTowerExactRamif.lean`・
M235F `IUT/LambdaTowerPiValBound.lean` の 3 層で個別に確立された、
λ-塔（Λₙ 塔）の分岐付値に関する成果を **一つの証明記録に束ねる**。
本モジュールは **新規の数学的主張を一切持たない**（新規証明ゼロ）。
全フィールドは既存定理 `tower_pi_val_ge_one` / `base_pi_val_exact` /
`tower_pi_val_ge_p` / `towerGen_transition_val_exact_uncond`（+ 任意で
`towerGen_transition_val_exact_of_pi`）をそのまま代入するだけで埋まる
（M224F `IUT/FormalGroupCapstone.lean` と同じ束ね capstone イディオム）。

* M243F-1（B-1a）`pi_val_ge_one` — π_n ∈ (λ_n)（付値 ≥ 1）が
  **全塔レベル・無条件**で成り立つ（M222F-1 `tower_pi_val_ge_one`）。
* M243F-2（B-1b）`base_exact` — 基点の厳密分岐: π_0 ∈ (λ_0^k) ⇔ k ≤ p−1、
  すなわち **v(π_0) = p−1** が正確に確定する（M222F-2
  `base_pi_val_exact`）。
* M243F-3（B-1c）`pi_val_ge_p` — 上位レベルの π の付値下界
  v(π_{n+1}) ≥ p が **全 n・無条件**で成り立つ（M235F-2
  `tower_pi_val_ge_p`）。
* M243F-4（B-1d, ヘッドライン）`transition_exact` — 塔遷移像 ι(λₙ) の
  **exact 付値 v(ι(λₙ)) = p の完全等号**が **仮定なし**で成り立つ
  （M235F-3 `towerGen_transition_val_exact_uncond`、M226F-6 の分岐入力
  v(π_{n+1}) ≥ p を discharge 済み）。
* M243F-5（参照・任意）`transition_exact_of_pi` — 上記無条件版の
  遡源となった **条件付き版**（M226F-6
  `towerGen_transition_val_exact_of_pi`）をそのまま参照フィールドとして
  併載する。分岐入力 v(π_{n+1}) ≥ p を仮定すれば ι(λₙ) の exact 付値が
  p に等しいという、無条件版の根拠を辿れるようにする。
* M243F-6 `LambdaTowerRamifCapstoneData` / `lambdaTowerRamifCapstoneData` /
  `lambdaTowerRamifCapstone_exists` — 総括レコードと witness・存在。

**意義**: 柱B B-1（λ-塔の分岐）で個別に積み上げられた
(i) 分岐入力 π_n ∈ (λ_n) の無条件確立（M222F）、
(ii) 基点の厳密分岐 e = p−1（M222F）、
(iii) π の付値下界 v(π_{n+1}) ≥ p の無条件確立（M235F）、
(iv) 遷移像 ι(λₙ) の exact 付値 v = p の無条件確立（M235F、M226F の
discharge）
を、共通パラメータ (p : Nat) (hp : 2 ≤ p) の下で一つの型
`LambdaTowerRamifCapstoneData` に固定し、new proof を一切追加せずに
3 モジュール（M222F・M226F・M235F）の合流点として閉じることを機械的に
証明する。

**正直な限定**: 本 capstone が束ねるのは
「λ-塔分岐の下界 v(π_n) ≥ 1（全レベル）・基点の厳密分岐 e = p−1・
π の下界 v(π_{n+1}) ≥ p（全レベル）・遷移像の exact 付値 v(ι(λₙ)) = p
（全レベル）が無条件に揃った」ことの certification のみである。
依然として **π_{n+1} の付値の完全等式**（分岐帰納
v(π_{n+1}) = p·v(π_n) のちょうどの実現・分岐指数 e = p の π 側での
直接確定）は未達（M222F/M235F の正直申告どおり、塔版 Eisenstein 関係式
が本塔で成立しないため剰余体拡大次数 f と分岐指数 e の ef=[L:K] 簿記を
要し次層に残る）。本モジュールはこの限定を変えず、既存 3 層の成果を
並べて束ねるのみである。

全て選択公理不使用（M222F/M226F/M235F から propext, Quot.sound を
継承、新規 Classical.choice を証明本体で導入しない）。サブエージェント
tier S（sonnet）・束ね capstone。
-/
import IUT.LambdaTowerPiValBound

namespace IUT

/-! ## M243F-6: λ-塔分岐 exact 付値の総括データ -/

/-- **λ-塔分岐 exact 付値 capstone データ（M243F-6）**: 素数パラメータ
    p・`hp : 2 ≤ p` に対し、分岐入力の無条件確立（π_n ∈ (λ_n)）・基点の
    厳密分岐（e = p−1）・π の付値下界の無条件化（v(π_{n+1}) ≥ p）・
    遷移像の exact 付値の無条件化（v(ι(λₙ)) = p）の 4 段（+ 参照として
    条件付き版）を一つの証明記録に束ねる。「柱B B-1 λ-塔分岐: 下界の
    無条件確立 → 基点の厳密分岐 → π 下界の無条件化 → 遷移像 exact 付値
    の無条件化」の単一証人。 -/
structure LambdaTowerRamifCapstoneData (p : Nat) (hp : 2 ≤ p) where
  /-- M243F-1（M222F-1）: ∀ n, π_n ∈ (λ_n)（付値 ≥ 1・全レベル・
      無条件）。 -/
  pi_val_ge_one : ∀ n,
    IsValAtLeast (towerLevel p n).ring (towerGen p n) (towerLevel p n).pi 1
  /-- M243F-2（M222F-2）: 基点の厳密分岐——π_0 ∈ (λ_0^k) ⇔ k ≤ p−1
      （v(π_0) = p−1）。 -/
  base_exact : ∀ k,
    IsValAtLeast (eisRing p) (eisLambda p)
        ((eisOf p).map ((toZp p).map ((p : Nat) : Int))) k
      ↔ k ≤ p - 1
  /-- M243F-3（M235F-2）: ∀ n, 上位レベルの π の付値下界
      v(π_{n+1}) ≥ p（π_{n+1} ∈ (λ_{n+1}^p)）、仮定なし。 -/
  pi_val_ge_p : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      (towerLevel p (n + 1)).pi p
  /-- M243F-4（M235F-3, ヘッドライン）: ∀ n k, 遷移像 ι(λₙ) は
      ι(λₙ) ∈ (λ_{n+1}^k) ⇔ k ≤ p、すなわち v(ι(λₙ)) = p の完全等号を
      仮定なしで。 -/
  transition_exact : ∀ n k,
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
        ((towerHom p n).map (towerGen p n)) k
      ↔ k ≤ p
  /-- M243F-5（参照・任意、M226F-6）: 条件付き版——v(π_{n+1}) ≥ p を
      明示仮定すれば ι(λₙ) ∈ (λ_{n+1}^k) ⇔ k ≤ p。上の無条件版
      `transition_exact` の遡源。 -/
  transition_exact_of_pi : ∀ n,
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      (towerLevel p (n + 1)).pi p →
    ∀ k,
      IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
          ((towerHom p n).map (towerGen p n)) k
        ↔ k ≤ p

/-- **証人（M243F-6）**: 本モジュールが柱B B-1 λ-塔分岐 exact 付値の
    4 段（+ 参照 1 段）を実際に一つのデータへ束ねる。全フィールドは
    既存 def/定理の代入のみ（新規証明ゼロ）。 -/
def lambdaTowerRamifCapstoneData (p : Nat) (hp : 2 ≤ p) :
    LambdaTowerRamifCapstoneData p hp where
  pi_val_ge_one := tower_pi_val_ge_one p hp
  base_exact := base_pi_val_exact p hp
  pi_val_ge_p := tower_pi_val_ge_p p hp
  transition_exact := towerGen_transition_val_exact_uncond p hp
  transition_exact_of_pi := fun n hpi k =>
    towerGen_transition_val_exact_of_pi p hp n hpi k

/-- **定理 (M243F-6): λ-塔分岐 exact 付値 capstone データの存在** —
    柱B B-1（λ-塔の分岐）: 分岐入力の無条件確立（π_n ∈ (λ_n)）→
    基点の厳密分岐（e = p−1）→ π 下界の無条件化（v(π_{n+1}) ≥ p）→
    遷移像 exact 付値の無条件化（v(ι(λₙ)) = p）の全段が無矛盾に存在する
    （完成した柱B B-1 部分プログラムの単一証明記録としての締めくくり）。 -/
theorem lambdaTowerRamifCapstone_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (LambdaTowerRamifCapstoneData p hp) :=
  ⟨lambdaTowerRamifCapstoneData p hp⟩

end IUT
