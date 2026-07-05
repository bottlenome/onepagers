/-
# M246F: 塔の剰余射の全射性 — 剰余体は全レベルで ℤ/p（f = 1・完全分岐）
        （柱B B-1・ef=[L:K] 簿記の f 側スライス）

M111 `IUT/ResidueTower.lean`（剰余射 ρₙ : Oₙ → ℤ/p の再帰構成・塔両立・
非自明性）の直上に立つ。

背景（M235F/M239F/M243F の正直な限定）:
  * M235F `IUT/LambdaTowerPiValBound.lean`・M239F
    `IUT/LambdaTowerPiValGeom.lean`・M243F
    `IUT/LambdaTowerRamifCapstone.lean` はいずれも「π_{n+1} の付値の
    **完全等式** v(π_{n+1}) = p·v(π_n) は未達。分岐指数 e と**剰余体
    拡大次数 f** の **ef = [L:K] 簿記**を要し次層に残る」と正直申告して
    いた。これらの層は e 側（分岐・付値）の下界を無条件に積み上げたが、
    **f 側（剰余体拡大次数）**は手つかずだった。
  * M111 は剰余射 ρₙ : Oₙ → ℤ/p を全レベルで構成し（`towerRes`）、塔
    両立（`towerRes_compat`）と非自明性（Oₙ ≠ 0・λₙ/πₙ 非単元）まで
    与えたが、ρₙ が **ℤ/p に全射**であること——すなわち**剰余体拡大が
    自明（f = 1）で塔が完全分岐（totally ramified）**であること——は
    形式化していなかった。

本層はこの **f 側の一片**を無条件に閉じる。すなわち、各レベルの剰余射
ρₙ : Oₙ → ℤ/p は**全射**であり、剰余体は塔を昇っても ℤ/p のまま
**大きくならない（剰余体拡大次数 f = 1）**。証明の骨格:

  * **基底の全射**: 任意の剰余類 c ∈ ℤ/p は整数代表 a を持つ
    （`Quot.exists_rep`）。基底環 O₀ = ℤ_p[[X]]/(E) の定数元
    ι_ℤ(a) := (eisOf)(toZp(a)) を取ると、その剰余像は定数項の mod p、
    すなわち ρ₀(ι_ℤ(a)) = (a mod p) = c（`eisRes` の定義計算、
    M111-3a `eisRes_pi` と同じ `show` 簡約）。よって ρ₀ は全射。
  * **上位レベルへの持ち上げ**: 塔両立 M111-7 `towerRes_compat`
    （ρ_{n+1}(ι(x)) = ρ_n(x)）により、ρ_n の像に入る任意の c は
    ρ_{n+1} の像にも入る（x の推移射像 ι(x) が証人）。よって n の帰納で
    **全レベルの ρ_n が全射**。剰余体は塔で不変 = ℤ/p（f = 1）。

内容:
  * M246F-1 `eisRes_surjective` — **基底の全射**: 基底剰余射
    ρ₀ = eisRes : O₀ → ℤ/p は全射（整数代表の定数元が証人）。
  * M246F-2 `tower_res_surjective` — **全レベルの全射（本丸）**:
    ∀ n, ρ_n = (towerRes p hp n).res : Oₙ → ℤ/p は全射。基底
    （M246F-1）を塔両立（M111-7）で n について持ち上げる。剰余体拡大
    次数 f = 1（完全分岐塔）の形式化。
  * M246F-3 `TowerResidueSurjData` / `towerResidueSurjData` /
    `towerResidueSurj_exists` — 総括レコード（全レベルの全射・塔両立・
    λₙ/πₙ の剰余消滅）と witness・存在。

意義: M235F/M239F/M243F が積み上げた e 側（分岐指数・付値下界）に対し、
本層は **ef = [L:K] 簿記の f 側（剰余体拡大次数 f = 1）**を無条件に
確定する。ρₙ の全射性は「剰余体が塔を昇っても ℤ/p のまま」——
**完全分岐塔（residue extension trivial）**——を意味し、e 側の付値成長
（M239F の 2^{n+1}(p−1)）が丸ごと分岐指数 e に乗る（剰余体には逃げ場が
ない）ことの構造的裏付けを与える。

正直な限定:
  * 本層が確定するのは **剰余体拡大次数 f = 1（ρₙ の全射性・剰余体が
    全レベルで ℤ/p）**まで。**分岐指数 e の完全な値**（v(π_{n+1}) の
    exact 等式・ef = [L:K] の等式そのもの・拡大次数 [Oₙ:O₀] = p^{…} の
    確定）は依然未達（M235F/M239F/M243F の正直申告どおり、次層に残る）。
    本層は f 側を単独で閉じるのみで、e と積 ef を結ぶ簿記の完成では
    ない。
  * 「剰余体 = ℤ/p」は ρₙ の**全射性**（値域が ℤ/p 全体）として形式化
    する。ρₙ の**核が極大イデアル**であること・剰余体が**体**である
    ことの完全な同一視（O_n / ker ≅ ℤ/p の環同型）は本層では扱わない
    （全射性 + M111 の λₙ/πₙ ∈ ker で骨格は与えるが、核 = (λₙ) の等式は
    別枝）。

全て選択公理不使用（M111/EisensteinRing/LocalCFT/Ring から propext,
Quot.sound を継承、新規 Classical.choice を証明本体で導入しない）。
サブエージェント並行部品（tier M）。
-/
import IUT.ResidueTower

namespace IUT

/-! ## M246F-1: 基底の全射 — ρ₀ = eisRes : O₀ → ℤ/p は全射 -/

/-- **定理 (M246F-1): 基底剰余射の全射性** — 基底剰余射
    ρ₀ = `eisRes p hp` : O₀ = ℤ_p[[X]]/(E) → ℤ/p は全射。
    任意の剰余類 c ∈ ℤ/p は整数代表 a を持ち（`Quot.exists_rep`）、
    定数元 ι_ℤ(a) = (eisOf)(toZp(a)) の剰余像は定数項の mod p 像
    = (a mod p) = c（M111-3a `eisRes_pi` と同じ `show` 簡約で
    `(projRing p 1).map ((toZp p).map a)` へ落ちる）。 -/
theorem eisRes_surjective (p : Nat) (hp : 2 ≤ p)
    (c : (zmodRing (p ^ 1)).carrier) :
    ∃ x : (eisRing p).carrier, (eisRes p hp).map x = c := by
  obtain ⟨a, ha⟩ := Quot.exists_rep c
  refine ⟨(eisOf p).map ((toZp p).map a), ?_⟩
  show (projRing p 1).map ((toZp p).map a) = c
  exact ha

/-! ## M246F-2: 全レベルの全射（本丸） -/

/-- **定理 (M246F-2, 本丸): 塔の剰余射の全射性** — ∀ n、レベル n の
    剰余射 ρ_n = `(towerRes p hp n).res` : Oₙ → ℤ/p は全射。
    基底（M246F-1 `eisRes_surjective`）を塔両立 M111-7
    `towerRes_compat`（ρ_{n+1}(ι(x)) = ρ_n(x)）で n について持ち上げる:
    ρ_n の像に入る c の証人 x を推移射 ι = `towerHom p n` で運べば、
    ρ_{n+1}(ι(x)) = ρ_n(x) = c。剰余体が塔で不変 = ℤ/p、すなわち
    **剰余体拡大次数 f = 1（完全分岐塔）**の形式化。 -/
theorem tower_res_surjective (p : Nat) (hp : 2 ≤ p) :
    ∀ (n : Nat) (c : (zmodRing (p ^ 1)).carrier),
      ∃ x : (towerLevel p n).ring.carrier,
        (towerRes p hp n).res.map x = c := by
  intro n
  induction n with
  | zero =>
    intro c
    obtain ⟨x, hx⟩ := eisRes_surjective p hp c
    exact ⟨x, hx⟩
  | succ n ih =>
    intro c
    obtain ⟨x, hx⟩ := ih c
    refine ⟨(towerHom p n).map x, ?_⟩
    rw [towerRes_compat p hp n x]
    exact hx

/-! ## M246F-3: 総括 -/

/-- **M246F-3a: 総括** — 塔の剰余射の全射性データ（ef = [L:K] 簿記の
    f 側）: 全レベルで ρ_n : Oₙ → ℤ/p が全射（剰余体 = ℤ/p・f = 1）・
    塔両立（ρ_{n+1} ∘ ι = ρ_n）・λₙ/πₙ の剰余消滅（M111 由来、ρ_n の
    核が極大イデアルを含むことの骨格）。 -/
structure TowerResidueSurjData (p : Nat) (hp : 2 ≤ p) where
  /-- M246F-2: 全レベルで ρ_n : Oₙ → ℤ/p は全射（剰余体 = ℤ/p・
      f = 1・完全分岐塔）。 -/
  res_surjective : ∀ (n : Nat) (c : (zmodRing (p ^ 1)).carrier),
    ∃ x : (towerLevel p n).ring.carrier,
      (towerRes p hp n).res.map x = c
  /-- M111-7: 剰余射は塔の推移射と両立 ρ_{n+1}(ι(x)) = ρ_n(x)
      （剰余体が塔で不変であることの両立性）。 -/
  compat : ∀ (n : Nat) (a : (towerLevel p n).ring.carrier),
    (towerRes p hp (n + 1)).res.map ((towerHom p n).map a)
      = (towerRes p hp n).res.map a
  /-- M111 由来: πₙ の剰余像は 0（πₙ ∈ ker ρ_n・極大イデアル）。 -/
  res_pi_zero : ∀ n,
    (towerRes p hp n).res.map (towerLevel p n).pi
      = (zmodRing (p ^ 1)).zero
  /-- M111 由来: λₙ の剰余像は 0（λₙ ∈ ker ρ_n・極大イデアル）。 -/
  res_lam_zero : ∀ n,
    (towerRes p hp n).res.map (towerLevel p n).lam
      = (zmodRing (p ^ 1)).zero

/-- **M246F-3b: witness** — `tower_res_surjective`（本層）と M111 の
    `towerRes_compat` / `(towerRes …).res_pi` / `.res_lam` で純レコードを
    充填（選択公理不使用）。 -/
def towerResidueSurjData (p : Nat) (hp : 2 ≤ p) :
    TowerResidueSurjData p hp where
  res_surjective := tower_res_surjective p hp
  compat := towerRes_compat p hp
  res_pi_zero := fun n => (towerRes p hp n).res_pi
  res_lam_zero := fun n => (towerRes p hp n).res_lam

/-- **M246F-3c: 存在定理（ヘッドライン）** — 塔の各レベルの剰余射
    ρ_n : Oₙ → ℤ/p は**全射**であり、剰余体は塔を昇っても ℤ/p のまま
    （**剰余体拡大次数 f = 1・完全分岐塔**）。M235F/M239F/M243F が
    積み上げた e 側（分岐指数・付値下界）に対する ef = [L:K] 簿記の
    **f 側**の一片。柱B B-1（λ-塔の剰余構造）の一段。 -/
theorem towerResidueSurj_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (TowerResidueSurjData p hp) :=
  ⟨towerResidueSurjData p hp⟩

end IUT
