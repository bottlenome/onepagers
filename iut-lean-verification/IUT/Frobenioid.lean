/-
  IUT/Frobenioid.lean — M12（Frobenioid 圏論 [FrdI]/[FrdII]）の形式化

  IUT III 定理3.11 (i)(c) は「数体 M_MOD の大域 realified Frobenioid の
  次数（arithmetic degree）が対数殻の log-volume で計算される」と主張
  する。その土台である Frobenioid 論（[FrdI]/[FrdII]）のうち、IUT が
  実際に使う**次数・Frobenius 構造の骨格**を形式化する。

  Frobenioid とは（粗く言って）「基底圏の上の因子モノイドの圏化」で
  あり、IUT で効くのはその次の三つの構造である:
  (1) 因子（直線束）の可換モノイド構造と**次数準同型** deg
  (2) **Frobenius 射** φ_n（次数を n 倍する自己射。Frobenius-like）
  (3) 次数 0 の部分（単数・étale-like）と次数 ≠ 0 の部分の二分法
      —— Θ-link が「Frobenius-like 構造だけを輸送する」ことの土台

  検証する定理（全て sorry なし）:
  * M12-1 `Frobenioid.deg_zero` — deg(0) = 0 は公理から**導出**される
    （モノイド準同型性の帰結。公理に含めず証明する）
  * M12-2 `frob_frob_deg` — Frobenius の合成則 deg(φ_n φ_m x) = nm·deg x
  * M12-3 `frob_not_invertible` — **Frobenius-like 性**: 次数 ≠ 0 の
    対象上で φ_n (n ≥ 2) は不動点を持たない（= 可逆でない）。
    Frobenius 射が圏の「時間の矢」であること（[FrdI] §I3 の
    Frobenius-like / étale-like 二分法）の形式的内容
  * M12-4 `units_etale_like` — 次数 0（単数 = étale-like 部分）は
    全ての Frobenius で次数 0 に留まる（étale-like 性の安定性）
  * M12-5 `gaussianDiv_deg` — **Gaussian 束の次数公式**（M12 → M4 接続）:
    テータ値の束 ⊕_{j=1}^{L} φ_{j²}(x) の次数 = (Σj²)·deg x が
    Frobenioid の公理だけから従う。M4 `sumDeg_eq` の簿記が Frobenioid
    構造に由来することの機械検証
  * M12-6 `frobenioid_realizes_qpilot` — **定理3.11 (i)(c) の骨格**
    （M12 → M5 接続）: 次数＝log-volume 両立データがあれば、
    q-パイロット因子（deg = |log q|）の実現は体積 −|log q| の領域を
    与える——`MultiradialRep` の `vol_q` フィールドの供給源
  * M12-7 `frobenioid_consistent` / `degree_volume_consistent` —
    公理系の無矛盾性（Div = ℤ、deg = id、φ_n = n倍 のモデル）

  **形式化の範囲（正直な申告）**: Frobenioid の圏論的実体（基底圏
  D 上のファイバー構造、poly-isomorphism、分裂 Frobenioid、
  realification の構成）は未形式化。ここで建設したのは IUT III
  定理3.11 (i)(c) が実際に消費する次数・Frobenius・体積両立の
  構造層であり、`DegreeVolumeCompat` の充足（実際の数体の
  Frobenioid で deg = log-volume を証明すること）が残る実質である。
-/
import IUT.Arithmetic
import IUT.Skeleton
import IUT.Multiradial

namespace IUT

/-- **Frobenioid の骨格**: 因子（直線束）の可換モノイド＋次数準同型＋
    Frobenius 自己射の族。realified 次数は Int で代用する
    （Skeleton と同じ正規化規約）。 -/
structure Frobenioid where
  /-- 因子（直線束）の型。 -/
  Div : Type
  /-- テンソル（因子の和）。 -/
  add : Div → Div → Div
  /-- 自明束。 -/
  zero : Div
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_comm : ∀ x y, add x y = add y x
  zero_add : ∀ x, add zero x = x
  /-- 次数準同型（arithmetic degree）。 -/
  deg : Div → Int
  deg_add : ∀ x y, deg (add x y) = deg x + deg y
  /-- Frobenius 射 φ_n（[FrdI] の Frobenius 構造）。 -/
  frob : Nat → Div → Div
  /-- Frobenius は次数を n 倍する。 -/
  frob_deg : ∀ (n : Nat) (x), deg (frob n x) = (n : Int) * deg x

/-- **定理 (M12-1)**: deg(0) = 0 は公理に含めなくても導出される
    （deg(0) = deg(0+0) = 2·deg(0)）。 -/
theorem Frobenioid.deg_zero (Φ : Frobenioid) : Φ.deg Φ.zero = 0 := by
  have h := Φ.deg_add Φ.zero Φ.zero
  rw [Φ.zero_add] at h
  omega

/-- **定理 (M12-2): Frobenius の合成則** — φ_n ∘ φ_m は次数を nm 倍
    する。Frobenius 構造がモノイド N≥1 の作用であることの次数面。 -/
theorem frob_frob_deg (Φ : Frobenioid) (n m : Nat) (x : Φ.Div) :
    Φ.deg (Φ.frob n (Φ.frob m x)) = ((n * m : Nat) : Int) * Φ.deg x := by
  rw [Φ.frob_deg, Φ.frob_deg, Int.natCast_mul, Int.mul_assoc]

/-- **定理 (M12-3): Frobenius-like 性（非可逆性）** — 次数 ≠ 0 の
    因子の上では φ_n (n ≥ 2) は不動点を持たない。Frobenius 射は
    「戻れない」射であり、これが [FrdI] の Frobenius-like /
    étale-like 二分法、ひいては Θ-link が一方向の貼り合わせである
    ことの形式的根拠である。 -/
theorem frob_not_invertible (Φ : Frobenioid) (n : Nat) (hn : 2 ≤ n)
    (x : Φ.Div) (hx : Φ.deg x ≠ 0) : Φ.frob n x ≠ x := by
  intro h
  have hd := Φ.frob_deg n x
  rw [h] at hd
  -- hd : deg x = n · deg x
  have h2 : ((n : Int) - 1) * Φ.deg x = 0 := by
    rw [Int.sub_mul, Int.one_mul, ← hd]
    omega
  obtain h3 | h3 := Int.mul_eq_zero.mp h2
  · omega
  · exact hx h3

/-- **定理 (M12-4): étale-like 部分の安定性** — 次数 0 の因子
    （単数的対象）は全ての Frobenius で次数 0 に留まる。
    Θ-link の両側で共有される「étale-like なコア」の次数面。 -/
theorem units_etale_like (Φ : Frobenioid) (n : Nat) (x : Φ.Div)
    (hx : Φ.deg x = 0) : Φ.deg (Φ.frob n x) = 0 := by
  rw [Φ.frob_deg, hx, Int.mul_zero]

/-- Gaussian 束: テータ値の束 φ_{1²}(x) ⊕ φ_{2²}(x) ⊕ … ⊕ φ_{L²}(x)
    （IUT II の Gaussian monoid の Frobenioid 版）。 -/
def gaussianDiv (Φ : Frobenioid) (x : Φ.Div) : Nat → Φ.Div
  | 0 => Φ.zero
  | j + 1 => Φ.add (gaussianDiv Φ x j) (Φ.frob ((j + 1) * (j + 1)) x)

/-- **定理 (M12-5): Gaussian 束の次数公式**（M12 → M4 接続）—
    deg(⊕_{j=1}^{L} φ_{j²} x) = (Σ_{j=1}^{L} j²)·deg x。
    M4 `sumDeg_eq` の次数簿記（系3.12 の左辺 |log Θ| の源）が
    Frobenioid の公理（deg_add・frob_deg）だけから従うことの
    機械検証であり、評価理論の簿記層に Frobenioid 論的基礎を与える。 -/
theorem gaussianDiv_deg (Φ : Frobenioid) (x : Φ.Div) (L : Nat) :
    Φ.deg (gaussianDiv Φ x L) = (sumSq L : Int) * Φ.deg x := by
  induction L with
  | zero =>
    show Φ.deg Φ.zero = ((sumSq 0 : Nat) : Int) * Φ.deg x
    rw [Φ.deg_zero]
    have h0 : ((sumSq 0 : Nat) : Int) = 0 := rfl
    rw [h0, Int.zero_mul]
  | succ n ih =>
    show Φ.deg (Φ.add (gaussianDiv Φ x n) (Φ.frob ((n + 1) * (n + 1)) x)) = _
    rw [Φ.deg_add, ih, Φ.frob_deg, sumSq_succ, Int.natCast_add, Int.add_mul]

/-- **次数＝log-volume 両立データ**（IUT III 定理3.11 (i)(c) の骨格）:
    Frobenioid の因子を体積理論の領域として実現する写像で、
    log-volume が（符号規約 |log(·)| = −vol(·) のもとで）次数に
    一致するもの。これが「大域 Frobenioid の次数が対数殻の
    log-volume で計算される」の形式的内容である。 -/
structure DegreeVolumeCompat (Φ : Frobenioid) (V : VolumeTheory) where
  realize : Φ.Div → V.Region
  vol_realize : ∀ x, V.vol (realize x) = -(Φ.deg x)

/-- 両立データのもとで Frobenius は体積を n 倍に伸ばす
    （次数面 M12-2 の体積面への転送）。 -/
theorem frob_volume (Φ : Frobenioid) (V : VolumeTheory)
    (C : DegreeVolumeCompat Φ V) (n : Nat) (x : Φ.Div) :
    V.vol (C.realize (Φ.frob n x)) = -((n : Int) * Φ.deg x) := by
  rw [C.vol_realize, Φ.frob_deg]

/-- **定理 (M12-6): q-パイロットの体積実現**（M12 → M5 接続）—
    次数 |log q| を持つ q-パイロット因子は、両立データのもとで
    体積 −|log q| の領域として実現される。これは `MultiradialRep`
    （M5、定理3.11 のインターフェース）の `vol_q` フィールドを
    Frobenioid データから供給する経路の機械検証である。 -/
theorem frobenioid_realizes_qpilot {V : VolumeTheory} {s : Skeleton}
    (Φ : Frobenioid) (C : DegreeVolumeCompat Φ V)
    (qDiv : Φ.Div) (hq : Φ.deg qDiv = s.logq) :
    V.vol (C.realize qDiv) = -s.logq := by
  rw [C.vol_realize, hq]

/-- **定理 (M12-7a): Frobenioid 公理系の無矛盾性** —
    Div = ℤ・deg = id・φ_n = n 倍のモデルで充足される。 -/
theorem frobenioid_consistent : Nonempty Frobenioid :=
  ⟨{ Div := Int
     add := fun x y => x + y
     zero := 0
     add_assoc := fun x y z => by omega
     add_comm := fun x y => by omega
     zero_add := fun x => by omega
     deg := fun x => x
     deg_add := fun _ _ => rfl
     frob := fun n x => (n : Int) * x
     frob_deg := fun _ _ => rfl }⟩

/-- **定理 (M12-7b): 次数＝体積両立データの無矛盾性** —
    M5 の整数体積モデルの上で realize = 反数 が両立データを与える。 -/
theorem degree_volume_consistent :
    ∃ (Φ : Frobenioid) (V : VolumeTheory), Nonempty (DegreeVolumeCompat Φ V) := by
  refine ⟨
    { Div := Int, add := fun x y => x + y, zero := 0,
      add_assoc := fun x y z => by omega,
      add_comm := fun x y => by omega,
      zero_add := fun x => by omega,
      deg := fun x => x, deg_add := fun _ _ => rfl,
      frob := fun n x => (n : Int) * x, frob_deg := fun _ _ => rfl },
    { Region := Int, le := (· ≤ ·),
      le_refl := Int.le_refl,
      le_trans := fun h1 h2 => Int.le_trans h1 h2,
      hull := fun a b => max a b,
      le_hull_left := fun a b => by omega,
      le_hull_right := fun a b => by omega,
      hull_least := fun h1 h2 => by omega,
      vol := fun x => x,
      vol_mono := fun h => h },
    ⟨{ realize := fun x => -x, vol_realize := fun x => rfl }⟩⟩

end IUT
