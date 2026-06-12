/-
  IUT/FrobenioidCat.lean — M48F（Frobenioid の圏論化）の形式化

  M12（IUT/Frobenioid.lean）は Frobenioid を「因子モノイド＋次数準同型
  deg＋Frobenius 自己射 φ_n」という**データの束**として公理化した。
  本モジュールはその次数面を M19（IUT/CategoryTheory.lean）の `Cat` 上の
  **実際の圏**として実装する。これは [FrdI] §1 の elementary Frobenioid
  F_Φ（基底圏が一点、因子モノイドが ℕ の場合）の射構造そのものである:

      対象   = 次数 n : ℤ（M12 の deg : Div → Int と同じ正規化）
      射 n→m = (d, c)、d ≥ 1 は Frobenius 次数、c ≥ 0 は効果的因子部分、
               線形条件 m = d·n + c（[FrdI] の Div(φ) ≥ 0 と
               deg の変換則 deg(φ(x)) = d·deg(x) + deg(Div(φ)) の骨格）

  恒等射は (1, 0)、合成は (d₁, c₁)·(d₂, c₂) = (d₁d₂, d₂c₁ + c₂)。
  Frobenius 次数は乗法的に、因子部分は「後段の Frobenius で膨らんでから
  加わる」——この捻れ半直積型の合成則が Frobenioid の圏構造の核心である。

  検証する定理（全て sorry なし）:
  * M48F-1 `elementaryFrobenioid` — 上記データが圏公理（id_comp・
    comp_id・assoc）を完全に満たすこと。M19 の `Cat` のインスタンス
  * M48F-2 `degFunctor` — **次数関手** F_Φ → (ℕ≥1, ×)。乗法モノイド
    ℕ≥1 を一対象圏 `frobDegCat` とみなし、射の Frobenius 次数部分を
    取り出す対応が関手であること（[FrdI] の deg_Fr の圏論版）
  * M48F-3 `frobFunctor` / `frobMor` — **Frobenius 自己関手** Φ_e
    （対象を e 倍、因子部分を e 倍）の関手性と、圏の中の Frobenius 射
    n → e·n（次数 e、因子部分 0）の構成
  * M48F-4 非可逆性定理群 — `frob_no_right_inverse`（次数 ≥ 2 の射は
    右逆を持たない）、`iso_deg_one`（同型の Frobenius 次数は必ず 1）、
    `iso_objects_eq`（**この圏の同型は対象を動かせない**）、
    `hom_exists_but_no_iso`（1 → 2 に射はあるが同型はない）。
    M12-3 `frob_not_invertible`（deg ≠ 0 の対象上の不動点不在）の
    圏論版であり、しかも仮定なしに強い形で成立する
  * M48F-5 M12 接続 — `degMor`（M12 の Frobenioid Φ の各 φ_e は
    deg を通して本圏の射を実現する）、`frobFunctor_matches_frob`
    （自己関手 Φ_e の対象写像 = M12 の deg∘frob、つまり M12 の公理
    frob_deg の関手化）、`deg_frobFunctor`（Φ_e は次数関手の上で恒等
    = Frobenius 自己関手は射の Frobenius 次数を保つ）

  【Galois 圏との対比（M20-21 との接続）】
  Galois 圏の公理 G6（M20-5 `gsets_G6_reflects_iso`）は「ファイバー
  関手が同型を反映する」こと、特に圏が同型を豊富に持つことを前提と
  する設計である。一方ここで建設した elementaryFrobenioid では
  `iso_objects_eq` により**同型が恒等射しかない**（n ≅ m ⟹ n = m）。
  次数 ≥ 2 の Frobenius 射は「進むだけで戻れない」時間の矢であり、
  これが「Frobenioid は Galois 圏ではない」——étale-like な世界
  （M20-21、同型＝可逆な対称性で編まれた圏）と Frobenius-like な世界
  （本圏、一方向の射で編まれた圏）の二分法——の一断面の機械検証である。
  Θ-link が「Frobenius-like 構造の一方向輸送」であること（M12 の
  ドキュメント参照）の圏論的根拠がここにある。

  **正直な申告（モデル化したものと本物の差）**: 本物の Frobenioid は
  基底圏 D（数体なら素点の圏）上のファイバー構造を持ち、因子モノイド
  Φ は D 上の関手、射は基底の射・Frobenius 次数・因子の三つ組である。
  ここで形式化したのは基底圏が一点・因子モノイドが ℕ（次数 ℤ に作用）
  の elementary な場合、すなわち**次数簿記が見る範囲の Frobenioid の
  圏構造**である。poly-isomorphism・分裂・realification は未形式化。
  ただし非可逆性（M48F-4）は一般の Frobenioid でも次数関手を通して
  本圏に落ちて成立する型の主張であり、elementary な場合の証明が
  その核心を捉えている。選択公理は不使用（全定理 propext 以下）。
-/
import IUT.Frobenioid
import IUT.CategoryTheory

namespace IUT

/-! ## 整数算術のヘルパー補題

    omega は var×var の積・キャスト混在の非線形項・構造体射影を
    読めないため、束縛変数だけの Int/Nat 補題に切り出す（規約3）。 -/

/-- 恒等射の線形条件: n = 1·n + 0。 -/
theorem frob_id_linear (n : Int) : n = ((1 : Nat) : Int) * n + 0 := by
  omega

/-- 合成射の線形条件: m = a·n + c₁ かつ k = b·m + c₂ なら
    k = (ab)·n + (b·c₁ + c₂)。捻れ半直積型の合成則の算術核。 -/
theorem frob_comp_linear {a b : Nat} {n m k c₁ c₂ : Int}
    (h₁ : m = (a : Int) * n + c₁) (h₂ : k = (b : Int) * m + c₂) :
    k = ((a * b : Nat) : Int) * n + ((b : Int) * c₁ + c₂) := by
  rw [h₂, h₁, Int.mul_add, Int.natCast_mul, ← Int.mul_assoc,
    Int.mul_comm (b : Int) (a : Int), Int.add_assoc]

/-- 合成射の因子部分の非負性: c₁ ≥ 0, c₂ ≥ 0 ⟹ b·c₁ + c₂ ≥ 0。 -/
theorem frob_comp_c_nonneg {b : Nat} {c₁ c₂ : Int}
    (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) : 0 ≤ (b : Int) * c₁ + c₂ :=
  Int.add_nonneg (Int.mul_nonneg (Int.natCast_nonneg b) h₁) h₂

/-- 左単位則の因子部分: b·0 + y = y。 -/
theorem frob_cast_mul_zero_add (b : Nat) (y : Int) :
    (b : Int) * 0 + y = y := by
  rw [Int.mul_zero, Int.zero_add]

/-- 右単位則の因子部分: 1·x + 0 = x。 -/
theorem frob_cast_one_mul_add_zero (x : Int) :
    ((1 : Nat) : Int) * x + 0 = x := by
  omega

/-- 結合則の因子部分: c·(b·x + y) + z = (bc)·x + (c·y + z)。 -/
theorem frob_assoc_c (b c : Nat) (x y z : Int) :
    (c : Int) * ((b : Int) * x + y) + z
      = ((b * c : Nat) : Int) * x + ((c : Int) * y + z) := by
  rw [Int.mul_add, Int.natCast_mul, ← Int.mul_assoc,
    Int.mul_comm (c : Int) (b : Int), Int.add_assoc]

/-- スケール換装の恒等式: e·(b·x + y) = b·(e·x) + e·y
    （Frobenius 自己関手の射部分が合成と可換であることの算術核）。 -/
theorem frob_scale_shuffle (e b : Nat) (x y : Int) :
    (e : Int) * ((b : Int) * x + y)
      = (b : Int) * ((e : Int) * x) + (e : Int) * y := by
  rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm (e : Int) (b : Int),
    Int.mul_assoc]

/-- a ≥ 1, b ≥ 1, a·b = 1 ⟹ a = 1（ℕ の乗法単数性）。
    a·b は omega の読めない var×var 積なので a·1 ≤ a·b で線形化する。 -/
theorem frob_mul_eq_one_left {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * b = 1) : a = 1 := by
  have h2 : a * 1 ≤ a * b := Nat.mul_le_mul (Nat.le_refl a) hb
  rw [Nat.mul_one, h] at h2
  omega

/-- a ≥ 2, b ≥ 1 ⟹ a·b ≠ 1（Frobenius 次数 ≥ 2 の射が
    可逆になれないことの算術核）。 -/
theorem frob_two_le_mul_ne_one {a b : Nat} (ha : 2 ≤ a) (hb : 1 ≤ b) :
    a * b ≠ 1 := by
  intro h
  have h1 : a = 1 := frob_mul_eq_one_left (by omega) hb h
  omega

/-- 同型の因子消滅: x ≥ 0, y ≥ 0, 1·x + y = 0 ⟹ x = 0。 -/
theorem frob_iso_c_vanish {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ((1 : Nat) : Int) * x + y = 0) : x = 0 := by
  omega

/-- 同型の対象固定: m = 1·n + 0 ⟹ n = m。 -/
theorem frob_iso_obj_eq {n m : Int} (h : m = ((1 : Nat) : Int) * n + 0) :
    n = m := by
  omega

/-! ## M48F-1: elementary Frobenioid の圏 -/

/-- elementary Frobenioid の射: 次数 n から次数 m への射は
    Frobenius 次数 d ≥ 1 と効果的因子部分 c ≥ 0 のペアで、
    線形条件 m = d·n + c を満たすもの（[FrdI] §1 の射データの
    次数簿記が見る部分）。 -/
structure FrobHom (n m : Int) where
  /-- Frobenius 次数（degree of Frobenius）。 -/
  d : Nat
  /-- 効果的因子部分の次数（deg Div(φ) ≥ 0）。 -/
  c : Int
  d_pos : 1 ≤ d
  c_nonneg : 0 ≤ c
  /-- 次数の変換則: deg(φ(x)) = d·deg(x) + deg(Div(φ))。 -/
  linear : m = (d : Int) * n + c

/-- 射の外延性: FrobHom は (d, c) 成分で決まる（線形条件は Prop）。 -/
theorem FrobHom.ext {n m : Int} {f g : FrobHom n m}
    (hd : f.d = g.d) (hc : f.c = g.c) : f = g := by
  cases f with | mk fd fc f1 f2 f3 =>
  cases g with | mk gd gc g1 g2 g3 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  subst hd'
  subst hc'
  rfl

/-- **定理 (M48F-1): elementary Frobenioid** — 対象 = 次数 ℤ、
    射 = (Frobenius 次数, 効果的因子) が M19 の `Cat` をなす。
    合成は (d₁,c₁)·(d₂,c₂) = (d₁d₂, d₂c₁+c₂)（捻れ半直積型）。 -/
def elementaryFrobenioid : Cat where
  Obj := Int
  Hom := FrobHom
  id := fun n => ⟨1, 0, Nat.le_refl 1, Int.le_refl 0, frob_id_linear n⟩
  comp := fun f g =>
    ⟨f.d * g.d, (g.d : Int) * f.c + g.c,
      Nat.mul_pos f.d_pos g.d_pos,
      frob_comp_c_nonneg f.c_nonneg g.c_nonneg,
      frob_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    FrobHom.ext (Nat.one_mul f.d) (frob_cast_mul_zero_add f.d f.c)
  comp_id := fun f =>
    FrobHom.ext (Nat.mul_one f.d) (frob_cast_one_mul_add_zero f.c)
  assoc := fun f g h =>
    FrobHom.ext (Nat.mul_assoc f.d g.d h.d)
      (frob_assoc_c g.d h.d f.c g.c h.c)

/-! ## M48F-2: 次数関手 -/

/-- 正の自然数（Frobenius 次数のなすモノイド ℕ≥1）。 -/
def PosNat := { d : Nat // 1 ≤ d }

/-- **乗法モノイド (ℕ≥1, ×) を一対象圏とみなしたもの** —
    次数関手の行き先。射 = Frobenius 次数、合成 = 乗法。 -/
def frobDegCat : Cat where
  Obj := Unit
  Hom := fun _ _ => PosNat
  id := fun _ => ⟨1, Nat.le_refl 1⟩
  comp := fun f g => ⟨f.val * g.val, Nat.mul_pos f.property g.property⟩
  id_comp := fun f => Subtype.ext (Nat.one_mul f.val)
  comp_id := fun f => Subtype.ext (Nat.mul_one f.val)
  assoc := fun f g h => Subtype.ext (Nat.mul_assoc f.val g.val h.val)

/-- **定理 (M48F-2): 次数関手** deg : F_Φ → (ℕ≥1, ×) —
    射の Frobenius 次数部分を取り出す対応は関手である
    （恒等射 ↦ 1、合成 ↦ 積。[FrdI] の deg_Fr の圏論版）。
    関手性は合成則の第一成分が d₁d₂ である設計から定義的に従う。 -/
def degFunctor : Functor elementaryFrobenioid frobDegCat where
  onObj := fun _ => ()
  onHom := fun f => ⟨f.d, f.d_pos⟩
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-! ## M48F-3: Frobenius 自己関手と Frobenius 射 -/

/-- **定理 (M48F-3a): Frobenius 自己関手** Φ_e : F_Φ → F_Φ —
    対象（次数）を e 倍し、射の因子部分を e 倍する（Frobenius 次数は
    保つ）。線形条件の保存は e·(d·n + c) = d·(e·n) + e·c。
    M12 の φ_e「次数を e 倍する自己射」の圏論版（自己**関手**化）。 -/
def frobFunctor (e : Nat) : Functor elementaryFrobenioid elementaryFrobenioid where
  onObj := fun (n : Int) => (e : Int) * n
  onHom := fun {n m : Int} f =>
    { d := f.d
      c := (e : Int) * f.c
      d_pos := f.d_pos
      c_nonneg := Int.mul_nonneg (Int.natCast_nonneg e) f.c_nonneg
      linear := by
        -- m は f の型に現れるため rw は使えない（motive 不正）。
        -- congrArg で m の出現を一箇所だけ書き換えてから合成する。
        have h : (e : Int) * m = (e : Int) * ((f.d : Int) * n + f.c) :=
          congrArg (fun t => (e : Int) * t) f.linear
        exact h.trans (frob_scale_shuffle e f.d n f.c) }
  map_id := fun n => FrobHom.ext rfl (Int.mul_zero (e : Int))
  map_comp := fun f g => FrobHom.ext rfl (frob_scale_shuffle e g.d f.c g.c)

/-- **定理 (M48F-3b): Frobenius 射** — 圏の中の純 Frobenius 射
    n → e·n（次数 e、因子部分 0）。[FrdI] の Frobenius 構造
    そのもの。 -/
def frobMor (e : Nat) (he : 1 ≤ e) (n : Int) :
    FrobHom n ((e : Int) * n) :=
  ⟨e, 0, he, Int.le_refl 0, (Int.add_zero ((e : Int) * n)).symm⟩

/-! ## M48F-4: 非可逆性 — Frobenioid は Galois 圏でない

    Galois 圏の公理 G6（M20-5 `gsets_G6_reflects_iso`）が要求する
    「同型の反映」は同型の存在を前提とした設計だが、本圏では同型が
    恒等射しかない（`iso_objects_eq`）。次数 ≥ 2 の Frobenius 射は
    決して可逆にならない——M12-3 `frob_not_invertible` の圏論版で、
    しかも対象側の仮定（deg ≠ 0）すら不要な強い形で成立する。 -/

/-- **定理 (M48F-4a): 右逆の不在** — Frobenius 次数 ≥ 2 の射 f は
    どんな射 g とも合成して恒等射にならない（f·g ≠ id）。 -/
theorem frob_no_right_inverse {n m : Int} (f : FrobHom n m)
    (hf : 2 ≤ f.d) (g : FrobHom m n) :
    elementaryFrobenioid.comp f g ≠ elementaryFrobenioid.id n := by
  intro h
  have hd : f.d * g.d = 1 := congrArg FrobHom.d h
  exact frob_two_le_mul_ne_one hf g.d_pos hd

/-- **定理 (M48F-4b): 同型の次数は 1** — 圏の同型（M19 の `CatIso`）の
    hom 成分の Frobenius 次数は必ず 1。対偶: 次数 ≥ 2 の Frobenius 射は
    いかなる同型のデータにもなれない。 -/
theorem iso_deg_one {n m : Int} (i : CatIso elementaryFrobenioid n m) :
    i.hom.d = 1 :=
  frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos (congrArg FrobHom.d i.hom_inv)

/-- **定理 (M48F-4c): 同型の因子部分は 0** — 同型の hom 成分は
    効果的因子を持てない（c ≥ 0 同士の和が 0 になるため）。 -/
theorem iso_c_zero {n m : Int} (i : CatIso elementaryFrobenioid n m) :
    i.hom.c = 0 := by
  have hdinv : i.inv.d = 1 :=
    frob_mul_eq_one_left i.inv.d_pos i.hom.d_pos (congrArg FrobHom.d i.inv_hom)
  have hc : (i.inv.d : Int) * i.hom.c + i.inv.c = 0 :=
    congrArg FrobHom.c i.hom_inv
  rw [hdinv] at hc
  exact frob_iso_c_vanish i.hom.c_nonneg i.inv.c_nonneg hc

/-- **定理 (M48F-4d): 同型は対象を動かせない** — n ≅ m ⟹ n = m。
    elementaryFrobenioid の同型は恒等射に限る。Galois 圏（同型＝
    対称性で編まれた étale-like の世界、M20-21）との決定的な対比:
    Frobenius-like の世界は「進むだけで戻れない」一方向の圏である。 -/
theorem iso_objects_eq {n m : Int} (i : CatIso elementaryFrobenioid n m) :
    n = m := by
  have hd := iso_deg_one i
  have hc := iso_c_zero i
  have hl := i.hom.linear
  rw [hd, hc] at hl
  exact frob_iso_obj_eq hl

/-- **定理 (M48F-4e): 射はあるが同型はない** — 1 → 2 には Frobenius 射
    （次数 2、因子 0）が存在するが、1 ≅ 2 なる同型は存在しない。
    「Frobenioid は Galois 圏でない」ことの具体的証人。 -/
theorem hom_exists_but_no_iso :
    Nonempty (FrobHom 1 2)
      ∧ ¬ Nonempty (CatIso elementaryFrobenioid (1 : Int) (2 : Int)) := by
  constructor
  · exact ⟨⟨2, 0, by omega, by omega, by omega⟩⟩
  · intro ⟨i⟩
    have h : (1 : Int) = 2 := iso_objects_eq i
    omega

/-! ## M48F-5: M12（Frobenioid データ）との接続 -/

/-- **定理 (M48F-5a): M12 の Frobenius 射の実現** — M12 の任意の
    Frobenioid Φ・因子 x・次数 e ≥ 1 に対し、φ_e : x → frob e x は
    deg を通して elementaryFrobenioid の射 deg x → deg(frob e x) を
    実現する（次数 e、因子部分 0。線形条件は M12 の公理 frob_deg）。 -/
def degMor (Φ : Frobenioid) (e : Nat) (he : 1 ≤ e) (x : Φ.Div) :
    FrobHom (Φ.deg x) (Φ.deg (Φ.frob e x)) where
  d := e
  c := 0
  d_pos := he
  c_nonneg := Int.le_refl 0
  linear := by rw [Φ.frob_deg, Int.add_zero]

/-- **定理 (M48F-5b): 自己関手と M12 の frob の整合** — Frobenius
    自己関手 Φ_e の対象写像は、M12 の deg∘frob と一致する。
    M12 の公理 frob_deg「deg(φ_e x) = e·deg x」の関手化。 -/
theorem frobFunctor_matches_frob (Φ : Frobenioid) (e : Nat) (x : Φ.Div) :
    (frobFunctor e).onObj (Φ.deg x) = Φ.deg (Φ.frob e x) :=
  (Φ.frob_deg e x).symm

/-- **定理 (M48F-5c): degMor の次数読み出し** — 次数関手は
    degMor から Frobenius 次数 e をそのまま回収する。 -/
theorem degFunctor_degMor (Φ : Frobenioid) (e : Nat) (he : 1 ≤ e)
    (x : Φ.Div) :
    (degFunctor.onHom (degMor Φ e he x)).val = e :=
  rfl

/-- **定理 (M48F-5d): degMor の合成の次数** — φ_a・φ_b の実現射の
    合成の Frobenius 次数は a·b（M12-2 `frob_frob_deg` の圏論面）。 -/
theorem degMor_comp_d (Φ : Frobenioid) (a b : Nat) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (x : Φ.Div) :
    (elementaryFrobenioid.comp (degMor Φ a ha x)
      (degMor Φ b hb (Φ.frob a x))).d = a * b :=
  rfl

/-- **定理 (M48F-5e): degMor の合成の因子部分は 0** — 純 Frobenius 射の
    合成は純 Frobenius 射のまま（効果的因子は発生しない）。 -/
theorem degMor_comp_c (Φ : Frobenioid) (a b : Nat) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (x : Φ.Div) :
    (elementaryFrobenioid.comp (degMor Φ a ha x)
      (degMor Φ b hb (Φ.frob a x))).c = 0 := by
  show (b : Int) * 0 + 0 = 0
  rw [Int.mul_zero, Int.add_zero]

/-- **定理 (M48F-5f): Frobenius 自己関手は次数関手の上で恒等** —
    Φ_e は射の Frobenius 次数を変えない（変わるのは対象と因子部分
    だけ）。「Frobenius 自己関手は étale-like な層（次数モノイド）を
    固定する」ことの形式的内容。 -/
theorem deg_frobFunctor (e : Nat) {n m : Int} (f : FrobHom n m) :
    degFunctor.onHom ((frobFunctor e).onHom f) = degFunctor.onHom f :=
  rfl

end IUT
