/-
  IUT/FullReciprocity.lean — M37（完全な相互写像 rec : ℚ_p^× → ẑ × ℤ_p^×）

  M27 の不分岐モデル（単数群を抽象データ punitGrp とした rec = 完備化∘付値）
  を、M36 までに実構成した**本物の単数群 ℤ_p^×** で置き換え、ℚ_p の
  局所類体論の相互写像を**両側とも実構成の群**の間の準同型として完成する:

    ℚ_p^× ≅ p^ℤ × ℤ_p^×   --rec-->   ẑ × ℤ_p^× ≅ Gal(ℚ_p^ab/ℚ_p)
    （付値部は Frobenius へ完備化、単数部は慣性群へ恒等的に）

  * M37-1 `idHom` / `prodHom` — 恒等準同型と直積準同型（単射性込み）
  * M37-2 `QpUnits` / `galAbQp` — **ℚ_p^× = p^ℤ × ℤ_p^× の表示**と
    **Gal(ℚ_p^ab/ℚ_p) = ẑ × ℤ_p^× の表示**（両因子とも実構成:
    ẑ = M13、ℤ_p^× = M36）
  * M37-3 `recQp` — **完全な相互写像** rec(p^k·u) = (Frob^k, u)。
    不分岐部（M27）に分岐部（恒等)を直積で結合
  * M37-4 `recQp_injective` — 単射性（p 進分離性 × 恒等）
  * M37-5 `recQp_units_to_inertia` — **単数は慣性群へ**: rec(0, u) =
    (1, u)。M27-5 の核の特徴付けの精密化（核は消えず慣性側に写る）
  * M37-6 `fullLocalCFT` — **LCFT インターフェース（M27-7）の完全模型**:
    Kx・Gab とも実構成で、単射性と全有限レベルへの全射性
    （Frobenius 稠密性 × 単数全射）を完全証明

  正直な申告: 右辺 ẑ × ℤ_p^× が実際の Gal(ℚ_p^ab/ℚ_p) と同型である
  こと（局所 Kronecker–Weber / Lubin–Tate 理論）はここでの形式化の
  対象外であり、本モジュールは「その表示の上での」相互写像の構成と
  性質の完全証明である。全て選択公理不使用。
-/
import IUT.ZpUnits

namespace IUT

/-! ## 恒等準同型と直積準同型 -/

/-- 恒等準同型。 -/
def idHom (G : Grp) : Hom G G where
  map := fun x => x
  map_mul := fun _ _ => rfl

/-- **M37-1: 直積準同型** — f × g : A × B → C × D（成分ごと）。 -/
def prodHom {A B C D : Grp} (f : Hom A C) (g : Hom B D) :
    Hom (prodGrp A B) (prodGrp C D) where
  map := fun x => (f.map x.1, g.map x.2)
  map_mul := fun a b => by
    show (f.map (A.mul a.1 b.1), g.map (B.mul a.2 b.2)) = _
    rw [f.map_mul, g.map_mul]

/-- 直積準同型は成分が単射なら単射。 -/
theorem prodHom_injective {A B C D : Grp} {f : Hom A C} {g : Hom B D}
    (hf : f.Injective) (hg : g.Injective) : (prodHom f g).Injective := by
  intro x y h
  have h1 : f.map x.1 = f.map y.1 := congrArg Prod.fst h
  have h2 : g.map x.2 = g.map y.2 := congrArg Prod.snd h
  have e1 := hf x.1 y.1 h1
  have e2 := hg x.2 y.2 h2
  show x = y
  rw [show x = (x.1, x.2) from rfl, show y = (y.1, y.2) from rfl, e1, e2]

/-! ## ℚ_p^× と Gal(ℚ_p^ab/ℚ_p) の表示 -/

/-- **M37-2a: ℚ_p^× の表示** — p^ℤ × ℤ_p^×（付値による分裂）。
    M27 の `unitsModel` の単数部を実構成（M36）で実体化したもの。 -/
def QpUnits (p : Nat) (hp : IsPrime p) : Grp :=
  prodGrp intGrp (zpUnits p hp)

/-- **M37-2b: Gal(ℚ_p^ab/ℚ_p) の表示** — ẑ × ℤ_p^×
    （不分岐部 = Frobenius の閉包 ẑ、慣性部 = ℤ_p^×）。 -/
def galAbQp (p : Nat) (hp : IsPrime p) : Grp :=
  prodGrp zhat (zpUnits p hp)

/-! ## 完全な相互写像 -/

/-- **定理 (M37-3): 完全な相互写像** rec : ℚ_p^× → ẑ × ℤ_p^× —
    付値部は完備化 ℤ → ẑ（Frobenius へ）、単数部は恒等的に慣性群へ。 -/
def recQp (p : Nat) (hp : IsPrime p) : Hom (QpUnits p hp) (galAbQp p hp) :=
  prodHom toZhat (idHom (zpUnits p hp))

/-- rec の明示式: rec(k, u) = (toZhat k, u)。 -/
theorem recQp_apply (p : Nat) (hp : IsPrime p) (k : Int)
    (u : (zpUnits p hp).carrier) :
    (recQp p hp).map (k, u) = (toZhat.map k, u) := rfl

/-- **定理 (M37-4): rec は単射**（p 進分離性 × 恒等）。 -/
theorem recQp_injective (p : Nat) (hp : IsPrime p) : (recQp p hp).Injective :=
  prodHom_injective toZhat_injective (fun _ _ h => h)

/-- **定理 (M37-5): 単数は慣性群へ** — rec(0, u) = (1, u)。
    M27-5「核 = 単数群」の精密化: 完全版では単数は消えるのではなく
    慣性因子に恒等的に写る。 -/
theorem recQp_units_to_inertia (p : Nat) (hp : IsPrime p)
    (u : (zpUnits p hp).carrier) :
    (recQp p hp).map ((0 : Int), u) = (zhat.one, u) := by
  show (toZhat.map (0 : Int), u) = (zhat.one, u)
  rw [show toZhat.map (0 : Int) = zhat.one from toZhat.map_one]

/-- **定理 (M37-6): LCFT インターフェースの完全模型** — Kx = ℚ_p^×、
    Gab = ẑ × ℤ_p^× とも実構成の群で、単射性と全有限レベル
    ℤ/n × ℤ_p^× への全射性を完全証明（M27-8 の不分岐 witness の
    完全版への置き換え）。 -/
def fullLocalCFT (p : Nat) (hp : IsPrime p) : LocalCFTData where
  Kx := QpUnits p hp
  Gab := galAbQp p hp
  recMap := recQp p hp
  recMap_inj := recQp_injective p hp
  levels := fun n => prodGrp (zmod n) (zpUnits p hp)
  projs := fun n => prodHom (limitProj zmodSystem n) (idHom (zpUnits p hp))
  recMap_level_surj := by
    intro n c
    obtain ⟨a, ha⟩ := Quot.exists_rep c.1
    refine ⟨(a, c.2), ?_⟩
    show ((limitProj zmodSystem n).map (toZhat.map a), c.2) = c
    rw [show (limitProj zmodSystem n).map (toZhat.map a)
        = Quot.mk (modCong n).rel a from rfl, ha]
    rfl

/-- 完全模型による無矛盾性の witness（M27 の不分岐 witness の強化）。 -/
theorem fullLocalCFT_consistent : Nonempty LocalCFTData :=
  ⟨fullLocalCFT 2 isPrime_two⟩

end IUT
