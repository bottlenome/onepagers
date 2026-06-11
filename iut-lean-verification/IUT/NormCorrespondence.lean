/-
  IUT/NormCorrespondence.lean — M28（ノルム部分群対応: LCFT の第二の柱）

  局所類体論のもう一つの主張は**ノルム部分群対応**: 相互写像 rec が
  K^× の部分群と Gal(K^ab/K) の部分群の間の忠実な対応を誘導する。
  その群論的核心を完全証明する:

  * M28-1 `Subgroup.comap` / `Subgroup.map` — 準同型に沿った部分群の
    引き戻し・押し出し（部分群性の完全証明）
  * M28-2 `map_le_iff_le_comap` — **随伴性**（ガロア接続）:
    map f S ⊆ T ⟺ S ⊆ comap f T
  * M28-3 `comap_map_of_injective` — **対応の忠実性**: f が単射なら
    comap (map f S) = S（部分群は対応で完全に復元される）。
    LCFT では「ノルム部分群から拡大が一意に決まる」ことの群論的内容
  * M28-4 `norm_correspondence` — LCFT インターフェース（M27-7）の
    相互写像に適用: **rec の単射性 ⟹ K^× の部分群はノルム対応で
    忠実に Gal 側に写る**。不分岐モデル（M27-8）で具体化
-/
import IUT.LocalCFT

namespace IUT

/-- 部分群の引き戻し（M28-1a）。 -/
def Subgroup.comap {G H : Grp} (f : Hom G H) (S : Subgroup H) : Subgroup G where
  mem := fun g => S.mem (f.map g)
  one_mem := by
    show S.mem (f.map G.one)
    rw [f.map_one]
    exact S.one_mem
  mul_mem := fun {a b} ha hb => by
    show S.mem (f.map (G.mul a b))
    rw [f.map_mul]
    exact S.mul_mem ha hb
  inv_mem := fun {a} ha => by
    show S.mem (f.map (G.inv a))
    rw [f.map_inv]
    exact S.inv_mem ha

/-- 部分群の押し出し（像、M28-1b）。 -/
def Subgroup.map {G H : Grp} (f : Hom G H) (S : Subgroup G) : Subgroup H where
  mem := fun y => ∃ x, S.mem x ∧ f.map x = y
  one_mem := ⟨G.one, S.one_mem, f.map_one⟩
  mul_mem := fun {a b} ⟨x, hx, hfx⟩ ⟨y, hy, hfy⟩ =>
    ⟨G.mul x y, S.mul_mem hx hy, by rw [f.map_mul, hfx, hfy]⟩
  inv_mem := fun {a} ⟨x, hx, hfx⟩ =>
    ⟨G.inv x, S.inv_mem hx, by rw [f.map_inv, hfx]⟩

/-- **定理 (M28-2): 随伴性（ガロア接続）** — map f S ⊆ T ⟺
    S ⊆ comap f T。部分群対応の順序論的核。 -/
theorem map_le_iff_le_comap {G H : Grp} (f : Hom G H)
    (S : Subgroup G) (T : Subgroup H) :
    (∀ y, (Subgroup.map f S).mem y → T.mem y) ↔
    (∀ x, S.mem x → (Subgroup.comap f T).mem x) := by
  constructor
  · intro h x hx
    exact h (f.map x) ⟨x, hx, rfl⟩
  · intro h y ⟨x, hx, hfx⟩
    have := h x hx
    rw [← hfx]
    exact this

/-- **定理 (M28-3): 対応の忠実性** — f 単射なら comap (map f S) = S
    （メンバーシップの同値）。部分群が対応で完全に復元される。 -/
theorem comap_map_of_injective {G H : Grp} (f : Hom G H)
    (hf : f.Injective) (S : Subgroup G) :
    ∀ x, (Subgroup.comap f (Subgroup.map f S)).mem x ↔ S.mem x := by
  intro x
  constructor
  · intro ⟨x', hx', hfx'⟩
    rw [hf x' x hfx'] at hx'
    exact hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **定理 (M28-4): ノルム部分群対応**（LCFT の第二の柱）—
    相互写像の単射性（`LocalCFTData.recMap_inj`）により、K^× の
    任意の部分群（ノルム部分群の抽象化）は Gal 側への押し出しから
    完全に復元される。「ノルム部分群 ⟷ アーベル拡大」の対応の
    忠実性の群論的内容。 -/
theorem norm_correspondence (D : LocalCFTData) (S : Subgroup D.Kx) :
    ∀ x, (Subgroup.comap D.recMap (Subgroup.map D.recMap S)).mem x ↔ S.mem x :=
  comap_map_of_injective D.recMap D.recMap_inj S

/-- 不分岐モデルでの具体化: 不分岐相互写像はノルム対応を忠実に誘導。 -/
theorem unramified_norm_correspondence (S : Subgroup unramifiedLocalCFT.Kx) :
    ∀ x, (Subgroup.comap unramifiedLocalCFT.recMap
      (Subgroup.map unramifiedLocalCFT.recMap S)).mem x ↔ S.mem x :=
  norm_correspondence unramifiedLocalCFT S

end IUT
