/-
  IUT/GaloisCategory.lean — M14（Galois 圏・ファイバー関手・étale π₁）の形式化

  Galois 圏の理論（SGA1）の骨組み: 有限 étale 被覆の圏 C と
  ファイバー関手 F : C → FinSet に対し、étale 基本群を
      π₁^ét := Aut(F)（ファイバー関手の自己同型群）
  と定義し、これが各有限レベルの自己同型群（デッキ群）の
  **逆極限 = 副有限群**（M13）になる、というのが理論の中核である。

  本モジュールはその中核機構を core Lean の完全証明で建設する:

  §1 G-集合（被覆の抽象化）と同変写像（被覆の射）
  * M14-1 `equivariant_is_right_mul` — **ファイバー関手の復元機構**:
    正則作用（普遍被覆のファイバー）の同変自己写像は右移動
    x ↦ x·c のみ。すなわち Aut(普遍被覆のファイバー) ≅ G——
    「基本群はファイバー関手の自己同型として復元される」の
    群論的核心（Galois 圏の主定理の片翼）の完全証明
  * M14-2 `rightMul_bijective` — 右移動は全単射（よって自己**同型**）
  * M14-3 `fiber_functor_recovers_group` — 同変自己写像と G の元の
    一対一対応（存在と一意性）
  * M14-4 `rightMul_comp` — 合成は積に対応（反変、Aut(F) ≅ G^op）

  §2 étale π₁ のファイバー関手的実現（M13 との接続）
  * M14-5 `levelAction` — 逆極限群（π₁^ét）は各有限レベルに射影を
    通じて作用する（ファイバー関手の値への作用）
  * M14-6 `level_transition_equivariant` — その作用は推移射と両立
    する。すなわち **π₁^ét の作用はファイバー関手の自然変換**である
    （「π₁^ét = Aut(F)」の自然性側の機械検証）

  §3 Galois 対応の順序論的骨格
  * M14-7〜10 — 反変 Galois 接続（部分群 ↔ 被覆）の単位・余単位・
    反単調性・閉包の冪等性。Galois 圏の対応定理
    「被覆 ↔ 開部分群（反変）」の束論的シャドウの完全証明

  **位置づけ（正直な申告）**: Galois 圏の公理（SGA1 V.4: 始対象・
  商・連結成分分解など）と主定理（C ≃ π₁-有限集合の圏全体の同値）
  そのものは未形式化。ここで証明したのは主定理の二つの核心機構——
  「Aut(ファイバー) = 群」（§1）と「π₁^ét は有限レベルの整合系に
  自然に作用する」（§2）——であり、双曲的曲線の実際の被覆圏が
  Galois 圏をなすこと（幾何的入力）が残る実質である。
-/
import IUT.Profinite

namespace IUT

/-! ## §1 G-集合とファイバー関手の復元機構 -/

/-- **G-集合**（群 G の作用）: Galois 圏の対象（有限 étale 被覆の
    ファイバー + モノドロミー作用）の抽象化。 -/
structure GAction (G : Grp) where
  carrier : Type
  act : G.carrier → carrier → carrier
  act_one : ∀ x, act G.one x = x
  act_mul : ∀ g h x, act (G.mul g h) x = act g (act h x)

/-- 同変写像（被覆の射）。 -/
structure ActHom {G : Grp} (X Y : GAction G) where
  map : X.carrier → Y.carrier
  equivariant : ∀ g x, map (X.act g x) = Y.act g (map x)

/-- **正則作用**: G の自分自身への左移動。普遍被覆（Galois 圏の
    pro-表現対象）のファイバーの模型。 -/
def regAction (G : Grp) : GAction G where
  carrier := G.carrier
  act := G.mul
  act_one := G.one_mul
  act_mul := G.mul_assoc

/-- 右移動 x ↦ x·c は正則作用の同変自己写像（左右の作用は可換）。 -/
def rightMul (G : Grp) (c : G.carrier) : ActHom (regAction G) (regAction G) where
  map := fun x => G.mul x c
  equivariant := fun g x => G.mul_assoc g x c

/-- **定理 (M14-1): ファイバー関手の復元機構** — 正則作用の同変
    自己写像は右移動 x ↦ x·φ(1) に限る。「普遍被覆のファイバーの
    自己同型 = 基本群そのもの」（Galois 圏で π₁ = Aut(F) と定義
    できる理由）の群論的核心。 -/
theorem equivariant_is_right_mul (G : Grp)
    (φ : ActHom (regAction G) (regAction G)) :
    ∀ x, φ.map x = G.mul x (φ.map G.one) := by
  intro x
  have h : φ.map (G.mul x G.one) = G.mul x (φ.map G.one) := φ.equivariant x G.one
  rw [G.mul_one] at h
  exact h

/-- **定理 (M14-2): 右移動は全単射**（同変自己**同型**である）。 -/
theorem rightMul_bijective (G : Grp) (c : G.carrier) :
    (∀ x y, (rightMul G c).map x = (rightMul G c).map y → x = y) ∧
    (∀ y, ∃ x, (rightMul G c).map x = y) := by
  constructor
  · intro x y h
    exact G.mul_right_cancel h
  · intro y
    refine ⟨G.mul y (G.inv c), ?_⟩
    show G.mul (G.mul y (G.inv c)) c = y
    rw [G.mul_assoc, G.inv_mul, G.mul_one]

/-- **定理 (M14-3): Aut(ファイバー) ↔ G の一対一対応** — 各同変
    自己写像 φ に対し、φ = 右移動 c となる c が一意に存在する。 -/
theorem fiber_functor_recovers_group (G : Grp)
    (φ : ActHom (regAction G) (regAction G)) :
    ∃ c : G.carrier,
      (∀ x, φ.map x = (rightMul G c).map x) ∧
      ∀ c', (∀ x, φ.map x = (rightMul G c').map x) → c' = c := by
  refine ⟨φ.map G.one, fun x => equivariant_is_right_mul G φ x, ?_⟩
  intro c' hc'
  have h : φ.map G.one = G.mul G.one c' := hc' G.one
  rw [G.one_mul] at h
  exact h.symm

/-- **定理 (M14-4): 合成は積に対応**（反変: Aut(F) ≅ G^op。
    群は自分の opposite と反同型なので π₁ ≅ Aut(F) が従う）。 -/
theorem rightMul_comp (G : Grp) (c c' : G.carrier) (x : G.carrier) :
    (rightMul G c).map ((rightMul G c').map x)
      = (rightMul G (G.mul c' c)).map x := by
  show G.mul (G.mul x c') c = G.mul x (G.mul c' c)
  exact G.mul_assoc x c' c

/-! ## §2 étale π₁ のファイバー関手的実現 -/

/-- **π₁^ét の有限レベルへの作用**（M14-5）: 逆極限群は射影を
    通じて各有限レベル（被覆塔の各段のファイバー）に作用する。 -/
def levelAction (S : InverseSystem) (i : S.Idx) : GAction (limitGrp S) where
  carrier := (S.G i).carrier
  act := fun σ x => (S.G i).mul ((limitProj S i).map σ) x
  act_one := fun x => by
    show (S.G i).mul ((limitProj S i).map (limitGrp S).one) x = x
    rw [(limitProj S i).map_one, (S.G i).one_mul]
  act_mul := fun g h x => by
    show (S.G i).mul ((limitProj S i).map ((limitGrp S).mul g h)) x = _
    rw [(limitProj S i).map_mul, (S.G i).mul_assoc]

/-- **定理 (M14-6): π₁^ét の作用は自然変換**（推移射と両立）—
    被覆塔の射（推移射）は π₁^ét-同変である。これが
    「π₁^ét = Aut(ファイバー関手)」の自然性条件の機械検証であり、
    Galois 圏の主定理の構造的内容の片翼。 -/
theorem level_transition_equivariant (S : InverseSystem) {i j : S.Idx}
    (h : S.le i j) (σ : (limitGrp S).carrier) (x : (S.G j).carrier) :
    (S.t h).map ((levelAction S j).act σ x)
      = (levelAction S i).act σ ((S.t h).map x) := by
  show (S.t h).map ((S.G j).mul ((limitProj S j).map σ) x)
      = (S.G i).mul ((limitProj S i).map σ) ((S.t h).map x)
  rw [(S.t h).map_mul, limitProj_compat]

/-! ## §3 Galois 対応の順序論的骨格 -/

/-- **反変 Galois 接続**: 部分群の順序集合（包含）と被覆の順序集合
    （支配）の間の反変随伴 F ⊣ Gm。Galois 圏の対応定理
    「被覆 ↔ 開部分群」の束論的核。 -/
structure GaloisConnection where
  A : Type
  B : Type
  leA : A → A → Prop
  leB : B → B → Prop
  leA_refl : ∀ a, leA a a
  leA_trans : ∀ {a b c}, leA a b → leA b c → leA a c
  leB_refl : ∀ b, leB b b
  leB_trans : ∀ {a b c}, leB a b → leB b c → leB a c
  /-- 部分群 ↦ 対応する被覆。 -/
  F : A → B
  /-- 被覆 ↦ 対応する部分群（ファイバーの固定化群）。 -/
  Gm : B → A
  /-- 反変随伴性。 -/
  adj : ∀ a b, leA a (Gm b) ↔ leB b (F a)

/-- **定理 (M14-7): 単位** — a ≤ Gm(F a)。 -/
theorem galois_unit (C : GaloisConnection) (a : C.A) : C.leA a (C.Gm (C.F a)) :=
  (C.adj a (C.F a)).mpr (C.leB_refl (C.F a))

/-- **定理 (M14-8): 余単位** — b ≤ F(Gm b)。 -/
theorem galois_counit (C : GaloisConnection) (b : C.B) : C.leB b (C.F (C.Gm b)) :=
  (C.adj (C.Gm b) b).mp (C.leA_refl (C.Gm b))

/-- **定理 (M14-9): F の反単調性** — a ≤ a' なら F a' ≤ F a
    （大きい部分群ほど小さい被覆）。 -/
theorem galois_F_antitone (C : GaloisConnection) {a a' : C.A}
    (h : C.leA a a') : C.leB (C.F a') (C.F a) :=
  (C.adj a (C.F a')).mp (C.leA_trans h (galois_unit C a'))

/-- Gm の反単調性。 -/
theorem galois_Gm_antitone (C : GaloisConnection) {b b' : C.B}
    (h : C.leB b b') : C.leA (C.Gm b') (C.Gm b) :=
  (C.adj (C.Gm b') b).mpr (C.leB_trans h (galois_counit C b'))

/-- **定理 (M14-10): 閉包の冪等性** — F(Gm(F a)) と F a は互いに
    支配し合う（= Galois 閉包で対応は安定する。対応定理が
    「閉じた」対象の間の全単射になる理由）。 -/
theorem galois_closure (C : GaloisConnection) (a : C.A) :
    C.leB (C.F (C.Gm (C.F a))) (C.F a) ∧
    C.leB (C.F a) (C.F (C.Gm (C.F a))) :=
  ⟨galois_F_antitone C (galois_unit C a), galois_counit C (C.F a)⟩

/-- **無矛盾性 (M14-11)**: 自明な接続（A = B = Unit）で充足可能。 -/
theorem galoisConnection_consistent : Nonempty GaloisConnection :=
  ⟨{ A := Unit, B := Unit,
     leA := fun _ _ => True, leB := fun _ _ => True,
     leA_refl := fun _ => trivial,
     leA_trans := fun _ _ => trivial,
     leB_refl := fun _ => trivial,
     leB_trans := fun _ _ => trivial,
     F := fun _ => (), Gm := fun _ => (),
     adj := fun _ _ => Iff.rfl }⟩

end IUT
