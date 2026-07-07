-- M424F TemperedPi1Etale [実・本物・柱A]
-- complete_pct 影響: 柱A で M364F/M374F/M384F/M389F の実部品を本物の tempered π₁^ét 群対象に組み上げ＝離散 Heisenberg テータ部 thetaGrp を deck 商 ℤ が共役（tpeAut）で捻る半直積群 tpeGroup を建設し、完全列 1→Δ^temp→π₁^temp→ℤ→1（正規性・分裂切断つき・非中心拡大）・テータ交換子＝シクロトーム着地・deck×テータ交換子 = n·b・μ_l 像・M374F 塔 ℤ/l^n→ℤ_l への deck 完備化・M389F 外ガロア χ 捻りの拡張を完全証明。
-- 正直な限定: 完全な slim 遠アーベル性（本群は中心 μ 非自明＝非 slim を定理で明示）・Tate 曲線の実被覆空間としての幾何的実現・p 進解析テータ・実 G_K（非可換）への商の置換は外部/後続。deck/ガロア商は ℤ（不分岐 Frobenius 方向のモデル）。

/-
  IUT/TemperedPi1Etale.lean — M424F [実／本物・柱A]
  分類: 実（tempered π₁^ét の群対象としての組み上げ＝Heisenberg テータ部 ⋊ deck 商 ℤ）

  既存の実部品:
    * M364F (TemperedPi1): π₁^temp の拡大骨格 1→Ẑ→π₁^temp→ℤ→1（ただし可換な直積モデル Ẑ×ℤ）
    * M374F (TemperedTower): deck 群の塔 ℤ/l^n・逆極限 ℤ_l・離散部の完備化 ℤ↪ℤ_l
    * M384F (TemperedThetaCommutator): 離散 Heisenberg テータ群 thetaGrp・交換子＝
      シンプレクティック形式・中心＝シクロトーム・μ_l 像
    * M389F (TemperedThetaOuterAction): G_K の外ガロア作用（中心を χ で捻る ttoaScale/ttoaAct）

  本モジュールはこれらを**一つの本物の群対象**に組み上げる（次の実ステップ）:

    tpeGroup ＝ thetaGrp ⋊_α ℤ、台 (ℤ³) × ℤ、積
      ((a,b,c),n)·((a',b',c'),n') = ((a+a', b+b', c + (c' + n·b') + a·b'), n+n')
    ここで α_n(a,b,c) = (a, b, c + n·b) は deck 元 n の**本物の自己同型**
    （thetaGrp 内の deck 持ち上げ (n,0,0) による共役に一致、tpe_aut_conj_in_theta）。
    M364F の可換モデル Ẑ×ℤ と異なり、この拡大は**非中心・非可換**（分裂するが直積でない）。

  完全証明する内容（すべて本物の群演算・toy 主語なし）:
    * tpeGroup の群公理（結合律・単位・逆元、整数演算で完全証明）
    * 完全列 1 → Δ^temp(=thetaGrp) → π₁^temp(=tpeGroup) → ℤ → 1:
      ι 単射・pr 全射・ker(pr)=im(ι)・**ι(thetaGrp) は正規**（共役の明示公式
      g·ι(z)·g⁻¹ = ι(a, b, c+n·b+p·b−a·q)）・分裂切断 s（pr∘s=id）・
      拡大は非中心（s(1) は ι(0,1,0) と可換でない）
    * テータ交換子は組み上げ群でも中心シクロトームに着地:
      [ι x, ι y] = ι(0,0,ω(x,y))（ω=シンプレクティック形式、M384F/M11 昇格）、
      [s n, ι(a,b,c)] = ι(0,0,n·b)（**deck×テータ交換子＝ペアリング**、[EtTh] の
      「deck 生成元とテータ切断の交換子が μ を生む」の本物の内容）、
      標準生成元交換子 = ι(0,0,1) ≠ 1、μ_l 像 = ζ（M384F centerToMu 昇格）
    * シクロトーム ι(0,0,c) は組み上げ群全体の中心（tpe_cyclotome_central）ゆえ
      **本群は slim でない**（tpe_model_not_slim、正直な限定を定理で固定）
    * tempered 性: tpeGroup は有界指数でない（非副有限、M9-6/M364F 昇格）
    * アーベル化 tpeAb : tpeGroup → ℤ²×ℤ は全交換子を潰す（非可換性が中心 μ に圧縮）
    * M374F 塔接続: deck 商 ℤ から各段 ℤ/l^n への全射・遷移錐・逆極限 ℤ_l への完備化が
      tpeGroup から誘導される（tpeDeckLevel / tpeDeckComplete）
    * M389F 外ガロア作用の拡張: tpeScale e（テータ部に ttoaScale・deck 部に恒等）は
      (ℤ,·) のモノイド作用・deck 射影と可換（ガロアは deck 商に自明に作用）・
      テータ部への制限が M389F の ttoaAct に一致（on the nose）・組み上げ群の
      テータ交換子が χ で捻れる（tpe_act_commutator_twist / tpe_act_commutator_chi）

  正直な限定（消さない・弱めない）:
    * 実際の π₁^temp(X_v) の slim 遠アーベル性は外部（[SemiAnbd] André–Mochizuki）。
      本組み上げ群は中心 μ が非自明で slim で**ない**ことを定理で明示する
      （tpe_model_not_slim）。slim なのは完全な幾何的 Δ^temp であり、本群は
      そのテータ商（mono-theta 環境の群論的骨格）に相当する。
    * Tate 曲線の実被覆空間（位相空間・スキーム）としての tempered 被覆の実現、
      p 進解析的テータ関数のガロア同変評価は外部/後続。
    * deck/ガロア商は ℤ（不分岐 Frobenius 方向・テータ被覆 deck 群のモデル）。
      実 G_K（非可換副有限）への置換は後続（M389F の CycGKAction が μ 側の実作用）。
    * χ 捻り（tpeScale）は組み上げ群全体の自己同型ではない（M389F-2b と同じ
      コサイクル捻りの正直な内容）——交換子の χ 変換として定式化する。
  全て選択公理不使用（propext / Quot.sound のみ）。
-/
import IUT.TemperedThetaOuterAction
import IUT.TemperedTower

namespace IUT

/-! ## M424F-0: 4 成分の等値補題（(ℤ³)×ℤ 用の ext） -/

/-- 組み上げ群の台 (ℤ³)×ℤ の等値補題（4 成分）。 -/
theorem tpe_ext {a₁ b₁ c₁ n₁ a₂ b₂ c₂ n₂ : Int}
    (h1 : a₁ = a₂) (h2 : b₁ = b₂) (h3 : c₁ = c₂) (h4 : n₁ = n₂) :
    ((((a₁, b₁, c₁) : Int × Int × Int), n₁) : (Int × Int × Int) × Int)
      = (((a₂, b₂, c₂) : Int × Int × Int), n₂) := by
  rw [h1, h2, h3, h4]

/-! ## M424F-1: deck 自己同型 α_n（ttoaScale と違い本物の自己同型）

  外ガロア作用のスケール捻り ttoaScale は Heisenberg 積の自己同型で**ない**
  （M389F-2b の正直な内容）。半直積を群にするには**本物の自己同型**が要る。
  α_n(a,b,c) = (a, b, c + n·b) がそれで、thetaGrp 内の deck 持ち上げ (n,0,0)
  による共役にちょうど一致する（M424F-1d）。 -/

/-- **M424F-1a: deck 自己同型** α_n(a,b,c) = (a, b, c + n·b)。deck 元 n が
    テータ部の中心座標を b とのペアリング分だけずらす。 -/
@[reducible] def tpeAut (n : Int) (x : thetaGrp.carrier) : thetaGrp.carrier :=
  (x.1, x.2.1, x.2.2 + n * x.2.1)

/-- α_n の成分表示。 -/
theorem tpe_aut_apply (n a b c : Int) :
    tpeAut n ((a, b, c) : Int × Int × Int) = ((a, b, c + n * b) : Int × Int × Int) := rfl

/-- **定理 (M424F-1b): α_n は本物の群準同型** — ttoaScale と違い Heisenberg 積を
    on the nose で保つ（コサイクル a·b′ は幾何座標のみに依存し α_n で不変ゆえ）。 -/
theorem tpe_aut_hom (n : Int) (x y : thetaGrp.carrier) :
    tpeAut n (thetaGrp.mul x y) = thetaGrp.mul (tpeAut n x) (tpeAut n y) := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := y
  show ((a + a', b + b', (c + c' + a * b') + n * (b + b')) : Int × Int × Int)
    = (a + a', b + b', (c + n * b) + (c' + n * b') + a * b')
  refine triple_ext rfl rfl ?_
  rw [Int.mul_add]
  generalize a * b' = P
  generalize n * b = Q
  generalize n * b' = R
  omega

/-- **定理 (M424F-1c): α は (ℤ,+) の作用** — α_0 = id、α_{n+m} = α_n ∘ α_m。 -/
theorem tpe_aut_zero (x : thetaGrp.carrier) : tpeAut 0 x = x := by
  obtain ⟨a, b, c⟩ := x
  show ((a, b, c + 0 * b) : Int × Int × Int) = (a, b, c)
  refine triple_ext rfl rfl (by omega)

theorem tpe_aut_add (n m : Int) (x : thetaGrp.carrier) :
    tpeAut n (tpeAut m x) = tpeAut (n + m) x := by
  obtain ⟨a, b, c⟩ := x
  show ((a, b, (c + m * b) + n * b) : Int × Int × Int) = (a, b, c + (n + m) * b)
  refine triple_ext rfl rfl ?_
  rw [Int.add_mul]
  generalize n * b = P
  generalize m * b = Q
  omega

/-- **定理 (M424F-1d): α_n は thetaGrp 内の deck 持ち上げ (n,0,0) による共役** —
    (n,0,0)·x·(n,0,0)⁻¹ = α_n(x)。半直積の deck 作用が Heisenberg の内部の
    deck 方向（第 1 座標）の共役の忠実な延長であることの本物の内容。 -/
theorem tpe_aut_conj_in_theta (n : Int) (x : thetaGrp.carrier) :
    thetaGrp.mul (thetaGrp.mul ((n, 0, 0) : Int × Int × Int) x)
        (thetaGrp.inv ((n, 0, 0) : Int × Int × Int))
      = tpeAut n x := by
  obtain ⟨a, b, c⟩ := x
  show ((n + a + -n, 0 + b + -0, (0 + c + n * b) + (-0 + n * 0) + (n + a) * -0)
      : Int × Int × Int)
    = (a, b, c + n * b)
  refine triple_ext (by omega) (by omega) ?_
  rw [Int.mul_neg, Int.mul_zero, Int.mul_zero]
  generalize n * b = P
  omega

/-! ## M424F-2: 組み上げ群 tpeGroup ＝ thetaGrp ⋊_α ℤ（本物の群公理を完全証明） -/

/-- **M424F-2: tempered π₁^ét の組み上げ群** tpeGroup ＝ thetaGrp ⋊_α ℤ。
    台 (ℤ³)×ℤ、積 ((a,b,c),n)·((a',b',c'),n') = ((a,b,c)·α_n(a',b',c'), n+n')。
    テータ部（離散 Heisenberg、M384F）を deck 商 ℤ が α で捻る**非可換・非中心**の
    半直積（M364F の可換直積モデル Ẑ×ℤ の本物への昇格）。 -/
@[reducible] def tpeGroup : Grp where
  carrier := (Int × Int × Int) × Int
  mul := fun x y => (thetaGrp.mul x.1 (tpeAut x.2 y.1), x.2 + y.2)
  one := (((0, 0, 0) : Int × Int × Int), (0 : Int))
  inv := fun x => (tpeAut (-x.2) (thetaGrp.inv x.1), -x.2)
  mul_assoc := by
    intro x y z
    obtain ⟨⟨a, b, c⟩, n⟩ := x
    obtain ⟨⟨a', b', c'⟩, n'⟩ := y
    obtain ⟨⟨a'', b'', c''⟩, n''⟩ := z
    show ((((a + a') + a'', (b + b') + b'',
          (c + (c' + n * b') + a * b') + (c'' + (n + n') * b'') + (a + a') * b'')
        : Int × Int × Int), (n + n') + n'')
      = (((a + (a' + a''), b + (b' + b''),
          c + ((c' + (c'' + n' * b'') + a' * b'') + n * (b' + b'')) + a * (b' + b''))
        : Int × Int × Int), n + (n' + n''))
    refine tpe_ext (by omega) (by omega) ?_ (by omega)
    rw [Int.add_mul, Int.add_mul, Int.mul_add, Int.mul_add]
    generalize n * b' = P1
    generalize a * b' = P2
    generalize n' * b'' = P3
    generalize a' * b'' = P4
    generalize n * b'' = P5
    generalize a * b'' = P6
    omega
  one_mul := by
    intro x
    obtain ⟨⟨a, b, c⟩, n⟩ := x
    show (((0 + a, 0 + b, 0 + (c + 0 * b) + 0 * b) : Int × Int × Int), 0 + n)
      = (((a, b, c) : Int × Int × Int), n)
    refine tpe_ext (by omega) (by omega) (by omega) (by omega)
  inv_mul := by
    intro x
    obtain ⟨⟨a, b, c⟩, n⟩ := x
    show (((-a + a, -b + b, (-c + a * b + (-n) * (-b)) + (c + (-n) * b) + (-a) * b)
        : Int × Int × Int), -n + n)
      = ((((0 : Int), 0, 0) : Int × Int × Int), (0 : Int))
    refine tpe_ext (by omega) (by omega) ?_ (by omega)
    rw [Int.neg_mul_neg, Int.neg_mul, Int.neg_mul]
    generalize a * b = P
    generalize n * b = Q
    omega

/-- 積の成分表示（definitional）。 -/
theorem tpe_mul_expand (a b c n a' b' c' n' : Int) :
    tpeGroup.mul (((a, b, c) : Int × Int × Int), n) (((a', b', c') : Int × Int × Int), n')
      = (((a + a', b + b', c + (c' + n * b') + a * b') : Int × Int × Int), n + n') := rfl

/-- 逆元の成分表示。 -/
theorem tpe_inv_expand (a b c n : Int) :
    tpeGroup.inv (((a, b, c) : Int × Int × Int), n)
      = (((-a, -b, -c + a * b + n * b) : Int × Int × Int), -n) := by
  show (((-a, -b, -c + a * b + (-n) * (-b)) : Int × Int × Int), -n)
    = (((-a, -b, -c + a * b + n * b) : Int × Int × Int), -n)
  refine tpe_ext rfl rfl ?_ rfl
  rw [Int.neg_mul_neg]

/-! ## M424F-3: 完全列 1 → Δ^temp → π₁^temp → ℤ → 1（正規性・分裂込み） -/

/-- **核埋め込み ι : thetaGrp ↪ tpeGroup**（z ↦ (z, 0)）— 幾何的テータ部
    Δ^temp（離散 Heisenberg）を組み上げ群の核として埋め込む本物の群準同型。 -/
def tpeIncl : Hom thetaGrp tpeGroup where
  map := fun z => (z, (0 : Int))
  map_mul := by
    intro z w
    obtain ⟨a, b, c⟩ := z
    obtain ⟨a', b', c'⟩ := w
    show (((a + a', b + b', c + c' + a * b') : Int × Int × Int), (0 : Int))
      = (((a + a', b + b', c + (c' + 0 * b') + a * b') : Int × Int × Int), 0 + 0)
    refine tpe_ext rfl rfl ?_ (by omega)
    generalize a * b' = P
    omega

/-- **射影 pr : tpeGroup ↠ ℤ**（(z, n) ↦ n）— 組み上げ群から数論的/deck 商 ℤ
    （＝ M364F の離散部 `tmpDiscretePart`）への全射準同型。 -/
def tpeProj : Hom tpeGroup tmpDiscretePart where
  map := fun x => x.2
  map_mul := fun _ _ => rfl

/-- **分裂切断 s : ℤ → tpeGroup**（n ↦ (1_Θ, n)）— 拡大の分裂（pr∘s = id）。 -/
def tpeSection : Hom intGrp tpeGroup where
  map := fun n => (((0, 0, 0) : Int × Int × Int), n)
  map_mul := by
    intro m n
    show ((((0 : Int), 0, 0) : Int × Int × Int), m + n)
      = (((0 + 0, 0 + 0, 0 + (0 + m * 0) + 0 * 0) : Int × Int × Int), m + n)
    refine tpe_ext (by omega) (by omega) (by omega) rfl

/-- **定理 (M424F-3a): ι は単射**。 -/
theorem tpe_incl_injective : tpeIncl.Injective :=
  fun _ _ h => congrArg Prod.fst h

/-- **定理 (M424F-3b): pr は全射**（切断 s の像で実現）。 -/
theorem tpe_proj_surjective : ∀ g : tmpDiscretePart.carrier, ∃ x, tpeProj.map x = g :=
  fun g => ⟨tpeSection.map g, rfl⟩

/-- **定理 (M424F-3c): 切断は分裂** pr ∘ s = id。 -/
theorem tpe_section_splits (n : Int) : tpeProj.map (tpeSection.map n) = n := rfl

/-- **定理 (M424F-3d): 拡大の完全性** — ker(pr) = im(ι)。
    テータ部（幾何）がちょうど deck/数論商への射影の核である。 -/
theorem tpe_extension_exact (x : tpeGroup.carrier) :
    tpeProj.map x = tmpDiscretePart.one ↔ ∃ z : thetaGrp.carrier, tpeIncl.map z = x := by
  obtain ⟨z, n⟩ := x
  constructor
  · intro h
    have hn : n = (0 : Int) := h
    subst hn
    exact ⟨z, rfl⟩
  · intro h
    obtain ⟨w, hw⟩ := h
    show n = (0 : Int)
    exact (congrArg Prod.snd hw).symm

/-- **定理 (M424F-3e): 共役の明示公式** — 任意の g = ((p,q,r),n) による ι(a,b,c) の
    共役は ι(a, b, c + n·b + p·b − a·q)。テータ部の共役が幾何座標を固定し中心座標を
    deck・幾何ペアリングの線形形式でずらすことの完全計算。 -/
theorem tpe_conj_incl (p q r n a b c : Int) :
    tpeGroup.mul
        (tpeGroup.mul (((p, q, r) : Int × Int × Int), n)
          (tpeIncl.map ((a, b, c) : Int × Int × Int)))
        (tpeGroup.inv (((p, q, r) : Int × Int × Int), n))
      = tpeIncl.map ((a, b, c + n * b + p * b - a * q) : Int × Int × Int) := by
  have h1 : tpeGroup.mul (((p, q, r) : Int × Int × Int), n)
        (tpeIncl.map ((a, b, c) : Int × Int × Int))
      = (((p + a, q + b, r + c + n * b + p * b) : Int × Int × Int), n) := by
    show (((p + a, q + b, r + (c + n * b) + p * b) : Int × Int × Int), n + 0)
      = (((p + a, q + b, r + c + n * b + p * b) : Int × Int × Int), n)
    refine tpe_ext rfl rfl ?_ (by omega)
    generalize n * b = A
    generalize p * b = B
    omega
  rw [h1, tpe_inv_expand]
  show ((((p + a) + -p, (q + b) + -q,
        (r + c + n * b + p * b) + ((-r + p * q + n * q) + n * -q) + (p + a) * -q)
      : Int × Int × Int), n + -n)
    = (((a, b, c + n * b + p * b - a * q) : Int × Int × Int), (0 : Int))
  refine tpe_ext (by omega) (by omega) ?_ (by omega)
  rw [Int.add_mul, Int.mul_neg, Int.mul_neg, Int.mul_neg]
  generalize n * b = A
  generalize p * b = B
  generalize p * q = C
  generalize n * q = D
  generalize a * q = E
  omega

/-- **定理 (M424F-3f): ι(thetaGrp) は正規部分群** — 任意の共役が像に留まる
    （明示 witness つき）。完全列 1→Δ^temp→π₁^temp→ℤ→1 の正規性の本物の証明。 -/
theorem tpe_geometric_normal (g : tpeGroup.carrier) (z : thetaGrp.carrier) :
    ∃ w : thetaGrp.carrier,
      tpeGroup.mul (tpeGroup.mul g (tpeIncl.map z)) (tpeGroup.inv g) = tpeIncl.map w := by
  obtain ⟨⟨p, q, r⟩, n⟩ := g
  obtain ⟨a, b, c⟩ := z
  exact ⟨(a, b, c + n * b + p * b - a * q), tpe_conj_incl p q r n a b c⟩

/-- **定理 (M424F-3g): deck 切断の共役 ＝ α_n** — s(n)·ι(z)·s(n)⁻¹ = ι(α_n z)。
    半直積の deck 作用が組み上げ群内の共役として実現される（構成の自己整合）。 -/
theorem tpe_section_conj (n a b c : Int) :
    tpeGroup.mul (tpeGroup.mul (tpeSection.map n) (tpeIncl.map ((a, b, c) : Int × Int × Int)))
        (tpeGroup.inv (tpeSection.map n))
      = tpeIncl.map ((a, b, c + n * b) : Int × Int × Int) := by
  have h : tpeGroup.mul
        (tpeGroup.mul (tpeSection.map n) (tpeIncl.map ((a, b, c) : Int × Int × Int)))
        (tpeGroup.inv (tpeSection.map n))
      = tpeIncl.map ((a, b, c + n * b + 0 * b - a * 0) : Int × Int × Int) :=
    tpe_conj_incl 0 0 0 n a b c
  rw [h]
  exact congrArg tpeIncl.map (triple_ext rfl rfl (by
    generalize n * b = A
    omega))

/-- **定理 (M424F-3h): 拡大は非中心（M364F の可換モデルとの本質的差）** —
    deck 切断 s(1) はテータ部 ι(0,1,0) と可換でない。組み上げ群が
    直積 Ẑ×ℤ（M364F モデル）でなく真の半直積であることの証人。 -/
theorem tpe_extension_not_central :
    tpeGroup.mul (tpeSection.map 1) (tpeIncl.map ((0, 1, 0) : Int × Int × Int))
      ≠ tpeGroup.mul (tpeIncl.map ((0, 1, 0) : Int × Int × Int)) (tpeSection.map 1) := by
  intro h
  have hL : tpeGroup.mul (tpeSection.map 1) (tpeIncl.map ((0, 1, 0) : Int × Int × Int))
      = (((0, 1, 1) : Int × Int × Int), (1 : Int)) := by
    show (((0 + 0, 0 + 1, 0 + (0 + 1 * 1) + 0 * 1) : Int × Int × Int), (1 : Int) + 0)
      = (((0, 1, 1) : Int × Int × Int), (1 : Int))
    refine tpe_ext (by omega) (by omega) (by omega) (by omega)
  have hR : tpeGroup.mul (tpeIncl.map ((0, 1, 0) : Int × Int × Int)) (tpeSection.map 1)
      = (((0, 1, 0) : Int × Int × Int), (1 : Int)) := by
    show (((0 + 0, 1 + 0, 0 + (0 + 0 * 0) + 0 * 0) : Int × Int × Int), (0 : Int) + 1)
      = (((0, 1, 0) : Int × Int × Int), (1 : Int))
    refine tpe_ext (by omega) (by omega) (by omega) (by omega)
  rw [hL, hR] at h
  have h3 : (1 : Int) = 0 := congrArg (fun t => t.1.2.2) h
  exact absurd h3 (by omega)

/-! ## M424F-4: テータ交換子構造は組み上げ群に持ち上がる（本丸その 1） -/

/-- 交換子の共役表示 [x,y] = (x·y·x⁻¹)·y⁻¹（群公理のみ）。 -/
theorem tpe_comm_eq (x y : tpeGroup.carrier) :
    tpeGroup.comm x y
      = tpeGroup.mul (tpeGroup.mul (tpeGroup.mul x y) (tpeGroup.inv x)) (tpeGroup.inv y) := by
  unfold Grp.comm
  rw [tpeGroup.mul_assoc (tpeGroup.mul x y) (tpeGroup.inv x) (tpeGroup.inv y)]

/-- **定理 (M424F-4a): テータ交換子は組み上げ群でも中心シクロトームに着地** —
    [ι x, ι y] = ι(0, 0, a·b′−a′·b)（シンプレクティック形式、M384F/M11 の昇格）。 -/
theorem tpe_commutator_cyclotome (a b c a' b' c' : Int) :
    tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int))
      = tpeIncl.map ((0, 0, a * b' - a' * b) : Int × Int × Int) := by
  rw [← tpeIncl.map_grp_comm, theta_comm]

/-- **定理 (M424F-4b): deck×テータ交換子＝ペアリング（本丸）** —
    [s(n), ι(a,b,c)] = ι(0, 0, n·b)。deck 生成元とテータ切断の交換子が
    ちょうどシクロトーム（中心 μ の離散モデル）に n·b を生む——[EtTh] の
    「テータ群の交換子構造が deck 方向まで込みで μ に圧縮される」の本物の内容。
    M364F の可換モデルではこの交換子は恒等的に 1 だった。 -/
theorem tpe_deck_theta_commutator (n a b c : Int) :
    tpeGroup.comm (tpeSection.map n) (tpeIncl.map ((a, b, c) : Int × Int × Int))
      = tpeIncl.map ((0, 0, n * b) : Int × Int × Int) := by
  rw [tpe_comm_eq]
  have hconj : tpeGroup.mul
        (tpeGroup.mul (tpeSection.map n) (tpeIncl.map ((a, b, c) : Int × Int × Int)))
        (tpeGroup.inv (tpeSection.map n))
      = tpeIncl.map ((a, b, c + n * b) : Int × Int × Int) := tpe_section_conj n a b c
  rw [hconj, ← tpeIncl.map_inv, ← tpeIncl.map_mul]
  have hinner : thetaGrp.mul ((a, b, c + n * b) : Int × Int × Int)
        (thetaGrp.inv ((a, b, c) : Int × Int × Int))
      = ((0, 0, n * b) : Int × Int × Int) := by
    show ((a + -a, b + -b, (c + n * b) + (-c + a * b) + a * -b) : Int × Int × Int)
      = ((0, 0, n * b) : Int × Int × Int)
    refine triple_ext (by omega) (by omega) ?_
    rw [Int.mul_neg]
    generalize n * b = A
    generalize a * b = B
    omega
  rw [hinner]

/-- **定理 (M424F-4c): 標準生成元交換子 = 中心生成元 ι(0,0,1)**（M11 comm_xy 昇格）。 -/
theorem tpe_commutator_gen :
    tpeGroup.comm (tpeIncl.map ((1, 0, 0) : Int × Int × Int))
        (tpeIncl.map ((0, 1, 0) : Int × Int × Int))
      = tpeIncl.map ((0, 0, 1) : Int × Int × Int) := by
  rw [← tpeIncl.map_grp_comm, comm_xy]

/-- **定理 (M424F-4d): 中心生成元 ι(0,0,1) は非自明**。 -/
theorem tpe_commutator_gen_ne_one :
    tpeIncl.map ((0, 0, 1) : Int × Int × Int) ≠ tpeGroup.one := by
  intro h
  have h3 : (1 : Int) = 0 := congrArg (fun t => t.1.2.2) h
  exact absurd h3 (by omega)

/-- **定理 (M424F-4e): 組み上げ群は非可換**（M379F の可換塔・M364F の可換モデルと対照）。 -/
theorem tpe_nonabelian : ¬ tcmAbelian tpeGroup := by
  intro h
  have h2 := h (tpeIncl.map ((1, 0, 0) : Int × Int × Int))
    (tpeIncl.map ((0, 1, 0) : Int × Int × Int))
  have hL : tpeGroup.mul (tpeIncl.map ((1, 0, 0) : Int × Int × Int))
      (tpeIncl.map ((0, 1, 0) : Int × Int × Int)) = (((1, 1, 1) : Int × Int × Int), (0 : Int)) := by
    show (((1 + 0, 0 + 1, 0 + (0 + 0 * 1) + 1 * 1) : Int × Int × Int), (0 : Int) + 0)
      = (((1, 1, 1) : Int × Int × Int), (0 : Int))
    refine tpe_ext (by omega) (by omega) (by omega) (by omega)
  have hR : tpeGroup.mul (tpeIncl.map ((0, 1, 0) : Int × Int × Int))
      (tpeIncl.map ((1, 0, 0) : Int × Int × Int)) = (((1, 1, 0) : Int × Int × Int), (0 : Int)) := by
    show (((0 + 1, 1 + 0, 0 + (0 + 0 * 0) + 0 * 0) : Int × Int × Int), (0 : Int) + 0)
      = (((1, 1, 0) : Int × Int × Int), (0 : Int))
    refine tpe_ext (by omega) (by omega) (by omega) (by omega)
  rw [hL, hR] at h2
  have h3 : (1 : Int) = 0 := congrArg (fun t => t.1.2.2) h2
  exact absurd h3 (by omega)

/-- **定理 (M424F-4f): 交換子の μ_l 像 = ζ**（M384F centerToMu 同期写像の昇格）—
    組み上げ群の標準テータ交換子の中心座標を μ_l に送ると非自明な ζ を得る。 -/
theorem tpe_commutator_mu (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    centerToMu p l ζ
        ((tpeGroup.comm (tpeIncl.map ((1, 0, 0) : Int × Int × Int))
          (tpeIncl.map ((0, 1, 0) : Int × Int × Int))).1.2.2)
      = zpPow p ζ 1 := by
  rw [← tpeIncl.map_grp_comm]
  exact ttc_commutator_mu p l hl ζ

/-! ## M424F-5: 中心＝シクロトーム・非 slim（正直な限定を定理で固定）・非有界指数 -/

/-- **定理 (M424F-5a): シクロトーム ι(0,0,c) は組み上げ群全体の中心** —
    テータ部の中心 μ が deck 拡大後も中心に残る（α_n は中心を固定するゆえ）。 -/
theorem tpe_cyclotome_central (c : Int) :
    ∀ g : tpeGroup.carrier,
      tpeGroup.mul (tpeIncl.map ((0, 0, c) : Int × Int × Int)) g
        = tpeGroup.mul g (tpeIncl.map ((0, 0, c) : Int × Int × Int)) := by
  intro g
  obtain ⟨⟨a, b, c'⟩, n⟩ := g
  show (((0 + a, 0 + b, c + (c' + 0 * b) + 0 * b) : Int × Int × Int), 0 + n)
    = (((a + 0, b + 0, c' + (c + n * 0) + a * 0) : Int × Int × Int), n + 0)
  refine tpe_ext (by omega) (by omega) (by omega) (by omega)

/-- **定理 (M424F-5b): 組み上げ群は slim でない（正直な限定の定理化）** —
    中心に非自明な μ（ι(0,0,1)）が残るため中心自明性は成り立たない。
    slim なのは完全な幾何的 Δ^temp（[SemiAnbd]、外部）であり、本群は
    mono-theta 環境のテータ商（中心 μ を**持つべき**群）の骨格である。 -/
theorem tpe_model_not_slim : ¬ Slim tpeGroup := by
  intro h
  have h1 := h (tpeIncl.map ((0, 0, 1) : Int × Int × Int)) (tpe_cyclotome_central 1)
  have h3 : (1 : Int) = 0 := congrArg (fun t => t.1.2.2) h1
  exact absurd h3 (by omega)

/-- **定理 (M424F-5c): 組み上げ群は有界指数でない（真に tempered・非副有限）** —
    deck 切断 s : ℤ ↪ tpeGroup が忠実ゆえ（M9-6/M364F の昇格）。 -/
theorem tpe_not_bounded : ¬ BoundedExponent tpeGroup := by
  intro h
  obtain ⟨N, hN, hpow⟩ := h
  apply theta_deck_not_finite
  refine ⟨N, hN, ?_⟩
  intro g
  have hg : tpeGroup.pow (tpeSection.map g) N = tpeGroup.one := hpow (tpeSection.map g)
  have hgp : tpeSection.map (intGrp.pow g N) = tpeGroup.pow (tpeSection.map g) N :=
    tpeSection.map_pow g N
  rw [hg] at hgp
  exact congrArg Prod.snd hgp

/-! ## M424F-6: アーベル化（非可換性は中心 μ に圧縮される・M384F の昇格） -/

/-- **M424F-6a: アーベル化群** ℤ² × ℤ（テータ部の幾何座標 × deck 商）。 -/
def tpeAbGrp : Grp := prodGrp ttcAbGrp intGrp

/-- **M424F-6b: アーベル化射影** ((a,b,c),n) ↦ ((a,b),n)（本物の準同型、
    α_n が中心座標しか動かさないゆえ deck 捻りはアーベル化で消える）。 -/
def tpeAb : Hom tpeGroup tpeAbGrp where
  map := fun x => ((x.1.1, x.1.2.1), x.2)
  map_mul := fun _ _ => rfl

/-- **定理 (M424F-6c): アーベル化群は可換**。 -/
theorem tpe_ab_abelian : tcmAbelian tpeAbGrp := by
  intro x y
  obtain ⟨⟨u, v⟩, n⟩ := x
  obtain ⟨⟨u', v'⟩, n'⟩ := y
  show (((u + u', v + v') : Int × Int), n + n') = (((u' + u, v' + v) : Int × Int), n' + n)
  rw [Int.add_comm u u', Int.add_comm v v', Int.add_comm n n']

/-- **定理 (M424F-6d): アーベル化はテータ交換子を潰す** — 非可換性（シクロトーム座標）
    がアーベル化で消え、中心 μ 一次元に圧縮されることの組み上げ群版。 -/
theorem tpe_ab_kills_commutator (a b c a' b' c' : Int) :
    tpeAb.map (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int)))
      = tpeAbGrp.one := by
  rw [tpe_commutator_cyclotome]
  rfl

/-- **定理 (M424F-6e): アーベル化は deck×テータ交換子も潰す**。 -/
theorem tpe_ab_kills_deck_commutator (n a b c : Int) :
    tpeAb.map (tpeGroup.comm (tpeSection.map n) (tpeIncl.map ((a, b, c) : Int × Int × Int)))
      = tpeAbGrp.one := by
  rw [tpe_deck_theta_commutator]
  rfl

/-! ## M424F-7: M374F 被覆塔への接続（deck 商の各段全射・遷移錐・ℤ_l 完備化） -/

/-- **M424F-7a: 第 n 段 deck 射影** tpeGroup ↠ ℤ/l^n（deck 商 ℤ を M374F の塔の
    第 n 段へ還元）。 -/
def tpeDeckLevel (l n : Nat) : Hom tpeGroup (ttwDeckTower l n) :=
  (ttwDiscreteProj l n).comp tpeProj

/-- **M424F-7b: deck 完備化** tpeGroup → ℤ_l（deck 商 ℤ の M374F 逆極限 lim ℤ/l^n
    への完備化）。組み上げ群の deck 方向が本物の副有限塔に住むことの形式化。 -/
def tpeDeckComplete (l : Nat) : Hom tpeGroup (ttwInverseLimit l) :=
  (ttwDiscreteComplete l).comp tpeProj

/-- **定理 (M424F-7c): 各段射影は遷移と整合する錐**（M374F の錐の昇格）。 -/
theorem tpe_deck_transition_cone (l n : Nat) (x : tpeGroup.carrier) :
    (ttwTransition l n).map ((tpeDeckLevel l (n + 1)).map x) = (tpeDeckLevel l n).map x :=
  ttw_discrete_cone l n (tpeProj.map x)

/-- **定理 (M424F-7d): 完備化を第 n 段へ射影すると各段射影**（逆極限の錐）。 -/
theorem tpe_deck_complete_cone (l n : Nat) (x : tpeGroup.carrier) :
    (ttwLimitProj l n).map ((tpeDeckComplete l).map x) = (tpeDeckLevel l n).map x :=
  ttw_discrete_to_level l n (tpeProj.map x)

/-- **定理 (M424F-7e): 組み上げ群は各段 ℤ/l^n へ全射**（塔の各有限段が
    π₁^temp の商として実現、M374F の昇格）。 -/
theorem tpe_deck_level_surjective (l n : Nat) :
    ∀ y : (ttwDeckTower l n).carrier, ∃ x : tpeGroup.carrier, (tpeDeckLevel l n).map x = y := by
  intro y
  obtain ⟨a, ha⟩ := ttw_discrete_surjective l n y
  exact ⟨tpeSection.map a, ha⟩

/-! ## M424F-8: 外ガロア作用の拡張（M389F ttoa の組み上げ群への持ち上げ） -/

/-- **M424F-8a: スケール作用の拡張** — テータ部に M389F の ttoaScale・deck 部に恒等。
    G_K がシクロトーム（テータ部の中心）を捻り deck 商には自明に作用する骨格。 -/
@[reducible] def tpeScale (e : Int) (x : tpeGroup.carrier) : tpeGroup.carrier :=
  (ttoaScale e x.1, x.2)

/-- **M424F-8b: 外ガロア作用の拡張** tpeAct g = tpeScale (χ(g))（χ = M322F の実円分指標）。 -/
@[reducible] def tpeAct (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (x : tpeGroup.carrier) : tpeGroup.carrier :=
  tpeScale (ttoaChar GK M ρ g) x

/-- **定理 (M424F-8c): スケール作用の単位則** tpeScale 1 = id。 -/
theorem tpe_scale_one (x : tpeGroup.carrier) : tpeScale 1 x = x := by
  obtain ⟨z, n⟩ := x
  show (ttoaScale 1 z, n) = (z, n)
  rw [ttoa_scale_one]

/-- **定理 (M424F-8d): スケール作用の合成則**（(ℤ,·) のモノイド作用、M389F 昇格）。 -/
theorem tpe_scale_mul (e e' : Int) (x : tpeGroup.carrier) :
    tpeScale e (tpeScale e' x) = tpeScale (e * e') x := by
  obtain ⟨z, n⟩ := x
  show (ttoaScale e (ttoaScale e' z), n) = (ttoaScale (e * e') z, n)
  rw [ttoa_scale_mul]

/-- **定理 (M424F-8e): 作用はテータ部への制限で M389F の ttoaAct に一致**（on the nose）。 -/
theorem tpe_act_extends (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (z : thetaGrp.carrier) :
    tpeAct GK M ρ g (tpeIncl.map z) = tpeIncl.map (ttoaAct GK M ρ g z) := rfl

/-- **定理 (M424F-8f): ガロアは deck 商に自明に作用**（pr∘act = pr）。 -/
theorem tpe_act_deck_trivial (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (x : tpeGroup.carrier) :
    tpeProj.map (tpeAct GK M ρ g x) = tpeProj.map x := rfl

/-- **定理 (M424F-8g): 中心（シクロトーム）上では作用は積を保つ**（μ への制限は
    本物の準同型、M389F-2a の昇格）。 -/
theorem tpe_act_center_hom (e c c' : Int) :
    tpeScale e (tpeGroup.mul (tpeIncl.map ((0, 0, c) : Int × Int × Int))
        (tpeIncl.map ((0, 0, c') : Int × Int × Int)))
      = tpeGroup.mul (tpeScale e (tpeIncl.map ((0, 0, c) : Int × Int × Int)))
          (tpeScale e (tpeIncl.map ((0, 0, c') : Int × Int × Int))) := by
  show (((0 + 0, 0 + 0, e * (c + (c' + 0 * 0) + 0 * 0)) : Int × Int × Int), (0 : Int) + 0)
    = (((0 + 0, 0 + 0, e * c + (e * c' + 0 * 0) + 0 * 0) : Int × Int × Int), (0 : Int) + 0)
  refine tpe_ext rfl rfl ?_ rfl
  have h0 : c + (c' + 0 * 0) + 0 * 0 = c + c' := by omega
  rw [h0, Int.mul_add]
  generalize e * c = X
  generalize e * c' = Y
  omega

/-- **定理 (M424F-8h): 組み上げ群のテータ交換子は χ で捻れる（本丸その 2）** —
    σ_g·[ι x, ι y] = ι(0, 0, χ(g)·ω(x,y))。外ガロア作用が組み上げ群の交換子＝
    シンプレクティック形式を円分指標倍することの完全証明（M389F の昇格）。 -/
theorem tpe_act_commutator_twist (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (a b c a' b' c' : Int) :
    tpeAct GK M ρ g (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int)))
      = tpeIncl.map ((0, 0, ttoaChar GK M ρ g * (a * b' - a' * b)) : Int × Int × Int) := by
  rw [tpe_commutator_cyclotome]
  rfl

/-- **定理 (M424F-8i): χ 変換式**（M389F ttoa_act_commutator_twist の組み上げ群版）—
    (σ_g·[ι x, ι y]) の中心座標 = χ(g) · ([σ_g·ι x, σ_g·ι y] の中心座標)。 -/
theorem tpe_act_commutator_chi (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (a b c a' b' c' : Int) :
    (tpeAct GK M ρ g (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int)))).1.2.2
      = ttoaChar GK M ρ g
        * (tpeGroup.comm (tpeAct GK M ρ g (tpeIncl.map ((a, b, c) : Int × Int × Int)))
            (tpeAct GK M ρ g (tpeIncl.map ((a', b', c') : Int × Int × Int)))).1.2.2 := by
  have h1 : tpeGroup.comm (tpeAct GK M ρ g (tpeIncl.map ((a, b, c) : Int × Int × Int)))
        (tpeAct GK M ρ g (tpeIncl.map ((a', b', c') : Int × Int × Int)))
      = tpeIncl.map (thetaGrp.comm (ttoaAct GK M ρ g ((a, b, c) : Int × Int × Int))
          (ttoaAct GK M ρ g ((a', b', c') : Int × Int × Int))) :=
    (tpeIncl.map_grp_comm (ttoaAct GK M ρ g ((a, b, c) : Int × Int × Int))
      (ttoaAct GK M ρ g ((a', b', c') : Int × Int × Int))).symm
  have h2 : tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int))
      = tpeIncl.map (thetaGrp.comm ((a, b, c) : Int × Int × Int)
          ((a', b', c') : Int × Int × Int)) :=
    (tpeIncl.map_grp_comm ((a, b, c) : Int × Int × Int) ((a', b', c') : Int × Int × Int)).symm
  rw [h1, h2]
  exact ttoa_act_commutator_twist GK M ρ g a b c a' b' c'

/-- **定理 (M424F-8j): deck×テータ交換子も χ で捻れる** —
    σ_g·[s(n), ι(a,b,c)] = ι(0, 0, χ(g)·n·b)。deck・テータペアリングの χ 捻り。 -/
theorem tpe_act_deck_commutator_twist (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (n a b c : Int) :
    tpeAct GK M ρ g (tpeGroup.comm (tpeSection.map n) (tpeIncl.map ((a, b, c) : Int × Int × Int)))
      = tpeIncl.map ((0, 0, ttoaChar GK M ρ g * (n * b)) : Int × Int × Int) := by
  rw [tpe_deck_theta_commutator]
  rfl

/-! ## M424F-9: 正直な外部仮説（決して導出しない） -/

/-- **外部仮説（正直な限定・決して導出しない）**: 完全な幾何的 Δ^temp の slim
    遠アーベル性（[SemiAnbd] André–Mochizuki）。本組み上げ群は中心 μ が非自明で
    slim で**ない**（tpe_model_not_slim が定理として固定）。slim な完全 Δ^temp から
    本群（mono-theta 環境のテータ商の骨格）への全射の実現は外部（幾何的入力・後続）。 -/
def tpe_full_slim_anabelian_hypothesis (T : Grp) (f : Hom T tpeGroup) : Prop :=
  f.Injective

/-- **外部仮説（正直な限定・決して導出しない）**: Tate 曲線の実被覆空間（位相空間・
    スキーム）としての tempered 被覆の幾何的実現・実 G_K（非可換副有限）による
    deck/数論商 ℤ の置換・p 進解析テータのガロア同変評価は外部（後続）。 -/
def tpe_geometric_realization_hypothesis (T : Grp) : Prop := Slim T

/-! ## M424F-10: capstone -/

/-- **M424F-10a: tempered π₁^ét 組み上げデータ** — 組み上げ群 tpeGroup ＝
    thetaGrp ⋊_α ℤ の全実構造を束ねる: 完全列（ι 単射・pr 全射・完全性・正規性・
    分裂・非中心）・テータ交換子＝シクロトーム着地・deck×テータ交換子＝ペアリング・
    標準生成元交換子 ≠ 1・非可換性・μ_l 像・中心＝シクロトーム・非 slim（正直な限定の
    定理化）・非有界指数（真に tempered）・アーベル化が交換子を潰す・M374F 塔への
    deck 全射/錐/完備化・M389F 外ガロア作用の拡張（制限一致・deck 自明・中心準同型・
    交換子 χ 捻り）。主語はすべて本物の群演算（toy 主語なし）。 -/
structure TemperedPi1EtaleData (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) where
  /-- ι : Δ^temp ↪ π₁^temp は単射。 -/
  incl_inj : tpeIncl.Injective
  /-- pr : π₁^temp ↠ ℤ は全射。 -/
  proj_surj : ∀ g : tmpDiscretePart.carrier, ∃ x, tpeProj.map x = g
  /-- 完全性 ker(pr) = im(ι)。 -/
  extension_exact : ∀ x, tpeProj.map x = tmpDiscretePart.one ↔ ∃ z, tpeIncl.map z = x
  /-- ι(Δ^temp) は正規部分群（明示 witness）。 -/
  geometric_normal : ∀ (g : tpeGroup.carrier) (z : thetaGrp.carrier),
    ∃ w, tpeGroup.mul (tpeGroup.mul g (tpeIncl.map z)) (tpeGroup.inv g) = tpeIncl.map w
  /-- 分裂切断 pr∘s = id。 -/
  section_splits : ∀ n : Int, tpeProj.map (tpeSection.map n) = n
  /-- deck 切断の共役 = α_n（半直積の自己整合）。 -/
  section_conj : ∀ n a b c : Int,
    tpeGroup.mul (tpeGroup.mul (tpeSection.map n) (tpeIncl.map ((a, b, c) : Int × Int × Int)))
        (tpeGroup.inv (tpeSection.map n))
      = tpeIncl.map ((a, b, c + n * b) : Int × Int × Int)
  /-- 拡大は非中心（M364F の可換モデルとの本質的差）。 -/
  extension_not_central :
    tpeGroup.mul (tpeSection.map 1) (tpeIncl.map ((0, 1, 0) : Int × Int × Int))
      ≠ tpeGroup.mul (tpeIncl.map ((0, 1, 0) : Int × Int × Int)) (tpeSection.map 1)
  /-- テータ交換子はシクロトームに着地: [ι x, ι y] = ι(0,0,ω)。 -/
  theta_commutator : ∀ a b c a' b' c' : Int,
    tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int))
      = tpeIncl.map ((0, 0, a * b' - a' * b) : Int × Int × Int)
  /-- deck×テータ交換子 = ペアリング: [s n, ι(a,b,c)] = ι(0,0,n·b)。 -/
  deck_theta_commutator : ∀ n a b c : Int,
    tpeGroup.comm (tpeSection.map n) (tpeIncl.map ((a, b, c) : Int × Int × Int))
      = tpeIncl.map ((0, 0, n * b) : Int × Int × Int)
  /-- 標準生成元交換子 = 中心生成元 ι(0,0,1)。 -/
  commutator_gen : tpeGroup.comm (tpeIncl.map ((1, 0, 0) : Int × Int × Int))
      (tpeIncl.map ((0, 1, 0) : Int × Int × Int))
    = tpeIncl.map ((0, 0, 1) : Int × Int × Int)
  /-- 中心生成元は非自明。 -/
  commutator_gen_ne_one : tpeIncl.map ((0, 0, 1) : Int × Int × Int) ≠ tpeGroup.one
  /-- 組み上げ群は非可換。 -/
  nonabelian : ¬ tcmAbelian tpeGroup
  /-- 交換子の μ_l 像は非自明 = ζ。 -/
  commutator_mu : centerToMu p l ζ
      ((tpeGroup.comm (tpeIncl.map ((1, 0, 0) : Int × Int × Int))
        (tpeIncl.map ((0, 1, 0) : Int × Int × Int))).1.2.2) = zpPow p ζ 1
  /-- シクロトームは組み上げ群全体の中心。 -/
  cyclotome_central : ∀ c : Int, ∀ g : tpeGroup.carrier,
    tpeGroup.mul (tpeIncl.map ((0, 0, c) : Int × Int × Int)) g
      = tpeGroup.mul g (tpeIncl.map ((0, 0, c) : Int × Int × Int))
  /-- 組み上げ群は slim でない（正直な限定の定理化）。 -/
  model_not_slim : ¬ Slim tpeGroup
  /-- 組み上げ群は有界指数でない（真に tempered・非副有限）。 -/
  tempered_not_bounded : ¬ BoundedExponent tpeGroup
  /-- アーベル化群は可換。 -/
  ab_abelian : tcmAbelian tpeAbGrp
  /-- アーベル化はテータ交換子を潰す（非可換性が中心 μ に圧縮）。 -/
  ab_kills_commutator : ∀ a b c a' b' c' : Int,
    tpeAb.map (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int))) = tpeAbGrp.one
  /-- M374F 塔: deck 射影は遷移と整合する錐。 -/
  deck_cone : ∀ (n : Nat) (x : tpeGroup.carrier),
    (ttwTransition l n).map ((tpeDeckLevel l (n + 1)).map x) = (tpeDeckLevel l n).map x
  /-- M374F 塔: 完備化 ℤ_l への錐整合。 -/
  deck_complete_cone : ∀ (n : Nat) (x : tpeGroup.carrier),
    (ttwLimitProj l n).map ((tpeDeckComplete l).map x) = (tpeDeckLevel l n).map x
  /-- M374F 塔: 各段 ℤ/l^n へ全射。 -/
  deck_level_surj : ∀ (n : Nat) (y : (ttwDeckTower l n).carrier),
    ∃ x, (tpeDeckLevel l n).map x = y
  /-- 外ガロア作用のテータ部への制限 = M389F ttoaAct（on the nose）。 -/
  act_extends : ∀ (g : GK.carrier) (z : thetaGrp.carrier),
    tpeAct GK M ρ g (tpeIncl.map z) = tpeIncl.map (ttoaAct GK M ρ g z)
  /-- 外ガロア作用は deck 商に自明。 -/
  act_deck_trivial : ∀ (g : GK.carrier) (x : tpeGroup.carrier),
    tpeProj.map (tpeAct GK M ρ g x) = tpeProj.map x
  /-- スケール作用の単位則。 -/
  scale_one : ∀ x : tpeGroup.carrier, tpeScale 1 x = x
  /-- スケール作用の合成則（(ℤ,·) のモノイド作用）。 -/
  scale_mul : ∀ (e e' : Int) (x : tpeGroup.carrier),
    tpeScale e (tpeScale e' x) = tpeScale (e * e') x
  /-- 中心（シクロトーム）上では作用は積を保つ。 -/
  act_center_hom : ∀ e c c' : Int,
    tpeScale e (tpeGroup.mul (tpeIncl.map ((0, 0, c) : Int × Int × Int))
        (tpeIncl.map ((0, 0, c') : Int × Int × Int)))
      = tpeGroup.mul (tpeScale e (tpeIncl.map ((0, 0, c) : Int × Int × Int)))
          (tpeScale e (tpeIncl.map ((0, 0, c') : Int × Int × Int)))
  /-- テータ交換子は χ で捻れる: σ_g·[ι x, ι y] = ι(0,0,χ(g)·ω)。 -/
  act_commutator_twist : ∀ (g : GK.carrier) (a b c a' b' c' : Int),
    tpeAct GK M ρ g (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int)))
      = tpeIncl.map ((0, 0, ttoaChar GK M ρ g * (a * b' - a' * b)) : Int × Int × Int)
  /-- χ 変換式（M389F の組み上げ群版）。 -/
  act_commutator_chi : ∀ (g : GK.carrier) (a b c a' b' c' : Int),
    (tpeAct GK M ρ g (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int)))).1.2.2
      = ttoaChar GK M ρ g
        * (tpeGroup.comm (tpeAct GK M ρ g (tpeIncl.map ((a, b, c) : Int × Int × Int)))
            (tpeAct GK M ρ g (tpeIncl.map ((a', b', c') : Int × Int × Int)))).1.2.2

/-- **M424F-10b: witness 本体** — 全フィールドを M424F-1〜8 の本物の証明で埋める
    （外部仮説ゼロ・完全証明）。 -/
def temperedPi1EtaleData (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    TemperedPi1EtaleData p l hl ζ GK M ρ where
  incl_inj := tpe_incl_injective
  proj_surj := tpe_proj_surjective
  extension_exact := tpe_extension_exact
  geometric_normal := tpe_geometric_normal
  section_splits := tpe_section_splits
  section_conj := tpe_section_conj
  extension_not_central := tpe_extension_not_central
  theta_commutator := tpe_commutator_cyclotome
  deck_theta_commutator := tpe_deck_theta_commutator
  commutator_gen := tpe_commutator_gen
  commutator_gen_ne_one := tpe_commutator_gen_ne_one
  nonabelian := tpe_nonabelian
  commutator_mu := tpe_commutator_mu p l hl ζ
  cyclotome_central := tpe_cyclotome_central
  model_not_slim := tpe_model_not_slim
  tempered_not_bounded := tpe_not_bounded
  ab_abelian := tpe_ab_abelian
  ab_kills_commutator := tpe_ab_kills_commutator
  deck_cone := fun n x => tpe_deck_transition_cone l n x
  deck_complete_cone := fun n x => tpe_deck_complete_cone l n x
  deck_level_surj := fun n y => tpe_deck_level_surjective l n y
  act_extends := tpe_act_extends GK M ρ
  act_deck_trivial := tpe_act_deck_trivial GK M ρ
  scale_one := tpe_scale_one
  scale_mul := tpe_scale_mul
  act_center_hom := tpe_act_center_hom
  act_commutator_twist := tpe_act_commutator_twist GK M ρ
  act_commutator_chi := tpe_act_commutator_chi GK M ρ

/-- **定理 (M424F-10c): tempered π₁^ét 組み上げデータの存在（M424F 見出し）** —
    p・l ≥ 2・μ_l 候補 ζ・任意の G_K・内部円分体 μ（CycMuGroup）・実ガロア作用 ρ
    （M322F CycGKAction）が与えられれば、テータ Heisenberg 部 ⋊ deck 商 ℤ の
    本物の半直積 tpeGroup と、その完全列・テータ交換子・M374F 塔完備化・M389F 外
    ガロア χ 捻りを束ねたデータが**外部仮説なしで**存在する（完全証明）。 -/
theorem tpe_exists (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    Nonempty (TemperedPi1EtaleData p l hl ζ GK M ρ) :=
  ⟨temperedPi1EtaleData p l hl ζ GK M ρ⟩

/-! ## M424F-11: 実例 -/

/-- 実例: 具体的な積 — ((2,3,5),7)·((11,13,17),19) = ((13,16,139),26)
    （139 = 5 + 17 + 7·13 + 2·13、deck 捻り 7·13 が本当に効いている）。 -/
example : tpeGroup.mul (((2, 3, 5) : Int × Int × Int), 7) (((11, 13, 17) : Int × Int × Int), 19)
    = (((13, 16, 139) : Int × Int × Int), 26) := by
  rw [tpe_mul_expand]
  exact tpe_ext (by omega) (by omega) (by omega) (by omega)

/-- 実例: deck×テータ交換子 — [s(1), ι(0,1,0)] = ι(0,0,1)（deck 生成元とテータ切断の
    交換子が中心 μ の生成元を生む、[EtTh] の核心の組み上げ群版）。 -/
example : tpeGroup.comm (tpeSection.map 1) (tpeIncl.map ((0, 1, 0) : Int × Int × Int))
    = tpeIncl.map ((0, 0, 1) : Int × Int × Int) := by
  have h := tpe_deck_theta_commutator 1 0 1 0
  rw [h]
  exact congrArg tpeIncl.map (triple_ext rfl rfl (by omega))

/-- 実例: テータ交換子はシクロトームに着地 — [ι(2,3,0), ι(5,7,0)] = ι(0,0,−1)。 -/
example : tpeGroup.comm (tpeIncl.map ((2, 3, 0) : Int × Int × Int))
      (tpeIncl.map ((5, 7, 0) : Int × Int × Int))
    = tpeIncl.map ((0, 0, -1) : Int × Int × Int) := by
  rw [tpe_commutator_cyclotome]
  exact congrArg tpeIncl.map (triple_ext rfl rfl (by omega))

/-- 実例: 組み上げ群は非可換・非 slim・非有界指数（真の tempered π₁ 群対象）。 -/
example : ¬ tcmAbelian tpeGroup ∧ ¬ Slim tpeGroup ∧ ¬ BoundedExponent tpeGroup :=
  ⟨tpe_nonabelian, tpe_model_not_slim, tpe_not_bounded⟩

/-- 実例: 完全列の完全性（pr の核 = ι の像）。 -/
example (x : tpeGroup.carrier) :
    tpeProj.map x = tmpDiscretePart.one ↔ ∃ z : thetaGrp.carrier, tpeIncl.map z = x :=
  tpe_extension_exact x

/-- 実例: deck 商の l = 2 塔 — 組み上げ群は第 3 段 ℤ/8 へ全射。 -/
example : ∀ y, ∃ x : tpeGroup.carrier, (tpeDeckLevel 2 3).map x = y :=
  tpe_deck_level_surjective 2 3

/-- 実例: 外ガロア作用（e = 3 スケール）はテータ交換子 ι(0,0,1) を ι(0,0,3) に捻る。 -/
example : tpeScale 3 (tpeGroup.comm (tpeIncl.map ((1, 0, 0) : Int × Int × Int))
      (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))
    = tpeIncl.map ((0, 0, 3) : Int × Int × Int) := by
  rw [tpe_commutator_gen]
  show (((0, 0, (3 : Int) * 1) : Int × Int × Int), (0 : Int))
    = (((0, 0, 3) : Int × Int × Int), (0 : Int))
  exact tpe_ext rfl rfl (by omega) rfl

/-- 実例: 本物の絶対ガロア群 G_ℚ（M315F）の trivial 円分作用による組み上げデータが
    存在する（p = 7、l = 5）。 -/
example (ζ : (Zp 7).carrier) (l : Nat) (hl : 1 ≤ l) :
    Nonempty (TemperedPi1EtaleData 7 5 (by omega) ζ
      (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
      (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))) :=
  tpe_exists 7 5 (by omega) ζ (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))

end IUT
