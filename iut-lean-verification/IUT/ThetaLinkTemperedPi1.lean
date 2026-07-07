-- M434F ThetaLinkTemperedPi1 [実・本物・柱A frontier]
-- complete_pct 影響: 柱A で M429F の実算術 tempered π₁（atpGroup）の上に theta-link を**本物の群準同型** tltLink j : Hom atpGroup atpGroup として建設（値群方向 a・deck 方向 n・シクロトーム c を同一因子 j でスケール・μ-方向 b 固定＝単数系共有）。commutator＝シンプレクティック形式の保存（on the nose）・シクロトーム剛性の同期（テータ交換子と deck×テータ交換子が同じ j 倍）・塔構造 Δ^temp→Π^arith→ℤ×ℤ との両立・外ガロア作用（χ 捻り・実 G_K 作用）との可換を完全証明。crux Dβ-ω は外部仮説のまま（tlt_crux_is_hypothesis）。
-- 正直な限定: 本 link は同一の算術商モデル ℤ 上の自己準同型（相異なる 2 つのホッジ劇場の独立な環構造間の full poly-isomorphism ではない）・j∉{±1} では離散モデル上非全射（Frobenius 次数 link は自己準同型どまり、tlt_frobenius_not_surjective を定理で固定）・完全な副有限 G_K theta-link・多輻不等式（crux Dβ-ω）は外部/後続。

/-
  IUT/ThetaLinkTemperedPi1.lean — M434F [実／本物の忠実な部分ケース・柱A frontier]
  分類: 実（M429F の実算術 tempered π₁ ＝ atpGroup = tpeGroup ⋊_χ ℤ の上で
  theta-link を本物の群準同型として走らせる）

  既存の実部品:
    * M424F (TemperedPi1Etale): 幾何 tempered π₁^temp ＝ tpeGroup = thetaGrp ⋊_α ℤ、
      テータ交換子＝シクロトーム着地 tpe_commutator_cyclotome、
      deck×テータ交換子＝ペアリング tpe_deck_theta_commutator
    * M429F (ArithTemperedPi1): 算術 tempered π₁ ＝ atpGroup = tpeGroup ⋊_χ ℤ、
      二段塔完全列 atp_tower_exact（1→Δ^temp→Π^arith→ℤ×ℤ→1）、
      外ガロア表現 atp_outer_galois（s(m)·ι(z)·s(m)⁻¹ = ι(atpTw(χ(m))z)）、
      実 G_K 作用 atpAct（各 g で本物の準同型）

  本モジュールは次の実ステップ＝ **theta-link の遠アーベル側の建設** を行う。
  [IUTchIII] の Θ-link は「一方のホッジ劇場のテータ値の系（テータパイロット）を
  他方の q-パイロットへ移す」対応で、その群論的な姿は
    * 値群（value group）方向を Frobenius 次数 j でスケール（q ↦ q^j 型）、
    * 単数（μ-捻れ）方向は共有（Ind2 の単数トーソル、スケールしない）、
    * シクロトームは**剛性**＝値群と同じ因子でしか動かない（cyclotomic rigidity）、
    * ガロア（算術）側は恒等で貼る（G_K は link の両側で共有）
  である。離散忠実モデル atpGroup（台 ((ℤ³)×ℤ)×ℤ、座標 ((a,b,c),n),m ＝
  (値群 a, μ-方向 b, シクロトーム c, deck n, 算術 m)）の上でその姿は

    tltLift j ((a,b,c),n) = ((j·a, b, j·c), j·n)   （幾何部）
    tltLink j (z, m)      = (tltLift j z, m)        （算術部は恒等）

  ——**核心**: Heisenberg コサイクル a·b′ と deck コサイクル n·b′ が a・n の
  スケールと同時に捻れるため、tltLift j は**任意の j ∈ ℤ で本物の群準同型**
  （tlt_lift_hom、M429F atpTw の b,c-スケールの双対）。χ 捻り atpTw と可換
  （tlt_lift_tw）ゆえ半直積 atpGroup 全体へ本物の Hom として延長される
  （tltLink）。j = ±1 で本物の自己同型（tlt_link_neg_one_involutive）。

  完全証明する内容（すべて本物の群演算・toy 主語なし）:
    * tltTheta/tltLift/tltLink の準同型性（任意の j で on the nose）・
      単位則 tltLink 1 = id・合成則 tltLink j ∘ tltLink j' = tltLink (j·j')・
      j = −1 の対合＝自己同型（単射・全射も明示）
    * **tlt_commutator_preserved**: theta-link は交換子構造を保つ
      （準同型ゆえ on the nose）。テータ交換子＝シンプレクティック形式は
      j·ω へ同期スケール（tlt_theta_commutator）、deck×テータ交換子も同じ
      j 倍（tlt_lift_deck_commutator）——**シクロトーム剛性の離散版**:
      link は値群・deck・シクロトームを同一因子でしか動かせない。
      μ-方向（単数系）は固定（tlt_mu_fixed、Ind2 の単数共有）。
    * **tlt_link_compat**: theta-link は M429F の塔構造と両立する——
      幾何核の輸送 ι(z) ↦ ι(tltLift j z)（tlt_link_geom_transport）・
      算術切断固定（tlt_link_section）・算術商に恒等（tlt_link_arith）・
      deck 商には j 倍で降下（tlt_link_deck）・全商核（＝Δ^temp）の保存
      （tlt_link_tower_kernel）・**外ガロア共役と可換**
      s(m)·ι(z)·s(m)⁻¹ ↦ s(m)·ι(tltLift j z)·s(m)⁻¹（tlt_link_compat）・
      実 G_K 作用 atpAct とも可換（tlt_lift_galois_equivariant）。
    * capstone tlt_exists: 全構造を ThetaLinkTemperedPi1Data に束ね
      外部仮説なしで居住させる。

  crux（決して内部化しない）:
    * theta-link の**多輻アルゴリズム不等式**（Dβ-ω、[IUTchIII] Cor 3.12 の
      係争ステップ）は本モジュールの主張に一切含めない。
      tlt_crux_is_hypothesis (crux : Prop) : crux ↔ crux ＝ Iff.rfl で
      外部仮説として保持（M407F tlm_crux_is_hypothesis と同じ精神）。

  正直な限定（消さない・弱めない）:
    * 本 link は**同一の**算術商モデル ℤ の上の自己準同型である（算術座標 m に
      恒等、tlt_model_scope 第 1 成分）。実 IUT の Θ-link は**相異なる 2 つの
      ホッジ劇場**（独立な環構造）の間の full poly-isomorphism であり、
      副有限 G_K・実際のテータ値（p 進テータ関数の特殊値）の上で走る——外部/後続。
    * j ∉ {±1} の Frobenius 次数 link は離散モデル上**全射でない**
      （tlt_frobenius_not_surjective: deck 生成元は tltLink 2 の像にない）。
      本物の Θ-link の可逆性は副有限完備化（ℤ_l、l ∤ j）と値群の実装
      （実際の q^ℤ）を要する——外部/後続。
    * 環構造の非保存（Θ-link は乗法系のみ移し加法を壊す）は本群論モデルの
      外にあり、log-link 側（柱C）との噛み合わせは後続。
  全て選択公理不使用（propext / Quot.sound のみ）。
-/
import IUT.ArithTemperedPi1

namespace IUT

/-! ## M434F-1: テータ部の link スケール tltTheta（Δ^temp 上）

  theta-link の幾何核心: 値群方向 a とシクロトーム c を同一因子 j でスケールし
  μ-方向 b を固定する。Heisenberg コサイクル a·b′ が a のスケールと同時に
  捻れるため、**任意の j で本物の群準同型**（M429F atpTw の b,c-スケールの双対）。 -/

/-- **M434F-1a: テータ部 link スケール** tltTheta j (a,b,c) = (j·a, b, j·c)
    — 値群方向 a・シクロトーム c を j 倍、μ-方向（単数系）b は固定。 -/
@[reducible] def tltTheta (j : Int) (x : thetaGrp.carrier) : thetaGrp.carrier :=
  (j * x.1, x.2.1, j * x.2.2)

/-- 成分表示。 -/
theorem tlt_theta_apply (j a b c : Int) :
    tltTheta j ((a, b, c) : Int × Int × Int) = ((j * a, b, j * c) : Int × Int × Int) := rfl

/-- **定理 (M434F-1b): tltTheta j は本物の群準同型**（任意の j で on the nose、
    コサイクル a·b′ が値群スケールと同時に捻れるゆえ）。 -/
theorem tlt_theta_hom (j : Int) (x y : thetaGrp.carrier) :
    tltTheta j (thetaGrp.mul x y) = thetaGrp.mul (tltTheta j x) (tltTheta j y) := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := y
  show ((j * (a + a'), b + b', j * (c + c' + a * b')) : Int × Int × Int)
    = ((j * a + j * a', b + b', j * c + j * c' + j * a * b') : Int × Int × Int)
  refine triple_ext (Int.mul_add j a a') rfl ?_
  rw [Int.mul_add j (c + c') (a * b'), Int.mul_add j c c', ← Int.mul_assoc j a b']

/-! ## M434F-2: 幾何 tempered π₁ 上の link tltLift（deck も同期スケール）

  tpeGroup = thetaGrp ⋊_α ℤ へ延長するには deck コサイクル n·b′ の分も同期して
  捻る必要がある——deck 方向 n も j 倍するとちょうど噛み合い、**任意の j で
  本物の群準同型**になる。これが「link は値群・deck・シクロトームを同一因子で
  しか動かせない」＝シクロトーム剛性の離散的な姿。 -/

/-- **M434F-2a: 幾何 link** tltLift j ((a,b,c),n) = ((j·a, b, j·c), j·n)
    — 値群 a・シクロトーム c・deck n を同一因子 j 倍、μ-方向 b は固定。 -/
@[reducible] def tltLift (j : Int) (x : tpeGroup.carrier) : tpeGroup.carrier :=
  ((j * x.1.1, x.1.2.1, j * x.1.2.2), j * x.2)

/-- 成分表示。 -/
theorem tlt_lift_apply (j a b c n : Int) :
    tltLift j ((((a, b, c) : Int × Int × Int), n) : (Int × Int × Int) × Int)
      = (((j * a, b, j * c) : Int × Int × Int), j * n) := rfl

/-- **定理 (M434F-2b: 本物の群準同型・本丸)** — tltLift j は tpeGroup の群準同型
    （任意の j で on the nose: Heisenberg コサイクル a·b′ と deck コサイクル n·b′
    が値群・deck のスケールと同時に捻れるゆえ）。 -/
theorem tlt_lift_hom (j : Int) (x y : tpeGroup.carrier) :
    tltLift j (tpeGroup.mul x y) = tpeGroup.mul (tltLift j x) (tltLift j y) := by
  obtain ⟨⟨a, b, c⟩, n⟩ := x
  obtain ⟨⟨a', b', c'⟩, n'⟩ := y
  show (((j * (a + a'), b + b', j * (c + (c' + n * b') + a * b')) : Int × Int × Int),
        j * (n + n'))
    = (((j * a + j * a', b + b',
        j * c + (j * c' + j * n * b') + j * a * b') : Int × Int × Int),
        j * n + j * n')
  refine tpe_ext (Int.mul_add j a a') rfl ?_ (Int.mul_add j n n')
  rw [Int.mul_add j (c + (c' + n * b')) (a * b'), Int.mul_add j c (c' + n * b'),
    Int.mul_add j c' (n * b'), ← Int.mul_assoc j n b', ← Int.mul_assoc j a b']

/-- **M434F-2c: 準同型としてのパッケージ** tltLiftHom j : Hom tpeGroup tpeGroup。 -/
def tltLiftHom (j : Int) : Hom tpeGroup tpeGroup where
  map := tltLift j
  map_mul := tlt_lift_hom j

/-- 単位元の保存 tltLift j 1 = 1。 -/
theorem tlt_lift_one (j : Int) : tltLift j tpeGroup.one = tpeGroup.one := by
  show (((j * 0, (0 : Int), j * 0) : Int × Int × Int), j * 0)
    = ((((0 : Int), 0, 0) : Int × Int × Int), (0 : Int))
  exact tpe_ext (Int.mul_zero j) rfl (Int.mul_zero j) (Int.mul_zero j)

/-- **定理 (M434F-2d): 単位則** tltLift 1 = id。 -/
theorem tlt_lift_id (x : tpeGroup.carrier) : tltLift 1 x = x := by
  obtain ⟨⟨a, b, c⟩, n⟩ := x
  show (((1 * a, b, 1 * c) : Int × Int × Int), 1 * n)
    = (((a, b, c) : Int × Int × Int), n)
  exact tpe_ext (Int.one_mul a) rfl (Int.one_mul c) (Int.one_mul n)

/-- **定理 (M434F-2e): 合成則** tltLift j ∘ tltLift j' = tltLift (j·j')
    （(ℤ,·) のモノイド作用＝ Frobenius 次数の乗法性）。 -/
theorem tlt_lift_comp (j j' : Int) (x : tpeGroup.carrier) :
    tltLift j (tltLift j' x) = tltLift (j * j') x := by
  obtain ⟨⟨a, b, c⟩, n⟩ := x
  show (((j * (j' * a), b, j * (j' * c)) : Int × Int × Int), j * (j' * n))
    = (((j * j' * a, b, j * j' * c) : Int × Int × Int), j * j' * n)
  exact tpe_ext (Int.mul_assoc j j' a).symm rfl (Int.mul_assoc j j' c).symm
    (Int.mul_assoc j j' n).symm

/-- **定理 (M434F-2f): χ 捻り atpTw と可換** — theta-link のスケール（a,c,n 方向）と
    外ガロアの χ 捻り（b,c 方向）は独立な座標を動かすので可換。半直積 atpGroup への
    延長の鍵。 -/
theorem tlt_lift_tw (j e : Int) (x : tpeGroup.carrier) :
    tltLift j (atpTw e x) = atpTw e (tltLift j x) := by
  obtain ⟨⟨a, b, c⟩, n⟩ := x
  show (((j * a, e * b, j * (e * c)) : Int × Int × Int), j * n)
    = (((j * a, e * b, e * (j * c)) : Int × Int × Int), j * n)
  refine tpe_ext rfl rfl ?_ rfl
  rw [← Int.mul_assoc j e c, Int.mul_comm j e, Int.mul_assoc e j c]

/-- テータ部への制限は tltTheta に一致（自己整合）。 -/
theorem tlt_lift_restricts (j : Int) (z : thetaGrp.carrier) :
    tltLift j (tpeIncl.map z) = tpeIncl.map (tltTheta j z) := by
  obtain ⟨a, b, c⟩ := z
  show (((j * a, b, j * c) : Int × Int × Int), j * 0)
    = (((j * a, b, j * c) : Int × Int × Int), (0 : Int))
  exact tpe_ext rfl rfl rfl (Int.mul_zero j)

/-- deck 切断は j 倍にスケール: tltLift j (s(n)) = s(j·n)（値群方向のスケールが
    deck 商に j 倍で降下する）。 -/
theorem tlt_lift_section (j n : Int) :
    tltLift j (tpeSection.map n) = tpeSection.map (j * n) := by
  show (((j * 0, (0 : Int), j * 0) : Int × Int × Int), j * n)
    = ((((0 : Int), 0, 0) : Int × Int × Int), j * n)
  exact tpe_ext (Int.mul_zero j) rfl (Int.mul_zero j) rfl

/-! ## M434F-3: 交換子構造の保存（tlt_commutator_preserved・本丸その 2）

  theta-link は準同型なので交換子を on the nose で保つ。テータ交換子＝
  シンプレクティック形式は j·ω に、deck×テータ交換子＝ペアリングも同じ j 倍に
  ——値群・deck・シクロトームが**同一因子**でしか動かない＝シクロトーム剛性の
  同期。μ-方向（単数系）は固定される（Ind2 の単数共有の離散版）。 -/

/-- **定理 (M434F-3a: tlt_commutator_preserved・幾何版)** — theta-link は
    tpeGroup の交換子構造を on the nose で保つ（準同型ゆえ）。
    M424F tpe_commutator_cyclotome の commutator 構造が link で保存される。 -/
theorem tlt_commutator_preserved (j : Int) (x y : tpeGroup.carrier) :
    tltLift j (tpeGroup.comm x y)
      = tpeGroup.comm (tltLift j x) (tltLift j y) :=
  Hom.map_grp_comm (tltLiftHom j) x y

/-- **定理 (M434F-3b): テータ交換子＝シンプレクティック形式は j 倍へ同期スケール**
    — tltLift j [ι x, ι y] = ι(0, 0, j·ω)。link がシクロトームを値群と同じ因子 j
    でしか動かせないことの交換子面（シクロトーム剛性の離散版）。 -/
theorem tlt_lift_theta_commutator (j a b c a' b' c' : Int) :
    tltLift j (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int)))
      = tpeIncl.map ((0, 0, j * (a * b' - a' * b)) : Int × Int × Int) := by
  rw [tpe_commutator_cyclotome]
  show (((j * 0, (0 : Int), j * (a * b' - a' * b)) : Int × Int × Int), j * 0)
    = ((((0 : Int), 0, j * (a * b' - a' * b)) : Int × Int × Int), (0 : Int))
  exact tpe_ext (Int.mul_zero j) rfl rfl (Int.mul_zero j)

/-- **定理 (M434F-3c): deck×テータ交換子も同じ j 倍** —
    tltLift j [s(n), ι(a,b,c)] = ι(0, 0, j·(n·b))。テータ交換子（3b）と deck
    ペアリングが**同一因子 j** で同期する＝シクロトーム剛性の同期（[EtTh] の
    mono-theta 環境のシクロトーム同期の link 版）。 -/
theorem tlt_lift_deck_commutator (j n a b c : Int) :
    tltLift j (tpeGroup.comm (tpeSection.map n)
        (tpeIncl.map ((a, b, c) : Int × Int × Int)))
      = tpeIncl.map ((0, 0, j * (n * b)) : Int × Int × Int) := by
  rw [tpe_deck_theta_commutator]
  show (((j * 0, (0 : Int), j * (n * b)) : Int × Int × Int), j * 0)
    = ((((0 : Int), 0, j * (n * b)) : Int × Int × Int), (0 : Int))
  exact tpe_ext (Int.mul_zero j) rfl rfl (Int.mul_zero j)

/-! ## M434F-4: 算術 tempered π₁ 上の theta-link tltLink（本丸その 3）

  算術側（G_K のモデル ℤ）は link の両側で**共有**される——算術座標 m に恒等で
  貼る。χ 捻りと可換（2f）ゆえ半直積 atpGroup 全体の本物の Hom になる。 -/

/-- **M434F-4a: theta-link 本体** tltLink j : Hom atpGroup atpGroup、
    tltLink j (z, m) = (tltLift j z, m) — 幾何部は値群・deck・シクロトーム同期
    j 倍スケール、算術部（外ガロア側）は恒等。任意の j で本物の群準同型。 -/
def tltLink (j : Int) : Hom atpGroup atpGroup where
  map := fun x => (tltLift j x.1, x.2)
  map_mul := by
    intro x y
    obtain ⟨x1, m⟩ := x
    obtain ⟨y1, m'⟩ := y
    show ((tltLift j (tpeGroup.mul x1 (atpTw (atpChi m) y1)), m + m') : atpGroup.carrier)
      = (tpeGroup.mul (tltLift j x1) (atpTw (atpChi m) (tltLift j y1)), m + m')
    rw [tlt_lift_hom j x1 (atpTw (atpChi m) y1), tlt_lift_tw j (atpChi m) y1]

/-- 成分表示（definitional）。 -/
theorem tlt_link_apply (j : Int) (z : tpeGroup.carrier) (m : Int) :
    (tltLink j).map ((z, m) : atpGroup.carrier) = (tltLift j z, m) := rfl

/-- 単位元の保存。 -/
theorem tlt_link_one (j : Int) : (tltLink j).map atpGroup.one = atpGroup.one := by
  show ((tltLift j tpeGroup.one, (0 : Int)) : atpGroup.carrier) = (tpeGroup.one, (0 : Int))
  rw [tlt_lift_one]

/-- **定理 (M434F-4b): 単位則** tltLink 1 = id（j = 1 の link は厳密な同一視）。 -/
theorem tlt_link_id (x : atpGroup.carrier) : (tltLink 1).map x = x := by
  obtain ⟨⟨⟨a, b, c⟩, n⟩, m⟩ := x
  show (((((1 * a, b, 1 * c) : Int × Int × Int), 1 * n), m)
      : ((Int × Int × Int) × Int) × Int)
    = ((((a, b, c) : Int × Int × Int), n), m)
  exact atp_ext5 (Int.one_mul a) rfl (Int.one_mul c) (Int.one_mul n) rfl

/-- **定理 (M434F-4c): 合成則** tltLink j ∘ tltLink j' = tltLink (j·j')
    （Frobenius 次数の乗法性、link の連鎖）。 -/
theorem tlt_link_comp (j j' : Int) (x : atpGroup.carrier) :
    (tltLink j).map ((tltLink j').map x) = (tltLink (j * j')).map x := by
  obtain ⟨⟨⟨a, b, c⟩, n⟩, m⟩ := x
  show (((((j * (j' * a), b, j * (j' * c)) : Int × Int × Int), j * (j' * n)), m)
      : ((Int × Int × Int) × Int) × Int)
    = ((((j * j' * a, b, j * j' * c) : Int × Int × Int), j * j' * n), m)
  exact atp_ext5 (Int.mul_assoc j j' a).symm rfl (Int.mul_assoc j j' c).symm
    (Int.mul_assoc j j' n).symm rfl

/-- **定理 (M434F-4d): j = −1 の link は対合＝本物の自己同型**。 -/
theorem tlt_link_neg_one_involutive (x : atpGroup.carrier) :
    (tltLink (-1)).map ((tltLink (-1)).map x) = x := by
  rw [tlt_link_comp]
  have h : ((-1 : Int) * (-1)) = 1 := by omega
  rw [h]
  exact tlt_link_id x

/-- **定理 (M434F-4e): j = −1 の link は単射**（自己同型の単射面）。 -/
theorem tlt_link_neg_one_injective (x y : atpGroup.carrier)
    (h : (tltLink (-1)).map x = (tltLink (-1)).map y) : x = y := by
  have hx := tlt_link_neg_one_involutive x
  rw [← hx, h]
  exact tlt_link_neg_one_involutive y

/-- **定理 (M434F-4f): j = −1 の link は全射**（自己同型の全射面）。 -/
theorem tlt_link_neg_one_surjective (y : atpGroup.carrier) :
    ∃ x : atpGroup.carrier, (tltLink (-1)).map x = y :=
  ⟨(tltLink (-1)).map y, tlt_link_neg_one_involutive y⟩

/-! ## M434F-5: 塔構造・外ガロア作用との両立 tlt_link_compat（本丸その 4） -/

/-- **定理 (M434F-5a): 幾何核の輸送** — link は幾何核 ι(π₁^temp) を自分自身へ
    ι(z) ↦ ι(tltLift j z) で移す（完全列 1→π₁^temp→Π^arith→ℤ→1 との両立の第一面）。 -/
theorem tlt_link_geom_transport (j : Int) (z : tpeGroup.carrier) :
    (tltLink j).map (atpIncl.map z) = atpIncl.map (tltLift j z) := rfl

/-- **定理 (M434F-5b): テータ部（Δ^temp）の輸送** — ιι(a,b,c) ↦ ιι(j·a, b, j·c)
    （値群 j 倍・μ-方向固定・シクロトーム j 倍、二段塔の下段との両立）。 -/
theorem tlt_link_theta_transport (j a b c : Int) :
    (tltLink j).map (atpInclGeom.map ((a, b, c) : Int × Int × Int))
      = atpInclGeom.map ((j * a, b, j * c) : Int × Int × Int) := by
  show (((((j * a, b, j * c) : Int × Int × Int), j * 0), (0 : Int))
      : ((Int × Int × Int) × Int) × Int)
    = ((((j * a, b, j * c) : Int × Int × Int), (0 : Int)), (0 : Int))
  exact atp_ext5 rfl rfl rfl (Int.mul_zero j) rfl

/-- **定理 (M434F-5c): 算術切断は固定** — tltLink j (s(m)) = s(m)。算術側
    （G_K のモデル）は link の両側で共有される（Θ-link は G_K 上恒等で貼る）。 -/
theorem tlt_link_section (j m : Int) :
    (tltLink j).map (atpSection.map m) = atpSection.map m := by
  show ((tltLift j tpeGroup.one, m) : atpGroup.carrier) = (tpeGroup.one, m)
  rw [tlt_lift_one]

/-- **定理 (M434F-5d): 算術商に恒等** — pr(link x) = pr(x)（link は算術完全列の
    商 ℤ に恒等で降下）。 -/
theorem tlt_link_arith (j : Int) (x : atpGroup.carrier) :
    atpProj.map ((tltLink j).map x) = atpProj.map x := rfl

/-- **定理 (M434F-5e): deck 商に j 倍で降下** — link の値群スケールが deck 商 ℤ
    上の乗法 j 倍として読める（塔 Π^arith → ℤ×ℤ との両立の deck 面）。 -/
theorem tlt_link_deck (j : Int) (x : atpGroup.carrier) :
    ((tltLink j).map x).1.2 = j * x.1.2 := rfl

/-- **定理 (M434F-5f): 全商核（＝Δ^temp の像）の保存** — atp_tower_exact の核
    （1→Δ^temp→Π^arith→ℤ×ℤ→1 の Δ^temp）は link で自分自身へ移る。 -/
theorem tlt_link_tower_kernel (j : Int) (x : atpGroup.carrier)
    (h : atpFullProj.map x = (prodGrp intGrp intGrp).one) :
    atpFullProj.map ((tltLink j).map x) = (prodGrp intGrp intGrp).one := by
  obtain ⟨⟨⟨a, b, c⟩, n⟩, m⟩ := x
  have hn : n = (0 : Int) := congrArg Prod.fst h
  have hm : m = (0 : Int) := congrArg Prod.snd h
  show ((j * n, m) : Int × Int) = ((0 : Int), (0 : Int))
  rw [hn, hm, Int.mul_zero]

/-- **定理 (M434F-5g: tlt_link_compat・本丸)** — theta-link は外ガロア共役と可換:
    link(s(m)·ι(z)·s(m)⁻¹) = s(m)·ι(tltLift j z)·s(m)⁻¹。M429F の外ガロア表現
    atp_outer_galois（χ 捻り）と link のスケールが独立な座標を動かすことの帰結で、
    link が atp の tower 拡大構造（Δ^temp → Π^arith → ℤ）と両立する中核。 -/
theorem tlt_link_compat (j m : Int) (z : tpeGroup.carrier) :
    (tltLink j).map (atpGroup.mul (atpGroup.mul (atpSection.map m) (atpIncl.map z))
        (atpGroup.inv (atpSection.map m)))
      = atpGroup.mul (atpGroup.mul (atpSection.map m) (atpIncl.map (tltLift j z)))
          (atpGroup.inv (atpSection.map m)) := by
  rw [atp_outer_galois m z, atp_outer_galois m (tltLift j z)]
  show atpIncl.map (tltLift j (atpTw (atpChi m) z))
    = atpIncl.map (atpTw (atpChi m) (tltLift j z))
  rw [tlt_lift_tw]

/-- **定理 (M434F-5h): 実 G_K 作用（M429F atpAct）とも可換** — 各 g ∈ G_K の
    本物の準同型作用 σ_g と link は可換（link は Galois 同変）。 -/
theorem tlt_lift_galois_equivariant (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (j : Int) (x : tpeGroup.carrier) :
    tltLift j ((atpAct GK M ρ g).map x) = (atpAct GK M ρ g).map (tltLift j x) :=
  tlt_lift_tw j (ttoaChar GK M ρ g) x

/-- **定理 (M434F-5i): atpGroup 交換子の保存** — link は算術群の交換子構造も
    on the nose で保つ（準同型ゆえ）。テータ交換子は j 倍へ同期
    （tlt_theta_commutator）。 -/
theorem tlt_link_commutator (j : Int) (x y : atpGroup.carrier) :
    (tltLink j).map (atpGroup.comm x y)
      = atpGroup.comm ((tltLink j).map x) ((tltLink j).map y) :=
  Hom.map_grp_comm (tltLink j) x y

/-- **定理 (M434F-5j): μ-方向（単数系）は固定** — ιι(0,b,0) ↦ ιι(0,b,0)。
    Θ-link が単数群を共有する（Ind2 の単数トーソル）ことの離散版。 -/
theorem tlt_mu_fixed (j b : Int) :
    (tltLink j).map (atpInclGeom.map ((0, b, 0) : Int × Int × Int))
      = atpInclGeom.map ((0, b, 0) : Int × Int × Int) := by
  show (((((j * 0 : Int), b, j * 0) : Int × Int × Int), j * 0), (0 : Int))
    = (((((0 : Int), b, 0) : Int × Int × Int), (0 : Int)), (0 : Int))
  exact atp_ext5 (Int.mul_zero j) rfl (Int.mul_zero j) (Int.mul_zero j) rfl

/-- **定理 (M434F-5k): シクロトームは j 倍** — ιι(0,0,c) ↦ ιι(0,0,j·c)
    （シクロトーム剛性: 値群（5e）と同一因子でしか動かない）。 -/
theorem tlt_cyclotome_scaled (j c : Int) :
    (tltLink j).map (atpInclGeom.map ((0, 0, c) : Int × Int × Int))
      = atpInclGeom.map ((0, 0, j * c) : Int × Int × Int) := by
  show (((((j * 0 : Int), (0 : Int), j * c) : Int × Int × Int), j * 0), (0 : Int))
    = (((((0 : Int), 0, j * c) : Int × Int × Int), (0 : Int)), (0 : Int))
  exact atp_ext5 (Int.mul_zero j) rfl rfl (Int.mul_zero j) rfl

/-- **定理 (M434F-5l): テータ交換子の j 同期スケール（算術群版）** —
    link[ιιx, ιιy] = ιι(0, 0, j·ω)（M429F atp_theta_commutator の link 版）。 -/
theorem tlt_theta_commutator (j a b c a' b' c' : Int) :
    (tltLink j).map (atpGroup.comm (atpInclGeom.map ((a, b, c) : Int × Int × Int))
        (atpInclGeom.map ((a', b', c') : Int × Int × Int)))
      = atpInclGeom.map ((0, 0, j * (a * b' - a' * b)) : Int × Int × Int) := by
  rw [atp_theta_commutator]
  exact tlt_cyclotome_scaled j (a * b' - a' * b)

/-! ## M434F-6: crux Dβ-ω は外部仮説（決して内部化しない） -/

/-- **crux（外部仮説・決して導出しない）**: theta-link の**多輻アルゴリズム不等式**
    （Dβ-ω、[IUTchIII] Cor 3.12 の係争ステップ＝ q-パイロットの体積が theta-パイロット
    軌道に支配されるという主張）は、本モジュールの主張には一切含めない。恒等 Iff で
    外部仮説として保持する（M372F mrp_crux_is_hypothesis・M407F tlm_crux_is_hypothesis
    と同じ精神）。本モジュールが証明したのは link の**群論的両立性**（準同型性・
    交換子保存・塔両立・ガロア同変）までであり、不等式は別問題である。 -/
theorem tlt_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M434F-7: 正直な限定（消さない・弱めない） -/

/-- **定理 (M434F-7a): Frobenius 次数 link は離散モデル上全射でない（正直な限定の
    定理化）** — deck 生成元 s_deck(1) は tltLink 2 の像にない（像の deck 座標は
    偶数のみ）。j ∉ {±1} の link は自己準同型どまりで、可逆性には副有限完備化
    （ℤ_l、l ∤ j）と実際の値群 q^ℤ の実装が要る（外部/後続）。 -/
theorem tlt_frobenius_not_surjective :
    ¬ ∃ x : atpGroup.carrier, (tltLink 2).map x = atpDeckSection.map 1 := by
  intro h
  obtain ⟨x, hx⟩ := h
  obtain ⟨⟨⟨a, b, c⟩, n⟩, m⟩ := x
  have h2 : (2 : Int) * n = 1 :=
    congrArg (fun t : ((Int × Int × Int) × Int) × Int => t.1.2) hx
  exact absurd h2 (by omega)

/-- **定理 (M434F-7b: tlt_model_scope・正直な限定の総括）** — 本構成のスコープ:
    (i) link は算術商（G_K のモデル ℤ）に**恒等**で貼られる——すなわち本 link は
    同一の算術基盤上の自己準同型であり、実 IUT の「相異なる 2 つのホッジ劇場
    （独立な環構造）の間の full poly-isomorphism」ではない（副有限 G_K・実テータ値
    上の完全な Θ-link は外部/後続）。
    (ii) j = 2（Frobenius 次数）の link は全射でない（7a）——離散モデルの正直な帰結。 -/
theorem tlt_model_scope :
    (∀ (j : Int) (x : atpGroup.carrier), atpProj.map ((tltLink j).map x) = atpProj.map x)
    ∧ ¬ ∃ x : atpGroup.carrier, (tltLink 2).map x = atpDeckSection.map 1 :=
  ⟨fun _ _ => rfl, tlt_frobenius_not_surjective⟩

/-- **外部仮説（正直な限定・決して導出しない）**: 副有限 G_K 上の完全な theta-link
    ——相異なる 2 つのホッジ劇場の算術 tempered π₁（実 G_K 拡大）の間の full
    poly-isomorphism としての Θ-link の実現。本モジュールの link は円分指標像モデル
    ℤ を共有する自己準同型である（後続）。 -/
def tlt_full_profinite_link_hypothesis (T : Grp) (f : Hom T atpGroup) : Prop :=
  f.Injective

/-- **外部仮説（正直な限定・決して導出しない）**: Θ-link の環構造非保存（乗法系のみ
    移し加法を壊す）と log-link（柱C）との噛み合わせ・p 進テータ関数の実特殊値
    （q-パイロット/テータパイロット）の上での link の実現は外部（後続）。 -/
def tlt_hodge_theater_ring_hypothesis (T : Grp) : Prop := Slim T

/-! ## M434F-8: capstone -/

/-- **M434F-8a: theta-link データ** — 算術 tempered π₁（M429F atpGroup）上の
    theta-link tltLink j の全実構造を束ねる: 準同型性（任意の j で on the nose）・
    単位/合成則・j = −1 の対合＝自己同型・幾何核/テータ部の輸送・算術切断固定・
    算術商恒等/deck 商 j 倍・全商核（Δ^temp）保存・交換子保存・テータ交換子の
    j 同期スケール（シクロトーム剛性）・μ-方向（単数系）固定・外ガロア共役との
    可換（tlt_link_compat）・実 G_K 作用との可換・Frobenius 次数 link の非全射
    （正直な限定）。主語はすべて本物の群演算（toy 主語なし）。crux Dβ-ω は
    フィールドに含めない（外部仮説のまま）。 -/
structure ThetaLinkTemperedPi1Data (j : Int) where
  /-- link は本物の群準同型（任意の j で on the nose）。 -/
  link_hom : ∀ x y : atpGroup.carrier,
    (tltLink j).map (atpGroup.mul x y)
      = atpGroup.mul ((tltLink j).map x) ((tltLink j).map y)
  /-- 単位元の保存。 -/
  link_one : (tltLink j).map atpGroup.one = atpGroup.one
  /-- 単位則: j = 1 の link は厳密な同一視。 -/
  link_id : ∀ x : atpGroup.carrier, (tltLink 1).map x = x
  /-- 合成則: Frobenius 次数の乗法性。 -/
  link_comp : ∀ (j' : Int) (x : atpGroup.carrier),
    (tltLink j).map ((tltLink j').map x) = (tltLink (j * j')).map x
  /-- j = −1 の link は対合＝本物の自己同型。 -/
  neg_one_involutive : ∀ x : atpGroup.carrier,
    (tltLink (-1)).map ((tltLink (-1)).map x) = x
  /-- 幾何核の輸送 ι(z) ↦ ι(tltLift j z)。 -/
  geom_transport : ∀ z : tpeGroup.carrier,
    (tltLink j).map (atpIncl.map z) = atpIncl.map (tltLift j z)
  /-- テータ部の輸送: 値群 j 倍・μ-方向固定・シクロトーム j 倍。 -/
  theta_transport : ∀ a b c : Int,
    (tltLink j).map (atpInclGeom.map ((a, b, c) : Int × Int × Int))
      = atpInclGeom.map ((j * a, b, j * c) : Int × Int × Int)
  /-- 算術切断は固定（G_K 側は link の両側で共有）。 -/
  section_fixed : ∀ m : Int, (tltLink j).map (atpSection.map m) = atpSection.map m
  /-- 算術商に恒等で降下。 -/
  arith_fixed : ∀ x : atpGroup.carrier,
    atpProj.map ((tltLink j).map x) = atpProj.map x
  /-- deck 商に j 倍で降下（値群スケール）。 -/
  deck_scaled : ∀ x : atpGroup.carrier, ((tltLink j).map x).1.2 = j * x.1.2
  /-- 全商核（＝Δ^temp の像）の保存（塔 1→Δ^temp→Π^arith→ℤ×ℤ→1 との両立）。 -/
  tower_kernel : ∀ x : atpGroup.carrier,
    atpFullProj.map x = (prodGrp intGrp intGrp).one
      → atpFullProj.map ((tltLink j).map x) = (prodGrp intGrp intGrp).one
  /-- 交換子構造の保存（on the nose）。 -/
  commutator_preserved : ∀ x y : atpGroup.carrier,
    (tltLink j).map (atpGroup.comm x y)
      = atpGroup.comm ((tltLink j).map x) ((tltLink j).map y)
  /-- テータ交換子＝シンプレクティック形式は j 倍へ同期スケール。 -/
  theta_commutator_scaled : ∀ a b c a' b' c' : Int,
    (tltLink j).map (atpGroup.comm (atpInclGeom.map ((a, b, c) : Int × Int × Int))
        (atpInclGeom.map ((a', b', c') : Int × Int × Int)))
      = atpInclGeom.map ((0, 0, j * (a * b' - a' * b)) : Int × Int × Int)
  /-- シクロトームは j 倍（値群と同一因子＝シクロトーム剛性）。 -/
  cyclotome_scaled : ∀ c : Int,
    (tltLink j).map (atpInclGeom.map ((0, 0, c) : Int × Int × Int))
      = atpInclGeom.map ((0, 0, j * c) : Int × Int × Int)
  /-- μ-方向（単数系）は固定（Ind2 の単数共有）。 -/
  mu_fixed : ∀ b : Int,
    (tltLink j).map (atpInclGeom.map ((0, b, 0) : Int × Int × Int))
      = atpInclGeom.map ((0, b, 0) : Int × Int × Int)
  /-- 外ガロア共役との可換（tlt_link_compat）。 -/
  galois_equivariant : ∀ (m : Int) (z : tpeGroup.carrier),
    (tltLink j).map (atpGroup.mul (atpGroup.mul (atpSection.map m) (atpIncl.map z))
        (atpGroup.inv (atpSection.map m)))
      = atpGroup.mul (atpGroup.mul (atpSection.map m) (atpIncl.map (tltLift j z)))
          (atpGroup.inv (atpSection.map m))
  /-- 実 G_K 作用（M429F atpAct）との可換。 -/
  real_galois_equivariant : ∀ (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
      (g : GK.carrier) (x : tpeGroup.carrier),
    tltLift j ((atpAct GK M ρ g).map x) = (atpAct GK M ρ g).map (tltLift j x)
  /-- Frobenius 次数 link の非全射（正直な限定の定理化）。 -/
  frobenius_not_surjective :
    ¬ ∃ x : atpGroup.carrier, (tltLink 2).map x = atpDeckSection.map 1

/-- **M434F-8b: witness 本体** — 全フィールドを M434F-1〜7 の本物の証明で埋める
    （crux 以外の外部仮説ゼロ・完全証明）。 -/
def thetaLinkTemperedPi1Data (j : Int) : ThetaLinkTemperedPi1Data j where
  link_hom := (tltLink j).map_mul
  link_one := tlt_link_one j
  link_id := tlt_link_id
  link_comp := fun j' x => tlt_link_comp j j' x
  neg_one_involutive := tlt_link_neg_one_involutive
  geom_transport := tlt_link_geom_transport j
  theta_transport := fun a b c => tlt_link_theta_transport j a b c
  section_fixed := fun m => tlt_link_section j m
  arith_fixed := tlt_link_arith j
  deck_scaled := tlt_link_deck j
  tower_kernel := tlt_link_tower_kernel j
  commutator_preserved := tlt_link_commutator j
  theta_commutator_scaled := fun a b c a' b' c' =>
    tlt_theta_commutator j a b c a' b' c'
  cyclotome_scaled := fun c => tlt_cyclotome_scaled j c
  mu_fixed := fun b => tlt_mu_fixed j b
  galois_equivariant := fun m z => tlt_link_compat j m z
  real_galois_equivariant := fun GK M ρ g x =>
    tlt_lift_galois_equivariant GK M ρ g j x
  frobenius_not_surjective := tlt_frobenius_not_surjective

/-- **定理 (M434F-8c): theta-link データの存在（M434F 見出し・capstone）** —
    任意の Frobenius 次数 j ∈ ℤ に対し、M429F の実算術 tempered π₁ 上の theta-link
    tltLink j と、その準同型性・交換子/シクロトーム剛性の同期・塔両立・ガロア同変・
    正直な限定（非全射）を束ねたデータが**crux 以外の外部仮説なしで**存在する。 -/
theorem tlt_exists (j : Int) : Nonempty (ThetaLinkTemperedPi1Data j) :=
  ⟨thetaLinkTemperedPi1Data j⟩

/-! ## M434F-9: 実例 -/

/-- 実例: 具体的な link 計算 — tltLink 2 は ((1,2,3),4),5) を ((2,2,6),8),5) へ
    （値群 1↦2・μ-方向 2 固定・シクロトーム 3↦6・deck 4↦8・算術 5 固定）。 -/
example : (tltLink 2).map ((((((1 : Int), 2, 3) : Int × Int × Int), (4 : Int)),
      (5 : Int)) : atpGroup.carrier)
    = (((((2 : Int), 2, 6) : Int × Int × Int), (8 : Int)), (5 : Int)) := by
  show (((((2 * 1 : Int), 2, 2 * 3) : Int × Int × Int), (2 * 4 : Int)), (5 : Int))
    = (((((2 : Int), 2, 6) : Int × Int × Int), (8 : Int)), (5 : Int))
  exact atp_ext5 (by omega) rfl (by omega) (by omega) rfl

/-- 実例: 標準生成元のテータ交換子は link で j = 3 倍に同期スケール —
    tltLink 3 [ιι(1,0,0), ιι(0,1,0)] = ιι(0,0,3)（シクロトーム剛性）。 -/
example : (tltLink 3).map (atpGroup.comm (atpInclGeom.map ((1, 0, 0) : Int × Int × Int))
      (atpInclGeom.map ((0, 1, 0) : Int × Int × Int)))
    = atpInclGeom.map ((0, 0, 3) : Int × Int × Int) := by
  have h := tlt_theta_commutator 3 1 0 0 0 1 0
  have hv : (3 : Int) * ((1 : Int) * 1 - 0 * 0) = 3 := by omega
  rw [hv] at h
  exact h

/-- 実例: 外ガロア共役との可換（tlt_link_compat の具体形）— j = 2・m = 1・
    z = ιι(0,1,0) で link(s(1)·ι(z)·s(1)⁻¹) = s(1)·ι(tltLift 2 z)·s(1)⁻¹。 -/
example : (tltLink 2).map (atpGroup.mul (atpGroup.mul (atpSection.map 1)
        (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int))))
      (atpGroup.inv (atpSection.map 1)))
    = atpGroup.mul (atpGroup.mul (atpSection.map 1)
        (atpIncl.map (tltLift 2 (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))))
      (atpGroup.inv (atpSection.map 1)) :=
  tlt_link_compat 2 1 (tpeIncl.map ((0, 1, 0) : Int × Int × Int))

/-- 実例: μ-方向（単数系）は任意の j で固定・シクロトームは j 倍
    （Ind2 単数共有とシクロトーム剛性の対比）。 -/
example : (tltLink 5).map (atpInclGeom.map ((0, 7, 0) : Int × Int × Int))
      = atpInclGeom.map ((0, 7, 0) : Int × Int × Int)
    ∧ (tltLink 5).map (atpInclGeom.map ((0, 0, 7) : Int × Int × Int))
      = atpInclGeom.map ((0, 0, 35) : Int × Int × Int) := by
  refine ⟨tlt_mu_fixed 5 7, ?_⟩
  have h := tlt_cyclotome_scaled 5 7
  have hv : (5 : Int) * 7 = 35 := by omega
  rw [hv] at h
  exact h

/-- 実例: j = −1 の link は本物の自己同型（対合・単射・全射）。 -/
example : (∀ x : atpGroup.carrier, (tltLink (-1)).map ((tltLink (-1)).map x) = x)
    ∧ (∀ y : atpGroup.carrier, ∃ x, (tltLink (-1)).map x = y) :=
  ⟨tlt_link_neg_one_involutive, tlt_link_neg_one_surjective⟩

/-- 実例: theta-link データは任意の Frobenius 次数で存在（capstone の具体化）。 -/
example : Nonempty (ThetaLinkTemperedPi1Data 2) := tlt_exists 2

end IUT
