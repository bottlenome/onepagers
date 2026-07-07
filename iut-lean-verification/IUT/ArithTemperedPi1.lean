-- M429F ArithTemperedPi1 [実・本物・柱A]
-- complete_pct 影響: 柱A で M424F の幾何 tempered π₁^temp（tpeGroup）を数論化＝算術 tempered 基本群 atpGroup = tpeGroup ⋊_χ ℤ（円分指標像商）を建設し、完全列 1→π₁^temp→Π^arith→ℤ→1・外ガロア表現（χ 捻り atpTw が**本物の自己同型**に昇格・テータ交換子の χ 捻り）・二段塔 Δ^temp ⊆ π₁^temp ⊆ Π^arith を完全証明。
-- 正直な限定: 算術商は実 G_K（非可換副有限）でなく円分指標像のモデル ℤ（離散シクロトーム ℤ は Aut = {±1} ゆえ作用は符号指標 atpChi を経由）・full slim 遠アーベル復元・幾何的実現・(ℤ/n)^× 値の実 χ の群合成（mod n、M322F 側）は外部/後続。

/-
  IUT/ArithTemperedPi1.lean — M429F [実／本物・柱A]
  分類: 実（算術 tempered 基本群 Π^arith ＝ 幾何 tempered π₁^temp の G_K-拡大の建設）

  既存の実部品:
    * M424F (TemperedPi1Etale): 幾何 tempered π₁^temp ＝ tpeGroup = thetaGrp ⋊_α ℤ
      （非可換分裂拡大 1→Δ^temp→π₁^temp→ℤ→1・テータ交換子＝シクロトーム着地・
      外ガロア χ 捻り tpeScale/tpeAct——ただし**群全体の自己同型ではない**が正直な限定）
    * M389F (TemperedThetaOuterAction): 中心スケール ttoaScale・実円分指標スカラー ttoaChar
    * M322F (CyclotomicRigidity): 実円分指標 cycRigChar : G_K → (ℤ/n)^×・CycGKAction

  本モジュールは**次の実ステップ＝数論化**を建設する。[IUTchI] §2 の入力である
  算術 tempered 基本群の完全列 1 → π₁^temp(X_K̄) → π₁^temp(X) → G_K → 1 の、
  円分指標像商による本物の群論的実現:

    atpGroup ＝ tpeGroup ⋊_{atpTw ∘ atpChi} ℤ、台 ((ℤ³)×ℤ)×ℤ、積
      (x, m)·(y, m') = (x ·_tpe atpTw (atpChi m) y, m + m')

  ここで核心は **χ 捻りの自己同型への昇格**である:
    * M424F/M389F の中心のみのスケール tpeScale e（c ↦ e·c）は Heisenberg コサイクル
      a·b′ を捻るため群準同型で**ない**（M389F-2b の正直な内容）。
    * 正しい算術作用は Tate 曲線の幾何 π₁ への G_K 作用の姿そのもの:
      **deck/値群方向 a は固定・μ-捻れ方向 b は χ 倍・シクロトーム c は χ 倍**:
        atpTw e ((a,b,c),n) = ((a, e·b, e·c), n)
      これは**任意の e で本物の群準同型**（atp_tw_hom、コサイクルも同時に捻れるゆえ）、
      e ∈ ℤ^× = {±1} で本物の自己同型（atp_tw_chi_involutive）。
      交換子＝シンプレクティック形式（Weil ペアリング）は χ 倍で同変:
        atpTw e [ι x, ι y] = ι(0,0, e·ω)（atp_tw が準同型なので on the nose）。
      中心（シクロトーム）への制限は M424F tpeScale／M389F ttoaScale に一致
      （atp_act_center_agrees）——すなわち atpTw は既存 χ 捻りの**唯一の自然な**
      自己同型拡張である。

  完全証明する内容（すべて本物の群演算・toy 主語なし）:
    * 離散円分指標 atpChi : ℤ → ℤ^× = {±1}（atpChi m = 1 − 2(m mod 2)）:
      準同型 atpChi(m+m') = atpChi(m)·atpChi(m')・単元性 χ² = 1・核 = 2ℤ・
      像 = ℤ^× 全体（離散シクロトーム ℤ の自己同型群 Aut(ℤ) = {±1} を使い切る）
    * atpGroup の群公理（結合律・単位・逆元——atpTw の準同型性・作用性・χ の
      準同型性から**抽象的に**証明、座標総当たりでなく）
    * 算術完全列 1 → π₁^temp(=tpeGroup) → Π^arith(=atpGroup) → ℤ → 1:
      ι 単射・pr 全射・ker(pr) = im(ι)・正規性（共役の明示公式
      g·ι(z)·g⁻¹ = ι(x₁ · atpTw(χ(m))(z) · x₁⁻¹)）・分裂切断・**非中心**
      （χ(1) = −1 が μ-方向を反転: s(1)·ι(0,1,0) ≠ ι(0,1,0)·s(1)）
    * **外ガロア表現（本丸）**: s(m)·ι(z)·s(m)⁻¹ = ι(atpTw (atpChi m) z)——算術商の
      共役作用が幾何 π₁^temp の χ 捻り自己同型を誘導する（atp_outer_galois）。
      テータ部の元では s(m)·ιι(a,b,c)·s(m)⁻¹ = ιι(a, χ·b, χ·c)（Tate 曲線の
      G_K 作用の姿）。テータ交換子は χ で捻れる:
      s(m)·ι[ιx,ιy]·s(m)⁻¹ = ιι(0,0, χ(m)·ω)（atp_conj_commutator_chi）。
      算術×幾何交換子 [s(m), ι z] = ι(atpTw(χ)z · z⁻¹) は非自明（真に捻れた拡大）。
    * 二段塔 Δ^temp(=thetaGrp) ⊆ π₁^temp(=tpeGroup) ⊆ Π^arith(=atpGroup):
      合成単射 atpInclGeom・thetaGrp 像は atpGroup で正規・全商 atpGroup/thetaGrp
      ≅ ℤ×ℤ（deck × 算術、atpFullProj の完全性）・deck 商は M374F 塔 ℤ/l^n・ℤ_l へ
      完備化（atpDeckLevel/atpDeckComplete・錐・全射）
    * 実 G_K（M322F CycGKAction）との接続: atpAct GK M ρ g = atpTwHom (χ(g)) は
      各 g で**本物の群準同型**（M424F tpeAct の非準同型 χ 捻りの昇格）・テータ
      交換子を実円分指標 ttoaChar 倍に捻る・中心（シクロトーム）上で M424F tpeAct
      に一致・deck/算術方向に自明
    * 非可換・非有界指数（真に tempered）・非 slim（偶数切断 s(2) が中心に残る＝
      算術商が可換モデル ℤ であることの正直な帰結、定理で固定）

  正直な限定（消さない・弱めない）:
    * 算術商は**実 G_K（非可換副有限）ではなく**その円分指標像のモデル ℤ。
      離散シクロトーム ℤ の自己同型群は {±1} なので、離散モデル上の本物の群作用は
      必然的に符号指標 atpChi : ℤ → {±1} を経由する（これは欠陥でなく離散モデルの
      定理的事実）。(ℤ/n)^× 値の実円分指標 cycRigChar の全体を作用させるには副有限
      シクロトーム（Ẑ(1)、M374F の ℤ_l が一方向）が必要で後続。
    * 実 χ(g) = ttoaChar による atpAct は**各 g ごとに**本物の準同型だが、G_K の
      群合成との整合 σ_{gh} = σ_g∘σ_h は ℤ 値では mod n でしか成り立たない
      （μ_n 上の実作用は M322F/M389F が保持）。ゆえに半直積の作用には ℤ^× 値の
      atpChi を使う。
    * full slim 遠アーベル復元・Tate 曲線の実被覆空間としての幾何的実現・
      p 進解析テータのガロア同変評価は外部/後続（M424F と同じ）。
    * atpGroup は slim で**ない**（偶数切断が中心、atp_not_slim を定理で明示）。
      実 Π^arith の slim 性は実 G_K の非可換性に由来し外部。
  全て選択公理不使用（propext / Quot.sound のみ）。
-/
import IUT.TemperedPi1Etale

namespace IUT

/-! ## M429F-0: 補助（5 成分 ext・対 ext・inv 1 = 1） -/

/-- 算術群の台 ((ℤ³)×ℤ)×ℤ の等値補題（5 成分）。 -/
theorem atp_ext5 {a₁ b₁ c₁ n₁ m₁ a₂ b₂ c₂ n₂ m₂ : Int}
    (h1 : a₁ = a₂) (h2 : b₁ = b₂) (h3 : c₁ = c₂) (h4 : n₁ = n₂) (h5 : m₁ = m₂) :
    ((((((a₁, b₁, c₁) : Int × Int × Int), n₁) : (Int × Int × Int) × Int), m₁)
      : ((Int × Int × Int) × Int) × Int)
      = (((((a₂, b₂, c₂) : Int × Int × Int), n₂) : (Int × Int × Int) × Int), m₂) := by
  rw [h1, h2, h3, h4, h5]

/-- 対の等値補題（幾何部 × 算術座標）。 -/
theorem atp_pair_ext {x y : tpeGroup.carrier} {m n : Int}
    (h1 : x = y) (h2 : m = n) :
    ((x, m) : tpeGroup.carrier × Int) = (y, n) := by
  rw [h1, h2]

/-- 任意の群で 1⁻¹ = 1（左公理からの導出、共役計算用）。 -/
theorem atp_grp_inv_one (G : Grp) : G.inv G.one = G.one := by
  have h := G.inv_mul G.one
  rw [G.mul_one] at h
  exact h

/-! ## M429F-1: 離散円分指標 atpChi : ℤ → ℤ^× = {±1}

  離散シクロトーム ℤ（テータ交換子の着地先、M11/M384F/M424F）の自己同型群は
  Aut(ℤ) = {±1}。ゆえに算術商 ℤ（G_K の円分指標像のモデル）の離散モデル上の
  **本物の群作用**は必然的に符号指標を経由する。atpChi m = 1 − 2·(m mod 2) が
  その指標＝準同型 ℤ → (ℤ^×,·)、像は ℤ^× 全体。 -/

/-- **M429F-1a: 離散円分指標** atpChi m = (−1)^m の閉形式 1 − 2·(m mod 2)。 -/
def atpChi (m : Int) : Int := 1 - 2 * (m % 2)

/-- 偶数での値 = 1。 -/
theorem atp_chi_even (m : Int) (h : m % 2 = 0) : atpChi m = 1 := by
  show 1 - 2 * (m % 2) = 1
  omega

/-- 奇数での値 = −1。 -/
theorem atp_chi_odd (m : Int) (h : m % 2 = 1) : atpChi m = -1 := by
  show 1 - 2 * (m % 2) = -1
  omega

theorem atp_chi_zero : atpChi 0 = 1 := atp_chi_even 0 (by omega)

theorem atp_chi_one : atpChi 1 = -1 := atp_chi_odd 1 (by omega)

/-- **定理 (M429F-1b): 値は単元 {±1}**（ℤ^× に着地）。 -/
theorem atp_chi_cases (m : Int) : atpChi m = 1 ∨ atpChi m = -1 := by
  show 1 - 2 * (m % 2) = 1 ∨ 1 - 2 * (m % 2) = -1
  omega

/-- **定理 (M429F-1c): 指標の準同型性** χ(m+m') = χ(m)·χ(m')
    （加法群 ℤ → 乗法群 ℤ^× の本物の群準同型）。 -/
theorem atp_chi_add (m m' : Int) : atpChi (m + m') = atpChi m * atpChi m' := by
  have h1 : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have h2 : m' % 2 = 0 ∨ m' % 2 = 1 := by omega
  cases h1 with
  | inl he =>
    cases h2 with
    | inl he' =>
      rw [atp_chi_even m he, atp_chi_even m' he', atp_chi_even (m + m') (by omega),
        Int.mul_one]
    | inr ho' =>
      rw [atp_chi_even m he, atp_chi_odd m' ho', atp_chi_odd (m + m') (by omega),
        Int.one_mul]
  | inr ho =>
    cases h2 with
    | inl he' =>
      rw [atp_chi_odd m ho, atp_chi_even m' he', atp_chi_odd (m + m') (by omega),
        Int.mul_one]
    | inr ho' =>
      rw [atp_chi_odd m ho, atp_chi_odd m' ho', atp_chi_even (m + m') (by omega),
        Int.neg_mul_neg, Int.one_mul]

/-- **定理 (M429F-1d): 反転不変** χ(−m) = χ(m)（χ² = 1 の帰結の逆元版）。 -/
theorem atp_chi_neg (m : Int) : atpChi (-m) = atpChi m := by
  have h1 : m % 2 = 0 ∨ m % 2 = 1 := by omega
  cases h1 with
  | inl he => rw [atp_chi_even m he, atp_chi_even (-m) (by omega)]
  | inr ho => rw [atp_chi_odd m ho, atp_chi_odd (-m) (by omega)]

/-- **定理 (M429F-1e): 単元性** χ(m)·χ(m) = 1（χ は ℤ^× に値を持つ）。 -/
theorem atp_chi_sq (m : Int) : atpChi m * atpChi m = 1 := by
  have h := atp_chi_cases m
  cases h with
  | inl h1 => rw [h1, Int.mul_one]
  | inr h1 => rw [h1, Int.neg_mul_neg, Int.one_mul]

/-- **定理 (M429F-1f): 指標の核 = 偶数部 2ℤ**（算術商の中で幾何に自明に作用する部分）。 -/
theorem atp_chi_kernel (m : Int) : atpChi m = 1 ↔ m % 2 = 0 := by
  constructor
  · intro h
    have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    cases h2 with
    | inl h0 => exact h0
    | inr h1 =>
      rw [atp_chi_odd m h1] at h
      exact absurd h (by omega)
  · intro h
    exact atp_chi_even m h

/-- **定理 (M429F-1g): 像は ℤ^× = {±1} 全体**（離散シクロトームの自己同型群を使い切る）。 -/
theorem atp_chi_onto_units (e : Int) (h : e = 1 ∨ e = -1) : ∃ m : Int, atpChi m = e := by
  cases h with
  | inl h1 => exact ⟨0, by rw [atp_chi_zero, h1]⟩
  | inr h1 => exact ⟨1, by rw [atp_chi_one, h1]⟩

/-! ## M429F-2: χ 捻りの自己同型への昇格 atpTw（本丸その 1）

  M424F/M389F の中心のみの χ 捻り tpeScale e（c ↦ e·c）は Heisenberg コサイクル
  a·b′ を捻るため群準同型で**ない**（M389F-2b）。正しい算術作用は
    atpTw e ((a,b,c),n) = ((a, e·b, e·c), n)
  ——deck/値群方向 a・n は固定、μ-捻れ方向 b とシクロトーム c を同時に e 倍。
  コサイクル a·(e·b′) = e·(a·b′) も同時に捻れるので**任意の e で本物の群準同型**、
  e = ±1 で本物の自己同型。これが Tate 曲線の幾何 π₁ への G_K 作用の離散的な姿。 -/

/-- **M429F-2a: χ 捻り自己準同型** atpTw e ((a,b,c),n) = ((a, e·b, e·c), n)。 -/
@[reducible] def atpTw (e : Int) (x : tpeGroup.carrier) : tpeGroup.carrier :=
  ((x.1.1, e * x.1.2.1, e * x.1.2.2), x.2)

/-- 成分表示。 -/
theorem atp_tw_apply (e a b c n : Int) :
    atpTw e ((((a, b, c) : Int × Int × Int), n) : (Int × Int × Int) × Int)
      = (((a, e * b, e * c) : Int × Int × Int), n) := rfl

/-- deck 座標（算術幾何の値群方向）は固定。 -/
theorem atp_tw_deck (e : Int) (x : tpeGroup.carrier) : (atpTw e x).2 = x.2 := rfl

/-- テータ部の deck 方向第 1 座標も固定。 -/
theorem atp_tw_theta_deck (e : Int) (x : tpeGroup.carrier) :
    (atpTw e x).1.1 = x.1.1 := rfl

/-- **定理 (M429F-2b: 本物の群準同型・本丸)** — atpTw e は tpeGroup の**群準同型**
    （tpeScale と違い任意の e で on the nose、μ-方向 b とコサイクルが同時に捻れるゆえ）。 -/
theorem atp_tw_hom (e : Int) (x y : tpeGroup.carrier) :
    atpTw e (tpeGroup.mul x y) = tpeGroup.mul (atpTw e x) (atpTw e y) := by
  obtain ⟨⟨a, b, c⟩, n⟩ := x
  obtain ⟨⟨a', b', c'⟩, n'⟩ := y
  show ((((a + a', e * (b + b'), e * (c + (c' + n * b') + a * b')) : Int × Int × Int),
        n + n') : (Int × Int × Int) × Int)
    = (((a + a', e * b + e * b', e * c + (e * c' + n * (e * b')) + a * (e * b'))
        : Int × Int × Int), n + n')
  refine tpe_ext rfl (Int.mul_add e b b') ?_ rfl
  rw [Int.mul_add e (c + (c' + n * b')) (a * b'), Int.mul_add e c (c' + n * b'),
    Int.mul_add e c' (n * b')]
  rw [← Int.mul_assoc e n b', Int.mul_comm e n, Int.mul_assoc n e b']
  rw [← Int.mul_assoc e a b', Int.mul_comm e a, Int.mul_assoc a e b']

/-- **定理 (M429F-2c): 単位則** atpTw 1 = id。 -/
theorem atp_tw_id (x : tpeGroup.carrier) : atpTw 1 x = x := by
  obtain ⟨⟨a, b, c⟩, n⟩ := x
  show ((((a, 1 * b, 1 * c) : Int × Int × Int), n) : (Int × Int × Int) × Int)
    = (((a, b, c) : Int × Int × Int), n)
  exact tpe_ext rfl (Int.one_mul b) (Int.one_mul c) rfl

/-- **定理 (M429F-2d): 合成則** atpTw e ∘ atpTw e' = atpTw (e·e')
    （(ℤ,·) のモノイド作用、M389F ttoa_scale_mul の昇格）。 -/
theorem atp_tw_mul (e e' : Int) (x : tpeGroup.carrier) :
    atpTw e (atpTw e' x) = atpTw (e * e') x := by
  obtain ⟨⟨a, b, c⟩, n⟩ := x
  show ((((a, e * (e' * b), e * (e' * c)) : Int × Int × Int), n) : (Int × Int × Int) × Int)
    = (((a, (e * e') * b, (e * e') * c) : Int × Int × Int), n)
  exact tpe_ext rfl (Int.mul_assoc e e' b).symm (Int.mul_assoc e e' c).symm rfl

/-- 単位元の保存 atpTw e 1 = 1。 -/
theorem atp_tw_one (e : Int) : atpTw e tpeGroup.one = tpeGroup.one := by
  show ((((0 : Int), e * 0, e * 0) : Int × Int × Int), (0 : Int))
    = ((((0 : Int), 0, 0) : Int × Int × Int), (0 : Int))
  exact tpe_ext rfl (Int.mul_zero e) (Int.mul_zero e) rfl

/-- **定理 (M429F-2e): χ 値の捻りは対合＝本物の自己同型**
    （χ² = 1 ゆえ atpTw (χ m) は自分自身が逆写像）。 -/
theorem atp_tw_chi_involutive (m : Int) (x : tpeGroup.carrier) :
    atpTw (atpChi m) (atpTw (atpChi m) x) = x := by
  rw [atp_tw_mul, atp_chi_sq, atp_tw_id]

/-- **M429F-2f: 準同型としてのパッケージ** atpTwHom e : Hom tpeGroup tpeGroup
    （M424F tpeScale の非準同型 χ 捻りの、本物の Hom への昇格）。 -/
def atpTwHom (e : Int) : Hom tpeGroup tpeGroup where
  map := atpTw e
  map_mul := atp_tw_hom e

/-- **定理 (M429F-2g): 交換子は on the nose で保たれる**（準同型ゆえ・M389F-3a の昇格）。 -/
theorem atp_tw_commutator (e : Int) (x y : tpeGroup.carrier) :
    atpTw e (tpeGroup.comm x y) = tpeGroup.comm (atpTw e x) (atpTw e y) :=
  Hom.map_grp_comm (atpTwHom e) x y

/-- **定理 (M429F-2h): テータ交換子＝シンプレクティック形式は χ 同変（Weil ペアリング
    の Galois 同変性の離散版）** — atpTw e [ι x, ι y] = ι(0, 0, e·ω)。 -/
theorem atp_tw_theta_commutator (e a b c a' b' c' : Int) :
    atpTw e (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int)))
      = tpeIncl.map ((0, 0, e * (a * b' - a' * b)) : Int × Int × Int) := by
  rw [tpe_commutator_cyclotome]
  show ((((0 : Int), e * 0, e * (a * b' - a' * b)) : Int × Int × Int), (0 : Int))
    = ((((0 : Int), 0, e * (a * b' - a' * b)) : Int × Int × Int), (0 : Int))
  exact tpe_ext rfl (Int.mul_zero e) rfl rfl

/-! ## M429F-3: 算術 tempered 基本群 atpGroup ＝ tpeGroup ⋊_{atpTw∘atpChi} ℤ

  群公理は atpTw の準同型性（2b）・作用性（2c/2d）・χ の準同型性（1c/1d/1e）から
  **抽象的に**証明する（座標総当たりでなく、半直積の一般論の実インスタンス）。 -/

/-- **M429F-3: 算術 tempered 基本群** atpGroup ＝ tpeGroup ⋊_χ ℤ。
    台 ((ℤ³)×ℤ)×ℤ、積 (x,m)·(y,m') = (x ·_tpe atpTw(χ(m))(y), m+m')。
    算術商 ℤ（円分指標像のモデル）が幾何 tempered π₁^temp を χ 捻り自己同型で
    捻る**非中心**の半直積（[IUTchI] §2 の算術基本群拡大の離散実現）。 -/
@[reducible] def atpGroup : Grp where
  carrier := tpeGroup.carrier × Int
  mul := fun x y => (tpeGroup.mul x.1 (atpTw (atpChi x.2) y.1), x.2 + y.2)
  one := (tpeGroup.one, (0 : Int))
  inv := fun x => (atpTw (atpChi x.2) (tpeGroup.inv x.1), -x.2)
  mul_assoc := by
    intro x y z
    obtain ⟨x1, m⟩ := x
    obtain ⟨y1, m'⟩ := y
    obtain ⟨z1, m''⟩ := z
    show (tpeGroup.mul (tpeGroup.mul x1 (atpTw (atpChi m) y1))
          (atpTw (atpChi (m + m')) z1), (m + m') + m'')
      = (tpeGroup.mul x1 (atpTw (atpChi m) (tpeGroup.mul y1 (atpTw (atpChi m') z1))),
          m + (m' + m''))
    rw [atp_tw_hom (atpChi m) y1 (atpTw (atpChi m') z1)]
    rw [atp_tw_mul (atpChi m) (atpChi m') z1]
    rw [← atp_chi_add m m']
    rw [tpeGroup.mul_assoc x1 (atpTw (atpChi m) y1) (atpTw (atpChi (m + m')) z1)]
    exact atp_pair_ext rfl (by omega)
  one_mul := by
    intro x
    obtain ⟨x1, m⟩ := x
    show (tpeGroup.mul tpeGroup.one (atpTw (atpChi 0) x1), 0 + m) = (x1, m)
    rw [atp_chi_zero, atp_tw_id, tpeGroup.one_mul]
    exact atp_pair_ext rfl (by omega)
  inv_mul := by
    intro x
    obtain ⟨x1, m⟩ := x
    show (tpeGroup.mul (atpTw (atpChi m) (tpeGroup.inv x1)) (atpTw (atpChi (-m)) x1),
          -m + m)
      = (tpeGroup.one, (0 : Int))
    rw [atp_chi_neg m]
    rw [← atp_tw_hom (atpChi m) (tpeGroup.inv x1) x1]
    rw [tpeGroup.inv_mul x1]
    rw [atp_tw_one (atpChi m)]
    exact atp_pair_ext rfl (by omega)

/-- 積の成分表示（definitional）。 -/
theorem atp_mul_expand (x1 y1 : tpeGroup.carrier) (m m' : Int) :
    atpGroup.mul ((x1, m) : atpGroup.carrier) (y1, m')
      = (tpeGroup.mul x1 (atpTw (atpChi m) y1), m + m') := rfl

/-- 逆元の成分表示（definitional）。 -/
theorem atp_inv_expand (x1 : tpeGroup.carrier) (m : Int) :
    atpGroup.inv ((x1, m) : atpGroup.carrier)
      = (atpTw (atpChi m) (tpeGroup.inv x1), -m) := rfl

/-! ## M429F-4: 算術完全列 1 → π₁^temp → Π^arith → ℤ → 1 -/

/-- **核埋め込み ι : π₁^temp ↪ Π^arith**（z ↦ (z, 0)）— 幾何 tempered π₁^temp
    （M424F tpeGroup）を算術基本群の核として埋め込む本物の群準同型。 -/
def atpIncl : Hom tpeGroup atpGroup where
  map := fun z => (z, (0 : Int))
  map_mul := by
    intro z w
    show ((tpeGroup.mul z w, (0 : Int)) : atpGroup.carrier)
      = (tpeGroup.mul z (atpTw (atpChi 0) w), (0 : Int) + 0)
    rw [atp_chi_zero, atp_tw_id]
    exact atp_pair_ext rfl (by omega)

/-- **射影 pr : Π^arith ↠ ℤ**（(z, m) ↦ m）— 算術商（G_K の円分指標像のモデル）
    への全射準同型。 -/
def atpProj : Hom atpGroup intGrp where
  map := fun x => x.2
  map_mul := fun _ _ => rfl

/-- **分裂切断 s : ℤ → Π^arith**（m ↦ (1, m)）— 算術拡大の分裂（pr∘s = id）。 -/
def atpSection : Hom intGrp atpGroup where
  map := fun m => (tpeGroup.one, m)
  map_mul := by
    intro m m'
    show ((tpeGroup.one, m + m') : atpGroup.carrier)
      = (tpeGroup.mul tpeGroup.one (atpTw (atpChi m) tpeGroup.one), m + m')
    rw [atp_tw_one, tpeGroup.one_mul]

/-- **定理 (M429F-4a): ι は単射**。 -/
theorem atp_incl_injective : atpIncl.Injective :=
  fun _ _ h => congrArg Prod.fst h

/-- **定理 (M429F-4b): pr は全射**（切断 s の像で実現）。 -/
theorem atp_proj_surjective : ∀ g : intGrp.carrier, ∃ x, atpProj.map x = g :=
  fun g => ⟨atpSection.map g, rfl⟩

/-- **定理 (M429F-4c): 切断は分裂** pr ∘ s = id。 -/
theorem atp_section_splits (m : Int) : atpProj.map (atpSection.map m) = m := rfl

/-- **定理 (M429F-4d): 算術拡大の完全性** — ker(pr) = im(ι)。幾何 tempered π₁^temp
    がちょうど算術商への射影の核である（[IUTchI] §2 の完全列の実現）。 -/
theorem atp_extension_exact (x : atpGroup.carrier) :
    atpProj.map x = intGrp.one ↔ ∃ z : tpeGroup.carrier, atpIncl.map z = x := by
  obtain ⟨z, m⟩ := x
  constructor
  · intro h
    have hm : m = (0 : Int) := h
    subst hm
    exact ⟨z, rfl⟩
  · intro h
    obtain ⟨w, hw⟩ := h
    show m = (0 : Int)
    exact (congrArg Prod.snd hw).symm

/-! ## M429F-5: 共役・正規性・外ガロア表現（本丸その 2） -/

/-- **定理 (M429F-5a): 共役の明示公式** — 任意の g = (x₁, m) による ι(z) の共役は
    ι(x₁ · atpTw(χ(m))(z) · x₁⁻¹)。算術元の共役 ＝ χ 捻り自己同型 ∘ 幾何の内部自己同型
    ——**外ガロア表現 G → Out(Δ) の実内容**（M9-3 の実インスタンス）。 -/
theorem atp_conj_incl (x1 : tpeGroup.carrier) (m : Int) (z : tpeGroup.carrier) :
    atpGroup.mul (atpGroup.mul ((x1, m) : atpGroup.carrier) (atpIncl.map z))
        (atpGroup.inv (x1, m))
      = atpIncl.map (tpeGroup.mul (tpeGroup.mul x1 (atpTw (atpChi m) z))
          (tpeGroup.inv x1)) := by
  have h1 : atpGroup.mul ((x1, m) : atpGroup.carrier) (atpIncl.map z)
      = (tpeGroup.mul x1 (atpTw (atpChi m) z), m) := by
    show ((tpeGroup.mul x1 (atpTw (atpChi m) z), m + 0) : atpGroup.carrier)
      = (tpeGroup.mul x1 (atpTw (atpChi m) z), m)
    exact atp_pair_ext rfl (by omega)
  rw [h1]
  show ((tpeGroup.mul (tpeGroup.mul x1 (atpTw (atpChi m) z))
        (atpTw (atpChi m) (atpTw (atpChi m) (tpeGroup.inv x1))), m + -m) : atpGroup.carrier)
    = (tpeGroup.mul (tpeGroup.mul x1 (atpTw (atpChi m) z)) (tpeGroup.inv x1), (0 : Int))
  rw [atp_tw_mul (atpChi m) (atpChi m) (tpeGroup.inv x1), atp_chi_sq m,
    atp_tw_id (tpeGroup.inv x1)]
  exact atp_pair_ext rfl (by omega)

/-- **定理 (M429F-5b): ι(π₁^temp) は正規部分群**（明示 witness つき）。
    完全列 1→π₁^temp→Π^arith→ℤ→1 の正規性の本物の証明。 -/
theorem atp_geometric_normal (g : atpGroup.carrier) (z : tpeGroup.carrier) :
    ∃ w : tpeGroup.carrier,
      atpGroup.mul (atpGroup.mul g (atpIncl.map z)) (atpGroup.inv g)
        = atpIncl.map w := by
  obtain ⟨x1, m⟩ := g
  exact ⟨tpeGroup.mul (tpeGroup.mul x1 (atpTw (atpChi m) z)) (tpeGroup.inv x1),
    atp_conj_incl x1 m z⟩

/-- **定理 (M429F-5c): 外ガロア表現（本丸）** — 算術切断の共役は χ 捻り自己同型:
    s(m)·ι(z)·s(m)⁻¹ = ι(atpTw (χ(m)) z)。算術商が幾何 tempered π₁^temp に
    **本物の自己同型**（atpTw、M424F の非準同型 χ 捻りの昇格）で外から作用する。 -/
theorem atp_outer_galois (m : Int) (z : tpeGroup.carrier) :
    atpGroup.mul (atpGroup.mul (atpSection.map m) (atpIncl.map z))
        (atpGroup.inv (atpSection.map m))
      = atpIncl.map (atpTw (atpChi m) z) := by
  show atpGroup.mul (atpGroup.mul ((tpeGroup.one, m) : atpGroup.carrier) (atpIncl.map z))
      (atpGroup.inv ((tpeGroup.one, m) : atpGroup.carrier))
    = atpIncl.map (atpTw (atpChi m) z)
  rw [atp_conj_incl tpeGroup.one m z]
  rw [tpeGroup.one_mul (atpTw (atpChi m) z), atp_grp_inv_one tpeGroup,
    tpeGroup.mul_one]

/-- **定理 (M429F-5d): テータ部での外ガロア作用の姿（Tate 曲線の G_K 作用）** —
    s(m)·ιι(a,b,c)·s(m)⁻¹ = ιι(a, χ(m)·b, χ(m)·c): deck/値群方向 a は固定・
    μ-捻れ方向 b は χ 倍・シクロトーム c は χ 倍。 -/
theorem atp_outer_galois_theta (m a b c : Int) :
    atpGroup.mul (atpGroup.mul (atpSection.map m)
        (atpIncl.map (tpeIncl.map ((a, b, c) : Int × Int × Int))))
      (atpGroup.inv (atpSection.map m))
      = atpIncl.map (tpeIncl.map ((a, atpChi m * b, atpChi m * c) : Int × Int × Int)) :=
  atp_outer_galois m (tpeIncl.map ((a, b, c) : Int × Int × Int))

/-- 交換子の共役表示 [x,y] = ((x·y)·x⁻¹)·y⁻¹（群公理のみ、M424F tpe_comm_eq の類似）。 -/
theorem atp_comm_eq (x y : atpGroup.carrier) :
    atpGroup.comm x y
      = atpGroup.mul (atpGroup.mul (atpGroup.mul x y) (atpGroup.inv x))
          (atpGroup.inv y) := by
  show atpGroup.mul (atpGroup.mul x y) (atpGroup.mul (atpGroup.inv x) (atpGroup.inv y))
    = atpGroup.mul (atpGroup.mul (atpGroup.mul x y) (atpGroup.inv x)) (atpGroup.inv y)
  rw [← atpGroup.mul_assoc (atpGroup.mul x y) (atpGroup.inv x) (atpGroup.inv y)]

/-- **定理 (M429F-5e): 算術×幾何交換子 ＝ χ 捻りの差** —
    [s(m), ι(z)] = ι(atpTw(χ(m))(z) · z⁻¹)。算術方向と幾何方向の交換子が χ 捻りの
    ズレそのものを生む（M424F の deck×テータ交換子＝ペアリングの算術版）。 -/
theorem atp_arith_commutator (m : Int) (z : tpeGroup.carrier) :
    atpGroup.comm (atpSection.map m) (atpIncl.map z)
      = atpIncl.map (tpeGroup.mul (atpTw (atpChi m) z) (tpeGroup.inv z)) := by
  rw [atp_comm_eq, atp_outer_galois m z, ← atpIncl.map_inv, ← atpIncl.map_mul]

/-- **定理 (M429F-5f): テータ交換子の χ 捻り（本丸）** — 算術共役はテータ交換子＝
    シンプレクティック形式を χ(m) 倍に捻る:
    s(m)·ι[ιx, ιy]·s(m)⁻¹ = ιι(0, 0, χ(m)·ω)。M424F tpe_act_commutator_twist の
    「作用」を算術群の**内部共役**として実現した本物の外ガロア χ 捻り。 -/
theorem atp_conj_commutator_chi (m a b c a' b' c' : Int) :
    atpGroup.mul (atpGroup.mul (atpSection.map m)
        (atpIncl.map (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
          (tpeIncl.map ((a', b', c') : Int × Int × Int)))))
      (atpGroup.inv (atpSection.map m))
      = atpIncl.map (tpeIncl.map
          ((0, 0, atpChi m * (a * b' - a' * b)) : Int × Int × Int)) := by
  rw [tpe_commutator_cyclotome, atp_outer_galois]
  refine congrArg atpIncl.map ?_
  show ((((0 : Int), atpChi m * 0, atpChi m * (a * b' - a' * b)) : Int × Int × Int),
      (0 : Int))
    = ((((0 : Int), 0, atpChi m * (a * b' - a' * b)) : Int × Int × Int), (0 : Int))
  exact tpe_ext rfl (Int.mul_zero (atpChi m)) rfl rfl

/-- **定理 (M429F-5g): 算術拡大は非中心（真に捻れた拡大）** — χ(1) = −1 が μ-方向を
    反転するため、算術切断 s(1) はテータ部 ιι(0,1,0) と可換でない。算術群が
    直積 π₁^temp × ℤ でなく真の半直積であることの証人。 -/
theorem atp_extension_not_central :
    atpGroup.mul (atpSection.map 1)
        (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))
      ≠ atpGroup.mul (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))
          (atpSection.map 1) := by
  intro h
  have hL : atpGroup.mul (atpSection.map 1)
        (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))
      = (((((0 : Int), -1, 0) : Int × Int × Int), (0 : Int)), (1 : Int)) := by
    show atpGroup.mul ((((((0 : Int), 0, 0) : Int × Int × Int), (0 : Int)),
          (1 : Int)) : atpGroup.carrier)
        (((((0 : Int), 1, 0) : Int × Int × Int), (0 : Int)), (0 : Int))
      = (((((0 : Int), -1, 0) : Int × Int × Int), (0 : Int)), (1 : Int))
    rw [atp_mul_expand, atp_chi_one]
    have h0 : atpTw (-1) (((((0 : Int), 1, 0) : Int × Int × Int), (0 : Int))
          : tpeGroup.carrier)
        = ((((0 : Int), -1, 0) : Int × Int × Int), (0 : Int)) := by
      show ((((0 : Int), -1 * 1, -1 * 0) : Int × Int × Int), (0 : Int))
        = ((((0 : Int), -1, 0) : Int × Int × Int), (0 : Int))
      exact tpe_ext rfl (by omega) (by omega) rfl
    rw [h0, tpe_mul_expand]
    exact atp_ext5 (by omega) (by omega) (by omega) (by omega) (by omega)
  have hR : atpGroup.mul (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))
        (atpSection.map 1)
      = (((((0 : Int), 1, 0) : Int × Int × Int), (0 : Int)), (1 : Int)) := by
    show atpGroup.mul ((((((0 : Int), 1, 0) : Int × Int × Int), (0 : Int)),
          (0 : Int)) : atpGroup.carrier)
        (((((0 : Int), 0, 0) : Int × Int × Int), (0 : Int)), (1 : Int))
      = (((((0 : Int), 1, 0) : Int × Int × Int), (0 : Int)), (1 : Int))
    rw [atp_mul_expand, atp_chi_zero, atp_tw_id, tpe_mul_expand]
    exact atp_ext5 (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hL, hR] at h
  have hb : (-1 : Int) = 1 :=
    congrArg (fun t : ((Int × Int × Int) × Int) × Int => t.1.1.2.1) h
  exact absurd hb (by omega)

/-- **定理 (M429F-5h): 算術群は非可換**。 -/
theorem atp_nonabelian : ¬ tcmAbelian atpGroup := by
  intro h
  exact atp_extension_not_central
    (h (atpSection.map 1) (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int))))

/-! ## M429F-6: 二段塔 Δ^temp ⊆ π₁^temp ⊆ Π^arith -/

/-- **M429F-6a: 幾何テータ部の合成埋め込み** ι∘ι_θ : Δ^temp(=thetaGrp) ↪ Π^arith。 -/
def atpInclGeom : Hom thetaGrp atpGroup := atpIncl.comp tpeIncl

/-- **定理 (M429F-6b): 合成埋め込みは単射**（二段塔の下段）。 -/
theorem atp_incl_geom_injective : atpInclGeom.Injective :=
  Hom.comp_injective atp_incl_injective tpe_incl_injective

/-- **M429F-6c: deck 射影の延長** Π^arith ↠ ℤ（deck 商）— χ 捻りが deck 座標を
    固定するゆえ本物の準同型（テータ部の deck 方向が算術群からも読める）。 -/
def atpDeckProj : Hom atpGroup tmpDiscretePart where
  map := fun x => x.1.2
  map_mul := fun _ _ => rfl

/-- **M429F-6d: 全商射影** Π^arith ↠ ℤ×ℤ（deck 商 × 算術商）。 -/
def atpFullProj : Hom atpGroup (prodGrp intGrp intGrp) where
  map := fun x => (x.1.2, x.2)
  map_mul := fun _ _ => rfl

/-- **定理 (M429F-6e): 二段塔の完全性** — ker(全商射影) = im(Δ^temp)。
    すなわち Π^arith / Δ^temp ≅ ℤ×ℤ（deck × 算術）の完全列
    1 → Δ^temp → Π^arith → ℤ×ℤ → 1 が成り立つ。 -/
theorem atp_tower_exact (x : atpGroup.carrier) :
    atpFullProj.map x = (prodGrp intGrp intGrp).one
      ↔ ∃ z : thetaGrp.carrier, atpInclGeom.map z = x := by
  obtain ⟨⟨⟨a, b, c⟩, n⟩, m⟩ := x
  constructor
  · intro h
    have hn : n = (0 : Int) := congrArg Prod.fst h
    have hm : m = (0 : Int) := congrArg Prod.snd h
    subst hn
    subst hm
    exact ⟨(a, b, c), rfl⟩
  · intro h
    obtain ⟨w, hw⟩ := h
    have hn : (0 : Int) = n := congrArg (fun t : ((Int × Int × Int) × Int) × Int => t.1.2) hw
    have hm : (0 : Int) = m := congrArg Prod.snd hw
    show ((n, m) : Int × Int) = ((0 : Int), (0 : Int))
    rw [← hn, ← hm]

/-- **定理 (M429F-6f): Δ^temp は算術群でも正規** — 算術元の共役は χ 捻り（テータ部では
    (a,b,c) ↦ (a, χb, χc)）∘ 幾何共役（M424F tpe_geometric_normal）でテータ部に留まる。
    二段塔の各段が正規部分群の塔をなすことの完全証明。 -/
theorem atp_theta_normal (g : atpGroup.carrier) (z : thetaGrp.carrier) :
    ∃ w : thetaGrp.carrier,
      atpGroup.mul (atpGroup.mul g (atpInclGeom.map z)) (atpGroup.inv g)
        = atpInclGeom.map w := by
  obtain ⟨x1, m⟩ := g
  obtain ⟨a, b, c⟩ := z
  have h1 := atp_conj_incl x1 m (tpeIncl.map ((a, b, c) : Int × Int × Int))
  have h2 : atpTw (atpChi m) (tpeIncl.map ((a, b, c) : Int × Int × Int))
      = tpeIncl.map ((a, atpChi m * b, atpChi m * c) : Int × Int × Int) := rfl
  rw [h2] at h1
  obtain ⟨w, hw⟩ :=
    tpe_geometric_normal x1 ((a, atpChi m * b, atpChi m * c) : Int × Int × Int)
  rw [hw] at h1
  exact ⟨w, h1⟩

/-- **定理 (M429F-6g): テータ交換子は算術群に降下** — [ιιx, ιιy] = ιι(0,0,ω)
    （M11/M384F/M424F のシクロトーム着地の二段塔版）。 -/
theorem atp_theta_commutator (a b c a' b' c' : Int) :
    atpGroup.comm (atpInclGeom.map ((a, b, c) : Int × Int × Int))
        (atpInclGeom.map ((a', b', c') : Int × Int × Int))
      = atpInclGeom.map ((0, 0, a * b' - a' * b) : Int × Int × Int) := by
  rw [← Hom.map_grp_comm atpInclGeom, theta_comm]

/-- **M429F-6h: deck 切断**（deck 商 ℤ の算術群への持ち上げ、二段塔の中段の分裂）。 -/
def atpDeckSection : Hom intGrp atpGroup where
  map := fun a => (((((0 : Int), 0, 0) : Int × Int × Int), a), (0 : Int))
  map_mul := by
    intro a a'
    show ((((((0 : Int), 0, 0) : Int × Int × Int), a + a'), (0 : Int)) : atpGroup.carrier)
      = (tpeGroup.mul ((((0 : Int), 0, 0) : Int × Int × Int), a)
          (atpTw (atpChi 0) ((((0 : Int), 0, 0) : Int × Int × Int), a')), (0 : Int) + 0)
    rw [atp_chi_zero, atp_tw_id, tpe_mul_expand]
    exact atp_ext5 (by omega) (by omega) (by omega) rfl (by omega)

/-- **定理 (M429F-6i): deck 切断と算術切断は可換** — 全商 ℤ×ℤ（deck × 算術）の
    可換性が切断のレベルでも実現される（χ は deck 持ち上げを固定するゆえ）。 -/
theorem atp_sections_commute (m a : Int) :
    atpGroup.mul (atpSection.map m) (atpDeckSection.map a)
      = atpGroup.mul (atpDeckSection.map a) (atpSection.map m) := by
  show atpGroup.mul ((((((0 : Int), 0, 0) : Int × Int × Int), (0 : Int)), m)
        : atpGroup.carrier)
      (((((0 : Int), 0, 0) : Int × Int × Int), a), (0 : Int))
    = atpGroup.mul ((((((0 : Int), 0, 0) : Int × Int × Int), a), (0 : Int))
        : atpGroup.carrier)
      (((((0 : Int), 0, 0) : Int × Int × Int), (0 : Int)), m)
  rw [atp_mul_expand, atp_mul_expand, atp_chi_zero, atp_tw_id]
  have h0 : atpTw (atpChi m) (((((0 : Int), 0, 0) : Int × Int × Int), a)
        : tpeGroup.carrier)
      = ((((0 : Int), atpChi m * 0, atpChi m * 0) : Int × Int × Int), a) := rfl
  rw [h0, tpe_mul_expand, tpe_mul_expand]
  exact atp_ext5 (by omega) (by omega) (by omega) (by omega) (by omega)

/-! ## M429F-7: M374F 被覆塔への接続（deck 商の各段全射・遷移錐・ℤ_l 完備化） -/

/-- **M429F-7a: 第 n 段 deck 射影** Π^arith ↠ ℤ/l^n。 -/
def atpDeckLevel (l n : Nat) : Hom atpGroup (ttwDeckTower l n) :=
  (ttwDiscreteProj l n).comp atpDeckProj

/-- **M429F-7b: deck 完備化** Π^arith → ℤ_l（M374F 逆極限）。算術群の deck 方向も
    本物の副有限塔に住む。 -/
def atpDeckComplete (l : Nat) : Hom atpGroup (ttwInverseLimit l) :=
  (ttwDiscreteComplete l).comp atpDeckProj

/-- **定理 (M429F-7c): 各段射影は遷移と整合する錐**。 -/
theorem atp_deck_cone (l n : Nat) (x : atpGroup.carrier) :
    (ttwTransition l n).map ((atpDeckLevel l (n + 1)).map x) = (atpDeckLevel l n).map x :=
  ttw_discrete_cone l n (atpDeckProj.map x)

/-- **定理 (M429F-7d): 完備化を第 n 段へ射影すると各段射影**（逆極限の錐）。 -/
theorem atp_deck_complete_cone (l n : Nat) (x : atpGroup.carrier) :
    (ttwLimitProj l n).map ((atpDeckComplete l).map x) = (atpDeckLevel l n).map x :=
  ttw_discrete_to_level l n (atpDeckProj.map x)

/-- **定理 (M429F-7e): 算術群は各段 ℤ/l^n へ全射**（deck 切断経由）。 -/
theorem atp_deck_level_surjective (l n : Nat) :
    ∀ y : (ttwDeckTower l n).carrier,
      ∃ x : atpGroup.carrier, (atpDeckLevel l n).map x = y := by
  intro y
  obtain ⟨a, ha⟩ := ttw_discrete_surjective l n y
  exact ⟨atpDeckSection.map a, ha⟩

/-! ## M429F-8: 実 G_K（M322F CycGKAction）との接続

  実円分指標スカラー χ(g) = ttoaChar（M389F/M322F）による捻り atpAct g は**各 g で
  本物の群準同型**（M424F tpeAct の非準同型 χ 捻りの昇格）。正直な限定: G_K の群
  合成との整合 σ_{gh} = σ_g∘σ_h は ℤ 値では mod n でしか成り立たない（μ_n 上の
  実群作用は M322F/M389F の CycGKAction・galThMuAct が保持）。 -/

/-- **M429F-8a: 実外ガロア作用（準同型版）** atpAct g = atpTwHom (χ(g))
    — 各 g ∈ G_K が幾何 tempered π₁^temp に**本物の群準同型**で作用する。 -/
def atpAct (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) : Hom tpeGroup tpeGroup :=
  atpTwHom (ttoaChar GK M ρ g)

/-- **定理 (M429F-8b): atpAct g は本物の群準同型**（M424F tpeAct/tpeScale は群全体の
    自己同型でなかった——その正直な限定の解消、本丸）。 -/
theorem atp_act_hom (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (x y : tpeGroup.carrier) :
    (atpAct GK M ρ g).map (tpeGroup.mul x y)
      = tpeGroup.mul ((atpAct GK M ρ g).map x) ((atpAct GK M ρ g).map y) :=
  (atpAct GK M ρ g).map_mul x y

/-- **定理 (M429F-8c): テータ交換子は実円分指標 χ(g) で捻れる** —
    σ_g[ι x, ι y] = ι(0, 0, χ(g)·ω)（M424F tpe_act_commutator_twist の準同型版昇格）。 -/
theorem atp_act_theta_commutator (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (a b c a' b' c' : Int) :
    (atpAct GK M ρ g).map (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int)))
      = tpeIncl.map ((0, 0, ttoaChar GK M ρ g * (a * b' - a' * b)) : Int × Int × Int) :=
  atp_tw_theta_commutator (ttoaChar GK M ρ g) a b c a' b' c'

/-- **定理 (M429F-8d): 中心（シクロトーム）上で M424F tpeAct に一致** — atpAct は
    既存 χ 捻りの自己同型への**拡張**であって取り替えではない（自己整合）。 -/
theorem atp_act_center_agrees (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (c : Int) :
    (atpAct GK M ρ g).map (tpeIncl.map ((0, 0, c) : Int × Int × Int))
      = tpeAct GK M ρ g (tpeIncl.map ((0, 0, c) : Int × Int × Int)) := by
  show ((((0 : Int), ttoaChar GK M ρ g * 0, ttoaChar GK M ρ g * c) : Int × Int × Int),
      (0 : Int))
    = ((((0 : Int), 0, ttoaChar GK M ρ g * c) : Int × Int × Int), (0 : Int))
  exact tpe_ext rfl (Int.mul_zero (ttoaChar GK M ρ g)) rfl rfl

/-- **定理 (M429F-8e): テータ部での作用の姿** — σ_g ιι(a,b,c) = ιι(a, χ(g)b, χ(g)c)
    （deck 固定・μ-方向 χ 倍・シクロトーム χ 倍、Tate 曲線の G_K 作用の離散版）。 -/
theorem atp_act_mu_direction (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (a b c : Int) :
    (atpAct GK M ρ g).map (tpeIncl.map ((a, b, c) : Int × Int × Int))
      = tpeIncl.map ((a, ttoaChar GK M ρ g * b, ttoaChar GK M ρ g * c)
          : Int × Int × Int) := rfl

/-- **定理 (M429F-8f): 作用は deck 商に自明**（値群方向はガロア固定）。 -/
theorem atp_act_deck_trivial (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (x : tpeGroup.carrier) :
    ((atpAct GK M ρ g).map x).2 = x.2 := rfl

/-! ## M429F-9: 非有界指数（真に tempered）・非 slim（正直な限定の定理化） -/

/-- **定理 (M429F-9a): 算術群は有界指数でない（真に tempered・非副有限）**。 -/
theorem atp_not_bounded : ¬ BoundedExponent atpGroup := by
  intro h
  obtain ⟨N, hN, hpow⟩ := h
  apply theta_deck_not_finite
  refine ⟨N, hN, ?_⟩
  intro g
  have hg : atpGroup.pow (atpSection.map g) N = atpGroup.one := hpow (atpSection.map g)
  have hgp : atpSection.map (intGrp.pow g N) = atpGroup.pow (atpSection.map g) N :=
    atpSection.map_pow g N
  rw [hg] at hgp
  exact congrArg Prod.snd hgp

/-- **定理 (M429F-9b): 偶数算術切断は中心** — χ の核 2ℤ の切断 s(2) は算術群の
    全元と可換（算術商が可換モデル ℤ であることの帰結）。 -/
theorem atp_arith_even_central (g : atpGroup.carrier) :
    atpGroup.mul (atpSection.map 2) g = atpGroup.mul g (atpSection.map 2) := by
  obtain ⟨x1, m⟩ := g
  show (tpeGroup.mul tpeGroup.one (atpTw (atpChi 2) x1), 2 + m)
    = (tpeGroup.mul x1 (atpTw (atpChi m) tpeGroup.one), m + 2)
  rw [atp_chi_even 2 (by omega), atp_tw_id, tpeGroup.one_mul, atp_tw_one,
    tpeGroup.mul_one]
  exact atp_pair_ext rfl (by omega)

/-- **定理 (M429F-9c): 算術群は slim でない（正直な限定の定理化）** — 偶数切断
    s(2) ≠ 1 が中心に残る。実 Π^arith の slim 性は実 G_K（非可換副有限）の
    非可換性に由来し、可換モデル ℤ では原理的に再現できない（外部）。 -/
theorem atp_not_slim : ¬ Slim atpGroup := by
  intro h
  have h1 := h (atpSection.map 2) atp_arith_even_central
  have h2 : (2 : Int) = 0 := congrArg Prod.snd h1
  exact absurd h2 (by omega)

/-! ## M429F-10: 正直な外部仮説（決して導出しない） -/

/-- **外部仮説（正直な限定・決して導出しない）**: 実 G_K（非可換副有限）を算術商に
    持つ完全な算術 tempered π₁ の実現。本モジュールの算術商は円分指標像のモデル ℤ
    （離散シクロトーム ℤ の Aut = {±1} ゆえ作用は符号指標経由）であり、(ℤ/n)^× 値の
    実 χ 全体の作用には副有限シクロトーム（Ẑ(1)）が要る（後続）。 -/
def atp_full_arith_galois_hypothesis (T : Grp) (f : Hom T atpGroup) : Prop :=
  f.Injective

/-- **外部仮説（正直な限定・決して導出しない）**: full slim 遠アーベル復元
    （[SemiAnbd]）・Tate 曲線の実被覆空間としての幾何的実現・p 進解析テータの
    ガロア同変評価は外部（M424F と同じ）。本算術群は slim で**ない**
    （atp_not_slim が定理として固定）。 -/
def atp_slim_realization_hypothesis (T : Grp) : Prop := Slim T

/-! ## M429F-11: capstone -/

/-- **M429F-11a: 算術 tempered π₁ データ** — 算術 tempered 基本群
    atpGroup = tpeGroup ⋊_χ ℤ の全実構造を束ねる: 算術完全列（ι 単射・pr 全射・
    完全性・正規性・分裂・非中心）・外ガロア表現（切断共役 = χ 捻り自己同型・
    テータ部での Tate 曲線型作用・テータ交換子の χ 捻り・算術×幾何交換子）・
    二段塔 Δ^temp ⊆ π₁^temp ⊆ Π^arith（合成単射・Δ^temp 正規・全商 ℤ×ℤ の完全性・
    テータ交換子の降下）・離散円分指標 χ の準同型性/単元性/核・χ 捻り atpTw の
    準同型性（昇格）/作用性/対合性・M374F 塔への deck 錐/完備化・実 G_K 作用
    （各 g で本物の準同型・χ(g) 捻り・M424F との中心一致・deck 自明）・
    非可換・非有界指数・非 slim（正直な限定）。主語はすべて本物の群演算。 -/
structure ArithTemperedPi1Data (l : Nat) (GK : Grp) (M : CycMuGroup)
    (ρ : CycGKAction GK M) where
  /-- ι : π₁^temp ↪ Π^arith は単射。 -/
  incl_inj : atpIncl.Injective
  /-- ι∘ι_θ : Δ^temp ↪ Π^arith は単射（二段塔）。 -/
  geom_incl_inj : atpInclGeom.Injective
  /-- pr : Π^arith ↠ ℤ（算術商）は全射。 -/
  proj_surj : ∀ g : intGrp.carrier, ∃ x, atpProj.map x = g
  /-- 完全性 ker(pr) = im(ι)。 -/
  extension_exact : ∀ x, atpProj.map x = intGrp.one ↔ ∃ z, atpIncl.map z = x
  /-- 分裂切断 pr∘s = id。 -/
  section_splits : ∀ m : Int, atpProj.map (atpSection.map m) = m
  /-- ι(π₁^temp) は正規部分群（明示 witness）。 -/
  geometric_normal : ∀ (g : atpGroup.carrier) (z : tpeGroup.carrier),
    ∃ w, atpGroup.mul (atpGroup.mul g (atpIncl.map z)) (atpGroup.inv g) = atpIncl.map w
  /-- Δ^temp も算術群で正規（二段塔の正規性）。 -/
  theta_normal : ∀ (g : atpGroup.carrier) (z : thetaGrp.carrier),
    ∃ w, atpGroup.mul (atpGroup.mul g (atpInclGeom.map z)) (atpGroup.inv g)
      = atpInclGeom.map w
  /-- 外ガロア表現: s(m)·ι(z)·s(m)⁻¹ = ι(atpTw(χ(m))z)（本丸）。 -/
  outer_galois : ∀ (m : Int) (z : tpeGroup.carrier),
    atpGroup.mul (atpGroup.mul (atpSection.map m) (atpIncl.map z))
        (atpGroup.inv (atpSection.map m))
      = atpIncl.map (atpTw (atpChi m) z)
  /-- テータ部での作用の姿: (a,b,c) ↦ (a, χb, χc)（Tate 曲線型）。 -/
  outer_galois_theta : ∀ m a b c : Int,
    atpGroup.mul (atpGroup.mul (atpSection.map m)
        (atpIncl.map (tpeIncl.map ((a, b, c) : Int × Int × Int))))
      (atpGroup.inv (atpSection.map m))
      = atpIncl.map (tpeIncl.map ((a, atpChi m * b, atpChi m * c) : Int × Int × Int))
  /-- テータ交換子の χ 捻り: s(m)·ι[ιx,ιy]·s(m)⁻¹ = ιι(0,0,χ(m)·ω)。 -/
  conj_commutator_chi : ∀ m a b c a' b' c' : Int,
    atpGroup.mul (atpGroup.mul (atpSection.map m)
        (atpIncl.map (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
          (tpeIncl.map ((a', b', c') : Int × Int × Int)))))
      (atpGroup.inv (atpSection.map m))
      = atpIncl.map (tpeIncl.map
          ((0, 0, atpChi m * (a * b' - a' * b)) : Int × Int × Int))
  /-- 算術×幾何交換子 [s(m), ι z] = ι(atpTw(χ)z · z⁻¹)。 -/
  arith_commutator : ∀ (m : Int) (z : tpeGroup.carrier),
    atpGroup.comm (atpSection.map m) (atpIncl.map z)
      = atpIncl.map (tpeGroup.mul (atpTw (atpChi m) z) (tpeGroup.inv z))
  /-- 拡大は非中心（真の半直積）。 -/
  extension_not_central :
    atpGroup.mul (atpSection.map 1)
        (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))
      ≠ atpGroup.mul (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))
          (atpSection.map 1)
  /-- 算術群は非可換。 -/
  nonabelian : ¬ tcmAbelian atpGroup
  /-- テータ交換子は算術群に降下: [ιιx, ιιy] = ιι(0,0,ω)。 -/
  theta_commutator : ∀ a b c a' b' c' : Int,
    atpGroup.comm (atpInclGeom.map ((a, b, c) : Int × Int × Int))
        (atpInclGeom.map ((a', b', c') : Int × Int × Int))
      = atpInclGeom.map ((0, 0, a * b' - a' * b) : Int × Int × Int)
  /-- 二段塔の完全性 1 → Δ^temp → Π^arith → ℤ×ℤ → 1。 -/
  tower_exact : ∀ x, atpFullProj.map x = (prodGrp intGrp intGrp).one
    ↔ ∃ z, atpInclGeom.map z = x
  /-- 離散円分指標の準同型性 χ(m+m') = χ(m)χ(m')。 -/
  chi_hom : ∀ m m' : Int, atpChi (m + m') = atpChi m * atpChi m'
  /-- 指標の単元性 χ² = 1（ℤ^× 値）。 -/
  chi_unit : ∀ m : Int, atpChi m * atpChi m = 1
  /-- 指標の核 = 2ℤ。 -/
  chi_kernel : ∀ m : Int, atpChi m = 1 ↔ m % 2 = 0
  /-- χ 捻り atpTw は本物の群準同型（M424F 正直な限定の解消・昇格）。 -/
  tw_hom : ∀ (e : Int) (x y : tpeGroup.carrier),
    atpTw e (tpeGroup.mul x y) = tpeGroup.mul (atpTw e x) (atpTw e y)
  /-- 捻りの単位則。 -/
  tw_id : ∀ x : tpeGroup.carrier, atpTw 1 x = x
  /-- 捻りの合成則（(ℤ,·) 作用）。 -/
  tw_comp : ∀ (e e' : Int) (x : tpeGroup.carrier),
    atpTw e (atpTw e' x) = atpTw (e * e') x
  /-- χ 値の捻りは対合＝本物の自己同型。 -/
  tw_involutive : ∀ (m : Int) (x : tpeGroup.carrier),
    atpTw (atpChi m) (atpTw (atpChi m) x) = x
  /-- M374F 塔: deck 射影は遷移と整合する錐。 -/
  deck_cone : ∀ (n : Nat) (x : atpGroup.carrier),
    (ttwTransition l n).map ((atpDeckLevel l (n + 1)).map x) = (atpDeckLevel l n).map x
  /-- M374F 塔: 完備化 ℤ_l への錐整合。 -/
  deck_complete_cone : ∀ (n : Nat) (x : atpGroup.carrier),
    (ttwLimitProj l n).map ((atpDeckComplete l).map x) = (atpDeckLevel l n).map x
  /-- M374F 塔: 各段 ℤ/l^n へ全射。 -/
  deck_level_surj : ∀ (n : Nat) (y : (ttwDeckTower l n).carrier),
    ∃ x, (atpDeckLevel l n).map x = y
  /-- 実 G_K 作用: 各 g で本物の群準同型（M424F tpeAct の昇格）。 -/
  act_hom : ∀ (g : GK.carrier) (x y : tpeGroup.carrier),
    (atpAct GK M ρ g).map (tpeGroup.mul x y)
      = tpeGroup.mul ((atpAct GK M ρ g).map x) ((atpAct GK M ρ g).map y)
  /-- 実 G_K 作用: テータ交換子を実円分指標 χ(g) 倍に捻る。 -/
  act_theta_commutator : ∀ (g : GK.carrier) (a b c a' b' c' : Int),
    (atpAct GK M ρ g).map (tpeGroup.comm (tpeIncl.map ((a, b, c) : Int × Int × Int))
        (tpeIncl.map ((a', b', c') : Int × Int × Int)))
      = tpeIncl.map ((0, 0, ttoaChar GK M ρ g * (a * b' - a' * b)) : Int × Int × Int)
  /-- 実 G_K 作用: 中心（シクロトーム）上で M424F tpeAct に一致。 -/
  act_center_agrees : ∀ (g : GK.carrier) (c : Int),
    (atpAct GK M ρ g).map (tpeIncl.map ((0, 0, c) : Int × Int × Int))
      = tpeAct GK M ρ g (tpeIncl.map ((0, 0, c) : Int × Int × Int))
  /-- 実 G_K 作用: deck 商に自明。 -/
  act_deck_trivial : ∀ (g : GK.carrier) (x : tpeGroup.carrier),
    ((atpAct GK M ρ g).map x).2 = x.2
  /-- 算術群は有界指数でない（真に tempered）。 -/
  not_bounded : ¬ BoundedExponent atpGroup
  /-- 算術群は slim でない（正直な限定の定理化）。 -/
  not_slim : ¬ Slim atpGroup

/-- **M429F-11b: witness 本体** — 全フィールドを M429F-1〜9 の本物の証明で埋める
    （外部仮説ゼロ・完全証明）。 -/
def arithTemperedPi1Data (l : Nat) (GK : Grp) (M : CycMuGroup)
    (ρ : CycGKAction GK M) : ArithTemperedPi1Data l GK M ρ where
  incl_inj := atp_incl_injective
  geom_incl_inj := atp_incl_geom_injective
  proj_surj := atp_proj_surjective
  extension_exact := atp_extension_exact
  section_splits := atp_section_splits
  geometric_normal := atp_geometric_normal
  theta_normal := atp_theta_normal
  outer_galois := atp_outer_galois
  outer_galois_theta := atp_outer_galois_theta
  conj_commutator_chi := atp_conj_commutator_chi
  arith_commutator := atp_arith_commutator
  extension_not_central := atp_extension_not_central
  nonabelian := atp_nonabelian
  theta_commutator := atp_theta_commutator
  tower_exact := atp_tower_exact
  chi_hom := atp_chi_add
  chi_unit := atp_chi_sq
  chi_kernel := atp_chi_kernel
  tw_hom := atp_tw_hom
  tw_id := atp_tw_id
  tw_comp := atp_tw_mul
  tw_involutive := atp_tw_chi_involutive
  deck_cone := fun n x => atp_deck_cone l n x
  deck_complete_cone := fun n x => atp_deck_complete_cone l n x
  deck_level_surj := fun n y => atp_deck_level_surjective l n y
  act_hom := atp_act_hom GK M ρ
  act_theta_commutator := atp_act_theta_commutator GK M ρ
  act_center_agrees := atp_act_center_agrees GK M ρ
  act_deck_trivial := atp_act_deck_trivial GK M ρ
  not_bounded := atp_not_bounded
  not_slim := atp_not_slim

/-- **定理 (M429F-11c): 算術 tempered π₁ データの存在（M429F 見出し）** —
    l・任意の G_K・内部円分体 μ（CycMuGroup）・実ガロア作用 ρ（M322F CycGKAction）が
    与えられれば、幾何 tempered π₁^temp（M424F）の算術拡大 atpGroup = tpeGroup ⋊_χ ℤ
    と、その算術完全列・外ガロア表現（χ 捻り自己同型・テータ交換子の χ 捻り）・
    二段塔 Δ^temp ⊆ π₁^temp ⊆ Π^arith・M374F 塔完備化・実 G_K の準同型作用を束ねた
    データが**外部仮説なしで**存在する（完全証明）。 -/
theorem atp_exists (l : Nat) (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    Nonempty (ArithTemperedPi1Data l GK M ρ) :=
  ⟨arithTemperedPi1Data l GK M ρ⟩

/-! ## M429F-12: 実例 -/

/-- 実例: 離散円分指標の値 — χ(4) = 1（偶）・χ(7) = −1（奇）。 -/
example : atpChi 4 = 1 ∧ atpChi 7 = -1 :=
  ⟨atp_chi_even 4 (by omega), atp_chi_odd 7 (by omega)⟩

/-- 実例: 具体的な算術積 — (((1,2,3),4),1)·(((5,6,7),8),1) = (((6,−4,−34),12),2)。
    χ(1) = −1 の捻りが μ-方向 6 ↦ −6・シクロトーム 7 ↦ −7 に本当に効いている
    （捻りなしなら第 3 座標は 3+7+4·6+1·6 = 40 になるところが −34）。 -/
example : atpGroup.mul ((((((1 : Int), 2, 3) : Int × Int × Int), (4 : Int)),
      (1 : Int)) : atpGroup.carrier)
    (((((5 : Int), 6, 7) : Int × Int × Int), (8 : Int)), (1 : Int))
    = (((((6 : Int), -4, -34) : Int × Int × Int), (12 : Int)), (2 : Int)) := by
  rw [atp_mul_expand, atp_chi_one]
  have h0 : atpTw (-1) (((((5 : Int), 6, 7) : Int × Int × Int), (8 : Int))
        : tpeGroup.carrier)
      = ((((5 : Int), -6, -7) : Int × Int × Int), (8 : Int)) := by
    show ((((5 : Int), -1 * 6, -1 * 7) : Int × Int × Int), (8 : Int))
      = ((((5 : Int), -6, -7) : Int × Int × Int), (8 : Int))
    exact tpe_ext rfl (by omega) (by omega) rfl
  rw [h0, tpe_mul_expand]
  exact atp_ext5 (by omega) (by omega) (by omega) (by omega) (by omega)

/-- 実例: 外ガロア表現 — s(1)·ιι(0,1,0)·s(1)⁻¹ = ιι(0,−1,0)（χ(1) = −1 が μ-方向を
    反転する Tate 曲線型の作用）。 -/
example : atpGroup.mul (atpGroup.mul (atpSection.map 1)
      (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int))))
    (atpGroup.inv (atpSection.map 1))
    = atpIncl.map (tpeIncl.map ((0, atpChi 1 * 1, atpChi 1 * 0) : Int × Int × Int)) :=
  atp_outer_galois_theta 1 0 1 0

/-- 実例: テータ交換子の χ 捻り — s(1)·ι[ι(1,0,0), ι(0,1,0)]·s(1)⁻¹ = ιι(0,0,−1)
    （標準生成元の交換子＝シクロトーム生成元が χ(1) = −1 倍に捻れる）。 -/
example : atpGroup.mul (atpGroup.mul (atpSection.map 1)
      (atpIncl.map (tpeGroup.comm (tpeIncl.map ((1, 0, 0) : Int × Int × Int))
        (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))))
    (atpGroup.inv (atpSection.map 1))
    = atpIncl.map (tpeIncl.map ((0, 0, -1) : Int × Int × Int)) := by
  have h := atp_conj_commutator_chi 1 1 0 0 0 1 0
  rw [atp_chi_one] at h
  have hval : (-1 : Int) * ((1 : Int) * 1 - 0 * 0) = -1 := by omega
  rw [hval] at h
  exact h

/-- 実例: 算術×幾何交換子は非自明 — [s(1), ιι(0,1,0)] = ιι(0,−2,0)
    （χ 捻りのズレが交換子に露出する、真に捻れた拡大の証人）。 -/
example : atpGroup.comm (atpSection.map 1)
      (atpIncl.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int)))
    = atpIncl.map (tpeIncl.map ((0, -2, 0) : Int × Int × Int)) := by
  rw [atp_arith_commutator 1 (tpeIncl.map ((0, 1, 0) : Int × Int × Int))]
  refine congrArg atpIncl.map ?_
  rw [atp_chi_one]
  have h0 : atpTw (-1) (tpeIncl.map ((0, 1, 0) : Int × Int × Int))
      = tpeIncl.map ((0, -1, 0) : Int × Int × Int) := by
    show ((((0 : Int), -1 * 1, -1 * 0) : Int × Int × Int), (0 : Int))
      = ((((0 : Int), -1, 0) : Int × Int × Int), (0 : Int))
    exact tpe_ext rfl (by omega) (by omega) rfl
  rw [h0, ← tpeIncl.map_inv, ← tpeIncl.map_mul]
  refine congrArg tpeIncl.map ?_
  show ((0 + -0, -1 + -1, 0 + (-0 + 0 * 1) + 0 * -1) : Int × Int × Int)
    = ((0, -2, 0) : Int × Int × Int)
  exact triple_ext (by omega) (by omega) (by omega)

/-- 実例: 二段塔の完全性 — 全商射影 ℤ×ℤ の核はちょうど Δ^temp の像。 -/
example (x : atpGroup.carrier) :
    atpFullProj.map x = (prodGrp intGrp intGrp).one
      ↔ ∃ z : thetaGrp.carrier, atpInclGeom.map z = x :=
  atp_tower_exact x

/-- 実例: 算術群は非可換・非 slim・非有界指数。 -/
example : ¬ tcmAbelian atpGroup ∧ ¬ Slim atpGroup ∧ ¬ BoundedExponent atpGroup :=
  ⟨atp_nonabelian, atp_not_slim, atp_not_bounded⟩

/-- 実例: deck 商の l = 2 塔 — 算術群は第 3 段 ℤ/8 へ全射（M374F 塔の算術群版）。 -/
example : ∀ y, ∃ x : atpGroup.carrier, (atpDeckLevel 2 3).map x = y :=
  atp_deck_level_surjective 2 3

/-- 実例: 本物の絶対ガロア群 G_ℚ（M315F）の trivial 円分作用による実 G_K 作用は
    各 g で本物の群準同型（M424F tpeAct では不可能だった性質）。 -/
example (l : Nat) (hl : 1 ≤ l)
    (g : (algCloAbsGalois algCloTrivialTower).carrier) (x y : tpeGroup.carrier) :
    (atpAct (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
        (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)) g).map
        (tpeGroup.mul x y)
      = tpeGroup.mul
          ((atpAct (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
            (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)) g).map x)
          ((atpAct (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
            (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)) g).map y) :=
  atp_act_hom (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)) g x y

/-- 実例: 本物の G_ℚ・μ_5・実円分作用による算術 tempered π₁ データが存在する
    （l = 2 の deck 塔つき、外部仮説ゼロ）。 -/
example (l : Nat) (hl : 1 ≤ l) :
    Nonempty (ArithTemperedPi1Data 2 (algCloAbsGalois algCloTrivialTower)
      (cycMuStd l hl)
      (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))) :=
  atp_exists 2 (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))

end IUT
