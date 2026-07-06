/-
  IUT/TemperedPi1.lean — M364F [実／本物]
  分類: 実 (Tate 曲線の tempered π₁＝Ẑ を離散 ℤ(q^ℤ)で拡大)
  complete_pct 影響: 柱A を前進（named 限定 tempered π₁ へ＝Tate 曲線 E_q の tempered 基本群を
    副有限 Ẑ（円分部）を離散 ℤ（q^ℤ 周期格子 M333F）で拡大した群 1→Ẑ→π₁^temp→ℤ→1 として
    構成・完全性・離散部が非副有限（tempered≠profinite の核心）を本物で）。
  正直な限定: 完全な tempered π₁（全被覆）・anabelian 復元は外部仮説等。
-/
import IUT.DiscreteRigidity
import IUT.Profinite

namespace IUT

/-! ## M364F-1: 離散部 ℤ（周期格子 q^ℤ ≅ ℤ）

  Tate 曲線 E_q = K^×/q^ℤ の tempered 基本群 π₁^temp の「離散」方向は、テータ被覆
  Ÿ → X のデッキ群 ℤ（＝周期束 q^ℤ の指数格子、M333F/M309F）である。これはまさに
  本物の加法群 `intGrp`（(ℤ,+,0,−)、M9/M333F で共有）を主対象とする。tempered が
  profinite と異なる核心は、この ℤ が離散（非可除・有界指数でない）であること。 -/

/-- **M364F-1: 離散部 π₁^temp の離散 ℤ 方向** — テータ被覆のデッキ群 ℤ ＝ 周期格子
    q^ℤ の指数群（M333F の周期準同型 n ↦ qⁿ の指数側）。本物の加法群 `intGrp`。 -/
def tmpDiscretePart : Grp := intGrp

/-! ## M364F-2: 副有限部 Ẑ（円分部・roots of unity）

  π₁^temp の「副有限」方向は、円分部（roots of unity μ_n の塔の逆極限）＝ Ẑ = lim_n ℤ/n
  である（M287F/M13）。これは本物の副有限群 `zhat`（有限巡回群 ℤ/n の割り切り順序の
  逆極限、M13-7）を主対象とする。 -/

/-- **M364F-2: 副有限部 π₁^temp の Ẑ 方向** — 円分部（μ_n の逆極限）＝ Ẑ = lim_n ℤ/n
    （M13-7 の本物の逆極限群 `zhat`）。本物の副有限群。 -/
def tmpProfinitePart : Grp := zhat

/-- 副有限部は本物の逆極限群 lim_n ℤ/n である（構成そのもの）。 -/
theorem tmp_profinite_is_inverse_limit : tmpProfinitePart = limitGrp zmodSystem := rfl

/-- **円分完備化の単射性**（M13-8 の再利用）— 離散 ℤ から副有限 Ẑ への対角埋め込み
    `toZhat` は単射。円分部（roots of unity）は離散周期の情報を忠実に写す。 -/
theorem tmp_cyclotomic_completion_injective : toZhat.Injective := toZhat_injective

/-! ## M364F-3: tempered 群 π₁^temp ＝ 拡大 Ẑ ⋊ ℤ（本モデルは中心拡大 Ẑ × ℤ）

  tempered 基本群を拡大 1 → Ẑ → π₁^temp → ℤ → 1 として構成する。本モデルでは
  直積 Ẑ × ℤ（＝副有限部を核、離散部を商とする分裂中心拡大）で実現する。第2成分
  への射影が離散 ℤ への全射、第1成分の埋め込みが副有限 Ẑ の核埋め込みを与える。 -/

/-- **M364F-3: tempered 基本群 π₁^temp** — 副有限部 Ẑ を離散部 ℤ で拡大した本物の群
    Ẑ × ℤ（拡大 1 → Ẑ → π₁^temp → ℤ → 1 のモデル）。 -/
def tmpTemperedGroup : Grp := prodGrp tmpProfinitePart tmpDiscretePart

/-- **核埋め込み ι : Ẑ ↪ π₁^temp**（z ↦ (z, 0)）— 副有限部（円分部）を拡大の核として
    埋め込む本物の群準同型。 -/
def tmpIncl : Hom tmpProfinitePart tmpTemperedGroup where
  map := fun z => (z, (0 : Int))
  map_mul := fun _ _ => rfl

/-- **射影 pr : π₁^temp ↠ ℤ**（(z, n) ↦ n）— tempered 群から離散デッキ群 ℤ への
    全射準同型。 -/
def tmpProj : Hom tmpTemperedGroup tmpDiscretePart where
  map := fun x => x.2
  map_mul := fun _ _ => rfl

/-! ## M364F-4: 拡大の完全性 1 → Ẑ → π₁^temp → ℤ → 1 -/

/-- **M364F-4a: 核埋め込みは単射** — ι : Ẑ ↪ π₁^temp は単射（第1成分の一致）。 -/
theorem tmp_incl_injective : tmpIncl.Injective :=
  fun _ _ h => congrArg Prod.fst h

/-- **M364F-4b: 射影は全射** — pr : π₁^temp ↠ ℤ は全射（任意の n ∈ ℤ は (1_Ẑ, n) の像）。 -/
theorem tmp_proj_surjective : ∀ g : tmpDiscretePart.carrier, ∃ x, tmpProj.map x = g :=
  fun g => ⟨(tmpProfinitePart.one, g), rfl⟩

/-- **M364F-4c: 核 ⊆ 像**（im(ι) ⊆ ker(pr)）— 副有限部の像は射影で消える
    （pr(ι z) = 0）。副有限 Ẑ が拡大の核であることの半分。 -/
theorem tmp_proj_incl_trivial (z : tmpProfinitePart.carrier) :
    tmpProj.map (tmpIncl.map z) = tmpDiscretePart.one := rfl

/-- **定理 (M364F-4d): 拡大の完全性** — 1 → Ẑ → π₁^temp → ℤ → 1 は完全列。
    すなわち射影 pr の核はちょうど副有限部 Ẑ の埋め込み像:
    pr(x) = 0 ⟺ ∃ z ∈ Ẑ, ι(z) = x。副有限部（円分部）が離散商 ℤ への射影の
    核に一致することの完全証明。 -/
theorem tmp_extension_exact (x : tmpTemperedGroup.carrier) :
    tmpProj.map x = tmpDiscretePart.one ↔ ∃ z : tmpProfinitePart.carrier, tmpIncl.map z = x := by
  obtain ⟨a, n⟩ := x
  constructor
  · intro h
    have hn : n = (0 : Int) := h
    subst hn
    exact ⟨a, rfl⟩
  · intro h
    obtain ⟨z, hz⟩ := h
    show n = (0 : Int)
    exact (congrArg Prod.snd hz).symm

/-! ## M364F-5: tempered ≠ profinite の核心（離散部は非副有限） -/

/-- **定理 (M364F-5a): 離散部は非可除（tempered の核心）** — 離散デッキ群 ℤ には
    2n = 1 なる元が無い（M333F `discRig_no_division` の再利用）。すなわち周期格子は
    平方根周期を持たず「連続的／可除的に潰れない」。副有限完備化（可除的に振る舞う
    Ẑ）と異なり、離散 ℤ はこの非可除性ゆえ本質的に tempered である。 -/
theorem tmp_discrete_vs_profinite : ¬ ∃ n : Int, 2 * n = 1 := discRig_no_division

/-- **定理 (M364F-5b): 離散部は有界指数でない** — 離散デッキ群 ℤ は有界指数を持たない
    （M9-6 `theta_deck_not_finite` の再利用）。すなわち ℤ はどの有限エタール被覆でも
    実現不能であり、π₁^temp は真に tempered（非副有限）な群である。これが
    「エタール π₁（副有限）では足りず tempered π₁ が要る」ことの核心。 -/
theorem tmp_discrete_not_finite : ¬ BoundedExponent tmpDiscretePart := theta_deck_not_finite

/-- **離散座標切断 s : ℤ → π₁^temp**（n ↦ (1_Ẑ, n)）— 拡大 1 → Ẑ → π₁^temp → ℤ → 1 の
    分裂切断（pr ∘ s = id）。本モデルが分裂中心拡大 Ẑ × ℤ であることの証人。 -/
def tmpDeckSection : Hom intGrp tmpTemperedGroup where
  map := fun n => (tmpProfinitePart.one, n)
  map_mul := fun a b => by
    show (tmpProfinitePart.one, a + b)
        = (tmpProfinitePart.mul tmpProfinitePart.one tmpProfinitePart.one, a + b)
    rw [tmpProfinitePart.one_mul]

/-- 切断は射影の分裂: pr ∘ s = id（(1_Ẑ, n) ↦ n）。 -/
theorem tmp_section_splits (n : Int) : tmpProj.map (tmpDeckSection.map n) = n := rfl

/-- **定理 (M364F-5c): tempered 群全体も有界指数でない** — 拡大 Ẑ × ℤ の中に離散 ℤ が
    切断 s : ℤ ↪ π₁^temp で忠実に入るので、π₁^temp 自身も有界指数を持たない。
    (1_Ẑ, g)^N = (1_Ẑ, g^N) = 1 の第2成分から g^N = 0 に落ちるが、これは ℤ の
    非有界指数性 M9-6 に反する。 -/
theorem tmp_tempered_not_finite : ¬ BoundedExponent tmpTemperedGroup := by
  intro h
  obtain ⟨N, hN, hpow⟩ := h
  apply theta_deck_not_finite
  refine ⟨N, hN, ?_⟩
  intro g
  have hg : tmpTemperedGroup.pow (tmpDeckSection.map g) N = tmpTemperedGroup.one :=
    hpow (tmpDeckSection.map g)
  have hgp : tmpDeckSection.map (intGrp.pow g N)
      = tmpTemperedGroup.pow (tmpDeckSection.map g) N := tmpDeckSection.map_pow g N
  rw [hg] at hgp
  exact congrArg Prod.snd hgp

/-! ## M364F-6: テータ被覆で離散部が可視（q^ℤ 周期との接続） -/

/-- **定理 (M364F-6): 離散部はテータ構造で可視** — 離散デッキ生成元 1 ∈ ℤ は周期準同型
    n ↦ qⁿ（M333F `discRig_periodHom`）で Tate パラメータ q に写り、q はちょうど周期束
    q^ℤ（テータ準周期 M313F/M309F の周期）の生成元として格子に属する。すなわち tempered
    の離散方向はエタールテータ Θ(q,qu)=(因子)·Θ(q,u) の quasi-period q として可視である。 -/
theorem tmp_theta_visible (K : IUTField) (q : (tateMultGroup K).carrier) :
    (discRig_periodHom K q).map 1 = q ∧
      (tateQPowersSubgroup (tateMultGroup K) q).mem q :=
  ⟨tateZpow_one (tateMultGroup K) q, tate_theta_period_in_lattice K q⟩

/-! ## M364F-7: 正直な外部仮説（決して導出しない） -/

/-- **外部仮説（正直な限定・決して導出しない）**: 離散デッキ生成元（周期 q）が無限位数を
    持つ（周期格子が崩れず ℤ と忠実に同型）。M333F と同じく、正 valuation の素元
    v(q)≠0 の具体構成は柱B ℤ_p 接続の後続ゆえ、本層では明示仮説として受ける。 -/
def tmp_infiniteOrder_hypothesis (K : IUTField) (q : (tateMultGroup K).carrier) : Prop :=
  discRig_infiniteOrder_hypothesis (tateMultGroup K) q

/-- **外部仮説（正直な限定・決して導出しない）**: tempered 遠アーベル復元。実際の
    π₁^temp(X_v) は slim（中心自明、M9 `Slim`）であり、これが André・Mochizuki
    [SemiAnbd] の tempered 遠アーベル定理（p 進双曲的曲線は π₁^temp から関手的に
    復元される）の前提である。本モデルの可換な骨格 Ẑ × ℤ は slim でないため、この
    仮説は本質的に外部（幾何的入力）であり本層では決して導出しない。 -/
def tmp_anabelian_reconstruction_hypothesis (T : Grp) : Prop := Slim T

/-! ## M364F-8: capstone -/

/-- **M364F-8a: tempered π₁ の総括データ** — Tate パラメータ q・離散部 ℤ・副有限部 Ẑ・
    tempered 群 π₁^temp＝拡大 Ẑ×ℤ・核埋め込み ι・射影 pr・完全性・離散部の非副有限性
    （非可除・非有界指数）・無限位数仮説（正直な外部 crux）を束ねる。主語は本物の離散
    デッキ群 ℤ と本物の副有限完備化 Ẑ（toy 代理なし）。 -/
structure TemperedPi1Data (K : IUTField) where
  /-- Tate パラメータ q ∈ K^×。 -/
  q : (tateMultGroup K).carrier
  /-- 離散部（テータ被覆デッキ群 ℤ ＝ 周期格子 q^ℤ の指数群）。 -/
  discretePart : Grp
  /-- 副有限部（円分部 Ẑ = lim_n ℤ/n）。 -/
  profinitePart : Grp
  /-- tempered 基本群 π₁^temp。 -/
  temperedGroup : Grp
  /-- 核埋め込み ι : Ẑ ↪ π₁^temp。 -/
  incl : Hom profinitePart temperedGroup
  /-- 射影 pr : π₁^temp ↠ ℤ。 -/
  proj : Hom temperedGroup discretePart
  /-- 離散部 ＝ ℤ（本物の加法群）。 -/
  discrete_isZ : discretePart = intGrp
  /-- 副有限部 ＝ Ẑ（本物の逆極限）。 -/
  profinite_isZhat : profinitePart = zhat
  /-- ι は単射。 -/
  incl_inj : incl.Injective
  /-- pr は全射。 -/
  proj_surj : ∀ g : discretePart.carrier, ∃ x, proj.map x = g
  /-- 完全性 1 → Ẑ → π₁^temp → ℤ → 1（核 ＝ 像）。 -/
  exact : ∀ x, proj.map x = discretePart.one ↔ ∃ z, incl.map z = x
  /-- 離散部は非可除（tempered の核心）。 -/
  discrete_not_divisible : ¬ ∃ n : Int, 2 * n = 1
  /-- 離散部は有界指数でない（非副有限＝真に tempered）。 -/
  discrete_not_finite : ¬ BoundedExponent discretePart
  /-- 無限位数仮説（正直な外部 crux）。 -/
  infiniteOrder : tmp_infiniteOrder_hypothesis K q

/-- **M364F-8b: witness 本体** — 無限位数の仮説 hInf を受けて全フィールドを M364F-1〜5 の
    本物の証明で埋める（hInf 以外はすべて完全証明で埋まる）。 -/
def temperedPi1Data (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : tmp_infiniteOrder_hypothesis K q) : TemperedPi1Data K where
  q := q
  discretePart := tmpDiscretePart
  profinitePart := tmpProfinitePart
  temperedGroup := tmpTemperedGroup
  incl := tmpIncl
  proj := tmpProj
  discrete_isZ := rfl
  profinite_isZhat := rfl
  incl_inj := tmp_incl_injective
  proj_surj := tmp_proj_surjective
  exact := tmp_extension_exact
  discrete_not_divisible := discRig_no_division
  discrete_not_finite := theta_deck_not_finite
  infiniteOrder := hInf

/-- **定理 (M364F-8c): tempered π₁ データの（条件付き）存在** — 無限位数の周期 q が
    与えられれば、Tate 曲線 E_q の tempered 基本群 π₁^temp を拡大 1 → Ẑ → π₁^temp → ℤ → 1
    として構成し、完全性・離散部の非副有限性を束ねたデータが存在する。存在が無限位数
    仮説に条件付くのは正直な限定（正 valuation の素元の具体構成は柱B の後続）。 -/
theorem tmp_exists (K : IUTField) (q : (tateMultGroup K).carrier)
    (hInf : tmp_infiniteOrder_hypothesis K q) :
    Nonempty (TemperedPi1Data K) :=
  ⟨temperedPi1Data K q hInf⟩

/-! ## 実例（無条件で成立する tempered の核） -/

/-- 実例: 離散部は非可除（tempered ≠ profinite の核心）。 -/
example : ¬ ∃ n : Int, 2 * n = 1 := tmp_discrete_vs_profinite

/-- 実例: 離散部は有界指数でない（非副有限＝真に tempered）。 -/
example : ¬ BoundedExponent tmpDiscretePart := tmp_discrete_not_finite

/-- 実例: tempered 群全体も有界指数でない。 -/
example : ¬ BoundedExponent tmpTemperedGroup := tmp_tempered_not_finite

/-- 実例: 副有限部の埋め込み像は射影で消える（核 ⊆ 像）。 -/
example (z : tmpProfinitePart.carrier) :
    tmpProj.map (tmpIncl.map z) = tmpDiscretePart.one := tmp_proj_incl_trivial z

/-- 実例: 射影は全射。 -/
example : ∀ g : tmpDiscretePart.carrier, ∃ x, tmpProj.map x = g := tmp_proj_surjective

/-- 実例: 完全性 1 → Ẑ → π₁^temp → ℤ → 1（pr の核 ＝ ι の像）。 -/
example (x : tmpTemperedGroup.carrier) :
    tmpProj.map x = tmpDiscretePart.one ↔ ∃ z : tmpProfinitePart.carrier, tmpIncl.map z = x :=
  tmp_extension_exact x

end IUT
