/-
  IUT/Q3TemperedPi1.lean — A5b（柱A A5: 実 pro-3 tempered π₁^{temp,(3)}(E_q) = ℤ₃(1) × ℤ）

  ── 主要成果の分類: **[実／昇格(a)]**。M364F `TemperedPi1.lean` の tempered 群模型
     `tmpTemperedGroup = Ẑ × ℤ`（副有限部が抽象 Ẑ = zhat・離散部が実曲線未接続の裸の ℤ）
     の**両成分**を実部品に置換する: profinite 側は **A7b の実 ℤ₃(1) = tmzLimit**（実円分体
     内の実 μ_{3^{n+1}} 塔の逆極限・遷移＝実 cube 写像）、離散側は **A5a の実 Tate 被覆
     ℚ₃^× → E_q(ℚ₃) のデッキ群 q^ℤ ≅ ℤ**（q3tdPeriodHom で実 q^ℤ ⊂ 実 ℚ₃^× と同定）。
     さらに M364F `tmp_exists` の条件節（外部仮説 hInf = `tmp_infiniteOrder_hypothesis`）を、
     実主語 q3tGrp・q3tQ m の上では **q3td_infinite_order で無条件に discharge** し、存在を
     入力仮説ゼロで成立させる（M364F 条件付き存在に対する質的前進）。実 Gal(ℚ(ζ_{3^∞})/ℚ)
     の作用 tmzActHom（A7b・χ 冪）を profinite 部分に載せ、離散デッキ部分を固定する
     算術 π₁ 標準形の実 Galois 作用も構成する。toy 主語なし——主語は実 tmzLimit（実 ℤ₃(1)）・
     実 q3tGrp・実 q3tQ m・実射影 q3tProj m。

  complete_pct 影響: **A5 0.1→0.15（見込み・独立監査確定が条件）**。内容:
  (i)   実 pro-3 tempered 群 q3tpGroup = tmzLimit × intGrp（両成分実）と完全列
        1 → ℤ₃(1) → π₁^{(3)} → ℤ → 1（q3tp_incl_injective・q3tp_proj_surjective・
        q3tp_extension_exact）——M364F の ẑ×ℤ 完全列の実成分版、
  (ii)  離散商 ℤ の実 Tate 被覆デッキ実現 q3tpDeckRealize = q3tdPeriodHom ∘ q3tpProj
        （(z,n)↦qⁿ）・像⊆核（q3tp_deck_realize_ker）・忠実性（q3tp_deck_faithful）、
  (iii) **旗艦**: M364F 条件付き存在の無条件化 q3tp_exists_unconditional（外部仮説 hInf 不要・
        infinite_order を q3td_infinite_order で充填）、
  (iv)  実 Gal(ℚ(ζ_{3^∞})/ℚ) 作用 q3tpGalAct（profinite 部分に tmzActHom・離散部分固定）・
        deck 固定（q3tp_gal_act_deck_trivial）・μ 部分の実 χ 倍（q3tp_gal_act_mu）、
  (v)   束ね Q3TemperedPi1Data / q3tpData（q=3 見出し実例・m=1）/ q3tp_exists_unconditional。

  正直な限定（§4 末 (1)-(5) 準拠・消去/弱化しない・既存 surrogate は消さない）:
  (1) profinite 側は **pro-3 部分のみ**（本物の ẑ(1)=lim_n μ_n 全体は全 n 円分塔が必要・
      p=3 恒久限定と衝突するため pro-3 で正直に主張する）。
  (2) compact E_q の **可換** tempered のみ——IUT 本丸の punctured 曲線の**非可換** θ 拡大
      （tpeGroup/atpGroup の実化・Heisenberg シクロトーム構造）は範囲外。
  (3) ℤ₃(1) は円分側（Tate 加群の μ 成分）——幾何的 T₃(E_q) の q^{1/3^n} 成分
      （w=q^{1/2} の A8b 系列一般化）との 2 成分拡大は未構成。
  (4) Gal は円分切片 Gal(ℚ(ζ_{3^∞})/ℚ)（実 G_{ℚ₃} 全体でない）。
  (5) 位相・解析構造なし・p = 3 固定。
  (6) 既存 M364F の仮説付き機構（TemperedPi1Data K・tmp_exists・tmp_infiniteOrder_hypothesis）
      は消さず併設する（§2(a) 昇格の規約）。q3Ring は IUTField を持たない（A2 恒久限定・
      choice-free 裏取り済み）ため M364F TemperedPi1Data K を直接インスタンス化できず、
      Grp 主語の新 structure Q3TemperedPi1Data を立てて実部品で充填する。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3TateDeck
import IUT.TemperedPi1
import IUT.TateModuleZ3
import IUT.CyclotomicTowerLimit

namespace IUT

/-! ## q3tp-1: pro-3 tempered 群と完全列 1 → ℤ₃(1) → π₁^{(3)} → ℤ → 1

  M364F `tmpTemperedGroup = prodGrp zhat intGrp`（副有限部が抽象 Ẑ）の Ẑ を、
  A7b の**実 ℤ₃(1) = tmzLimit**（実円分 μ の逆極限）に置換した実成分版。
  compact Tate 曲線の tempered π₁ は可換（≅ ẑ(1)×ℤ）なので直積は群構造として忠実。 -/

/-- **q3tp-1（★）: 実 pro-3 tempered 模型** π₁^{temp,(3)}(E_q) = ℤ₃(1) × ℤ。
    副有限（pro-3）部分は実 ℤ₃(1) = tmzLimit、離散部分は実デッキ群 ℤ = intGrp。 -/
def q3tpGroup : Grp := prodGrp tmzLimit intGrp

/-- **核埋め込み ι : ℤ₃(1) ↪ π₁^{(3)}**（z ↦ (z, 0)）— pro-3 円分部分を拡大の核として
    埋め込む本物の群準同型（M364F tmpIncl の実成分版）。 -/
def q3tpIncl : Hom tmzLimit q3tpGroup where
  map := fun z => (z, (0 : Int))
  map_mul := fun _ _ => rfl

/-- **射影 pr : π₁^{(3)} ↠ ℤ**（(z, n) ↦ n）— tempered 群から実デッキ群 ℤ への
    全射準同型（M364F tmpProj の実成分版）。 -/
def q3tpProj : Hom q3tpGroup intGrp where
  map := fun x => x.2
  map_mul := fun _ _ => rfl

/-- **q3tp-1a: 核埋め込みは単射** — ι : ℤ₃(1) ↪ π₁^{(3)} は単射（第1成分の一致）。 -/
theorem q3tp_incl_injective : q3tpIncl.Injective :=
  fun _ _ h => congrArg Prod.fst h

/-- **q3tp-1b: 射影は全射** — pr : π₁^{(3)} ↠ ℤ は全射（任意 n は (1_{ℤ₃(1)}, n) の像）。 -/
theorem q3tp_proj_surjective : ∀ g : intGrp.carrier, ∃ x, q3tpProj.map x = g :=
  fun g => ⟨(tmzLimit.one, g), rfl⟩

/-- **q3tp-1c: 核 ⊆ 像**（im(ι) ⊆ ker(pr)）— pro-3 部分の像は射影で消える。 -/
theorem q3tp_proj_incl_trivial (z : tmzLimit.carrier) :
    q3tpProj.map (q3tpIncl.map z) = intGrp.one := rfl

/-- **q3tp-1d（★）: 拡大の完全性** — 1 → ℤ₃(1) → π₁^{(3)} → ℤ → 1 は完全列。
    射影 pr の核はちょうど pro-3 部分 ℤ₃(1) の埋め込み像:
    pr(x) = 0 ⟺ ∃ z ∈ ℤ₃(1), ι(z) = x。M364F tmp_extension_exact の実成分版
    （成分計算の構造は同型）。 -/
theorem q3tp_extension_exact (x : q3tpGroup.carrier) :
    q3tpProj.map x = intGrp.one ↔ ∃ z : tmzLimit.carrier, q3tpIncl.map z = x := by
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

/-! ## q3tp-2: 離散商の実 Tate 被覆デッキ実現（A5a の消費・本モジュールの核）

  離散商 ℤ ＝ 実 Tate 被覆のデッキ群。q3tpProj の値域 ℤ を q3tdPeriodHom
  （単射・像＝ker(q3tProj)）を通じて実 q^ℤ ⊂ 実 ℚ₃^× と同定する。合成
  q3tpGroup → ℤ → ℚ₃^× は準同型で、像 ⊆ 実被覆 q3tProj の核。 -/

/-- **q3tp-2a（★）: 離散商 ℤ の実被覆デッキ実現** — (z,n) ↦ qⁿ。
    q3tdPeriodHom（実周期準同型 t↦qᵗ）と q3tpProj（(z,n)↦n）の合成。 -/
def q3tpDeckRealize (m : Nat) : Hom q3tpGroup q3tGrp :=
  (q3tdPeriodHom m).comp q3tpProj

/-- **q3tp-2b（★）: 像 ⊆ 実被覆の核** — qⁿ ∈ q^ℤ = ker(q3tProj) ゆえ
    q3tProj(q3tpDeckRealize x) = 1_{E_q}。実デッキ実現が確かに被覆 ℚ₃^× → E_q の
    核（周期格子 q^ℤ）へ落ちることの証明。 -/
theorem q3tp_deck_realize_ker (m : Nat) (hm : 1 ≤ m) (x : q3tpGroup.carrier) :
    (q3tProj m).map ((q3tpDeckRealize m).map x) = (q3tCurve m).one :=
  (q3td_ker m ((q3tpDeckRealize m).map x)).mpr ⟨x.2, rfl⟩

/-- **q3tp-2c（★）: デッキ実現の忠実性** — 周期準同型 t↦qᵗ は単射（q^ℤ ≅ ℤ）。
    離散商 ℤ が実 q^ℤ に忠実に同定される（A5a q3td_period_inj の再輸出）。 -/
theorem q3tp_deck_faithful (m : Nat) (hm : 1 ≤ m) :
    ∀ a b : Int, (q3tdPeriodHom m).map a = (q3tdPeriodHom m).map b → a = b :=
  q3td_period_inj m hm

/-! ## q3tp-3: 実 Gal(ℚ(ζ_{3^∞})/ℚ) の作用（A7b tmzActHom の消費）

  arithmetic tempered π₁ の標準形: profinite（μ=ℤ₃(1)）方向には実 Galois 作用
  tmzActHom s（χ 冪）、離散デッキ（値群 ℤ）方向には自明作用（deck/値群方向固定・
  μ 方向 χ 倍）。M429F atpTw と同じ形。成分ごとの積で q3tpGroup 全体の実自己準同型。 -/

/-- **q3tp-3（★）: 実 Gal(ℚ(ζ_{3^∞})/ℚ) の作用** — s ∈ ctlProfinite に対し
    profinite 部分 ℤ₃(1) には実作用 tmzActHom s（χ 冪）、離散デッキ部分 ℤ には
    自明作用を施す群自己準同型 π₁^{(3)} → π₁^{(3)}。 -/
def q3tpGalAct (s : ctlProfinite.carrier) : Hom q3tpGroup q3tpGroup where
  map := fun x => ((tmzActHom s).map x.1, x.2)
  map_mul := fun x y => by
    show ((tmzActHom s).map (tmzLimit.mul x.1 y.1), intGrp.mul x.2 y.2)
        = (tmzLimit.mul ((tmzActHom s).map x.1) ((tmzActHom s).map y.1), intGrp.mul x.2 y.2)
    rw [(tmzActHom s).map_mul]

/-- **q3tp-3a: 離散デッキ部分は固定** — Gal 作用は離散（値群 ℤ）方向を動かさない。 -/
theorem q3tp_gal_act_deck_trivial (s : ctlProfinite.carrier) (x : q3tpGroup.carrier) :
    ((q3tpGalAct s).map x).2 = x.2 := rfl

/-- **q3tp-3b: μ 部分は実 χ 冪で作用** — Gal 作用の pro-3 円分（μ=ℤ₃(1)）方向は
    実 Galois 作用 tmzActHom s（χ 冪・A7b）で与えられる。 -/
theorem q3tp_gal_act_mu (s : ctlProfinite.carrier) (x : q3tpGroup.carrier) :
    ((q3tpGalAct s).map x).1 = (tmzActHom s).map x.1 := rfl

/-- **q3tp-3c: 単位元 Gal の作用は恒等** — s = 1 では作用は id（tmzGModule.act_one の消費）。 -/
theorem q3tp_gal_act_one (x : q3tpGroup.carrier) :
    (q3tpGalAct ctlProfinite.one).map x = x := by
  obtain ⟨a, n⟩ := x
  have h1 : (tmzActHom ctlProfinite.one).map a = a := tmzGModule.act_one a
  show ((tmzActHom ctlProfinite.one).map a, n) = (a, n)
  rw [h1]

/-! ## q3tp-4: tempered 核の継承（離散部は非副有限＝真に tempered） -/

/-- **q3tp-4: 離散デッキ部分は有界指数でない**（M364F/M9 theta_deck_not_finite の再利用）—
    実デッキ群 ℤ はどの有限エタール被覆でも実現不能で、π₁^{(3)} は真に tempered
    （非副有限）。「エタール π₁ では足りず tempered π₁ が要る」核心を実主語で継承。 -/
theorem q3tp_discrete_not_finite : ¬ BoundedExponent intGrp := theta_deck_not_finite

/-! ## q3tp-5: capstone — 実 pro-3 tempered π₁ データ（無条件存在）

  q3Ring は IUTField を持たない（A2 恒久限定）ため M364F TemperedPi1Data K を直接
  インスタンス化できない。Grp 主語の新 structure を立てて実部品で充填する。
  M364F との質的差: infinite_order フィールドは外部仮説 hInf でなく
  q3td_infinite_order（実主語上の定理）で**無条件に**埋まる。 -/

/-- **q3tp-5a: 実 pro-3 tempered π₁ 総括データ** — 実 pro-3 tempered 群
    π₁^{temp,(3)}(E_q)=ℤ₃(1)×ℤ（両成分実）・核埋め込み ι・射影 pr・完全列・
    離散部の非副有限性・実 Tate 被覆デッキ実現（像⊆核・忠実）・**無条件**無限位数
    （M333F/M364F 外部仮説の実 discharge）を束ねる。主語は実 tmzLimit（実 ℤ₃(1)）・
    実 q3tGrp・実 q=3^m（toy 代理なし）。 -/
structure Q3TemperedPi1Data where
  /-- Tate パラメータの指数 m（q = 3^m）。 -/
  m : Nat
  /-- m ≥ 1（真の退化パラメータ）。 -/
  hm : 1 ≤ m
  /-- pro-3 円分部分（実 ℤ₃(1) = lim μ_{3^{n+1}}）。 -/
  profinitePart : Grp
  /-- 離散デッキ部分（実 Tate 被覆デッキ群 ℤ）。 -/
  discretePart : Grp
  /-- 実 pro-3 tempered 群 π₁^{temp,(3)}。 -/
  temperedGroup : Grp
  /-- profinite 部分 ＝ 実 ℤ₃(1)。 -/
  profinite_isZ3 : profinitePart = tmzLimit
  /-- 離散部分 ＝ 実デッキ群 ℤ。 -/
  discrete_isZ : discretePart = intGrp
  /-- 核埋め込み ι : ℤ₃(1) ↪ π₁^{(3)}。 -/
  incl : Hom profinitePart temperedGroup
  /-- 射影 pr : π₁^{(3)} ↠ ℤ。 -/
  proj : Hom temperedGroup discretePart
  /-- ι は単射。 -/
  incl_inj : incl.Injective
  /-- pr は全射。 -/
  proj_surj : ∀ g : discretePart.carrier, ∃ x, proj.map x = g
  /-- 完全列 1 → ℤ₃(1) → π₁^{(3)} → ℤ → 1（核 ＝ 像）。 -/
  exact : ∀ x, proj.map x = discretePart.one ↔ ∃ z, incl.map z = x
  /-- 離散部は有界指数でない（非副有限＝真に tempered）。 -/
  discrete_not_finite : ¬ BoundedExponent discretePart
  /-- 実 Tate 被覆デッキ実現 (z,n) ↦ qⁿ。 -/
  deck_realize : Hom temperedGroup q3tGrp
  /-- デッキ実現の像 ⊆ 実被覆 q3tProj の核（qⁿ ∈ q^ℤ）。 -/
  deck_realize_ker : ∀ x, (q3tProj m).map (deck_realize.map x) = (q3tCurve m).one
  /-- デッキ実現の忠実性（周期準同型の単射・q^ℤ ≅ ℤ）。 -/
  deck_faithful : ∀ a b : Int,
    (q3tdPeriodHom m).map a = (q3tdPeriodHom m).map b → a = b
  /-- 実 Gal(ℚ(ζ_{3^∞})/ℚ) の作用（profinite 部分に χ 冪・離散部分固定）。 -/
  gal_act : ctlProfinite.carrier → Hom temperedGroup temperedGroup
  /-- **無条件**無限位数（M333F/M364F 外部仮説の実 discharge・入力仮説ゼロ）。 -/
  infinite_order : discRig_infiniteOrder_hypothesis q3tGrp (q3tQ m)

/-- **q3tp-5b: 見出し実例 q = 3**（m=1）— 全フィールドを q3tp-1〜4 の本物の証明で充填。
    infinite_order は q3td_infinite_order（実主語上の定理）で**無条件に**埋まる
    ——M364F temperedPi1Data が外部仮説 hInf を必要としたのと対照的。 -/
def q3tpData : Q3TemperedPi1Data where
  m := 1
  hm := Nat.le_refl 1
  profinitePart := tmzLimit
  discretePart := intGrp
  temperedGroup := q3tpGroup
  profinite_isZ3 := rfl
  discrete_isZ := rfl
  incl := q3tpIncl
  proj := q3tpProj
  incl_inj := q3tp_incl_injective
  proj_surj := q3tp_proj_surjective
  exact := q3tp_extension_exact
  discrete_not_finite := theta_deck_not_finite
  deck_realize := q3tpDeckRealize 1
  deck_realize_ker := q3tp_deck_realize_ker 1 (Nat.le_refl 1)
  deck_faithful := q3tp_deck_faithful 1 (Nat.le_refl 1)
  gal_act := q3tpGalAct
  infinite_order := q3td_infinite_order 1 (Nat.le_refl 1)

/-- **q3tp-5c（★）: 実主語では tempered データが無条件に存在** — M364F `tmp_exists`
    が外部仮説 hInf（tmp_infiniteOrder_hypothesis）に条件付いたのに対し、実 Tate 被覆の
    実主語では q3td_infinite_order が仮定ゼロで無限位数を与えるため、実 pro-3 tempered π₁
    データは**入力仮説なしで存在する**。M364F 条件付き存在に対する質的前進。 -/
theorem q3tp_exists_unconditional : Nonempty Q3TemperedPi1Data := ⟨q3tpData⟩

/-! ## 実例（無条件で成立する tempered の実部分ケース） -/

/-- 実例: 実 pro-3 tempered 群の完全列 1 → ℤ₃(1) → π₁^{(3)} → ℤ → 1。 -/
example (x : q3tpGroup.carrier) :
    q3tpProj.map x = intGrp.one ↔ ∃ z : tmzLimit.carrier, q3tpIncl.map z = x :=
  q3tp_extension_exact x

/-- 実例: 実デッキ実現の像は実被覆の核へ落ちる（qⁿ ∈ q^ℤ）。 -/
example (x : q3tpGroup.carrier) :
    (q3tProj 1).map ((q3tpDeckRealize 1).map x) = (q3tCurve 1).one :=
  q3tp_deck_realize_ker 1 (Nat.le_refl 1) x

/-- 実例: 実 tempered データは無条件に存在（外部仮説 hInf 不要）。 -/
example : Nonempty Q3TemperedPi1Data := q3tp_exists_unconditional

end IUT
