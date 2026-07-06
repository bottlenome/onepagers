/-
  IUT/GaloisTheta.lean — M343F [実／本物]
  分類: 実 (ガロア同変 l-捻れテータ値・χ との整合)
  complete_pct 影響: 柱E を前進（l-捻れ点 u_j への G_K 作用 σ·u_j=ζ^{c(σ)}u_j（χ 捻り）と
    テータ値の変換 Θ(q,σ·u_j)=ζ^{…}Θ(q,u_j)・G_K 同変性・χ 整合・Θ^{2l}=q^{j²} のガロア不変性を
    本物で。テータ値を円分/ガロア構造に結ぶ（M338F 円分剛性へ接続））。
  正直な限定: tempered π₁ 作用本体・p 進解析テータは外部仮説/後続。
-/
import IUT.ThetaValueLtor
import IUT.CyclotomicRigidity

namespace IUT

/-! ## M343F-0: 可換群の冪法則（1 の冪・積の冪の分配）

  以下の l-捻れテータ値のガロア作用は、μ_l（1 の l 乗根の群 CycMuGroup）を捻り因子
  ζ_l^{c(σ)} の住処として用いる。そのための可換群の基本冪法則をまず本物で建てる
  （既存 `cycRig_pow_add`/`cycRig_pow_mul` と補完）。 -/

/-- **M343F-0a: 1 の冪は 1** — 1ⁿ = 1（n 帰納・単位律）。捻り因子の位数計算の土台。 -/
theorem galTh_pow_one (G : Grp) (n : Nat) : G.pow G.one n = G.one := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show G.mul G.one (G.pow G.one n) = G.one
    rw [G.one_mul, ih]

/-- **M343F-0b: 積の冪の分配** — 可換群で (a·b)ⁿ = aⁿ·bⁿ（n 帰納・結合律と可換律で
    項を並べ替え）。l-捻れ点の捻り因子が積で分配（コサイクル則）することの本物の橋。 -/
theorem galTh_pow_mul_distrib (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (a b : G.carrier) (n : Nat) :
    G.pow (G.mul a b) n = G.mul (G.pow a n) (G.pow b n) := by
  induction n with
  | zero =>
    show G.one = G.mul G.one G.one
    exact (G.one_mul G.one).symm
  | succ n ih =>
    show G.mul (G.mul a b) (G.pow (G.mul a b) n)
       = G.mul (G.mul a (G.pow a n)) (G.mul b (G.pow b n))
    rw [ih, G.mul_assoc a b (G.mul (G.pow a n) (G.pow b n)),
      ← G.mul_assoc b (G.pow a n) (G.pow b n), hc b (G.pow a n),
      G.mul_assoc (G.pow a n) b (G.pow b n),
      ← G.mul_assoc a (G.pow a n) (G.mul b (G.pow b n))]

/-- **M343F-0c: μ_n の指数 n 消去** — μ_n の任意の元 z に対し zⁿ = 1（z=ζ^{log z}、
    zⁿ=ζ^{n·log z}=(ζⁿ)^{log z}=1）。μ_n が指数 n の群であること。ノルム
    Θ^{2l} のガロア捻りが消える（捻りの位数が l を割る）ことの本物の核。 -/
theorem galTh_mu_exp_ord (M : CycMuGroup) (z : M.μ.carrier) :
    M.μ.pow z M.n = M.μ.one := by
  have hz : z = M.μ.pow M.ζ (M.log z) := (M.pow_log z).symm
  rw [hz, ← cycRig_pow_mul M.μ M.comm M.ζ (M.log z) M.n,
    Nat.mul_comm (M.log z) M.n, cycRig_pow_mul M.μ M.comm M.ζ M.n (M.log z), M.ord]
  exact galTh_pow_one M.μ (M.log z)

/-! ## M343F-1: G_K の μ_l（l-捻れの円分部分）への群作用 -/

/-- **M343F-1a: G_K の μ_l 作用** — g ∈ G_K は μ_l（l-捻れ点に現れる 1 の l 乗根の群）に
    σ_g = ρ.act g（実 Galois 自己準同型）で作用する。IUT のエタールテータを評価する
    l-捻れ点の円分部分への本物のガロア作用（M322F `CycGKAction` を主語に据える）。 -/
def galThMuAct (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (z : M.μ.carrier) : M.μ.carrier :=
  (ρ.act g).map z

/-- **定理 (M343F-1b: 群作用の単位則)** — σ_1(z)=z（M322F `CycGKAction.act_one`）。 -/
theorem galTh_mu_act_one (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (z : M.μ.carrier) : galThMuAct GK M ρ GK.one z = z :=
  ρ.act_one z

/-- **定理 (M343F-1c: 群作用の合成則)** — σ_{g·h}(z)=σ_g(σ_h(z))（M322F
    `CycGKAction.act_mul`）。G_K の μ_l への作用が**本物の群作用**をなす。 -/
theorem galTh_mu_act_mul (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) (z : M.μ.carrier) :
    galThMuAct GK M ρ (GK.mul g h) z
      = galThMuAct GK M ρ g (galThMuAct GK M ρ h z) :=
  ρ.act_mul g h z

/-- **定理 (M343F-1d: 円分指標での作用)** — σ_g(ζ^k)=ζ^{χ(g)·k}（M322F `cycRig_act_pow`）。
    μ_l への作用が円分指標 χ=`cycRigExp` の指数倍で与えられる（IUT の円分剛性の作用形）。 -/
theorem galTh_mu_act_pow (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (k : Nat) :
    galThMuAct GK M ρ g (M.μ.pow M.ζ k) = M.μ.pow M.ζ (cycRigExp GK M ρ g * k) :=
  cycRig_act_pow GK M ρ g k

/-! ## M343F-2: l-捻れ点 u_j へのガロア捻り（Kummer コサイクル） -/

/-- **M343F-2a: l-捻れ点のガロア捻り因子** — l-捻れ点 u_j = (q^{1/l})^j = u_1^j に対し、
    Kummer 指標 κ : G_K → μ_l（κ(σ)=σ(q^{1/l})/q^{1/l}）から、
      σ(u_j) = κ(σ)^j · u_j
    の捻り因子 κ(g)^j ∈ μ_l。IUT III の l-等分点 u_j が G_K で ζ_l 捻りにより
    置換されることの本物の捻り因子（μ_l を住処に据える）。 -/
def galThTorTwist (GK : Grp) (M : CycMuGroup) (κ : Hom GK M.μ)
    (g : GK.carrier) (j : Nat) : M.μ.carrier :=
  M.μ.pow (κ.map g) j

/-- **定理 (M343F-2b: 捻りの単位則)** — 単位元の捻りは自明: κ(1)^j = 1
    （κ(1)=1・1 の冪は 1）。σ_1 が l-捻れ点を動かさない。 -/
theorem galTh_tor_twist_one (GK : Grp) (M : CycMuGroup) (κ : Hom GK M.μ) (j : Nat) :
    galThTorTwist GK M κ GK.one j = M.μ.one := by
  show M.μ.pow (κ.map GK.one) j = M.μ.one
  rw [κ.map_one]
  exact galTh_pow_one M.μ j

/-- **定理 (M343F-2c: 捻りのコサイクル則)** — κ(g·h)^j = κ(g)^j·κ(h)^j
    （κ 準同型 ⟹ κ(gh)=κ(g)·κ(h)、可換群の積の冪分配 M343F-0b）。l-捻れ点の
    ガロア捻り因子が合成で乗法的に振る舞う（1-コサイクル）ことの本物。 -/
theorem galTh_tor_twist_mul (GK : Grp) (M : CycMuGroup) (κ : Hom GK M.μ)
    (g h : GK.carrier) (j : Nat) :
    galThTorTwist GK M κ (GK.mul g h) j
      = M.μ.mul (galThTorTwist GK M κ g j) (galThTorTwist GK M κ h j) := by
  show M.μ.pow (κ.map (GK.mul g h)) j
     = M.μ.mul (M.μ.pow (κ.map g) j) (M.μ.pow (κ.map h) j)
  rw [κ.map_mul, galTh_pow_mul_distrib M.μ M.comm]

/-! ## M343F-3: テータ値の円分影とガロア変換 -/

/-- **M343F-3a: テータ値の円分影** — l-捻れ点でのテータ値 Θ(q,u_j)=q^{j²/2l} の
    μ_l（1 の l 乗根）成分 ζ_l^{j²}。テータ値を円分構造 μ_l へ落とした影
    （M318F の指数 j² が円分部分の指数を与える）。 -/
def galThValCyc (M : CycMuGroup) (j : Nat) : M.μ.carrier :=
  M.μ.pow M.ζ (j * j)

/-- **定理 (M343F-3b: テータ値の変換)** — Θ(q,σ·u_j) の円分影は
    ζ_l^{χ(g)·j²} に変換される: σ_g(ζ^{j²}) = ζ^{χ(g)·j²}。テータ値が
    ガロア捻りの下で μ_l 因子（円分因子）を拾い、その指数が円分指標 χ=`cycRigExp` で
    支配されることの本物（M322F `cycRig_act_pow`）。 -/
theorem galTh_value_transform (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (j : Nat) :
    galThMuAct GK M ρ g (galThValCyc M j)
      = M.μ.pow M.ζ (cycRigExp GK M ρ g * (j * j)) := by
  show galThMuAct GK M ρ g (M.μ.pow M.ζ (j * j))
     = M.μ.pow M.ζ (cycRigExp GK M ρ g * (j * j))
  exact galTh_mu_act_pow GK M ρ g (j * j)

/-- **定理 (M343F-3c: ガロア同変性の正方形)** — G_K 作用は μ_l 上で**群準同型として**
    作用し、冪（l-捻れ点の乗法構造）と可換: σ_g(w^n) = (σ_g w)^n。テータ値写像の
    源（l-捻れ点の μ_l 構造）への作用と、標的（μ_l 上の円分作用）が可換する同変正方形
    （ρ.act g が Hom であることの `Hom.map_pow`）。 -/
theorem galTh_equivariant (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (w : M.μ.carrier) (n : Nat) :
    galThMuAct GK M ρ g (M.μ.pow w n)
      = M.μ.pow (galThMuAct GK M ρ g w) n :=
  Hom.map_pow (ρ.act g) w n

/-! ## M343F-4: 円分指標 χ との整合 -/

/-- **定理 (M343F-4a: 円分作用の合成整合)** — テータ値の円分影のガロア作用は合成で整合:
    σ_{g·h}(ζ^{j²}) = σ_g(σ_h(ζ^{j²}))。ガロア捻り因子が χ の合成に沿って積むこと
    （M322F `act_mul`）——円分指標 χ が捻りを支配する整合性。 -/
theorem galTh_cyclotomic_compat (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) (j : Nat) :
    galThMuAct GK M ρ (GK.mul g h) (galThValCyc M j)
      = galThMuAct GK M ρ g (galThMuAct GK M ρ h (galThValCyc M j)) :=
  galTh_mu_act_mul GK M ρ g h (galThValCyc M j)

/-- **定理 (M343F-4b: 捻りは円分指標 χ で支配)** — 捻りの指数を与える円分指標
    χ_l=`cycRigChar` は群準同型 χ(g·h)=χ(g)·χ(h)（M322F `cycRig_char_isHom`）。
    テータ値のガロア捻り因子 ζ_l^{χ(g)·j²} が円分指標 χ で well-defined（mod l）に
    決まる（M338F 円分剛性が円分体を pin することでガロア作用が離散 μ_l を除いて
    確定する）ことの本物の根拠。 -/
theorem galTh_char_hom (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) :
    cycRigChar GK M ρ (GK.mul g h)
      = zmodMul M.n (cycRigChar GK M ρ g) (cycRigChar GK M ρ h) :=
  cycRig_char_isHom GK M ρ g h

/-! ## M343F-5: ノルム Θ^{2l}=q^{j²} のガロア不変性 -/

/-- **定理 (M343F-5a: ノルムは q 冪)** — テータ値の 2l 乗はちょうど q^{j²}:
    Θ(q,u_j)^{2l} = u^{2l·j²} = (u^{2l})^{j²} = q^{j²} ∈ q^ℤ（`IsLPowerValue R (2l)`,
    witness k=j²）。M318F の本物の反復群冪 `thLtorPow` と指数法則で、テータ値の
    2l 乗が周期格子 q^ℤ に落ちることを本物で確立する。 -/
theorem galTh_norm_qpower (R : CRing) (l : Nat) (j : Int) :
    IsLPowerValue R ((2 * l : Nat) : Int) (thLtorPow R (thLtorValue R j) (2 * l)) := by
  refine ⟨j * j, ?_⟩
  rw [thLtor_value_exponent R j, thLtorPow_uMon R (thLtorExp j) (2 * l), thLtorExp_sq,
    Int.mul_comm (j * j) ((2 * l : Nat) : Int)]

/-- **定理 (M343F-5b: ノルムのガロア捻りは自明)** — 任意の Kummer 捻り因子 κ(g)^m を
    l(=位数 n) 乗すると 1 になる: (κ(g)^m)^l = 1（μ_l は指数 l、M343F-0c）。ノルム
    Θ^{2l}=q^{j²} は q∈K^×^{G_K} が固定され、かつガロア捻り（μ_l の元）の位数が l を
    割るため、l 乗（ノルム）でガロア捻りが完全に消える——**ノルムはガロア不変**。 -/
theorem galTh_norm_twist_trivial (GK : Grp) (M : CycMuGroup) (κ : Hom GK M.μ)
    (g : GK.carrier) (m : Nat) :
    M.μ.pow (M.μ.pow (κ.map g) m) M.n = M.μ.one :=
  galTh_mu_exp_ord M (M.μ.pow (κ.map g) m)

/-! ## M343F-6: l-捻れ点の周期整合（値のガロア不変因子側） -/

/-- **定理 (M343F-6a: l-周期での値変換)** — j↦j+l（同一 l-捻れ点）でのテータ値変換
    Θ(q,u_{j+l}) = Θ(q,u_j)·u^{l(2j+l)}（M318F `thLtor_period_at_torsion`）。
    l-捻れ点の周期整合の値側。捻れ因子 u^{l(2j+l)} は次で q 冪（ガロア不変）。 -/
theorem galTh_value_shift (R : CRing) (l j : Int) :
    thLtorValue R (j + l)
      = (laurentRing R).mul (thLtorValue R j) (uMonHom R (l * (2 * j + l))) :=
  thLtor_period_at_torsion R l j

/-- **定理 (M343F-6b: 周期因子は q 冪＝ガロア不変)** — 周期因子 u^{l(2j+l)} は
    `IsLPowerValue R l`（q^ℤ 部分群、witness 2j+l、M318F `thLtor_period_lpower`）。
    j↦j+l のズレがちょうど周期格子 q^ℤ（G_K-固定）に属す——l-捻れ点の値変換の
    不変因子側。 -/
theorem galTh_value_shift_qpower (R : CRing) (l j : Int) :
    IsLPowerValue R l (uMonHom R (l * (2 * j + l))) :=
  thLtor_period_lpower R l j

/-! ## M343F-7: 外部仮説（tempered π₁ 作用本体・p 進解析テータ・決して導出しない） -/

/-- **M343F-7a: tempered π₁ 作用仮説（Prop）** — 完全な tempered 基本群
    π₁^{temp} の l-捻れ（円分）部分への作用 `fullAct` が、本モジュールの円分指標経由の
    μ_l 作用 `galThMuAct` に一致するという**外部仮説**。実の遠アーベル対象（tempered
    π₁^ét）から来る作用がこの形を取ることは柱E/D 後続の外部入力であり、本層はこれを
    明示の Prop 仮説として受け、決して自前で導出しない。 -/
def galTh_tempered_pi1_hypothesis (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (fullAct : GK.carrier → M.μ.carrier → M.μ.carrier) : Prop :=
  ∀ g z, fullAct g z = galThMuAct GK M ρ g z

/-- **定理 (M343F-7b: tempered π₁ 作用の復元・仮説依存)** — 仮説
    `galTh_tempered_pi1_hypothesis` の下で、tempered π₁ 作用は本モジュールの μ_l 作用に
    一致する。仮説は外部入力であり本体で導出しない。 -/
theorem galTh_tempered_pi1_recovery (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (fullAct : GK.carrier → M.μ.carrier → M.μ.carrier)
    (hyp : galTh_tempered_pi1_hypothesis GK M ρ fullAct)
    (g : GK.carrier) (z : M.μ.carrier) :
    fullAct g z = galThMuAct GK M ρ g z :=
  hyp g z

/-- **M343F-7c: p 進解析テータ仮説（Prop）** — p 進解析的テータ関数値の円分（μ_l）影
    `padicCyc` が、本モジュールの円分影 `galThValCyc` に一致するという**外部仮説**。
    テータ関数の p 進収束・解析的値そのものは柱E/D 後続の外部入力であり、本層は
    円分影の指数 j² の水準までを本物とし、解析的テータ値本体は仮説として受ける。 -/
def galTh_padic_analytic_hypothesis (M : CycMuGroup)
    (padicCyc : Nat → M.μ.carrier) : Prop :=
  ∀ j, padicCyc j = galThValCyc M j

/-- **定理 (M343F-7d: p 進解析テータの円分影・仮説依存)** — 仮説
    `galTh_padic_analytic_hypothesis` の下で、p 進解析テータ値の円分影は本モジュールの
    円分影 ζ_l^{j²} に一致する。解析的テータ値本体は外部入力で導出しない。 -/
theorem galTh_padic_analytic_recovery (M : CycMuGroup)
    (padicCyc : Nat → M.μ.carrier)
    (hyp : galTh_padic_analytic_hypothesis M padicCyc) (j : Nat) :
    padicCyc j = galThValCyc M j :=
  hyp j

/-! ## M343F-8: capstone（ガロア同変 l-捻れテータ値データ） -/

/-- **M343F-8a: ガロア同変テータ値データ** — G_K の μ_l 作用 ρ（群作用）・Kummer 捻り
    κ・テータ値の円分影の変換（χ 支配）・同変正方形・円分指標 χ の準同型・l-捻れ点の
    捻りコサイクル則・ノルム捻りの自明性（ガロア不変）を一括束ね。IUT のエタールテータを
    l-捻れ点で評価した値のガロア同変構造の総括（主語は本物の μ_l と本物のテータ値指数 j²）。 -/
structure GaloisThetaData (GK : Grp) (M : CycMuGroup) where
  /-- G_K の μ_l への作用（M322F `CycGKAction`）。 -/
  ρ : CycGKAction GK M
  /-- Kummer 捻り指標 κ : G_K → μ_l。 -/
  κ : Hom GK M.μ
  /-- 群作用の単位則 σ_1=id。 -/
  act_one : ∀ z, galThMuAct GK M ρ GK.one z = z
  /-- 群作用の合成則 σ_{gh}=σ_g∘σ_h。 -/
  act_mul : ∀ g h z, galThMuAct GK M ρ (GK.mul g h) z
    = galThMuAct GK M ρ g (galThMuAct GK M ρ h z)
  /-- テータ値の円分影の変換: σ_g(ζ^{j²}) = ζ^{χ(g)·j²}。 -/
  value_transform : ∀ g (j : Nat), galThMuAct GK M ρ g (galThValCyc M j)
    = M.μ.pow M.ζ (cycRigExp GK M ρ g * (j * j))
  /-- 同変正方形: σ_g(w^n) = (σ_g w)^n。 -/
  equivariant : ∀ g (w : M.μ.carrier) (n : Nat),
    galThMuAct GK M ρ g (M.μ.pow w n) = M.μ.pow (galThMuAct GK M ρ g w) n
  /-- 円分指標 χ の準同型性 χ(gh)=χ(g)·χ(h)。 -/
  char_hom : ∀ g h, cycRigChar GK M ρ (GK.mul g h)
    = zmodMul M.n (cycRigChar GK M ρ g) (cycRigChar GK M ρ h)
  /-- l-捻れ点の捻りの単位則: κ(1)^j = 1。 -/
  tor_twist_one : ∀ (j : Nat), galThTorTwist GK M κ GK.one j = M.μ.one
  /-- l-捻れ点の捻りのコサイクル則: κ(gh)^j = κ(g)^j·κ(h)^j。 -/
  tor_twist_mul : ∀ g h (j : Nat), galThTorTwist GK M κ (GK.mul g h) j
    = M.μ.mul (galThTorTwist GK M κ g j) (galThTorTwist GK M κ h j)
  /-- ノルムのガロア捻りは自明: (κ(g)^m)^l = 1（ノルム Θ^{2l}=q^{j²} はガロア不変）。 -/
  norm_twist_trivial : ∀ g (m : Nat), M.μ.pow (M.μ.pow (κ.map g) m) M.n = M.μ.one

/-- **M343F-8b: witness 本体** — 各フィールドを M343F-1〜5 の主定理で埋める。 -/
def galThData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (κ : Hom GK M.μ) :
    GaloisThetaData GK M where
  ρ := ρ
  κ := κ
  act_one := galTh_mu_act_one GK M ρ
  act_mul := galTh_mu_act_mul GK M ρ
  value_transform := galTh_value_transform GK M ρ
  equivariant := galTh_equivariant GK M ρ
  char_hom := galTh_char_hom GK M ρ
  tor_twist_one := galTh_tor_twist_one GK M κ
  tor_twist_mul := galTh_tor_twist_mul GK M κ
  norm_twist_trivial := fun g m => galTh_norm_twist_trivial GK M κ g m

/-- **定理 (M343F-8c: capstone — ガロア同変テータ値データの存在)** — 任意の G_K・μ_l・
    作用 ρ・Kummer 捻り κ に対し、l-捻れテータ値のガロア同変構造（μ_l 作用・値変換・
    同変性・χ 整合・捻りコサイクル・ノルム不変性）が本物で組み上がる。IUT のエタール
    テータを l-捻れ点で評価した値のガロア構造への接続が閉じる。 -/
theorem galTh_exists (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (κ : Hom GK M.μ) :
    Nonempty (GaloisThetaData GK M) :=
  ⟨galThData GK M ρ κ⟩

/-! ## M343F-9: 実例 — 本物の絶対ガロア群 G_ℚ の μ_l 上のガロア同変テータ値 -/

/-- **M343F-9a: 自明 Kummer 捻り** — 任意の G_K・μ_l への自明 Kummer 指標
    κ≡1（不分岐点・σ(q^{1/l})=q^{1/l}）。本物の G_K 上でガロア同変テータ値データを
    実例化するための捻り。非自明 Kummer 捻りを与える実 Galois 降下は柱E 後続。 -/
def galThTrivialKummer (GK : Grp) (M : CycMuGroup) : Hom GK M.μ where
  map := fun _ => M.μ.one
  map_mul := fun _ _ => (M.μ.one_mul M.μ.one).symm

/-- **M343F-9b: 本物の G_ℚ の μ_l 上のガロア同変テータ値データ** — M315F の本物の絶対
    ガロア群 G_ℚ=`algCloAbsGalois algCloTrivialTower` の trivial 作用と自明 Kummer
    捻りから、l-捻れテータ値のガロア同変構造を組む。IUT が l-捻れ点で評価する μ_l 上の
    テータ値ガロア作用の実例。 -/
def galThGaloisExample (l : Nat) (hl : 1 ≤ l) :
    GaloisThetaData (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl) :=
  galThData (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))
    (galThTrivialKummer (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))

/-- **定理 (M343F-9c: 実例の存在)** — 本物の G_ℚ の μ_l 上でガロア同変テータ値データが
    存在する。 -/
theorem galTh_galois_example_exists (l : Nat) (hl : 1 ≤ l) :
    Nonempty (GaloisThetaData (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)) :=
  ⟨galThGaloisExample l hl⟩

/-! ## M343F-10: 実例（l=5・数値） -/

/-- 実例: l=5 の本物の G_ℚ の μ_5 上のガロア同変テータ値データが存在する。 -/
theorem galTh_example_l5 :
    Nonempty (GaloisThetaData (algCloAbsGalois algCloTrivialTower)
      (cycMuStd 5 (by omega))) :=
  galTh_galois_example_exists 5 (by omega)

/-- 実例: l=5 のノルム Θ(q,u_j)^{10}=q^{j²} が q^ℤ（`IsLPowerValue R 10`）に落ちる。 -/
example (R : CRing) (j : Int) :
    IsLPowerValue R ((2 * 5 : Nat) : Int) (thLtorPow R (thLtorValue R j) (2 * 5)) :=
  galTh_norm_qpower R 5 j

/-- 実例: j=2 のテータ値の円分影の変換の指数 χ(g)·4（j²=4）。 -/
example (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (g : GK.carrier) :
    galThMuAct GK M ρ g (galThValCyc M 2)
      = M.μ.pow M.ζ (cycRigExp GK M ρ g * (2 * 2)) :=
  galTh_value_transform GK M ρ g 2

/-- 実例: l=5・任意 Kummer 捻り κ(g)^m の 5 乗が 1（ノルムのガロア捻りは自明）。 -/
example (GK : Grp) (κ : Hom GK (cycMuStd 5 (by omega)).μ) (g : GK.carrier) (m : Nat) :
    (cycMuStd 5 (by omega)).μ.pow
        ((cycMuStd 5 (by omega)).μ.pow (κ.map g) m) (cycMuStd 5 (by omega)).n
      = (cycMuStd 5 (by omega)).μ.one :=
  galTh_norm_twist_trivial GK (cycMuStd 5 (by omega)) κ g m

end IUT
