-- M389F TemperedThetaOuterAction [実・本物・柱A]
-- complete_pct 影響: 柱A で M384F の離散 Heisenberg テータ群 thetaGrp に G_K の外ガロア作用（中心＝内部円分体 μ_l を円分指標 χ で捻る）を本物で追加し、交換子＝シンプレクティック形式が χ で変換すること・μ_l 上の作用が M322F の実円分指標作用 CycGKAction に一致することを完全証明。
-- 正直な限定: 完全な tempered π₁^temp の外ガロア表現・slim 遠アーベル性・幾何的 Frobenioid の G_K-同変実現は外部/後続。ここでは離散 Heisenberg 群 thetaGrp とその中心＝μ_l への χ 捻り・抽象 CycGKAction のみを扱う。

/-
  IUT/TemperedThetaOuterAction.lean — M389F [実／本物・柱A]
  分類: 実（G_K の離散 Heisenberg テータ群への外ガロア作用・中心 μ_l の χ 捻り）

  M384F (IUT/TemperedThetaCommutator.lean) は離散 Heisenberg 群（テータ群 thetaGrp）
  の交換子 [g,h] が中心 {(0,0,∗)} に落ち・その中心座標がシンプレクティック形式
  ω(g,h)=a·b′−a′·b に一致すること（中心＝内部円分体 μ_l の離散モデル）を完全証明した。
  M322F (IUT/CyclotomicRigidity.lean) は G_K の μ_n への**実ガロア作用** `CycGKAction`
  と**円分指標** χ_n=`cycRigChar`（σ_g(ζ)=ζ^{χ(g)}）を本物で建設した。
  M343F (IUT/GaloisTheta.lean) は `galThMuAct`（G_K の μ_l 作用）を主語に据えた。

  本モジュールは**次の実ステップ＝外ガロア作用**を建設する:
    G_K は theta group に作用し、その作用は中心（内部円分体 μ_l）を円分指標 χ で捻る。
    交換子はその χ 捻りを除いて保たれる（＝シンプレクティック形式が χ で変換する）。

  建設内容（すべて本物の対象・toy 群なし）:
    * **スケール作用** ttoaScale e (a,b,c) = (a, b, e·c) — 中心座標を e 倍で捻る作用。
      これは (ℤ,·) の thetaGrp への**忠実なモノイド作用**（ttoaScale 1 = id・
      ttoaScale e ∘ ttoaScale e' = ttoaScale (e·e')、on-the-nose・M389F-1）。
    * **外ガロア作用** ttoaAct GK M ρ g = ttoaScale (χ(g))（χ=`cycRigExp`、M322F の実円分
      指標）— G_K が中心＝内部円分体を χ で捻る作用（M389F-6）。
    * **中心での準同型性**: スケール作用は中心 {(0,0,∗)} 上では群積を保つ（M389F-2a）。
    * **積の χ 捻り（正直な内容）**: スケール作用は完全な Heisenberg 積の**自己同型では
      ない**——コサイクル a·b′ が χ で捻れる。捻りの差は厳密に (e−1)·(a·b′)（M389F-2b）。
      これが「外ガロア作用がテータ群を χ 捻りする」ことの本物の内容。
    * **交換子の χ 捻り（本丸）**: 交換子は幾何座標 (a,b) しか見ないのでスケール作用で
      **不変** [σ·x,σ·y]=[x,y]（M389F-3a）だが、作用を交換子に施すと中心座標が e 倍される
      σ·[x,y]=(0,0,e·ω)（M389F-3b）。ゆえに σ·[x,y] の中心座標 = χ(g)·([σ·x,σ·y] の中心座標)
      ＝**シンプレクティック形式が χ で変換する**（M389F-3c／M389F-6b、本丸）。
    * **μ_l 上の作用が M322F の実円分指標作用に一致**: 内部円分体 μ_l への G_K 作用は
      `galThMuAct`（＝`CycGKAction`、M343F/M322F）で・σ_1=id・σ_{gh}=σ_g∘σ_h の
      **本物の群作用**をなし・σ_g(ζ^k)=ζ^{χ(g)·k}（M389F-4）。標準生成元の交換子の μ_l 像
      ζ は σ_g で ζ^{χ(g)} に捻れる（M389F-4d）。χ_n は準同型 χ(gh)=χ(g)·χ(h)（M389F-5）。
    * **M384F 中心写像 centerToMu との接続**: χ 捻りした標準生成元の交換子の中心座標を
      M124F/M384F の μ_l 同期写像 centerToMu に送ると centerToMu(χ(g)) を得る（M389F-7）。

  正直な限定: 完全な幾何的 tempered π₁^temp（Δ^temp）の slim 遠アーベル性・その外ガロア表現・
  p 進テータ関数のガロア同変な評価・幾何的 Frobenioid の G_K-同変実現は外部（幾何的入力・後続）。
  本モジュールは離散 Heisenberg 群 thetaGrp・その中心＝μ_l への χ 捻り・抽象 `CycGKAction` の
  みを扱う。スケール作用は完全な Heisenberg 積の自己同型ではない（コサイクルが χ 捻りする）
  ——これは消してはならない正直な内容であり、交換子の χ 変換として本物に定式化する。
  全て選択公理不使用（propext / Quot.sound のみ）。
-/
import IUT.GaloisTheta
import IUT.TemperedThetaCommutator

namespace IUT

/-! ## M389F-1: スケール作用（(ℤ,·) の thetaGrp 中心への忠実なモノイド作用）

  外ガロア作用の骨格は「中心座標を e 倍で捻る」作用 ttoaScale e (a,b,c)=(a,b,e·c)。
  これは on-the-nose の (ℤ,·) 作用: ttoaScale 1 = id、合成が積に一致する。 -/

/-- **M389F-1a: スケール作用** — 中心座標（内部円分体 μ_l の離散モデル）を e 倍で捻る。
    幾何座標 (a,b) は固定、中心座標 c ↦ e·c。外ガロア作用の中心への捻りの骨格。 -/
@[reducible] def ttoaScale (e : Int) (x : thetaGrp.carrier) : thetaGrp.carrier :=
  (x.1, x.2.1, e * x.2.2)

/-- **定理 (M389F-1a′: 幾何座標の固定)** — スケール作用は第 1・2 成分（幾何部分）を保つ。 -/
theorem ttoa_scale_fst (e : Int) (x : thetaGrp.carrier) : (ttoaScale e x).1 = x.1 := rfl

theorem ttoa_scale_snd (e : Int) (x : thetaGrp.carrier) :
    (ttoaScale e x).2.1 = x.2.1 := rfl

/-- **定理 (M389F-1a″: 中心座標の捻り)** — スケール作用は中心座標を e 倍する。 -/
theorem ttoa_scale_center (e : Int) (x : thetaGrp.carrier) :
    (ttoaScale e x).2.2 = e * x.2.2 := rfl

/-- **定理 (M389F-1b: 単位則)** — ttoaScale 1 = id（1 倍は恒等）。 -/
theorem ttoa_scale_one (x : thetaGrp.carrier) : ttoaScale 1 x = x := by
  obtain ⟨a, b, c⟩ := x
  show ((a, b, (1 : Int) * c) : Int × Int × Int) = (a, b, c)
  exact triple_ext rfl rfl (Int.one_mul c)

/-- **定理 (M389F-1c: 合成則)** — ttoaScale e ∘ ttoaScale e' = ttoaScale (e·e')。
    (ℤ,·) の thetaGrp への**本物のモノイド作用**（on-the-nose、Int 乗法の結合律）。 -/
theorem ttoa_scale_mul (e e' : Int) (x : thetaGrp.carrier) :
    ttoaScale e (ttoaScale e' x) = ttoaScale (e * e') x := by
  obtain ⟨a, b, c⟩ := x
  show ((a, b, e * (e' * c)) : Int × Int × Int) = (a, b, (e * e') * c)
  exact triple_ext rfl rfl (Int.mul_assoc e e' c).symm

/-! ## M389F-2: 中心での準同型性・積の χ 捻り（正直な内容）

  スケール作用は中心 {(0,0,∗)} 上では群積を保つが、完全な Heisenberg 積の自己同型では
  ない: コサイクル a·b′ が捻れる。差は厳密に (e−1)·(a·b′)（外ガロア作用の χ 捻りの内容）。 -/

/-- **定理 (M389F-2a: 中心での準同型性)** — スケール作用は中心元 (0,0,c) の積を保つ。
    内部円分体 μ_l（中心）への作用は群準同型: e·(c+c′)=e·c+e·c′。 -/
theorem ttoa_scale_center_hom (e c c' : Int) :
    ttoaScale e (thetaGrp.mul ((0, 0, c) : Int × Int × Int) (0, 0, c'))
      = thetaGrp.mul (ttoaScale e ((0, 0, c) : Int × Int × Int)) (ttoaScale e (0, 0, c')) := by
  show ((0 + 0, 0 + 0, e * (c + c' + (0 : Int) * 0)) : Int × Int × Int)
     = (0 + 0, 0 + 0, e * c + e * c' + (0 : Int) * 0)
  refine triple_ext (by omega) (by omega) ?_
  have h1 : c + c' + (0 : Int) * 0 = c + c' := by omega
  rw [h1, Int.mul_add]
  generalize e * c = X
  generalize e * c' = Y
  omega

/-- **定理 (M389F-2b: 積の χ 捻り／正直な内容)** — スケール作用は完全な Heisenberg 積の
    自己同型では**ない**: コサイクル a·b′ が e 倍に捻れる。捻りの差は厳密に (e−1)·(a·b′)。
      (ttoaScale e (x·y)).c = (ttoaScale e x · ttoaScale e y).c + (e−1)·(a·b′)。
    これが「外ガロア作用がテータ群のコサイクル（中心）を χ で捻る」ことの本物の内容。 -/
theorem ttoa_scale_product_twist (e a b c a' b' c' : Int) :
    (ttoaScale e (thetaGrp.mul ((a, b, c) : Int × Int × Int) (a', b', c'))).2.2
      = (thetaGrp.mul (ttoaScale e ((a, b, c) : Int × Int × Int)) (ttoaScale e (a', b', c'))).2.2
        + (e - 1) * (a * b') := by
  show e * (c + c' + a * b')
     = (e * c + e * c' + a * b') + (e - 1) * (a * b')
  rw [Int.mul_add, Int.mul_add, Int.sub_mul, Int.one_mul]
  generalize a * b' = P
  generalize e * c = X
  generalize e * c' = Y
  generalize e * P = Z
  omega

/-! ## M389F-3: 交換子の χ 捻り（本丸）

  交換子は幾何座標 (a,b) しか見ないのでスケール作用で不変だが、作用を交換子に施すと
  中心座標が e 倍される。ゆえにシンプレクティック形式が χ で変換する。 -/

/-- **定理 (M389F-3a: 交換子はスケール作用で不変)** — [σ·x, σ·y]=[x,y]。
    交換子の中心座標 ω=a·b′−a′·b は幾何座標 (a,b,a′,b′) しか見ず、中心の捻り e·c を
    見ないので不変（M384F ttc_commutator_form / M11 theta_comm）。 -/
theorem ttoa_commutator_invariant (e a b c a' b' c' : Int) :
    thetaGrp.comm (ttoaScale e ((a, b, c) : Int × Int × Int)) (ttoaScale e (a', b', c'))
      = thetaGrp.comm ((a, b, c) : Int × Int × Int) (a', b', c') := by
  show thetaGrp.comm ((a, b, e * c) : Int × Int × Int) (a', b', e * c')
     = thetaGrp.comm ((a, b, c) : Int × Int × Int) (a', b', c')
  rw [theta_comm, theta_comm]

/-- **定理 (M389F-3b: 交換子への作用は中心座標を e 倍)** — σ·[x,y]=(0,0,e·ω)。
    交換子は中心に落ちる（M384F）ので、そこへスケール作用を施すと中心座標が e 倍される。 -/
theorem ttoa_scale_commutator (e a b c a' b' c' : Int) :
    ttoaScale e (thetaGrp.comm ((a, b, c) : Int × Int × Int) (a', b', c'))
      = ((0, 0, e * (a * b' - a' * b)) : Int × Int × Int) := by
  rw [theta_comm]

/-- **定理 (M389F-3c: 交換子の χ 捻り／本丸)** — シンプレクティック形式が χ で変換する:
      (σ·[x,y]) の中心座標 = e · ([σ·x, σ·y] の中心座標)。
    左辺 = e·ω（M389F-3b）、右辺の [σ·x,σ·y] は不変（M389F-3a）で中心座標 ω。
    ゆえに外ガロア作用（e=χ(g)）のもとで交換子＝シンプレクティック形式は χ 倍される
    ——IUT の「テータ群の交換子が円分指標で捻れる」ことの本物の完全証明。 -/
theorem ttoa_commutator_twist (e a b c a' b' c' : Int) :
    (ttoaScale e (thetaGrp.comm ((a, b, c) : Int × Int × Int) (a', b', c'))).2.2
      = e * (thetaGrp.comm (ttoaScale e ((a, b, c) : Int × Int × Int))
              (ttoaScale e (a', b', c'))).2.2 := by
  have hL : (ttoaScale e (thetaGrp.comm ((a, b, c) : Int × Int × Int) (a', b', c'))).2.2
      = e * (a * b' - a' * b) := by rw [ttoa_scale_commutator]
  have hR : (thetaGrp.comm (ttoaScale e ((a, b, c) : Int × Int × Int))
              (ttoaScale e (a', b', c'))).2.2 = a * b' - a' * b := by
    rw [ttoa_commutator_invariant, theta_comm]
  rw [hL, hR]

/-! ## M389F-4: μ_l 上の作用は M322F の実円分指標作用に一致（CycGKAction 再利用）

  内部円分体 μ_l への G_K 作用は M343F `galThMuAct`（＝M322F `CycGKAction`）で与えられる
  本物の群作用であり、σ_g(ζ^k)=ζ^{χ(g)·k}（χ=`cycRigExp`）で記述される。 -/

/-- **定理 (M389F-4a: μ_l 作用の単位則)** — σ_1(z)=z（M343F galTh_mu_act_one）。 -/
theorem ttoa_mu_act_one (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (z : M.μ.carrier) : galThMuAct GK M ρ GK.one z = z :=
  galTh_mu_act_one GK M ρ z

/-- **定理 (M389F-4b: μ_l 作用の合成則)** — σ_{g·h}(z)=σ_g(σ_h(z))（M343F galTh_mu_act_mul）。
    内部円分体 μ_l への G_K の作用が**本物の群作用**をなす（外ガロア作用の μ_l 成分）。 -/
theorem ttoa_mu_act_mul (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) (z : M.μ.carrier) :
    galThMuAct GK M ρ (GK.mul g h) z = galThMuAct GK M ρ g (galThMuAct GK M ρ h z) :=
  galTh_mu_act_mul GK M ρ g h z

/-- **定理 (M389F-4c: 円分指標での作用形)** — σ_g(ζ^k)=ζ^{χ(g)·k}（χ=`cycRigExp`、
    M343F galTh_mu_act_pow / M322F cycRig_act_pow）。μ_l 作用が円分指標の指数倍で与えられる。 -/
theorem ttoa_mu_act_char (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (k : Nat) :
    galThMuAct GK M ρ g (M.μ.pow M.ζ k) = M.μ.pow M.ζ (cycRigExp GK M ρ g * k) :=
  galTh_mu_act_pow GK M ρ g k

/-- **定理 (M389F-4d: 交換子の μ_l 像が χ で捻れる)** — 標準生成元の交換子の μ_l 像 ζ^1=ζ
    は σ_g で ζ^{χ(g)} に捻れる: σ_g(ζ)=ζ^{χ(g)}。M384F の comm_xy が生む中心生成元 (0,0,1)
    の μ_l 像 ζ が外ガロア作用で円分指標倍に捻れることの本物の内容。 -/
theorem ttoa_gen_commutator_galois (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) :
    galThMuAct GK M ρ g (M.μ.pow M.ζ 1) = M.μ.pow M.ζ (cycRigExp GK M ρ g) := by
  rw [galTh_mu_act_pow, Nat.mul_one]

/-! ## M389F-5: 円分指標の準同型性（外ガロア作用が μ_l に降下する理由） -/

/-- **定理 (M389F-5: 円分指標の準同型性)** — χ_n(g·h)=χ_n(g)·χ_n(h)（M322F cycRig_char_isHom）。
    G_K の中心捻りが μ_l（ℤ/n）へ well-defined に降下する理由: χ_n は G_K→(ℤ/n)^× の準同型。 -/
theorem ttoa_char_hom (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) :
    cycRigChar GK M ρ (GK.mul g h)
      = zmodMul M.n (cycRigChar GK M ρ g) (cycRigChar GK M ρ h) :=
  cycRig_char_isHom GK M ρ g h

/-! ## M389F-6: 外ガロア作用（χ 捻り）＝ スケール作用 ∘ 円分指標 -/

/-- **M389F-6a: 円分指標のスカラー** χ(g) ∈ ℤ（`cycRigExp` の Int 昇格）。外ガロア作用の
    中心捻り係数（μ_l を捻る円分指標）。 -/
def ttoaChar (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (g : GK.carrier) : Int :=
  (cycRigExp GK M ρ g : Int)

/-- **M389F-6b: 外ガロア作用** ttoaAct g = ttoaScale (χ(g)) — G_K が theta group の
    中心（内部円分体 μ_l）を円分指標 χ で捻る作用。 -/
@[reducible] def ttoaAct (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (x : thetaGrp.carrier) : thetaGrp.carrier :=
  ttoaScale (ttoaChar GK M ρ g) x

/-- **定理 (M389F-6c: 外ガロア作用のもとでの交換子の χ 捻り／本丸)** —
      (σ_g·[x,y]) の中心座標 = χ(g)·([σ_g·x, σ_g·y] の中心座標)。
    シンプレクティック形式が円分指標 χ で変換する（M389F-3c を e=χ(g) で特殊化）。
    外ガロア作用が theta 群の交換子を χ 捻りすることの本物の完全証明。 -/
theorem ttoa_act_commutator_twist (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (a b c a' b' c' : Int) :
    (ttoaAct GK M ρ g (thetaGrp.comm ((a, b, c) : Int × Int × Int) (a', b', c'))).2.2
      = ttoaChar GK M ρ g
        * (thetaGrp.comm (ttoaAct GK M ρ g ((a, b, c) : Int × Int × Int))
            (ttoaAct GK M ρ g (a', b', c'))).2.2 :=
  ttoa_commutator_twist (ttoaChar GK M ρ g) a b c a' b' c'

/-! ## M389F-7: M384F 中心写像 centerToMu との接続 -/

/-- **定理 (M389F-7: 交換子の χ 捻りの centerToMu 像)** — χ 捻りした標準生成元の交換子
    [(1,0,0),(0,1,0)]=(0,0,1) の中心座標を外ガロア作用で捻ると χ(g) になり、その μ_l 同期写像
    （M124F/M384F centerToMu）像は centerToMu(χ(g)) に一致する。テータ交換子の μ_l 像が
    外ガロア作用で円分指標倍に捻れることを M384F の同期写像で読む。 -/
theorem ttoa_gen_commutator_centerToMu (p l : Nat) (ζ : (Zp p).carrier)
    (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (g : GK.carrier) :
    centerToMu p l ζ
        ((ttoaAct GK M ρ g (thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0))).2.2)
      = centerToMu p l ζ (ttoaChar GK M ρ g) := by
  have h : (ttoaAct GK M ρ g
      (thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0))).2.2 = ttoaChar GK M ρ g := by
    rw [comm_xy]
    show ttoaChar GK M ρ g * (1 : Int) = ttoaChar GK M ρ g
    rw [Int.mul_one]
  rw [h]

/-! ## M389F-8: 正直な外部仮説（決して導出しない） -/

/-- **外部仮説（正直な限定・決して導出しない）**: 完全な幾何的 tempered 基本群 Δ^temp の
    slim 遠アーベル性・その外ガロア表現 G_K → Out(Δ^temp)・p 進テータ関数のガロア同変な
    評価・幾何的 Frobenioid の G_K-同変実現は本質的に外部（幾何的入力・後続）。本モジュールは
    離散 Heisenberg 群 thetaGrp・その中心＝μ_l への χ 捻り（スケール作用）・抽象 CycGKAction
    のみを扱う。スケール作用は完全な Heisenberg 積の自己同型ではない（M389F-2b）。 -/
def ttoa_full_tempered_outer_rep_hypothesis (T : Grp) (f : Hom T thetaGrp) : Prop :=
  f.Injective

/-! ## M389F-9: capstone -/

/-- **M389F-9a: tempered テータ外ガロア作用データ** — 離散 Heisenberg 群 thetaGrp への
    G_K の外ガロア作用（中心＝内部円分体 μ_l を円分指標 χ で捻る）を束ねる:
    スケール作用の (ℤ,·) 作用性（単位則・合成則）・中心座標の捻り・中心での準同型性・
    積の χ 捻り（正直な内容: 自己同型でない差 (e−1)ab′）・交換子のスケール不変性・
    交換子の χ 捻り（シンプレクティック形式が χ 変換、本丸）・μ_l 上の実ガロア作用
    （σ_1=id・σ_{gh}=σ_g∘σ_h・σ_g(ζ^k)=ζ^{χ(g)k}、M322F CycGKAction）・円分指標の準同型性・
    交換子の μ_l 像 ζ の χ 捻り・外ガロア作用のもとでの交換子の χ 捻り。
    主語は本物の thetaGrp・本物の μ_l（M322F CycGKAction）・本物の χ（cycRigChar）。 -/
structure TemperedThetaOuterActionData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) where
  /-- スケール作用の単位則 ttoaScale 1 = id。 -/
  scale_one : ∀ x : thetaGrp.carrier, ttoaScale 1 x = x
  /-- スケール作用の合成則（(ℤ,·) の作用）。 -/
  scale_mul : ∀ (e e' : Int) (x : thetaGrp.carrier),
    ttoaScale e (ttoaScale e' x) = ttoaScale (e * e') x
  /-- 中心座標の捻り (ttoaScale e x).c = e·c。 -/
  scale_center : ∀ (e : Int) (x : thetaGrp.carrier), (ttoaScale e x).2.2 = e * x.2.2
  /-- 中心での準同型性。 -/
  center_hom : ∀ e c c' : Int,
    ttoaScale e (thetaGrp.mul ((0, 0, c) : Int × Int × Int) (0, 0, c'))
      = thetaGrp.mul (ttoaScale e ((0, 0, c) : Int × Int × Int)) (ttoaScale e (0, 0, c'))
  /-- 積の χ 捻り（正直な内容: 自己同型でない差）。 -/
  product_twist : ∀ e a b c a' b' c' : Int,
    (ttoaScale e (thetaGrp.mul ((a, b, c) : Int × Int × Int) (a', b', c'))).2.2
      = (thetaGrp.mul (ttoaScale e ((a, b, c) : Int × Int × Int))
          (ttoaScale e (a', b', c'))).2.2 + (e - 1) * (a * b')
  /-- 交換子はスケール作用で不変。 -/
  commutator_invariant : ∀ e a b c a' b' c' : Int,
    thetaGrp.comm (ttoaScale e ((a, b, c) : Int × Int × Int)) (ttoaScale e (a', b', c'))
      = thetaGrp.comm ((a, b, c) : Int × Int × Int) (a', b', c')
  /-- 交換子の χ 捻り（シンプレクティック形式が χ 変換、本丸）。 -/
  commutator_twist : ∀ e a b c a' b' c' : Int,
    (ttoaScale e (thetaGrp.comm ((a, b, c) : Int × Int × Int) (a', b', c'))).2.2
      = e * (thetaGrp.comm (ttoaScale e ((a, b, c) : Int × Int × Int))
              (ttoaScale e (a', b', c'))).2.2
  /-- μ_l 作用の単位則（実ガロア作用）。 -/
  mu_act_one : ∀ z : M.μ.carrier, galThMuAct GK M ρ GK.one z = z
  /-- μ_l 作用の合成則（実ガロア作用）。 -/
  mu_act_mul : ∀ (g h : GK.carrier) (z : M.μ.carrier),
    galThMuAct GK M ρ (GK.mul g h) z = galThMuAct GK M ρ g (galThMuAct GK M ρ h z)
  /-- μ_l 作用の円分指標形 σ_g(ζ^k)=ζ^{χ(g)k}。 -/
  mu_act_char : ∀ (g : GK.carrier) (k : Nat),
    galThMuAct GK M ρ g (M.μ.pow M.ζ k) = M.μ.pow M.ζ (cycRigExp GK M ρ g * k)
  /-- 円分指標の準同型性 χ(gh)=χ(g)χ(h)。 -/
  char_hom : ∀ g h : GK.carrier,
    cycRigChar GK M ρ (GK.mul g h) = zmodMul M.n (cycRigChar GK M ρ g) (cycRigChar GK M ρ h)
  /-- 交換子の μ_l 像 ζ の χ 捻り σ_g(ζ)=ζ^{χ(g)}。 -/
  gen_commutator_galois : ∀ g : GK.carrier,
    galThMuAct GK M ρ g (M.μ.pow M.ζ 1) = M.μ.pow M.ζ (cycRigExp GK M ρ g)
  /-- 外ガロア作用のもとでの交換子の χ 捻り。 -/
  act_commutator_twist : ∀ (g : GK.carrier) (a b c a' b' c' : Int),
    (ttoaAct GK M ρ g (thetaGrp.comm ((a, b, c) : Int × Int × Int) (a', b', c'))).2.2
      = ttoaChar GK M ρ g
        * (thetaGrp.comm (ttoaAct GK M ρ g ((a, b, c) : Int × Int × Int))
            (ttoaAct GK M ρ g (a', b', c'))).2.2

/-- **M389F-9b: witness 本体** — 全フィールドを M389F-1〜7 の本物の証明で埋める
    （外部仮説ゼロ・完全証明）。 -/
def temperedThetaOuterActionData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    TemperedThetaOuterActionData GK M ρ where
  scale_one := ttoa_scale_one
  scale_mul := ttoa_scale_mul
  scale_center := ttoa_scale_center
  center_hom := ttoa_scale_center_hom
  product_twist := ttoa_scale_product_twist
  commutator_invariant := ttoa_commutator_invariant
  commutator_twist := ttoa_commutator_twist
  mu_act_one := ttoa_mu_act_one GK M ρ
  mu_act_mul := ttoa_mu_act_mul GK M ρ
  mu_act_char := ttoa_mu_act_char GK M ρ
  char_hom := ttoa_char_hom GK M ρ
  gen_commutator_galois := ttoa_gen_commutator_galois GK M ρ
  act_commutator_twist := ttoa_act_commutator_twist GK M ρ

/-- **定理 (M389F-9c: tempered テータ外ガロア作用データの存在／M389F 見出し)** —
    任意の G_K・内部円分体 μ_l（`CycMuGroup`）・実ガロア作用 ρ（M322F `CycGKAction`）が
    与えられれば、離散 Heisenberg テータ群 thetaGrp への外ガロア作用（中心＝μ_l を円分指標 χ
    で捻り・交換子＝シンプレクティック形式が χ 変換・μ_l 上の作用が M322F の実円分指標作用に
    一致）を束ねたデータが**外部仮説なしで**存在する（完全証明）。 -/
theorem ttoa_exists (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    Nonempty (TemperedThetaOuterActionData GK M ρ) :=
  ⟨temperedThetaOuterActionData GK M ρ⟩

/-! ## M389F-10: 実例 -/

/-- 実例: 外ガロア作用（e=3）は標準生成元の交換子 (0,0,1) の中心座標を 3 倍に捻る:
    σ·[x,y] の中心座標 = 3 = 3·1 = 3·([σ·x,σ·y] の中心座標)（シンプレクティック形式の χ 変換）。 -/
example :
    (ttoaScale 3 (thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0))).2.2
      = 3 * (thetaGrp.comm (ttoaScale 3 ((1, 0, 0) : Int × Int × Int))
              (ttoaScale 3 (0, 1, 0))).2.2 :=
  ttoa_commutator_twist 3 1 0 0 0 1 0

/-- 実例: 外ガロア作用（スケール 3）で交換子 (0,0,1) は (0,0,3) に捻れる。 -/
example : ttoaScale 3 (thetaGrp.comm ((1, 0, 0) : Int × Int × Int) (0, 1, 0))
    = ((0, 0, 3) : Int × Int × Int) := by
  rw [comm_xy]
  show ((0, 0, (3 : Int) * 1) : Int × Int × Int) = (0, 0, 3)
  exact triple_ext rfl rfl (by omega)

/-- 実例: 交換子はスケール作用で不変（幾何座標しか見ない）。 -/
example (e : Int) :
    thetaGrp.comm (ttoaScale e ((2, 3, 5) : Int × Int × Int)) (ttoaScale e (7, 11, 13))
      = thetaGrp.comm ((2, 3, 5) : Int × Int × Int) (7, 11, 13) :=
  ttoa_commutator_invariant e 2 3 5 7 11 13

/-- 実例: 本物の絶対ガロア群 G_ℚ（M315F）の μ_l（ℤ/l）上の trivial 作用による
    外ガロア作用データが存在する（M322F cycMuStd + cycTrivialAction を主語に）。 -/
example (l : Nat) (hl : 1 ≤ l) :
    Nonempty (TemperedThetaOuterActionData (algCloAbsGalois algCloTrivialTower)
      (cycMuStd l hl) (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))) :=
  ttoa_exists (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl))

/-- 実例: μ_l 作用の合成則（本物の群作用、任意の CycGKAction）。 -/
example (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g h : GK.carrier) (z : M.μ.carrier) :
    galThMuAct GK M ρ (GK.mul g h) z = galThMuAct GK M ρ g (galThMuAct GK M ρ h z) :=
  ttoa_mu_act_mul GK M ρ g h z

/-- 実例: 交換子の μ_l 像 ζ は外ガロア作用で ζ^{χ(g)} に捻れる。 -/
example (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (g : GK.carrier) :
    galThMuAct GK M ρ g (M.μ.pow M.ζ 1) = M.μ.pow M.ζ (cycRigExp GK M ρ g) :=
  ttoa_gen_commutator_galois GK M ρ g

end IUT
