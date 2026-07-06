/-
  IUT/WeilGaloisEquiv.lean — M344F [実／本物]
  分類: 実 (Weil ペアリングのガロア同変性 e_n(σP,σQ)=χ(σ)·e_n(P,Q))
  complete_pct 影響: 柱A を前進（M339F Weil ペアリングの「ガロア同変性は後続」限定を閉じ、
    e_n(σP,σQ)=χ(σ)e_n(P,Q) を本物で＝ペアリングが円分指標 χ を見る・M343F と接続）。
  正直な限定: G_K の E_q[n]=ℤ/n×ℤ/n への作用は、Tate 一意化の生成元 ζ_n（円分方向）と
    Q=q^{1/n}（周期方向）への作用の形——σ(ζ^aQ^b)=ζ^{χ(σ)a+β(σ)b}Q^b——から本物で
    構成する（上三角行列 [[χ,β],[0,1]]、χ=円分指標・β=Kummer 捻り指数）。作用が本物の
    群作用をなすこと（σ_1=id・σ_{gh}=σ_g∘σ_h、捻り β の 1-コサイクル則込み）・
    determinant 形式 e_n=ad−bc が χ 倍にスケールすること（同変性）・固定点での不変性・
    円分指標 χ=M322F `cycRigChar` との一致を core Lean のみで完全証明する。ただし
    (i) β の捻りコサイクル則（β(gh)=χ(g)β(h)+β(g)）は `WeilGKAction` の構造フィールドとして
    受ける（実 Kummer 指標 κ:G_K→μ_n からの供給は柱E 後続。実例では trivial β≡0 を与える）、
    (ii) 完全な幾何的 Weil ペアリング（ℓ-進 Tate 加群のカップ積）の G_K 表現との一致は
    外部仮説 `wge_*_hypothesis`（決して導出しない）。ここでは座標 (a,b) への上三角作用と
    e_n の χ スケーリングを本物で閉じる（toy を主語にしない・M339F の限定を実際に閉じる）。

  * M344F-1 整数恒等式 `wge_int_equivariant`（determinant の χ スケール核）・
    `wge_int_actmul`（作用合成の捻りコサイクル核）
  * M344F-2 `WeilGKAction` — G_K の E_q[n] への上三角作用データ（χ・β と単位/合成/コサイクル則）
  * M344F-3 `wgeTorAct` — 作用本体・`wge_tor_act_one`/`wge_tor_act_mul`（本物の群作用）
  * M344F-4 `wge_equivariant` — e_n(σP,σQ)=χ(σ)·e_n(P,Q)（同変性・本丸）
  * M344F-5 `wge_fixed_pairing` — 固定点でのペアリング不変性
  * M344F-6 `wgeCharAction`/`wge_kummer_compat`/`wge_equivariant_char` — 円分指標 χ との接続
  * M344F-7 外部仮説（幾何的 Weil ペアリングの G_K 表現・決して導出しない）
  * M344F-8 capstone `WeilGaloisEquivData`/`wge_exists` + 実例（n=3・trivial 作用）

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用。共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
  一般名は `wge` 接頭辞で衝突回避。
-/
import IUT.WeilPairing
import IUT.GaloisTheta

namespace IUT

/-! ## M344F-1: 整数恒等式（determinant の χ スケール核・作用合成の捻りコサイクル核） -/

/-- **M344F-1a: determinant の χ スケール核** — 上三角作用 (a,b)↦(χa+βb, b) の下で
    determinant 形式が χ 倍にスケール:
      (χa+βb)·d − b·(χc+βd) = χ·(a·d − b·c)。
    交叉項 β·b·d が相殺し、Weil ペアリングの Galois 同変因子が χ だけになることの整数核。 -/
theorem wge_int_equivariant (chi beta a b c d : Int) :
    (chi * a + beta * b) * d + -(b * (chi * c + beta * d))
      = chi * (a * d + -(b * c)) := by
  have e1 : (chi * a + beta * b) * d = chi * (a * d) + beta * (b * d) := by
    rw [Int.add_mul, Int.mul_assoc, Int.mul_assoc]
  have e2 : b * (chi * c + beta * d) = chi * (b * c) + beta * (b * d) := by
    rw [Int.mul_add, ← Int.mul_assoc b chi c, Int.mul_comm b chi, Int.mul_assoc chi b c,
      ← Int.mul_assoc b beta d, Int.mul_comm b beta, Int.mul_assoc beta b d]
  have e3 : chi * (a * d + -(b * c)) = chi * (a * d) + -(chi * (b * c)) := by
    rw [Int.mul_add, Int.mul_neg]
  rw [e1, e2, e3]
  generalize chi * (a * d) = X
  generalize beta * (b * d) = Y
  generalize chi * (b * c) = Z
  omega

/-- **M344F-1b: 作用合成の捻りコサイクル核** — 上三角行列の積
      [[χg,βg],[0,1]]·[[χh,βh],[0,1]] = [[χg·χh, χg·βh+βg],[0,1]]
    の第 1 座標成分:
      (χg·χh)·a + (χg·βh+βg)·b = χg·(χh·a + βh·b) + βg·b。
    G_K 作用が本物の群作用（σ_{gh}=σ_g∘σ_h）をなすことの整数核。 -/
theorem wge_int_actmul (cg ch bg bh a b : Int) :
    (cg * ch) * a + (cg * bh + bg) * b
      = cg * (ch * a + bh * b) + bg * b := by
  rw [Int.add_mul (cg * bh) bg b, Int.mul_add cg (ch * a) (bh * b),
    Int.mul_assoc cg ch a, Int.mul_assoc cg bh b]
  generalize cg * (ch * a) = X
  generalize cg * (bh * b) = Y
  generalize bg * b = Z
  omega

/-! ## M344F-1c: ℤ/n 上の補助計算則（作用の座標計算） -/

/-- **M344F-1c-i: 1 倍は恒等** — ℤ/n の乗法で class 1 を掛けるのは恒等。 -/
theorem wge_zmul_one (n : Nat) (x : (zmod n).carrier) :
    zmodMul n (Quot.mk (modCong n).rel 1) x = x := by
  induction x using Quot.ind; rename_i a
  show Quot.mk (modCong n).rel (1 * a) = Quot.mk (modCong n).rel a
  have h : (1 : Int) * a = a := by omega
  rw [h]

/-- **M344F-1c-ii: 0 倍は零** — ℤ/n の乗法で class 0 を掛けるのは零元。 -/
theorem wge_zmul_zero (n : Nat) (x : (zmod n).carrier) :
    zmodMul n x (Quot.mk (modCong n).rel 0) = Quot.mk (modCong n).rel 0 := by
  induction x using Quot.ind; rename_i a
  show Quot.mk (modCong n).rel (a * 0) = Quot.mk (modCong n).rel 0
  rw [Int.mul_zero]

/-! ## M344F-2: G_K の E_q[n]=ℤ/n×ℤ/n への上三角作用データ -/

/-- **M344F-2: G_K の E_q[n] への上三角作用データ** — Tate 一意化での n-捻れ点
    P=ζ_n^a·Q^b（Q=q^{1/n}）に、各 g∈G_K は
      σ_g(ζ_n) = ζ_n^{χ(g)}   （円分指標 χ の作用）,
      σ_g(Q)   = ζ_n^{β(g)}·Q（Kummer 捻り β の作用）
    から σ_g(ζ^aQ^b)=ζ^{χ(g)a+β(g)b}Q^b、すなわち座標に上三角行列
    [[χ(g),β(g)],[0,1]] で作用する。χ は乗法的（円分指標）・β は捻り 1-コサイクル
    （β(gh)=χ(g)β(h)+β(g)）。IUT の l-捻れ点への G_K 作用の本物の代数構造。 -/
structure WeilGKAction (GK : Grp) (n : Nat) where
  /-- 円分指標成分 χ : G_K → ℤ/n（ζ_n への作用の指数）。 -/
  chi : GK.carrier → (zmod n).carrier
  /-- Kummer 捻り成分 β : G_K → ℤ/n（Q=q^{1/n} への μ_n 捻りの指数）。 -/
  beta : GK.carrier → (zmod n).carrier
  /-- χ(1)=1（単位元での円分指標は自明）。 -/
  chi_one : chi GK.one = Quot.mk (modCong n).rel 1
  /-- χ(g·h)=χ(g)·χ(h)（円分指標の乗法性・M322F `cycRig_char_isHom`）。 -/
  chi_mul : ∀ g h, chi (GK.mul g h) = zmodMul n (chi g) (chi h)
  /-- β(1)=0（単位元では捻り無し）。 -/
  beta_one : beta GK.one = Quot.mk (modCong n).rel 0
  /-- β(g·h)=χ(g)·β(h)+β(g)（捻り 1-コサイクル則・半直積作用）。 -/
  beta_mul : ∀ g h, beta (GK.mul g h)
    = (zmod n).mul (zmodMul n (chi g) (beta h)) (beta g)

/-! ## M344F-3: 作用本体と群作用性 -/

/-- **M344F-3a: E_q[n] への上三角作用本体** — σ_g(ζ^aQ^b)=ζ^{χ(g)a+β(g)b}Q^b。
    座標 (a,b) を (χ(g)·a+β(g)·b, b) に送る（z 方向のみ捻り、q 方向は保存）。 -/
def wgeTorAct (GK : Grp) (n : Nat) (ρ : WeilGKAction GK n) (g : GK.carrier)
    (P : WeilTorsion n) : WeilTorsion n :=
  ⟨(zmod n).mul (zmodMul n (ρ.chi g) P.zExp) (zmodMul n (ρ.beta g) P.qExp), P.qExp⟩

/-- **M344F-3b: 単位元の作用は恒等** σ_1=id（χ(1)=1・β(1)=0）。 -/
theorem wge_tor_act_one (GK : Grp) (n : Nat) (ρ : WeilGKAction GK n)
    (P : WeilTorsion n) :
    wgeTorAct GK n ρ GK.one P = P := by
  cases P with
  | mk a b =>
    show WeilTorsion.mk
        ((zmod n).mul (zmodMul n (ρ.chi GK.one) a) (zmodMul n (ρ.beta GK.one) b)) b
      = WeilTorsion.mk a b
    rw [ρ.chi_one, ρ.beta_one]
    induction a using Quot.ind; rename_i a
    induction b using Quot.ind; rename_i b
    show WeilTorsion.mk (Quot.mk (modCong n).rel (1 * a + 0 * b))
        (Quot.mk (modCong n).rel b)
      = WeilTorsion.mk (Quot.mk (modCong n).rel a) (Quot.mk (modCong n).rel b)
    have h : (1 : Int) * a + 0 * b = a := by omega
    rw [h]

/-- **M344F-3c: 座標 z-成分の合成則**（作用合成の捻りコサイクル核の ℤ/n 版）。 -/
theorem wge_zexp_actmul (n : Nat) (cg ch bg bh a b : (zmod n).carrier) :
    (zmod n).mul (zmodMul n (zmodMul n cg ch) a)
        (zmodMul n ((zmod n).mul (zmodMul n cg bh) bg) b)
      = (zmod n).mul
          (zmodMul n cg ((zmod n).mul (zmodMul n ch a) (zmodMul n bh b)))
          (zmodMul n bg b) := by
  induction cg using Quot.ind; rename_i cg
  induction ch using Quot.ind; rename_i ch
  induction bg using Quot.ind; rename_i bg
  induction bh using Quot.ind; rename_i bh
  induction a using Quot.ind; rename_i a
  induction b using Quot.ind; rename_i b
  show Quot.mk (modCong n).rel ((cg * ch) * a + (cg * bh + bg) * b)
     = Quot.mk (modCong n).rel (cg * (ch * a + bh * b) + bg * b)
  rw [wge_int_actmul cg ch bg bh a b]

/-- **M344F-3d: 合成の作用は作用の合成** σ_{g·h}=σ_g∘σ_h（本物の群作用）。
    χ の乗法性と β の捻り 1-コサイクル則から、上三角作用が G_K の作用をなす。 -/
theorem wge_tor_act_mul (GK : Grp) (n : Nat) (ρ : WeilGKAction GK n)
    (g h : GK.carrier) (P : WeilTorsion n) :
    wgeTorAct GK n ρ (GK.mul g h) P
      = wgeTorAct GK n ρ g (wgeTorAct GK n ρ h P) := by
  cases P with
  | mk a b =>
    show WeilTorsion.mk
        ((zmod n).mul (zmodMul n (ρ.chi (GK.mul g h)) a)
          (zmodMul n (ρ.beta (GK.mul g h)) b)) b
      = WeilTorsion.mk
          ((zmod n).mul
            (zmodMul n (ρ.chi g)
              ((zmod n).mul (zmodMul n (ρ.chi h) a) (zmodMul n (ρ.beta h) b)))
            (zmodMul n (ρ.beta g) b)) b
    rw [ρ.chi_mul g h, ρ.beta_mul g h, wge_zexp_actmul]

/-! ## M344F-4: ガロア同変性（本丸）— e_n(σP,σQ)=χ(σ)·e_n(P,Q) -/

/-- **M344F-4a: determinant の χ スケール（座標版）** — 上三角作用の下で
    e_n((χa+βb,b),(χc+βd,d)) = χ·e_n(a,b,c,d)。交叉項 β·b·d が相殺する。 -/
theorem wge_pairing_scale (n : Nat) (chi beta a b c d : (zmod n).carrier) :
    weilPairing n
        ((zmod n).mul (zmodMul n chi a) (zmodMul n beta b)) b
        ((zmod n).mul (zmodMul n chi c) (zmodMul n beta d)) d
      = zmodMul n chi (weilPairing n a b c d) := by
  induction chi using Quot.ind; rename_i chi
  induction beta using Quot.ind; rename_i beta
  induction a using Quot.ind; rename_i a
  induction b using Quot.ind; rename_i b
  induction c using Quot.ind; rename_i c
  induction d using Quot.ind; rename_i d
  show Quot.mk (modCong n).rel ((chi * a + beta * b) * d + -(b * (chi * c + beta * d)))
     = Quot.mk (modCong n).rel (chi * (a * d + -(b * c)))
  rw [wge_int_equivariant chi beta a b c d]

/-- **M344F-4b: ガロア同変性（本丸）** — e_n(σ_g·P, σ_g·Q) = χ(g)·e_n(P,Q)。
    Weil ペアリング（determinant 双線形形式）は G_K の上三角作用の下で円分指標 χ 倍に
    スケールする＝ペアリングが円分指標 χ を「見る」。M339F の限定「ガロア同変性は後続」を
    本物で閉じる柱A の前進。 -/
theorem wge_equivariant (GK : Grp) (n : Nat) (ρ : WeilGKAction GK n) (g : GK.carrier)
    (P Q : WeilTorsion n) :
    weilPairingPt n (wgeTorAct GK n ρ g P) (wgeTorAct GK n ρ g Q)
      = zmodMul n (ρ.chi g) (weilPairingPt n P Q) := by
  cases P with
  | mk a b =>
    cases Q with
    | mk c d =>
      exact wge_pairing_scale n (ρ.chi g) (ρ.beta g) a b c d

/-! ## M344F-5: 固定点でのペアリング不変性（χ=1 / 自明作用の帰結） -/

/-- **M344F-5: 固定点でのペアリング不変性** — P・Q がともに σ_g で固定される
    （σ_g·P=P・σ_g·Q=Q）なら χ(g)·e_n(P,Q)=e_n(P,Q)。ガロア固定点上でペアリングの
    円分捻りが消える（χ(g) 因子が自明化する）。同変性 e_n(σP,σQ)=χ e_n の固定点特殊化。 -/
theorem wge_fixed_pairing (GK : Grp) (n : Nat) (ρ : WeilGKAction GK n) (g : GK.carrier)
    (P Q : WeilTorsion n)
    (hP : wgeTorAct GK n ρ g P = P) (hQ : wgeTorAct GK n ρ g Q = Q) :
    zmodMul n (ρ.chi g) (weilPairingPt n P Q) = weilPairingPt n P Q := by
  have h := wge_equivariant GK n ρ g P Q
  rw [hP, hQ] at h
  exact h.symm

/-! ## M344F-6: 円分指標 χ=M322F `cycRigChar` との接続 -/

/-- **M344F-6a: 円分指標由来の上三角作用** — M322F の円分指標 χ_n=`cycRigChar` を
    z-方向の作用に、β≡0（trivial Kummer 捻り）を q-方向に据えた `WeilGKAction`。
    χ の乗法性・χ(1)=1 は M322F `cycRig_char_isHom`/`cycRig_char_one` で本物に埋まる。
    非自明な β を与える実 Kummer 指標 κ:G_K→μ_n の供給は柱E 後続。 -/
def wgeCharAction (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) :
    WeilGKAction GK M.n where
  chi := cycRigChar GK M ρ
  beta := fun _ => Quot.mk (modCong M.n).rel 0
  chi_one := cycRig_char_one GK M ρ
  chi_mul := cycRig_char_isHom GK M ρ
  beta_one := rfl
  beta_mul := fun g _ => by
    show Quot.mk (modCong M.n).rel 0
       = (zmod M.n).mul
          (zmodMul M.n (cycRigChar GK M ρ g) (Quot.mk (modCong M.n).rel 0))
          (Quot.mk (modCong M.n).rel 0)
    rw [wge_zmul_zero M.n (cycRigChar GK M ρ g)]
    show Quot.mk (modCong M.n).rel 0 = Quot.mk (modCong M.n).rel (0 + 0)
    have h : (0 : Int) + 0 = 0 := by omega
    rw [h]

/-- **M344F-6b: Kummer 互換性** — `wgeCharAction` の円分成分は M322F の円分指標
    χ_n=`cycRigChar` に一致する。Weil ペアリングの同変因子が本物の円分指標であること
    （ペアリングが χ を見る・M343F/M322F と接続）。 -/
theorem wge_kummer_compat (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) :
    (wgeCharAction GK M ρ).chi g = cycRigChar GK M ρ g := rfl

/-- **M344F-6c: 円分指標での同変性** — e_n(σ_g·P, σ_g·Q) = χ_n(g)·e_n(P,Q)、
    χ_n=`cycRigChar`（本物の円分指標）。M339F Weil ペアリング + M343F GaloisTheta +
    M322F 円分剛性を接続した「Weil ペアリングは円分指標を見る」の本物の形。 -/
theorem wge_equivariant_char (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (P Q : WeilTorsion M.n) :
    weilPairingPt M.n (wgeTorAct GK M.n (wgeCharAction GK M ρ) g P)
        (wgeTorAct GK M.n (wgeCharAction GK M ρ) g Q)
      = zmodMul M.n (cycRigChar GK M ρ g) (weilPairingPt M.n P Q) :=
  wge_equivariant GK M.n (wgeCharAction GK M ρ) g P Q

/-! ## M344F-7: 外部仮説（幾何的 Weil ペアリングの G_K 表現・決して導出しない） -/

/-- **M344F-7a: 幾何的同変性仮説（Prop）** — 完全な幾何的 Weil ペアリング
    （ℓ-進 Tate 加群のカップ積による定義）に付随する G_K の E_q[n] への幾何的作用
    `geomAct` が、本モジュールの上三角作用 `wgeTorAct` に一致するという**外部仮説**。
    実の Tate 加群・エタールコホモロジーのカップ積から来る作用がこの座標形を取ることは
    柱A/E の外部入力であり、本層はこれを明示の Prop 仮説として受け、決して導出しない。 -/
def wge_geometric_equivariance_hypothesis (GK : Grp) (n : Nat) (ρ : WeilGKAction GK n)
    (geomAct : GK.carrier → WeilTorsion n → WeilTorsion n) : Prop :=
  ∀ g P, geomAct g P = wgeTorAct GK n ρ g P

/-- **M344F-7b: 幾何的同変性の復元（仮説依存）** — 仮説
    `wge_geometric_equivariance_hypothesis` の下で、幾何的作用は本モジュールの上三角作用に
    一致し、したがって幾何的 Weil ペアリングも χ 倍にスケールする。仮説は外部入力で導出しない。 -/
theorem wge_geometric_recovery (GK : Grp) (n : Nat) (ρ : WeilGKAction GK n)
    (geomAct : GK.carrier → WeilTorsion n → WeilTorsion n)
    (hyp : wge_geometric_equivariance_hypothesis GK n ρ geomAct)
    (g : GK.carrier) (P Q : WeilTorsion n) :
    weilPairingPt n (geomAct g P) (geomAct g Q)
      = zmodMul n (ρ.chi g) (weilPairingPt n P Q) := by
  rw [hyp g P, hyp g Q]
  exact wge_equivariant GK n ρ g P Q

/-! ## M344F-8: capstone -/

/-- **M344F-8a: Weil ペアリングのガロア同変性データ** — G_K の上三角作用 ρ・その群作用性
    （σ_1=id・σ_{gh}=σ_g∘σ_h）・ガロア同変性 e_n(σP,σQ)=χ(σ)e_n(P,Q) を束ねる。
    M339F Weil ペアリングの「ガロア同変性は後続」限定を閉じる総括。 -/
structure WeilGaloisEquivData (GK : Grp) (n : Nat) where
  /-- G_K の E_q[n] への上三角作用データ。 -/
  ρ : WeilGKAction GK n
  /-- 作用本体。 -/
  act : GK.carrier → WeilTorsion n → WeilTorsion n
  /-- act = wgeTorAct。 -/
  act_eq : ∀ g P, act g P = wgeTorAct GK n ρ g P
  /-- 単位元の作用は恒等。 -/
  act_one : ∀ P, act GK.one P = P
  /-- 合成の作用は作用の合成。 -/
  act_mul : ∀ g h P, act (GK.mul g h) P = act g (act h P)
  /-- ガロア同変性 e_n(σP,σQ)=χ(σ)·e_n(P,Q)。 -/
  equivariant : ∀ g P Q, weilPairingPt n (act g P) (act g Q)
    = zmodMul n (ρ.chi g) (weilPairingPt n P Q)

/-- **M344F-8b: 証人** — 任意の上三角作用 ρ からガロア同変性データを本物で組む。 -/
def wgeData (GK : Grp) (n : Nat) (ρ : WeilGKAction GK n) :
    WeilGaloisEquivData GK n where
  ρ := ρ
  act := wgeTorAct GK n ρ
  act_eq := fun _ _ => rfl
  act_one := wge_tor_act_one GK n ρ
  act_mul := wge_tor_act_mul GK n ρ
  equivariant := wge_equivariant GK n ρ

/-- **M344F-8c: capstone — Weil ペアリングのガロア同変性の存在** — 任意の G_K・n・
    上三角作用に対し、Weil ペアリングのガロア同変構造（本物の群作用 + e_n(σP,σQ)=χ e_n）が
    組み上がる。M339F の限定「ガロア同変性は後続」が閉じる。 -/
theorem wge_exists (GK : Grp) (n : Nat) (ρ : WeilGKAction GK n) :
    Nonempty (WeilGaloisEquivData GK n) :=
  ⟨wgeData GK n ρ⟩

/-! ## M344F-9: 実例（n=3・trivial 作用） -/

/-- **M344F-9a: trivial 上三角作用**（χ≡1・β≡0、不分岐点 σ(ζ)=ζ・σ(Q)=Q）。
    本物の群作用の実例化のための作用。非自明 χ/β を与える実 Galois 降下は柱A/E 後続。 -/
def wgeTrivialAction (GK : Grp) (n : Nat) : WeilGKAction GK n where
  chi := fun _ => Quot.mk (modCong n).rel 1
  beta := fun _ => Quot.mk (modCong n).rel 0
  chi_one := rfl
  chi_mul := fun _ _ => by
    show Quot.mk (modCong n).rel 1
       = zmodMul n (Quot.mk (modCong n).rel 1) (Quot.mk (modCong n).rel 1)
    show Quot.mk (modCong n).rel 1 = Quot.mk (modCong n).rel (1 * 1)
    have h : (1 : Int) * 1 = 1 := by omega
    rw [h]
  beta_one := rfl
  beta_mul := fun _ _ => by
    show Quot.mk (modCong n).rel 0
       = (zmod n).mul
          (zmodMul n (Quot.mk (modCong n).rel 1) (Quot.mk (modCong n).rel 0))
          (Quot.mk (modCong n).rel 0)
    rw [wge_zmul_zero n (Quot.mk (modCong n).rel 1)]
    show Quot.mk (modCong n).rel 0 = Quot.mk (modCong n).rel (0 + 0)
    have h : (0 : Int) + 0 = 0 := by omega
    rw [h]

/-- **M344F-9b: 実例 — n=3 で Weil ペアリングのガロア同変性データが存在する**。 -/
theorem wge_example_n3_exists (GK : Grp) :
    Nonempty (WeilGaloisEquivData GK 3) :=
  wge_exists GK 3 (wgeTrivialAction GK 3)

/-- **M344F-9c: 実例 — n=3・trivial 作用で e_3(σP,σQ)=1·e_3(P,Q)=e_3(P,Q)**
    （χ≡1 ゆえペアリングは不変）。 -/
theorem wge_example_n3_invariant (GK : Grp) (g : GK.carrier) (P Q : WeilTorsion 3) :
    weilPairingPt 3 (wgeTorAct GK 3 (wgeTrivialAction GK 3) g P)
        (wgeTorAct GK 3 (wgeTrivialAction GK 3) g Q)
      = weilPairingPt 3 P Q := by
  rw [wge_equivariant GK 3 (wgeTrivialAction GK 3) g P Q]
  exact wge_zmul_one 3 (weilPairingPt 3 P Q)

/-- **M344F-9d: 実例 — 本物の G_ℚ の μ_5 上で Weil ペアリングが円分指標 χ_5 を見る**
    （M322F の本物の絶対ガロア群 G_ℚ の trivial 作用由来の χ_5=`cycRigChar` で同変）。 -/
theorem wge_example_galois_char (g : (algCloAbsGalois algCloTrivialTower).carrier)
    (P Q : WeilTorsion 5) :
    weilPairingPt 5
        (wgeTorAct (algCloAbsGalois algCloTrivialTower) 5
          (wgeCharAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
            (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))))
          g P)
        (wgeTorAct (algCloAbsGalois algCloTrivialTower) 5
          (wgeCharAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
            (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))))
          g Q)
      = zmodMul 5
          (cycRigChar (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
            (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))) g)
          (weilPairingPt 5 P Q) :=
  wge_equivariant_char (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))) g P Q

end IUT
