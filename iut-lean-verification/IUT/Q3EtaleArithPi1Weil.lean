-- Q3EtaleArithPi1Weil [実／(b) 本物の先行建設・柱A A4「実 π₁^ét」AP-4]
-- complete_pct 影響: A4 マイルストーン AP-4（Weil ペアリングスライス）＋外 Galois 非自明性
--   witness（σ₂ × tζ）。q3ap（実算術 π₁^ét 完全列）の残欠 2 件——(1) E[9]≅(ℤ/9)²（格子×μ）
--   座標上の ℤ/9 値 Weil ペアリングとその Galois 同変性 ⟨σx,σy⟩=χ₉(σ)·⟨x,y⟩、(2) 明示的
--   非自明性 witness s(σ₂)·ι(tζ)·s(σ₂)⁻¹ ≠ ι(tζ)——を完全証明で discharge する。
--   予測 s_A4 0.58→0.59（監査確定・過大主張しない）。w=14 でも単独では表示 57 を動かさない
--   （表示 mover を主張しない）。
--
-- 正直な限定（§4 規約により消さない・弱めない・sorry で埋めない・q3ap §正直限定を全て継承）:
--  (i)   これは依然**分裂・次数付きスライス**である。本モジュールの非自明性は**外作用の
--        非自明性**（切断の共役が実 Galois 捻りとして幾何 π₁ を実際に動かす）であって、
--        **非分裂群拡大 0→ℤ₃(1)→T₃E→ℤ₃→0 の非分裂性ではない**——それには Kummer
--        コサイクル σ(3^{1/3})/3^{1/3}・実 ℚ₃(ζ₂₇,3^{1/3}) の建設が前提（named future
--        target）。「非分裂拡大を構成した」とは書かない。
--  (ii)  Weil ペアリングは **π₁ 指標座標（q9tdLatChar × q9tdMuChar）上の determinant 形式
--        （M339F weilPairing の実消費）**であり、∧²T₃E ≅ ℤ₃(1) の mod-9 の影である。
--        ℓ 進 Tate 加群のカップ積による幾何的 Weil ペアリングとの一致は未形式化
--        （M339F/M344F 正直限定 (i)(ii) 継承）。双線形性・交代性は座標定義の帰結（credit 低）
--        と正直申告する。★非自明な内容は **Galois 同変性**（q3ap_mu_equivariant の実消費）
--        と**実 profinite Gal での初の非自明 χ インスタンス**（M344F の実例は χ≡1 trivial
--        だった——本モジュールは χ₉(σ₂)=2 の本物の非自明円分指標で WeilGKAction を初めて
--        実インスタンス化する）。
--  (iii) 上三角作用の Kummer 捻り成分は β≡0（分裂 mod-9 スライスに忠実）。非自明 β は
--        (i) の Kummer コサイクルと同じ named future。
--  (iv)  G = Gal(ℚ(ζ_{3^∞})/ℚ)（ℚ 上円分切片）であって実局所 G_{ℚ₃} でも実 G_K でもない
--        （q3ap (iii)・tmz (iii) 継承）。Galois は曲線の点には作用しない（同変性は π₁ 指標
--        レベル・q3ap (iv) 継承）。スキーム・エタールサイト・位相・anabelian 逆再構成ゼロ。
--        pro-3・単一曲線 E_{3⁹}・q=3⁹ 忠実部分ケース（q9td/q3pe 恒久限定継承）。
--
-- 全て選択公理不使用（新規 Classical.choice を導入しない・propext/Quot.sound のみ）。
-- 禁止タクティク不使用（omega は純 Int/Nat アトムのみ）。新規ファイル 1 個のみ
-- （共有ファイル不更新・親統合）。prefix `q3aw`。

/-
  IUT/Q3EtaleArithPi1Weil.lean — A4 AP-4: 実算術 π₁^ét の Weil ペアリングスライスと
    外 Galois 非自明性 witness（σ₂ × tζ）

  分類: [実／(b) 本物の先行建設]。設計 = audit/pillar-A4-pi1etale-deepen-detail-2026-07-20.md
    §2.4（witness の閉形式）＋ §3 AP-4（Weil スライス・任意檗）。

  内容:
   * §A  χ₉ の ℤ/9 値化 q3awChi と指標則（chi_one/chi_mul・cliChar 消費）・
         μ 指標の χ 捻れのスカラー形 q3aw_mu_char_twist（q3ap_mu_equivariant 消費）。
   * §B  ★実 WeilGKAction インスタンス q3awGKAction——GK = 実 profinite
         Gal(ℚ(ζ_{3^∞})/ℚ) = ctlProfinite・χ = 実円分指標 χ₉（cliChar 経由）・β ≡ 0。
         M344F の「非自明 χ を与える実 Galois 降下は後続」の正面 discharge（初の非自明実例）。
   * §C  座標写像 q3awCoord : π₁^geom → E[9]≅(ℤ/9)²（q9tdMuChar × q9tdLatChar）・
         加法性・★同変性 q3aw_coord_equivariant（q3apTw の E[9] 座標作用 = 実 GK 作用）。
   * §D  ★★Weil ペアリングスライス: q3awPair（M339F weilPairing の π₁ 指標座標引き戻し）・
         双線形・交代・反対称・（座標）非退化・E[9] 実曲線点上の well-definedness
         （q9td_phi_injective 消費）・★★Galois 同変性 q3aw_weil_galois
         ⟨σx,σy⟩ = χ₉(σ)·⟨x,y⟩・共役形 q3aw_conj_pair（q3ap_outer_galois 消費）・
         μ₉ 値実曲線着地 q3aw_pair_curve_galois（[ζ₉]^⟨x,y⟩ ∈ E_{3⁹}）。
   * §E  ★★明示的非自明性 witness: σ₂ = cliFrom(定数 2 整合族)（χ₉(σ₂)=2）・
         tζ = ζ 生成元整合族（χ_μ(tζ)=1）・(tmzActHom σ₂)(tζ) ≠ tζ・
         s(σ₂)·ι(tζ,1)·s(σ₂)⁻¹ ≠ ι(tζ,1)（外 Galois 作用の非自明性）・
         Weil ペアリング値も Galois で実際に動く（⟨σ₂y,σ₂x⟩ = 2·⟨y,x⟩ ≠ ⟨y,x⟩）。
   * §F  capstone Q3ArithWeilData / q3aw_data / q3aw_exists。

  firewall: Q3TemperedPi1・ArithTemperedPi1・Q3Mu9ThetaGroup は import しない（q3ap 同様）。
  M339F/M344F は「Weil ペアリング機構」として消費し、その正直限定は書き換えない。
-/
import IUT.Q3EtaleArithPi1
import IUT.CyclotomicRigidityAut
import IUT.WeilGaloisEquiv

namespace IUT

/-! ## §A: χ₉ の ℤ/9 値化と μ 指標の χ 捻れ（スカラー形） -/

/-- **§A-1: 実円分指標の ℤ/9 値化** χ₉ : Gal(ℚ(ζ_{3^∞})/ℚ) → ℤ/9（q3ap の Nat 値
    `q3apChi9`（= cliChar レベル 1 段の値）を ℤ/9 剰余類に載せる）。 -/
def q3awChi (σ : ctlProfinite.carrier) : (zmod 9).carrier :=
  Quot.mk (modCong 9).rel ((q3apChi9 σ : Nat) : Int)

/-- **§A-2: χ₉(1) = 1（Nat 値）**（cliChar の map_one）。 -/
theorem q3aw_chi9_one : q3apChi9 ctlProfinite.one = 1 :=
  congrArg Subtype.val (Hom.map_one (cliChar 1))

/-- **§A-3: χ₉ の乗法性（Nat 値・mod 9）**（cliChar の map_mul・(ℤ/9)^× の積は
    val の積 mod 9）。 -/
theorem q3aw_chi9_mul (g h : ctlProfinite.carrier) :
    q3apChi9 (ctlProfinite.mul g h) = q3apChi9 g * q3apChi9 h % 9 :=
  congrArg Subtype.val ((cliChar 1).map_mul (g.val 1) (h.val 1))

/-- **§A-4（★ 核）: μ 指標の χ 捻れのスカラー形** —
    χ_μ((tmzActHom σ)(s)) = χ₉(σ) ·_{ℤ/9} χ_μ(s)（ℤ/9 の環積 `zmodMul`）。
    q3ap_mu_equivariant（A4 AP-3c）の ℤ/9 環スカラー読み替え——Weil スライスの入力。 -/
theorem q3aw_mu_char_twist (σ : ctlProfinite.carrier) (s : tmzLimit.carrier) :
    q9tdMuChar.map ((tmzActHom σ).map s) = zmodMul 9 (q3awChi σ) (q9tdMuChar.map s) := by
  rw [q3ap_mu_equivariant σ s]
  show Quot.mk (modCong 9).rel
        ((q3apChi9 σ * ctmFind 2 q9td_h2 (s.val 1).val : Nat) : Int)
     = Quot.mk (modCong 9).rel
        (((q3apChi9 σ : Nat) : Int) * ((ctmFind 2 q9td_h2 (s.val 1).val : Nat) : Int))
  rw [Int.natCast_mul (q3apChi9 σ) (ctmFind 2 q9td_h2 (s.val 1).val)]

/-! ## §B: ★実 WeilGKAction インスタンス（実 profinite Gal・実 χ₉・β≡0） -/

/-- **§B-1（★）: 実 profinite Gal の E[9] 上三角作用データ** — GK = 実
    Gal(ℚ(ζ_{3^∞})/ℚ) = ctlProfinite（A3 実 profinite）・χ = 実円分指標 χ₉
    （cliChar 経由・非自明: §E で χ₉(σ₂)=2）・β ≡ 0（分裂 mod-9 スライスに忠実・
    非自明 Kummer 捻りは named future・正直限定 (iii)）。M344F `WeilGKAction` の
    **初の非自明 χ 実インスタンス**（既存実例は χ≡1 trivial / 抽象 GK のみ）。 -/
def q3awGKAction : WeilGKAction ctlProfinite 9 where
  chi := q3awChi
  beta := fun _ => Quot.mk (modCong 9).rel 0
  chi_one := by
    show Quot.mk (modCong 9).rel ((q3apChi9 ctlProfinite.one : Nat) : Int)
       = Quot.mk (modCong 9).rel 1
    rw [q3aw_chi9_one]
    exact Quot.sound ⟨0, by omega⟩
  chi_mul := fun g h => by
    show Quot.mk (modCong 9).rel ((q3apChi9 (ctlProfinite.mul g h) : Nat) : Int)
       = zmodMul 9 (q3awChi g) (q3awChi h)
    rw [q3aw_chi9_mul g h]
    show Quot.mk (modCong 9).rel ((q3apChi9 g * q3apChi9 h % 9 : Nat) : Int)
       = Quot.mk (modCong 9).rel (((q3apChi9 g : Nat) : Int) * ((q3apChi9 h : Nat) : Int))
    rw [← Int.natCast_mul (q3apChi9 g) (q3apChi9 h)]
    exact Quot.sound (q3ap_ar_mod9 (q3apChi9 g * q3apChi9 h))
  beta_one := rfl
  beta_mul := fun g _ => by
    show Quot.mk (modCong 9).rel 0
       = (zmod 9).mul (zmodMul 9 (q3awChi g) (Quot.mk (modCong 9).rel 0))
           (Quot.mk (modCong 9).rel 0)
    rw [wge_zmul_zero 9 (q3awChi g)]
    show Quot.mk (modCong 9).rel 0 = Quot.mk (modCong 9).rel (0 + 0)
    have h : (0 : Int) + 0 = 0 := by omega
    rw [h]

/-- **§B-2: 実 GK 作用の単位則**（M344F wge_tor_act_one の実インスタンス）。 -/
theorem q3aw_act_one (P : WeilTorsion 9) :
    wgeTorAct ctlProfinite 9 q3awGKAction ctlProfinite.one P = P :=
  wge_tor_act_one ctlProfinite 9 q3awGKAction P

/-- **§B-3: 実 GK 作用の合成則**（M344F wge_tor_act_mul の実インスタンス——実 profinite
    Gal が E[9] 座標に本物の群作用で作用する）。 -/
theorem q3aw_act_mul (g h : ctlProfinite.carrier) (P : WeilTorsion 9) :
    wgeTorAct ctlProfinite 9 q3awGKAction (ctlProfinite.mul g h) P
      = wgeTorAct ctlProfinite 9 q3awGKAction g (wgeTorAct ctlProfinite 9 q3awGKAction h P) :=
  wge_tor_act_mul ctlProfinite 9 q3awGKAction g h P

/-! ## §C: 座標写像 π₁^geom → E[9]≅(ℤ/9)² とその Galois 同変性 -/

/-- **§C-1: 座標写像** — 幾何 π₁ スライス z = (s, γ) ∈ ℤ₃(1)×ℤ₃ を E[9] 座標
    （zExp = μ 方向指標 χ_μ(s)・qExp = 格子方向指標 χ_lat(γ)）へ落とす
    （q9td の E[9]≅(ℤ/9)² 二方向分解の指標座標）。 -/
def q3awCoord (z : q3apGeom.carrier) : WeilTorsion 9 :=
  ⟨q9tdMuChar.map z.1, q9tdLatChar.map z.2⟩

/-- **§C-2: 座標写像の加法性**（両指標の map_mul）。 -/
theorem q3aw_coord_add (z w : q3apGeom.carrier) :
    q3awCoord (q3apGeom.mul z w) = weilTorAdd 9 (q3awCoord z) (q3awCoord w) := by
  show WeilTorsion.mk (q9tdMuChar.map (tmzLimit.mul z.1 w.1))
        (q9tdLatChar.map ((q3pePi1 3).mul z.2 w.2))
     = WeilTorsion.mk ((zmod 9).mul (q9tdMuChar.map z.1) (q9tdMuChar.map w.1))
        ((zmod 9).mul (q9tdLatChar.map z.2) (q9tdLatChar.map w.2))
  rw [q9tdMuChar.map_mul z.1 w.1, q9tdLatChar.map_mul z.2 w.2]

/-- 0 の左環積は 0（zmodMul_comm ＋ wge_zmul_zero）。 -/
theorem q3aw_zmul_zero_left (x : (zmod 9).carrier) :
    zmodMul 9 (Quot.mk (modCong 9).rel 0) x = Quot.mk (modCong 9).rel 0 := by
  rw [zmodMul_comm 9 (Quot.mk (modCong 9).rel 0) x]
  exact wge_zmul_zero 9 x

/-- 0 の右加法は恒等。 -/
theorem q3aw_mul_zero_right (x : (zmod 9).carrier) :
    (zmod 9).mul x (Quot.mk (modCong 9).rel 0) = x := by
  induction x using Quot.ind; rename_i a
  show Quot.mk (modCong 9).rel (a + 0) = Quot.mk (modCong 9).rel a
  rw [Int.add_zero]

/-- **§C-3（★）: 座標の Galois 同変性** — q3ap の Galois 捻り q3apTw σ（算術 π₁ の
    外 Galois 作用・q3ap_outer_galois の右辺）は、E[9] 座標上で実 GK 作用
    `wgeTorAct q3awGKAction σ`（μ 座標に χ₉ 倍・格子座標固定）に写る:
    coord((tw σ)(z)) = σ · coord(z)。算術 π₁ の外作用と E[9] の Galois 表現の接続。 -/
theorem q3aw_coord_equivariant (σ : ctlProfinite.carrier) (z : q3apGeom.carrier) :
    q3awCoord ((q3apTw σ).map z)
      = wgeTorAct ctlProfinite 9 q3awGKAction σ (q3awCoord z) := by
  show WeilTorsion.mk (q9tdMuChar.map ((tmzActHom σ).map z.1)) (q9tdLatChar.map z.2)
     = WeilTorsion.mk
        ((zmod 9).mul (zmodMul 9 (q3awChi σ) (q9tdMuChar.map z.1))
          (zmodMul 9 (Quot.mk (modCong 9).rel 0) (q9tdLatChar.map z.2)))
        (q9tdLatChar.map z.2)
  rw [q3aw_zmul_zero_left (q9tdLatChar.map z.2),
      q3aw_mul_zero_right (zmodMul 9 (q3awChi σ) (q9tdMuChar.map z.1)),
      q3aw_mu_char_twist σ z.1]

/-! ## §D: ★★Weil ペアリングスライスと Galois 同変性 -/

/-- **§D-1（★）: π₁ 指標座標上の Weil ペアリング** —
    ⟨(s,γ), (s',γ')⟩ := χ_μ(s)·χ_lat(γ') − χ_μ(s')·χ_lat(γ) ∈ ℤ/9
    （M339F determinant 形式 `weilPairingPt` の実 π₁ 指標座標への引き戻し・
    ∧²T₃E ≅ ℤ₃(1) の mod-9 の影・正直限定 (ii)）。 -/
def q3awPair (z w : q3apGeom.carrier) : (zmod 9).carrier :=
  weilPairingPt 9 (q3awCoord z) (q3awCoord w)

/-- **§D-2: 第一引数双線形性**（座標加法性 ＋ M339F 双線形性——定義の帰結・credit 低と
    正直申告）。 -/
theorem q3aw_pair_bilinear_left (z z' w : q3apGeom.carrier) :
    q3awPair (q3apGeom.mul z z') w = (zmod 9).mul (q3awPair z w) (q3awPair z' w) := by
  show weilPairingPt 9 (q3awCoord (q3apGeom.mul z z')) (q3awCoord w)
     = (zmod 9).mul (q3awPair z w) (q3awPair z' w)
  rw [q3aw_coord_add z z']
  exact weil_pt_bilinear_left 9 (q3awCoord z) (q3awCoord z') (q3awCoord w)

/-- **§D-3: 第二引数双線形性**。 -/
theorem q3aw_pair_bilinear_right (z w w' : q3apGeom.carrier) :
    q3awPair z (q3apGeom.mul w w') = (zmod 9).mul (q3awPair z w) (q3awPair z w') := by
  show weilPairingPt 9 (q3awCoord z) (q3awCoord (q3apGeom.mul w w'))
     = (zmod 9).mul (q3awPair z w) (q3awPair z w')
  rw [q3aw_coord_add w w']
  exact weil_bilinear_right 9 (q3awCoord z).zExp (q3awCoord z).qExp
    (q3awCoord w).zExp (q3awCoord w').zExp (q3awCoord w).qExp (q3awCoord w').qExp

/-- **§D-4: 交代性** ⟨z,z⟩ = 0。 -/
theorem q3aw_pair_alternating (z : q3apGeom.carrier) :
    q3awPair z z = (zmod 9).one :=
  weil_pt_alternating 9 (q3awCoord z)

/-- **§D-5: 反対称性** ⟨z,w⟩ = −⟨w,z⟩。 -/
theorem q3aw_pair_antisymmetric (z w : q3apGeom.carrier) :
    q3awPair z w = (zmod 9).inv (q3awPair w z) :=
  weil_pt_antisymmetric 9 (q3awCoord z) (q3awCoord w)

/-- **§D-6: 座標非退化性**（M339F の仮説不要非退化性の座標スライス——coord z の全対と
    直交すれば coord z = 0）。 -/
theorem q3aw_coord_nondegenerate (z : q3apGeom.carrier)
    (h : ∀ Q : WeilTorsion 9, weilPairingPt 9 (q3awCoord z) Q = (zmod 9).one) :
    q3awCoord z = weilTorZero 9 :=
  weil_pt_nondegenerate 9 (q3awCoord z) h

/-- **§D-7: E[9] 二方向座標上のペアリング**（q9td の E[9] 座標 (格子, μ) で読んだ形）。 -/
def q3awPairE9 (p q : q9tdE9) : (zmod 9).carrier :=
  weilPairing 9 p.2 p.1 q.2 q.1

/-- **§D-8: π₁ ペアリングと E[9] 座標ペアリングの橋**（定義一致）。 -/
theorem q3aw_pair_via_e9 (z w : q3apGeom.carrier) :
    q3awPair z w
      = q3awPairE9 (q9tdLatChar.map z.2, q9tdMuChar.map z.1)
          (q9tdLatChar.map w.2, q9tdMuChar.map w.1) := rfl

/-- **§D-9（★ 実曲線点上の well-definedness）: 実曲線 E_{3⁹} の 9-torsion 点で座標が
    一致すればペアリング値も一致**（q9td_phi_injective 消費——ペアリングが座標の取り方に
    依らず実曲線 E_{3⁹}[9] の点の関数として well-defined）。 -/
theorem q3aw_pairE9_welldef (p p' q q' : q9tdE9)
    (hp : q9tdPhi p = q9tdPhi p') (hq : q9tdPhi q = q9tdPhi q') :
    q3awPairE9 p q = q3awPairE9 p' q' := by
  rw [q9td_phi_injective p p' hp, q9td_phi_injective q q' hq]

/-- **§D-10（★★ 本丸・AP-4 headline）: Weil ペアリングの Galois 同変性** —
    ⟨(tw σ)(z), (tw σ)(w)⟩ = χ₉(σ) · ⟨z,w⟩。実算術 π₁^ét の外 Galois 捻り（q3apTw =
    q3ap_outer_galois の共役実現）の下で、Weil ペアリングは実円分指標 χ₉ 倍にスケールする
    （[IUTchI] §2 入力形「二方向 ＋ 外 Galois ＋ pairing」の pairing 節・q3pe 正直限定 (3)
    「Weil ペアリング」残欠の mod-9 discharge）。 -/
theorem q3aw_weil_galois (σ : ctlProfinite.carrier) (z w : q3apGeom.carrier) :
    q3awPair ((q3apTw σ).map z) ((q3apTw σ).map w)
      = zmodMul 9 (q3awChi σ) (q3awPair z w) := by
  show weilPairingPt 9 (q3awCoord ((q3apTw σ).map z)) (q3awCoord ((q3apTw σ).map w))
     = zmodMul 9 (q3awChi σ) (weilPairingPt 9 (q3awCoord z) (q3awCoord w))
  rw [q3aw_coord_equivariant σ z, q3aw_coord_equivariant σ w]
  exact wge_equivariant ctlProfinite 9 q3awGKAction σ (q3awCoord z) (q3awCoord w)

/-- **§D-11（★ 共役形）: 算術共役とペアリング** — s(σ)·ι(z)·s(σ)⁻¹ = ι(z')・
    s(σ)·ι(w)·s(σ)⁻¹ = ι(w') なら ⟨z',w'⟩ = χ₉(σ)·⟨z,w⟩
    （q3ap_outer_galois ＋ ι 単射で z'=(tw σ)z を同定し §D-10 に帰着——算術基本群の
    共役作用が Weil ペアリングを χ₉ 倍にスケールさせる実形）。 -/
theorem q3aw_conj_pair (σ : ctlProfinite.carrier) (z w z' w' : q3apGeom.carrier)
    (hz : q3apArith.mul (q3apArith.mul (q3apSection.map σ) (q3apIncl.map z))
        (q3apArith.inv (q3apSection.map σ)) = q3apIncl.map z')
    (hw : q3apArith.mul (q3apArith.mul (q3apSection.map σ) (q3apIncl.map w))
        (q3apArith.inv (q3apSection.map σ)) = q3apIncl.map w') :
    q3awPair z' w' = zmodMul 9 (q3awChi σ) (q3awPair z w) := by
  have hz2 : z' = (q3apTw σ).map z :=
    q3ap_incl_injective z' ((q3apTw σ).map z)
      (hz.symm.trans (q3ap_outer_galois σ z))
  have hw2 : w' = (q3apTw σ).map w :=
    q3ap_incl_injective w' ((q3apTw σ).map w)
      (hw.symm.trans (q3ap_outer_galois σ w))
  rw [hz2, hw2]
  exact q3aw_weil_galois σ z w

/-- **§D-12（★ μ₉ 値実曲線着地）: ペアリング値の実曲線 E_{3⁹} 上の [ζ₉] 冪としての
    同変性** — [ζ₉]^{⟨σz,σw⟩} = [ζ₉]^{χ₉(σ)·⟨z,w⟩} ∈ E_{3⁹}（q9tdCpow で ℤ/9 値を
    実曲線の μ₉ 点に持ち上げた形——ペアリングの μ₉ 値スライス）。 -/
theorem q3aw_pair_curve_galois (σ : ctlProfinite.carrier) (z w : q3apGeom.carrier) :
    q9tdCpow q9tlZeta9 q9tl_zeta9_pow9
        (q3awPair ((q3apTw σ).map z) ((q3apTw σ).map w))
      = q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 (zmodMul 9 (q3awChi σ) (q3awPair z w)) :=
  congrArg (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9) (q3aw_weil_galois σ z w)

/-! ## §E: ★★明示的非自明性 witness（σ₂ × tζ・設計 §2.4 の閉形式） -/

/-- **§E-1: σ₂ の単数側 witness** — 定数 2 の整合族 ∈ ℤ₃^× = zpsLimit
    （各段 2 < 3^{m+1}・3∤2・zps の既存整合族）。 -/
def q3awU2 : zpsLimit.carrier := ⟨zpsConstFam, zpsConstFam_compat⟩

/-- **§E-2（★）: Galois 元 σ₂** — cliFrom（極限代入自己同型 ℤ₃^× ≅ Gal）で定数 2 族を
    実 profinite Gal(ℚ(ζ_{3^∞})/ℚ) の実元に持ち上げたもの。 -/
def q3awSigma2 : ctlProfinite.carrier := cliFrom.map q3awU2

/-- **§E-3（★）: χ₉(σ₂) = 2** — レベル 1 段の成分右逆 cli_char_aut で閉形式計算
    （σ₂ は非自明円分指標値を持つ実 Galois 元）。 -/
theorem q3aw_chi9_sigma2 : q3apChi9 q3awSigma2 = 2 :=
  congrArg Subtype.val (cli_char_aut 1 (zpsConstFam 1))

/-- **§E-4: tζ の各段成分** — レベル n に ζ_{3^{n+1}} の実生成元 cmrZeta を置く族。 -/
def q3awTZetaFam (n : Nat) : (tmzG n).carrier := cmrZeta (n + 1) (by omega)

/-- **§E-5: tζ 族の整合性** — 遷移 tmzT は指数読み替えゆえ find(ζ)=1（cra_find_zeta）で
    ζ ↦ ζ^1 = ζ（choice-free 閉形式）。 -/
theorem q3awTZetaFam_compat : Compatible tmzSystem q3awTZetaFam := by
  intro a b h
  show (cmrGrp (a + 1) (by omega)).pow (cmrZeta (a + 1) (by omega))
        (ctmFind (b + 1) (by omega) (cmrZeta (b + 1) (by omega)).val)
      = cmrZeta (a + 1) (by omega)
  rw [cra_find_zeta (b + 1) (by omega)]
  apply Subtype.ext
  rw [cmr_pow_zeta (a + 1) (by omega) 1]
  exact ctm_pow_one (a + 1) (by omega)

/-- **§E-6（★）: μ 方向 π₁ の生成元 tζ ∈ T = ℤ₃(1)** — ζ 生成元整合族
    （tmzLimit の実元・witness の T 側）。 -/
def q3awTZeta : tmzLimit.carrier := ⟨q3awTZetaFam, q3awTZetaFam_compat⟩

/-- **§E-7: χ_μ(tζ) = 1** — μ 指標は tζ を ℤ/9 の生成元 1 に送る（find(ζ)=1）。 -/
theorem q3aw_mu_char_tzeta : q9tdMuChar.map q3awTZeta = Quot.mk (modCong 9).rel 1 := by
  have h1 : ctmFind 2 q9td_h2 (q3awTZeta.val 1).val = 1 := cra_find_zeta 2 q9td_h2
  show Quot.mk (modCong 9).rel ((ctmFind 2 q9td_h2 (q3awTZeta.val 1).val : Nat) : Int)
     = Quot.mk (modCong 9).rel 1
  rw [h1]
  exact Quot.sound ⟨0, by omega⟩

/-- **§E-8（★★ witness の核）: 実 Galois 作用は tζ を実際に動かす** —
    (tmzActHom σ₂)(tζ) ≠ tζ。μ 指標で分離: 左辺の指標は χ₉(σ₂)·find(tζ) = 2·1 = 2、
    右辺は 1、mod 9 で相異（Quot 分離 quot_exact）。A7b 実作用 tmzActHom が
    ℤ₃(1) 上で非自明であることの初の明示 witness。 -/
theorem q3aw_galois_moves_tzeta : (tmzActHom q3awSigma2).map q3awTZeta ≠ q3awTZeta := by
  intro h
  have hc : q9tdMuChar.map ((tmzActHom q3awSigma2).map q3awTZeta)
      = q9tdMuChar.map q3awTZeta := congrArg q9tdMuChar.map h
  have h1 : ctmFind 2 q9td_h2 (q3awTZeta.val 1).val = 1 := cra_find_zeta 2 q9td_h2
  rw [q3ap_mu_equivariant q3awSigma2 q3awTZeta, q3aw_mu_char_tzeta,
      q3aw_chi9_sigma2, h1] at hc
  have hrel := quot_exact intGrp (modCong 9) hc
  obtain ⟨k, hk⟩ := hrel
  omega

/-- **§E-9: 幾何 π₁ の witness 元** z₀ = (tζ, 1)（μ 方向生成元・格子方向単位元）。 -/
def q3awZgen : q3apGeom.carrier := (q3awTZeta, (q3pePi1 3).one)

/-- **§E-10（★）: Galois 捻りは幾何 π₁ を動かす** — (q3apTw σ₂)(z₀) ≠ z₀
    （第 1 成分で §E-8 に帰着）。 -/
theorem q3aw_tw_moves : (q3apTw q3awSigma2).map q3awZgen ≠ q3awZgen :=
  fun h => q3aw_galois_moves_tzeta (congrArg Prod.fst h)

/-- **§E-11（★★ AP-2 非自明性 witness・audit §2.4）: 外 Galois 作用の非自明性** —
    s(σ₂)·ι(tζ,1)·s(σ₂)⁻¹ ≠ ι(tζ,1)。算術切断 s の共役は幾何 π₁ を実際に動かす＝
    Π^arith は（この分裂に関して）**直積ではない**半直積であり、外 Galois 表現
    G → Aut(π₁^geom) は非自明（q3ap_outer_galois ＋ ι 単射 ＋ §E-10）。
    注意（正直限定 (i)）: これは外作用の非自明性であって、非分裂群拡大の主張ではない。 -/
theorem q3aw_outer_nontrivial :
    q3apArith.mul (q3apArith.mul (q3apSection.map q3awSigma2) (q3apIncl.map q3awZgen))
        (q3apArith.inv (q3apSection.map q3awSigma2))
      ≠ q3apIncl.map q3awZgen := by
  intro h
  have h2 : q3apIncl.map ((q3apTw q3awSigma2).map q3awZgen) = q3apIncl.map q3awZgen :=
    (q3ap_outer_galois q3awSigma2 q3awZgen).symm.trans h
  exact q3aw_tw_moves (q3ap_incl_injective ((q3apTw q3awSigma2).map q3awZgen) q3awZgen h2)

/-- **§E-12: 系 — 切断は中心化しない**（共役が恒等になる分裂＝直積的分裂は存在しない
    ことの witness 形——∀σ∀z で共役 = ι(z) は成り立たない）。 -/
theorem q3aw_conj_not_trivial :
    ¬ (∀ (σ : ctlProfinite.carrier) (z : q3apGeom.carrier),
        q3apArith.mul (q3apArith.mul (q3apSection.map σ) (q3apIncl.map z))
            (q3apArith.inv (q3apSection.map σ))
          = q3apIncl.map z) :=
  fun h => q3aw_outer_nontrivial (h q3awSigma2 q3awZgen)

/-- **§E-13: 系 — 外 Galois 捻り準同型は非自明**（∃σ∃z, (tw σ)(z) ≠ z）。 -/
theorem q3aw_tw_nontrivial :
    ∃ (σ : ctlProfinite.carrier) (z : q3apGeom.carrier), (q3apTw σ).map z ≠ z :=
  ⟨q3awSigma2, q3awZgen, q3aw_tw_moves⟩

/-! ### ペアリングも Galois で実際に動く（witness の Weil 版） -/

/-- **§E-14: 格子方向の witness 元** γ₁ = ℤ→ℤ₃ の 1 の像（χ_lat(γ₁)=1・q9td 消費）。 -/
def q3awGamma1 : (q3pePi1 3).carrier := (toZp 3).map 1

/-- **§E-15: 幾何 π₁ の格子側 witness 元** x₀ = (1, γ₁)。 -/
def q3awXlat : q3apGeom.carrier := (tmzLimit.one, q3awGamma1)

/-- z₀ = (tζ,1) の座標は (zExp, qExp) = (1, 0)。 -/
theorem q3aw_coord_zgen :
    q3awCoord q3awZgen = ⟨Quot.mk (modCong 9).rel 1, (zmod 9).one⟩ := by
  show WeilTorsion.mk (q9tdMuChar.map q3awTZeta) (q9tdLatChar.map (q3pePi1 3).one)
     = WeilTorsion.mk (Quot.mk (modCong 9).rel 1) (zmod 9).one
  rw [q3aw_mu_char_tzeta, q9tdLatChar.map_one]

/-- x₀ = (1,γ₁) の座標は (zExp, qExp) = (0, 1)。 -/
theorem q3aw_coord_xlat :
    q3awCoord q3awXlat = ⟨(zmod 9).one, Quot.mk (modCong 9).rel 1⟩ := by
  show WeilTorsion.mk (q9tdMuChar.map tmzLimit.one) (q9tdLatChar.map q3awGamma1)
     = WeilTorsion.mk (zmod 9).one (Quot.mk (modCong 9).rel 1)
  rw [q9tdMuChar.map_one]
  rfl

/-- **§E-16: 基底対のペアリング値** ⟨z₀, x₀⟩ = 1（μ 生成元 × 格子生成元は 1 に
    ペアリングされる——非退化スライスの明示値）。 -/
theorem q3aw_pair_gen : q3awPair q3awZgen q3awXlat = Quot.mk (modCong 9).rel 1 := by
  show weilPairingPt 9 (q3awCoord q3awZgen) (q3awCoord q3awXlat)
     = Quot.mk (modCong 9).rel 1
  rw [q3aw_coord_zgen, q3aw_coord_xlat]
  show Quot.mk (modCong 9).rel ((1 : Int) * 1 + -((0 : Int) * 0))
     = Quot.mk (modCong 9).rel 1
  exact Quot.sound ⟨0, by omega⟩

/-- **§E-17: ペアリングの非自明性** ⟨z₀, x₀⟩ ≠ 0。 -/
theorem q3aw_pair_gen_ne_one : q3awPair q3awZgen q3awXlat ≠ (zmod 9).one := by
  intro h
  rw [q3aw_pair_gen] at h
  have h0 : Quot.mk (modCong 9).rel (1 : Int) = Quot.mk (modCong 9).rel (0 : Int) := h
  have hrel := quot_exact intGrp (modCong 9) h0
  obtain ⟨k, hk⟩ := hrel
  omega

/-- **§E-18（★ witness の Weil 版）: ペアリング値は Galois で実際に動く** —
    ⟨(tw σ₂)(z₀), (tw σ₂)(x₀)⟩ = χ₉(σ₂)·⟨z₀,x₀⟩ = 2·1 = 2 ≠ 1 = ⟨z₀,x₀⟩。
    §D-10 の同変性が空虚でない（χ₉ の非自明値で本当にスケールする）ことの明示 witness。 -/
theorem q3aw_pair_galois_moves :
    q3awPair ((q3apTw q3awSigma2).map q3awZgen) ((q3apTw q3awSigma2).map q3awXlat)
      ≠ q3awPair q3awZgen q3awXlat := by
  intro h
  rw [q3aw_weil_galois q3awSigma2 q3awZgen q3awXlat, q3aw_pair_gen] at h
  have hchi : q3awChi q3awSigma2 = Quot.mk (modCong 9).rel 2 := by
    show Quot.mk (modCong 9).rel ((q3apChi9 q3awSigma2 : Nat) : Int)
       = Quot.mk (modCong 9).rel 2
    rw [q3aw_chi9_sigma2]
    exact Quot.sound ⟨0, by omega⟩
  rw [hchi] at h
  have hrel := quot_exact intGrp (modCong 9) h
  obtain ⟨k, hk⟩ := hrel
  omega

/-! ## §F: capstone -/

/-- **§F-1: A4 AP-4 Weil スライス＋非自明性 witness データ** — 実 profinite Gal の
    E[9] 実作用（初の非自明 χ 実インスタンス）・座標同変性・Weil ペアリング
    （双線形・交代・反対称・実曲線点 well-defined）・★Galois 同変性・共役形・
    ★明示的非自明性 witness（σ₂ × tζ）を束ねる。 -/
structure Q3ArithWeilData where
  /-- 実 GK 作用の単位則。 -/
  act_one : ∀ P : WeilTorsion 9,
    wgeTorAct ctlProfinite 9 q3awGKAction ctlProfinite.one P = P
  /-- 実 GK 作用の合成則（本物の群作用）。 -/
  act_mul : ∀ (g h : ctlProfinite.carrier) (P : WeilTorsion 9),
    wgeTorAct ctlProfinite 9 q3awGKAction (ctlProfinite.mul g h) P
      = wgeTorAct ctlProfinite 9 q3awGKAction g (wgeTorAct ctlProfinite 9 q3awGKAction h P)
  /-- 座標の Galois 同変性（q3apTw ↦ 実 GK 作用）。 -/
  coord_equivariant : ∀ (σ : ctlProfinite.carrier) (z : q3apGeom.carrier),
    q3awCoord ((q3apTw σ).map z)
      = wgeTorAct ctlProfinite 9 q3awGKAction σ (q3awCoord z)
  /-- 双線形性（第一引数）。 -/
  pair_bilinear : ∀ z z' w, q3awPair (q3apGeom.mul z z') w
      = (zmod 9).mul (q3awPair z w) (q3awPair z' w)
  /-- 交代性。 -/
  pair_alternating : ∀ z, q3awPair z z = (zmod 9).one
  /-- 実曲線 E_{3⁹}[9] の点上の well-definedness（q9td_phi_injective）。 -/
  pair_welldef : ∀ p p' q q', q9tdPhi p = q9tdPhi p' → q9tdPhi q = q9tdPhi q' →
    q3awPairE9 p q = q3awPairE9 p' q'
  /-- ★Weil ペアリングの Galois 同変性 ⟨σz,σw⟩ = χ₉(σ)·⟨z,w⟩。 -/
  weil_galois : ∀ (σ : ctlProfinite.carrier) (z w : q3apGeom.carrier),
    q3awPair ((q3apTw σ).map z) ((q3apTw σ).map w)
      = zmodMul 9 (q3awChi σ) (q3awPair z w)
  /-- ★算術共役形（q3ap_outer_galois 消費）。 -/
  conj_pair : ∀ (σ : ctlProfinite.carrier) (z w z' w' : q3apGeom.carrier),
    q3apArith.mul (q3apArith.mul (q3apSection.map σ) (q3apIncl.map z))
        (q3apArith.inv (q3apSection.map σ)) = q3apIncl.map z' →
    q3apArith.mul (q3apArith.mul (q3apSection.map σ) (q3apIncl.map w))
        (q3apArith.inv (q3apSection.map σ)) = q3apIncl.map w' →
    q3awPair z' w' = zmodMul 9 (q3awChi σ) (q3awPair z w)
  /-- ★χ₉(σ₂) = 2（witness の Galois 側閉形式）。 -/
  chi_sigma2 : q3apChi9 q3awSigma2 = 2
  /-- ★★実 Galois 作用は tζ を動かす（A7b 作用の非自明性 witness）。 -/
  galois_moves : (tmzActHom q3awSigma2).map q3awTZeta ≠ q3awTZeta
  /-- ★★外 Galois 作用の非自明性 s(σ₂)·ι(tζ,1)·s(σ₂)⁻¹ ≠ ι(tζ,1)。 -/
  outer_nontrivial :
    q3apArith.mul (q3apArith.mul (q3apSection.map q3awSigma2) (q3apIncl.map q3awZgen))
        (q3apArith.inv (q3apSection.map q3awSigma2))
      ≠ q3apIncl.map q3awZgen
  /-- ★ペアリングの非自明性 ⟨z₀,x₀⟩ ≠ 0。 -/
  pair_nontrivial : q3awPair q3awZgen q3awXlat ≠ (zmod 9).one
  /-- ★ペアリング値も Galois で実際に動く（同変性の非空虚性）。 -/
  pair_galois_moves :
    q3awPair ((q3apTw q3awSigma2).map q3awZgen) ((q3apTw q3awSigma2).map q3awXlat)
      ≠ q3awPair q3awZgen q3awXlat

/-- **§F-2: 見出し実例** — 全フィールド既証明の純レコード。 -/
def q3aw_data : Q3ArithWeilData where
  act_one := q3aw_act_one
  act_mul := q3aw_act_mul
  coord_equivariant := q3aw_coord_equivariant
  pair_bilinear := q3aw_pair_bilinear_left
  pair_alternating := q3aw_pair_alternating
  pair_welldef := q3aw_pairE9_welldef
  weil_galois := q3aw_weil_galois
  conj_pair := q3aw_conj_pair
  chi_sigma2 := q3aw_chi9_sigma2
  galois_moves := q3aw_galois_moves_tzeta
  outer_nontrivial := q3aw_outer_nontrivial
  pair_nontrivial := q3aw_pair_gen_ne_one
  pair_galois_moves := q3aw_pair_galois_moves

/-- **§F-3: 存在** — A4 AP-4 Weil ペアリングスライス＋外 Galois 非自明性 witness。 -/
theorem q3aw_exists : Nonempty Q3ArithWeilData := ⟨q3aw_data⟩

end IUT
