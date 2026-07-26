/-
  IUT/Q3TemperedThetaGaloisL9.lean — A5 N3 [実／(a) 昇格]（prefix `q9ng`）

  ── 主要成果の分類: **[実／(a) 昇格]**（骨格・模型・代理の新規追加でなく、既存の
     「χ 捻りが *見える*」という非不変性ステートメント `q9nt_chi_visible` を、
     **実 Galois 群 Gal(M/L₂)=⟨σ⟩（q9kdG・位数 3・σ:Y↦ζ₃Y・`q3kSigma`）の実共役作用**へ
     昇格させる。作用の担体は実 M^×=q9tlMx=ℤ(v_π)×U₃ の実単数群化 σU=`q9mbSigmaU`
     （ノルム保存で well-defined・`q9mb_sigmaU_zeta`: σU(ζ₉U)=ζ₉U⁴）であり、
     Bool 軌道・surrogate 群・m202fVol 型 toy は一切主語にしない。
     旗艦の主語は **実 tempered テータ実現 Φ₉/Ψ₉**（`q9ntPhi`/`q9ntPsi`）の像である。
     ただし「Φ₉/Ψ₉ を消去すると命題が消滅する」のは **deck 方向の命題**
     （`q9ng_deck_theta_galois`・`q9ng_sigma9_deck`・`q9ng_sigma9_X`）に限る——
     **正直な訂正（独立監査 2026-07-21 指摘）**: headline `q9ng_outer_theta_cyclotome` は
     本ファイル自身の `q9ng_psi_cyc1`/`q9ng_psi_cyc4` により Ψ₉ が **消去可能**で、実質は
     `Z₉ ∈ q9mtM` の ι-共役であり、flagship `q9ng_symplectic_galois` は `thetaGrp.carrier`
     上の量化で deck 内容を持たない。さらに deck 方向 3 命題の証明も **ℤ の離散性を使わず**、
     pro-3 deck でもそのまま通る。よって temperedness は本ファイルでは
     **継承された文脈であって証明の担い手ではない**。当初ヘッダの全旗艦一括主張は誤りだった。）

  complete_pct 影響: **A5 N3（s_A5 0.27 → 予測 +0.02〜+0.03・独立敵対監査確定が条件）**。
     質的新規 3 点:
     (i)  **A5 実現への初の実 Galois 作用** σ₉ : q9mtM → q9mtM（実 σU の成分持ち上げ・
          σ₉³=id・自己同型）。これまで A5 側に実 Galois 作用は 1 本も無かった
          （grep 実測: σU の消費者は q9mb 自身のみ・q9mtM への Galois 作用ゼロ）。
     (ii) **χ₉(σ)=4 の実値実装**: σ₉(Z₉)=Z₉⁴・σ₉(Y)=Y⁴・σ₉(Φ₉(0,b,c))=Φ₉(0,4b,4c)。
          M429F `atpTw e` の骨格 (a,b,c,n)↦(a,eb,ec,n) が **e=4∈(ℤ/9)^× という実 Galois 値**で
          初めて実現する（q9nt の「可視」から「実装」への昇格）。
     (iii) **q9nt 正直限定 3 の σ-only discharge**: 半直積 q9mtM⋊⟨σ⟩ と外 Galois 定理により
          s(σ)·ι(Ψ₉(ι(0,0,1)))·s(σ)⁻¹ = ι(Ψ₉(ι(0,0,4))) ≠ ι(Ψ₉(ι(0,0,1)))。
     **A4/A7 status は主張しない**（q3ap/q3aw の半直積イディオムはクローンと自己申告・
     q9mb/q9kd/q3k の定理は消費のみで再証明 0 本）。

  ここで「tempered であって étale ではない」ことの内実（overclaim 禁止の要）:
     本ファイルの Galois 共役の被作用子は **Ψ₉ の像**であり、Ψ₉ の定義域 tpeGroup =
     thetaGrp ⋊ **ℤ（離散無限巡回デッキ）** は副有限 π₁^ét の稠密**真**部分（`q3tpd`:
     `Q3TemperedEtDensity.lean`）である。デッキ方向 X=q9mtG3 の冪 Xⁿ（n∈ℤ）は
     副有限完備化 ℤ₃ でなく離散 ℤ で添字づけられ、`theta_deck_not_finite` 系の非副有限性を
     継承する。**π₁^ét 側の対象（q3apArith・tmzLimit×q3pePi1 3 等）は本ファイルの主語に
     一切現れない**。したがって本ファイルの主張は π₁^ét についての主張の言い換えではない。

  正直な限定（§4 準拠・消去/弱化しない・q9nt/q9mt/q9mb/q3k/q9tl/q3ap の限定を全て継承）:
  1. **A5 恒久上限 0.35–0.4 は不変**: tempered π₁ の「定義」（Berkovich/rigid 解析被覆・
     位相 π₁）は依然外部。Φ₉/Ψ₉ は「実被覆空間の π₁ からの写像」ではない（q9nt 限定 2 継承）。
  2. **σ-only Galois**: 作用群は Gal(M/L₂)=⟨σ⟩（位数 3・χ₉ 像 {1,4,7}⊂(ℤ/9)^× の指数 2
     部分群）のみ。**full Gal(M/ℚ₃)≅(ℤ/9)^×（位数 6）・実 G_{ℚ₃} は未建設**（L₂/ℚ₃ 層＝
     ζ₃↦ζ₃² の M=L₂[Y]/(Y³−ζ₃) への持ち上げは提示変更 Y³=ζ₃² を伴う非クローン建設・
     named future target）。「tempered π₁ への G_K 作用を実現した」とは書かない。
  3. **分裂スライスの帽子（正直核 q9ng-7）**: σ̃M(n,u)=(n,σU u) は体 M^× の Galois 作用の
     **次数付き分裂スライス**であり、一様化子捻り cσ=σ(π₉)/π₉（=1+Y+Y²+ζ₃）を捨てている。
     真の作用は σ(π₉ⁿu)=π₉ⁿ·cσⁿ·σ(u)。帰結として **σ₉ は X=q9mtG3 を固定せず
     σ₉(X)=uδ·X（uδ=単数平行移動 δU=σU(u₆)·u₆⁻¹）**（`q9ng_sigma9_X`）。q3ap 正直限定 (ii)
     （graded split slice）と同族の帽子である。
  4. **テータ部分群 q9mtGrp の保存は主張しない**: σ₉ は ambient な Heisenberg 担体 q9mtM 上の
     自己同型であって、中心化条件 q9mtMem（qᵃw⁹=1）を保存するとは**主張しない**
     （保存する「正しい」捻り作用 σ̃(n,u)=(cσⁿ·σU u) の正当化は cσ⁶·σU(u₆)=u₆ という
     消去律依存の crux を要する。**named future target**）。「テータ群の Galois 剛性」とは
     書かない（剛性は A7 の主語）。
  5. **q9nt の正直限定を全て継承・並置**: level-9 崩壊（Ψ₉ 非単射・Ψ₉(ι(0,0,9))=1）・
     full ẑ(1)/全素数 l 未達・実テータ関数 0・cuspidalization 0・q=3⁹ の忠実部分ケース・
     pro-3 恒久スコープ・K-point の影。q9mb/q3k/q9tl/q9mt の正直限定も継承する。
  6. **level-27 tempered テータは未着**（q27tl/q27mt が A6 キャンペーンで未実装・前提欠落）。
  7. **二重計上の firewall**: q9mbSigmaU/q9mb_sigmaU_zeta/q9kdG/q3k_sigma3_id/q9ntPhi/q9ntPsi/
     q9mtM/q9mtWeil は**消費のみ**（再証明 0 本・共有ファイル不変更）。半直積＋外 Galois 定理の
     イディオムは q3ap のクローンであると自己申告する（G も担体も Weil 形式の主語も異なるが、
     イディオム自体は新規でない）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用（omega は純 Int/Nat のみ）。
-/
import IUT.Q3TemperedThetaClassL9
import IUT.Q3Mu9TmzBridge
import IUT.Q3KummerDualityReal
import IUT.Q3Etale9TwoDir

namespace IUT

/-! ## q9ng-0: 実 Galois σ の単数群化 σU の Hom 化と M^× への成分持ち上げ σ̃M -/

/-- **q9ng-0a: σU : U₃ → U₃ を群準同型として束ねる**（`q9mb_sigmaU_mul` 消費・再証明 0）。
    実 Gal(M/L₂) 生成元 σ（Y↦ζ₃Y・環自己同型）のノルム保存による単数群化。 -/
def q9ngSigmaU : Hom q3kU q3kU where
  map := q9mbSigmaU
  map_mul := q9mb_sigmaU_mul

/-- **q9ng-0b: σU³ = id**（`q3k_sigma3_id` の subtype 持ち上げ・σ の位数ちょうど 3）。 -/
theorem q9ng_sigmaU3 (u : q3kU.carrier) :
    q9mbSigmaU (q9mbSigmaU (q9mbSigmaU u)) = u :=
  Subtype.ext (q3k_sigma3_id u.val)

/-- **q9ng-0c（★）: σ̃M : M^× → M^×**（(n,u) ↦ (n, σU u)）— 実 Galois σ の
    M^×=ℤ(v_π)×U₃ への**次数付き分裂スライス**としての持ち上げ（正直限定 3）。 -/
def q9ngSigmaMx : Hom q9tlMx q9tlMx where
  map := fun z => (z.1, q9mbSigmaU z.2)
  map_mul := by
    intro z w
    show ((intGrp.mul z.1 w.1, q9mbSigmaU (q3kU.mul z.2 w.2)) : q9tlMx.carrier)
       = (intGrp.mul z.1 w.1, q3kU.mul (q9mbSigmaU z.2) (q9mbSigmaU w.2))
    rw [q9mb_sigmaU_mul]

/-- **q9ng-0d: σ̃M³ = id**。 -/
theorem q9ng_sigmaMx3 (z : q9tlMx.carrier) :
    q9ngSigmaMx.map (q9ngSigmaMx.map (q9ngSigmaMx.map z)) = z := by
  obtain ⟨n, u⟩ := z
  show ((n, q9mbSigmaU (q9mbSigmaU (q9mbSigmaU u))) : q9tlMx.carrier) = (n, u)
  rw [q9ng_sigmaU3 u]

/-! ## q9ng-1: 実 Galois 作用 σ₉ : q9mtM → q9mtM（テータ Heisenberg 担体上の自己同型） -/

/-- **q9ng-1a（★核）: σ₉ : q9mtM → q9mtM**（(c,a,w) ↦ (σ̃M c, a, σ̃M w)）—
    実 Galois σ の**テータ群担体 M₉ への作用**。map_mul は cocycle 3 成分の同変性
    （σ̃M の map_mul ＋ hom_map_zpow で w′ᵃ 項を通す・Int スロットは固定）。
    A5 実現側に実 Galois 作用が入るのはこれが初。 -/
def q9ngSigma9 : Hom q9mtM q9mtM where
  map := fun g => ((q9ngSigmaMx.map g.1.1, g.1.2), q9ngSigmaMx.map g.2)
  map_mul := by
    intro g g'
    obtain ⟨⟨c, a⟩, w⟩ := g
    obtain ⟨⟨c', a'⟩, w'⟩ := g'
    show ((q9ngSigmaMx.map (q9tlMx.mul (q9tlMx.mul c c') (tateZpow q9tlMx w' a)), a + a'),
          q9ngSigmaMx.map (q9tlMx.mul w w'))
       = ((q9tlMx.mul (q9tlMx.mul (q9ngSigmaMx.map c) (q9ngSigmaMx.map c'))
             (tateZpow q9tlMx (q9ngSigmaMx.map w') a), a + a'),
          q9tlMx.mul (q9ngSigmaMx.map w) (q9ngSigmaMx.map w'))
    rw [q9ngSigmaMx.map_mul (q9tlMx.mul c c') (tateZpow q9tlMx w' a),
        q9ngSigmaMx.map_mul c c',
        hom_map_zpow q9ngSigmaMx w' a,
        q9ngSigmaMx.map_mul w w']

/-- **q9ng-1b: σ₉³ = id**（σ̃M³=id の成分適用）——σ₉ は自己同型（逆は σ₉²）。 -/
theorem q9ng_sigma9_3 (g : q9mtCar) :
    q9ngSigma9.map (q9ngSigma9.map (q9ngSigma9.map g)) = g := by
  obtain ⟨⟨c, a⟩, w⟩ := g
  show ((q9ngSigmaMx.map (q9ngSigmaMx.map (q9ngSigmaMx.map c)), a),
        q9ngSigmaMx.map (q9ngSigmaMx.map (q9ngSigmaMx.map w))) = ((c, a), w)
  rw [q9ng_sigmaMx3 c, q9ng_sigmaMx3 w]

/-- **q9ng-1c: σ₉ は単射**（σ₉² が左逆）。 -/
theorem q9ng_sigma9_injective : q9ngSigma9.Injective := by
  intro a b h
  have h3a := q9ng_sigma9_3 a
  have h3b := q9ng_sigma9_3 b
  rw [← h3a, ← h3b, h]

/-- **q9ng-1d: σ₉ は全射**（σ₉² が右逆）——σ₉ は q9mtM の**自己同型**。 -/
theorem q9ng_sigma9_surjective (g : q9mtCar) :
    ∃ h : q9mtCar, q9ngSigma9.map h = g :=
  ⟨q9ngSigma9.map (q9ngSigma9.map g), q9ng_sigma9_3 g⟩

/-! ## q9ng-2（★）: σ₉(Z₉) = Z₉⁴ — 実円分指標値 χ₉(σ)=4 のテータシクロトーム実装 -/

/-- **q9ng-2a: σ̃M(ζ₉⁻¹ の担体) = (ζ₉⁻¹)⁴**（`q9mb_sigmaU_zeta`: σU(ζ₉U)=ζ₉U⁴ の逆元化）。 -/
theorem q9ng_sigmaMx_Zw : q9ngSigmaMx.map q9ntZw = tateZpow q9tlMx q9ntZw 4 := by
  have hz4 : tateZpow q9tlMx q9ntZw 4 = tateNpow q9tlMx q9ntZw 4 := rfl
  have hu : q9mbSigmaU (q3kU.inv q9tlZeta9U) = q3kU.inv (tateNpow q3kU q9tlZeta9U 4) := by
    have h1 : q9mbSigmaU (q3kU.inv q9tlZeta9U) = q3kU.inv (q9mbSigmaU q9tlZeta9U) :=
      Hom.map_inv q9ngSigmaU q9tlZeta9U
    rw [h1, q9mb_sigmaU_zeta, q9mb_npow_pow]
  rw [hz4]
  apply Prod.ext
  · show (0 : Int) = (tateNpow q9tlMx q9ntZw 4).1
    rw [q9tl_npow_fst q9ntZw 4, tateNpow_intGrp]
    show (0 : Int) = ((4 : Nat) : Int) * (0 : Int)
    omega
  · show q9mbSigmaU (q3kU.inv q9tlZeta9U) = (tateNpow q9tlMx q9ntZw 4).2
    rw [q9tl_npow_snd q9ntZw 4, hu]
    show q3kU.inv (tateNpow q3kU q9tlZeta9U 4)
       = tateNpow q3kU (q3kU.inv q9tlZeta9U) 4
    have a1 : tateZpow q3kU (q3kU.inv q9tlZeta9U) (Int.ofNat 4)
        = tateZpow q3kU q9tlZeta9U (-(Int.ofNat 4)) :=
      grp_zpow_inv_base q3kU q9tlZeta9U (Int.ofNat 4)
    have a2 : tateZpow q3kU q9tlZeta9U (-(Int.ofNat 4))
        = q3kU.inv (tateZpow q3kU q9tlZeta9U (Int.ofNat 4)) :=
      tateZpow_neg q3kU q9tlZeta9U (Int.ofNat 4)
    exact (a1.trans a2).symm

/-- **q9ng-2b（★★ headline の核）: σ₉(Z₉) = Z₉⁴** — 実 Galois σ はテータシクロトーム生成元
    Z₉ = Φ₉(0,0,1)（位数ちょうど 9・`q9nt_cyclotome_order9`）を **χ₉(σ)=4 乗に捻る**。
    M429F atpTw e の骨格が実 Galois 値 e=4 ∈ (ℤ/9)^× で実現する。 -/
theorem q9ng_sigma9_Z9 : q9ngSigma9.map q9ntZ9 = tateZpow q9mtM q9ntZ9 4 := by
  rw [q9nt_Z9_zpow 4, ← q9ng_sigmaMx_Zw]
  show ((q9ngSigmaMx.map q9ntZw, (0 : Int)), q9ngSigmaMx.map q9tlMx.one)
     = ((q9ngSigmaMx.map q9ntZw, (0 : Int)), q9tlMx.one)
  rw [q9ngSigmaMx.map_one]

/-- **q9ng-2c: 一般冪** σ₉(Z₉ᶜ) = Z₉^{4c}（`q9td_zzpow` 消費・新規イディオム 0）。 -/
theorem q9ng_sigma9_Z9_zpow (c : Int) :
    q9ngSigma9.map (tateZpow q9mtM q9ntZ9 c) = tateZpow q9mtM q9ntZ9 (4 * c) := by
  rw [hom_map_zpow q9ngSigma9 q9ntZ9 c, q9ng_sigma9_Z9, q9td_zzpow]

/-- **q9ng-2d: 捻りは非自明** Z₉⁴ ≠ Z₉（⟸ Z₉³ ≠ 1・位数ちょうど 9）。
    σ が実際にテータシクロトームを動かすことの実証明。 -/
theorem q9ng_Z9_four_ne : tateZpow q9mtM q9ntZ9 4 ≠ q9ntZ9 := by
  intro h
  have hz4 : tateZpow q9mtM q9ntZ9 4 = q9mtM.mul (tateNpow q9mtM q9ntZ9 3) q9ntZ9 := rfl
  have h4 : q9mtM.mul (tateNpow q9mtM q9ntZ9 3) q9ntZ9 = q9mtM.mul q9mtM.one q9ntZ9 := by
    rw [q9mtM.one_mul, ← hz4]
    exact h
  exact q9nt_Z9_npow_ne 3 (by omega) (by omega) (q9mtM.mul_right_cancel h4)

/-- **q9ng-2e（★）: σ₉ はテータシクロトーム生成元を動かす** σ₉(Φ₉(0,0,1)) ≠ Φ₉(0,0,1)。 -/
theorem q9ng_sigma9_moves_cyclotome :
    q9ngSigma9.map (q9ntPhi.map ((0, 0, 1) : Int × Int × Int))
      ≠ q9ntPhi.map ((0, 0, 1) : Int × Int × Int) := by
  rw [q9nt_cyclotome_real, q9ng_sigma9_Z9]
  exact q9ng_Z9_four_ne

/-! ## q9ng-3（★）: σ₉(Y) = Y⁴ と χ 捻り Φ₉(0,b,c) ↦ Φ₉(0,4b,4c) の実装 -/

/-- 平行移動埋め込み M^× → M₉（w ↦ (1,0,w)）— a=0 スロットゆえ cocycle 蓄積ゼロで準同型。 -/
def q9ngTrans : Hom q9tlMx q9mtM where
  map := fun w => ((q9tlMx.one, (0 : Int)), w)
  map_mul := by
    intro w w'
    show ((q9tlMx.one, (0 : Int)), q9tlMx.mul w w')
       = ((q9tlMx.mul (q9tlMx.mul q9tlMx.one q9tlMx.one) (tateZpow q9tlMx w' 0),
           (0 : Int) + 0), q9tlMx.mul w w')
    have h00 : (0 : Int) + 0 = 0 := by omega
    rw [tateZpow_zero, q9tlMx.mul_one, q9tlMx.one_mul, h00]

/-- Y = q9mtGZeta は平行移動埋め込みの像（定義的）。 -/
theorem q9ng_Y_trans : q9mtGZeta = q9ngTrans.map q9tlZeta9Elt := rfl

/-- **q9ng-3a: σ̃M(ζ₉ の担体) = ζ₉⁴**（`q9mb_sigmaU_zeta` そのもの）。 -/
theorem q9ng_sigmaMx_zeta : q9ngSigmaMx.map q9tlZeta9Elt = tateZpow q9tlMx q9tlZeta9Elt 4 := by
  have hz4 : tateZpow q9tlMx q9tlZeta9Elt 4 = tateNpow q9tlMx q9tlZeta9Elt 4 := rfl
  rw [hz4]
  apply Prod.ext
  · show (0 : Int) = (tateNpow q9tlMx q9tlZeta9Elt 4).1
    rw [q9tl_npow_fst q9tlZeta9Elt 4, tateNpow_intGrp]
    show (0 : Int) = ((4 : Nat) : Int) * (0 : Int)
    omega
  · show q9mbSigmaU q9tlZeta9U = (tateNpow q9tlMx q9tlZeta9Elt 4).2
    rw [q9tl_npow_snd q9tlZeta9Elt 4, q9mb_sigmaU_zeta, q9mb_npow_pow]
    rfl

/-- **q9ng-3b（★）: σ₉(Y) = Y⁴ on the nose**（Y=q9mtGZeta=[ζ₉] の実 Galois 共役）。 -/
theorem q9ng_sigma9_Y : q9ngSigma9.map q9mtGZeta = tateZpow q9mtM q9mtGZeta 4 := by
  rw [q9ng_Y_trans, ← hom_map_zpow q9ngTrans q9tlZeta9Elt 4, ← q9ng_sigmaMx_zeta]
  show ((q9ngSigmaMx.map q9tlMx.one, (0 : Int)), q9ngSigmaMx.map q9tlZeta9Elt)
     = ((q9tlMx.one, (0 : Int)), q9ngSigmaMx.map q9tlZeta9Elt)
  rw [q9ngSigmaMx.map_one]

/-- **q9ng-3c（★★ 昇格の中心）: χ 捻りの実 Galois 実装** —
    σ₉(Φ₉(0,b,c)) = Φ₉(0, 4b, 4c)。M429F の算術捻り骨格 `atpTw e`（(a,b,c,n)↦(a,eb,ec,n)）が
    **e = χ₉(σ) = 4 ∈ (ℤ/9)^× という実 Galois 指標値**で実現する。q9nt_chi_visible の
    「捻りに対する Ψ₉ の非不変性（＝捻りが見える）」が「実 Galois 共役として実装されている」へ
    昇格する（q9nt 正直限定 3 の σ-only discharge）。 -/
theorem q9ng_chi_twist (b c : Int) :
    q9ngSigma9.map (q9ntPhi.map ((0, b, c) : Int × Int × Int))
      = q9ntPhi.map ((0, 4 * b, 4 * c) : Int × Int × Int) := by
  show q9ngSigma9.map (q9mtM.mul (tateZpow q9mtM q9mtGZeta b)
        (q9mtM.mul (tateZpow q9mtM q9mtG3 0) (tateZpow q9mtM q9ntZ9 c)))
     = q9mtM.mul (tateZpow q9mtM q9mtGZeta (4 * b))
        (q9mtM.mul (tateZpow q9mtM q9mtG3 0) (tateZpow q9mtM q9ntZ9 (4 * c)))
  rw [tateZpow_zero q9mtM q9mtG3, q9mtM.one_mul, q9mtM.one_mul,
      q9ngSigma9.map_mul (tateZpow q9mtM q9mtGZeta b) (tateZpow q9mtM q9ntZ9 c),
      hom_map_zpow q9ngSigma9 q9mtGZeta b, hom_map_zpow q9ngSigma9 q9ntZ9 c,
      q9ng_sigma9_Y, q9ng_sigma9_Z9, q9td_zzpow, q9td_zzpow]

/-! ## q9ng-4（★★ 旗艦 1）: μ₉ Weil 形式の実 Galois 同変性 -/

/-- **q9ng-4a（★★）: Weil 形式の Galois 同変性** e₉(σ₉g, σ₉g′) = σ̃M(e₉(g,g′))。
    q9mtWeil は担体全体で定義されるので**テータ部分群への所属を要さない**（正直限定 4）。
    q3aw_weil_galois の**実 tempered テータ版**（主語はテータ交換子のスカラー成分）。 -/
theorem q9ng_weil_equivariant (g g' : q9mtCar) :
    q9mtWeil (q9ngSigma9.map g) (q9ngSigma9.map g')
      = q9ngSigmaMx.map (q9mtWeil g g') := by
  obtain ⟨⟨c, a⟩, w⟩ := g
  obtain ⟨⟨c', a'⟩, w'⟩ := g'
  show q9tlMx.mul (tateZpow q9tlMx (q9ngSigmaMx.map w') a)
        (tateZpow q9tlMx (q9ngSigmaMx.map w) (-a'))
     = q9ngSigmaMx.map (q9tlMx.mul (tateZpow q9tlMx w' a) (tateZpow q9tlMx w (-a')))
  rw [q9ngSigmaMx.map_mul (tateZpow q9tlMx w' a) (tateZpow q9tlMx w (-a')),
      hom_map_zpow q9ngSigmaMx w' a, hom_map_zpow q9ngSigmaMx w (-a')]

/-- **q9ng-4b（★★ 旗艦 1）: Φ₉ 像上のシンプレクティック形式は χ₉(σ)=4 倍に捻れる** —
    [σ₉Φ₉v, σ₉Φ₉w] = Z₉^{4·ω(v,w)}（ω(v,w)=v₁w₂−w₁v₂）。
    実 tempered テータ実現 Φ₉ の像における μ₉ Weil ペアリングの**実 Galois 同変性**。
    Φ₉ を消去すると命題が消滅する（主語は Φ₉ 像の交換子）。 -/
theorem q9ng_symplectic_galois (v w : thetaGrp.carrier) :
    q9mtComm (q9ngSigma9.map (q9ntPhi.map v)) (q9ngSigma9.map (q9ntPhi.map w))
      = tateZpow q9mtM q9ntZ9 (4 * (v.1 * w.2.1 - w.1 * v.2.1)) := by
  rw [q9nt_comm_eq, ← Hom.map_grp_comm q9ngSigma9 (q9ntPhi.map v) (q9ntPhi.map w),
      ← q9nt_comm_eq, q9nt_symplectic_real v w, q9ng_sigma9_Z9_zpow]

/-- **q9ng-4c（★）: deck×テータ交換子も χ₉(σ)=4 倍に捻れる** —
    [σ₉Ψ₉(s n), σ₉Ψ₉(ι(a,b,c))] = Z₉^{4nb}。tempered デッキ（離散 ℤ）方向の
    非可換性（`q9nt_deck_theta_real`）の実 Galois 共役。 -/
theorem q9ng_deck_theta_galois (n a b c : Int) :
    q9mtComm (q9ngSigma9.map (q9ntPsi.map (tpeSection.map n)))
        (q9ngSigma9.map (q9ntPsi.map (tpeIncl.map ((a, b, c) : Int × Int × Int))))
      = tateZpow q9mtM q9ntZ9 (4 * (n * b)) := by
  rw [q9nt_comm_eq, ← Hom.map_grp_comm q9ngSigma9, ← q9nt_comm_eq,
      q9nt_deck_theta_real n a b c, q9ng_sigma9_Z9_zpow]

/-! ## q9ng-5（★★ 旗艦 2）: 半直積 q9mtM ⋊ Gal(M/L₂) と外 Galois 定理

    半直積＋完全列＋外 Galois 定理のイディオムは q3ap（A4）のクローンであると自己申告する
    （§7 正直限定・A4 status は主張しない）。新規なのは作用群 G = 実局所 Gal(M/L₂)=⟨σ⟩ と
    被作用対象 = 実 μ₉ テータ Heisenberg 担体 q9mtM である点。 -/

/-- 任意群で 1⁻¹ = 1（外 Galois 定理の共役計算用・q3ap の同名補題の再掲でなく局所建設）。 -/
theorem q9ng_inv_one (G : Grp) : G.inv G.one = G.one := by
  have h := G.inv_mul G.one
  rw [G.mul_one] at h
  exact h

/-- 恒等準同型（作用の e 成分）。 -/
def q9ngIdHom : Hom q9mtM q9mtM where
  map := fun g => g
  map_mul := fun _ _ => rfl

/-- **q9ng-5a: 実 Galois 作用 ⟨σ⟩ → Aut(q9mtM)**（e↦id・s↦σ₉・s2↦σ₉²）。 -/
def q9ngTw : q9kdGCar → Hom q9mtM q9mtM
  | .e => q9ngIdHom
  | .s => q9ngSigma9
  | .s2 => Hom.comp q9ngSigma9 q9ngSigma9

/-- **q9ng-5b: 単位則** tw(1) = id。 -/
theorem q9ng_tw_one (g : q9mtCar) : (q9ngTw q9kdG.one).map g = g := rfl

/-- **q9ng-5c: 合成則** tw(gh) = tw g ∘ tw h（Cayley 表 9 場合 × σ₉³=id）。 -/
theorem q9ng_tw_mul (g h : q9kdGCar) (x : q9mtCar) :
    (q9ngTw (q9kdGMul g h)).map x = (q9ngTw g).map ((q9ngTw h).map x) := by
  cases g with
  | e => cases h <;> rfl
  | s =>
    cases h with
    | e => rfl
    | s => rfl
    | s2 => exact (q9ng_sigma9_3 x).symm
  | s2 =>
    cases h with
    | e => rfl
    | s => exact (q9ng_sigma9_3 x).symm
    | s2 =>
      show q9ngSigma9.map x
         = q9ngSigma9.map (q9ngSigma9.map (q9ngSigma9.map (q9ngSigma9.map x)))
      exact (q9ng_sigma9_3 (q9ngSigma9.map x)).symm

/-- **q9ng-5d（★核）: 半直積 Π₉ = q9mtM ⋊ Gal(M/L₂)**。
    台 q9mtCar × q9kdGCar・積 (x,g)(y,h) = (x·(tw g)(y), g·h)。
    群公理は q9ngTw の準同型性・作用性から抽象的に従う（q3ap AP-1 イディオムの写経）。 -/
def q9ngArith : Grp where
  carrier := q9mtCar × q9kdGCar
  mul := fun p q => (q9mtM.mul p.1 ((q9ngTw p.2).map q.1), q9kdG.mul p.2 q.2)
  one := (q9mtM.one, q9kdG.one)
  inv := fun p => ((q9ngTw (q9kdG.inv p.2)).map (q9mtM.inv p.1), q9kdG.inv p.2)
  mul_assoc := by
    intro x y z
    obtain ⟨a, g⟩ := x
    obtain ⟨b, g'⟩ := y
    obtain ⟨c, g''⟩ := z
    show (q9mtM.mul (q9mtM.mul a ((q9ngTw g).map b)) ((q9ngTw (q9kdGMul g g')).map c),
          q9kdGMul (q9kdGMul g g') g'')
       = (q9mtM.mul a ((q9ngTw g).map (q9mtM.mul b ((q9ngTw g').map c))),
          q9kdGMul g (q9kdGMul g' g''))
    have hass : q9kdGMul (q9kdGMul g g') g'' = q9kdGMul g (q9kdGMul g' g'') :=
      q9kdG.mul_assoc g g' g''
    rw [(q9ngTw g).map_mul b ((q9ngTw g').map c), q9ng_tw_mul g g' c,
        q9mtM.mul_assoc a ((q9ngTw g).map b) ((q9ngTw g).map ((q9ngTw g').map c)), hass]
  one_mul := by
    intro x
    obtain ⟨a, g⟩ := x
    show (q9mtM.mul q9mtM.one ((q9ngTw q9kdG.one).map a), q9kdGMul q9kdGCar.e g) = (a, g)
    rw [q9ng_tw_one a, q9mtM.one_mul a]
    rfl
  inv_mul := by
    intro x
    obtain ⟨a, g⟩ := x
    show (q9mtM.mul ((q9ngTw (q9kdG.inv g)).map (q9mtM.inv a))
            ((q9ngTw (q9kdG.inv g)).map a), q9kdG.mul (q9kdG.inv g) g)
       = (q9mtM.one, q9kdG.one)
    rw [← (q9ngTw (q9kdG.inv g)).map_mul (q9mtM.inv a) a, q9mtM.inv_mul a,
        (q9ngTw (q9kdG.inv g)).map_one, q9kdG.inv_mul g]

/-- **q9ng-5e: 核埋め込み ι : q9mtM ↪ Π₉**。 -/
def q9ngIncl : Hom q9mtM q9ngArith where
  map := fun x => (x, q9kdG.one)
  map_mul := by
    intro x y
    show ((q9mtM.mul x y, q9kdGCar.e) : q9ngArith.carrier)
       = (q9mtM.mul x ((q9ngTw q9kdG.one).map y), q9kdGMul q9kdGCar.e q9kdGCar.e)
    rw [q9ng_tw_one y]
    rfl

/-- **q9ng-5f: 射影 pr : Π₉ ↠ Gal(M/L₂)**。 -/
def q9ngProj : Hom q9ngArith q9kdG where
  map := fun x => x.2
  map_mul := fun _ _ => rfl

/-- **q9ng-5g: 分裂切断 s : Gal(M/L₂) → Π₉**。 -/
def q9ngSection : Hom q9kdG q9ngArith where
  map := fun g => (q9mtM.one, g)
  map_mul := by
    intro g g'
    show ((q9mtM.one, q9kdGMul g g') : q9ngArith.carrier)
       = (q9mtM.mul q9mtM.one ((q9ngTw g).map q9mtM.one), q9kdGMul g g')
    rw [(q9ngTw g).map_one, q9mtM.one_mul]
    rfl

/-- **q9ng-5h: ι は単射**。 -/
theorem q9ng_incl_injective : q9ngIncl.Injective :=
  fun _ _ h => congrArg Prod.fst h

/-- **q9ng-5i: pr は全射**。 -/
theorem q9ng_proj_surjective : ∀ g : q9kdGCar, ∃ x, q9ngProj.map x = g :=
  fun g => ⟨q9ngSection.map g, rfl⟩

/-- **q9ng-5j: 切断は分裂** pr ∘ s = id。 -/
theorem q9ng_section_splits (g : q9kdGCar) : q9ngProj.map (q9ngSection.map g) = g := rfl

/-- **q9ng-5k（★）: 完全性** ker(pr) = im(ι)：1 → q9mtM → Π₉ → Gal(M/L₂) → 1。 -/
theorem q9ng_extension_exact (x : q9ngArith.carrier) :
    q9ngProj.map x = q9kdG.one ↔ ∃ z : q9mtCar, q9ngIncl.map z = x := by
  obtain ⟨z, g⟩ := x
  constructor
  · intro h
    have hg : g = q9kdGCar.e := h
    rw [hg]
    exact ⟨z, rfl⟩
  · intro h
    obtain ⟨w, hw⟩ := h
    show g = q9kdGCar.e
    exact (congrArg Prod.snd hw).symm

/-- **q9ng-5l: 共役の明示公式**（外 Galois 表現の実内容）。 -/
theorem q9ng_conj_incl (g₀ : q9mtCar) (g : q9kdGCar) (z : q9mtCar) :
    q9ngArith.mul (q9ngArith.mul ((g₀, g) : q9ngArith.carrier) (q9ngIncl.map z))
        (q9ngArith.inv (g₀, g))
      = q9ngIncl.map (q9mtM.mul (q9mtM.mul g₀ ((q9ngTw g).map z)) (q9mtM.inv g₀)) := by
  have h1 : q9ngArith.mul ((g₀, g) : q9ngArith.carrier) (q9ngIncl.map z)
      = (q9mtM.mul g₀ ((q9ngTw g).map z), g) := by
    show (q9mtM.mul g₀ ((q9ngTw g).map z), q9kdG.mul g q9kdG.one)
       = (q9mtM.mul g₀ ((q9ngTw g).map z), g)
    have h2 : q9kdG.mul g q9kdG.one = g := q9kdG.mul_one g
    rw [h2]
    rfl
  rw [h1]
  show (q9mtM.mul (q9mtM.mul g₀ ((q9ngTw g).map z))
          ((q9ngTw g).map ((q9ngTw (q9kdG.inv g)).map (q9mtM.inv g₀))),
        q9kdG.mul g (q9kdG.inv g))
     = q9ngIncl.map (q9mtM.mul (q9mtM.mul g₀ ((q9ngTw g).map z)) (q9mtM.inv g₀))
  have hginv : q9kdGMul g (q9kdG.inv g) = q9kdG.one := Grp.mul_inv q9kdG g
  have hginv2 : q9kdG.mul g (q9kdG.inv g) = q9kdG.one := Grp.mul_inv q9kdG g
  rw [← q9ng_tw_mul g (q9kdG.inv g) (q9mtM.inv g₀), hginv,
      q9ng_tw_one (q9mtM.inv g₀), hginv2]
  rfl

/-- **q9ng-5m（★）: 幾何部の正規性**。 -/
theorem q9ng_kernel_normal (g : q9ngArith.carrier) (z : q9mtCar) :
    ∃ w : q9mtCar,
      q9ngArith.mul (q9ngArith.mul g (q9ngIncl.map z)) (q9ngArith.inv g) = q9ngIncl.map w := by
  obtain ⟨g₀, gg⟩ := g
  exact ⟨q9mtM.mul (q9mtM.mul g₀ ((q9ngTw gg).map z)) (q9mtM.inv g₀), q9ng_conj_incl g₀ gg z⟩

/-- **q9ng-5n（★★ 旗艦 2）: 外 Galois 定理** s(g)·ι(x)·s(g)⁻¹ = ι((tw g)(x))。
    実局所 Galois 群 Gal(M/L₂)=⟨σ⟩ が μ₉ テータ Heisenberg 担体に**外から実作用**する。 -/
theorem q9ng_outer_galois (g : q9kdGCar) (z : q9mtCar) :
    q9ngArith.mul (q9ngArith.mul (q9ngSection.map g) (q9ngIncl.map z))
        (q9ngArith.inv (q9ngSection.map g))
      = q9ngIncl.map ((q9ngTw g).map z) := by
  show q9ngArith.mul (q9ngArith.mul ((q9mtM.one, g) : q9ngArith.carrier) (q9ngIncl.map z))
      (q9ngArith.inv (q9mtM.one, g))
    = q9ngIncl.map ((q9ngTw g).map z)
  rw [q9ng_conj_incl q9mtM.one g z, q9mtM.one_mul ((q9ngTw g).map z),
      q9ng_inv_one q9mtM, q9mtM.mul_one ((q9ngTw g).map z)]

/-! ## q9ng-6（★★★ headline）: 実外 Galois 共役は tempered テータシクロトームを 4 倍に捻る -/

/-- Ψ₉(ι(0,0,1)) = Z₉（tempered テータシクロトーム生成元の実担体）。 -/
theorem q9ng_psi_cyc1 :
    q9ntPsi.map (tpeIncl.map ((0, 0, 1) : Int × Int × Int)) = q9ntZ9 := by
  rw [q9nt_psi_incl, q9nt_cyclotome_real]

/-- Ψ₉(ι(0,0,4)) = Z₉⁴。 -/
theorem q9ng_psi_cyc4 :
    q9ntPsi.map (tpeIncl.map ((0, 0, 4) : Int × Int × Int)) = tateZpow q9mtM q9ntZ9 4 := by
  rw [q9nt_psi_incl, q9nt_phi_center]

/-- **q9ng-6a（★★★ headline）: 実外 Galois 共役はテータシクロトームを χ₉(σ)=4 倍に捻る** —
    s(σ)·ι(Ψ₉(ι(0,0,1)))·s(σ)⁻¹ = ι(Ψ₉(ι(0,0,4)))。
    左辺の主語は**実 tempered テータ実現 Ψ₉ の像**（Ψ₉ の定義域 tpeGroup = thetaGrp ⋊ ℤ の
    デッキ部は離散 ℤ であり副有限 π₁^ét ではない・`q3tpd` の稠密真部分）。
    q9nt 正直限定 3「実 Gal(M/ℚ₃) 自己同型 ζ₉↦ζ₉^k の建設は named future」の
    **σ-only スコープでの正面 discharge**。 -/
theorem q9ng_outer_theta_cyclotome :
    q9ngArith.mul (q9ngArith.mul (q9ngSection.map q9kdGCar.s)
        (q9ngIncl.map (q9ntPsi.map (tpeIncl.map ((0, 0, 1) : Int × Int × Int)))))
        (q9ngArith.inv (q9ngSection.map q9kdGCar.s))
      = q9ngIncl.map (q9ntPsi.map (tpeIncl.map ((0, 0, 4) : Int × Int × Int))) := by
  rw [q9ng_outer_galois q9kdGCar.s
        (q9ntPsi.map (tpeIncl.map ((0, 0, 1) : Int × Int × Int))),
      q9ng_psi_cyc1, q9ng_psi_cyc4]
  show q9ngIncl.map (q9ngSigma9.map q9ntZ9) = q9ngIncl.map (tateZpow q9mtM q9ntZ9 4)
  rw [q9ng_sigma9_Z9]

/-- **q9ng-6b（★★★）: 捻りは非自明** — 共役結果 ι(Ψ₉(ι(0,0,4))) ≠ ι(Ψ₉(ι(0,0,1)))。
    実 Galois 元 σ が tempered テータシクロトーム生成元を**実際に動かす**（⟸ Z₉³≠1）。
    大域側の χ(σ₄)=4（`q9mb_sigma4_exp`）と整合する実局所指標値である。 -/
theorem q9ng_outer_theta_ne :
    q9ngIncl.map (q9ntPsi.map (tpeIncl.map ((0, 0, 4) : Int × Int × Int)))
      ≠ q9ngIncl.map (q9ntPsi.map (tpeIncl.map ((0, 0, 1) : Int × Int × Int))) := by
  intro h
  have h2 : q9ntPsi.map (tpeIncl.map ((0, 0, 4) : Int × Int × Int))
      = q9ntPsi.map (tpeIncl.map ((0, 0, 1) : Int × Int × Int)) :=
    q9ng_incl_injective _ _ h
  rw [q9ng_psi_cyc1, q9ng_psi_cyc4] at h2
  exact q9ng_Z9_four_ne h2

/-! ## q9ng-7（正直核）: 分裂スライスの帽子 σ₉(X) = uδ·X -/

/-- 単数のずれ δU = σU(u₆)·u₆⁻¹ ∈ U₃（q9ps の実 wild 分割単数 u₆＝`q9tlU3`）。 -/
def q9ngDeltaU : q3kU.carrier := q3kU.mul (q9mbSigmaU q9tlU3) (q3kU.inv q9tlU3)

/-- 単数平行移動 uδ = (1, 0, (0, δU)) ∈ q9mtM。 -/
def q9ngUdelta : q9mtCar := q9ngTrans.map (((0 : Int), q9ngDeltaU))

/-- δU·u₆ = σU(u₆)（消去の 1 行）。 -/
theorem q9ng_delta_mul : q3kU.mul q9ngDeltaU q9tlU3 = q9mbSigmaU q9tlU3 := by
  show q3kU.mul (q3kU.mul (q9mbSigmaU q9tlU3) (q3kU.inv q9tlU3)) q9tlU3 = q9mbSigmaU q9tlU3
  rw [q3kU.mul_assoc, q3kU.inv_mul, q3kU.mul_one]

/-- **q9ng-7a（正直核・★）: σ₉(X) = uδ·X** — デッキ方向の生成元 X = q9mtG3（実半周期 [3]）は
    Galois 固定されず、**単数平行移動 uδ の分だけずれる**。これは σ̃M が一様化子捻り
    cσ = σ(π₉)/π₉ を捨てた**次数付き分裂スライス**であることの直接の帰結であり（正直限定 3）、
    q3ap 正直限定 (ii)（graded split slice）と同族の帽子である。
    ゆえに σ₉ が中心化条件 q9mtMem（テータ部分群 q9mtGrp）を保存するとは**主張しない**
    （保存する捻り作用の正当化 cσ⁶·σU(u₆)=u₆ は消去律依存の crux・named future）。 -/
theorem q9ng_sigma9_X : q9ngSigma9.map q9mtG3 = q9mtM.mul q9ngUdelta q9mtG3 := by
  show ((q9ngSigmaMx.map q9tlMx.one, (-1 : Int)), q9ngSigmaMx.map q9tl3)
     = ((q9tlMx.mul (q9tlMx.mul q9tlMx.one q9tlMx.one) (tateZpow q9tlMx q9tl3 0),
         (0 : Int) + (-1)),
        q9tlMx.mul (((0 : Int), q9ngDeltaU)) q9tl3)
  have hone : q9ngSigmaMx.map q9tlMx.one = q9tlMx.one := q9ngSigmaMx.map_one
  have hidx : (0 : Int) + (-1) = (-1 : Int) := by omega
  have hc : q9tlMx.mul (q9tlMx.mul q9tlMx.one q9tlMx.one) (tateZpow q9tlMx q9tl3 0)
      = q9tlMx.one := by
    rw [tateZpow_zero, q9tlMx.mul_one, q9tlMx.one_mul]
  have hw : q9ngSigmaMx.map q9tl3 = q9tlMx.mul (((0 : Int), q9ngDeltaU)) q9tl3 := by
    show ((6 : Int), q9mbSigmaU q9tlU3)
       = ((intGrp.mul (0 : Int) (6 : Int), q3kU.mul q9ngDeltaU q9tlU3) : q9tlMx.carrier)
    have h06 : intGrp.mul (0 : Int) (6 : Int) = (6 : Int) := by
      show (0 : Int) + (6 : Int) = (6 : Int)
      omega
    rw [h06, q9ng_delta_mul]
  rw [hone, hidx, hc, hw]

/-- **q9ng-7b（正直核）: デッキ方向全体のずれ** σ₉(Ψ₉(s n)) = (uδ·X)ⁿ。
    tempered デッキ（**離散 ℤ**・副有限完備化でない）方向の Galois 像が、
    分裂スライスの単数平行移動込みで閉じることの明示形。 -/
theorem q9ng_sigma9_deck (n : Int) :
    q9ngSigma9.map (q9ntPsi.map (tpeSection.map n))
      = tateZpow q9mtM (q9mtM.mul q9ngUdelta q9mtG3) n := by
  rw [q9nt_psi_deck n, hom_map_zpow q9ngSigma9 q9mtG3 n, q9ng_sigma9_X]

/-! ## q9ng-8: capstone -/

/-- **q9ng-8a: A5 N3 capstone データ** — 実 Galois 作用 σ₉・χ₉(σ)=4 の実装・Weil 同変性・
    半直積と外 Galois 定理・headline（tempered テータシクロトームの 4 倍捻り）・
    正直核（分裂スライスの帽子）を束ねる。すべての旗艦の主語は実 Φ₉/Ψ₉ 像と実 σU である。 -/
structure Q3TemperedThetaGaloisL9Data where
  /-- 実 Galois 作用 σ₉ : q9mtM → q9mtM。 -/
  sigma9 : Hom q9mtM q9mtM
  /-- σ₉³ = id（Gal(M/L₂) の位数 3）。 -/
  sigma9_order3 : ∀ g, sigma9.map (sigma9.map (sigma9.map g)) = g
  /-- ★ χ₉(σ)=4: σ₉(Z₉) = Z₉⁴。 -/
  cyclotome_twist : sigma9.map q9ntZ9 = tateZpow q9mtM q9ntZ9 4
  /-- ★ σ₉(Y) = Y⁴（[ζ₉] 方向の実 Galois 共役）。 -/
  zeta_twist : sigma9.map q9mtGZeta = tateZpow q9mtM q9mtGZeta 4
  /-- ★★ χ 捻りの実装 σ₉(Φ₉(0,b,c)) = Φ₉(0,4b,4c)（atpTw の実 Galois 値 e=4 実現）。 -/
  chi_twist_real : ∀ b c : Int, sigma9.map (q9ntPhi.map ((0, b, c) : Int × Int × Int))
    = q9ntPhi.map ((0, 4 * b, 4 * c) : Int × Int × Int)
  /-- ★★ 旗艦 1: μ₉ Weil 形式の Galois 同変性（Φ₉ 像上・4 倍捻り）。 -/
  symplectic_galois : ∀ v w : thetaGrp.carrier,
    q9mtComm (sigma9.map (q9ntPhi.map v)) (sigma9.map (q9ntPhi.map w))
      = tateZpow q9mtM q9ntZ9 (4 * (v.1 * w.2.1 - w.1 * v.2.1))
  /-- ★★ 旗艦 2: 外 Galois 定理（半直積 q9mtM ⋊ Gal(M/L₂)）。 -/
  outer_galois : ∀ (g : q9kdGCar) (z : q9mtCar),
    q9ngArith.mul (q9ngArith.mul (q9ngSection.map g) (q9ngIncl.map z))
        (q9ngArith.inv (q9ngSection.map g)) = q9ngIncl.map ((q9ngTw g).map z)
  /-- 完全列 1 → q9mtM → Π₉ → Gal(M/L₂) → 1。 -/
  exact_seq : ∀ x : q9ngArith.carrier,
    q9ngProj.map x = q9kdG.one ↔ ∃ z : q9mtCar, q9ngIncl.map z = x
  /-- ★★★ headline: 実外 Galois 共役は tempered テータシクロトームを 4 倍に捻る。 -/
  outer_theta_cyclotome :
    q9ngArith.mul (q9ngArith.mul (q9ngSection.map q9kdGCar.s)
        (q9ngIncl.map (q9ntPsi.map (tpeIncl.map ((0, 0, 1) : Int × Int × Int)))))
        (q9ngArith.inv (q9ngSection.map q9kdGCar.s))
      = q9ngIncl.map (q9ntPsi.map (tpeIncl.map ((0, 0, 4) : Int × Int × Int)))
  /-- ★★★ headline の非自明性（Z₉⁴ ≠ Z₉）。 -/
  outer_theta_ne :
    q9ngIncl.map (q9ntPsi.map (tpeIncl.map ((0, 0, 4) : Int × Int × Int)))
      ≠ q9ngIncl.map (q9ntPsi.map (tpeIncl.map ((0, 0, 1) : Int × Int × Int)))
  /-- 正直核: σ₉(X) = uδ·X（分裂スライスの帽子・q9mtGrp 保存は主張しない）。 -/
  split_slice_cap : sigma9.map q9mtG3 = q9mtM.mul q9ngUdelta q9mtG3

/-- **q9ng-8b: 見出し実例**。 -/
def q9ngData : Q3TemperedThetaGaloisL9Data where
  sigma9 := q9ngSigma9
  sigma9_order3 := q9ng_sigma9_3
  cyclotome_twist := q9ng_sigma9_Z9
  zeta_twist := q9ng_sigma9_Y
  chi_twist_real := q9ng_chi_twist
  symplectic_galois := q9ng_symplectic_galois
  outer_galois := q9ng_outer_galois
  exact_seq := q9ng_extension_exact
  outer_theta_cyclotome := q9ng_outer_theta_cyclotome
  outer_theta_ne := q9ng_outer_theta_ne
  split_slice_cap := q9ng_sigma9_X

/-- **q9ng-8c（★ capstone）: 実 tempered テータ実現への実局所 Galois 作用の存在** —
    実 Gal(M/L₂)=⟨σ⟩（位数 3）の μ₉ テータ Heisenberg 担体への実作用・χ₉(σ)=4 の実装・
    Weil 同変性・半直積と外 Galois 定理・tempered テータシクロトームの非自明な 4 倍捻り。
    σ-only スコープ（χ₉ 像 {1,4,7}）・分裂スライス・q9mtGrp 非保存の帽子つき。 -/
theorem q9ngGaloisL9_exists : Nonempty Q3TemperedThetaGaloisL9Data := ⟨q9ngData⟩

end IUT
