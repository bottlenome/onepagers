-- Q3EtaleArithPi1 [実／(b) 本物の先行建設・柱A A4「実 π₁^ét」]
-- complete_pct 影響: A4 マイルストーン AP — 実算術 π₁^ét 完全列スライスを建設する。
--   両側とも実 profinite な半直積 Π^arith = π₁^geom ⋊ G を、幾何 π₁ = q9td 二方向 π₁ 対象
--   （geom = ℤ₃(1)=tmzLimit × ℤ₃=q3pePi1 3）と G = A3 実 profinite Gal(ℚ(ζ_{3^∞})/ℚ)=ctlProfinite
--   の A7b 実作用 tmzActHom で本物に構成し、完全列 1→π₁^geom→Π^arith→G→1（実 ι 単射・実 pr 全射・
--   exactness im ι = ker pr）・外 Galois 定理 s(σ)·ι(z)·s(σ)⁻¹ = ι(σ·z)・E_{3⁹}[9] の μ 方向作用の
--   χ 同変性（q9td μ 実現で実曲線上に可視化）を完全証明する。予測 s_A4 0.56→0.58（監査確定）。
--   w=14 ゆえ単独では表示 57 を動かさない（Σ_A 56.86→~57.1・表示 57 据え置き・表示 mover は主張しない）。
--
-- 正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
--  (i)   これは SGA1 の punctured/スキーム完全列では**ない**（スキーム・エタールサイト・punctured
--        曲線対象はリポジトリに皆無——punctured 側の非可換 π₁ は tempered=A5 の主語で q9nt が担当）。
--  (ii)  幾何 π₁ = ℤ₃(1)×ℤ₃ は T₃(E_q) の**次数付き（graded）分裂スライス**であり、本物の非分裂拡大
--        0→ℤ₃(1)→T₃E→ℤ₃→0（Kummer 類 q）ではない。格子方向への trivial 作用は「商への作用」として
--        のみ正確。level 27 以深の Kummer コサイクル σ(3^{1/3})/3^{1/3} は未構成（実 ℚ₃(ζ₂₇,3^{1/3})
--        の建設が前提の named future target）。「非分裂拡大を構成した」とは書かない。
--  (iii) G = Gal(ℚ(ζ_{3^∞})/ℚ)（ℚ 上円分切片）であって実局所 G_{ℚ₃} でも実 G_K（非可換副有限全体）
--        でもない（tmz (iii)・ctl 継承）。古典同型 Gal(ℚ₃(ζ_{3^∞})/ℚ₃) ≅ Gal(ℚ(ζ_{3^∞})/ℚ) は未形式化。
--  (iv)  Galois は曲線の点には作用しない（同変性は π₁ 作用・指標のレベル）。E_{3⁹}(M) 担体への実局所
--        Galois 自己同型作用は未構成（A3/A7 と調整の named future）。full ẑ×ẑ(1)・非中心性 witness
--        （σ₂ 整合族×ζ 生成元族）・Weil ペアリングスライスは後続。q9td/tmz/A3 の正直限定を全て継承する。
--
-- 全て選択公理不使用（新規 Classical.choice を導入しない・propext/Quot.sound のみ）。
-- 禁止タクティク不使用（omega は純 Int/Nat アトムのみ）。新規ファイル 1 個のみ（共有ファイル不更新・親統合）。
-- prefix `q3ap`。

/-
  IUT/Q3EtaleArithPi1.lean — A4（実 π₁^ét）マイルストーン AP: 実算術 π₁^ét 完全列
    1 → π₁^geom → Π^arith → G → 1・外 Galois 作用・E_{3⁹}[9] 上の χ 同変性

  分類: [実／(b) 本物の先行建設]。両監査（reaudit-A4-pi1-etale-tate §5・
    reaudit-q9td-twodir-a4 §4.2）が blocker として名指しした「G_{ℚ₃} 外作用ゼロ」を、
    A7b tmzActHom（実 profinite Gal の ℤ₃(1) への実作用）と A3 cliChar（実指標）を消費して
    discharge する。設計 = audit/pillar-A4-pi1etale-deepen-detail-2026-07-20.md §3 の梯子 AP-0〜AP-3+AP-5。

  内容:
   * AP-0  幾何スライス q3apGeom = tmzLimit × q3pePi1 3・Galois 捻り q3apTw σ（(tmzActHom σ)×id）・
           tw(1)=id・tw(στ)=tw σ∘tw τ（tmzGModule.act_one/act_mul の抽象系）。
   * AP-1  半直積 Π^arith = q3apArith = q3apGeom ⋊ ctlProfinite（積・群公理・atp 写経）。
   * AP-2  算術完全列: q3apIncl 単射・q3apProj 全射・exactness（ker pr = im ι）・分裂切断 q3apSection・
           共役公式 q3ap_conj_incl・★外 Galois 定理 q3ap_outer_galois。
   * AP-3  E_{3⁹}[9] μ 方向 χ 同変性: q3ap_mu_equivariant（指標指数が χ₉(σ) 倍）・スカラー形
           q3ap_mu_equivariant_scalar（ℤ/9 の npow）・実曲線実現 q3ap_mu_realize_galois（q9td μ 実現）。
   * AP-5  capstone Q3EtaleArithPi1Data / q3ap_data / q3ap_exists。
-/
import IUT.Q3Etale9TwoDir
import IUT.CyclotomicLimitIso

namespace IUT

/-! ## AP-0: 幾何スライス q3apGeom と Galois 捻り q3apTw -/

/-- **AP-0a: 幾何 π₁ スライス** π₁^geom = ℤ₃(1) × ℤ₃ = tmzLimit × q3pePi1 3。
    μ 方向 ℤ₃(1)=tmzLimit（実 μ 塔逆極限）と格子方向 ℤ₃=q3pePi1 3（実 Tate 逆極限）の直積で、
    q9td 二方向 π₁ 対象そのもの（次数付き分裂スライス・正直限定 (ii)）。 -/
def q3apGeom : Grp := prodGrp tmzLimit (q3pePi1 3)

/-- **AP-0b: Galois 捻り q3apTw** — σ ∈ G の π₁^geom への作用を与える群自己準同型
    (tmzActHom σ) × id: μ 方向に実 Gal 作用 tmzActHom・格子方向は固定（次数付きスライスの
    「商への作用」・正直限定 (ii)）。map_mul は tmzActHom の map_mul（成分ごと）。 -/
def q3apTw (σ : ctlProfinite.carrier) : Hom q3apGeom q3apGeom where
  map := fun z => ((tmzActHom σ).map z.1, z.2)
  map_mul := fun z w => by
    show ((tmzActHom σ).map (tmzLimit.mul z.1 w.1), (q3pePi1 3).mul z.2 w.2)
       = (tmzLimit.mul ((tmzActHom σ).map z.1) ((tmzActHom σ).map w.1), (q3pePi1 3).mul z.2 w.2)
    rw [(tmzActHom σ).map_mul z.1 w.1]

/-- **AP-0c: 単位則** tw(1) = id（tmzGModule.act_one：実 Gal の単位元は ℤ₃(1) に自明作用）。 -/
theorem q3ap_tw_one (z : q3apGeom.carrier) : (q3apTw ctlProfinite.one).map z = z :=
  Prod.ext (tmzGModule.act_one z.1) rfl

/-- **AP-0d: 合成則** tw(σσ') = tw σ ∘ tw σ'（tmzGModule.act_mul：実 Gal 作用の合成則）。 -/
theorem q3ap_tw_mul (σ σ' : ctlProfinite.carrier) (z : q3apGeom.carrier) :
    (q3apTw (ctlProfinite.mul σ σ')).map z = (q3apTw σ).map ((q3apTw σ').map z) :=
  Prod.ext (tmzGModule.act_mul σ σ' z.1) rfl

/-- **AP-0e: 任意群で 1⁻¹ = 1**（外 Galois 定理の共役計算用）。 -/
theorem q3ap_inv_one (G : Grp) : G.inv G.one = G.one := by
  have h := G.inv_mul G.one
  rw [G.mul_one] at h
  exact h

/-! ## AP-1: 半直積 Π^arith = q3apArith = q3apGeom ⋊ ctlProfinite -/

/-- **AP-1（★核）: 実算術基本群 Π^arith = q3apArith = π₁^geom ⋊ G**。
    台 q3apGeom.carrier × ctlProfinite.carrier、積 (z,σ)(z',σ') = (z ·_geom (tw σ)(z'), σ·σ')。
    両側とも実 profinite（geom = tmzLimit×q3pePi1 3・G = A3 ctlProfinite）——[IUTchI] §2 の
    算術基本群拡大 Π_X → G_K の形の実インスタンス。群公理は q3apTw の準同型性（AP-0b）・
    作用性（AP-0c/0d）から抽象的に証明（atp イディオムの写経・座標総当たりでない）。 -/
def q3apArith : Grp where
  carrier := q3apGeom.carrier × ctlProfinite.carrier
  mul := fun x y => (q3apGeom.mul x.1 ((q3apTw x.2).map y.1), ctlProfinite.mul x.2 y.2)
  one := (q3apGeom.one, ctlProfinite.one)
  inv := fun x =>
    ((q3apTw (ctlProfinite.inv x.2)).map (q3apGeom.inv x.1), ctlProfinite.inv x.2)
  mul_assoc := by
    intro x y z
    obtain ⟨a, σ⟩ := x
    obtain ⟨b, σ'⟩ := y
    obtain ⟨c, σ''⟩ := z
    show (q3apGeom.mul (q3apGeom.mul a ((q3apTw σ).map b))
            ((q3apTw (ctlProfinite.mul σ σ')).map c),
          ctlProfinite.mul (ctlProfinite.mul σ σ') σ'')
       = (q3apGeom.mul a ((q3apTw σ).map (q3apGeom.mul b ((q3apTw σ').map c))),
          ctlProfinite.mul σ (ctlProfinite.mul σ' σ''))
    rw [(q3apTw σ).map_mul b ((q3apTw σ').map c),
        q3ap_tw_mul σ σ' c,
        q3apGeom.mul_assoc a ((q3apTw σ).map b) ((q3apTw σ).map ((q3apTw σ').map c)),
        ctlProfinite.mul_assoc σ σ' σ'']
  one_mul := by
    intro x
    obtain ⟨a, σ⟩ := x
    show (q3apGeom.mul q3apGeom.one ((q3apTw ctlProfinite.one).map a),
          ctlProfinite.mul ctlProfinite.one σ) = (a, σ)
    rw [q3ap_tw_one a, q3apGeom.one_mul a, ctlProfinite.one_mul σ]
  inv_mul := by
    intro x
    obtain ⟨a, σ⟩ := x
    show (q3apGeom.mul ((q3apTw (ctlProfinite.inv σ)).map (q3apGeom.inv a))
            ((q3apTw (ctlProfinite.inv σ)).map a),
          ctlProfinite.mul (ctlProfinite.inv σ) σ)
       = (q3apGeom.one, ctlProfinite.one)
    rw [← (q3apTw (ctlProfinite.inv σ)).map_mul (q3apGeom.inv a) a,
        q3apGeom.inv_mul a, (q3apTw (ctlProfinite.inv σ)).map_one,
        ctlProfinite.inv_mul σ]

/-- 積の成分表示（definitional）。 -/
theorem q3ap_mul_expand (a b : q3apGeom.carrier) (σ σ' : ctlProfinite.carrier) :
    q3apArith.mul ((a, σ) : q3apArith.carrier) (b, σ')
      = (q3apGeom.mul a ((q3apTw σ).map b), ctlProfinite.mul σ σ') := rfl

/-- 逆元の成分表示（definitional）。 -/
theorem q3ap_inv_expand (a : q3apGeom.carrier) (σ : ctlProfinite.carrier) :
    q3apArith.inv ((a, σ) : q3apArith.carrier)
      = ((q3apTw (ctlProfinite.inv σ)).map (q3apGeom.inv a), ctlProfinite.inv σ) := rfl

/-! ## AP-2: 算術完全列 1 → π₁^geom → Π^arith → G → 1 -/

/-- **AP-2a: 核埋め込み ι : π₁^geom ↪ Π^arith**（z ↦ (z, 1_G)）— 幾何 π₁ を算術基本群の核と
    して埋め込む実群準同型。 -/
def q3apIncl : Hom q3apGeom q3apArith where
  map := fun z => (z, ctlProfinite.one)
  map_mul := by
    intro z w
    show ((q3apGeom.mul z w, ctlProfinite.one) : q3apArith.carrier)
       = (q3apGeom.mul z ((q3apTw ctlProfinite.one).map w),
          ctlProfinite.mul ctlProfinite.one ctlProfinite.one)
    rw [q3ap_tw_one w, ctlProfinite.one_mul ctlProfinite.one]

/-- **AP-2b: 射影 pr : Π^arith ↠ G**（(z, σ) ↦ σ）— 実 profinite Gal への全射準同型。 -/
def q3apProj : Hom q3apArith ctlProfinite where
  map := fun x => x.2
  map_mul := fun _ _ => rfl

/-- **AP-2c: 分裂切断 s : G → Π^arith**（σ ↦ (1_geom, σ)）— 算術拡大の分裂（pr∘s = id）。 -/
def q3apSection : Hom ctlProfinite q3apArith where
  map := fun σ => (q3apGeom.one, σ)
  map_mul := by
    intro σ σ'
    show ((q3apGeom.one, ctlProfinite.mul σ σ') : q3apArith.carrier)
       = (q3apGeom.mul q3apGeom.one ((q3apTw σ).map q3apGeom.one), ctlProfinite.mul σ σ')
    rw [(q3apTw σ).map_one, q3apGeom.one_mul]

/-- **AP-2d: ι は単射**。 -/
theorem q3ap_incl_injective : q3apIncl.Injective :=
  fun _ _ h => congrArg Prod.fst h

/-- **AP-2e: pr は全射**（切断 s の像で実現）。 -/
theorem q3ap_proj_surjective : ∀ g : ctlProfinite.carrier, ∃ x, q3apProj.map x = g :=
  fun g => ⟨q3apSection.map g, rfl⟩

/-- **AP-2f: 切断は分裂** pr ∘ s = id。 -/
theorem q3ap_section_splits (σ : ctlProfinite.carrier) :
    q3apProj.map (q3apSection.map σ) = σ := rfl

/-- **AP-2g（★）: 算術拡大の完全性** — ker(pr) = im(ι)。幾何 π₁^geom がちょうど算術射影の核
    である（[IUTchI] §2 の完全列 1 → π₁^geom → Π^arith → G → 1 の実現）。 -/
theorem q3ap_extension_exact (x : q3apArith.carrier) :
    q3apProj.map x = ctlProfinite.one ↔ ∃ z : q3apGeom.carrier, q3apIncl.map z = x := by
  obtain ⟨z, σ⟩ := x
  constructor
  · intro h
    have hσ : σ = ctlProfinite.one := h
    subst hσ
    exact ⟨z, rfl⟩
  · intro h
    obtain ⟨w, hw⟩ := h
    show σ = ctlProfinite.one
    exact (congrArg Prod.snd hw).symm

/-- **AP-2h: 共役の明示公式** — g = (g₀, σ) による ι(z) の共役は
    ι(g₀ · (tw σ)(z) · g₀⁻¹)。算術元の共役 = Galois 捻り自己同型 ∘ 幾何の内部自己同型
    （外 Galois 表現 G → Out(π₁^geom) の実内容）。 -/
theorem q3ap_conj_incl (g₀ : q3apGeom.carrier) (σ : ctlProfinite.carrier) (z : q3apGeom.carrier) :
    q3apArith.mul (q3apArith.mul ((g₀, σ) : q3apArith.carrier) (q3apIncl.map z))
        (q3apArith.inv (g₀, σ))
      = q3apIncl.map (q3apGeom.mul (q3apGeom.mul g₀ ((q3apTw σ).map z)) (q3apGeom.inv g₀)) := by
  have h1 : q3apArith.mul ((g₀, σ) : q3apArith.carrier) (q3apIncl.map z)
      = (q3apGeom.mul g₀ ((q3apTw σ).map z), σ) := by
    show (q3apGeom.mul g₀ ((q3apTw σ).map z), ctlProfinite.mul σ ctlProfinite.one)
       = (q3apGeom.mul g₀ ((q3apTw σ).map z), σ)
    rw [ctlProfinite.mul_one σ]
  rw [h1]
  show (q3apGeom.mul (q3apGeom.mul g₀ ((q3apTw σ).map z))
          ((q3apTw σ).map ((q3apTw (ctlProfinite.inv σ)).map (q3apGeom.inv g₀))),
        ctlProfinite.mul σ (ctlProfinite.inv σ))
     = q3apIncl.map (q3apGeom.mul (q3apGeom.mul g₀ ((q3apTw σ).map z)) (q3apGeom.inv g₀))
  rw [← q3ap_tw_mul σ (ctlProfinite.inv σ) (q3apGeom.inv g₀),
      Grp.mul_inv ctlProfinite σ, q3ap_tw_one (q3apGeom.inv g₀)]
  rfl

/-- **AP-2i（★）: ι(π₁^geom) は正規部分群**（明示 witness つき）— 完全列の正規性の実証明。 -/
theorem q3ap_geometric_normal (g : q3apArith.carrier) (z : q3apGeom.carrier) :
    ∃ w : q3apGeom.carrier,
      q3apArith.mul (q3apArith.mul g (q3apIncl.map z)) (q3apArith.inv g) = q3apIncl.map w := by
  obtain ⟨g₀, σ⟩ := g
  exact ⟨q3apGeom.mul (q3apGeom.mul g₀ ((q3apTw σ).map z)) (q3apGeom.inv g₀),
    q3ap_conj_incl g₀ σ z⟩

/-- **AP-2j（★★ アナベルの心臓）: 外 Galois 定理** — 算術切断の共役は Galois 捻り自己同型:
    s(σ)·ι(z)·s(σ)⁻¹ = ι((tw σ)(z))。算術商 G = Gal(ℚ(ζ_{3^∞})/ℚ) が幾何 π₁^geom に
    **実 tmzActHom 作用**（μ 方向 ℤ₃(1) への実 profinite Galois 作用）で外から作用する。
    算術基本群の外作用が実 Galois 作用であること——A4 の named blocker「G 外作用ゼロ」の discharge。 -/
theorem q3ap_outer_galois (σ : ctlProfinite.carrier) (z : q3apGeom.carrier) :
    q3apArith.mul (q3apArith.mul (q3apSection.map σ) (q3apIncl.map z))
        (q3apArith.inv (q3apSection.map σ))
      = q3apIncl.map ((q3apTw σ).map z) := by
  show q3apArith.mul (q3apArith.mul ((q3apGeom.one, σ) : q3apArith.carrier) (q3apIncl.map z))
      (q3apArith.inv (q3apGeom.one, σ))
    = q3apIncl.map ((q3apTw σ).map z)
  rw [q3ap_conj_incl q3apGeom.one σ z, q3apGeom.one_mul ((q3apTw σ).map z),
      q3ap_inv_one q3apGeom, q3apGeom.mul_one ((q3apTw σ).map z)]

/-! ## AP-3: E_{3⁹}[9] μ 方向作用の χ 同変性（q9td μ 実現で実曲線上に可視化） -/

/-- **AP-3a: mod 9 の剰余可除性**（Quot.sound 用の純 Nat/Int 補題）。 -/
theorem q3ap_ar_mod9 (n : Nat) : ((9 : Nat) : Int) ∣ (((n % 9 : Nat) : Int) - ((n : Nat) : Int)) := by
  omega

/-- **AP-3b: ℤ/9 の自然数冪 = 剰余類のスカラー倍**（tateNpow (mk a) k = mk (k·a)、
    加法群 ℤ/9 の npow を整数座標に降ろす・帰納 1 本・choice-free）。 -/
theorem q3ap_zmod9_npow (a : Nat) (k : Nat) :
    tateNpow (zmod 9) (Quot.mk (modCong 9).rel ((a : Nat) : Int)) k
      = Quot.mk (modCong 9).rel ((k * a : Nat) : Int) := by
  induction k with
  | zero =>
    show Quot.mk (modCong 9).rel intGrp.one = Quot.mk (modCong 9).rel ((0 * a : Nat) : Int)
    apply Quot.sound
    show ((9 : Nat) : Int) ∣ ((0 : Int) - ((0 * a : Nat) : Int))
    omega
  | succ j ih =>
    show (zmod 9).mul (tateNpow (zmod 9) (Quot.mk (modCong 9).rel ((a : Nat) : Int)) j)
           (Quot.mk (modCong 9).rel ((a : Nat) : Int))
       = Quot.mk (modCong 9).rel (((j + 1) * a : Nat) : Int)
    rw [ih]
    show Quot.mk (modCong 9).rel (intGrp.mul ((j * a : Nat) : Int) ((a : Nat) : Int))
       = Quot.mk (modCong 9).rel (((j + 1) * a : Nat) : Int)
    have hstep : intGrp.mul ((j * a : Nat) : Int) ((a : Nat) : Int) = (((j + 1) * a : Nat) : Int) := by
      show ((j * a : Nat) : Int) + ((a : Nat) : Int) = (((j + 1) * a : Nat) : Int)
      rw [Nat.succ_mul j a]
      omega
    rw [hstep]

/-- χ₉(σ) := ((cliChar 1).map (σ.val 1)).val ∈ ℤ の実円分指標値（A3 cliChar のレベル 1 段・
    Gal(ℚ(ζ₉)/ℚ) → (ℤ/9)^× の実指標）。 -/
def q3apChi9 (σ : ctlProfinite.carrier) : Nat := ((cliChar 1).map (σ.val 1)).val

/-- **AP-3c（★ χ 同変性の核）: μ 指標は Galois で χ 捻れる** —
    χ_μ((tmzActHom σ)(s)) = [χ₉(σ)·χ_μ(s)] ∈ ℤ/9。実 Gal 作用 tmzActHom（A7b）で捻った
    μ 方向 π₁ 元の μ 指標は、元の指標指数を χ₉(σ) 倍したもの（tmz_act_char の n=1 適用＋
    tmz_find_pow ℓ=2＋Quot.sound）。E_{3⁹}[9] の μ 座標作用が Galois で χ 捻れることの実内容。 -/
theorem q3ap_mu_equivariant (σ : ctlProfinite.carrier) (s : tmzLimit.carrier) :
    q9tdMuChar.map ((tmzActHom σ).map s)
      = Quot.mk (modCong 9).rel
          ((q3apChi9 σ * ctmFind 2 q9td_h2 (s.val 1).val : Nat) : Int) := by
  -- Galois で捻った元の レベル1 成分の val = ζ₉^{χ·f}（tmz_act_char ＋ cmr_pow_zeta）
  have hval : (((tmzActHom σ).map s).val 1).val
      = ctmPow 2 q9td_h2 (q3apChi9 σ * ctmFind 2 q9td_h2 (s.val 1).val) := by
    rw [tmz_act_char σ s 1]
    exact cmr_pow_zeta 2 q9td_h2 (q3apChi9 σ * ctmFind 2 q9td_h2 (s.val 1).val)
  -- その離散対数 = (χ·f) % 9（tmz_find_pow ℓ=2）
  have hfind : ctmFind 2 q9td_h2 (((tmzActHom σ).map s).val 1).val
      = (q3apChi9 σ * ctmFind 2 q9td_h2 (s.val 1).val) % 9 := by
    rw [hval]
    exact tmz_find_pow 2 q9td_h2 (q3apChi9 σ * ctmFind 2 q9td_h2 (s.val 1).val)
  show Quot.mk (modCong 9).rel
        ((ctmFind 2 q9td_h2 (((tmzActHom σ).map s).val 1).val : Nat) : Int)
     = Quot.mk (modCong 9).rel ((q3apChi9 σ * ctmFind 2 q9td_h2 (s.val 1).val : Nat) : Int)
  rw [hfind]
  apply Quot.sound
  exact q3ap_ar_mod9 (q3apChi9 σ * ctmFind 2 q9td_h2 (s.val 1).val)

/-- **AP-3d（★ スカラー形）: μ 指標の Galois 捻りは χ₉(σ) 冪** —
    χ_μ((tmzActHom σ)(s)) = (χ_μ(s))^{χ₉(σ)}（ℤ/9 の npow）。AP-3c を ℤ/9 の
    加法群スカラー倍（q3ap_zmod9_npow）で読み替えたもの。 -/
theorem q3ap_mu_equivariant_scalar (σ : ctlProfinite.carrier) (s : tmzLimit.carrier) :
    q9tdMuChar.map ((tmzActHom σ).map s)
      = tateNpow (zmod 9) (q9tdMuChar.map s) (q3apChi9 σ) := by
  have hms : q9tdMuChar.map s
      = Quot.mk (modCong 9).rel ((ctmFind 2 q9td_h2 (s.val 1).val : Nat) : Int) := rfl
  rw [q3ap_mu_equivariant σ s, hms,
      q3ap_zmod9_npow (ctmFind 2 q9td_h2 (s.val 1).val) (q3apChi9 σ)]

/-- **AP-3e（★★ 実曲線上の可視化）: Galois 捻り π₁ 元の実曲線 E_{3⁹} 上の μ 平行移動** —
    φ((tmzActHom σ)(s) が誘導する μ 作用の像) = φ(p)·[ζ₉]^{χ_μ((tmzActHom σ)(s))}。
    q9td_mu_realize を Galois 捻り元に適用——実 Gal 作用で捻った μ 方向 π₁ 元が実曲線 E_{3⁹} に
    作用し、その [ζ₉] 平行移動が AP-3c/3d により χ₉(σ) 捻れることを可視化する（μ 方向作用の
    χ 同変性の実曲線着地・正直限定 (iv)：Galois は曲線の点には作用しない）。 -/
theorem q3ap_mu_realize_galois (σ : ctlProfinite.carrier) (s : tmzLimit.carrier) (p : q9tdE9) :
    q9tdPhi (q9tdMuAct.act ((tmzActHom σ).map s) p)
      = q9tlCurve.mul (q9tdPhi p)
          (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 (q9tdMuChar.map ((tmzActHom σ).map s))) :=
  q9td_mu_realize ((tmzActHom σ).map s) p

/-! ## AP-5: capstone -/

/-- **AP-5a: 実算術 π₁^ét 完全列スライスデータ** — 半直積 Π^arith・完全列（ι 単射・pr 全射・
    exactness・正規性・分裂切断）・外 Galois 定理・E_{3⁹}[9] μ 方向 χ 同変性・実曲線実現を束ねる。 -/
structure Q3EtaleArithPi1Data where
  /-- ι は単射（幾何 π₁ の核埋め込み）。 -/
  incl_inj : q3apIncl.Injective
  /-- pr は全射（実 profinite Gal への射影）。 -/
  proj_surj : ∀ g : ctlProfinite.carrier, ∃ x, q3apProj.map x = g
  /-- 分裂切断 pr∘s = id。 -/
  section_splits : ∀ σ : ctlProfinite.carrier, q3apProj.map (q3apSection.map σ) = σ
  /-- 完全性 ker(pr) = im(ι)。 -/
  exact_seq : ∀ x : q3apArith.carrier,
    q3apProj.map x = ctlProfinite.one ↔ ∃ z : q3apGeom.carrier, q3apIncl.map z = x
  /-- 幾何部の正規性。 -/
  geom_normal : ∀ (g : q3apArith.carrier) (z : q3apGeom.carrier),
    ∃ w : q3apGeom.carrier,
      q3apArith.mul (q3apArith.mul g (q3apIncl.map z)) (q3apArith.inv g) = q3apIncl.map w
  /-- ★外 Galois 定理 s(σ)·ι(z)·s(σ)⁻¹ = ι((tw σ)z)（実 tmzActHom 作用）。 -/
  outer_galois : ∀ (σ : ctlProfinite.carrier) (z : q3apGeom.carrier),
    q3apArith.mul (q3apArith.mul (q3apSection.map σ) (q3apIncl.map z))
        (q3apArith.inv (q3apSection.map σ))
      = q3apIncl.map ((q3apTw σ).map z)
  /-- ★E_{3⁹}[9] μ 方向作用の χ 同変性（指標指数が χ₉(σ) 倍）。 -/
  mu_equivariant : ∀ (σ : ctlProfinite.carrier) (s : tmzLimit.carrier),
    q9tdMuChar.map ((tmzActHom σ).map s)
      = Quot.mk (modCong 9).rel ((q3apChi9 σ * ctmFind 2 q9td_h2 (s.val 1).val : Nat) : Int)
  /-- ★Galois 捻り π₁ 元の実曲線 E_{3⁹} μ 平行移動としての実現。 -/
  mu_realize_galois : ∀ (σ : ctlProfinite.carrier) (s : tmzLimit.carrier) (p : q9tdE9),
    q9tdPhi (q9tdMuAct.act ((tmzActHom σ).map s) p)
      = q9tlCurve.mul (q9tdPhi p)
          (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 (q9tdMuChar.map ((tmzActHom σ).map s)))

/-- **AP-5b: 見出し実例** — 実算術 π₁^ét 完全列スライス（半直積＋完全列＋外 Galois＋χ 同変性）。 -/
def q3ap_data : Q3EtaleArithPi1Data where
  incl_inj := q3ap_incl_injective
  proj_surj := q3ap_proj_surjective
  section_splits := q3ap_section_splits
  exact_seq := q3ap_extension_exact
  geom_normal := q3ap_geometric_normal
  outer_galois := q3ap_outer_galois
  mu_equivariant := q3ap_mu_equivariant
  mu_realize_galois := q3ap_mu_realize_galois

/-- **AP-5c: 存在** — 実算術 π₁^ét 完全列スライス。 -/
theorem q3ap_exists : Nonempty Q3EtaleArithPi1Data := ⟨q3ap_data⟩

end IUT
