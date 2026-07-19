/-
  IUT/Q3TemperedPi1Deepen.lean — A5d（柱A A5: 実 tempered π₁ → 実 π₁^ét 比較・
    tempered ⊊ étale の忠実 embedding と「有限段稠密・全体非全射」）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**。A5b `Q3TemperedPi1.lean` の実 pro-3
     tempered 群 π₁^{temp,(3)}(E_q) = ℤ₃(1) × ℤ（tmzLimit × intGrp）は、これまで
     **π₁^ét（副有限完備化）への比較を一切持たなかった**——A5b の主対象は tempered 群
     単体であり、「なぜ étale では足りず tempered が要るか」という IUT の核心（Mochizuki
     temperoid 理論の出発点）が Lean 上の**関係射としては未構成**だった。本モジュールは
     M27/M374F の実 ℤ_p = Zp 3（= ttwInverseLimit 3・実逆極限 lim ℤ/3^n）と実完備化
     toZp 3（= ttwDiscreteComplete 3・M27 の実対角埋め込み）を**消費**して、実比較射
     q3tpEtComp : π₁^{temp,(3)} → π₁^{ét,(3)} = ℤ₃(1) × ℤ₃ を本物に建て、
       (1) 忠実性（単射・q3tpEtComp_injective）、
       (2) 各有限段 ℤ/3^n での全射性（q3tpEt_finite_level_surjective・「稠密」の代数的影）、
       (3) **全体 ℤ₃ への非全射性（q3tpEtComp_not_surjective）**——離散 ℤ ⊊ ℤ₃ の
           明示 witness（幾何級数元 ω_n = 1+3+…+3^{n-1}・値 −1/2 ∉ ℤ）で完全証明
     を実施する。(1)+(2)+(3) が合わさって「tempered 群は自身の副有限完備化の**真の稠密
     部分群**」＝**tempered π₁ は étale π₁ より真に細かい**という IUT の質的核心を、実主語
     （tmzLimit・intGrp・実 Zp 3・実 toZp 3）の上で toy 代理なしに定理化する。

  complete_pct 影響: **A5 0.2→（独立監査確定が条件・見込み 0.22）**。realizes A5b が
  持たなかった「実 tempered ↔ 実 π₁^ét 比較」。真水（新規主張）:
  (i)   実比較射 q3tpEtComp: π₁^{temp,(3)} → ℤ₃(1) × ℤ₃（μ 方向恒等・離散方向 toZp）・
        群準同型、
  (ii)  忠実性 q3tpEtComp_injective（toZp_injective + 恒等の積・tempered が完備化で
        情報を失わない）、
  (iii) 実完備化との両立 q3tpEtComp_via_ttwComplete（M374F ttwDiscreteComplete と rfl 一致）・
        離散射影両立 q3tpEtComp_disc_completion（= toZp ∘ q3tpProj）、
  (iv)  各有限段全射 q3tpEt_finite_level_surjective（∀ n, ℤ/3^n を尽くす＝稠密の代数的影）、
  (v)   **旗艦**: 全体非全射 q3tpEtComp_not_surjective（離散 ℤ ⊊ ℤ₃）——幾何級数
        witness q3tpEtWitness（整合族 ω_n=(3^n−1)/2）が toZp 3 の像に**属さない**
        （q3tp_disc_not_surjective・2a+1=0 の整数不存在 = 実 3 進分離性 int_pow_separated
        の消費）ことの完全証明。tempered の質的優位の実 discharge、
  (vi)  束ね Q3TemperedEtComparisonData / q3tpecData / q3tpec_exists。

  正直な限定（§4 規約・消去/弱化しない・A5b/A4/A5c の既存限定を全て継承の上に追記のみ）:
  (1) **依然 pro-3**（π₁^ét の離散方向は ℤ₃ = pro-3 完備化のみ・full ẑ ではない・
      A5b 限定(1) 継承）。μ 方向は tmzLimit = ℤ₃(1)（A5b/A7 計上済）をそのまま担ぐ。
  (2) **compact E_q の可換 tempered のみ**——punctured 曲線の非可換 θ 拡大（Heisenberg・
      tpeGroup 実化）は範囲外（A5b 限定(2) 継承）。比較は可換な格子/円分方向の embedding。
  (3) **「稠密」は代数的影のみ**——位相・p 進位相を本ファイルは一切使わない。稠密性は
      「各有限商 ℤ/3^n で全射」という代数的言明（q3tpEt_finite_level_surjective）で
      正直に述べ、**位相的稠密性（閉包＝全体）は主張しない**（Zp の位相は M15/M25 に
      あるが本ファイルでは接続しない）。非全射は逆に「全体 ℤ₃ には像が届かない」の
      集合論的言明。
  (4) π₁^ét 側 q3tpEtGroup = ℤ₃(1) × ℤ₃ は tempered 群の**pro-3 副有限完備化の模型**
      （直積）——一般の π₁^ét（非分裂・G_{ℚ₃} 外作用込み）ではない。Weil ペアリング・
      G_{ℚ₃} 外作用・anabelian 逆再構成はゼロ（A4/A5c の恒久限定 (3)(4)(5) 継承）。
  (5) 担体は群提示（A2/A8 恒久限定の継承）。位相・スキーム・エタールサイト皆無。
  (6) 既存 A5b の tempered データ・M27/M374F の完備化機構・M364F 仮説機構は
      消さず併設する（§2(a)(b) の規約）。本ファイルは A5b の上に**比較層**を追加する。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3TemperedPi1
import IUT.TemperedTower
import IUT.LocalCFT
import IUT.Profinite

namespace IUT

/-! ## q3tpec-0: 幾何級数元 ω_n = 1 + 3 + … + 3^{n-1} = (3^n − 1)/2（実 ℤ₃∖ℤ の witness の核） -/

/-- **q3tpec-0a: 幾何級数の部分和** ω_n := 1 + 3 + 9 + … + 3^{n-1}（ω_0 = 0）。
    整合族 (ω_n mod 3^n) が toZp 3 の像外の実 3 進整数（値 −1/2 ∉ ℤ）を与える。 -/
def q3tpGeom : Nat → Int
  | 0 => 0
  | (n + 1) => q3tpGeom n + ((3 ^ n : Nat) : Int)

/-- 3^{n+1} の Int キャストの漸化式: ((3^{n+1}) : Int) = 3 · ((3^n) : Int)。 -/
theorem q3tpec_cast3 (n : Nat) :
    ((3 ^ (n + 1) : Nat) : Int) = 3 * ((3 ^ n : Nat) : Int) := by
  rw [Nat.pow_succ, Int.natCast_mul]
  have h3 : ((3 : Nat) : Int) = 3 := rfl
  rw [h3, Int.mul_comm]

/-- **q3tpec-0b: 幾何級数の閉形式** 2·ω_n + 1 = 3^n（n についての帰納）。
    値 ω = −1/2（2ω+1 = 0）を「有限段の合同」として担う核恒等式。 -/
theorem q3tpec_geom_two : ∀ n : Nat, 2 * q3tpGeom n + 1 = ((3 ^ n : Nat) : Int) := by
  intro n
  induction n with
  | zero =>
    show 2 * q3tpGeom 0 + 1 = ((3 ^ 0 : Nat) : Int)
    show (2 * 0 + 1 : Int) = ((1 : Nat) : Int)
    rfl
  | succ k ih =>
    show 2 * (q3tpGeom k + ((3 ^ k : Nat) : Int)) + 1 = ((3 ^ (k + 1) : Nat) : Int)
    rw [q3tpec_cast3 k]
    omega

/-- **q3tpec-0c: 幾何級数の整合性** i ≤ j → 3^i ∣ (ω_j − ω_i)。
    整合族 (ω_n) が逆極限 Zp 3 の要素をなすことの核（各段の推移射で両立）。 -/
theorem q3tpec_geom_coh : ∀ j i : Nat, i ≤ j →
    ((3 ^ i : Nat) : Int) ∣ (q3tpGeom j - q3tpGeom i) := by
  intro j
  induction j with
  | zero =>
    intro i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    rw [hi0]
    exact ⟨0, by rw [Int.sub_self, Int.mul_zero]⟩
  | succ k ih =>
    intro i hi
    have hcase : i = k + 1 ∨ i ≤ k := by omega
    cases hcase with
    | inl he =>
      rw [he]
      exact ⟨0, by rw [Int.sub_self, Int.mul_zero]⟩
    | inr hle =>
      have hstep : q3tpGeom (k + 1) - q3tpGeom i
          = (q3tpGeom k - q3tpGeom i) + ((3 ^ k : Nat) : Int) := by
        show (q3tpGeom k + ((3 ^ k : Nat) : Int)) - q3tpGeom i
            = (q3tpGeom k - q3tpGeom i) + ((3 ^ k : Nat) : Int)
        omega
      rw [hstep]
      have hpow : ((3 ^ i : Nat) : Int) ∣ ((3 ^ k : Nat) : Int) :=
        Int.ofNat_dvd.mpr (pow_dvd_mono 3 hle)
      exact Int.dvd_add (ih i hle) hpow

/-! ## q3tpec-1: π₁^ét 側の実対象（ℤ₃(1) × ℤ₃ = pro-3 副有限完備化模型） -/

/-- **q3tpec-1（★）: 実 pro-3 étale 基本群模型** π₁^{ét,(3)}(E_q) = ℤ₃(1) × ℤ₃。
    μ 方向は実 ℤ₃(1) = tmzLimit（A7b・A5b と共有）、離散方向は実 ℤ₃ = Zp 3
    （= ttwInverseLimit 3・M27/M374F の実逆極限 lim ℤ/3^n）。A5b tempered 群の
    離散 ℤ を pro-3 完備化 ℤ₃ に置換した副有限側。 -/
def q3tpEtGroup : Grp := prodGrp tmzLimit (Zp 3)

/-- 離散方向は M374F 実逆極限 ttwInverseLimit 3（= Zp 3）である（実対象の同定）。 -/
theorem q3tpEt_disc_is_ttwLimit : q3tpEtGroup = prodGrp tmzLimit (ttwInverseLimit 3) := rfl

/-! ## q3tpec-2: 実比較射 π₁^{temp,(3)} → π₁^{ét,(3)}（★ 本モジュールの主対象） -/

/-- **q3tpec-2（★）: 実 tempered → 実 étale 比較射** — (z, n) ↦ (z, toZp 3 n)。
    μ 方向 ℤ₃(1) は恒等、離散方向 ℤ は実完備化 toZp 3: ℤ → ℤ₃ で送る本物の群準同型。
    「tempered π₁ を副有限完備化して étale π₁ を得る」自然射の実成分版。 -/
def q3tpEtComp : Hom q3tpGroup q3tpEtGroup where
  map := fun x => (x.1, (toZp 3).map x.2)
  map_mul := fun x y => by
    show (tmzLimit.mul x.1 y.1, (toZp 3).map (intGrp.mul x.2 y.2))
        = (tmzLimit.mul x.1 y.1, (Zp 3).mul ((toZp 3).map x.2) ((toZp 3).map y.2))
    rw [(toZp 3).map_mul]

/-- **q3tpec-2a: μ 方向は恒等** — 比較射は円分 ℤ₃(1) 成分をそのまま保つ。 -/
theorem q3tpEtComp_mu (x : q3tpGroup.carrier) : (q3tpEtComp.map x).1 = x.1 := rfl

/-- **q3tpec-2b: 離散方向は実完備化** — 比較射の離散成分 ＝ toZp 3 ∘ q3tpProj。 -/
theorem q3tpEtComp_disc_completion (x : q3tpGroup.carrier) :
    (q3tpEtComp.map x).2 = (toZp 3).map (q3tpProj.map x) := rfl

/-- **q3tpec-2c: M374F 実完備化との一致** — 比較射の離散成分は M27/M374F の実対角埋め込み
    ttwDiscreteComplete 3（= toZp 3）に rfl で一致する（実機構の消費・二重定義でない）。 -/
theorem q3tpEtComp_via_ttwComplete (x : q3tpGroup.carrier) :
    (q3tpEtComp.map x).2 = (ttwDiscreteComplete 3).map (q3tpProj.map x) := rfl

/-- **q3tpec-2d（★）: 比較射は忠実（単射）** — tempered 群は副有限完備化で情報を失わない。
    μ 方向恒等 ＋ 離散方向 toZp_injective（3 進分離性）の積。M13-8/M27-3 の実消費。 -/
theorem q3tpEtComp_injective : q3tpEtComp.Injective := by
  intro x y h
  have h1 : x.1 = y.1 := by rw [← q3tpEtComp_mu x, ← q3tpEtComp_mu y, h]
  have h2 : (toZp 3).map x.2 = (toZp 3).map y.2 := congrArg Prod.snd h
  have h3 : x.2 = y.2 := toZp_injective 3 (by omega) x.2 y.2 h2
  exact Prod.ext h1 h3

/-! ## q3tpec-3: 各有限段での全射性（「稠密」の代数的影） -/

/-- **q3tpec-3（★）: 各有限段 ℤ/3^n で比較射は全射** — 任意の c ∈ ℤ/3^n は
    tempered 群の元 (1, a) の像の第 n 段。tempered ⊂ étale の像が**すべての有限商を
    尽くす**＝副有限完備化の「稠密」の代数的影。位相を使わない real statement。 -/
theorem q3tpEt_finite_level_surjective (n : Nat) (c : (zmod (3 ^ n)).carrier) :
    ∃ x : q3tpGroup.carrier,
      (limitProj (padicSystem 3) n).map (q3tpEtComp.map x).2 = c := by
  induction c using Quot.ind
  rename_i a
  exact ⟨(tmzLimit.one, a), rfl⟩

/-! ## q3tpec-4: 全体への非全射性（★ 旗艦: 離散 ℤ ⊊ ℤ₃ = tempered ⊊ étale） -/

/-- **q3tpec-4a: 実 ℤ₃∖ℤ の witness** ω = (ω_n mod 3^n) ∈ Zp 3。幾何級数の整合族
    （q3tpec_geom_coh で各段の推移射と両立）。この元は toZp 3 の像に属さない
    （値 −1/2 ∉ ℤ）。 -/
def q3tpEtWitness : (Zp 3).carrier :=
  ⟨fun n => Quot.mk (modCong (3 ^ n)).rel (q3tpGeom n), by
    intro i j h
    apply Quot.sound
    exact q3tpec_geom_coh j i h⟩

/-- **q3tpec-4b（★）: 離散完備化 ℤ → ℤ₃ は非全射** — witness ω は toZp 3 の像に属さない。
    もし toZp 3 a = ω なら ∀ n, 3^n ∣ (a − ω_n)、ゆえに 2·(a−ω_n) + (2ω_n+1) = 2a+1 が
    ∀ n で 3^n で割れる（q3tpec_geom_two: 2ω_n+1 = 3^n）。実 3 進分離性
    int_pow_separated ⟹ 2a+1 = 0、これは整数で不可能。tempered の離散 ℤ が完備化 ℤ₃ の
    **真部分群**であることの完全証明。 -/
theorem q3tp_disc_not_surjective : ¬ ∃ a : Int, (toZp 3).map a = q3tpEtWitness := by
  intro h
  obtain ⟨a, ha⟩ := h
  have hval := congrArg Subtype.val ha
  -- 各段の合同 3^n ∣ (a − ω_n)
  have hcoh : ∀ n : Nat, ((3 ^ n : Nat) : Int) ∣ (a - q3tpGeom n) := by
    intro n
    exact quot_exact intGrp (modCong (3 ^ n)) (congrFun hval n)
  -- 2a + 1 が全 n で 3^n で割れる
  have hodd : ∀ n : Nat, ((3 ^ n : Nat) : Int) ∣ (2 * a + 1) := by
    intro n
    have hd1 : ((3 ^ n : Nat) : Int) ∣ (2 * a - 2 * q3tpGeom n) := by
      obtain ⟨c, hc⟩ := hcoh n
      exact ⟨2 * c, by
        rw [Int.mul_comm ((3 ^ n : Nat) : Int) (2 * c)]
        have hc2 : 2 * a - 2 * q3tpGeom n = 2 * (a - q3tpGeom n) := by omega
        rw [hc2, hc, Int.mul_comm ((3 ^ n : Nat) : Int) c, Int.mul_assoc]⟩
    have hd2 : ((3 ^ n : Nat) : Int) ∣ (2 * q3tpGeom n + 1) := by
      rw [q3tpec_geom_two n]
      exact ⟨1, (Int.mul_one _).symm⟩
    have hsum := Int.dvd_add hd1 hd2
    have heq : (2 * a - 2 * q3tpGeom n) + (2 * q3tpGeom n + 1) = 2 * a + 1 := by omega
    rw [heq] at hsum
    exact hsum
  -- 3 進分離性で 2a+1 = 0、整数で矛盾
  have hzero : 2 * a + 1 = 0 :=
    int_pow_separated 3 (by omega) (2 * a + 1) 0 (fun n => by
      have hn := hodd n
      have hsub : (2 * a + 1) - 0 = 2 * a + 1 := by omega
      rw [hsub]
      exact hn)
  omega

/-- **q3tpec-4c（★・旗艦）: 比較射は全体へは非全射** — (1, ω) ∈ ℤ₃(1) × ℤ₃ は
    q3tpEtComp の像に属さない。忠実（q3tpEtComp_injective）かつ各有限段全射
    （q3tpEt_finite_level_surjective）でありながら**全体 ℤ₃ には届かない**——
    tempered π₁ が自身の副有限完備化（étale π₁）の**真の稠密部分群**であること、
    すなわち **tempered π₁ ⊊ étale π₁**（IUT が étale でなく tempered を要する核心）の
    実定理化。 -/
theorem q3tpEtComp_not_surjective :
    ¬ ∀ y : q3tpEtGroup.carrier, ∃ x : q3tpGroup.carrier, q3tpEtComp.map x = y := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (tmzLimit.one, q3tpEtWitness)
  have h2 : (toZp 3).map x.2 = q3tpEtWitness := congrArg Prod.snd hx
  exact q3tp_disc_not_surjective ⟨x.2, h2⟩

/-! ## q3tpec-5: capstone — 実 tempered ↔ 実 étale 比較データ -/

/-- **q3tpec-5a: 実 tempered → 実 étale 比較の総括データ** — 実比較射・忠実性・実完備化
    との一致・各有限段全射（稠密の代数的影）・全体非全射（tempered ⊊ étale）を束ねる。
    主語は実 tmzLimit（実 ℤ₃(1)）・実 intGrp・実 Zp 3・実 toZp 3（toy 代理なし）。 -/
structure Q3TemperedEtComparisonData where
  /-- tempered 群 π₁^{temp,(3)} = ℤ₃(1) × ℤ。 -/
  temperedGroup : Grp
  /-- étale 群 π₁^{ét,(3)} = ℤ₃(1) × ℤ₃。 -/
  etaleGroup : Grp
  /-- tempered ＝ A5b の実 tempered 群。 -/
  tempered_isA5b : temperedGroup = q3tpGroup
  /-- étale の離散方向 ＝ M374F 実逆極限 ℤ₃。 -/
  etale_isLadic : etaleGroup = prodGrp tmzLimit (ttwInverseLimit 3)
  /-- 実比較射 π₁^{temp} → π₁^{ét}。 -/
  comparison : Hom temperedGroup etaleGroup
  /-- 忠実性（単射）。 -/
  comp_inj : comparison.Injective
  /-- **全体への非全射性**（tempered ⊊ étale）。 -/
  not_surj : ¬ ∀ y, ∃ x, comparison.map x = y

/-- **q3tpec-5b: 見出し実例 q = 3**（pro-3・m=1）— 全フィールドを q3tpec-1〜4 の本物の
    証明で充填。旗艦フィールド not_surj は q3tpEtComp_not_surjective（tempered ⊊ étale の
    実 witness 証明）で埋まる。 -/
def q3tpecData : Q3TemperedEtComparisonData where
  temperedGroup := q3tpGroup
  etaleGroup := q3tpEtGroup
  tempered_isA5b := rfl
  etale_isLadic := rfl
  comparison := q3tpEtComp
  comp_inj := q3tpEtComp_injective
  not_surj := q3tpEtComp_not_surjective

/-- **q3tpec-5c（★）: 実 tempered ↔ 実 étale 比較データは存在する** — 忠実・各有限段稠密・
    全体非全射（tempered ⊊ étale）を満たす実比較射が入力仮説なしで構成できる。IUT の
    「étale では足りず tempered が要る」質的核心の、実主語上の第一実インスタンス。 -/
theorem q3tpec_exists : Nonempty Q3TemperedEtComparisonData := ⟨q3tpecData⟩

/-! ## 実例（tempered ⊊ étale の実部分ケース） -/

/-- 実例: 比較射は忠実（tempered は完備化で情報を失わない）。 -/
example : q3tpEtComp.Injective := q3tpEtComp_injective

/-- 実例: 比較射は各有限段 ℤ/3^n で全射（稠密の代数的影）。 -/
example (n : Nat) (c : (zmod (3 ^ n)).carrier) :
    ∃ x : q3tpGroup.carrier,
      (limitProj (padicSystem 3) n).map (q3tpEtComp.map x).2 = c :=
  q3tpEt_finite_level_surjective n c

/-- 実例: 比較射は全体へは非全射（tempered π₁ ⊊ étale π₁）。 -/
example : ¬ ∀ y : q3tpEtGroup.carrier, ∃ x : q3tpGroup.carrier, q3tpEtComp.map x = y :=
  q3tpEtComp_not_surjective

end IUT
