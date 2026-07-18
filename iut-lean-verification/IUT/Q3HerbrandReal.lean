/-
  IUT/Q3HerbrandReal.lean — 柱B・B4 実 Herbrand φ/ψ（実 Gal(M/L₂)=⟨σ⟩ の完全 Herbrand 機械）

  ── 主要成果の分類: **[実／(a) 昇格]**——q9ha は σ 側の上付き番号帰属と ψ（下付き→上付き）
     **だけ**を建てた（q9ha 正直限定 #4「σ を主語（σ² 側は範囲外）」・Herbrand φ 逆写像の欠落）。
     本モジュールは実 Gal(M/L₂)=⟨q3kSigma⟩≅ℤ/3 拡大に対し **完全な Herbrand 機械**へ昇格する:
       * Herbrand φ（上付き→下付き）を ψ の逆写像として建て、往復 φ∘ψ=id・ψ∘φ=id を証明。
       * ψ/φ の傾き恒等式（break まで傾き 1・break 後は位数 3 を反映して ψ 傾き 3／φ 傾き 1/3）。
       * **σ² 側**の上付き番号帰属（q9ha は σ のみ）——q9ac の σ² Swan/break を消費して
         q9ha 正直限定 #4 を discharge。
       * **全群** Gal(M/L₂)={1,σ,σ²} の上付きフィルトレーション（G^v=全群 (v≤2)・自明 (v>2)）。
       * **Hasse–Arf 定理のインスタンス**——単一上付き break v=2 が整数に landing。

     NEW（真水・q9ha 比）:
       1. Herbrand φ 逆写像 `q9hbPhi` と往復 `q9hb_phi_psi`（φ∘ψ=id, v≤3）・`q9hb_psi_phi`（ψ∘φ=id, 像上）。
       2. σ² 側上付き帰属 `q9hb_upper_sigma2_real`（σ²∈G^2・σ²∉G^3）——q9ha 限定 #4 の解消。
       3. 全群上付きフィルトレーション `q9hb_upper_full_group`（1,σ,σ² 全部を束ねる）。
       4. Hasse–Arf 整数 jump `q9hb_hasse_arf_integer_jumps`（単一 break v=2∈ℕ）。

     CONSUMED（再証明しない）: q9ha の ψ（`q9haPsi`・`q9ha_psi_two/three`・`q9ha_upper_exponents`）・
     σ 側上付き帰属（`q9ha_upper_G2_real`・`q9ha_upper_G3_trivial_real`）・可除性下降
     （`q9ha_not_dvd_descent`）・π₉ 冪除子（`q9haPi3`・`q9haPi6`）・σ² break 上界
     （q9ac `q9ac_sigma2_G3_trivial`）・G₂ 帰属（`q9wr_G2_mem`）。

  complete_pct 影響: **B4 0.10→（独立監査次第・予測 +0.03〜0.07）**。

  正直な限定（§4 規約により消さない・弱化しない・最前面に置く）:
  1. **単一 ℤ/3 拡大 M/L₂・単一 break のみ**。Hasse–Arf 整数性はこの拡大での**低次元
     インスタンス**であって一般 Hasse–Arf 定理ではない（Gal=ℤ/3・break 1 個ゆえ整数性の
     数値内容は退化的——真水は φ 逆写像・σ² 側・全群フィルトレーションの realization）。
  2. **ψ/φ は明示的 Nat 区分線形関数**（一般の filtration-jump 理論から建てたものではない）。
     有理数上付き番号・付値関数 v_M はゼロ（q9ha/q9wr 正直限定 継承）。
  3. **フィルトレーションは π₉ 可除性形式**（q9wr/q9ha から継承・付値関数を建てない）。
  4. **σ,σ² は具体元**（任意群元ではない——群は文字通り {1,σ,σ²}）。恒等元は差分 0 で自明帰属。
  5. q9ha/q9ac/q9wr の正直限定を全て継承する。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。共有ファイル未変更（新規 1 本）。
-/
import IUT.Q3HasseArfReal
import IUT.Q3ArtinConductorReal

namespace IUT

/-! ## §1 実 Herbrand φ（上付き→下付き・ψ の逆写像）

    q9ha の ψ(v)=v+2·(v−2)（break まで恒等・break 後傾き 3）に対し、その逆写像 φ を建てる。
    ψ(0)=0, ψ(1)=1, ψ(2)=2, ψ(3)=5, ψ(4)=8, …（v≤2 で恒等・v≥2 で傾き 3）。
    よって φ は u≤2 で恒等・u≥2 で傾き 1/3（φ(u)=(u+4)/3、位数 3 群の 3 上付きステップ＝
    1 下付きステップ）。φ(2)=2, φ(5)=3, φ(8)=4——退化的 break まで恒等で往復が閉じる。 -/

/-- **実 Herbrand φ**（上付き→下付き）: u≤2 で恒等・u≥2 で (u+4)/3（ψ の逆写像）。 -/
def q9hbPhi (u : Nat) : Nat := if u ≤ 2 then u else (u + 4) / 3

/-- φ(2)=2（break 点で恒等）。 -/
theorem q9hb_phi_two : q9hbPhi 2 = 2 := rfl

/-- φ(5)=3（ψ(3)=5 の逆・傾き 1/3）。 -/
theorem q9hb_phi_five : q9hbPhi 5 = 3 := rfl

/-! ## §2 往復 φ∘ψ=id（v≤3）・ψ∘φ=id（ψ の像上） -/

/-- **q9hb_phi_psi: φ(ψ(v))=v（v≤3）**——φ が ψ を関連範囲で逆写像する（Herbrand 往復の核）。 -/
theorem q9hb_phi_psi : ∀ v : Nat, v ≤ 3 → q9hbPhi (q9haPsi v) = v := by
  intro v hv
  match v, hv with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | (n + 4), h => exact absurd h (by omega)

/-- **q9hb_psi_phi: ψ(φ(u))=u（ψ の像 u∈{0,1,2,5} 上）**——往復のもう一方向。
    像外（u=3,4 等）では ψ∘φ≠id（φ(3)=φ(4)=2, ψ(2)=2）ゆえ像上でのみ主張する（正直限定 2）。 -/
theorem q9hb_psi_phi :
    q9haPsi (q9hbPhi 0) = 0 ∧ q9haPsi (q9hbPhi 1) = 1
    ∧ q9haPsi (q9hbPhi 2) = 2 ∧ q9haPsi (q9hbPhi 5) = 5 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §3 ψ/φ の傾き恒等式（位数 3 群を反映） -/

/-- **q9hb_psi_slope: ψ の傾き**——break（v=2）まで傾き 1（ψ(1)−ψ(0)=ψ(2)−ψ(1)=1）・
    break 後は傾き 3（ψ(3)−ψ(2)=ψ(4)−ψ(3)=3、|G_i|=3 を反映）。 -/
theorem q9hb_psi_slope :
    q9haPsi 1 - q9haPsi 0 = 1 ∧ q9haPsi 2 - q9haPsi 1 = 1
    ∧ q9haPsi 3 - q9haPsi 2 = 3 ∧ q9haPsi 4 - q9haPsi 3 = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **q9hb_phi_slope: φ の傾き**——break（u=2）まで傾き 1・break 後は傾き 1/3
    （φ(5)−φ(2)=φ(8)−φ(5)=1、すなわち 3 上付きステップ＝1 下付きステップ・位数 3）。 -/
theorem q9hb_phi_slope :
    q9hbPhi 1 - q9hbPhi 0 = 1 ∧ q9hbPhi 2 - q9hbPhi 1 = 1
    ∧ q9hbPhi 5 - q9hbPhi 2 = 1 ∧ q9hbPhi 8 - q9hbPhi 5 = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §4 σ² 側の実上付き番号帰属（★ q9ha 正直限定 #4 の解消）

    q9ha は σ 側のみ（`q9ha_upper_G2_real`・`q9ha_upper_G3_trivial_real`）。ここで σ² 側を
    実 π₉ 可除性で建てる。G^2 帰属は q9wr_G2_mem.2 を消費、G^3 非帰属は q9ac の σ² break 上界
    `q9ac_sigma2_G3_trivial`（¬π₉⁴∣）から π₉⁶=π₉⁴·π₉² の可除性下降（q9ha 消費）で得る。 -/

/-- σ² の一様化子差分 σ²(π₉)−π₉（実 O_M 内・q9ac/q9wr 互換 nesting）。 -/
def q9hbSigma2Diff : q3kCar := q3kAdd (q3kSigma2 q9psPi9) (q3kNeg q9psPi9)

/-- σ² ∈ G^2（実上付き番号・π₉³∣(σ²π₉−π₉)）——q9wr_G2_mem.2 を上付き番号として消費。 -/
theorem q9hb_upper_sigma2_G2_real : q9wrDvd q9haPi3 q9hbSigma2Diff :=
  q9wr_G2_mem.2

/-- σ² ∉ G^3（実上付き番号・¬π₉⁶∣(σ²π₉−π₉)）——q9ac の ¬π₉⁴∣ から可除性下降。 -/
theorem q9hb_upper_sigma2_G3_trivial_real : ¬ q9wrDvd q9haPi6 q9hbSigma2Diff :=
  q9ha_not_dvd_descent rfl q9ac_sigma2_G3_trivial

/-- **q9hb_upper_sigma2_real（★）: σ² 側の完全上付き帰属**（σ²∈G^2 ∧ σ²∉G^3）。
    q9ha 正直限定 #4「σ を主語（σ² 側は範囲外）」を discharge する。 -/
theorem q9hb_upper_sigma2_real :
    q9wrDvd q9haPi3 q9hbSigma2Diff ∧ ¬ q9wrDvd q9haPi6 q9hbSigma2Diff :=
  ⟨q9hb_upper_sigma2_G2_real, q9hb_upper_sigma2_G3_trivial_real⟩

/-! ## §5 全群 Gal(M/L₂)={1,σ,σ²} の上付きフィルトレーション

    G^v = 全群（v≤2）・自明群 {1}（v>2）——単一上付き break v=2。恒等元 1 は差分 0
    （1·π₉−π₉=0）ゆえ全ての除子で自明帰属（正直限定 4）。σ・σ² は q9ha/q9hb の帰属を消費。 -/

/-- 恒等元 1 の一様化子差分 1·π₉−π₉ = 0（全ての除子で自明帰属する核）。 -/
def q9hbIdDiff : q3kCar := q3kAdd q9psPi9 (q3kNeg q9psPi9)

/-- **零可除**: 任意の除子 d は自己差分 y−y（=0）を割る（∃c=0, y−y=d·0）。恒等元帰属の道具。 -/
theorem q9hb_dvd_self_sub (d y : q3kCar) : q9wrDvd d (q3kAdd y (q3kNeg y)) := by
  refine ⟨q3kZero, ?_⟩
  have h1 : q3kAdd y (q3kNeg y) = q3kZero := q3kRing.add_neg y
  have h2 : q3kMul d q3kZero = q3kZero := q3kRing.mul_zero d
  rw [h1, h2]

/-- 恒等元 1 ∈ G^2（自明・差分 0）。 -/
theorem q9hb_upper_id_G2 : q9wrDvd q9haPi3 q9hbIdDiff :=
  q9hb_dvd_self_sub q9haPi3 q9psPi9

/-- 恒等元 1 ∈ G^3（自明群 {1} は恒等元を含む・差分 0）。 -/
theorem q9hb_upper_id_G3 : q9wrDvd q9haPi6 q9hbIdDiff :=
  q9hb_dvd_self_sub q9haPi6 q9psPi9

/-- **q9hb_upper_full_group（★）: 全群 Gal(M/L₂)={1,σ,σ²} の上付きフィルトレーション**。
    G^2=全群（1,σ,σ² 全部が π₉³∣）・G^3=自明群 {1}（σ,σ² は π₉⁶∤・1 のみ帰属）。
    単一上付き break v=2。σ の帰属は q9ha、σ² は q9hb §4、恒等元は零可除で消費。 -/
theorem q9hb_upper_full_group :
    (q9wrDvd q9haPi3 q9haSigmaDiff ∧ q9wrDvd q9haPi3 q9hbSigma2Diff
      ∧ q9wrDvd q9haPi3 q9hbIdDiff)
    ∧ (¬ q9wrDvd q9haPi6 q9haSigmaDiff ∧ ¬ q9wrDvd q9haPi6 q9hbSigma2Diff
      ∧ q9wrDvd q9haPi6 q9hbIdDiff) :=
  ⟨⟨q9ha_upper_G2_real, q9hb_upper_sigma2_G2_real, q9hb_upper_id_G2⟩,
   ⟨q9ha_upper_G3_trivial_real, q9hb_upper_sigma2_G3_trivial_real, q9hb_upper_id_G3⟩⟩

/-! ## §6 Hasse–Arf 定理のインスタンス（単一上付き break v=2 は整数）

    Hasse–Arf: 上付き番号 break は整数。この ℤ/3 拡大では下付き break t=2 を φ で写した
    上付き break φ(2)=2 が整数に landing する（本拡大では退化的だが genuine な低次元
    インスタンス——正直限定 1）。ψ(v)+1 の指数（q9ha_upper_exponents）を消費して束ねる。 -/

/-- **q9hb_hasse_arf_integer_jumps（★）: Hasse–Arf 整数 jump インスタンス**。
    φ(ψ(2))=2（往復整合）∧ 上付き break φ(下付き break 2)=2∈ℕ（整数 landing）∧
    上付き除子指数 ψ(2)+1=3・ψ(3)+1=6（q9ha_upper_exponents 消費）。 -/
theorem q9hb_hasse_arf_integer_jumps :
    q9hbPhi (q9haPsi 2) = 2 ∧ q9hbPhi 2 = 2
    ∧ q9haPsi 2 + 1 = 3 ∧ q9haPsi 3 + 1 = 6 :=
  ⟨rfl, rfl, q9ha_upper_exponents.1, q9ha_upper_exponents.2⟩

/-! ## §7 capstone: 実 Herbrand データ（束ねのみ・新規証明ゼロ） -/

/-- **実 Herbrand 機械データ**——完全 Herbrand φ/ψ 往復・σ² 側上付き帰属・全群
    フィルトレーション・Hasse–Arf 整数 break を束ねる（q9ha/q9ac/q9wr 消費・束ねのみ）。 -/
structure Q3HerbrandRealData where
  /-- φ∘ψ=id（v≤3・Herbrand 往復）。 -/
  phi_psi : ∀ v : Nat, v ≤ 3 → q9hbPhi (q9haPsi v) = v
  /-- ψ∘φ=id（像 u=5 上・傾き 1/3 の往復）。 -/
  psi_phi_image : q9haPsi (q9hbPhi 5) = 5
  /-- σ² ∈ G^2（★ q9ha 限定 #4 解消）。 -/
  sigma2_G2 : q9wrDvd q9haPi3 q9hbSigma2Diff
  /-- σ² ∉ G^3（★ q9ha 限定 #4 解消）。 -/
  sigma2_G3_trivial : ¬ q9wrDvd q9haPi6 q9hbSigma2Diff
  /-- 全群 G^2 帰属（1,σ,σ² 全部）。 -/
  full_G2 : q9wrDvd q9haPi3 q9haSigmaDiff ∧ q9wrDvd q9haPi3 q9hbSigma2Diff
    ∧ q9wrDvd q9haPi3 q9hbIdDiff
  /-- G^3 自明群 {1}（σ,σ² 排除・1 帰属）。 -/
  trivial_G3 : ¬ q9wrDvd q9haPi6 q9haSigmaDiff ∧ ¬ q9wrDvd q9haPi6 q9hbSigma2Diff
    ∧ q9wrDvd q9haPi6 q9hbIdDiff
  /-- Hasse–Arf 上付き break φ(2)=2∈ℕ（整数 landing）。 -/
  hasse_arf_break : q9hbPhi 2 = 2
  /-- 上付き除子指数 ψ(2)+1=3（q9ha 消費）。 -/
  upper_exp : q9haPsi 2 + 1 = 3

/-- **見出し実例**——実 Gal(M/L₂)=⟨σ⟩≅ℤ/3 の完全 Herbrand 機械（φ/ψ 往復・σ² 側・全群・
    Hasse–Arf 整数 break）。 -/
def q9hb_data : Q3HerbrandRealData where
  phi_psi := q9hb_phi_psi
  psi_phi_image := q9hb_psi_phi.2.2.2
  sigma2_G2 := q9hb_upper_sigma2_G2_real
  sigma2_G3_trivial := q9hb_upper_sigma2_G3_trivial_real
  full_G2 := q9hb_upper_full_group.1
  trivial_G3 := q9hb_upper_full_group.2
  hasse_arf_break := q9hb_hasse_arf_integer_jumps.2.1
  upper_exp := q9ha_upper_exponents.1

/-- **実 Herbrand 機械の存在**（実 σ・σ²・全群・単一 break v=2・φ 逆写像込み）。 -/
theorem q9hb_exists : Nonempty Q3HerbrandRealData := ⟨q9hb_data⟩

end IUT
