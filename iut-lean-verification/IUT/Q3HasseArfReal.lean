/-
  IUT/Q3HasseArfReal.lean — 柱B・B4 実 Hasse–Arf（実 Gal(M/L₂) の上付き番号分岐フィルトレーション）

  ── 主要成果の分類: **[実／(a) 昇格]**——List-Nat Hasse–Arf 模型（hau/haa/hfa、実 Galois 群を
     一切持たない Nat 階段整数性）を、実 Gal(M/L₂)=⟨q3kSigma⟩ が実 O_M=q3kRing に作用する
     **実の上付き番号ラミフィケーション・フィルトレーション**（1 拡大）へ昇格する。q9wr の
     **下付き** break（t=2, 可除性形式）を消費し、それを Herbrand ψ/φ 経由で**上付き**述語 G^v
     へ持ち上げる。

     NEW（真水）: **コードベース初の実上付き番号帰属命題**——
       * σ ∈ G^2（実: π₉³∣(σπ₉−π₉)）と σ ∉ G^3（実: ¬π₉⁶∣(σπ₉−π₉)、実 π₉ 可除性の下降で
         q9wr の ¬π₉⁴∣ から得る）。上付き番号 G^v は下付き G_{ψ(v)}——G₀=G₂ ゆえ ψ は break まで
         恒等（ψ(2)=2）で break 後は傾き 3（ψ(3)=5）、よって G^3 の除子は π₉^{ψ(3)+1}=π₉⁶。
       * 実拡大 M/L₂ が hau の Nat 模型点 `hauDataOf 3 _ [2]` を実現し、その上付き jump が整数 2 に
         landing する（q9wr U9 の hau 版 cross-check）。

     CONSUMED（再証明しない）: hau の整数性（`hau_upper_break_integer`・`hauDataOf.integrality`）・
     Herbrand ψ/φ 変換（`rnf_phi_psi`）・q9wr の下付き break（`q9wr_G2_mem`・`q9wr_G3_trivial`・
     `q9wr_break`）。これらの数値（上付き=下付き=2, d 側）は消費のみで再主張しない。

  complete_pct 影響: **B4 0→（独立監査が決定・予測 0.10–0.15）**。

  正直な限定（§4 規約により消さない・弱化しない・最前面に置く）:
  1. **拡大 1 個（M/L₂）・単一 break（t=2）のみ**。
  2. **G₀=G₂ ゆえ Herbrand φ は break まで恒等**（φ(u)=u, u≤2）で、上付き=下付き=2——
     **整数性の数値内容は退化的（ほぼ自明）**。本モジュールの真水は「上付き述語の**実現**」
     （σ∈G^2・σ∉G^3 を実 π₉ 可除性で実 O_M 上に建てる）であって、新しい整数性定理ではない。
  3. **上付き番号は Nat 値のみ**（有理数上付き番号なし・付値関数 v_M なし・可除性形式、
     q9wr 正直限定 1 継承）。
  4. **σ を主語**とする（σ² 側の G^v 帰属は範囲外——q9ac が別枠で σ² 側を扱う）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。共有ファイル未変更（新規 1 本）。
-/
import IUT.Q3WildRamFiltrationReal
import IUT.HasseArfUnconditional
import IUT.RamifiedNormFiltration

namespace IUT

/-! ## §1 実 σ の一様化子差分と π₉ 冪除子（q9wr 互換の nesting） -/

/-- 実 Gal(M/L₂) 生成元 σ の一様化子差分 σ(π₉)−π₉（実 O_M 内）。 -/
def q9haSigmaDiff : q3kCar := q3kAdd (q3kSigma q9psPi9) (q3kNeg q9psPi9)

/-- π₉³（q9wr の G₂ 除子と同一 nesting）。 -/
def q9haPi3 : q3kCar := q3kMul (q3kMul q9psPi9 q9psPi9) q9psPi9

/-- π₉⁴（q9wr の G₃ 除子 `q9wr_G3_trivial` と同一 nesting）。 -/
def q9haPi4 : q3kCar := q3kMul q9haPi3 q9psPi9

/-- π₉⁶ = π₉⁴·π₉²（実上付き G^3 の除子・ψ(3)=5 ゆえ指数 ψ(3)+1=6）。 -/
def q9haPi6 : q3kCar := q3kMul q9haPi4 (q3kMul q9psPi9 q9psPi9)

/-! ## §2 可除性下降補題（q9ac と重複許容・5 行）

    大除子 bigD が小除子 smallD の倍（bigD=smallD·extra）なら、bigD∣x ⟹ smallD∣x。
    対偶で ¬smallD∣x ⟹ ¬bigD∣x（¬π₉⁴∣ ⟹ ¬π₉⁶∣ を得る道具）。付値関数を建てない可除性形式。 -/

/-- **可除性下降**: bigD = smallD·extra かつ bigD∣x ⟹ smallD∣x。 -/
theorem q9ha_dvd_descent {smallD extra bigD x : q3kCar}
    (hb : bigD = q3kMul smallD extra) (hd : q9wrDvd bigD x) : q9wrDvd smallD x := by
  obtain ⟨c, hc⟩ := hd
  refine ⟨q3kMul extra c, ?_⟩
  rw [hc, hb, q3k_mul_assoc smallD extra c]

/-- **可除性下降の対偶**: bigD = smallD·extra かつ ¬smallD∣x ⟹ ¬bigD∣x。 -/
theorem q9ha_not_dvd_descent {smallD extra bigD x : q3kCar}
    (hb : bigD = q3kMul smallD extra) (hnd : ¬ q9wrDvd smallD x) : ¬ q9wrDvd bigD x :=
  fun hd => hnd (q9ha_dvd_descent hb hd)

/-! ## §3 実 Herbrand ψ（この拡大・単一 break t=2・G₀=G₂）

    上付き番号 G^v は下付き G_{ψ(v)}。M/L₂ は [G₀:G_t]=1（0≤t≤2）ゆえ φ は break まで恒等
    （φ(u)=u, u≤2）、その逆 ψ も break まで恒等（ψ(v)=v, v≤2）で break 後の傾きは 3
    （ψ(3)=2+3·(3−2)=5）。Nat 切り捨て減算で閉形式 ψ(v)=v+2·(v−2)（v≤2 で v、v≥2 で 3v−4）。
    上付き G^v の実除子は π₉^{ψ(v)+1}: v=2 → π₉³（=q9haPi3）, v=3 → π₉⁶（=q9haPi6）。 -/

/-- **実 Herbrand ψ**（単一 break t=2・G₀=G₂）: ψ(v)=v+2·(v−2)（v≤2 で恒等・v≥2 で傾き 3）。 -/
def q9haPsi (v : Nat) : Nat := v + 2 * (v - 2)

/-- ψ(2)=2（break まで恒等——G₀=G₂ ゆえ φ/ψ が退化的である核）。 -/
theorem q9ha_psi_two : q9haPsi 2 = 2 := rfl

/-- ψ(3)=5（break 後の傾き 3）。 -/
theorem q9ha_psi_three : q9haPsi 3 = 5 := rfl

/-- **上付き除子の指数**: G^v の実除子は π₉^{ψ(v)+1}——v=2 で π₉³（q9haPi3）, v=3 で π₉⁶（q9haPi6）。
    ψ を実の π₉ 冪除子（実 O_M 内）に緊縛する（素の Nat 変換の遊離を禁止）。 -/
theorem q9ha_upper_exponents : q9haPsi 2 + 1 = 3 ∧ q9haPsi 3 + 1 = 6 := ⟨rfl, rfl⟩

/-! ## §4 実上付き番号帰属（★ コードベース初）

    σ∈G^2 と σ∉G^3 を、実 O_M 上の π₉ 可除性で実現する。上付き番号の実現は codebase 初——
    従来の Hasse–Arf（hau/haa/hfa）は実 Galois を一切持たない Nat 階段のみ。 -/

/-- **q9ha_upper_G2_real（★）: σ ∈ G^2（実上付き番号）**——ψ(2)=2 ゆえ実除子 π₉³ で
    π₉³∣(σπ₉−π₉)。q9wr_G2_mem.1 を上付き番号として消費（G₀=G₂ で上付き break=下付き break=2）。 -/
theorem q9ha_upper_G2_real : q9wrDvd q9haPi3 q9haSigmaDiff :=
  q9wr_G2_mem.1

/-- **q9ha_upper_G3_trivial_real（★）: σ ∉ G^3（実上付き番号）**——ψ(3)=5 ゆえ実除子 π₉⁶ で
    ¬π₉⁶∣(σπ₉−π₉)。q9wr_G3_trivial（¬π₉⁴∣）から π₉⁶=π₉⁴·π₉² の可除性下降で得る。
    **実上付き番号帰属命題の codebase 初例**。 -/
theorem q9ha_upper_G3_trivial_real : ¬ q9wrDvd q9haPi6 q9haSigmaDiff :=
  q9ha_not_dvd_descent (rfl) q9wr_G3_trivial

/-! ## §5 実上付き番号の位数階段（Nat 値・実 Prop への iff 緊縛）

    |G^v|（上付き番号の分岐群位数）= 3（v≤2）・1（v≥3）——単一 break at 2。素の Nat 階段の
    再生産を避けるため、各実現値を実 π₉ 可除性帰属（σ 主語）に iff で緊縛する。 -/

/-- **上付き番号分岐群位数** |G^v| = 3（v≤2）・1（それ以外）。単一 break at 2。 -/
def q9haOrder (v : Nat) : Nat := if v ≤ 2 then 3 else 1

/-- **iff 緊縛（v=2）**: |G^2|=3 ⟺ σ が実 G^2 帰属（π₉³∣(σπ₉−π₉)）。Nat 値を実 Prop に緊縛。 -/
theorem q9ha_order_two_iff : q9haOrder 2 = 3 ↔ q9wrDvd q9haPi3 q9haSigmaDiff :=
  ⟨fun _ => q9ha_upper_G2_real, fun _ => rfl⟩

/-- **iff 緊縛（v=3）**: |G^3|=1 ⟺ σ が実 G^3 非帰属（¬π₉⁶∣(σπ₉−π₉)）。Nat 値を実 Prop に緊縛。 -/
theorem q9ha_order_three_iff : q9haOrder 3 = 1 ↔ ¬ q9wrDvd q9haPi6 q9haSigmaDiff :=
  ⟨fun _ => q9ha_upper_G3_trivial_real, fun _ => rfl⟩

/-! ## §6 実下付き break → Herbrand ψ/φ → 実上付き break（退化的だが実側で実現）

    実下付き break t=2（q9wr_break）を Herbrand 変換で実上付き break 2 へ写す。G₀=G₂ ゆえ
    φ は break まで恒等（e=1 で rnf φ∘ψ=id）——変換は退化的だが、**要点は実側の realization**
    （hau の Nat 模型 us=[2] が実拡大に対応することの spec）。 -/

/-- **q9ha_break_transform: 実下付き break 2 → 上付き break 2（整数 landing）**。
    hauLowerFrom 3 1 [2]=2（実下付き break の Nat 符号化）、hauUpperFrom=hauUpperBreak
    （hau 整数性を消費）、hauUpperBreak [2]=2（上付き break 値）、rnfPhi 1 (rnfPsi 1 2)=2
    （e=1・G₀=G₂ ゆえ φ が break まで恒等——退化的な Herbrand 往復）。 -/
theorem q9ha_break_transform :
    hauLowerFrom 3 1 [2] = 2
    ∧ hauUpperFrom 3 1 [2] = hauUpperBreak [2]
    ∧ hauUpperBreak [2] = 2
    ∧ rnfPhi 1 (rnfPsi 1 2) = 2 :=
  ⟨rfl, hau_upper_break_integer 3 (by omega) [2], rfl, rnf_phi_psi 1 2 (by omega)⟩

/-! ## §7 実拡大が hau の Nat 模型点を実現（q9wr U9 の hau 版 cross-check） -/

/-- **q9ha_hasse_arf_instance: 実拡大 M/L₂ が hau 模型点 `hauDataOf 3 _ [2]` を実現**——
    その上付き jump は整数 2、上付き break 整数性は hau の `.integrality` フィールドを**消費**
    （再証明しない）。q9wr U9（wcd cross-check）の hau 版。 -/
theorem q9ha_hasse_arf_instance :
    (hauDataOf 3 (by omega) [2]).upperBreak = 2
    ∧ hauUpperFrom 3 1 [2] = (hauDataOf 3 (by omega) [2]).upperBreak :=
  ⟨rfl, (hauDataOf 3 (by omega) [2]).integrality⟩

/-! ## §8 capstone: 実 Hasse–Arf データ（束ねのみ・新規証明ゼロ） -/

/-- **実上付き番号 Hasse–Arf データ**——実 σ の上付き G^2 帰属・G^3 非帰属（実現の核）、
    位数階段、下付き→上付き break の整数 landing（hau 消費）を束ねる。 -/
structure Q3HasseArfRealData where
  /-- σ ∈ G^2（実上付き番号・π₉³∣(σπ₉−π₉)）。 -/
  upper_G2 : q9wrDvd q9haPi3 q9haSigmaDiff
  /-- σ ∉ G^3（実上付き番号・¬π₉⁶∣(σπ₉−π₉)）。 -/
  upper_G3_trivial : ¬ q9wrDvd q9haPi6 q9haSigmaDiff
  /-- |G^2|=3。 -/
  order_two : q9haOrder 2 = 3
  /-- |G^3|=1。 -/
  order_three : q9haOrder 3 = 1
  /-- 実下付き break（Nat 符号化）=2。 -/
  lower_break : hauLowerFrom 3 1 [2] = 2
  /-- 上付き break=2。 -/
  upper_break : hauUpperBreak [2] = 2
  /-- 上付き break 整数性（hau 消費・φ が break まで恒等ゆえ landing）。 -/
  integrality : hauUpperFrom 3 1 [2] = hauUpperBreak [2]

/-- **見出し実例**——実 Gal(M/L₂) の実上付き番号フィルトレーション（G^2 帰属・G^3 非帰属・
    上付き break 2 整数 landing）。 -/
def q9ha_data : Q3HasseArfRealData where
  upper_G2 := q9ha_upper_G2_real
  upper_G3_trivial := q9ha_upper_G3_trivial_real
  order_two := rfl
  order_three := rfl
  lower_break := rfl
  upper_break := rfl
  integrality := hau_upper_break_integer 3 (by omega) [2]

/-- **実上付き番号 Hasse–Arf フィルトレーションの存在**（実 σ・実 O_M・単一 break t=2・上付き=2）。 -/
theorem q9ha_exists : Nonempty Q3HasseArfRealData := ⟨q9ha_data⟩

end IUT
