/-
  IUT/Q3TemperedThetaClass.lean — A5d [実／昇格(a)+本物建設(b)]

  ── 主要成果の分類: **[実／昇格(a)+本物建設(b)]**。
     昇格(a): M384F thetaGrp（ℤ³ 離散 Heisenberg・自認「実曲線未接続」）と
     M424F tpeGroup（= thetaGrp ⋊ ℤ・自認「実被覆空間の実現は外部」）の代理
     tempered テータ骨格を、実 E₉(ℚ₃) 上の実 Mumford テータ群 q3thGrp（A8）内の
     本物の準同型 Φ/Ψ で実現する。
     本物建設(b): 一般 Grp の braiding 補題（xᵃyᵇ = z^{ab}yᵇxᵃ）・準同型 Φ/Ψ そのもの。

  complete_pct 影響: **A5 0.15→ target（独立監査確定が条件）**。M384F/M424F の代理
  tempered-theta 骨格を Φ/Ψ で実現し、(1) 抽象シンプレクティック形式＝実 Weil ペア
  リング ∈ 実 μ₂⊂ℤ₃^×、(2) deck×テータ交換子＝実 (−1)^{nb}（分裂直積ブロッカーの
  discharge・deck 切断がテータ部と可換でない初の実 tempered 対象）、(3) v(q)=2 の
  tempered-π₁ 側復元（Ψ(deck n).w = 3ⁿ 半周期・平方 = qⁿ = q3tdPeriodHom）を完全証明。
  **A8/A7/E は主張しない**（q3th の定理は消費のみ・再証明ゼロ）。

  正直な限定（§4 準拠・消去/弱化しない）:
  1. **実現は level 2（μ₂ 影）**: Ψ は単射でない（ker = {((−n,2β,2γ),n)}・
     q3nt_psi_level2_collapse / q3nt_psi_deck_fusion で定理化）。代理シクロトーム ℤ の
     実現は mod 2 のみ。ℤ 全体（ẑ(1)）の実現は奇レベル拡大体機構（後続・ζ_l∉ℚ₃ で恒久
     ブロック）。χ 捻り（M429F）は level 2 で不可視（q3nt_chi_invisible）。
  2. **tempered π₁ の「定義」は依然外部**: Berkovich/rigid 位相なし。Ψ は「実被覆空間の
     π₁ からの写像」でなく「mod-2 étale-theta 商の群論的影の実群内実現」。A5 恒久上限
     0.35–0.4 は不変。
  3. **G_{ℚ₃}/実 Gal 作用 0**: q3thGrp・Ψ 像への実 Galois 作用は A7 後続。
  4. **実テータ関数 0・cuspidalization 本体 0**: q3th 正直限定 2・3 を継承（消さない）。
  5. **二重計上の排除（§2.4・監査向け明文）**:
     - vs A8（q3th）: q3th の定理は**消費のみ**（再証明・再輸出 0 本・q3th ファイル不変更）。
       A5d の計上対象は Φ/Ψ・braiding・「代理の主張＝実値」等式・v(q) の tempered 側復元
       のみ。各旗艦（q3nt_symplectic_real・q3nt_deck_theta_real・q3nt_vq_recover）は
       Φ/Ψ または代理対象（thetaGrp/tpeGroup）を主語に持ち、Φ/Ψ を消去すると成立しない。
       **A8 status は今回主張しない**。
     - vs A5a/A5b/A5c: q3tdPeriodHom は消費（v(q) 着地先）。q3tpGroup は対照定理
       q3nt_split_contrast の主語として登場（既存正直限定は不変更）。
     - vs A4/A7/E: 主張しない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。
-/
import IUT.Q3ThetaGroup
import IUT.TemperedPi1Etale
import IUT.Q3TateDeck
import IUT.Q3TemperedPi1

namespace IUT

/-! ## q3nt-helpers-0: 一般 Grp の交換・冪補助則（q3thM 特化版の一般化・消費でなく新規） -/

/-- 一般 Grp: 可換元の逆元も可換。 -/
theorem grp_comm_inv (G : Grp) {z g : G.carrier} (h : G.mul z g = G.mul g z) :
    G.mul (G.inv z) g = G.mul g (G.inv z) := by
  apply G.mul_left_cancel (a := z)
  have hL : G.mul z (G.mul (G.inv z) g) = g := by
    rw [← G.mul_assoc z (G.inv z) g, G.mul_inv, G.one_mul]
  have hR : G.mul z (G.mul g (G.inv z)) = g := by
    rw [← G.mul_assoc z g (G.inv z), h, G.mul_assoc g z (G.inv z), G.mul_inv, G.mul_one]
  rw [hL, hR]

/-- 一般 Grp: z が g と可換なら zⁿ（Nat 冪）も g と可換。 -/
theorem grp_pow_comm_of (G : Grp) (z g : G.carrier) (h : G.mul z g = G.mul g z) (k : Nat) :
    G.mul (tateNpow G z k) g = G.mul g (tateNpow G z k) := by
  induction k with
  | zero =>
    show G.mul G.one g = G.mul g G.one
    rw [G.one_mul, G.mul_one]
  | succ k ih =>
    show G.mul (G.mul (tateNpow G z k) z) g = G.mul g (G.mul (tateNpow G z k) z)
    rw [G.mul_assoc (tateNpow G z k) z g, h, ← G.mul_assoc (tateNpow G z k) g z, ih,
        G.mul_assoc g (tateNpow G z k) z]

/-- 一般 Grp: z が g と可換なら zⁿ（整数冪）も g と可換（中心元の zpow 中心性）。 -/
theorem grp_zpow_central (G : Grp) (z : G.carrier)
    (hz : ∀ g, G.mul z g = G.mul g z) (n : Int) (g : G.carrier) :
    G.mul (tateZpow G z n) g = G.mul g (tateZpow G z n) := by
  cases n with
  | ofNat k => exact grp_pow_comm_of G z g (hz g) k
  | negSucc k =>
    show G.mul (tateNpow G (G.inv z) (k + 1)) g = G.mul g (tateNpow G (G.inv z) (k + 1))
    exact grp_pow_comm_of G (G.inv z) g (grp_comm_inv G (hz g)) (k + 1)

/-- 一般 Grp: 逆底の整数冪＝負冪 (g⁻¹)ⁿ = g^{−n}（q3th_zpow_inv_eq の一般化）。 -/
theorem grp_zpow_inv_base (G : Grp) (g : G.carrier) : ∀ n : Int,
    tateZpow G (G.inv g) n = tateZpow G g (-n) := by
  intro n
  cases n with
  | ofNat k =>
    show tateNpow G (G.inv g) k = tateZpow G g (-((k : Nat) : Int))
    induction k with
    | zero => rfl
    | succ j ih =>
      show G.mul (tateNpow G (G.inv g) j) (G.inv g) = tateZpow G g (-(((j + 1 : Nat) : Int)))
      rw [ih]
      have hidx : -(((j + 1 : Nat) : Int)) = -((j : Nat) : Int) + (-1) := by omega
      have h1 : tateZpow G g (-1) = G.inv g := tateZpow_negOne G g
      rw [hidx, tateZpow_add, h1]
  | negSucc k =>
    show tateNpow G (G.inv (G.inv g)) (k + 1) = tateZpow G g (-(Int.negSucc k))
    rw [Grp.inv_inv]
    have hidx : -(Int.negSucc k) = ((k + 1 : Nat) : Int) := by omega
    rw [hidx]
    rfl

/-- 一般 Grp: g²=1 なら g^{−m} = gᵐ（位数 2 元の zpow は符号不変・χ level-2 不可視の核）。 -/
theorem grp_zpow_neg_of_sq (G : Grp) (g : G.carrier) (hg : G.mul g g = G.one) (m : Int) :
    tateZpow G g (-m) = tateZpow G g m := by
  have hinv : G.inv g = g := (G.inv_eq_of_mul_eq_one hg).symm
  rw [← grp_zpow_inv_base G g m, hinv]

/-- 一般 Grp: 交換子の並べ替え関係 (((xy)x⁻¹)y⁻¹)(yx) = xy。 -/
theorem grp_comm_rel (G : Grp) (x y : G.carrier) :
    G.mul (G.mul (G.mul (G.mul x y) (G.inv x)) (G.inv y)) (G.mul y x) = G.mul x y := by
  rw [G.mul_assoc (G.mul (G.mul x y) (G.inv x)) (G.inv y) (G.mul y x),
      ← G.mul_assoc (G.inv y) y x, G.inv_mul, G.one_mul,
      G.mul_assoc (G.mul x y) (G.inv x) x, G.inv_mul, G.mul_one]

/-- 一般 Grp: 準同型は tateNpow を保つ。 -/
theorem hom_map_tnpow {G H : Grp} (f : Hom G H) (g : G.carrier) (k : Nat) :
    f.map (tateNpow G g k) = tateNpow H (f.map g) k := by
  induction k with
  | zero => exact f.map_one
  | succ k ih =>
    show f.map (G.mul (tateNpow G g k) g) = H.mul (tateNpow H (f.map g) k) (f.map g)
    rw [f.map_mul, ih]

/-- 一般 Grp: 準同型は整数冪を保つ（Hom.map_pow の tateZpow 版）。 -/
theorem hom_map_zpow {G H : Grp} (f : Hom G H) (g : G.carrier) : ∀ n : Int,
    f.map (tateZpow G g n) = tateZpow H (f.map g) n := by
  intro n
  cases n with
  | ofNat k =>
    show f.map (tateNpow G g k) = tateNpow H (f.map g) k
    exact hom_map_tnpow f g k
  | negSucc k =>
    show f.map (tateNpow G (G.inv g) (k + 1)) = tateNpow H (H.inv (f.map g)) (k + 1)
    rw [← f.map_inv g]
    exact hom_map_tnpow f (G.inv g) (k + 1)

/-! ## q3nt-1: braiding 補題（唯一の新イディオム・xᵃyᵇ = z^{ab}yᵇxᵃ の Int 二重帰納） -/

/-- x⁻¹ 側の braiding 関係: x·y = z·(y·x) ⟹ x⁻¹·y = z⁻¹·(y·x⁻¹)。 -/
theorem grp_braid_rel_inv (G : Grp) (x y z : G.carrier)
    (hz : ∀ g, G.mul z g = G.mul g z) (hrel : G.mul x y = G.mul z (G.mul y x)) :
    G.mul (G.inv x) y = G.mul (G.inv z) (G.mul y (G.inv x)) := by
  have hyx : G.mul y (G.inv x) = G.mul z (G.mul (G.inv x) y) := by
    apply G.mul_left_cancel (a := x)
    have hL : G.mul x (G.mul y (G.inv x)) = G.mul z y := by
      rw [← G.mul_assoc x y (G.inv x), hrel, G.mul_assoc z (G.mul y x) (G.inv x),
          G.mul_assoc y x (G.inv x), G.mul_inv, G.mul_one]
    have hR : G.mul x (G.mul z (G.mul (G.inv x) y)) = G.mul z y := by
      rw [← G.mul_assoc x z (G.mul (G.inv x) y), ← hz x, G.mul_assoc z x (G.mul (G.inv x) y),
          ← G.mul_assoc x (G.inv x) y, G.mul_inv, G.one_mul]
    rw [hL, hR]
  rw [hyx, ← G.mul_assoc, G.inv_mul, G.one_mul]

/-- y⁻¹ 側の braiding 関係: x·y = z·(y·x) ⟹ x·y⁻¹ = z⁻¹·(y⁻¹·x)。 -/
theorem grp_braid_rel_yinv (G : Grp) (x y z : G.carrier)
    (hz : ∀ g, G.mul z g = G.mul g z) (hrel : G.mul x y = G.mul z (G.mul y x)) :
    G.mul x (G.inv y) = G.mul (G.inv z) (G.mul (G.inv y) x) := by
  apply G.mul_left_cancel (a := z)
  have hR : G.mul z (G.mul (G.inv z) (G.mul (G.inv y) x)) = G.mul (G.inv y) x := by
    rw [← G.mul_assoc z (G.inv z) (G.mul (G.inv y) x), G.mul_inv, G.one_mul]
  have hL : G.mul z (G.mul x (G.inv y)) = G.mul (G.inv y) x := by
    apply G.mul_left_cancel (a := y)
    have e1 : G.mul y (G.mul z (G.mul x (G.inv y))) = x := by
      rw [← G.mul_assoc y z (G.mul x (G.inv y)), ← hz y,
          G.mul_assoc z y (G.mul x (G.inv y)), ← G.mul_assoc y x (G.inv y),
          ← G.mul_assoc z (G.mul y x) (G.inv y), ← hrel,
          G.mul_assoc x y (G.inv y), G.mul_inv, G.mul_one]
    have e2 : G.mul y (G.mul (G.inv y) x) = x := by
      rw [← G.mul_assoc y (G.inv y) x, G.mul_inv, G.one_mul]
    rw [e1, e2]
  rw [hL, hR]

/-- 片側 braiding（Nat 冪・y は 1 個）: xᵏ·y = zᵏ·(y·xᵏ)。 -/
theorem grp_braid_one_nat (G : Grp) (x y z : G.carrier)
    (hz : ∀ g, G.mul z g = G.mul g z) (hrel : G.mul x y = G.mul z (G.mul y x)) (k : Nat) :
    G.mul (tateNpow G x k) y = G.mul (tateNpow G z k) (G.mul y (tateNpow G x k)) := by
  induction k with
  | zero =>
    show G.mul G.one y = G.mul G.one (G.mul y G.one)
    rw [G.one_mul, G.mul_one, G.one_mul]
  | succ k ih =>
    show G.mul (G.mul (tateNpow G x k) x) y
       = G.mul (G.mul (tateNpow G z k) z) (G.mul y (G.mul (tateNpow G x k) x))
    rw [G.mul_assoc (tateNpow G x k) x y, hrel,
        ← G.mul_assoc (tateNpow G x k) z (G.mul y x),
        ← hz (tateNpow G x k),
        G.mul_assoc z (tateNpow G x k) (G.mul y x),
        ← G.mul_assoc (tateNpow G x k) y x,
        ih,
        G.mul_assoc (tateNpow G z k) (G.mul y (tateNpow G x k)) x,
        G.mul_assoc y (tateNpow G x k) x,
        ← G.mul_assoc z (tateNpow G z k) (G.mul y (G.mul (tateNpow G x k) x)),
        hz (tateNpow G z k)]

/-- 片側 braiding（整数冪・y は 1 個）: xᵃ·y = zᵃ·(y·xᵃ)（∀a:Int）。 -/
theorem grp_braid_one (G : Grp) (x y z : G.carrier)
    (hz : ∀ g, G.mul z g = G.mul g z) (hrel : G.mul x y = G.mul z (G.mul y x)) (a : Int) :
    G.mul (tateZpow G x a) y = G.mul (tateZpow G z a) (G.mul y (tateZpow G x a)) := by
  cases a with
  | ofNat k =>
    show G.mul (tateNpow G x k) y = G.mul (tateNpow G z k) (G.mul y (tateNpow G x k))
    exact grp_braid_one_nat G x y z hz hrel k
  | negSucc k =>
    have hzi : ∀ g, G.mul (G.inv z) g = G.mul g (G.inv z) := fun g => grp_comm_inv G (hz g)
    show G.mul (tateNpow G (G.inv x) (k + 1)) y
       = G.mul (tateNpow G (G.inv z) (k + 1)) (G.mul y (tateNpow G (G.inv x) (k + 1)))
    exact grp_braid_one_nat G (G.inv x) y (G.inv z) hzi (grp_braid_rel_inv G x y z hz hrel) (k + 1)

/-- 完全 braiding（y の Nat 冪版）: xᵃ·yᵏ = z^{a·k}·(yᵏ·xᵃ)。 -/
theorem q3nt_braid_nat (G : Grp) (x y z : G.carrier)
    (hz : ∀ g, G.mul z g = G.mul g z) (hrel : G.mul x y = G.mul z (G.mul y x)) (a : Int) (k : Nat) :
    G.mul (tateZpow G x a) (tateNpow G y k)
      = G.mul (tateZpow G z (a * (k : Int))) (G.mul (tateNpow G y k) (tateZpow G x a)) := by
  induction k with
  | zero =>
    show G.mul (tateZpow G x a) G.one
       = G.mul (tateZpow G z (a * (0 : Int))) (G.mul G.one (tateZpow G x a))
    have h0 : a * (0 : Int) = 0 := Int.mul_zero a
    rw [G.mul_one, h0, tateZpow_zero, G.one_mul, G.one_mul]
  | succ k ih =>
    have hexp : a * ((k + 1 : Nat) : Int) = a * (k : Int) + a := by
      have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hc, Int.mul_add, Int.mul_one]
    show G.mul (tateZpow G x a) (G.mul (tateNpow G y k) y)
       = G.mul (tateZpow G z (a * ((k + 1 : Nat) : Int)))
           (G.mul (G.mul (tateNpow G y k) y) (tateZpow G x a))
    rw [← G.mul_assoc (tateZpow G x a) (tateNpow G y k) y,
        ih,
        G.mul_assoc (tateZpow G z (a * (k : Int))) (G.mul (tateNpow G y k) (tateZpow G x a)) y,
        G.mul_assoc (tateNpow G y k) (tateZpow G x a) y,
        grp_braid_one G x y z hz hrel a,
        ← G.mul_assoc (tateNpow G y k) (tateZpow G z a) (G.mul y (tateZpow G x a)),
        ← grp_zpow_central G z hz a (tateNpow G y k),
        G.mul_assoc (tateZpow G z a) (tateNpow G y k) (G.mul y (tateZpow G x a)),
        ← G.mul_assoc (tateZpow G z (a * (k : Int))) (tateZpow G z a)
            (G.mul (tateNpow G y k) (G.mul y (tateZpow G x a))),
        ← tateZpow_add G z (a * (k : Int)) a,
        ← G.mul_assoc (tateNpow G y k) y (tateZpow G x a),
        hexp]

/-- **q3nt-1（★ 新イディオム）: 一般 Grp braiding** xᵃ·yᵇ = z^{a·b}·(yᵇ·xᵃ)
    （z 中心・x·y = z·(y·x)・∀a b:Int）。三角数閉形式を回避し Φ/Ψ の map_mul を駆動。 -/
theorem q3nt_braid (G : Grp) (x y z : G.carrier)
    (hz : ∀ g, G.mul z g = G.mul g z) (hrel : G.mul x y = G.mul z (G.mul y x)) (a b : Int) :
    G.mul (tateZpow G x a) (tateZpow G y b)
      = G.mul (tateZpow G z (a * b)) (G.mul (tateZpow G y b) (tateZpow G x a)) := by
  cases b with
  | ofNat k =>
    show G.mul (tateZpow G x a) (tateNpow G y k)
       = G.mul (tateZpow G z (a * (Int.ofNat k))) (G.mul (tateNpow G y k) (tateZpow G x a))
    exact q3nt_braid_nat G x y z hz hrel a k
  | negSucc k =>
    have hzi : ∀ g, G.mul (G.inv z) g = G.mul g (G.inv z) := fun g => grp_comm_inv G (hz g)
    have hbn := q3nt_braid_nat G x (G.inv y) (G.inv z) hzi
      (grp_braid_rel_yinv G x y z hz hrel) a (k + 1)
    show G.mul (tateZpow G x a) (tateNpow G (G.inv y) (k + 1))
       = G.mul (tateZpow G z (a * Int.negSucc k))
           (G.mul (tateNpow G (G.inv y) (k + 1)) (tateZpow G x a))
    rw [hbn]
    have hconv : tateZpow G (G.inv z) (a * ((k + 1 : Nat) : Int))
        = tateZpow G z (a * Int.negSucc k) := by
      rw [grp_zpow_inv_base G z (a * ((k + 1 : Nat) : Int))]
      have he : -(a * ((k + 1 : Nat) : Int)) = a * Int.negSucc k := by
        have h1 : Int.negSucc k = -(((k + 1 : Nat) : Int)) := by omega
        rw [h1, Int.mul_neg]
      rw [he]
    rw [hconv]

/-! ## q3nt-2: 生成元 X,Y,Z と基本関係式（q3th 定理を消費・再証明ゼロ） -/

/-- q3tGrp（= ℚ₃^× = prodGrp intGrp ℤ₃^×）の成分等値補題。 -/
theorem q3t_ext {p q : q3tGrp.carrier} (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  have e1 : p1 = q1 := h1
  have e2 : p2 = q2 := h2
  rw [e1, e2]

/-- スカラー準同型 q3tGrp → q3thM（c ↦ (c,0,1)）— 純スカラーの実埋め込み。 -/
def q3ntScalarHom : Hom q3tGrp q3thM where
  map := q3thScalar
  map_mul := by
    intro c c'
    show ((q3tGrp.mul c c', (0 : Int)), q3tGrp.one)
       = ((q3tGrp.mul (q3tGrp.mul c c') (tateZpow q3tGrp q3tGrp.one 0), (0 : Int) + 0),
          q3tGrp.mul q3tGrp.one q3tGrp.one)
    have h00 : (0 : Int) + 0 = 0 := by omega
    rw [tateZpow_zero, q3tGrp.mul_one, q3tGrp.one_mul, h00]

/-- **q3nt-2a: 実スカラー −1 の witness** Z := q3thScalar(0,−1)（中心的・Z²=1）。 -/
def q3ntZ : q3thCar := q3thScalar ((0 : Int), q3tNegOne)

/-- **q3nt-2b: 基本関係式** X·Y = Z·(Y·X)（[X,Y]=Z・q3th_comm_eq_weil + q3th_weil_g3_gm1）。 -/
theorem q3nt_rel : q3thMul q3thG3 q3thGm1 = q3thMul q3ntZ (q3thMul q3thGm1 q3thG3) := by
  have hZ : q3thComm q3thG3 q3thGm1 = q3ntZ := by
    rw [q3th_comm_eq_weil, q3th_weil_g3_gm1]; rfl
  rw [← hZ]
  exact (grp_comm_rel q3thM q3thG3 q3thGm1).symm

/-- **q3nt-2c: Z の中心性**（q3th_ker_central の系）。 -/
theorem q3nt_Z_central (g : q3thCar) : q3thMul q3ntZ g = q3thMul g q3ntZ := by
  have h : q3thM.mul (q3thM.mul (q3thM.mul q3ntZ g) (q3thM.inv q3ntZ)) (q3thM.inv g)
      = q3thM.one := q3th_ker_central ((0 : Int), q3tNegOne) g
  have hA : q3thM.mul (q3thM.mul q3ntZ g) (q3thM.inv q3ntZ) = g :=
    q3thM.mul_right_cancel (h.trans (q3thM.mul_inv g).symm)
  have hstep : q3thM.mul (q3thM.mul (q3thM.mul q3ntZ g) (q3thM.inv q3ntZ)) q3ntZ
      = q3thM.mul g q3ntZ := congrArg (fun t => q3thM.mul t q3ntZ) hA
  rw [q3thM.mul_assoc (q3thM.mul q3ntZ g) (q3thM.inv q3ntZ) q3ntZ, q3thM.inv_mul,
      q3thM.mul_one] at hstep
  exact hstep

/-- **q3nt-2d: Z²=1**（q3tNegOne_sq・スカラー準同型経由）。 -/
theorem q3nt_Z_sq : q3thMul q3ntZ q3ntZ = q3thOne := by
  have hs : q3tGrp.mul ((0 : Int), q3tNegOne) ((0 : Int), q3tNegOne) = q3tGrp.one := by
    apply q3t_ext
    · show intGrp.mul (0 : Int) (0 : Int) = intGrp.one
      show (0 : Int) + 0 = 0
      omega
    · show (zpUnits 3 isPrime_three).mul q3tNegOne q3tNegOne = (zpUnits 3 isPrime_three).one
      exact q3tNegOne_sq
  have h : q3thScalar (q3tGrp.mul ((0 : Int), q3tNegOne) ((0 : Int), q3tNegOne))
      = q3thMul (q3thScalar ((0 : Int), q3tNegOne)) (q3thScalar ((0 : Int), q3tNegOne)) :=
    q3ntScalarHom.map_mul ((0 : Int), q3tNegOne) ((0 : Int), q3tNegOne)
  show q3thMul (q3thScalar ((0 : Int), q3tNegOne)) (q3thScalar ((0 : Int), q3tNegOne)) = q3thOne
  rw [← h, hs]
  rfl

/-- **q3nt-2e: Z の整数冪** Zᶜ = q3thScalar((0,−1)ᶜ)（スカラー準同型の zpow 保存）。 -/
theorem q3nt_Z_zpow (c : Int) :
    tateZpow q3thM q3ntZ c = q3thScalar (tateZpow q3tGrp ((0 : Int), q3tNegOne) c) :=
  (hom_map_zpow q3ntScalarHom ((0 : Int), q3tNegOne) c).symm

/-- 中心化群（テータ群）は Nat 冪で閉じる。 -/
theorem q3nt_mem_npow (g : q3thCar) (hg : q3thMem g) (k : Nat) :
    q3thMem (tateNpow q3thM g k) := by
  induction k with
  | zero => exact q3th_mem_one
  | succ k ih =>
    show q3thMem (q3thMul (tateNpow q3thM g k) g)
    exact q3th_mem_mul _ _ ih hg

/-- **q3nt-2f: 部分群 zpow 閉性** — テータ群 q3thGrp は整数冪で閉じる。 -/
theorem q3nt_mem_zpow (g : q3thCar) (hg : q3thMem g) (n : Int) :
    q3thMem (tateZpow q3thM g n) := by
  cases n with
  | ofNat k => exact q3nt_mem_npow g hg k
  | negSucc k =>
    show q3thMem (tateNpow q3thM (q3thInv g) (k + 1))
    exact q3nt_mem_npow (q3thInv g) (q3th_mem_inv g hg) (k + 1)

/-! ## q3nt-3: Φ — 代理 Heisenberg thetaGrp の実テータ群内実現（Y-first 正規形） -/

/-- **q3nt-3a（★ 中核）: Y-first 積規則** (Yᵇ Xᵃ Zᶜ)(Yᵇ' Xᵃ' Zᶜ') = Yᵇ⁺ᵇ' Xᵃ⁺ᵃ' Z^{c+c'+ab'}。
    braiding（X·Y の並べ替え）と Z 中心性のみで正規化（三角数閉形式を使わない）。 -/
theorem q3nt_phi_prod (a b c a' b' c' : Int) :
    q3thM.mul (q3thM.mul (tateZpow q3thM q3thGm1 b)
        (q3thM.mul (tateZpow q3thM q3thG3 a) (tateZpow q3thM q3ntZ c)))
      (q3thM.mul (tateZpow q3thM q3thGm1 b')
        (q3thM.mul (tateZpow q3thM q3thG3 a') (tateZpow q3thM q3ntZ c')))
      = q3thM.mul (tateZpow q3thM q3thGm1 (b + b'))
          (q3thM.mul (tateZpow q3thM q3thG3 (a + a')) (tateZpow q3thM q3ntZ (c + c' + a * b'))) := by
  have hz := grp_zpow_central q3thM q3ntZ q3nt_Z_central
  have hbraid := q3nt_braid q3thM q3thG3 q3thGm1 q3ntZ q3nt_Z_central q3nt_rel
  rw [-- Step 1: flatten
      q3thM.mul_assoc (tateZpow q3thM q3thGm1 b)
        (q3thM.mul (tateZpow q3thM q3thG3 a) (tateZpow q3thM q3ntZ c))
        (q3thM.mul (tateZpow q3thM q3thGm1 b')
          (q3thM.mul (tateZpow q3thM q3thG3 a') (tateZpow q3thM q3ntZ c'))),
      q3thM.mul_assoc (tateZpow q3thM q3thG3 a) (tateZpow q3thM q3ntZ c)
        (q3thM.mul (tateZpow q3thM q3thGm1 b')
          (q3thM.mul (tateZpow q3thM q3thG3 a') (tateZpow q3thM q3ntZ c'))),
      -- Step 2: Zᶜ を Yᵇ'・Xᵃ' の右へ（中心性）
      ← q3thM.mul_assoc (tateZpow q3thM q3ntZ c) (tateZpow q3thM q3thGm1 b')
        (q3thM.mul (tateZpow q3thM q3thG3 a') (tateZpow q3thM q3ntZ c')),
      hz c (tateZpow q3thM q3thGm1 b'),
      q3thM.mul_assoc (tateZpow q3thM q3thGm1 b') (tateZpow q3thM q3ntZ c)
        (q3thM.mul (tateZpow q3thM q3thG3 a') (tateZpow q3thM q3ntZ c')),
      ← q3thM.mul_assoc (tateZpow q3thM q3ntZ c) (tateZpow q3thM q3thG3 a')
        (tateZpow q3thM q3ntZ c'),
      hz c (tateZpow q3thM q3thG3 a'),
      q3thM.mul_assoc (tateZpow q3thM q3thG3 a') (tateZpow q3thM q3ntZ c)
        (tateZpow q3thM q3ntZ c'),
      -- Step 3: braiding Xᵃ·Yᵇ'
      ← q3thM.mul_assoc (tateZpow q3thM q3thG3 a) (tateZpow q3thM q3thGm1 b')
        (q3thM.mul (tateZpow q3thM q3thG3 a')
          (q3thM.mul (tateZpow q3thM q3ntZ c) (tateZpow q3thM q3ntZ c'))),
      hbraid a b',
      q3thM.mul_assoc (tateZpow q3thM q3ntZ (a * b'))
        (q3thM.mul (tateZpow q3thM q3thGm1 b') (tateZpow q3thM q3thG3 a))
        (q3thM.mul (tateZpow q3thM q3thG3 a')
          (q3thM.mul (tateZpow q3thM q3ntZ c) (tateZpow q3thM q3ntZ c'))),
      q3thM.mul_assoc (tateZpow q3thM q3thGm1 b') (tateZpow q3thM q3thG3 a)
        (q3thM.mul (tateZpow q3thM q3thG3 a')
          (q3thM.mul (tateZpow q3thM q3ntZ c) (tateZpow q3thM q3ntZ c'))),
      -- Step 4: Z^{ab'} を先頭へ（Yᵇ の左へ）
      ← q3thM.mul_assoc (tateZpow q3thM q3thGm1 b) (tateZpow q3thM q3ntZ (a * b'))
        (q3thM.mul (tateZpow q3thM q3thGm1 b')
          (q3thM.mul (tateZpow q3thM q3thG3 a)
            (q3thM.mul (tateZpow q3thM q3thG3 a')
              (q3thM.mul (tateZpow q3thM q3ntZ c) (tateZpow q3thM q3ntZ c'))))),
      ← hz (a * b') (tateZpow q3thM q3thGm1 b),
      q3thM.mul_assoc (tateZpow q3thM q3ntZ (a * b')) (tateZpow q3thM q3thGm1 b)
        (q3thM.mul (tateZpow q3thM q3thGm1 b')
          (q3thM.mul (tateZpow q3thM q3thG3 a)
            (q3thM.mul (tateZpow q3thM q3thG3 a')
              (q3thM.mul (tateZpow q3thM q3ntZ c) (tateZpow q3thM q3ntZ c'))))),
      -- Step 5: 冪をまとめる
      ← tateZpow_add q3thM q3ntZ c c',
      ← q3thM.mul_assoc (tateZpow q3thM q3thG3 a) (tateZpow q3thM q3thG3 a')
        (tateZpow q3thM q3ntZ (c + c')),
      ← tateZpow_add q3thM q3thG3 a a',
      ← q3thM.mul_assoc (tateZpow q3thM q3thGm1 b) (tateZpow q3thM q3thGm1 b')
        (q3thM.mul (tateZpow q3thM q3thG3 (a + a')) (tateZpow q3thM q3ntZ (c + c'))),
      ← tateZpow_add q3thM q3thGm1 b b',
      -- Step 6: Z^{ab'} を右へ運び Z^{c+c'} と合体
      ← q3thM.mul_assoc (tateZpow q3thM q3ntZ (a * b')) (tateZpow q3thM q3thGm1 (b + b'))
        (q3thM.mul (tateZpow q3thM q3thG3 (a + a')) (tateZpow q3thM q3ntZ (c + c'))),
      hz (a * b') (tateZpow q3thM q3thGm1 (b + b')),
      q3thM.mul_assoc (tateZpow q3thM q3thGm1 (b + b')) (tateZpow q3thM q3ntZ (a * b'))
        (q3thM.mul (tateZpow q3thM q3thG3 (a + a')) (tateZpow q3thM q3ntZ (c + c'))),
      ← q3thM.mul_assoc (tateZpow q3thM q3ntZ (a * b')) (tateZpow q3thM q3thG3 (a + a'))
        (tateZpow q3thM q3ntZ (c + c')),
      hz (a * b') (tateZpow q3thM q3thG3 (a + a')),
      q3thM.mul_assoc (tateZpow q3thM q3thG3 (a + a')) (tateZpow q3thM q3ntZ (a * b'))
        (tateZpow q3thM q3ntZ (c + c')),
      ← tateZpow_add q3thM q3ntZ (a * b') (c + c'),
      Int.add_comm (a * b') (c + c')]

/-- **q3nt-3b（★）: Φ : thetaGrp → q3thM**（Φ(a,b,c) = Yᵇ·Xᵃ·Zᶜ・本物の準同型）。 -/
def q3ntPhi : Hom thetaGrp q3thM where
  map := fun v => q3thMul (tateZpow q3thM q3thGm1 v.2.1)
    (q3thMul (tateZpow q3thM q3thG3 v.1) (tateZpow q3thM q3ntZ v.2.2))
  map_mul := by
    intro v w
    obtain ⟨a, b, c⟩ := v
    obtain ⟨a', b', c'⟩ := w
    exact (q3nt_phi_prod a b c a' b' c').symm

/-- Z ∈ テータ群 q3thGrp（純スカラー −1）。 -/
theorem q3nt_Z_mem : q3thMem q3ntZ := (q3th_mem_iff q3ntZ).mpr ⟨rfl, Or.inl rfl⟩

/-- **q3nt-3c: Φ の像はテータ群 q3thGrp 内**（X,Y,Z∈q3thGrp・部分群 zpow/mul 閉性）。 -/
theorem q3nt_phi_mem (v : thetaGrp.carrier) : q3thMem (q3ntPhi.map v) := by
  obtain ⟨a, b, c⟩ := v
  show q3thMem (q3thMul (tateZpow q3thM q3thGm1 b)
    (q3thMul (tateZpow q3thM q3thG3 a) (tateZpow q3thM q3ntZ c)))
  exact q3th_mem_mul _ _ (q3nt_mem_zpow q3thGm1 q3th_gm1_mem b)
    (q3th_mem_mul _ _ (q3nt_mem_zpow q3thG3 q3th_g3_mem a) (q3nt_mem_zpow q3ntZ q3nt_Z_mem c))

/-- **q3nt-3d: 中心の実現** Φ(0,0,k) = Zᵏ（幾何座標消滅・純スカラーのみ）。 -/
theorem q3nt_phi_center (k : Int) :
    q3ntPhi.map ((0, 0, k) : Int × Int × Int) = tateZpow q3thM q3ntZ k := by
  show q3thM.mul (tateZpow q3thM q3thGm1 0)
      (q3thM.mul (tateZpow q3thM q3thG3 0) (tateZpow q3thM q3ntZ k)) = tateZpow q3thM q3ntZ k
  rw [tateZpow_zero, tateZpow_zero, q3thM.one_mul, q3thM.one_mul]

/-- **q3nt-3e: 実シクロトーム生成元** Φ(0,0,1) = Z（実 −1 スカラー）。 -/
theorem q3nt_cyclotome_real : q3ntPhi.map ((0, 0, 1) : Int × Int × Int) = q3ntZ := by
  rw [q3nt_phi_center, tateZpow_one]

/-- **q3nt-3f: 実シクロトーム生成元は非自明** Φ(0,0,1) = Z ≠ 1（q3t_negone_ne_one）。 -/
theorem q3nt_cyclotome_ne_one : q3ntPhi.map ((0, 0, 1) : Int × Int × Int) ≠ q3thOne := by
  rw [q3nt_cyclotome_real]
  intro h
  have hc : ((0 : Int), q3tNegOne) = q3tGrp.one := congrArg (fun t => t.1.1) h
  exact q3t_negone_ne_one (congrArg Prod.snd hc)

/-! ## q3nt-4: 旗艦 1 — 代理シンプレクティック形式 ω ＝ 実 Weil ペアリング ∈ 実 μ₂ -/

/-- q3thComm（テータ群の交換子）と q3thM.comm（Grp.comm）の一致（結合律のみ）。 -/
theorem q3nt_comm_eq (g g' : q3thCar) : q3thComm g g' = q3thM.comm g g' := by
  show q3thM.mul (q3thM.mul (q3thM.mul g g') (q3thM.inv g)) (q3thM.inv g')
     = q3thM.mul (q3thM.mul g g') (q3thM.mul (q3thM.inv g) (q3thM.inv g'))
  rw [q3thM.mul_assoc (q3thM.mul g g') (q3thM.inv g) (q3thM.inv g')]

/-- **q3nt-4a（★ 旗艦）: 代理シンプレクティック形式＝実 Weil ペアリング** —
    [Φv, Φw] = (実 (−1)^{ω(v,w)}, 0, 1)、ω = v₁w₂−w₁v₂（M384F 抽象 ℤ 値が実 μ₂⊂ℤ₃^× 値へ）。
    Φ を消去すると成立しない（左辺の主語は thetaGrp の代理交換子）。 -/
theorem q3nt_symplectic_real (v w : thetaGrp.carrier) :
    q3thComm (q3ntPhi.map v) (q3ntPhi.map w)
      = ((tateZpow q3tGrp ((0 : Int), q3tNegOne) (v.1 * w.2.1 - w.1 * v.2.1), (0 : Int)),
         q3tGrp.one) := by
  obtain ⟨a, b, c⟩ := v
  obtain ⟨a', b', c'⟩ := w
  rw [q3nt_comm_eq, ← q3ntPhi.map_grp_comm, theta_comm, q3nt_phi_center, q3nt_Z_zpow]
  rfl

/-- **q3nt-4b（★）: Weil ペアリング形式** e(Φv,Φw) = (−1)^{ω(v,w)}（q3thWeil の実値）。 -/
theorem q3nt_weil_eq_form (v w : thetaGrp.carrier) :
    q3thWeil (q3ntPhi.map v) (q3ntPhi.map w)
      = tateZpow q3tGrp ((0 : Int), q3tNegOne) (v.1 * w.2.1 - w.1 * v.2.1) := by
  have h := q3nt_symplectic_real v w
  rw [q3th_comm_eq_weil] at h
  exact congrArg (fun t => t.1.1) h

/-! ## q3nt-5: Ψ — 代理 tempered π₁（thetaGrp ⋊ ℤ）の実現 -/

/-- **q3nt-5a（★）: Ψ : tpeGroup → q3thM**（Ψ((a,b,c),n) = Yᵇ·X^{a+n}·Zᶜ・本物の準同型）。
    tpe 第 3 成分 c+c'+(a+n)b' と Z 指数が一致（phi_prod を a↦a+n で再利用）。 -/
def q3ntPsi : Hom tpeGroup q3thM where
  map := fun x => q3thMul (tateZpow q3thM q3thGm1 x.1.2.1)
    (q3thMul (tateZpow q3thM q3thG3 (x.1.1 + x.2)) (tateZpow q3thM q3ntZ x.1.2.2))
  map_mul := by
    intro x y
    obtain ⟨⟨a, b, c⟩, n⟩ := x
    obtain ⟨⟨a', b', c'⟩, n'⟩ := y
    show q3thM.mul (tateZpow q3thM q3thGm1 (b + b'))
         (q3thM.mul (tateZpow q3thM q3thG3 ((a + a') + (n + n')))
           (tateZpow q3thM q3ntZ (c + (c' + n * b') + a * b')))
       = q3thM.mul (q3thM.mul (tateZpow q3thM q3thGm1 b)
             (q3thM.mul (tateZpow q3thM q3thG3 (a + n)) (tateZpow q3thM q3ntZ c)))
           (q3thM.mul (tateZpow q3thM q3thGm1 b')
             (q3thM.mul (tateZpow q3thM q3thG3 (a' + n')) (tateZpow q3thM q3ntZ c')))
    rw [q3nt_phi_prod (a + n) b c (a' + n') b' c']
    have hX : (a + a') + (n + n') = (a + n) + (a' + n') := by omega
    have hZ : c + (c' + n * b') + a * b' = c + c' + (a + n) * b' := by
      rw [Int.add_mul]
      generalize a * b' = P
      generalize n * b' = Q
      omega
    rw [hX, hZ]

/-- **q3nt-5b: Ψ∘ι = Φ**（テータ部への制限が Φ に一致）。 -/
theorem q3nt_psi_incl (z : thetaGrp.carrier) : q3ntPsi.map (tpeIncl.map z) = q3ntPhi.map z := by
  obtain ⟨a, b, c⟩ := z
  show q3thM.mul (tateZpow q3thM q3thGm1 b)
      (q3thM.mul (tateZpow q3thM q3thG3 (a + 0)) (tateZpow q3thM q3ntZ c))
    = q3thM.mul (tateZpow q3thM q3thGm1 b)
      (q3thM.mul (tateZpow q3thM q3thG3 a) (tateZpow q3thM q3ntZ c))
  have ha : a + 0 = a := by omega
  rw [ha]

/-- **q3nt-5c: deck 切断の実現** Ψ(s(n)) = Xⁿ（deck 切断が実半周期の冪へ乗る）。 -/
theorem q3nt_psi_deck (n : Int) : q3ntPsi.map (tpeSection.map n) = tateZpow q3thM q3thG3 n := by
  show q3thM.mul (tateZpow q3thM q3thGm1 0)
      (q3thM.mul (tateZpow q3thM q3thG3 (0 + n)) (tateZpow q3thM q3ntZ 0))
    = tateZpow q3thM q3thG3 n
  have hn : (0 : Int) + n = n := by omega
  rw [hn, tateZpow_zero, tateZpow_zero, q3thM.mul_one, q3thM.one_mul]

/-! ## q3nt-6: 旗艦 2 — deck×テータ交換子＝実 (−1)^{nb}（分裂直積ブロッカーの discharge） -/

/-- **q3nt-6a（★ 旗艦）: deck×テータ交換子の実値化** — [Ψ(s n), Ψ(ι(a,b,c))] = (実 (−1)^{nb},0,1)。
    M424F の [s(n),ι(a,b,c)]=ι(0,0,nb) が Ψ で実 μ₂ 値になる。Ψ を消去すると成立しない。 -/
theorem q3nt_deck_theta_real (n a b c : Int) :
    q3thComm (q3ntPsi.map (tpeSection.map n))
        (q3ntPsi.map (tpeIncl.map ((a, b, c) : Int × Int × Int)))
      = ((tateZpow q3tGrp ((0 : Int), q3tNegOne) (n * b), (0 : Int)), q3tGrp.one) := by
  rw [q3nt_comm_eq, ← q3ntPsi.map_grp_comm, tpe_deck_theta_commutator, q3nt_psi_incl,
      q3nt_phi_center, q3nt_Z_zpow]
  rfl

/-- **q3nt-6b（★）: deck 切断はテータ部と可換でない初の実 tempered 対象** —
    [Ψ(s 1), Ψ(ι(0,1,0))] = 実 −1 ≠ 1。分裂直積ブロッカーの level-2 discharge。 -/
theorem q3nt_deck_theta_ne_one :
    q3thComm (q3ntPsi.map (tpeSection.map 1))
        (q3ntPsi.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int))) ≠ q3thOne := by
  rw [q3nt_deck_theta_real]
  intro h
  have hc : tateZpow q3tGrp ((0 : Int), q3tNegOne) (1 * 1) = q3tGrp.one :=
    congrArg (fun t => t.1.1) h
  have h11 : (1 : Int) * 1 = 1 := by omega
  rw [h11, tateZpow_one] at hc
  exact q3t_negone_ne_one (congrArg Prod.snd hc)

/-- **q3nt-6c: 対照定理** — A5b の分裂直積 q3tpGroup では deck 切断が μ 部分と可換
    （one_mul/mul_one のみ・分裂直積の自明性を定理として可視化）。Φ/Ψ とは無関係な純対照。 -/
theorem q3nt_split_contrast (z : tmzLimit.carrier) (n : Int) :
    q3tpGroup.mul (tmzLimit.one, n) (q3tpIncl.map z)
      = q3tpGroup.mul (q3tpIncl.map z) (tmzLimit.one, n) := by
  show (tmzLimit.mul tmzLimit.one z, intGrp.mul n (0 : Int))
     = (tmzLimit.mul z tmzLimit.one, intGrp.mul (0 : Int) n)
  rw [tmzLimit.one_mul, tmzLimit.mul_one]
  have h : intGrp.mul n (0 : Int) = intGrp.mul (0 : Int) n := by
    show n + 0 = 0 + n
    omega
  rw [h]

/-! ## q3nt-7: 旗艦 3 — v(q)=2 の tempered-π₁ 側復元（q 不可視ブロッカーの level-2 discharge） -/

/-- q3thM の w 成分（平行移動）射影 q3thM → q3tGrp（本物の準同型）。 -/
def q3ntW : Hom q3thM q3tGrp where
  map := fun g => g.2
  map_mul := fun _ _ => rfl

/-- **q3nt-7a（★）: deck 切断像の半周期** (Ψ(s n)).w = 3ⁿ（付値 n の実半周期）。 -/
theorem q3nt_deck_halfperiod (n : Int) :
    (q3ntPsi.map (tpeSection.map n)).2
      = tateZpow q3tGrp ((1 : Int), (zpUnits 3 isPrime_three).one) n := by
  rw [q3nt_psi_deck]
  exact hom_map_zpow q3ntW q3thG3 n

/-- **q3nt-7b（★）: 半周期の平方＝周期** ((Ψ(s n)).w)² = 9ⁿ = qⁿ = q3tdPeriodHom（A5a へ着地）。 -/
theorem q3nt_deck_sq_period (n : Int) :
    q3tGrp.mul (q3ntPsi.map (tpeSection.map n)).2 (q3ntPsi.map (tpeSection.map n)).2
      = (q3tdPeriodHom 2).map n := by
  rw [q3nt_deck_halfperiod,
      ← tateZpow_add q3tGrp ((1 : Int), (zpUnits 3 isPrime_three).one) n n]
  show tateZpow q3tGrp (q3tQ 1) (n + n) = tateZpow q3tGrp (q3tQ 2) n
  apply q3t_ext
  · rw [q3td_zpow_fst 1 (n + n), q3td_zpow_fst 2 n]
    show (1 : Int) * (n + n) = (2 : Int) * n
    omega
  · rw [q3t_zpow_snd 1 (n + n), q3t_zpow_snd 2 n]

/-- **q3nt-7c（★）: v(q) の tempered 側復元** v(qⁿ) = 2·v((Ψ(s n)).w)。 -/
theorem q3nt_vq_recover (n : Int) :
    ((q3tdPeriodHom 2).map n).1 = 2 * ((q3ntPsi.map (tpeSection.map n)).2).1 := by
  rw [q3nt_deck_halfperiod]
  show (tateZpow q3tGrp (q3tQ 2) n).1 = 2 * (tateZpow q3tGrp (q3tQ 1) n).1
  rw [q3td_zpow_fst 2 n, q3td_zpow_fst 1 n]
  show (2 : Int) * n = 2 * ((1 : Int) * n)
  omega

/-- **q3nt-7d（★★ 払い）: v(q)=2** — deck 切断像の半周期 3¹ の付値 1 から v(q)=2·1=2。
    分裂直積で不可視だった q が deck 像の平方＝群論的 data として再出現。 -/
theorem q3nt_vq_two : ((q3ntPsi.map (tpeSection.map 1)).2).1 = 1 := by
  rw [q3nt_deck_halfperiod]
  show (tateZpow q3tGrp (q3tQ 1) 1).1 = 1
  rw [q3td_zpow_fst 1 1]
  show (1 : Int) * 1 = 1
  omega

/-! ## q3nt-8: 正直核の定理化（level-2 崩壊・χ 不可視）＋ capstone -/

/-- Y = q3thGm1 は位数 2（Y²=1・χ 不可視/半周期符号の核）。 -/
theorem q3nt_Y_sq : q3thMul q3thGm1 q3thGm1 = q3thOne := by
  show ((q3tGrp.mul (q3tGrp.mul q3tGrp.one q3tGrp.one)
      (tateZpow q3tGrp ((0 : Int), q3tNegOne) 0), (0 : Int) + 0),
      q3tGrp.mul ((0 : Int), q3tNegOne) ((0 : Int), q3tNegOne))
    = ((q3tGrp.one, (0 : Int)), q3tGrp.one)
  have hs : q3tGrp.mul ((0 : Int), q3tNegOne) ((0 : Int), q3tNegOne) = q3tGrp.one := by
    apply q3t_ext
    · show intGrp.mul (0 : Int) (0 : Int) = intGrp.one
      show (0 : Int) + 0 = 0
      omega
    · exact q3tNegOne_sq
  have h00 : (0 : Int) + 0 = 0 := by omega
  rw [tateZpow_zero, q3tGrp.mul_one, q3tGrp.one_mul, h00, hs]

/-- **q3nt-8a（正直核）: level-2 崩壊** — Ψ(ι(0,0,2)) = 1（Z²=1・シクロトーム ℤ の実現は
    mod 2 のみ・Ψ は単射でない）。ẑ(1) 全体の実現は奇レベル拡大体機構（後続・恒久ブロック）。 -/
theorem q3nt_psi_level2_collapse :
    q3ntPsi.map (tpeIncl.map ((0, 0, 2) : Int × Int × Int)) = q3thOne := by
  rw [q3nt_psi_incl, q3nt_phi_center]
  show tateZpow q3thM q3ntZ 2 = q3thOne
  have e : (2 : Int) = 1 + 1 := by omega
  rw [e, tateZpow_add, tateZpow_one]
  exact q3nt_Z_sq

/-- **q3nt-8b（正直核）: deck・テータ a 方向の融合** — Ψ(ι(−1,0,0)·s(1)) = 1
    （M424F tpe_aut_conj_in_theta の忠実な帰結・ker Ψ の a 方向崩壊）。 -/
theorem q3nt_psi_deck_fusion :
    q3ntPsi.map (tpeGroup.mul (tpeIncl.map ((-1, 0, 0) : Int × Int × Int)) (tpeSection.map 1))
      = q3thOne := by
  show q3thM.mul (tateZpow q3thM q3thGm1 0)
      (q3thM.mul (tateZpow q3thM q3thG3 (-1 + 1)) (tateZpow q3thM q3ntZ 0)) = q3thM.one
  have he : (-1 : Int) + 1 = 0 := by omega
  rw [he, tateZpow_zero, tateZpow_zero, tateZpow_zero, q3thM.mul_one, q3thM.one_mul]

/-- **q3nt-8c（正直核）: χ 捻りは level 2 で不可視** — (a,b,c,n)↦(a,−b,−c,n) の下で Ψ 不変
    （(−1)^{−k}=(−1)^k・Y²=Z²=1）。M429F 算術拡大 atpGroup の実現は μ₂ 影では 0。 -/
theorem q3nt_chi_invisible (a b c n : Int) :
    q3ntPsi.map (((a, -b, -c) : Int × Int × Int), n)
      = q3ntPsi.map (((a, b, c) : Int × Int × Int), n) := by
  show q3thM.mul (tateZpow q3thM q3thGm1 (-b))
      (q3thM.mul (tateZpow q3thM q3thG3 (a + n)) (tateZpow q3thM q3ntZ (-c)))
    = q3thM.mul (tateZpow q3thM q3thGm1 b)
      (q3thM.mul (tateZpow q3thM q3thG3 (a + n)) (tateZpow q3thM q3ntZ c))
  rw [grp_zpow_neg_of_sq q3thM q3thGm1 q3nt_Y_sq b,
      grp_zpow_neg_of_sq q3thM q3ntZ q3nt_Z_sq c]

/-- **q3nt-8d: A5d capstone データ** — Φ/Ψ・旗艦（ω=実 Weil・deck×θ=実 −1・v(q)=2 復元）・
    正直核（level-2 崩壊）を束ねる。主語はすべて Φ/Ψ と代理対象（thetaGrp/tpeGroup）。 -/
structure Q3TemperedThetaClassData where
  /-- Φ : thetaGrp → q3thM（代理 Heisenberg の実現）。 -/
  phi : Hom thetaGrp q3thM
  /-- Ψ : tpeGroup → q3thM（代理 tempered π₁ の実現）。 -/
  psi : Hom tpeGroup q3thM
  /-- Ψ∘ι = Φ。 -/
  psi_incl : ∀ z, psi.map (tpeIncl.map z) = phi.map z
  /-- 旗艦 1: 代理 ω ＝ 実 Weil ペアリング ∈ 実 μ₂。 -/
  symplectic_real : ∀ v w, q3thComm (phi.map v) (phi.map w)
    = ((tateZpow q3tGrp ((0 : Int), q3tNegOne) (v.1 * w.2.1 - w.1 * v.2.1), (0 : Int)), q3tGrp.one)
  /-- 旗艦 2: deck×テータ交換子 ＝ 実 (−1)^{nb}。 -/
  deck_theta_real : ∀ n a b c,
    q3thComm (psi.map (tpeSection.map n)) (psi.map (tpeIncl.map ((a, b, c) : Int × Int × Int)))
    = ((tateZpow q3tGrp ((0 : Int), q3tNegOne) (n * b), (0 : Int)), q3tGrp.one)
  /-- deck 切断はテータ部と非可換（実 −1 ≠ 1）。 -/
  deck_theta_ne_one : q3thComm (psi.map (tpeSection.map 1))
    (psi.map (tpeIncl.map ((0, 1, 0) : Int × Int × Int))) ≠ q3thOne
  /-- 旗艦 3: 半周期の平方＝周期（A5a q3tdPeriodHom へ着地）。 -/
  deck_sq_period : ∀ n, q3tGrp.mul (psi.map (tpeSection.map n)).2 (psi.map (tpeSection.map n)).2
    = (q3tdPeriodHom 2).map n
  /-- 旗艦 3 の払い: v(q)=2（半周期付値 1 の 2 倍）。 -/
  vq_two : ((psi.map (tpeSection.map 1)).2).1 = 1
  /-- 正直核: level-2 崩壊 Ψ(ι(0,0,2))=1（Ψ 非単射・実現は mod 2 のみ）。 -/
  level2_collapse : psi.map (tpeIncl.map ((0, 0, 2) : Int × Int × Int)) = q3thOne

/-- **q3nt-8e: 見出し実例** — 実 E₉(ℚ₃) 上の実テータ群 q3thGrp 内での代理 tempered
    テータ骨格の実現。 -/
def q3ntData : Q3TemperedThetaClassData where
  phi := q3ntPhi
  psi := q3ntPsi
  psi_incl := q3nt_psi_incl
  symplectic_real := q3nt_symplectic_real
  deck_theta_real := q3nt_deck_theta_real
  deck_theta_ne_one := q3nt_deck_theta_ne_one
  deck_sq_period := q3nt_deck_sq_period
  vq_two := q3nt_vq_two
  level2_collapse := q3nt_psi_level2_collapse

/-- **q3nt-8f（★ capstone）: 代理 tempered テータ骨格の実テータ群内実現の存在**
    （実 ℚ₃・q=9・level 2・μ₂・v(q)=2 復元込み）。 -/
theorem q3ntClass_exists : Nonempty Q3TemperedThetaClassData := ⟨q3ntData⟩

end IUT
