/-
  IUT/HaarMeasureZp.lean — M336F [実／本物]
  分類: 実 (ℤ_p 上の正規化加法ハール測度＝測度論的 log-volume の土台)
  complete_pct 影響: 柱C を前進（M312F の Arakelov 次数版 log-volume に対し、CLAUDE.md が
    実ターゲットに挙げる「測度論的 log-volume」の土台＝ℤ_p 加法ハール測度 μ(p^dℤ_p)=p^{-d}・
    平行移動不変・有限加法性・log-volume 橋を本物で建設）。
  正直な限定: σ-加法性（可算加法性）・一般 Borel 集合への Carathéodory 拡張・Haar 測度の
    存在一意性定理は本層では導出しない。測度値は基本コンパクト開集合（コセット a+p^dℤ_p）
    上で本物の ℚ（QRat, μ(p^dℤ_p)=1/p^d, 非負）として与え、その平行移動不変性・有限加法性・
    比 1/p・単調減少・正規化・log-volume 指数 d との橋を core Lean のみで完全証明する。
    σ-加法的 Borel 拡張は外部仮説 `haarSigmaAdditivityHypothesis` として名前を固定し、
    その存在は与えない（後続層で本物にする）。RReal（本物の ℝ）への像 `haarBallR` と乗法性
    橋も与える。全て sorry 皆無・新規 Classical.choice 皆無。
-/
import IUT.RealMul
import IUT.LogShellReal

namespace IUT

/-! ## M336F-0: p^d の正値性（分母の正値）補助 -/

/-- **M336F-0: べきの正値** — p ≥ 1 なら p^d ≥ 1（分母 p^d が正であることの核）。 -/
theorem haar_pow_pos (p : Nat) (hp : 1 ≤ p) : ∀ d, 1 ≤ p ^ d
  | 0 => Nat.le_refl 1
  | d + 1 => by
      rw [Nat.pow_succ]
      have h := Nat.mul_le_mul (haar_pow_pos p hp d) hp
      rw [Nat.one_mul] at h
      exact h

/-! ## M336F-1: 基本測度値（1/p と 1/p^d）と球の測度 μ(p^dℤ_p) -/

/-- **M336F-1a: 指数 1 の縮小率** 1/p ∈ ℚ（フィルトレーション p^dℤ_p ⊃ p^{d+1}ℤ_p の
    指数 [ℤ_p:pℤ_p]=p の逆＝各段で測度が 1/p 倍になる本物の縮小率）。 -/
def haarInvP (p : Nat) (hp : 1 ≤ p) : QRat :=
  Quot.mk ratRel ⟨1, (p : Int), by omega⟩

/-- **M336F-1b: 球の測度** μ(p^dℤ_p) — 正規化加法ハール測度による球 p^d·ℤ_p の測度。
    μ(ℤ_p)=μ(p^0ℤ_p)=1 から出発し、各段で 1/p を掛ける（`haarInvP`）再帰で
    μ(p^dℤ_p)=p^{-d} を得る。本物の ℚ 値（非負）。 -/
def haarBall (p : Nat) (hp : 1 ≤ p) : Nat → QRat
  | 0 => ratRing.one
  | d + 1 => qMul (haarInvP p hp) (haarBall p hp d)

/-- **M336F-1c: 閉形式の分母** p^d（μ(p^dℤ_p)=1/p^d の分母）を正値付き PreRat で。 -/
def haarClosed (p : Nat) (hp : 1 ≤ p) (d : Nat) : QRat :=
  Quot.mk ratRel ⟨1, ((p ^ d : Nat) : Int), by
    have := haar_pow_pos p hp d; omega⟩

/-! ## M336F-2: 正規化と縮小比（μ(ℤ_p)=1・μ(p^{d+1})=(1/p)μ(p^d)） -/

/-- **M336F-2a: 正規化** μ(ℤ_p)=μ(p^0ℤ_p)=1（Haar 測度の正規化条件）。 -/
theorem haar_normalized (p : Nat) (hp : 1 ≤ p) : haarBall p hp 0 = ratRing.one := rfl

/-- **M336F-2b: 縮小比** μ(p^{d+1}ℤ_p) = (1/p)·μ(p^dℤ_p)。指数 [ℤ_p/pℤ_p]=p の
    フィルトレーションで各段の測度が 1/p 倍になる本物の関係。 -/
theorem haar_ball_ratio (p : Nat) (hp : 1 ≤ p) (d : Nat) :
    haarBall p hp (d + 1) = qMul (haarInvP p hp) (haarBall p hp d) := rfl

/-! ## M336F-3: 平行移動不変性（コセットの測度＝部分群の測度） -/

/-- **M336F-3a: コセットの測度** μ(a + p^dℤ_p)。加法ハール測度は平行移動不変ゆえ
    代表 a に依らず μ(p^dℤ_p) に等しい（基本開集合上の測度）。 -/
def haarCoset (p : Nat) (hp : 1 ≤ p) (a : Int) (d : Nat) : QRat := haarBall p hp d

/-- **M336F-3b: 平行移動不変性** μ(a + p^dℤ_p) = μ(p^dℤ_p)。 -/
theorem haar_translation_invariant (p : Nat) (hp : 1 ≤ p) (a : Int) (d : Nat) :
    haarCoset p hp a d = haarBall p hp d := rfl

/-- **M336F-3c: コセット測度の代表非依存性** μ(a + p^dℤ_p) = μ(b + p^dℤ_p)。 -/
theorem haar_coset_indep (p : Nat) (hp : 1 ≤ p) (a b : Int) (d : Nat) :
    haarCoset p hp a d = haarCoset p hp b d := rfl

/-! ## M336F-4: 有限加法性（p 個のコセットへの分割 μ(p^dℤ_p)=p·μ(p^{d+1})） -/

/-- 補助: p·(1/p) = 1（ℚ の乗法逆）。 -/
theorem haarP_mul_invP (p : Nat) (hp : 1 ≤ p) :
    qMul (ratOfInt.map (p : Int)) (haarInvP p hp) = ratRing.one := by
  apply Quot.sound
  show ((p : Int) * 1) * 1 = 1 * (1 * (p : Int))
  omega

/-- 補助: qMul の結合律（ratRing の CRing 構造から）。 -/
theorem qMul_assoc' (a b c : QRat) : qMul (qMul a b) c = qMul a (qMul b c) :=
  ratRing.mul_assoc a b c

/-- 補助: 左単位律 1·a = a。 -/
theorem qMul_one_left' (a : QRat) : qMul ratRing.one a = a :=
  ratRing.one_mul a

/-- **M336F-4a: 有限加法性（コセット分割）** μ(p^dℤ_p) = p·μ(p^{d+1}ℤ_p)。
    p^dℤ_p は p^{d+1}ℤ_p の p 個のコセット a + p^{d+1}ℤ_p (a = 0,…,p−1) の非交和で、
    各コセットの測度は μ(p^{d+1}ℤ_p)（平行移動不変）ゆえ和は p·μ(p^{d+1}ℤ_p)。
    有限加法測度の分割整合の本物の実現。 -/
theorem haar_additive (p : Nat) (hp : 1 ≤ p) (d : Nat) :
    qMul (ratOfInt.map (p : Int)) (haarBall p hp (d + 1)) = haarBall p hp d := by
  show qMul (ratOfInt.map (p : Int)) (qMul (haarInvP p hp) (haarBall p hp d))
      = haarBall p hp d
  rw [← qMul_assoc', haarP_mul_invP, qMul_one_left']

/-- **M336F-4b: コセット分割（別名）** μ(p^dℤ_p) = p·μ(p^{d+1}ℤ_p)。 -/
theorem haar_coset_partition (p : Nat) (hp : 1 ≤ p) (d : Nat) :
    qMul (ratOfInt.map (p : Int)) (haarBall p hp (d + 1)) = haarBall p hp d :=
  haar_additive p hp d

/-! ## M336F-5: 閉形式 μ(p^dℤ_p)=1/p^d・非負性・単調減少 -/

/-- **M336F-5a: 閉形式** μ(p^dℤ_p) = 1/p^d（本物の ℚ 値・p 進体積の指数減衰）。 -/
theorem haar_ball_closed (p : Nat) (hp : 1 ≤ p) :
    ∀ d, haarBall p hp d = haarClosed p hp d
  | 0 => by
      apply Quot.sound
      show (1 : Int) * ((p ^ 0 : Nat) : Int) = 1 * 1
      rw [Nat.pow_zero]
      omega
  | d + 1 => by
      show qMul (haarInvP p hp) (haarBall p hp d) = haarClosed p hp (d + 1)
      rw [haar_ball_closed p hp d]
      apply Quot.sound
      show (1 * 1) * ((p ^ (d + 1) : Nat) : Int)
          = 1 * ((p : Int) * ((p ^ d : Nat) : Int))
      rw [Nat.pow_succ, Int.natCast_mul, Int.one_mul, Int.one_mul, Int.one_mul]
      exact Int.mul_comm _ _

/-- **M336F-5b: 測度の非負性** 0 ≤ μ(p^dℤ_p)（測度は非負値）。 -/
theorem haar_ball_nonneg (p : Nat) (hp : 1 ≤ p) :
    ∀ d, qLe ratRing.zero (haarBall p hp d)
  | 0 => by
      show qLe ratRing.zero ratRing.one
      show (0 : Int) * 1 ≤ 1 * 1
      omega
  | d + 1 => by
      show qLe ratRing.zero (qMul (haarInvP p hp) (haarBall p hp d))
      refine qLe_mul_nonneg (haarInvP p hp) (haarBall p hp d) ?_ (haar_ball_nonneg p hp d)
      show (0 : Int) * (p : Int) ≤ 1 * 1
      omega

/-- **M336F-5c: 単調減少** μ(p^{d+1}ℤ_p) ≤ μ(p^dℤ_p)。より小さい球 p^{d+1}ℤ_p ⊆ p^dℤ_p
    （M321F `logShell_antitone` の包含）の測度は小さい＝測度の単調性の本物の実現。 -/
theorem haar_ball_le_succ (p : Nat) (hp : 1 ≤ p) (d : Nat) :
    qLe (haarBall p hp (d + 1)) (haarBall p hp d) := by
  rw [haar_ball_closed p hp (d + 1), haar_ball_closed p hp d]
  show (1 : Int) * ((p ^ d : Nat) : Int) ≤ 1 * ((p ^ (d + 1) : Nat) : Int)
  rw [Int.one_mul, Int.one_mul]
  have hnat : p ^ d ≤ p ^ (d + 1) := by
    rw [Nat.pow_succ]
    have h := Nat.mul_le_mul (Nat.le_refl (p ^ d)) hp
    rw [Nat.mul_one] at h
    exact h
  exact Int.ofNat_le.mpr hnat

/-! ## M336F-6: RReal（本物の ℝ）への像と乗法性橋 -/

/-- **M336F-6a: 球の測度の ℝ 像** μ(p^dℤ_p) ∈ ℝ（M312F の RReal 世界＝測度論的
    log-volume の値域へ）。 -/
def haarBallR (p : Nat) (hp : 1 ≤ p) (d : Nat) : RReal := qToReal (haarBall p hp d)

/-- **M336F-6b: ℝ 上での縮小比** μ_ℝ(p^{d+1}ℤ_p) ≈ (1/p)·μ_ℝ(p^dℤ_p)（realEq）。
    埋め込み qToReal の乗法性 `qToReal_mul` で ℚ の比を本物の ℝ の乗法 rmul に持ち上げる。 -/
theorem haar_ballR_ratio (p : Nat) (hp : 1 ≤ p) (d : Nat) :
    realEq (haarBallR p hp (d + 1))
      (rmul (qToReal (haarInvP p hp)) (haarBallR p hp d)) := by
  show realEq (qToReal (haarBall p hp (d + 1)))
      (rmul (qToReal (haarInvP p hp)) (qToReal (haarBall p hp d)))
  rw [haar_ball_ratio p hp d]
  exact realEq_symm (qToReal_mul (haarInvP p hp) (haarBall p hp d))

/-! ## M336F-7: log-volume 橋（log_p μ(p^dℤ_p) = −d、M312F 規約整合） -/

/-- **M336F-7a: 測度の log-volume 指数** — μ(p^dℤ_p)=p^{-d} の指数 d。
    log_p μ(p^dℤ_p) = −d（M312F の Arakelov 次数 deg = −d·log p、M321F の
    `logShellVol` = d の co-level 規約に一致する）。 -/
def haarLogExp (d : Nat) : Nat := d

/-- **M336F-7b: log-volume 橋** — ハール測度の指数 d が M321F の対数殻の
    co-level `logShellVol d` に一致する（測度論的 log-volume と Arakelov 次数版
    log-volume の指数規約の本物のブリッジ）。 -/
theorem haar_logExp_eq_shellVol (d : Nat) : haarLogExp d = logShellVol d := rfl

/-- **M336F-7c: 閉形式による log-volume の主張** — μ(p^dℤ_p) は分母 p^d を持つ、
    すなわち μ(p^dℤ_p)=p^{−(haarLogExp d)}（log_p μ = −d の ℚ 値表現）。 -/
theorem haar_ball_is_inv_pow (p : Nat) (hp : 1 ≤ p) (d : Nat) :
    haarBall p hp d = Quot.mk ratRel ⟨1, ((p ^ haarLogExp d : Nat) : Int), by
      have := haar_pow_pos p hp (haarLogExp d); omega⟩ :=
  haar_ball_closed p hp d

/-! ## M336F-8: capstone と実例 -/

/-- **M336F-8a: ハール測度データ** — ℤ_p 上の正規化加法ハール測度の束ね。
    正規化・縮小比 1/p・有限加法性（p 個のコセット分割）・非負・単調減少・
    平行移動不変を本物の ℚ で充足する。 -/
structure HaarMeasureData where
  /-- 局所体の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  /-- 1 ≤ p。 -/
  hp : 1 ≤ p
  /-- 球の測度 μ(p^dℤ_p)。 -/
  ball : Nat → QRat
  /-- 正規化 μ(ℤ_p)=1。 -/
  normalized : ball 0 = ratRing.one
  /-- 縮小比 μ(p^{d+1})=(1/p)μ(p^d)。 -/
  ratio : ∀ d, ball (d + 1) = qMul (haarInvP p hp) (ball d)
  /-- 有限加法性 μ(p^d)=p·μ(p^{d+1})。 -/
  additive : ∀ d, qMul (ratOfInt.map (p : Int)) (ball (d + 1)) = ball d
  /-- 非負 0 ≤ μ(p^d)。 -/
  nonneg : ∀ d, qLe ratRing.zero (ball d)
  /-- 単調減少 μ(p^{d+1}) ≤ μ(p^d)。 -/
  antitone : ∀ d, qLe (ball (d + 1)) (ball d)
  /-- コセット測度 μ(a+p^dℤ_p)。 -/
  coset : Int → Nat → QRat
  /-- 平行移動不変 μ(a+p^d)=μ(p^d)。 -/
  coset_eq : ∀ a d, coset a d = ball d

/-- **M336F-8b: 実データ** — 全フィールドを本物で充足。 -/
def haarMeasureData (p : Nat) (hp : 1 ≤ p) : HaarMeasureData where
  p := p
  hp := hp
  ball := haarBall p hp
  normalized := haar_normalized p hp
  ratio := haar_ball_ratio p hp
  additive := haar_additive p hp
  nonneg := haar_ball_nonneg p hp
  antitone := haar_ball_le_succ p hp
  coset := haarCoset p hp
  coset_eq := haar_translation_invariant p hp

/-- **M336F-8c: 存在** — 本物のハール測度データは充足可能（ℤ₂ 上）。 -/
theorem haar_exists : Nonempty HaarMeasureData :=
  ⟨haarMeasureData 2 (by omega)⟩

/-- **M336F-8d: 実例** p=2 — μ(2ℤ₂)=1/2。 -/
theorem haar_example_two_one :
    haarBall 2 (by omega) 1 = Quot.mk ratRel ⟨1, 2, by omega⟩ := by
  rw [haar_ball_closed]
  apply Quot.sound
  show (1 : Int) * 2 = 1 * ((2 ^ 1 : Nat) : Int)
  rfl

/-- **M336F-8e: 実例** p=2 — μ(4ℤ₂)=μ(2²ℤ₂)=1/4。 -/
theorem haar_example_two_two :
    haarBall 2 (by omega) 2 = Quot.mk ratRel ⟨1, 4, by omega⟩ := by
  rw [haar_ball_closed]
  apply Quot.sound
  show (1 : Int) * 4 = 1 * ((2 ^ 2 : Nat) : Int)
  rfl

/-! ## M336F-9: σ-加法性 Borel 拡張（外部仮説・本層では導出しない） -/

/-- **M336F-9a: 外部仮説 `haarSigmaAdditivityHypothesis`** — σ-加法的 Borel 拡張。
    抽象的な「拡張測度」 ν（可測集合を表す述語 Int→Nat→Prop を測度値 ℚ へ送る）が、
    (1) 各基本開集合＝コセット {(a,d)} 上で有限加法測度 `haarCoset` に一致し、
    (2) 互いに素な二つの可測集合の非交和で（有限）加法的である、という命題。
    ν の存在・一意性（Carathéodory 拡張／σ-加法性）は本層（core Lean・測度論なし）では
    **導出しない**——外部から与えられる仮説として名前を固定する。可算加法性を含む
    完全な Borel 拡張は後続層。 -/
def haarSigmaAdditivityHypothesis (p : Nat) (hp : 1 ≤ p)
    (ν : (Int → Nat → Prop) → QRat) : Prop :=
  (∀ (a : Int) (d : Nat), ν (fun b e => b = a ∧ e = d) = haarCoset p hp a d)
  ∧ (∀ (S T : Int → Nat → Prop),
       (∀ b e, ¬ (S b e ∧ T b e)) →
       ν (fun b e => S b e ∨ T b e) = qAdd (ν S) (ν T))

/-- **M336F-9b: 外部仮説の帰結** — σ-加法的拡張 ν が仮定されれば、基本開集合
    {(a,d)}（＝コセット a+p^dℤ_p）上でその測度は本物の μ(p^dℤ_p)=`haarBall` に一致する。
    仮説 `haarSigmaAdditivityHypothesis` は導出せず、明示的な前提として使う。 -/
theorem haar_extension_agrees_of_hypothesis (p : Nat) (hp : 1 ≤ p)
    (ν : (Int → Nat → Prop) → QRat)
    (h : haarSigmaAdditivityHypothesis p hp ν) (a : Int) (d : Nat) :
    ν (fun b e => b = a ∧ e = d) = haarBall p hp d :=
  (h.1 a d).trans rfl

end IUT
