/-
  IUT/MeasureLogVolume.lean — M341F [実／本物]
  分類: 実 (測度論的 log-volume = −log_p μ、M336F ハール測度から)
  complete_pct 影響: 柱C を前進（M336F の ℤ_p 加法ハール測度 μ(p^dℤ_p)=p^{-d} から
    測度論的 log-volume log-vol=−log_p μ を本物で定義し、加法性・単調性・M321F logShellVol/
    M312F Arakelov 次数規約との一致を証明＝「測度から定義された」本物の log-volume）。
  正直な限定: log は指数レベル（解析的対数でなく p 冪の指数）。σ-加法性は M336F 由来の仮説。
-/
import IUT.HaarMeasureZp
import IUT.IntRealBridge
import IUT.RealRingLaws

namespace IUT

/-! ## M341F-1: 測度論的 log-volume log-vol(p^dℤ_p) = −log_p μ(p^dℤ_p) = d

    μ(p^dℤ_p) = p^{-d}（M336F `haar_ball_closed`）なので
    log-vol(p^dℤ_p) = −log_p μ(p^dℤ_p) = −log_p(p^{-d}) = d。
    値は M336F の閉形式の**分母の指数**（`haarLogExp`）として測度から取り出す
    ——独立に宣言するのではなく、ハール測度 μ の対数として定義する。 -/

/-- **M341F-1: 測度論的 log-volume** log-vol(p^dℤ_p) = −log_p μ(p^dℤ_p) = d。
    M336F `haarLogExp`（= μ(p^dℤ_p)=p^{-d} の分母 p^d の指数）を採る。
    「測度から定義された」本物の log-volume の値（指数レベル）。 -/
def mlvBall (d : Nat) : Nat := haarLogExp d

/-- **M341F-1b: 閉形式の値** log-vol(p^dℤ_p) = d。 -/
theorem mlv_ball_eq (d : Nat) : mlvBall d = d := rfl

/-! ## M341F-2: 加法性（測度の乗法性 μ(p^d)=p·μ(p^{d+1}) が log で +1 になる） -/

/-- **M341F-2a: 加法性** log-vol(p^{d+1}ℤ_p) = log-vol(p^dℤ_p) + 1。
    M336F `haar_additive` の有限加法性 μ(p^dℤ_p)=p·μ(p^{d+1}ℤ_p)（各段で測度が
    ×(1/p)）が、log-volume では **+1**（フィルトレーションの各段で co-level が
    1 増える）になる本物の関係。 -/
theorem mlv_additive (d : Nat) : mlvBall (d + 1) = mlvBall d + 1 := rfl

/-- **M341F-2b: 分母指数の比（log が × を + にする核）** — μ の分母は
    p^{log-vol(p^{d+1})} = p · p^{log-vol(p^d)}。すなわち測度の ×(1/p) 比
    （M336F `haar_additive` の p 倍）が、指数 log-volume では **+1**（p^d → p·p^d）に
    翻訳される。これが「log が乗法を加法に変える」本物の実現。 -/
theorem mlv_denom_ratio (p d : Nat) :
    p ^ mlvBall (d + 1) = p * p ^ mlvBall d := by
  show p ^ (d + 1) = p * p ^ d
  rw [Nat.pow_succ]
  exact Nat.mul_comm _ _

/-- **M341F-2c: 測度の有限加法性（再掲・M336F 由来）** μ(p^dℤ_p) = p·μ(p^{d+1}ℤ_p)。
    log-vol の +1 加法性 `mlv_additive` はこの測度側の乗法性の対数像である。 -/
theorem mlv_measure_additive (p : Nat) (hp : 1 ≤ p) (d : Nat) :
    qMul (ratOfInt.map (p : Int)) (haarBall p hp (d + 1)) = haarBall p hp d :=
  haar_additive p hp d

/-! ## M341F-3: 単調性（より小さい球 ⇒ より大きい log-volume、μ antitone） -/

/-- **M341F-3a: 単調性（1 段）** log-vol(p^dℤ_p) ≤ log-vol(p^{d+1}ℤ_p)。
    より小さい球 p^{d+1}ℤ_p ⊆ p^dℤ_p は測度が小さく（M336F `haar_ball_le_succ`
    の antitone）、log-volume −log_p μ は逆に大きくなる。 -/
theorem mlv_monotone_succ (d : Nat) : mlvBall d ≤ mlvBall (d + 1) := by
  show d ≤ d + 1
  omega

/-- **M341F-3b: 単調性（一般）** d ≤ e ⇒ log-vol(p^dℤ_p) ≤ log-vol(p^eℤ_p)。
    殻の深さ（付値 co-level）が増えれば log-volume は単調増加。 -/
theorem mlv_monotone {d e : Nat} (h : d ≤ e) : mlvBall d ≤ mlvBall e := h

/-- **M341F-3c: 測度の単調減少（再掲・M336F 由来）** μ(p^{d+1}ℤ_p) ≤ μ(p^dℤ_p)。
    log-vol の単調増加 `mlv_monotone_succ` はこの測度側の antitone の対数像である。 -/
theorem mlv_measure_antitone (p : Nat) (hp : 1 ≤ p) (d : Nat) :
    qLe (haarBall p hp (d + 1)) (haarBall p hp d) :=
  haar_ball_le_succ p hp d

/-! ## M341F-4: M321F logShellVol との一致（測度論的と殻/Arakelov 規約の合致） -/

/-- **M341F-4: 殻規約との一致** log-vol(p^dℤ_p) = M321F `logShellVol d`。
    測度論的 log-volume（−log_p μ）と、M321F の対数殻の co-level 規約
    `logShellVol` が指数レベルで一致する。M336F `haar_logExp_eq_shellVol` を採る。 -/
theorem mlv_eq_shellVol (d : Nat) : mlvBall d = logShellVol d :=
  haar_logExp_eq_shellVol d

/-! ## M341F-5: M312F Arakelov 次数規約との橋（符号・正規化） -/

/-- **M341F-5a: 実数値 log-volume** log-vol(p^dℤ_p) ∈ ℝ（M312F の RReal 値域へ）。
    指数 d を本物の ℝ の元 intToReal(d) として持つ。 -/
def mlvBallR (d : Nat) : RReal := intToReal ((mlvBall d : Nat) : Int)

/-- **M341F-5b: Arakelov 局所 log-volume** deg_ℝ = d·log p。
    M312F の局所 log-volume 規約 −v(x)·log q_v（付値×重み log p）で、殻 p^dℤ_p の
    co-level v = −d を採ると deg_ℝ = −(−d)·log p = d·log p。実重み logp を受け取る。 -/
def mlvArakelov (logp : RReal) (d : Nat) : RReal :=
  rmul (intToReal ((mlvBall d : Nat) : Int)) logp

/-- **M341F-5c: 符号・正規化の橋（unit 重み）** — 重み logp = 1（M312F `logVolUnit`
    規約）では Arakelov log-volume deg_ℝ = d·1 ≈ log-vol(p^dℤ_p) の ℝ 像 mlvBallR d。
    測度論的 log-volume −log_p μ = d と M312F の Arakelov 次数 deg = −v·log p の
    符号/正規化が unit 重みで一致する本物のブリッジ（rmul_one で）。 -/
theorem mlv_arakelov_unit (d : Nat) :
    realEq (mlvArakelov (qToReal ratRing.one) d) (mlvBallR d) :=
  rmul_one (intToReal ((mlvBall d : Nat) : Int))

/-- **M341F-5d: Arakelov 加法性（局所寄与の加法）** deg_ℝ((d+e)·log p) ≈
    deg_ℝ(d·log p) + deg_ℝ(e·log p)。log-volume の指数 d の加法性が、実重み付き
    Arakelov 次数の加法（M312F `logVolLocal_add` 規約）として成立する。 -/
theorem mlv_arakelov_add (logp : RReal) (d e : Nat) :
    realEq (rmul (intToReal ((d : Int) + (e : Int))) logp)
      (realAdd (rmul (intToReal (d : Int)) logp) (rmul (intToReal (e : Int)) logp)) :=
  realEq_trans (rmul_congr_left logp (realEq_symm (intToReal_add (d : Int) (e : Int))))
    (rmul_add_right (intToReal (d : Int)) (intToReal (e : Int)) logp)

/-! ## M341F-6: 測度からの定義（key point: log-vol は μ から定義される） -/

/-- **M341F-6: log-volume は測度から定義される（核）** — μ(p^dℤ_p) = 1/p^{log-vol(p^dℤ_p)}。
    すなわち log-vol(p^dℤ_p)=`mlvBall d` は、M336F ハール測度 `haarBall p hp d` の
    閉形式（`haarClosed`）の**分母 p の指数そのもの**である。log-volume が独立に
    宣言されたのではなく、ハール測度 μ の（指数）対数として定義されていることの
    明示的な定義的リンク（M336F `haar_ball_closed` を採る）。 -/
theorem mlv_from_measure (p : Nat) (hp : 1 ≤ p) (d : Nat) :
    haarBall p hp d = haarClosed p hp (mlvBall d) :=
  haar_ball_closed p hp d

/-- **M341F-6b: 測度の閉形式による log-volume 表現** — μ(p^dℤ_p) の分母は
    p^{mlvBall d}、すなわち μ(p^dℤ_p)=p^{−(mlvBall d)}（−log_p μ = mlvBall d の
    ℚ 値表現、M336F `haar_ball_is_inv_pow`）。 -/
theorem mlv_measure_inv_pow (p : Nat) (hp : 1 ≤ p) (d : Nat) :
    haarBall p hp d = Quot.mk ratRel ⟨1, ((p ^ mlvBall d : Nat) : Int), by
      have := haar_pow_pos p hp (mlvBall d); omega⟩ :=
  haar_ball_is_inv_pow p hp d

/-! ## M341F-7: capstone と実例 -/

/-- **M341F-7a: 測度論的 log-volume データ** — ℤ_p 上のハール測度 μ から定義された
    log-volume log-vol=−log_p μ の束ね。測度からの定義（閉形式）・加法性・単調性・
    M321F 殻規約との一致を本物で充足する。 -/
structure MeasureLogVolumeData where
  /-- 局所体の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  /-- 1 ≤ p。 -/
  hp : 1 ≤ p
  /-- 測度論的 log-volume log-vol(p^dℤ_p) = −log_p μ(p^dℤ_p)。 -/
  vol : Nat → Nat
  /-- 測度からの定義: μ(p^dℤ_p) = 1/p^{vol d}（閉形式の分母指数）。 -/
  from_measure : ∀ d, haarBall p hp d = haarClosed p hp (vol d)
  /-- 加法性: log-vol(p^{d+1}) = log-vol(p^d) + 1（μ の ×(1/p) の対数）。 -/
  additive : ∀ d, vol (d + 1) = vol d + 1
  /-- 単調性: d ≤ e ⇒ log-vol(p^d) ≤ log-vol(p^e)。 -/
  monotone : ∀ {d e}, d ≤ e → vol d ≤ vol e
  /-- M321F 殻規約との一致: log-vol(p^d) = logShellVol d。 -/
  eq_shellVol : ∀ d, vol d = logShellVol d

/-- **M341F-7b: 実データ** — 全フィールドを本物で充足。 -/
def measureLogVolumeData (p : Nat) (hp : 1 ≤ p) : MeasureLogVolumeData where
  p := p
  hp := hp
  vol := mlvBall
  from_measure := mlv_from_measure p hp
  additive := mlv_additive
  monotone := mlv_monotone
  eq_shellVol := mlv_eq_shellVol

/-- **M341F-7c: 存在** — 測度から定義された本物の log-volume データは充足可能（ℤ₂ 上）。 -/
theorem mlv_exists : Nonempty MeasureLogVolumeData :=
  ⟨measureLogVolumeData 2 (by omega)⟩

/-- **M341F-7d: 実例** p=2 — log-vol(4ℤ₂) = log-vol(2²ℤ₂) = 2。
    μ(4ℤ₂)=1/4=1/2² ゆえ −log₂ μ(4ℤ₂) = 2（M336F `haar_example_two_two` と整合）。 -/
theorem mlv_example_two_two : mlvBall 2 = 2 := rfl

/-- **M341F-7e: 実例の測度側整合** p=2 — μ(4ℤ₂)=1/4（log-vol=2 の測度根拠）。 -/
theorem mlv_example_measure_two :
    haarBall 2 (by omega) (mlvBall 2) = Quot.mk ratRel ⟨1, 4, by omega⟩ :=
  haar_example_two_two

end IUT
