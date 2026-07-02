/-
# M131F: 実数値 log-volume への橋 — Frobenioid 次数 × 本物の ℝ

柱C（issue #37）C-1 の橋渡し。M12/M51F（Frobenioid 次数理論 QDiv・degZ）
と M67F（形式実化 RDiv・degR）を、M115F〜M130 でスクラッチ構成した
本物の ℝ（Bishop 流正則実数列 RReal）に接続する。これまで log-volume
は Int / ℚ≥0 値の形式簿記だったが、本層で合成準同型

  QDiv --degZ--> ℤ --ratOfInt--> ℚ --qToReal--> ℝ

を `rlogVol` として実体化し、次数の加法性・Frobenius スケーリング・
零・非負性・単調性を RReal の言葉（realEq / rLe / realAdd / rmul）で
言い直して機械検証する。

  * M131F-1 `qdegQ` — **次数の有理数化** deg_ℚ = ratOfInt ∘ degZ:
    加法性 `qdegQ_add`・Frobenius 斉次性 `qdegQ_frob`・零 `qdegQ_zero`・
    非負性 `qdegQ_nonneg`（M51F の degZ 法則 + ratOfInt の準同型性）
  * M131F-2 `qToReal_mono` — **埋め込み ℚ → ℝ の単調性**
    （定数列なので各 n で a ≤ b + 2/(n+1)、M130 の rLe_refl の踏襲）
  * M131F-3 `rlogVol` — **実数値 log-volume（本丸）**:
    `rlogVol_add`（realAdd での加法性）・`rlogVol_frob`（rmul での
    Frobenius スケーリング）・`rlogVol_zero`・`rlogVol_nonneg`・
    `rlogVol_mono`
  * M131F-4 `nnqToQ` — **比較射 ℚ≥0 → ℚ**（M67F の商 NNQ から
    M115F の商 QRat へ、a/(b+1) ↦ a/(b+1)）と `nnqToQ_ofNat`
  * M131F-5 `qdegQ_compat_realify` / `rlogVol_compat` — **M67F との
    整合**: 形式実化次数 degR ∘ realify と本橋 qdegQ が比較射 nnqToQ
    を通して同じ ℚ 値（従って同じ実数値）に落ちる可換図式
  * M131F-6 `LogVolBridgeData` — 総括

M12 接続: rationalFrobenioid（M51F）の deg はまさに degZ w なので、
M12 の次数＝log-volume 両立（vol_q 供給・定理3.11 (i)(c) 骨格）は
本橋によりそのまま実数値 log-volume の言明に持ち上がる。

## 意義

柱C C-1（#37）の橋渡し。M12（Frobenioid 次数）・M67F（形式実化）と
M115F〜M130 のスクラッチ ℝ を接続し、log-volume が本物の実数として
加法的・Frobenius 共変・非負・単調に振る舞うことを機械検証。
柱E E-2（系3.12 の ℝ 化）と柱D（定理3.11 の体積側）への供給線。

## 正直な申告

* 実数側の Frobenius 係数は qToReal (ratOfInt e)（自然数 e の定数列）
  であり、一般実数係数のスカラー倍構造は未形式化（rmul で代用）。
* 単調性は「degZ の比較 ⟹ rlogVol の比較」（埋め込みの単調性
  `qToReal_mono` / `rlogVol_mono`）の形で言明した。因子の効果性順序
  （mult の点ごと比較）から degZ の比較を導く nsum の単調性簿記は
  本層では扱わない。
* M67F との整合は「値の一致」（nnqToQ を通した QRat の等式）で言明
  した。比較射 nnqToQ が加法まで保つこと（モノイド準同型性）は本橋
  の定理には不要なため次層に回した。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.RealLe
import IUT.Realification

namespace IUT

/-! ## M131F-1: 次数の有理数化 deg_ℚ = ratOfInt ∘ degZ -/

/-- **M131F-1a: 有理数値次数** — QDiv の重み付き次数を ℚ に読む
    deg_ℚ(x) = ι(deg_ℤ(x))（ι = ratOfInt、M51F の degZ との合成）。 -/
def qdegQ (w : Nat → Nat) (x : QDiv) : QRat :=
  ratOfInt.map (degZ w x)

/-- **定理 (M131F-1b): 有理数値次数の加法性** —
    deg_ℚ(x + y) = deg_ℚ(x) + deg_ℚ(y)（degZ_add + ratOfInt.map_add）。 -/
theorem qdegQ_add (w : Nat → Nat) (x y : QDiv) :
    qdegQ w (qadd x y) = qAdd (qdegQ w x) (qdegQ w y) := by
  show ratOfInt.map (degZ w (qadd x y)) = qAdd (qdegQ w x) (qdegQ w y)
  rw [degZ_add]
  exact ratOfInt.map_add (degZ w x) (degZ w y)

/-- **定理 (M131F-1c): 有理数値次数の Frobenius 斉次性** —
    deg_ℚ(φ_e x) = e · deg_ℚ(x)（degZ_frob + ratOfInt.map_mul）。 -/
theorem qdegQ_frob (w : Nat → Nat) (e : Nat) (x : QDiv) :
    qdegQ w (qfrob e x) = qMul (ratOfInt.map (e : Int)) (qdegQ w x) := by
  show ratOfInt.map (degZ w (qfrob e x))
      = qMul (ratOfInt.map (e : Int)) (qdegQ w x)
  rw [degZ_frob]
  exact ratOfInt.map_mul (e : Int) (degZ w x)

/-- **M131F-1d: 自明因子の有理数値次数は 0**（degZ_zero + ι(0) = 0）。 -/
theorem qdegQ_zero (w : Nat → Nat) : qdegQ w qzero = ratRing.zero := by
  show ratOfInt.map (degZ w qzero) = ratRing.zero
  rw [degZ_zero]
  rfl

/-- **M131F-1e: 有理数値次数の非負性**（有効因子なので
    degZ_nonneg + ratOfInt の順序保存）。 -/
theorem qdegQ_nonneg (w : Nat → Nat) (x : QDiv) :
    qLe ratRing.zero (qdegQ w x) :=
  ratOfInt_le (degZ_nonneg w x)

/-! ## M131F-2: 埋め込み ℚ → ℝ の単調性 -/

/-- **定理 (M131F-2): 埋め込みの単調性** — a ≤ b なら
    qToReal a ≤ qToReal b。定数列なので各 n で
    a ≤ b + 2/(n+1) が「a ≤ b と揺らぎの非負性」から直ちに出る
    （M130 の rLe_refl の証明パターンの踏襲）。 -/
theorem qToReal_mono {a b : QRat} (h : qLe a b) :
    rLe (qToReal a) (qToReal b) := by
  intro n
  show qLe a (qAdd b (qAdd (qUnitFrac n) (qUnitFrac n)))
  have h1 : qLe (qAdd b ratRing.zero)
      (qAdd b (qAdd (qUnitFrac n) (qUnitFrac n))) :=
    qLe_add_two (qLe_refl b) (qFrac_add_nonneg 1 n 1 n)
  rw [qAdd_zero] at h1
  exact qLe_trans _ _ _ h h1

/-! ## M131F-3: 実数値 log-volume（本丸） -/

/-- **M131F-3a: 実数値 log-volume** — Frobenioid 次数を本物の ℝ に
    読む合成 rlogVol = qToReal ∘ ratOfInt ∘ degZ。IUT の
    「対象の log-volume は実数」の実体化（[IUTchIII] §3 の
    log-volume 簿記の受け皿）。 -/
def rlogVol (w : Nat → Nat) (x : QDiv) : RReal :=
  qToReal (qdegQ w x)

/-- **定理 (M131F-3b): 実数値 log-volume の加法性** —
    vol(x + y) ≈ vol(x) + vol(y)（qdegQ_add + 埋め込みの加法性
    qToReal_add）。次数関手の加法性が本物の実数の加法として成立する。 -/
theorem rlogVol_add (w : Nat → Nat) (x y : QDiv) :
    realEq (rlogVol w (qadd x y))
      (realAdd (rlogVol w x) (rlogVol w y)) := by
  show realEq (qToReal (qdegQ w (qadd x y)))
    (realAdd (qToReal (qdegQ w x)) (qToReal (qdegQ w y)))
  rw [qdegQ_add]
  exact realEq_symm (qToReal_add (qdegQ w x) (qdegQ w y))

/-- **定理 (M131F-3c): 実数値 log-volume の Frobenius スケーリング** —
    vol(φ_e x) ≈ e · vol(x)（qdegQ_frob + 埋め込みの乗法性 qToReal_mul）。
    M12 の frob_deg（Frobenius 射は次数を e 倍する）が本物の実数の
    乗法 rmul として成立する。 -/
theorem rlogVol_frob (w : Nat → Nat) (e : Nat) (x : QDiv) :
    realEq (rlogVol w (qfrob e x))
      (rmul (qToReal (ratOfInt.map (e : Int))) (rlogVol w x)) := by
  show realEq (qToReal (qdegQ w (qfrob e x)))
    (rmul (qToReal (ratOfInt.map (e : Int))) (qToReal (qdegQ w x)))
  rw [qdegQ_frob]
  exact realEq_symm (qToReal_mul (ratOfInt.map (e : Int)) (qdegQ w x))

/-- **M131F-3d: 自明因子の実数値 log-volume は 0**。 -/
theorem rlogVol_zero (w : Nat → Nat) :
    realEq (rlogVol w qzero) realZero := by
  show realEq (qToReal (qdegQ w qzero)) realZero
  rw [qdegQ_zero]
  exact realEq_refl realZero

/-- **定理 (M131F-3e): 実数値 log-volume の非負性** — 有効因子の
    log-volume は本物の ℝ の順序 rLe で 0 以上（degZ_nonneg を
    埋め込みの単調性で持ち上げる）。 -/
theorem rlogVol_nonneg (w : Nat → Nat) (x : QDiv) :
    rLe realZero (rlogVol w x) :=
  qToReal_mono (qdegQ_nonneg w x)

/-- **定理 (M131F-3f): 実数値 log-volume の単調性** — 次数の比較
    deg_ℤ(x) ≤ deg_ℤ(y) は実数の順序 rLe に持ち上がる。 -/
theorem rlogVol_mono (w : Nat → Nat) {x y : QDiv}
    (h : degZ w x ≤ degZ w y) : rLe (rlogVol w x) (rlogVol w y) :=
  qToReal_mono (ratOfInt_le h)

/-! ## M131F-4: 比較射 ℚ≥0 → ℚ（M67F の NNQ を M115F の QRat に読む） -/

/-- **M131F-4a: 比較射** ℚ≥0 → ℚ — 代表 (a, b)（= a/(b+1)）を
    PreRat ⟨a, b+1⟩ に送る。well-definedness は交差積の Nat 等式を
    `Int.natCast_mul` で Int にキャストするだけ（choice-free な
    Quot.lift の直接定義）。 -/
def nnqToQ (x : NNQ) : QRat :=
  Quot.lift
    (fun p => Quot.mk ratRel ⟨(p.1 : Int), (p.2 : Int) + 1, by omega⟩)
    (fun p q h => Quot.sound (by
      have hN : p.1 * (q.2 + 1) = q.1 * (p.2 + 1) := h
      show (p.1 : Int) * ((q.2 : Int) + 1) = (q.1 : Int) * ((p.2 : Int) + 1)
      have h' : ((p.1 * (q.2 + 1) : Nat) : Int)
          = ((q.1 * (p.2 + 1) : Nat) : Int) := by rw [hN]
      rw [Int.natCast_mul, Int.natCast_mul] at h'
      have e1 : ((q.2 + 1 : Nat) : Int) = (q.2 : Int) + 1 := by omega
      have e2 : ((p.2 + 1 : Nat) : Int) = (p.2 : Int) + 1 := by omega
      rw [e1, e2] at h'
      exact h')) x

/-- **M131F-4b: 比較射と埋め込みの両立** — nnqToQ(ι_ℚ≥0(n)) = ι_ℚ(n)
    （ℕ の両側埋め込みの可換三角形。交差積 n·1 = n·(0+1)）。 -/
theorem nnqToQ_ofNat (n : Nat) :
    nnqToQ (nnqOfNat n) = ratOfInt.map ((n : Nat) : Int) := by
  apply Quot.sound
  show (n : Int) * 1 = (n : Int) * (((0 : Nat) : Int) + 1)
  omega

/-! ## M131F-5: M67F（形式実化）との整合 -/

/-- **定理 (M131F-5a): 次数の可換図式（ℚ 値）** — M67F の形式実化次数
    degR ∘ realify と本橋の qdegQ は比較射 nnqToQ を通して一致する:
    nnqToQ(deg_R(realify x)) = deg_ℚ(x)。M67F-4e（degR_realify）と
    M131F-4b の合成（degZ = ι ∘ degN は定義から）。 -/
theorem qdegQ_compat_realify (w : Nat → Nat) (x : QDiv) :
    nnqToQ (degR w (realify x)) = qdegQ w x := by
  rw [degR_realify]
  exact nnqToQ_ofNat (degN w x)

/-- **定理 (M131F-5b): 次数の可換図式（ℝ 値）** — 形式実化 RDiv 側の
    log-volume（degR ∘ realify を ℝ に読んだもの）と本橋の rlogVol は
    実数として等しい（realEq）。M67F の「形式実化」が本物の ℝ の中で
    本橋と可換であることの機械検証。 -/
theorem rlogVol_compat (w : Nat → Nat) (x : QDiv) :
    realEq (qToReal (nnqToQ (degR w (realify x)))) (rlogVol w x) := by
  rw [qdegQ_compat_realify]
  exact realEq_refl (rlogVol w x)

/-! ## M131F-6: 総括 -/

/-- **M131F-6a: 総括** — 実数値 log-volume 橋のデータ束。
    Frobenioid 次数（M12/M51F）が本物の ℝ（M115F〜M130）の中で
    加法的・Frobenius 共変・非負・単調に振る舞い、M67F の形式実化と
    可換であることの実定理のみを束ねる。 -/
structure LogVolBridgeData where
  /-- 加法性: vol(x + y) ≈ vol(x) + vol(y)。 -/
  add : ∀ (w : Nat → Nat) (x y : QDiv),
    realEq (rlogVol w (qadd x y)) (realAdd (rlogVol w x) (rlogVol w y))
  /-- Frobenius スケーリング: vol(φ_e x) ≈ e · vol(x)。 -/
  frob : ∀ (w : Nat → Nat) (e : Nat) (x : QDiv),
    realEq (rlogVol w (qfrob e x))
      (rmul (qToReal (ratOfInt.map (e : Int))) (rlogVol w x))
  /-- 零: vol(0) ≈ 0。 -/
  zero : ∀ w : Nat → Nat, realEq (rlogVol w qzero) realZero
  /-- 非負性: 0 ≤ vol(x)。 -/
  nonneg : ∀ (w : Nat → Nat) (x : QDiv), rLe realZero (rlogVol w x)
  /-- 単調性: deg_ℤ の比較は rLe に持ち上がる。 -/
  mono : ∀ (w : Nat → Nat) {x y : QDiv}, degZ w x ≤ degZ w y →
    rLe (rlogVol w x) (rlogVol w y)
  /-- M67F との整合: degR ∘ realify と qdegQ の可換図式。 -/
  compat : ∀ (w : Nat → Nat) (x : QDiv),
    nnqToQ (degR w (realify x)) = qdegQ w x

/-- **M131F-6b: witness**。 -/
def logVolBridgeData : LogVolBridgeData where
  add := rlogVol_add
  frob := rlogVol_frob
  zero := rlogVol_zero
  nonneg := rlogVol_nonneg
  mono := rlogVol_mono
  compat := qdegQ_compat_realify

/-- **M131F-6c: 存在**。 -/
theorem logVolBridge_exists : Nonempty LogVolBridgeData :=
  ⟨logVolBridgeData⟩

end IUT
