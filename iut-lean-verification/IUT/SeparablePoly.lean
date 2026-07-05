/-
  IUT/SeparablePoly.lean — M270F（形式微分と分離多項式:
  実エタール性/分離拡大の本物の先行建設）

  ── 分類 **[実]**（本物の先行建設。骨格・模型・代理でなく本物の証明）。

  **complete_pct 影響**: 柱A「実エタール性/分離拡大」の本物の先行建設。
  分離性（重根なし ⟺ gcd(f, Df) = 1）は分離拡大・エタール射・実 π₁^ét の
  核心概念であり、その第一石である**形式微分 D** とその代数則
  （線形性・ライプニッツ則）、および**微分による重根判定**を、既存の
  係数列多項式（PS = ℕ→R）と Cauchy 積 psMul の上に本物で建てる。

  本層の主要成果（すべて本物・sorry 不使用・Classical.choice 不使用）:

  * M270F-1 `rnsmul` — 環元の自然数倍 n·a（= a を n 個加える）と代数則:
    `rnsmul_zero`（n·0 = 0）・`rnsmul_add`（n·(a+b)=n·a+n·b）・
    `rnsmul_neg`（n·(−a)=−(n·a)）・`rnsmul_mul_right/left`
    （(n·a)·b = n·(a·b)・a·(n·b)=n·(a·b)）。形式微分の係数
    i·aᵢ に必要な本物のスカラー作用。
  * M270F-2 `formalDeriv` — **形式微分** D(f)ₙ = (n+1)·f(n+1)
    （D(Σ aᵢXⁱ) = Σ i aᵢ X^{i−1} の係数列表現）。
  * M270F-3 微分の本物の法則:
    - `formalDeriv_add`  **線形性** D(f+g) = Df + Dg
    - `formalDeriv_neg`  D(−f) = −Df
    - `formalDeriv_smul` D(c·f) = c·Df（スカラー線形）
    - `formalDeriv_psC` / `formalDeriv_psOne` D(定数) = 0
    - `formalDeriv_psX`  D(X) = 1
    - `formalDeriv_psSingle_succ` **D(c·X^{m+1}) = (m+1)·c·X^m**（単項式則）
  * M270F-4 **ライプニッツ則（積の微分）** の本物の各実ケース:
    - `psMul_psX_succ` / `psMul_psX_zero` — X 倍（右シフト）の係数
    - `formalDeriv_mul_psX`  **D(f·X) = Df·X + f**（f·DX、DX=1）
    - `psMul_psC` — 定数倍の係数、`formalDeriv_mul_psC`
      **D(f·c) = Df·c**（Dc=0 のライプニッツ）
    - `psMul_psAdd`（乗法の右分配）・`formalDeriv_mul_linFactor`
      **D(f·(X−a)) = Df·(X−a) + f**（一次因子のライプニッツ、
      X 倍と定数倍のケースと線形性から合成——本物のライプニッツ実例）
  * M270F-5 **分離性/重根判定** の本物:
    - `psLinFactor` — 一次因子 X − a、`psDvd` — 級数の整除
    - `sep_repeated_factor` **(X−a)² ∣ f ⟹ (X−a) ∣ f ∧ (X−a) ∣ Df**:
      重根（(X−a)² を因子に持つ）⟹ f と Df が共通因子 (X−a) を持つ。
      f = (ℓ·h)·ℓ に一次因子ライプニッツを当て Df = ℓ·(Dg + h) を得る
      （ℓ = X−a, g = ℓ·h）。分離性の微分判定
      「f 分離 ⟺ gcd(f,Df)=1 ⟺ 重根なし」の**⟹方向の核**。
  * M270F-6 capstone `SeparableData` / `separableWitness` /
    `separable_exists` — 微分則 + 重根判定の束ね。

  正直な限定（消去・弱化禁止）:
   - 多項式は係数列 PS = ℕ→R として扱う。「重根 a を持つ」は
     **級数レベルの整除 (X−a)² ∣ f**（∃ 証人）で表現し、`sep_repeated_factor`
     は ⟹方向（重根 ⟹ f と Df の共通因子 (X−a)）を本物で閉じる。
     **⟸方向**（(X−a)∣f ∧ (X−a)∣Df ⟹ (X−a)²∣f）と、完全な
     **分離性 gcd(f, Df) = 1** は体上ユークリッド互除法（既存 M268F
     `field_division_exists` を土台に次層）が要るため本層に含めない。
   - 微分の値 f(a)・Df(a) と評価 pEval の橋渡し（pEval が環準同型で
     あること = ライプニッツの評価版）は本層では行わず、整除
     (X−a)∣g（⟺ 級数レベルで g が a を根に持つ）で honest に閉じる。
   - ライプニッツ則は X 倍・定数倍・一次因子の**本物の実ケース**を
     証明する。任意 g との一般 D(f·g)=Df·g+f·Dg（有限台の単項式分解
     による持ち上げ）は本層に含めない（一次因子ケースで重根判定には十分）。

  全て選択公理不使用。禁止タクティク不使用。サブエージェント新規部品
  （共有ファイル不更新）。
-/
import IUT.PolyFieldDivision

namespace IUT

/-! ## M270F-1: 環元の自然数倍 -/

/-- **M270F-1: 自然数倍** n·a = a を n 個加えたもの。形式微分の係数
    i·aᵢ に必要な本物のスカラー作用（一般可換環で構成的に定義）。 -/
def rnsmul (R : CRing) : Nat → R.carrier → R.carrier
  | 0, _ => R.zero
  | n + 1, a => R.add (rnsmul R n a) a

/-- n·0 = 0。 -/
theorem rnsmul_zero (R : CRing) : ∀ n, rnsmul R n R.zero = R.zero := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show R.add (rnsmul R n R.zero) R.zero = R.zero
    rw [ih, R.zero_add]

/-- n·(a+b) = n·a + n·b。 -/
theorem rnsmul_add (R : CRing) : ∀ (n : Nat) (a b : R.carrier),
    rnsmul R n (R.add a b) = R.add (rnsmul R n a) (rnsmul R n b) := by
  intro n
  induction n with
  | zero =>
    intro a b
    show R.zero = R.add R.zero R.zero
    rw [R.zero_add]
  | succ n ih =>
    intro a b
    show R.add (rnsmul R n (R.add a b)) (R.add a b)
      = R.add (R.add (rnsmul R n a) a) (R.add (rnsmul R n b) b)
    rw [ih a b]
    exact R.add_add_add_comm (rnsmul R n a) (rnsmul R n b) a b

/-- n·(−a) = −(n·a)。 -/
theorem rnsmul_neg (R : CRing) : ∀ (n : Nat) (a : R.carrier),
    rnsmul R n (R.neg a) = R.neg (rnsmul R n a) := by
  intro n
  induction n with
  | zero =>
    intro a
    show R.zero = R.neg R.zero
    rw [CRing.neg_zero R]
  | succ n ih =>
    intro a
    show R.add (rnsmul R n (R.neg a)) (R.neg a) = R.neg (R.add (rnsmul R n a) a)
    rw [ih a, CRing.neg_add_dist R (rnsmul R n a) a]

/-- (n·a)·b = n·(a·b)（右分配の反復）。 -/
theorem rnsmul_mul_right (R : CRing) : ∀ (n : Nat) (a b : R.carrier),
    R.mul (rnsmul R n a) b = rnsmul R n (R.mul a b) := by
  intro n
  induction n with
  | zero =>
    intro a b
    show R.mul R.zero b = R.zero
    exact CRing.zero_mul R b
  | succ n ih =>
    intro a b
    show R.mul (R.add (rnsmul R n a) a) b
      = R.add (rnsmul R n (R.mul a b)) (R.mul a b)
    rw [CRing.right_distrib R (rnsmul R n a) a b, ih a b]

/-- a·(n·b) = n·(a·b)。 -/
theorem rnsmul_mul_left (R : CRing) (n : Nat) (a b : R.carrier) :
    R.mul a (rnsmul R n b) = rnsmul R n (R.mul a b) := by
  rw [R.mul_comm a (rnsmul R n b), rnsmul_mul_right R n b a, R.mul_comm b a]

/-! ## M270F-2: 形式微分 -/

/-- **M270F-2: 形式微分** D(f)ₙ = (n+1)·f(n+1)。
    D(Σ aᵢ Xⁱ) = Σ i aᵢ X^{i−1} の係数列表現（本物）。 -/
def formalDeriv (R : CRing) (f : PS R) : PS R :=
  fun n => rnsmul R (n + 1) (f (n + 1))

/-! ## M270F-3: 微分の本物の法則 -/

/-- **M270F-3a: 線形性** D(f+g) = Df + Dg。 -/
theorem formalDeriv_add (R : CRing) (f g : PS R) :
    formalDeriv R (psAdd R f g)
      = psAdd R (formalDeriv R f) (formalDeriv R g) := by
  funext n
  show rnsmul R (n + 1) (R.add (f (n + 1)) (g (n + 1)))
    = R.add (rnsmul R (n + 1) (f (n + 1))) (rnsmul R (n + 1) (g (n + 1)))
  exact rnsmul_add R (n + 1) (f (n + 1)) (g (n + 1))

/-- **M270F-3b: 反数** D(−f) = −Df。 -/
theorem formalDeriv_neg (R : CRing) (f : PS R) :
    formalDeriv R (psNeg R f) = psNeg R (formalDeriv R f) := by
  funext n
  show rnsmul R (n + 1) (R.neg (f (n + 1)))
    = R.neg (rnsmul R (n + 1) (f (n + 1)))
  exact rnsmul_neg R (n + 1) (f (n + 1))

/-- **M270F-3c: スカラー線形** D(c·f) = c·Df。 -/
theorem formalDeriv_smul (R : CRing) (c : R.carrier) (f : PS R) :
    formalDeriv R (psSmul R c f) = psSmul R c (formalDeriv R f) := by
  funext n
  show rnsmul R (n + 1) (R.mul c (f (n + 1)))
    = R.mul c (rnsmul R (n + 1) (f (n + 1)))
  exact (rnsmul_mul_left R (n + 1) c (f (n + 1))).symm

/-- **M270F-3d: 定数の微分は 0** D(c) = 0。 -/
theorem formalDeriv_psC (R : CRing) (c : R.carrier) :
    formalDeriv R (psC R c) = psZero R := by
  funext n
  show rnsmul R (n + 1) (psC R c (n + 1)) = R.zero
  rw [show psC R c (n + 1) = R.zero from if_neg (by omega)]
  exact rnsmul_zero R (n + 1)

/-- **M270F-3e: D(1) = 0**。 -/
theorem formalDeriv_psOne (R : CRing) :
    formalDeriv R (psOne R) = psZero R := by
  funext n
  show rnsmul R (n + 1) (psOne R (n + 1)) = R.zero
  rw [show psOne R (n + 1) = R.zero from if_neg (by omega)]
  exact rnsmul_zero R (n + 1)

/-- **M270F-3f: D(X) = 1**。 -/
theorem formalDeriv_psX (R : CRing) :
    formalDeriv R (psX R) = psOne R := by
  funext n
  show rnsmul R (n + 1) (psX R (n + 1)) = psOne R n
  cases n with
  | zero =>
    show rnsmul R (0 + 1) (psX R (0 + 1)) = psOne R 0
    rw [show psX R (0 + 1) = R.one from if_pos rfl,
      show psOne R 0 = R.one from if_pos rfl]
    show R.add R.zero R.one = R.one
    exact R.zero_add R.one
  | succ m =>
    show rnsmul R (m + 1 + 1) (psX R (m + 1 + 1)) = psOne R (m + 1)
    rw [show psX R (m + 1 + 1) = R.zero from if_neg (by omega),
      show psOne R (m + 1) = R.zero from if_neg (by omega)]
    exact rnsmul_zero R (m + 1 + 1)

/-- **M270F-3g: 単項式則** D(c·X^{m+1}) = (m+1)·c·X^m。 -/
theorem formalDeriv_psSingle_succ (R : CRing) (c : R.carrier) (m : Nat) :
    formalDeriv R (psSingle R c (m + 1))
      = psSingle R (rnsmul R (m + 1) c) m := by
  funext n
  show rnsmul R (n + 1) (psSingle R c (m + 1) (n + 1))
    = psSingle R (rnsmul R (m + 1) c) m n
  cases Nat.decEq n m with
  | isTrue h =>
    rw [h,
      show psSingle R c (m + 1) (m + 1) = c from if_pos rfl,
      show psSingle R (rnsmul R (m + 1) c) m m = rnsmul R (m + 1) c
        from if_pos rfl]
  | isFalse h =>
    rw [show psSingle R c (m + 1) (n + 1) = R.zero
        from if_neg (fun he => h (by omega)),
      show psSingle R (rnsmul R (m + 1) c) m n = R.zero from if_neg h]
    exact rnsmul_zero R (n + 1)

/-! ## M270F-4: ライプニッツ則の本物の実ケース -/

/-- **M270F-4a: X 倍の係数（正の次数）** (f·X)_{n+1} = f n。
    Cauchy 和は psX の台 {1} により i = n の中央 1 項に潰れる。 -/
theorem psMul_psX_succ (R : CRing) (f : PS R) (n : Nat) :
    psMul R f (psX R) (n + 1) = f n := by
  show rsum R (fun k => R.mul (f k) (psX R (n + 1 - k))) (n + 2) = f n
  have hmid : rsum R (fun k => R.mul (f k) (psX R (n + 1 - k))) (n + 2)
      = R.mul (f n) (psX R (n + 1 - n)) :=
    rsum_single_middle R (fun k => R.mul (f k) (psX R (n + 1 - k))) n (n + 2)
      (fun k hk hkn => by
        show R.mul (f k) (psX R (n + 1 - k)) = R.zero
        rw [show psX R (n + 1 - k) = R.zero from if_neg (by omega)]
        exact CRing.mul_zero R (f k))
      (by omega)
  rw [hmid, show n + 1 - n = 1 from by omega,
    show psX R 1 = R.one from if_pos rfl, CRing.mul_one R (f n)]

/-- **M270F-4b: X 倍の定数項は 0** (f·X)_0 = 0。 -/
theorem psMul_psX_zero (R : CRing) (f : PS R) :
    psMul R f (psX R) 0 = R.zero := by
  show R.add R.zero (R.mul (f 0) (psX R (0 - 0))) = R.zero
  rw [show psX R (0 - 0) = R.zero from if_neg (by omega),
    CRing.mul_zero R (f 0), R.zero_add]

/-- **M270F-4c: ライプニッツ（X 倍）** D(f·X) = Df·X + f。
    DX = 1 なので f·DX = f。係数比較: 定数項は両辺 f 0、正の次数
    (n+1) では (n+2)·f(n+1) = ((n+1)·f(n+1)) + f(n+1) が rnsmul の
    一段展開で一致する（本物のライプニッツ実例）。 -/
theorem formalDeriv_mul_psX (R : CRing) (f : PS R) :
    formalDeriv R (psMul R f (psX R))
      = psAdd R (psMul R (formalDeriv R f) (psX R)) f := by
  funext n
  cases n with
  | zero =>
    show rnsmul R (0 + 1) (psMul R f (psX R) (0 + 1))
      = R.add (psMul R (formalDeriv R f) (psX R) 0) (f 0)
    rw [psMul_psX_succ R f 0, psMul_psX_zero R (formalDeriv R f), R.zero_add]
    show R.add R.zero (f 0) = f 0
    exact R.zero_add (f 0)
  | succ m =>
    show rnsmul R (m + 1 + 1) (psMul R f (psX R) (m + 1 + 1))
      = R.add (psMul R (formalDeriv R f) (psX R) (m + 1)) (f (m + 1))
    rw [psMul_psX_succ R f (m + 1), psMul_psX_succ R (formalDeriv R f) m]
    show R.add (rnsmul R (m + 1) (f (m + 1))) (f (m + 1))
      = R.add (rnsmul R (m + 1) (f (m + 1))) (f (m + 1))
    rfl

/-- **M270F-4d: 定数倍の係数** (f·c)_n = f n · c。 -/
theorem psMul_psC (R : CRing) (f : PS R) (c : R.carrier) (n : Nat) :
    psMul R f (psC R c) n = R.mul (f n) c := by
  show rsum R (fun k => R.mul (f k) (psC R c (n - k))) (n + 1) = R.mul (f n) c
  have hmid : rsum R (fun k => R.mul (f k) (psC R c (n - k))) (n + 1)
      = R.mul (f n) (psC R c (n - n)) :=
    rsum_single_middle R (fun k => R.mul (f k) (psC R c (n - k))) n (n + 1)
      (fun k hk hkn => by
        show R.mul (f k) (psC R c (n - k)) = R.zero
        rw [show psC R c (n - k) = R.zero from if_neg (by omega)]
        exact CRing.mul_zero R (f k))
      (by omega)
  rw [hmid, show n - n = 0 from by omega, show psC R c 0 = c from if_pos rfl]

/-- **M270F-4e: ライプニッツ（定数倍）** D(f·c) = Df·c。
    Dc = 0 のライプニッツ実例。係数 (n+1)·(f(n+1)·c) = ((n+1)·f(n+1))·c
    は rnsmul_mul_right（本物のスカラー則）。 -/
theorem formalDeriv_mul_psC (R : CRing) (f : PS R) (c : R.carrier) :
    formalDeriv R (psMul R f (psC R c))
      = psMul R (formalDeriv R f) (psC R c) := by
  funext n
  show rnsmul R (n + 1) (psMul R f (psC R c) (n + 1))
    = psMul R (formalDeriv R f) (psC R c) n
  rw [psMul_psC R f c (n + 1), psMul_psC R (formalDeriv R f) c n]
  show rnsmul R (n + 1) (R.mul (f (n + 1)) c)
    = R.mul (rnsmul R (n + 1) (f (n + 1))) c
  exact (rnsmul_mul_right R (n + 1) (f (n + 1)) c).symm

/-- **M270F-4f: 乗法の右分配** f·(u+v) = f·u + f·v（係数ごとの分配）。 -/
theorem psMul_psAdd (R : CRing) (f u v : PS R) :
    psMul R f (psAdd R u v) = psAdd R (psMul R f u) (psMul R f v) := by
  funext n
  show rsum R (fun k => R.mul (f k) (R.add (u (n - k)) (v (n - k)))) (n + 1)
    = R.add (rsum R (fun k => R.mul (f k) (u (n - k))) (n + 1))
        (rsum R (fun k => R.mul (f k) (v (n - k))) (n + 1))
  have hc : rsum R
      (fun k => R.mul (f k) (R.add (u (n - k)) (v (n - k)))) (n + 1)
      = rsum R (fun k => R.add (R.mul (f k) (u (n - k)))
          (R.mul (f k) (v (n - k)))) (n + 1) :=
    rsum_congr R (n + 1) (fun k _ =>
      R.left_distrib (f k) (u (n - k)) (v (n - k)))
  rw [hc]
  exact rsum_add R _ _ (n + 1)

/-! ## M270F-5: 分離性/重根判定 -/

/-- **M270F-5a: 一次因子** X − a（係数: 1 番目に 1、0 番目に −a）。 -/
def psLinFactor (R : CRing) (a : R.carrier) : PS R :=
  psAdd R (psX R) (psC R (R.neg a))

/-- **M270F-5b: 級数の整除** d ∣ g ⟺ ∃ q, g = d·q。 -/
def psDvd (R : CRing) (d g : PS R) : Prop := ∃ q : PS R, g = psMul R d q

/-- **M270F-5c: ライプニッツ（一次因子）** D(f·(X−a)) = Df·(X−a) + f。
    (X−a) 倍を X 倍と定数倍 (−a) に分配し（psMul_psAdd）、線形性で
    D を分配、X 倍・定数倍のライプニッツを当て、再び因子化する。
    一次因子 ℓ の微分は Dℓ = 1 なので f·Dℓ = f（末尾の +f）。 -/
theorem formalDeriv_mul_linFactor (R : CRing) (f : PS R) (a : R.carrier) :
    formalDeriv R (psMul R f (psLinFactor R a))
      = psAdd R (psMul R (formalDeriv R f) (psLinFactor R a)) f := by
  have hdist1 : psMul R f (psLinFactor R a)
      = psAdd R (psMul R f (psX R)) (psMul R f (psC R (R.neg a))) :=
    psMul_psAdd R f (psX R) (psC R (R.neg a))
  have hdist2 : psMul R (formalDeriv R f) (psLinFactor R a)
      = psAdd R (psMul R (formalDeriv R f) (psX R))
          (psMul R (formalDeriv R f) (psC R (R.neg a))) :=
    psMul_psAdd R (formalDeriv R f) (psX R) (psC R (R.neg a))
  rw [hdist1,
    formalDeriv_add R (psMul R f (psX R)) (psMul R f (psC R (R.neg a))),
    formalDeriv_mul_psX R f, formalDeriv_mul_psC R f (R.neg a), hdist2]
  funext n
  show R.add (R.add (psMul R (formalDeriv R f) (psX R) n) (f n))
      (psMul R (formalDeriv R f) (psC R (R.neg a)) n)
    = R.add (R.add (psMul R (formalDeriv R f) (psX R) n)
        (psMul R (formalDeriv R f) (psC R (R.neg a)) n)) (f n)
  rw [R.add_assoc (psMul R (formalDeriv R f) (psX R) n) (f n)
      (psMul R (formalDeriv R f) (psC R (R.neg a)) n),
    R.add_comm (f n) (psMul R (formalDeriv R f) (psC R (R.neg a)) n),
    ← R.add_assoc (psMul R (formalDeriv R f) (psX R) n)
      (psMul R (formalDeriv R f) (psC R (R.neg a)) n) (f n)]

/-- **定理 (M270F-5d): 重根の微分判定（本物・⟹方向）** —
    ℓ = X − a とし f が (X−a)² を因子に持つ（f = (ℓ·h)·ℓ）なら、
    **f も Df も一次因子 (X−a) を持つ**。すなわち a は f と Df の
    共通根。一次因子ライプニッツ（M270F-5c）で
    Df = D(g·ℓ) = Dg·ℓ + g（g = ℓ·h）、g = ℓ·h と可換性・右分配で
    Df = ℓ·(Dg + h)。これが分離性の微分判定
    「f 分離 ⟺ gcd(f, Df) = 1 ⟺ 重根なし」の ⟹方向の核。 -/
theorem sep_repeated_factor (R : CRing) (a : R.carrier) (h f : PS R)
    (hf : f = psMul R (psMul R (psLinFactor R a) h) (psLinFactor R a)) :
    psDvd R (psLinFactor R a) f
      ∧ psDvd R (psLinFactor R a) (formalDeriv R f) := by
  refine ⟨⟨psMul R (psLinFactor R a) h, ?_⟩, ?_⟩
  · -- (X−a) ∣ f: f = ℓ·(ℓ·h)（可換性）
    rw [hf]
    exact (psRing R).mul_comm (psMul R (psLinFactor R a) h) (psLinFactor R a)
  · -- (X−a) ∣ Df: Df = ℓ·(Dg + h)
    refine ⟨psAdd R (formalDeriv R (psMul R (psLinFactor R a) h)) h, ?_⟩
    rw [hf, formalDeriv_mul_linFactor R (psMul R (psLinFactor R a) h) a,
      psMul_psAdd R (psLinFactor R a)
        (formalDeriv R (psMul R (psLinFactor R a) h)) h]
    have hc : psMul R (formalDeriv R (psMul R (psLinFactor R a) h))
          (psLinFactor R a)
        = psMul R (psLinFactor R a)
          (formalDeriv R (psMul R (psLinFactor R a) h)) :=
      (psRing R).mul_comm _ _
    rw [hc]

/-! ## M270F-6: capstone -/

/-- **M270F-6: 分離性データ** — 形式微分と、その本物の代数則
    （線形性・定数則・X 倍ライプニッツ）および重根の微分判定を束ねる。 -/
structure SeparableData (R : CRing) where
  deriv : PS R → PS R
  deriv_add : ∀ f g, deriv (psAdd R f g) = psAdd R (deriv f) (deriv g)
  deriv_const : ∀ c, deriv (psC R c) = psZero R
  leibniz_X : ∀ f,
    deriv (psMul R f (psX R)) = psAdd R (psMul R (deriv f) (psX R)) f
  repeated : ∀ (a : R.carrier) (hh f : PS R),
    f = psMul R (psMul R (psLinFactor R a) hh) (psLinFactor R a) →
    psDvd R (psLinFactor R a) f ∧ psDvd R (psLinFactor R a) (deriv f)

/-- 証人: 形式微分 formalDeriv と M270F-3/4/5 をそのまま束ねる。 -/
def separableWitness (R : CRing) : SeparableData R where
  deriv := formalDeriv R
  deriv_add := formalDeriv_add R
  deriv_const := formalDeriv_psC R
  leibniz_X := formalDeriv_mul_psX R
  repeated := fun a hh f hf => sep_repeated_factor R a hh f hf

/-- **見出し (M270F): 分離性データの存在**（任意の可換環上）。 -/
theorem separable_exists (R : CRing) : Nonempty (SeparableData R) :=
  ⟨separableWitness R⟩

end IUT
