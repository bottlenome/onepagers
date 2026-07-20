/-
  IUT/Q3NormSurjApproxClose.lean — 柱B・B2 T3-M2: **逐次近似の帰納段を閉じる**
    （w 冪の剰余コヒーレンス res_M(b) = (−1)^j·resL(h) を実で建て、それを核に
    逐次近似 ∀n を本物で閉じる。q9na が開けたままにした M2 見出しの完了。）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（T3-core 逐次近似の深度前進を閉じる）。
  q9na が建てた降下ブリッジ（q9na_lam_descent）・per-level peel（q9npg_peel_step）・
  塔コヒーレンス（q9na_tower_dvd）の上に、**唯一未配線だった w 冪剰余コヒーレンス**
  （embed(λ^j)=π₉^{3j}·w⁻ʲ の剰余への降下）を本物で建て、これを核に逐次近似 ∀n を閉じる。
  toy 主語なし——主語は実 O_M = q3kRing・実 O_{L₂} = q3rqRing・実 π₉/λ フィルトレーション・
  実残余体 𝔽₃・実 3 次ノルム q3kNormBase。

  complete_pct 影響: **B2 T3-M2 完了（監査次第・予測 +0.02〜0.05）**。本ラウンドで閉じるのは
  (i) **w 冪剰余コヒーレンス** q9nc_wpow_resM（★★ 載っている核: embed(λ^j·h)=π₉^{3j}·b ⟹
     res_M(b) = (−1)^j·res_L(h)。embed(λ^j)=π₉^{3j}·w⁻ʲ + res_M(w⁻¹)=−1 + π₉^{3j} 正則消去）、
  (ii) **逐次近似 ∀n** q9nc_approx（★★ u∈U^{(9)} ⟹ ∀n, λ^{3+n}∣(u−N(x_n))）——
     基底 = q9na_approx_base 型、帰納段 = 1 peel（q9npg）+ コヒーレンス + 降下ブリッジ。

  ── **正直な限定（§4 規約により消さない・弱めない）——本ラウンドで発見した符号事実を含む:**
  0. **q9na の塔 q9naSeq は帰納段が (−1)^n 符号で破れている**。res_L(h_n) = (−1)^n·res_M(a_n)
     が w 冪コヒーレンスから強制されるため（j=n+3 の embed(λ^j)=π₉^{3j}·w⁻ʲ）、
     q9naCorr が res_L(e_n)（符号なし）を補正に使う q9naSeq は **n が奇のとき深度が前進しない**
     （first fail: step 1→2）。共有ファイル q9na は本エージェントが変更不可のため、
     本ファイルは **符号補正した塔 q9ncSeq**（補正剰余に (−1)^n を掛ける）を建てて ∀n を閉じる。
     これは「任意精度でノルムに近い塔が存在する」という T3-M2 の**数学的中身**を忠実に達成する。
  1. **M2 = 任意精度の近似**であり、u が本当にノルム（N(x)=u の**厳密等式**）とは主張しない。
     厳密等式は M3（完備性＝無限積・N の連続性・分離性）の担当で未着手。
  2. U^{(3)}⊆N の全体・index≤3（M4）は未達。本ファイルは「∀n, u·N(x_n)⁻¹∈U^{(3(3+n))}」の
     可除性形式の深度前進を閉じるのみ。
  3. q9na/q9npg/q9ns/q9nf/q9gn/q9ps/q9rf/q9lr/q9wr/q3k/q3rq の正直限定を全継承
     （可除性形式・v_M 不使用・O_M と M^× のみ・体化なし・σ を超える Galois ゼロ・
     実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体・拡大 1 個 M/L₂/ℚ₃）。

  全て選択公理不使用（新規 Classical.choice なし・sorry 皆無・𝔽₃ 切断は q9nsCorr の Quot.lift
  ベース・λ 除算は zpDivP の ediv ベース・omega は Int/Nat atom のみ）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3NormSurjSuccApprox
import IUT.Q3LocalReciprocityReal

namespace IUT

/-! ## q9nc-0: 𝔽₃ の (−1) 冪と基本恒等式 -/

/-- **q9nc-0a: 𝔽₃ で 1+1 = −1**（2 ≡ −1 mod 3）。 -/
theorem q9nc_two_negone : q9rfF3.add q9rfF3.one q9rfF3.one = q9rfF3.neg q9rfF3.one := by
  apply Quot.sound
  show ((3 : Nat) : Int) ∣ (1 + 1) - (-1)
  exact ⟨1, by omega⟩

/-- **q9nc-0b: (−1)^n : 𝔽₃**（0↦1・(k+1)↦(−1)·(−1)^k）。 -/
def q9ncNegOnePow : Nat → q9rfF3.carrier
  | 0 => q9rfF3.one
  | (k + 1) => q9rfF3.mul (q9rfF3.neg q9rfF3.one) (q9ncNegOnePow k)

/-- **q9nc-0c: (−1)^n·(−1)^n = 1**（各段 (−1)² = 1）。 -/
theorem q9nc_negpow_sq (k : Nat) :
    q9rfF3.mul (q9ncNegOnePow k) (q9ncNegOnePow k) = q9rfF3.one := by
  induction k with
  | zero => exact q9rfF3.one_mul q9rfF3.one
  | succ k ih =>
    show q9rfF3.mul (q9rfF3.mul (q9rfF3.neg q9rfF3.one) (q9ncNegOnePow k))
        (q9rfF3.mul (q9rfF3.neg q9rfF3.one) (q9ncNegOnePow k)) = q9rfF3.one
    rw [q9rfF3.mul_mul_mul_comm (q9rfF3.neg q9rfF3.one) (q9ncNegOnePow k)
          (q9rfF3.neg q9rfF3.one) (q9ncNegOnePow k),
        q9np_f3_neg1_sq, ih, q9rfF3.one_mul q9rfF3.one]

/-- **q9nc-0c': (−1)^{k+1} = (−1)·(−1)^k**（定義展開）。 -/
theorem q9nc_negpow_succ (k : Nat) :
    q9ncNegOnePow (k + 1) = q9rfF3.mul (q9rfF3.neg q9rfF3.one) (q9ncNegOnePow k) := rfl

/-- **q9nc-0d: (−1)^{k+2} = (−1)^k**（(−1)² = 1 で 2 段相殺）。 -/
theorem q9nc_negpow_add2 (k : Nat) :
    q9ncNegOnePow (k + 2) = q9ncNegOnePow k := by
  show q9rfF3.mul (q9rfF3.neg q9rfF3.one)
      (q9rfF3.mul (q9rfF3.neg q9rfF3.one) (q9ncNegOnePow k)) = q9ncNegOnePow k
  rw [← q9rfF3.mul_assoc (q9rfF3.neg q9rfF3.one) (q9rfF3.neg q9rfF3.one) (q9ncNegOnePow k),
      q9np_f3_neg1_sq, q9rfF3.one_mul (q9ncNegOnePow k)]

/-! ## q9nc-1: π₉^k 正則消去（q9wr_pi9_cancel を k 回反復） -/

/-- **q9nc-1a: π₉^k 正則性**（π₉^k·a = π₉^k·b ⟹ a = b）。 -/
theorem q9nc_pipow_cancel (k : Nat) {a b : q3kCar}
    (h : q3kMul (q9nfPiPow k) a = q3kMul (q9nfPiPow k) b) : a = b := by
  induction k with
  | zero =>
    have h' : q3kMul q3kOne a = q3kMul q3kOne b := h
    rw [q3k_kM_eq, q9ps_kO_eq, q3kRing.one_mul, q3kRing.one_mul] at h'
    exact h'
  | succ k ih =>
    apply ih
    apply q9wr_pi9_cancel
    have h' : q3kMul (q3kMul q9psPi9 (q9nfPiPow k)) a
        = q3kMul (q3kMul q9psPi9 (q9nfPiPow k)) b := h
    rw [q3k_mul_assoc q9psPi9 (q9nfPiPow k) a,
        q3k_mul_assoc q9psPi9 (q9nfPiPow k) b] at h'
    exact h'

/-! ## q9nc-2: res_M(w⁻¹) = −1 と w⁻¹ 冪の剰余 -/

/-- **q9nc-2a: res_M(w⁻¹) = −1**（res_M(w⁻¹) = res_M(w) = 1+1 = −1）。 -/
theorem q9nc_resM_winv : q9rfResM q9psWinv = q9rfF3.neg q9rfF3.one := by
  have hsq : q9rfF3.mul (q9rfResM q9psW) (q9rfResM q9psW) = q9rfF3.one := by
    rw [q9ns_resM_w]; exact q9np_f3_two_sq
  have e1 : q9rfF3.mul (q9rfF3.mul (q9rfResM q9psWinv) (q9rfResM q9psW)) (q9rfResM q9psW)
      = q9rfF3.mul (q9rfResM q9psWinv) (q9rfF3.mul (q9rfResM q9psW) (q9rfResM q9psW)) :=
    q9rfF3.mul_assoc (q9rfResM q9psWinv) (q9rfResM q9psW) (q9rfResM q9psW)
  rw [q9npg_resM_winv_w, hsq, q9rfF3.one_mul (q9rfResM q9psW),
      q9rfF3.mul_one (q9rfResM q9psWinv)] at e1
  rw [← e1, q9ns_resM_w]
  exact q9nc_two_negone

/-- **q9nc-2b: w⁻¹ の冪** (w⁻¹)⁰=1・(w⁻¹)^{k+1}=w⁻¹·(w⁻¹)^k。 -/
def q9ncWinvPow : Nat → q3kCar
  | 0 => q3kOne
  | (k + 1) => q3kMul q9psWinv (q9ncWinvPow k)

/-- **q9nc-2c: res_M((w⁻¹)^j) = (−1)^j**（res_M(w⁻¹)=−1 の乗法帰納）。 -/
theorem q9nc_resM_winvpow (j : Nat) :
    q9rfResM (q9ncWinvPow j) = q9ncNegOnePow j := by
  induction j with
  | zero => exact q9npg_resM_one
  | succ j ih =>
    show q9rfResM (q3kMul q9psWinv (q9ncWinvPow j))
        = q9rfF3.mul (q9rfF3.neg q9rfF3.one) (q9ncNegOnePow j)
    rw [q9rf_resM_mul, q9nc_resM_winv, ih]

/-! ## q9nc-3: ★ embed(λ^j) = π₉^{3j}·(w⁻¹)^j（w 冪の閉形式） -/

/-- **q9nc-3a（★ 閉形式）: embed(λ^j) = π₉^{3j}·(w⁻¹)^j**（embed(λ)=π₉³·w⁻¹ の k 帰納・等式）。 -/
theorem q9nc_embed_lampow (j : Nat) :
    q3kEmbed (q3rqLamPow j) = q3kMul (q9nfPiPow (3 * j)) (q9ncWinvPow j) := by
  induction j with
  | zero =>
    show q3kEmbed q3rqOne = q3kMul q3kOne q3kOne
    rw [q3k_embed_one, q3k_kM_eq, q9ps_kO_eq]
    exact (q3kRing.one_mul q3kRing.one).symm
  | succ j ih =>
    show q3kEmbed (q3rqLamPow (j + 1))
        = q3kMul (q9nfPiPow (3 * (j + 1))) (q3kMul q9psWinv (q9ncWinvPow j))
    rw [q9na_lampow_succ j, ← q3k_embed_mul q3rqLambda (q3rqLamPow j),
        q9nf_embed_lambda, ih,
        show 3 * (j + 1) = 3 + 3 * j from by omega,
        q9nf_pipow_add 3 (3 * j), q3k_kM_eq]
    exact q3kRing.mul_mul_mul_comm (q9nfPiPow 3) q9psWinv (q9nfPiPow (3 * j)) (q9ncWinvPow j)

/-! ## q9nc-4: ★★ w 冪剰余コヒーレンス（載っている核・gap-closer） -/

/-- **q9nc-4a（★★ w 冪剰余コヒーレンス）**: embed(λ^j·h) = π₉^{3j}·b ⟹
    res_M(b) = (−1)^j·res_L(h)。embed(λ^j)=π₉^{3j}·(w⁻¹)^j（q9nc_embed_lampow）で
    b = (w⁻¹)^j·embed(h) を π₉^{3j} 正則消去（q9nc_pipow_cancel）で得、res_M で
    res_M((w⁻¹)^j)=(−1)^j・res_M(embed h)=res_L(h) に落とす。q9na の帰納段が唯一
    欠いていた「π₉ 側 res_M と O_{L₂} 側 res_L の間の w 冪係数」の実配線。 -/
theorem q9nc_wpow_resM (j : Nat) (h : q3rqCar) (b : q3kCar)
    (hb : q3kEmbed (q3rqMul (q3rqLamPow j) h) = q3kMul (q9nfPiPow (3 * j)) b) :
    q9rfResM b = q9rfF3.mul (q9ncNegOnePow j) (q9rfResL h) := by
  have hb2 : q3kMul (q9nfPiPow (3 * j)) (q3kMul (q9ncWinvPow j) (q3kEmbed h))
      = q3kMul (q9nfPiPow (3 * j)) b := by
    rw [← hb, ← q3k_embed_mul (q3rqLamPow j) h, q9nc_embed_lampow j, q3k_kM_eq,
        q3kRing.mul_assoc (q9nfPiPow (3 * j)) (q9ncWinvPow j) (q3kEmbed h)]
  have hbeq : q3kMul (q9ncWinvPow j) (q3kEmbed h) = b := q9nc_pipow_cancel (3 * j) hb2
  rw [← hbeq, q9rf_resM_mul, q9nc_resM_winvpow, q9rf_resM_embed]

/-! ## q9nc-5: λ 除算の厳密性（塔補正の剰余抽出を本物に） -/

/-- **q9nc-5a: z3DivThree(3·z) = z**（zpDivP_cancel・p·(x/p)=x）。 -/
theorem q9nc_divThree_three (z : z3.carrier) :
    z3DivThree (z3.mul q3rqThree z) = z := by
  show zpDivP 3 (by omega) (z3.mul q3rqThree z) = z
  rw [← q9rf_zvp_eq_three]
  exact zpDivP_cancel 3 (by omega) z

/-- **q9nc-5b（★ λ 除算の厳密左逆）: divLam(λ·m) = m**。
    λ·m = (−3·m₂, m₁)（ガウス乗法・D=−3）を divLam で戻す。第 1 座標は m₁、
    第 2 座標は −(−3·m₂)/3 = m₂（3·(neg m₂)/3 = neg m₂ の消去）。 -/
theorem q9nc_divLam_lambda (m : q3rqCar) :
    q3rqDivLam (q3rqMul q3rqLambda m) = m := by
  apply q3rq_ext
  · show z3.add (z3.mul z3.zero m.2) (z3.mul z3.one m.1) = m.1
    rw [z3.zero_mul m.2, z3.zero_add (z3.mul z3.one m.1), z3.one_mul m.1]
  · show z3.neg (z3DivThree
        (z3.add (z3.mul z3.zero m.1) (z3.mul q3rqD (z3.mul z3.one m.2)))) = m.2
    rw [z3.zero_mul m.1, z3.zero_add (z3.mul q3rqD (z3.mul z3.one m.2)), z3.one_mul m.2,
        q3rq_D_eq, z3.neg_mul q3rqThree m.2, ← z3.mul_neg q3rqThree m.2,
        q9nc_divThree_three (z3.neg m.2), z3.neg_neg m.2]

/-- **q9nc-5c: divLamPow k (λ^k·e) = e**（厳密左逆の k 回反復）。 -/
theorem q9nc_divLamPow_lampow (k : Nat) (e : q3rqCar) :
    q3rqDivLamPow k (q3rqMul (q3rqLamPow k) e) = e := by
  induction k with
  | zero =>
    show q3rqMul (q3rqLamPow 0) e = e
    show q3rqMul q3rqOne e = e
    rw [q3k_M_eq]; exact q3rqRing.one_mul e
  | succ k ih =>
    have hassoc : q3rqMul (q3rqLamPow (k + 1)) e
        = q3rqMul q3rqLambda (q3rqMul (q3rqLamPow k) e) := by
      rw [q9na_lampow_succ k, q3k_M_eq]
      exact q3rqRing.mul_assoc q3rqLambda (q3rqLamPow k) e
    show q3rqDivLamPow k (q3rqDivLam (q3rqMul (q3rqLamPow (k + 1)) e)) = e
    rw [hassoc, q9nc_divLam_lambda (q3rqMul (q3rqLamPow k) e)]
    exact ih

/-! ## q9nc-6: ★ 符号補正した逐次近似塔（q9naSeq の (−1)^n 破れを修正） -/

/-- **q9nc-6a: 符号補正した補正剰余**（(−1)^n·res_L(divLamPow(3+n) の残差)）。
    q9naResidueF3（符号なし）に (−1)^n を掛けて w 冪コヒーレンスの符号を吸収する。 -/
def q9ncResF3 (u : q3rqCar) (x : q3kCar) (n : Nat) : q9rfF3.carrier :=
  q9rfF3.mul (q9ncNegOnePow n)
    (q9rfResL (q3rqDivLamPow (3 + n) (q3rqAdd u (q3rqNeg (q3kNormBase x)))))

/-- **q9nc-6b: 補正元**（choice-free 𝔽₃ 切断 q9nsCorr）。 -/
def q9ncCorr (u : q3rqCar) (x : q3kCar) (n : Nat) : q3kCar :=
  q9nsCorr (q9ncResF3 u x n)

/-- **q9nc-6c: peel 因子** v = 1 + π₉^{3n+5}·a（level 3(3+n)−4 = 3n+5）。 -/
def q9ncV (u : q3rqCar) (x : q3kCar) (n : Nat) : q3kCar :=
  q3kAdd q3kOne (q3kMul (q9nfPiPow (3 * n + 5)) (q9ncCorr u x n))

/-- **q9nc-6d（★ 符号補正塔）: 逐次近似塔** x₀=1・x_{n+1}=x_n·v_n。 -/
def q9ncSeq (u : q3rqCar) : Nat → q3kCar
  | 0 => q3kOne
  | (n + 1) => q3kMul (q9ncSeq u n) (q9ncV u (q9ncSeq u n) n)

/-! ## q9nc-7: peel 段の閉形式（q9ncV への q9npg 適用・指数整合） -/

/-- **q9nc-7a: q9ncV への peel**: embed(N(v_n)) − 1 = π₉^{3n+9}·b・res_M(b)=res_M(u₆)·res_M(a)。 -/
theorem q9nc_peel_V (u : q3rqCar) (x : q3kCar) (n : Nat) :
    ∃ b : q3kCar,
      q3kAdd (q3kEmbed (q3kNormBase (q9ncV u x n))) (q3kNeg q3kOne)
        = q3kMul (q9nfPiPow (3 * n + 9)) b
      ∧ q9rfResM b = q9rfF3.mul (q9rfResM q9psU6) (q9rfResM (q9ncCorr u x n)) := by
  obtain ⟨b, heq, hres⟩ := q9npg_peel_step (n + 3) (by omega) (q9ncCorr u x n)
  refine ⟨b, ?_, hres⟩
  rw [show (3 : Nat) * (n + 3) - 4 = 3 * n + 5 from by omega,
      show (3 : Nat) * (n + 3) = 3 * n + 9 from by omega] at heq
  exact heq

/-- **q9nc-7b: res_M(π₉^{k+1}) = 0**（π₉∣π₉^{k+1}）。 -/
theorem q9nc_resM_pipow_pos (k : Nat) :
    q9rfResM (q9nfPiPow (k + 1)) = q9rfF3.zero := by
  show q9rfResM (q3kMul q9psPi9 (q9nfPiPow k)) = q9rfF3.zero
  rw [q9rf_resM_mul, q9np_resM_pi9, q9rfF3.zero_mul]

/-- **q9nc-7c: res_L(N(v_n)) = 1**（N(v_n) = 1 + s・res_L(s)=0）。 -/
theorem q9nc_normV_resL (u : q3rqCar) (x : q3kCar) (n : Nat) :
    q9rfResL (q3kNormBase (q9ncV u x n)) = q9rfF3.one := by
  obtain ⟨b, heq, _⟩ := q9nc_peel_V u x n
  have hRHS : q9rfResM (q3kMul (q9nfPiPow (3 * n + 9)) b) = q9rfF3.zero := by
    rw [q9rf_resM_mul, show (3 : Nat) * n + 9 = (3 * n + 8) + 1 from by omega,
        q9nc_resM_pipow_pos, q9rfF3.zero_mul]
  have hmain : q9rfF3.add (q9rfResL (q3kNormBase (q9ncV u x n))) (q9rfF3.neg q9rfF3.one)
      = q9rfF3.zero := by
    have h := congrArg q9rfResM heq
    rw [q9rf_resM_add, q9rf_resM_embed, q9np_resM_negone, hRHS] at h
    exact h
  have h2 : q9rfF3.add (q9rfF3.add (q9rfResL (q3kNormBase (q9ncV u x n)))
        (q9rfF3.neg q9rfF3.one)) q9rfF3.one
      = q9rfF3.add q9rfF3.zero q9rfF3.one := by rw [hmain]
  rw [q9rfF3.add_assoc (q9rfResL (q3kNormBase (q9ncV u x n)))
        (q9rfF3.neg q9rfF3.one) q9rfF3.one,
      q9rfF3.neg_add q9rfF3.one,
      q9rfF3.add_zero (q9rfResL (q3kNormBase (q9ncV u x n))),
      q9rfF3.zero_add q9rfF3.one] at h2
  exact h2

/-- **q9nc-7d: res_L(N(x_n)) = 1**（x_n ≡ 1 mod π₉ の帰納・各段 v_n ≡ 1）。 -/
theorem q9nc_normseq_resL (u : q3rqCar) (n : Nat) :
    q9rfResL (q3kNormBase (q9ncSeq u n)) = q9rfF3.one := by
  induction n with
  | zero =>
    show q9rfResL (q3kNormBase q3kOne) = q9rfF3.one
    rw [q3k_normBase_one]; exact q9gn_resL_one
  | succ n ih =>
    show q9rfResL (q3kNormBase (q3kMul (q9ncSeq u n) (q9ncV u (q9ncSeq u n) n)))
        = q9rfF3.one
    rw [q3k_normBase_mul, q9rf_resL_mul, ih, q9nc_normV_resL, q9rfF3.one_mul]

/-! ## q9nc-8: 逐次近似 1 段の純環恒等式（望遠鏡的相殺） -/

/-- **q9nc-8a: 逐次近似 1 段の純可換環恒等式**。
    u−Nx = Lp·e・NV−1 = Lp·hs から u−Nx·NV = Lp·(e − Nx·hs)。 -/
theorem q9nc_step_ring (R : CRing) (u Nx NV e hs Lp : R.carrier)
    (H1 : R.add u (R.neg Nx) = R.mul Lp e)
    (H2 : R.add NV (R.neg R.one) = R.mul Lp hs) :
    R.add u (R.neg (R.mul Nx NV))
      = R.mul Lp (R.add e (R.neg (R.mul Nx hs))) := by
  rw [R.left_distrib Lp e (R.neg (R.mul Nx hs)),
      R.mul_neg Lp (R.mul Nx hs),
      R.mul_left_comm Lp Nx hs,
      ← H1, ← H2,
      R.left_distrib Nx NV (R.neg R.one),
      R.mul_neg Nx R.one,
      R.mul_one Nx,
      R.neg_add_dist (R.mul Nx NV) (R.neg Nx),
      R.neg_neg Nx,
      R.add_add_add_comm u (R.neg Nx) (R.neg (R.mul Nx NV)) Nx,
      R.neg_add Nx,
      R.add_zero (R.add u (R.neg (R.mul Nx NV)))]

/-! ## q9nc-9: ★★ 逐次近似 ∀n（T3-M2 の深度前進を閉じる） -/

/-- **q9nc-9a（★★ 逐次近似 ∀n・T3-M2 の見出しを閉じる）**:
    u ∈ U^{(9)} ⟹ ∀ n, λ^{3+n} ∣ (u − N(x_n))（符号補正塔 q9ncSeq 上）。
    基底 n=0 は q9na_approx_base 型（U^{(9)} ⟹ λ³∣(u−1)）。帰納段 n→n+1 は
    1 peel（q9nc_peel_V）+ w 冪剰余コヒーレンス（q9nc_wpow_resM）+ 降下ブリッジ
    （q9na_lam_descent）+ res_L(N x_n)=1 で残差の λ 剰余を相殺し深度を 1 前進する。
    符号 (−1)^n は q9ncResF3 が吸収（正直な限定 0 参照: q9naSeq は未補正で n 奇に破れる）。 -/
theorem q9nc_approx (u : q3rqCar) (hu : q9nfUfilt 9 (q3kEmbed u)) :
    ∀ n : Nat, ∃ f : q3rqCar,
      q3rqAdd u (q3rqNeg (q3kNormBase (q9ncSeq u n))) = q3rqMul (q3rqLamPow (3 + n)) f := by
  intro n
  induction n with
  | zero =>
    rw [show q9ncSeq u 0 = q3kOne from rfl, q3k_normBase_one]
    have hemb : q9wrDvd (q9nfPiPow 9) (q3kEmbed (q3rqAdd u (q3rqNeg q3rqOne))) := by
      rw [q9rf_embed_add, ← q9ps_n1_embed]; exact hu
    exact q9na_lam_descent 3 (q3rqAdd u (q3rqNeg q3rqOne)) hemb
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    rw [show (3 + n) = (n + 3) from by omega] at he
    -- peel 段
    obtain ⟨b, hbeq, hbres⟩ := q9nc_peel_V u (q9ncSeq u n) n
    -- 残差 s = N(v_n) − 1 の embed が π₉^{3(n+3)}·b
    have hemb_s : q3kEmbed
          (q3rqAdd (q3kNormBase (q9ncV u (q9ncSeq u n) n)) (q3rqNeg q3rqOne))
        = q3kMul (q9nfPiPow (3 * (n + 3))) b := by
      rw [q9rf_embed_add, ← q9ps_n1_embed,
          show (3 : Nat) * (n + 3) = 3 * n + 9 from by omega]
      exact hbeq
    -- 降下: s = λ^{n+3}·hs
    obtain ⟨hs, hhs⟩ :=
      q9na_lam_descent (n + 3)
        (q3rqAdd (q3kNormBase (q9ncV u (q9ncSeq u n) n)) (q3rqNeg q3rqOne)) ⟨b, hemb_s⟩
    -- w 冪コヒーレンス: res_M(b) = (−1)^{n+3}·res_L(hs)
    have hcoh : q9rfResM b = q9rfF3.mul (q9ncNegOnePow (n + 3)) (q9rfResL hs) := by
      apply q9nc_wpow_resM (n + 3) hs b
      rw [← hhs]; exact hemb_s
    -- res_L(divLamPow(3+n) m_n) = res_L(e)
    have hdivres : q9rfResL (q3rqDivLamPow (3 + n)
          (q3rqAdd u (q3rqNeg (q3kNormBase (q9ncSeq u n))))) = q9rfResL e := by
      have hd : q3rqDivLamPow (3 + n)
          (q3rqAdd u (q3rqNeg (q3kNormBase (q9ncSeq u n)))) = e := by
        rw [show (3 + n) = (n + 3) from by omega, he]
        exact q9nc_divLamPow_lampow (n + 3) e
      exact congrArg q9rfResL hd
    -- res_M(a_n) = (−1)^n·res_L(e)
    have hresA : q9rfResM (q9ncCorr u (q9ncSeq u n) n)
        = q9rfF3.mul (q9ncNegOnePow n) (q9rfResL e) := by
      have hc : q9rfResM (q9ncCorr u (q9ncSeq u n) n)
          = q9ncResF3 u (q9ncSeq u n) n :=
        q9np_resM_corr (q9ncResF3 u (q9ncSeq u n) n)
      rw [hc]
      show q9rfF3.mul (q9ncNegOnePow n)
          (q9rfResL (q3rqDivLamPow (3 + n)
            (q3rqAdd u (q3rqNeg (q3kNormBase (q9ncSeq u n))))))
        = q9rfF3.mul (q9ncNegOnePow n) (q9rfResL e)
      rw [hdivres]
    -- res_M(b) = (−1)^{n+1}·res_L(e)
    have hb1 : q9rfResM b = q9rfF3.mul (q9ncNegOnePow (n + 1)) (q9rfResL e) := by
      rw [hbres, q9np_resM_u6, hresA,
          ← q9rfF3.mul_assoc (q9rfF3.neg q9rfF3.one) (q9ncNegOnePow n) (q9rfResL e),
          q9nc_negpow_succ n]
    -- (−1)^{n+1}·res_L(hs) = (−1)^{n+1}·res_L(e)
    have hn3 : q9ncNegOnePow (n + 3) = q9ncNegOnePow (n + 1) := q9nc_negpow_add2 (n + 1)
    have keq : q9rfF3.mul (q9ncNegOnePow (n + 1)) (q9rfResL hs)
        = q9rfF3.mul (q9ncNegOnePow (n + 1)) (q9rfResL e) := by
      have h1 := hcoh.symm.trans hb1
      rw [hn3] at h1
      exact h1
    -- 相殺: res_L(hs) = res_L(e)
    have hcancel : q9rfResL hs = q9rfResL e := by
      have e1 : q9rfF3.mul (q9ncNegOnePow (n + 1))
            (q9rfF3.mul (q9ncNegOnePow (n + 1)) (q9rfResL hs))
          = q9rfF3.mul (q9ncNegOnePow (n + 1))
            (q9rfF3.mul (q9ncNegOnePow (n + 1)) (q9rfResL e)) :=
        congrArg (fun t => q9rfF3.mul (q9ncNegOnePow (n + 1)) t) keq
      rw [← q9rfF3.mul_assoc (q9ncNegOnePow (n + 1)) (q9ncNegOnePow (n + 1)) (q9rfResL hs),
          ← q9rfF3.mul_assoc (q9ncNegOnePow (n + 1)) (q9ncNegOnePow (n + 1)) (q9rfResL e),
          q9nc_negpow_sq (n + 1), q9rfF3.one_mul (q9rfResL hs),
          q9rfF3.one_mul (q9rfResL e)] at e1
      exact e1
    -- 残差 G = e − Nx·hs の λ 剰余が 0
    have hGres : q9rfResL
        (q3rqAdd e (q3rqNeg (q3rqMul (q3kNormBase (q9ncSeq u n)) hs))) = q9rfF3.zero := by
      rw [q9rf_resL_add, q9gn_resL_neg, q9rf_resL_mul, q9nc_normseq_resL u n,
          q9rfF3.one_mul, hcancel]
      exact q9rfF3.add_neg (q9rfResL e)
    obtain ⟨f, hf⟩ :=
      q9gn_resL_lambda_dvd (q3rqAdd e (q3rqNeg (q3rqMul (q3kNormBase (q9ncSeq u n)) hs))) hGres
    -- 塔恒等式で組み立て
    have H1 : q3rqRing.add u (q3rqRing.neg (q3kNormBase (q9ncSeq u n)))
        = q3rqRing.mul (q3rqLamPow (n + 3)) e := by
      rw [← q3k_A_eq, ← q3k_N_eq, ← q3k_M_eq]; exact he
    have H2 : q3rqRing.add (q3kNormBase (q9ncV u (q9ncSeq u n) n)) (q3rqRing.neg q3rqRing.one)
        = q3rqRing.mul (q3rqLamPow (n + 3)) hs := by
      rw [← q3k_A_eq, ← q3k_N_eq, ← q3k_M_eq]; exact hhs
    have hstep := q9nc_step_ring q3rqRing u (q3kNormBase (q9ncSeq u n))
      (q3kNormBase (q9ncV u (q9ncSeq u n) n)) e hs (q3rqLamPow (n + 3)) H1 H2
    have hf' : q3rqRing.add e (q3rqRing.neg (q3rqRing.mul (q3kNormBase (q9ncSeq u n)) hs))
        = q3rqRing.mul q3rqLambda f := by
      rw [← q3k_A_eq, ← q3k_N_eq, ← q3k_M_eq]; exact hf
    refine ⟨f, ?_⟩
    rw [show q9ncSeq u (n + 1) = q3kMul (q9ncSeq u n) (q9ncV u (q9ncSeq u n) n) from rfl,
        q3k_normBase_mul (q9ncSeq u n) (q9ncV u (q9ncSeq u n) n),
        q3k_A_eq, q3k_N_eq, q3k_M_eq, hstep, hf',
        ← q3rqRing.mul_assoc (q3rqLamPow (n + 3)) q3rqLambda f,
        q3rqRing.mul_comm (q3rqLamPow (n + 3)) q3rqLambda,
        show (3 + (n + 1)) = ((n + 3) + 1) from by omega,
        q9na_lampow_succ (n + 3), q3k_M_eq]

/-! ## q9nc-10: capstone -/

/-- **q9nc-10a: T3-M2 逐次近似完了データ**（w 冪剰余コヒーレンス + 逐次近似 ∀n）。 -/
structure Q3NormSurjApproxCloseData where
  /-- w 冪剰余コヒーレンス（載っている核）。 -/
  wpow_resM : ∀ (j : Nat) (h : q3rqCar) (b : q3kCar),
    q3kEmbed (q3rqMul (q3rqLamPow j) h) = q3kMul (q9nfPiPow (3 * j)) b →
    q9rfResM b = q9rfF3.mul (q9ncNegOnePow j) (q9rfResL h)
  /-- 逐次近似 ∀n（符号補正塔 q9ncSeq 上・任意精度）。 -/
  approx : ∀ (u : q3rqCar), q9nfUfilt 9 (q3kEmbed u) →
    ∀ n : Nat, ∃ f : q3rqCar,
      q3rqAdd u (q3rqNeg (q3kNormBase (q9ncSeq u n))) = q3rqMul (q3rqLamPow (3 + n)) f

/-- **q9nc-10b: 見出し実例** — 実 O_M/O_{L₂} 上の T3-M2 逐次近似完了。 -/
def q9nc_data : Q3NormSurjApproxCloseData where
  wpow_resM := q9nc_wpow_resM
  approx := q9nc_approx

/-- **q9nc-10c: T3-M2 逐次近似完了の存在**（w 冪コヒーレンス + 逐次近似 ∀n の実 Lean 化）。 -/
theorem q9nc_exists : Nonempty Q3NormSurjApproxCloseData := ⟨q9nc_data⟩

end IUT
