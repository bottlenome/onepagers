/-
  IUT/PadicSeries2.lean — M110F（柱B B-1 第三段: p 進級数和・第二層）

  M107F（IUT/PadicSeries.lean）が実構成した p 進級数和 zpSeriesSum に、
  O = ℤ_p[[X]]/(E) の完備性論法（B-1 第三段）で直接使う主 API を
  追加供給する: **スカラー倍**（zpMul との交換）・**m 段の頭出し分割**
  （Σ = 部分和 + πᵐ·尾部の和）・その系である**剰余の可除性**
  （Σ − 部分和 は πᵐ の倍数、witness 付き）。

  鍵となる技法: 全ての等式を **zpRing レベル**（成分ごとのレベル m へ
  降りずに、zpRing の公理 left_distrib / mul_assoc / add_assoc から
  直接）で閉じる。m 段の頭出し分割（本丸）は m についての帰納法で、
  帰納段は M107F-9c（zpSeriesSum_head）を尾部の和に一段適用し、
  left_distrib で πᵐ·(g(m) + π·尾部') を分配、πᵐ·π = π^{m+1}
  （rpow の succ 段 + mul_assoc）、zpSum の succ 段（zpSum_succ）と
  add_assoc で組み直す。添字の付け替え（(n+1)+m = n+(m+1) 等）は
  congrArg g (by omega) で処理する（Nat の純算術は omega 可、
  ∃ ゴール本体や intGrp.carrier 変数には使わない）。

  * M110F-1 `zpTerm_zero` — 第 n 項が 0：g が恒等的に 0 なら
    zpTerm g n = 0（CRing.mul_zero を zpRing レベルで直接適用）
  * M110F-2 `zpSeriesSum_zero_fun` — **零関数の級数和は 0**
  * M110F-3 `zpMul_swap` — zpMul の入れ替え簿記
    c·(a·b) = a·(c·b)（mul_comm/mul_assoc の組み合わせ）
  * M110F-4 `zpSum_smul` — 有限部分和のスカラー倍
    c·(Σ_{k<m} f k) = Σ_{k<m} (c·f k)（left_distrib の m 帰納）
  * M110F-5 `zpTerm_smul` — 第 n 項とスカラー倍の交換
    c·(π^n·g n) = π^n·(c·g n)（M110F-3 の適用）
  * M110F-6 `zpSeriesSum_smul` — **級数和のスカラー倍**
    c·Σg = Σ(c·g)（M110F-4/5 を全レベルへ）
  * M110F-7 `zpSeriesSum_split` — **本丸: m 段の頭出し分割**
    Σg = (Σ_{k<m} g_k の π 級数部分) + π^m·Σ(shift_m g)。
    m の帰納法（succ 段は zpSeriesSum_head 一段適用 + left_distrib +
    rpow succ + zpSum_succ + add_assoc）
  * M110F-8 `zpSeriesSum_tail_dvd` — **系: 剰余の可除性**
    Σg − (Σ_{k<m} g_k の部分和) は π^m の倍数（witness = 尾部の和、
    CRing.add_add_neg_cancel で移項）
  * M110F-9 `PadicSeriesSplitData` / `padicSeriesSplitData` /
    `padicSeriesSplit_exists` — 総括レコード（split・tail_dvd・smul
    を束ねた witness）

  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.PadicSeries

namespace IUT

/-! ## 零関数の級数和 -/

/-- **M110F-1: 第 n 項が 0** — g が恒等的に (zpRing p).zero なら
    zpTerm p g n = (zpRing p).zero（CRing.mul_zero をそのまま
    zpRing レベルで適用、defeq 越しに `exact` で処理）。 -/
theorem zpTerm_zero (p : Nat) (n : Nat) :
    zpTerm p (fun _ => (zpRing p).zero) n = (zpRing p).zero :=
  CRing.mul_zero (zpRing p) (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n)

/-- 有限部分和の零関数版: 全項が 0 なら部分和も 0。 -/
theorem zpSum_zero_fun (p : Nat) : ∀ m,
    zpSum p (zpTerm p (fun _ => (zpRing p).zero)) m = (zpRing p).zero := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    show (zpRing p).add
        (zpSum p (zpTerm p (fun _ => (zpRing p).zero)) m)
        (zpTerm p (fun _ => (zpRing p).zero) m)
      = (zpRing p).zero
    rw [ih, zpTerm_zero p m, (zpRing p).zero_add]

/-- **定理 (M110F-2): 零関数の級数和は 0**。 -/
theorem zpSeriesSum_zero_fun (p : Nat) (hp : 2 ≤ p) :
    zpSeriesSum p hp (fun _ => (zpRing p).zero) = (zpRing p).zero := by
  refine Subtype.ext ?_
  funext m
  rw [zpSeriesSum_partial p hp _ m, zpSum_zero_fun p m]

/-! ## スカラー倍 -/

/-- **M110F-3: zpMul の入れ替え簿記** c·(a·b) = a·(c·b)
    （mul_comm と mul_assoc を zpRing レベルで組み合わせる）。 -/
theorem zpMul_swap (p : Nat) (c a b : (Zp p).carrier) :
    zpMul p c (zpMul p a b) = zpMul p a (zpMul p c b) := by
  show (zpRing p).mul c ((zpRing p).mul a b) = (zpRing p).mul a ((zpRing p).mul c b)
  rw [← (zpRing p).mul_assoc, (zpRing p).mul_comm c a, (zpRing p).mul_assoc]

/-- **M110F-4: 有限部分和のスカラー倍** c·(zpSum f m) = zpSum (c·f) m
    （zpRing の left_distrib を m の帰納で積み上げる）。 -/
theorem zpSum_smul (p : Nat) (c : (Zp p).carrier) (f : Nat → (Zp p).carrier) :
    ∀ m, zpMul p c (zpSum p f m) = zpSum p (fun n => zpMul p c (f n)) m := by
  intro m
  induction m with
  | zero =>
    show zpMul p c (zpRing p).zero = (zpRing p).zero
    exact CRing.mul_zero (zpRing p) c
  | succ m ih =>
    show zpMul p c ((zpRing p).add (zpSum p f m) (f m))
      = (zpRing p).add (zpSum p (fun n => zpMul p c (f n)) m) (zpMul p c (f m))
    have hdist : zpMul p c ((zpRing p).add (zpSum p f m) (f m))
        = (zpRing p).add (zpMul p c (zpSum p f m)) (zpMul p c (f m)) :=
      (zpRing p).left_distrib c (zpSum p f m) (f m)
    rw [hdist, ih]

/-- **M110F-5: 第 n 項とスカラー倍の交換**
    c·(π^n·g n) = π^n·(c·g n)（M110F-3 の直接適用）。 -/
theorem zpTerm_smul (p : Nat) (c : (Zp p).carrier) (g : Nat → (Zp p).carrier)
    (n : Nat) :
    zpMul p c (zpTerm p g n) = zpTerm p (fun k => zpMul p c (g k)) n :=
  zpMul_swap p c (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n) (g n)

/-- **定理 (M110F-6): 級数和のスカラー倍** c·Σg = Σ(c·g)
    （M110F-4/5 をレベル m の値の一致経由で全レベルへ持ち上げる）。 -/
theorem zpSeriesSum_smul (p : Nat) (hp : 2 ≤ p) (c : (Zp p).carrier)
    (g : Nat → (Zp p).carrier) :
    zpMul p c (zpSeriesSum p hp g) = zpSeriesSum p hp (fun n => zpMul p c (g n)) := by
  refine Subtype.ext ?_
  funext m
  show zmodMul (p ^ m) (c.val m) ((zpSeriesSum p hp g).val m)
    = (zpSum p (zpTerm p (fun n => zpMul p c (g n))) m).val m
  rw [zpSeriesSum_partial p hp g m]
  have hval : zmodMul (p ^ m) (c.val m) ((zpSum p (zpTerm p g) m).val m)
      = (zpMul p c (zpSum p (zpTerm p g) m)).val m := rfl
  have hfun : (fun n => zpMul p c (zpTerm p g n))
      = zpTerm p (fun n => zpMul p c (g n)) := by
    funext n
    exact zpTerm_smul p c g n
  rw [hval, zpSum_smul p c (zpTerm p g) m, hfun]

/-! ## m 段の頭出し分割（本丸） -/

/-- **定理 (M110F-7): m 段の頭出し分割** —
    Σₙπⁿg(n) = (長さ m の部分和) + πᵐ·Σₙπⁿg(n+m)。
    m の帰納法。succ 段は zpSeriesSum_head を尾部に一段適用し、
    left_distrib で分配、πᵐ·π = π^{m+1}（mul_assoc）、zpSum_succ、
    add_assoc で組み直す（全て zpRing レベル、val へ降りない）。 -/
theorem zpSeriesSum_split (p : Nat) (hp : 2 ≤ p) (g : Nat → (Zp p).carrier) :
    ∀ m, zpSeriesSum p hp g = (zpRing p).add (zpSum p (zpTerm p g) m)
      (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
        (zpSeriesSum p hp (fun n => g (n + m)))) := by
  intro m
  induction m with
  | zero =>
    show zpSeriesSum p hp g = (zpRing p).add (zpRing p).zero
        (zpMul p (zpRing p).one (zpSeriesSum p hp (fun n => g (n + 0))))
    have hg : (fun n => g (n + 0)) = g := by
      funext n
      exact congrArg g (by omega)
    rw [hg, (zpRing p).zero_add]
    exact ((zpRing p).one_mul (zpSeriesSum p hp g)).symm
  | succ m ih =>
    show zpSeriesSum p hp g = (zpRing p).add (zpSum p (zpTerm p g) (m + 1))
        (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 1))
          (zpSeriesSum p hp (fun n => g (n + (m + 1)))))
    have hg0 : g (0 + m) = g m := congrArg g (by omega)
    have hgS : (fun n => g (n + 1 + m)) = fun n => g (n + (m + 1)) := by
      funext n
      exact congrArg g (by omega)
    have hhead : zpSeriesSum p hp (fun n => g (n + m))
        = (zpRing p).add (g m)
          (zpMul p ((toZp p).map ((p : Nat) : Int))
            (zpSeriesSum p hp (fun n => g (n + (m + 1))))) := by
      rw [zpSeriesSum_head p hp (fun n => g (n + m)), hg0, hgS]
    have hdist : zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
        ((zpRing p).add (g m)
          (zpMul p ((toZp p).map ((p : Nat) : Int))
            (zpSeriesSum p hp (fun n => g (n + (m + 1))))))
        = (zpRing p).add
          (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m) (g m))
          (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
            (zpMul p ((toZp p).map ((p : Nat) : Int))
              (zpSeriesSum p hp (fun n => g (n + (m + 1)))))) :=
      (zpRing p).left_distrib
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m) (g m)
        (zpMul p ((toZp p).map ((p : Nat) : Int))
          (zpSeriesSum p hp (fun n => g (n + (m + 1)))))
    have hterm : zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m) (g m)
        = zpTerm p g m := rfl
    have hpow : zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
        (zpMul p ((toZp p).map ((p : Nat) : Int))
          (zpSeriesSum p hp (fun n => g (n + (m + 1)))))
        = zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 1))
          (zpSeriesSum p hp (fun n => g (n + (m + 1)))) :=
      ((zpRing p).mul_assoc
        (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
        ((toZp p).map ((p : Nat) : Int))
        (zpSeriesSum p hp (fun n => g (n + (m + 1))))).symm
    have hstep : zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
        (zpSeriesSum p hp (fun n => g (n + m)))
        = (zpRing p).add (zpTerm p g m)
          (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 1))
            (zpSeriesSum p hp (fun n => g (n + (m + 1))))) := by
      rw [hhead, hdist, hterm, hpow]
    rw [ih, hstep, zpSum_succ p (zpTerm p g) m]
    exact ((zpRing p).add_assoc (zpSum p (zpTerm p g) m) (zpTerm p g m)
      (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) (m + 1))
        (zpSeriesSum p hp (fun n => g (n + (m + 1)))))).symm

/-! ## 系: 剰余の可除性 -/

/-- **定理 (M110F-8): 剰余の可除性** — Σg から長さ m の部分和を引いた
    残余は πᵐ の倍数（witness = 尾部の和、M110F-7 の分割を
    CRing.add_add_neg_cancel で移項）。 -/
theorem zpSeriesSum_tail_dvd (p : Nat) (hp : 2 ≤ p) (g : Nat → (Zp p).carrier)
    (m : Nat) :
    ∃ e, (zpRing p).add (zpSeriesSum p hp g)
        ((zpRing p).neg (zpSum p (zpTerm p g) m))
      = zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m) e := by
  refine ⟨zpSeriesSum p hp (fun n => g (n + m)), ?_⟩
  rw [zpSeriesSum_split p hp g m]
  exact CRing.add_add_neg_cancel (zpRing p) (zpSum p (zpTerm p g) m)
    (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
      (zpSeriesSum p hp (fun n => g (n + m))))

/-! ## 総括レコード -/

/-- **定理 (M110F-9a): p 進級数和の第二層インターフェース** —
    m 段の頭出し分割・剰余の可除性・スカラー倍を束ねた構造。
    O の完備性論法（B-1 第三段）で使う統一インターフェース。 -/
structure PadicSeriesSplitData (p : Nat) (hp : 2 ≤ p) where
  split : ∀ (g : Nat → (Zp p).carrier) (m : Nat),
    zpSeriesSum p hp g = (zpRing p).add (zpSum p (zpTerm p g) m)
      (zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m)
        (zpSeriesSum p hp (fun n => g (n + m))))
  tail_dvd : ∀ (g : Nat → (Zp p).carrier) (m : Nat), ∃ e,
    (zpRing p).add (zpSeriesSum p hp g)
        ((zpRing p).neg (zpSum p (zpTerm p g) m))
      = zpMul p (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) m) e
  smul : ∀ (c : (Zp p).carrier) (g : Nat → (Zp p).carrier),
    zpMul p c (zpSeriesSum p hp g) = zpSeriesSum p hp (fun n => zpMul p c (g n))

/-- **定理 (M110F-9b): witness** — zpSeriesSum が PadicSeriesSplitData を
    完全証明で充足する（choice 不使用）。 -/
def padicSeriesSplitData (p : Nat) (hp : 2 ≤ p) : PadicSeriesSplitData p hp where
  split := zpSeriesSum_split p hp
  tail_dvd := zpSeriesSum_tail_dvd p hp
  smul := zpSeriesSum_smul p hp

/-- **定理 (M110F-9c)**: PadicSeriesSplitData は充足可能（witness 存在）。 -/
theorem padicSeriesSplit_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (PadicSeriesSplitData p hp) :=
  ⟨padicSeriesSplitData p hp⟩

end IUT
