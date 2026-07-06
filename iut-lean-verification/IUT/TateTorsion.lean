/-
  IUT/TateTorsion.lean — M314F: Tate 曲線の n-捻れ部分群 E_q[n]（IUT の l-捻れ）

  ── 主要成果の分類: **[実]**（本物の体 K の乗法群 K^× 上に建てた本物の Tate 曲線
  E_q = K^×/q^ℤ（M309F）の **n-捻れ部分群 E_q[n] を本物の部分群として実構成**する。
  Mochizuki の IUT はエタールテータ Θ を **l-捻れ点**（l 素数）で評価し、その値の
  遠アーベル復元を行う。E_q[n] はその評価点が住む中心対象である）。

  complete_pct 影響: **柱A「Tate 曲線の捻れ点＝IUT の l-捻れ」の本物の先行建設**。
  既存 `IUT/TateCurve.lean`（M309F）は E_q = K^×/q^ℤ・整数冪 tateZpow・q^ℤ 部分群・
  点の周期性 [u]=[qu] を本物で建てたが、**n-捻れ部分群 E_q[n]（n·[u]=0 なる点の集合）
  そのもの**は無かった。本ファイルはそれを、K^× の中で **uⁿ∈q^ℤ を満たす u 全体**（=
  E_q[n] の K^× への引き戻し）として**本物の部分群 `tateTorSubgroup`** に実構成し、
  さらに (i) μ_n（1 の n 乗根 ζⁿ=1）が捻れ部分群であること、(ii) q の n 乗根 w（wⁿ=q）
  の類が n-捻れであること、(iii) その **q^{1/n} 方向の位数がちょうど n であること**
  （付値 v による本物の証明: wᵏ∈q^ℤ ⟹ n∣k）を core Lean のみで完全証明する。

  * M314F-1 補題 `tateTorOnePow` / `tateTorMulPow` / `tateTorInvPow` / `tateTorInvOne`
    — 群冪の基本則（1ⁿ=1、可換群で (ab)ⁿ=aⁿbⁿ、(a⁻¹)ⁿ=(aⁿ)⁻¹）。部分群性の核。
  * M314F-2 `tateTorSubgroup K q n` — **n-捻れ部分群 E_q[n]**（K^× の中で uⁿ∈q^ℤ を
    満たす u 全体）を**本物の `Subgroup (K^×)`** として実構成（1∈・積閉・逆元閉を
    tateTorMulPow/tateTorInvPow から完全証明）。
  * M314F-3 `tateTorMuSubgroup K n` — **μ_n = {ζ | ζⁿ=1}**（1 の n 乗根）を本物の
    部分群として実構成。`tateTor_mu_sub` で **μ_n ⊆ E_q[n]**（ζⁿ=1=q⁰∈q^ℤ）。
  * M314F-4 `tateTorQrootMem` — **q の n 乗根 w（wⁿ=q）の類 [w] は n-捻れ**
    （[w]ⁿ=[q]=[1]、wⁿ=q∈q^ℤ）。witness 形（分離閉包での根の存在は柱A 後続）。
  * M314F-5 付値による**位数 n の本物の証明** `tateTorInvVal` / `tateTorZpowVal` /
    `tateTorQrootOrder` — v(q)=n·v(w) の下で **wᵏ∈q^ℤ ⟹ n∣k**（q^{1/n} 方向の
    位数がちょうど n であることの本物の核）。整数冪 q^j の付値 v(q^j)=v(q)·j も本物で。
  * M314F-6 capstone `TateTorsionData` / `tateTor_exists` / `tateTor_mu_in_torsion` /
    `tateTor_prime_example`（n=l 素数で E_q[l]・μ_l⊆E_q[l]、IUT の l-捻れ）。

  正直な限定（何が本物で何が骨組みか）:
  - **本物**: E_q[n] が K^× の**本物の部分群**（1∈・積閉・逆元閉を完全証明、sorry 皆無・
    新規 choice 皆無）、μ_n が**本物の部分群**かつ **μ_n ⊆ E_q[n]**、q の n 乗根 w の類が
    n-捻れであること、そして **q^{1/n} 方向の位数がちょうど n（wᵏ∈q^ℤ ⟹ n∣k）が付値で
    完全証明**。整数冪 q^j の付値公式 v(q^j)=v(q)·j（全整数 j）も本物。
  - **q^{1/n}（wⁿ=q）は witness で受け取る**: n 乗して q になる元 w の存在（分離閉包での
    n 乗根の存在）そのものは柱A の後続。位数 n の証明は「w が与えられ v(w)=d(≠0) のとき」
    の条件付き本物（正 valuation v(w)>0 の具体構成は柱B ℤ_p 接続後続。M301F の
    trivialValuation は rank 0 で正 valuation の元を持たない）。
  - **E_q[n] ≅ (ℤ/n)² の完全な構造定理は骨組み**: μ_n 方向と q^{1/n} 方向がそれぞれ位数 n
    を持つ本物までで、直積分解 E_q[n]=μ_n × ⟨q^{1/n}⟩ の完全性（両因子の交わりが自明で
    生成すること）は骨組み。μ_n≅ℤ/n（K に原始 n 乗根がある場合）も後続。
  - **テータの l-捻れ点評価（IUT の本丸）は柱E 後続**: ここは E_q[n] の部分群構造と
    位数までで、Θ|E_q[l] の値と遠アーベル復元は M308F EtaleThetaReal 系の後続。

  全て選択公理不使用（新規 choice を証明本体に導入しない）。禁止タクティク不使用。
  共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
-/
import IUT.TateCurve

namespace IUT

/-! ## M314F-1: 群冪の基本則（部分群性の核） -/

/-- **1ⁿ = 1**（単位元の冪は単位元）。 -/
theorem tateTorOnePow (G : Grp) : ∀ n : Nat, tateNpow G G.one n = G.one := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show G.mul (tateNpow G G.one k) G.one = G.one
    rw [ih, G.mul_one]

/-- **(ab)ⁿ = aⁿ·bⁿ**（可換群での冪の乗法性）。step で bᵏ·a = a·bᵏ を使い並べ替える。 -/
theorem tateTorMulPow (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (a b : G.carrier) :
    ∀ n : Nat, tateNpow G (G.mul a b) n = G.mul (tateNpow G a n) (tateNpow G b n) := by
  intro n
  induction n with
  | zero =>
    show G.one = G.mul G.one G.one
    rw [G.one_mul]
  | succ k ih =>
    show G.mul (tateNpow G (G.mul a b) k) (G.mul a b)
        = G.mul (G.mul (tateNpow G a k) a) (G.mul (tateNpow G b k) b)
    rw [ih,
      G.mul_assoc (tateNpow G a k) (tateNpow G b k) (G.mul a b),
      ← G.mul_assoc (tateNpow G b k) a b,
      hc (tateNpow G b k) a,
      G.mul_assoc a (tateNpow G b k) b,
      ← G.mul_assoc (tateNpow G a k) a (G.mul (tateNpow G b k) b)]

/-- **inv(1) = 1**。 -/
theorem tateTorInvOne (G : Grp) : G.inv G.one = G.one :=
  (G.inv_eq_of_mul_eq_one (G.one_mul G.one)).symm

/-- **(a⁻¹)ⁿ = (aⁿ)⁻¹**（可換群での冪の逆元）。aⁿ·(a⁻¹)ⁿ=(a·a⁻¹)ⁿ=1ⁿ=1 から。 -/
theorem tateTorInvPow (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (a : G.carrier) (n : Nat) :
    tateNpow G (G.inv a) n = G.inv (tateNpow G a n) := by
  have h : G.mul (tateNpow G a n) (tateNpow G (G.inv a) n) = G.one := by
    rw [← tateTorMulPow G hc a (G.inv a) n, G.mul_inv]
    exact tateTorOnePow G n
  exact G.inv_eq_of_mul_eq_one h

/-! ## M314F-2: n-捻れ部分群 E_q[n] = { u ∈ K^× | uⁿ ∈ q^ℤ } -/

/-- **n-捻れ部分群 E_q[n]** — Tate 曲線 E_q = K^×/q^ℤ の n-捻れ（n·[u]=0）の
    K^× への引き戻し。すなわち **uⁿ ∈ q^ℤ を満たす u ∈ K^× 全体**。乗法群 K^× の
    本物の部分群であることを、単位（1ⁿ=1∈q^ℤ）・積閉（(uv)ⁿ=uⁿvⁿ∈q^ℤ）・
    逆元閉（(u⁻¹)ⁿ=(uⁿ)⁻¹∈q^ℤ）で完全証明する。IUT のテータ評価点 E_q[l] の母胎。 -/
def tateTorSubgroup (K : IUTField) (q : (tateMultGroup K).carrier) (n : Nat) :
    Subgroup (tateMultGroup K) where
  mem := fun u =>
    (tateQPowersSubgroup (tateMultGroup K) q).mem (tateNpow (tateMultGroup K) u n)
  one_mem := by
    show (tateQPowersSubgroup (tateMultGroup K) q).mem
      (tateNpow (tateMultGroup K) (tateMultGroup K).one n)
    rw [tateTorOnePow (tateMultGroup K) n]
    exact (tateQPowersSubgroup (tateMultGroup K) q).one_mem
  mul_mem := fun {a b} ha hb => by
    show (tateQPowersSubgroup (tateMultGroup K) q).mem
      (tateNpow (tateMultGroup K) ((tateMultGroup K).mul a b) n)
    rw [tateTorMulPow (tateMultGroup K) (tateMultGroup_comm K) a b n]
    exact (tateQPowersSubgroup (tateMultGroup K) q).mul_mem ha hb
  inv_mem := fun {a} ha => by
    show (tateQPowersSubgroup (tateMultGroup K) q).mem
      (tateNpow (tateMultGroup K) ((tateMultGroup K).inv a) n)
    rw [tateTorInvPow (tateMultGroup K) (tateMultGroup_comm K) a n]
    exact (tateQPowersSubgroup (tateMultGroup K) q).inv_mem ha

/-- **E_q[n] は部分群（単位）**: 1 ∈ E_q[n]。 -/
theorem tateTor_one_mem (K : IUTField) (q : (tateMultGroup K).carrier) (n : Nat) :
    (tateTorSubgroup K q n).mem (tateMultGroup K).one :=
  (tateTorSubgroup K q n).one_mem

/-- **E_q[n] は部分群（積閉）**: u,v ∈ E_q[n] ⟹ uv ∈ E_q[n]。 -/
theorem tateTor_mul_mem (K : IUTField) (q : (tateMultGroup K).carrier) (n : Nat)
    {a b : (tateMultGroup K).carrier}
    (ha : (tateTorSubgroup K q n).mem a) (hb : (tateTorSubgroup K q n).mem b) :
    (tateTorSubgroup K q n).mem ((tateMultGroup K).mul a b) :=
  (tateTorSubgroup K q n).mul_mem ha hb

/-- **E_q[n] は部分群（逆元閉）**: u ∈ E_q[n] ⟹ u⁻¹ ∈ E_q[n]。 -/
theorem tateTor_inv_mem (K : IUTField) (q : (tateMultGroup K).carrier) (n : Nat)
    {a : (tateMultGroup K).carrier} (ha : (tateTorSubgroup K q n).mem a) :
    (tateTorSubgroup K q n).mem ((tateMultGroup K).inv a) :=
  (tateTorSubgroup K q n).inv_mem ha

/-! ## M314F-3: μ_n = { ζ | ζⁿ = 1 } と μ_n ⊆ E_q[n] -/

/-- **μ_n = 1 の n 乗根の群** — K^× の中で ζⁿ = 1 を満たす ζ 全体。本物の部分群
    （1ⁿ=1、(ζξ)ⁿ=ζⁿξⁿ=1、(ζ⁻¹)ⁿ=(ζⁿ)⁻¹=1）。 -/
def tateTorMuSubgroup (K : IUTField) (n : Nat) : Subgroup (tateMultGroup K) where
  mem := fun z => tateNpow (tateMultGroup K) z n = (tateMultGroup K).one
  one_mem := tateTorOnePow (tateMultGroup K) n
  mul_mem := fun {a b} ha hb => by
    show tateNpow (tateMultGroup K) ((tateMultGroup K).mul a b) n
        = (tateMultGroup K).one
    rw [tateTorMulPow (tateMultGroup K) (tateMultGroup_comm K) a b n, ha, hb,
      (tateMultGroup K).one_mul]
  inv_mem := fun {a} ha => by
    show tateNpow (tateMultGroup K) ((tateMultGroup K).inv a) n
        = (tateMultGroup K).one
    rw [tateTorInvPow (tateMultGroup K) (tateMultGroup_comm K) a n, ha,
      tateTorInvOne (tateMultGroup K)]

/-- **μ_n ⊆ E_q[n]** — 1 の n 乗根 ζ（ζⁿ=1）は n-捻れ（ζⁿ=1=q⁰∈q^ℤ）。 -/
theorem tateTor_mu_sub (K : IUTField) (q : (tateMultGroup K).carrier) (n : Nat)
    (z : (tateMultGroup K).carrier) (hz : (tateTorMuSubgroup K n).mem z) :
    (tateTorSubgroup K q n).mem z := by
  have hz' : tateNpow (tateMultGroup K) z n = (tateMultGroup K).one := hz
  show (tateQPowersSubgroup (tateMultGroup K) q).mem (tateNpow (tateMultGroup K) z n)
  rw [hz']
  exact (tateQPowersSubgroup (tateMultGroup K) q).one_mem

/-! ## M314F-4: q^{1/n}（wⁿ=q）の類は n-捻れ（witness 形） -/

/-- **q の n 乗根 w（wⁿ=q）の類 [w] は n-捻れ** — [w]ⁿ=[q]=[1]、すなわち wⁿ=q∈q^ℤ。
    n 乗して q になる元 w を witness で受け取る（分離閉包での根の存在は柱A 後続）。 -/
theorem tateTorQrootMem (K : IUTField) (q w : (tateMultGroup K).carrier) (n : Nat)
    (hw : tateNpow (tateMultGroup K) w n = q) :
    (tateTorSubgroup K q n).mem w := by
  show (tateQPowersSubgroup (tateMultGroup K) q).mem (tateNpow (tateMultGroup K) w n)
  rw [hw]
  exact tate_gen_mem (tateMultGroup K) q

/-! ## M314F-5: 付値による位数 n の本物の証明 -/

/-- **v(x⁻¹) = -v(x)**（付値の乗法性から: v(x)+v(x⁻¹)=v(1)=0）。 -/
theorem tateTorInvVal (K : IUTField) (val : valRingValuation K) (x : K.carrier)
    (hx : x ≠ K.zero) {m : Int} (h : val.v x = some m) :
    val.v (K.inv x) = some (-m) := by
  have hv1 : val.v (K.mul x (K.inv x)) = valOptAdd (val.v x) (val.v (K.inv x)) :=
    val.v_mul x (K.inv x)
  rw [K.mul_inv_cancel x hx, val.v_one, h] at hv1
  cases hvi : val.v (K.inv x) with
  | none =>
    rw [hvi, valOptAdd_some_none] at hv1
    nomatch hv1
  | some c =>
    rw [hvi, valOptAdd_some_some] at hv1
    have hcc : (0 : Int) = m + c := Option.some.inj hv1
    have hc : c = -m := by omega
    rw [hc]

/-- 補助 Int 恒等式: (-m)·(n+1) = m·(negSucc n)（= m·(-(n+1))）。 -/
theorem tateTorNegMul (m : Int) (n : Nat) :
    (-m) * Int.ofNat (n + 1) = m * Int.negSucc n := by
  have h : Int.negSucc n = -(Int.ofNat (n + 1)) := rfl
  rw [h, Int.mul_neg, Int.neg_mul]

/-- **整数冪の付値 v(q^j) = v(q)·j（全整数 j）** — 自然数冪は M309F `tate_qpow_val`、
    負冪は逆元の付値 `tateTorInvVal` から。q^ℤ 上で位数を測る本物の道具。 -/
theorem tateTorZpowVal (K : IUTField) (val : valRingValuation K)
    (qv : K.carrier) (hq0 : qv ≠ K.zero) {m : Int} (h : val.v qv = some m) :
    ∀ j : Int,
      val.v ((tateZpow (tateMultGroup K) ⟨qv, hq0⟩ j).val) = some (m * j) := by
  intro j
  cases j with
  | ofNat n =>
    exact tate_qpow_val K val qv hq0 h n
  | negSucc n =>
    have hinv : val.v (K.inv qv) = some (-m) := tateTorInvVal K val qv hq0 h
    have e := tate_qpow_val K val (K.inv qv) (K.inv_ne_zero hq0) hinv (n + 1)
    rw [← tateTorNegMul m n]
    exact e

/-- **q^{1/n} 方向の位数はちょうど n（本物）** — wⁿ=q（q の n 乗根）で v(w)=d≠0 のとき、
    **wᵏ ∈ q^ℤ ⟹ n ∣ k**。証明: v(wᵏ)=d·k、v(q)=d·n ゆえ wᵏ=q^j なら d·k=d·n·j、
    d≠0 で消去して k=n·j。これが [w]∈E_q[n] の位数がちょうど n（真の n-捻れ）である
    ことの本物の核。*正 valuation v(w)>0 の具体構成は柱B ℤ_p 接続後続*。 -/
theorem tateTorQrootOrder (K : IUTField) (val : valRingValuation K)
    (qv wv : K.carrier) (hq0 : qv ≠ K.zero) (hw0 : wv ≠ K.zero) (n : Nat)
    {d : Int} (hd : d ≠ 0) (hvw : val.v wv = some d)
    (hwn : tateNpow (tateMultGroup K) ⟨wv, hw0⟩ n = ⟨qv, hq0⟩)
    (k : Nat)
    (hmem : (tateQPowersSubgroup (tateMultGroup K) ⟨qv, hq0⟩).mem
             (tateNpow (tateMultGroup K) ⟨wv, hw0⟩ k)) :
    Int.ofNat n ∣ Int.ofNat k := by
  obtain ⟨j, hj⟩ := hmem
  have hvq : val.v qv = some (d * Int.ofNat n) := by
    have e := tate_qpow_val K val wv hw0 hvw n
    have hval : (tateNpow (tateMultGroup K) ⟨wv, hw0⟩ n).val = qv :=
      congrArg Subtype.val hwn
    rw [hval] at e
    exact e
  have hL : val.v ((tateZpow (tateMultGroup K) ⟨qv, hq0⟩ j).val)
      = some (d * Int.ofNat n * j) :=
    tateTorZpowVal K val qv hq0 hvq j
  have hR : val.v ((tateNpow (tateMultGroup K) ⟨wv, hw0⟩ k).val)
      = some (d * Int.ofNat k) :=
    tate_qpow_val K val wv hw0 hvw k
  have hvaleq : (tateZpow (tateMultGroup K) ⟨qv, hq0⟩ j).val
      = (tateNpow (tateMultGroup K) ⟨wv, hw0⟩ k).val :=
    congrArg Subtype.val hj
  rw [hvaleq, hR] at hL
  have heq : d * Int.ofNat k = d * Int.ofNat n * j := Option.some.inj hL
  have heq2 : d * Int.ofNat k = d * (Int.ofNat n * j) := by
    rw [heq, Int.mul_assoc]
  have hk : Int.ofNat k = Int.ofNat n * j := Int.eq_of_mul_eq_mul_left hd heq2
  exact ⟨j, hk⟩

/-! ## M314F-6: capstone -/

/-- **Tate 曲線 n-捻れの総括データ** — Tate パラメータ q・次数 n・n-捻れ部分群 E_q[n]・
    μ_n・そして μ_n ⊆ E_q[n] を束ねる。 -/
structure TateTorsionData (K : IUTField) where
  /-- Tate パラメータ q ∈ K^×。 -/
  q : (tateMultGroup K).carrier
  /-- 捻れの次数 n（IUT では素数 l）。 -/
  n : Nat
  /-- n-捻れ部分群 E_q[n]。 -/
  torsion : Subgroup (tateMultGroup K)
  /-- μ_n（1 の n 乗根）。 -/
  mu : Subgroup (tateMultGroup K)
  /-- torsion = E_q[n]（本物の部分群）。 -/
  isTorsion : torsion = tateTorSubgroup K q n
  /-- mu = μ_n（本物の部分群）。 -/
  isMu : mu = tateTorMuSubgroup K n
  /-- μ_n ⊆ E_q[n]。 -/
  muSub : ∀ z, mu.mem z → torsion.mem z

/-- **witness** — 任意の体 K・任意の q・n に対し n-捻れデータが存在する
    （E_q[n]・μ_n を本物の部分群として与え、μ_n ⊆ E_q[n] を本物で示す）。 -/
def tateTorData (K : IUTField) (q : (tateMultGroup K).carrier) (n : Nat) :
    TateTorsionData K where
  q := q
  n := n
  torsion := tateTorSubgroup K q n
  mu := tateTorMuSubgroup K n
  isTorsion := rfl
  isMu := rfl
  muSub := fun z hz => tateTor_mu_sub K q n z hz

/-- **n-捻れデータの存在**（任意の体 K）。 -/
theorem tateTor_exists (K : IUTField) (q : (tateMultGroup K).carrier) (n : Nat) :
    Nonempty (TateTorsionData K) :=
  ⟨tateTorData K q n⟩

/-- **μ_n ⊆ E_q[n]（capstone）** — 1 の n 乗根はすべて n-捻れ点。 -/
theorem tateTor_mu_in_torsion (K : IUTField) (q : (tateMultGroup K).carrier) (n : Nat) :
    ∀ z, (tateTorMuSubgroup K n).mem z → (tateTorSubgroup K q n).mem z :=
  fun z hz => tateTor_mu_sub K q n z hz

/-- **実例（IUT の l-捻れ）** — n = l（素数）で E_q[l] を取り、μ_l ⊆ E_q[l]。
    Mochizuki の IUT がエタールテータ Θ を評価する l-捻れ点 μ_l が E_q[l] に含まれる。 -/
theorem tateTor_prime_example (K : IUTField) (q : (tateMultGroup K).carrier) (l : Nat) :
    ∀ z, (tateTorMuSubgroup K l).mem z → (tateTorSubgroup K q l).mem z :=
  fun z hz => tateTor_mu_sub K q l z hz

/-- **実例 ℚ 上の Tate 曲線 n-捻れの存在**。 -/
theorem tateTor_exists_rat : Nonempty (TateTorsionData ratIUTField) :=
  ⟨tateTorData ratIUTField (tateMultGroup ratIUTField).one 5⟩

end IUT
