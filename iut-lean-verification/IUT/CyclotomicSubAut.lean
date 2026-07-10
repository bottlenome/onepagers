/-
  IUT/CyclotomicSubAut.lean — CSA（A3 一般 n 塔 M2: 一般代入自己同型 σ_a）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・
     実円分体の各段 ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ})（`cteField n hn` = gefNF 担体・
     deg = 2·3^{n−1}）の上で、生成元 ζ_n = x̄ を ζ_n^a に送る**冪代入自己同型
     σ_a: ζ_n ↦ ζ_n^a（a coprime to 3）を n 一般で本物に構成**する。評価準同型
     `evalSum` で σ_a を定義し、加法・乗法（★根での Φ_{3ⁿ} 簡約消去）・単位・
     両側逆（`cae_endo_ext` の ζ 一点比較・ζ^{a·a'}=ζ）を本物に証明して
     本物の体自己同型 `csaAut` へ昇格し、ℚ 各点固定 `csaAut_mem`・
     σ_a(ζ_n)=ζ_n^a `csaAut_zeta` を確立する。CG9（degree 6・数値 9 固定）の
     σ_a 構成を **最初から n 引数で** 一般化・昇格したもの。honest 仮説 0 本・
     sorry 皆無・新規 Classical.choice 皆無。

  **complete_pct 影響**: A3 一般 n 塔（M2）——一般段の Galois 自己同型
  σ_a: ζ_n ↦ ζ_n^a を n 一般で本物に構成する。res_n（ctr）・res 全射性一般・
  M4 指標同型の**三者が共有する中核部品**。本ファイル単体では complete_pct
  未設定（M2 完成＝ctr 到達で反映）。

  段分解（設計 audit/A3-inverse-limit-roadmap-2026-07-09.md §3.4 の R3-4/5/6）:
   * (R3-4) `csa_phi_at_pow_zero` — Φ_{3ⁿ}(ζ_n^a) = 0（3∤a）。核恒等式
     `cts_pow_sub_one`（X^{3ⁿ}−1 = Φ_{3ⁿ}·(X^{3^{n−1}}−1)）を ζ_n^a で評価し、
     (ζ_n^a)^{3ⁿ}=1（LHS=0）・(ζ_n^a)^{3^{n−1}}≠1（ctm の位数論法＋3∤a）で
     体の整域性（零因子なし）から Φ_{3ⁿ}(ζ_n^a)=0 を得る。
   * (R3-5) `csaSub` — 代入写像 σ_a（評価 `evalSum`・商をくぐらない・全域）。
     `csaSub_add`/`csaSub_one`/**`csaSub_mul`（★山場・根での簡約消去
     `csa_eval_hphi`＋`evalHom_mul`）**・単項式 `csaSub_zeta`（σ_a(ζ_n)=ζ_n^a）。
   * (R3-6) `csaAut` — 自己同型化。両側逆は `cae_endo_ext` の ζ 一点比較
     （ζ_n^{a·a'}=ζ_n・a·a'≡1 mod 3ⁿ）。ℚ 各点固定 `csaAut_mem`。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・ℚ 上・円分塔 ℚ(ζ_{3ⁿ}) のみの忠実な部分ケース。
   (ii)  `csaAut a a'` は **逆元 a'（a·a'≡1 mod 3ⁿ）を明示 witness として受け取る**
         設計（core FieldAut は明示 invFun を要するため）。CG9 の設計 (iii) と
         同じ正直申告。逆元 a' の**構成的抽出（mod 3ⁿ 逆元の choice-free 生成・
         拡張 Euclid / (ℤ/3ⁿ)^× の群性）は本ファイルに含めない**（後続。res_n の
         指標 % 3ⁿ に対する原像抽出は ctr 側で a' を供給する）。
   (iii) 本ファイルは σ_a の構成・環準同型性・自己同型化まで。制限準同型 res_n
         の compat・全射性一般は ctr、(ℤ/3ⁿ)^× との群同型は M4（後続）の射程。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/
  dashboard/graph/tools は不更新・親が統合）。3ⁿ は omega 不可（cte_pow3_pos /
  ctm_pow3_split を明示補助）。
-/
import IUT.CyclotomicMuTower
import IUT.CyclotomicAutExt
import IUT.Field
import IUT.LTErrorDivisible

namespace IUT

/-! ## CSA-0: 定数埋め込み ℚ → K = ℚ(ζ_{3ⁿ}) の RingHom 梱包 -/

/-- **CSA-0: 定数埋め込み RingHom** ι : ℚ → K = ℚ(ζ_{3ⁿ})（`gefIncl` の RingHom
    梱包・= (cteExt n hn).incl）。CG9 の `cg9Iota` の n 一般化。 -/
def cteInclHom (n : Nat) (hn : 1 ≤ n) : RingHom ratRing (cteField n hn).toCRing where
  map := gefIncl (ctsPhi n) (2 * 3 ^ (n - 1)) (cte_nf_pos n hn)
  map_add := fun x y => Subtype.ext ((psConstHom ratRing).map_add x y)
  map_mul := fun x y => by
    apply Subtype.ext
    show psC ratRing (ratRing.mul x y)
        = pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1))
            (psMul ratRing (psC ratRing x) (psC ratRing y))
    have hmm : psMul ratRing (psC ratRing x) (psC ratRing y)
        = psC ratRing (ratRing.mul x y) := ((psConstHom ratRing).map_mul x y).symm
    rw [hmm]
    have hbc : IsPolyBounded ratRing (psC ratRing (ratRing.mul x y)) (2 * 3 ^ (n - 1)) := by
      intro j hj
      show (if j = 0 then ratRing.mul x y else ratRing.zero) = ratRing.zero
      exact if_neg (by have hp := cte_pow3_pos (n - 1); omega)
    funext j
    exact (pfdRed_of_bounded (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
      (2 * 3 ^ (n - 1)) (psC ratRing (ratRing.mul x y)) hbc j).symm
  map_one := Subtype.ext (psConstHom ratRing).map_one

/-! ## CSA-1: 生成元の同定・冪の周期性（ctm 資産の橋渡し） -/

/-- **CSA-1a: 生成元の同定** — caeGen（= gefAlpha・cae の生成元）と ζ_n（= ctmZeta・
    ctm の生成元）は一致する（両者とも NF 担体の X̄ = 単項式 X の像・deg 1 < nf で
    簡約恒等）。cae の決定補題（caeGen で述べる）と ctm の位数論（ζ_n で述べる）を
    繋ぐ橋。 -/
theorem csa_gen_eq (n : Nat) (hn : 1 ≤ n) : caeGen n hn = ctmZeta n hn := by
  apply Subtype.ext
  funext j
  show pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) 1 (psSingle ratRing ratRing.one 1) j
    = psSingle ratRing ratRing.one 1 j
  exact pfdRed_of_bounded (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
    1 (psSingle ratRing ratRing.one 1)
    (fun m hm => if_neg (by have hp := cte_pow3_pos (n - 1); omega)) j

/-- **CSA-1b: ζ_n^1 = ζ_n**（one_mul）。 -/
theorem ctm_pow_one (n : Nat) (hn : 1 ≤ n) : ctmPow n hn 1 = ctmZeta n hn :=
  (ctmR n hn).one_mul (ctmZeta n hn)

/-- **CSA-1c: 冪の周期性** — ζ_n^k は k mod 3ⁿ にのみ依存（ζ_n^{3ⁿ}=1 の
    telescoping）。CG9 `cg9_pow_mod` の n 一般化。 -/
theorem ctm_pow_mod (n : Nat) (hn : 1 ≤ n) (k : Nat) :
    ctmPow n hn k = ctmPow n hn (k % 3 ^ n) := by
  have hdm : (k / 3 ^ n) * 3 ^ n + k % 3 ^ n = k := by
    have h := Nat.div_add_mod k (3 ^ n)
    rw [Nat.mul_comm (3 ^ n) (k / 3 ^ n)] at h
    exact h
  have key : ctmPow n hn ((k / 3 ^ n) * 3 ^ n + k % 3 ^ n) = ctmPow n hn (k % 3 ^ n) := by
    rw [ctmPow_add n hn ((k / 3 ^ n) * 3 ^ n) (k % 3 ^ n), ctmr_pow_mul n hn (k / 3 ^ n)]
    exact (ctmK n hn).ring.one_mul (ctmPow n hn (k % 3 ^ n))
  rw [hdm] at key
  exact key

/-! ## CSA-2: 代入写像 σ_a（評価準同型で定義・全域） -/

/-- **CSA-2: 代入写像** σ_a : y ↦ ev_{ζ_n^a}(y)（評価 `evalSum`・商をくぐらない・
    全域）。CG9 `cg9Subst` の n 一般化。 -/
def csaSub (n : Nat) (hn : 1 ≤ n) (a : Nat) (y : (cteField n hn).carrier) :
    (cteField n hn).carrier :=
  evalSum (cteInclHom n hn) (ctmPow n hn a) y.val (2 * 3 ^ (n - 1))

/-- **加法** σ_a(y+z) = σ_a(y)+σ_a(z)。 -/
theorem csaSub_add (n : Nat) (hn : 1 ≤ n) (a : Nat) (y z : (cteField n hn).carrier) :
    csaSub n hn a ((cteField n hn).toCRing.add y z)
      = (cteField n hn).toCRing.add (csaSub n hn a y) (csaSub n hn a z) :=
  evalHom_add (cteInclHom n hn) (ctmPow n hn a) y.val z.val (2 * 3 ^ (n - 1))

/-- **単位** σ_a(1) = 1。 -/
theorem csaSub_one (n : Nat) (hn : 1 ≤ n) (a : Nat) :
    csaSub n hn a (cteField n hn).toCRing.one = (cteField n hn).toCRing.one := by
  show evalSum (cteInclHom n hn) (ctmPow n hn a) (psOne ratRing) (2 * 3 ^ (n - 1))
    = (cteField n hn).toCRing.one
  rw [evalHom_stable (cteInclHom n hn) (ctmPow n hn a) (psOne ratRing) 1
    (fun j hj => if_neg (by omega)) (2 * 3 ^ (n - 1)) (by have hp := cte_pow3_pos (n - 1); omega)]
  exact evalHom_one (cteInclHom n hn) (ctmPow n hn a)

/-! ## CSA-3: Φ_{3ⁿ}(ζ_n^a) = 0（3∤a・R3-4） -/

/-- **CSA-3a: X^m − 1 は m+1 有界**。 -/
theorem csa_xm1_bound (m : Nat) : IsPolyBounded ratRing (ctsXm1 m) (m + 1) := by
  intro j hj
  show ratRing.add (psSingle ratRing ratRing.one m j)
      (psC ratRing (ratRing.neg ratRing.one) j) = ratRing.zero
  rw [show psSingle ratRing ratRing.one m j = ratRing.zero from if_neg (by omega),
    show psC ratRing (ratRing.neg ratRing.one) j = ratRing.zero from if_neg (by omega),
    ratRing.zero_add]

/-- **CSA-3b: X^m − 1 の評価** — ev_{ζ_n^a}(X^m − 1) = (ζ_n^a)^m − 1
    （= rpow α m + (−1)、`evalHom_add`＋一点集中和）。 -/
theorem csa_eval_xm1 (n : Nat) (hn : 1 ≤ n) (a m : Nat) :
    evalSum (cteInclHom n hn) (ctmPow n hn a) (ctsXm1 m) (m + 1)
      = (cteField n hn).toCRing.add (rpow (cteField n hn).toCRing (ctmPow n hn a) m)
          ((cteField n hn).toCRing.neg (cteField n hn).toCRing.one) := by
  have hp1 : evalSum (cteInclHom n hn) (ctmPow n hn a) (psSingle ratRing ratRing.one m) (m + 1)
      = rpow (cteField n hn).toCRing (ctmPow n hn a) m := by
    show rsum (cteField n hn).toCRing
        (fun i => (cteField n hn).toCRing.mul ((cteInclHom n hn).map (psSingle ratRing ratRing.one m i))
          (rpow (cteField n hn).toCRing (ctmPow n hn a) i)) (m + 1)
      = rpow (cteField n hn).toCRing (ctmPow n hn a) m
    rw [rsum_single (cteField n hn).toCRing _ m (m + 1) (by omega) (fun j hj hjne => by
      show (cteField n hn).toCRing.mul ((cteInclHom n hn).map (psSingle ratRing ratRing.one m j))
          (rpow (cteField n hn).toCRing (ctmPow n hn a) j) = (cteField n hn).toCRing.zero
      rw [show psSingle ratRing ratRing.one m j = ratRing.zero from if_neg hjne,
        RingHom.map_zero (cteInclHom n hn), CRing.zero_mul (cteField n hn).toCRing])]
    show (cteField n hn).toCRing.mul ((cteInclHom n hn).map (psSingle ratRing ratRing.one m m))
        (rpow (cteField n hn).toCRing (ctmPow n hn a) m)
      = rpow (cteField n hn).toCRing (ctmPow n hn a) m
    rw [show psSingle ratRing ratRing.one m m = ratRing.one from if_pos rfl,
      (cteInclHom n hn).map_one, (cteField n hn).toCRing.one_mul]
  have hp2 : evalSum (cteInclHom n hn) (ctmPow n hn a)
        (psC ratRing (ratRing.neg ratRing.one)) (m + 1)
      = (cteField n hn).toCRing.neg (cteField n hn).toCRing.one := by
    show rsum (cteField n hn).toCRing
        (fun i => (cteField n hn).toCRing.mul
          ((cteInclHom n hn).map (psC ratRing (ratRing.neg ratRing.one) i))
          (rpow (cteField n hn).toCRing (ctmPow n hn a) i)) (m + 1)
      = (cteField n hn).toCRing.neg (cteField n hn).toCRing.one
    rw [rsum_single (cteField n hn).toCRing _ 0 (m + 1) (by omega) (fun j hj hjne => by
      show (cteField n hn).toCRing.mul
          ((cteInclHom n hn).map (psC ratRing (ratRing.neg ratRing.one) j))
          (rpow (cteField n hn).toCRing (ctmPow n hn a) j) = (cteField n hn).toCRing.zero
      rw [show psC ratRing (ratRing.neg ratRing.one) j = ratRing.zero from if_neg hjne,
        RingHom.map_zero (cteInclHom n hn), CRing.zero_mul (cteField n hn).toCRing])]
    show (cteField n hn).toCRing.mul
        ((cteInclHom n hn).map (psC ratRing (ratRing.neg ratRing.one) 0))
        (rpow (cteField n hn).toCRing (ctmPow n hn a) 0)
      = (cteField n hn).toCRing.neg (cteField n hn).toCRing.one
    rw [show psC ratRing (ratRing.neg ratRing.one) 0 = ratRing.neg ratRing.one from if_pos rfl,
      show rpow (cteField n hn).toCRing (ctmPow n hn a) 0 = (cteField n hn).toCRing.one from rfl,
      CRing.mul_one (cteField n hn).toCRing, RingHom.map_neg (cteInclHom n hn) ratRing.one,
      (cteInclHom n hn).map_one]
  show evalSum (cteInclHom n hn) (ctmPow n hn a)
      (psAdd ratRing (psSingle ratRing ratRing.one m)
        (psC ratRing (ratRing.neg ratRing.one))) (m + 1)
    = (cteField n hn).toCRing.add (rpow (cteField n hn).toCRing (ctmPow n hn a) m)
        ((cteField n hn).toCRing.neg (cteField n hn).toCRing.one)
  rw [evalHom_add (cteInclHom n hn) (ctmPow n hn a) (psSingle ratRing ratRing.one m)
      (psC ratRing (ratRing.neg ratRing.one)) (m + 1), hp1, hp2]

/-- **CSA-3c: (ζ_n^a)^{3^{n−1}} ≠ 1（3∤a）** — ζ_n^{a·3^{n−1}} は指数 mod 3ⁿ が
    (a%3)·3^{n−1} ∈ {3^{n−1}, 2·3^{n−1}}（0 < · < 3ⁿ）に落ち、位数ちょうど 3ⁿ
    （`ctm_order`）に反する。 -/
theorem csa_pow_sub_ne (n : Nat) (hn : 1 ≤ n) (a : Nat) (ha : ¬ 3 ∣ a) :
    ctmPow n hn (a * 3 ^ (n - 1)) ≠ (cteField n hn).toCRing.one := by
  have hp := cte_pow3_pos (n - 1)
  have h3' : 3 ^ n = 3 * 3 ^ (n - 1) := by rw [ctm_pow3_split n hn, Nat.mul_comm]
  have hexp : a * 3 ^ (n - 1) = (a / 3) * 3 ^ n + (a % 3) * 3 ^ (n - 1) := by
    have key : a * 3 ^ (n - 1)
        = (a / 3) * (3 * 3 ^ (n - 1)) + (a % 3) * 3 ^ (n - 1) := by
      rw [← Nat.mul_assoc, ← Nat.add_mul, show (a / 3) * 3 + a % 3 = a from by omega]
    rw [key, ← h3']
  have hpow_eq : ctmPow n hn (a * 3 ^ (n - 1)) = ctmPow n hn ((a % 3) * 3 ^ (n - 1)) := by
    rw [hexp, ctmPow_add n hn ((a / 3) * 3 ^ n) ((a % 3) * 3 ^ (n - 1)),
      ctmr_pow_mul n hn (a / 3)]
    exact (ctmK n hn).ring.one_mul (ctmPow n hn ((a % 3) * 3 ^ (n - 1)))
  have hr : a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hlt : (a % 3) * 3 ^ (n - 1) < 3 ^ n := by
    cases hr with
    | inl h1 => rw [h1]; omega
    | inr h2 => rw [h2]; omega
  have hne0 : 0 < (a % 3) * 3 ^ (n - 1) := by
    cases hr with
    | inl h1 => rw [h1]; omega
    | inr h2 => rw [h2]; omega
  rw [hpow_eq]
  exact (ctm_order n hn).2 ((a % 3) * 3 ^ (n - 1)) hne0 hlt

/-- **CSA-3（R3-4）: Φ_{3ⁿ}(ζ_n^a) = 0（3∤a）** — 核恒等式 `cts_pow_sub_one`
    X^{3ⁿ}−1 = Φ_{3ⁿ}·(X^{3^{n−1}}−1) を ζ_n^a で評価する（`evalHom_mul`）。
    左辺 = (ζ_n^a)^{3ⁿ}−1 = 0（`ctmr_rpow_pow`）、右辺の第2因子
    (ζ_n^a)^{3^{n−1}}−1 ≠ 0（`csa_pow_sub_ne`）ゆえ体の整域性
    （`eq_zero_of_mul_eq_zero_right`）で第1因子 Φ_{3ⁿ}(ζ_n^a) = 0。 -/
theorem csa_phi_at_pow_zero (n : Nat) (hn : 1 ≤ n) (a : Nat) (ha : ¬ 3 ∣ a) :
    evalSum (cteInclHom n hn) (ctmPow n hn a) (ctsPhi n) (2 * 3 ^ (n - 1) + 1)
      = (cteField n hn).toCRing.zero := by
  have hp := cte_pow3_pos (n - 1)
  have h3 : (3 : Nat) ^ n = 3 ^ (n - 1) * 3 := ctm_pow3_split n hn
  -- rpow の橋（ctm 側から (cteField).toCRing 側へ・defeq）
  have hrp : rpow (cteField n hn).toCRing (ctmPow n hn a) (3 ^ (n - 1))
      = ctmPow n hn (a * 3 ^ (n - 1)) := ctmr_rpow_ctmPow n hn a (3 ^ (n - 1))
  have hrp3n : rpow (cteField n hn).toCRing (ctmPow n hn a) (3 ^ n)
      = (cteField n hn).toCRing.one := ctmr_rpow_pow n hn a
  -- 第2因子 Q = (ζ_n^a)^{3^{n-1}} − 1
  have hQval : evalSum (cteInclHom n hn) (ctmPow n hn a) (ctsXm1 (3 ^ (n - 1))) (3 ^ (n - 1) + 1)
      = (cteField n hn).toCRing.add (ctmPow n hn (a * 3 ^ (n - 1)))
          ((cteField n hn).toCRing.neg (cteField n hn).toCRing.one) := by
    rw [csa_eval_xm1 n hn a (3 ^ (n - 1)), hrp]
  have hQ : evalSum (cteInclHom n hn) (ctmPow n hn a) (ctsXm1 (3 ^ (n - 1))) (3 ^ (n - 1) + 1)
      ≠ (cteField n hn).toCRing.zero := by
    rw [hQval]
    intro h0
    exact csa_pow_sub_ne n hn a ha (CRing.eq_of_sub_eq_zero (cteField n hn).toCRing h0)
  -- 積の評価（evalHom_mul）
  have hprod : evalSum (cteInclHom n hn) (ctmPow n hn a)
        (psMul ratRing (ctsPhi n) (ctsXm1 (3 ^ (n - 1))))
        ((2 * 3 ^ (n - 1) + 1) + (3 ^ (n - 1) + 1) + 1)
      = (cteField n hn).toCRing.mul
          (evalSum (cteInclHom n hn) (ctmPow n hn a) (ctsPhi n) (2 * 3 ^ (n - 1) + 1))
          (evalSum (cteInclHom n hn) (ctmPow n hn a) (ctsXm1 (3 ^ (n - 1))) (3 ^ (n - 1) + 1)) :=
    evalHom_mul (cteInclHom n hn) (ctmPow n hn a) (ctsPhi n) (ctsXm1 (3 ^ (n - 1)))
      (2 * 3 ^ (n - 1) + 1) (3 ^ (n - 1) + 1) (ctsPhi_bound n hn) (csa_xm1_bound (3 ^ (n - 1)))
  -- 積 = X^{3ⁿ} − 1（核恒等式）
  rw [(cts_pow_sub_one n hn).symm] at hprod
  -- 左辺 = 0
  have hLHS0 : evalSum (cteInclHom n hn) (ctmPow n hn a) (ctsXm1 (3 ^ n))
        ((2 * 3 ^ (n - 1) + 1) + (3 ^ (n - 1) + 1) + 1) = (cteField n hn).toCRing.zero := by
    rw [evalHom_stable (cteInclHom n hn) (ctmPow n hn a) (ctsXm1 (3 ^ n)) (3 ^ n + 1)
        (csa_xm1_bound (3 ^ n)) ((2 * 3 ^ (n - 1) + 1) + (3 ^ (n - 1) + 1) + 1) (by omega),
      csa_eval_xm1 n hn a (3 ^ n), hrp3n]
    exact CRing.add_neg (cteField n hn).toCRing (cteField n hn).toCRing.one
  -- mul P Q = 0 ⟹ P = 0
  have hmulPQ : (cteField n hn).toCRing.mul
      (evalSum (cteInclHom n hn) (ctmPow n hn a) (ctsPhi n) (2 * 3 ^ (n - 1) + 1))
      (evalSum (cteInclHom n hn) (ctmPow n hn a) (ctsXm1 (3 ^ (n - 1))) (3 ^ (n - 1) + 1))
      = (cteField n hn).toCRing.zero := by rw [← hprod]; exact hLHS0
  exact (cteField n hn).eq_zero_of_mul_eq_zero_right hmulPQ hQ

/-! ## CSA-4: 根での簡約消去 と 乗法性（R3-5・★山場） -/

/-- **CSA-4a: h·Φ_{3ⁿ} の評価は根で消える（3∤a）** — CG9 `cg9_eval_hphi` の
    n 一般化。`evalHom_mul` で ev(h)·ev(Φ_{3ⁿ}) に分け、ev(Φ_{3ⁿ}) = 0
    （`csa_phi_at_pow_zero`）で潰す。 -/
theorem csa_eval_hphi (n : Nat) (hn : 1 ≤ n) (a : Nat) (ha : ¬ 3 ∣ a)
    (h : PS ratRing) (Nh : Nat) (hhb : IsPolyBounded ratRing h Nh)
    (M : Nat) (hM : Nh + (2 * 3 ^ (n - 1) + 1) + 1 ≤ M) :
    evalSum (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing h (ctsPhi n)) M
      = (cteField n hn).toCRing.zero := by
  have hb : IsPolyBounded ratRing (psMul ratRing h (ctsPhi n)) (Nh + (2 * 3 ^ (n - 1) + 1)) :=
    simpleExt_mul_bounded ratRing hhb (ctsPhi_bound n hn)
  have e1 : evalSum (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing h (ctsPhi n)) M
      = evalSum (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing h (ctsPhi n))
          (Nh + (2 * 3 ^ (n - 1) + 1)) :=
    evalHom_stable (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing h (ctsPhi n))
      (Nh + (2 * 3 ^ (n - 1) + 1)) hb M (by omega)
  have e2 : evalSum (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing h (ctsPhi n))
        (Nh + (2 * 3 ^ (n - 1) + 1) + 1)
      = evalSum (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing h (ctsPhi n))
          (Nh + (2 * 3 ^ (n - 1) + 1)) :=
    evalHom_stable (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing h (ctsPhi n))
      (Nh + (2 * 3 ^ (n - 1) + 1)) hb (Nh + (2 * 3 ^ (n - 1) + 1) + 1) (by omega)
  have hmul := evalHom_mul (cteInclHom n hn) (ctmPow n hn a) h (ctsPhi n) Nh (2 * 3 ^ (n - 1) + 1)
    hhb (ctsPhi_bound n hn)
  rw [e1, ← e2, hmul, csa_phi_at_pow_zero n hn a ha, CRing.mul_zero (cteField n hn).toCRing]

/-- **CSA-4（R3-5 本丸）: 乗法性** σ_a(y·z) = σ_a(y)·σ_a(z)（3∤a）。ζ_n^a での
    評価が積の Φ_{3ⁿ} 簡約を消す（`csa_eval_hphi`）・`evalHom_mul` で残りを閉じる。
    CG9 `cg9Subst_mul` の n 一般化。 -/
theorem csaSub_mul (n : Nat) (hn : 1 ≤ n) (a : Nat) (ha : ¬ 3 ∣ a)
    (y z : (cteField n hn).carrier) :
    csaSub n hn a ((cteField n hn).toCRing.mul y z)
      = (cteField n hn).toCRing.mul (csaSub n hn a y) (csaSub n hn a z) := by
  have hwb : IsPolyBounded ratRing (psMul ratRing y.val z.val)
      (2 * 3 ^ (n - 1) + 2 * 3 ^ (n - 1)) :=
    simpleExt_mul_bounded ratRing y.property z.property
  obtain ⟨h, ⟨Nh, hhb⟩, he⟩ :=
    gnfCong_red (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
      (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val) hwb
  have heq2 : pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val)
      = psAdd ratRing (psMul ratRing y.val z.val) (psMul ratRing h (ctsPhi n)) := by
    funext j
    have hej : ratRing.add
        (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val) j)
        (ratRing.neg (psMul ratRing y.val z.val j)) = psMul ratRing h (ctsPhi n) j :=
      congrFun he j
    show pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val) j
      = ratRing.add (psMul ratRing y.val z.val j) (psMul ratRing h (ctsPhi n) j)
    have key : ratRing.add (psMul ratRing y.val z.val j) (psMul ratRing h (ctsPhi n) j)
        = pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val) j := by
      rw [← hej, ratRing.add_comm
          (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val) j)
          (ratRing.neg (psMul ratRing y.val z.val j)),
        ← ratRing.add_assoc (psMul ratRing y.val z.val j)
          (ratRing.neg (psMul ratRing y.val z.val j))
          (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val) j),
        ratRing.add_neg (psMul ratRing y.val z.val j), ratRing.zero_add]
    exact key.symm
  have hRHS : (cteField n hn).toCRing.mul (csaSub n hn a y) (csaSub n hn a z)
      = evalSum (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing y.val z.val)
          (2 * 3 ^ (n - 1) + 2 * 3 ^ (n - 1) + 1) :=
    (evalHom_mul (cteInclHom n hn) (ctmPow n hn a) y.val z.val (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1))
      y.property z.property).symm
  have hpf6 : IsPolyBounded ratRing
      (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val))
      (2 * 3 ^ (n - 1)) :=
    pfdRed_bound (ctsPhi n) (2 * 3 ^ (n - 1)) (ctsPhi_bound n hn) (cte_lead_ne n hn)
      (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val) hwb
  show evalSum (cteInclHom n hn) (ctmPow n hn a)
      (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val))
      (2 * 3 ^ (n - 1))
    = (cteField n hn).toCRing.mul (csaSub n hn a y) (csaSub n hn a z)
  rw [hRHS,
    (evalHom_stable (cteInclHom n hn) (ctmPow n hn a)
      (pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1)) (psMul ratRing y.val z.val))
      (2 * 3 ^ (n - 1)) hpf6 (Nh + 2 * 3 ^ (n - 1) + 2 * 3 ^ (n - 1) + 10)
      (by have hp := cte_pow3_pos (n - 1); omega)).symm,
    heq2,
    evalHom_add (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing y.val z.val)
      (psMul ratRing h (ctsPhi n)) (Nh + 2 * 3 ^ (n - 1) + 2 * 3 ^ (n - 1) + 10),
    csa_eval_hphi n hn a ha h Nh hhb (Nh + 2 * 3 ^ (n - 1) + 2 * 3 ^ (n - 1) + 10)
      (by have hp := cte_pow3_pos (n - 1); omega),
    CRing.add_zero (cteField n hn).toCRing,
    evalHom_stable (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing y.val z.val)
      (2 * 3 ^ (n - 1) + 2 * 3 ^ (n - 1)) hwb (Nh + 2 * 3 ^ (n - 1) + 2 * 3 ^ (n - 1) + 10)
      (by omega)]
  exact (evalHom_stable (cteInclHom n hn) (ctmPow n hn a) (psMul ratRing y.val z.val)
    (2 * 3 ^ (n - 1) + 2 * 3 ^ (n - 1)) hwb (2 * 3 ^ (n - 1) + 2 * 3 ^ (n - 1) + 1) (by omega)).symm

/-! ## CSA-5: 単項式の評価 σ_a(ζ_n) = ζ_n^a・冪 σ_a(ζ_n^i) = ζ_n^{a·i} -/

/-- **CSA-5a（R3-5）: σ_a(ζ_n) = ζ_n^a**（単項式の評価・一点集中和）。 -/
theorem csaSub_zeta (n : Nat) (hn : 1 ≤ n) (a : Nat) :
    csaSub n hn a (ctmZeta n hn) = ctmPow n hn a := by
  show rsum (cteField n hn).toCRing
      (fun k => (cteField n hn).toCRing.mul
        ((cteInclHom n hn).map (psSingle ratRing ratRing.one 1 k))
        (rpow (cteField n hn).toCRing (ctmPow n hn a) k)) (2 * 3 ^ (n - 1)) = ctmPow n hn a
  rw [rsum_single (cteField n hn).toCRing _ 1 (2 * 3 ^ (n - 1))
    (by have hp := cte_pow3_pos (n - 1); omega) (fun j hj hjne => by
      show (cteField n hn).toCRing.mul ((cteInclHom n hn).map (psSingle ratRing ratRing.one 1 j))
          (rpow (cteField n hn).toCRing (ctmPow n hn a) j) = (cteField n hn).toCRing.zero
      rw [show psSingle ratRing ratRing.one 1 j = ratRing.zero from if_neg hjne,
        RingHom.map_zero (cteInclHom n hn), CRing.zero_mul (cteField n hn).toCRing])]
  show (cteField n hn).toCRing.mul ((cteInclHom n hn).map (psSingle ratRing ratRing.one 1 1))
      (rpow (cteField n hn).toCRing (ctmPow n hn a) 1) = ctmPow n hn a
  rw [show psSingle ratRing ratRing.one 1 1 = ratRing.one from if_pos rfl,
    (cteInclHom n hn).map_one, (cteField n hn).toCRing.one_mul]
  show (cteField n hn).toCRing.mul (cteField n hn).toCRing.one (ctmPow n hn a) = ctmPow n hn a
  exact (cteField n hn).toCRing.one_mul (ctmPow n hn a)

/-- **CSA-5b: σ_a(ζ_n^i) = ζ_n^{a·i}**（3∤a・i 帰納・`csaSub_mul`＋`ctmPow_add`）。
    CG9 `cg9_subst_pow` の n 一般化。 -/
theorem csa_subst_pow (n : Nat) (hn : 1 ≤ n) (a : Nat) (ha : ¬ 3 ∣ a) :
    ∀ i, csaSub n hn a (ctmPow n hn i) = ctmPow n hn (a * i) := by
  intro i
  induction i with
  | zero =>
    show csaSub n hn a (cteField n hn).toCRing.one = ctmPow n hn (a * 0)
    rw [Nat.mul_zero]
    exact csaSub_one n hn a
  | succ i ih =>
    show csaSub n hn a ((cteField n hn).toCRing.mul (ctmPow n hn i) (ctmZeta n hn))
      = ctmPow n hn (a * (i + 1))
    rw [csaSub_mul n hn a ha (ctmPow n hn i) (ctmZeta n hn), ih, csaSub_zeta n hn a,
      Nat.mul_succ a i]
    exact (ctmPow_add n hn (a * i) a).symm

/-! ## CSA-6: ℚ 各点固定 と 両側逆（R3-6） -/

/-- **CSA-6a: σ_a は ℚ を固定** — σ_a(ι(c)) = ι(c)（定数の評価）。 -/
theorem csa_subst_incl (n : Nat) (hn : 1 ≤ n) (a : Nat) (c : QRat) :
    csaSub n hn a (caeIncl n hn c) = caeIncl n hn c := by
  show evalSum (cteInclHom n hn) (ctmPow n hn a) (psC ratRing c) (2 * 3 ^ (n - 1))
    = caeIncl n hn c
  rw [evalHom_stable (cteInclHom n hn) (ctmPow n hn a) (psC ratRing c) 1
    (fun j hj => if_neg (by omega)) (2 * 3 ^ (n - 1)) (by have hp := cte_pow3_pos (n - 1); omega)]
  exact evalHom_C (cteInclHom n hn) (ctmPow n hn a) c

/-- **CSA-6b: 合成 σ_{a'}∘σ_a は環準同型**（両者 3∤・`csaSub_add`/`csaSub_mul`/
    `csaSub_one`）。両側逆の `cae_endo_ext` に渡す φ。 -/
def csaCompHom (n : Nat) (hn : 1 ≤ n) (a a' : Nat) (ha : ¬ 3 ∣ a) (ha' : ¬ 3 ∣ a') :
    RingHom (cteField n hn).toCRing (cteField n hn).toCRing where
  map := fun y => csaSub n hn a' (csaSub n hn a y)
  map_add := fun y z => by
    show csaSub n hn a' (csaSub n hn a ((cteField n hn).toCRing.add y z))
      = (cteField n hn).toCRing.add (csaSub n hn a' (csaSub n hn a y))
          (csaSub n hn a' (csaSub n hn a z))
    rw [csaSub_add n hn a y z, csaSub_add n hn a' (csaSub n hn a y) (csaSub n hn a z)]
  map_mul := fun y z => by
    show csaSub n hn a' (csaSub n hn a ((cteField n hn).toCRing.mul y z))
      = (cteField n hn).toCRing.mul (csaSub n hn a' (csaSub n hn a y))
          (csaSub n hn a' (csaSub n hn a z))
    rw [csaSub_mul n hn a ha y z, csaSub_mul n hn a' ha' (csaSub n hn a y) (csaSub n hn a z)]
  map_one := by
    show csaSub n hn a' (csaSub n hn a (cteField n hn).toCRing.one) = (cteField n hn).toCRing.one
    rw [csaSub_one n hn a, csaSub_one n hn a']

/-- **CSA-6c: 両側逆（R3-6）** — a·a'≡1 (mod 3ⁿ) のとき σ_{a'}(σ_a(y)) = y。
    `cae_endo_ext` で生成元 ζ_n 一点比較（ζ_n^{a'·a} = ζ_n^{(a'·a) mod 3ⁿ} =
    ζ_n^1 = ζ_n）に還元する（CG9 の decompose 経由を cae の決定補題に置換）。 -/
theorem csaSub_left_inv (n : Nat) (hn : 1 ≤ n) (a a' : Nat)
    (ha : ¬ 3 ∣ a) (ha' : ¬ 3 ∣ a') (haa' : a * a' % 3 ^ n = 1)
    (y : (cteField n hn).carrier) :
    csaSub n hn a' (csaSub n hn a y) = y := by
  have hkey : ∀ w, (csaCompHom n hn a a' ha ha').map w = (evalHomId (cteField n hn).toCRing).map w :=
    cae_endo_ext n hn (csaCompHom n hn a a' ha ha') (evalHomId (cteField n hn).toCRing)
      (fun c => by
        show csaSub n hn a' (csaSub n hn a (caeIncl n hn c)) = caeIncl n hn c
        rw [csa_subst_incl n hn a c, csa_subst_incl n hn a' c])
      (fun c => rfl)
      (by
        show csaSub n hn a' (csaSub n hn a (caeGen n hn)) = caeGen n hn
        rw [csa_gen_eq n hn, csaSub_zeta n hn a, csa_subst_pow n hn a' ha' a,
          ctm_pow_mod n hn (a' * a),
          show (a' * a) % 3 ^ n = 1 from by rw [Nat.mul_comm a' a]; exact haa']
        exact ctm_pow_one n hn)
  exact hkey y

/-! ## CSA-7: 自己同型化 σ_a ∈ Gal(ℚ(ζ_{3ⁿ})/ℚ) -/

/-- **CSA-7a（R3-6）: σ_a は体自己同型** — 明示逆元 a'（a·a'≡1 mod 3ⁿ）付き。
    CG9 `cg9Aut` の n 一般化。 -/
def csaAut (n : Nat) (hn : 1 ≤ n) (a a' : Nat)
    (ha : ¬ 3 ∣ a) (ha' : ¬ 3 ∣ a') (haa' : a * a' % 3 ^ n = 1) :
    FieldAut (cteField n hn) where
  toFun := csaSub n hn a
  invFun := csaSub n hn a'
  map_add := csaSub_add n hn a
  map_mul := csaSub_mul n hn a ha
  map_one := csaSub_one n hn a
  left_inv := csaSub_left_inv n hn a a' ha ha' haa'
  right_inv := csaSub_left_inv n hn a' a ha' ha (by rw [Nat.mul_comm]; exact haa')

/-- **CSA-7b: σ_a ∈ Gal(ℚ(ζ_{3ⁿ})/ℚ)**（ℚ 各点固定）。 -/
theorem csaAut_mem (n : Nat) (hn : 1 ≤ n) (a a' : Nat)
    (ha : ¬ 3 ∣ a) (ha' : ¬ 3 ∣ a') (haa' : a * a' % 3 ^ n = 1) :
    (galoisSubgroup (cteExt n hn)).mem (csaAut n hn a a' ha ha' haa') :=
  fun k => csa_subst_incl n hn a k

/-- **CSA-7c: σ_a(ζ_n) = ζ_n^a**（後段 ctr の指標抽出が使う）。 -/
theorem csaAut_zeta (n : Nat) (hn : 1 ≤ n) (a a' : Nat)
    (ha : ¬ 3 ∣ a) (ha' : ¬ 3 ∣ a') (haa' : a * a' % 3 ^ n = 1) :
    (csaAut n hn a a' ha ha' haa').toFun (ctmZeta n hn) = ctmPow n hn a :=
  csaSub_zeta n hn a

end IUT
