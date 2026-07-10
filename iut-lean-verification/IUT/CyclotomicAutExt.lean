/-
  IUT/CyclotomicAutExt.lean — CAE（A3 一般 n 塔 M2: 一般段 ℚ(ζ_{3ⁿ}) の
  分解補題と自己同型決定補題）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・
     実円分体の各段 ℚ(ζ_{3ⁿ}) = ℚ[x]/(Φ_{3ⁿ})（`cteField n hn` = gefNF 担体・
     deg = 2·3^{n−1}）の上で、任意の担体元が生成元 x̄ = α の冪の ℚ-線形結合に
     分解すること（`cae_decompose`）と、ℚ を固定する環自己準同型／体自己同型が
     生成元 x̄ の像だけで一意に決まること（`cae_endo_ext`/`cae_aut_ext`）を、
     **最初から n 引数で** core Lean のみで choice-free に完全証明する。
     CG3（nf=2）・CG9（nf=6）の decompose/aut_ext を nf=2·3^{n−1} 一般へ写経・
     昇格したもの。honest 仮説 0 本・sorry 皆無・新規 Classical.choice 皆無）。

  **complete_pct 影響**: A3 一般 n 塔（M2）——一般段の体自己同型が生成元 x̄ の
  像で決まるという決定補題を n 一般で確立する。後段 csa（代入自己同型 σ_a の
  一意性）・ctr（制限 res_n の well-defined 性）は「σ が x̄ の像で決まる」本補題に
  依存する。本ファイル単体では complete_pct 未設定（M2 完成＝ctr 到達で反映）。
  A3 一般 n 塔の complete_pct は、一般段機構 M2（ι_n の体埋め込み cte・一般 μ の
  同定 ctm・決定補題 cae＝本ファイル・代入自己同型 csa・制限 ctr）が本物で揃った
  段で反映する。

  内容（設計 audit/A3-inverse-limit-roadmap-2026-07-09.md §3.3）:
   * `caeGen n hn`      — 生成元 x̄ = α = [x]（`gefAlpha` の Φ_{3ⁿ} 実例化）。
   * `caePow n hn i`    — x̄^i（環冪 `rpow`・= `gefNFPow` と defeq）。
   * `caeIncl n hn c`   — 定数埋め込み ι(c) = psC c（`gefIncl`・= cteExt.incl）。
   * `cae_decompose`    — y = Σ_{i<2·3^{n−1}} ι(y_i)·x̄^i（有限和 `rsum`・
     `gefAlphaPowVal`（x̄^i=X^i）＋剰余無し積 `pfdRed_of_bounded` で再構成）。
   * `cae_endo_ext`     — ℚ 固定の環準同型 φ,ψ が x̄ で一致 ⟹ 全点一致
     （invFun 不要版・`ringHom_rsum`/`ringHom_rpow` で分解の各項を追う）。
   * `cae_aut_ext`      — ℚ 固定の体自己同型 σ,τ が x̄ で一致 ⟹ σ=τ
     （`cae_endo_ext` + `FieldAut.ext`・invFun は left_inv 経由）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・ℚ 上・円分塔 ℚ(ζ_{3ⁿ}) のみの忠実な部分ケース（一般素数 p は
         本層に含めない）。
   (ii)  本ファイルは**決定補題（σ は x̄ の像で決まる）まで**。生成元 x̄ の像
         σ(x̄) が実際に x̄^a になる代入自己同型 σ_a の**構成は csa**（後段）。
         res 全射性・分離性・正規性の一般論も未形式化。
   (iii) `cae_endo_ext` は環準同型 `RingHom` で述べる（invFun 不要）。全単射性を
         要する `cae_aut_ext` は `FieldAut` で述べ、逆写像は明示 invFun の
         left_inv/right_inv 経由（choice 不使用）。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/
  dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.CyclotomicEmbedTower
import IUT.GenExtBasisAlpha
import IUT.FieldAutGroup
import IUT.PSFunctor

namespace IUT

/-! ## CAE-0: 生成元 x̄ = α・その冪 x̄^i・定数埋め込み ι -/

/-- **CAE-0a: 生成元** x̄ = α = [x]（`gefAlpha` の Φ_{3ⁿ} 実例化）。 -/
def caeGen (n : Nat) (hn : 1 ≤ n) : (cteField n hn).carrier :=
  gefAlpha (ctsPhi n) (2 * 3 ^ (n - 1))
    (ctsPhi_bound n hn) (cte_lead_ne n hn) (cte_nf_pos n hn)

/-- **CAE-0b: 生成元の冪** x̄^i（環冪 `rpow`・`gefNFPow` と defeq）。 -/
def caePow (n : Nat) (hn : 1 ≤ n) (i : Nat) : (cteField n hn).carrier :=
  rpow (cteField n hn).toCRing (caeGen n hn) i

/-- **CAE-0c: 定数埋め込み** ι(c) = psC c（`gefIncl`・cteExt.incl と defeq）。 -/
def caeIncl (n : Nat) (hn : 1 ≤ n) (c : QRat) : (cteField n hn).carrier :=
  gefIncl (ctsPhi n) (2 * 3 ^ (n - 1)) (cte_nf_pos n hn) c

/-! ## CAE-1: x̄^i の正規形係数（= 単項式 X^i） -/

/-- **CAE-1a: caePow = gefNFPow** — 環冪 `rpow` による x̄^i は `gefNFPow`
    （F9 の担体冪）と一致する（i 帰納・両者とも同じ NF 環の乗法の反復）。 -/
theorem caePow_eq (n : Nat) (hn : 1 ≤ n) (i : Nat) :
    caePow n hn i
      = gefNFPow (ctsPhi n) (2 * 3 ^ (n - 1))
          (ctsPhi_bound n hn) (cte_lead_ne n hn) (cte_nf_pos n hn) (caeGen n hn) i := by
  induction i with
  | zero => rfl
  | succ k ih =>
    show (cteField n hn).toCRing.mul (caePow n hn k) (caeGen n hn)
      = gefNFPow (ctsPhi n) (2 * 3 ^ (n - 1))
          (ctsPhi_bound n hn) (cte_lead_ne n hn) (cte_nf_pos n hn) (caeGen n hn) (k + 1)
    rw [ih]
    rfl

/-- **CAE-1: x̄^i = X^i**（i < 2·3^{n−1}・`gefAlphaPowVal` の実例化）。
    caePow は `gefNFPow (gefAlpha)` と一致（`caePow_eq`）ゆえ係数は単項式 X^i。 -/
theorem caePow_val (n : Nat) (hn : 1 ≤ n) (i : Nat) (hi : i < 2 * 3 ^ (n - 1)) :
    (caePow n hn i).val = psSingle ratRing ratRing.one i := by
  rw [caePow_eq n hn i]
  exact gefAlphaPowVal (ctsPhi n) (2 * 3 ^ (n - 1))
    (ctsPhi_bound n hn) (cte_lead_ne n hn) (cte_nf_pos n hn) i hi

/-! ## CAE-2: 基底項 ι(c)·x̄^i の正規形係数（= psSingle c i） -/

/-- **CAE-2: ι(c)·x̄^i の係数 = psSingle c i**（i < 2·3^{n−1}）。定数 psC c
    （次数 0）と単項式 X^i の積は psSingle c i（`gefSmulCoeff`）で、
    deg = i < nf ゆえ剰余簡約が恒等（`pfdRed_of_bounded`）。 -/
theorem caeInclPow_val (n : Nat) (hn : 1 ≤ n) (c : QRat) (i : Nat)
    (hi : i < 2 * 3 ^ (n - 1)) :
    ((cteField n hn).mul (caeIncl n hn c) (caePow n hn i)).val
      = psSingle ratRing c i := by
  show pfdRed (ctsPhi n) (2 * 3 ^ (n - 1)) (2 * 3 ^ (n - 1))
      (psMul ratRing (psC ratRing c) (caePow n hn i).val)
    = psSingle ratRing c i
  rw [caePow_val n hn i hi]
  have hps : psMul ratRing (psC ratRing c) (psSingle ratRing ratRing.one i)
      = psSingle ratRing c i := by
    funext k
    rw [gefSmulCoeff c (psSingle ratRing ratRing.one i) k]
    show ratRing.mul c (psSingle ratRing ratRing.one i k) = psSingle ratRing c i k
    cases Nat.decEq k i with
    | isTrue hk =>
      rw [show psSingle ratRing ratRing.one i k = ratRing.one from if_pos hk,
        show psSingle ratRing c i k = c from if_pos hk, CRing.mul_one ratRing]
    | isFalse hk =>
      rw [show psSingle ratRing ratRing.one i k = ratRing.zero from if_neg hk,
        show psSingle ratRing c i k = ratRing.zero from if_neg hk, CRing.mul_zero ratRing]
  rw [hps]
  funext k
  exact pfdRed_of_bounded (ctsPhi n) (2 * 3 ^ (n - 1))
    (ctsPhi_bound n hn) (cte_lead_ne n hn) (2 * 3 ^ (n - 1)) (psSingle ratRing c i)
    (fun m hm => if_neg (by omega)) k

/-! ## CAE-3: 有限和の係数（各点で pointwise） -/

/-- **CAE-3: 環有限和の係数** — (Σ g i)_j = Σ (g i)_j（`gefNFRing` の add は
    各点 psAdd）。 -/
theorem caeRsumVal (n : Nat) (hn : 1 ≤ n)
    (g : Nat → (cteField n hn).carrier) (j : Nat) :
    ∀ m, (rsum (cteField n hn).toCRing g m).val j
        = rsum ratRing (fun i => (g i).val j) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    show ratRing.add ((rsum (cteField n hn).toCRing g m).val j) ((g m).val j)
      = ratRing.add (rsum ratRing (fun i => (g i).val j) m) ((g m).val j)
    rw [ih]

/-! ## CAE-4: 分解補題 y = Σ_{i<2·3^{n−1}} ι(y_i)·x̄^i -/

/-- **CAE-4: 分解補題** — 任意の担体元 y は生成元 x̄ の冪の ℚ-線形結合
    y = Σ_{i<2·3^{n−1}} ι(y_i)·x̄^i。CG9 の `cg9_decompose` の nf 一般化。
    各基底項の係数は psSingle y_i i（`caeInclPow_val`）で、和の j 次係数は
    j < nf のとき y_j（一点集中 `rsum_single`）、j ≥ nf のとき 0 = y_j
    （担体の有界性 `y.property`）。 -/
theorem cae_decompose (n : Nat) (hn : 1 ≤ n) (y : (cteField n hn).carrier) :
    rsum (cteField n hn).toCRing
      (fun i => (cteField n hn).mul (caeIncl n hn (y.val i)) (caePow n hn i))
      (2 * 3 ^ (n - 1)) = y := by
  apply Subtype.ext
  funext j
  rw [caeRsumVal n hn
      (fun i => (cteField n hn).mul (caeIncl n hn (y.val i)) (caePow n hn i)) j
      (2 * 3 ^ (n - 1)),
    rsum_congr ratRing (2 * 3 ^ (n - 1)) (fun i hi =>
      congrFun (caeInclPow_val n hn (y.val i) i hi) j)]
  cases Nat.lt_or_ge j (2 * 3 ^ (n - 1)) with
  | inl hj =>
    rw [rsum_single ratRing (fun i => psSingle ratRing (y.val i) i j) j
      (2 * 3 ^ (n - 1)) hj
      (fun i hi hij => by
        show psSingle ratRing (y.val i) i j = ratRing.zero
        exact if_neg (fun hh => hij hh.symm))]
    show psSingle ratRing (y.val j) j j = y.val j
    exact if_pos rfl
  | inr hj =>
    rw [rsum_congr ratRing (2 * 3 ^ (n - 1)) (fun i hi => by
        show psSingle ratRing (y.val i) i j = ratRing.zero
        exact if_neg (by omega)),
      rsum_const_zero ratRing (2 * 3 ^ (n - 1))]
    exact (y.property j hj).symm

/-! ## CAE-5: 決定補題（環準同型版・invFun 不要） -/

/-- **CAE-5: 環準同型の決定補題** — ℚ を固定する環自己準同型 φ,ψ が生成元 x̄ で
    一致すれば全点一致。CG9 `cg9_aut_ext` の pointwise 中核を `RingHom` で述べた
    invFun 不要版（後段 csa の左右逆で使う）。分解 `cae_decompose` を φ,ψ で
    像し（`ringHom_rsum`）、各基底項 ι(y_i)·x̄^i の像を map_mul + ℚ 固定 +
    冪保存 `ringHom_rpow` で σ(x̄) の像に還元し、h : φ(x̄)=ψ(x̄) で閉じる。 -/
theorem cae_endo_ext (n : Nat) (hn : 1 ≤ n)
    (φ ψ : RingHom (cteField n hn).toCRing (cteField n hn).toCRing)
    (hφ : ∀ c, φ.map (caeIncl n hn c) = caeIncl n hn c)
    (hψ : ∀ c, ψ.map (caeIncl n hn c) = caeIncl n hn c)
    (h : φ.map (caeGen n hn) = ψ.map (caeGen n hn)) :
    ∀ y, φ.map y = ψ.map y := by
  intro y
  rw [← cae_decompose n hn y,
    ringHom_rsum φ
      (fun i => (cteField n hn).mul (caeIncl n hn (y.val i)) (caePow n hn i))
      (2 * 3 ^ (n - 1)),
    ringHom_rsum ψ
      (fun i => (cteField n hn).mul (caeIncl n hn (y.val i)) (caePow n hn i))
      (2 * 3 ^ (n - 1))]
  apply rsum_congr (cteField n hn).toCRing (2 * 3 ^ (n - 1))
  intro i hi
  show φ.map ((cteField n hn).mul (caeIncl n hn (y.val i)) (caePow n hn i))
    = ψ.map ((cteField n hn).mul (caeIncl n hn (y.val i)) (caePow n hn i))
  rw [φ.map_mul (caeIncl n hn (y.val i)) (caePow n hn i),
      ψ.map_mul (caeIncl n hn (y.val i)) (caePow n hn i),
      hφ (y.val i), hψ (y.val i),
      show caePow n hn i = rpow (cteField n hn).toCRing (caeGen n hn) i from rfl,
      ringHom_rpow φ (caeGen n hn) i, ringHom_rpow ψ (caeGen n hn) i, h]

/-! ## CAE-6: 決定補題（体自己同型版） -/

/-- 体自己同型 σ を環準同型 `RingHom` として梱包（toFun の準同型性のみ使用）。 -/
def caeAutHom (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField n hn)) :
    RingHom (cteField n hn).toCRing (cteField n hn).toCRing where
  map := σ.toFun
  map_add := σ.map_add
  map_mul := σ.map_mul
  map_one := σ.map_one

/-- **CAE-6: 自己同型の決定補題** — ℚ を固定する体自己同型 σ,τ が生成元 x̄ で
    一致すれば σ = τ。CG3/CG9 `cg3_aut_ext`/`cg9_aut_ext` の nf 一般化。
    pointwise 一致は `cae_endo_ext`（σ,τ を `caeAutHom` で環準同型化）で得、
    invFun の一致は σ の right_inv と τ の left_inv 経由（choice 不使用）。 -/
theorem cae_aut_ext (n : Nat) (hn : 1 ≤ n) (σ τ : FieldAut (cteField n hn))
    (hσ : (galoisSubgroup (cteExt n hn)).mem σ)
    (hτ : (galoisSubgroup (cteExt n hn)).mem τ)
    (h : σ.toFun (caeGen n hn) = τ.toFun (caeGen n hn)) : σ = τ := by
  have htofun : ∀ y, σ.toFun y = τ.toFun y :=
    cae_endo_ext n hn (caeAutHom n hn σ) (caeAutHom n hn τ)
      (fun c => hσ c) (fun c => hτ c) h
  apply FieldAut.ext
  · funext y; exact htofun y
  · funext x
    have h1 : σ.toFun (σ.invFun x) = x := σ.right_inv x
    have h2 : τ.toFun (σ.invFun x) = x := by rw [← htofun (σ.invFun x)]; exact h1
    have h3 : τ.invFun (τ.toFun (σ.invFun x)) = σ.invFun x := τ.left_inv (σ.invFun x)
    rw [h2] at h3
    exact h3.symm

end IUT
