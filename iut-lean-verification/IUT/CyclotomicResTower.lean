/-
  IUT/CyclotomicResTower.lean — CTR（A3 一般 n 塔 M2: 一般段の制限準同型
  res_n : Gal(ℚ(ζ_{3^{n+1}})/ℚ) → Gal(ℚ(ζ_{3ⁿ})/ℚ)）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・
     実円分塔 ℚ(ζ_{3ⁿ}) ⊂ ℚ(ζ_{3^{n+1}}) の上での、**任意段の制限準同型
     res_n の本物の構成**を n 一般で行う。上段自己同型 σ の指標
     a = ctrChar σ（σ(ζ_{n+1}) = ζ_{n+1}^a・`ctmFind` 抽出）に対し
     res_n(σ) := σ_{a mod 3ⁿ}（`csaAut`・下段の代入自己同型）と定め、逆元 witness を
     σ 自身の逆 `fieldAutInv σ` の指標から choice-free に供給する（Bezout 不使用）。
     意味論 compat（ι_n ∘ res_n(σ) = σ ∘ ι_n）と群準同型性（map_mul）を完全証明する。
     これは M2（一般段機構）の最終部品であり、CR39（n=1 の res₁）の n 一般化。

  **complete_pct 影響**: A3 一般 n 塔（M2）——**任意段の制限準同型
  res_n: Gal(ℚ(ζ_{3^{n+1}})/ℚ) → Gal(ℚ(ζ_{3ⁿ})/ℚ)（compat ＋ 群準同型）を
  n 一般で本物に構成**する。これで M2（ι_n の体埋め込み cte・一般 μ の同定 ctm・
  決定補題 cae・代入自己同型 csa・制限 ctr＝本ファイル）が本物で揃う。逆系
  InverseSystem／逆極限 profinite G_K（ctl・M3）の直接の前提が整う。本ファイル
  単体では complete_pct 未設定（M2 完成として独立監査で反映）。

  内容（設計 audit/A3-inverse-limit-roadmap-2026-07-09.md §3.5）:
   * `ctr_rpow_hom`/`ctr_pow_rpow` — σ の冪保存・rpow と ctmPow の同一視。
   * `ctr_sigma_zeta_pow` — σ(ζ_{n+1})^{3^{n+1}} = 1（map 連鎖）。
   * `ctrChar`/`ctr_char_spec`/`ctr_char_lt` — 指標 a = ctmFind(σ ζ_{n+1})。
   * `ctr_sigma_pow` — σ(ζ_{n+1}^k) = ζ_{n+1}^{a·k}。
   * `ctrChar_not_dvd3` — 3∤a（σ 単射 ＋ 位数論法）。
   * `ctr_map_zeta`/`ctr_map_pow` — ι_n(ζ_n) = ζ_{n+1}³・ι_n(ζ_n^k) = ζ_{n+1}^{3k}。
   * `ctr_char_mul_mod_big`/`ctr_res_haa` — a·b ≡ 1 (mod 3^{n+1})（σ の逆から）。
   * `ctrRes`/`ctrRes_mem` — res_n 本体（下段代入自己同型）と Gal 所属。
   * `ctr_halpha`/`ctr_map_ext`/`ctr_compat` — 意味論 compat（生成元 → 全点）。
   * `ctr_res_comp`/`ctrResHom` — 群準同型 res_n(σ∘τ) = res_n(σ)∘res_n(τ)。
   * `ctr_inv_exists` — mod 3^{n+1} 逆元の Hensel 構成（choice-free・Bezout 不使用）。
   * `ctr_surjective` — res_n の全射性（一般 n・M4 を待たず・仮説 0 本）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・ℚ 上・円分塔 ℚ(ζ_{3ⁿ}) ⊂ ℚ(ζ_{3^{n+1}}) の忠実な部分ケース。
   (ii)  本ファイルは res_n の族（compat ＋ 群準同型 ＋ 全射性）まで。**逆系
         InverseSystem・逆極限 profinite G_K は ctl（M3・後段）の射程**であり
         本ファイルに含めない。
   (iii) **res_n の全射性（`ctr_surjective`）は本ファイルで完全証明**した（一般 n・
         M4 の群同型を待たず）。原像 σ の構成に要する mod 3^{n+1} 逆元は
         `ctr_inv_exists`（Hensel 持ち上げ・choice-free・Bezout 不使用）で構成的に
         供給する。ただし **res_n の核が位数 3 の巡回群である等の完全な短完全列
         同型（Gal ≅ (ℤ/3^{n+1})^×）は未形式化**（M4 の射程）。
   (iv)  分離性・正規性の一般論も未形式化。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/
  dashboard/graph/tools は不更新・親が統合）。3ⁿ は omega 不可
  （ctm_pow3_split / Nat.pow_succ を明示補助）。
-/
import IUT.CyclotomicSubAut
import IUT.CyclotomicAutExt
import IUT.FundamentalGroup

namespace IUT

/-! ## CTR-0: σ の冪保存と rpow / ctmPow の同一視 -/

/-- **CTR-0a: σ の冪保存** — 体自己同型 σ は冪を保つ:
    rpow(σ z) m = σ(rpow z m)。m 帰納（map_one で 0 次・map_mul で漸化）。 -/
theorem ctr_rpow_hom (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega)))
    (z : (cteField (n + 1) (by omega)).carrier) : ∀ m,
    rpow (cteField (n + 1) (by omega)).toCRing (σ.toFun z) m
      = σ.toFun (rpow (cteField (n + 1) (by omega)).toCRing z m) := by
  intro m
  induction m with
  | zero => exact σ.map_one.symm
  | succ m ih =>
    show (cteField (n + 1) (by omega)).toCRing.mul
        (rpow (cteField (n + 1) (by omega)).toCRing (σ.toFun z) m) (σ.toFun z)
      = σ.toFun ((cteField (n + 1) (by omega)).toCRing.mul
        (rpow (cteField (n + 1) (by omega)).toCRing z m) z)
    rw [ih, σ.map_mul (rpow (cteField (n + 1) (by omega)).toCRing z m) z]

/-- **CTR-0b: rpow = ctmPow** — 各段 ℚ(ζ_{3ⁿ}) 上の rpow による ζ_n の冪は
    ctmPow（NF 環の乗法の反復）と一致する（k 帰納・同じ NF 環の乗法）。 -/
theorem ctr_pow_rpow (n : Nat) (hn : 1 ≤ n) (k : Nat) :
    ctmPow n hn k = rpow (cteField n hn).toCRing (ctmZeta n hn) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (cteField n hn).toCRing.mul (ctmPow n hn k) (ctmZeta n hn)
      = (cteField n hn).toCRing.mul (rpow (cteField n hn).toCRing (ctmZeta n hn) k) (ctmZeta n hn)
    rw [ih]

/-! ## CTR-1: 段間写像 ι_n(ζ_n) = ζ_{n+1}³ と ι_n(ζ_n^k) = ζ_{n+1}^{3k} -/

/-- **CTR-1a: ι_n(ζ_n) = ζ_{n+1}³** — cteMap（= stretch X ↦ X³）は生成元 ζ_n（= X̄）を
    ζ_{n+1}³ = X̄³ = ctmPow (n+1) 3 に送る（deg 3 < 2·3ⁿ で簡約不要）。 -/
theorem ctr_map_zeta (n : Nat) (hn : 1 ≤ n) :
    cteMap n hn (ctmZeta n hn) = ctmPow (n + 1) (by omega) 3 := by
  apply Subtype.ext
  show ctsStretch (psSingle ratRing ratRing.one 1) = (ctmPow (n + 1) (by omega) 3).val
  rw [ctsStretch_single ratRing.one 1,
      ctm_pow_small (n + 1) (by omega) 3
        (show (3 : Nat) < 2 * 3 ^ n from by
          have hp := cte_pow3_pos (n - 1)
          have hs := ctm_pow3_split n hn
          omega)]

/-- **CTR-1b: ι_n(ζ_n^k) = ζ_{n+1}^{3k}** — 段間写像は環準同型（`cteIota`）で冪を保つ
    （`ringHom_rpow`）ゆえ ζ_n^k を (ζ_{n+1}³)^k = ζ_{n+1}^{3k} に送る。 -/
theorem ctr_map_pow (n : Nat) (hn : 1 ≤ n) (k : Nat) :
    cteMap n hn (ctmPow n hn k) = ctmPow (n + 1) (by omega) (3 * k) := by
  rw [ctr_pow_rpow n hn k]
  show (cteIota n hn).map (rpow (cteField n hn).toCRing (ctmZeta n hn) k)
    = ctmPow (n + 1) (by omega) (3 * k)
  rw [ringHom_rpow (cteIota n hn) (ctmZeta n hn) k]
  have hz : (cteIota n hn).map (ctmZeta n hn) = ctmPow (n + 1) (by omega) 3 := ctr_map_zeta n hn
  rw [hz]
  exact ctmr_rpow_ctmPow (n + 1) (by omega) 3 k

/-! ## CTR-2: σ(ζ_{n+1})^{3^{n+1}} = 1・指標 a = ctrChar σ -/

/-- **CTR-2a: σ(ζ_{n+1})^{3^{n+1}} = 1** — map の 3^{n+1} 連鎖: σ(ζ)^{3^{n+1}} =
    σ(ζ^{3^{n+1}}) = σ(1) = 1（冪保存 ＋ `ctm_zeta_pow` ＋ `map_one`）。 -/
theorem ctr_sigma_zeta_pow (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    rpow (cteField (n + 1) (by omega)).toCRing (σ.toFun (ctmZeta (n + 1) (by omega))) (3 ^ (n + 1))
      = (cteField (n + 1) (by omega)).toCRing.one := by
  rw [ctr_rpow_hom n hn σ (ctmZeta (n + 1) (by omega)) (3 ^ (n + 1)),
      ← ctr_pow_rpow (n + 1) (by omega) (3 ^ (n + 1)), ctm_zeta_pow (n + 1) (by omega)]
  exact σ.map_one

/-- **CTR-2b: 指標 a = ctrChar σ** — σ(ζ_{n+1}) = ζ_{n+1}^a の a（`ctmFind` 抽出）。 -/
def ctrChar (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) : Nat :=
  ctmFind (n + 1) (by omega) (σ.toFun (ctmZeta (n + 1) (by omega)))

/-- **CTR-2c: σ(ζ_{n+1}) = ζ_{n+1}^a**（`ctmFind_spec`）。 -/
theorem ctr_char_spec (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    σ.toFun (ctmZeta (n + 1) (by omega)) = ctmPow (n + 1) (by omega) (ctrChar n hn σ) :=
  (ctmFind_spec (n + 1) (by omega) (σ.toFun (ctmZeta (n + 1) (by omega)))
    (ctr_sigma_zeta_pow n hn σ)).1

/-- **CTR-2d: a < 3^{n+1}**（`ctmFind_spec`）。 -/
theorem ctr_char_lt (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    ctrChar n hn σ < 3 ^ (n + 1) :=
  (ctmFind_spec (n + 1) (by omega) (σ.toFun (ctmZeta (n + 1) (by omega)))
    (ctr_sigma_zeta_pow n hn σ)).2

/-- **CTR-2e: σ(ζ_{n+1}^k) = ζ_{n+1}^{a·k}** — 冪保存 ＋ 指標 ＋ `ctmr_rpow_ctmPow`。 -/
theorem ctr_sigma_pow (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) (k : Nat) :
    σ.toFun (ctmPow (n + 1) (by omega) k) = ctmPow (n + 1) (by omega) (ctrChar n hn σ * k) := by
  rw [ctr_pow_rpow (n + 1) (by omega) k,
      ← ctr_rpow_hom n hn σ (ctmZeta (n + 1) (by omega)) k, ctr_char_spec n hn σ]
  exact ctmr_rpow_ctmPow (n + 1) (by omega) (ctrChar n hn σ) k

/-! ## CTR-3: σ の単射性・3∤a -/

/-- **CTR-3a: σ は単射**（明示逆写像 `left_inv` の帰結）。 -/
theorem ctr_sigma_inj (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega)))
    {p q : (cteField (n + 1) (by omega)).carrier} (h : σ.toFun p = σ.toFun q) : p = q := by
  have hc : σ.invFun (σ.toFun p) = σ.invFun (σ.toFun q) := congrArg σ.invFun h
  rw [σ.left_inv p, σ.left_inv q] at hc
  exact hc

/-- **CTR-3b: 3∤a** — もし 3∣a なら σ(ζ^{3ⁿ}) = ζ^{a·3ⁿ} = ζ^{t·3^{n+1}} = 1 = σ(1)、
    σ 単射で ζ^{3ⁿ} = 1 となり `ctm_zeta_pow_sub_ne` に矛盾。 -/
theorem ctrChar_not_dvd3 (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    ¬ 3 ∣ ctrChar n hn σ := by
  intro hdvd
  obtain ⟨t, ht⟩ := hdvd
  have h1 : σ.toFun (ctmPow (n + 1) (by omega) (3 ^ n))
      = ctmPow (n + 1) (by omega) (ctrChar n hn σ * 3 ^ n) := ctr_sigma_pow n hn σ (3 ^ n)
  have h2 : ctrChar n hn σ * 3 ^ n = t * 3 ^ (n + 1) := by
    rw [ht]
    calc 3 * t * 3 ^ n
        = t * 3 * 3 ^ n := by rw [Nat.mul_comm 3 t]
      _ = t * (3 * 3 ^ n) := Nat.mul_assoc t 3 (3 ^ n)
      _ = t * (3 ^ n * 3) := by rw [Nat.mul_comm 3 (3 ^ n)]
      _ = t * 3 ^ (n + 1) := by rw [← Nat.pow_succ]
  rw [h2, ctmr_pow_mul (n + 1) (by omega) t] at h1
  have h4 : σ.toFun (ctmPow (n + 1) (by omega) (3 ^ n))
      = σ.toFun (cteField (n + 1) (by omega)).toCRing.one := by
    rw [h1]; exact σ.map_one.symm
  have h5 : ctmPow (n + 1) (by omega) (3 ^ n) = (cteField (n + 1) (by omega)).toCRing.one :=
    ctr_sigma_inj n hn σ h4
  exact ctm_zeta_pow_sub_ne (n + 1) (by omega) h5

/-! ## CTR-4: a·b ≡ 1 (mod 3^{n+1})（σ の逆 fieldAutInv σ の指標 b から） -/

/-- **CTR-4a: 指標が 1 を与える** — ζ^k = ζ^1 ⟹ k ≡ 1 (mod 3^{n+1})
    （冪の周期性 ＋ 冪の相異性）。 -/
theorem ctr_index_one (n : Nat) (hn : 1 ≤ n) (k : Nat)
    (hk : ctmPow (n + 1) (by omega) k = ctmPow (n + 1) (by omega) 1) :
    k % 3 ^ (n + 1) = 1 := by
  have hmod : ctmPow (n + 1) (by omega) k = ctmPow (n + 1) (by omega) (k % 3 ^ (n + 1)) :=
    ctm_pow_mod (n + 1) (by omega) k
  have hpos : 0 < 3 ^ (n + 1) := by have := cte_pow3_pos (n + 1); omega
  have hmlt : k % 3 ^ (n + 1) < 3 ^ (n + 1) := Nat.mod_lt k hpos
  have h1lt : 1 < 3 ^ (n + 1) := by have := cte_pow3_pos n; rw [Nat.pow_succ]; omega
  cases Nat.decEq (k % 3 ^ (n + 1)) 1 with
  | isTrue h => exact h
  | isFalse h =>
    exact absurd (hmod.symm.trans hk)
      (ctm_powers_distinct (n + 1) (by omega) (k % 3 ^ (n + 1)) 1 hmlt h1lt h)

/-- **CTR-4b: a·b ≡ 1 (mod 3^{n+1})** — b = ctrChar(fieldAutInv σ) は σ⁻¹ の指標
    （σ⁻¹(ζ) = ζ^b）。σ(ζ^b) = ζ^{a·b}（`ctr_sigma_pow`）かつ σ(σ⁻¹(ζ)) = ζ
    （`right_inv`）より ζ^{a·b} = ζ、指標一致で a·b ≡ 1。 -/
theorem ctr_char_mul_mod_big (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    (ctrChar n hn σ * ctrChar n hn (fieldAutInv σ)) % 3 ^ (n + 1) = 1 := by
  apply ctr_index_one n hn (ctrChar n hn σ * ctrChar n hn (fieldAutInv σ))
  have hinv : σ.invFun (ctmZeta (n + 1) (by omega))
      = ctmPow (n + 1) (by omega) (ctrChar n hn (fieldAutInv σ)) :=
    ctr_char_spec n hn (fieldAutInv σ)
  have hstep : σ.toFun (ctmPow (n + 1) (by omega) (ctrChar n hn (fieldAutInv σ)))
      = ctmZeta (n + 1) (by omega) := by
    rw [← hinv]; exact σ.right_inv (ctmZeta (n + 1) (by omega))
  have hsp := ctr_sigma_pow n hn σ (ctrChar n hn (fieldAutInv σ))
  rw [ctm_pow_one (n + 1) (by omega), ← hsp]
  exact hstep

/-! ## CTR-5: res_n 本体（下段代入自己同型 σ_{a mod 3ⁿ}） -/

/-- **CTR-5a: 3∤(a mod 3ⁿ)** — 3∤a と 3∣3ⁿ（n≥1）から。 -/
theorem ctr_mod_not_dvd3 (n : Nat) (hn : 1 ≤ n) (a : Nat) (ha : ¬ 3 ∣ a) :
    ¬ 3 ∣ (a % 3 ^ n) := by
  intro h
  apply ha
  have hd3 : (3 : Nat) ∣ 3 ^ n := ⟨3 ^ (n - 1), by rw [ctm_pow3_split n hn, Nat.mul_comm]⟩
  have hmm : a % 3 ^ n % 3 = a % 3 := Nat.mod_mod_of_dvd a hd3
  obtain ⟨r, hr⟩ := h
  have hz : a % 3 ^ n % 3 = 0 := by rw [hr]; omega
  rw [hmm] at hz
  exact Nat.dvd_of_mod_eq_zero hz

/-- **CTR-5b: 3∤(ctrChar σ mod 3ⁿ)**。 -/
theorem ctr_res_nd (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    ¬ 3 ∣ (ctrChar n hn σ % 3 ^ n) :=
  ctr_mod_not_dvd3 n hn (ctrChar n hn σ) (ctrChar_not_dvd3 n hn σ)

/-- **CTR-5c: 3∤(ctrChar(fieldAutInv σ) mod 3ⁿ)**。 -/
theorem ctr_res_nd_inv (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    ¬ 3 ∣ (ctrChar n hn (fieldAutInv σ) % 3 ^ n) :=
  ctr_mod_not_dvd3 n hn (ctrChar n hn (fieldAutInv σ)) (ctrChar_not_dvd3 n hn (fieldAutInv σ))

/-- **CTR-5d: (a mod 3ⁿ)·(b mod 3ⁿ) ≡ 1 (mod 3ⁿ)** — a·b ≡ 1 (mod 3^{n+1}) を
    3ⁿ に落とし（`Nat.mod_mod_of_dvd`）、剰余の積で書き直す（`Nat.mul_mod`）。 -/
theorem ctr_res_haa (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    (ctrChar n hn σ % 3 ^ n) * (ctrChar n hn (fieldAutInv σ) % 3 ^ n) % 3 ^ n = 1 := by
  have hbig : (ctrChar n hn σ * ctrChar n hn (fieldAutInv σ)) % 3 ^ (n + 1) = 1 :=
    ctr_char_mul_mod_big n hn σ
  have hdvd : (3 : Nat) ^ n ∣ 3 ^ (n + 1) := ⟨3, Nat.pow_succ 3 n⟩
  have hmm := Nat.mod_mod_of_dvd (ctrChar n hn σ * ctrChar n hn (fieldAutInv σ)) hdvd
  rw [hbig] at hmm
  have hp : 1 < 3 ^ n := by have hpp := cte_pow3_pos (n - 1); rw [ctm_pow3_split n hn]; omega
  have h1 : (1 : Nat) % 3 ^ n = 1 := Nat.mod_eq_of_lt hp
  rw [h1] at hmm
  have key : (ctrChar n hn σ % 3 ^ n) * (ctrChar n hn (fieldAutInv σ) % 3 ^ n) % 3 ^ n
      = (ctrChar n hn σ * ctrChar n hn (fieldAutInv σ)) % 3 ^ n :=
    (Nat.mul_mod (ctrChar n hn σ) (ctrChar n hn (fieldAutInv σ)) (3 ^ n)).symm
  rw [key]
  exact hmm.symm

/-- **CTR-5e: 制限準同型 res_n(σ)** — 指標 a = ctrChar σ に対し、下段の代入
    自己同型 σ_{a mod 3ⁿ}（`csaAut`）。逆元 witness は σ⁻¹ = fieldAutInv σ の
    指標 b（a·b ≡ 1 mod 3^{n+1} ⟹ (a%3ⁿ)·(b%3ⁿ) ≡ 1 mod 3ⁿ）から choice-free に供給。 -/
def ctrRes (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    FieldAut (cteField n hn) :=
  csaAut n hn (ctrChar n hn σ % 3 ^ n) (ctrChar n hn (fieldAutInv σ) % 3 ^ n)
    (ctr_res_nd n hn σ) (ctr_res_nd_inv n hn σ) (ctr_res_haa n hn σ)

/-- **CTR-5f: res_n(σ) ∈ Gal(ℚ(ζ_{3ⁿ})/ℚ)**（ℚ 各点固定・`csaAut_mem`）。 -/
theorem ctrRes_mem (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    (galoisSubgroup (cteExt n hn)).mem (ctrRes n hn σ) :=
  csaAut_mem n hn (ctrChar n hn σ % 3 ^ n) (ctrChar n hn (fieldAutInv σ) % 3 ^ n)
    (ctr_res_nd n hn σ) (ctr_res_nd_inv n hn σ) (ctr_res_haa n hn σ)

/-! ## CTR-6: 冪の周期補題 3a ≡ 3(a mod 3ⁿ) (mod 3^{n+1}) -/

/-- **CTR-6: 周期補題** — ζ_{n+1}^{a·3} = ζ_{n+1}^{3·(a mod 3ⁿ)}。
    a·3 = (a/3ⁿ)·3^{n+1} + 3·(a mod 3ⁿ) と分割し、第1項の冪を 1 に潰す。 -/
theorem ctr_pow_period (n : Nat) (hn : 1 ≤ n) (a : Nat) :
    ctmPow (n + 1) (by omega) (a * 3) = ctmPow (n + 1) (by omega) (3 * (a % 3 ^ n)) := by
  have hdm : (a / 3 ^ n) * 3 ^ n + a % 3 ^ n = a := by
    have h0 := Nat.div_add_mod a (3 ^ n)
    rw [Nat.mul_comm (3 ^ n) (a / 3 ^ n)] at h0
    exact h0
  have harith : a * 3 = (a / 3 ^ n) * 3 ^ (n + 1) + (a % 3 ^ n) * 3 := by
    calc a * 3
        = ((a / 3 ^ n) * 3 ^ n + a % 3 ^ n) * 3 := by rw [hdm]
      _ = (a / 3 ^ n) * 3 ^ n * 3 + (a % 3 ^ n) * 3 := by rw [Nat.add_mul]
      _ = (a / 3 ^ n) * (3 ^ n * 3) + (a % 3 ^ n) * 3 := by rw [Nat.mul_assoc]
      _ = (a / 3 ^ n) * 3 ^ (n + 1) + (a % 3 ^ n) * 3 := by rw [← Nat.pow_succ]
  rw [harith, ctmPow_add (n + 1) (by omega) ((a / 3 ^ n) * 3 ^ (n + 1)) ((a % 3 ^ n) * 3),
      ctmr_pow_mul (n + 1) (by omega) (a / 3 ^ n), Nat.mul_comm (a % 3 ^ n) 3]
  exact (ctmK (n + 1) (by omega)).ring.one_mul (ctmPow (n + 1) (by omega) (3 * (a % 3 ^ n)))

/-! ## CTR-7: 生成元での意味論 halpha -/

/-- **CTR-7: 生成元での意味論** — ι_n(res_n(σ)(ζ_n)) = σ(ι_n(ζ_n))。
    ι_n(res_n(σ)(ζ_n)) = ι_n(ζ_n^{a mod 3ⁿ}) = ζ_{n+1}^{3·(a mod 3ⁿ)}、
    σ(ι_n(ζ_n)) = σ(ζ_{n+1}³) = ζ_{n+1}^{a·3}。周期補題で一致。 -/
theorem ctr_halpha (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    cteMap n hn ((ctrRes n hn σ).toFun (caeGen n hn))
      = σ.toFun (cteMap n hn (caeGen n hn)) := by
  rw [csa_gen_eq n hn,
      show (ctrRes n hn σ).toFun (ctmZeta n hn) = ctmPow n hn (ctrChar n hn σ % 3 ^ n) from
        csaSub_zeta n hn (ctrChar n hn σ % 3 ^ n),
      ctr_map_pow n hn (ctrChar n hn σ % 3 ^ n),
      ctr_map_zeta n hn, ctr_sigma_pow n hn σ 3]
  exact (ctr_pow_period n hn (ctrChar n hn σ)).symm

/-! ## CTR-8: 全点 compat（生成元 → 全点の決定補題 ＋ 二写像への適用） -/

/-- **CTR-8a: 段間決定補題** — 下段の 2 つの環準同型 φ,ψ : ℚ(ζ_{3ⁿ}) → ℚ(ζ_{3^{n+1}})
    が ℚ を（上段の ι へ）固定し生成元 ζ_n で一致すれば全点一致。`cae_endo_ext` の
    codomain を次段に一般化した版（分解 `cae_decompose` を φ,ψ で像し各項を
    `ringHom_rpow` で ζ_n の像に還元）。 -/
theorem ctr_map_ext (n : Nat) (hn : 1 ≤ n)
    (φ ψ : RingHom (cteField n hn).toCRing (cteField (n + 1) (by omega)).toCRing)
    (hφ : ∀ c, φ.map (caeIncl n hn c) = caeIncl (n + 1) (by omega) c)
    (hψ : ∀ c, ψ.map (caeIncl n hn c) = caeIncl (n + 1) (by omega) c)
    (h : φ.map (caeGen n hn) = ψ.map (caeGen n hn)) :
    ∀ y, φ.map y = ψ.map y := by
  intro y
  rw [← cae_decompose n hn y,
    ringHom_rsum φ
      (fun i => (cteField n hn).mul (caeIncl n hn (y.val i)) (caePow n hn i)) (2 * 3 ^ (n - 1)),
    ringHom_rsum ψ
      (fun i => (cteField n hn).mul (caeIncl n hn (y.val i)) (caePow n hn i)) (2 * 3 ^ (n - 1))]
  apply rsum_congr (cteField (n + 1) (by omega)).toCRing (2 * 3 ^ (n - 1))
  intro i hi
  show φ.map ((cteField n hn).mul (caeIncl n hn (y.val i)) (caePow n hn i))
    = ψ.map ((cteField n hn).mul (caeIncl n hn (y.val i)) (caePow n hn i))
  rw [φ.map_mul (caeIncl n hn (y.val i)) (caePow n hn i),
      ψ.map_mul (caeIncl n hn (y.val i)) (caePow n hn i),
      hφ (y.val i), hψ (y.val i),
      show caePow n hn i = rpow (cteField n hn).toCRing (caeGen n hn) i from rfl,
      ringHom_rpow φ (caeGen n hn) i, ringHom_rpow ψ (caeGen n hn) i, h]

/-- **CTR-8b: 環準同型 φ = ι_n ∘ res_n(σ)**（下段自己同型を上段へ）。 -/
def ctrResHomMap (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    RingHom (cteField n hn).toCRing (cteField (n + 1) (by omega)).toCRing where
  map := fun x => cteMap n hn ((ctrRes n hn σ).toFun x)
  map_add := fun x y => by
    show cteMap n hn ((ctrRes n hn σ).toFun ((cteField n hn).toCRing.add x y))
      = (cteField (n + 1) (by omega)).toCRing.add
          (cteMap n hn ((ctrRes n hn σ).toFun x)) (cteMap n hn ((ctrRes n hn σ).toFun y))
    rw [(ctrRes n hn σ).map_add x y,
        cteMap_add n hn ((ctrRes n hn σ).toFun x) ((ctrRes n hn σ).toFun y)]
  map_mul := fun x y => by
    show cteMap n hn ((ctrRes n hn σ).toFun ((cteField n hn).toCRing.mul x y))
      = (cteField (n + 1) (by omega)).toCRing.mul
          (cteMap n hn ((ctrRes n hn σ).toFun x)) (cteMap n hn ((ctrRes n hn σ).toFun y))
    rw [(ctrRes n hn σ).map_mul x y,
        cteMap_mul n hn ((ctrRes n hn σ).toFun x) ((ctrRes n hn σ).toFun y)]
  map_one := by
    show cteMap n hn ((ctrRes n hn σ).toFun (cteField n hn).toCRing.one)
      = (cteField (n + 1) (by omega)).toCRing.one
    rw [(ctrRes n hn σ).map_one, cteMap_one n hn]

/-- **CTR-8c: 環準同型 ψ = σ ∘ ι_n**（上段自己同型を ι_n の後に）。 -/
def ctrSigmaMap (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega))) :
    RingHom (cteField n hn).toCRing (cteField (n + 1) (by omega)).toCRing where
  map := fun x => σ.toFun (cteMap n hn x)
  map_add := fun x y => by
    show σ.toFun (cteMap n hn ((cteField n hn).toCRing.add x y))
      = (cteField (n + 1) (by omega)).toCRing.add
          (σ.toFun (cteMap n hn x)) (σ.toFun (cteMap n hn y))
    rw [cteMap_add n hn x y, σ.map_add (cteMap n hn x) (cteMap n hn y)]
  map_mul := fun x y => by
    show σ.toFun (cteMap n hn ((cteField n hn).toCRing.mul x y))
      = (cteField (n + 1) (by omega)).toCRing.mul
          (σ.toFun (cteMap n hn x)) (σ.toFun (cteMap n hn y))
    rw [cteMap_mul n hn x y, σ.map_mul (cteMap n hn x) (cteMap n hn y)]
  map_one := by
    show σ.toFun (cteMap n hn (cteField n hn).toCRing.one)
      = (cteField (n + 1) (by omega)).toCRing.one
    rw [cteMap_one n hn, σ.map_one]

/-- **CTR-8d: φ は ℚ を（上段 ι へ）固定** — res_n(σ) が ℚ を固定（`csa_subst_incl`）し
    ι_n が定数を保つ（`cte_incl_compat`）。 -/
theorem ctr_res_fix_incl (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega)))
    (c : QRat) :
    (ctrResHomMap n hn σ).map (caeIncl n hn c) = caeIncl (n + 1) (by omega) c := by
  have h1 : (ctrRes n hn σ).toFun (caeIncl n hn c) = caeIncl n hn c :=
    csa_subst_incl n hn (ctrChar n hn σ % 3 ^ n) c
  show cteMap n hn ((ctrRes n hn σ).toFun (caeIncl n hn c)) = caeIncl (n + 1) (by omega) c
  rw [h1]
  show cteMap n hn (gefIncl (ctsPhi n) (2 * 3 ^ (n - 1)) (cte_nf_pos n hn) c)
    = caeIncl (n + 1) (by omega) c
  rw [cte_incl_compat n hn c]
  rfl

/-- **CTR-8e: ψ は ℚ を（上段 ι へ）固定** — ι_n が定数を保ち σ が ℚ を固定（hσ）。 -/
theorem ctr_sigma_fix_incl (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega)))
    (hσ : (galoisSubgroup (cteExt (n + 1) (by omega))).mem σ) (c : QRat) :
    (ctrSigmaMap n hn σ).map (caeIncl n hn c) = caeIncl (n + 1) (by omega) c := by
  show σ.toFun (cteMap n hn (caeIncl n hn c)) = caeIncl (n + 1) (by omega) c
  show σ.toFun (cteMap n hn (gefIncl (ctsPhi n) (2 * 3 ^ (n - 1)) (cte_nf_pos n hn) c))
    = caeIncl (n + 1) (by omega) c
  rw [cte_incl_compat n hn c]
  exact hσ c

/-- **CTR-8f: 意味論 compat（本丸）** — ι_n ∘ res_n(σ) = σ ∘ ι_n（全点）。
    二写像 φ,ψ を段間決定補題 `ctr_map_ext` に渡し、生成元一致 `ctr_halpha` で閉じる。 -/
theorem ctr_compat (n : Nat) (hn : 1 ≤ n) (σ : FieldAut (cteField (n + 1) (by omega)))
    (hσ : (galoisSubgroup (cteExt (n + 1) (by omega))).mem σ) :
    ∀ x, cteMap n hn ((ctrRes n hn σ).toFun x) = σ.toFun (cteMap n hn x) := by
  intro x
  exact ctr_map_ext n hn (ctrResHomMap n hn σ) (ctrSigmaMap n hn σ)
    (ctr_res_fix_incl n hn σ) (ctr_sigma_fix_incl n hn σ hσ) (ctr_halpha n hn σ) x

/-! ## CTR-9: 群準同型性 res_n(σ∘τ) = res_n(σ)∘res_n(τ) -/

/-- **CTR-9a: res_n は乗法的** — 両辺は Gal(ℚ(ζ_{3ⁿ})/ℚ) の元で、生成元 ζ_n での
    一致（`cae_aut_ext`）に帰着。ι_n の単射性 `cteMap_inj` で
    ι_n(res(σ∘τ) ζ_n) = ι_n(res(σ)(res(τ) ζ_n)) を compat の 3 連鎖で σ(τ(ι ζ_n)) に揃える。 -/
theorem ctr_res_comp (n : Nat) (hn : 1 ≤ n)
    (σ τ : FieldAut (cteField (n + 1) (by omega)))
    (hσ : (galoisSubgroup (cteExt (n + 1) (by omega))).mem σ)
    (hτ : (galoisSubgroup (cteExt (n + 1) (by omega))).mem τ) :
    ctrRes n hn (fieldAutComp σ τ) = fieldAutComp (ctrRes n hn σ) (ctrRes n hn τ) := by
  refine cae_aut_ext n hn (ctrRes n hn (fieldAutComp σ τ))
    (fieldAutComp (ctrRes n hn σ) (ctrRes n hn τ))
    (ctrRes_mem n hn (fieldAutComp σ τ))
    ((galoisSubgroup (cteExt n hn)).mul_mem (ctrRes_mem n hn σ) (ctrRes_mem n hn τ)) ?_
  apply cteMap_inj n hn
  have hA : cteMap n hn ((ctrRes n hn (fieldAutComp σ τ)).toFun (caeGen n hn))
      = σ.toFun (τ.toFun (cteMap n hn (caeGen n hn))) :=
    ctr_compat n hn (fieldAutComp σ τ)
      ((galoisSubgroup (cteExt (n + 1) (by omega))).mul_mem hσ hτ) (caeGen n hn)
  have hB : cteMap n hn ((fieldAutComp (ctrRes n hn σ) (ctrRes n hn τ)).toFun (caeGen n hn))
      = σ.toFun (τ.toFun (cteMap n hn (caeGen n hn))) := by
    show cteMap n hn ((ctrRes n hn σ).toFun ((ctrRes n hn τ).toFun (caeGen n hn)))
        = σ.toFun (τ.toFun (cteMap n hn (caeGen n hn)))
    rw [ctr_compat n hn σ hσ ((ctrRes n hn τ).toFun (caeGen n hn)),
        ctr_compat n hn τ hτ (caeGen n hn)]
  rw [hA, hB]

/-- **CTR-9b: 制限準同型 res_n : Gal(ℚ(ζ_{3^{n+1}})/ℚ) → Gal(ℚ(ζ_{3ⁿ})/ℚ)** — 群準同型
    （`Hom`）。map は res_n 本体、map_mul は `ctr_res_comp`。M2（一般段機構）の最終部品。 -/
def ctrResHom (n : Nat) (hn : 1 ≤ n) :
    Hom (galoisGroupGrp (cteExt (n + 1) (by omega))) (galoisGroupGrp (cteExt n hn)) where
  map := fun a => ⟨ctrRes n hn a.val, ctrRes_mem n hn a.val⟩
  map_mul := fun a b => by
    apply Subtype.ext
    show ctrRes n hn (fieldAutComp a.val b.val)
        = fieldAutComp (ctrRes n hn a.val) (ctrRes n hn b.val)
    exact ctr_res_comp n hn a.val b.val a.property b.property

/-! ## CTR-10: 段一般の指標（全射性の準備・ℓ 一般） -/

/-- **CTR-10a: 冪保存（ℓ 一般）**。 -/
theorem ctr_rpow_hom_gen (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ : FieldAut (cteField ℓ hℓ))
    (z : (cteField ℓ hℓ).carrier) : ∀ m,
    rpow (cteField ℓ hℓ).toCRing (σ.toFun z) m = σ.toFun (rpow (cteField ℓ hℓ).toCRing z m) := by
  intro m
  induction m with
  | zero => exact σ.map_one.symm
  | succ m ih =>
    show (cteField ℓ hℓ).toCRing.mul (rpow (cteField ℓ hℓ).toCRing (σ.toFun z) m) (σ.toFun z)
      = σ.toFun ((cteField ℓ hℓ).toCRing.mul (rpow (cteField ℓ hℓ).toCRing z m) z)
    rw [ih, σ.map_mul (rpow (cteField ℓ hℓ).toCRing z m) z]

/-- **CTR-10b: σ(ζ_ℓ)^{3^ℓ} = 1（ℓ 一般）**。 -/
theorem ctr_zeta_pow_gen (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ : FieldAut (cteField ℓ hℓ)) :
    rpow (cteField ℓ hℓ).toCRing (σ.toFun (ctmZeta ℓ hℓ)) (3 ^ ℓ)
      = (cteField ℓ hℓ).toCRing.one := by
  rw [ctr_rpow_hom_gen ℓ hℓ σ (ctmZeta ℓ hℓ) (3 ^ ℓ), ← ctr_pow_rpow ℓ hℓ (3 ^ ℓ), ctm_zeta_pow ℓ hℓ]
  exact σ.map_one

/-- **CTR-10c: 指標（ℓ 一般）** a = ctmFind(σ ζ_ℓ)。 -/
def ctr_charG (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ : FieldAut (cteField ℓ hℓ)) : Nat :=
  ctmFind ℓ hℓ (σ.toFun (ctmZeta ℓ hℓ))

/-- **CTR-10d: σ(ζ_ℓ) = ζ_ℓ^a（ℓ 一般）**。 -/
theorem ctr_charG_spec (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ : FieldAut (cteField ℓ hℓ)) :
    σ.toFun (ctmZeta ℓ hℓ) = ctmPow ℓ hℓ (ctr_charG ℓ hℓ σ) :=
  (ctmFind_spec ℓ hℓ (σ.toFun (ctmZeta ℓ hℓ)) (ctr_zeta_pow_gen ℓ hℓ σ)).1

/-- **CTR-10e: a < 3^ℓ（ℓ 一般）**。 -/
theorem ctr_charG_lt (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ : FieldAut (cteField ℓ hℓ)) :
    ctr_charG ℓ hℓ σ < 3 ^ ℓ :=
  (ctmFind_spec ℓ hℓ (σ.toFun (ctmZeta ℓ hℓ)) (ctr_zeta_pow_gen ℓ hℓ σ)).2

/-- **CTR-10f: σ(ζ_ℓ^k) = ζ_ℓ^{a·k}（ℓ 一般）**。 -/
theorem ctr_sigma_powG (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ : FieldAut (cteField ℓ hℓ)) (k : Nat) :
    σ.toFun (ctmPow ℓ hℓ k) = ctmPow ℓ hℓ (ctr_charG ℓ hℓ σ * k) := by
  rw [ctr_pow_rpow ℓ hℓ k, ← ctr_rpow_hom_gen ℓ hℓ σ (ctmZeta ℓ hℓ) k, ctr_charG_spec ℓ hℓ σ]
  exact ctmr_rpow_ctmPow ℓ hℓ (ctr_charG ℓ hℓ σ) k

/-- **CTR-10g: σ は単射（ℓ 一般）**。 -/
theorem ctr_sigma_injG (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ : FieldAut (cteField ℓ hℓ))
    {p q : (cteField ℓ hℓ).carrier} (h : σ.toFun p = σ.toFun q) : p = q := by
  have hc : σ.invFun (σ.toFun p) = σ.invFun (σ.toFun q) := congrArg σ.invFun h
  rw [σ.left_inv p, σ.left_inv q] at hc
  exact hc

/-- **CTR-10h: 3∤a（ℓ 一般）** — σ 単射 ＋ 位数論法。 -/
theorem ctr_charG_nd3 (ℓ : Nat) (hℓ : 1 ≤ ℓ) (σ : FieldAut (cteField ℓ hℓ)) :
    ¬ 3 ∣ ctr_charG ℓ hℓ σ := by
  intro hdvd
  obtain ⟨t, ht⟩ := hdvd
  have h1 : σ.toFun (ctmPow ℓ hℓ (3 ^ (ℓ - 1)))
      = ctmPow ℓ hℓ (ctr_charG ℓ hℓ σ * 3 ^ (ℓ - 1)) := ctr_sigma_powG ℓ hℓ σ (3 ^ (ℓ - 1))
  have h2 : ctr_charG ℓ hℓ σ * 3 ^ (ℓ - 1) = t * 3 ^ ℓ := by
    rw [ht]
    calc 3 * t * 3 ^ (ℓ - 1)
        = t * 3 * 3 ^ (ℓ - 1) := by rw [Nat.mul_comm 3 t]
      _ = t * (3 * 3 ^ (ℓ - 1)) := Nat.mul_assoc t 3 (3 ^ (ℓ - 1))
      _ = t * (3 ^ (ℓ - 1) * 3) := by rw [Nat.mul_comm 3 (3 ^ (ℓ - 1))]
      _ = t * 3 ^ ℓ := by rw [← ctm_pow3_split ℓ hℓ]
  rw [h2, ctmr_pow_mul ℓ hℓ t] at h1
  have h4 : σ.toFun (ctmPow ℓ hℓ (3 ^ (ℓ - 1))) = σ.toFun (cteField ℓ hℓ).toCRing.one := by
    rw [h1]; exact σ.map_one.symm
  have h5 : ctmPow ℓ hℓ (3 ^ (ℓ - 1)) = (cteField ℓ hℓ).toCRing.one := ctr_sigma_injG ℓ hℓ σ h4
  exact ctm_zeta_pow_sub_ne ℓ hℓ h5

/-! ## CTR-11: mod 3^ℓ 逆元の choice-free 構成（Hensel 持ち上げ・Bezout 不使用） -/

/-- **CTR-11a: mod 3 の逆元選択** — 3∤a のとき q + a·t ≡ 0 (mod 3) となる t が在る
    （a mod 3 ∈ {1,2} の可逆性で構成的に）。 -/
theorem ctr_tex (a q : Nat) (ha : a % 3 = 1 ∨ a % 3 = 2) : ∃ t, (q + a * t) % 3 = 0 := by
  cases ha with
  | inl h1 => refine ⟨(3 - q % 3) % 3, ?_⟩; rw [Nat.add_mod, Nat.mul_mod, h1]; omega
  | inr h2 => refine ⟨q % 3, ?_⟩; rw [Nat.add_mod, Nat.mul_mod, h2]; omega

/-- **CTR-11b: mod 3^{m+1} 逆元の存在（Hensel）** — 3∤a なら 3∤b かつ a·b ≡ 1 (mod 3^{m+1})
    となる b が在る。m 帰納: mod 3 の逆元（`ctr_tex`）を 3^{m+1} → 3^{m+2} へ持ち上げる
    （b' := b + t·3^{m+1}・a·b' = 1 + (k+a·t)·3^{m+1} を 1 + w·3^{m+2} に）。choice 不使用。 -/
theorem ctr_inv_exists : ∀ m a, ¬ 3 ∣ a → ∃ b, ¬ 3 ∣ b ∧ a * b % 3 ^ (m + 1) = 1 := by
  intro m
  induction m with
  | zero =>
    intro a ha
    refine ⟨a % 3, ?_, ?_⟩
    · intro hd; obtain ⟨k, hk⟩ := hd; omega
    · show a * (a % 3) % 3 = 1
      rw [Nat.mul_mod a (a % 3) 3, Nat.mod_mod_of_dvd a (Nat.dvd_refl 3)]
      have h : a % 3 = 1 ∨ a % 3 = 2 := by omega
      cases h with
      | inl h1 => rw [h1]
      | inr h2 => rw [h2]
  | succ m ih =>
    intro a ha
    obtain ⟨b, hb3, hbm⟩ := ih a ha
    have hamod : a % 3 = 1 ∨ a % 3 = 2 := by omega
    have hdm := Nat.div_add_mod (a * b) (3 ^ (m + 1))
    rw [hbm] at hdm
    obtain ⟨t, ht⟩ := ctr_tex a (a * b / 3 ^ (m + 1)) hamod
    refine ⟨b + t * 3 ^ (m + 1), ?_, ?_⟩
    · intro hd
      apply hb3
      have hQ3 : (3 : Nat) ∣ 3 ^ (m + 1) := ⟨3 ^ m, by rw [Nat.pow_succ, Nat.mul_comm]⟩
      obtain ⟨s, hs⟩ := hQ3
      obtain ⟨w, hw⟩ := hd
      have hts : t * 3 ^ (m + 1) = 3 * (t * s) := by
        rw [hs, ← Nat.mul_assoc, Nat.mul_comm t 3, Nat.mul_assoc]
      exact ⟨w - t * s, by omega⟩
    · obtain ⟨w, hw⟩ :=
        (Nat.dvd_of_mod_eq_zero ht : (3 : Nat) ∣ (a * b / 3 ^ (m + 1) + a * t))
      have hQ : (3 : Nat) ^ (m + 1 + 1) = 3 ^ (m + 1) * 3 := Nat.pow_succ 3 (m + 1)
      have hval : a * (b + t * 3 ^ (m + 1)) = 1 + w * 3 ^ (m + 1 + 1) := by
        have e1 : a * (b + t * 3 ^ (m + 1)) = a * b + a * t * 3 ^ (m + 1) := by
          rw [Nat.mul_add, Nat.mul_assoc]
        have e2 : (a * b / 3 ^ (m + 1) + a * t) * 3 ^ (m + 1)
            = 3 ^ (m + 1) * (a * b / 3 ^ (m + 1)) + a * t * 3 ^ (m + 1) := by
          rw [Nat.add_mul, Nat.mul_comm (a * b / 3 ^ (m + 1)) (3 ^ (m + 1))]
        have e3 : (a * b / 3 ^ (m + 1) + a * t) * 3 ^ (m + 1) = 3 * w * 3 ^ (m + 1) := by rw [hw]
        have e4 : 3 ^ (m + 1) * (a * b / 3 ^ (m + 1)) + a * t * 3 ^ (m + 1)
            = 3 * w * 3 ^ (m + 1) := by rw [← e2]; exact e3
        have e5 : w * (3 ^ (m + 1) * 3) = 3 * w * 3 ^ (m + 1) := by
          rw [Nat.mul_comm (3 ^ (m + 1)) 3, ← Nat.mul_assoc, Nat.mul_comm w 3]
        rw [e1, ← hdm, hQ, e5]
        omega
      rw [hval]
      have hp : 1 < 3 ^ (m + 1 + 1) := by
        have h1 : 1 ≤ 3 ^ (m + 1) := Nat.one_le_pow (m + 1) 3 (by omega)
        rw [hQ]; omega
      have hmod : (1 + w * 3 ^ (m + 1 + 1)) % 3 ^ (m + 1 + 1) = 1 % 3 ^ (m + 1 + 1) :=
        Nat.add_mul_mod_self_right 1 w (3 ^ (m + 1 + 1))
      rw [hmod, Nat.mod_eq_of_lt hp]

/-! ## CTR-12: res_n の全射性（★一般 n で M4 を待たず） -/

/-- **CTR-12: res_n は全射（本丸）** — 任意の τ ∈ Gal(ℚ(ζ_{3ⁿ})/ℚ) に σ ∈ Gal(ℚ(ζ_{3^{n+1}})/ℚ)
    で res_n(σ) = τ。τ の指標 a := ctr_charG τ（τ(ζ_n)=ζ_n^a・3∤a・a<3ⁿ）を 3^{n+1} 上へ
    そのまま持ち上げ、逆元 witness を `ctr_inv_exists`（Hensel・choice-free）で供給して
    σ := σ_a（`csaAut`）を作る。ctrChar σ = a・a%3ⁿ = a より res_n(σ) = σ_a = τ
    （`cae_aut_ext` の生成元一致）。仮説 0 本。 -/
theorem ctr_surjective (n : Nat) (hn : 1 ≤ n) :
    ∀ τ : (galoisGroupGrp (cteExt n hn)).carrier,
      ∃ σ : (galoisGroupGrp (cteExt (n + 1) (by omega))).carrier,
        (ctrResHom n hn).map σ = τ := by
  intro τ
  -- τ の指標 a
  have ha_lt : ctr_charG n hn τ.val < 3 ^ n := ctr_charG_lt n hn τ.val
  have ha_nd : ¬ 3 ∣ ctr_charG n hn τ.val := ctr_charG_nd3 n hn τ.val
  have ha_spec : τ.val.toFun (ctmZeta n hn) = ctmPow n hn (ctr_charG n hn τ.val) :=
    ctr_charG_spec n hn τ.val
  -- 逆元 witness（mod 3^{n+1}）
  obtain ⟨ainv, hainv_nd, hainv⟩ := ctr_inv_exists n (ctr_charG n hn τ.val) ha_nd
  -- 持ち上げた σ
  let σaut : FieldAut (cteField (n + 1) (by omega)) :=
    csaAut (n + 1) (by omega) (ctr_charG n hn τ.val) ainv ha_nd hainv_nd hainv
  have hσmem : (galoisSubgroup (cteExt (n + 1) (by omega))).mem σaut :=
    csaAut_mem (n + 1) (by omega) (ctr_charG n hn τ.val) ainv ha_nd hainv_nd hainv
  have hσzeta : σaut.toFun (ctmZeta (n + 1) (by omega))
      = ctmPow (n + 1) (by omega) (ctr_charG n hn τ.val) :=
    csaAut_zeta (n + 1) (by omega) (ctr_charG n hn τ.val) ainv ha_nd hainv_nd hainv
  -- ctrChar σaut = a（両者 < 3^{n+1}・冪相異性）
  have hchar : ctrChar n hn σaut = ctr_charG n hn τ.val := by
    have hspec : σaut.toFun (ctmZeta (n + 1) (by omega))
        = ctmPow (n + 1) (by omega) (ctrChar n hn σaut) := ctr_char_spec n hn σaut
    have heq : ctmPow (n + 1) (by omega) (ctr_charG n hn τ.val)
        = ctmPow (n + 1) (by omega) (ctrChar n hn σaut) := by rw [← hσzeta, hspec]
    have hlt1 : ctrChar n hn σaut < 3 ^ (n + 1) := ctr_char_lt n hn σaut
    have hlt2 : ctr_charG n hn τ.val < 3 ^ (n + 1) := by
      have hnn : (3 : Nat) ^ n < 3 ^ (n + 1) := by
        rw [Nat.pow_succ]; have := Nat.one_le_pow n 3 (by omega); omega
      omega
    cases Nat.decEq (ctrChar n hn σaut) (ctr_charG n hn τ.val) with
    | isTrue h => exact h
    | isFalse h =>
      exact absurd heq
        (ctm_powers_distinct (n + 1) (by omega) (ctr_charG n hn τ.val) (ctrChar n hn σaut)
          hlt2 hlt1 (fun he => h he.symm))
  -- 原像を構成
  refine ⟨⟨σaut, hσmem⟩, ?_⟩
  apply Subtype.ext
  show ctrRes n hn σaut = τ.val
  refine cae_aut_ext n hn (ctrRes n hn σaut) τ.val (ctrRes_mem n hn σaut) τ.property ?_
  rw [csa_gen_eq n hn,
      show (ctrRes n hn σaut).toFun (ctmZeta n hn) = ctmPow n hn (ctrChar n hn σaut % 3 ^ n) from
        csaSub_zeta n hn (ctrChar n hn σaut % 3 ^ n),
      ha_spec, hchar, Nat.mod_eq_of_lt ha_lt]

end IUT
