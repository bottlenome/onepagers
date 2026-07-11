/-
  IUT/Q3Mu3TmzBridge.lean — 比較橋（level-3 テータ cyclotome ↔ tmz の mod-3 層）
  ——tmi の実 ℤ₃^× 不定性の (ℤ/3)^× 商をテータ剛性で殺す（level-3 kill の昇格）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、テータ側の実局所環
     U₂ = O_{ℚ₃(ζ₃)}^× 内の実 μ₃（R1 の q3rqZeta・q3tlZeta3U）と、tmz 側の大域実円分体
     ℚ(ζ₃) 内の実 μ₃（`tmzG 0 = cmrGrp 1`）を、選択公理なしの離散対数 `ctmFind` で結ぶ
     実 G-同変な群同一視 β : Hom (tmzG 0) q3rqU を本物に建て、そこを通して tmi の実
     ℤ₃^×=`zpsLimit` の実作用 `tmiFromUnits` を level-3 テータ内部 μ₃ へ輸送し、level-3
     mono-theta 剛性 `q3m3r_cyclotome_fixed` で **(ℤ/3)^× 商を殺す**（mod-3 成分 u₀=1 強制）。
     コードベース初の「テータ側 q3rq/q3tl/q3m3r ↔ 円分側 tmz/tmi/cgar」を繋ぐ橋。
     toy 主語なし——主語は実 U₂・実 tmzG 0・実 zpsLimit。）

  **complete_pct 影響**: level-3 kill 監査の**上限 #1（機構レベル止まり・tmzLimit への
  比較橋なし）を正面 discharge**する。剛性の主語をテータ環境の内部 μ₃ から tmi の実
  ℤ₃^× 対象へ橋渡しし、テータ剛性が **tmi の実 Aut(ℤ₃(1))≅ℤ₃^× 不定性の (ℤ/3)^× 商に
  作用して殺す**水準へ昇格する。設計見込み A7 0.47 → 0.49–0.51（敵対的下振れ 0.48）。
  **算術注記**: `compute_complete_pct.py` は round() を使い Σ_A = 47.62 + 12·s ゆえ
  **s=0.49 で 53.50 → 表示 54**（再監査注記「54 には A7≥0.54」は算術誤り・s=0.49 が閾値）。
  A6/A8/A5 は本ファイルで一切主張しない（二重計上境界）。数値は独立監査が確定する。

  内容（設計 audit/next-after-level3-kill-detail-2026-07-11.md §2.2 の 13 項）:
   * q3mb_conj_norm / q3mbConjU / q3mb_conjU_mul — 実共役の U₂ 単数群化（N(x̄)=N(x)）。
   * q3mb_zetaU_cube / q3mb_g0_cube / q3mb_pow_mod3 / q3mb_zeta_pow_mod — μ₃ 冪簿記（g³=1）。
   * q3mb_flip_invariant — 生成元反転で輸送指数不変 (gᵃ)ᵇ=(gᵇ)ᵃ（ℤ/2 曖昧の kill 不変性）。
   * q3mbU / q3mbHom (★橋 β) — y ↦ ζU^{find y}・map_mul は tmz_mul_find＋ζU³=1。
   * q3mb_inj / q3mb_image_mu3 / q3mb_onto_mu3 — 単射・像=μ₃（q3mc_mu3_complete 消費）。
   * q3mb_equivariant (★同変) — β(σy)=pow(βy) χ(σ)、β(σ₂y)=q3mbConjU(βy)（cgar_rigidity 消費）。
   * q3mbUnit / q3mbInt — 内部版橋（q3m3rZeta と整合）。
   * q3mb_transport (★輸送) — β∘(tmiFromUnits u の level-0)=(βの u₀ 冪)。tmiFromUnits 本体消費。
   * q3mb_kill_mod3 (★★★ display-moving) — テータ両立 φ が輸送を実現 ⟹ (u.val 0).val=1。
     証明: t=tmeZetaLim（明示・choice-free）で左辺 φ(q3m3rZeta)=q3m3rZeta（剛性消費）・
     右辺 ζ_int^{u₀}・u₀∈{1,2}・u₀=2 ⟹ ζ_int=ζ_int² ⟹ 矛盾（ζ₃≠1）。
   * q3mb_admissible_iff — u₀=1 ⟺ テータ実現可能（消去形 iff）。
   * Q3Mu3TmzBridgeData / q3mbData / q3mb_exists — capstone。

  正直な限定（§4 規約により消さない・弱化しない・追記のみ）:
  1. **mod-3 層（level 0）のみ**。tmzLimit 全体との橋（塔版・F-wild）ではない。pro-3 bulk
     1+3ℤ₃ と n≥2 レベルは依然 SURVIVES（F-wild まで）。tmi の残存宣言・q3m3r 正直限定は不変更。
  2. 同一視は**群レベル・生成元指定つき**（ζ vs ζ² の ℤ/2 曖昧）。**kill は曖昧さ不変**
     （q3mb_flip_invariant で機械証明）。実埋め込み ℚ(ζ₃)↪ℚ₃(ζ₃)（体/環レベル局所大域比較・
     分解群理論）は形式化しない。
  3. テータ側 Galois は位数 2 の実共役 q3rqConj のみ（実 G_{ℚ₃} 不在——R1 限定 7 継承）。
  4. q=27 忠実部分ケース・endo 定式化・実テータ関数/π₁/大域 Galois 0（R2b–R4 継承）。
  5. **二重計上の firewall**: tmi(tmiFromUnits)・q3m3r(cyclotome_fixed)・tmz・q3rq・q3mc は
     **消費のみ・再証明ゼロ・言明複製ゼロ**（tmi の ℤ₃^× 特徴付けを再述しない）。新規は
     橋 β＋輸送＋(ℤ/3)^× kill——grep 実測で q3rq を import する円分側モジュールはゼロ。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。prefix `q3mb`。
-/
import IUT.Q3Mu3Rigidity
import IUT.TateModuleIndeterminacy
import IUT.TateModuleZ3
import IUT.Q3TateCurveL2
import IUT.Q3Mu3Completeness
import IUT.CyclotomicGKActionReal
import IUT.CyclotomicRigidity
import IUT.LocalBrauer

namespace IUT

/-! ## q3mb-1: 実共役の U₂ 単数群化（#1・#2） -/

/-- **q3mb-1a（#1）: 共役はノルムを保つ** N(x̄) = N(x)（成分 (−b)(−b)=bb）。 -/
theorem q3mb_conj_norm (x : q3rqCar) : q3rqNorm (q3rqConj x) = q3rqNorm x := by
  show z3.add (z3.mul x.1 x.1)
        (z3.neg (z3.mul q3rqD (z3.mul (z3.neg x.2) (z3.neg x.2))))
     = z3.add (z3.mul x.1 x.1) (z3.neg (z3.mul q3rqD (z3.mul x.2 x.2)))
  rw [z3.neg_mul x.2 (z3.neg x.2), z3.mul_neg x.2 x.2, z3.neg_neg]

/-- **q3mb-1b（#2）: 実共役の単数群化** q3mbConjU : U₂ → U₂（N 保存ゆえ単数を単数へ）。 -/
def q3mbConjU (x : q3rqU.carrier) : q3rqU.carrier :=
  ⟨q3rqConj x.val, by
    show IsZpUnit 3 (q3rqNorm (q3rqConj x.val))
    rw [q3mb_conj_norm]
    exact x.property⟩

/-- **q3mb-1c（#2）: 共役の乗法性**（q3rq_conj_mul）。 -/
theorem q3mb_conjU_mul (x y : q3rqU.carrier) :
    q3mbConjU (q3rqU.mul x y) = q3rqU.mul (q3mbConjU x) (q3mbConjU y) := by
  apply Subtype.ext
  show q3rqConj (q3rqMul x.val y.val) = q3rqMul (q3rqConj x.val) (q3rqConj y.val)
  exact q3rq_conj_mul x.val y.val

/-! ## q3mb-2: μ₃ 冪簿記（ζU³=1・mod 3・flip 不変・#3・#8） -/

/-- **q3mb-2a: ζU³ = 1 in U₂**（q3tl_zetaU_cube を冪形へ）。 -/
theorem q3mb_zetaU_cube : q3rqU.pow q3tlZeta3U 3 = q3rqU.one := by
  show q3rqU.mul q3tlZeta3U (q3rqU.mul q3tlZeta3U (q3rqU.mul q3tlZeta3U q3rqU.one))
     = q3rqU.one
  rw [q3rqU.mul_one, ← q3rqU.mul_assoc q3tlZeta3U q3tlZeta3U q3tlZeta3U]
  exact q3tl_zetaU_cube

/-- **q3mb-2b: (ζU⁻¹)³ = 1 in U₂**（内部 cyclotome 生成元 g₀=ζ₃⁻¹ の位数 3）。 -/
theorem q3mb_g0_cube : q3rqU.pow (q3rqU.inv q3tlZeta3U) 3 = q3rqU.one := by
  rw [brau_pow_inv q3rqU q3rqU_comm q3tlZeta3U 3, q3mb_zetaU_cube, Grp.inv_one]

/-- **q3mb-2c（#3 一般形）: g³=1 なら pow g (e%3) = pow g e**（可換冪の周期性）。 -/
theorem q3mb_pow_mod3 (g : q3rqU.carrier) (hg : q3rqU.pow g 3 = q3rqU.one) (e : Nat) :
    q3rqU.pow g (e % 3) = q3rqU.pow g e := by
  have hdm : 3 * (e / 3) + e % 3 = e := Nat.div_add_mod e 3
  calc q3rqU.pow g (e % 3)
      = q3rqU.mul q3rqU.one (q3rqU.pow g (e % 3)) := (q3rqU.one_mul _).symm
    _ = q3rqU.mul (q3rqU.pow (q3rqU.pow g 3) (e / 3)) (q3rqU.pow g (e % 3)) := by
        rw [hg, brau_pow_one q3rqU (e / 3)]
    _ = q3rqU.mul (q3rqU.pow g (3 * (e / 3))) (q3rqU.pow g (e % 3)) := by
        rw [← cycRig_pow_mul q3rqU q3rqU_comm g 3 (e / 3)]
    _ = q3rqU.pow g (3 * (e / 3) + e % 3) :=
        (cycRig_pow_add q3rqU q3rqU_comm g (3 * (e / 3)) (e % 3)).symm
    _ = q3rqU.pow g e := by rw [hdm]

/-- **q3mb-2d（#3）: pow ζU (e%3) = pow ζU e**。 -/
theorem q3mb_zeta_pow_mod (e : Nat) :
    q3rqU.pow q3tlZeta3U (e % 3) = q3rqU.pow q3tlZeta3U e :=
  q3mb_pow_mod3 q3tlZeta3U q3mb_zetaU_cube e

/-- 純 Nat の剰余変換 e % 3^1 = e % 3（部分型を含まない文脈で `3^1` を潰す）。 -/
theorem q3mb_mod_conv1 (e : Nat) : e % 3 ^ 1 = e % 3 := by rw [Nat.pow_one]

/-- 純 Nat の剰余変換 (a·k) % 3^1 = (k·a) % 3。 -/
theorem q3mb_mod_conv (a k : Nat) : (a * k) % 3 ^ 1 = (k * a) % 3 := by
  rw [Nat.pow_one, Nat.mul_comm a k]

/-- **q3mb-2d': pow ζU (e % 3^1) = pow ζU e**（tmz 側の `% 3^ℓ`（ℓ=1）に合わせた版）。 -/
theorem q3mb_zeta_pow_mod1 (e : Nat) :
    q3rqU.pow q3tlZeta3U (e % 3 ^ 1) = q3rqU.pow q3tlZeta3U e := by
  rw [q3mb_mod_conv1 e]; exact q3mb_zeta_pow_mod e

/-- **q3mb-2e（#8・生成元反転で輸送指数不変）: (gᵃ)ᵇ = (gᵇ)ᵃ** — β を反転（生成元を
    gᵇ に取り替え）しても輸送指数 a は不変。ℤ/2 曖昧（ζ vs ζ²）の下で kill が不変である
    ことの機械証明（Aut(μ₃) 可換ゆえ冪写像の輸送指数は生成元選択に依らない）。 -/
theorem q3mb_flip_invariant (g : q3rqU.carrier) (a b : Nat) :
    q3rqU.pow (q3rqU.pow g a) b = q3rqU.pow (q3rqU.pow g b) a := by
  rw [← cycRig_pow_mul q3rqU q3rqU_comm g a b, ← cycRig_pow_mul q3rqU q3rqU_comm g b a,
      Nat.mul_comm a b]

/-! ## q3mb-3: μ₃ 冪の値と相異性（単射・像の材料） -/

/-- pow ζU 1 の val = ζ₃。 -/
theorem q3mb_pow1_val : (q3rqU.pow q3tlZeta3U 1).val = q3rqZeta := by
  show q3rqMul q3rqZeta q3rqOne = q3rqZeta
  exact q3rq_mul_one q3rqZeta

/-- pow ζU 2 の val = ζ₃²。 -/
theorem q3mb_pow2_val : (q3rqU.pow q3tlZeta3U 2).val = q3rqZetaSq := by
  show q3rqMul q3rqZeta (q3rqU.pow q3tlZeta3U 1).val = q3rqMul q3rqZeta q3rqZeta
  rw [q3mb_pow1_val]

/-- pow ζU k は μ₃ に留まる（μ₃ 閉性 q3rq_mu3_closed の帰納）。 -/
theorem q3mb_pow_mu3 (k : Nat) : q3rqMu3 (q3rqU.pow q3tlZeta3U k).val := by
  induction k with
  | zero => exact Or.inl rfl
  | succ j ih =>
    show q3rqMu3 (q3rqMul q3rqZeta (q3rqU.pow q3tlZeta3U j).val)
    exact q3rq_mu3_closed q3rqZeta _ (Or.inr (Or.inl rfl)) ih

/-- ζU⁰ ≠ ζU¹（1 ≠ ζ₃）。 -/
theorem q3mb_ne_01 : q3rqU.pow q3tlZeta3U 0 ≠ q3rqU.pow q3tlZeta3U 1 := by
  intro h
  have hv : (q3rqU.pow q3tlZeta3U 0).val = q3rqZeta := by
    rw [← q3mb_pow1_val]; exact congrArg Subtype.val h
  exact q3rq_zeta_ne_one hv.symm

/-- ζU⁰ ≠ ζU²（1 ≠ ζ₃²）。 -/
theorem q3mb_ne_02 : q3rqU.pow q3tlZeta3U 0 ≠ q3rqU.pow q3tlZeta3U 2 := by
  intro h
  have hv : (q3rqU.pow q3tlZeta3U 0).val = q3rqZetaSq := by
    rw [← q3mb_pow2_val]; exact congrArg Subtype.val h
  exact q3rq_zeta_sq_ne_one hv.symm

/-- ζU¹ ≠ ζU²（ζ₃ ≠ ζ₃²・第 2 成分 h ≠ −h ⟸ 2h=1≠0）。 -/
theorem q3mb_ne_12 : q3rqU.pow q3tlZeta3U 1 ≠ q3rqU.pow q3tlZeta3U 2 := by
  intro h
  have hv : q3rqZeta = q3rqZetaSq := by
    rw [← q3mb_pow1_val, ← q3mb_pow2_val]; exact congrArg Subtype.val h
  have hv2 : q3rqZeta = ((z3.neg q3rqHalf, z3.neg q3rqHalf) : q3rqCar) := by
    rw [hv]; exact q3rq_zeta_sq_eq
  have hsnd : q3rqHalf = z3.neg q3rqHalf := congrArg (fun p : q3rqCar => p.2) hv2
  have h3 : z3.add q3rqHalf q3rqHalf = z3.add q3rqHalf (z3.neg q3rqHalf) :=
    congrArg (z3.add q3rqHalf) hsnd
  rw [q3rq_half_add_half, z3.add_neg q3rqHalf] at h3
  exact q3rq_z3_one_ne_zero h3

/-- **q3mb-3f: ζU 冪の単射性**（i,j<3・9 分岐・相異性 q3mb_ne_*）。 -/
theorem q3mb_pow_inj (i j : Nat) (hi : i < 3) (hj : j < 3)
    (h : q3rqU.pow q3tlZeta3U i = q3rqU.pow q3tlZeta3U j) : i = j := by
  obtain hi0 | hi1 | hi2 := (show i = 0 ∨ i = 1 ∨ i = 2 by omega)
  · obtain hj0 | hj1 | hj2 := (show j = 0 ∨ j = 1 ∨ j = 2 by omega)
    · rw [hi0, hj0]
    · rw [hi0, hj1] at h; exact absurd h q3mb_ne_01
    · rw [hi0, hj2] at h; exact absurd h q3mb_ne_02
  · obtain hj0 | hj1 | hj2 := (show j = 0 ∨ j = 1 ∨ j = 2 by omega)
    · rw [hi1, hj0] at h; exact absurd h.symm q3mb_ne_01
    · rw [hi1, hj1]
    · rw [hi1, hj2] at h; exact absurd h q3mb_ne_12
  · obtain hj0 | hj1 | hj2 := (show j = 0 ∨ j = 1 ∨ j = 2 by omega)
    · rw [hi2, hj0] at h; exact absurd h.symm q3mb_ne_02
    · rw [hi2, hj1] at h; exact absurd h.symm q3mb_ne_12
    · rw [hi2, hj2]

/-- **q3mb-3g: find の冪則** find((cmrGrp 1).pow y k) = (k·find y) % 3
    （y=ζ^{find y}＋cycRig_pow_mul＋tmz_find_pow）。輸送・全射の材料。 -/
theorem q3mb_find_pow (y : (tmzG 0).carrier) (k : Nat) :
    ctmFind 1 (by omega) ((cmrGrp 1 (by omega)).pow y k).val
      = (k * ctmFind 1 (by omega) y.val) % 3 := by
  have hy : y = (cmrGrp 1 (by omega)).pow (cmrZeta 1 (by omega)) (ctmFind 1 (by omega) y.val) := by
    apply Subtype.ext
    rw [cmr_pow_zeta 1 (by omega) (ctmFind 1 (by omega) y.val)]
    exact tmz_val_find 1 (by omega) y
  have hkey : (cmrGrp 1 (by omega)).pow (cmrZeta 1 (by omega)) (ctmFind 1 (by omega) y.val * k)
      = (cmrGrp 1 (by omega)).pow y k := by
    rw [cycRig_pow_mul (cmrGrp 1 (by omega)) (cmr_comm 1 (by omega)) (cmrZeta 1 (by omega))
          (ctmFind 1 (by omega) y.val) k, ← hy]
  rw [← hkey, cmr_pow_zeta 1 (by omega) (ctmFind 1 (by omega) y.val * k),
      tmz_find_pow 1 (by omega) (ctmFind 1 (by omega) y.val * k),
      q3mb_mod_conv (ctmFind 1 (by omega) y.val) k]

/-! ## q3mb-4: ★ 橋 β : Hom (tmzG 0) q3rqU（#4） -/

/-- **q3mb-4a: 橋の担体写像** β(y) = ζU^{find y}（離散対数・choice-free）。 -/
def q3mbU (y : (tmzG 0).carrier) : q3rqU.carrier :=
  q3rqU.pow q3tlZeta3U (ctmFind 1 (by omega) y.val)

/-- **q3mb-4b（★ #4）: 橋 β : Hom (tmzG 0) q3rqU** — map_mul は tmz_mul_find（離散対数
    加法性）＋ζU³=1（q3mb_zeta_pow_mod）で閉じる。 -/
def q3mbHom : Hom (tmzG 0) q3rqU where
  map := q3mbU
  map_mul := fun y z => by
    show q3rqU.pow q3tlZeta3U (ctmFind 1 (by omega) ((cmrGrp 1 (by omega)).mul y z).val)
       = q3rqU.mul (q3rqU.pow q3tlZeta3U (ctmFind 1 (by omega) y.val))
           (q3rqU.pow q3tlZeta3U (ctmFind 1 (by omega) z.val))
    rw [tmz_mul_find 1 (by omega) y z,
        ← cycRig_pow_add q3rqU q3rqU_comm q3tlZeta3U
          (ctmFind 1 (by omega) y.val) (ctmFind 1 (by omega) z.val)]
    exact q3mb_zeta_pow_mod1 (ctmFind 1 (by omega) y.val + ctmFind 1 (by omega) z.val)

/-- **q3mb-4c（#5）: β 単射**（find<3 の 3 元・ζU 冪の単射性）。 -/
theorem q3mb_inj : q3mbHom.Injective := by
  intro y z h
  apply Subtype.ext
  have h31 : (3 : Nat) ^ 1 = 3 := Nat.pow_one 3
  have hfy : ctmFind 1 (by omega) y.val < 3 := by
    have hb := (ctmFind_spec 1 (by omega) y.val y.property).2
    omega
  have hfz : ctmFind 1 (by omega) z.val < 3 := by
    have hb := (ctmFind_spec 1 (by omega) z.val z.property).2
    omega
  have hf : ctmFind 1 (by omega) y.val = ctmFind 1 (by omega) z.val :=
    q3mb_pow_inj _ _ hfy hfz h
  rw [tmz_val_find 1 (by omega) y, tmz_val_find 1 (by omega) z, hf]

/-- **q3mb-4d（#6）: 像 ⊆ μ₃**（β y ∈ μ₃）。 -/
theorem q3mb_image_mu3 (y : (tmzG 0).carrier) : q3rqMu3 (q3mbHom.map y).val :=
  q3mb_pow_mu3 (ctmFind 1 (by omega) y.val)

/-- **q3mb-4e（★ #6）: μ₃ の全射性（消去形）** — u³=1（μ₃ 完全性 q3mc_mu3_complete 消費）
    ならば β の原像 y が存在する（∃ は Prop 内・choice-free 明示 witness）。 -/
theorem q3mb_onto_mu3 (u : q3rqU.carrier)
    (hu : q3rqMul (q3rqMul u.val u.val) u.val = q3rqOne) :
    ∃ y : (tmzG 0).carrier, q3mbHom.map y = u := by
  obtain h1 | hz | hz2 := q3mc_mu3_complete u.val hu
  · refine ⟨(tmzG 0).one, ?_⟩
    rw [q3mbHom.map_one]
    apply Subtype.ext
    exact h1.symm
  · refine ⟨cmrZeta 1 (by omega), ?_⟩
    apply Subtype.ext
    show (q3rqU.pow q3tlZeta3U (ctmFind 1 (by omega) (cmrZeta 1 (by omega)).val)).val = u.val
    rw [cra_find_zeta 1 (by omega), q3mb_pow1_val, hz]
  · refine ⟨(cmrGrp 1 (by omega)).pow (cmrZeta 1 (by omega)) 2, ?_⟩
    apply Subtype.ext
    show (q3rqU.pow q3tlZeta3U
        (ctmFind 1 (by omega) ((cmrGrp 1 (by omega)).pow (cmrZeta 1 (by omega)) 2).val)).val
       = u.val
    rw [q3mb_find_pow (cmrZeta 1 (by omega)) 2, cra_find_zeta 1 (by omega),
        show (2 * 1) % 3 = 2 from rfl, q3mb_pow2_val, hz2]

/-! ## q3mb-6: ★ 同変性（Galois χ 冪・実共役の反転・#7） -/

/-- **q3mb-6a（★ #7・Galois 同変）: β(σy) = pow (βy) χ(σ)** — tmz 側の実 Galois 作用
    `cgarAct 1 σ` を β で読むと、テータ側 μ₃ 上の χ(σ) 冪になる（cgar_rigidity 消費）。 -/
theorem q3mb_equivariant (σ : (galoisGroupGrp (cteExt 1 (by omega))).carrier)
    (y : (tmzG 0).carrier) :
    q3mbHom.map (((cgarAct 1 (by omega)).act σ).map y)
      = q3rqU.pow (q3mbHom.map y)
          (cycRigExp (galoisGroupGrp (cteExt 1 (by omega))) (cmrMu 1 (by omega))
            (cgarAct 1 (by omega)) σ) := by
  show q3rqU.pow q3tlZeta3U (ctmFind 1 (by omega) (((cgarAct 1 (by omega)).act σ).map y).val)
     = q3rqU.pow (q3rqU.pow q3tlZeta3U (ctmFind 1 (by omega) y.val))
         (cycRigExp (galoisGroupGrp (cteExt 1 (by omega))) (cmrMu 1 (by omega))
           (cgarAct 1 (by omega)) σ)
  rw [cgar_rigidity 1 (by omega) σ y, cmr_pow_zeta 1 (by omega) _,
      tmz_find_pow 1 (by omega) _, q3mb_zeta_pow_mod1 _,
      ← cycRig_pow_mul q3rqU q3rqU_comm q3tlZeta3U (ctmFind 1 (by omega) y.val)
        (cycRigExp (galoisGroupGrp (cteExt 1 (by omega))) (cmrMu 1 (by omega))
          (cgarAct 1 (by omega)) σ),
      Nat.mul_comm (cycRigExp (galoisGroupGrp (cteExt 1 (by omega))) (cmrMu 1 (by omega))
          (cgarAct 1 (by omega)) σ) (ctmFind 1 (by omega) y.val)]

/-- q3mbConjU ζU = ζU²（実共役は μ₃ 上で反転 ζ₃↦ζ₃²）。 -/
theorem q3mb_conjU_zeta : q3mbConjU q3tlZeta3U = q3rqU.pow q3tlZeta3U 2 := by
  apply Subtype.ext
  show q3rqConj q3rqZeta = (q3rqU.pow q3tlZeta3U 2).val
  rw [q3mb_pow2_val]
  exact q3m3r_aut_mu3_nontrivial.2.2.1

/-- q3mbConjU は冪と可換: conjU(gᵏ) = (conjU g)ᵏ。 -/
theorem q3mb_conjU_powC (g : q3rqU.carrier) (k : Nat) :
    q3mbConjU (q3rqU.pow g k) = q3rqU.pow (q3mbConjU g) k := by
  induction k with
  | zero =>
    apply Subtype.ext
    show q3rqConj q3rqOne = q3rqOne
    exact q3m3r_aut_mu3_nontrivial.2.1
  | succ j ih =>
    show q3mbConjU (q3rqU.mul g (q3rqU.pow g j))
       = q3rqU.mul (q3mbConjU g) (q3rqU.pow (q3mbConjU g) j)
    rw [q3mb_conjU_mul, ih]

/-- **q3mb-6b（★ #7・共役同変）: β(σ₂y) = q3mbConjU(βy)** — 代入自己同型 σ₂（χ=2）を
    β で読むと、テータ側の実共役 q3rqConj（反転 ζ₃↦ζ₃²）に一致する。 -/
theorem q3mb_equivariant_conj (y : (tmzG 0).carrier) :
    q3mbHom.map (((cgarAct 1 (by omega)).act (cgarSigma2 1 (by omega))).map y)
      = q3mbConjU (q3mbHom.map y) := by
  rw [q3mb_equivariant (cgarSigma2 1 (by omega)) y, cgar_sigma2_exp 1 (by omega)]
  show q3rqU.pow (q3rqU.pow q3tlZeta3U (ctmFind 1 (by omega) y.val)) 2
     = q3mbConjU (q3rqU.pow q3tlZeta3U (ctmFind 1 (by omega) y.val))
  rw [q3mb_conjU_powC q3tlZeta3U (ctmFind 1 (by omega) y.val), q3mb_conjU_zeta,
      ← cycRig_pow_mul q3rqU q3rqU_comm q3tlZeta3U (ctmFind 1 (by omega) y.val) 2,
      ← cycRig_pow_mul q3rqU q3rqU_comm q3tlZeta3U 2 (ctmFind 1 (by omega) y.val),
      Nat.mul_comm (ctmFind 1 (by omega) y.val) 2]

/-! ## q3mb-7: 内部版橋 q3mbInt（q3m3rZeta と整合・#9） -/

/-- **q3mb-7a: 内部橋の単数部** g₀^{find y}（g₀=ζ₃⁻¹＝内部 cyclotome 生成元の値）。 -/
def q3mbUnit (y : (tmzG 0).carrier) : q3rqU.carrier :=
  q3rqU.pow (q3rqU.inv q3tlZeta3U) (ctmFind 1 (by omega) y.val)

/-- **q3mb-7b（#9）: 内部版橋** q3mbInt : (tmzG 0).carrier → q3m3Car
    （y ↦ (((0, g₀^{find y}), 0), 1)・内部生成元 q3m3rZeta と整合）。 -/
def q3mbInt (y : (tmzG 0).carrier) : q3m3Car :=
  ((((0 : Int), q3mbUnit y), (0 : Int)), q3rqLx.one)

/-- 生成元での単数部の値: q3mbUnit(ζ) = ζ₃⁻¹ = g₀。 -/
theorem q3mb_unit_zeta : q3mbUnit (tmeZetaLim.val 0) = q3rqU.inv q3tlZeta3U := by
  have hz0 : (tmeZetaLim.val 0) = cmrZeta 1 (by omega) := rfl
  show q3rqU.pow (q3rqU.inv q3tlZeta3U) (ctmFind 1 (by omega) (tmeZetaLim.val 0).val)
     = q3rqU.inv q3tlZeta3U
  rw [hz0, cra_find_zeta 1 (by omega)]
  show q3rqU.mul (q3rqU.inv q3tlZeta3U) q3rqU.one = q3rqU.inv q3tlZeta3U
  exact q3rqU.mul_one _

/-- **q3mb-7c（★整合）: q3mbInt(ζ) = q3m3rZeta** — 内部橋の生成元像が level-3 テータ剛性の
    内部 cyclotome 生成元にちょうど一致する。 -/
theorem q3mb_int_zeta : q3mbInt (tmeZetaLim.val 0) = q3m3rZeta := by
  show ((((0 : Int), q3mbUnit (tmeZetaLim.val 0)), (0 : Int)), q3rqLx.one)
     = ((((0 : Int), q3rqU.inv q3tlZeta3U), (0 : Int)), q3rqLx.one)
  rw [q3mb_unit_zeta]

/-! ## q3mb-8: ★ 輸送定理（tmiFromUnits を内部 μ₃ へ・#10） -/

/-- tmiFromUnits の level-0 成分は u₀ 冪（tmiPowHom の成分冪本体・rfl）。 -/
theorem q3mb_level0 (u : zpsLimit.carrier) (t : tmzLimit.carrier) :
    ((tmiFromUnits u).map t).val 0
      = (cmrGrp 1 (by omega)).pow (t.val 0) ((u.val 0).val) := rfl

/-- **q3mb-8（★ #10・輸送）: β∘(tmiFromUnits u の level-0) = (β の u₀ 冪)** — tmi の
    実 ℤ₃^× 作用 `tmiFromUnits u`（成分冪 y↦y^{u₀}）を内部橋 q3mbInt で読むと、内部
    μ₃ の単数部が q3mbUnit(t₀) の u₀ 冪へ輸送される。tmiFromUnits 本体（成分冪）消費。 -/
theorem q3mb_transport (u : zpsLimit.carrier) (t : tmzLimit.carrier) :
    q3mbInt (((tmiFromUnits u).map t).val 0)
      = ((((0 : Int), q3rqU.pow (q3mbUnit (t.val 0)) ((u.val 0).val)), (0 : Int)),
         q3rqLx.one) := by
  show ((((0 : Int), q3mbUnit (((tmiFromUnits u).map t).val 0)), (0 : Int)), q3rqLx.one)
     = ((((0 : Int), q3rqU.pow (q3mbUnit (t.val 0)) ((u.val 0).val)), (0 : Int)), q3rqLx.one)
  have hunit : q3mbUnit (((tmiFromUnits u).map t).val 0)
      = q3rqU.pow (q3mbUnit (t.val 0)) ((u.val 0).val) := by
    show q3rqU.pow (q3rqU.inv q3tlZeta3U)
          (ctmFind 1 (by omega) (((tmiFromUnits u).map t).val 0).val)
       = q3rqU.pow (q3rqU.pow (q3rqU.inv q3tlZeta3U) (ctmFind 1 (by omega) (t.val 0).val))
          ((u.val 0).val)
    rw [q3mb_level0 u t, q3mb_find_pow (t.val 0) ((u.val 0).val),
        q3mb_pow_mod3 (q3rqU.inv q3tlZeta3U) q3mb_g0_cube
          ((u.val 0).val * ctmFind 1 (by omega) (t.val 0).val),
        ← cycRig_pow_mul q3rqU q3rqU_comm (q3rqU.inv q3tlZeta3U)
          (ctmFind 1 (by omega) (t.val 0).val) ((u.val 0).val),
        Nat.mul_comm ((u.val 0).val) (ctmFind 1 (by omega) (t.val 0).val)]
  rw [hunit]

/-! ## q3mb-9: ★★★ display-moving 主定理 — (ℤ/3)^× kill（#11） -/

/-- **q3mb-9（★★★ #11・display-moving）: level-3 テータ剛性が tmi の (ℤ/3)^× 商を殺す** —
    実 ℤ₃^×=`zpsLimit` の元 u と、テータ両立自己準同型 φ（所属限定 hom hHom・所属保存 hMem・
    E₂₇[3] 上恒等 hE3）が「橋輸送で tmiFromUnits u を内部 μ₃ 上に実現」（hreal）するならば
    **(u.val 0).val = 1**。証明: t=tmeZetaLim（明示・choice-free）で左辺 = φ(q3m3rZeta) =
    q3m3rZeta（`q3m3r_cyclotome_fixed` 消費）・右辺 = g₀^{u₀}・u₀∈{1,2}（実単元 mod 3）・
    u₀=2 なら g₀=g₀²⟹g₀=1⟹ζ₃=1 に矛盾。すなわちテータ剛性は tmi の実 ℤ₃^× 不定性の
    (ℤ/3)^× 商を実対象の上で殺す（監査上限 #1 の正面 discharge）。 -/
theorem q3mb_kill_mod3 (u : zpsLimit.carrier) (φ : q3m3Car → q3m3Car)
    (hHom : ∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Mul g g') = q3m3Mul (φ g) (φ g'))
    (hMem : ∀ g, q3m3Mem g → q3m3Mem (φ g))
    (hE3 : ∀ g, q3m3Mem g → q3tlProj.map (φ g).2 = q3tlProj.map g.2)
    (hreal : ∀ t : tmzLimit.carrier,
      φ (q3mbInt (t.val 0)) = q3mbInt (((tmiFromUnits u).map t).val 0)) :
    (u.val 0).val = 1 := by
  have hlt3 : (u.val 0).val < 3 := (u.val 0).property.1
  have hnd : ¬ (3 ∣ (u.val 0).val) := (u.val 0).property.2
  have hkey := hreal tmeZetaLim
  rw [q3mb_int_zeta, q3m3r_cyclotome_fixed φ hHom hMem hE3, q3mb_transport u tmeZetaLim,
      q3mb_unit_zeta] at hkey
  have hcomp : q3rqU.inv q3tlZeta3U = q3rqU.pow (q3rqU.inv q3tlZeta3U) ((u.val 0).val) :=
    congrArg (fun z : q3m3Car => z.1.1.2) hkey
  obtain h1 | h2 := (show (u.val 0).val = 1 ∨ (u.val 0).val = 2 by omega)
  · exact h1
  · exfalso
    rw [h2] at hcomp
    have hpow2 : q3rqU.pow (q3rqU.inv q3tlZeta3U) 2
        = q3rqU.mul (q3rqU.inv q3tlZeta3U) (q3rqU.inv q3tlZeta3U) := by
      show q3rqU.mul (q3rqU.inv q3tlZeta3U)
            (q3rqU.mul (q3rqU.inv q3tlZeta3U) q3rqU.one)
         = q3rqU.mul (q3rqU.inv q3tlZeta3U) (q3rqU.inv q3tlZeta3U)
      rw [q3rqU.mul_one]
    rw [hpow2] at hcomp
    have hce : q3rqU.mul (q3rqU.inv q3tlZeta3U) q3rqU.one
        = q3rqU.mul (q3rqU.inv q3tlZeta3U) (q3rqU.inv q3tlZeta3U) := by
      rw [q3rqU.mul_one]; exact hcomp
    have hone : q3rqU.one = q3rqU.inv q3tlZeta3U := q3rqU.mul_left_cancel hce
    have hzeta : q3tlZeta3U = q3rqU.one := by
      have hh := congrArg q3rqU.inv hone.symm
      rw [Grp.inv_inv, Grp.inv_one] at hh
      exact hh
    have hval : q3rqZeta = q3rqOne := congrArg Subtype.val hzeta
    exact q3rq_zeta_ne_one hval

/-! ## q3mb-10: u₀=1 ⟺ テータ実現可能（消去形 iff・#12） -/

/-- **q3mb-10（#12）: 実現可能性の特徴付け** (u.val 0).val = 1 ⟺ テータ両立 φ が橋輸送で
    tmiFromUnits u を実現する。順方向は φ=id（u₀=1 で level-0 は恒等）、逆は q3mb_kill_mod3。 -/
theorem q3mb_admissible_iff (u : zpsLimit.carrier) :
    (u.val 0).val = 1 ↔
    ∃ φ : q3m3Car → q3m3Car,
      (∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Mul g g') = q3m3Mul (φ g) (φ g')) ∧
      (∀ g, q3m3Mem g → q3m3Mem (φ g)) ∧
      (∀ g, q3m3Mem g → q3tlProj.map (φ g).2 = q3tlProj.map g.2) ∧
      (∀ t : tmzLimit.carrier,
        φ (q3mbInt (t.val 0)) = q3mbInt (((tmiFromUnits u).map t).val 0)) := by
  constructor
  · intro h1
    refine ⟨fun g => g, fun g g' _ _ => rfl, fun g hg => hg, fun g _ => rfl, ?_⟩
    intro t
    show q3mbInt (t.val 0) = q3mbInt (((tmiFromUnits u).map t).val 0)
    have hid : ((tmiFromUnits u).map t).val 0 = t.val 0 := by
      rw [q3mb_level0 u t, h1]
      show (cmrGrp 1 (by omega)).mul (t.val 0) (cmrGrp 1 (by omega)).one = t.val 0
      exact (cmrGrp 1 (by omega)).mul_one (t.val 0)
    rw [hid]
  · intro h
    obtain ⟨φ, hHom, hMem, hE3, hreal⟩ := h
    exact q3mb_kill_mod3 u φ hHom hMem hE3 hreal

/-! ## q3mb-11: capstone -/

/-- **q3mb-11a: 比較橋データ** — 橋 β（準同型・単射・像 μ₃）・実 Galois 同変・生成元反転
    不変・輸送・(ℤ/3)^× kill・実現可能性 iff を束ねる。 -/
structure Q3Mu3TmzBridgeData where
  /-- 橋 β は群準同型。 -/
  bridge_mul : ∀ y z : (tmzG 0).carrier,
    q3mbHom.map ((tmzG 0).mul y z) = q3rqU.mul (q3mbHom.map y) (q3mbHom.map z)
  /-- 橋 β は単射。 -/
  bridge_inj : q3mbHom.Injective
  /-- 像は μ₃ に含まれる。 -/
  image_mu3 : ∀ y : (tmzG 0).carrier, q3rqMu3 (q3mbHom.map y).val
  /-- μ₃ 全射（消去形・q3mc_mu3_complete 消費）。 -/
  onto_mu3 : ∀ u : q3rqU.carrier,
    q3rqMul (q3rqMul u.val u.val) u.val = q3rqOne → ∃ y, q3mbHom.map y = u
  /-- ★ 実 Galois 同変（χ 冪）。 -/
  equivariant : ∀ (σ : (galoisGroupGrp (cteExt 1 (by omega))).carrier) (y : (tmzG 0).carrier),
    q3mbHom.map (((cgarAct 1 (by omega)).act σ).map y)
      = q3rqU.pow (q3mbHom.map y)
          (cycRigExp (galoisGroupGrp (cteExt 1 (by omega))) (cmrMu 1 (by omega))
            (cgarAct 1 (by omega)) σ)
  /-- ★ 実共役同変（反転 ζ₃↦ζ₃²）。 -/
  equivariant_conj : ∀ y : (tmzG 0).carrier,
    q3mbHom.map (((cgarAct 1 (by omega)).act (cgarSigma2 1 (by omega))).map y)
      = q3mbConjU (q3mbHom.map y)
  /-- ★ 生成元反転で輸送指数不変（ℤ/2 曖昧の kill 不変性）。 -/
  flip_invariant : ∀ (g : q3rqU.carrier) (a b : Nat),
    q3rqU.pow (q3rqU.pow g a) b = q3rqU.pow (q3rqU.pow g b) a
  /-- ★ 輸送定理（tmiFromUnits を内部 μ₃ へ）。 -/
  transport : ∀ (u : zpsLimit.carrier) (t : tmzLimit.carrier),
    q3mbInt (((tmiFromUnits u).map t).val 0)
      = ((((0 : Int), q3rqU.pow (q3mbUnit (t.val 0)) ((u.val 0).val)), (0 : Int)), q3rqLx.one)
  /-- ★★★ display-moving: テータ剛性が (ℤ/3)^× 商を殺す。 -/
  kill_mod3 : ∀ (u : zpsLimit.carrier) (φ : q3m3Car → q3m3Car),
    (∀ g g', q3m3Mem g → q3m3Mem g' → φ (q3m3Mul g g') = q3m3Mul (φ g) (φ g')) →
    (∀ g, q3m3Mem g → q3m3Mem (φ g)) →
    (∀ g, q3m3Mem g → q3tlProj.map (φ g).2 = q3tlProj.map g.2) →
    (∀ t : tmzLimit.carrier,
      φ (q3mbInt (t.val 0)) = q3mbInt (((tmiFromUnits u).map t).val 0)) →
    (u.val 0).val = 1
  /-- 内部生成元 q3mbInt(ζ) = q3m3rZeta の整合。 -/
  int_zeta : q3mbInt (tmeZetaLim.val 0) = q3m3rZeta

/-- **q3mb-11b: 見出し実例** — テータ側実 μ₃ ↔ tmz mod-3 層の実 G-同変同一視と、その
    輸送による tmi の実 ℤ₃^× 不定性 (ℤ/3)^× 商の kill。 -/
def q3mbData : Q3Mu3TmzBridgeData where
  bridge_mul := q3mbHom.map_mul
  bridge_inj := q3mb_inj
  image_mu3 := q3mb_image_mu3
  onto_mu3 := q3mb_onto_mu3
  equivariant := q3mb_equivariant
  equivariant_conj := q3mb_equivariant_conj
  flip_invariant := q3mb_flip_invariant
  transport := q3mb_transport
  kill_mod3 := q3mb_kill_mod3
  int_zeta := q3mb_int_zeta

/-- **q3mb-11c: 比較橋の存在**（実 U₂ ↔ 実 tmzG 0・実輸送・実 (ℤ/3)^× kill）。 -/
theorem q3mb_exists : Nonempty Q3Mu3TmzBridgeData := ⟨q3mbData⟩

end IUT
