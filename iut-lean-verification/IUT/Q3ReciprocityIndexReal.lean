/-
  IUT/Q3ReciprocityIndexReal.lean — 柱B・B2 T3-M4-b: **index [U_{L₂}:N(U_M)] = 3 と
    Gal(M/L₂) ≅ U_{L₂}/N(U_M)（B2 相互律 HEADLINE）**
    （tame 掃き出し（q9ut・M4-a）と wild 厳密ノルム（q9cl・T3-core）を合成して
     単数ノルム指数をちょうど 3 に確定し、q9qcGalHom を単射から全単射 Hom
     （= codebase の同型標準）へ昇格する。）

  ── 主要成果の分類: **[実／(a) 昇格]**（q9qc の「Gal ↪ 余核（単射のみ）」を
     「Gal ≅ 余核（全単射 Hom・firstIsoHom と同格の同型標準）」へ昇格。部品は全て実:
     実 O_{L₂} = q3rqRing・実 O_M = q3kRing・実 3 次ノルム q3kNormBase・実 Gal(M/L₂) =
     q9kdG・実 literal 商群 q9qcCoker。audit/pillar-B2-T3-M4-index-detail-2026-07-20.md
     §3 M4-b（b1–b4）の実装。toy 主語なし。）

  complete_pct 影響: **B2 T3-M4-b 完了 = T3 完走（相互律の単数部）・B2 headline**
  （監査次第・設計予測 s_B2 → 0.55–0.60・予測 +0.05〜0.10）。本ファイルで閉じるもの:
   * b1 `q9ix_unit_decomp`（★★ index ≤ 3 の実体）: ∀u 単数, ∃g ∈ Gal,
       q9rcCongMod (q9rgPhi g) u——q9ut_tame_decomp（tame: u·N(w)·φ(g) ∈ U^{(3)}_λ）+
       q9cl_norm_surj（wild: U^{(3)}_λ の単数は厳密にノルム）の合成。
       すなわち **U^{(3)}_λ ⊆ N(U_M) の下で全単数が {1,4,16}·N(U_M) に入る**。
   * b1' `q9ix_index_le_three`: 元レベル形——∀u 単数, [u] ∈ {[1],[4],[16]}。
   * b2 `q9ix_gal_surjective`（★★ 全射性）: ∀ y : q9qcCoker, ∃ g, q9qcGalHom.map g = y
       （quotientProjN_surjective + q9qc_proj_eq_of_cong で b1 を商へ降ろす）。
   * b3 `q9ix_coker_complete`/`q9ix_coker_distinct`/`q9ix_index_eq_three`（★★★）:
       余核はちょうど {[1],[4],[16]} の 3 元（被覆 = 上界・pairwise 相異 = 下界
       q9rc_z3_injects/q9qc_gal_injective）——**[U_{L₂}:N(U_M)] = 3**。
   * b4 `q9ix_gal_iso`（★★★ HEADLINE）: q9qcGalHom は準同型・単射・全射——
       **Gal(M/L₂) ≅ U_{L₂}/N(U_M)**（codebase の同型標準 = 全単射 Hom・
       QuotientGroup の firstIsoHom（firstIso_injective + firstIso_surjective）と同格。
       逆向き Hom の構成は建てない——設計書 §2 A3 のとおり義務でない）。
   * `Q3ReciprocityIndexRealData` / q9ix_data / q9ix_exists — capstone。

  正直な限定（§4 規約により消さない・弱めない・q9cl/q9ut/q9rc/q9qc/q9rg/q9nc/q9nf/
  q9gn/q9ps/q9rf/q9wr/q9kd/q3k/q3rq/z3c 継承の上に追記のみ）:
  1. **本ファイルの index=3・Gal≅余核は単数部 U_{L₂}/N(U_M) のもの**。分数元
     （uniformizer π₉^ℤ）込みの **full L₂^×/N(M^×) の完全配線は未達**（cap b・
     q9qc 限定 1 の継承——値群側 N(π₉)=ζ₃−1 は q9wr 済だが M^× ≅ π₉^ℤ×U_M の
     直積分解を通した束ねは別モジュール）。
  2. **Artin 正規化は未達**: q9rgPhi（e↦1, s↦4, s2↦16）は「単射になる生成元対応」で
     あって Frobenius 正規化から導出された Artin 写像ではない（σ ↦ [4] か [4²] かの
     正規化は未決定・q9rg 限定の継承・不分岐データを足す将来仕事）。
  3. **余核・合同は element/𝔽₃-level**: q9rcCongMod は「∃単数 witness x, a·N(x)=b」の
     witness 形・q9qcCoker は q3rqU の literal Quot 商。「同型」は codebase 標準の
     **全単射 Hom** まで（逆向き Hom q9qcCoker → q9kdG のデータ関数化はスコープ外）。
  4. **単一拡大 M/L₂/ℚ₃ のみ**・一般局所体ゼロ・体化なし・σ を超える Galois ゼロ・
     実テータ関数ゼロ・π₁ 同定ゼロ・可除性 witness 形式（total 付値関数不使用）。
  5. q9cl（modulus 形完備性）・q9ut（tame 掃き出し）・q9rc（下界）・q9qc（literal 商）・
     q9rg（φ の性質）の正直限定を全継承。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用
  （omega は Int/Nat 原子のみ・本ファイルでは不使用）。
-/
import IUT.Q3NormSurjCompleteLimit
import IUT.Q3UnitTameDecomp
import IUT.Q3CokernelObjectReal

namespace IUT

/-! ## q9ix-0: Gal(M/L₂) の逆元簿記 -/

/-- **q9ix-0a: g⁻¹·g = e**（3 元群 Cayley 表・cases で rfl）。 -/
theorem q9ix_ginv_mul (g : q9kdGCar) : q9kdGMul (q9kdGInv g) g = q9kdGCar.e := by
  cases g with
  | e => rfl
  | s => rfl
  | s2 => rfl

/-! ## q9ix-1: b1 前半——掃き出し先はノルム（tame × wild の合成点） -/

/-- **q9ix-1a（★ U^{(3)}_λ ⊆ N の消費形）**: 任意の単数 u に対し
    u·N(w)·φ(g) が**厳密にノルム**となる g, w が存在する。
    tame（q9ut_tame_decomp: u·N(w)·φ(g) は単数かつ U^{(3)}_λ = embed 側 Ufilt 9）+
    wild（q9cl_norm_surj: U^{(3)}_λ の単数は厳密に N(x)）の合成。 -/
theorem q9ix_sweep_is_norm (u : q3rqCar) (hu : q3rqUnitMem u) :
    ∃ g : q9kdGCar, ∃ w : q3kCar, q3kUnitMem w ∧
      q9utIsNorm (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)) := by
  obtain ⟨g, w, hw, hUu, hUf⟩ := q9ut_tame_decomp u hu
  exact ⟨g, w, hw,
    q9cl_norm_surj (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)) hUu hUf⟩

/-! ## q9ix-2: b1——分解定理（index ≤ 3 の実体） -/

/-- **q9ix-2a（★★ b1・分解定理）**: 任意の実単数 u ∈ U_{L₂} に対し
    ∃ g ∈ Gal(M/L₂), φ(g) ≡ u (mod N(U_M))。
    証明: u·N(w)·φ(g) = N(x₀)（q9ix-1a）と φ(g⁻¹)·φ(g) = N(t)（q9rg_hom の e-collapse）
    から witness y = x₀·(w·t)⁻¹ で φ(g⁻¹)·N(y) = u を陽に組む——choice 無縁。 -/
theorem q9ix_unit_decomp (u : q3rqCar) (hu : q3rqUnitMem u) :
    ∃ g : q9kdGCar, q9rcCongMod (q9rgPhi g) u := by
  obtain ⟨g, w, hw, hNorm⟩ := q9ix_sweep_is_norm u hu
  obtain ⟨x0, hx0, hNx0⟩ := hNorm
  obtain ⟨t, ht, hte⟩ := q9rg_hom (q9kdGInv g) g
  have hT : q3kNormBase t = q3rqMul (q9rgPhi (q9kdGInv g)) (q9rgPhi g) := by
    rw [← hte, q9ix_ginv_mul g]
    exact (q3rq_one_mul (q3kNormBase t)).symm
  have hwt : q3kUnitMem (q3kMul w t) := q3k_unit_mul hw ht
  have hI : q3rqMul (q3kNormBase (q3kMul w t))
      (q3kNormBase (q3kInv (q3kMul w t) hwt)) = q3rqOne := by
    rw [← q3k_normBase_mul (q3kMul w t) (q3kInv (q3kMul w t) hwt),
        q3k_inv_mul (q3kMul w t) hwt, q3k_normBase_one]
  refine ⟨q9kdGInv g, q3kMul x0 (q3kInv (q3kMul w t) hwt),
    q3k_unit_mul hx0 (q3k_unit_inv (q3kMul w t) hwt), ?_⟩
  rw [q3k_normBase_mul x0 (q3kInv (q3kMul w t) hwt), hNx0,
      ← q9rg_mul_assoc (q9rgPhi (q9kdGInv g))
        (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g))
        (q3kNormBase (q3kInv (q3kMul w t) hwt)),
      q9rg_mul_comm (q9rgPhi (q9kdGInv g))
        (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g)),
      q9rg_mul_assoc (q3rqMul u (q3kNormBase w)) (q9rgPhi g) (q9rgPhi (q9kdGInv g)),
      q9rg_mul_comm (q9rgPhi g) (q9rgPhi (q9kdGInv g)),
      ← hT,
      q9rg_mul_assoc u (q3kNormBase w) (q3kNormBase t),
      ← q3k_normBase_mul w t,
      q9rg_mul_assoc u (q3kNormBase (q3kMul w t))
        (q3kNormBase (q3kInv (q3kMul w t) hwt)),
      hI]
  exact q3rq_mul_one u

/-- **q9ix-2b（b1'・元レベル index ≤ 3）**: 任意の単数の N-剰余類は
    {[1], [4], [16]} のいずれかに入る（φ(e)=1, φ(s)=4, φ(s2)=16 の場合分け）。 -/
theorem q9ix_index_le_three (u : q3rqCar) (hu : q3rqUnitMem u) :
    q9rcCongMod q3rqOne u ∨ q9rcCongMod q9rcFour u ∨ q9rcCongMod q9rcFourSq u := by
  obtain ⟨g, hg⟩ := q9ix_unit_decomp u hu
  cases g with
  | e => exact Or.inl hg
  | s => exact Or.inr (Or.inl hg)
  | s2 => exact Or.inr (Or.inr hg)

/-! ## q9ix-3: b2——q9qcGalHom の全射性 -/

/-- **q9ix-3a（★★ b2・全射性）**: ∀ y ∈ q9qcCoker（literal 商群）, ∃ g ∈ Gal,
    q9qcGalHom.map g = y。射影の全射性（quotientProjN_surjective）で代表 a を取り、
    b1 の g を q9qc_proj_eq_of_cong で商へ降ろす——Prop ∃ のみ・choice 無縁。 -/
theorem q9ix_gal_surjective (y : q9qcCoker.carrier) :
    ∃ g : q9kdGCar, q9qcGalHom.map g = y := by
  obtain ⟨a, ha⟩ := quotientProjN_surjective q3rqU q9qcNormSub q9qc_norm_normal y
  obtain ⟨g, hg⟩ := q9ix_unit_decomp a.val a.property
  refine ⟨g, ?_⟩
  rw [← ha]
  exact q9qc_proj_eq_of_cong ⟨q9rgPhi g, q9qcPhiUnit g⟩ a hg

/-! ## q9ix-4: b3——余核はちょうど 3 元（[U_{L₂}:N(U_M)] = 3） -/

/-- **q9ix-4a（b3・被覆 = 上界）**: 余核の全元は {[1], [4], [16]} =
    {map e, map s, map s2} のいずれか。 -/
theorem q9ix_coker_complete (y : q9qcCoker.carrier) :
    y = q9qcGalHom.map q9kdGCar.e ∨ y = q9qcGalHom.map q9kdGCar.s ∨
      y = q9qcGalHom.map q9kdGCar.s2 := by
  obtain ⟨g, hg⟩ := q9ix_gal_surjective y
  cases g with
  | e => exact Or.inl hg.symm
  | s => exact Or.inr (Or.inl hg.symm)
  | s2 => exact Or.inr (Or.inr hg.symm)

/-- **q9ix-4b（b3・相異 = 下界）**: {[1], [4], [16]} は商群 q9qcCoker で
    pairwise 相異（q9qc_gal_injective 経由・実体は q9rc の 4∉N・4²∉N）。 -/
theorem q9ix_coker_distinct :
    q9qcGalHom.map q9kdGCar.e ≠ q9qcGalHom.map q9kdGCar.s ∧
    q9qcGalHom.map q9kdGCar.e ≠ q9qcGalHom.map q9kdGCar.s2 ∧
    q9qcGalHom.map q9kdGCar.s ≠ q9qcGalHom.map q9kdGCar.s2 :=
  ⟨fun h => q9kdGCar.noConfusion (q9qc_gal_injective q9kdGCar.e q9kdGCar.s h),
   fun h => q9kdGCar.noConfusion (q9qc_gal_injective q9kdGCar.e q9kdGCar.s2 h),
   fun h => q9kdGCar.noConfusion (q9qc_gal_injective q9kdGCar.s q9kdGCar.s2 h)⟩

/-- **q9ix-4c（★★★ b3・INDEX = 3）: [U_{L₂} : N(U_M)] = 3**——literal 商群
    q9qcCoker = U_{L₂}/N(U_M) はちょうど {[1], [4], [16]} の 3 元:
    被覆（上界 ≤ 3・tame+wild 合成）∧ pairwise 相異（下界 ≥ 3・4∉N/4²∉N）。 -/
theorem q9ix_index_eq_three :
    (∀ y : q9qcCoker.carrier,
      y = q9qcGalHom.map q9kdGCar.e ∨ y = q9qcGalHom.map q9kdGCar.s ∨
        y = q9qcGalHom.map q9kdGCar.s2) ∧
    (q9qcGalHom.map q9kdGCar.e ≠ q9qcGalHom.map q9kdGCar.s ∧
     q9qcGalHom.map q9kdGCar.e ≠ q9qcGalHom.map q9kdGCar.s2 ∧
     q9qcGalHom.map q9kdGCar.s ≠ q9qcGalHom.map q9kdGCar.s2) :=
  ⟨q9ix_coker_complete, q9ix_coker_distinct⟩

/-- **q9ix-4d（b3・元レベル形）**: 単数の N-剰余は {[1],[4],[16]} を完全被覆し
    （上界）、三類は q9rcCongMod で pairwise 相異（下界・q9rc_z3_injects）。 -/
theorem q9ix_index_eq_three_elt :
    (∀ u : q3rqCar, q3rqUnitMem u →
      q9rcCongMod q3rqOne u ∨ q9rcCongMod q9rcFour u ∨ q9rcCongMod q9rcFourSq u) ∧
    (q9rcCongMod q3rqOne q9rcFourCube ∧
      (¬ q9rcCongMod q3rqOne q9rcFour) ∧
      (¬ q9rcCongMod q3rqOne q9rcFourSq) ∧
      (¬ q9rcCongMod q9rcFour q9rcFourSq)) :=
  ⟨q9ix_index_le_three, q9rc_z3_injects⟩

/-! ## q9ix-5: b4——★★★ HEADLINE: Gal(M/L₂) ≅ U_{L₂}/N(U_M) -/

/-- **q9ix-5a（★★★ b4・B2 相互律 HEADLINE）: Gal(M/L₂) ≅ U_{L₂}/N(U_M)**——
    q9qcGalHom : Hom q9kdG q9qcCoker は
    (1) 群準同型（Hom.map_mul）・(2) 単射（q9qc_gal_injective）・(3) 全射（q9ix-3a）。
    全単射 Hom = codebase の同型標準（QuotientGroup 正直限定 2・firstIsoHom が前例:
    firstIso_injective + firstIso_surjective の対）。q9qc の「Gal ↪ 余核」を
    「Gal ≅ 余核」へ昇格——**M/L₂ の局所相互律（単数部）の同型**。 -/
theorem q9ix_gal_iso :
    (∀ g h, q9qcGalHom.map (q9kdGMul g h)
        = q9qcCoker.mul (q9qcGalHom.map g) (q9qcGalHom.map h)) ∧
    (∀ g h, q9qcGalHom.map g = q9qcGalHom.map h → g = h) ∧
    (∀ y : q9qcCoker.carrier, ∃ g : q9kdGCar, q9qcGalHom.map g = y) :=
  ⟨q9qcGalHom.map_mul, q9qc_gal_injective, q9ix_gal_surjective⟩

/-! ## q9ix-6: capstone -/

/-- **q9ix-6a: T3-M4-b 完了データ**——分解定理・index = 3（商レベル・元レベル）・
    Gal ≅ 余核（全単射 Hom）を束ねる。 -/
structure Q3ReciprocityIndexRealData where
  /-- b1 前半: u·N(w)·φ(g) は厳密にノルム（tame × wild の合成点）。 -/
  sweep_is_norm : ∀ u : q3rqCar, q3rqUnitMem u →
    ∃ g : q9kdGCar, ∃ w : q3kCar, q3kUnitMem w ∧
      q9utIsNorm (q3rqMul (q3rqMul u (q3kNormBase w)) (q9rgPhi g))
  /-- b1: 分解定理 ∀u 単数, ∃g, φ(g) ≡ u (mod N)。 -/
  unit_decomp : ∀ u : q3rqCar, q3rqUnitMem u →
    ∃ g : q9kdGCar, q9rcCongMod (q9rgPhi g) u
  /-- b1': 元レベル index ≤ 3（[u] ∈ {[1],[4],[16]}）。 -/
  index_le_three : ∀ u : q3rqCar, q3rqUnitMem u →
    q9rcCongMod q3rqOne u ∨ q9rcCongMod q9rcFour u ∨ q9rcCongMod q9rcFourSq u
  /-- b2: q9qcGalHom は全射。 -/
  gal_surjective : ∀ y : q9qcCoker.carrier, ∃ g : q9kdGCar, q9qcGalHom.map g = y
  /-- 単射（q9qc から継承・iso の半分）。 -/
  gal_injective : ∀ g h, q9qcGalHom.map g = q9qcGalHom.map h → g = h
  /-- b3: 余核の完全被覆（上界）。 -/
  coker_complete : ∀ y : q9qcCoker.carrier,
    y = q9qcGalHom.map q9kdGCar.e ∨ y = q9qcGalHom.map q9kdGCar.s ∨
      y = q9qcGalHom.map q9kdGCar.s2
  /-- b3: 3 類 pairwise 相異（下界）——index = 3。 -/
  coker_distinct :
    q9qcGalHom.map q9kdGCar.e ≠ q9qcGalHom.map q9kdGCar.s ∧
    q9qcGalHom.map q9kdGCar.e ≠ q9qcGalHom.map q9kdGCar.s2 ∧
    q9qcGalHom.map q9kdGCar.s ≠ q9qcGalHom.map q9kdGCar.s2
  /-- 元レベル下界（q9rc_z3_injects 継承）。 -/
  transversal_distinct :
    q9rcCongMod q3rqOne q9rcFourCube ∧
      (¬ q9rcCongMod q3rqOne q9rcFour) ∧
      (¬ q9rcCongMod q3rqOne q9rcFourSq) ∧
      (¬ q9rcCongMod q9rcFour q9rcFourSq)

/-- **q9ix-6b: 見出し実例**——実 U_{L₂} = q3rqU・実 literal 商 q9qcCoker 上の
    index = 3 と Gal ≅ 余核。 -/
def q9ix_data : Q3ReciprocityIndexRealData where
  sweep_is_norm := q9ix_sweep_is_norm
  unit_decomp := q9ix_unit_decomp
  index_le_three := q9ix_index_le_three
  gal_surjective := q9ix_gal_surjective
  gal_injective := q9qc_gal_injective
  coker_complete := q9ix_coker_complete
  coker_distinct := q9ix_coker_distinct
  transversal_distinct := q9rc_z3_injects

/-- **q9ix-6c: T3-M4-b 完了の存在**（B2 相互律 headline——[U_{L₂}:N(U_M)] = 3・
    Gal(M/L₂) ≅ U_{L₂}/N(U_M)・単数部）。 -/
theorem q9ix_exists : Nonempty Q3ReciprocityIndexRealData := ⟨q9ix_data⟩

end IUT
