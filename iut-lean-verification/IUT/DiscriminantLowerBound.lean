/-
  IUT/DiscriminantLowerBound.lean — M401F [実・本物・柱C]
-- M401F DiscriminantLowerBound [実・本物・柱C]
-- complete_pct 影響: 柱C で 分岐する数体は |disc(K/ℚ)| > 1 を本物化（Minkowski 風・
--   「分岐は必然」の算術核）：M396F の |disc| = ∏_v p_v^{f_v·d_v} を再利用し、
--   分岐素点（p_v≥2・f_v≥1・d_v≥1）が一つでも在れば積が 1 を超えることを ℕ 算術
--   （Nat.one_lt_pow / Nat.one_lt_mul_iff）で証明。さらに指数リストの特徴付け
--   |disc| = 1 ⟺ すべての d_v = 0（不分岐）を両向き証明。M386F ℚ(ζ_{p^k})
--   （p≥2・cppDifferentExp≥1 ⇒ |disc|=p^{p^{k-1}(k(p−1)−1)}>1）・具体 ℚ(ζ_9)=3^9=19683・
--   ℚ(ζ_5)=5^3=125・二次体 ℚ(√5)=5・ℚ(i)=4 へ特化して「非自明な円分体/二次体は必ず
--   分岐し |disc|>1」を本物に検算（M396F/M386F/M381F/M371F の再利用）。
-- 正直な限定: これは「分岐 ⇒ |disc|>1」の部分ケースであり、完全な Minkowski 幾何下界
--   |disc| ≥ (π/4)^{r_2}·n^n/n!（数の幾何・Minkowski 束・格子体積・archimedean 埋め込み）
--   は後続。数体は M396F と同じく「分岐素点データ (p_v,f_v,d_v) の有限リスト」で模型化する
--   （実 O_K の整基底・判別式行列・different イデアル構成・幾何下界は未実装）。
-/
import IUT.RingOfIntegersDiscriminant

namespace IUT

/-! ## M401F-1: 素点の適格性と分岐（well-formed / ramified）

    実の有理素数は p_v ≥ 2、剰余次数は f_v ≥ 1。分岐素点は加えて局所 different 指数
    d_v ≥ 1（不分岐なら d_v = 0）。判別式は分岐素点上にのみ台を持つ（M396F-3）。 -/

/-- **M401F-1a: 素点の適格性** — 有理素数 p_v ≥ 2 かつ剰余次数 f_v ≥ 1。実数体の素点データ
    が満たす最小条件（p は本物の有理素数、f は正の剰余次数）。 -/
def dlbWellFormed (v : ridPlace) : Prop := 2 ≤ v.p ∧ 1 ≤ v.f

/-- **M401F-1b: リスト全体の適格性** — 全素点が適格。 -/
def dlbAllWF : List ridPlace → Prop
  | [] => True
  | v :: vs => dlbWellFormed v ∧ dlbAllWF vs

/-- **M401F-1c: 分岐素点の存在** — d_v ≥ 1 の素点がリスト中に少なくとも一つ在る
    （K が或る素数で分岐する）。 -/
def dlbHasRam : List ridPlace → Prop
  | [] => False
  | v :: vs => 1 ≤ v.d ∨ dlbHasRam vs

/-- **M401F-1d: すべて不分岐** — 全素点で d_v = 0（K は至る所不分岐）。 -/
def dlbAllUnram : List ridPlace → Prop
  | [] => True
  | v :: vs => v.d = 0 ∧ dlbAllUnram vs

/-! ## M401F-2: 局所因子の正値性・1 超え（分岐局所寄与 > 1） -/

/-- **M401F-2a: 局所判別式寄与は正（本物）** — p_v ≥ 1 ⇒ p_v^{f_v·d_v} ≥ 1。 -/
theorem dlb_localDisc_pos (v : ridPlace) (hp : 1 ≤ v.p) : 0 < ridLocalDisc v :=
  Nat.pow_pos hp

/-- **M401F-2b: 分岐局所寄与は 1 を超える（本物・下界の核）** — p_v ≥ 2・f_v ≥ 1・d_v ≥ 1
    ⇒ p_v^{f_v·d_v} > 1（指数 f_v·d_v ≥ 1 かつ底 p_v ≥ 2）。分岐素点の局所判別式は自明でない。 -/
theorem dlb_localDisc_gt_one (v : ridPlace)
    (hp : 2 ≤ v.p) (hf : 1 ≤ v.f) (hd : 1 ≤ v.d) : 1 < ridLocalDisc v := by
  show 1 < v.p ^ (v.f * v.d)
  refine Nat.one_lt_pow ?_ hp
  -- f_v·d_v ≠ 0：f_v ≥ 1 かつ d_v ≥ 1
  intro hfd
  cases Nat.mul_eq_zero.mp hfd with
  | inl h => omega
  | inr h => omega

/-! ## M401F-3: 判別式の大きさは正・分岐なら 1 を超える -/

/-- **M401F-3a: 判別式の大きさは正（本物）** — 全素点適格（p_v ≥ 2 ⇒ p_v ≥ 1）ゆえ各局所因子
    ≥ 1、積 ∏_v p_v^{f_v·d_v} ≥ 1。 -/
theorem dlb_discMag_pos (places : List ridPlace) (hwf : dlbAllWF places) :
    0 < ridDiscMag places := by
  induction places with
  | nil => exact Nat.one_pos
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := hwf
    obtain ⟨hp, _⟩ := hv
    show 0 < ridLocalDisc v * ridDiscMag vs
    have h1 : 0 < ridLocalDisc v := dlb_localDisc_pos v (by omega)
    have h2 : 0 < ridDiscMag vs := ih hvs
    exact Nat.mul_pos h1 h2

/-- **M401F-3b: 分岐する数体は |disc| > 1（本物・柱C の主成果・Minkowski 風）** —
    適格な分岐素点データが一つでも d_v ≥ 1 を含めば |disc| = ∏_v p_v^{f_v·d_v} > 1。
    リスト帰納：分岐素点が先頭なら局所因子 > 1・残り ≥ 1（M401F-2b, 3a）、
    分岐素点が末尾なら局所因子 ≥ 1・残り > 1（帰納法）。いずれも `Nat.one_lt_mul_iff`
    で積 > 1。「ℚ の不分岐拡大は存在しない」（|disc|=1 ⇒ K=ℚ）の算術核の部分ケース。 -/
theorem dlb_disc_gt_one (places : List ridPlace)
    (hwf : dlbAllWF places) (hram : dlbHasRam places) : 1 < ridDiscMag places := by
  induction places with
  | nil => exact absurd hram (by intro h; exact h)
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := hwf
    obtain ⟨hp, hf⟩ := hv
    have hp1 : 1 ≤ v.p := by omega
    show 1 < ridLocalDisc v * ridDiscMag vs
    cases hram with
    | inl hd =>
      -- 先頭が分岐：局所因子 > 1、残りは > 0
      have hlt : 1 < ridLocalDisc v := dlb_localDisc_gt_one v hp hf hd
      have hpos : 0 < ridDiscMag vs := dlb_discMag_pos vs hvs
      refine Nat.one_lt_mul_iff.mpr ⟨?_, hpos, Or.inl hlt⟩
      exact Nat.lt_trans Nat.one_pos hlt
    | inr hrest =>
      -- 末尾に分岐：残りが > 1、局所因子は > 0
      have hlt : 1 < ridDiscMag vs := ih hvs hrest
      have hpos : 0 < ridLocalDisc v := dlb_localDisc_pos v hp1
      refine Nat.one_lt_mul_iff.mpr ⟨hpos, ?_, Or.inr hlt⟩
      exact Nat.lt_trans Nat.one_pos hlt

/-! ## M401F-4: 指数リストの特徴付け（|disc| = 1 ⟺ 全 d_v = 0） -/

/-- **M401F-4a: 不分岐 ⇒ |disc| = 1（本物）** — 全 d_v = 0 ⇒ 各局所因子 p_v^{f_v·0} = 1、
    積 = 1。判別式は分岐素点上にのみ台を持つ（M396F-3 の全域版）。 -/
theorem dlb_disc_eq_one_of_unram (places : List ridPlace)
    (h : dlbAllUnram places) : ridDiscMag places = 1 := by
  induction places with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨hd, hrest⟩ := h
    show ridLocalDisc v * ridDiscMag vs = 1
    rw [rid_local_disc_unramified v hd, ih hrest, Nat.one_mul]

/-- **M401F-4b: |disc| = 1 ⇒ 不分岐（本物・逆向き）** — 適格リストで ∏_v p_v^{f_v·d_v} = 1
    なら各因子 = 1（Nat：積 1 ⇒ 各因子 1）、p_v ≥ 2 ゆえ p_v^{f_v·d_v} = 1 は指数 f_v·d_v = 0
    を強制（`Nat.pow_eq_one`）、f_v ≥ 1 ゆえ d_v = 0。全素点で不分岐。 -/
theorem dlb_unram_of_disc_eq_one (places : List ridPlace)
    (hwf : dlbAllWF places) (h : ridDiscMag places = 1) : dlbAllUnram places := by
  induction places with
  | nil => exact True.intro
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := hwf
    obtain ⟨hp, hf⟩ := hv
    have hcons : ridLocalDisc v * ridDiscMag vs = 1 := h
    have hloc : ridLocalDisc v = 1 := Nat.eq_one_of_mul_eq_one_right hcons
    have hrest : ridDiscMag vs = 1 := Nat.eq_one_of_mul_eq_one_left hcons
    -- p_v^{f_v·d_v} = 1 かつ p_v ≥ 2 ⇒ f_v·d_v = 0
    have hpow : v.p ^ (v.f * v.d) = 1 := hloc
    have hexp : v.f * v.d = 0 := by
      cases Nat.pow_eq_one.mp hpow with
      | inl hp1 => omega
      | inr hn => exact hn
    have hd : v.d = 0 := by
      cases Nat.mul_eq_zero.mp hexp with
      | inl hf0 => omega
      | inr hd0 => exact hd0
    exact ⟨hd, ih hvs hrest⟩

/-- **M401F-4c: 特徴付け |disc| = 1 ⟺ 全 d_v = 0（本物・両向き）** — 適格な数体の判別式が
    1 になるのは全素点で不分岐なとき、かつそのときに限る。Minkowski「|disc|=1 ⇒ K=ℚ」の
    算術的中核（この模型では「不分岐 ⟺ disc=1」）。 -/
theorem dlb_disc_eq_one_iff (places : List ridPlace) (hwf : dlbAllWF places) :
    ridDiscMag places = 1 ↔ dlbAllUnram places :=
  ⟨dlb_unram_of_disc_eq_one places hwf, dlb_disc_eq_one_of_unram places⟩

/-- **M401F-4d: 分岐 ⇒ ¬全不分岐（本物・橋渡し）** — d_v ≥ 1 の素点が在れば全素点 d_v = 0
    ではない。 -/
theorem dlb_hasRam_not_allUnram (places : List ridPlace)
    (hram : dlbHasRam places) : ¬ dlbAllUnram places := by
  induction places with
  | nil => exact absurd hram (by intro h; exact h)
  | cons v vs ih =>
    intro hall
    obtain ⟨hd, hrest⟩ := hall
    cases hram with
    | inl hge => omega
    | inr hr => exact ih hr hrest

/-! ## M401F-5: M386F ℚ(ζ_{p^k}) への特化（分岐 ⇒ |disc| > 1・整合性チェック） -/

/-- **M401F-5a: ℚ(ζ_{p^k}) の分岐素点データは適格（本物）** — 唯一の分岐素点 (p,1,d)、
    p ≥ 2 かつ f = cppResidueDeg = 1 ≥ 1。 -/
theorem dlb_cpp_wf (p k : Nat) (hp : 2 ≤ p) : dlbAllWF (ridCycloPPPlaces p k) :=
  ⟨⟨hp, Nat.le_refl 1⟩, True.intro⟩

/-- **M401F-5b: 分岐する ℚ(ζ_{p^k}) は |disc| > 1（本物・M386F 特化）** —
    p ≥ 2 かつ cppDifferentExp p k ≥ 1（p≥3 または k≥2 で成立）なら
    |disc| = p^{p^{k-1}(k(p−1)−1)} > 1。M396F-5 の disc=norm 公式と M386F 野生分岐指数を再利用。 -/
theorem dlb_cpp_gt_one (p k : Nat) (hp : 2 ≤ p) (hd : 1 ≤ cppDifferentExp p k) :
    1 < ridDiscMag (ridCycloPPPlaces p k) :=
  dlb_disc_gt_one (ridCycloPPPlaces p k) (dlb_cpp_wf p k hp) (Or.inl hd)

/-- **M401F-5c: cppDiscMag 経由の |disc| > 1（本物・M386F 直結）** — 指数 cppDiscExp p k ≠ 0
    かつ p ≥ 2 なら cppDiscMag p k = p^{cppDiscExp} > 1。M396F-5c `rid_specialize_cpp` を再利用。 -/
theorem dlb_cpp_discMag_gt_one (p k : Nat) (hp : 2 ≤ p) (he : cppDiscExp p k ≠ 0) :
    1 < ridDiscMag (ridCycloPPPlaces p k) := by
  rw [rid_specialize_cpp p k]
  show 1 < p ^ cppDiscExp p k
  exact Nat.one_lt_pow he hp

/-- **M401F-5d: ℚ(ζ_9)=ℚ(ζ_{3^2}) は分岐し |disc| = 3^9 = 19683 > 1（本物・M386F 具体）** —
    唯一の分岐素点 3・f=1・d=9、|disc| = 19683 > 1。非自明円分体の分岐必然性の実例。 -/
theorem dlb_zeta9_gt_one : 1 < ridDiscMag (ridCycloPPPlaces 3 2) := by
  rw [rid_example_zeta9]
  omega

/-! ## M401F-6: M381F ℚ(ζ_p)・M371F 二次体への特化 -/

/-- **M401F-6a: ℚ(ζ_p)（p≥3）は分岐し |disc| = p^{p−2} > 1（本物・M381F 特化）** —
    唯一の分岐素点 p・f=1・d=p−2 ≥ 1（p≥3）、|disc| = p^{p−2} > 1。 -/
theorem dlb_cyd_gt_one (p : Nat) (hp : 3 ≤ p) : 1 < ridDiscMag (ridCycloPrimePlaces p) := by
  refine dlb_disc_gt_one (ridCycloPrimePlaces p) ⟨⟨?_, ?_⟩, True.intro⟩ (Or.inl ?_)
  · show 2 ≤ p; omega
  · show 1 ≤ (1 : Nat); omega
  · -- cdfDifferentExp p = p - 2 ≥ 1（p ≥ 3）
    show 1 ≤ p - 2; omega

/-- **M401F-6b: ℚ(ζ_5) は分岐し |disc| = 5^3 = 125 > 1（本物・M381F 具体）** — 分岐素数 5 のみ・
    d=3、|disc| = 125 > 1。 -/
theorem dlb_zeta5_gt_one : 1 < ridDiscMag (ridCycloPrimePlaces 5) := by
  rw [rid_example_zeta5]
  omega

/-- **M401F-6c: 二次体 ℚ(√5) は分岐し |disc| = 5 > 1（本物・M371F reuse）** — 分岐素点 [(5,1,1)]、
    ∏ = 5 > 1。非自明二次体の分岐必然性の実例。 -/
theorem dlb_quad_sqrt5_gt_one : 1 < ridDiscMag [(⟨5, 1, 1⟩ : ridPlace)] := by
  refine dlb_disc_gt_one [⟨5, 1, 1⟩] ⟨⟨?_, ?_⟩, True.intro⟩ (Or.inl ?_)
  · show 2 ≤ 5; omega
  · show 1 ≤ (1 : Nat); omega
  · show 1 ≤ (1 : Nat); omega

/-- **M401F-6d: ℚ(i)=ℚ(√−1) は分岐し |disc| = 4 > 1（本物・M371F reuse）** — 分岐素点 [(2,1,2)]、
    ∏ = 2^2 = 4 > 1（2 は野生分岐 d=2）。 -/
theorem dlb_quad_gauss_gt_one : 1 < ridDiscMag [(⟨2, 1, 2⟩ : ridPlace)] := by
  refine dlb_disc_gt_one [⟨2, 1, 2⟩] ⟨⟨?_, ?_⟩, True.intro⟩ (Or.inl ?_)
  · show 2 ≤ 2; omega
  · show 1 ≤ (1 : Nat); omega
  · show 1 ≤ (2 : Nat); omega

/-! ## M401F-7: capstone — 分岐する数体は |disc| > 1（下界データ） -/

/-- **M401F-7a: capstone データ** — 適格な分岐素点データ（少なくとも一つ d_v ≥ 1）を持つ
    数体 K/ℚ について、判別式の大きさ |disc| = ∏_v p_v^{f_v·d_v} と、それが 1 を超えること
    （分岐 ⇒ |disc|>1、Minkowski 風下界の部分ケース）を束ねる（全フィールド本物）。 -/
structure DiscriminantLowerBoundData where
  /-- 分岐素点データのリスト（各 (p_v, f_v, d_v)）。 -/
  places : List ridPlace
  /-- 全素点適格（p_v ≥ 2・f_v ≥ 1）。 -/
  wf : dlbAllWF places
  /-- 少なくとも一つの分岐素点（d_v ≥ 1）が存在。 -/
  ram : dlbHasRam places
  /-- 判別式の大きさ |disc(K/ℚ)|。 -/
  discMag : Nat
  /-- |disc| = ∏_v p_v^{f_v·d_v}（本物・M396F 再利用）。 -/
  disc_eq : discMag = ridDiscMag places
  /-- |disc| > 1（本物・分岐必然性）。 -/
  disc_gt_one : 1 < discMag

/-- **M401F-7b: 実データ**（適格な分岐素点リストから下界データを構成）。 -/
def dlbData (places : List ridPlace)
    (hwf : dlbAllWF places) (hram : dlbHasRam places) : DiscriminantLowerBoundData where
  places := places
  wf := hwf
  ram := hram
  discMag := ridDiscMag places
  disc_eq := rfl
  disc_gt_one := dlb_disc_gt_one places hwf hram

/-- **M401F-7c: capstone — 存在**（適格な分岐素点データを持つ数体の下界データは充足可能）。 -/
theorem dlb_exists (places : List ridPlace)
    (hwf : dlbAllWF places) (hram : dlbHasRam places) :
    Nonempty DiscriminantLowerBoundData :=
  ⟨dlbData places hwf hram⟩

/-- **M401F-7d: capstone の |disc| > 1（本物・下界の再確認）** — 任意の適格分岐データで成立。 -/
theorem dlb_data_gt_one (places : List ridPlace)
    (hwf : dlbAllWF places) (hram : dlbHasRam places) :
    1 < (dlbData places hwf hram).discMag :=
  dlb_disc_gt_one places hwf hram

/-- **M401F-7e0: ℚ(ζ_9) の分岐（本物）** — 唯一の分岐素点 3 は d = cppDifferentExp 3 2 = 9 ≥ 1。 -/
theorem dlb_zeta9_ram : dlbHasRam (ridCycloPPPlaces 3 2) :=
  Or.inl (by show (1 : Nat) ≤ cppDifferentExp 3 2; exact (by omega : (1 : Nat) ≤ 9))

/-- **M401F-7e: worked example ℚ(ζ_9) 下界データ（本物・M386F）** — 分岐素点 [(3,1,9)]・
    |disc| = 19683 > 1。 -/
theorem dlb_example_zeta9_data :
    (dlbData (ridCycloPPPlaces 3 2) (dlb_cpp_wf 3 2 (by omega)) dlb_zeta9_ram).discMag = 19683
    ∧ 1 < (dlbData (ridCycloPPPlaces 3 2) (dlb_cpp_wf 3 2 (by omega)) dlb_zeta9_ram).discMag :=
  ⟨rid_example_zeta9, dlb_zeta9_gt_one⟩

/-- **M401F-7f: 具体 capstone まとめ（本物）** — 非自明な円分体/二次体は必ず分岐し |disc| > 1：
    ℚ(ζ_9)（3^9=19683・M386F）・ℚ(ζ_5)（5^3=125・M381F）・ℚ(√5)（5・M371F）・
    ℚ(i)（4・M371F）を一括で示し、「分岐は必然（|disc|>1）」が M386F/M381F/M371F の各クラスで
    整合することを実証する。 -/
theorem dlb_examples :
    1 < ridDiscMag (ridCycloPPPlaces 3 2) ∧
    1 < ridDiscMag (ridCycloPrimePlaces 5) ∧
    1 < ridDiscMag [(⟨5, 1, 1⟩ : ridPlace)] ∧
    1 < ridDiscMag [(⟨2, 1, 2⟩ : ridPlace)] :=
  ⟨dlb_zeta9_gt_one, dlb_zeta5_gt_one, dlb_quad_sqrt5_gt_one, dlb_quad_gauss_gt_one⟩

end IUT
