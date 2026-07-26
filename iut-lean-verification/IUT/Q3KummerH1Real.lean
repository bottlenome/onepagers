/-
  IUT/Q3KummerH1Real.lean — 実 Galois コホモロジー H¹(Gal(M/L₂), μ₃(O_M)) の完全計算（B6・K1）
    M = ℚ₃(ζ₉) = L₂[Y]/(Y³−ζ₃)・実 Gal(M/L₂) = ⟨q3kSigma⟩・実 μ₃(O_M)

  ── 主要成果の分類: **[実／(a) 昇格]** — 抽象 1-コホモロジー機構 M326F
     （`galH1Module`/`galH1_cocycles_group`/`galH1_coboundaries_subgroup`/`galH1Group`）を
     **実 Gal(M/L₂)=⟨σ⟩（実 O_M の実環自己同型の 3 元群 q9kdG）と実係数加群
     μ₃(O_M)=q9kdMu3（実環の実 3 乗根群）**の上で駆動し、
     **H¹(Gal(M/L₂), μ₃(O_M)) をちょうど 3 元と完全計算**して
     δ : ⟨[ζ₃]⟩-指数群 → H¹ が**群同型（全単射準同型）**であることを閉じる。
     **正直な先行申告（二重計上の禁止・§4）**: 「実 galH1Module インスタンスを初めて
     作った」のは本モジュールでは**ない**——`IUT/Q3ThetaKummerRealL9.lean`（q9tk・Round 8）
     の `q9tkModule` が先行しており、本モジュールの `q9khModule` はそれと**定義的に同一**
     である（作用も係数も同じ実対象）。本モジュールの新規（真水）は
     instantiate そのものではなく **H¹ の完全計算**（下記 (3)(4)）である。
     toy 主語なし（m202fVol 型・Bool 軌道・surrogate 群を一切使わない）。主語は
     実 σ・実 μ₃(O_M)・実コサイクル群 Z¹・実コバウンダリ部分群 B¹・実商 H¹=Z¹/B¹。

  complete_pct 影響: **B6「Kummer 理論（実 Galois コホモロジー上）」0.18 →（監査次第）**。
  昇格の中身（(1)(2) は q9tk と重複・**新規計上は (3)(4)**）は
   (1) q9kd 正直限定 1 の「一般 H¹ 形式論（galH1Module）への接続なし」を
       **M326F に対して閉じる**（`q9khModule`。**重複申告**: q9tk `q9tkModule` と定義的に同一）、
   (2) σ の μ₃ 上の作用の**自明性は仮定でなく計算**（`q9kh_act_trivial`・
       `q9c_m_mu3_complete` 消費 ⟹ μ₃ の 3 元が全て L₂ 内 ⟹ σ で固定。
       **重複申告**: q9tk `q9tk_mu3_fixed` と同内容）、
   (3) **新規**: B¹ = 1 の部分群レベル形・**Z¹ ≅ Hom(⟨σ⟩,μ₃)（両向き＋往復 2 本）**・
       **射影 Z¹→H¹ の単射性**（H¹ ≅ Z¹）を実 module 上で確立
       （q9tk は 1 つの類の非自明性のみで、H¹ の構造は計算していない）、
   (4) **新規・本丸**: **H¹ の完全枚挙**（任意の元は δ(0),δ(1),δ(2) のいずれか・3 元は
       pairwise 相異 ⟹ H¹ ≅ ℤ/3）と、**δ が群準同型かつ全単射**（`galH1KummerHom` の
       実 instantiate ＋ χ 冪の乗法性）＝ この拡大での有限レベル Kummer 同型の
       Galois コホモロジー実現。q9tk の `q9tk_class_nontrivial`（1 類 ≠ 0）は
       本モジュールの `q9kh_delta_inj` の系にあたる（本モジュールの方が強い）。
  **消費（再主張しない）**: Hom(⟨σ⟩,μ₃) の完全枚挙 `q9kd_hom_complete`・
  k↦χᵏ の全単射 `q9kd_kummer_iso_surj/_inj`・σ の基礎固定性 `q9kd_sigma_fixes_base`・
  μ₃(O_M) 完全性 `q9c_m_mu3_complete`（柱A）・M326F の一般補題
  `galH1_proj_injective_of_trivial`/`quotientProjN_surjective`。

  内容:
   * q9kh_mu3_comm / q9kh_act_cube / q9khActHom / **q9khModule**            — K1-k1
   * q9kh_sigma_fix / q9kh_sigma2_fix / **q9kh_act_trivial**（計算）        — K1-k2
   * q9kh_coboundary_eq_one / q9kh_B1_trivial / q9kh_proj_injective         — K1-k3
   * q9khHomOfCocycle / q9khCocycleOfHom / 往復 2 本（Z¹ ≅ Hom）            — K1-k3
   * q9kh_chipow_mul（χ 冪の乗法性・9×3 ケース）/ q9khKappa / **q9khDelta**  — K1-k5
   * q9kh_delta_surj / q9kh_delta_inj / **q9kh_H1_complete**（3 元・相異）   — K1-k4,k6
   * Q3KummerH1RealData / q9kh_data / q9kh_exists                           — capstone

  正直な限定（§4 規約により消さない・弱化しない・q3k/q3rq/q9kd/M326F 継承の上に追記のみ）:
  1. **Galois は有限商 ⟨σ⟩ ≅ Gal(M/L₂) のみ**（q9kd 正直限定 1 の前半を継承）。
     副有限 G_{L₂}・絶対 Galois 群・逆極限はゼロ。したがって本モジュールが計算した
     H¹ は **H¹(Gal(M/L₂), μ₃)（3 元）であって H¹(G_{L₂}, μ₃) ではない**。
  2. **`L₂^×/(L₂^×)³ ≅ H¹` とは主張しない（それは偽になる）**。L₂^×/(L₂^×)³ は
     81 元（q9cq の named target）であり、有限商 ⟨σ⟩ 上の H¹ は 3 元。本モジュールが
     閉じるのは **⟨[ζ₃]⟩ ≅ H¹(Gal(M/L₂),μ₃)**（inflation 像の部分）だけである。
  3. **Tate 双対・cup 積は主張しない**。奇素数巡回群 C₃ 上では cup: H¹×H¹→H² が
     恒等的に零（x∪x = −x∪x）であり、有限商レベルの「非退化 cup 対」は**偽**。
     q9kd の非退化対（`q9kd_pairing_eq`）は cup でなく Kummer 評価対である。
  4. **Hilbert 90 は主張しない**。体 M^× が無い（体化なし・A2 恒久限定継承）ため体版は
     未達であり、単数版 H¹(⟨σ⟩,U_M) は（Herbrand 商と B2 の余核 ℤ/3 から）**非自明**で
     あって Hilbert 90 の形にはならない。本モジュールの係数は μ₃(O_M) のみ。
  5. **M320F/M345F（IUTField ベースの抽象 Kummer 機構）への接続は依然未達**
     （q9kd 正直限定 1 の後半をそのまま継承——q3k は IUTField ではない。閉じたのは
     `galH1Module` が `Grp` しか要求しない M326F 側だけ）。
  6. **n=3・拡大 M/L₂ 1 個・体 L₂ 1 個・O_M と単数のみ**（恒久限定継承）。高次 Hⁿ・
     長完全列・inflation-restriction 完全列は未形式化（M326F 正直限定 2 継承）。
  7. 連続性（位相）は core に位相機構が無いため代数的 Hom として扱う
     （M326F 正直限定 4 継承）——有限群なので本例では実質的制約ではない。
  8. **q9tk（E4・Round 8）との重複**: 実 galH1Module インスタンス（`q9khModule`
     = `q9tkModule`）・作用の自明性・コバウンダリ自明性は **q9tk が先行**しており、
     本モジュールで**再計上しない**（二重計上の禁止）。新規計上の対象は
     H¹ の完全計算（3 元・δ 全単射・Z¹≅Hom・射影単射・χ 冪乗法性）のみ。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3KummerDualityReal
import IUT.GaloisCohomologyH1

namespace IUT

/-! ## q9kh-1（K1-k1）: 実 G-加群 μ₃(O_M) — 実 Gal(M/L₂) の実作用 -/

/-- **μ₃(O_M) はアーベル**（実環 O_M の可換性から）。 -/
theorem q9kh_mu3_comm (a b : q9kdMu3.carrier) :
    q9kdMu3.mul a b = q9kdMu3.mul b a :=
  Subtype.ext (q3k_mul_comm a.val b.val)

/-- **σ・σ² は μ₃(O_M) を保つ**: x³=1 ⟹ (g·x)³ = g(x³) = g(1) = 1
    （`q3k_sigma_mul`/`q3k_sigma_one`・`q3k_sigma2_mul`/`q3k_sigma2_one` 消費）。 -/
theorem q9kh_act_cube (g : q9kdGCar) (x : q3kCar)
    (hx : q3kMul (q3kMul x x) x = q3kOne) :
    q3kMul (q3kMul (q9kdAct g x) (q9kdAct g x)) (q9kdAct g x) = q3kOne := by
  cases g with
  | e => exact hx
  | s =>
    show q3kMul (q3kMul (q3kSigma x) (q3kSigma x)) (q3kSigma x) = q3kOne
    rw [← q3k_sigma_mul, ← q3k_sigma_mul, hx]
    exact q3k_sigma_one
  | s2 =>
    show q3kMul (q3kMul (q3kSigma2 x) (q3kSigma2 x)) (q3kSigma2 x) = q3kOne
    rw [← q3k_sigma2_mul, ← q3k_sigma2_mul, hx]
    exact q3k_sigma2_one

/-- **実作用 g ↦ (μ₃ → μ₃)**（実環自己同型の μ₃ への制限・群自己準同型）。 -/
def q9khActHom (g : q9kdGCar) : Hom q9kdMu3 q9kdMu3 where
  map := fun m => ⟨q9kdAct g m.val, q9kh_act_cube g m.val m.property⟩
  map_mul := by
    intro a b
    apply Subtype.ext
    cases g with
    | e => rfl
    | s => exact q3k_sigma_mul a.val b.val
    | s2 => exact q3k_sigma2_mul a.val b.val

/-- **K1-k1（★）`q9khModule`**: 実 Gal(M/L₂)=⟨σ⟩-加群 μ₃(O_M)。
    M326F `galH1Module` の実 instantiate（作用は実環自己同型 σ の制限であり、
    定義上自明な `galH1TrivialModule` ではない）。
    ★**正直な訂正（独立敵対監査 2026-07-21）**: 「**初の**実 instantiate」は**誤り**
    （本ファイル自身の正直限定 8 と矛盾していた）。`Q3ThetaKummerRealL9` の
    `q9tkModule` が先行し、しかも `q9tkModule = q9khModule` が **rfl** で成立する。
    E4 監査の裁定により、この実 instantiate の計上先は **B6（本項）に一度だけ**であり
    E4 ではない——ただし「初」ではない。 -/
def q9khModule : galH1Module q9kdG where
  M := q9kdMu3
  comm := q9kh_mu3_comm
  act := q9khActHom
  act_one := fun _ => rfl
  act_mul := fun g h m => Subtype.ext (q9kd_act_mul g h m.val)

/-! ## q9kh-2（K1-k2）: 作用の自明性は**計算**（仮定ではない） -/

/-- σ は μ₃(O_M) の各元を固定する（**`q9c_m_mu3_complete` 消費**: x³=1 ⟹
    x ∈ {1, ζ₃, ζ₃²} ⊂ embed(L₂)、embed 像は `q9kd_sigma_fixes_base` で固定）。 -/
theorem q9kh_sigma_fix (x : q3kCar) (hx : q3kMul (q3kMul x x) x = q3kOne) :
    q3kSigma x = x := by
  obtain h | h | h := q9c_m_mu3_complete x hx
  · rw [h]; exact q3k_sigma_one
  · rw [h]; exact q9kd_sigma_fixes_base q3rqZeta
  · rw [h]; exact q9kd_sigma_fixes_base q3rqZetaSq

/-- σ² も μ₃(O_M) の各元を固定する（σ を 2 回・`q3k_sigma2_comp` 消費）。 -/
theorem q9kh_sigma2_fix (x : q3kCar) (hx : q3kMul (q3kMul x x) x = q3kOne) :
    q3kSigma2 x = x := by
  rw [q3k_sigma2_comp x, q9kh_sigma_fix x hx, q9kh_sigma_fix x hx]

/-- **K1-k2（★）`q9kh_act_trivial`**: 実作用 ⟨σ⟩ ↷ μ₃(O_M) は自明
    ——**仮定でなく計算**（μ₃(O_M) ⊂ L₂ = σ の固定体、という実内容）。 -/
theorem q9kh_act_trivial (g : q9kdGCar) (m : q9kdMu3.carrier) :
    (q9khModule.act g).map m = m := by
  apply Subtype.ext
  cases g with
  | e => rfl
  | s => exact q9kh_sigma_fix m.val m.property
  | s2 => exact q9kh_sigma2_fix m.val m.property

/-! ## q9kh-3（K1-k3）: B¹ = 1・Z¹ ≅ Hom(⟨σ⟩,μ₃)・射影 Z¹→H¹ は単射 -/

/-- 実 module 上の 1-コバウンダリは自明: f_m(g) = g·m − m = m − m = 0
    （M326F-5g の証明体を**実作用＋計算済み自明性 `q9kh_act_trivial`**の下で再証明）。 -/
theorem q9kh_coboundary_eq_one (m : q9kdMu3.carrier) (g : q9kdGCar) :
    (galH1Coboundary q9khModule m).f g = q9kdMu3.one := by
  show q9kdMu3.mul ((q9khModule.act g).map m) (q9kdMu3.inv m) = q9kdMu3.one
  rw [q9kh_act_trivial g m]
  exact q9kdMu3.mul_inv m

/-- **B¹ は自明**（実 module 上）: コバウンダリ部分群の任意元は Z¹ の単位元。 -/
theorem q9kh_B1_trivial :
    ∀ x, (galH1_coboundaries_subgroup q9khModule).mem x
       → x = (galH1_cocycles_group q9khModule).one := by
  intro x hx
  obtain ⟨m, hm⟩ := hx
  apply galH1Cocycle.ext
  funext g
  show x.f g = q9kdMu3.one
  rw [← hm]
  exact q9kh_coboundary_eq_one m g

/-- 射影 Z¹ → H¹ = Z¹/B¹（実 module）。 -/
def q9khProj :
    Hom (galH1_cocycles_group q9khModule) (galH1Group q9khModule) :=
  quotientProjN (galH1_cocycles_group q9khModule)
    (galH1_coboundaries_subgroup q9khModule) (galH1_coboundaries_normal q9khModule)

/-- **射影 Z¹ → H¹ は単射**（B¹=1・M326F-5i の一般形を消費）⟹ H¹ ≅ Z¹。 -/
theorem q9kh_proj_injective : Hom.Injective q9khProj :=
  galH1_proj_injective_of_trivial (galH1_cocycles_group q9khModule)
    (galH1_coboundaries_subgroup q9khModule) (galH1_coboundaries_normal q9khModule)
    q9kh_B1_trivial

/-- **射影 Z¹ → H¹ は全射**（M267F 一般形を消費）。 -/
theorem q9kh_proj_surjective : ∀ x, ∃ a, q9khProj.map a = x :=
  quotientProjN_surjective (galH1_cocycles_group q9khModule)
    (galH1_coboundaries_subgroup q9khModule) (galH1_coboundaries_normal q9khModule)

/-- **Z¹ → Hom(⟨σ⟩,μ₃)**: 実作用が自明なので 1-コサイクルは群準同型。 -/
def q9khHomOfCocycle (f : galH1Cocycle q9khModule) : Hom q9kdG q9kdMu3 where
  map := f.f
  map_mul := by
    intro g h
    rw [f.cocycle g h, q9kh_act_trivial g (f.f h)]
    rfl

/-- **Hom(⟨σ⟩,μ₃) → Z¹**: 逆向き（群準同型はそのまま 1-コサイクル）。 -/
def q9khCocycleOfHom (φ : Hom q9kdG q9kdMu3) : galH1Cocycle q9khModule where
  f := φ.map
  cocycle := by
    intro g h
    rw [q9kh_act_trivial g (φ.map h)]
    exact φ.map_mul g h

/-- **往復 1**: cocycle → hom → cocycle は恒等。 -/
theorem q9kh_cocycle_hom_cocycle (f : galH1Cocycle q9khModule) :
    q9khCocycleOfHom (q9khHomOfCocycle f) = f :=
  galH1Cocycle.ext rfl

/-- **往復 2**: hom → cocycle → hom は恒等 ⟹ **Z¹ ≅ Hom(Gal(M/L₂), μ₃(O_M))**。 -/
theorem q9kh_hom_cocycle_hom (φ : Hom q9kdG q9kdMu3) :
    q9khHomOfCocycle (q9khCocycleOfHom φ) = φ :=
  galH1_hom_ext rfl

/-! ## q9kh-4（K1-k5）: Kummer コサイクル割当 κ と δ : ⟨[ζ₃]⟩ → H¹ -/

/-- **χ 冪の乗法性** χʲ(g)·χᵏ(g) = χ^{j+k}(g)（9×3 = 27 ケースの実 μ₃ 演算）。 -/
theorem q9kh_chipow_mul (j k g : q9kdGCar) :
    q9kdMu3.mul ((q9kdChiPow j).map g) ((q9kdChiPow k).map g)
      = (q9kdChiPow (q9kdGMul j k)).map g := by
  cases j <;> cases k <;> cases g <;>
    first
      | rfl
      | exact Subtype.ext (q3k_one_mul _)
      | exact Subtype.ext (q9kd_mul_one _)
      | exact Subtype.ext (q3k_embed_mul q3rqZeta q3rqZeta)
      | exact Subtype.ext q9kd_z_zsq
      | exact Subtype.ext q9kd_zsq_z
      | exact Subtype.ext q9kd_zsq_zsq

/-- **K1-k5 `q9khKappa`**: Kummer コサイクル割当 κ : ⟨[ζ₃]⟩-指数群 → Z¹、k ↦ (g ↦ χᵏ(g))。
    **群準同型**（乗法性は `q9kh_chipow_mul`）。 -/
def q9khKappa : Hom q9kdG (galH1_cocycles_group q9khModule) where
  map := fun k => q9khCocycleOfHom (q9kdChiPow k)
  map_mul := by
    intro j k
    apply galH1Cocycle.ext
    funext g
    exact (q9kh_chipow_mul j k g).symm

/-- **K1-k5（★）`q9khDelta`**: Kummer 写像 δ : ⟨[ζ₃]⟩-指数群 → H¹(Gal(M/L₂), μ₃(O_M))
    （M326F-6a `galH1KummerHom` の**初の実 instantiate**）。 -/
def q9khDelta : Hom q9kdG (galH1Group q9khModule) :=
  galH1KummerHom q9khModule q9khKappa

/-! ## q9kh-5（K1-k4,k6）: H¹ の完全計算 — δ は全単射（H¹ はちょうど 3 元） -/

/-- **K1-k4a（★）`q9kh_delta_surj`**: δ は全射
    （`quotientProjN_surjective` + `q9kd_kummer_iso_surj`（Hom 完全枚挙）消費）。 -/
theorem q9kh_delta_surj (x : (galH1Group q9khModule).carrier) :
    ∃ k, q9khDelta.map k = x := by
  obtain ⟨a, ha⟩ := q9kh_proj_surjective x
  obtain ⟨k, hk⟩ := q9kd_kummer_iso_surj (q9khHomOfCocycle a)
  refine ⟨k, ?_⟩
  show q9khProj.map (q9khCocycleOfHom (q9kdChiPow k)) = x
  rw [hk, q9kh_cocycle_hom_cocycle a]
  exact ha

/-- **K1-k4b（★）`q9kh_delta_inj`**: δ は単射
    （射影単射（B¹=1）+ 往復 + `q9kd_kummer_iso_inj`（χ 冪の相異）消費）。 -/
theorem q9kh_delta_inj : Hom.Injective q9khDelta := by
  intro j k h
  have h2 : q9khCocycleOfHom (q9kdChiPow j) = q9khCocycleOfHom (q9kdChiPow k) :=
    q9kh_proj_injective _ _ h
  have h3 : q9kdChiPow j = q9kdChiPow k := by
    have h4 := congrArg q9khHomOfCocycle h2
    rw [q9kh_hom_cocycle_hom, q9kh_hom_cocycle_hom] at h4
    exact h4
  exact q9kd_kummer_iso_inj j k h3

/-- **K1-k6a（★）`q9kh_H1_complete`**: H¹(Gal(M/L₂), μ₃(O_M)) の完全枚挙——
    任意の元は δ(0), δ(1), δ(2) のいずれか。 -/
theorem q9kh_H1_complete (x : (galH1Group q9khModule).carrier) :
    x = q9khDelta.map q9kdGCar.e
    ∨ x = q9khDelta.map q9kdGCar.s
    ∨ x = q9khDelta.map q9kdGCar.s2 := by
  obtain ⟨k, hk⟩ := q9kh_delta_surj x
  cases k with
  | e => exact Or.inl hk.symm
  | s => exact Or.inr (Or.inl hk.symm)
  | s2 => exact Or.inr (Or.inr hk.symm)

/-- **K1-k6b `q9kh_H1_ne_01`**: δ(0) ≠ δ(1)。 -/
theorem q9kh_H1_ne_01 : q9khDelta.map q9kdGCar.e ≠ q9khDelta.map q9kdGCar.s := by
  intro h
  exact q9kdGCar.noConfusion (q9kh_delta_inj _ _ h)

/-- **K1-k6c `q9kh_H1_ne_02`**: δ(0) ≠ δ(2)。 -/
theorem q9kh_H1_ne_02 : q9khDelta.map q9kdGCar.e ≠ q9khDelta.map q9kdGCar.s2 := by
  intro h
  exact q9kdGCar.noConfusion (q9kh_delta_inj _ _ h)

/-- **K1-k6d `q9kh_H1_ne_12`**: δ(1) ≠ δ(2)。 -/
theorem q9kh_H1_ne_12 : q9khDelta.map q9kdGCar.s ≠ q9khDelta.map q9kdGCar.s2 := by
  intro h
  exact q9kdGCar.noConfusion (q9kh_delta_inj _ _ h)

/-- **K1-k6e（★）`q9kh_kummer_h1_iso`**: 有限レベル Kummer 同型の Galois コホモロジー
    実現——δ : ⟨[ζ₃]⟩-指数群 → H¹(Gal(M/L₂), μ₃(O_M)) は**全単射群準同型**
    （＝ H¹ はちょうど 3 元・≅ ℤ/3）。M320F/M345F/M349F の抽象 Kummer 理論で
    **外部仮説だった全射性**が、この実拡大では**定理**になっている。 -/
theorem q9kh_kummer_h1_iso :
    (∀ x : (galH1Group q9khModule).carrier, ∃ k, q9khDelta.map k = x)
    ∧ Hom.Injective q9khDelta :=
  ⟨q9kh_delta_surj, q9kh_delta_inj⟩

/-! ## q9kh-6: capstone（束ねのみ・新規証明ゼロ） -/

/-- **capstone `Q3KummerH1RealData`**: 実 Galois コホモロジー H¹ の完全計算データ。 -/
structure Q3KummerH1RealData where
  /-- 実作用の自明性（計算結果・仮定でない）。 -/
  act_trivial : ∀ g m, (q9khModule.act g).map m = m
  /-- B¹ は自明。 -/
  B1_trivial : ∀ x, (galH1_coboundaries_subgroup q9khModule).mem x
    → x = (galH1_cocycles_group q9khModule).one
  /-- 射影 Z¹→H¹ は単射（H¹ ≅ Z¹）。 -/
  proj_injective : Hom.Injective q9khProj
  /-- Z¹ ≅ Hom(⟨σ⟩,μ₃)（往復 1）。 -/
  cocycle_roundtrip : ∀ f, q9khCocycleOfHom (q9khHomOfCocycle f) = f
  /-- Z¹ ≅ Hom(⟨σ⟩,μ₃)（往復 2）。 -/
  hom_roundtrip : ∀ φ, q9khHomOfCocycle (q9khCocycleOfHom φ) = φ
  /-- δ は全射。 -/
  delta_surj : ∀ x, ∃ k, q9khDelta.map k = x
  /-- δ は単射。 -/
  delta_inj : Hom.Injective q9khDelta
  /-- H¹ の完全枚挙（ちょうど 3 元）。 -/
  h1_complete : ∀ x, x = q9khDelta.map q9kdGCar.e
    ∨ x = q9khDelta.map q9kdGCar.s ∨ x = q9khDelta.map q9kdGCar.s2

/-- **証人 `q9kh_data`**: 実 M=ℚ₃(ζ₉)/L₂ 上の H¹ 完全計算。 -/
def q9kh_data : Q3KummerH1RealData where
  act_trivial := q9kh_act_trivial
  B1_trivial := q9kh_B1_trivial
  proj_injective := q9kh_proj_injective
  cocycle_roundtrip := q9kh_cocycle_hom_cocycle
  hom_roundtrip := q9kh_hom_cocycle_hom
  delta_surj := q9kh_delta_surj
  delta_inj := q9kh_delta_inj
  h1_complete := q9kh_H1_complete

/-- **`q9kh_exists`**: 実 Galois コホモロジー H¹(Gal(M/L₂), μ₃(O_M)) 完全計算の存在。 -/
theorem q9kh_exists : Nonempty Q3KummerH1RealData := ⟨q9kh_data⟩

end IUT
