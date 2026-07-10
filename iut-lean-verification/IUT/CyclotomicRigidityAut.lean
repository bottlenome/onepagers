/-
  IUT/CyclotomicRigidityAut.lean — CRA（柱A7 A7c: 実円分剛性の「定理内容」——実
  μ_{3^ℓ} ⊂ ℚ(ζ_{3^ℓ}) の自己準同型の冪分類・Gal ≅ Aut(μ_{3^ℓ})・円分指標 χ の
  生成元非依存性・正直な (ℤ/3^ℓ)^× 不定性）

  ── 主要成果の分類: **[実／昇格(a)]**（骨格・模型・代理でなく、実 ℚ・実円分体
     ℚ(ζ_{3^ℓ}) = ℚ[x]/(Φ_{3^ℓ}) の中の実 μ_{3^ℓ}=`cmrGrp`（cmr の実群）と実 Gal
     作用 `cgarAct`（cgar の実 CycGKAction）の上で、円分剛性の「教科書形の内容」を
     本物に確立する。cmr/cgar が実 μ・実作用・非自明 χ を供給したのに対し、本ファイル
     はその上で **(i) 任意の群自己準同型 e : μ→μ が冪写像 y↦y^{χ(e)} で尽くされる
     こと（Galois 由来でない e への剛性）・(ii) 作用写像 Gal→End(μ) が単射でその像が
     可逆自己準同型全体（＝Gal がちょうど Aut(μ_{3^ℓ}) を尽くす）・(iii) χ が原始根
     ζ の取り替えに依存しない canonical 指標であること**を証明し、M322F cycRig_rigidity
     〔作用の χ 決定〕を真に強化する。**Aut(μ) を Grp として新設せず**、単射性＋実現＋
     分類の 3 定理で同型を消去形で述べる（cci の Gal≅(ℤ/3^ℓ)^× と合成可能）。

  **complete_pct 影響**: A7 A7c——**実 μ_{3^ℓ} の自己準同型が冪写像で尽くされ
  （`cra_endo_pow`）・Gal がその可逆自己同型全体と一致（`cra_gal_inj`＋
  `cra_gal_realize`）・χ が生成元非依存に canonical（`cra_char_canonical`）**。
  M322F cycRig_rigidity（1 個の作用データに対する χ 決定）から、「μ の**全**自己準同型
  の分類」「Gal = Aut(μ) の消去形同型」へ引き上げる。正直な (ℤ/3^ℓ)^× 不定性
  `cra_indeterminacy` を定理として明示（消さない）。設計見込み A7 →0.3。

  内容（設計 audit/A7-real-cyclotomic-rigidity-detail-2026-07-10.md §3.2・CRA-0〜6）:
   * `cra_hom_ext`       — Hom の外延性（map 一致 ⟹ Hom 一致・map_mul は Prop）。CRA-0。
   * `craEndoChar`       — 自己準同型 e の円分指標 χ(e)=log_ζ(e ζ)。CRA-1。
   * `cra_endo_pow`      — ★任意 e の冪分類 e(y)=ζ^{χ(e)·log y}（Galois 仮定なし）。CRA-1。
   * `cra_endo_ext`      — χ(e)=χ(e') ⟹ e=e'（指標が自己準同型を決める）。CRA-1。
   * `craPowHom`         — 冪写像 y↦y^a（データ）。CRA-2。
   * `cra_iso_of_unit`   — 3∤a ⟹ y↦y^a と y↦y^{a⁻¹} が左右逆。CRA-2。
   * `cra_unit_of_iso`   — e 可逆 ⟹ 3∤χ(e)（単元指標）。CRA-2。
   * `cra_gal_inj`       — ★作用写像 Gal→End(μ) は単射（`cae_aut_ext`）。CRA-3。
   * `cra_gal_realize`   — ★可逆自己準同型は Galois で実現される（`cciFromUnits` witness）。CRA-3。
   * `cra_char_canonical`— χ は生成元 ζ の取り替えに依存しない canonical 指標。CRA-4。
   * `cra_indeterminacy` — ★正直な不定性: 全冪写像が Galois 作用と可換（(ℤ/3^ℓ)^× 不定性）。CRA-5。
   * `CraRigidityData`/`craRigidityData` — capstone。CRA-6。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   **p = 3・素数冪 3^ℓ 専用**の実円分体 ℚ(ζ_{3^ℓ})。一般素数 p は含めない。
   (ii)  ここで閉じるのは**純群論的な円分剛性**（μ の自己準同型分類・Gal=Aut(μ)・χ の
         生成元非依存）まで。IUT 本丸の **mono-theta 環境の円分剛性**（[EtTh]・
         ẑ^× 不定性を殺す幾何的円分剛性）は依然 scope 外（設計 §7）。
   (iii) **正直な (ℤ/3^ℓ)^× 不定性 `cra_indeterminacy` は消さない**——可換群 μ には
         全冪写像 y↦y^a（a∈(ℤ/3^ℓ)^×）が Galois 作用と可換に残る。これを殺すのが
         mono-theta 円分剛性であり、本ファイルはその「不定性の実在」を定理で固定する
         （柱E/D 後続・本設計 scope 外）。
   (iv)  Aut(μ_{3^ℓ}) を Grp として新設しない（Hom レコードの群化は共有インフラ級・
         範囲外）——単射性＋実現＋分類の 3 定理で同型を消去形で述べる。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・propext/Quot.sound
  のみ）。禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。許可タクティク（cases/obtain/induction/rw/show/
  refine/exact/apply/intro/generalize/funext/Subtype.ext/omega）のみ使用。3^ℓ は
  omega 不可（`zpu_pow_pos`/`zpu_one_lt` 再利用）。新規ファイル 1 個のみ（共有ファイル
  IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。prefix `cra`。
-/
import IUT.CyclotomicMuGroupReal
import IUT.CyclotomicGKActionReal
import IUT.CyclotomicCharIso
import IUT.CyclotomicMuTower
import IUT.Zmod3PowUnits

namespace IUT

/-! ## CRA-0: Hom の外延性 -/

/-- **CRA-0: Hom の外延性** — map が pointwise 一致すれば Hom は一致する。
    map_mul は Prop なので、map の一致（funext）を `cases` で消去すれば
    証明無関係で閉じる（choice 不使用）。 -/
theorem cra_hom_ext {G H : Grp} (e e' : Hom G H) (h : ∀ y, e.map y = e'.map y) : e = e' := by
  cases e with
  | mk m1 p1 =>
    cases e' with
    | mk m2 p2 =>
      have hm : m1 = m2 := funext h
      cases hm
      rfl

/-! ## CRA-補: 実 μ_{3^ℓ} の離散対数・位数・剰余還元（本ファイル簿記の基盤） -/

/-- **CRA-補0: 生成元の担体値** — cmr 生成元 ζ の val は NF 環の ζ（定義展開）。 -/
theorem cra_zeta_val (ℓ : Nat) (hℓ : 1 ≤ ℓ) : (cmrZeta ℓ hℓ).val = ctmZeta ℓ hℓ := rfl

/-- **CRA-補a: 離散対数の逆算** — y ∈ μ に対し ζ^{log y} = y（log y = ctmFind y.val）。
    cmr の `ctmFind_spec` と三者橋 `cmr_pow_zeta` から。 -/
theorem cra_pow_log (ℓ : Nat) (hℓ : 1 ≤ ℓ) (y : cmrCarrier ℓ hℓ) :
    (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (ctmFind ℓ hℓ y.val) = y := by
  apply Subtype.ext
  show ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (ctmFind ℓ hℓ y.val)).val = y.val
  rw [cmr_pow_zeta ℓ hℓ (ctmFind ℓ hℓ y.val)]
  exact ((ctmFind_spec ℓ hℓ y.val y.property).1).symm

/-- **CRA-補b: μ の元は位数 3^ℓ を割る** — 任意 y ∈ μ で y^{3^ℓ}=1（担体の root 性）。 -/
theorem cra_pow_ord (ℓ : Nat) (hℓ : 1 ≤ ℓ) (y : cmrCarrier ℓ hℓ) :
    (cmrGrp ℓ hℓ).pow y (3 ^ ℓ) = (cmrGrp ℓ hℓ).one := by
  apply Subtype.ext
  show ((cmrGrp ℓ hℓ).pow y (3 ^ ℓ)).val = (cmrGrp ℓ hℓ).one.val
  rw [cmr_pow_val ℓ hℓ y (3 ^ ℓ)]
  exact y.property

/-- **CRA-補c: μ の冪の mod 3^ℓ 還元** — y^a = y^{a % 3^ℓ}（位数 3^ℓ の周期性）。 -/
theorem cra_pow_reduce (ℓ : Nat) (hℓ : 1 ≤ ℓ) (y : cmrCarrier ℓ hℓ) (a : Nat) :
    (cmrGrp ℓ hℓ).pow y a = (cmrGrp ℓ hℓ).pow y (a % 3 ^ ℓ) :=
  cycRig_pow_reduce (cmrGrp ℓ hℓ) (cmr_comm ℓ hℓ) y (3 ^ ℓ) (cra_pow_ord ℓ hℓ y) a

/-- **CRA-補d: log ζ = 1** — 生成元 ζ の離散対数はちょうど 1。 -/
theorem cra_find_zeta (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    ctmFind ℓ hℓ (cmrZeta ℓ hℓ).val = 1 := by
  have h1 : (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (ctmFind ℓ hℓ (cmrZeta ℓ hℓ).val) = cmrZeta ℓ hℓ :=
    cra_pow_log ℓ hℓ (cmrZeta ℓ hℓ)
  have hv : ctmPow ℓ hℓ (ctmFind ℓ hℓ (cmrZeta ℓ hℓ).val) = ctmPow ℓ hℓ 1 := by
    rw [ctm_pow_one ℓ hℓ, ← cmr_pow_zeta ℓ hℓ (ctmFind ℓ hℓ (cmrZeta ℓ hℓ).val), h1,
        cra_zeta_val ℓ hℓ]
  have hlt : ctmFind ℓ hℓ (cmrZeta ℓ hℓ).val < 3 ^ ℓ :=
    (ctmFind_spec ℓ hℓ (cmrZeta ℓ hℓ).val (cmrZeta ℓ hℓ).property).2
  have hidx := cci_indexG ℓ hℓ (ctmFind ℓ hℓ (cmrZeta ℓ hℓ).val) 1 (zpu_one_lt ℓ hℓ) hv
  rw [Nat.mod_eq_of_lt hlt] at hidx
  exact hidx

/-! ## CRA-1: 自己準同型の指標と冪分類（★任意 e——Galois 仮定なし） -/

/-- **CRA-1a: 自己準同型の円分指標** χ(e) = log_ζ(e ζ)。e(ζ) ∈ μ は担体の subtype
    性で自動なので、走査 `ctmFind` がそのまま指標を与える。 -/
def craEndoChar (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (e : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ)) : Nat :=
  ctmFind ℓ hℓ (e.map (cmrZeta ℓ hℓ)).val

/-- **CRA-1b（★自己準同型の冪分類）: e(y) = ζ^{χ(e)·log y}** — Galois 由来でない
    **任意**の群自己準同型 e が冪写像で尽くされる。y=ζ^{log y}（`cra_pow_log`）→
    `Hom.map_pow` → e(ζ)=ζ^{χ(e)}（`cra_pow_log`・e ζ ∈ μ は subtype で自動）→
    可換群冪法則 `cycRig_pow_mul`。M322F cycRig_rigidity からの真の強化。 -/
theorem cra_endo_pow (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (e : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ)) (y : cmrCarrier ℓ hℓ) :
    e.map y = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e * ctmFind ℓ hℓ y.val) := by
  have hy : y = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (ctmFind ℓ hℓ y.val) :=
    (cra_pow_log ℓ hℓ y).symm
  have hz : e.map (cmrZeta ℓ hℓ) = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e) :=
    (cra_pow_log ℓ hℓ (e.map (cmrZeta ℓ hℓ))).symm
  calc e.map y
      = e.map ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (ctmFind ℓ hℓ y.val)) := congrArg e.map hy
    _ = (cmrGrp ℓ hℓ).pow (e.map (cmrZeta ℓ hℓ)) (ctmFind ℓ hℓ y.val) :=
        e.map_pow (cmrZeta ℓ hℓ) (ctmFind ℓ hℓ y.val)
    _ = (cmrGrp ℓ hℓ).pow ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e))
          (ctmFind ℓ hℓ y.val) :=
        congrArg (fun w => (cmrGrp ℓ hℓ).pow w (ctmFind ℓ hℓ y.val)) hz
    _ = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e * ctmFind ℓ hℓ y.val) :=
        (cycRig_pow_mul (cmrGrp ℓ hℓ) (cmr_comm ℓ hℓ) (cmrZeta ℓ hℓ)
          (craEndoChar ℓ hℓ e) (ctmFind ℓ hℓ y.val)).symm

/-- **CRA-1c: 指標が自己準同型を決める** — χ(e)=χ(e') ⟹ e=e'。冪分類＋外延性。 -/
theorem cra_endo_ext (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (e e' : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ))
    (h : craEndoChar ℓ hℓ e = craEndoChar ℓ hℓ e') : e = e' := by
  apply cra_hom_ext
  intro y
  rw [cra_endo_pow ℓ hℓ e y, cra_endo_pow ℓ hℓ e' y, h]

/-! ## CRA-2: 可逆性 ⟺ 単元指標 -/

/-- **CRA-2 補: 可換群の冪の積分配** — (y·z)^a = y^a·z^a。可換性の a 帰納。 -/
theorem cra_pow_mul_dist (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (y z : G.carrier) (a : Nat) :
    G.pow (G.mul y z) a = G.mul (G.pow y a) (G.pow z a) := by
  induction a with
  | zero => exact (G.one_mul G.one).symm
  | succ a ih =>
    show G.mul (G.mul y z) (G.pow (G.mul y z) a)
       = G.mul (G.mul y (G.pow y a)) (G.mul z (G.pow z a))
    rw [ih, G.mul_assoc y z (G.mul (G.pow y a) (G.pow z a)),
        ← G.mul_assoc z (G.pow y a) (G.pow z a), hc z (G.pow y a),
        G.mul_assoc (G.pow y a) z (G.pow z a),
        ← G.mul_assoc y (G.pow y a) (G.mul z (G.pow z a))]

/-- **CRA-2a: 冪写像** y ↦ y^a（可換群なので群自己準同型・map_mul は `cra_pow_mul_dist`）。 -/
def craPowHom (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : Nat) :
    Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ) where
  map := fun y => (cmrGrp ℓ hℓ).pow y a
  map_mul := fun y z => cra_pow_mul_dist (cmrGrp ℓ hℓ) (cmr_comm ℓ hℓ) y z a

/-- **CRA-2 補: 冪写像の合成** (y↦y^a)∘(・)^{a'} の値 y^{a'} を y^a に送ると y^{a'·a}
    ではなく、`craPowHom a'` を先に適用してから `craPowHom a` で y^{a·a'}。 -/
theorem cra_comp_pow (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a a' : Nat) (y : cmrCarrier ℓ hℓ) :
    (craPowHom ℓ hℓ a').map ((craPowHom ℓ hℓ a).map y)
      = (cmrGrp ℓ hℓ).pow y (a * a') := by
  show (cmrGrp ℓ hℓ).pow ((cmrGrp ℓ hℓ).pow y a) a' = (cmrGrp ℓ hℓ).pow y (a * a')
  exact (cycRig_pow_mul (cmrGrp ℓ hℓ) (cmr_comm ℓ hℓ) y a a').symm

/-- **CRA-2b: 単元 ⟹ 可逆** — 3∤a なら y↦y^a と y↦y^{a⁻¹}（a⁻¹=`zpuInvL ℓ a`）は
    左右逆。a·a⁻¹ ≡ 1 mod 3^ℓ（`zpuInvL_one`）＋位数 3^ℓ の還元（`cra_pow_reduce`）。 -/
theorem cra_iso_of_unit (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : Nat) (ha : ¬ 3 ∣ a) :
    (∀ y, (craPowHom ℓ hℓ (zpuInvL ℓ a)).map ((craPowHom ℓ hℓ a).map y) = y) ∧
    (∀ y, (craPowHom ℓ hℓ a).map ((craPowHom ℓ hℓ (zpuInvL ℓ a)).map y) = y) := by
  refine ⟨?_, ?_⟩
  · intro y
    rw [cra_comp_pow ℓ hℓ a (zpuInvL ℓ a) y,
        cra_pow_reduce ℓ hℓ y (a * zpuInvL ℓ a),
        zpuInvL_one ℓ hℓ a ha]
    exact (cmrGrp ℓ hℓ).mul_one y
  · intro y
    rw [cra_comp_pow ℓ hℓ (zpuInvL ℓ a) a y,
        Nat.mul_comm (zpuInvL ℓ a) a,
        cra_pow_reduce ℓ hℓ y (a * zpuInvL ℓ a),
        zpuInvL_one ℓ hℓ a ha]
    exact (cmrGrp ℓ hℓ).mul_one y

/-- **CRA-2c: 可逆 ⟹ 単元指標** — 左右逆 Hom を持つ e は 3∤χ(e)。生成元 ζ で読み
    χ(e')·χ(e) ≡ 1 mod 3^ℓ（`cci_indexG`）ゆえ 3∤χ(e)。 -/
theorem cra_unit_of_iso (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (e e' : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ))
    (hl : ∀ y, e'.map (e.map y) = y) (hr : ∀ y, e.map (e'.map y) = y) :
    ¬ 3 ∣ craEndoChar ℓ hℓ e := by
  have he : e.map (cmrZeta ℓ hℓ) = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e) := by
    rw [cra_endo_pow ℓ hℓ e (cmrZeta ℓ hℓ), cra_find_zeta ℓ hℓ, Nat.mul_one]
  have he' : e'.map (cmrZeta ℓ hℓ) = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e') := by
    rw [cra_endo_pow ℓ hℓ e' (cmrZeta ℓ hℓ), cra_find_zeta ℓ hℓ, Nat.mul_one]
  have key : (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e' * craEndoChar ℓ hℓ e)
      = cmrZeta ℓ hℓ := by
    have hcomp : e'.map (e.map (cmrZeta ℓ hℓ)) = cmrZeta ℓ hℓ := hl (cmrZeta ℓ hℓ)
    rw [he, e'.map_pow, he'] at hcomp
    rw [cycRig_pow_mul (cmrGrp ℓ hℓ) (cmr_comm ℓ hℓ) (cmrZeta ℓ hℓ)
          (craEndoChar ℓ hℓ e') (craEndoChar ℓ hℓ e)]
    exact hcomp
  have hval : ctmPow ℓ hℓ (craEndoChar ℓ hℓ e' * craEndoChar ℓ hℓ e) = ctmPow ℓ hℓ 1 := by
    rw [ctm_pow_one ℓ hℓ,
        ← cmr_pow_zeta ℓ hℓ (craEndoChar ℓ hℓ e' * craEndoChar ℓ hℓ e), key, cra_zeta_val ℓ hℓ]
  have hmod : (craEndoChar ℓ hℓ e' * craEndoChar ℓ hℓ e) % 3 ^ ℓ = 1 :=
    cci_indexG ℓ hℓ (craEndoChar ℓ hℓ e' * craEndoChar ℓ hℓ e) 1 (zpu_one_lt ℓ hℓ) hval
  intro hdvd
  have h3 : (3 : Nat) ∣ (craEndoChar ℓ hℓ e' * craEndoChar ℓ hℓ e) := by
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨craEndoChar ℓ hℓ e' * t, ?_⟩
    rw [ht, ← Nat.mul_assoc, Nat.mul_comm (craEndoChar ℓ hℓ e') 3, Nat.mul_assoc]
  have hd3 : (3 : Nat) ∣ 3 ^ ℓ := zpu_three_dvd_pow ℓ hℓ
  have hmm : (craEndoChar ℓ hℓ e' * craEndoChar ℓ hℓ e) % 3 ^ ℓ % 3
      = (craEndoChar ℓ hℓ e' * craEndoChar ℓ hℓ e) % 3 :=
    Nat.mod_mod_of_dvd _ hd3
  obtain ⟨s, hs⟩ := h3
  rw [hmod, hs] at hmm
  omega

/-! ## CRA-3: ★Gal ≅ Aut(μ_{3^ℓ})（円分剛性の教科書形・A7c 本丸） -/

/-- **CRA-3 補: 実作用の値** — ((cgarAct).act σ) の μ 上の写像は σ の体自己同型の
    制限（`cgarRestrict` の担体 val は σ.val.toFun）。 -/
theorem cra_act_val (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) (y : cmrCarrier ℓ hℓ) :
    (((cgarAct ℓ hℓ).act σ).map y).val = σ.val.toFun y.val := rfl

/-- **CRA-3a（★単射）: 作用写像 Gal → End(μ) は単射** — 二つの σ,τ が μ 上で同じ
    自己準同型を与えるなら σ=τ。生成元 ζ で読み `cae_aut_ext`（既存の決定補題）。 -/
theorem cra_gal_inj (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ τ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier)
    (h : ∀ y, ((cgarAct ℓ hℓ).act σ).map y = ((cgarAct ℓ hℓ).act τ).map y) : σ = τ := by
  apply Subtype.ext
  refine cae_aut_ext ℓ hℓ σ.val τ.val σ.property τ.property ?_
  rw [csa_gen_eq ℓ hℓ]
  have hz := congrArg Subtype.val (h (cmrZeta ℓ hℓ))
  rw [cra_act_val ℓ hℓ σ (cmrZeta ℓ hℓ), cra_act_val ℓ hℓ τ (cmrZeta ℓ hℓ)] at hz
  exact hz

/-- **CRA-3 補: 単元指標の witness** — 可逆 e から (ℤ/3^ℓ)^× の元 χ(e) mod 3^ℓ。 -/
def craUnit (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (e : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ)) (hnd : ¬ 3 ∣ craEndoChar ℓ hℓ e) :
    (zpuGrp ℓ hℓ).carrier :=
  ⟨craEndoChar ℓ hℓ e % 3 ^ ℓ, Nat.mod_lt _ (by have := zpu_pow_pos ℓ; omega),
    zpu_mod_nd3 ℓ hℓ (craEndoChar ℓ hℓ e) hnd⟩

/-- **CRA-3b（★実現）: 可逆自己準同型は Galois で実現される** — 左右逆 Hom を持つ
    e に対し、σ := `cciFromUnits`⟨χ(e) mod 3^ℓ,…⟩ ∈ Gal が μ 上で e に一致する。
    単射性（CRA-3a）と合わせ「作用写像 Gal → Aut(μ_{3^ℓ}) は全単射」＝円分剛性の
    教科書形。witness は choice-free（∃ は Prop ゴール内のみ）。 -/
theorem cra_gal_realize (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (e e' : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ))
    (hl : ∀ y, e'.map (e.map y) = y) (hr : ∀ y, e.map (e'.map y) = y) :
    ∃ σ, ∀ y, ((cgarAct ℓ hℓ).act σ).map y = e.map y := by
  have hnd : ¬ 3 ∣ craEndoChar ℓ hℓ e := cra_unit_of_iso ℓ hℓ e e' hl hr
  refine ⟨(cciFromUnits ℓ hℓ).map (craUnit ℓ hℓ e hnd), ?_⟩
  intro y
  have hexp : cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ)
      ((cciFromUnits ℓ hℓ).map (craUnit ℓ hℓ e hnd)) = craEndoChar ℓ hℓ e % 3 ^ ℓ := by
    rw [cgar_exp_eq ℓ hℓ ((cciFromUnits ℓ hℓ).map (craUnit ℓ hℓ e hnd))]
    exact cci_charG_csaAut ℓ hℓ (craUnit ℓ hℓ e hnd)
  rw [cgar_rigidity ℓ hℓ ((cciFromUnits ℓ hℓ).map (craUnit ℓ hℓ e hnd)) y, hexp,
      cra_endo_pow ℓ hℓ e y,
      cra_pow_reduce ℓ hℓ (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e % 3 ^ ℓ * ctmFind ℓ hℓ y.val),
      cra_pow_reduce ℓ hℓ (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e * ctmFind ℓ hℓ y.val),
      zpu_mod_mul (craEndoChar ℓ hℓ e) (ctmFind ℓ hℓ y.val) (3 ^ ℓ)]

/-! ## CRA-4: χ の canonical 性（生成元非依存・同一視の剛性） -/

/-- **CRA-4（★canonical）: χ は生成元非依存** — 任意の**原始**3^ℓ 乗根 y'（¬3∤log y'）
    に対し σ(y') = y'^{χ(σ)}。σ(y')=σ(ζ^b)=ζ^{ab}=(ζ^b)^a=y'^a——どの原始根で読んでも
    同じ指数 a=χ(σ)。μ≅ℤ/3^ℓ の同一視の選択に χ が依存しない（円分指標の内在性）。
    正直申告: 仮説 hy'（y' が原始根）は「生成元の取り替え」を主語に固定するもの。 -/
theorem cra_char_canonical (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) (y' : cmrCarrier ℓ hℓ)
    (hy' : ¬ 3 ∣ ctmFind ℓ hℓ y'.val) :
    ((cgarAct ℓ hℓ).act σ).map y' = (cmrGrp ℓ hℓ).pow y' (ctr_charG ℓ hℓ σ.val) := by
  rw [cgar_rigidity ℓ hℓ σ y', cgar_exp_eq ℓ hℓ σ]
  have hy : y' = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (ctmFind ℓ hℓ y'.val) :=
    (cra_pow_log ℓ hℓ y').symm
  have hR : (cmrGrp ℓ hℓ).pow y' (ctr_charG ℓ hℓ σ.val)
      = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (ctmFind ℓ hℓ y'.val * ctr_charG ℓ hℓ σ.val) := by
    have e1 : (cmrGrp ℓ hℓ).pow y' (ctr_charG ℓ hℓ σ.val)
        = (cmrGrp ℓ hℓ).pow ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (ctmFind ℓ hℓ y'.val))
            (ctr_charG ℓ hℓ σ.val) :=
      congrArg (fun w => (cmrGrp ℓ hℓ).pow w (ctr_charG ℓ hℓ σ.val)) hy
    rw [e1, ← cycRig_pow_mul (cmrGrp ℓ hℓ) (cmr_comm ℓ hℓ) (cmrZeta ℓ hℓ)
          (ctmFind ℓ hℓ y'.val) (ctr_charG ℓ hℓ σ.val)]
  rw [hR, Nat.mul_comm (ctr_charG ℓ hℓ σ.val) (ctmFind ℓ hℓ y'.val)]

/-! ## CRA-5: 正直な不定性（消さない・IUT 本丸との距離の明示） -/

/-- **CRA-5（★正直な不定性・消さない）: 全冪写像が Galois 作用と可換** —
    任意の a に対し σ(y^a) = (σ y)^a。可換群 μ には冪写像 y↦y^a（a∈(ℤ/3^ℓ)^×）が
    Galois 作用と可換に残る＝純 Galois 加群としての μ の (ℤ/3^ℓ)^× 不定性。
    この不定性を殺すのが mono-theta 環境の円分剛性（[EtTh]・柱E/D 後続・本設計 scope 外）。
    両辺とも (σ y)^a（((cgarAct).act σ) が Hom ゆえ `Hom.map_pow`）。 -/
theorem cra_indeterminacy (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : Nat)
    (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) (y : cmrCarrier ℓ hℓ) :
    ((cgarAct ℓ hℓ).act σ).map ((craPowHom ℓ hℓ a).map y)
      = (craPowHom ℓ hℓ a).map (((cgarAct ℓ hℓ).act σ).map y) := by
  show ((cgarAct ℓ hℓ).act σ).map ((cmrGrp ℓ hℓ).pow y a)
     = (cmrGrp ℓ hℓ).pow (((cgarAct ℓ hℓ).act σ).map y) a
  exact ((cgarAct ℓ hℓ).act σ).map_pow y a

/-! ## CRA-6: capstone -/

/-- **CRA-6a: 円分剛性データ**（実 μ_{3^ℓ} の自己準同型分類・Gal=Aut(μ)・χ canonical）。 -/
structure CraRigidityData (ℓ : Nat) (hℓ : 1 ≤ ℓ) where
  /-- 任意の自己準同型は冪写像で尽くされる。 -/
  endo_pow : ∀ (e : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ)) (y : cmrCarrier ℓ hℓ),
    e.map y = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e * ctmFind ℓ hℓ y.val)
  /-- 指標が自己準同型を決める。 -/
  endo_ext : ∀ (e e' : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ)),
    craEndoChar ℓ hℓ e = craEndoChar ℓ hℓ e' → e = e'
  /-- 作用写像 Gal → End(μ) は単射。 -/
  gal_inj : ∀ (σ τ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier),
    (∀ y, ((cgarAct ℓ hℓ).act σ).map y = ((cgarAct ℓ hℓ).act τ).map y) → σ = τ
  /-- 可逆自己準同型は Galois で実現される。 -/
  gal_realize : ∀ (e e' : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ)),
    (∀ y, e'.map (e.map y) = y) → (∀ y, e.map (e'.map y) = y) →
    ∃ σ, ∀ y, ((cgarAct ℓ hℓ).act σ).map y = e.map y
  /-- χ は生成元非依存。 -/
  char_canonical : ∀ (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) (y' : cmrCarrier ℓ hℓ),
    ¬ 3 ∣ ctmFind ℓ hℓ y'.val →
    ((cgarAct ℓ hℓ).act σ).map y' = (cmrGrp ℓ hℓ).pow y' (ctr_charG ℓ hℓ σ.val)

/-- **CRA-6b: witness** — 全フィールド既証明の純レコード（実 μ_{3^ℓ} を主語）。 -/
def craRigidityData (ℓ : Nat) (hℓ : 1 ≤ ℓ) : CraRigidityData ℓ hℓ where
  endo_pow := cra_endo_pow ℓ hℓ
  endo_ext := cra_endo_ext ℓ hℓ
  gal_inj := cra_gal_inj ℓ hℓ
  gal_realize := cra_gal_realize ℓ hℓ
  char_canonical := cra_char_canonical ℓ hℓ

end IUT
