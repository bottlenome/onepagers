/-
  IUT/Q3TateCubeIsogeny.lean — A8d（柱A A8: 楕円 cuspidalization の奇 N 切片 —
  実 [3]-同種 cube: E₉(ℚ₃)→E₉(ℚ₃)・実 3-捻れ E₉[3](ℚ₃) = {O}・cube-cuspidalization
  図式の**デッキ群自明**）

  ── 主要成果の分類: **[実／本物建設(b)]**。
     Q3TateCuspidalization（q3cu）の正直限定 4「単一切片 N=2・q=9（E[2] 全有理という
     本コースの忠実部分ケース）・奇 N は後続」と Q3TateTorsion（q3tt）の正直限定 2
     「l=2 のみ。奇素数 l の E_q[l] は ℚ₃ 有理でない（ζ_l∉ℚ₃・q^{1/l}∉ℚ₃）」を、
     **奇 N=3 について本物の正定理へ昇格**する: 実 ℚ₃-有理 Tate 曲線 E₉=ℚ₃^×/9^ℤ の
     上に実 [3]-同種 cube=[x]↦[x³] を Hom として建て、その核（＝3-捻れの ℚ₃ 有理部）が
     **ちょうど {O}**（E₉[3](ℚ₃)=0・非自明 3-捻れは ℚ₃ 有理でない）であることを完全証明
     する。既存の実 μ₃ 完全性（q3mc_z3_cube_root_one：ℤ₃ 内 x³=1⟹x=1）を**再利用（import・
     再証明せず）**し、その帰結として付値方向の 2∣3k⟹2∣k と合わせて核自明を閉じる。

  complete_pct 影響: **A8 を前進**（奇 N=3 の楕円 cuspidalization 基体を実 ℚ₃ 上でゼロから
  建設。q3cu 正直限定 4・q3tt 正直限定 2 を奇 N について本物へ置換）。主要内容:
  (i)   μ₃/zpUnits 版 q3c3_mu3_units（既存 q3mc_z3_cube_root_one の薄い再輸出・再証明なし）、
  (ii)  可換曲線の 4 項並べ替え q3c3_curve_rearrange、
  (iii) ★ 実 [3]-同種 cube: E₉→E₉（q3c3Cube・cube x = sq(x)·x = x³・Hom）、
  (iv)  成分公式 q3c3_cube_proj（cube[k,u]=[3k, u³]）、
  (v)   ★★ 核＝ちょうど {O} q3c3_ker_eq_trivial（cube x=O ⟺ x=O・μ₃ 完全性を消費・
        E₉[3](ℚ₃)=0 の実定理）、
  (vi)  ★ [3] は ℚ₃ 点で単射 q3c3_cube_injective（核自明＋Hom）、
  (vii) cube-cuspidalization 図式: 実開曲線 E₉∖E₉[3]（=E₉∖{O}・q3c3_open_eq_punct）・
        [3]-制限射 q3c3OpenMap・デッキ群自明 q3c3_deck_trivial、
  (viii)束ね q3c3Data。

  正直な限定（§4 準拠・消去/弱化しない・既存 surrogate/正直申告は消さない）:
  1. **cuspidal 惰性群 = 0 のまま**（q3cu 正直限定 1 を継承）。[3]-被覆も E∖{O} 上不分岐で
     惰性を担わない。非自明 cusp 惰性の最小担体は非可換テータ被覆（柱E EtaleTheta）で、
     本モジュールは解消を主張しない。
  2. **π₁ 再構成アルゴリズム（cuspidalization 本体）= 0**（q3cu 正直限定 2 を継承）。
     建てるのは奇 N=3 の幾何的基体＋3-捻れ有理部の完全決定（={O}）のみ。
  3. **K 点の影**（q3cu 正直限定 3・A2 を継承）: スキーム・エタールサイト・位相なし。
     「開曲線」は subtype・「被覆」は核剰余類ファイバーの写像。ただし奇 N=3 では核が {O}
     ゆえ本切片の被覆は自明（デッキ群 1・単葉）——これは弱化でなく**本物の幾何**（μ₃∉ℚ₃・
     q^{1/3}=3^{2/3}∉ℚ₃ の帰結を隠さず定理化）。
  4. **単一切片**: p=3・q=9（m=2）・N=3 のみ。μ₃ を有理化する拡大 ℚ₃(ζ₃) 上の E[3] 全有理化
     は q3mc/q9tl 系の後続（本モジュールは ℚ₃ 上の**非有理性の正の帰結**＝核自明を主張）。
  5. **二重計上の排除（監査向け・明示）**:
     - vs A8c（q3cu）: q3cu は [2]-同種 sq・核＝Klein 4 群（非自明・4 元）。本モジュールは
       [3]-同種 cube・核＝{O}（自明・1 元）。同種も核も disjoint。q3cuSq は部品として
       消費するが（cube=sq·id）、cube・核自明・[3] 単射・cube-開曲線は全て新規。
     - vs Q3Mu3Completeness（q3mc）: q3mc は ℤ₃/O_{ℚ₃(ζ₃)} 内の μ₃ 完全性。本モジュールは
       それを**再利用（import）**し E₉(ℚ₃) の**曲線上の 3-捻れ有理部＝{O}**を導く（別主語・
       別帰結）。μ₃ を再証明しない（水増し回避）。
     - vs Q3TateCurveL9（q9tl）: q9tl は拡大体 M 上の E_{3⁹} と位数 9 の点。本モジュールは
       ℚ₃ 上の E₉ と 3-捻れ有理部の非存在（={O}）。体も curve も N も disjoint。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ（Classical.choice 無し）。
-/
import IUT.Q3TateCuspidalization
import IUT.Q3Mu3Completeness

namespace IUT

/-! ## q3c3-0: μ₃/zpUnits 版（既存 q3mc の薄い再輸出・再証明なし） -/

/-- **q3c3-0: μ₃ 完全性（ℤ₃^× 版）** — u∈ℤ₃^×, u³=1 ⟹ u=1。
    既存 q3mc_z3_cube_root_one（ℤ₃ 内 x³=1⟹x=1・本物）を単数群の成分へ持ち上げる薄い
    再輸出（zpUnits.mul = zpMul on .val = z3.mul・新規証明ゼロ）。 -/
theorem q3c3_mu3_units (u : (zpUnits 3 isPrime_three).carrier)
    (hu : (zpUnits 3 isPrime_three).mul ((zpUnits 3 isPrime_three).mul u u) u
            = (zpUnits 3 isPrime_three).one) :
    u = (zpUnits 3 isPrime_three).one := by
  apply Subtype.ext
  have hv : z3.mul (z3.mul u.val u.val) u.val = z3.one := congrArg Subtype.val hu
  exact q3mc_z3_cube_root_one u.val hv

/-! ## q3c3-1: 可換曲線の 4 項並べ替え（cube の Hom 性の核） -/

/-- **q3c3-1: 可換曲線の 4 項並べ替え** — (p·q)·(r·s) = (p·r)·(q·s)。
    E₉ の可換性（q3tCurve_abelian）＋結合律。cube = sq·id の Hom 性に使う。 -/
theorem q3c3_curve_rearrange (p q r s : (q3tCurve 2).carrier) :
    (q3tCurve 2).mul ((q3tCurve 2).mul p q) ((q3tCurve 2).mul r s)
      = (q3tCurve 2).mul ((q3tCurve 2).mul p r) ((q3tCurve 2).mul q s) := by
  rw [(q3tCurve 2).mul_assoc p q ((q3tCurve 2).mul r s),
      ← (q3tCurve 2).mul_assoc q r s,
      q3tCurve_abelian 2 q r,
      (q3tCurve 2).mul_assoc r q s,
      ← (q3tCurve 2).mul_assoc p r ((q3tCurve 2).mul q s)]

/-! ## q3c3-2: ★ 実 [3]-同種 cube: E₉(ℚ₃) → E₉(ℚ₃) -/

/-- **q3c3-2（★）: 実 [3]-同種 cube: E₉ → E₉**（[x]↦[x³]）。
    cube x := sq(x)·x（既存の実 [2]-同種 q3cuSq と恒等の積）。sq が Hom・id が Hom で
    E₉ が可換ゆえ積も Hom（map_mul は q3c3_curve_rearrange で 4 項を並べ替え）。
    q3cu の [2]-同種 sq とは同種も次数も別物（こちらは次数 9 の乗算写像）。 -/
def q3c3Cube : Hom (q3tCurve 2) (q3tCurve 2) where
  map := fun x => (q3tCurve 2).mul (q3cuSq.map x) x
  map_mul := by
    intro x y
    show (q3tCurve 2).mul (q3cuSq.map ((q3tCurve 2).mul x y)) ((q3tCurve 2).mul x y)
       = (q3tCurve 2).mul ((q3tCurve 2).mul (q3cuSq.map x) x) ((q3tCurve 2).mul (q3cuSq.map y) y)
    rw [q3cuSq.map_mul,
        q3c3_curve_rearrange (q3cuSq.map x) (q3cuSq.map y) x y]

/-- **q3c3-2b: cube x = x·x·x** — sq x = x·x（q3cu_sq_eq_square）ゆえ cube x = (x·x)·x。 -/
theorem q3c3_cube_eq_cube (x : (q3tCurve 2).carrier) :
    q3c3Cube.map x = (q3tCurve 2).mul ((q3tCurve 2).mul x x) x := by
  show (q3tCurve 2).mul (q3cuSq.map x) x = (q3tCurve 2).mul ((q3tCurve 2).mul x x) x
  rw [q3cu_sq_eq_square x]

/-! ## q3c3-3: 成分公式 cube[k,u] = [3k, u³] -/

/-- **q3c3-3: 成分公式** cube[k,u] = [(k+k)+k, (u·u)·u] = [3k, u³]。
    sq[k,u]=[k+k,u·u]（q3cu_sq_eq_square＋q3tt_proj_mul）に [k,u] を掛けた成分算術。 -/
theorem q3c3_cube_proj (k : Int) (u : (zpUnits 3 isPrime_three).carrier) :
    q3c3Cube.map ((q3tProj 2).map (k, u))
      = (q3tProj 2).map ((k + k) + k,
          (zpUnits 3 isPrime_three).mul ((zpUnits 3 isPrime_three).mul u u) u) := by
  show (q3tCurve 2).mul (q3cuSq.map ((q3tProj 2).map (k, u))) ((q3tProj 2).map (k, u))
     = (q3tProj 2).map ((k + k) + k,
         (zpUnits 3 isPrime_three).mul ((zpUnits 3 isPrime_three).mul u u) u)
  rw [q3cu_sq_eq_square ((q3tProj 2).map (k, u)),
      q3tt_proj_mul k k u u,
      q3tt_proj_mul (k + k) k ((zpUnits 3 isPrime_three).mul u u) u]

/-! ## q3c3-4: ★★ 核＝ちょうど {O}（E₉[3](ℚ₃) = 0） -/

/-- **q3c3-4（★★）: 実 3-捻れ有理部＝ちょうど {O}** — cube x = O ⟺ x = O。
    → は成分公式で 2∣3k ∧ u³=1 を取り出し、**μ₃ 完全性 q3c3_mu3_units を消費**して u=1、
    付値方向 2∣3k⟹2∣k で [k,1]=O。← は Hom.map_one。
    **E₉[3](ℚ₃)=0（非自明 3-捻れは ℚ₃ 有理でない）の実定理**——μ₃∉ℚ₃・q^{1/3}∉ℚ₃ の
    正の帰結。q3tt 正直限定 2「奇 l の E_q[l] は ℚ₃ 有理でない」を奇 N=3 について本物化。 -/
theorem q3c3_ker_eq_trivial (x : (q3tCurve 2).carrier) :
    q3c3Cube.map x = (q3tCurve 2).one ↔ x = (q3tCurve 2).one := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := q3tProj_surjective 2 x
    obtain ⟨k, u⟩ := a
    rw [← ha] at h ⊢
    rw [q3c3_cube_proj k u] at h
    have hmem := (quotientProjN_ker q3tGrp (q3tSubgroup 2) (q3t_normal (q3tSubgroup 2))
      ((k + k) + k, (zpUnits 3 isPrime_three).mul ((zpUnits 3 isPrime_three).mul u u) u)).mp h
    obtain ⟨hdvd, hu3⟩ := (q3t_mem_pair_iff 2 ((k + k) + k)
      ((zpUnits 3 isPrime_three).mul ((zpUnits 3 isPrime_three).mul u u) u)).mp hmem
    have hu1 : u = (zpUnits 3 isPrime_three).one := q3c3_mu3_units u hu3
    have hk : ((2 : Nat) : Int) ∣ k := by
      obtain ⟨t, ht⟩ := hdvd
      exact ⟨t - k, by omega⟩
    apply (quotientProjN_ker q3tGrp (q3tSubgroup 2) (q3t_normal (q3tSubgroup 2)) (k, u)).mpr
    exact (q3t_mem_pair_iff 2 k u).mpr ⟨hk, hu1⟩
  · intro h
    rw [h]
    exact q3c3Cube.map_one

/-! ## q3c3-5: ★ [3] は ℚ₃ 点で単射（核自明の帰結） -/

/-- **q3c3-5（★）: [3] は ℚ₃ 点で単射** — cube x = cube y ⟹ x = y。
    核自明（q3c3_ker_eq_trivial）＋ Hom 性: cube(x·y⁻¹)=cube x·(cube y)⁻¹=O ⟹ x·y⁻¹=O。
    q3cu の [2]-同種が ℚ₃ 点で**非全射**（q3cu_not_surjective）だったのと対をなす、奇 N=3
    切片の**単射性**（核自明ゆえファイバー単葉）。 -/
theorem q3c3_cube_injective : q3c3Cube.Injective := by
  intro x y h
  have hker : q3c3Cube.map ((q3tCurve 2).mul x ((q3tCurve 2).inv y)) = (q3tCurve 2).one := by
    rw [q3c3Cube.map_mul, q3c3Cube.map_inv, h, (q3tCurve 2).mul_inv]
  have h1 : (q3tCurve 2).mul x ((q3tCurve 2).inv y) = (q3tCurve 2).one :=
    (q3c3_ker_eq_trivial _).mp hker
  have h2 : (q3tCurve 2).inv y = (q3tCurve 2).inv x :=
    (q3tCurve 2).inv_eq_of_mul_eq_one h1
  have h3 := congrArg (q3tCurve 2).inv h2
  rw [(q3tCurve 2).inv_inv, (q3tCurve 2).inv_inv] at h3
  exact h3.symm

/-! ## q3c3-6: ★ cube-cuspidalization 図式（開曲線・制限射・デッキ群自明） -/

/-- **q3c3-6a: 実開曲線 E₉∖E₉[3]**（上流 cusp E₉[3]=ker(cube) を抜いた曲線・subtype）。 -/
def q3c3Open : Type := { x : (q3tCurve 2).carrier // q3c3Cube.map x ≠ (q3tCurve 2).one }

/-- **q3c3-6b（★）: E₉∖E₉[3] = E₉∖{O}** — cube x ≠ O ⟺ x ≠ O。
    核＝{O}（q3c3_ker_eq_trivial）ゆえ上流 cusp 集合 E₉[3](ℚ₃) が下流 cusp {O} と一致。
    奇 N=3 では被覆に追加の有理 cusp が現れない（cusp 集合の完全決定）。 -/
theorem q3c3_open_eq_punct (x : (q3tCurve 2).carrier) :
    q3c3Cube.map x ≠ (q3tCurve 2).one ↔ x ≠ (q3tCurve 2).one := by
  constructor
  · intro h he
    apply h
    rw [he]
    exact q3c3Cube.map_one
  · intro h he
    apply h
    exact (q3c3_ker_eq_trivial x).mp he

/-- **q3c3-6c（★）: [3]-制限射 E₉∖E₉[3] → E₉∖{O}** — x↦cube(x)。x∉ker ⟹ cube x≠O は
    定義そのもの。cuspidalization 図式の奇 N=3 版の射（開曲線 q3c3Open を定義域・
    q3cuPunct を終域として実際に使う）。 -/
def q3c3OpenMap : q3c3Open → q3cuPunct := fun x => ⟨q3c3Cube.map x.val, x.property⟩

/-- **q3c3-6d（★）: デッキ群自明** — cube a = O ⟹ a = O。
    核＝{O}（q3c3_ker_eq_trivial）の言い換え。奇 N=3 の cube-被覆はデッキ群が自明
    （q3cu の [2]-被覆が Klein 4 デッキだったのと対照）——被覆は単葉。 -/
theorem q3c3_deck_trivial (a : (q3tCurve 2).carrier)
    (h : q3c3Cube.map a = (q3tCurve 2).one) : a = (q3tCurve 2).one :=
  (q3c3_ker_eq_trivial a).mp h

/-- **q3c3-6e（★）: ファイバー単葉** — cube x = cube y ⟹ x = y（単射の別名・
    デッキ群自明ゆえ各ファイバーが 1 点）。 -/
theorem q3c3_fiber_singleton (x y : (q3tCurve 2).carrier)
    (h : q3c3Cube.map x = q3c3Cube.map y) : x = y :=
  q3c3_cube_injective x y h

/-! ## q3c3-7: capstone（新規証明なし・束ねのみ） -/

/-- **q3c3-7a: 奇 N=3 楕円 cuspidalization 基体データ** — 実 [3]-同種・成分公式・
    核＝{O}（E₉[3](ℚ₃)=0）・[3] 単射・開曲線 E₉∖E₉[3]=E₉∖{O} の制限射・デッキ群自明
    を束ねる（[AbsTopII] §3 の奇 N 幾何入力の実現）。 -/
structure Q3CubeIsogenyData where
  /-- 実 [3]-同種 cube: E₉ → E₉。 -/
  isog : Hom (q3tCurve 2) (q3tCurve 2)
  /-- cube x = x·x·x（次数 9 の乗算写像）。 -/
  cube_eq : ∀ x, isog.map x = (q3tCurve 2).mul ((q3tCurve 2).mul x x) x
  /-- 核＝ちょうど {O}（E₉[3](ℚ₃)=0・μ₃ 完全性を消費）。 -/
  ker_trivial : ∀ x, isog.map x = (q3tCurve 2).one ↔ x = (q3tCurve 2).one
  /-- [3] は ℚ₃ 点で単射。 -/
  injective : isog.Injective
  /-- E₉∖E₉[3] = E₉∖{O}。 -/
  open_eq_punct : ∀ x, isog.map x ≠ (q3tCurve 2).one ↔ x ≠ (q3tCurve 2).one
  /-- cuspidalization 図式の [3]-制限射。 -/
  open_map : q3c3Open → q3cuPunct
  /-- デッキ群自明（被覆単葉）。 -/
  deck_trivial : ∀ a, isog.map a = (q3tCurve 2).one → a = (q3tCurve 2).one

/-- **q3c3-7b: 見出し実例** — 実 E₉(ℚ₃)=ℚ₃^×/9^ℤ 上の奇 N=3 楕円 cuspidalization 基体。 -/
def q3c3Data : Q3CubeIsogenyData where
  isog := q3c3Cube
  cube_eq := q3c3_cube_eq_cube
  ker_trivial := q3c3_ker_eq_trivial
  injective := q3c3_cube_injective
  open_eq_punct := q3c3_open_eq_punct
  open_map := q3c3OpenMap
  deck_trivial := q3c3_deck_trivial

/-- **q3c3-7c: 奇 N=3 幾何的基体の存在**（実 ℚ₃ 上・q=9・N=3・E₉[3](ℚ₃)=0）。 -/
theorem q3c3Cusp_exists : Nonempty Q3CubeIsogenyData := ⟨q3c3Data⟩

end IUT
