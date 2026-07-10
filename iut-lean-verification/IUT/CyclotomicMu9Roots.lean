/-
  IUT/CyclotomicMu9Roots.lean — W-C/CM9 残欠（9 乗根の全射性と構成的指標抽出）

  ── 分類 **[実／本物建設(b)]**（本物の先行建設。実 NF 担体 `GefNF cpdPhi9 6`
     ＝ ℚ(ζ_9) の第二表示の上で、「y⁹ = 1 ⟹ y は x̄₉ の冪のいずれか」
     （μ_9 の全射性）と、その指標 a を choice-free に抽出する `cm9Find` を
     本物に完全証明する。骨格・模型・代理・toy 主語なし・sorry 皆無・
     新規 Classical.choice 皆無）。

  **complete_pct 影響**: A3（円分塔 res₁ = CR39）への承認済み足場(c)。
  CyclotomicMu9（cm9）で確立した「x̄₉⁹ = 1・位数 9・冪 9 個相異」に対し、本
  ファイルは逆向き＝**9 乗根群の全射性** μ_9(ℚ(ζ_9)) = ⟨x̄₉⟩ を、体上多項式の
  根数上界 `prc_roots_le_degree`（X⁹−1 の根は高々 9 個）と choice-free な等号
  判定 `cm9rEq`（`qIsZero` の 6 係数連言）で閉じる。これで制限準同型 res の
  σ(x̄₉) = x̄₉^a の指標 a を **構成的に** 取り出す土台（`cm9Find`）が立つ。
  本ファイル単体では complete_pct 未設定（W-C 本体＝CR39 で反映・独立監査確定）。

  内容:
   * `cm9K`               — 体 K = ℚ(ζ_9) = ℚ[x]/(Φ_9)（`gefNF268`・Field268）。
   * `cm9rX9m1K`          — K 係数の X⁹ − 1（定数 −1・9 次係数 1）。
   * `cm9r_eval`          — ev_y(X⁹−1)|_{10} = y⁹ − 1（一点集中和 rsum_single）。
   * `cm9r_y_is_root`     — y⁹ = 1 ⟹ y は X⁹−1 の根（prcIsRoot）。
   * `cm9r_pow_is_root`   — x̄₉^a は X⁹−1 の根（rpow(x̄₉^a)⁹ = 1）。
   * `cm9rEq / cm9rEq_iff`— NF 担体の等号 Bool 判定（qIsZero の 6 係数連言・choice-free）。
   * `cm9r_scan`          — 有限走査による決定 Or（∃ a<n 一致 ∨ ∀ a<n 不一致）。
   * `cm9_root_in_powers` — **本丸**: y⁹ = 1 ⟹ ∃ a<9, y = x̄₉^a
                            （10 要素相異リストで prc_roots_le_degree の 10 ≤ 9 矛盾）。
   * `cm9Find / cm9Find_spec` — 構成的指標抽出（下から走査・最初の一致 a）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   - **本物**: 全定理は実 NF 担体上の本物の等式・存在・不等式。X⁹−1 は実 K 係数
     多項式で、根は実評価準同型 evalSum で判定する。模型・代理なし。
   - **部分ケースであること（消さない）**: p = 3・円分塔 2 段目（ℚ(ζ_9)）の
     9 乗根群の全射性と指標抽出のみ。制限準同型 res の compat・群準同型性・
     σ の存在自体は CR39（W-C 本体）の射程であり本ファイルに含めない。
   - 等号判定 `cm9rEq` は「6 係数（deg < 6）の qIsZero 連言」＝ GefNF 担体の
     .val 係数の choice-free 一致判定で、6 以上の係数は担体有界性で自動一致。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/
  dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.CyclotomicMu9
import IUT.PolyRootCount
import IUT.PolyLeadFindQ
import IUT.EvaluationHom
import IUT.Composition
import IUT.LubinTateZp

namespace IUT

/-! ## CM9R-0: 体 K = ℚ(ζ_9) と多項式 X⁹ − 1 -/

/-- **CM9R-0a: 体 K = ℚ(ζ_9) = ℚ[x]/(Φ_9)**（Field268・`gefNF268`）。
    その担体環 `cm9K.ring` は `cm9R`（＝ `gefNFRing cpdPhi9 6 …`）に定義等値。 -/
def cm9K : Field268 :=
  gefNF268 cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead (by omega) p9i_irreducible

/-- **CM9R-0b: K 係数の X⁹ − 1** — 9 次係数 1・定数 −1。 -/
def cm9rX9m1K : PS cm9K.ring :=
  psAdd cm9K.ring (psSingle cm9K.ring cm9K.ring.one 9)
    (psC cm9K.ring (cm9K.ring.neg cm9K.ring.one))

/-- **CM9R-0c: X⁹ − 1 は 10 有界**（deg 9）。 -/
theorem cm9rX9m1K_bound : IsPolyBounded cm9K.ring cm9rX9m1K 10 := by
  intro j hj
  show cm9K.ring.add (psSingle cm9K.ring cm9K.ring.one 9 j)
      (psC cm9K.ring (cm9K.ring.neg cm9K.ring.one) j) = cm9K.ring.zero
  rw [show psSingle cm9K.ring cm9K.ring.one 9 j = cm9K.ring.zero from if_neg (by omega),
    show psC cm9K.ring (cm9K.ring.neg cm9K.ring.one) j = cm9K.ring.zero from if_neg (by omega),
    cm9K.ring.zero_add]

/-- **CM9R-0d: X⁹ − 1 の先頭係数（9 次）= 1**。 -/
theorem cm9rX9m1K_lead : cm9rX9m1K 9 = cm9K.ring.one := by
  show cm9K.ring.add (psSingle cm9K.ring cm9K.ring.one 9 9)
      (psC cm9K.ring (cm9K.ring.neg cm9K.ring.one) 9) = cm9K.ring.one
  rw [show psSingle cm9K.ring cm9K.ring.one 9 9 = cm9K.ring.one from if_pos rfl,
    show psC cm9K.ring (cm9K.ring.neg cm9K.ring.one) 9 = cm9K.ring.zero from if_neg (by omega),
    CRing.add_zero cm9K.ring]

/-- **CM9R-0e: K の非自明性** 1 ≠ 0（`gnf_zero_ne_one` の Φ_9 実例）。 -/
theorem cm9r_one_ne_zero : cm9K.ring.one ≠ cm9K.ring.zero :=
  gnf_zero_ne_one cpdPhi9 6 cpdPhi9_bound p9e_phi9_lead (by omega)

/-- **CM9R-0f: 先頭係数 ≠ 0**（root 数上界の入力）。 -/
theorem cm9rX9m1K_lead_ne : cm9rX9m1K 9 ≠ cm9K.ring.zero := by
  rw [cm9rX9m1K_lead]
  exact cm9r_one_ne_zero

/-! ## CM9R-1: 評価 ev_y(X⁹ − 1) = y⁹ − 1 -/

/-- **CM9R-1: 評価値** — ev_y(X⁹ − 1)|_{10} = y⁹ + (−1)。加法保存 `evalHom_add`
    で単項式 X⁹ と定数 −1 に分け、各を一点集中和 `rsum_single` で潰す。 -/
theorem cm9r_eval (y : cm9K.ring.carrier) :
    evalSum (evalHomId cm9K.ring) y cm9rX9m1K 10
      = cm9K.ring.add (rpow cm9K.ring y 9) (cm9K.ring.neg cm9K.ring.one) := by
  have hp1 : evalSum (evalHomId cm9K.ring) y (psSingle cm9K.ring cm9K.ring.one 9) 10
      = rpow cm9K.ring y 9 := by
    rw [evalSum_id,
      rsum_single cm9K.ring _ 9 10 (by omega) (fun j hj hjne => by
        show cm9K.ring.mul (psSingle cm9K.ring cm9K.ring.one 9 j) (rpow cm9K.ring y j)
          = cm9K.ring.zero
        rw [show psSingle cm9K.ring cm9K.ring.one 9 j = cm9K.ring.zero from if_neg hjne,
          CRing.zero_mul cm9K.ring])]
    show cm9K.ring.mul (psSingle cm9K.ring cm9K.ring.one 9 9) (rpow cm9K.ring y 9)
      = rpow cm9K.ring y 9
    rw [show psSingle cm9K.ring cm9K.ring.one 9 9 = cm9K.ring.one from if_pos rfl,
      cm9K.ring.one_mul (rpow cm9K.ring y 9)]
  have hp2 : evalSum (evalHomId cm9K.ring) y
        (psC cm9K.ring (cm9K.ring.neg cm9K.ring.one)) 10
      = cm9K.ring.neg cm9K.ring.one := by
    rw [evalSum_id,
      rsum_single cm9K.ring _ 0 10 (by omega) (fun j hj hjne => by
        show cm9K.ring.mul (psC cm9K.ring (cm9K.ring.neg cm9K.ring.one) j) (rpow cm9K.ring y j)
          = cm9K.ring.zero
        rw [show psC cm9K.ring (cm9K.ring.neg cm9K.ring.one) j = cm9K.ring.zero from if_neg hjne,
          CRing.zero_mul cm9K.ring])]
    show cm9K.ring.mul (psC cm9K.ring (cm9K.ring.neg cm9K.ring.one) 0) (rpow cm9K.ring y 0)
      = cm9K.ring.neg cm9K.ring.one
    rw [show psC cm9K.ring (cm9K.ring.neg cm9K.ring.one) 0 = cm9K.ring.neg cm9K.ring.one
        from if_pos rfl,
      show rpow cm9K.ring y 0 = cm9K.ring.one from rfl,
      CRing.mul_one cm9K.ring]
  rw [show cm9rX9m1K = psAdd cm9K.ring (psSingle cm9K.ring cm9K.ring.one 9)
        (psC cm9K.ring (cm9K.ring.neg cm9K.ring.one)) from rfl,
    evalHom_add (evalHomId cm9K.ring) y (psSingle cm9K.ring cm9K.ring.one 9)
      (psC cm9K.ring (cm9K.ring.neg cm9K.ring.one)) 10, hp1, hp2]

/-! ## CM9R-2: y⁹ = 1 は X⁹ − 1 の根 -/

/-- **CM9R-2a: 一般の 9 乗根は X⁹ − 1 の根** — y⁹ = 1 ⟹ prcIsRoot。 -/
theorem cm9r_y_is_root (y : cm9K.ring.carrier)
    (hy : rpow cm9K.ring y 9 = cm9K.ring.one) :
    prcIsRoot cm9K cm9rX9m1K y := by
  apply prc_root_of_eval cm9K cm9rX9m1K y 10 cm9rX9m1K_bound
  rw [cm9r_eval y, hy]
  exact CRing.add_neg cm9K.ring cm9K.ring.one

/-! ## CM9R-3: x̄₉^a の 9 乗 = 1（rpow の準同型連鎖） -/

/-- **CM9R-3a: rpow(x̄₉^a) = x̄₉^{a·m}** — 冪の反復を `cm9Pow_add` で回収。 -/
theorem cm9r_rpow_cm9Pow (a : Nat) : ∀ m,
    rpow cm9K.ring (cm9Pow a) m = cm9Pow (a * m) := by
  intro m
  induction m with
  | zero =>
    show cm9K.ring.one = cm9Pow (a * 0)
    rw [Nat.mul_zero]
    rfl
  | succ m ih =>
    show cm9K.ring.mul (rpow cm9K.ring (cm9Pow a) m) (cm9Pow a) = cm9Pow (a * (m + 1))
    have harith : a * (m + 1) = a * m + a := Nat.mul_succ a m
    rw [ih, harith, cm9Pow_add (a * m) a]
    rfl

/-- **CM9R-3b: x̄₉^{a·9} = 1**（cm9_zeta_pow9 を a 回反復）。 -/
theorem cm9r_pow_mul9 (a : Nat) : cm9Pow (a * 9) = cm9K.ring.one := by
  induction a with
  | zero =>
    show cm9Pow (0 * 9) = cm9K.ring.one
    rw [Nat.zero_mul]
    rfl
  | succ a ih =>
    show cm9Pow ((a + 1) * 9) = cm9K.ring.one
    have harith : (a + 1) * 9 = a * 9 + 9 := Nat.succ_mul a 9
    rw [harith, cm9Pow_add (a * 9) 9, ih, cm9_zeta_pow9]
    exact cm9K.ring.one_mul cm9K.ring.one

/-- **CM9R-3c: (x̄₉^a)⁹ = 1**（3a + 3b の合成）。 -/
theorem cm9r_rpow_pow9 (a : Nat) : rpow cm9K.ring (cm9Pow a) 9 = cm9K.ring.one := by
  rw [cm9r_rpow_cm9Pow a 9]
  exact cm9r_pow_mul9 a

/-- **CM9R-3d: x̄₉^a は X⁹ − 1 の根**。 -/
theorem cm9r_pow_is_root (a : Nat) : prcIsRoot cm9K cm9rX9m1K (cm9Pow a) := by
  apply cm9r_y_is_root
  exact cm9r_rpow_pow9 a

/-! ## CM9R-4: NF 担体の等号 Bool 判定（choice-free） -/

/-- **CM9R-4a: 担体等号 Bool 判定** — deg < 6 の 6 係数について
    qIsZero(u_j − v_j) を連言する（`qIsZero` は choice-free）。 -/
def cm9rEq (u v : GefNF cpdPhi9 6) : Bool :=
  qIsZero (ratRing.add (u.val 0) (ratRing.neg (v.val 0)))
    && qIsZero (ratRing.add (u.val 1) (ratRing.neg (v.val 1)))
    && qIsZero (ratRing.add (u.val 2) (ratRing.neg (v.val 2)))
    && qIsZero (ratRing.add (u.val 3) (ratRing.neg (v.val 3)))
    && qIsZero (ratRing.add (u.val 4) (ratRing.neg (v.val 4)))
    && qIsZero (ratRing.add (u.val 5) (ratRing.neg (v.val 5)))

/-- **CM9R-4b: 1 係数の同値** — qIsZero(u_j − v_j) = true ⟺ u_j = v_j
    （`qIsZero_iff` + `eq_of_sub_eq_zero` / `add_neg`）。 -/
theorem cm9r_coord_iff (u v : GefNF cpdPhi9 6) (j : Nat) :
    qIsZero (ratRing.add (u.val j) (ratRing.neg (v.val j))) = true ↔ u.val j = v.val j := by
  rw [qIsZero_iff]
  apply Iff.intro
  · intro h
    exact CRing.eq_of_sub_eq_zero ratRing h
  · intro h
    rw [h]
    exact CRing.add_neg ratRing (v.val j)

/-- **CM9R-4c: 判定の特徴付け** — cm9rEq u v = true ⟺ u = v。
    forward は 6 連言を `Bool.and_eq_true` で分解し各係数の一致（4b）＋担体有界性
    （deg ≥ 6 は両者 0）で Subtype.ext。backward は各 u_j − u_j = 0。 -/
theorem cm9rEq_iff (u v : GefNF cpdPhi9 6) : cm9rEq u v = true ↔ u = v := by
  apply Iff.intro
  · intro h
    have h6 : (qIsZero (ratRing.add (u.val 0) (ratRing.neg (v.val 0)))
        && qIsZero (ratRing.add (u.val 1) (ratRing.neg (v.val 1)))
        && qIsZero (ratRing.add (u.val 2) (ratRing.neg (v.val 2)))
        && qIsZero (ratRing.add (u.val 3) (ratRing.neg (v.val 3)))
        && qIsZero (ratRing.add (u.val 4) (ratRing.neg (v.val 4)))
        && qIsZero (ratRing.add (u.val 5) (ratRing.neg (v.val 5)))) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true] at h6
    obtain ⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩ := h6
    apply Subtype.ext
    funext j
    cases Nat.lt_or_ge j 6 with
    | inr hge =>
      rw [u.property j hge, v.property j hge]
    | inl hlt =>
      have d0 := (cm9r_coord_iff u v 0).mp e0
      have d1 := (cm9r_coord_iff u v 1).mp e1
      have d2 := (cm9r_coord_iff u v 2).mp e2
      have d3 := (cm9r_coord_iff u v 3).mp e3
      have d4 := (cm9r_coord_iff u v 4).mp e4
      have d5 := (cm9r_coord_iff u v 5).mp e5
      cases j with
      | zero => exact d0
      | succ j => cases j with
        | zero => exact d1
        | succ j => cases j with
          | zero => exact d2
          | succ j => cases j with
            | zero => exact d3
            | succ j => cases j with
              | zero => exact d4
              | succ j => cases j with
                | zero => exact d5
                | succ j => exact absurd hlt (by omega)
  · intro h
    subst h
    have hz : ∀ k, qIsZero (ratRing.add (u.val k) (ratRing.neg (u.val k))) = true := by
      intro k
      rw [CRing.add_neg ratRing (u.val k)]
      exact (qIsZero_iff ratRing.zero).mpr rfl
    show (qIsZero (ratRing.add (u.val 0) (ratRing.neg (u.val 0)))
        && qIsZero (ratRing.add (u.val 1) (ratRing.neg (u.val 1)))
        && qIsZero (ratRing.add (u.val 2) (ratRing.neg (u.val 2)))
        && qIsZero (ratRing.add (u.val 3) (ratRing.neg (u.val 3)))
        && qIsZero (ratRing.add (u.val 4) (ratRing.neg (u.val 4)))
        && qIsZero (ratRing.add (u.val 5) (ratRing.neg (u.val 5)))) = true
    rw [hz 0, hz 1, hz 2, hz 3, hz 4, hz 5]
    rfl

/-! ## CM9R-5: 冪リストと相異・根 -/

/-- **CM9R-5a: 冪のリスト** [x̄₉^{n−1}, …, x̄₉^0]（長さ n）。 -/
def cm9rPows : Nat → List (GefNF cpdPhi9 6)
  | 0 => []
  | k + 1 => cm9Pow k :: cm9rPows k

/-- 長さは n。 -/
theorem cm9rPows_len (n : Nat) : (cm9rPows n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (cm9Pow n :: cm9rPows n).length = n + 1
    rw [List.length_cons, ih]

/-- 所属 ⟹ 冪指標の存在。 -/
theorem cm9rPows_mem (n : Nat) (x : GefNF cpdPhi9 6) (hx : x ∈ cm9rPows n) :
    ∃ a, a < n ∧ x = cm9Pow a := by
  induction n with
  | zero =>
    have hnil : x ∈ ([] : List (GefNF cpdPhi9 6)) := hx
    exact absurd hnil List.not_mem_nil
  | succ n ih =>
    have hx' : x ∈ cm9Pow n :: cm9rPows n := hx
    cases List.mem_cons.mp hx' with
    | inl he => exact ⟨n, by omega, he⟩
    | inr hm =>
      obtain ⟨a, ha, hae⟩ := ih hm
      exact ⟨a, by omega, hae⟩

/-- **CM9R-5b: 冪リストは相異** — 位数 9（`cm9_powers_distinct`）から。 -/
theorem cm9rPows_distinct : ∀ n, n ≤ 9 → prcDistinct (cm9rPows n) := by
  intro n
  induction n with
  | zero => intro _; exact True.intro
  | succ n ih =>
    intro hn
    show prcDistinct (cm9Pow n :: cm9rPows n)
    refine ⟨fun x hx => ?_, ih (by omega)⟩
    obtain ⟨a, ha, hae⟩ := cm9rPows_mem n x hx
    rw [hae]
    exact cm9_powers_distinct a n (by omega) (by omega) (by omega)

/-- **CM9R-5c: 冪リストの各元は X⁹ − 1 の根**。 -/
theorem cm9rPows_roots (n : Nat) (x : GefNF cpdPhi9 6) (hx : x ∈ cm9rPows n) :
    prcIsRoot cm9K cm9rX9m1K x := by
  obtain ⟨a, ha, hae⟩ := cm9rPows_mem n x hx
  rw [hae]
  exact cm9r_pow_is_root a

/-! ## CM9R-6: 有限走査による決定 Or -/

/-- **CM9R-6: 決定 Or** — [0, n) の中に y = x̄₉^a となる a が在るか否かを
    choice-free に決定する（`cm9rEq` の Bool 分岐で n 帰納）。 -/
theorem cm9r_scan (y : GefNF cpdPhi9 6) : ∀ n,
    (∃ a, a < n ∧ y = cm9Pow a) ∨ (∀ a, a < n → y ≠ cm9Pow a) := by
  intro n
  induction n with
  | zero => exact Or.inr (fun a ha => absurd ha (by omega))
  | succ n ih =>
    cases ih with
    | inl h =>
      obtain ⟨a, ha, hae⟩ := h
      exact Or.inl ⟨a, by omega, hae⟩
    | inr hno =>
      cases hb : cm9rEq y (cm9Pow n) with
      | true =>
        exact Or.inl ⟨n, by omega, (cm9rEq_iff y (cm9Pow n)).mp hb⟩
      | false =>
        refine Or.inr (fun a ha => ?_)
        cases Nat.lt_or_ge a n with
        | inl hlt => exact hno a hlt
        | inr hge =>
          have han : a = n := by omega
          rw [han]
          intro hyeq
          have hcon : cm9rEq y (cm9Pow n) = true := (cm9rEq_iff y (cm9Pow n)).mpr hyeq
          rw [hb] at hcon
          exact Bool.noConfusion hcon

/-! ## CM9R-7: 本丸 — 9 乗根はすべて x̄₉ の冪 -/

/-- **CM9R-7（本丸）: μ_9 の全射性** — y⁹ = 1 ⟹ ∃ a < 9, y = x̄₉^a。
    走査で不一致なら S = [y, x̄₉^0, …, x̄₉^8]（長さ 10）は相異な根 10 個となり、
    次数 9 の X⁹−1 に対し `prc_roots_le_degree` の 10 ≤ 9 で矛盾。 -/
theorem cm9_root_in_powers (y : cm9K.ring.carrier)
    (hy : rpow cm9K.ring y 9 = cm9K.ring.one) :
    ∃ a, a < 9 ∧ y = cm9Pow a := by
  cases cm9r_scan y 9 with
  | inl h => exact h
  | inr hno =>
    exfalso
    have hlen : (y :: cm9rPows 9).length = 10 := by
      have h1 : (y :: cm9rPows 9).length = (cm9rPows 9).length + 1 :=
        List.length_cons
      have h2 : (cm9rPows 9).length = 9 := cm9rPows_len 9
      omega
    have hroots : ∀ r, r ∈ (y :: cm9rPows 9) → prcIsRoot cm9K cm9rX9m1K r := by
      intro r hr
      cases List.mem_cons.mp hr with
      | inl he =>
        rw [he]
        exact cm9r_y_is_root y hy
      | inr hm => exact cm9rPows_roots 9 r hm
    have hdist : prcDistinct (y :: cm9rPows 9) := by
      refine ⟨fun x hx => ?_, cm9rPows_distinct 9 (by omega)⟩
      obtain ⟨a, ha, hae⟩ := cm9rPows_mem 9 x hx
      rw [hae]
      intro hcon
      exact hno a ha hcon.symm
    have hbound : IsPolyBounded cm9K.ring cm9rX9m1K (9 + 1) := cm9rX9m1K_bound
    have hle : (y :: cm9rPows 9).length ≤ 9 :=
      prc_roots_le_degree cm9K 9 cm9rX9m1K hbound cm9rX9m1K_lead_ne
        (y :: cm9rPows 9) hroots hdist
    rw [hlen] at hle
    omega

/-! ## CM9R-8: 構成的指標抽出 cm9Find -/

/-- **CM9R-8a: 下からの走査** — 位置 i から fuel 段、最初に cm9rEq が真になる
    位置を返す（無ければ i + fuel）。 -/
def cm9FindGo (y : GefNF cpdPhi9 6) : Nat → Nat → Nat
  | i, 0 => i
  | i, fuel + 1 => if cm9rEq y (cm9Pow i) then i else cm9FindGo y (i + 1) fuel

/-- **CM9R-8b: 指標抽出** — 0 から 9 段走査（見つからねば 9）。 -/
def cm9Find (y : GefNF cpdPhi9 6) : Nat := cm9FindGo y 0 9

/-- 走査結果の上界 cm9FindGo y i fuel ≤ i + fuel。 -/
theorem cm9FindGo_le (y : GefNF cpdPhi9 6) : ∀ fuel i,
    cm9FindGo y i fuel ≤ i + fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro i
    show i ≤ i + 0
    omega
  | succ fuel ih =>
    intro i
    cases hb : cm9rEq y (cm9Pow i) with
    | true =>
      have he : cm9FindGo y i (fuel + 1) = i := by
        show (if cm9rEq y (cm9Pow i) then i else cm9FindGo y (i + 1) fuel) = i
        rw [if_pos hb]
      rw [he]
      omega
    | false =>
      have he : cm9FindGo y i (fuel + 1) = cm9FindGo y (i + 1) fuel := by
        show (if cm9rEq y (cm9Pow i) then i else cm9FindGo y (i + 1) fuel)
          = cm9FindGo y (i + 1) fuel
        rw [if_neg (by rw [hb]; exact fun hh => Bool.noConfusion hh)]
      rw [he]
      have hih := ih (i + 1)
      omega

/-- **CM9R-8c: 走査は範囲内の一致を捕まえる** — [i, i+fuel) に一致が在れば、
    返す位置は一致かつ範囲内。fuel 帰納（i で一致なら停止、さもなくば i+1 へ）。 -/
theorem cm9FindGo_hit (y : GefNF cpdPhi9 6) : ∀ fuel i,
    (∃ a, i ≤ a ∧ a < i + fuel ∧ cm9rEq y (cm9Pow a) = true) →
    cm9rEq y (cm9Pow (cm9FindGo y i fuel)) = true ∧ cm9FindGo y i fuel < i + fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro i h
    obtain ⟨a, ha1, ha2, _⟩ := h
    exfalso
    omega
  | succ fuel ih =>
    intro i h
    cases hb : cm9rEq y (cm9Pow i) with
    | true =>
      have he : cm9FindGo y i (fuel + 1) = i := by
        show (if cm9rEq y (cm9Pow i) then i else cm9FindGo y (i + 1) fuel) = i
        rw [if_pos hb]
      rw [he]
      refine ⟨hb, ?_⟩
      clear h ih
      omega
    | false =>
      have he : cm9FindGo y i (fuel + 1) = cm9FindGo y (i + 1) fuel := by
        show (if cm9rEq y (cm9Pow i) then i else cm9FindGo y (i + 1) fuel)
          = cm9FindGo y (i + 1) fuel
        rw [if_neg (by rw [hb]; exact fun hh => Bool.noConfusion hh)]
      rw [he]
      obtain ⟨a, ha1, ha2, ha3⟩ := h
      have hane : a ≠ i := by
        intro hai
        rw [hai, hb] at ha3
        exact Bool.noConfusion ha3
      obtain ⟨hr1, hr2⟩ := ih (i + 1) ⟨a, by omega, by omega, ha3⟩
      exact ⟨hr1, by omega⟩

/-- **CM9R-8d: cm9Find の範囲** — cm9Find y < 9 ∨ cm9Find y = 9。 -/
theorem cm9Find_lt (y : GefNF cpdPhi9 6) : cm9Find y < 9 ∨ cm9Find y = 9 := by
  have h := cm9FindGo_le y 9 0
  show cm9FindGo y 0 9 < 9 ∨ cm9FindGo y 0 9 = 9
  omega

/-- **CM9R-8e: 抽出の仕様** — y⁹ = 1 ⟹ y = x̄₉^{cm9Find y} かつ cm9Find y < 9。
    全射性（7）で一致 a を得、走査がそれを捕まえる（8c）。 -/
theorem cm9Find_spec (y : cm9K.ring.carrier)
    (hy : rpow cm9K.ring y 9 = cm9K.ring.one) :
    y = cm9Pow (cm9Find y) ∧ cm9Find y < 9 := by
  obtain ⟨a, ha, hae⟩ := cm9_root_in_powers y hy
  have hmatch : cm9rEq y (cm9Pow a) = true := (cm9rEq_iff y (cm9Pow a)).mpr hae
  have hhit := cm9FindGo_hit y 9 0 ⟨a, by omega, by omega, hmatch⟩
  show y = cm9Pow (cm9FindGo y 0 9) ∧ cm9FindGo y 0 9 < 9
  refine ⟨(cm9rEq_iff y (cm9Pow (cm9FindGo y 0 9))).mp hhit.1, ?_⟩
  have hlt := hhit.2
  omega

end IUT
