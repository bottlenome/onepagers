/-
  IUT/Q3TateTorsion.lean — A8b（柱A A8: 実 Tate 曲線 E₉(ℚ₃) の 2-捻れ E₉[2]）

  ── 主要成果の分類: **[実／昇格(a)]**。M314F `TateTorsion.lean` の **2 つの外部仮定**
     — (i) q の n 乗根 w を「wⁿ=q の witness で受け取る」・(ii) 位数言明
     `tateTorQrootOrder` が付値 v を「外部入力」で受け取る — を、実 ℚ₃ の上で
     **実 witness と実算術で discharge** する。q = q3tQ 2（= 3² = 9・実付値 v(q)=2・
     q3t 昇格済み）を主語に、2 乗根 **w = 3 が体拡大なしで ℚ₃ 内に実在**（w²=q=9・
     q3tt_w_sq）し、その E₉ 上の類 [w] の**位数がちょうど 2**（q3tt_w_order・外部付値
     仮定なし・quotientProjN_ker と第1成分の実 Int 算術で閉じる）ことを完全証明する。
     さらに実 μ₂ = {±1} ⊂ ℤ₃^×（q3tNegOne・(−1)²=1・−1≠1）を捻れ点として実現し、
     **Klein 4 群 {[1],[3],[−1],[−3]} ⊆ E₉[2]（4 点相異・積閉）を実構成**する。
     toy 主語なし——主語は実 q3tGrp = QpUnits 3（実 ℚ₃^× の群提示）・実 q3tCurve 2・
     実 q3tNegOne（実 −1 ∈ ℤ₃^×）。

  complete_pct 影響: **A8 A8b を前進**（設計 `audit/A8-real-tate-curve-detail-2026-07-10.md`
  §4 見込み A8 0.55→0.6・A8a と合わせ柱A 46→47・独立監査確定が条件）。内容:
  (i)   実 2 乗根 w=3・w²=q=9（q3tt_w_sq）——M314F「w は witness」の実 discharge、
  (ii)  [w]²=[q]=[1]（q3tt_w_torsion）、
  (iii) [w] の**実位数ちょうど 2**（q3tt_w_order: 外部付値仮定なし・射影核と 2t=k・omega）
        ——M314F `tateTorQrootOrder` の「付値 v を外部入力」を実 ℚ₃ 上で discharge、
  (iv)  実 μ₂={±1} の捻れ点 [−1]（q3ttMuPoint・q3tt_mu_torsion・q3tt_mu_ne_one）、
  (v)   類分離補題 q3tt_class_eq_iff（[k,u]=[k',u'] ⟺ 2∣(k'−k) ∧ u=u'）、
  (vi)  **Klein 4 群 ⊆ E₉[2]**（q3tt_klein_distinct: 4 点相異・q3tt_klein_closed: 積閉・
        q3tt_klein_torsion: 各点 2-捻れ）、
  (vii) 束ね q3ttData。

  正直な限定（§3 準拠・消去/弱化しない・既存 surrogate は消さない）:
  1. E_q の担体は**群提示 3^ℤ×ℤ₃^×**（q3uEmbed 単射同定・∃形限定・A2 継承）。q3t の限定を継承。
  2. **l = 2 のみ**。奇素数 l の E_q[l] は ℚ₃ 有理でない（ζ_l∉ℚ₃（l≠2）・q^{1/l}∉ℚ₃）——
     IUT の l≥5 奇捻れは ℚ₃ の拡大体機構（未建設）の後続。これは「本コースの忠実な部分ケース」。
  3. 群提示は **∃形**（k,u で表示する加法/乗法群）——直積分解 E₉[2]=μ₂×⟨w⟩ の
     **μ₂ の完全性（u²=1 ⟹ u=±1）は stretch/後続**（本ファイルでは未達・等号を主張しない。
     Klein 4 群は E₉[2] への**包含**まで）。
  4. Galois 作用（G_{ℚ₃} の E_q[n] への作用）は皆無（実 G_{ℚ₃} 自体が A2 後続）。
  5. Weierstrass 模型（M304F）との同型・cuspidalization・T_l 皆無（q3t 限定を継承）。
  6. M314F の一般機構（IUTField 上）・既存 TateCover 系は消さず併設（§2(a) 昇格の規約）。
     本ファイルは q3tGrp 上に部分群機構を建て直す（tateTorSubgroup は IUTField 特化のため）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ（Classical.choice 無し）。
-/
import IUT.Q3TateCurve
import IUT.TateTorsion

namespace IUT

/-! ## q3tt-0: 補助 — prodGrp の冪の第1成分算術（実位数の核） -/

/-- q3tGrp の元の自然数冪の第1成分（付値部）: (gⁿ).1 = n·g.1（一般 g・帰納）。 -/
theorem q3t_npow_fst_gen (g : q3tGrp.carrier) : ∀ n : Nat,
    (tateNpow q3tGrp g n).1 = (n : Int) * g.1 := by
  intro n
  induction n with
  | zero =>
    show (0 : Int) = ((0 : Nat) : Int) * g.1
    have h0 : ((0 : Nat) : Int) = (0 : Int) := by omega
    rw [h0, Int.zero_mul]
  | succ k ih =>
    show (tateNpow q3tGrp g k).1 + g.1 = ((k + 1 : Nat) : Int) * g.1
    rw [ih]
    have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [hcast, Int.add_mul, Int.one_mul]

/-- q^ℤ の整数冪 q^t の第1成分（付値部）: (qᵗ).1 = m·t（全整数 t）。
    正冪は q3t_npow_fst、負冪は inv(q) の第1成分 −m から。 -/
theorem q3t_zpow_fst (m : Nat) (t : Int) :
    (tateZpow q3tGrp (q3tQ m) t).1 = (m : Int) * t := by
  cases t with
  | ofNat n =>
    show (tateNpow q3tGrp (q3tQ m) n).1 = (m : Int) * (n : Int)
    exact q3t_npow_fst m n
  | negSucc n =>
    show (tateNpow q3tGrp (q3tGrp.inv (q3tQ m)) (n + 1)).1 = (m : Int) * Int.negSucc n
    rw [q3t_npow_fst_gen (q3tGrp.inv (q3tQ m)) (n + 1), Int.mul_comm]
    show -((m : Nat) : Int) * Int.ofNat (n + 1) = (m : Int) * Int.negSucc n
    exact tateTorNegMul (m : Int) n

/-! ## q3tt-1: ★ 実 2 乗根 witness — w=3, w²=q=9（M314F「w は witness」の実 discharge） -/

/-- **q3tt-1（★）: 実 2 乗根 w=3, w²=q=9** — 第1成分 1+1=2・第2成分 1·1=1。
    M314F `tateTorQrootMem` が「wⁿ=q の w を witness で受け取る」外部仮定を、
    **体拡大なしで ℚ₃ 内に実在する w=3（q3tQ 1）**で実 discharge する。 -/
theorem q3tt_w_sq : q3tGrp.mul (q3tQ 1) (q3tQ 1) = q3tQ 2 := by
  show (intGrp.mul ((1 : Nat) : Int) ((1 : Nat) : Int),
        (zpUnits 3 isPrime_three).mul (zpUnits 3 isPrime_three).one
          (zpUnits 3 isPrime_three).one)
     = (((2 : Nat) : Int), (zpUnits 3 isPrime_three).one)
  have h1 : intGrp.mul ((1 : Nat) : Int) ((1 : Nat) : Int) = ((2 : Nat) : Int) := by
    show ((1 : Nat) : Int) + ((1 : Nat) : Int) = ((2 : Nat) : Int); omega
  have h2 : (zpUnits 3 isPrime_three).mul (zpUnits 3 isPrime_three).one
      (zpUnits 3 isPrime_three).one = (zpUnits 3 isPrime_three).one :=
    (zpUnits 3 isPrime_three).one_mul _
  rw [h1, h2]

/-! ## q3tt-2: ★ [w]=[3] の位数ちょうど 2（外部付値仮定を実算術で置換） -/

/-- **q3tt-2a（★）: [w]²=[q]=[1]** — [3]²=[9]=[q₉]=1（w_sq＋q₉∈q^ℤ で射影が単位）。 -/
theorem q3tt_w_torsion :
    (q3tCurve 2).mul ((q3tProj 2).map (q3tQ 1)) ((q3tProj 2).map (q3tQ 1))
      = (q3tCurve 2).one := by
  rw [← (q3tProj 2).map_mul, q3tt_w_sq]
  exact (quotientProjN_ker q3tGrp (q3tSubgroup 2) (q3t_normal (q3tSubgroup 2))
    (q3tQ 2)).mpr (tate_gen_mem q3tGrp (q3tQ 2))

/-- 射影と冪の可換: proj(gᵏ) = (proj g)ᵏ（帰納）。位数言明の橋。 -/
theorem q3t_proj_npow (m : Nat) (x : q3tGrp.carrier) : ∀ k : Nat,
    (q3tProj m).map (tateNpow q3tGrp x k)
      = tateNpow (q3tCurve m) ((q3tProj m).map x) k := by
  intro k
  induction k with
  | zero => exact (q3tProj m).map_one
  | succ j ih =>
    show (q3tProj m).map (q3tGrp.mul (tateNpow q3tGrp x j) x)
        = (q3tCurve m).mul (tateNpow (q3tCurve m) ((q3tProj m).map x) j) ((q3tProj m).map x)
    rw [(q3tProj m).map_mul, ih]

/-- **q3tt-2b（★・核）: [w]=[3] の実位数はちょうど 2** — [3]ᵏ=1 ⟹ 2∣k。
    **外部付値仮定を一切使わない**——M314F `tateTorQrootOrder` の「付値 v を外部入力」を、
    射影核 quotientProjN_ker（[x]=1 ⟺ x∈q₉^ℤ）と第1成分の実 Int 算術（2t=k・omega）で
    実 ℚ₃ の中で discharge する。q₉=q3tQ 2 の第1成分 v(q₉)=2 が「ちょうど 2」の源。 -/
theorem q3tt_w_order (k : Nat) :
    tateNpow (q3tCurve 2) ((q3tProj 2).map (q3tQ 1)) k = (q3tCurve 2).one → (2 : Nat) ∣ k := by
  intro h
  rw [← q3t_proj_npow 2 (q3tQ 1) k] at h
  have hmem := (quotientProjN_ker q3tGrp (q3tSubgroup 2) (q3t_normal (q3tSubgroup 2))
    (tateNpow q3tGrp (q3tQ 1) k)).mp h
  obtain ⟨t, ht⟩ := hmem
  have hfst : (tateZpow q3tGrp (q3tQ 2) t).1 = (tateNpow q3tGrp (q3tQ 1) k).1 :=
    congrArg Prod.fst ht
  rw [q3t_zpow_fst 2 t, q3t_npow_fst 1 k] at hfst
  have hfst2 : (2 : Int) * t = (1 : Int) * (k : Int) := hfst
  refine ⟨t.toNat, ?_⟩
  omega

/-! ## q3tt-3: ★ 実 μ₂ = {±1} ⊂ ℤ₃^× の 2 捻れ -/

/-- **q3tt-3a: 実 μ₂ 捻れ点 [−1]** — 実 −1 ∈ ℤ₃^×（q3tNegOne）が与える E₉ の点。 -/
def q3ttMuPoint : (q3tCurve 2).carrier := (q3tProj 2).map ((0 : Int), q3tNegOne)

/-- **q3tt-3b（★）: [−1]²=[1]** — (0+0, (−1)·(−1))=(0,1)（q3tNegOne_sq）で単位の類。 -/
theorem q3tt_mu_torsion :
    (q3tCurve 2).mul q3ttMuPoint q3ttMuPoint = (q3tCurve 2).one := by
  show (q3tCurve 2).mul ((q3tProj 2).map ((0 : Int), q3tNegOne))
        ((q3tProj 2).map ((0 : Int), q3tNegOne)) = (q3tCurve 2).one
  rw [← (q3tProj 2).map_mul]
  have hmul : q3tGrp.mul ((0 : Int), q3tNegOne) ((0 : Int), q3tNegOne) = q3tGrp.one := by
    show (intGrp.mul (0 : Int) (0 : Int),
          (zpUnits 3 isPrime_three).mul q3tNegOne q3tNegOne)
       = (intGrp.one, (zpUnits 3 isPrime_three).one)
    have h1 : intGrp.mul (0 : Int) (0 : Int) = intGrp.one := by
      show (0 : Int) + (0 : Int) = (0 : Int); omega
    rw [h1, q3tNegOne_sq]
  rw [hmul]
  exact (q3tProj 2).map_one

/-- **q3tt-3c（★）: [−1]≠[1]** — q^ℤ の元は第2成分 1 なのに (0,−1) は −1
    （q3t_negone_ne_one）。M309F/q3t 退化 witness の質的超克を捻れ側で再確認。 -/
theorem q3tt_mu_ne_one : q3ttMuPoint ≠ (q3tCurve 2).one :=
  q3t_point_ne_one 2 (by omega)

/-! ## q3tt-4: ★ 類の分離補題（4 点の相互区別を一手で閉じる簿記） -/

/-- q3tGrp 上で proj a = proj b ⟺ a⁻¹b ∈ q₉^ℤ（射影核の一般形）。 -/
theorem q3t_proj_eq_iff (m : Nat) (a b : q3tGrp.carrier) :
    (q3tProj m).map a = (q3tProj m).map b ↔
      (q3tSubgroup m).mem (q3tGrp.mul (q3tGrp.inv a) b) := by
  constructor
  · intro h
    have key : (q3tProj m).map (q3tGrp.mul (q3tGrp.inv a) b) = (q3tCurve m).one := by
      rw [(q3tProj m).map_mul, (q3tProj m).map_inv, h, (q3tCurve m).inv_mul]
    exact (quotientProjN_ker q3tGrp (q3tSubgroup m) (q3t_normal (q3tSubgroup m))
      (q3tGrp.mul (q3tGrp.inv a) b)).mp key
  · intro hmem
    have h1 : (q3tProj m).map (q3tGrp.mul (q3tGrp.inv a) b) = (q3tCurve m).one :=
      (quotientProjN_ker q3tGrp (q3tSubgroup m) (q3t_normal (q3tSubgroup m))
        (q3tGrp.mul (q3tGrp.inv a) b)).mpr hmem
    rw [(q3tProj m).map_mul, (q3tProj m).map_inv] at h1
    have h2 := (q3tCurve m).inv_eq_of_mul_eq_one h1
    rw [(q3tCurve m).inv_inv] at h2
    exact h2.symm

/-- q₉^ℤ 部分群への所属の成分特徴付け: (c,v) ∈ q₉^ℤ ⟺ 2∣c ∧ v=1。
    第1成分 2t（q3t_zpow_fst）・第2成分 1（q3t_zpow_snd）が核。 -/
theorem q3t_mem_pair_iff (m : Nat) (c : Int) (v : (zpUnits 3 isPrime_three).carrier) :
    (q3tSubgroup m).mem (c, v) ↔ (m : Int) ∣ c ∧ v = (zpUnits 3 isPrime_three).one := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h
    have hfst : (tateZpow q3tGrp (q3tQ m) t).1 = c := congrArg Prod.fst ht
    have hsnd : (tateZpow q3tGrp (q3tQ m) t).2 = v := congrArg Prod.snd ht
    rw [q3t_zpow_fst m t] at hfst
    rw [q3t_zpow_snd m t] at hsnd
    exact ⟨⟨t, hfst.symm⟩, hsnd.symm⟩
  · intro hcv
    obtain ⟨⟨t, ht⟩, hv⟩ := hcv
    refine ⟨t, ?_⟩
    have e1 : (tateZpow q3tGrp (q3tQ m) t).1 = c := by rw [q3t_zpow_fst m t]; exact ht.symm
    have e2 : (tateZpow q3tGrp (q3tQ m) t).2 = v := by rw [q3t_zpow_snd m t, hv]
    rw [show (tateZpow q3tGrp (q3tQ m) t)
        = ((tateZpow q3tGrp (q3tQ m) t).1, (tateZpow q3tGrp (q3tQ m) t).2) from rfl, e1, e2]

/-- 単数部の分離: (inv u)·u' = 1 ⟺ u = u'。 -/
theorem q3t_invmul_eq_one_iff (u u' : (zpUnits 3 isPrime_three).carrier) :
    (zpUnits 3 isPrime_three).mul ((zpUnits 3 isPrime_three).inv u) u'
      = (zpUnits 3 isPrime_three).one ↔ u = u' := by
  constructor
  · intro h
    have h2 := (zpUnits 3 isPrime_three).inv_eq_of_mul_eq_one h
    rw [(zpUnits 3 isPrime_three).inv_inv] at h2
    exact h2.symm
  · intro h
    rw [h]
    exact (zpUnits 3 isPrime_three).inv_mul u'

/-- **q3tt-4（★）: 類分離** — E₉ の点 [k,u]=[k',u'] ⟺ **2∣(k'−k) かつ u=u'**。
    付値方向（2 で割る＝q₉=3² の周期）と単数方向（μ₂）の**直交**を一手で与える簿記。
    4 点相異（Klein 4 群）の証明を一様に閉じる。 -/
theorem q3tt_class_eq_iff (k k' : Int) (u u' : (zpUnits 3 isPrime_three).carrier) :
    (q3tProj 2).map (k, u) = (q3tProj 2).map (k', u') ↔
      ((2 : Int) ∣ (k' - k)) ∧ u = u' := by
  rw [q3t_proj_eq_iff 2 (k, u) (k', u')]
  have hpair : q3tGrp.mul (q3tGrp.inv (k, u)) (k', u')
      = (-k + k', (zpUnits 3 isPrime_three).mul ((zpUnits 3 isPrime_three).inv u) u') := rfl
  rw [hpair, q3t_mem_pair_iff 2 (-k + k')
    ((zpUnits 3 isPrime_three).mul ((zpUnits 3 isPrime_three).inv u) u'),
    q3t_invmul_eq_one_iff u u']
  have h2c : ((2 : Nat) : Int) = (2 : Int) := by omega
  have hd : (-k + k') = (k' - k) := by omega
  rw [h2c, hd]

/-! ## q3tt-5: ★ Klein 4 群 {[1],[3],[−1],[−3]} ⊆ E₉[2] -/

/-- Klein 4 群の担体述語: [k, u]（u ∈ {±1}）の類。E₉[2] の ℚ₃ 有理部分（∃形群提示）。 -/
def q3ttKleinMem (x : (q3tCurve 2).carrier) : Prop :=
  ∃ (k : Int) (u : (zpUnits 3 isPrime_three).carrier),
    (u = (zpUnits 3 isPrime_three).one ∨ u = q3tNegOne)
      ∧ x = (q3tProj 2).map (k, u)

/-- proj の積は成分ごと: [k,u]·[k',u'] = [k+k', u·u']（map_mul と prodGrp の成分算術）。 -/
theorem q3tt_proj_mul (k k' : Int) (u u' : (zpUnits 3 isPrime_three).carrier) :
    (q3tCurve 2).mul ((q3tProj 2).map (k, u)) ((q3tProj 2).map (k', u'))
      = (q3tProj 2).map (k + k', (zpUnits 3 isPrime_three).mul u u') := by
  rw [← (q3tProj 2).map_mul]
  rfl

/-- **q3tt-5a（★）: 各 Klein 点は 2-捻れ（⊆ E₉[2]）** — [k,u]²=[2k, u²]=[0,1]=[1]
    （u²=1 は u=±1・付値 2k は 2∣2k で消える）。Klein 4 群が E₉[2] に含まれることの実証。 -/
theorem q3tt_klein_torsion (x : (q3tCurve 2).carrier) (hx : q3ttKleinMem x) :
    (q3tCurve 2).mul x x = (q3tCurve 2).one := by
  obtain ⟨k, u, hu, hxe⟩ := hx
  have hsq : (zpUnits 3 isPrime_three).mul u u = (zpUnits 3 isPrime_three).one := by
    obtain hu1 | hu2 := hu
    · rw [hu1]; exact (zpUnits 3 isPrime_three).one_mul _
    · rw [hu2]; exact q3tNegOne_sq
  rw [hxe, q3tt_proj_mul, hsq]
  have hcls := (q3tt_class_eq_iff 0 (k + k) (zpUnits 3 isPrime_three).one
    (zpUnits 3 isPrime_three).one).mpr ⟨⟨k, by omega⟩, rfl⟩
  rw [← hcls]
  exact (q3tProj 2).map_one

/-- **q3tt-5b（★）: Klein 4 群は積で閉じる** — [k,u]·[k',u']=[k+k', u·u'] で
    u·u' ∈ {±1}（±1 の積は ±1）。4 元 {[0,1],[1,1],[0,−1],[1,−1]} の閉性（(ℤ/2)²）。 -/
theorem q3tt_klein_closed (x y : (q3tCurve 2).carrier)
    (hx : q3ttKleinMem x) (hy : q3ttKleinMem y) :
    q3ttKleinMem ((q3tCurve 2).mul x y) := by
  obtain ⟨k, u, hu, hxe⟩ := hx
  obtain ⟨k', u', hu', hye⟩ := hy
  refine ⟨k + k', (zpUnits 3 isPrime_three).mul u u', ?_, ?_⟩
  · obtain hu1 | hu2 := hu
    · obtain hu1' | hu2' := hu'
      · left; rw [hu1, hu1']; exact (zpUnits 3 isPrime_three).one_mul _
      · right; rw [hu1, hu2']; exact (zpUnits 3 isPrime_three).one_mul _
    · obtain hu1' | hu2' := hu'
      · right; rw [hu2, hu1']; exact (zpUnits 3 isPrime_three).mul_one _
      · left; rw [hu2, hu2']; exact q3tNegOne_sq
  · rw [hxe, hye, q3tt_proj_mul]

/-! ### q3tt-5c: 4 点相異（6 組）-/

/-- Klein 4 群の 4 点。[1]=[0,1]・[3]=[1,1]・[−1]=[0,−1]・[−3]=[1,−1]。 -/
def q3ttW0 : (q3tCurve 2).carrier := (q3tProj 2).map ((0 : Int), (zpUnits 3 isPrime_three).one)
def q3ttW1 : (q3tCurve 2).carrier := (q3tProj 2).map ((1 : Int), (zpUnits 3 isPrime_three).one)
def q3ttW2 : (q3tCurve 2).carrier := (q3tProj 2).map ((0 : Int), q3tNegOne)
def q3ttW3 : (q3tCurve 2).carrier := (q3tProj 2).map ((1 : Int), q3tNegOne)

/-- 4 点はすべて Klein 4 群に属する。 -/
theorem q3ttW0_mem : q3ttKleinMem q3ttW0 := ⟨0, _, Or.inl rfl, rfl⟩
theorem q3ttW1_mem : q3ttKleinMem q3ttW1 := ⟨1, _, Or.inl rfl, rfl⟩
theorem q3ttW2_mem : q3ttKleinMem q3ttW2 := ⟨0, _, Or.inr rfl, rfl⟩
theorem q3ttW3_mem : q3ttKleinMem q3ttW3 := ⟨1, _, Or.inr rfl, rfl⟩

/-- 付値方向の分離: 2 ∤ (1−0)。 -/
theorem q3t_klein_idx01 : ¬ (2 : Int) ∣ ((1 : Int) - (0 : Int)) := by
  intro h; obtain ⟨c, hc⟩ := h; omega
/-- 付値方向の分離: 2 ∤ (0−1)。 -/
theorem q3t_klein_idx10 : ¬ (2 : Int) ∣ ((0 : Int) - (1 : Int)) := by
  intro h; obtain ⟨c, hc⟩ := h; omega

/-- **q3tt-5c（★）: Klein 4 群の 4 点は相異（6 組）** — 付値方向（2∤1）と
    単数方向（−1≠1・q3t_negone_ne_one）の直交（q3tt_class_eq_iff）で一様に閉じる。 -/
theorem q3tt_klein_distinct :
    q3ttW0 ≠ q3ttW1 ∧ q3ttW0 ≠ q3ttW2 ∧ q3ttW0 ≠ q3ttW3 ∧
    q3ttW1 ≠ q3ttW2 ∧ q3ttW1 ≠ q3ttW3 ∧ q3ttW2 ≠ q3ttW3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact q3t_klein_idx01 ((q3tt_class_eq_iff 0 1 _ _).mp h).1
  · intro h
    exact q3t_negone_ne_one ((q3tt_class_eq_iff 0 0 _ _).mp h).2.symm
  · intro h
    exact q3t_klein_idx01 ((q3tt_class_eq_iff 0 1 _ _).mp h).1
  · intro h
    exact q3t_klein_idx10 ((q3tt_class_eq_iff 1 0 _ _).mp h).1
  · intro h
    exact q3t_negone_ne_one ((q3tt_class_eq_iff 1 1 _ _).mp h).2.symm
  · intro h
    exact q3t_klein_idx01 ((q3tt_class_eq_iff 0 1 _ _).mp h).1

/-! ## q3tt-6: capstone -/

/-- **q3tt-6a: 実 Tate 2-捻れデータ** — 実 w=3（w²=q=9・体拡大なし）・実位数ちょうど 2・
    実 μ₂={±1} 捻れ点・Klein 4 群 ⊆ E₉[2]（積閉・各点 2-捻れ）を束ねる。 -/
structure Q3TateTorsionData where
  /-- 実 2 乗根 w=3, w²=q=9（M314F witness 仮定の実 discharge）。 -/
  wSq : q3tGrp.mul (q3tQ 1) (q3tQ 1) = q3tQ 2
  /-- [w]²=[q]=[1]。 -/
  wTorsion : (q3tCurve 2).mul ((q3tProj 2).map (q3tQ 1)) ((q3tProj 2).map (q3tQ 1))
    = (q3tCurve 2).one
  /-- [w] の実位数はちょうど 2（外部付値仮定なし）。 -/
  wOrder : ∀ k : Nat, tateNpow (q3tCurve 2) ((q3tProj 2).map (q3tQ 1)) k
    = (q3tCurve 2).one → (2 : Nat) ∣ k
  /-- 実 μ₂ 捻れ点 [−1]²=[1]。 -/
  muTorsion : (q3tCurve 2).mul q3ttMuPoint q3ttMuPoint = (q3tCurve 2).one
  /-- [−1]≠[1]（非自明捻れ点）。 -/
  muNeOne : q3ttMuPoint ≠ (q3tCurve 2).one
  /-- Klein 4 群は各点が 2-捻れ（⊆ E₉[2]）。 -/
  kleinTorsion : ∀ x, q3ttKleinMem x → (q3tCurve 2).mul x x = (q3tCurve 2).one
  /-- Klein 4 群は積で閉じる。 -/
  kleinClosed : ∀ x y, q3ttKleinMem x → q3ttKleinMem y
    → q3ttKleinMem ((q3tCurve 2).mul x y)

/-- **q3tt-6b: 見出し実例** — E₉(ℚ₃)=ℚ₃^×/9^ℤ の 2-捻れ E₉[2] の実構成。 -/
def q3ttData : Q3TateTorsionData where
  wSq := q3tt_w_sq
  wTorsion := q3tt_w_torsion
  wOrder := q3tt_w_order
  muTorsion := q3tt_mu_torsion
  muNeOne := q3tt_mu_ne_one
  kleinTorsion := q3tt_klein_torsion
  kleinClosed := q3tt_klein_closed

/-- **q3tt-6c: 実 2-捻れの存在**（実 ℚ₃ 上・q=9・l=2）。 -/
theorem q3ttTorsion_exists : Nonempty Q3TateTorsionData := ⟨q3ttData⟩

end IUT
