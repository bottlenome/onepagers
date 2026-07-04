/-
  IUT/MuLIdentification.lean — M162F: μ_l 同一視・l⋇ ラベリング（柱E E-1・並行部品）

  柱E 残課題 E-1（#39）の μ_l 同一視・l⋇ ラベリング切片。
  M121F（μ_l 部分群）・M124F（シクロトミック同期 centerToMu）・
  M116F（±-構造 ι）・M2（F_l の ±1 商 orbitRep）を接合し、
  **μ_l(O) 上の反転（±）作用の軌道が orbitRep ラベルでちょうど分類され、
  非単位軌道の個数が l⋇ = (l−1)/2 である**ことを機械検証する。
  [EtTh] の「μ_l 係数シクロトーム ↔ O の l 乗根 μ_l(O) の同一視は
  ±-構造・テータ値ラベリングと両立する」の離散核。

  * M162F-1 `zpPow_eq_one_small` / `zpPow_eq_one_cases` /
    `zpPow_negMod_mul` — 冪の相異性からの核の決定（e < l で ζ^e = 1
    なら e = 0、e < 2l なら e ∈ {0, l}）と、μ_l の反転
    ζ^j · ζ^{negMod l j} = 1（j と negMod l j = l−j は互いに逆元）
  * M162F-2 `MuPMRel` / `mu_pm_orbit_iff`（**本丸1**）— μ_l 上の
    ±-軌道関係（同一 or 積 = 1）と **軌道の完全分類**:
    ζ^j ～ ζ^{j'} ⟺ orbitRep l j = orbitRep l j'。
    F_l/{±1} のラベル集合（M2）が μ_l(O)/(反転) を過不足なく
    ラベルすることの厳密形
  * M162F-3 `centerToMu_natCast` / `centerToMu_neg_natCast` /
    `centerToMu_neg_inv` / `mu_neg_label` — 係数シクロトーム側の
    符号反転 z ↦ −z が μ_l 側の逆元（反転）に写ること:
    centerToMu(j) = ζ^j、centerToMu(−j) = ζ^{negMod l j}、
    centerToMu(z) · centerToMu(−z) = 1。M124F 同期写像の ±-同変性
  * M162F-4 `lstar_eq_half` / `mu_theta_labels` /
    `mu_theta_pm_compat` / `theta_pm_mu_label`（**本丸2**）—
    l⋇ = (l−1)/2 と **非単位 μ_l 冪のラベルがちょうど {1, …, l⋇}**
    （範囲 + 切断）。さらに M116F の ι がテータ切断ラベル j ↦ l−j を
    （中心捻れ付きで）入れ替える事実と μ_l 側の反転 ζ^j ↔ ζ^{l−j} が
    同じ ± 同一視であることの両側接合
  * M162F-5 `MuLIdentificationData` / `muLIdentificationData` /
    `muLIdentification_exists` — 総括レコード: μ_l 生成元 ζ
    （Teichmüller 形）・同期の生成元対応 1 ↦ ζ・±-同変性・
    軌道分類・l⋇ = (l−1)/2 ラベリングの一括束ね

  意義: E-1 のうち「μ_l 係数シクロトーム ↔ μ_l(O) の同一視が
  ±-構造と l⋇ ラベリングに両立する」部分を閉じる。M124F は
  中心 → μ_l の準同型・忠実性まで、M116F はテータ群側の ± まで
  だったのに対し、本モジュールは μ_l(O) 側の ±-商を初めて構成し、
  テータ値ラベル {1, …, l⋇}（M2 theta_labels・M4 lstar）と同定する。

  正直な限定: 扱うのは固定素数 p・l ∣ p−1 の ℤ_p 内の μ_l(O) と
  その反転作用の軌道論のみ。一般の p 進局所体 O・ガロア同変性・
  tempered π₁ の商としての実現・エタールテータの関数等式リフトは
  未形式化（E-1 残）。±-軌道関係 MuPMRel は「y = x ∨ x·y = 1」の
  witness 形で、商群としての μ_l/{±1} の構成（Quot）はとらない
  （ラベル分類 mu_pm_orbit_iff が商の内容を過不足なく表現する）。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.CyclotomicSync
import IUT.HodgeTheater

namespace IUT

/-! ## M162F-1: 冪の核の決定と μ_l の反転 -/

/-- **定理 (M162F-1a): 小さい冪の核は自明** — 冪 ζ^0, …, ζ^{l−1} が
    相異なるとき、e < l で ζ^e = 1 なら e = 0（ζ^0 = 1 = ζ^e が
    相異性に矛盾）。 -/
theorem zpPow_eq_one_small (p l : Nat) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    {e : Nat} (he : e < l) (h1 : zpPow p ζ e = zpOne p) : e = 0 := by
  cases Nat.eq_zero_or_pos e with
  | inl h0 => exact h0
  | inr hpos =>
    have h0 : zpPow p ζ 0 = zpPow p ζ e := by
      rw [zpPow_zero]
      exact h1.symm
    exact absurd h0 (hdist 0 e hpos he)

/-- **定理 (M162F-1b): 2l 未満の核は {0, l}** — ζ^l = 1 のとき
    e < 2l で ζ^e = 1 なら e = 0 か e = l（l ≤ e は e−l に還元して
    M162F-1a）。±-軌道分類（M162F-2）で j + j' の値を確定する鍵。 -/
theorem zpPow_eq_one_cases (p l : Nat) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    {e : Nat} (he : e < 2 * l) (h1 : zpPow p ζ e = zpOne p) :
    e = 0 ∨ e = l := by
  cases Nat.lt_or_ge e l with
  | inl hlt => exact Or.inl (zpPow_eq_one_small p l ζ hdist hlt h1)
  | inr hge =>
    refine Or.inr ?_
    have hsplit : e = (e - l) + l := by omega
    rw [hsplit, zpPow_add, hζl, zpMul_comm, zpOne_mul] at h1
    have h0 : e - l = 0 := zpPow_eq_one_small p l ζ hdist (by omega) h1
    omega

/-- **定理 (M162F-1c): μ_l の反転** — ζ^l = 1 のとき
    ζ^j · ζ^{negMod l j} = 1。つまり指数の ±1 作用 j ↦ negMod l j
    （M2）は μ_l 側では逆元 x ↦ x⁻¹ に対応する。 -/
theorem zpPow_negMod_mul (p l : Nat) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) {j : Nat} (hj : j < l) :
    zpMul p (zpPow p ζ j) (zpPow p ζ (negMod l j)) = zpOne p := by
  cases Nat.eq_zero_or_pos j with
  | inl h0 =>
    have hneg : negMod l j = 0 := by
      unfold negMod
      rw [if_pos h0]
    rw [hneg, h0, zpPow_zero, zpOne_mul]
  | inr hpos =>
    have hneg : negMod l j = l - j := by
      unfold negMod
      rw [if_neg (by omega)]
    rw [hneg, ← zpPow_add]
    have he : j + (l - j) = l := by omega
    rw [he]
    exact hζl

/-! ## M162F-2: ±-軌道関係と軌道の完全分類（本丸1） -/

/-- **M162F-2a: μ_l 上の ±-軌道関係** — x ～ y :⟺ y = x または
    x·y = 1（y が x 自身か x の逆元）。反転 x ↦ x⁻¹ による
    {±1}-軌道の witness 形。 -/
def MuPMRel (p : Nat) (x y : (Zp p).carrier) : Prop :=
  y = x ∨ zpMul p x y = zpOne p

/-- **定理 (M162F-2b): ±-軌道の完全分類（本丸1）** — 位数 l の
    ζ について、ζ^j ～ ζ^{j'} ⟺ orbitRep l j = orbitRep l j'
    （j, j' < l）。左⇒右: 同一なら相異性から j = j'、積 = 1 なら
    ζ^{j+j'} = 1 と j+j' < 2l から j+j' ∈ {0, l}（M162F-1b）で
    orbitRep が一致。右⇒左: M2-6 orbitRep_eq_iff で j' ∈ {j, negMod l j}
    に分解し、negMod 側は M162F-1c。F_l/{±1} のラベル（M2）が
    μ_l(O)/(反転) を過不足なく分類することの厳密形。 -/
theorem mu_pm_orbit_iff (p l L : Nat) (ζ : (Zp p).carrier)
    (hodd : l = 2 * L + 1)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    {j j' : Nat} (hj : j < l) (hj' : j' < l) :
    MuPMRel p (zpPow p ζ j) (zpPow p ζ j')
      ↔ orbitRep l j = orbitRep l j' := by
  refine Iff.intro (fun hpm => ?_) (fun h => ?_)
  · cases hpm with
    | inl heq =>
      cases Nat.lt_or_ge j j' with
      | inl hlt => exact absurd heq.symm (hdist j j' hlt hj')
      | inr hge =>
        cases Nat.lt_or_ge j' j with
        | inl hlt' => exact absurd heq (hdist j' j hlt' hj)
        | inr hge' =>
          have heq2 : j = j' := by omega
          rw [heq2]
    | inr hmul =>
      rw [← zpPow_add] at hmul
      cases zpPow_eq_one_cases p l ζ hζl hdist (by omega) hmul with
      | inl hzero =>
        have hj0 : j = 0 := by omega
        have hj'0 : j' = 0 := by omega
        rw [hj0, hj'0]
      | inr hsum =>
        unfold orbitRep
        omega
  · cases (orbitRep_eq_iff hodd hj hj').mp h with
    | inl heq =>
      refine Or.inl ?_
      rw [heq]
    | inr heq =>
      refine Or.inr ?_
      rw [heq]
      exact zpPow_negMod_mul p l ζ hζl hj

/-! ## M162F-3: 同期写像 centerToMu の ±-同変性 -/

/-- **定理 (M162F-3a): 自然数ラベルの像** — j < l なら
    centerToMu p l ζ j = ζ^j（j % l = j の余りの一意性）。
    M124F の同期写像が切断ラベル j をそのまま μ_l の冪に送る。 -/
theorem centerToMu_natCast (p l : Nat) (ζ : (Zp p).carrier)
    {j : Nat} (hj : j < l) :
    centerToMu p l ζ ((j : Nat) : Int) = zpPow p ζ j := by
  have hb : (0 : Int) < ((l : Nat) : Int) := by omega
  have hmod : ((j : Nat) : Int) % ((l : Nat) : Int) = ((j : Nat) : Int) :=
    int_emod_unique _ _ _ hb (by omega) (by omega) ⟨0, by omega⟩
  show zpPow p ζ (((j : Nat) : Int) % ((l : Nat) : Int)).toNat = zpPow p ζ j
  rw [hmod]
  have ht : (((j : Nat) : Int)).toNat = j := by omega
  rw [ht]

/-- **定理 (M162F-3b): 負ラベルの像** — j < l なら
    centerToMu p l ζ (−j) = ζ^{negMod l j}（−j % l = l−j の余りの
    一意性、j = 0 は 0 に退化）。係数シクロトーム側の符号反転が
    μ_l 側の ±1 作用（M2 negMod）に正確に対応する。 -/
theorem centerToMu_neg_natCast (p l : Nat) (ζ : (Zp p).carrier)
    {j : Nat} (hj : j < l) :
    centerToMu p l ζ (-((j : Nat) : Int)) = zpPow p ζ (negMod l j) := by
  have hb : (0 : Int) < ((l : Nat) : Int) := by omega
  cases Nat.eq_zero_or_pos j with
  | inl h0 =>
    have hneg : negMod l j = 0 := by
      unfold negMod
      rw [if_pos h0]
    have hz : -((j : Nat) : Int) = 0 := by omega
    rw [hz, hneg, centerToMu_zero, zpPow_zero]
  | inr hpos =>
    have hneg : negMod l j = l - j := by
      unfold negMod
      rw [if_neg (by omega)]
    have hmod : (-((j : Nat) : Int)) % ((l : Nat) : Int)
        = (((l - j : Nat) : Nat) : Int) :=
      int_emod_unique _ _ _ hb (by omega) (by omega) ⟨-1, by omega⟩
    show zpPow p ζ ((-((j : Nat) : Int)) % ((l : Nat) : Int)).toNat
      = zpPow p ζ (negMod l j)
    rw [hmod, hneg]
    have ht : ((((l - j : Nat) : Nat) : Int)).toNat = l - j := by omega
    rw [ht]

/-- **定理 (M162F-3c): 同期写像の反転恒等式** —
    centerToMu(z) · centerToMu(−z) = 1（準同型性 M124F-3a と
    0 ↦ 1）。中心座標の符号反転は μ_l の逆元をとることに写る。 -/
theorem centerToMu_neg_inv (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) (z : Int) :
    zpMul p (centerToMu p l ζ z) (centerToMu p l ζ (-z)) = zpOne p := by
  rw [← centerToMu_add p l hl ζ hζl z (-z)]
  have hz : z + -z = 0 := by omega
  rw [hz]
  exact centerToMu_zero p l ζ

/-- **定理 (M162F-3d): 反転とラベルの両立** — ζ^j と centerToMu(−j)
    は同じ ±-軌道に属し（積 = 1）、指数の ±1 作用は orbitRep
    ラベルを変えない（M2-4）。 -/
theorem mu_neg_label (p l : Nat) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) {j : Nat} (hj : j < l) :
    MuPMRel p (zpPow p ζ j) (centerToMu p l ζ (-((j : Nat) : Int)))
      ∧ orbitRep l (negMod l j) = orbitRep l j := by
  refine ⟨Or.inr ?_, orbitRep_negMod (by omega) hj⟩
  rw [centerToMu_neg_natCast p l ζ hj]
  exact zpPow_negMod_mul p l ζ hζl hj

/-! ## M162F-4: l⋇ = (l−1)/2 ラベリング（本丸2） -/

/-- **定理 (M162F-4a): l⋇ の閉形式** — l = 2l⋇+1 なら l⋇ = (l−1)/2。 -/
theorem lstar_eq_half {l L : Nat} (hodd : l = 2 * L + 1) :
    L = (l - 1) / 2 := by omega

/-- **定理 (M162F-4b): 非単位 μ_l 冪のラベルはちょうど {1, …, l⋇}
    （本丸2）** — (範囲) ζ^j ≠ 1（j < l）のラベルは 1 ≤ orbitRep ≤ l⋇、
    (切断) 各 k ∈ {1, …, l⋇} は自分自身をラベルとする非単位冪 ζ^k を
    持つ。M162F-2b と合わせ、μ_l(O)∖{1} の ±-軌道はちょうど
    l⋇ = (l−1)/2 個 — テータ値 q^{1²}, …, q^{l⋇²} のラベル集合
    （M2-7 theta_labels・M4 lstar と同内容。選択公理回避のため
    範囲は orbitRep の展開で直接示す）と同定される。 -/
theorem mu_theta_labels (p l L : Nat) (ζ : (Zp p).carrier)
    (hodd : l = 2 * L + 1)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) :
    (∀ j, j < l → zpPow p ζ j ≠ zpOne p →
      1 ≤ orbitRep l j ∧ orbitRep l j ≤ L) ∧
    (∀ k, 1 ≤ k → k ≤ L →
      zpPow p ζ k ≠ zpOne p ∧ orbitRep l k = k) := by
  refine ⟨fun j hj hne => ?_, fun k hk1 hkL => ⟨fun h1 => ?_, ?_⟩⟩
  · have hj0 : j ≠ 0 := by
      intro h0
      apply hne
      rw [h0]
      exact zpPow_zero p ζ
    unfold orbitRep
    refine ⟨?_, ?_⟩
    · omega
    · omega
  · have h0 : zpPow p ζ 0 = zpPow p ζ k := by
      rw [zpPow_zero]
      exact h1.symm
    exact absurd h0 (hdist 0 k (by omega) (by omega))
  · exact orbitRep_fixes hodd hkL

/-- **定理 (M162F-4c): μ_l 側の ± 同一視 j ↔ l−j** — 0 < j < l で
    ζ^j · ζ^{l−j} = 1 かつ orbitRep l (l−j) = orbitRep l j。
    テータ切断側のラベル入替（M116F-5b）と同じ対 j ↔ l−j。 -/
theorem mu_theta_pm_compat (p l : Nat) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) {j : Nat} (hpos : 0 < j) (hj : j < l) :
    zpMul p (zpPow p ζ j) (zpPow p ζ (l - j)) = zpOne p
      ∧ orbitRep l (l - j) = orbitRep l j := by
  have hneg : negMod l j = l - j := by
    unfold negMod
    rw [if_neg (by omega)]
  refine ⟨?_, ?_⟩
  · rw [← hneg]
    exact zpPow_negMod_mul p l ζ hζl hj
  · rw [← hneg]
    exact orbitRep_negMod (by omega) hj

/-- **定理 (M162F-4d): テータ ± と μ_l 反転の両側接合** — M116F の
    ι はテータ切断ラベル j を（中心捻れ付きで）l−j に入れ替え
    （thetaNeg_label_center）、同じ対 j ↔ l−j が μ_l 側では互いに
    逆元 ζ^j · ζ^{l−j} = 1。テータ環境の ±-構造と μ_l(O) の反転が
    同一の {±1}-同一視であることの witness。 -/
theorem theta_pm_mu_label (p l : Nat) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) {j : Nat} (hpos : 0 < j) (hj : j < l) :
    (∃ z : Int, thetaRelMod l (thetaNeg.map (thetaSection j))
        (thetaGrp.mul (thetaSection (l - j)) (0, 0, z)))
      ∧ zpMul p (zpPow p ζ j) (zpPow p ζ (l - j)) = zpOne p :=
  ⟨thetaNeg_label_center l j (by omega),
    (mu_theta_pm_compat p l ζ hζl hpos hj).1⟩

/-! ## M162F-5: 総括レコード -/

/-- **M162F-5a: μ_l 同一視・l⋇ ラベリングデータ** — μ_l(O) の生成元 ζ
    （Teichmüller 形・位数 l）、同期写像の生成元対応 1 ↦ ζ と
    ±-同変性、±-軌道の orbitRep による完全分類、非単位軌道の
    l⋇ = (l−1)/2 ラベリングの一括束ね。E-1 の μ_l 同一視・
    l⋇ ラベリング切片の witness。 -/
structure MuLIdentificationData (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) where
  /-- μ_l(O) の生成元（O = ℤ_p 内の l 乗根）。 -/
  ζ : (Zp p).carrier
  /-- ζ は l 乗根: ζ^l = 1。 -/
  root : zpPow p ζ l = zpOne p
  /-- 冪 ζ^0, …, ζ^{l−1} は相異なる（位数ちょうど l）。 -/
  distinct : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j
  /-- ζ は Teichmüller 代表 ω(a)（p ∤ a）— O^× の標準的 l 乗根。 -/
  teich_form : ∃ a : Int, ¬ ((p : Nat) : Int) ∣ a ∧ ζ = teich p hp a
  /-- 同期: 中心生成元 1 ↦ μ_l 生成元 ζ（M124F-3c）。 -/
  sync_gen : centerToMu p l ζ 1 = ζ
  /-- 同期の ±-同変性: centerToMu(z) · centerToMu(−z) = 1。 -/
  sync_inv : ∀ z : Int,
    zpMul p (centerToMu p l ζ z) (centerToMu p l ζ (-z)) = zpOne p
  /-- ±-軌道の完全分類: ζ^j ～ ζ^{j'} ⟺ orbitRep 一致。 -/
  pm_orbit : ∀ j j', j < l → j' < l →
    (MuPMRel p (zpPow p ζ j) (zpPow p ζ j')
      ↔ orbitRep l j = orbitRep l j')
  /-- l⋇ = (l−1)/2。 -/
  lstar_half : L = (l - 1) / 2
  /-- 非単位冪のラベルは {1, …, l⋇} に収まる。 -/
  label_range : ∀ j, j < l → zpPow p ζ j ≠ zpOne p →
    1 ≤ orbitRep l j ∧ orbitRep l j ≤ L
  /-- 各ラベル k ∈ {1, …, l⋇} は非単位冪 ζ^k で実現される。 -/
  label_section : ∀ k, 1 ≤ k → k ≤ L →
    zpPow p ζ k ≠ zpOne p ∧ orbitRep l k = k
  /-- テータ ± との接合: ι のラベル入替 j ↔ l−j = μ_l の反転。 -/
  theta_compat : ∀ j, 0 < j → j < l →
    (∃ z : Int, thetaRelMod l (thetaNeg.map (thetaSection j))
        (thetaGrp.mul (thetaSection (l - j)) (0, 0, z)))
      ∧ zpMul p (zpPow p ζ j) (zpPow p ζ (l - j)) = zpOne p

/-- **M162F-5b: witness 本体** — 位数 l の生成元 ζ（とその証拠）から
    全フィールドを M162F-1〜4 で埋める。 -/
def muLIdentificationData (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1)
    (ζ : (Zp p).carrier) (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (ha : ∃ a : Int, ¬ ((p : Nat) : Int) ∣ a ∧ ζ = teich p hp a) :
    MuLIdentificationData p l L hp hL hodd hdvd where
  ζ := ζ
  root := hζl
  distinct := hdist
  teich_form := ha
  sync_gen := centerToMu_one_gen p l (by omega) ζ
  sync_inv := fun z => centerToMu_neg_inv p l (by omega) ζ hζl z
  pm_orbit := fun _ _ hj hj' =>
    mu_pm_orbit_iff p l L ζ hodd hζl hdist hj hj'
  lstar_half := lstar_eq_half hodd
  label_range := fun j hj hne =>
    (mu_theta_labels p l L ζ hodd hdist).1 j hj hne
  label_section := fun k hk1 hkL =>
    (mu_theta_labels p l L ζ hodd hdist).2 k hk1 hkL
  theta_compat := fun _ hpos hj =>
    theta_pm_mu_label p l ζ hζl hpos hj

/-- **定理 (M162F-5c): μ_l 同一視データの存在（M162F 見出し）** —
    p 素数・l = 2l⋇+1 ∣ p−1 なら μ_l 同一視・l⋇ ラベリングデータが
    存在する（生成元は M121F mu_l_zp_exists から）。 -/
theorem muLIdentification_exists (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) :
    Nonempty (MuLIdentificationData p l L hp hL hodd hdvd) := by
  obtain ⟨ζ, hζl, hdist, ha⟩ := mu_l_zp_exists p l hp (by omega) hdvd
  exact ⟨muLIdentificationData p l L hp hL hodd hdvd ζ hζl hdist ha⟩

end IUT
