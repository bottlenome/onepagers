/-
  IUT/AlgebraTensor.lean — M278F: 分裂 K-代数のテンソル積 K^m ⊗_K K^n ≅ K^{mn}
  ── 柱A 実 FÉt(K) のモノイダル構造（被覆のファイバー積）の本物の先行建設

  分類 **[実]**（本物の分裂エタール K-代数のテンソル積 = 被覆のファイバー積の
  実構成; toy 代理ではなく funPowCRing 直積環の上の完全証明）。

  **complete_pct 影響: 柱A 実 FÉt(K) が有限直積（テンソル積）で閉じることの
  本物の先行建設**。幾何的には Spec(K^m ⊗_K K^n) = Spec(K^m) ×_{Spec K} Spec(K^n)
  であり、ファイバー数が積 m·n になる（π₁^ét 作用が積で振る舞う; FÉt(K) の
  対称モノイダル構造の入口）。本モジュールは M272F（FiniteEtaleAlgebra）の
  分裂エタール代数 K^n を土台に、**分裂対象のテンソル積を直積環 K^{m·n}
  （= funPowCRing (m*n)）として本物で実現**し、次を完全証明する:
  * 自前の全単射 Fin m × Fin n ≅ Fin (m*n)（`algTensorToFin`/`algTensorFromFin`・
    左右逆・除算/剰余による本物の証明）
  * 直交冪等元の完全系の保存: e_i⊗e_j = e_{(i,j)} が K^{mn} の直交冪等元
    （(e_i⊗e_j)² = e_i⊗e_j・相異なるペアで積 0・**二重和 Σ_{i,j} e_i⊗e_j = 1**）
  * rank の乗法性: rank(K^m ⊗ K^n) = m·n（被覆のファイバー積 = ファイバー基数の積）
  * 両因子からの標準射 K^m → K^m⊗K^n（a ↦ a⊗1）・K^n → K^m⊗K^n（b ↦ 1⊗b）を
    K-代数準同型として本物で構成
  * capstone: テンソル積が再び有限エタール分裂対象（FÉt(K) がテンソル積で閉じる）・
    存在・実例（ℚ 上 m=2,n=3 で rank=6）

  正直な限定（何が本物で何が範囲外か）:
  1. **本物**: 分裂対象 K^m と K^n のテンソル積は、分裂被覆のファイバー積の
     座標環として直積環 K^{mn} で忠実に実現される（分裂＝自明被覆の圏はこの
     直積で閉じる）。全単射・直交冪等元の完全系・rank 乗法性・両因子の標準射は
     完全証明（sorry 皆無・新規 Classical.choice 皆無）。これは toy 模型ではなく
     分裂被覆のファイバー積の本物の実現である。
  2. **範囲外（正直申告）**: 一般の K-代数の抽象テンソル積 A ⊗_K B（普遍性・
     双線形写像・基底非依存の構成）は範囲外。ここでは**分裂対象 K^m, K^n の
     具体的実現（直積環 K^{mn}）に限る**。一般対象への拡張は M272F の一般
     有限エタール代数（分離拡大の直積）の建設後に後続で行う。
  3. Fin (m*n) との対応は自前の全単射（除算/剰余）で構成し、m=0 または n=0 の
     退化（空被覆）では二重和・rank は自明に成立する。標準射・全単射の逆は n>0 を
     仮定して構成する（n=0 なら K^0 は零環で射は自明）。

  選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。
  禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。
-/
import IUT.FiniteEtaleAlgebra

namespace IUT

/-! ## M278F-0: Nat 補助（ファイバー積の添字算術） -/

/-- **M278F-0a: ペア添字の上界** i·n + j < m·n（i<m, j<n）。
    ファイバー積 Fin m × Fin n が Fin (m·n) に収まることの核。 -/
theorem algTensor_pair_lt {m n : Nat} (i : Fin m) (j : Fin n) :
    i.val * n + j.val < m * n := by
  have h1 : i.val + 1 ≤ m := i.isLt
  have h2 : (i.val + 1) * n ≤ m * n := Nat.mul_le_mul h1 (Nat.le_refl n)
  have h3 : (i.val + 1) * n = i.val * n + n := Nat.succ_mul i.val n
  have hj : j.val < n := j.isLt
  omega

/-- **M278F-0b: 積の正値から両因子の正値** 0 < m·n ⇒ 0 < m ∧ 0 < n。 -/
theorem algTensor_pos_both {m n : Nat} (h : 0 < m * n) : 0 < m ∧ 0 < n := by
  cases m with
  | zero =>
    have hz : 0 * n = 0 := Nat.zero_mul n
    rw [hz] at h
    exact absurd h (Nat.lt_irrefl 0)
  | succ m' =>
    cases n with
    | zero =>
      have hz : (m' + 1) * 0 = 0 := Nat.mul_zero (m' + 1)
      rw [hz] at h
      exact absurd h (Nat.lt_irrefl 0)
    | succ n' => exact ⟨Nat.succ_pos m', Nat.succ_pos n'⟩

/-! ## M278F-1: 全単射 Fin m × Fin n ≅ Fin (m·n)（自前構成） -/

/-- **M278F-1a: ペア → 平坦添字** (i,j) ↦ i·n + j。 -/
def algTensorToFin (m n : Nat) (i : Fin m) (j : Fin n) : Fin (m * n) :=
  ⟨i.val * n + j.val, algTensor_pair_lt i j⟩

/-- **M278F-1b: 平坦添字の剰余は第2成分** (i·n + j) % n = j。 -/
theorem algTensor_val_mod {m n : Nat} (i : Fin m) (j : Fin n) :
    (i.val * n + j.val) % n = j.val := by
  rw [Nat.mul_comm i.val n, Nat.mul_add_mod n i.val j.val, Nat.mod_eq_of_lt j.isLt]

/-- **M278F-1c: 平坦添字の商は第1成分** (i·n + j) / n = i（n>0）。 -/
theorem algTensor_val_div {m n : Nat} (hn : 0 < n) (i : Fin m) (j : Fin n) :
    (i.val * n + j.val) / n = i.val := by
  rw [Nat.mul_comm i.val n, Nat.mul_add_div hn i.val j.val, Nat.div_eq_of_lt j.isLt,
    Nat.add_zero]

/-- **M278F-1d: ペア添字の単射性** i·n + j = i'·n + j' ⇒ (i,j) = (i',j')（n>0）。
    冪等元 e_i⊗e_j の直交性（相異なるペアで積 0）の基礎。 -/
theorem algTensorToFin_inj {m n : Nat} (hn : 0 < n) {i i' : Fin m} {j j' : Fin n}
    (h : algTensorToFin m n i j = algTensorToFin m n i' j') : i = i' ∧ j = j' := by
  have hv : i.val * n + j.val = i'.val * n + j'.val := congrArg Fin.val h
  have hjj : j.val = j'.val := by
    have e1 := algTensor_val_mod i j
    have e2 := algTensor_val_mod i' j'
    rw [hv] at e1
    rw [e2] at e1
    exact e1.symm
  have hii : i.val = i'.val := by
    have e1 := algTensor_val_div hn i j
    have e2 := algTensor_val_div hn i' j'
    rw [hv] at e1
    rw [e2] at e1
    exact e1.symm
  exact ⟨kAlgFin_ext hii, kAlgFin_ext hjj⟩

/-- **M278F-1e: 平坦添字 → ペア** k ↦ (k/n, k%n)（n>0）。 -/
def algTensorFromFin (m n : Nat) (hn : 0 < n) (k : Fin (m * n)) : Fin m × Fin n :=
  (⟨k.val / n, (Nat.div_lt_iff_lt_mul hn).mpr k.isLt⟩, ⟨k.val % n, Nat.mod_lt k.val hn⟩)

/-- **M278F-1f: 自前の全単射構造** Fin m × Fin n ≅ Fin (m·n)。 -/
structure AlgTensorPairEquiv (m n : Nat) where
  /-- ペア → 平坦添字。 -/
  toFin : Fin m → Fin n → Fin (m * n)
  /-- 平坦添字 → ペア。 -/
  ofFin : Fin (m * n) → Fin m × Fin n
  /-- 左逆: ofFin ∘ toFin = id。 -/
  left_inv : ∀ i j, ofFin (toFin i j) = (i, j)
  /-- 右逆: toFin ∘ ofFin = id。 -/
  right_inv : ∀ k, toFin (ofFin k).1 (ofFin k).2 = k

/-- **M278F-1g: 全単射の構成**（n>0; 除算/剰余の本物の逆写像）。 -/
def algTensor_pairEquiv (m n : Nat) (hn : 0 < n) : AlgTensorPairEquiv m n where
  toFin := algTensorToFin m n
  ofFin := algTensorFromFin m n hn
  left_inv := fun i j => by
    have hd : (i.val * n + j.val) / n = i.val := algTensor_val_div hn i j
    have hm : (i.val * n + j.val) % n = j.val := algTensor_val_mod i j
    apply Prod.ext
    · exact kAlgFin_ext hd
    · exact kAlgFin_ext hm
  right_inv := fun k => by
    apply kAlgFin_ext
    show (k.val / n) * n + k.val % n = k.val
    rw [Nat.mul_comm (k.val / n) n]
    exact Nat.div_add_mod k.val n

/-! ## M278F-2: 分裂 K-代数のテンソル積とその冪等元 -/

/-- **M278F-2a: 分裂対象のテンソル積** K^m ⊗_K K^n := K^{m·n}。
    被覆のファイバー積 Spec(K^m) ×_{Spec K} Spec(K^n) の座標環。 -/
def algTensorSplit (K : IUTField) (m n : Nat) : KAlgebra K :=
  splitEtaleAlgebra K (m * n)

/-- **M278F-2b: テンソル冪等元** e_i ⊗ e_j := e_{(i,j)}（平坦添字の標準冪等元）。 -/
def algTensorIdem (K : IUTField) (m n : Nat) (i : Fin m) (j : Fin n) :
    (funPowCRing K.toCRing (m * n)).carrier :=
  splitIdem K (m * n) (algTensorToFin m n i j)

/-- **M278F-2c: 冪等性** (e_i⊗e_j)² = e_i⊗e_j。 -/
theorem algTensor_idem_mul_self (K : IUTField) (m n : Nat) (i : Fin m) (j : Fin n) :
    (funPowCRing K.toCRing (m * n)).mul (algTensorIdem K m n i j) (algTensorIdem K m n i j)
      = algTensorIdem K m n i j :=
  splitIdem_mul_self K (m * n) (algTensorToFin m n i j)

/-- **M278F-2d: 直交性** 相異なるペアで (e_i⊗e_j)(e_i'⊗e_j') = 0（n>0）。
    ファイバー積の連結成分が交わらないことの環論的実体。 -/
theorem algTensor_idem_orthogonal (K : IUTField) (m n : Nat) (hn : 0 < n)
    {i i' : Fin m} {j j' : Fin n} (h : ¬ (i = i' ∧ j = j')) :
    (funPowCRing K.toCRing (m * n)).mul
        (algTensorIdem K m n i j) (algTensorIdem K m n i' j')
      = (funPowCRing K.toCRing (m * n)).zero := by
  apply splitIdem_mul_orth
  intro hc
  exact h (algTensorToFin_inj hn hc)

/-! ## M278F-3: 直交冪等元の完全系の保存（二重和 Σ_{i,j} e_i⊗e_j = 1） -/

/-- **M278F-3a: テンソル冪等元の二重和** Σ_{i:Fin m} Σ_{j:Fin n} e_i⊗e_j。 -/
def algTensorDoubleSum (K : IUTField) (m n : Nat) :
    (funPowCRing K.toCRing (m * n)).carrier :=
  kPowSum (funPowCRing K.toCRing (m * n)) m
    (fun i => kPowSum (funPowCRing K.toCRing (m * n)) n
      (fun j => algTensorIdem K m n i j))

/-- **M278F-3b: 内側和の評価**（第 k 座標）— 固定 i について
    Σ_j [e_i⊗e_j が座標 k で 1] = [i = k/n]（除算/剰余の一意性）。 -/
theorem algTensor_inner_sum (K : IUTField) (m n : Nat) (hn : 0 < n)
    (k : Fin (m * n)) (i : Fin m)
    (a : Nat) (ha : a < m) (b : Nat) (hb : b < n)
    (hkval : k.val = a * n + b) :
    kPowSum K.toCRing n
        (fun j => if algTensorToFin m n i j = k then K.one else K.zero)
      = if i.val = a then K.one else K.zero := by
  cases kAlgDecEm (i.val = a) with
  | inl hia =>
    rw [if_pos hia]
    have hcongr : ∀ j : Fin n,
        (if algTensorToFin m n i j = k then K.one else K.zero)
          = (if j = (⟨b, hb⟩ : Fin n) then K.one else K.zero) := by
      intro j
      cases kAlgDecEm (j = (⟨b, hb⟩ : Fin n)) with
      | inl hj =>
        have hjv : j.val = b := congrArg Fin.val hj
        have heq : algTensorToFin m n i j = k := by
          apply kAlgFin_ext
          show i.val * n + j.val = k.val
          rw [hia, hjv, hkval]
        rw [if_pos heq, if_pos hj]
      | inr hj =>
        have hne : ¬ algTensorToFin m n i j = k := by
          intro hc
          apply hj
          have hcv : i.val * n + j.val = k.val := congrArg Fin.val hc
          rw [hia, hkval] at hcv
          have hjb : j.val = b := by omega
          exact kAlgFin_ext hjb
        rw [if_neg hne, if_neg hj]
    rw [kPowSum_congr K.toCRing n _ _ hcongr]
    exact kPowSum_delta K.toCRing n (⟨b, hb⟩ : Fin n)
  | inr hia =>
    rw [if_neg hia]
    apply kPowSum_zero
    intro j
    have hne : ¬ algTensorToFin m n i j = k := by
      intro hc
      have hcv : i.val * n + j.val = k.val := congrArg Fin.val hc
      rw [hkval] at hcv
      have hmod : (i.val * n + j.val) % n = j.val := algTensor_val_mod i j
      have hmod2 : (a * n + b) % n = b :=
        algTensor_val_mod (⟨a, ha⟩ : Fin m) (⟨b, hb⟩ : Fin n)
      rw [hcv, hmod2] at hmod
      have hdiv : (i.val * n + j.val) / n = i.val := algTensor_val_div hn i j
      have hdiv2 : (a * n + b) / n = a :=
        algTensor_val_div hn (⟨a, ha⟩ : Fin m) (⟨b, hb⟩ : Fin n)
      rw [hcv, hdiv2] at hdiv
      exact hia hdiv.symm
    rw [if_neg hne]

/-- **M278F-3c: 分割の完全性** Σ_{i,j} e_i⊗e_j = 1（n>0）—
    テンソル積 K^{mn} は m·n 個の連結成分（ファイバー積の点）に過不足なく分解する。
    M272F の splitIdem_complete の**積版**（直交冪等元の完全系の保存）。 -/
theorem algTensor_idem_complete (K : IUTField) (m n : Nat) (hn : 0 < n) :
    algTensorDoubleSum K m n = (funPowCRing K.toCRing (m * n)).one := by
  funext k
  have ha : k.val / n < m := (Nat.div_lt_iff_lt_mul hn).mpr k.isLt
  have hb : k.val % n < n := Nat.mod_lt k.val hn
  have hkval : k.val = (k.val / n) * n + k.val % n := by
    rw [Nat.mul_comm (k.val / n) n]
    exact (Nat.div_add_mod k.val n).symm
  show kPowSum (funPowCRing K.toCRing (m * n)) m
      (fun i => kPowSum (funPowCRing K.toCRing (m * n)) n
        (fun j => algTensorIdem K m n i j)) k
    = (funPowCRing K.toCRing (m * n)).one k
  rw [kPowSum_apply K.toCRing (m * n) k m
    (fun i => kPowSum (funPowCRing K.toCRing (m * n)) n
      (fun j => algTensorIdem K m n i j))]
  have step1 : ∀ i : Fin m,
      (kPowSum (funPowCRing K.toCRing (m * n)) n
          (fun j => algTensorIdem K m n i j)) k
        = kPowSum K.toCRing n
            (fun j => if algTensorToFin m n i j = k then K.one else K.zero) := by
    intro i
    rw [kPowSum_apply K.toCRing (m * n) k n (fun j => algTensorIdem K m n i j)]
    apply kPowSum_congr
    intro j
    rfl
  rw [kPowSum_congr K.toCRing m _ _ step1]
  have step2 : ∀ i : Fin m,
      kPowSum K.toCRing n
          (fun j => if algTensorToFin m n i j = k then K.one else K.zero)
        = if i.val = k.val / n then K.one else K.zero := by
    intro i
    exact algTensor_inner_sum K m n hn k i (k.val / n) ha (k.val % n) hb hkval
  rw [kPowSum_congr K.toCRing m _ _ step2]
  have step3 : ∀ i : Fin m,
      (if i.val = k.val / n then K.one else K.zero)
        = (if i = (⟨k.val / n, ha⟩ : Fin m) then K.one else K.zero) := by
    intro i
    cases kAlgDecEm (i.val = k.val / n) with
    | inl h => rw [if_pos h, if_pos (kAlgFin_ext h)]
    | inr h =>
      have hne : ¬ i = (⟨k.val / n, ha⟩ : Fin m) := by
        intro hc
        exact h (congrArg Fin.val hc)
      rw [if_neg h, if_neg hne]
  rw [kPowSum_congr K.toCRing m _ _ step3]
  exact kPowSum_delta K.toCRing m (⟨k.val / n, ha⟩ : Fin m)

/-! ## M278F-4: 両因子からの標準射（a ↦ a⊗1・b ↦ 1⊗b） -/

/-- **M278F-4a: 左標準射** K^m → K^m⊗K^n, a ↦ a⊗1（座標 k で a_{k/n}）（n>0）。 -/
def algTensor_inl (K : IUTField) (m n : Nat) (hn : 0 < n) :
    KAlgHom (splitEtaleAlgebra K m) (algTensorSplit K m n) where
  hom :=
    { map := fun a k => a ⟨k.val / n, (Nat.div_lt_iff_lt_mul hn).mpr k.isLt⟩
      map_add := fun _ _ => rfl
      map_mul := fun _ _ => rfl
      map_one := rfl }
  compat := fun _ => rfl

/-- **M278F-4b: 右標準射** K^n → K^m⊗K^n, b ↦ 1⊗b（座標 k で b_{k%n}）（n>0）。 -/
def algTensor_inr (K : IUTField) (m n : Nat) (hn : 0 < n) :
    KAlgHom (splitEtaleAlgebra K n) (algTensorSplit K m n) where
  hom :=
    { map := fun b k => b ⟨k.val % n, Nat.mod_lt k.val hn⟩
      map_add := fun _ _ => rfl
      map_mul := fun _ _ => rfl
      map_one := rfl }
  compat := fun _ => rfl

/-! ## M278F-5: rank の乗法性（ファイバー基数の積） -/

/-- **M278F-5a: rank = m·n** テンソル積のファイバー数は積。 -/
theorem algTensor_rank (K : IUTField) (m n : Nat) :
    (splitFEt K (m * n)).rank = m * n := rfl

/-- **M278F-5b: rank の乗法性** rank(K^m⊗K^n) = rank(K^m)·rank(K^n)。
    被覆のファイバー積 ⇒ ファイバー基数の乗法性（π₁ 作用の積構造）。 -/
theorem algTensor_rank_mul (K : IUTField) (m n : Nat) :
    (splitFEt K (m * n)).rank = (splitFEt K m).rank * (splitFEt K n).rank := rfl

/-! ## M278F-6: capstone — FÉt(K) がテンソル積で閉じる -/

/-- **M278F-6a: テンソル積は再び有限エタール分裂対象** — FÉt(K) がテンソル積で
    閉じる（自明被覆の圏はファイバー積で閉じる）。 -/
def algTensorSplit_isFiniteEtale (K : IUTField) (m n : Nat) : FiniteEtaleData K :=
  splitFEt K (m * n)

/-- **M278F-6b: テンソル積データ** — 有限エタール対象 + rank 乗法性 +
    両因子の標準射 + 直交冪等元の完全系。 -/
structure AlgTensorData (K : IUTField) (m n : Nat) where
  /-- テンソル積の有限エタール対象（分裂 witness 付き）。 -/
  fEt : FiniteEtaleData K
  /-- rank の乗法性 rank = m·n。 -/
  rank_eq : fEt.rank = m * n
  /-- 左標準射 K^m → K^m⊗K^n。 -/
  inl : KAlgHom (splitEtaleAlgebra K m) fEt.obj
  /-- 右標準射 K^n → K^m⊗K^n。 -/
  inr : KAlgHom (splitEtaleAlgebra K n) fEt.obj
  /-- 直交冪等元の完全系 Σ_{i,j} e_i⊗e_j = 1。 -/
  complete : algTensorDoubleSum K m n = (funPowCRing K.toCRing (m * n)).one

/-- **M278F-6c: テンソル積データの構成**（n>0）。 -/
def algTensorData (K : IUTField) (m n : Nat) (hn : 0 < n) : AlgTensorData K m n where
  fEt := splitFEt K (m * n)
  rank_eq := rfl
  inl := algTensor_inl K m n hn
  inr := algTensor_inr K m n hn
  complete := algTensor_idem_complete K m n hn

/-- **M278F-6d: capstone — テンソル積の存在**（n>0 なら FÉt(K) はテンソル積で
    閉じる: K^m⊗K^n が対象）。 -/
theorem algTensor_exists (K : IUTField) (m n : Nat) (hn : 0 < n) :
    Nonempty (AlgTensorData K m n) :=
  ⟨algTensorData K m n hn⟩

/-! ## M278F-7: 実例 — ℚ 上のテンソル積 K^2 ⊗ K^3 ≅ K^6 -/

/-- **M278F-7a: 実例** — 本物の数体 ℚ 上の分裂被覆 2 枚 ⊗ 3 枚 = 6 枚。 -/
def ratAlgTensor23 : AlgTensorData ratIUTField 2 3 :=
  algTensorData ratIUTField 2 3 (Nat.succ_pos 2)

/-- **M278F-7b: rank = 6** ファイバー基数の乗法性 2·3 = 6 の実確認。 -/
theorem ratAlgTensor23_rank : ratAlgTensor23.fEt.rank = 6 := rfl

/-- **M278F-7c: 存在**（ℚ 上のテンソル積 FÉt(ℚ) 対象）。 -/
theorem ratAlgTensor_exists : Nonempty (AlgTensorData ratIUTField 2 3) :=
  ⟨ratAlgTensor23⟩

end IUT
