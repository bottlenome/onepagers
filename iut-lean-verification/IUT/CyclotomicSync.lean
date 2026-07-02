/-
  IUT/CyclotomicSync.lean — M124F: シクロトミック同期 — テータ中心 (0,0,z) ↦ ζ^z と μ_l の同一視

  テータ群 mod l（M98F）の中心 (0,0,z) と μ_l（M121F）の同一視
  = cyclotomic synchronization の witness 形。M98F の mod-l cyclotomic
  rigidity が指定する中心生成元 (0,0,1) を μ_l の生成元 ζ に対応させる
  標準写像 z ↦ ζ^{z mod l} を構成し、well-definedness・準同型性・
  忠実性・±-両立を機械検証する。

  * M124F-1 `zpPow_add` / `zpPow_mul_period` — ℤ_p 冪の加法則
    ζ^{a+b} = ζ^a·ζ^b（b 帰納 + zpPow_succ）と l 周期性
    ζ^{e+lk} = ζ^e（ζ^l = 1 のとき）
  * M124F-2 `int_emod_unique` / `int_emod_congr` / `centerToMu` /
    `centerToMu_congr` — Int の余りの一意性（M120F int_ediv_unique の
    % 版、除算項を ∀ d r 形に隔離して omega の変数除算制限を回避）、
    中心写像 z ↦ ζ^{(z % l).toNat} とその well-definedness
    （l ∣ z−z' なら値一致）
  * M124F-3 `centerToMu_add`（**本丸1**）/ `centerToMu_zero` /
    `centerToMu_one_gen` — **準同型性** ζ^{(z+z') mod l} =
    ζ^{z mod l}·ζ^{z' mod l}（余りの和の δ ∈ {0,1} 二分岐 +
    l 周期性で余分な l を消去）、0 ↦ 1、**1 ↦ ζ**
    （中心生成元 (0,0,1) ↦ μ_l 生成元）
  * M124F-4 `centerToMu_faithful`（**本丸2**）/ `centerToMu_period` —
    **忠実性**: ζ^{z mod l} = 1 なら l ∣ z（冪の相異性 hdist との背理）
    と逆向き（l ∣ z なら値 1）= 核がちょうど l·ℤ
  * M124F-5 `theta_center_mul` / `theta_center_descend` /
    `theta_center_to_mu_hom` / `theta_center_neg_invariant` —
    テータ群との接合: 中心の Heisenberg 積は z+z'（コサイクル 0·0
    消滅）、thetaRelMod（mod-l 合同）で centerToMu は降下、
    **中心部分群 → μ_l の準同型**、M116F の ι は中心を固定するので
    ±-構造と自明に両立
  * M124F-6 `CyclotomicSyncData` / `cyclotomicSyncData` /
    `cyclotomicSync_exists` — 総括レコードと witness・Nonempty

  意義: 柱E E-1（#39）の接合層。M98F の mod-l cyclotomic rigidity が
  固定する中心生成元 (0,0,1) を μ_l の生成元 ζ（M121F）へ送る標準
  写像の well-definedness・準同型性・忠実性。M116F の ±-構造とも
  両立 — [EtTh] の「テータ環境のシクロトームと基礎体のシクロトームの
  同期」の離散核。

  正直申告: 商群 thetaGrpMod l レベルの言明（thetaRed 経由）ではなく、
  thetaGrp レベルの中心 (0,0,z) + mod-l 降下 `theta_center_descend`
  （thetaRelMod で合同な中心は同じ値に写る）の組で商レベルの内容を
  表現した（商の carrier から ℤ_p への Quot.lift を作るには centerToMu
  の全成分不変性が必要で、中心以外の成分を持つ代表への拡張は本層の
  範囲外）。また `centerToMu_faithful` は hζl（ζ^l = 1）を、
  `centerToMu_period` は hζl・hdist を必要としなかったため仮定から
  除いた（余りへの還元が先に働くため）。準同型性 centerToMu_add の
  δ 場合分けは指示通り `cases Nat.lt_or_ge (e + e') l` の 2 分岐で
  実装。全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.MuLSubgroup
import IUT.ThetaPM

namespace IUT

/-! ## M124F-1: ℤ_p 冪の加法則と l 周期性 -/

/-- **定理 (M124F-1a): ℤ_p 冪の加法則** — x^{a+b} = x^a · x^b
    （b の帰納。基底は x^0 = 1 と単位律、帰納段は zpPow_succ と
    結合律の付け替え）。 -/
theorem zpPow_add (p : Nat) (x : (Zp p).carrier) (a b : Nat) :
    zpPow p x (a + b) = zpMul p (zpPow p x a) (zpPow p x b) := by
  induction b with
  | zero =>
    rw [zpPow_zero, zpMul_comm, zpOne_mul]
    rfl
  | succ b ih =>
    show zpPow p x ((a + b) + 1) = zpMul p (zpPow p x a) (zpPow p x (b + 1))
    rw [zpPow_succ p x (a + b), ih, zpPow_succ p x b, zpMul_assoc]

/-- **定理 (M124F-1b): l 周期性** — ζ^l = 1 なら ζ^{e+lk} = ζ^e
    （k 帰納 + 加法則 + 単位律）。中心写像の well-definedness の核。 -/
theorem zpPow_mul_period (p l : Nat) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) :
    ∀ (k e : Nat), zpPow p ζ (e + l * k) = zpPow p ζ e := by
  intro k
  induction k with
  | zero => intro e; rfl
  | succ k ih =>
    intro e
    have hstep : e + l * (k + 1) = (e + l * k) + l := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
    rw [hstep, zpPow_add, hζl, zpMul_comm, zpOne_mul, ih e]

/-! ## M124F-2: Int の余りの一意性と中心写像 -/

/-- **定理 (M124F-2a): Euclid 余りの一意性** — 0 ≤ r < b かつ
    b ∣ a − r なら a % b = r。M120F `int_ediv_unique` の % 版:
    除算項を ∀ d r' 形の補助命題に隔離し `Int.mul_ediv_add_emod` 等で
    instantiate（omega が変数除数の / % を扱えないため、除算項を
    変数 d r' に押し込め、積 b·d は原子として omega へ）。 -/
theorem int_emod_unique (a b r : Int) (hb : 0 < b) (h0 : 0 ≤ r)
    (h1 : r < b) (hdvd : b ∣ a - r) : a % b = r := by
  obtain ⟨k, hk⟩ := hdvd
  have key : ∀ d r' : Int, b * d + r' = a → 0 ≤ r' → r' < b → r' = r := by
    intro d r' hd hr0 hrb
    cases Int.lt_or_le d k with
    | inl hlt =>
      have hm : b * d ≤ b * (k - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hb)
      have e : b * (k - 1) = b * k - b := by rw [Int.mul_sub, Int.mul_one]
      omega
    | inr hge =>
      cases Int.lt_or_le k d with
      | inl hlt2 =>
        have hm : b * (k + 1) ≤ b * d :=
          Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hb)
        have e : b * (k + 1) = b * k + b := by rw [Int.mul_add, Int.mul_one]
        omega
      | inr hge2 =>
        have hdk : d = k := by omega
        rw [hdk] at hd
        omega
  exact key (a / b) (a % b) (Int.mul_ediv_add_emod a b)
    (Int.emod_nonneg a (by omega)) (Int.emod_lt_of_pos a hb)

/-- **定理 (M124F-2b): 余りの合同不変性** — b ∣ z − z' なら
    z % b = z' % b（z' の余りが z の余りの特徴付けを満たすことを
    一意性で閉じる）。 -/
theorem int_emod_congr {b z z' : Int} (hb : 0 < b) (h : b ∣ z - z') :
    z % b = z' % b := by
  obtain ⟨k, hk⟩ := h
  have h2 := Int.mul_ediv_add_emod z' b
  have hr0 : 0 ≤ z' % b := Int.emod_nonneg z' (by omega)
  have hrb : z' % b < b := Int.emod_lt_of_pos z' hb
  refine int_emod_unique z b (z' % b) hb hr0 hrb ⟨k + z' / b, ?_⟩
  rw [Int.mul_add]
  omega

/-- **M124F-2c: 中心写像** — テータ中心の座標 z ∈ ℤ を μ_l の元
    ζ^{(z % l).toNat} に送る。z % l は非負（l > 0）なので toNat は
    忠実。M98F の rigidity が固定する (0,0,1) ↦ ζ の Z-線形拡張。 -/
def centerToMu (p l : Nat) (ζ : (Zp p).carrier) (z : Int) :
    (Zp p).carrier :=
  zpPow p ζ (z % ((l : Nat) : Int)).toNat

/-- **定理 (M124F-2d): 中心写像の well-definedness** — l ∣ z − z' なら
    centerToMu の値は一致する（余りの合同不変性 + congrArg）。 -/
theorem centerToMu_congr (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    {z z' : Int} (h : ((l : Nat) : Int) ∣ z - z') :
    centerToMu p l ζ z = centerToMu p l ζ z' := by
  have hb : (0 : Int) < ((l : Nat) : Int) := by omega
  show zpPow p ζ (z % ((l : Nat) : Int)).toNat
    = zpPow p ζ (z' % ((l : Nat) : Int)).toNat
  rw [int_emod_congr hb h]

/-! ## M124F-3: 準同型性（本丸1） -/

/-- **定理 (M124F-3a): 準同型性（本丸1）** —
    centerToMu (z + z') = centerToMu z · centerToMu z'。
    e := (z%l).toNat、e' := (z'%l).toNat とすると右辺 = ζ^{e+e'}
    （加法則）。(z+z')%l と e+e' のズレは l·δ（δ ∈ {0,1}）:
    `cases Nat.lt_or_ge (e + e') l` の 2 分岐で余りの一意性から
    Nat 等式を確立し、δ = 1 側は l 周期性で余分な l を消す。 -/
theorem centerToMu_add (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) (z z' : Int) :
    centerToMu p l ζ (z + z')
      = zpMul p (centerToMu p l ζ z) (centerToMu p l ζ z') := by
  have hb : (0 : Int) < ((l : Nat) : Int) := by omega
  have hz0 : 0 ≤ z % ((l : Nat) : Int) := Int.emod_nonneg z (by omega)
  have hzl : z % ((l : Nat) : Int) < ((l : Nat) : Int) :=
    Int.emod_lt_of_pos z hb
  have hz0' : 0 ≤ z' % ((l : Nat) : Int) := Int.emod_nonneg z' (by omega)
  have hzl' : z' % ((l : Nat) : Int) < ((l : Nat) : Int) :=
    Int.emod_lt_of_pos z' hb
  have hs0 : 0 ≤ (z + z') % ((l : Nat) : Int) :=
    Int.emod_nonneg (z + z') (by omega)
  -- (z+z') ≡ (z%l) + (z'%l) (mod l): 商の witness を明示
  have hdvd : ((l : Nat) : Int)
      ∣ (z + z') - (z % ((l : Nat) : Int) + z' % ((l : Nat) : Int)) := by
    refine ⟨z / ((l : Nat) : Int) + z' / ((l : Nat) : Int), ?_⟩
    have h1 := Int.mul_ediv_add_emod z ((l : Nat) : Int)
    have h2 := Int.mul_ediv_add_emod z' ((l : Nat) : Int)
    rw [Int.mul_add]
    omega
  have hcongr : (z + z') % ((l : Nat) : Int)
      = (z % ((l : Nat) : Int) + z' % ((l : Nat) : Int)) % ((l : Nat) : Int) :=
    int_emod_congr hb hdvd
  show zpPow p ζ ((z + z') % ((l : Nat) : Int)).toNat
    = zpMul p (zpPow p ζ (z % ((l : Nat) : Int)).toNat)
        (zpPow p ζ (z' % ((l : Nat) : Int)).toNat)
  rw [← zpPow_add]
  cases Nat.lt_or_ge
      ((z % ((l : Nat) : Int)).toNat + (z' % ((l : Nat) : Int)).toNat) l with
  | inl hlt =>
    -- δ = 0: 余りの和がそのまま (z+z') の余り
    have hsmall : (z % ((l : Nat) : Int) + z' % ((l : Nat) : Int))
          % ((l : Nat) : Int)
        = z % ((l : Nat) : Int) + z' % ((l : Nat) : Int) :=
      int_emod_unique _ _ _ hb (by omega) (by omega) ⟨0, by omega⟩
    have heq : ((z + z') % ((l : Nat) : Int)).toNat
        = (z % ((l : Nat) : Int)).toNat + (z' % ((l : Nat) : Int)).toNat := by
      omega
    rw [heq]
  | inr hge =>
    -- δ = 1: 余りの和は l だけ超過、周期性で吸収
    have hsmall : (z % ((l : Nat) : Int) + z' % ((l : Nat) : Int))
          % ((l : Nat) : Int)
        = z % ((l : Nat) : Int) + z' % ((l : Nat) : Int)
            - ((l : Nat) : Int) :=
      int_emod_unique _ _ _ hb (by omega) (by omega) ⟨1, by omega⟩
    have heq : (z % ((l : Nat) : Int)).toNat + (z' % ((l : Nat) : Int)).toNat
        = ((z + z') % ((l : Nat) : Int)).toNat + l * 1 := by
      omega
    rw [heq]
    exact (zpPow_mul_period p l ζ hζl 1
      (((z + z') % ((l : Nat) : Int)).toNat)).symm

/-- **定理 (M124F-3b): 零は単位に** — centerToMu 0 = 1
    （0 % l = 0、ζ^0 = 1）。 -/
theorem centerToMu_zero (p l : Nat) (ζ : (Zp p).carrier) :
    centerToMu p l ζ 0 = zpOne p := by
  show zpPow p ζ ((0 : Int) % ((l : Nat) : Int)).toNat = zpOne p
  rw [Int.zero_emod]
  exact zpPow_zero p ζ

/-- **定理 (M124F-3c): 中心生成元 ↦ μ_l 生成元** — centerToMu 1 = ζ。
    M98F の rigidity が固定する (0,0,1) が μ_l の生成元 ζ に対応する
    シクロトミック同期の要（1 % l = 1 は l ≥ 2 から）。 -/
theorem centerToMu_one_gen (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    centerToMu p l ζ 1 = ζ := by
  have hb : (0 : Int) < ((l : Nat) : Int) := by omega
  have h1 : (1 : Int) % ((l : Nat) : Int) = 1 :=
    int_emod_unique 1 ((l : Nat) : Int) 1 hb (by omega) (by omega)
      ⟨0, by omega⟩
  have h2 : zpPow p ζ 1 = ζ := by
    show zpPow p ζ (0 + 1) = ζ
    rw [zpPow_succ p ζ 0, zpPow_zero p ζ]
    exact zpOne_mul p ζ
  show zpPow p ζ ((1 : Int) % ((l : Nat) : Int)).toNat = ζ
  rw [h1]
  exact h2

/-! ## M124F-4: 忠実性（本丸2） -/

/-- **定理 (M124F-4a): 忠実性（本丸2）** — centerToMu z = 1 なら l ∣ z。
    e := (z%l).toNat < l。e ≠ 0 なら ζ^0 = 1 = ζ^e が冪の相異性
    hdist（0 < e < l）に矛盾 → e = 0 → z % l = 0 → l ∣ z
    （除算分解）。核がちょうど l·ℤ であることの片翼。 -/
theorem centerToMu_faithful (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (z : Int) (hz : centerToMu p l ζ z = zpOne p) :
    ((l : Nat) : Int) ∣ z := by
  have hb : (0 : Int) < ((l : Nat) : Int) := by omega
  have hz0 : 0 ≤ z % ((l : Nat) : Int) := Int.emod_nonneg z (by omega)
  have hzl : z % ((l : Nat) : Int) < ((l : Nat) : Int) :=
    Int.emod_lt_of_pos z hb
  have hdiv := Int.mul_ediv_add_emod z ((l : Nat) : Int)
  cases Nat.eq_zero_or_pos ((z % ((l : Nat) : Int)).toNat) with
  | inl h0 =>
    refine ⟨z / ((l : Nat) : Int), ?_⟩
    omega
  | inr hpos =>
    exfalso
    apply hdist 0 ((z % ((l : Nat) : Int)).toNat) hpos (by omega)
    rw [zpPow_zero]
    exact hz.symm

/-- **定理 (M124F-4b): 周期性（忠実性の逆向き）** — l ∣ z なら
    centerToMu z = 1（well-definedness で z ~ 0 → 零は単位に）。
    核がちょうど l·ℤ であることのもう片翼。 -/
theorem centerToMu_period (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (z : Int) (h : ((l : Nat) : Int) ∣ z) :
    centerToMu p l ζ z = zpOne p := by
  obtain ⟨k, hk⟩ := h
  have hc : centerToMu p l ζ z = centerToMu p l ζ 0 :=
    centerToMu_congr p l hl ζ ⟨k, by omega⟩
  rw [hc]
  exact centerToMu_zero p l ζ

/-! ## M124F-5: テータ群との接合 -/

/-- **定理 (M124F-5a): 中心の Heisenberg 積** —
    (0,0,z)·(0,0,z') = (0,0,z+z')（コサイクル項 0·0 は消滅、成分計算）。 -/
theorem theta_center_mul (z z' : Int) :
    thetaGrp.mul ((0, 0, z) : thetaGrp.carrier)
        ((0, 0, z') : thetaGrp.carrier)
      = ((0, 0, z + z') : Int × Int × Int) := by
  show ((0 : Int) + 0, (0 : Int) + 0, z + z' + (0 : Int) * 0)
    = (((0 : Int), (0 : Int), z + z') : Int × Int × Int)
  refine triple_ext (by omega) (by omega) (by omega)

/-- **定理 (M124F-5b): mod-l 降下** — thetaRelMod l で合同な中心
    (0,0,z) ~ (0,0,z') は centerToMu で同じ値に写る（第 3 成分の
    l-整除を well-definedness に渡す）。商群 thetaGrpMod l の中心
    類上で centerToMu が確定することの witness 形。 -/
theorem theta_center_descend (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    {z z' : Int}
    (h : thetaRelMod l ((0, 0, z) : thetaGrp.carrier)
      ((0, 0, z') : thetaGrp.carrier)) :
    centerToMu p l ζ z = centerToMu p l ζ z' := by
  obtain ⟨_, _, h3⟩ := h
  exact centerToMu_congr p l hl ζ h3

/-- **定理 (M124F-5c): 中心部分群 → μ_l の準同型** — centerToMu は
    Heisenberg 中心の積を μ_l の積に送る（M124F-5a + 本丸1 の合成）。
    [EtTh] のシクロトーム同期「テータ環境の中心 = 基礎体の μ_l」の
    群構造保存の離散核。 -/
theorem theta_center_to_mu_hom (p l : Nat) (hl : 2 ≤ l)
    (ζ : (Zp p).carrier) (hζl : zpPow p ζ l = zpOne p) (z z' : Int) :
    centerToMu p l ζ (thetaGrp.mul ((0, 0, z) : thetaGrp.carrier)
        ((0, 0, z') : thetaGrp.carrier)).2.2
      = zpMul p (centerToMu p l ζ z) (centerToMu p l ζ z') := by
  rw [theta_center_mul]
  exact centerToMu_add p l hl ζ hζl z z'

/-- **定理 (M124F-5d): ±-構造との両立** — M116F の ι は中心を固定する
    （thetaNeg_center）ので、centerToMu は ι で送っても値が変わらない。
    ±-同期はシクロトミック同期と自明に両立する。 -/
theorem theta_center_neg_invariant (p l : Nat) (ζ : (Zp p).carrier)
    (z : Int) :
    centerToMu p l ζ (thetaNeg.map ((0, 0, z) : thetaGrp.carrier)).2.2
      = centerToMu p l ζ z := by
  rw [thetaNeg_center]

/-! ## M124F-6: 総括レコード -/

/-- **M124F-6a: シクロトミック同期データ** — μ_l 生成元の存在
    （M121F の再輸出）と、任意の witness ζ についての中心写像の
    準同型性・0/1 の像・忠実性・周期性・mod-l 降下・±-両立の
    一括束ね。[EtTh] の cyclotomic synchronization の離散核。 -/
structure CyclotomicSyncData (p l : Nat) (hp : IsPrime p) (hl : 2 ≤ l)
    (hdvd : l ∣ p - 1) where
  /-- μ_l 生成元の存在（M121F mu_l_zp_exists の再輸出）。 -/
  gen_exists : ∃ z : (Zp p).carrier, zpPow p z l = zpOne p
    ∧ (∀ i j, i < j → j < l → zpPow p z i ≠ zpPow p z j)
    ∧ ∃ a : Int, ¬ ((p : Nat) : Int) ∣ a ∧ z = teich p hp a
  /-- 準同型性: centerToMu (z+z') = centerToMu z · centerToMu z'。 -/
  hom : ∀ ζ : (Zp p).carrier, zpPow p ζ l = zpOne p → ∀ z z' : Int,
    centerToMu p l ζ (z + z')
      = zpMul p (centerToMu p l ζ z) (centerToMu p l ζ z')
  /-- 零は単位に: centerToMu 0 = 1。 -/
  zero : ∀ ζ : (Zp p).carrier, centerToMu p l ζ 0 = zpOne p
  /-- 中心生成元 (0,0,1) ↦ μ_l 生成元 ζ。 -/
  gen : ∀ ζ : (Zp p).carrier, centerToMu p l ζ 1 = ζ
  /-- 忠実性: centerToMu z = 1 なら l ∣ z（冪相異な ζ について）。 -/
  faithful : ∀ ζ : (Zp p).carrier,
    (∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j) →
    ∀ z : Int, centerToMu p l ζ z = zpOne p → ((l : Nat) : Int) ∣ z
  /-- 周期性: l ∣ z なら centerToMu z = 1。 -/
  period : ∀ ζ : (Zp p).carrier, ∀ z : Int,
    ((l : Nat) : Int) ∣ z → centerToMu p l ζ z = zpOne p
  /-- mod-l 降下: thetaRelMod で合同な中心は同じ値に写る。 -/
  theta_descend : ∀ ζ : (Zp p).carrier, ∀ z z' : Int,
    thetaRelMod l ((0, 0, z) : thetaGrp.carrier)
      ((0, 0, z') : thetaGrp.carrier) →
    centerToMu p l ζ z = centerToMu p l ζ z'
  /-- 中心部分群 → μ_l の準同型（Heisenberg 積を μ_l の積に）。 -/
  center_hom : ∀ ζ : (Zp p).carrier, zpPow p ζ l = zpOne p →
    ∀ z z' : Int,
    centerToMu p l ζ (thetaGrp.mul ((0, 0, z) : thetaGrp.carrier)
        ((0, 0, z') : thetaGrp.carrier)).2.2
      = zpMul p (centerToMu p l ζ z) (centerToMu p l ζ z')
  /-- ±-両立: ι（M116F）で送っても centerToMu の値は不変。 -/
  pm_invariant : ∀ ζ : (Zp p).carrier, ∀ z : Int,
    centerToMu p l ζ (thetaNeg.map ((0, 0, z) : thetaGrp.carrier)).2.2
      = centerToMu p l ζ z

/-- **M124F-6b: witness 本体** — 全フィールドが既証明の純レコード。 -/
def cyclotomicSyncData (p l : Nat) (hp : IsPrime p) (hl : 2 ≤ l)
    (hdvd : l ∣ p - 1) : CyclotomicSyncData p l hp hl hdvd where
  gen_exists := mu_l_zp_exists p l hp (by omega) hdvd
  hom := fun ζ hζl z z' => centerToMu_add p l hl ζ hζl z z'
  zero := fun ζ => centerToMu_zero p l ζ
  gen := fun ζ => centerToMu_one_gen p l hl ζ
  faithful := fun ζ hdist z hz => centerToMu_faithful p l hl ζ hdist z hz
  period := fun ζ z h => centerToMu_period p l hl ζ z h
  theta_descend := fun ζ _ _ h => theta_center_descend p l hl ζ h
  center_hom := fun ζ hζl z z' => theta_center_to_mu_hom p l hl ζ hζl z z'
  pm_invariant := fun ζ z => theta_center_neg_invariant p l ζ z

/-- **定理 (M124F-6c): シクロトミック同期データの存在（M124F 見出し）**。 -/
theorem cyclotomicSync_exists (p l : Nat) (hp : IsPrime p) (hl : 2 ≤ l)
    (hdvd : l ∣ p - 1) : Nonempty (CyclotomicSyncData p l hp hl hdvd) :=
  ⟨cyclotomicSyncData p l hp hl hdvd⟩

end IUT
