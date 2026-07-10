/-
  IUT/Zp3ValuationRing.lean — A2a（柱A2: 実 p 進局所体 — 実 ℤ₃ の局所体パッケージ）

  ── 主要成果の分類: **[実／本物建設(b)]**（既存の実 ℤ₃ = lim ℤ/3ⁿ（M27 の逆極限環・
     LocalCFT/Ring）と実 p 除算（M43 PadicDivision）・実単数群 ℤ_p^×（M36 ZpUnits）・
     実 witness 付き付値分解（M91F ZpDomain の Hensel 帰納 zpValDecompose）の上に、
     実 ℤ₃ の**局所体としての内容**——付値関係 v(x)≥n・因数分解 x=3^v·u・極大イデアル
     3ℤ₃・剰余体 ℤ₃/3ℤ₃ ≅ 𝔽₃——を本物に確立する。toy 主語なし。主語は実 zpRing 3。）

  complete_pct 影響: **A2 A2a を前進**。M301F 抽象 valRingValuation の「具体的な離散
  付値の構成は後続」を初 discharge する実例（実 ℤ₃ 上の離散付値の関係形）。かつ M295F
  `resFieldMaximal`/`resFieldQuot`（剰余体機構）への**初の非自明実例代入**——従来の
  唯一の実例は「体 K の零イデアル (0)」だったが、本ファイルは**体でない**環 ℤ₃ の真の
  極大イデアル 3ℤ₃（= ker(proj 1)）を resFieldMaximal に代入し、剰余体 ℤ₃/3ℤ₃ ≅ 𝔽₃ を
  実構成する。極大性の witness（r=明示逆元 zpUnitInv・s=0）が即納する。

  * A2a-1 `z3vGe` / `z3vExact`          — 付値の関係形 v(x)≥n（x.val n = [0]）
  * A2a-2 `z3vGe_zero` / `z3vGe_zero_all` / `z3vGe_antitone` / `z3vGe_add`
          / `z3vGe_mul_left`            — 付値関係の基本律（超距離・整合族の遷移）
  * A2a-3 `z3v_unit_of_lev1`            — レベル1非零 ⟹ 単数（ℤ_p^×）
  * A2a-4 `z3vGe_p_pow_mul` / `rpow_zpRing_eq_zpPow`
          / `z3v_extract`               — **因数分解 x=3^v·u（Hensel 帰納・choice-free）**
                                          （M91F zpValDecompose の局所体版パッケージ）
  * A2a-5 `z3v_domain_pos` / `z3v_exact_mul`
                                        — 付値の加法性 v(xy)=v(x)+v(y)（正の witness 形）
  * A2a-6 `z3vMax`                      — 極大イデアル 3ℤ₃ = {v≥1}（primeSpecIdeal）
  * A2a-7 `z3vMaximal`                  — **resFieldMaximal 3ℤ₃（★機構への初の非自明実例・
                                          局所環性）**（maximal_witness = ⟨zpUnitInv,0,…⟩ 即納）
  * A2a-8 `z3vResidue` / `z3vResToF3` / `z3vF3ToRes` / `z3v_res_iso`
                                        — **剰余体 ℤ₃/3ℤ₃ ≅ 𝔽₃**（環同型データ）

  正直な限定（何が本物で何が honest 限定か・§3 準拠）:
  - **付値は「関数」でなく「関係」で持つ**（z3vGe/z3vExact）。total な付値関数 v : ℤ₃ → Nat
    は v(0)=∞ の総関数化と非零判定（Π⁰₂ = 排中律の断片）を要し choice-free に書けない。
    レベル述語（各 n での [0] 判定）が逆極限モデル固有の忠実版。この限定は消さない。
  - **整域性は「正の witness 形」** `¬v≥n+1 → ¬v≥m+1 → ¬v≥n+m+1`（z3v_domain_pos）。
    否定形 x≠0→y≠0→xy≠0 は witness 抽出に Markov を要するため採らない（M91F と同じ線）。
  - **p = 3 固定**（付値関係の基本律は zpRing p 一般で書き、極大イデアル・剰余体 𝔽₃ は
    p=3 で実例化）。完備化体 ℚ₃・ℤ₃ の完備性は本ファイルの範囲外（A2b/A2c 後続）。
  - 実 ℤ₃ は既存（新設せず消費）。既存 surrogate は消さない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
-/
import IUT.ResidueField
import IUT.ZpDomain
import IUT.ZpUnits
import IUT.RootsOfUnity
import IUT.Fermat

namespace IUT

/-! ## A2a-0: 主語の固定 -/

/-- 実 ℤ₃（既設の逆極限環・p=3 固定）。 -/
@[reducible] def z3 : CRing := zpRing 3

/-- ℤ_p 内の元 p（= 対角埋め込み toZp p の値）。付値の一様化子。 -/
@[reducible] def z3vP (p : Nat) : (Zp p).carrier := (toZp p).map ((p : Nat) : Int)

/-! ## A2a-1: 付値の関係形 -/

/-- **A2a-1a: 付値関係 v(x) ≥ n** — レベル n 成分が 0（x ≡ 0 mod pⁿ）。
    total 付値関数を避けた逆極限モデル固有の忠実版（§3.1）。 -/
def z3vGe (p : Nat) (x : (Zp p).carrier) (n : Nat) : Prop :=
  x.val n = Quot.mk (modCong (p ^ n)).rel 0

/-- **A2a-1b: 厳密付値 v(x) = n** — v(x) ≥ n かつ ¬ v(x) ≥ n+1。 -/
def z3vExact (p : Nat) (x : (Zp p).carrier) (n : Nat) : Prop :=
  z3vGe p x n ∧ ¬ z3vGe p x (n + 1)

/-! ## A2a-2: 付値関係の基本律 -/

/-- **A2a-2a: レベル 0 では常に v ≥ 0**（ℤ/p⁰ = ℤ/1 は自明群）。 -/
theorem z3vGe_zero (p : Nat) (x : (Zp p).carrier) : z3vGe p x 0 := by
  obtain ⟨a, ha⟩ := Quot.exists_rep (x.val 0)
  show x.val 0 = Quot.mk (modCong (p ^ 0)).rel 0
  rw [← ha]
  apply Quot.sound
  show ((p ^ 0 : Nat) : Int) ∣ a - 0
  refine ⟨a, ?_⟩
  rw [Nat.pow_zero]
  omega

/-- **A2a-2b: 零元は全レベルで v ≥ n**（v(0) = ∞）。 -/
theorem z3vGe_zero_all (p : Nat) : ∀ n, z3vGe p (zpRing p).zero n :=
  fun _ => rfl

/-- **A2a-2c: 反単調** — m ≤ n かつ v ≥ n なら v ≥ m（整合族の遷移で下降）。 -/
theorem z3vGe_antitone (p : Nat) (x : (Zp p).carrier) {m n : Nat}
    (hmn : m ≤ n) (hn : z3vGe p x n) : z3vGe p x m := by
  have hc := x.property hmn
  have hn' : x.val n = Quot.mk (modCong (p ^ n)).rel 0 := hn
  show x.val m = Quot.mk (modCong (p ^ m)).rel 0
  rw [← hc, hn']
  rfl

/-- **A2a-2d: 超距離 v(x+y) ≥ min の n 形** — v(x) ≥ n, v(y) ≥ n なら v(x+y) ≥ n
    （成分の加法計算）。 -/
theorem z3vGe_add (p : Nat) {x y : (Zp p).carrier} {n : Nat}
    (hx : z3vGe p x n) (hy : z3vGe p y n) : z3vGe p ((zpRing p).add x y) n := by
  have hx' : x.val n = Quot.mk (modCong (p ^ n)).rel 0 := hx
  have hy' : y.val n = Quot.mk (modCong (p ^ n)).rel 0 := hy
  show ((zpRing p).add x y).val n = Quot.mk (modCong (p ^ n)).rel 0
  show (zmod (p ^ n)).mul (x.val n) (y.val n) = Quot.mk (modCong (p ^ n)).rel 0
  rw [hx', hy']
  show Quot.mk (modCong (p ^ n)).rel (0 + 0) = Quot.mk (modCong (p ^ n)).rel 0
  rw [Int.add_zero]

/-- **A2a-2e: 環倍で v は保存（増加）** — v(x) ≥ n なら v(r·x) ≥ n。 -/
theorem z3vGe_mul_left (p : Nat) (r : (Zp p).carrier) {x : (Zp p).carrier} {n : Nat}
    (hx : z3vGe p x n) : z3vGe p (zpMul p r x) n := by
  have hx' : x.val n = Quot.mk (modCong (p ^ n)).rel 0 := hx
  show (zpMul p r x).val n = Quot.mk (modCong (p ^ n)).rel 0
  show zmodMul (p ^ n) (r.val n) (x.val n) = Quot.mk (modCong (p ^ n)).rel 0
  rw [hx']
  induction r.val n using Quot.ind
  rename_i ρ
  show Quot.mk (modCong (p ^ n)).rel (ρ * 0) = Quot.mk (modCong (p ^ n)).rel 0
  rw [Int.mul_zero]

/-! ## A2a-3: レベル 1 非零 ⟹ 単数 -/

/-- **A2a-3: ¬ v ≥ 1 ⟹ 単数**（レベル 1 の代表が p と素）。 -/
theorem z3v_unit_of_lev1 (p : Nat) (x : (Zp p).carrier) (h : ¬ z3vGe p x 1) :
    IsZpUnit p x := by
  obtain ⟨a, ha⟩ := Quot.exists_rep (x.val 1)
  refine ⟨a, ha.symm, ?_⟩
  intro hpa
  apply h
  show x.val 1 = Quot.mk (modCong (p ^ 1)).rel 0
  rw [← ha]
  apply Quot.sound
  show ((p ^ 1 : Nat) : Int) ∣ a - 0
  rw [Nat.pow_one]
  obtain ⟨k, hk⟩ := hpa
  exact ⟨k, by omega⟩

/-! ## A2a-4: 因数分解 x = pᵛ·u（Hensel 帰納・choice-free） -/

/-- **A2a-4a: pᶜ·w は v ≥ c**（一様化子倍は付値を持ち上げる。c の帰納・M91F の
    成分簿記 val_zero_p_mul）。 -/
theorem z3vGe_p_pow_mul (p : Nat) (w : (Zp p).carrier) (c : Nat) :
    z3vGe p (zpMul p (rpow (zpRing p) (z3vP p) c) w) c := by
  induction c with
  | zero => exact z3vGe_zero p _
  | succ c ih =>
    have heq : zpMul p (rpow (zpRing p) (z3vP p) (c + 1)) w
        = zpMul p (z3vP p) (zpMul p (rpow (zpRing p) (z3vP p) c) w) := by
      show zpMul p (zpMul p (rpow (zpRing p) (z3vP p) c) (z3vP p)) w
        = zpMul p (z3vP p) (zpMul p (rpow (zpRing p) (z3vP p) c) w)
      rw [zpMul_comm p (rpow (zpRing p) (z3vP p) c) (z3vP p),
        zpMul_assoc p (z3vP p) (rpow (zpRing p) (z3vP p) c) w]
    show z3vGe p (zpMul p (rpow (zpRing p) (z3vP p) (c + 1)) w) (c + 1)
    rw [heq]
    exact val_zero_p_mul p (zpMul p (rpow (zpRing p) (z3vP p) c) w) c ih

/-- **A2a-4b: 環冪 rpow と ℤ_p 冪 zpPow の一致**（設計インターフェース接着）。 -/
theorem rpow_zpRing_eq_zpPow (p : Nat) (a : (Zp p).carrier) (k : Nat) :
    rpow (zpRing p) a k = zpPow p a k := by
  induction k with
  | zero =>
    apply Subtype.ext
    funext n
    show Quot.mk (modCong (p ^ n)).rel 1 = zmodPow (p ^ n) (a.val n) 0
    induction a.val n using Quot.ind
    rfl
  | succ k ih =>
    show (zpRing p).mul (rpow (zpRing p) a k) a = zpPow p a (k + 1)
    rw [zpPow_succ, ← ih]
    rfl

/-- **A2a-4c（★中核）: 因数分解 x = pᵛ·u** — ¬ v ≥ n+1（非零 witness）を持つ元は、
    一意化子 p の冪 pᵛ（v ≤ n）と単数 u の積で、v が厳密付値。Hensel 帰納の witness
    構成（M91F zpValDecompose・zpDivP 再帰）＝choice-free。 -/
theorem z3v_extract (n : Nat) (x : (Zp 3).carrier) (h : ¬ z3vGe 3 x (n + 1)) :
    ∃ (v : Nat) (u : (Zp 3).carrier), v ≤ n ∧ IsZpUnit 3 u ∧
      x = zpMul 3 (zpPow 3 (z3vP 3) v) u ∧ z3vExact 3 x v := by
  obtain ⟨k, u, hk, hu, he⟩ := zpValDecompose 3 (by omega) (n + 1) x h
  refine ⟨k, u, by omega, z3v_unit_of_lev1 3 u hu, ?_, ?_, ?_⟩
  · rw [he, rpow_zpRing_eq_zpPow]
  · rw [he]
    exact z3vGe_p_pow_mul 3 u k
  · rw [he]
    exact neZeroAt_p_pow_mul 3 (by omega) u hu k

/-! ## A2a-5: 付値の加法性 v(xy) = v(x)+v(y) -/

/-- **A2a-5a: 整域性の正の witness 形** — ¬ v(x) ≥ n+1, ¬ v(y) ≥ m+1 なら
    ¬ v(xy) ≥ n+m+1（v(xy) ≤ n+m の系。M91F の付値分解 + p シフト）。 -/
theorem z3v_domain_pos {x y : (Zp 3).carrier} {n m : Nat}
    (hx : ¬ z3vGe 3 x (n + 1)) (hy : ¬ z3vGe 3 y (m + 1)) :
    ¬ z3vGe 3 (zpMul 3 x y) (n + m + 1) := by
  obtain ⟨k1, u1, hk1, hu1, he1⟩ := zpValDecompose 3 (by omega) (n + 1) x hx
  obtain ⟨k2, u2, hk2, hu2, he2⟩ := zpValDecompose 3 (by omega) (m + 1) y hy
  have hxy : zpMul 3 x y
      = zpMul 3 (rpow (zpRing 3) (z3vP 3) (k1 + k2)) (zpMul 3 u1 u2) := by
    rw [he1, he2, zpMul_mul_mul_comm 3 (rpow (zpRing 3) (z3vP 3) k1) u1
      (rpow (zpRing 3) (z3vP 3) k2) u2, rpow_add (zpRing 3) (z3vP 3) k1 k2]
    rfl
  have huv : NeZeroAt 3 (zpMul 3 u1 u2) 1 :=
    neZeroAt_one_mul 3 isPrime_three u1 u2 hu1 hu2
  have hmain : NeZeroAt 3 (zpMul 3 x y) (k1 + k2 + 1) := by
    rw [hxy]
    exact neZeroAt_p_pow_mul 3 (by omega) (zpMul 3 u1 u2) huv (k1 + k2)
  exact neZeroAt_mono 3 (zpMul 3 x y) (by omega : k1 + k2 + 1 ≤ n + m + 1) hmain

/-- **A2a-5b: 厳密付値の加法性** v(x)=a, v(y)=b ⟹ v(xy)=a+b。 -/
theorem z3v_exact_mul {x y : (Zp 3).carrier} {a b : Nat}
    (hx : z3vExact 3 x a) (hy : z3vExact 3 y b) :
    z3vExact 3 (zpMul 3 x y) (a + b) := by
  obtain ⟨hxge, hxgt⟩ := hx
  obtain ⟨hyge, hygt⟩ := hy
  obtain ⟨k1, u1, hk1, hu1, he1⟩ := zpValDecompose 3 (by omega) (a + 1) x hxgt
  obtain ⟨k2, u2, hk2, hu2, he2⟩ := zpValDecompose 3 (by omega) (b + 1) y hygt
  have hne1 : NeZeroAt 3 x (k1 + 1) := by
    rw [he1]; exact neZeroAt_p_pow_mul 3 (by omega) u1 hu1 k1
  have hne2 : NeZeroAt 3 y (k2 + 1) := by
    rw [he2]; exact neZeroAt_p_pow_mul 3 (by omega) u2 hu2 k2
  have hak1 : a ≤ k1 := by
    cases Nat.lt_or_ge k1 a with
    | inr h => exact h
    | inl h => exact absurd hxge (neZeroAt_mono 3 x (by omega) hne1)
  have hbk2 : b ≤ k2 := by
    cases Nat.lt_or_ge k2 b with
    | inr h => exact h
    | inl h => exact absurd hyge (neZeroAt_mono 3 y (by omega) hne2)
  have hxy : zpMul 3 x y
      = zpMul 3 (rpow (zpRing 3) (z3vP 3) (k1 + k2)) (zpMul 3 u1 u2) := by
    rw [he1, he2, zpMul_mul_mul_comm 3 (rpow (zpRing 3) (z3vP 3) k1) u1
      (rpow (zpRing 3) (z3vP 3) k2) u2, rpow_add (zpRing 3) (z3vP 3) k1 k2]
    rfl
  have hge_big : z3vGe 3 (zpMul 3 x y) (k1 + k2) := by
    rw [hxy]
    exact z3vGe_p_pow_mul 3 (zpMul 3 u1 u2) (k1 + k2)
  refine ⟨z3vGe_antitone 3 (zpMul 3 x y) (by omega : a + b ≤ k1 + k2) hge_big, ?_⟩
  exact z3v_domain_pos hxgt hygt

/-! ## A2a-6: 極大イデアル 3ℤ₃ = {v ≥ 1} -/

/-- **A2a-6: 極大イデアル 3ℤ₃** = ker(proj 1) = {x | v(x) ≥ 1}（primeSpecIdeal）。 -/
def z3vMax : primeSpecIdeal (zpRing 3) where
  mem := fun x => z3vGe 3 x 1
  zero_mem := z3vGe_zero_all 3 1
  add_mem := fun _ _ hx hy => z3vGe_add 3 hx hy
  smul_mem := fun r _ hx => z3vGe_mul_left 3 r hx

/-! ## A2a-7: resFieldMaximal（★機構への初の非自明実例・局所環性） -/

/-- **A2a-7（★）: 3ℤ₃ は極大イデアル**（resFieldMaximal）——ℤ₃ は局所環。
    真イデアル性は 3 ∤ 1、極大性の witness は x∉m（= 単数）に対し
    r = 明示逆元 zpUnitInv・s = 0 で r·x + 0 = 1 が**即納**（zpUnitInv_mul）。
    M295F `resFieldMaximal` 機構への**体でない環における初の非自明実例代入**。 -/
def z3vMaximal : resFieldMaximal (zpRing 3) where
  toprimeSpecIdeal := z3vMax
  proper := by
    intro h
    have h'' : Quot.mk (modCong (3 ^ 1)).rel 1 = Quot.mk (modCong (3 ^ 1)).rel 0 := h
    obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (3 ^ 1)) h''
    rw [Nat.pow_one] at hk
    omega
  maximal_witness := fun x hx => by
    have hu : IsZpUnit 3 x := z3v_unit_of_lev1 3 x hx
    refine ⟨zpUnitInv 3 isPrime_three x hu, (zpRing 3).zero, z3vMax.zero_mem, ?_⟩
    show (zpRing 3).add ((zpRing 3).mul (zpUnitInv 3 isPrime_three x hu) x) (zpRing 3).zero
      = (zpRing 3).one
    rw [CRing.add_zero (zpRing 3) ((zpRing 3).mul (zpUnitInv 3 isPrime_three x hu) x)]
    exact zpUnitInv_mul 3 isPrime_three x hu

/-! ## A2a-8: 剰余体 ℤ₃/3ℤ₃ ≅ 𝔽₃ -/

/-- **A2a-8a: 剰余環 ℤ₃/3ℤ₃**（M295F resFieldQuot の実例）。 -/
def z3vResidue : CRing := resFieldQuot z3vMax

/-- レベル 1 の差が 3ℤ₃ に属せばレベル 1 成分は一致（剰余写像の well-defined 性）。 -/
theorem z3v_val1_eq_of_mem {a b : (Zp 3).carrier}
    (h : z3vGe 3 ((zpRing 3).add a ((zpRing 3).neg b)) 1) : a.val 1 = b.val 1 := by
  obtain ⟨α, hα⟩ := Quot.exists_rep (a.val 1)
  obtain ⟨β, hβ⟩ := Quot.exists_rep (b.val 1)
  have h' : (zmod (3 ^ 1)).mul (a.val 1) ((zmod (3 ^ 1)).inv (b.val 1))
      = Quot.mk (modCong (3 ^ 1)).rel 0 := h
  rw [← hα, ← hβ] at h'
  have h'' : Quot.mk (modCong (3 ^ 1)).rel (α + (-β)) = Quot.mk (modCong (3 ^ 1)).rel 0 := h'
  obtain ⟨k, hk⟩ := quot_exact intGrp (modCong (3 ^ 1)) h''
  rw [← hα, ← hβ]
  apply Quot.sound
  show ((3 ^ 1 : Nat) : Int) ∣ α - β
  refine ⟨k, ?_⟩
  omega

/-- **A2a-8b: 剰余体 → 𝔽₃**（[x] ↦ x のレベル 1 成分）。 -/
def z3vResToF3 : RingHom z3vResidue (zmodRing 3) where
  map := Quot.lift (fun x => x.val 1) (fun _ _ hab => z3v_val1_eq_of_mem hab)
  map_add := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    rfl
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    rfl
  map_one := rfl

/-- **A2a-8c: 𝔽₃ → 剰余体**（[a] ↦ [toZp₃ a]）。 -/
def z3vF3ToRes : RingHom (zmodRing 3) z3vResidue where
  map := Quot.lift (fun a => Quot.mk (resFieldRel z3vMax) ((toZp 3).map a))
    (fun a a' hab => by
      apply Quot.sound
      show z3vGe 3 ((zpRing 3).add ((toZp 3).map a) ((zpRing 3).neg ((toZp 3).map a'))) 1
      show (zmod (3 ^ 1)).mul (((toZp 3).map a).val 1)
          ((zmod (3 ^ 1)).inv (((toZp 3).map a').val 1))
        = Quot.mk (modCong (3 ^ 1)).rel 0
      show Quot.mk (modCong (3 ^ 1)).rel (a + (-a')) = Quot.mk (modCong (3 ^ 1)).rel 0
      apply Quot.sound
      show ((3 ^ 1 : Nat) : Int) ∣ (a + (-a')) - 0
      obtain ⟨k, hk⟩ := hab
      refine ⟨k, ?_⟩
      rw [Nat.pow_one]
      omega)
  map_add := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i a'
    show Quot.mk (resFieldRel z3vMax) ((toZp 3).map (a + a'))
       = Quot.mk (resFieldRel z3vMax) ((zpRing 3).add ((toZp 3).map a) ((toZp 3).map a'))
    exact congrArg (Quot.mk (resFieldRel z3vMax)) ((toZpRing 3).map_add a a')
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i a'
    show Quot.mk (resFieldRel z3vMax) ((toZp 3).map (a * a'))
       = Quot.mk (resFieldRel z3vMax) ((zpRing 3).mul ((toZp 3).map a) ((toZp 3).map a'))
    exact congrArg (Quot.mk (resFieldRel z3vMax)) ((toZpRing 3).map_mul a a')
  map_one := congrArg (Quot.mk (resFieldRel z3vMax)) ((toZpRing 3).map_one)

/-- 𝔽₃ → 剰余体 → 𝔽₃ は恒等（レベル 1 成分は代表を保つ）。 -/
theorem z3v_resToF3_f3ToRes (w : (zmodRing 3).carrier) :
    z3vResToF3.map (z3vF3ToRes.map w) = w := by
  induction w using Quot.ind; rename_i a
  show ((toZp 3).map a).val 1 = Quot.mk (modCong 3).rel a
  rfl

/-- 剰余体 → 𝔽₃ → 剰余体 は恒等（レベル 1 成分の代表で復元）。 -/
theorem z3v_f3ToRes_resToF3 (z : z3vResidue.carrier) :
    z3vF3ToRes.map (z3vResToF3.map z) = z := by
  induction z using Quot.ind; rename_i x
  obtain ⟨α, hα⟩ := Quot.exists_rep (x.val 1)
  have hxv : x.val 1 = Quot.mk (modCong (3 ^ 1)).rel α := hα.symm
  show z3vF3ToRes.map (x.val 1) = Quot.mk (resFieldRel z3vMax) x
  rw [hxv]
  show Quot.mk (resFieldRel z3vMax) ((toZp 3).map α) = Quot.mk (resFieldRel z3vMax) x
  apply Quot.sound
  show z3vGe 3 ((zpRing 3).add ((toZp 3).map α) ((zpRing 3).neg x)) 1
  show (zmod (3 ^ 1)).mul (((toZp 3).map α).val 1) ((zmod (3 ^ 1)).inv (x.val 1))
     = Quot.mk (modCong (3 ^ 1)).rel 0
  rw [hxv]
  show Quot.mk (modCong (3 ^ 1)).rel (α + (-α)) = Quot.mk (modCong (3 ^ 1)).rel 0
  apply Quot.sound
  show ((3 ^ 1 : Nat) : Int) ∣ (α + (-α)) - 0
  exact ⟨0, by omega⟩

/-- **A2a-8d: 環同型データ ℤ₃/3ℤ₃ ≅ 𝔽₃**。 -/
structure z3vRingEquivData (R S : CRing) where
  toFun : RingHom R S
  invFun : RingHom S R
  left_inv : ∀ x, invFun.map (toFun.map x) = x
  right_inv : ∀ y, toFun.map (invFun.map y) = y

/-- **A2a-8e（★）: 剰余体同型 ℤ₃/3ℤ₃ ≅ 𝔽₃**。 -/
def z3v_res_iso : z3vRingEquivData z3vResidue (zmodRing 3) where
  toFun := z3vResToF3
  invFun := z3vF3ToRes
  left_inv := z3v_f3ToRes_resToF3
  right_inv := z3v_resToF3_f3ToRes

end IUT
