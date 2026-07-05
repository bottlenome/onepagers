/-
  IUT/IntegralExtension.lean — M300F: 整元・整閉包（数体の整数環の土台）
  ── 柱A「数環の土台（整拡大・整閉包）」の本物の先行建設

  主要成果の分類: **[実]**（本物の可換環拡大 R⊆S 上の整元・整閉包の実構成。
  骨格・模型・代理ではなく、可換環準同型 ι : R→S と S の元 s に対する
  「s が R 上モニック多項式の根であること」を自前のモニック多項式評価で
  本物に定義し、その性質を core Lean のみで証明する）。

  **complete_pct 影響: 柱A 数環の土台の本物の先行建設（整元の定義・
  基底元の整性・スカラー R 倍の整性・体の整閉性）**。数体 K の整数環 O_K・
  遠アーベル復元の局所整構造は「基底環 R ⊆ 拡大環 S の中で R 上整な元全体
  R̄」を土台語彙とするが、既存資産（M264F 体・M273F 最小多項式）は
  「体上代数的元」までで、**環拡大上の整元・整閉包（整の判定・基底整性・
  スカラー倍の整性・整閉包が環をなす骨組み・整閉性）は 0 ファイル**であった。
  本モジュールがそれを可換環準同型 ι : R→S の上で本物に構成する。

  * M300F-1 `intExtPow` / `intExtEvalSum` — S 内のべき乗と、R 係数モニック
    多項式の「低次部分」 Σ_{i<n} ι(aᵢ)·sⁱ の自前評価（構造的再帰）。
  * M300F-2 `IsIntegral ι s` — **整元**: ∃ n≥1, ∃ 係数 a:ℕ→R,
    sⁿ + Σ_{i<n} ι(aᵢ)sⁱ = 0（s は R 上モニック多項式の根）。
  * M300F-3 環準同型の基本則（本物）: `intExtRingHomZero`（ι0=0）・
    `intExtRingHomNeg`（ι(-r)=-ιr）・`intExtRingHomPow`（ι(xⁿ)=(ιx)ⁿ）と、
    可換環の補題 `intExtMulOne`/`intExtAddZero`/`intExtAddRightCancel`/
    `intExtMulMulMulComm`/`intExtPowAdd`/`intExtPowMul`。
  * M300F-4 `intExt_base_integral` — **基底元は整**（ι(r) は 1 次モニック
    X−r の根）。**本物**（sorry 皆無）。
  * M300F-5 `intExt_zero_integral`/`intExt_one_integral` — 0,1 は整
    （ι0=0・ι1=1 と基底整性から）。**本物**。
  * M300F-6 `intExtEvalSumScale`/`intExt_scalar_integral` — **整元の R
    スカラー倍は整**: s 整 ⟹ ι(r)·s 整。証明は「sⁿ+Σaᵢsⁱ=0 の両辺に
    (ιr)ⁿ を掛け、係数を bᵢ=r^{n-i}aᵢ に組み替える」本物の可換環計算
    （rⁿ の分配・(ιr·s)ᵏ=(ιr)ᵏsᵏ・rⁿ=r^{n-k}rᵏ を全て証明して閉じる）。
    **本物**（sorry 皆無・新規 choice 皆無）。
  * M300F-7 `IntExtClosureSubring`/`intExt_closure_of_witness`/
    `intExt_id_closure` — **整閉包が部分環をなす骨組み**（0,1,基底,スカラー倍
    の整性は本物のフィールドで充足、和・積の閉性は honest witness フィールド）。
    恒等拡大 R⊆R では全元が基底整のため和・積の閉性も**本物**で充足する
    完全実インスタンス `intExt_id_closure` を与える。
  * M300F-8 `intExtComp`/`IntExtTower`/`intExt_tower_id` — 整拡大の**推移性**
    の骨組み（合成環準同型は本物、一般の推移性は honest witness フィールド、
    恒等塔 `intExt_tower_id` は本物）。
  * M300F-9 `IsIntegrallyClosed`/`intExt_id_integrallyClosed`/
    `intExt_field_integrallyClosed` — **整閉性**の定義と、**体は整閉**
    （Frac(K)=K の中で K の整元は全て K に入る）を**本物**で。
  * M300F-10 capstone `IntegralExtensionData`/`intExt_exists`/
    `intExt_closure_data`/`intExt_field_extensionData` — 整拡大データの束ね
    と存在（ℤ⊆ℤ・任意 R⊆R・体 K⊆K の実例）。

  正直な限定（何が本物で何が honest witness か・消去/弱化はしない）:
   - **本物**（完全証明・sorry 皆無・新規 Classical.choice 皆無・禁止タクティク
     不使用）: 整元 `IsIntegral` の定義そのもの、基底元の整性、0/1 の整性、
     **整元の R スカラー倍の整性**（本物の可換環計算で完全）、環準同型の
     0/負/べきの保存、体の整閉性、恒等拡大での整閉包が部分環をなすこと。
   - **honest witness（後続で本物化）1**: 一般の整元 a,b に対する
     「a+b・a·b が整」の完全証明は、R[a,b] が有限生成 R 加群であること＝
     Cayley–Hamilton による整の判定を要し重い。本モジュールは
     `IntExtClosureSubring` の `add_mem`/`mul_mem` を **witness フィールド
     （仮説）** として受け、恒等拡大でのみ本物に充足する。**有限生成加群
     による一般の本証明は後続**（消去・弱化はしない）。
   - **honest witness 2**: 整拡大の推移性 `IntExtTower.transitive` も同様に
     witness フィールドで受け、恒等塔でのみ本物に充足。一般の推移性の
     本証明（合成モニック多項式の構成＝有限生成の推移）は後続。
   - **honest 補足**: 整閉性は「ι:R→S の中で S の整元が ι の像に入る」
     で定式化し、体 K は ι=恒等（Frac(K)=K）で自明に整閉。数体 O_K の
     整閉包の普遍性は M303F（別モジュール）で本物化予定。

  全て選択公理不使用（新規 choice を証明本体に導入しない）。
-/
import IUT.Ring
import IUT.Field

namespace IUT

/-! ## M300F-1: べき乗とモニック多項式の低次部分の自前評価 -/

/-- **M300F-1a: S 内のべき乗** sᵏ（構造的再帰）。 -/
def intExtPow (S : CRing) (s : S.carrier) : Nat → S.carrier
  | 0 => S.one
  | (k+1) => S.mul s (intExtPow S s k)

/-- **M300F-1b: モニック多項式の低次部分の評価** Σ_{i<n} ι(aᵢ)·sⁱ
    （構造的再帰。n は「何項まで足すか」）。 -/
def intExtEvalSum {R S : CRing} (ι : RingHom R S) (a : Nat → R.carrier)
    (s : S.carrier) : Nat → S.carrier
  | 0 => S.zero
  | (k+1) => S.add (intExtEvalSum ι a s k) (S.mul (ι.map (a k)) (intExtPow S s k))

/-! ## M300F-2: 整元の定義 -/

/-- **M300F-2: 整元** — `s : S` が `ι : R→S` の下で R 上整とは、
    ∃ n≥1 と係数 a : ℕ→R で `sⁿ + Σ_{i<n} ι(aᵢ)sⁱ = 0`
    （s が R 上のモニック多項式 Xⁿ + a_{n-1}X^{n-1} + … + a₀ の根）。 -/
def IsIntegral {R S : CRing} (ι : RingHom R S) (s : S.carrier) : Prop :=
  ∃ n : Nat, ∃ a : Nat → R.carrier,
    1 ≤ n ∧ S.add (intExtPow S s n) (intExtEvalSum ι a s n) = S.zero

/-! ## M300F-3: 可換環・環準同型の基本補題（本物） -/

/-- a·1 = a（可換性から）。 -/
theorem intExtMulOne (R : CRing) (a : R.carrier) : R.mul a R.one = a := by
  rw [R.mul_comm, R.one_mul]

/-- a+0 = a（可換性から）。 -/
theorem intExtAddZero (R : CRing) (a : R.carrier) : R.add a R.zero = a := by
  rw [R.add_comm, R.zero_add]

/-- 加法の右簡約（可換 + 左簡約）。 -/
theorem intExtAddRightCancel (R : CRing) {a b c : R.carrier}
    (h : R.add a c = R.add b c) : a = b := by
  have h2 : R.add c a = R.add c b := by
    rw [R.add_comm c a, R.add_comm c b]
    exact h
  exact R.add_left_cancel h2

/-- 4 因子の入れ替え (a·b)·(c·d) = (a·c)·(b·d)（結合・可換から）。 -/
theorem intExtMulMulMulComm (R : CRing) (a b c d : R.carrier) :
    R.mul (R.mul a b) (R.mul c d) = R.mul (R.mul a c) (R.mul b d) := by
  rw [R.mul_assoc a b (R.mul c d), ← R.mul_assoc b c d, R.mul_comm b c,
    R.mul_assoc c b d, ← R.mul_assoc a c (R.mul b d)]

/-- **べきの加法則** x^{m+n} = xᵐ·xⁿ（第二引数で帰納）。 -/
theorem intExtPowAdd (S : CRing) (x : S.carrier) (m n : Nat) :
    intExtPow S x (m + n) = S.mul (intExtPow S x m) (intExtPow S x n) := by
  induction n with
  | zero => exact (intExtMulOne S (intExtPow S x m)).symm
  | succ n ih =>
    show S.mul x (intExtPow S x (m + n))
        = S.mul (intExtPow S x m) (S.mul x (intExtPow S x n))
    rw [ih, ← S.mul_assoc x (intExtPow S x m) (intExtPow S x n),
      S.mul_comm x (intExtPow S x m),
      S.mul_assoc (intExtPow S x m) x (intExtPow S x n)]

/-- **べきの積分配** (x·y)ᵏ = xᵏ·yᵏ（可換性から）。 -/
theorem intExtPowMul (S : CRing) (x y : S.carrier) (k : Nat) :
    intExtPow S (S.mul x y) k = S.mul (intExtPow S x k) (intExtPow S y k) := by
  induction k with
  | zero => exact (S.one_mul S.one).symm
  | succ k ih =>
    show S.mul (S.mul x y) (intExtPow S (S.mul x y) k)
        = S.mul (S.mul x (intExtPow S x k)) (S.mul y (intExtPow S y k))
    rw [ih]
    exact intExtMulMulMulComm S x y (intExtPow S x k) (intExtPow S y k)

/-- **環準同型はべきを保つ** ι(xᵏ) = (ιx)ᵏ。 -/
theorem intExtRingHomPow {R S : CRing} (ι : RingHom R S) (x : R.carrier) (k : Nat) :
    ι.map (intExtPow R x k) = intExtPow S (ι.map x) k := by
  induction k with
  | zero => exact ι.map_one
  | succ k ih =>
    show ι.map (R.mul x (intExtPow R x k))
        = S.mul (ι.map x) (intExtPow S (ι.map x) k)
    rw [ι.map_mul, ih]

/-- **環準同型は 0 を保つ** ι(0) = 0。 -/
theorem intExtRingHomZero {R S : CRing} (ι : RingHom R S) :
    ι.map R.zero = S.zero := by
  have h1 : ι.map R.zero = S.add (ι.map R.zero) (ι.map R.zero) := by
    rw [← ι.map_add, R.zero_add]
  have h2 : S.add (ι.map R.zero) S.zero = S.add (ι.map R.zero) (ι.map R.zero) := by
    rw [intExtAddZero S (ι.map R.zero)]
    exact h1
  exact (S.add_left_cancel h2).symm

/-- **環準同型は負を保つ** ι(−r) = −ι(r)。 -/
theorem intExtRingHomNeg {R S : CRing} (ι : RingHom R S) (r : R.carrier) :
    ι.map (R.neg r) = S.neg (ι.map r) := by
  have h1 : S.add (ι.map (R.neg r)) (ι.map r) = S.zero := by
    rw [← ι.map_add, R.neg_add, intExtRingHomZero]
  have h2 : S.add (S.neg (ι.map r)) (ι.map r) = S.zero := S.neg_add (ι.map r)
  have h3 : S.add (ι.map (R.neg r)) (ι.map r) = S.add (S.neg (ι.map r)) (ι.map r) := by
    rw [h1, h2]
  exact intExtAddRightCancel S h3

/-! ## M300F-4: 基底元は整（本物） -/

/-- **M300F-4: 基底元 ι(r) は R 上整**（1 次モニック X − r の根）。 -/
theorem intExt_base_integral {R S : CRing} (ι : RingHom R S) (r : R.carrier) :
    IsIntegral ι (ι.map r) := by
  refine ⟨1, fun _ => R.neg r, Nat.le_refl 1, ?_⟩
  show S.add (S.mul (ι.map r) S.one)
        (S.add S.zero (S.mul (ι.map (R.neg r)) S.one)) = S.zero
  rw [intExtMulOne S (ι.map r), intExtMulOne S (ι.map (R.neg r)), S.zero_add,
    intExtRingHomNeg ι r, S.add_comm (ι.map r) (S.neg (ι.map r)), S.neg_add]

/-! ## M300F-5: 0,1 は整（本物） -/

/-- **M300F-5a: 0 は整**（0 = ι(0) は基底整）。 -/
theorem intExt_zero_integral {R S : CRing} (ι : RingHom R S) :
    IsIntegral ι S.zero := by
  have h := intExt_base_integral ι R.zero
  rw [intExtRingHomZero] at h
  exact h

/-- **M300F-5b: 1 は整**（1 = ι(1) は基底整）。 -/
theorem intExt_one_integral {R S : CRing} (ι : RingHom R S) :
    IsIntegral ι S.one := by
  have h := intExt_base_integral ι R.one
  rw [ι.map_one] at h
  exact h

/-! ## M300F-6: 整元の R スカラー倍は整（本物） -/

/-- **M300F-6a: スケール補題** — (ιr)ⁿ を低次部分 Σ_{i<k} ι(aᵢ)sⁱ に掛けると、
    係数を bᵢ = r^{n-i}·aᵢ に組み替えた (ιr·s) の低次部分に一致する
    （k ≤ n の全 k で成立。項ごとに (ιr)ⁿ·(ι(aᵢ)sⁱ) = ι(bᵢ)·(ιr·s)ⁱ を検証）。 -/
theorem intExtEvalSumScale {R S : CRing} (ι : RingHom R S) (a : Nat → R.carrier)
    (s : S.carrier) (r : R.carrier) (n : Nat) :
    ∀ k, k ≤ n →
      S.mul (intExtPow S (ι.map r) n) (intExtEvalSum ι a s k)
        = intExtEvalSum ι (fun i => R.mul (intExtPow R r (n - i)) (a i))
            (S.mul (ι.map r) s) k := by
  intro k
  induction k with
  | zero => intro _; exact S.mul_zero (intExtPow S (ι.map r) n)
  | succ k ih =>
    intro hk1
    have hk : k ≤ n := by omega
    show S.mul (intExtPow S (ι.map r) n)
          (S.add (intExtEvalSum ι a s k) (S.mul (ι.map (a k)) (intExtPow S s k)))
        = S.add
            (intExtEvalSum ι (fun i => R.mul (intExtPow R r (n - i)) (a i))
              (S.mul (ι.map r) s) k)
            (S.mul (ι.map (R.mul (intExtPow R r (n - k)) (a k)))
              (intExtPow S (S.mul (ι.map r) s) k))
    have hRHS :
        S.mul (ι.map (R.mul (intExtPow R r (n - k)) (a k)))
            (intExtPow S (S.mul (ι.map r) s) k)
          = S.mul (intExtPow S (ι.map r) n)
              (S.mul (ι.map (a k)) (intExtPow S s k)) := by
      rw [ι.map_mul, intExtRingHomPow, intExtPowMul, intExtMulMulMulComm,
        ← intExtPowAdd, Nat.sub_add_cancel hk]
    rw [S.left_distrib, ih hk, hRHS]

/-- **M300F-6b: 整元の R スカラー倍は整** — s 整 ⟹ ι(r)·s 整。
    sⁿ+Σaᵢsⁱ=0 の両辺に (ιr)ⁿ を掛け、係数を bᵢ=r^{n-i}aᵢ に組み替える。 -/
theorem intExt_scalar_integral {R S : CRing} (ι : RingHom R S) (r : R.carrier)
    {s : S.carrier} (hs : IsIntegral ι s) : IsIntegral ι (S.mul (ι.map r) s) := by
  obtain ⟨n, a, hn, heq⟩ := hs
  refine ⟨n, fun i => R.mul (intExtPow R r (n - i)) (a i), hn, ?_⟩
  have hscale := intExtEvalSumScale ι a s r n n (Nat.le_refl n)
  have key :
      S.mul (intExtPow S (ι.map r) n)
          (S.add (intExtPow S s n) (intExtEvalSum ι a s n))
        = S.add (intExtPow S (S.mul (ι.map r) s) n)
            (intExtEvalSum ι (fun i => R.mul (intExtPow R r (n - i)) (a i))
              (S.mul (ι.map r) s) n) := by
    rw [S.left_distrib, hscale, ← intExtPowMul]
  rw [heq, S.mul_zero] at key
  exact key.symm

/-! ## M300F-7: 整閉包が部分環をなす骨組み -/

/-- **M300F-7a: 整閉包の部分環データ** — R̄ = {s | s は R 上整} が
    0,1 を含み和・積・R スカラー倍で閉じることを束ねる。0/1/基底/スカラー倍
    の整性は本物、和・積の閉性は honest witness（後続で有限生成加群により本物化）。 -/
structure IntExtClosureSubring (R S : CRing) (ι : RingHom R S) where
  /-- 0 は整（本物）。 -/
  zero_mem : IsIntegral ι S.zero
  /-- 1 は整（本物）。 -/
  one_mem : IsIntegral ι S.one
  /-- 基底元は整（本物）。 -/
  base_mem : ∀ r : R.carrier, IsIntegral ι (ι.map r)
  /-- R スカラー倍で閉じる（本物）。 -/
  scalar_mem : ∀ (r : R.carrier) (s : S.carrier),
    IsIntegral ι s → IsIntegral ι (S.mul (ι.map r) s)
  /-- 和で閉じる（honest witness）。 -/
  add_mem : ∀ (a b : S.carrier),
    IsIntegral ι a → IsIntegral ι b → IsIntegral ι (S.add a b)
  /-- 積で閉じる（honest witness）。 -/
  mul_mem : ∀ (a b : S.carrier),
    IsIntegral ι a → IsIntegral ι b → IsIntegral ι (S.mul a b)

/-- **M300F-7b: witness からの整閉包部分環** — 和・積の閉性の witness を受け、
    0/1/基底/スカラー倍は本物のフィールドで充足して部分環データを組む。 -/
def intExt_closure_of_witness {R S : CRing} (ι : RingHom R S)
    (hadd : ∀ (a b : S.carrier),
      IsIntegral ι a → IsIntegral ι b → IsIntegral ι (S.add a b))
    (hmul : ∀ (a b : S.carrier),
      IsIntegral ι a → IsIntegral ι b → IsIntegral ι (S.mul a b)) :
    IntExtClosureSubring R S ι where
  zero_mem := intExt_zero_integral ι
  one_mem := intExt_one_integral ι
  base_mem := intExt_base_integral ι
  scalar_mem := fun r _ hs => intExt_scalar_integral ι r hs
  add_mem := hadd
  mul_mem := hmul

/-! ## M300F-7c: 恒等環準同型と恒等拡大での完全実インスタンス -/

/-- **恒等環準同型** id : R → R。 -/
def intExtIdHom (R : CRing) : RingHom R R where
  map := fun x => x
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_one := rfl

/-- **恒等拡大では全元が整**（各 x は基底元 id(x)=x）。 -/
theorem intExt_id_all_integral (R : CRing) (x : R.carrier) :
    IsIntegral (intExtIdHom R) x :=
  intExt_base_integral (intExtIdHom R) x

/-- **M300F-7c: 恒等拡大 R⊆R の整閉包は完全な部分環**（和・積の閉性も
    全元が基底整ゆえ本物で充足）。honest witness を使わない実インスタンス。 -/
def intExt_id_closure (R : CRing) : IntExtClosureSubring R R (intExtIdHom R) where
  zero_mem := intExt_zero_integral (intExtIdHom R)
  one_mem := intExt_one_integral (intExtIdHom R)
  base_mem := intExt_base_integral (intExtIdHom R)
  scalar_mem := fun r _ hs => intExt_scalar_integral (intExtIdHom R) r hs
  add_mem := fun a b _ _ => intExt_id_all_integral R (R.add a b)
  mul_mem := fun a b _ _ => intExt_id_all_integral R (R.mul a b)

/-! ## M300F-8: 整拡大の推移性（骨組み） -/

/-- **合成環準同型** ψ∘φ : R → T（本物）。 -/
def intExtComp {R S T : CRing} (φ : RingHom R S) (ψ : RingHom S T) :
    RingHom R T where
  map := fun r => ψ.map (φ.map r)
  map_add := by intro a b; rw [φ.map_add, ψ.map_add]
  map_mul := by intro a b; rw [φ.map_mul, ψ.map_mul]
  map_one := by rw [φ.map_one, ψ.map_one]

/-- **合成の基底元は整**（ψ(φ(r)) は R 上整・本物）。 -/
theorem intExt_comp_base_integral {R S T : CRing} (φ : RingHom R S)
    (ψ : RingHom S T) (r : R.carrier) :
    IsIntegral (intExtComp φ ψ) ((intExtComp φ ψ).map r) :=
  intExt_base_integral (intExtComp φ ψ) r

/-- **M300F-8: 整拡大の塔 R⊆S⊆T** — S が R 上整・T が S 上整のとき
    T が R 上整（推移性）を束ねる。s_over_r/t_over_s は前提、transitive は
    honest witness（一般の本証明は合成モニック多項式＝有限生成の推移で後続）。 -/
structure IntExtTower (R S T : CRing) (φ : RingHom R S) (ψ : RingHom S T) where
  /-- S の各元は R 上整。 -/
  s_over_r : ∀ x : S.carrier, IsIntegral φ x
  /-- T の各元は S 上整。 -/
  t_over_s : ∀ y : T.carrier, IsIntegral ψ y
  /-- 推移性: T の各元は R 上整（honest witness）。 -/
  transitive : ∀ y : T.carrier, IsIntegral (intExtComp φ ψ) y

/-- **M300F-8b: 恒等塔 R⊆R⊆R** の完全実インスタンス（推移性も基底整で本物）。 -/
def intExt_tower_id (R : CRing) :
    IntExtTower R R R (intExtIdHom R) (intExtIdHom R) where
  s_over_r := intExt_id_all_integral R
  t_over_s := intExt_id_all_integral R
  transitive := fun y =>
    intExt_base_integral (intExtComp (intExtIdHom R) (intExtIdHom R)) y

/-! ## M300F-9: 整閉性（体は整閉・本物） -/

/-- **M300F-9a: 整閉性** — ι : R→S が整閉とは、S の R 上整な元が全て
    ι の像に入ること（∀ s 整, ∃ r, ι(r)=s）。R が Frac(R) の中で整閉に対応。 -/
def IsIntegrallyClosed {R S : CRing} (ι : RingHom R S) : Prop :=
  ∀ s : S.carrier, IsIntegral ι s → ∃ r : R.carrier, ι.map r = s

/-- **M300F-9b: 恒等拡大は整閉**（各整元 s に対し r=s で ι(r)=s）。 -/
theorem intExt_id_integrallyClosed (R : CRing) :
    IsIntegrallyClosed (intExtIdHom R) := by
  intro s _
  exact ⟨s, rfl⟩

/-- **M300F-9c: 体は整閉**（本物）— 体 K は Frac(K)=K であり、K の
    整元は全て K に入る（恒等拡大 K⊆K が整閉）。 -/
theorem intExt_field_integrallyClosed (K : IUTField) :
    IsIntegrallyClosed (intExtIdHom K.toCRing) :=
  intExt_id_integrallyClosed K.toCRing

/-! ## M300F-10: capstone — 整拡大データと存在 -/

/-- **M300F-10a: 整拡大データ** — 基底環 R・拡大環 S・包含 ι・整閉包の部分環。 -/
structure IntegralExtensionData where
  /-- 基底環 R。 -/
  baseRing : CRing
  /-- 拡大環 S。 -/
  extRing : CRing
  /-- 包含（環準同型 ι : R→S）。 -/
  incl : RingHom baseRing extRing
  /-- 整閉包が部分環をなすデータ。 -/
  closure : IntExtClosureSubring baseRing extRing incl

/-- **M300F-10b: 任意環 R の恒等整拡大データ**（整閉包が完全な部分環で本物）。 -/
def intExt_closure_data (R : CRing) : IntegralExtensionData where
  baseRing := R
  extRing := R
  incl := intExtIdHom R
  closure := intExt_id_closure R

/-- **M300F-10c: 体 K の恒等整拡大データ**。 -/
def intExt_field_extensionData (K : IUTField) : IntegralExtensionData where
  baseRing := K.toCRing
  extRing := K.toCRing
  incl := intExtIdHom K.toCRing
  closure := intExt_id_closure K.toCRing

/-- **M300F-10d: ℤ⊆ℤ の整拡大データ**（実例）。 -/
def intExt_intExtensionData : IntegralExtensionData := intExt_closure_data intRing

/-- **M300F-10e: ℚ⊆ℚ の整拡大データ**（体の実例）。 -/
def intExt_ratExtensionData : IntegralExtensionData :=
  intExt_field_extensionData ratIUTField

/-- **M300F-10f: 整拡大データは存在する**（ℤ⊆ℤ の実例）。 -/
theorem intExt_exists : Nonempty IntegralExtensionData :=
  ⟨intExt_intExtensionData⟩

/-- **M300F-10g: 体の整拡大データは存在する**（ℚ⊆ℚ）。 -/
theorem intExt_field_exists : Nonempty IntegralExtensionData :=
  ⟨intExt_ratExtensionData⟩

end IUT
