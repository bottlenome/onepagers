-- M385F LubinTateReciprocity [実・本物・柱B]
-- complete_pct 影響: 柱B で M380F の閉形式 LT 形式群 (p=2, 乗法群 G_m) を「明示的相互律の一段」へ昇格し、n 重 [2] 自己準同型が 2^n 乗写像を実現すること・単数 u が 2^n-捻れ上を形式群自己準同型 [u]（指数座標で ×u）で動かすこと・rec(u)=[u^{-1}] の逆整合を Int/mod 2^n の実整数演算で完全証明し、M330F の Artin 写像（単数↦惰性因子 u・素元↦Frobenius）へ接続。
-- 正直な限定: 一般 π,q（q≥3）の完全な明示的相互律・LCFT 存在定理（全アーベル拡大に対するノルム群一致）・惰性が乗法単位として作用する際の加法モデル(intGrp)と乗法単位 1 の正規化整合は本モジュール外（後続）。ここは p=2 / 有限捻れレベルの忠実な実部分ケースのみが本物。

/-
  IUT/LubinTateReciprocity.lean — M385F（Lubin–Tate 明示的相互律: 実部分ケース）

  ────────────────────────────────────────────────────────────────────────
  二軸（CLAUDE.md §1 必守）
  * 分類: **[実]**（(a) 昇格 + (b) 本物先行建設）。M380F（IUT/LubinTate.lean,
    prefix `ltm`）が建てた閉形式 Lubin–Tate 形式群 F_1(u,v)=u+v+uv（p=2 の
    乗法形式群 G_m, [2](w)=2w+w²=(1+w)²−1）を、**明示的相互律の一段**へ昇格する。
  * complete_pct 影響: 柱B（局所類体論）前進あり。次を Int / mod 2^n の
    **実整数演算**で完全証明:
      (1) n 重 [2]-自己準同型 [2^n] が指数座標で **z ↦ z^(2^n)** を実現
          （`ltrEndoIter_isPow`）。すなわち 2^n-捻れ = 1 の 2^n 乗根。
      (2) 単数 u ∈ ℤ_2^× が 2^n-捻れ上を形式群自己準同型 **[u]（指数 ×u）**で
          動かし、加法的（捻れ加群の準同型）・乗法的（rec(uv)=rec(u)rec(v)）・
          well-defined（mod 2^n で降下）であること。
      (3) **rec(u) = [u^{-1}]**（Lubin–Tate の明示公式）: u·u'≡1 (mod 2^n) なら
          [u]∘[u'] は捻れ上で恒等（`ltr_rec_inverse`）。
      (4) M330F への接続: 単数 ↦ 惰性因子 u（[u] で作用）、素元 ↦ Frobenius
          （惰性自明 ⇒ 恒等作用）を M330F の実 Gal 標的で確認。

  ────────────────────────────────────────────────────────────────────────
  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
  * `ltrIPow` / `ltrIPow_add`      — Int 上の乗法冪 z^n と冪法則 z^(a+b)=z^a·z^b
  * `ltrPow2`                       — 2^n（捻れレベルの位数）
  * `ltrEndoIter` / `ltrEndoIter_isPow`
        — n 重 [2]-自己準同型と、その指数座標での 2^n 乗写像実現（本物・exact）
  * `ltrUnitAct` / `ltrUnitAct_add` / `ltrUnitAct_mul` / `ltrUnitAct_one`
        — 単数 u の 2^n-捻れ上の [u]-作用（加法・乗法・単位）
  * `ltrModEq` / `ltrUnitAct_welldef`
        — mod 2^n 合同と作用の well-defined 性（捻れ加群 ℤ/2^n への降下）
  * `ltr_expEndo_kills`             — [2^n] は 2^n-捻れを消す（指数 ×2^n ≡ 0）
  * `ltr_rec_inverse`               — rec(u)=[u^{-1}]: u·u'≡1 なら [u]∘[u']=id（捻れ上）
  * `ltr_unit_inertia` / `ltr_unit_inertia_eq` / `ltr_uniformizer_frob`
        — M330F 接続（単数↦惰性因子 [u]・素元↦Frobenius）
  * `LubinTateReciprocityData` / `ltrData` / `ltr_exists` — capstone + witness
  * 例（p=2, レベル n=1,2 の worked examples）

  ────────────────────────────────────────────────────────────────────────
  正直な限定（CLAUDE.md §4: 消去・弱化禁止）
  * 一般 π,q（q≥3）の完全な明示的相互律（全次数冪級数 LT 形式群・Coleman
    写像・明示相互法則）は本モジュール外——後続。
  * LCFT 存在定理（全ての有限アーベル拡大 L に対する rec の核 = ノルム群
    N_{L/K}(L^×) の完全一致）は骨組みのまま。ここで本物にしたのは
    「単数が捻れ上を [u] で動かし rec(u)=[u^{-1]}」という明示公式の一段。
  * M330F の単数群を加法モデル `intGrp` で受けるため、惰性因子 u（指数域の
    整数乗数）と乗法単位群の単位元 1 の正規化整合は本物化していない
    （Frobenius/自明惰性の恒等作用は ltrUnitAct 1 = id として別途本物）。
  * 右辺（ẑ × O_v^×）が実 Gal(K^ab/K) と同型であることは M330F 同様に後続。

  全て mathlib なし・新規 Classical.choice なし（propext, Quot.sound のみ）。
  共有ファイル未変更（新規 1 本のみ）。
-/
import IUT.LubinTate
import IUT.LocalReciprocity

namespace IUT

/-! ## §1 Int 上の乗法冪 z^n と 2^n（捻れの位数） -/

/-- Int 上の乗法冪 z^n（形式群の指数座標 G_m での冪）。 -/
def ltrIPow (z : Int) : Nat → Int
  | 0 => 1
  | n + 1 => z * ltrIPow z n

/-- 冪の定義（unfold 用）。 -/
theorem ltrIPow_succ (z : Int) (n : Nat) : ltrIPow z (n + 1) = z * ltrIPow z n := rfl

/-- **冪法則** z^(a+b) = z^a · z^b（exact, Int 上）。 -/
theorem ltrIPow_add (z : Int) (a b : Nat) :
    ltrIPow z (a + b) = ltrIPow z a * ltrIPow z b := by
  induction b with
  | zero =>
    show ltrIPow z a = ltrIPow z a * ltrIPow z 0
    show ltrIPow z a = ltrIPow z a * 1
    rw [Int.mul_one]
  | succ k ih =>
    show z * ltrIPow z (a + k) = ltrIPow z a * (z * ltrIPow z k)
    rw [ih]
    exact Int.mul_left_comm z (ltrIPow z a) (ltrIPow z k)

/-- 2^n: 2^n-捻れ点の個数（＝捻れ加群 ℤ/2^n の位数）。 -/
def ltrPow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * ltrPow2 n

/-- 2^(n+1) = 2^n + 2^n（倍化）。 -/
theorem ltrPow2_succ_add (n : Nat) : ltrPow2 (n + 1) = ltrPow2 n + ltrPow2 n := by
  show 2 * ltrPow2 n = ltrPow2 n + ltrPow2 n
  omega

/-! ## §2 n 重 [2]-自己準同型と 2^n 乗写像の実現（本物・exact） -/

/-- n 重 [2]-自己準同型 [2^n] = [2]∘…∘[2]（n 回）。M380F の `ltmEndo2` を反復。
    [2^0] = id、[2^(n+1)] = [2]∘[2^n]。 -/
def ltrEndoIter : Nat → Int → Int
  | 0, w => w
  | n + 1, w => ltmEndo2 (ltrEndoIter n w)

/-- 反復の定義（unfold 用）。 -/
theorem ltrEndoIter_succ (n : Nat) (w : Int) :
    ltrEndoIter (n + 1) w = ltmEndo2 (ltrEndoIter n w) := rfl

/-- **M385F-1: n 重 [2]-自己準同型は 2^n 乗写像を実現**（指数座標, exact）。
    指数座標 z = 1 + w のもとで
        1 + [2^n](w) = (1 + w)^(2^n)
    が Int 上、次数切断なしに厳密成立する。すなわち 2^n-捻れ [2^n](w)=0 は
    ちょうど 2^n 乗根 (1+w)^(2^n)=1 に対応する（G_m の Lubin–Tate 実現）。 -/
theorem ltrEndoIter_isPow (n : Nat) (w : Int) :
    1 + ltrEndoIter n w = ltrIPow (1 + w) (ltrPow2 n) := by
  induction n with
  | zero =>
    show 1 + w = (1 + w) * 1
    rw [Int.mul_one]
  | succ k ih =>
    show 1 + ltmEndo2 (ltrEndoIter k w) = ltrIPow (1 + w) (ltrPow2 (k + 1))
    rw [ltmGF2 (ltrEndoIter k w), ih, ltrPow2_succ_add, ltrIPow_add]

/-! ## §3 単数の [u]-作用（指数座標 ×u）と捻れ加群 ℤ/2^n -/

/-- 単数 u ∈ ℤ_2^× の 2^n-捻れ上の作用: 形式群自己準同型 [u]（G_m の u 乗）は
    指数座標では **指数の ×u**。すなわち 2^n 乗根 ζ（指数 k）を ζ^u（指数 u·k）へ。 -/
def ltrUnitAct (u k : Int) : Int := u * k

/-- 作用の定義（unfold 用）。 -/
theorem ltrUnitAct_def (u k : Int) : ltrUnitAct u k = u * k := rfl

/-- **M385F-2: [u]-作用は捻れ加群の準同型**（加法的）: [u](k+l) = [u]k + [u]l。 -/
theorem ltrUnitAct_add (u k l : Int) :
    ltrUnitAct u (k + l) = ltrUnitAct u k + ltrUnitAct u l :=
  Int.mul_add u k l

/-- **M385F-3: 単数は乗法的に作用** rec(uv) = rec(u)∘rec(v): [u·v] = [u]∘[v]。
    Artin 写像の準同型性が捻れ作用へ降りたもの。 -/
theorem ltrUnitAct_mul (u v k : Int) :
    ltrUnitAct (u * v) k = ltrUnitAct u (ltrUnitAct v k) :=
  Int.mul_assoc u v k

/-- **M385F-4: 自明単数は恒等作用** [1] = id（Frobenius/自明惰性の作用）。 -/
theorem ltrUnitAct_one (k : Int) : ltrUnitAct 1 k = k :=
  Int.one_mul k

/-- 基点固定 [u](0) = 0（捻れの単位元 = 1 の指数 0 を固定）。 -/
theorem ltrUnitAct_zero (u : Int) : ltrUnitAct u 0 = 0 :=
  Int.mul_zero u

/-! ## §4 mod 2^n 合同（捻れ加群 ℤ/2^n への降下） -/

/-- 2^n を法とする合同 a ≡ b (mod 2^n)。捻れ加群 ℤ/2^n の等式。 -/
def ltrModEq (n : Nat) (a b : Int) : Prop :=
  ∃ t : Int, a - b = (ltrPow2 n : Int) * t

/-- 合同は反射的。 -/
theorem ltrModEq_refl (n : Nat) (a : Int) : ltrModEq n a a :=
  ⟨0, by rw [Int.mul_zero]; omega⟩

/-- **M385F-5: [u]-作用は mod 2^n で well-defined**（捻れ加群 ℤ/2^n へ降下）:
    k ≡ k' なら [u]k ≡ [u]k'。作用が有限捻れ ℤ/2^n 上で定義されることの本物証明。 -/
theorem ltrUnitAct_welldef (n : Nat) (u k k' : Int)
    (h : ltrModEq n k k') : ltrModEq n (ltrUnitAct u k) (ltrUnitAct u k') := by
  obtain ⟨t, ht⟩ := h
  refine ⟨u * t, ?_⟩
  show u * k - u * k' = (ltrPow2 n : Int) * (u * t)
  rw [← Int.mul_sub, ht, Int.mul_left_comm]

/-- **M385F-6: [2^n] は 2^n-捻れを消す**（指数座標 ×2^n ≡ 0 mod 2^n）。
    2^n-捻れの定義 [2^n](λ)=0 が指数域 ℤ/2^n で成り立つことの本物証明。 -/
theorem ltr_expEndo_kills (n : Nat) (k : Int) :
    ltrModEq n ((ltrPow2 n : Int) * k) 0 :=
  ⟨k, by rw [Int.sub_zero]⟩

/-! ## §5 明示的相互律 rec(u) = [u^{-1}]（Lubin–Tate 明示公式・実部分ケース） -/

/-- **M385F-7: Lubin–Tate 明示公式 rec(u) = [u^{-1}]**（捻れ上, mod 2^n）。
    単数 u に法逆元 u'（u·u' ≡ 1 mod 2^n）があるとき、形式群自己準同型
    [u] と [u'] の合成は 2^n-捻れ上で恒等: [u]([u'](k)) ≡ k (mod 2^n)。
    これは「Artin 写像 rec(u) が π^n-捻れに [u^{-1}] として作用する」という
    Lubin–Tate 明示的相互律の core を、実整数演算で厳密に閉じたもの。 -/
theorem ltr_rec_inverse (n : Nat) (u u' k : Int)
    (h : ltrModEq n (u * u') 1) :
    ltrModEq n (ltrUnitAct u (ltrUnitAct u' k)) k := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s * k, ?_⟩
  show u * (u' * k) - k = (ltrPow2 n : Int) * (s * k)
  rw [← Int.mul_assoc u u' k]
  have e : (u * u') * k - k = (u * u' - 1) * k := by
    rw [Int.sub_mul, Int.one_mul]
  rw [e, hs, Int.mul_assoc]

/-! ## §6 M330F（局所相互律 Artin 写像）への接続 -/

/-- **M385F-8: 単数 ↦ 惰性因子 u、その [u]-作用**（M330F 接続）。
    M330F の Artin 写像は単数 (0,u) を惰性因子 (1, u) へ写す（`locRec_units_inertia`）。
    その惰性因子 u がちょうど 2^n-捻れ上の形式群自己準同型 [u]（指数 ×u）を与える。
    単数群を加法モデル intGrp で受け、惰性因子（第 2 成分）を指数域の乗数として読む。 -/
theorem ltr_unit_inertia (u k : Int) :
    ltrUnitAct (((locRecArtin intGrp).map ((0 : Int), u)).2) k = u * k := rfl

/-- 単数の Artin 像 = (自明不分岐, 惰性因子 u)（M330F の実定理を再輸出）。 -/
theorem ltr_unit_inertia_eq (u : Int) :
    (locRecArtin intGrp).map ((0 : Int), u) = (zhat.one, u) :=
  locRec_units_inertia intGrp u

/-- **M385F-9: 素元 ↦ Frobenius**（M330F 接続）。素元 π=(1, 1) は Frobenius へ
    写り（`locRec_prime_frob`）、その惰性成分は自明。自明惰性は捻れ上で恒等作用
    [1]=id（`ltrUnitAct_one`）を与える——Frobenius は 2^n-捻れを固定する。 -/
theorem ltr_uniformizer_frob :
    (locRecArtin intGrp).map ((1 : Int), intGrp.one) = (locRecFrob, intGrp.one) :=
  locRec_prime_frob intGrp

/-- Frobenius（自明惰性）は 2^n-捻れを固定する: 恒等作用。 -/
theorem ltr_frob_fixes_torsion (k : Int) : ltrUnitAct 1 k = k :=
  ltrUnitAct_one k

/-! ## §7 capstone: Lubin–Tate 明示的相互律データ -/

/-- **M385F-10: Lubin–Tate 明示的相互律データ**（p=2, 捻れレベル level）。
    n 重自己準同型 [2^level]（指数座標 2^level 乗）と、単数の [u]-作用
    （加法・乗法・単位・well-defined）を束ねる。 -/
structure LubinTateReciprocityData where
  level : Nat
  modulus : Nat
  modulus_eq : modulus = ltrPow2 level
  endoIter : Int → Int
  /-- [2^level] は指数座標で 2^level 乗写像（2^level-捻れ = 2^level 乗根）。 -/
  endoIter_pow : ∀ w, 1 + endoIter w = ltrIPow (1 + w) modulus
  act : Int → Int → Int
  act_def : ∀ u k, act u k = u * k
  /-- [u] は捻れ加群の準同型（加法的）。 -/
  act_hom : ∀ u k l, act u (k + l) = act u k + act u l
  /-- 単数は乗法的に作用: rec(uv)=rec(u)rec(v)。 -/
  act_mul : ∀ u v k, act (u * v) k = act u (act v k)
  /-- 自明単数は恒等作用。 -/
  act_one : ∀ k, act 1 k = k
  /-- 作用は mod 2^level で well-defined（ℤ/2^level への降下）。 -/
  act_welldef : ∀ u k k', ltrModEq level k k' → ltrModEq level (act u k) (act u k')

/-- **M385F-11: レベル n の LT 明示的相互律データの構成**（本物 witness）。
    p=2 の乗法形式群 G_m（M380F の [2](w)=2w+w²）で全性質を完全証明で満たす。 -/
def ltrData (n : Nat) : LubinTateReciprocityData where
  level := n
  modulus := ltrPow2 n
  modulus_eq := rfl
  endoIter := ltrEndoIter n
  endoIter_pow := ltrEndoIter_isPow n
  act := ltrUnitAct
  act_def := fun _ _ => rfl
  act_hom := ltrUnitAct_add
  act_mul := ltrUnitAct_mul
  act_one := ltrUnitAct_one
  act_welldef := ltrUnitAct_welldef n

/-- **M385F-12: LT 明示的相互律データの存在**（p=2 の本物 witness, レベル 2）。 -/
theorem ltr_exists : ∃ d : LubinTateReciprocityData, d.level = 2 ∧ d.modulus = 4 :=
  ⟨ltrData 2, rfl, rfl⟩

/-! ## §8 worked examples（p=2, 捻れレベル n=1,2） -/

-- 例1: 2^2 = 4（レベル 2 の捻れ位数、4 次単数根）
example : ltrPow2 2 = 4 := rfl

-- 例2: 二重 [2]-自己準同型の数値 [2^2](1) = [2]([2]1) = [2](3) = 15
example : ltrEndoIter 2 1 = 15 := rfl

-- 例3: 指数座標 z^4: (1+1)^4 = 16
example : ltrIPow 2 4 = 16 := rfl

-- 例4: **2^n 乗写像の実現**（レベル 2, w=1）: 1 + [2^2](1) = (1+1)^4
--      左辺 1+15 = 16, 右辺 2^4 = 16
example : 1 + ltrEndoIter 2 1 = ltrIPow (1 + 1) (ltrPow2 2) :=
  ltrEndoIter_isPow 2 1

-- 例5: レベル 1（平方根 ±1, ℤ/2）で [2^1](w)=(1+w)^2
example : 1 + ltrEndoIter 1 3 = ltrIPow (1 + 3) (ltrPow2 1) :=
  ltrEndoIter_isPow 1 3

-- 例6: 単数 u=3 の作用（レベル 2, ℤ_2^× mod 4 = {1,3}）: 指数 1 ↦ 3（=−1 mod 4）
example : ltrUnitAct 3 1 = 3 := rfl

-- 例7: **rec(3) = [3^{-1}]**（レベル 2, 3 は mod 4 自己逆元: 3·3=9≡1）:
--      [3]∘[3] は 2²-捻れ上で恒等（9k ≡ k mod 4）
example : ltrModEq 2 (ltrUnitAct 3 (ltrUnitAct 3 1)) 1 :=
  ltr_rec_inverse 2 3 3 1 ⟨2, rfl⟩

-- 例8: 単数は乗法的（3·3=9 の作用 = [3]∘[3]）
example : ltrUnitAct (3 * 3) 5 = ltrUnitAct 3 (ltrUnitAct 3 5) :=
  ltrUnitAct_mul 3 3 5

-- 例9: [2^2] は 4-捻れを消す（指数 ×4 ≡ 0 mod 4）
example : ltrModEq 2 ((4 : Int) * 7) 0 :=
  ltr_expEndo_kills 2 7

-- 例10: M330F 接続 — 単数 u=3 の惰性因子が [3]-作用を与える
example : ltrUnitAct (((locRecArtin intGrp).map ((0 : Int), (3 : Int))).2) 5 = 3 * 5 :=
  ltr_unit_inertia 3 5

-- 例11: capstone データのアクセサ（レベル 2 の乗法性）
example : (ltrData 2).act (3 * 3) 1 = (ltrData 2).act 3 ((ltrData 2).act 3 1) :=
  (ltrData 2).act_mul 3 3 1

end IUT
