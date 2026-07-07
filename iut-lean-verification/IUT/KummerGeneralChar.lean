-- M458F KummerGeneralChar [実・昇格（(a)）・柱E×柱A]
-- complete_pct 影響: 柱E/柱A で、M453F(knc)が正直に残した限定「本モジュールが実際に
--   非自明にするのは位数 2 の複素共役型 χ 一種（σ(ζ)=ζ^{-1}）のみ——一般の mod-n
--   円分指標（(ℤ/n)^× の任意の元を χ(g) に持つ一般ケース）・完全副有限円分指標
--   Ẑ^×(1) の逆極限レベルの非自明性へは配線しない」を、**一般の (ℤ/n)^× 円分指標**
--   （単元 a∈(ℤ/n)^× による σ_a(ζ)=ζ^a、a=n−1 の位数 2 ケースを特殊ケースとして含む）
--   へ実際に昇格・拡張する。本物の単元群 `kgcUnitGroup n`（zmodMul による mod n 単元
--   の pair-with-witness 構成、既存の zmod/zmodMul の上に本物の Grp として構成）を
--   ゼロから建設し、任意の単元 a が定める円分作用 `kgcCyclotomicActionGen` を
--   CycGKAction のインスタンスとして構成、M443F cid_galois_equivariant への
--   実インスタンス化（`kgc_galois_equivariant_general`）・M443F-7 共有元同定への配線
--   （`kgc_commutator_agree_general`）を一般単元 a について完全証明する。
--   M453F の a=n−1（位数 2、複素共役型）は `kgc_specializes_to_knc` により
--   本モジュールの特殊ケースとして回収される。
-- 正直な限定: 昇格するのは**有限 (ℤ/n)^× レベル（mod n）**の円分指標のみ——完全副有限
--   円分指標 Ẑ^×(1) の逆極限レベルの非自明性・κ 自身（M353F の具体的 Kummer 指標）を
--   非自明係数加群上の 1-コサイクルへ格上げする接続は、本モジュールでも引き続き
--   範囲外（後続）。単元群 kgcUnitGroup n は「明示的な逆元データを伴う単元」として
--   構成しており、任意の a∈(ℤ/n)^× に対しその明示的逆元（Bézout 係数）を計算する
--   アルゴリズム自体は本モジュールの範囲外（呼び出し側が逆元を供給する）。

/-
  IUT/KummerGeneralChar.lean — M458F [実／昇格・柱E×柱A]
  分類: 実（(a) 昇格 — M453F(knc)の限定「位数 2 の複素共役型 χ 一種のみ」を、
  一般の (ℤ/n)^× 円分指標へ実際に破る）

  背景（M453F の限定・そのまま引用）:
    M453F（KummerNontrivialChar, prefix `knc`）は、複素共役の生成する ⟨c⟩≅ℤ/2 を
    模型 `kncZ2` として構成し、その非自明反転作用 `kncCyclotomicActionGen` の
    非自明性・cidThetaMuIso との Galois 同変性・M443F-7 共有元同定との両立を
    完全証明したが、`knc_model_scope` は正直に次を限定として残した:
      「本モジュールが実際に非自明にするのは位数 2 の複素共役型 χ 一種
       （σ(ζ)=ζ^{-1}）のみ——一般の mod-n 円分指標（(ℤ/n)^× の任意の元を χ(g) に
       持つ一般ケース）・完全副有限円分指標 Ẑ^×(1) の逆極限レベルの非自明性へは
       配線しない。他の位数の非自明指標（例えば位数 3 以上の χ）は同じ手法
       （Aut(μ_n)≅(ℤ/n)^× の乗法群からの群準同型を χ に取る）で構成できるはずだが
       本モジュールでは複素共役の実例に留める。」

  本モジュールはこの限定を、**一般の (ℤ/n)^× 円分指標**で実際に突破する:

  1. **`kgcUnitCarrier`/`kgcUnitGroup`（本丸1・本物の単元群の構成）**: (ℤ/n)^× を
     「明示的な逆元データを伴う単元の pair」（a, ainv : (zmod n).carrier で
     zmodMul n a ainv = 1 を満たすもの）として本物の `Grp` に構成する。積・単位元・
     逆元は全て zmodMul の既存の代数法則（`zmodMul_assoc`/`zmodMul_comm`/
     `zmodOne_mul`、M29/M102 既証明）に帰着し完全証明する——選択公理不使用
     （逆元は既存の witness ペアの入れ替えで直接得る、Bézout 探索アルゴリズムなし）。
  2. **`kgcExp`/`kgc_pow_eq_zmodMul`/`kgc_all_pow_ord`/`kgc_exp_mul`
     （本丸2・単元の指数化と乗法整合性）**: 各単元 g の「a」成分を標準模型
     cycMuStd n の離散対数で Nat 指数へ読み替え（`kgcExp`）、この指数化が
     kgcUnitGroup の積（zmodMul）と mod n で整合すること（`kgc_exp_mul`、
     Grp.pow と zmodMul の橋渡し `kgc_pow_eq_zmodMul` 経由）を完全証明する。
  3. **`kgcCyclotomicActionGen`（本丸3・一般単元作用の本物の構成）**: 任意の
     CycMuGroup X（X.n=n）に、単元 g の a-成分の指数で z を冪乗する
     z↦z^{a} という**本物の CycGKAction**を構成する。act_mul は
     `kgc_pow_mul_distrib`（冪の積分配則、可換群の一般事実）と `kgc_exp_mul`・
     `kgc_all_pow_ord`（周期性、任意の元が位数 n を持つことの一般化）から
     完全証明する——**M453F kncCyclotomicActionGen（Bool=位数 2 のみ）を
     真に一般の (ℤ/n)^× へ拡張**する本丸。
  4. **`kgc_specializes_to_knc`（本丸4・M453F を特殊ケースとして回収）**:
     単元 a=n−1（`kgcNegOne`、自己逆元 (n−1)²≡1 mod n）での作用が、M453F の
     複素共役型反転作用 `kncCyclotomicActionGen X` の true ケースと**literally
     一致する**ことを、`kgc_pow_pred_eq_inv_general`（z^{n−1}=z⁻¹、任意の z へ
     `knc_pow_pred_eq_inv` を一般化）から示す。
  5. **`kgc_char_general`（本丸5・一般単元の非自明性）**: a-成分が単位元（class 1）
     と異なる任意の単元 g で、作用は生成元を動かす——`cycRig_pow_inj` による
     指数の相異性からの完全証明。
  6. **`kgc_hchar`/`kgc_galois_equivariant_general`（本丸6・M443F を一般単元へ
     実インスタンス化）**: `cid_galois_equivariant`（M443F）を
     ρM=ρN=`kgcCyclotomicActionGen`（**任意の単元 g**、複素共役型に限らない）に
     実インスタンス化し、hchar を `kgc_hchar`（`cmu_log_pow_mod` から外部仮説でなく
     証明）で満たす。cidThetaMuIso が**一般の (ℤ/n)^× 作用**の下で G_K 同変で
     あることを示す——M453F の「位数 2 のみ」を実際に破る本丸。
  7. **`kgc_commutator_agree_general`（本丸7・M443F-7 を一般単元へ）**: テータ交換子
     μ_l 像の「同一元の 2 実現」が一般単元作用の下でも成立することを、
     `kgc_galois_equivariant_general` と `cid_commutator_agree_via_iso`（M443F-7）
     の合成で示す。
  8. `KummerGeneralCharData`/`kummerGeneralCharData`/`kgc_exists` — 総括レコード。
     `kgc_model_scope` — 残る限定の正直な宣言（M453F の限定を実際に破ったことの
     明示込み）。

  * M458F-1 `kgcUnitCarrier`/`kgcUnitMulClose`/`kgcUnitGroup`
  * M458F-2 `kgc_zmod_pow_rep`/`kgc_pow_eq_zmodMul`/`kgc_pow_one_eq_one`/
    `kgc_all_pow_ord`/`kgcExp`/`kgc_exp_mul`
  * M458F-3 `kgc_pow_mul_distrib`/`kgcCyclotomicActionGen`
  * M458F-4 `kgc_pow_pred_eq_inv_general`/`kgcNegOne`/`kgc_specializes_to_knc`
  * M458F-5 `kgc_char_general`
  * M458F-6 `kgc_hchar`/`kgc_galois_equivariant_general`（本橋渡し・限定を破る）
  * M458F-7 `kgc_commutator_agree_general`
  * M458F-8 `KummerGeneralCharData`/`kummerGeneralCharData`/`kgc_exists`/
    `kgc_model_scope`
  * M458F-9 実例

  **正直な限定（消去・弱化禁止）**:
  - `kgcUnitGroup n` は「明示的な逆元データ（ainv）を伴う単元の pair」として
    構成する——各要素は自身の逆元を DATA として携える（Prop の存在量化ではなく
    構造体フィールド）。任意の a∈(ℤ/n)^× に対しその逆元を**アルゴリズム的に
    計算する**（Bézout の互除法など）ことは本モジュールの範囲外——本モジュールを
    使う側が、単元とその明示的逆元のペアを供給する必要がある（M448F の
    `hg0`・M443F の `hn : E.n=l` と同じ「外部から与える 1 データ」の位置づけ）。
  - 昇格するのは**有限 (ℤ/n)^× レベル（mod n）**の円分指標のみ——完全副有限
    円分指標 Ẑ^×(1) の逆極限レベルの同定・p 進解析的同一視は含まない（M322F-7・
    M443F cid_model_scope (3) と同じ位置づけ、そのまま継承）。
  - M353F の具体的 Kummer 指標 κ:GK→M.μ 自身が住む係数加群は、本モジュールでも
    引き続き外部（M448F kcwKummerAction・M453F knc_model_scope の限定をそのまま
    継承——本モジュールが一般化したのは cidThetaMuIso の Galois 同変性を測る
    **外側の** CycGKAction ρ であり、κ 自身の係数加群格上げは範囲外）。
  - E.n = l（外部仮定）・A 側 ζ の位数 l 性 hζl・distinctness hdist の外部仮定という
    M443F cid_model_scope の限定、および κ が生成元を撃つ校正 hg0 の外部仮定という
    M448F kcw_model_scope (iii) の限定は、そのまま継承する（本モジュールは解消しない）。
  - 全て選択公理を証明本体で新規導入せず（新規 Classical・新規 Classical.choice
    なし）。禁止タクティク不使用（simp/decide/by_cases/rcases/ring/nlinarith/
    positivity/conv/nth_rewrite/field_simp 不使用）。許可タクティクのみ
    （cases/obtain/induction/rw/show/refine/exact/apply/intro/generalize/funext/
    omega）。共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は
    一切変更していない。一般名は `kgc` 接頭辞で衝突回避（グレップ確認済み・
    既存コードに重複なし）。
-/
import IUT.KummerNontrivialChar
import IUT.ZmodOrder

namespace IUT

/-! ## M458F-1: 本物の単元群 (ℤ/n)^× の構成 -/

/-- **M458F-1a: 単元の carrier**——「明示的な逆元データを伴う単元の pair」
    (a, ainv : (zmod n).carrier)、zmodMul n a ainv = 1 を満たすもの。選択公理・
    存在量化からの抽出なしに、単元とその逆元を DATA として直接携える。 -/
def kgcUnitCarrier (n : Nat) : Type :=
  { p : (zmod n).carrier × (zmod n).carrier //
      zmodMul n p.1 p.2 = Quot.mk (modCong n).rel 1 }

/-- **定理 (M458F-1b: 本丸・単元の積閉性)** — a·ainv=1・c·cinv=1 なら
    (a·c)·(ainv·cinv)=1（可換モノイドの中間交換、zmodMul_assoc/zmodMul_comm の
    連鎖のみで完全証明）。 -/
theorem kgcUnitMulClose (n : Nat) (a b c d : (zmod n).carrier)
    (hab : zmodMul n a b = Quot.mk (modCong n).rel 1)
    (hcd : zmodMul n c d = Quot.mk (modCong n).rel 1) :
    zmodMul n (zmodMul n a c) (zmodMul n b d) = Quot.mk (modCong n).rel 1 := by
  rw [zmodMul_assoc, ← zmodMul_assoc n c b d, zmodMul_comm n c b, zmodMul_assoc n b c d,
    ← zmodMul_assoc n a b (zmodMul n c d), hab, hcd, zmodOne_mul]

/-- **定理 (M458F-1c: 本丸・単元群 (ℤ/n)^× : Grp)** — 積・単位元・逆元
    （witness の入れ替え）を持つ本物の可換群。群法則は全て zmodMul の既存代数法則
    （M29/M102）に帰着し完全証明する。 -/
def kgcUnitGroup (n : Nat) : Grp where
  carrier := kgcUnitCarrier n
  mul := fun x y => ⟨(zmodMul n x.val.1 y.val.1, zmodMul n x.val.2 y.val.2),
    kgcUnitMulClose n x.val.1 x.val.2 y.val.1 y.val.2 x.property y.property⟩
  one := ⟨(Quot.mk (modCong n).rel 1, Quot.mk (modCong n).rel 1),
    zmodOne_mul n (Quot.mk (modCong n).rel 1)⟩
  inv := fun x => ⟨(x.val.2, x.val.1), by
    show zmodMul n x.val.2 x.val.1 = Quot.mk (modCong n).rel 1
    rw [zmodMul_comm n x.val.2 x.val.1]
    exact x.property⟩
  mul_assoc := by
    intro x y z
    apply Subtype.ext
    show (zmodMul n (zmodMul n x.val.1 y.val.1) z.val.1,
          zmodMul n (zmodMul n x.val.2 y.val.2) z.val.2)
      = (zmodMul n x.val.1 (zmodMul n y.val.1 z.val.1),
         zmodMul n x.val.2 (zmodMul n y.val.2 z.val.2))
    rw [zmodMul_assoc, zmodMul_assoc]
  one_mul := by
    intro x
    apply Subtype.ext
    show (zmodMul n (Quot.mk (modCong n).rel 1) x.val.1,
          zmodMul n (Quot.mk (modCong n).rel 1) x.val.2)
      = (x.val.1, x.val.2)
    rw [zmodOne_mul, zmodOne_mul]
  inv_mul := by
    intro x
    apply Subtype.ext
    show (zmodMul n x.val.2 x.val.1, zmodMul n x.val.1 x.val.2)
      = (Quot.mk (modCong n).rel 1, Quot.mk (modCong n).rel 1)
    rw [zmodMul_comm n x.val.2 x.val.1, x.property]
    rfl

/-! ## M458F-2: 単元の指数化と乗法整合性 -/

/-- **M458F-2a**: `(zmod n).pow` の代表元計算（一般の x の Grp.pow は
    class(x·k) に一致する、cycStd_pow の一般 x 版）。 -/
theorem kgc_zmod_pow_rep (n : Nat) (x : Int) (k : Nat) :
    (zmod n).pow (Quot.mk (modCong n).rel x) k = Quot.mk (modCong n).rel (x * (k : Int)) := by
  induction k with
  | zero =>
    show (zmod n).one = Quot.mk (modCong n).rel (x * ((0 : Nat) : Int))
    have hz : x * ((0 : Nat) : Int) = 0 := by omega
    rw [hz]
    rfl
  | succ k ih =>
    show (zmod n).mul (Quot.mk (modCong n).rel x)
        ((zmod n).pow (Quot.mk (modCong n).rel x) k)
      = Quot.mk (modCong n).rel (x * ((k + 1 : Nat) : Int))
    rw [ih]
    show Quot.mk (modCong n).rel (x + x * (k : Int))
      = Quot.mk (modCong n).rel (x * ((k + 1 : Nat) : Int))
    have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    have heq : x + x * (k : Int) = x * ((k + 1 : Nat) : Int) := by
      rw [hcast, Int.mul_add, Int.mul_one]
      omega
    rw [heq]

/-- **定理 (M458F-2b: 本丸・Grp.pow と zmodMul の橋渡し)** — 任意の c で
    `(zmod n).pow c k = zmodMul n c ((zmod n).pow ζ k)`（ζ=class 1）。可換な
    「加法的な冪」と「本物の乗法 zmodMul」を接続する橋。 -/
theorem kgc_pow_eq_zmodMul (n : Nat) (c : (zmod n).carrier) (k : Nat) :
    (zmod n).pow c k = zmodMul n c ((zmod n).pow (Quot.mk (modCong n).rel 1) k) := by
  induction c using Quot.ind
  rename_i x
  rw [kgc_zmod_pow_rep n x k, cycStd_pow n k]
  rfl

/-- **M458F-2c**: 単位元の冪は単位元（任意の可換群、帰納法）。 -/
theorem kgc_pow_one_eq_one (G : Grp) (k : Nat) : G.pow G.one k = G.one := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show G.mul G.one (G.pow G.one k) = G.one
    rw [G.one_mul, ih]

/-- **定理 (M458F-2d: 本丸・任意の元は位数 n を持つ)** — CycMuGroup X の任意の元 z で
    z^{X.n}=1（生成元だけでなく全ての元に一般化、`X.ord` の一般化）。 -/
theorem kgc_all_pow_ord (X : CycMuGroup) (z : X.μ.carrier) :
    X.μ.pow z X.n = X.μ.one := by
  have h1 : X.μ.pow z X.n = X.μ.pow (X.μ.pow X.ζ (X.log z)) X.n := by
    rw [X.pow_log z]
  rw [h1, ← cycRig_pow_mul X.μ X.comm X.ζ (X.log z) X.n]
  have hcomm : X.log z * X.n = X.n * X.log z := Nat.mul_comm (X.log z) X.n
  rw [hcomm, cycRig_pow_mul X.μ X.comm X.ζ X.n (X.log z), X.ord, kgc_pow_one_eq_one X.μ (X.log z)]

/-- **M458F-2e: 単元の指数化**——単元 g の a-成分を標準模型 cycMuStd n の離散対数で
    Nat 指数へ読み替える。 -/
def kgcExp (n : Nat) (hn2 : 2 ≤ n) (g : kgcUnitCarrier n) : Nat :=
  (cycMuStd n (by omega)).log g.val.1

/-- **定理 (M458F-2f: 本丸・指数化の乗法整合性)** — kgcUnitGroup の積（zmodMul）で
    指数化は mod n で積を保つ: `kgcExp(g·h) ≡ kgcExp(h)·kgcExp(g) (mod n)`。
    `kgc_pow_eq_zmodMul`・`pow_log`・`cycRig_pow_mul`・`cycRig_pow_inj` の合成で
    完全証明する。 -/
theorem kgc_exp_mul (n : Nat) (hn2 : 2 ≤ n) (g h : kgcUnitCarrier n) :
    kgcExp n hn2 ((kgcUnitGroup n).mul g h) % n
      = (kgcExp n hn2 h * kgcExp n hn2 g) % n := by
  have heqM : (cycMuStd n (by omega : (1:Nat) ≤ n)).μ.pow
        (cycMuStd n (by omega : (1:Nat) ≤ n)).ζ
        ((cycMuStd n (by omega)).log (zmodMul n g.val.1 h.val.1))
      = (cycMuStd n (by omega : (1:Nat) ≤ n)).μ.pow
        (cycMuStd n (by omega : (1:Nat) ≤ n)).ζ
        ((cycMuStd n (by omega)).log h.val.1 * (cycMuStd n (by omega)).log g.val.1) := by
    rw [(cycMuStd n (by omega)).pow_log (zmodMul n g.val.1 h.val.1),
      cycRig_pow_mul (cycMuStd n (by omega)).μ (cycMuStd n (by omega)).comm
        (cycMuStd n (by omega)).ζ ((cycMuStd n (by omega)).log h.val.1)
        ((cycMuStd n (by omega)).log g.val.1),
      (cycMuStd n (by omega)).pow_log h.val.1]
    show zmodMul n g.val.1 h.val.1
      = (zmod n).pow h.val.1 ((cycMuStd n (by omega)).log g.val.1)
    rw [kgc_pow_eq_zmodMul n h.val.1 ((cycMuStd n (by omega)).log g.val.1)]
    show zmodMul n g.val.1 h.val.1
      = zmodMul n h.val.1
          ((cycMuStd n (by omega)).μ.pow (cycMuStd n (by omega)).ζ
            ((cycMuStd n (by omega)).log g.val.1))
    rw [(cycMuStd n (by omega)).pow_log g.val.1, zmodMul_comm n h.val.1 g.val.1]
  exact cycRig_pow_inj (cycMuStd n (by omega)).μ (cycMuStd n (by omega)).comm
    (cycMuStd n (by omega)).ζ (cycMuStd n (by omega)).n (cycMuStd n (by omega)).hn
    (cycMuStd n (by omega)).ord (cycMuStd n (by omega)).distinct _ _ heqM

/-! ## M458F-3: 一般単元作用の本物の構成——M453F を一般 (ℤ/n)^× へ拡張 -/

/-- **定理 (M458F-3a: 冪の積分配則)** — 任意の可換群で (z·w)^k = z^k·w^k
    （k の帰納、中間交換）。 -/
theorem kgc_pow_mul_distrib (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a)
    (z w : G.carrier) (k : Nat) :
    G.pow (G.mul z w) k = G.mul (G.pow z k) (G.pow w k) := by
  induction k with
  | zero => exact (G.mul_one G.one).symm
  | succ k ih =>
    show G.mul (G.mul z w) (G.pow (G.mul z w) k)
      = G.mul (G.mul z (G.pow z k)) (G.mul w (G.pow w k))
    rw [ih, G.mul_assoc z w (G.mul (G.pow z k) (G.pow w k)),
      ← G.mul_assoc w (G.pow z k) (G.pow w k), hc w (G.pow z k),
      G.mul_assoc (G.pow z k) w (G.pow w k), ← G.mul_assoc z (G.pow z k) (G.mul w (G.pow w k))]

/-- **定理 (M458F-3b: 本丸・一般単元作用の本物の構成)** — 任意の CycMuGroup X
    （X.n=n）に、単元 g の a-成分の指数で z を冪乗する z↦z^{kgcExp g} という
    本物の CycGKAction (kgcUnitGroup n) X。**M453F kncCyclotomicActionGen
    （位数 2 の Bool のみ）を真に一般の (ℤ/n)^× へ拡張**する本丸。 -/
def kgcCyclotomicActionGen (n : Nat) (hn2 : 2 ≤ n) (X : CycMuGroup) (hXn : X.n = n) :
    CycGKAction (kgcUnitGroup n) X where
  act := fun g =>
    { map := fun z => X.μ.pow z (kgcExp n hn2 g)
      map_mul := fun z w => kgc_pow_mul_distrib X.μ X.comm z w (kgcExp n hn2 g) }
  act_one := by
    intro z
    show X.μ.pow z (kgcExp n hn2 (kgcUnitGroup n).one) = z
    have he : kgcExp n hn2 (kgcUnitGroup n).one = 1 := by
      show (cycMuStd n (by omega)).log (Quot.mk (modCong n).rel 1) = 1
      show ((1 : Int) % (n : Int)).toNat = 1
      have h1 : (1 : Int) % (n : Int) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
      rw [h1]
      rfl
    rw [he]
    show X.μ.mul z X.μ.one = z
    exact X.μ.mul_one z
  act_mul := by
    intro g h z
    show X.μ.pow z (kgcExp n hn2 ((kgcUnitGroup n).mul g h))
      = X.μ.pow (X.μ.pow z (kgcExp n hn2 h)) (kgcExp n hn2 g)
    rw [← cycRig_pow_mul X.μ X.comm z (kgcExp n hn2 h) (kgcExp n hn2 g)]
    rw [cycRig_pow_reduce X.μ X.comm z X.n (kgc_all_pow_ord X z)
      (kgcExp n hn2 ((kgcUnitGroup n).mul g h)),
      cycRig_pow_reduce X.μ X.comm z X.n (kgc_all_pow_ord X z)
        (kgcExp n hn2 h * kgcExp n hn2 g)]
    rw [hXn]
    exact congrArg (X.μ.pow z) (kgc_exp_mul n hn2 g h)

/-! ## M458F-4: M453F（位数 2）の特殊ケースとしての回収 -/

/-- **定理 (M458F-4a)** — 任意の CycMuGroup X の任意の元 z で、z^{X.n−1} = z⁻¹
    （`knc_pow_pred_eq_inv` の一般 z 版、`kgc_all_pow_ord` から）。 -/
theorem kgc_pow_pred_eq_inv_general (X : CycMuGroup) (z : X.μ.carrier) :
    X.μ.pow z (X.n - 1) = X.μ.inv z := by
  apply Grp.inv_eq_of_mul_eq_one
  have hone : X.μ.pow z 1 = z := by
    show X.μ.mul z X.μ.one = z
    exact X.μ.mul_one z
  have hsum : 1 + (X.n - 1) = X.n := by
    have h := X.hn
    omega
  have key := cycRig_pow_add X.μ X.comm z 1 (X.n - 1)
  rw [hsum, hone, kgc_all_pow_ord X z] at key
  exact key.symm

/-- **M458F-4b: 単元 a=n−1**（自己逆元、(n−1)²≡1 mod n）——複素共役型の
    位数 2 ケースの一般 n 版。 -/
def kgcNegOne (n : Nat) : kgcUnitCarrier n :=
  ⟨(Quot.mk (modCong n).rel ((n : Int) - 1), Quot.mk (modCong n).rel ((n : Int) - 1)), by
    show zmodMul n (Quot.mk (modCong n).rel ((n : Int) - 1))
        (Quot.mk (modCong n).rel ((n : Int) - 1))
      = Quot.mk (modCong n).rel 1
    apply Quot.sound
    show ((n : Nat) : Int) ∣ (((n : Int) - 1) * ((n : Int) - 1) - 1)
    have hcong : ((n : Nat) : Int) ∣ (((n : Int) - 1) - (-1)) := ⟨1, by omega⟩
    have hresult : ((n : Nat) : Int) ∣
        (((n : Int) - 1) * ((n : Int) - 1)) - ((-1 : Int) * (-1 : Int)) :=
      dvd_sub_mul hcong hcong
    have hval : (-1 : Int) * (-1 : Int) = 1 := by omega
    rw [hval] at hresult
    exact hresult⟩

/-- **定理 (M458F-4c: 本丸・M453F を特殊ケースとして回収)** — 単元 a=n−1
    （`kgcNegOne`）での本モジュールの作用は、M453F の複素共役型反転作用
    `kncCyclotomicActionGen X` の true ケースと literally 一致する
    （z^{n−1}=z⁻¹、`kgc_pow_pred_eq_inv_general` から）。 -/
theorem kgc_specializes_to_knc (n : Nat) (hn2 : 2 ≤ n) (X : CycMuGroup) (hXn : X.n = n)
    (z : X.μ.carrier) :
    ((kgcCyclotomicActionGen n hn2 X hXn).act (kgcNegOne n)).map z
      = ((kncCyclotomicActionGen X).act true).map z := by
  show X.μ.pow z (kgcExp n hn2 (kgcNegOne n)) = X.μ.inv z
  have he : kgcExp n hn2 (kgcNegOne n) = n - 1 := by
    show (cycMuStd n (by omega)).log (Quot.mk (modCong n).rel ((n : Int) - 1)) = n - 1
    show (((n : Int) - 1) % (n : Int)).toNat = n - 1
    have h1 : ((n : Int) - 1) % (n : Int) = (n : Int) - 1 :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [h1]
    have h2 : ((n : Int) - 1) = (((n - 1 : Nat) : Int)) := by
      have := hn2
      omega
    rw [h2, Int.toNat_natCast]
  rw [he, ← hXn]
  exact kgc_pow_pred_eq_inv_general X z

/-! ## M458F-5: 一般単元の非自明性 -/

/-- **定理 (M458F-5: 本丸・一般単元の非自明性)** — a-成分が単位元（class 1）と
    異なる任意の単元 g で、作用は生成元を動かす（σ_g(ζ)≠ζ）。`cycRig_pow_inj` に
    よる指数の相異性から完全証明する——M453F が位数 2 の 1 種に留めていたのを、
    任意の非自明単元へ実際に一般化する。 -/
theorem kgc_char_general (n : Nat) (hn2 : 2 ≤ n) (X : CycMuGroup) (hXn : X.n = n)
    (g : kgcUnitCarrier n) (hga : g.val.1 ≠ Quot.mk (modCong n).rel 1) :
    ((kgcCyclotomicActionGen n hn2 X hXn).act g).map X.ζ ≠ X.ζ := by
  intro heq
  apply hga
  show g.val.1 = Quot.mk (modCong n).rel 1
  have heq0 : X.μ.pow X.ζ (kgcExp n hn2 g) = X.ζ := heq
  have hone : X.μ.pow X.ζ 1 = X.ζ := by
    show X.μ.mul X.ζ X.μ.one = X.ζ
    exact X.μ.mul_one X.ζ
  have heq' : X.μ.pow X.ζ (kgcExp n hn2 g) = X.μ.pow X.ζ 1 := by
    rw [heq0, hone]
  have hmod : kgcExp n hn2 g % X.n = 1 % X.n :=
    cycRig_pow_inj X.μ X.comm X.ζ X.n X.hn X.ord X.distinct _ _ heq'
  have hmodn : kgcExp n hn2 g % n = 1 % n := by rw [hXn] at hmod; exact hmod
  have h1n : (1 : Nat) % n = 1 := Nat.mod_eq_of_lt (by omega)
  have hlt : kgcExp n hn2 g < n := (cycMuStd n (by omega)).log_lt g.val.1
  have heqExp : kgcExp n hn2 g = 1 := by
    have h2 : kgcExp n hn2 g % n = kgcExp n hn2 g := Nat.mod_eq_of_lt hlt
    rw [h1n] at hmodn
    rw [← h2, hmodn]
  have hpow1 : (cycMuStd n (by omega)).μ.pow (cycMuStd n (by omega)).ζ (kgcExp n hn2 g)
      = g.val.1 := (cycMuStd n (by omega)).pow_log g.val.1
  rw [heqExp] at hpow1
  show g.val.1 = (cycMuStd n (by omega)).ζ
  rw [← hpow1]
  show (cycMuStd n (by omega)).ζ = (cycMuStd n (by omega)).μ.mul
      (cycMuStd n (by omega)).ζ (cycMuStd n (by omega)).μ.one
  exact (( cycMuStd n (by omega)).μ.mul_one (cycMuStd n (by omega)).ζ).symm

/-! ## M458F-6: Galois 同変性を一般単元へ実インスタンス化——M453F の限定を破る本丸 -/

/-- **定理 (M458F-6a: hchar の証明)** — 標準模型 cycMuStd n と任意の CycMuGroup E
    （E.n=n）で、一般単元作用の円分指数は各単元 g で mod n 一致する
    （`cmu_log_pow_mod` から外部仮説でなく証明）。 -/
theorem kgc_hchar (n : Nat) (hn2 : 2 ≤ n) (E : CycMuGroup) (hEn : E.n = n)
    (g : kgcUnitCarrier n) :
    cycRigExp (kgcUnitGroup n) (cycMuStd n (by omega))
        (kgcCyclotomicActionGen n hn2 (cycMuStd n (by omega)) (kcwStdOrder n (by omega))) g
        % (cycMuStd n (by omega)).n
      = cycRigExp (kgcUnitGroup n) E (kgcCyclotomicActionGen n hn2 E hEn) g % E.n := by
  show (cycMuStd n (by omega)).log
      ((cycMuStd n (by omega)).μ.pow (cycMuStd n (by omega)).ζ (kgcExp n hn2 g))
      % (cycMuStd n (by omega)).n
    = E.log (E.μ.pow E.ζ (kgcExp n hn2 g)) % E.n
  rw [cmu_log_pow_mod (cycMuStd n (by omega)) (kgcExp n hn2 g),
    cmu_log_pow_mod E (kgcExp n hn2 g), kcwStdOrder n (by omega), hEn]

/-- **定理 (M458F-6b: 本丸・一般単元作用での Galois 同変性——M453F の限定を実際に
    破る)** — `cid_galois_equivariant`（M443F）を ρM=ρN=`kgcCyclotomicActionGen`
    （**任意の単元 g∈(ℤ/n)^×**、複素共役型の位数 2 に限らない）に実インスタンス化
    する。hchar は `kgc_hchar` で外部仮説でなく証明する。cidThetaMuIso が一般の
    (ℤ/n)^× 円分作用の下でも G_K 同変であることを示す。 -/
theorem kgc_galois_equivariant_general (n : Nat) (hn2 : 2 ≤ n)
    (E : CycMuGroup) (hEn : E.n = n) (g : kgcUnitCarrier n)
    (z : (cycMuStd n (by omega)).μ.carrier) :
    cmuMap (cycMuStd n (by omega)) E
        (((kgcCyclotomicActionGen n hn2 (cycMuStd n (by omega)) (kcwStdOrder n (by omega))).act
          g).map z)
      = ((kgcCyclotomicActionGen n hn2 E hEn).act g).map
          (cmuMap (cycMuStd n (by omega)) E z) :=
  cid_galois_equivariant (kgcUnitGroup n) (cycMuStd n (by omega)) E hEn.symm
    (kgcCyclotomicActionGen n hn2 (cycMuStd n (by omega)) (kcwStdOrder n (by omega)))
    (kgcCyclotomicActionGen n hn2 E hEn)
    (kgc_hchar n hn2 E hEn) g z

/-! ## M458F-7: M443F-7 の共有元同定を一般単元へ -/

/-- **定理 (M458F-7: 本丸・共有元同定の一般単元両立)** — M443F の共有指数元
    class(tccbExp j) を一般単元作用で twist した標準模型側の実現は、E 側で
    同じ元を twist した実現に一致する。`kgc_galois_equivariant_general`
    （同変性）と `cid_commutator_agree_via_iso`（M443F-7）を合成して示す。 -/
theorem kgc_commutator_agree_general (n : Nat) (hn2 : 2 ≤ n) (p : Nat)
    (ζ0 : (Zp p).carrier) (E : CycMuGroup) (hEn : E.n = n) (g : kgcUnitCarrier n)
    (j : Nat) :
    cmuMap (cycMuStd n (by omega)) E
        (((kgcCyclotomicActionGen n hn2 (cycMuStd n (by omega))
            (kcwStdOrder n (by omega))).act g).map
          (Quot.mk (modCong n).rel ((tccbExp j : Nat) : Int)))
      = ((kgcCyclotomicActionGen n hn2 E hEn).act g).map
          (E.μ.pow E.ζ ((((tccbExp j : Nat) : Int) % ((n : Nat) : Int)).toNat)) := by
  have hbridge : cmuMap (cycMuStd n (by omega)) E
      (Quot.mk (modCong n).rel ((tccbExp j : Nat) : Int))
    = E.μ.pow E.ζ ((((tccbExp j : Nat) : Int) % ((n : Nat) : Int)).toNat) :=
    (cid_commutator_agree_via_iso p n (by omega) ζ0 E hEn j).2
  rw [kgc_galois_equivariant_general n hn2 E hEn g
    (Quot.mk (modCong n).rel ((tccbExp j : Nat) : Int)), hbridge]

/-! ## M458F-8: 総括レコードと残る限定の宣言 -/

/-- **M458F-8a: 一般円分指標配線データ** — 一般単元 g の非自明性の可能性・一般単元
    作用での具体的 Galois 同変性・共有元同定の一般単元両立を一括束ねる（M453F の
    「位数 2 のみ」を一般 (ℤ/n)^× へ実際に破るデータ）。 -/
structure KummerGeneralCharData (n : Nat) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (p : Nat)
    (ζ0 : (Zp p).carrier) (E : CycMuGroup) (hEn : E.n = n) where
  /-- 標準模型上の a=n−1 の単元は自明単元と実際に異なる（生成元を動かす）。 -/
  charNontrivial : ((kgcCyclotomicActionGen n hn2 (cycMuStd n (by omega))
      (kcwStdOrder n (by omega))).act (kgcNegOne n)).map (cycMuStd n (by omega)).ζ
    ≠ (cycMuStd n (by omega)).ζ
  /-- 任意の単元 g での cidThetaMuIso の具体的 Galois 同変性。 -/
  galoisEquivariant : ∀ (g : kgcUnitCarrier n) (z : (cycMuStd n (by omega)).μ.carrier),
    cmuMap (cycMuStd n (by omega)) E
        (((kgcCyclotomicActionGen n hn2 (cycMuStd n (by omega))
            (kcwStdOrder n (by omega))).act g).map z)
      = ((kgcCyclotomicActionGen n hn2 E hEn).act g).map (cmuMap (cycMuStd n (by omega)) E z)
  /-- 共有指数元の twist 済み実現が両側で一致（全ての単元 g・j で）。 -/
  commutatorAgree : ∀ (g : kgcUnitCarrier n) (j : Nat),
    cmuMap (cycMuStd n (by omega)) E
        (((kgcCyclotomicActionGen n hn2 (cycMuStd n (by omega))
            (kcwStdOrder n (by omega))).act g).map
          (Quot.mk (modCong n).rel ((tccbExp j : Nat) : Int)))
      = ((kgcCyclotomicActionGen n hn2 E hEn).act g).map
          (E.μ.pow E.ζ ((((tccbExp j : Nat) : Int) % ((n : Nat) : Int)).toNat))

/-- **M458F-8b: witness 本体**（全フィールドを本モジュールの完全証明で埋める）。 -/
def kummerGeneralCharData (n : Nat) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (p : Nat)
    (ζ0 : (Zp p).carrier) (E : CycMuGroup) (hEn : E.n = n) :
    KummerGeneralCharData n hn2 hn3 p ζ0 E hEn where
  charNontrivial := by
    have h := kgc_specializes_to_knc n hn2 (cycMuStd n (by omega)) (kcwStdOrder n (by omega))
      (cycMuStd n (by omega)).ζ
    rw [h]
    exact knc_char_nontrivial n hn3
  galoisEquivariant := kgc_galois_equivariant_general n hn2 E hEn
  commutatorAgree := kgc_commutator_agree_general n hn2 p ζ0 E hEn

/-- **定理 (M458F-8c: capstone — 一般円分指標配線データの存在)** — n≥3（複素共役型
    特殊ケースの非自明性用）・E.n=n を外部仮定として与えれば、標準模型上の
    **一般の (ℤ/n)^× 円分指標**に関する非自明性・任意単元での具体的 Galois 同変性・
    共有元同定の両立（M453F の「位数 2 のみ」を実際に破るデータ）が存在する。 -/
theorem kgc_exists (n : Nat) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (p : Nat) (ζ0 : (Zp p).carrier)
    (E : CycMuGroup) (hEn : E.n = n) :
    Nonempty (KummerGeneralCharData n hn2 hn3 p ζ0 E hEn) :=
  ⟨kummerGeneralCharData n hn2 hn3 p ζ0 E hEn⟩

/-- **kgc_model_scope（正直な限定の宣言）**: 本モジュールが実際に閉じるのは、
    標準模型 cycMuStd n（n≥2）上の**一般の (ℤ/n)^× 円分指標**（単元 a による
    σ_a(ζ)=ζ^a）について、(i) a=n−1 の特殊ケースが M453F の複素共役型非自明作用と
    literally 一致すること、(ii) cidThetaMuIso が**任意の単元** g∈(ℤ/n)^× の作用の
    下でも G_K 同変であること——である。M453F knc_model_scope が「位数 2 の複素共役型
    χ 一種のみ」と正直に残した限定を、一般の (ℤ/n)^× 円分指標について実際に破る。
    kgcUnitGroup n の各単元は明示的な逆元データを伴う構成であり、任意の a に対する
    逆元の**アルゴリズム的計算**（Bézout の互除法）は本モジュールの範囲外——完全副有限
    円分指標 Ẑ^×(1) レベルの非自明性への配線、および M353F の具体的 Kummer 指標 κ 自身
    を非自明係数加群上の 1-コサイクルへ格上げする接続は、引き続き本モジュールの範囲外
    （後続）。 -/
theorem kgc_model_scope (n : Nat) (hn2 : 2 ≤ n) :
    (∀ (X : CycMuGroup) (hXn : X.n = n) (z : X.μ.carrier),
      ((kgcCyclotomicActionGen n hn2 X hXn).act (kgcNegOne n)).map z
        = ((kncCyclotomicActionGen X).act true).map z) ∧
    ∀ (E : CycMuGroup) (hEn : E.n = n),
      ∀ (g : kgcUnitCarrier n) (z : (cycMuStd n (by omega)).μ.carrier),
        cmuMap (cycMuStd n (by omega)) E
            (((kgcCyclotomicActionGen n hn2 (cycMuStd n (by omega))
                (kcwStdOrder n (by omega))).act g).map z)
          = ((kgcCyclotomicActionGen n hn2 E hEn).act g).map
              (cmuMap (cycMuStd n (by omega)) E z) :=
  ⟨fun X hXn z => kgc_specializes_to_knc n hn2 X hXn z,
    fun E hEn g z => kgc_galois_equivariant_general n hn2 E hEn g z⟩

/-! ## M458F-9: 実例 -/

/-- 実例: 標準模型 cycMuStd 5 上で、単元 a=4=n−1 の作用が M453F の複素共役型
    非自明作用と literally 一致する。 -/
example (z : (cycMuStd 5 (by omega)).μ.carrier) :
    ((kgcCyclotomicActionGen 5 (by omega) (cycMuStd 5 (by omega)) (kcwStdOrder 5 (by omega))).act
        (kgcNegOne 5)).map z
      = ((kncCyclotomicActionGen (cycMuStd 5 (by omega))).act true).map z :=
  kgc_specializes_to_knc 5 (by omega) (cycMuStd 5 (by omega)) (kcwStdOrder 5 (by omega)) z

/-- 実例: 標準模型 cycMuStd 5 の自己同定（E := cycMuStd 5 自身）で、単元 a=n−1
    の作用の下 cidThetaMuIso（の下位関数 cmuMap）が具体的に Galois 同変である
    ことを確認する。 -/
example (z : (cycMuStd 5 (by omega)).μ.carrier) :
    cmuMap (cycMuStd 5 (by omega)) (cycMuStd 5 (by omega))
        (((kgcCyclotomicActionGen 5 (by omega) (cycMuStd 5 (by omega))
            (kcwStdOrder 5 (by omega))).act (kgcNegOne 5)).map z)
      = ((kgcCyclotomicActionGen 5 (by omega) (cycMuStd 5 (by omega))
          (kcwStdOrder 5 (by omega))).act (kgcNegOne 5)).map
          (cmuMap (cycMuStd 5 (by omega)) (cycMuStd 5 (by omega)) z) :=
  kgc_galois_equivariant_general 5 (by omega) (cycMuStd 5 (by omega)) (kcwStdOrder 5 (by omega))
    (kgcNegOne 5) z

/-- 実例: 一般円分指標配線データが本物の具体例 n=5・p=7 で存在する
    （E := cycMuStd 5 自身）。 -/
example :
    Nonempty (KummerGeneralCharData 5 (by omega) (by omega) 7 (zpOne 7)
      (cycMuStd 5 (by omega)) (kcwStdOrder 5 (by omega))) :=
  kgc_exists 5 (by omega) (by omega) 7 (zpOne 7) (cycMuStd 5 (by omega)) (kcwStdOrder 5 (by omega))

end IUT
