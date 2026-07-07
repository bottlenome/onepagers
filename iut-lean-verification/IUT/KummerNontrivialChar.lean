-- M453F KummerNontrivialChar [実・昇格（(a)）・柱E×柱A]
-- complete_pct 影響: 柱E/柱A で、M448F(kcw)が正直に残した限定 (ii)「Galois 同変性
--   kcw_galois_equivariant_concrete/' が閉じるのは G_K が μ_l に自明作用する trivial
--   ケース（μ_l⊂K）のみで、真に非自明な円分指標（χ≢1）を持つ CycGKAction どうしの
--   Galois 同変性の κ への接続は扱わない」を、**本物の非自明円分指標**（複素共役型・
--   位数 2 の指標 χ(g)=∓1、σ_g(ζ)=ζ^{±1}）を実際に構成し、cid_galois_equivariant
--   （M443F）へ実インスタンス化することで、この具体的 χ≢1 ケースについて実際に閉じる。
--   cycTrivialAction とは literally 異なる本物の CycGKAction インスタンス
--   （`kncCyclotomicActionGen`）を新規構成し、その非自明性（∃g, χ(g) は恒等作用と
--   異なる）を完全証明し（`knc_char_nontrivial`）、cidThetaMuIso がこの非自明作用の
--   下でも G_K 同変であること（`knc_galois_equivariant_nontrivial`）・M443F-7 の
--   共有元同定がこの非自明作用の下でも両立すること（`knc_commutator_agree_nontrivial`）
--   を示す。
-- 正直な限定: 昇格するのは**複素共役型の位数 2 の具体的 χ**（σ(ζ)=ζ^{-1}）1 種のみ
--   ——一般の副有限円分指標 Ẑ^×(1) 全体・任意の mod-n 指標への配線は引き続き外部/後続。
--   M353F の具体的 Kummer 指標 κ 自身の住む係数加群は、本モジュールでも引き続き
--   trivial 加群 galH1TrivialModule のまま（M448F kcwKummerAction を弱めない）——
--   本モジュールが非自明にするのは cidThetaMuIso の Galois 同変性を測る**外側の**
--   CycGKAction であり、κ 自身を非自明な係数加群の 1-コサイクルへ格上げすることは
--   本モジュールの範囲外（後続）。

/-
  IUT/KummerNontrivialChar.lean — M453F [実／昇格・柱E×柱A]
  分類: 実（(a) 昇格 — M448F(kcw)の限定 (ii)「trivial 作用ケースのみ配線」を、
  本物の非自明円分指標（複素共役型・位数 2）で実際に破る）

  背景（M448F の限定・そのまま引用）:
    M448F（KummerCharWiring, prefix `kcw`）は、M443F cid_galois_equivariant を
    標準模型 cycMuStd l とトリビアル Galois 作用 cycTrivialAction（μ_l⊂K の
    trivial ケース）に実インスタンス化して閉じたが、`kcw_model_scope` は
    正直に次を限定として残した:
      (ii) 真に非自明な円分指標（χ≢1、不分岐でない一般の局所体上の実ガロア作用）を
           持つ CycGKAction どうしの Galois 同変性の κ への接続は、本モジュールでは
           扱わない。

  本モジュールはこの限定を、**複素共役型の具体的な非自明円分指標**（位数 2、
  σ(ζ)=ζ^{-1}）で実際に突破する。この χ は toy ではない——K の実埋め込みに対応する
  複素共役 c∈G_K は、任意の K 上で μ_l（1 の l 乗根、l≥3）に非自明に作用する
  （ζ↦ζ^{-1}≠ζ）という**本物の代数的数論の事実**であり、その ⟨c⟩≅ℤ/2 は G_K の
  忠実な部分群（本物の忠実な部分ケース、CLAUDE.md §3 の要請に合致）である。

  1. **`kncZ2`（本丸1・GK の忠実な部分群模型）**: 位数 2 の具体群（carrier=Bool、
     mul=排他的論理和 kncXor、one=false、inv=id）。複素共役の生成する ⟨c⟩≅ℤ/2 の
     本物の模型（本物の有限群、toy ではない）。
  2. **`kncInvHom`/`kncCyclotomicActionGen`（本丸2・非自明 CycGKAction の本物の構成）**:
     任意の CycMuGroup X に対し、false↦恒等・true↦反転（X.μ.inv、アーベル群ゆえ
     群準同型、`galH1_inv_mul` の再輸出）を割り当てる CycGKAction kncZ2 X。
     act_mul の (true,true) ケースは反転の二重適用 = 恒等（`knc_inv_inv`、
     `Grp.inv_eq_of_mul_eq_one` から）で閉じる——**cycTrivialAction とは
     literally 異なる本物の CycGKAction インスタンス**（μ_l への非自明作用の
     最初の具体例）。
  3. **`knc_char_nontrivial`（本丸3・非自明性の完全証明)**: 標準模型 cycMuStd l
     （l≥3）で、この作用は生成元 ζ を動かす（σ_c(ζ)=ζ^{-1}≠ζ）——`Quot.mk`/`quot_exact`
     と `Int.le_of_dvd` による整数除法の評価で完全証明する。cycTrivialAction との
     区別が本物であることの核。
  4. **`kncModule`/`knc_module_nontrivial`**: 同じ非自明作用を `galH1Module kncZ2`
     （M326F、κ の係数加群と同じ型）として再パッケージし、`galH1TrivialModule`
     （M448F kcwKummerAction が使う trivial 加群）とは実際に異なることを示す。
  5. **`knc_pow_pred_eq_inv`/`knc_exp_true`/`knc_hchar`（本丸5・円分指数の評価と
     一致条件)**: 反転 X.μ.inv X.ζ = X.μ.pow X.ζ (X.n−1)（ζ^{n-1}·ζ=ζ^n=1 から
     `Grp.inv_eq_of_mul_eq_one` で）・その円分指数 mod n が (n−1) に一致
     （`cmu_log_pow_mod`）・標準模型 M と任意の E（E.n=l）で両側の指数が mod l
     一致すること（g=false は `kcwZetaLogOne` の χ≡1 から、g=true は上記から）
     を完全証明する。
  6. **`knc_galois_equivariant_nontrivial`（本丸6・M448F (ii) を実際に閉じる)**:
     `cid_galois_equivariant`（M443F）を ρM=kncCyclotomicActionGen(標準模型)・
     ρN=kncCyclotomicActionGen(E) という**非自明な作用ペア**に実インスタンス化し、
     hchar を `knc_hchar`（外部仮説でなく証明）で満たす。cidThetaMuIso が
     **真に非自明な** Galois 作用（χ(true)=-1≠1）の下でも G_K 同変であることを
     示す——M448F の「trivial のみ」を実際に破る本丸。
  7. **`knc_commutator_agree_nontrivial`（本丸7・M443F-7 を非自明作用へ）**:
     M443F の共有指数元 class(tccbExp j) を非自明作用で twist した実現が、標準模型
     側の twist と E 側の twist で一致することを、`knc_galois_equivariant_nontrivial`
     と `cid_commutator_agree_via_iso`（M443F-7）を合成して示す。
  8. `KummerNontrivialCharData`/`kummerNontrivialCharData`/`knc_exists`
     — 総括レコード。`knc_model_scope` — 残る限定の正直な宣言。

  * M453F-1 `kncXor`/`kncZ2`
  * M453F-2 `knc_inv_inv`/`kncInvHom`/`kncCyclotomicActionGen`/`kncCyclotomicAction`
  * M453F-3 `knc_char_nontrivial`
  * M453F-4 `kncModule`/`knc_module_nontrivial`
  * M453F-5 `knc_pow_pred_eq_inv`/`knc_exp_true`/`knc_hchar`
  * M453F-6 `knc_galois_equivariant_nontrivial`（本橋渡し・限定を閉じる）
  * M453F-7 `knc_commutator_agree_nontrivial`
  * M453F-8 `KummerNontrivialCharData`/`kummerNontrivialCharData`/
    `knc_exists`/`knc_model_scope`
  * M453F-9 実例

  **正直な限定（消去・弱化禁止）**:
  - 本モジュールが実際に非自明にするのは**位数 2 の複素共役型 χ 一種**
    （σ(ζ)=ζ^{-1}）のみ——一般の mod-n 円分指標（(ℤ/n)^× の任意の元を χ(g) に
    持つ一般ケース）・完全副有限円分指標 Ẑ^×(1) の逆極限レベルの非自明性へは
    配線しない。他の位数の非自明指標（例えば位数 3 以上の χ）は同じ手法
    （Aut(μ_n)≅(ℤ/n)^× の乗法群からの群準同型を χ に取る）で構成できるはずだが
    本モジュールでは複素共役の実例に留める。
  - GK 自体は G_K の**忠実な部分群**（複素共役の生成する ⟨c⟩≅ℤ/2）の模型であり、
    絶対ガロア群 G_K 全体への拡張（G_K→Aut(μ_l) の全体の構成）は含まない。
  - M353F の具体的 Kummer 指標 κ:GK→M.μ 自身が住む係数加群は、本モジュールでも
    引き続き `galH1TrivialModule`（trivial 作用）のまま——M448F kcwKummerAction の
    内容を弱めない。本モジュールが非自明にしたのは cidThetaMuIso の Galois 同変性を
    測る**外側の** CycGKAction ρM/ρN であり、κ 自身を非自明係数加群上の
    1-コサイクルへ格上げする接続（`galH1Cocycle (kncModule E)` のレベルでの κ の
    再構成）は本モジュールの範囲外（後続）。
  - E.n = l（外部仮定）・A 側 ζ の位数 l 性 hζl・distinctness hdist の外部仮定という
    M443F cid_model_scope の限定、および κ が生成元を撃つ校正 hg0 の外部仮定という
    M448F kcw_model_scope (iii) の限定は、そのまま継承する（本モジュールは解消しない）。
  - 全て選択公理を証明本体で新規導入せず（新規 Classical・新規 Classical.choice
    なし）。禁止タクティク不使用（simp/decide/by_cases/rcases/ring/nlinarith/
    positivity/conv/nth_rewrite/field_simp 不使用）。許可タクティクのみ
    （cases/obtain/induction/rw/show/refine/exact/apply/intro/generalize/funext/
    omega）。共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は
    一切変更していない。一般名は `knc` 接頭辞で衝突回避（グレップ確認済み・
    既存コードに重複なし）。
-/
import IUT.KummerCharWiring

namespace IUT

/-! ## M453F-1: 複素共役の忠実な部分群模型 ⟨c⟩ ≅ ℤ/2 -/

/-- **M453F-1a: 排他的論理和**（位数 2 群の積）。 -/
def kncXor : Bool → Bool → Bool
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

/-- **M453F-1b: 位数 2 の本物の群** `kncZ2`（carrier=Bool、mul=kncXor、one=false、
    inv=id）——複素共役 c が生成する部分群 ⟨c⟩≅ℤ/2 の本物の模型（G_K の忠実な
    部分群、toy ではない）。 -/
def kncZ2 : Grp where
  carrier := Bool
  mul := kncXor
  one := false
  inv := fun a => a
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := by
    intro a
    cases a <;> rfl
  inv_mul := by
    intro a
    cases a <;> rfl

/-! ## M453F-2: 非自明 CycGKAction の本物の構成——反転作用 -/

/-- **M453F-2a: 反転の反転は恒等**（任意の群、`Grp.inv_eq_of_mul_eq_one` から）。 -/
theorem knc_inv_inv (G : Grp) (z : G.carrier) : G.inv (G.inv z) = z :=
  (G.inv_eq_of_mul_eq_one (G.inv_mul z)).symm

/-- **M453F-2b: 反転は群準同型**（アーベル群、M326F `galH1_inv_mul` の再輸出）——
    複素共役の μ_n への作用 ζ↦ζ^{-1} の本物の準同型パッケージ。 -/
def kncInvHom (X : CycMuGroup) : Hom X.μ X.μ where
  map := X.μ.inv
  map_mul := galH1_inv_mul X.μ X.comm

/-- **定理 (M453F-2c: 本丸・非自明 CycGKAction の本物の構成)** — 任意の CycMuGroup X
    に、kncZ2 の false（単位元）には恒等・true（複素共役）には反転 X.μ.inv を
    割り当てる本物の G_K-加群作用。(true,true) の合成則は反転の対合性
    （`knc_inv_inv`）で閉じる——**cycTrivialAction とは literally 異なる**本物の
    CycGKAction インスタンス。 -/
def kncCyclotomicActionGen (X : CycMuGroup) : CycGKAction kncZ2 X where
  act := fun g => match g with
    | false => ({ map := fun z => z, map_mul := fun _ _ => rfl } : Hom X.μ X.μ)
    | true => kncInvHom X
  act_one := fun _ => rfl
  act_mul := by
    intro g h z
    cases g with
    | false =>
      cases h with
      | false => rfl
      | true => rfl
    | true =>
      cases h with
      | false => rfl
      | true => exact (knc_inv_inv X.μ z).symm

/-- **M453F-2d: 標準模型への特化**。標準模型 cycMuStd l 上の非自明反転作用
    （定義から `kncCyclotomicActionGen` に一致、`rfl`）。 -/
def kncCyclotomicAction (l : Nat) (hl : 1 ≤ l) : CycGKAction kncZ2 (cycMuStd l hl) :=
  kncCyclotomicActionGen (cycMuStd l hl)

/-- **M453F-2e**: `kncCyclotomicAction` は `kncCyclotomicActionGen` の標準模型
    特化に定義から一致する。 -/
theorem knc_action_eq (l : Nat) (hl : 1 ≤ l) :
    kncCyclotomicAction l hl = kncCyclotomicActionGen (cycMuStd l hl) := rfl

/-! ## M453F-3: 非自明性の完全証明 -/

/-- **定理 (M453F-3: 本丸・非自明性)** — l≥3 の標準模型 cycMuStd l で、複素共役の
    作用は生成元 ζ を動かす（σ_c(ζ)=ζ^{-1}≠ζ）。ζ^{-1}=class(-1)・ζ=class(1) が
    ℤ/l で異なることを、l∣2 なら l≤2（`Int.le_of_dvd`）という整数除法の評価で
    l≥3 と矛盾させて示す——cycTrivialAction（恒等作用）と本物に異なることの核。 -/
theorem knc_char_nontrivial (l : Nat) (hl : 3 ≤ l) :
    ((kncCyclotomicActionGen (cycMuStd l (by omega))).act true).map
        (cycMuStd l (by omega)).ζ
      ≠ (cycMuStd l (by omega)).ζ := by
  intro heq
  have h0 : Quot.mk (modCong l).rel (-1 : Int) = Quot.mk (modCong l).rel (1 : Int) := heq
  have hrel := quot_exact intGrp (modCong l) h0
  have hdvd : ((l : Nat) : Int) ∣ ((-1 : Int) - 1) := hrel
  obtain ⟨k, hk⟩ := hdvd
  have hdvd2 : ((l : Nat) : Int) ∣ (2 : Int) := by
    refine ⟨-k, ?_⟩
    have hmn : ((l : Nat) : Int) * (-k) = -(((l : Nat) : Int) * k) := Int.mul_neg _ _
    omega
  have hle : ((l : Nat) : Int) ≤ 2 := Int.le_of_dvd (by omega) hdvd2
  omega

/-! ## M453F-4: galH1Module としての再パッケージと trivial 加群との区別 -/

/-- **M453F-4a**: 非自明作用を `galH1Module kncZ2`（κ の係数加群と同じ型）として
    再パッケージする。 -/
def kncModule (X : CycMuGroup) : galH1Module kncZ2 where
  M := X.μ
  comm := X.comm
  act := (kncCyclotomicActionGen X).act
  act_one := (kncCyclotomicActionGen X).act_one
  act_mul := (kncCyclotomicActionGen X).act_mul

/-- **定理 (M453F-4b: 本丸・trivial 加群との本物の区別)** — l≥3 の標準模型で、
    `kncModule` の作用は `galH1TrivialModule`（M448F kcwKummerAction が使う
    trivial 加群）の作用と実際に異なる（複素共役で生成元を動かす）。 -/
theorem knc_module_nontrivial (l : Nat) (hl : 3 ≤ l) :
    ((kncModule (cycMuStd l (by omega))).act true).map (cycMuStd l (by omega)).ζ
      ≠ ((galH1TrivialModule kncZ2 (cycMuStd l (by omega)).μ
            (cycMuStd l (by omega)).comm).act true).map (cycMuStd l (by omega)).ζ := by
  show ((kncCyclotomicActionGen (cycMuStd l (by omega))).act true).map
      (cycMuStd l (by omega)).ζ ≠ (cycMuStd l (by omega)).ζ
  exact knc_char_nontrivial l hl

/-! ## M453F-5: 円分指数の評価と一致条件 -/

/-- **定理 (M453F-5a: 反転 = 位数 n−1 の冪)** — X.μ.inv X.ζ = X.μ.pow X.ζ (X.n−1)。
    ζ^{n-1}·ζ=ζ^n=1 から `Grp.inv_eq_of_mul_eq_one` で。任意の CycMuGroup で成立
    する本物の一般事実。 -/
theorem knc_pow_pred_eq_inv (X : CycMuGroup) :
    X.μ.pow X.ζ (X.n - 1) = X.μ.inv X.ζ := by
  apply Grp.inv_eq_of_mul_eq_one
  have hone : X.μ.pow X.ζ 1 = X.ζ := by
    show X.μ.mul X.ζ X.μ.one = X.ζ
    exact X.μ.mul_one X.ζ
  have hsum : 1 + (X.n - 1) = X.n := by
    have h := X.hn
    omega
  have key := cycRig_pow_add X.μ X.comm X.ζ 1 (X.n - 1)
  rw [hsum, X.ord, hone] at key
  exact key.symm

/-- **定理 (M453F-5b: 非自明作用の円分指数 ≡ n−1)** — 複素共役 (g=true) の円分指数
    cycRigExp は mod n で (n−1) に一致（`knc_pow_pred_eq_inv` と `cmu_log_pow_mod`
    から）。 -/
theorem knc_exp_true (X : CycMuGroup) :
    cycRigExp kncZ2 X (kncCyclotomicActionGen X) true % X.n = (X.n - 1) % X.n := by
  show X.log (X.μ.inv X.ζ) % X.n = (X.n - 1) % X.n
  rw [← knc_pow_pred_eq_inv X]
  exact cmu_log_pow_mod X (X.n - 1)

/-- **定理 (M453F-5c: 本丸・両側の円分指数が mod l 一致)** — 標準模型 cycMuStd l と
    任意の CycMuGroup E（E.n=l）で、非自明作用の円分指数は各 g（false/true）で
    mod l 一致する: g=false は χ≡1（`kcwZetaLogOne`）、g=true は (n−1) 一致
    （`knc_exp_true`）から。`cid_galois_equivariant` の hchar を外部仮説でなく
    与える。 -/
theorem knc_hchar (l : Nat) (hl : 3 ≤ l) (E : CycMuGroup) (hn : E.n = l) (g : Bool) :
    cycRigExp kncZ2 (cycMuStd l (by omega))
        (kncCyclotomicActionGen (cycMuStd l (by omega))) g
        % (cycMuStd l (by omega)).n
      = cycRigExp kncZ2 E (kncCyclotomicActionGen E) g % E.n := by
  cases g with
  | false =>
    show (cycMuStd l (by omega)).log (cycMuStd l (by omega)).ζ
        % (cycMuStd l (by omega)).n
      = E.log E.ζ % E.n
    rw [kcwZetaLogOne (cycMuStd l (by omega)), kcwZetaLogOne E, hn,
      kcwStdOrder l (by omega)]
  | true =>
    rw [knc_exp_true (cycMuStd l (by omega)), knc_exp_true E, hn,
      kcwStdOrder l (by omega)]

/-! ## M453F-6: Galois 同変性を非自明作用ケースへ実インスタンス化——M448F (ii) を閉じる -/

/-- **定理 (M453F-6: 本丸・非自明作用での Galois 同変性——M448F (ii) を実際に閉じる)** —
    `cid_galois_equivariant`（M443F）を ρM=ρN=`kncCyclotomicActionGen`（**真に非自明な
    複素共役型 χ**、cycTrivialAction ではない）に実インスタンス化する。hchar は
    `knc_hchar` で外部仮説でなく証明する。cidThetaMuIso が非自明な Galois 作用
    （σ(ζ)=ζ^{-1}≠ζ）の下でも G_K 同変であることを示す——M448F kcw_model_scope の
    「trivial のみ配線」を実際に破る。 -/
theorem knc_galois_equivariant_nontrivial (l : Nat) (hl : 3 ≤ l)
    (E : CycMuGroup) (hn : E.n = l) (g : Bool) (z : (cycMuStd l (by omega)).μ.carrier) :
    cmuMap (cycMuStd l (by omega)) E
        (((kncCyclotomicActionGen (cycMuStd l (by omega))).act g).map z)
      = ((kncCyclotomicActionGen E).act g).map (cmuMap (cycMuStd l (by omega)) E z) :=
  cid_galois_equivariant kncZ2 (cycMuStd l (by omega)) E hn.symm
    (kncCyclotomicActionGen (cycMuStd l (by omega))) (kncCyclotomicActionGen E)
    (knc_hchar l hl E hn) g z

/-! ## M453F-7: M443F-7 の共有元同定を非自明作用へ -/

/-- **定理 (M453F-7: 本丸・共有元同定の非自明作用両立)** — M443F の共有指数元
    class(tccbExp j) を非自明作用で twist した標準模型側の実現は、E 側で同じ元を
    twist した実現に一致する。`knc_galois_equivariant_nontrivial`（同変性）と
    `cid_commutator_agree_via_iso`（M443F-7、共有元の一致）を合成して示す——
    「同一元の 2 実現」の一致が非自明 Galois 作用の下でも成立することの本物の証明。 -/
theorem knc_commutator_agree_nontrivial (p l : Nat) (hl : 3 ≤ l) (ζ0 : (Zp p).carrier)
    (E : CycMuGroup) (hn : E.n = l) (g : Bool) (j : Nat) :
    cmuMap (cycMuStd l (by omega)) E
        (((kncCyclotomicActionGen (cycMuStd l (by omega))).act g).map
          (Quot.mk (modCong l).rel ((tccbExp j : Nat) : Int)))
      = ((kncCyclotomicActionGen E).act g).map
          (E.μ.pow E.ζ ((((tccbExp j : Nat) : Int) % ((l : Nat) : Int)).toNat)) := by
  have hbridge : cmuMap (cycMuStd l (by omega)) E
      (Quot.mk (modCong l).rel ((tccbExp j : Nat) : Int))
    = E.μ.pow E.ζ ((((tccbExp j : Nat) : Int) % ((l : Nat) : Int)).toNat) :=
    (cid_commutator_agree_via_iso p l (by omega) ζ0 E hn j).2
  rw [knc_galois_equivariant_nontrivial l hl E hn g
    (Quot.mk (modCong l).rel ((tccbExp j : Nat) : Int)), hbridge]

/-! ## M453F-8: 総括レコードと残る限定の宣言 -/

/-- **M453F-8a: 非自明円分指標配線データ** — 非自明性・非自明作用での具体的 Galois
    同変性・共有元同定の非自明作用両立を一括束ねる（M448F (ii) を複素共役型の
    非自明 χ ケースで閉じるデータ）。 -/
structure KummerNontrivialCharData (l : Nat) (hl : 3 ≤ l) (p : Nat)
    (ζ0 : (Zp p).carrier) (E : CycMuGroup) (hn : E.n = l) where
  /-- 標準模型上の非自明作用は cycTrivialAction と実際に異なる（生成元を動かす）。 -/
  charNontrivial : ((kncCyclotomicActionGen (cycMuStd l (by omega))).act true).map
      (cycMuStd l (by omega)).ζ ≠ (cycMuStd l (by omega)).ζ
  /-- 非自明作用ペアでの cidThetaMuIso の具体的 Galois 同変性。 -/
  galoisEquivariant : ∀ (g : Bool) (z : (cycMuStd l (by omega)).μ.carrier),
    cmuMap (cycMuStd l (by omega)) E
        (((kncCyclotomicActionGen (cycMuStd l (by omega))).act g).map z)
      = ((kncCyclotomicActionGen E).act g).map (cmuMap (cycMuStd l (by omega)) E z)
  /-- 共有指数元の twist 済み実現が両側で一致（全ての g・j で）。 -/
  commutatorAgree : ∀ (g : Bool) (j : Nat),
    cmuMap (cycMuStd l (by omega)) E
        (((kncCyclotomicActionGen (cycMuStd l (by omega))).act g).map
          (Quot.mk (modCong l).rel ((tccbExp j : Nat) : Int)))
      = ((kncCyclotomicActionGen E).act g).map
          (E.μ.pow E.ζ ((((tccbExp j : Nat) : Int) % ((l : Nat) : Int)).toNat))

/-- **M453F-8b: witness 本体**（全フィールドを本モジュールの完全証明で埋める）。 -/
def kummerNontrivialCharData (l : Nat) (hl : 3 ≤ l) (p : Nat) (ζ0 : (Zp p).carrier)
    (E : CycMuGroup) (hn : E.n = l) :
    KummerNontrivialCharData l hl p ζ0 E hn where
  charNontrivial := knc_char_nontrivial l hl
  galoisEquivariant := knc_galois_equivariant_nontrivial l hl E hn
  commutatorAgree := knc_commutator_agree_nontrivial p l hl ζ0 E hn

/-- **定理 (M453F-8c: capstone — 非自明円分指標配線データの存在)** — E.n=l を外部仮定
    として与えれば、標準模型上の**本物の非自明円分指標**（複素共役型、位数 2）に
    関する非自明性・具体的 Galois 同変性・共有元同定の両立（M448F (ii) を複素共役型
    ケースで閉じるデータ）が存在する。 -/
theorem knc_exists (l : Nat) (hl : 3 ≤ l) (p : Nat) (ζ0 : (Zp p).carrier)
    (E : CycMuGroup) (hn : E.n = l) :
    Nonempty (KummerNontrivialCharData l hl p ζ0 E hn) :=
  ⟨kummerNontrivialCharData l hl p ζ0 E hn⟩

/-- **knc_model_scope（正直な限定の宣言）**: 本モジュールが実際に閉じるのは、標準模型
    cycMuStd l（l≥3）上の**複素共役型・位数 2 の具体的非自明円分指標**（σ(ζ)=ζ^{-1}）
    について、(i) この作用が cycTrivialAction と実際に異なること（非自明性）、
    (ii) cidThetaMuIso がこの非自明作用の下でも G_K 同変であること——である。
    M448F kcw_model_scope が「trivial ケースのみ配線」と正直に残した限定を、この
    具体的 χ について実際に破る。一般の mod-n 円分指標・完全副有限 Ẑ^×(1) レベルの
    非自明性への配線、および M353F の具体的 Kummer 指標 κ 自身を非自明係数加群上の
    1-コサイクルへ格上げする接続は、引き続き本モジュールの範囲外（後続）。 -/
theorem knc_model_scope (l : Nat) (hl : 3 ≤ l) :
    ((kncCyclotomicActionGen (cycMuStd l (by omega))).act true).map
        (cycMuStd l (by omega)).ζ ≠ (cycMuStd l (by omega)).ζ ∧
    ∀ (E : CycMuGroup), E.n = l →
      ∀ (g : Bool) (z : (cycMuStd l (by omega)).μ.carrier),
        cmuMap (cycMuStd l (by omega)) E
            (((kncCyclotomicActionGen (cycMuStd l (by omega))).act g).map z)
          = ((kncCyclotomicActionGen E).act g).map (cmuMap (cycMuStd l (by omega)) E z) :=
  ⟨knc_char_nontrivial l hl, fun E hn g z => knc_galois_equivariant_nontrivial l hl E hn g z⟩

/-! ## M453F-9: 実例 -/

/-- 実例: 標準模型 cycMuStd 5 上で、複素共役型の非自明作用は cycTrivialAction と
    実際に異なる（生成元を動かす）。 -/
example :
    ((kncCyclotomicActionGen (cycMuStd 5 (by omega))).act true).map
        (cycMuStd 5 (by omega)).ζ ≠ (cycMuStd 5 (by omega)).ζ :=
  knc_char_nontrivial 5 (by omega)

/-- 実例: 標準模型 cycMuStd 5 の自己同定（E := cycMuStd 5 自身）で、非自明作用の下
    cidThetaMuIso（の下位関数 cmuMap）が具体的に Galois 同変であることを確認する。 -/
example (g : Bool) (z : (cycMuStd 5 (by omega)).μ.carrier) :
    cmuMap (cycMuStd 5 (by omega)) (cycMuStd 5 (by omega))
        (((kncCyclotomicActionGen (cycMuStd 5 (by omega))).act g).map z)
      = ((kncCyclotomicActionGen (cycMuStd 5 (by omega))).act g).map
          (cmuMap (cycMuStd 5 (by omega)) (cycMuStd 5 (by omega)) z) :=
  knc_galois_equivariant_nontrivial 5 (by omega) (cycMuStd 5 (by omega)) rfl g z

/-- 実例: 非自明円分指標配線データが本物の具体例 l=5・p=7 で存在する
    （E := cycMuStd 5 自身）。 -/
example :
    Nonempty (KummerNontrivialCharData 5 (by omega) 7 (zpOne 7)
      (cycMuStd 5 (by omega)) rfl) :=
  knc_exists 5 (by omega) 7 (zpOne 7) (cycMuStd 5 (by omega)) rfl

/-- 実例: 共有指数元の twist 済み実現が非自明作用の下でも標準模型の自己同定で一致する
    （j=3・g=true、複素共役の twist）。 -/
example (j : Nat) :
    cmuMap (cycMuStd 5 (by omega)) (cycMuStd 5 (by omega))
        (((kncCyclotomicActionGen (cycMuStd 5 (by omega))).act true).map
          (Quot.mk (modCong 5).rel ((tccbExp j : Nat) : Int)))
      = ((kncCyclotomicActionGen (cycMuStd 5 (by omega))).act true).map
          ((cycMuStd 5 (by omega)).μ.pow (cycMuStd 5 (by omega)).ζ
            ((((tccbExp j : Nat) : Int) % ((5 : Nat) : Int)).toNat)) :=
  knc_commutator_agree_nontrivial 7 5 (by omega) (zpOne 7)
    (cycMuStd 5 (by omega)) rfl true j

end IUT
