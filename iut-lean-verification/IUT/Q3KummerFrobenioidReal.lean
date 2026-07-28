/-
  IUT/Q3KummerFrobenioidReal.lean — q9kf（柱C・C6「実 Kummer–Frobenioid 両立」）
    実局所体 L₂ = ℚ₃(ζ₃) の実 Kummer データ（立方剰余類）を、M307F/M331F の
    Frobenioid 因子・次数・射の形式へ **実付値で実体化して** 接続する。

  ── 主要成果の分類: **[実／(a) 昇格]**。
     昇格の中身は M307F `PicardDivisor` と M331F `FrobenioidCategory` が自ら
     正直限定に書いた次の一点である:
       「付値系は `PicDivValuation` を**パラメータ**として受け取る……特定の楕円曲線／
        局所体上の実付値で `PicDivValuation` を**実体化**するのは後続」(M307F §正直な限定)
     本ファイルはその「後続」を実行する——本リポジトリで**初めて** `PicDivValuation` を
     実算術データで実体化し（従来の唯一のインスタンスは全付値 0 の
     `picDivTrivialVal`＝空虚）、実 L₂^× = `q3rqLx` = ℤ×U₂（R1 q3rq の実単数群 U₂ =
     O_{L₂}^× 付き群提示）の実 λ-付値を Frobenioid の因子・次数・Frobenius 射へ載せる。
     主語は実 q3rqLx・実 ζ₃・実単数 4・実埋め込み ℚ₃^×↪L₂^×（分岐 e=2）であり、
     toy 模型（m202fVol 型・Bool 軌道・surrogate 群）は主語に一切現れない。

  complete_pct 影響: **C6「実 Kummer–Frobenioid 両立」0.00 →（監査次第）**。
     C6 は未着手 0 であった。本ファイルは C6 の**両側を実対象で結ぶ最初の定理群**を与える:
      (i) Kummer 側は実 L₂^× の立方剰余（q9cq/q9c3 の実クラス [λ]・[ζ₃]・[4]）、
      (ii) Frobenioid 側は M307F の因子群 Div・次数準同型 deg・Frobenius [n]・M331F の
           射 `frobCHom`——これらを**実 λ-付値で実体化**して初めて算術的中身を持たせる。
     ただし下記「Frobenioid 側の実在性についての正直申告」を必ず併読のこと。

  ## Frobenioid 側の実在性についての正直申告（★ 本ファイルの第一の発見・消去禁止）

  監査・後続実装者への一次情報として明記する:
  * M307F `picDivGrp`（Div）・M331F `frobCCat`・M411F/M416F/M449F の Frobenioid 層は
    **代数としては本物だが、算術的入力を一切持たない汎用枠組み**であった。素点は
    「ℕ で番号付けされた添字」であって Spec の点ではなく、付値は構造体
    `PicDivValuation` の**パラメータ**である。本ファイル執筆時点で `PicDivValuation` の
    インスタンスはコードベース全体で `picDivTrivialVal`（全付値 0＝div≡0）ただ 1 つであり、
    Frobenioid の圏・realification・log-theta-lattice はいずれも**実体化された付値なしで**
    積み上げられていた（`grep picDivPrincipalHom` の結果は M307F と M311F IdealClassGroup
    の 2 ファイルのみで、いずれも G と v を全称パラメータとして受ける）。
  * したがって「実 Kummer × 実 Frobenioid」の両立は、**Frobenioid 側に実算術を注入する**
    ところからしか始まらない。本ファイルはその注入（実 L₂^× の実 λ-付値 → 実 div → 実 deg →
    実 frobCHom）を行い、その上で実 Kummer 側との両立を証明する。
  * それでも **C6 は本ファイルで閉じない**。残る本質的欠落を名指しする（後続の設計図）:
      (1) 素点集合が Spec O_{L₂} の点として実体化されていない（本ファイルの実付値は
          唯一の閉点 λ に対応する第 0 素点のみを使い、他の ℕ 添字は 0 で埋める。
          局所体としては数学的に正しいが、Div の「自由アーベル群」性は実質使われない）。
      (2) Frobenioid の **realification/Arakelov 次数**（C3=0.05）は実計量を持たないので、
          本ファイルは実 deg を **ℤ 値**でしか接続しない（実数値 deg_ℝ とは接続しない）。
      (3) **theta-link（×2l）・log-link・log-theta-lattice の対象は依然として実算術入力を
          持たない**（M416F/M449F は本ファイルの実付値を使っていない）。ゆえに
          「実 Kummer ↔ 実 theta-link Frobenioid」は未達。
      (4) Galois コホモロジー側（q9kh の H¹・q9kd の実 Gal⟨σ⟩・μ₃(O_M)）とは**接続しない**。
          本ファイルの両立は L₂ レベルの立方剰余群と因子次数の間のものである（§正直な限定 4）。

  ## 内容（q9kf-1 .. q9kf-10）

  * q9kf-1 `q9kfOrdL`/`q9kfValL`/`q9kfValQ`
        — **実付値データ**（コードベース初の非自明 `PicDivValuation` インスタンス）:
          L₂^× の λ-付値（群提示第 1 成分）・ℚ₃^× の 3-付値。
  * q9kf-2 `q9kfDivL`/`q9kfDivQ`/`q9kfDeg`/`q9kf_deg_eq_val`/`q9kf_deg_mul`
        — 実単項因子準同型 div : L₂^× → Div と **Frobenioid 次数 = 実 λ-付値**。
  * q9kf-3 `q9kfPow`/`q9kf_div_pow`/`q9kfCube`/`q9kf_div_cube`/`q9kf_deg_cube`
        — **べき写像 ↔ Frobenius [n]**: div(xⁿ) = [n]·div(x)（Kummer 指数 l=3 は [3]）。
  * q9kf-4 `q9kfKummerRel`/`q9kf_deg_kummer_invariant`/`q9kf_deg_mod3_wd`
        — **★ 中核: Frobenioid 次数 mod 3 は実 Kummer 立方類の不変量**。
  * q9kf-5 `q9kf_deg_lambda`/`q9kf_frobenioid_detects_lambda`/`q9kf_deg_unit_zero`
          /`q9kf_degree_blind_to_units`
        — 次数は [λ] を検出し、単数方向（[ζ₃]・[4]＝既知 3 次元のうち 2 次元）には**盲目**。
  * q9kf-6 `q9kfCubeHom`/`q9kfCubeSub`/`q9kfCubeQuot`/`q9kfProj`
        — **実立方剰余群 L₂^×/(L₂^×)³ を literal な商群として構成**（q9cq 正直限定 3
          「商群オブジェクトは建てない」を、q9cq を書き換えずに新ファイルの構成で discharge）。
  * q9kf-7 `q9kfZ3`/`q9kfDegClass`/`q9kf_degClass_proj`/`q9kf_degClass_surjective`
          /`q9kf_degClass_lambda_ne_one`/`q9kf_degClass_units_one`
          /`q9kf_degree_kummer_compatibility`
        — **実 Kummer 群 → ℤ/3 の Frobenioid 次数準同型**（因子次数が誘導する本物の Hom）と
          その像・核の実計算（全射・[λ] は生成元へ・[ζ₃]/[4] は核だが商群では非自明）。
  * q9kf-8 `q9kfCubeMor`/`q9kfRamMor`/`q9kf_ram_degree_two`/`q9kf_comp_degree_six`
        — **実算術から来る Frobenioid 射**: 立方＝Frobenius 次数 3 の射、実分岐
          ℚ₃^×↪L₂^×（e=2）＝Frobenius 次数 2 の射、合成の次数 6 = e·l（M331F 次数関手）。
  * q9kf-9 `q9kfCoeff`/`q9kf_place0_surjective`/`q9kf_place1_not_principal`
          /`q9kf_pic_bookkeeping_artifact`
        — **★ 素点簿記の忠実性診断（定理）**: 実 λ-方向では div は全射（忠実）だが、
          M307F の ℕ 添字「幽霊素点」[P₁] は単項でなく Pic を非自明にする。局所体の
          真の Pic は 0 ゆえ、これは Frobenioid 因子層が Spec O_{L₂} を忠実に表して
          いないことの**証明された証拠**（C6 完成に必要な作業の名指し）。
  * q9kf-10 capstone `Q3KummerFrobenioidData`/`q9kf_data`/`q9kf_exists`。

  ## 消費（再主張しない・二重計上防止）

  * [λ] の非立方性は `q9cq_lambda_nontrivial`（B6・q9cq）で**既に証明済**。本ファイルの
    `q9kf_frobenioid_detects_lambda` は**同じ事実**を Frobenioid 次数関手経由で導く
    別経路であり、**新しい算術的事実ではない**（新しいのは「その障害が Frobenioid の
    次数準同型の像である」という同定）。付値方向一般形も `q9cq_val_nontrivial` を消費。
  * [ζ₃]・[ζ₃²]・[4]・[16] の非立方性は `q9cq`/`q9c3`（B6）を消費する。
  * 実 L₂^×=ℤ×U₂・実 ζ₃・実 4・埋め込み ℚ₃^×↪L₂^×（e=2）は R1 `q3rq`／B2 `q9rc` を消費。
  * Div・deg・[n]・Pic・frobCHom・圏公理・次数関手は M307F/M331F を消費（再証明しない）。

  ## 正直な限定（§4 規約により消さない・弱めない・追記のみ）

  1. **素点は 1 個**。実付値は Spec O_{L₂} の唯一の閉点 λ に対応する第 0 素点のみを
     非自明に使う（局所体として正しいが、Div の自由アーベル群としての階数は実質 1）。
     大域体（数体）の実素点族での実体化・積公式との接続は未達。
  2. **次数は ℤ 値**。実数値 realified degree（M411F `frRealDeg`・Arakelov, C3=0.05）とは
     接続しない——実計量が存在しないため（上記 Frobenioid 実在性申告 (2)）。
  3. **theta-link/log-link とは未接続**（同 (3)）。本ファイルの実対象は M416F/M449F の
     Θ-link 函手・log-theta-lattice に入力されていない。C6 の IUT 本来の主張
     （Kummer 同型が Frobenioid の Θ-link 両側で両立する）は未達。
  4. **Galois コホモロジー側と未接続**（同 (4)）。q9kh の H¹(Gal(M/L₂),μ₃)・q9kd の実 σ・
     μ₃(O_M) は本ファイルに現れない。ここでの「Kummer」は実 L₂^×/(L₂^×)³ の意味である。
     実 μ₃ 由来のクラスが次数 0 であること（q9kf-5）は、まさに次数関手が H¹ 方向を
     見ないことの証拠であり、この限定を数値的に裏づけている。
  5. **[λ] 非立方性は新規事実でない**（上記「消費」）。本ファイルの新規性は Frobenioid 側の
     実体化・literal 立方剰余商群・誘導次数準同型・実算術由来の Frobenioid 射にある。
  6. q3rq/q9cq/q9c3 の恒久限定（O_L と L^× のみ・体化なし・rank≥3 下界のみ・n=3・体 L₂ 1 個）
     を継承する。
  7. **`q9kf_deg_eq_val`（deg = v_λ）自体は浅い**（付値データを差し込めば `0 + v = v` に
     還元される）。本ファイルの数学的中身はその等式ではなく、(i) 実 Kummer 立方剰余群を
     literal 商群として構成したこと、(ii) 次数準同型が**その商上で well-defined**である
     こと（well-defined 性の証明が q9kf-4 の Kummer 不変性そのもの）、(iii) 実分岐 e=2 と
     実 Kummer 指数 l=3 が **Frobenioid 射の Frobenius 次数**として現れること、
     (iv) q9kf-9 の忠実性診断、にある。過大主張を避けるため明記する。
  8. **素点簿記は忠実でない**（q9kf-9 で定理化）。M307F の Div は ℕ 添字の幽霊素点を
     持ち、実局所体の Pic=0 を再現しない。C6 の完成には素点集合の実 Spec 化が必要。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3CubeRankThree
import IUT.FrobenioidCategory

namespace IUT

/-! ## q9kf-1: 実付値データ（コードベース初の非自明 `PicDivValuation` 実体化） -/

/-- **q9kf-1a: 実 λ-付値の素点分解** — 実 L₂^× = ℤ×U₂ の第 0 素点（唯一の閉点 λ）の
    付値は群提示の第 1 成分 v_λ、その他の ℕ 添字素点では 0。局所体 L₂ の Spec は
    閉点 1 個ゆえこれが正しい因子データである。 -/
def q9kfOrdL : Nat → q3rqLx.carrier → Int
  | 0 => fun x => x.1
  | _ + 1 => fun _ => 0

/-- **q9kf-1b（★ 初）: 実 L₂^× の付値データ** — M307F `PicDivValuation` の
    **実算術インスタンス**。従来の唯一のインスタンスは全付値 0 の `picDivTrivialVal`
    （div≡0＝空虚）であった。 -/
def q9kfValL : PicDivValuation q3rqLx where
  ord := q9kfOrdL
  ord_mul := by
    intro k a b
    cases k with
    | zero =>
      show (q3rqLx.mul a b).1 = a.1 + b.1
      rfl
    | succ n =>
      show (0 : Int) = 0 + 0
      omega
  fbound := fun _ => 1
  fbound_spec := by
    intro a k hk
    cases k with
    | zero => exact absurd hk (by omega)
    | succ n => rfl

/-- **q9kf-1c: 実 ℚ₃^× の 3-付値データ** — 実 q3tGrp = QpUnits 3 = ℤ×ℤ₃^× の
    第 1 成分（v₃）。分岐比較（q9kf-8）で使う。 -/
def q9kfOrdQ : Nat → q3tGrp.carrier → Int
  | 0 => fun x => x.1
  | _ + 1 => fun _ => 0

/-- **q9kf-1d: 実 ℚ₃^× の付値データ**。 -/
def q9kfValQ : PicDivValuation q3tGrp where
  ord := q9kfOrdQ
  ord_mul := by
    intro k a b
    cases k with
    | zero =>
      show (q3tGrp.mul a b).1 = a.1 + b.1
      rfl
    | succ n =>
      show (0 : Int) = 0 + 0
      omega
  fbound := fun _ => 1
  fbound_spec := by
    intro a k hk
    cases k with
    | zero => exact absurd hk (by omega)
    | succ n => rfl

/-! ## q9kf-2: 実単項因子準同型と Frobenioid 次数 -/

/-- **q9kf-2a: 実単項因子準同型** div : L₂^× → Div（M307F の普遍形を実付値で実体化）。 -/
def q9kfDivL : Hom q3rqLx picDivGrp := picDivPrincipalHom q9kfValL

/-- **q9kf-2b: 実単項因子準同型** div : ℚ₃^× → Div。 -/
def q9kfDivQ : Hom q3tGrp picDivGrp := picDivPrincipalHom q9kfValQ

/-- **q9kf-2c: 実 Frobenioid 次数** deg(div(x))（M307F `picDivDegree` ∘ 実 div）。 -/
def q9kfDeg (x : q3rqLx.carrier) : Int :=
  picDivDegree.map (q9kfDivL.map x)

/-- **q9kf-2d: 実 ℚ₃^× 側の Frobenioid 次数**。 -/
def q9kfDegQ (x : q3tGrp.carrier) : Int :=
  picDivDegree.map (q9kfDivQ.map x)

/-- **q9kf-2e（★）: Frobenioid 次数 ＝ 実 λ-付値** deg(div(x)) = v_λ(x)。
    実算術（付値）と Frobenioid 形式（因子の次数）の**最初の等式**。 -/
theorem q9kf_deg_eq_val (x : q3rqLx.carrier) : q9kfDeg x = x.1 := by
  show (0 : Int) + x.1 = x.1
  omega

/-- **q9kf-2f: ℚ₃ 側の同定** deg(div(y)) = v₃(y)。 -/
theorem q9kf_degQ_eq_val (y : q3tGrp.carrier) : q9kfDegQ y = y.1 := by
  show (0 : Int) + y.1 = y.1
  omega

/-- **q9kf-2g: 次数は準同型** deg(xy) = deg x + deg y（div と deg の合成）。 -/
theorem q9kf_deg_mul (x y : q3rqLx.carrier) :
    q9kfDeg (q3rqLx.mul x y) = q9kfDeg x + q9kfDeg y := by
  rw [q9kf_deg_eq_val, q9kf_deg_eq_val, q9kf_deg_eq_val]
  rfl

/-! ## q9kf-3: べき写像 ↔ Frobenius [n]（Kummer 指数 l=3 は Frobenius [3]） -/

/-- **q9kf-3a: 実 L₂^× のべき** xⁿ。 -/
def q9kfPow (x : q3rqLx.carrier) : Nat → q3rqLx.carrier
  | 0 => q3rqLx.one
  | n + 1 => q3rqLx.mul (q9kfPow x n) x

/-- **q9kf-3b: べきの付値** v_λ(xⁿ) = n·v_λ(x)。 -/
theorem q9kf_pow_fst (x : q3rqLx.carrier) :
    ∀ n : Nat, (q9kfPow x n).1 = (n : Int) * x.1 := by
  intro n
  induction n with
  | zero =>
    show (0 : Int) = (0 : Int) * x.1
    rw [Int.zero_mul]
  | succ p ih =>
    show (q9kfPow x p).1 + x.1 = ((p + 1 : Nat) : Int) * x.1
    have hc : ((p + 1 : Nat) : Int) = (p : Int) + 1 := by omega
    rw [hc, Int.add_mul, Int.one_mul, ih]

/-- **q9kf-3c（★）: べき写像は Frobenioid の Frobenius [n]** — div(xⁿ) = [n]·div(x)。
    実 Kummer の指数 n（本コースでは l=3）が、Frobenioid の Frobenius 次数 n と
    **同一のもの**であることの実対象上の等式。 -/
theorem q9kf_div_pow (x : q3rqLx.carrier) (n : Nat) :
    q9kfDivL.map (q9kfPow x n) = (picDivFrob n).map (q9kfDivL.map x) := by
  show Quot.mk rawEq (picDivPrincipalRaw q9kfValL (q9kfPow x n))
      = Quot.mk rawEq (picDivFrobRaw n (picDivPrincipalRaw q9kfValL x))
  refine Quot.sound (fun k => ?_)
  cases k with
  | zero =>
    show (q9kfPow x n).1 = (n : Int) * x.1
    exact q9kf_pow_fst x n
  | succ p =>
    show (0 : Int) = (n : Int) * 0
    rw [Int.mul_zero]

/-- **q9kf-3d: 実立方** x³（q9cq/q9c3 と**同一の式**を主語にする）。 -/
def q9kfCube (x : q3rqLx.carrier) : q3rqLx.carrier :=
  q3rqLx.mul (q3rqLx.mul x x) x

/-- **q9kf-3e: 立方はべき 3**。 -/
theorem q9kf_cube_eq_pow (x : q3rqLx.carrier) : q9kfCube x = q9kfPow x 3 := by
  show q3rqLx.mul (q3rqLx.mul x x) x
      = q3rqLx.mul (q3rqLx.mul (q3rqLx.mul q3rqLx.one x) x) x
  rw [q3rqLx.one_mul]

/-- **q9kf-3f（★）: Kummer 立方 ＝ Frobenius [3]** — div(x³) = [3]·div(x)。 -/
theorem q9kf_div_cube (x : q3rqLx.carrier) :
    q9kfDivL.map (q9kfCube x) = (picDivFrob 3).map (q9kfDivL.map x) := by
  rw [q9kf_cube_eq_pow, q9kf_div_pow]

/-- **q9kf-3g: 立方の次数** deg(x³) = 3·deg(x)（M307F `picDiv_frob_degree` 実適用）。 -/
theorem q9kf_deg_cube (x : q3rqLx.carrier) :
    q9kfDeg (q9kfCube x) = 3 * q9kfDeg x := by
  show picDivDegree.map (q9kfDivL.map (q9kfCube x)) = 3 * picDivDegree.map (q9kfDivL.map x)
  rw [q9kf_div_cube, picDiv_frob_degree]
  rfl

/-! ## q9kf-4（★ 中核）: Frobenioid 次数 mod 3 は実 Kummer 立方類の不変量 -/

/-- **q9kf-4a: 実 Kummer 同値** — x と y が実立方剰余群 L₂^×/(L₂^×)³ の同じ類
    （y = x·g³）。 -/
def q9kfKummerRel (x y : q3rqLx.carrier) : Prop :=
  ∃ g : q3rqLx.carrier, y = q3rqLx.mul x (q9kfCube g)

/-- **q9kf-4b（★ 中核）: Kummer 類の Frobenioid 次数不変量** — 同じ実 Kummer 類の
    元は Frobenioid 次数が mod 3 で一致する。すなわち実 Kummer 側の類関数として
    「Frobenioid 次数 mod 3」が well-defined。 -/
theorem q9kf_deg_kummer_invariant {x y : q3rqLx.carrier} (h : q9kfKummerRel x y) :
    (3 : Int) ∣ (q9kfDeg y - q9kfDeg x) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨q9kfDeg g, ?_⟩
  rw [hg, q9kf_deg_mul, q9kf_deg_cube]
  omega

/-- **q9kf-4c: 明示形** — y = x·g³ ⟹ deg y = deg x + 3·deg g。 -/
theorem q9kf_deg_mod3_wd (x g : q3rqLx.carrier) :
    q9kfDeg (q3rqLx.mul x (q9kfCube g)) = q9kfDeg x + 3 * q9kfDeg g := by
  rw [q9kf_deg_mul, q9kf_deg_cube]

/-! ## q9kf-5: 次数が検出するもの・検出しないもの（実 Kummer 3 次元のうち 1 次元） -/

/-- **q9kf-5a: 一様化子クラスの次数** deg([λ]) = 1（実 λ-付値 1）。 -/
theorem q9kf_deg_lambda : q9kfDeg q9cq_lambdaClass = 1 := q9kf_deg_eq_val _

/-- **q9kf-5b: 単数クラスの次数は 0** — 実単数群 U₂ = O_{L₂}^× の元は因子次数 0
    （Frobenioid の「次数 0 部分」＝単数部）。 -/
theorem q9kf_deg_unit_zero (u : q3rqU.carrier) :
    q9kfDeg (((0 : Int), u) : q3rqLx.carrier) = 0 := q9kf_deg_eq_val _

/-- **q9kf-5c: Frobenioid 次数による [λ] 非立方性の検出** — 次数関手が
    実 Kummer 障害を計算する（**事実自体は `q9cq_lambda_nontrivial` で既証・消費**。
    新規なのは「その障害が Frobenioid 次数準同型の像である」という同定）。 -/
theorem q9kf_frobenioid_detects_lambda :
    ¬ ∃ g : q3rqLx.carrier, q9kfCube g = q9cq_lambdaClass := by
  intro hex
  obtain ⟨g, hg⟩ := hex
  have h1 : q9kfDeg (q9kfCube g) = q9kfDeg q9cq_lambdaClass := congrArg q9kfDeg hg
  rw [q9kf_deg_cube, q9kf_deg_lambda] at h1
  have key : ∀ n : Int, 3 * n = 1 → False := by intro n hn; omega
  exact key (q9kfDeg g) h1

/-- **q9kf-5d（★ 正直な鋭さ）: 次数は実 Kummer 3 次元のうち 1 次元しか見ない** —
    [λ] は次数 1 で検出されるが、[ζ₃]・[4]（q9c3 が実立方剰余群の 2・3 次元目として
    建てた実クラス）は**非立方なのに次数 0**。Frobenioid 次数関手は単数方向
    （＝Galois コホモロジー H¹ が住む方向）に**盲目**である。 -/
theorem q9kf_degree_blind_to_units :
    (q9kfDeg (((0 : Int), q9cq_zetaUnit) : q3rqLx.carrier) = 0
      ∧ ¬ ∃ g : q3rqLx.carrier, q9kfCube g = ((0 : Int), q9cq_zetaUnit))
    ∧ (q9kfDeg (((0 : Int), q9c3FourUnit) : q3rqLx.carrier) = 0
      ∧ ¬ ∃ g : q3rqLx.carrier, q9kfCube g = ((0 : Int), q9c3FourUnit)) :=
  ⟨⟨q9kf_deg_unit_zero q9cq_zetaUnit, q9c3_indep.1⟩,
   ⟨q9kf_deg_unit_zero q9c3FourUnit, q9c3_indep.2.2.1⟩⟩

/-- **q9kf-5e: 次数が検出する方向の一般形** — 3∤deg(x) なら x は非立方
    （付値方向の非立方性を Frobenioid 次数の語彙で述べたもの。事実は
    `q9cq_val_nontrivial` と同値・消費）。 -/
theorem q9kf_deg_noncube (x : q3rqLx.carrier) (h : ¬ (3 : Int) ∣ q9kfDeg x) :
    ¬ ∃ g : q3rqLx.carrier, q9kfCube g = x := by
  intro hex
  obtain ⟨g, hg⟩ := hex
  have h1 : q9kfDeg (q9kfCube g) = q9kfDeg x := congrArg q9kfDeg hg
  rw [q9kf_deg_cube] at h1
  exact h ⟨q9kfDeg g, h1.symm⟩

/-! ## q9kf-6: 実立方剰余群 L₂^×/(L₂^×)³ を literal な商群として構成 -/

/-- **q9kf-6a: L₂^× は可換**（ℤ の加法 ＋ `q3rqU_comm`）。 -/
theorem q9kf_lx_comm (x y : q3rqLx.carrier) :
    q3rqLx.mul x y = q3rqLx.mul y x := by
  have key : ∀ a b : Int, a + b = b + a := by intro a b; omega
  have h1 := key x.1 y.1
  have h2 : q3rqU.mul x.2 y.2 = q3rqU.mul y.2 x.2 := q3rqU_comm x.2 y.2
  show ((x.1 + y.1 : Int), q3rqU.mul x.2 y.2) = ((y.1 + x.1 : Int), q3rqU.mul y.2 x.2)
  rw [h1, h2]

/-- **q9kf-6b: 可換群の 4 項組み替え** (ab)(cd) = (ac)(bd)。 -/
theorem q9kf_mul4 (a b c d : q3rqLx.carrier) :
    q3rqLx.mul (q3rqLx.mul a b) (q3rqLx.mul c d)
      = q3rqLx.mul (q3rqLx.mul a c) (q3rqLx.mul b d) := by
  rw [q3rqLx.mul_assoc a b (q3rqLx.mul c d), ← q3rqLx.mul_assoc b c d,
    q9kf_lx_comm b c, q3rqLx.mul_assoc c b d,
    ← q3rqLx.mul_assoc a c (q3rqLx.mul b d)]

/-- **q9kf-6c: 立方写像は準同型**（L₂^× 可換）— (xy)³ = x³y³。 -/
theorem q9kf_cube_mul (x y : q3rqLx.carrier) :
    q9kfCube (q3rqLx.mul x y) = q3rqLx.mul (q9kfCube x) (q9kfCube y) := by
  show q3rqLx.mul (q3rqLx.mul (q3rqLx.mul x y) (q3rqLx.mul x y)) (q3rqLx.mul x y)
      = q3rqLx.mul (q3rqLx.mul (q3rqLx.mul x x) x) (q3rqLx.mul (q3rqLx.mul y y) y)
  rw [q9kf_mul4 x y x y, q9kf_mul4 (q3rqLx.mul x x) (q3rqLx.mul y y) x y]

/-- **q9kf-6d: 立方準同型** L₂^× → L₂^×。 -/
def q9kfCubeHom : Hom q3rqLx q3rqLx where
  map := q9kfCube
  map_mul := q9kf_cube_mul

/-- **q9kf-6e: 立方部分群** (L₂^×)³ ⊆ L₂^×（像部分群）。 -/
def q9kfCubeSub : Subgroup q3rqLx := imSubgroup q9kfCubeHom

/-- **q9kf-6f: 可換ゆえ正規**。 -/
theorem q9kfCubeNormal : IsNormalSubgroup q3rqLx q9kfCubeSub := by
  intro g n hn
  have hcomm : q3rqLx.mul (q3rqLx.mul g n) (q3rqLx.inv g) = n := by
    rw [q9kf_lx_comm g n, q3rqLx.mul_assoc, q3rqLx.mul_inv, q3rqLx.mul_one]
  rw [hcomm]
  exact hn

/-- **q9kf-6g（★）: 実立方剰余群** L₂^×/(L₂^×)³ を **literal な商群オブジェクト**として
    構成する（q9cq 正直限定 3「商群オブジェクトは建てない」を、q9cq を書き換えずに
    新ファイルの構成で discharge する）。 -/
def q9kfCubeQuot : Grp := quotientGroupN q3rqLx q9kfCubeSub q9kfCubeNormal

/-- **q9kf-6h: 射影** L₂^× ↠ L₂^×/(L₂^×)³。 -/
def q9kfProj : Hom q3rqLx q9kfCubeQuot :=
  quotientProjN q3rqLx q9kfCubeSub q9kfCubeNormal

/-- **q9kf-6i: 商での自明性 ⟺ 立方** — 非立方性述語（q9cq/q9c3 の ∃ 形）が
    literal 商群の非自明性として読めることの橋。 -/
theorem q9kf_class_trivial_iff (x : q3rqLx.carrier) :
    q9kfProj.map x = q9kfCubeQuot.one ↔ ∃ g : q3rqLx.carrier, q9kfCube g = x :=
  quotientProjN_ker q3rqLx q9kfCubeSub q9kfCubeNormal x

/-- **q9kf-6j: 実クラスの商群内非自明性** — [λ]・[ζ₃]・[4] は literal 商群
    L₂^×/(L₂^×)³ で非自明（非立方性 q9cq/q9c3 を商群の言葉へ昇格）。 -/
theorem q9kf_classes_nontrivial_in_quot :
    q9kfProj.map q9cq_lambdaClass ≠ q9kfCubeQuot.one
    ∧ q9kfProj.map (((0 : Int), q9cq_zetaUnit) : q3rqLx.carrier) ≠ q9kfCubeQuot.one
    ∧ q9kfProj.map (((0 : Int), q9c3FourUnit) : q3rqLx.carrier) ≠ q9kfCubeQuot.one := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact q9kf_frobenioid_detects_lambda ((q9kf_class_trivial_iff _).mp h)
  · intro h
    exact q9c3_indep.1 ((q9kf_class_trivial_iff _).mp h)
  · intro h
    exact q9c3_indep.2.2.1 ((q9kf_class_trivial_iff _).mp h)

/-! ## q9kf-7（★）: 実 Kummer 群 → ℤ/3 の Frobenioid 次数準同型 -/

/-- **q9kf-7a: 3 倍準同型** ℤ → ℤ。 -/
def q9kfTripleHom : Hom intGrp intGrp where
  map := fun n => 3 * n
  map_mul := by
    intro a b
    show (3 : Int) * (a + b) = 3 * a + 3 * b
    omega

/-- **q9kf-7b: 部分群 3ℤ ⊆ ℤ**。 -/
def q9kfThreeSub : Subgroup intGrp := imSubgroup q9kfTripleHom

/-- **q9kf-7c: 3ℤ は正規**（ℤ は可換）。 -/
theorem q9kfThreeNormal : IsNormalSubgroup intGrp q9kfThreeSub := by
  intro g n hn
  have key : ∀ a b : Int, a + b + -a = b := by intro a b; omega
  have hcomm : intGrp.mul (intGrp.mul g n) (intGrp.inv g) = n := key g n
  rw [hcomm]
  exact hn

/-- **q9kf-7d: ℤ/3 を literal な商群として**（Kummer 指数 l=3 の係数群）。 -/
def q9kfZ3 : Grp := quotientGroupN intGrp q9kfThreeSub q9kfThreeNormal

/-- **q9kf-7e: 射影** ℤ ↠ ℤ/3。 -/
def q9kfZ3Proj : Hom intGrp q9kfZ3 :=
  quotientProjN intGrp q9kfThreeSub q9kfThreeNormal

/-- **q9kf-7f: 3 の倍数は ℤ/3 で自明**。 -/
theorem q9kf_z3_triple (k : Int) : q9kfZ3Proj.map (3 * k) = q9kfZ3.one :=
  (quotientProjN_ker intGrp q9kfThreeSub q9kfThreeNormal (3 * k)).mpr ⟨k, rfl⟩

/-- **q9kf-7g: 逆元の次数** deg(x⁻¹) = −deg(x)。 -/
theorem q9kf_deg_inv (x : q3rqLx.carrier) :
    q9kfDeg (q3rqLx.inv x) = - q9kfDeg x := by
  rw [q9kf_deg_eq_val, q9kf_deg_eq_val]
  rfl

/-- **q9kf-7h: 次数の mod 3 還元準同型** L₂^× → ℤ/3。 -/
def q9kfDegZ3 : Hom q3rqLx q9kfZ3 where
  map := fun x => q9kfZ3Proj.map (q9kfDeg x)
  map_mul := by
    intro a b
    show q9kfZ3Proj.map (q9kfDeg (q3rqLx.mul a b))
        = q9kfZ3.mul (q9kfZ3Proj.map (q9kfDeg a)) (q9kfZ3Proj.map (q9kfDeg b))
    rw [q9kf_deg_mul]
    exact q9kfZ3Proj.map_mul (q9kfDeg a) (q9kfDeg b)

/-- **q9kf-7i（★ 中核）: 実 Kummer 群 L₂^×/(L₂^×)³ 上の Frobenioid 次数準同型** —
    因子次数 deg が実立方剰余群から ℤ/3 への**本物の群準同型**を誘導する
    （well-defined 性は q9kf-4 の Kummer 不変性そのもの）。C6「実 Kummer–Frobenioid
    両立」の中核等式: **Kummer 類 ↦ Frobenioid 次数（mod l）** が well-defined。 -/
def q9kfDegClass : Hom q9kfCubeQuot q9kfZ3 where
  map := Quot.lift (fun x => q9kfDegZ3.map x) (by
    intro a b hab
    obtain ⟨g, hg⟩ := hab
    have hg2 : q9kfCube g = q3rqLx.mul (q3rqLx.inv a) b := hg
    have hdiff : q9kfDeg (q3rqLx.mul (q3rqLx.inv a) b) = 3 * q9kfDeg g := by
      rw [← hg2, q9kf_deg_cube]
    rw [q9kf_deg_mul, q9kf_deg_inv] at hdiff
    have hb : q9kfDeg b = q9kfDeg a + 3 * q9kfDeg g := by omega
    show q9kfZ3Proj.map (q9kfDeg a) = q9kfZ3Proj.map (q9kfDeg b)
    rw [hb]
    have hsplit : q9kfZ3Proj.map (q9kfDeg a + 3 * q9kfDeg g)
        = q9kfZ3.mul (q9kfZ3Proj.map (q9kfDeg a)) (q9kfZ3Proj.map (3 * q9kfDeg g)) :=
      q9kfZ3Proj.map_mul (q9kfDeg a) (3 * q9kfDeg g)
    rw [hsplit, q9kf_z3_triple, q9kfZ3.mul_one])
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show q9kfDegZ3.map (q3rqLx.mul a b)
        = q9kfZ3.mul (q9kfDegZ3.map a) (q9kfDegZ3.map b)
    exact q9kfDegZ3.map_mul a b

/-- **q9kf-7j: 誘導則** — 射影と次数の可換性（Kummer 類の次数は代表の次数）。 -/
theorem q9kf_degClass_proj (x : q3rqLx.carrier) :
    q9kfDegClass.map (q9kfProj.map x) = q9kfZ3Proj.map (q9kfDeg x) := rfl

/-- **q9kf-7k: 次数準同型は全射** — 実 Kummer 群から ℤ/3 への次数写像は onto
    （一様化子べき類が生成元を与える＝Frobenioid 次数が Kummer 群の付値次元を
    ちょうど 1 次元分検出する）。 -/
theorem q9kf_degClass_surjective :
    ∀ z : q9kfZ3.carrier, ∃ c : q9kfCubeQuot.carrier, q9kfDegClass.map c = z := by
  intro z
  induction z using Quot.ind; rename_i n
  refine ⟨q9kfProj.map ((n, q3rqU.one) : q3rqLx.carrier), ?_⟩
  show q9kfZ3Proj.map (q9kfDeg ((n, q3rqU.one) : q3rqLx.carrier)) = _
  rw [q9kf_deg_eq_val]
  rfl

/-- **q9kf-7l: [λ] は生成元へ**（次数 1 は ℤ/3 で非自明）。 -/
theorem q9kf_degClass_lambda_ne_one :
    q9kfDegClass.map (q9kfProj.map q9cq_lambdaClass) ≠ q9kfZ3.one := by
  intro h
  have h1 : q9kfZ3Proj.map (q9kfDeg q9cq_lambdaClass) = q9kfZ3.one := h
  rw [q9kf_deg_lambda] at h1
  obtain ⟨m, hm⟩ :=
    (quotientProjN_ker intGrp q9kfThreeSub q9kfThreeNormal (1 : Int)).mp h1
  have key : ∀ a : Int, 3 * a = 1 → False := by intro a ha; omega
  exact key m hm

/-- **q9kf-7m: 単数クラスは核へ** — [ζ₃]・[4] は非自明な実 Kummer 類でありながら
    Frobenioid 次数準同型の**核**に入る（次数 0）。 -/
theorem q9kf_degClass_units_one :
    q9kfDegClass.map (q9kfProj.map (((0 : Int), q9cq_zetaUnit) : q3rqLx.carrier))
        = q9kfZ3.one
    ∧ q9kfDegClass.map (q9kfProj.map (((0 : Int), q9c3FourUnit) : q3rqLx.carrier))
        = q9kfZ3.one := by
  constructor
  · show q9kfZ3Proj.map (q9kfDeg (((0 : Int), q9cq_zetaUnit) : q3rqLx.carrier))
        = q9kfZ3.one
    rw [q9kf_deg_unit_zero]
    exact q9kfZ3Proj.map_one
  · show q9kfZ3Proj.map (q9kfDeg (((0 : Int), q9c3FourUnit) : q3rqLx.carrier))
        = q9kfZ3.one
    rw [q9kf_deg_unit_zero]
    exact q9kfZ3Proj.map_one

/-- **q9kf-7n（★ 正直な鋭さ・capstone）: 次数準同型は全射だが核は非自明** —
    実 Kummer 群 L₂^×/(L₂^×)³（既知 rank≥3）のうち Frobenioid 次数が見るのは
    ちょうど 1 次元（付値方向）であり、[ζ₃]・[4] の 2 次元は核に落ちる。
    これは C6 の両立が**成り立つ範囲と成り立たない範囲**を同時に確定する。 -/
theorem q9kf_degree_kummer_compatibility :
    (∀ z : q9kfZ3.carrier, ∃ c : q9kfCubeQuot.carrier, q9kfDegClass.map c = z)
    ∧ (q9kfDegClass.map (q9kfProj.map q9cq_lambdaClass) ≠ q9kfZ3.one)
    ∧ (q9kfProj.map (((0 : Int), q9cq_zetaUnit) : q3rqLx.carrier) ≠ q9kfCubeQuot.one
       ∧ q9kfDegClass.map (q9kfProj.map (((0 : Int), q9cq_zetaUnit) : q3rqLx.carrier))
           = q9kfZ3.one)
    ∧ (q9kfProj.map (((0 : Int), q9c3FourUnit) : q3rqLx.carrier) ≠ q9kfCubeQuot.one
       ∧ q9kfDegClass.map (q9kfProj.map (((0 : Int), q9c3FourUnit) : q3rqLx.carrier))
           = q9kfZ3.one) :=
  ⟨q9kf_degClass_surjective, q9kf_degClass_lambda_ne_one,
   ⟨q9kf_classes_nontrivial_in_quot.2.1, q9kf_degClass_units_one.1⟩,
   ⟨q9kf_classes_nontrivial_in_quot.2.2, q9kf_degClass_units_one.2⟩⟩

/-! ## q9kf-8: 実算術から来る Frobenioid 射（M331F `frobCHom` の実インスタンス） -/

/-- **q9kf-8a（★）: Kummer 立方射** div(x) → div(x³) — Frobenius 次数 3・有効部 0 の
    実 Frobenioid 射。**Kummer 指数 l=3 ＝ Frobenioid の Frobenius 次数**。 -/
def q9kfCubeMor (x : q3rqLx.carrier) :
    frobCHom (q9kfDivL.map x) (q9kfDivL.map (q9kfCube x)) where
  deg := 3
  deg_pos := by omega
  eff := picDivGrp.one
  eff_effective := frobCEffective_one
  linear := by
    rw [picDivGrp.mul_one]
    exact q9kf_div_cube x

/-- **q9kf-8b: 立方射の次数は 3**。 -/
theorem q9kf_cubeMor_deg (x : q3rqLx.carrier) : (q9kfCubeMor x).deg = 3 := rfl

/-- **q9kf-8c（★）: 実分岐 ℚ₃^× ↪ L₂^× は Frobenius [2]** — div_L(ι y) = [2]·div_{ℚ₃}(y)。
    実分岐指数 e=2（`q3rq_ramification`）が Frobenioid の Frobenius 次数として現れる。 -/
theorem q9kf_div_embed (y : q3tGrp.carrier) :
    q9kfDivL.map (q3rqEmbed.map y) = (picDivFrob 2).map (q9kfDivQ.map y) := by
  show Quot.mk rawEq (picDivPrincipalRaw q9kfValL (q3rqEmbed.map y))
      = Quot.mk rawEq (picDivFrobRaw 2 (picDivPrincipalRaw q9kfValQ y))
  refine Quot.sound (fun k => ?_)
  cases k with
  | zero =>
    show (q3rqEmbed.map y).1 = (2 : Int) * y.1
    exact q3rq_ramification y
  | succ p =>
    show (0 : Int) = (2 : Int) * 0
    rw [Int.mul_zero]

/-- **q9kf-8d: 分岐次数則** deg_L(ι y) = 2·deg_{ℚ₃}(y)（e=2 の次数版）。 -/
theorem q9kf_deg_embed (y : q3tGrp.carrier) :
    q9kfDeg (q3rqEmbed.map y) = 2 * q9kfDegQ y := by
  show picDivDegree.map (q9kfDivL.map (q3rqEmbed.map y))
      = 2 * picDivDegree.map (q9kfDivQ.map y)
  rw [q9kf_div_embed, picDiv_frob_degree]
  rfl

/-- **q9kf-8e（★）: 分岐射** div_{ℚ₃}(y) → div_L(ι y) — Frobenius 次数 2（＝実分岐指数
    e）・有効部 0 の実 Frobenioid 射。 -/
def q9kfRamMor (y : q3tGrp.carrier) :
    frobCHom (q9kfDivQ.map y) (q9kfDivL.map (q3rqEmbed.map y)) where
  deg := 2
  deg_pos := by omega
  eff := picDivGrp.one
  eff_effective := frobCEffective_one
  linear := by
    rw [picDivGrp.mul_one]
    exact q9kf_div_embed y

/-- **q9kf-8f: 分岐射の次数は 2 ＝ e**。 -/
theorem q9kf_ram_degree_two (y : q3tGrp.carrier) : (q9kfRamMor y).deg = 2 := rfl

/-- **q9kf-8g（★）: 合成射 ℚ₃^× → L₂^× → 立方** の Frobenius 次数は 6 = e·l
    （M331F の次数関手の乗法性 `frobC_degree_mult` の**実算術インスタンス**——
    分岐指数 2 と Kummer 指数 3 が Frobenioid の次数として掛かる）。 -/
theorem q9kf_comp_degree_six (y : q3tGrp.carrier) :
    (frobCComp (q9kfRamMor y) (q9kfCubeMor (q3rqEmbed.map y))).deg = 6 := rfl

/-- **q9kf-8h: 次数関手の乗法性の実適用** deg(g∘f) = deg f · deg g。 -/
theorem q9kf_comp_degree_mult (y : q3tGrp.carrier) :
    (frobCComp (q9kfRamMor y) (q9kfCubeMor (q3rqEmbed.map y))).deg
      = (q9kfRamMor y).deg * (q9kfCubeMor (q3rqEmbed.map y)).deg :=
  frobC_degree_mult (q9kfRamMor y) (q9kfCubeMor (q3rqEmbed.map y))

/-! ## q9kf-9: 素点簿記の忠実性診断（★ Frobenioid 層への正直な指摘を**定理で**与える） -/

/-- **q9kf-9a: 素点での係数評価** Div → ℤ（第 k 素点の重複度）。M307F は次数（総和）
    しか持たなかったので、素点ごとの評価準同型をここで建てる。 -/
def q9kfCoeff (k : Nat) : Hom picDivGrp intGrp where
  map := Quot.lift (fun a => a.coeff k) (fun _ _ h => h k)
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show a.coeff k + b.coeff k = a.coeff k + b.coeff k
    rfl

/-- **q9kf-9b: 第 1 素点の因子** [P₁]（M307F の ℕ 添字素点のうち 2 番目）。 -/
def q9kfP1Raw : RawDiv where
  coeff := fun k =>
    match k with
    | 0 => 0
    | 1 => 1
    | _ + 2 => 0
  bound := 2
  vanish := by
    intro k hk
    cases k with
    | zero => exact absurd hk (by omega)
    | succ p =>
      cases p with
      | zero => exact absurd hk (by omega)
      | succ q => rfl

/-- **q9kf-9c: 第 0 素点方向では div は全射** — 実 λ-付値は ℤ 全体を取る
    （実算術部分は忠実）。 -/
theorem q9kf_place0_surjective (n : Int) :
    (q9kfCoeff 0).map (q9kfDivL.map ((n, q3rqU.one) : q3rqLx.carrier)) = n := rfl

/-- **q9kf-9d（★ 診断）: [P₁] は単項でない** — M307F の ℕ 添字素点のうち、実 L₂ に
    対応しない「幽霊素点」が Pic を非自明にする。**局所体 L₂ の真の Picard 群は 0**
    （離散付値環は PID）であるから、これは M307F の素点簿記が Spec O_{L₂} を
    忠実に表していないことの**証明された証拠**である。C6 の完成には素点集合を
    実 Spec（あるいは実大域体の素点族）として実体化する必要がある。 -/
theorem q9kf_place1_not_principal :
    ¬ ∃ x : q3rqLx.carrier, q9kfDivL.map x = Quot.mk rawEq q9kfP1Raw := by
  intro hex
  obtain ⟨x, hx⟩ := hex
  have h1 : (q9kfCoeff 1).map (q9kfDivL.map x)
      = (q9kfCoeff 1).map (Quot.mk rawEq q9kfP1Raw) := congrArg (q9kfCoeff 1).map hx
  have h2 : (0 : Int) = 1 := h1
  exact absurd h2 (by omega)

/-- **q9kf-9e（★ 診断・帰結）: 実付値データに対する M307F の Pic は非自明** —
    すなわち Frobenioid の因子層は現状「実 Spec の素点」ではなく抽象添字で動いている。
    （§正直な限定 1 の named gap を定理として固定する。） -/
theorem q9kf_pic_bookkeeping_artifact :
    ∃ D : picDivGrp.carrier, ¬ ∃ x : q3rqLx.carrier, q9kfDivL.map x = D :=
  ⟨Quot.mk rawEq q9kfP1Raw, q9kf_place1_not_principal⟩

/-! ## q9kf-10: capstone（データ束ね・新規証明ゼロ） -/

/-- **q9kf-9a: 実 Kummer–Frobenioid 両立データ**（C6）。 -/
structure Q3KummerFrobenioidData where
  /-- Frobenioid 次数 ＝ 実 λ-付値（実算術の注入）。 -/
  deg_eq_val : ∀ x : q3rqLx.carrier, q9kfDeg x = x.1
  /-- Kummer べき ＝ Frobenius [n]。 -/
  div_pow : ∀ (x : q3rqLx.carrier) (n : Nat),
    q9kfDivL.map (q9kfPow x n) = (picDivFrob n).map (q9kfDivL.map x)
  /-- Frobenioid 次数 mod 3 は実 Kummer 類の不変量。 -/
  kummer_invariant : ∀ {x y : q3rqLx.carrier}, q9kfKummerRel x y →
    (3 : Int) ∣ (q9kfDeg y - q9kfDeg x)
  /-- 実立方剰余群からの次数準同型は全射。 -/
  degClass_surj : ∀ z : q9kfZ3.carrier,
    ∃ c : q9kfCubeQuot.carrier, q9kfDegClass.map c = z
  /-- [λ] は次数準同型で非自明（付値次元を検出）。 -/
  lambda_detected : q9kfDegClass.map (q9kfProj.map q9cq_lambdaClass) ≠ q9kfZ3.one
  /-- [ζ₃] は商群で非自明だが次数準同型の核（単数次元は不可視）。 -/
  zeta_blind :
    q9kfProj.map (((0 : Int), q9cq_zetaUnit) : q3rqLx.carrier) ≠ q9kfCubeQuot.one
    ∧ q9kfDegClass.map (q9kfProj.map (((0 : Int), q9cq_zetaUnit) : q3rqLx.carrier))
        = q9kfZ3.one
  /-- 実分岐 e=2 は Frobenius [2]。 -/
  ram_frob : ∀ y : q3tGrp.carrier,
    q9kfDivL.map (q3rqEmbed.map y) = (picDivFrob 2).map (q9kfDivQ.map y)
  /-- 合成 Frobenioid 射の次数は e·l = 6。 -/
  comp_deg : ∀ y : q3tGrp.carrier,
    (frobCComp (q9kfRamMor y) (q9kfCubeMor (q3rqEmbed.map y))).deg = 6
  /-- 診断: M307F の素点簿記は実 Spec O_{L₂} を忠実に表していない（幽霊素点）。 -/
  bookkeeping_artifact :
    ∃ D : picDivGrp.carrier, ¬ ∃ x : q3rqLx.carrier, q9kfDivL.map x = D

/-- **q9kf-9b: 見出し実例** — 実 L₂ = ℚ₃(ζ₃) の Kummer 立方剰余と実 Frobenioid
    因子次数の両立。 -/
def q9kf_data : Q3KummerFrobenioidData where
  deg_eq_val := q9kf_deg_eq_val
  div_pow := q9kf_div_pow
  kummer_invariant := q9kf_deg_kummer_invariant
  degClass_surj := q9kf_degClass_surjective
  lambda_detected := q9kf_degClass_lambda_ne_one
  zeta_blind := ⟨q9kf_classes_nontrivial_in_quot.2.1, q9kf_degClass_units_one.1⟩
  ram_frob := q9kf_div_embed
  comp_deg := q9kf_comp_degree_six
  bookkeeping_artifact := q9kf_pic_bookkeeping_artifact

/-- **q9kf-9c: 存在**。 -/
theorem q9kf_exists : Nonempty Q3KummerFrobenioidData := ⟨q9kf_data⟩

end IUT
