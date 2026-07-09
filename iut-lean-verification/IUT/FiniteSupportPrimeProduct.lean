/-
  IUT/FiniteSupportPrimeProduct.lean — B5 積公式スライス:
  「素数リスト上の有限台積の機構」

  ── 主要成果の分類: **[実]**（本物の有理数体 QRat = Quot ratRel の乗法
     `ratRing.mul` 上で組む、純粋に組合せ論的な実補題群。toy 模型・代理・
     surrogate は一切用いない）。

  complete_pct 影響: **未設定（承認済み足場 (c)）**。積公式
  ∏_{p∈S} |x|_p の「有限積」＝台の外では |x|_p = 1 で自明に落ちる、という
  B5（積公式）の**有限性の核**を、実 QRat 値の可換環積として実装する足場。
  本ファイル単独では complete_pct を動かさない（付値 |·|_p 本体・大域積公式
  ∏_p |x|_p = 1 との接続は上位スライスで行う）。ここは付値項を抽象化した
  関数 f : Nat → QRat 上の**組合せ論的機構のみ**を本物に確定する。

  * B5-fsp-1 `fspProd`               — 素数リスト上の有限積（ratRing.mul 畳み込み）
  * B5-fsp-2 `fsp_prod_singleton`    — 単元リストの積 = f p
  * B5-fsp-3 `fsp_prod_append`       — 連結の積 = 積の積（mul_assoc / one_mul）
  * B5-fsp-4 `fsp_prod_mul_pointwise`— 点毎積の積 = 積の積（可換環の並べ替え）
  * B5-fsp-5 `fsp_prod_trivial_on`   — 台の外（f≡1）では積 = 1
  * B5-fsp-6 `fsp_prod_extend`       — **本丸**: f が 1 の素数を足しても積は不変

  正直な限定（何が本物で何が未達か）:
  - **本物**: 上記の全定理は QRat = Quot ratRel の本物の乗法
    `ratRing.mul`（M115F の可換環 `ratRing` の `mul_assoc`/`one_mul`/
    `mul_comm`）の上で完全証明（sorry 皆無・新規 Classical.choice 皆無）。
    値は代理値ではなく本物の有理数。
  - **未達（正直申告）**: f は「素数 p での付値項 |x|_p」を抽象化した一般の
    関数であり、付値 |·|_p 本体・素数性・大域積公式 ∏_p |x|_p = 1 は
    本ファイルの対象外（上位スライスで本物化して接続する）。ここが確定するのは
    「有限積の代数的機構」と「台の外は 1 で落ちる」有限性の核のみ。
  - リストは重複・順序を許すマルチ集合的な扱い（∏ は積なので重複は積に効く）。
    `fsp_prod_extend` は「f p = 1 な p だけを追加」する不変性で、これが
    積公式の有限台性の本質（対象素点の外は寄与 1）。

  全て選択公理不使用（新規 choice を証明本体に導入しない）。
  #print axioms は [propext, Quot.sound] のみ。
-/
import IUT.Rationals

namespace IUT

/-! ## 補助: ratRing の右単位律（mul_one） -/

/-- ratRing は右単位律 `a·1 = a` を持つ（可換性 + 左単位律から導出）。 -/
theorem fsp_rat_mul_one (a : QRat) : ratRing.mul a ratRing.one = a := by
  rw [ratRing.mul_comm, ratRing.one_mul]

/-- ratRing の (a·b)·(c·d) = (a·c)·(b·d)（可換環の並べ替え）。 -/
theorem fsp_rat_mul_mul_mul_comm (a b c d : QRat) :
    ratRing.mul (ratRing.mul a b) (ratRing.mul c d)
      = ratRing.mul (ratRing.mul a c) (ratRing.mul b d) := by
  rw [ratRing.mul_assoc a b (ratRing.mul c d),
    ← ratRing.mul_assoc b c d,
    ratRing.mul_comm b c,
    ratRing.mul_assoc c b d,
    ← ratRing.mul_assoc a c (ratRing.mul b d)]

/-! ## B5-fsp-1: 素数リスト上の有限積 -/

/-- **B5-fsp-1: 有限台積** — 素数リスト `S` 上で f の値を `ratRing.mul` で
    畳み込む。空リストは単位元 `ratRing.one`。積公式 ∏_{p∈S} f(p) の実装。 -/
def fspProd (f : Nat → QRat) : List Nat → QRat
  | [] => ratRing.one
  | p :: rest => ratRing.mul (f p) (fspProd f rest)

/-! ## B5-fsp-2: 単元リスト -/

/-- **B5-fsp-2: 単元リストの積** — `∏_{p∈[p]} f(p) = f p`。 -/
theorem fsp_prod_singleton (f : Nat → QRat) (p : Nat) :
    fspProd f [p] = f p := by
  show ratRing.mul (f p) (fspProd f []) = f p
  show ratRing.mul (f p) ratRing.one = f p
  rw [fsp_rat_mul_one]

/-! ## B5-fsp-3: 連結の積 -/

/-- **B5-fsp-3: 連結の積 = 積の積** — `∏_{S++T} = (∏_S)·(∏_T)`。 -/
theorem fsp_prod_append (f : Nat → QRat) (S T : List Nat) :
    fspProd f (S ++ T) = ratRing.mul (fspProd f S) (fspProd f T) := by
  induction S with
  | nil =>
    show fspProd f T = ratRing.mul ratRing.one (fspProd f T)
    rw [ratRing.one_mul]
  | cons p rest ih =>
    show ratRing.mul (f p) (fspProd f (rest ++ T))
       = ratRing.mul (ratRing.mul (f p) (fspProd f rest)) (fspProd f T)
    rw [ih, ratRing.mul_assoc]

/-! ## B5-fsp-4: 点毎積の積 -/

/-- **B5-fsp-4: 点毎積の積 = 積の積** — `∏_S (f·g) = (∏_S f)·(∏_S g)`。
    可換環の並べ替え（fsp_rat_mul_mul_mul_comm）で示す。 -/
theorem fsp_prod_mul_pointwise (f g : Nat → QRat) (S : List Nat) :
    fspProd (fun p => ratRing.mul (f p) (g p)) S
      = ratRing.mul (fspProd f S) (fspProd g S) := by
  induction S with
  | nil =>
    show ratRing.one = ratRing.mul ratRing.one ratRing.one
    rw [ratRing.one_mul]
  | cons p rest ih =>
    show ratRing.mul (ratRing.mul (f p) (g p))
           (fspProd (fun q => ratRing.mul (f q) (g q)) rest)
       = ratRing.mul (ratRing.mul (f p) (fspProd f rest))
           (ratRing.mul (g p) (fspProd g rest))
    rw [ih, fsp_rat_mul_mul_mul_comm]

/-! ## B5-fsp-5: 台の外では積 = 1 -/

/-- **B5-fsp-5: 台の外では積 = 1** — `T` 上で f が恒等的に 1 なら
    `∏_{p∈T} f(p) = 1`。積公式の有限台性の核。 -/
theorem fsp_prod_trivial_on (f : Nat → QRat) (T : List Nat)
    (hT : ∀ p ∈ T, f p = ratRing.one) : fspProd f T = ratRing.one := by
  induction T with
  | nil =>
    show ratRing.one = ratRing.one
    rfl
  | cons p rest ih =>
    show ratRing.mul (f p) (fspProd f rest) = ratRing.one
    have hp : f p = ratRing.one := hT p (List.Mem.head rest)
    have hrest : ∀ q ∈ rest, f q = ratRing.one := by
      intro q hq
      exact hT q (List.Mem.tail p hq)
    rw [hp, ratRing.one_mul, ih hrest]

/-! ## B5-fsp-6: 本丸 — support 拡大不変 -/

/-- **B5-fsp-6（本丸）: support 拡大不変** — f が 1 をとる素数 `T` を
    足しても積は不変: `∏_{S++T} f = ∏_S f`（`hT: ∀ p∈T, f p = 1`）。
    積公式 ∏_p |x|_p の有限性＝台の外は |x|_p = 1 で落ちる、の核。 -/
theorem fsp_prod_extend (f : Nat → QRat) (S T : List Nat)
    (hT : ∀ p ∈ T, f p = ratRing.one) :
    fspProd f (S ++ T) = fspProd f S := by
  rw [fsp_prod_append, fsp_prod_trivial_on f T hT, fsp_rat_mul_one]

/-! ## 系: f ≡ 1 なら任意リスト上で積 = 1 -/

/-- **系: f ≡ 1 なら積 = 1** — 全域で f = 1 なら任意の `S` で `∏_S f = 1`。 -/
theorem fsp_prod_one (f : Nat → QRat) (S : List Nat)
    (hf : ∀ p, f p = ratRing.one) : fspProd f S = ratRing.one := by
  apply fsp_prod_trivial_on
  intro p _
  exact hf p

end IUT
