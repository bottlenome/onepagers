/-
  IUT/MinimalPolynomial.lean — M273F: 代数的元と最小多項式
  ── 柱A 実 Galois 理論の本物の先行建設

  分類 **[実]**（本物の体拡大・Galois 理論の先行建設。骨格でなく本物）。

  **complete_pct 影響: 柱A 実 Galois 理論の本物の先行建設
  （代数的元・最小多項式・既約性・核 = (最小多項式)）**。遠アーベル復元・
  Gal(L/K) の実理論は「基礎体 K 上の代数的元 α とその最小多項式」を
  基礎語彙とする。既存資産では体の除法定理（M268F `field_division_exists`）・
  体の整域性（M268F-2 `mul_eq_zero_left268`）・体上多項式評価準同型の
  素材は揃っていたが、**最小多項式そのもの（存在・一意性・既約性・
  核の生成）は 0 ファイル**であった。本モジュールがそれを core Lean のみで
  本物に構成する。

  * M273F-1 `PolyEval`      — 評価準同型 K[X] → E（α ∈ E での評価。
    K・E は体 `Field268`、ev は加法・乗法・零を保つ）。`polyEval_neg` /
    `polyEval_sub_vanish` / `PolyDvd` / `polyEval_vanish_of_dvd`。
  * M273F-2 `IsAlgebraic`   — α が K 上代数的 ⟺ ∃ 非零 f∈K[X], f(α)=0。
  * M273F-3 `psMul_const_coeff` / `minPoly_normalize` — 定数倍の係数公式と
    **モニック化**（先頭係数の逆元を掛けて先頭 = 1、体固有の実構成）。
  * M273F-4 `MinPolyData`   — 最小多項式データ（モニック・有界・零・
    最小次数性を束ねる）。`minPoly_nonzero_eval`（最小性の対偶：次数 < d の
    非零多項式は α で消えない）・`minPolyData_isAlgebraic`。
  * M273F-5 `minPoly_unique`     — **一意性**：同次数モニックで α を消す
    多項式は最小多項式に一致（差が次数 < d で零 → 最小性で相等）。
  * M273F-6 `minPoly_irreducible` — **既約性**：m = g·h（deg g,h < d、g,h≠0）
    は不可能（最小性の対偶で ev g ≠ 0・ev h ≠ 0、E の整域性で ev g·ev h ≠ 0、
    しかし = ev m = 0 で矛盾）。**選言に依らず**構成的。
  * M273F-7 `minPoly_dvd_of_vanish` / `minPoly_vanish_of_dvd` / `minPoly_ker`
    — **核 = (最小多項式)**：f(α)=0 ⟺ m ∣ f。前向きは**体上除法**
    （M268F）で剰余 r（deg r < d）を取り、ev r = 0・最小性で r = 0 → m ∣ f
    （**除法定理の本丸の応用**）。後向きは ev の乗法性。
  * M273F-8 `minPolyData_of_witness` / `MinPolyResult` / `minPoly_result` /
    `minPoly_exists` — capstone（最小次数 witness からの最小多項式構成と、
    一意性・既約性・核生成の総括）。

  意義: K(α) ≅ K[X]/(m)（m 最小多項式）の代数的骨組み。最小多項式の
  一意・既約・核生成は分離性・Galois 理論・遠アーベル復元の代数的基盤。

  正直な限定（何が本物で何が honest 仮説か）:
   - **本物**: `PolyEval`（体上多項式評価準同型）を仮説として持つとき、
     最小多項式の一意性・既約性・核 = (m)・モニック化は完全証明
     （sorry 皆無・新規 Classical.choice 皆無・禁止タクティク不使用）。
     一意性は「差の次数降下 + 最小性」、既約性は「最小性の対偶 + E の
     整域性」、核生成は「体上除法（M268F）+ 最小性」で閉じる。
   - **honest 仮説 1（評価準同型の抽象化）**: 評価 ev : K[X] → E は
     ring 準同型（加法・乗法・零を保つ）を**仮説**として受け取る。埋め込み
     ι : K → E と α ∈ E から ev を構成する（Cauchy 積が準同型である
     ことの証明 = 別層）は本モジュールに含めない。ev は本物の評価が
     満たす defining property そのものであり toy 主語ではない。
   - **honest 仮説 2（存在 = 最小次数 witness）**: 「α 代数的 ⟹ 最小多項式が
     存在」の完全形は「α を消す非零多項式のうち次数最小のもの」の抽出＝
     ℕ の整列性を要するが、抽象体 E 上で「多項式が α で消えるか」は
     一般に非可述（decidable でない）ため、新規 Classical.choice を証明
     本体に入れずには最小次数元を選べない。よって本モジュールは
     **最小次数 witness（f・次数 d・最小性）を入力**として受け取り
     （`minPoly_exists`）、そこからモニック化して `MinPolyData` を構成し、
     一意・既約・核生成を導く。この最小次数 witness は代数的元に対し
     数学的には存在する（honest 申告）。
   - K(α) ≅ K[X]/(m) の同型構成そのもの（商環の実装）は本層の範囲外。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyFieldDivision

namespace IUT

/-! ## M273F-1: 評価準同型 K[X] → E -/

/-- **M273F-1a: 多項式評価準同型** — 体 `K` 上の多項式環 `K[X] = PS K.ring`
    から体 `E` への環準同型 `ev`（α ∈ E での評価の抽象化）。加法・乗法・
    零を保つ性質を仮説として持つ（本物の評価が満たす defining property）。 -/
structure PolyEval where
  /-- 基礎体 K。 -/
  K : Field268
  /-- 拡大体 E（α の住む体、整域性を提供）。 -/
  E : Field268
  /-- 評価写像 K[X] → E。 -/
  ev : PS K.ring → E.ring.carrier
  /-- 加法を保つ。 -/
  ev_add : ∀ f g, ev (psAdd K.ring f g) = E.ring.add (ev f) (ev g)
  /-- 乗法を保つ。 -/
  ev_mul : ∀ f g, ev (psMul K.ring f g) = E.ring.mul (ev f) (ev g)
  /-- 零多項式は 0 に写る。 -/
  ev_zero : ev (psZero K.ring) = E.ring.zero

/-- **M273F-1b: 評価は符号を保つ** — ev(−f) = −ev(f)
    （ev(f + (−f)) = ev(0) = 0 から）。 -/
theorem polyEval_neg (P : PolyEval) (f : PS P.K.ring) :
    P.ev (psNeg P.K.ring f) = P.E.ring.neg (P.ev f) := by
  have hz : psAdd P.K.ring f (psNeg P.K.ring f) = psZero P.K.ring := by
    funext n
    exact CRing.add_neg P.K.ring (f n)
  have h1 : P.E.ring.add (P.ev f) (P.ev (psNeg P.K.ring f)) = P.E.ring.zero := by
    rw [← P.ev_add f (psNeg P.K.ring f), hz, P.ev_zero]
  exact (CRing.neg_eq_of_add_eq_zero P.E.ring h1).symm

/-- **M273F-1c: 差の消滅** — f(α) = 0 かつ g(α) = 0 なら (f − g)(α) = 0。 -/
theorem polyEval_sub_vanish (P : PolyEval) (f g : PS P.K.ring)
    (hf : P.ev f = P.E.ring.zero) (hg : P.ev g = P.E.ring.zero) :
    P.ev (psAdd P.K.ring f (psNeg P.K.ring g)) = P.E.ring.zero := by
  rw [P.ev_add f (psNeg P.K.ring g), polyEval_neg P g, hf, hg,
    CRing.neg_zero P.E.ring, P.E.ring.zero_add]

/-- **M273F-1d: 整除** — m ∣ f、すなわち ∃ q, f = q·m（係数ごと）。 -/
def PolyDvd (R : CRing) (m f : PS R) : Prop :=
  ∃ q, ∀ j, f j = psMul R q m j

/-- **M273F-1e: 整除は消滅を保つ** — m(α) = 0 かつ m ∣ f なら f(α) = 0
    （ev の乗法性）。 -/
theorem polyEval_vanish_of_dvd (P : PolyEval) (m f : PS P.K.ring)
    (hm : P.ev m = P.E.ring.zero) (hdvd : PolyDvd P.K.ring m f) :
    P.ev f = P.E.ring.zero := by
  obtain ⟨q, hq⟩ := hdvd
  have hfe : f = psMul P.K.ring q m := funext hq
  rw [hfe, P.ev_mul q m, hm, CRing.mul_zero P.E.ring (P.ev q)]

/-! ## M273F-2: 代数的元 -/

/-- **M273F-2: 代数的元** — α が K 上代数的 ⟺ 非零多項式（有界かつ
    恒等的には 0 でない）が α で消える。 -/
def IsAlgebraic (P : PolyEval) : Prop :=
  ∃ (d : Nat) (f : PS P.K.ring), IsPolyBounded P.K.ring f (d + 1) ∧
    (∃ i, f i ≠ P.K.ring.zero) ∧ P.ev f = P.E.ring.zero

/-! ## M273F-3: 定数倍とモニック化 -/

/-- **M273F-3a: 定数倍の係数公式** — (c·f)_j = c·f_j
    （単項式 c·X⁰ との Cauchy 積は i = 0 の項だけ残る）。 -/
theorem psMul_const_coeff (R : CRing) (c : R.carrier) (f : PS R) (j : Nat) :
    psMul R (psSingle R c 0) f j = R.mul c (f j) := by
  show rsum R (fun i => R.mul (psSingle R c 0 i) (f (j - i))) (j + 1)
    = R.mul c (f j)
  have hmid : rsum R (fun i => R.mul (psSingle R c 0 i) (f (j - i))) (j + 1)
      = R.mul (psSingle R c 0 0) (f (j - 0)) :=
    rsum_single_middle R (fun i => R.mul (psSingle R c 0 i) (f (j - i))) 0
      (j + 1)
      (fun i _ hi0 => by
        show R.mul (psSingle R c 0 i) (f (j - i)) = R.zero
        rw [show psSingle R c 0 i = R.zero from if_neg hi0]
        exact CRing.zero_mul R _)
      (by omega)
  rw [hmid, show psSingle R c 0 0 = c from if_pos rfl, Nat.sub_zero]

/-- **M273F-3b: モニック化（体固有）** — 先頭係数 f_d ≠ 0 の多項式 f を
    (f_d)⁻¹ で定数倍すると、先頭係数 1（モニック）・有界性維持・α での
    消滅維持。**先頭係数の逆元**を使う点が体固有。 -/
theorem minPoly_normalize (P : PolyEval) (f : PS P.K.ring) (d : Nat)
    (hfb : IsPolyBounded P.K.ring f (d + 1))
    (hlead : f d ≠ P.K.ring.zero)
    (hfv : P.ev f = P.E.ring.zero) :
    IsPolyBounded P.K.ring
        (psMul P.K.ring (psSingle P.K.ring (P.K.invf (f d)) 0) f) (d + 1)
      ∧ (psMul P.K.ring (psSingle P.K.ring (P.K.invf (f d)) 0) f) d
          = P.K.ring.one
      ∧ P.ev (psMul P.K.ring (psSingle P.K.ring (P.K.invf (f d)) 0) f)
          = P.E.ring.zero := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [psMul_const_coeff P.K.ring (P.K.invf (f d)) f i, hfb i hi,
      CRing.mul_zero P.K.ring (P.K.invf (f d))]
  · rw [psMul_const_coeff P.K.ring (P.K.invf (f d)) f d, P.K.ring.mul_comm]
    exact P.K.mul_inv_cancel (f d) hlead
  · rw [P.ev_mul (psSingle P.K.ring (P.K.invf (f d)) 0) f, hfv,
      CRing.mul_zero P.E.ring (P.ev (psSingle P.K.ring (P.K.invf (f d)) 0))]

/-! ## M273F-4: 最小多項式データ -/

/-- **M273F-4a: 最小多項式データ** — 体上多項式評価 `P` に対する α の
    最小多項式 m（次数 d）を束ねる: モニック（m_d = 1）・有界（deg ≤ d）・
    α で消える・**最小次数性**（deg < d の任意の消える多項式は零）・
    体の非自明性（1 ≠ 0）。 -/
structure MinPolyData where
  /-- 台となる体上多項式評価。 -/
  P : PolyEval
  /-- 最小多項式の次数。 -/
  deg : Nat
  /-- 最小多項式。 -/
  m : PS P.K.ring
  /-- 有界（次数 ≤ deg）。 -/
  bounded : IsPolyBounded P.K.ring m (deg + 1)
  /-- モニック（先頭係数 = 1）。 -/
  monic : m deg = P.K.ring.one
  /-- α で消える。 -/
  vanishes : P.ev m = P.E.ring.zero
  /-- **最小次数性**: deg 未満で α を消す多項式は零。 -/
  minimal : ∀ f, IsPolyBounded P.K.ring f deg → P.ev f = P.E.ring.zero →
    ∀ i, f i = P.K.ring.zero
  /-- 体の非自明性 1 ≠ 0。 -/
  nontrivial : P.K.ring.one ≠ P.K.ring.zero

/-- **M273F-4b: 最小性の対偶** — 次数 < deg の非零多項式は α で消えない。 -/
theorem minPoly_nonzero_eval (D : MinPolyData) (f : PS D.P.K.ring)
    (hb : IsPolyBounded D.P.K.ring f D.deg)
    (hne : ∃ i, f i ≠ D.P.K.ring.zero) :
    D.P.ev f ≠ D.P.E.ring.zero := by
  intro hev
  obtain ⟨i, hi⟩ := hne
  exact hi (D.minimal f hb hev i)

/-- **M273F-4c: 最小多項式は非零 ⟹ α は代数的**。 -/
theorem minPolyData_isAlgebraic (D : MinPolyData) : IsAlgebraic D.P :=
  ⟨D.deg, D.m, D.bounded, ⟨D.deg, by rw [D.monic]; exact D.nontrivial⟩,
    D.vanishes⟩

/-! ## M273F-5: 一意性 -/

/-- **定理 (M273F-5): 最小多項式の一意性** — 同じ次数 deg のモニック多項式
    m' が α を消すなら m = m'。差 m − m' は次数 < deg（先頭が両者 1 で
    打ち消し）で α を消すので、最小性から零、ゆえに相等。 -/
theorem minPoly_unique (D : MinPolyData) (m' : PS D.P.K.ring)
    (hb' : IsPolyBounded D.P.K.ring m' (D.deg + 1))
    (hmonic' : m' D.deg = D.P.K.ring.one)
    (hvan' : D.P.ev m' = D.P.E.ring.zero) :
    ∀ i, D.m i = m' i := by
  have hdiffb : IsPolyBounded D.P.K.ring
      (psAdd D.P.K.ring D.m (psNeg D.P.K.ring m')) D.deg := by
    intro j hj
    show D.P.K.ring.add (D.m j) (D.P.K.ring.neg (m' j)) = D.P.K.ring.zero
    cases Nat.lt_or_ge j (D.deg + 1) with
    | inl hlt =>
      have hje : j = D.deg := by omega
      subst hje
      rw [D.monic, hmonic', CRing.add_neg D.P.K.ring D.P.K.ring.one]
    | inr hge =>
      rw [D.bounded j hge, hb' j hge, CRing.neg_zero D.P.K.ring,
        D.P.K.ring.zero_add]
  have hvan : D.P.ev (psAdd D.P.K.ring D.m (psNeg D.P.K.ring m'))
      = D.P.E.ring.zero :=
    polyEval_sub_vanish D.P D.m m' D.vanishes hvan'
  intro i
  have hz : D.P.K.ring.add (D.m i) (D.P.K.ring.neg (m' i)) = D.P.K.ring.zero :=
    D.minimal (psAdd D.P.K.ring D.m (psNeg D.P.K.ring m')) hdiffb hvan i
  exact CRing.eq_of_sub_eq_zero D.P.K.ring hz

/-! ## M273F-6: 既約性 -/

/-- **定理 (M273F-6): 最小多項式は既約** — m = g·h（deg g, deg h < deg、
    g, h ともに非零）は不可能。最小性の対偶で ev g ≠ 0・ev h ≠ 0、E の
    整域性で ev g·ev h ≠ 0、しかし ev(g·h) = ev m = 0 で矛盾。**選言に
    依らず**構成的（case split 不要）。 -/
theorem minPoly_irreducible (D : MinPolyData)
    (g h : PS D.P.K.ring) (dg dh : Nat)
    (hgb : IsPolyBounded D.P.K.ring g (dg + 1))
    (hhb : IsPolyBounded D.P.K.ring h (dh + 1))
    (hdg : dg < D.deg) (hdh : dh < D.deg)
    (hgne : ∃ i, g i ≠ D.P.K.ring.zero)
    (hhne : ∃ i, h i ≠ D.P.K.ring.zero)
    (hfac : ∀ j, D.m j = psMul D.P.K.ring g h j) : False := by
  have hgb' : IsPolyBounded D.P.K.ring g D.deg := fun i hi => hgb i (by omega)
  have hhb' : IsPolyBounded D.P.K.ring h D.deg := fun i hi => hhb i (by omega)
  have hge : D.P.ev g ≠ D.P.E.ring.zero := minPoly_nonzero_eval D g hgb' hgne
  have hmfac : D.m = psMul D.P.K.ring g h := funext hfac
  have hprod : D.P.E.ring.mul (D.P.ev g) (D.P.ev h) = D.P.E.ring.zero := by
    rw [← D.P.ev_mul g h, ← hmfac, D.vanishes]
  have hgz : D.P.ev g = D.P.E.ring.zero :=
    mul_eq_zero_left268 D.P.E.ring D.P.E.invf D.P.E.mul_inv_cancel
      (minPoly_nonzero_eval D h hhb' hhne) hprod
  exact hge hgz

/-! ## M273F-7: 核 = (最小多項式) -/

/-- **定理 (M273F-7a): 消滅 ⟹ 整除（体上除法の応用）** — f が有界で
    f(α) = 0 なら m ∣ f。f = q·m + r（体上除法 M268F、deg r < deg）で、
    ev r = ev f − ev q·ev m = 0、r は次数 < deg で消えるので最小性から
    r = 0、ゆえ f = q·m。**除法定理の本丸の応用**。 -/
theorem minPoly_dvd_of_vanish (D : MinPolyData) (N : Nat) (f : PS D.P.K.ring)
    (hfb : IsPolyBounded D.P.K.ring f (N + D.deg))
    (hfv : D.P.ev f = D.P.E.ring.zero) :
    PolyDvd D.P.K.ring D.m f := by
  have hlead : D.m D.deg ≠ D.P.K.ring.zero := by
    rw [D.monic]; exact D.nontrivial
  obtain ⟨q, r, _hq, hr, heq⟩ :=
    field_division_exists D.P.K.ring D.P.K.invf D.P.K.mul_inv_cancel
      D.m D.deg D.bounded hlead N f hfb
  have hfeq : f = psAdd D.P.K.ring (psMul D.P.K.ring q D.m) r := funext heq
  have hevr : D.P.ev r = D.P.E.ring.zero := by
    have hsplit : D.P.ev f
        = D.P.E.ring.add (D.P.E.ring.mul (D.P.ev q) (D.P.ev D.m)) (D.P.ev r) := by
      rw [hfeq, D.P.ev_add, D.P.ev_mul]
    rw [D.vanishes, CRing.mul_zero D.P.E.ring (D.P.ev q),
      D.P.E.ring.zero_add] at hsplit
    rw [← hsplit]; exact hfv
  have hrzero : ∀ i, r i = D.P.K.ring.zero := D.minimal r hr hevr
  refine ⟨q, ?_⟩
  intro j
  rw [heq j]
  show D.P.K.ring.add (psMul D.P.K.ring q D.m j) (r j)
    = psMul D.P.K.ring q D.m j
  rw [hrzero j, CRing.add_zero D.P.K.ring (psMul D.P.K.ring q D.m j)]

/-- **定理 (M273F-7b): 整除 ⟹ 消滅** — m ∣ f なら f(α) = 0。 -/
theorem minPoly_vanish_of_dvd (D : MinPolyData) (f : PS D.P.K.ring)
    (hdvd : PolyDvd D.P.K.ring D.m f) : D.P.ev f = D.P.E.ring.zero :=
  polyEval_vanish_of_dvd D.P D.m f D.vanishes hdvd

/-- **定理 (M273F-7c): 核 = (最小多項式)** — 有界な f について
    f(α) = 0 ⟺ m ∣ f。評価準同型の核はちょうど最小多項式の生成する
    イデアル（体上除法 M268F が本質）。 -/
theorem minPoly_ker (D : MinPolyData) (N : Nat) (f : PS D.P.K.ring)
    (hfb : IsPolyBounded D.P.K.ring f (N + D.deg)) :
    (D.P.ev f = D.P.E.ring.zero) ↔ PolyDvd D.P.K.ring D.m f :=
  ⟨fun hv => minPoly_dvd_of_vanish D N f hfb hv,
   fun hd => minPoly_vanish_of_dvd D f hd⟩

/-! ## M273F-8: capstone -/

/-- **M273F-8a: 最小次数 witness からの最小多項式構成** — 次数 d の非零
    （先頭係数 f_d ≠ 0）多項式 f が α を消し、d が最小（deg < d の消える
    多項式は零）なら、f をモニック化して `MinPolyData` を得る。 -/
def minPolyData_of_witness (P : PolyEval) (d : Nat) (f : PS P.K.ring)
    (hfb : IsPolyBounded P.K.ring f (d + 1))
    (hlead : f d ≠ P.K.ring.zero)
    (hfv : P.ev f = P.E.ring.zero)
    (hmin : ∀ g, IsPolyBounded P.K.ring g d → P.ev g = P.E.ring.zero →
      ∀ i, g i = P.K.ring.zero)
    (hne : P.K.ring.one ≠ P.K.ring.zero) : MinPolyData where
  P := P
  deg := d
  m := psMul P.K.ring (psSingle P.K.ring (P.K.invf (f d)) 0) f
  bounded := (minPoly_normalize P f d hfb hlead hfv).1
  monic := (minPoly_normalize P f d hfb hlead hfv).2.1
  vanishes := (minPoly_normalize P f d hfb hlead hfv).2.2
  minimal := hmin
  nontrivial := hne

/-- **M273F-8b: 最小多項式の総括性質** — 一意性・既約性・核 = (m) を束ねる。 -/
def MinPolyResult (D : MinPolyData) : Prop :=
  (∀ m', IsPolyBounded D.P.K.ring m' (D.deg + 1) → m' D.deg = D.P.K.ring.one →
      D.P.ev m' = D.P.E.ring.zero → ∀ i, D.m i = m' i)
  ∧ (∀ (g h : PS D.P.K.ring) (dg dh : Nat),
      IsPolyBounded D.P.K.ring g (dg + 1) → IsPolyBounded D.P.K.ring h (dh + 1) →
      dg < D.deg → dh < D.deg → (∃ i, g i ≠ D.P.K.ring.zero) →
      (∃ i, h i ≠ D.P.K.ring.zero) →
      (∀ j, D.m j = psMul D.P.K.ring g h j) → False)
  ∧ (∀ (N : Nat) (w : PS D.P.K.ring), IsPolyBounded D.P.K.ring w (N + D.deg) →
      (D.P.ev w = D.P.E.ring.zero ↔ PolyDvd D.P.K.ring D.m w))

/-- **M273F-8c: 総括性質の証明** — 一意性（M273F-5）・既約性（M273F-6）・
    核生成（M273F-7c）を一本化。 -/
theorem minPoly_result (D : MinPolyData) : MinPolyResult D :=
  ⟨fun m' hb hm hv => minPoly_unique D m' hb hm hv,
   fun g h dg dh hgb hhb hdg hdh hgne hhne hfac =>
     minPoly_irreducible D g h dg dh hgb hhb hdg hdh hgne hhne hfac,
   fun N w hw => minPoly_ker D N w hw⟩

/-- **定理 (M273F-8d): 最小多項式の存在と総括** — 最小次数 witness から
    `MinPolyData` を構成し、それが一意・既約・核生成の総括性質を満たす。
    （最小次数 witness の抽出＝ℕ の整列性は非可述性のため入力とする。
    honest 限定はヘッダ参照。） -/
theorem minPoly_exists (P : PolyEval) (d : Nat) (f : PS P.K.ring)
    (hfb : IsPolyBounded P.K.ring f (d + 1))
    (hlead : f d ≠ P.K.ring.zero)
    (hfv : P.ev f = P.E.ring.zero)
    (hmin : ∀ g, IsPolyBounded P.K.ring g d → P.ev g = P.E.ring.zero →
      ∀ i, g i = P.K.ring.zero)
    (hne : P.K.ring.one ≠ P.K.ring.zero) :
    ∃ D : MinPolyData, MinPolyResult D :=
  ⟨minPolyData_of_witness P d f hfb hlead hfv hmin hne, minPoly_result _⟩

end IUT
