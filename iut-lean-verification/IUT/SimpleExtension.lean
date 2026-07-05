/-
  IUT/SimpleExtension.lean — M269F（単純体拡大 K[X]/(f): 柱A 実 Galois
  理論の本物の先行建設）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無）。

  **complete_pct 影響**: 柱A「実 Galois 理論／実 π₁^ét」の本物の先行建設。
  体拡大の最も基本的な構成 **K[X]/(f)**（f 既約なら体）を、既存の体
  `Field268`（M268F）・体上多項式除法（M268F）・一般単項イデアル商環
  `quotCRing`（M109）の上に**本物の多項式環 K[X]**（冪級数環の有限台
  部分環）を建て、その単項イデアル商として実構成する。既存 `quotCRing`
  は**冪級数環** K[[X]] の商だが、体拡大には**多項式環** K[X] の商が
  要る（K[[X]] では定数項が非零な f は単元になり商が潰れる）——本層は
  この差を埋め、K[X] を真の環として構成して初めて「K[X]/(f) が K の
  体拡大」を本物に語れる。

  * M269F-1 `simpleExt_add_bounded` / `_neg_bounded` / `_mul_bounded` —
    有限台（多項式）の加法・符号・**積**の有界性（積の上界 N+M は
    Cauchy 和の各項が台の外で消えることを添字計算で示す・本物）
  * M269F-2 `IsPoly` / `Poly` / `polyAdd` / `polyNeg` / `polyMul` /
    `polyZero` / `polyOne` / **`polyCRing`** — **多項式環 K[X]**（冪級数環
    `psRing` の有限台部分環、環法則は `psRing` の法則へ Subtype.ext で
    降下）
  * M269F-3 `polyC` — 定数埋め込み K → K[X]（`psConstHom` の部分環版、
    環準同型）
  * M269F-4 `quotField_of_bezout` — **一般環の Bezout ⟹ 体**（本丸の核）:
    可換環 S で「E で割り切れない任意元 a が E と互いに素（∃u v, uE+va=1）」
    なら S/(E) は体（非零元に逆元が存在）。逆元は [v]、逆元性は
    va − 1 = (−u)E のイデアル計算（選択公理不要・∃ 形）
  * M269F-5 `simpleExtModulus` / `simpleExtRing` / `simpleExtC` —
    **K[X]/(f)** とその中への K の埋め込み（定数の商像）
  * M269F-6 `simpleExt_const_mul_zero` — 次数論法の核（定数 = w·f なら
    w=0、ゆえに定数=0）: `poly_mul_g_bounded_zero268`（M268F 整域性）を
    多項式環の商に適用
  * M269F-7 `simpleExtC_injective` — **K ↪ K[X]/(f) は単射**（deg f ≥ 1）:
    [c]=[d] ⟹ f ∣ (c−d)（定数）⟹ c=d
  * M269F-8 `simpleExt_nontrivial` — **K[X]/(f) は非自明**（1 ≠ 0、
    deg f ≥ 1・K 非自明）: f は単元でない
  * M269F-9 `simpleExt_field` — **f のイデアルが極大（Bezout）⟹ K[X]/(f)
    は体**（M269F-4 の instance、非零元に逆元）
  * M269F-10 `SimpleFieldExt` / `SimpleExtData` / `SimpleExtData.build` /
    `simpleExt_exists` — capstone（体拡大レコードの構成と存在）

  正直な限定（何が本物で何が honest 仮説か）:
   - **本物**: 多項式環 K[X] そのもの（部分環の全環法則）、単純拡大環
     K[X]/(f)、K の単射埋め込み、非自明性、そして「Bezout（極大性）⟹
     体」の含意（逆元の存在まで）は完全証明（sorry 皆無・新規 choice 皆無）。
   - **honest 仮説（deferred）**: 「f 既約 ⟹ 極大イデアル（= 割り切れない
     任意元と互いに素・Bezout ∃u v, uf+va=1）」は honest 仮説
     `SimpleExtData.bezout` として持ち回る。これを**素の既約性から
     拡張ユークリッド互除法（次数に関する整礎再帰）で構成する**のが
     本層に含めない重い後続（別モジュール）。Bezout は toy でなく実
     多項式環上の本物の命題であり、消さず honest に明示する（§4 準拠）。
   - **体の形**: 逆元は「非零元 ⟹ ∃ 逆元」の**構成的 ∃ 形**で述べる
     （`Field268` のような**全域 inv 函数**への昇格は選択原理を要し、
     本規約の証明本体での Classical.choice 禁止に触れるため対象外——
     Field.lean の整域性が仮説形である honest 申告と同じ精神）。
   - 次数上界の witness は仮説（有界性）として受け取る（有限台性からの
     次数抽出は行わない）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyFieldDivision
import IUT.EisTowerRings

namespace IUT

/-! ## M269F-1: 有限台（多項式）の演算の有界性 -/

/-- **M269F-1a: 加法の有界性** — g が N・h が M で有界なら g+h は N+M で
    有界（j ≥ N+M では両方 0）。 -/
theorem simpleExt_add_bounded (R : CRing) {g h : PS R} {N M : Nat}
    (hg : IsPolyBounded R g N) (hh : IsPolyBounded R h M) :
    IsPolyBounded R (psAdd R g h) (N + M) := by
  intro j hj
  show R.add (g j) (h j) = R.zero
  rw [hg j (by omega), hh j (by omega), R.zero_add]

/-- **M269F-1b: 符号の有界性**。 -/
theorem simpleExt_neg_bounded (R : CRing) {g : PS R} {N : Nat}
    (hg : IsPolyBounded R g N) : IsPolyBounded R (psNeg R g) N := by
  intro j hj
  show R.neg (g j) = R.zero
  rw [hg j hj, CRing.neg_zero R]

/-- **M269F-1c: 積の有界性** — g が N・h が M で有界なら g·h は N+M で
    有界。Cauchy 和 Σ_{k≤j} g_k h_{j−k} の各項は、k ≥ N なら g_k=0、
    k < N なら j−k ≥ M で h_{j−k}=0（j ≥ N+M）。 -/
theorem simpleExt_mul_bounded (R : CRing) {g h : PS R} {N M : Nat}
    (hg : IsPolyBounded R g N) (hh : IsPolyBounded R h M) :
    IsPolyBounded R (psMul R g h) (N + M) := by
  intro j hj
  show rsum R (fun k => R.mul (g k) (h (j - k))) (j + 1) = R.zero
  have hz : rsum R (fun k => R.mul (g k) (h (j - k))) (j + 1)
      = rsum R (fun _ => R.zero) (j + 1) :=
    rsum_congr R (j + 1) (fun k _ => by
      cases Nat.lt_or_ge k N with
      | inl hkN =>
        show R.mul (g k) (h (j - k)) = R.zero
        rw [hh (j - k) (by omega), CRing.mul_zero R (g k)]
      | inr hkN =>
        show R.mul (g k) (h (j - k)) = R.zero
        rw [hg k hkN, CRing.zero_mul R (h (j - k))])
  rw [hz]
  exact rsum_const_zero R (j + 1)

/-! ## M269F-2: 多項式環 K[X]（有限台部分環） -/

/-- **M269F-2a: 多項式性** — 係数列 g がある上界 N で有界（有限台）。 -/
def IsPoly (R : CRing) (g : PS R) : Prop := ∃ N, IsPolyBounded R g N

/-- **M269F-2b: 多項式**（冪級数環の有限台元）。 -/
def Poly (R : CRing) : Type := { g : PS R // IsPoly R g }

/-- 多項式の加法。 -/
def polyAdd (R : CRing) (a b : Poly R) : Poly R :=
  ⟨psAdd R a.val b.val, by
    obtain ⟨N, hN⟩ := a.property
    obtain ⟨M, hM⟩ := b.property
    exact ⟨N + M, simpleExt_add_bounded R hN hM⟩⟩

/-- 多項式の符号。 -/
def polyNeg (R : CRing) (a : Poly R) : Poly R :=
  ⟨psNeg R a.val, by
    obtain ⟨N, hN⟩ := a.property
    exact ⟨N, simpleExt_neg_bounded R hN⟩⟩

/-- 多項式の積。 -/
def polyMul (R : CRing) (a b : Poly R) : Poly R :=
  ⟨psMul R a.val b.val, by
    obtain ⟨N, hN⟩ := a.property
    obtain ⟨M, hM⟩ := b.property
    exact ⟨N + M, simpleExt_mul_bounded R hN hM⟩⟩

/-- 零多項式。 -/
def polyZero (R : CRing) : Poly R := ⟨psZero R, ⟨0, fun _ _ => rfl⟩⟩

/-- 単位多項式。 -/
def polyOne (R : CRing) : Poly R :=
  ⟨psOne R, ⟨1, fun i hi => if_neg (by omega)⟩⟩

/-- **定理 (M269F-2c): 多項式環 K[X]** — 冪級数環 `psRing` の有限台
    部分環は可換環。環法則は代表の `psRing` の法則へ Subtype.ext で降下。 -/
def polyCRing (R : CRing) : CRing where
  carrier := Poly R
  add := polyAdd R
  zero := polyZero R
  neg := polyNeg R
  mul := polyMul R
  one := polyOne R
  add_assoc := by
    intro a b c
    apply Subtype.ext
    exact (psRing R).add_assoc a.val b.val c.val
  zero_add := by
    intro a
    apply Subtype.ext
    exact (psRing R).zero_add a.val
  neg_add := by
    intro a
    apply Subtype.ext
    exact (psRing R).neg_add a.val
  add_comm := by
    intro a b
    apply Subtype.ext
    exact (psRing R).add_comm a.val b.val
  mul_assoc := by
    intro a b c
    apply Subtype.ext
    exact (psRing R).mul_assoc a.val b.val c.val
  one_mul := by
    intro a
    apply Subtype.ext
    exact (psRing R).one_mul a.val
  mul_comm := by
    intro a b
    apply Subtype.ext
    exact (psRing R).mul_comm a.val b.val
  left_distrib := by
    intro a b c
    apply Subtype.ext
    exact (psRing R).left_distrib a.val b.val c.val

/-! ## M269F-3: 定数埋め込み K → K[X] -/

/-- **M269F-3: 定数埋め込み** K → K[X]（`psConstHom` の部分環版、
    環準同型）。 -/
def polyC (R : CRing) : RingHom R (polyCRing R) where
  map := fun c => ⟨psC R c, ⟨1, fun i _ => if_neg (by omega)⟩⟩
  map_add := fun a b => Subtype.ext ((psConstHom R).map_add a b)
  map_mul := fun a b => Subtype.ext ((psConstHom R).map_mul a b)
  map_one := Subtype.ext (psConstHom R).map_one

/-! ## M269F-4: 一般環の Bezout ⟹ 体（本丸の核） -/

/-- **定理 (M269F-4): Bezout ⟹ 体（一般可換環）** — 可換環 S で、E で
    割り切れない任意元 a が E と互いに素（∃ u v, u·E + v·a = 1）なら、
    商環 S/(E) では**非零元に必ず乗法逆元が存在する**（= 体）。逆元は
    [v]：v·a − 1 = (−u)·E よりイデアル計算 [a·v] = [1]。選択公理不要、
    逆元は構成的 ∃ 形（全域 inv 函数は作らない）。 -/
theorem quotField_of_bezout (S : CRing) (E : S.carrier)
    (hBez : ∀ a : S.carrier, ¬ idealRel S E a S.zero →
      ∃ u v : S.carrier, S.add (S.mul u E) (S.mul v a) = S.one) :
    ∀ x : (quotCRing S E).carrier, x ≠ (quotCRing S E).zero →
      ∃ y, (quotCRing S E).mul x y = (quotCRing S E).one := by
  intro x
  induction x using Quot.ind
  rename_i a
  intro hx
  have hnr : ¬ idealRel S E a S.zero := fun hr => hx (Quot.sound hr)
  obtain ⟨u, v, huv⟩ := hBez a hnr
  refine ⟨Quot.mk (idealRel S E) v, ?_⟩
  show Quot.mk (idealRel S E) (S.mul a v) = Quot.mk (idealRel S E) S.one
  apply Quot.sound
  refine ⟨S.neg u, ?_⟩
  show S.add (S.mul a v) (S.neg S.one) = S.mul (S.neg u) E
  rw [S.mul_comm a v, CRing.neg_mul S u E, ← huv,
    CRing.neg_add_dist S (S.mul u E) (S.mul v a),
    S.add_comm (S.neg (S.mul u E)) (S.neg (S.mul v a)),
    ← S.add_assoc (S.mul v a) (S.neg (S.mul v a)) (S.neg (S.mul u E)),
    CRing.add_neg S (S.mul v a), S.zero_add]

/-! ## M269F-5: 単純拡大 K[X]/(f) と埋め込み -/

/-- **M269F-5a: 法多項式**（K[X] の元としての f）。 -/
def simpleExtModulus (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) : Poly K.ring :=
  ⟨f, ⟨m + 1, hf⟩⟩

/-- **M269F-5b: 単純拡大環** K[X]/(f)。 -/
def simpleExtRing (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) : CRing :=
  quotCRing (polyCRing K.ring) (simpleExtModulus K f m hf)

/-- **M269F-5c: 基礎体の埋め込み** K → K[X]/(f)（定数の商像、環準同型）。 -/
def simpleExtC (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) :
    RingHom K.ring (simpleExtRing K f m hf) :=
  RingHom.comp (polyC K.ring)
    (quotOf (polyCRing K.ring) (simpleExtModulus K f m hf))

/-! ## M269F-6: 次数論法の核 -/

/-- **定理 (M269F-6): 定数 = w·f ⟹ 定数 = 0** — A が 1 で有界（次数 0 の
    定数）で A = w·f（f は m+1 有界・先頭係数 ≠ 0・m ≥ 1）なら A の定数項
    は 0。次数 ≥ m の部分が全て 0 なので M268F の整域的正則性
    `poly_mul_g_bounded_zero268` で w = 0、ゆえに A = w·f = 0。 -/
theorem simpleExt_const_mul_zero (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) (hlead : f m ≠ K.ring.zero)
    (hm1 : 1 ≤ m) (A w : PS K.ring) (Nw : Nat)
    (hw : IsPolyBounded K.ring w Nw) (hA1 : IsPolyBounded K.ring A 1)
    (heq : ∀ j, A j = psMul K.ring w f j) :
    A 0 = K.ring.zero := by
  have hwzero : ∀ i, w i = K.ring.zero :=
    poly_mul_g_bounded_zero268 K.ring K.invf K.mul_inv_cancel f m hf hlead
      w Nw hw (fun j hj => by
        rw [← heq j]
        exact hA1 j (by omega))
  have h0 : psMul K.ring w f 0 = K.ring.zero := by
    show K.ring.add K.ring.zero (K.ring.mul (w 0) (f (0 - 0))) = K.ring.zero
    rw [hwzero 0, CRing.zero_mul K.ring (f (0 - 0)), K.ring.zero_add]
  rw [heq 0, h0]

/-! ## M269F-7: 埋め込みの単射性 -/

/-- **定理 (M269F-7): K ↪ K[X]/(f) は単射**（deg f ≥ 1）— [c] = [d] なら
    f ∣ (c−d)（定数）、定数を割る非零 f は次数論法（M269F-6）で
    c − d = 0 を強制、ゆえに c = d。 -/
theorem simpleExtC_injective (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) (hlead : f m ≠ K.ring.zero)
    (hm1 : 1 ≤ m) {c d : K.ring.carrier}
    (h : (simpleExtC K f m hf).map c = (simpleExtC K f m hf).map d) :
    c = d := by
  have hr := quot_exact_ideal (polyCRing K.ring)
    (simpleExtModulus K f m hf) h
  obtain ⟨w, hw⟩ := hr
  have hval : psAdd K.ring (psC K.ring c) (psNeg K.ring (psC K.ring d))
      = psMul K.ring w.val f :=
    congrArg (fun t : Poly K.ring => t.val) hw
  obtain ⟨Nw, hwb⟩ := w.property
  have hA1 : IsPolyBounded K.ring
      (psAdd K.ring (psC K.ring c) (psNeg K.ring (psC K.ring d))) 1 := by
    intro j hj
    show K.ring.add (psC K.ring c j) (K.ring.neg (psC K.ring d j)) = K.ring.zero
    rw [show psC K.ring c j = K.ring.zero from if_neg (by omega),
      show psC K.ring d j = K.ring.zero from if_neg (by omega),
      CRing.neg_zero K.ring, K.ring.zero_add]
  have hA0 := simpleExt_const_mul_zero K f m hf hlead hm1
    (psAdd K.ring (psC K.ring c) (psNeg K.ring (psC K.ring d))) w.val Nw
    hwb hA1 (fun j => congrFun hval j)
  apply CRing.eq_of_sub_eq_zero K.ring
  exact hA0

/-! ## M269F-8: 非自明性 -/

/-- **定理 (M269F-8): K[X]/(f) は非自明**（1 ≠ 0）— deg f ≥ 1・K 非自明
    なら、1 = h·f（f が単元）は次数論法で 1 = 0 を導き K の非自明性に
    反する。 -/
theorem simpleExt_nontrivial (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) (hlead : f m ≠ K.ring.zero)
    (hm1 : 1 ≤ m) (hK1 : K.ring.one ≠ K.ring.zero) :
    (simpleExtRing K f m hf).one ≠ (simpleExtRing K f m hf).zero := by
  intro h
  have hr := quot_exact_ideal (polyCRing K.ring)
    (simpleExtModulus K f m hf) h
  obtain ⟨w, hw⟩ := hr
  have hval : psAdd K.ring (psOne K.ring) (psNeg K.ring (psZero K.ring))
      = psMul K.ring w.val f :=
    congrArg (fun t : Poly K.ring => t.val) hw
  obtain ⟨Nw, hwb⟩ := w.property
  have hA1 : IsPolyBounded K.ring
      (psAdd K.ring (psOne K.ring) (psNeg K.ring (psZero K.ring))) 1 := by
    intro j hj
    show K.ring.add (psOne K.ring j) (K.ring.neg (psZero K.ring j)) = K.ring.zero
    rw [show psOne K.ring j = K.ring.zero from if_neg (by omega),
      show psZero K.ring j = K.ring.zero from rfl,
      CRing.neg_zero K.ring, K.ring.zero_add]
  have hA0 := simpleExt_const_mul_zero K f m hf hlead hm1
    (psAdd K.ring (psOne K.ring) (psNeg K.ring (psZero K.ring))) w.val Nw
    hwb hA1 (fun j => congrFun hval j)
  have e : K.ring.add K.ring.one (K.ring.neg K.ring.zero) = K.ring.zero := hA0
  rw [CRing.neg_zero K.ring, CRing.add_zero K.ring] at e
  exact hK1 e

/-! ## M269F-9: f のイデアルが極大（Bezout）⟹ 体 -/

/-- **定理 (M269F-9): Bezout ⟹ K[X]/(f) は体** — 「f で割り切れない
    任意多項式 a が f と互いに素（∃ u v, u·f + v·a = 1）」なら、
    K[X]/(f) の非零元は必ず逆元を持つ。M269F-4 の instance。 -/
theorem simpleExt_field (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1))
    (hBez : ∀ a : Poly K.ring,
      ¬ idealRel (polyCRing K.ring) (simpleExtModulus K f m hf) a
        (polyCRing K.ring).zero →
      ∃ u v : Poly K.ring,
        (polyCRing K.ring).add
          ((polyCRing K.ring).mul u (simpleExtModulus K f m hf))
          ((polyCRing K.ring).mul v a) = (polyCRing K.ring).one) :
    ∀ x : (simpleExtRing K f m hf).carrier,
      x ≠ (simpleExtRing K f m hf).zero →
      ∃ y, (simpleExtRing K f m hf).mul x y = (simpleExtRing K f m hf).one :=
  quotField_of_bezout (polyCRing K.ring) (simpleExtModulus K f m hf) hBez

/-! ## M269F-10: capstone -/

/-- **M269F-10a: 単純体拡大の出力レコード** — 拡大環・埋め込み・単射性・
    非自明性・逆元の存在を束ねる。 -/
structure SimpleFieldExt (K : Field268) where
  /-- 拡大環 K[X]/(f)。 -/
  ring : CRing
  /-- 基礎体の埋め込み K → K[X]/(f)。 -/
  emb : RingHom K.ring ring
  /-- 埋め込みは単射。 -/
  emb_injective : ∀ {c d : K.ring.carrier}, emb.map c = emb.map d → c = d
  /-- 非自明（1 ≠ 0）。 -/
  nontrivial : ring.one ≠ ring.zero
  /-- 体性: 非零元は乗法逆元を持つ（構成的 ∃ 形）。 -/
  has_inverses : ∀ x : ring.carrier, x ≠ ring.zero →
    ∃ y, ring.mul x y = ring.one

/-- **M269F-10b: 単純体拡大の入力データ** — 法多項式 f と、その既約性を
    体化する honest 仮説（Bezout / 極大性）。 -/
structure SimpleExtData (K : Field268) where
  /-- 法多項式（係数列）。 -/
  modulus : PS K.ring
  /-- 次数上界パラメータ deg（deg = 実次数）。 -/
  deg : Nat
  /-- 有界性（deg+1 で消える）。 -/
  bound : IsPolyBounded K.ring modulus (deg + 1)
  /-- 先頭係数 ≠ 0。 -/
  lead : modulus deg ≠ K.ring.zero
  /-- deg ≥ 1（f は非定数）。 -/
  deg_pos : 1 ≤ deg
  /-- 基礎体 K の非自明性。 -/
  base_nontrivial : K.ring.one ≠ K.ring.zero
  /-- **honest 仮説**: f のイデアルは極大（割り切れない任意元と互いに素）。
      素の既約性からの拡張ユークリッド互除法での構成は後続（deferred）。 -/
  bezout : ∀ a : Poly K.ring,
    ¬ idealRel (polyCRing K.ring) (simpleExtModulus K modulus deg bound) a
      (polyCRing K.ring).zero →
    ∃ u v : Poly K.ring,
      (polyCRing K.ring).add
        ((polyCRing K.ring).mul u (simpleExtModulus K modulus deg bound))
        ((polyCRing K.ring).mul v a) = (polyCRing K.ring).one

/-- **定理 (M269F-10c): 単純体拡大の構成** — 入力データから、体拡大
    レコード（拡大環・単射埋め込み・非自明・逆元）を本物に組み上げる。 -/
def SimpleExtData.build (K : Field268) (d : SimpleExtData K) :
    SimpleFieldExt K where
  ring := simpleExtRing K d.modulus d.deg d.bound
  emb := simpleExtC K d.modulus d.deg d.bound
  emb_injective := fun {_ _} h =>
    simpleExtC_injective K d.modulus d.deg d.bound d.lead d.deg_pos h
  nontrivial :=
    simpleExt_nontrivial K d.modulus d.deg d.bound d.lead d.deg_pos
      d.base_nontrivial
  has_inverses :=
    simpleExt_field K d.modulus d.deg d.bound d.bezout

/-- **定理 (M269F-10d): 単純体拡大の存在** — 入力データがあれば K の
    体拡大 K[X]/(f) が存在する（f 既約性の Bezout 化を honest 仮説として）。 -/
theorem simpleExt_exists (K : Field268) (d : SimpleExtData K) :
    Nonempty (SimpleFieldExt K) :=
  ⟨d.build K⟩

end IUT
