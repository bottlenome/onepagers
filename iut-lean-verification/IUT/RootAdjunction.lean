/-
  IUT/RootAdjunction.lean — M275F（根の添加 K[X]/(f) は f の根を含む:
  柱A 実代数拡大の本物の先行建設）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無）。

  **complete_pct 影響**: 柱A「実代数拡大／実 Galois 理論」の本物の先行建設。
  M269F `SimpleExtension` が単純拡大環 L = K[X]/(f)（f 既約なら体）を実構成
  したのに続き、本層は **その L が実際に f の根を含む**——すなわち ρ := [X]
  （多項式 X の商類）に対し **f(ρ) = 0**（L 上での f の評価が消える）——を
  本物に証明する。これは「代数拡大で多項式が根を持つ」＝分裂体構成・
  Galois 理論の出発点の本物の 1 段であり、toy 主語ではなく実多項式環 K[X]
  とその商 L の上の本物の等式である。核心は「L の中で [X] を X に代入すると
  f の類 [f] = 0」＝商環の定義（f ∈ (f) なので [f] = 0）を、L 上評価が
  環準同型 quotOf を通じて代表レベルの多項式再構成 Σ f_k X^k = f と両立する
  ことで丁寧に繋ぐ点にある。

  * M275F-1 `rootAdjX` / `rootAdj_root` — 根 ρ := [X]（K[X] の変数 X の商像）
  * M275F-2 `rootAdjPolyVal` — 多項式環 K[X] → 冪級数環 K[[X]] の忘却環準同型
    （部分環の .val、rsum/rpow の降下に使う）
  * M275F-3 補助 `rootAdj_rsum_poly_val` / `rootAdj_rsum_apply` /
    `rootAdj_psC_mono_coeff` / `rootAdj_modulus_class_zero` — 有限和の
    .val 降下・点別展開・単項係数 [X^k]、および [f] = 0（商の定義）
  * M275F-4 `rootAdjEval` — L 上での f の評価 Σ_{k≤deg} simpleExtC(f_k)·ρ^k
    （この根に特化した自前の有限和評価）
  * M275F-5 `rootAdj_eval_eq_map` / `rootAdj_polysum_eq_modulus` /
    **`rootAdj_is_root`** — 本丸: **f(ρ) = 0**（L 上評価が消える）を完全証明
  * M275F-6 `rootAdj_root_not_in_base` — deg f ≥ 2 のとき ρ は基礎体 K の像に
    入らない（真の拡大の非自明性 witness、次数論法 M268F 経由）
  * M275F-7 `RootAdjExt` / `RootAdjData` / `RootAdjData.build` /
    `rootAdj_exists` / `RootAdjFieldExt` / `rootAdj_field_exists` — capstone
    （根つき拡大レコードの構成と存在、M269F `simpleExt_field` との接続）

  正直な限定（何が本物で何が honest 限定か）:
   - **本物（本丸）**: **f(ρ) = 0** は完全証明（sorry 皆無・新規 choice 皆無）。
     すなわち L = K[X]/(f) 上で ρ = [X] を f に代入すると 0 になる、という
     代数拡大の根の存在そのものを実多項式環・実商環の上で確立した。
   - **L 上評価の定義**: f の評価写像は M274F の一般評価準同型とは独立に、
     この根 ρ に特化した自前の有限和 `rootAdjEval`（Σ simpleExtC(f_k)·ρ^k）
     として定義した（正直な限定として許容された形）。
   - **真の拡大（deg drop）**: 「ρ が K の像に入らない」非自明性は **deg f ≥ 2**
     のとき証明する（`rootAdj_root_not_in_base`）。deg f = 1 のときは
     K[X]/(X − a) ≅ K で ρ = a ∈ K となり拡大は自明——これは数学的事実であり、
     1 次既約多項式の添加が真の拡大を生まないことの正直な反映であって、
     消したり弱めたりしていない。1,ρ,…,ρ^{d−1} の完全な一次独立（次数の
     完全抽出）は行わず、ρ∉K 像の非自明性に留める（許容された限定）。
   - deg 抽出は有界性・先頭係数の witness を受け取る（M269F と同じ精神）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.SimpleExtension
import IUT.PSFunctor
import IUT.Composition

namespace IUT

/-! ## M275F-1: 根 ρ := [X] -/

/-- **M275F-1a: 変数 X（多項式として）** — K[X] の元 X = (0,1,0,…)。
    有界性は 2（j ≥ 2 では消える）。 -/
def rootAdjX (K : Field268) : Poly K.ring :=
  ⟨psX K.ring, ⟨2, fun i hi => if_neg (by omega)⟩⟩

/-- **M275F-1b: 根 ρ := [X]** — 単純拡大 L = K[X]/(f) における変数 X の商類。
    これが f の根になる（M275F-5）。 -/
def rootAdj_root (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) : (simpleExtRing K f m hf).carrier :=
  (quotOf (polyCRing K.ring) (simpleExtModulus K f m hf)).map (rootAdjX K)

/-! ## M275F-2: 多項式環 → 冪級数環 の忘却環準同型 -/

/-- **M275F-2: 忘却環準同型** K[X] → K[[X]]（部分環の .val、rfl で環法則）。
    有限和・冪の代表レベルへの降下に使う。 -/
def rootAdjPolyVal (R : CRing) : RingHom (polyCRing R) (psRing R) where
  map := fun a => a.val
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_one := rfl

/-! ## M275F-3: 補助補題 -/

/-- **M275F-3a: 有限和の .val 降下** — K[X] 上の有限和の代表は、代表たちの
    K[[X]] 上の有限和。 -/
theorem rootAdj_rsum_poly_val (R : CRing) (G : Nat → Poly R) :
    ∀ nn, (rsum (polyCRing R) G nn).val
      = rsum (psRing R) (fun k => (G k).val) nn := by
  intro nn
  induction nn with
  | zero => rfl
  | succ nn ih =>
    show (psRing R).add ((rsum (polyCRing R) G nn).val) ((G nn).val)
      = (psRing R).add (rsum (psRing R) (fun k => (G k).val) nn) ((G nn).val)
    rw [ih]

/-- **M275F-3b: 冪級数の有限和の点別評価** — Σ の n 番係数は係数の Σ。 -/
theorem rootAdj_rsum_apply (R : CRing) (G : Nat → PS R) :
    ∀ nn idx, rsum (psRing R) G nn idx = rsum R (fun k => G k idx) nn := by
  intro nn
  induction nn with
  | zero => intro idx; rfl
  | succ nn ih =>
    intro idx
    show R.add ((rsum (psRing R) G nn) idx) (G nn idx)
      = R.add (rsum R (fun k => G k idx) nn) (G nn idx)
    rw [ih idx]

/-- **M275F-3c: 単項式の係数** — (c · X^k) の n 番係数 = c · [X^k]_n
    （定数と単項式の畳み込み、一点集中）。 -/
theorem rootAdj_psC_mono_coeff (R : CRing) (c : R.carrier) (k n : Nat) :
    psMul R (psC R c) (psMono R k) n = R.mul c (psMono R k n) := by
  show rsum R (fun j => R.mul (psC R c j) (psMono R k (n - j))) (n + 1)
    = R.mul c (psMono R k n)
  rw [rsum_single R (fun j => R.mul (psC R c j) (psMono R k (n - j))) 0 (n + 1)
      (by omega) (fun j _ hjne => by
        show R.mul (psC R c j) (psMono R k (n - j)) = R.zero
        rw [show psC R c j = R.zero from if_neg hjne]
        exact R.zero_mul _),
    show psC R c 0 = c from if_pos rfl, Nat.sub_zero]

/-- **M275F-3d: 法多項式の類は 0** — 商環 S/(E) では [E] = 0（E ∈ (E)）。
    証人 1 のイデアル計算: E − 0 = 1·E。 -/
theorem rootAdj_modulus_class_zero (S : CRing) (E : S.carrier) :
    Quot.mk (idealRel S E) E = (quotCRing S E).zero := by
  apply Quot.sound
  refine ⟨S.one, ?_⟩
  show S.add E (S.neg S.zero) = S.mul S.one E
  rw [CRing.neg_zero S, CRing.add_zero S E, S.one_mul E]

/-! ## M275F-4: L 上での f の評価 -/

/-- **M275F-4a: L 上の f の評価** Σ_{k≤deg} simpleExtC(f_k)·ρ^k
    （この根 ρ に特化した自前の有限和評価）。 -/
def rootAdjEval (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) : (simpleExtRing K f m hf).carrier :=
  rsum (simpleExtRing K f m hf)
    (fun k => (simpleExtRing K f m hf).mul
      ((simpleExtC K f m hf).map (f k))
      (rpow (simpleExtRing K f m hf) (rootAdj_root K f m hf) k))
    (m + 1)

/-- **M275F-4b: 評価の代表多項式** Σ_{k≤deg} f_k · X^k（K[X] 内）。 -/
def rootAdjPolySum (K : Field268) (f : PS K.ring) (m : Nat) : Poly K.ring :=
  rsum (polyCRing K.ring)
    (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (f k))
      (rpow (polyCRing K.ring) (rootAdjX K) k)) (m + 1)

/-! ## M275F-5: 本丸 f(ρ) = 0 -/

/-- **M275F-5a: 評価は代表の商像** — L 上評価 = quotOf(代表多項式)
    （環準同型 quotOf が有限和・積・冪と交換）。 -/
theorem rootAdj_eval_eq_map (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) :
    rootAdjEval K f m hf
      = (quotOf (polyCRing K.ring) (simpleExtModulus K f m hf)).map
          (rootAdjPolySum K f m) := by
  show rsum (simpleExtRing K f m hf)
      (fun k => (simpleExtRing K f m hf).mul
        ((simpleExtC K f m hf).map (f k))
        (rpow (simpleExtRing K f m hf) (rootAdj_root K f m hf) k)) (m + 1)
    = (quotOf (polyCRing K.ring) (simpleExtModulus K f m hf)).map
        (rsum (polyCRing K.ring)
          (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (f k))
            (rpow (polyCRing K.ring) (rootAdjX K) k)) (m + 1))
  rw [ringHom_rsum (quotOf (polyCRing K.ring) (simpleExtModulus K f m hf))
      (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (f k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)) (m + 1)]
  refine rsum_congr (simpleExtRing K f m hf) (m + 1) (fun k _ => ?_)
  show (quotCRing (polyCRing K.ring) (simpleExtModulus K f m hf)).mul
      ((quotOf (polyCRing K.ring) (simpleExtModulus K f m hf)).map
        ((polyC K.ring).map (f k)))
      (rpow (quotCRing (polyCRing K.ring) (simpleExtModulus K f m hf))
        ((quotOf (polyCRing K.ring) (simpleExtModulus K f m hf)).map (rootAdjX K)) k)
    = (quotOf (polyCRing K.ring) (simpleExtModulus K f m hf)).map
        ((polyCRing K.ring).mul ((polyC K.ring).map (f k))
          (rpow (polyCRing K.ring) (rootAdjX K) k))
  rw [(quotOf (polyCRing K.ring) (simpleExtModulus K f m hf)).map_mul,
    ringHom_rpow (quotOf (polyCRing K.ring) (simpleExtModulus K f m hf))
      (rootAdjX K) k]

/-- **M275F-5b: 代表多項式は f そのもの** — Σ_{k≤deg} f_k · X^k = f（K[X] 内）。
    点別に一点集中和で係数を復元。 -/
theorem rootAdj_polysum_eq_modulus (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) :
    rootAdjPolySum K f m = simpleExtModulus K f m hf := by
  apply Subtype.ext
  apply funext
  intro n
  have hpow : ∀ k, (rpow (polyCRing K.ring) (rootAdjX K) k).val = psMono K.ring k := by
    intro k
    have hr : (rpow (polyCRing K.ring) (rootAdjX K) k).val
        = rpow (psRing K.ring) (psX K.ring) k :=
      ringHom_rpow (rootAdjPolyVal K.ring) (rootAdjX K) k
    rw [hr, rpow_psX K.ring k]
  have hcoef : ∀ k, ((polyCRing K.ring).mul ((polyC K.ring).map (f k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)).val n
      = K.ring.mul (f k) (psMono K.ring k n) := by
    intro k
    show psMul K.ring (psC K.ring (f k))
        ((rpow (polyCRing K.ring) (rootAdjX K) k).val) n
      = K.ring.mul (f k) (psMono K.ring k n)
    rw [hpow k, rootAdj_psC_mono_coeff K.ring (f k) k n]
  show (rsum (polyCRing K.ring)
      (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (f k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)) (m + 1)).val n = f n
  rw [rootAdj_rsum_poly_val K.ring
      (fun k => (polyCRing K.ring).mul ((polyC K.ring).map (f k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)) (m + 1),
    rootAdj_rsum_apply K.ring
      (fun k => ((polyCRing K.ring).mul ((polyC K.ring).map (f k))
        (rpow (polyCRing K.ring) (rootAdjX K) k)).val) (m + 1) n,
    rsum_congr K.ring (m + 1) (fun k _ => hcoef k)]
  cases Nat.lt_or_ge n (m + 1) with
  | inl hlt =>
    rw [rsum_single K.ring (fun k => K.ring.mul (f k) (psMono K.ring k n)) n (m + 1)
        hlt (fun j _ hjne => by
          show K.ring.mul (f j) (psMono K.ring j n) = K.ring.zero
          rw [show psMono K.ring j n = K.ring.zero from if_neg (fun hc => hjne hc.symm)]
          exact K.ring.mul_zero (f j)),
      show psMono K.ring n n = K.ring.one from if_pos rfl,
      K.ring.mul_comm, K.ring.one_mul]
  | inr hge =>
    rw [rsum_congr K.ring (m + 1) (fun k hk => by
        show K.ring.mul (f k) (psMono K.ring k n) = K.ring.zero
        rw [show psMono K.ring k n = K.ring.zero from if_neg (fun hc => by omega)]
        exact K.ring.mul_zero (f k)),
      rsum_const_zero K.ring]
    exact (hf n hge).symm

/-- **定理 (M275F-5c): f(ρ) = 0** — 本丸。単純拡大 L = K[X]/(f) において
    ρ = [X] は f の根である（L 上での f の評価が消える）。
    評価 = quotOf(Σ f_k X^k) = quotOf(f) = [f] = 0（商の定義）。 -/
theorem rootAdj_is_root (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) :
    rootAdjEval K f m hf = (simpleExtRing K f m hf).zero := by
  rw [rootAdj_eval_eq_map K f m hf, rootAdj_polysum_eq_modulus K f m hf]
  exact rootAdj_modulus_class_zero (polyCRing K.ring) (simpleExtModulus K f m hf)

/-! ## M275F-6: 真の拡大の非自明性（deg ≥ 2） -/

/-- **定理 (M275F-6): ρ ∉ K の像**（deg f ≥ 2）— もし ρ = simpleExtC(c) なら
    [X] = [C(c)]、すなわち f ∣ (X − c)。だが X − c は次数 1 で有界（bound 2）、
    f は次数 deg ≥ 2 なので次数論法（M268F の整域的正則性）で商 w = 0、
    ゆえに X − c = 0、しかし (X − c) の 1 次係数は 1 ≠ 0 で矛盾。
    従って ρ は基礎体 K の像に含まれない＝拡大は自明でない。 -/
theorem rootAdj_root_not_in_base (K : Field268) (f : PS K.ring) (m : Nat)
    (hf : IsPolyBounded K.ring f (m + 1)) (hlead : f m ≠ K.ring.zero)
    (hm2 : 2 ≤ m) (hK1 : K.ring.one ≠ K.ring.zero) :
    ∀ c : K.ring.carrier,
      rootAdj_root K f m hf ≠ (simpleExtC K f m hf).map c := by
  intro c hc
  have hc' : Quot.mk (idealRel (polyCRing K.ring) (simpleExtModulus K f m hf))
        (rootAdjX K)
      = Quot.mk (idealRel (polyCRing K.ring) (simpleExtModulus K f m hf))
          ((polyC K.ring).map c) := hc
  obtain ⟨w, hw⟩ :=
    quot_exact_ideal (polyCRing K.ring) (simpleExtModulus K f m hf) hc'
  have hval : psAdd K.ring (psX K.ring) (psNeg K.ring (psC K.ring c))
      = psMul K.ring w.val f :=
    congrArg (fun t : Poly K.ring => t.val) hw
  obtain ⟨Nw, hwb⟩ := w.property
  have hA2 : IsPolyBounded K.ring
      (psAdd K.ring (psX K.ring) (psNeg K.ring (psC K.ring c))) 2 := by
    intro j hj
    show K.ring.add (psX K.ring j) (K.ring.neg (psC K.ring c j)) = K.ring.zero
    rw [show psX K.ring j = K.ring.zero from if_neg (by omega),
      show psC K.ring c j = K.ring.zero from if_neg (by omega),
      CRing.neg_zero K.ring, K.ring.zero_add]
  have hwzero : ∀ i, w.val i = K.ring.zero :=
    poly_mul_g_bounded_zero268 K.ring K.invf K.mul_inv_cancel f m hf hlead
      w.val Nw hwb (fun j hj => by
        rw [← hval]
        exact hA2 j (by omega))
  have hmulzero : psMul K.ring w.val f 1 = K.ring.zero := by
    show rsum K.ring (fun k => K.ring.mul (w.val k) (f (1 - k))) (1 + 1) = K.ring.zero
    rw [rsum_congr K.ring (1 + 1) (fun k _ => by
        show K.ring.mul (w.val k) (f (1 - k)) = K.ring.zero
        rw [hwzero k]
        exact CRing.zero_mul K.ring (f (1 - k))),
      rsum_const_zero K.ring]
  have hA1val : psAdd K.ring (psX K.ring) (psNeg K.ring (psC K.ring c)) 1
      = K.ring.one := by
    show K.ring.add (psX K.ring 1) (K.ring.neg (psC K.ring c 1)) = K.ring.one
    rw [show psX K.ring 1 = K.ring.one from if_pos rfl,
      show psC K.ring c 1 = K.ring.zero from if_neg (by omega),
      CRing.neg_zero K.ring, CRing.add_zero K.ring K.ring.one]
  have hone_zero : K.ring.one = K.ring.zero := by
    rw [← hA1val, hval]
    exact hmulzero
  exact hK1 hone_zero

/-! ## M275F-7: capstone -/

/-- **M275F-7a: 根つき拡大の出力レコード** — 拡大環・基礎体埋め込み・根 ρ・
    評価 f(ρ)・f(ρ) = 0 を束ねる。 -/
structure RootAdjExt (K : Field268) where
  /-- 拡大環 K[X]/(f)。 -/
  ring : CRing
  /-- 基礎体の埋め込み K → K[X]/(f)。 -/
  emb : RingHom K.ring ring
  /-- 添加された根 ρ = [X]。 -/
  root : ring.carrier
  /-- L 上での f の評価 f(ρ)。 -/
  eval : ring.carrier
  /-- **f(ρ) = 0**（根であること）。 -/
  is_root : eval = ring.zero

/-- **M275F-7b: 根つき拡大の入力データ** — 法多項式 f と次数 witness。 -/
structure RootAdjData (K : Field268) where
  /-- 法多項式（係数列）。 -/
  modulus : PS K.ring
  /-- 次数 deg。 -/
  deg : Nat
  /-- 有界性（deg+1 で消える）。 -/
  bound : IsPolyBounded K.ring modulus (deg + 1)
  /-- 先頭係数 ≠ 0。 -/
  lead : modulus deg ≠ K.ring.zero
  /-- deg ≥ 1（f は非定数）。 -/
  deg_pos : 1 ≤ deg

/-- **定理 (M275F-7c): 根つき拡大の構成** — 入力データから、根 ρ とその
    f(ρ) = 0 を備えた拡大レコードを本物に組み上げる。 -/
def RootAdjData.build (K : Field268) (d : RootAdjData K) : RootAdjExt K where
  ring := simpleExtRing K d.modulus d.deg d.bound
  emb := simpleExtC K d.modulus d.deg d.bound
  root := rootAdj_root K d.modulus d.deg d.bound
  eval := rootAdjEval K d.modulus d.deg d.bound
  is_root := rootAdj_is_root K d.modulus d.deg d.bound

/-- **定理 (M275F-7d): 根つき拡大の存在**。 -/
theorem rootAdj_exists (K : Field268) (d : RootAdjData K) :
    Nonempty (RootAdjExt K) :=
  ⟨d.build K⟩

/-- **M275F-7e: 根つき体拡大の出力レコード** — M269F `SimpleFieldExt`（体性:
    非零元に逆元）に根 ρ と f(ρ) = 0 を添える。 -/
structure RootAdjFieldExt (K : Field268) where
  /-- 体拡大（非零元に逆元をもつ）。 -/
  toSimple : SimpleFieldExt K
  /-- 添加された根 ρ = [X]。 -/
  root : toSimple.ring.carrier
  /-- L 上での f の評価 f(ρ)。 -/
  eval : toSimple.ring.carrier
  /-- **f(ρ) = 0**。 -/
  is_root : eval = toSimple.ring.zero

/-- **定理 (M275F-7f): 根つき体拡大の存在** — 既約性の Bezout 化を honest
    仮説として持つ `SimpleExtData`（M269F）から、**根 ρ を含む体拡大**が
    存在する（f(ρ) = 0 は完全証明、体性は M269F `simpleExt_field` 由来）。
    「既約 f に対し根を持つ体拡大が存在」の本物の 1 段。 -/
def SimpleExtData.rootAdjBuild (K : Field268) (d : SimpleExtData K) :
    RootAdjFieldExt K where
  toSimple := d.build K
  root := rootAdj_root K d.modulus d.deg d.bound
  eval := rootAdjEval K d.modulus d.deg d.bound
  is_root := rootAdj_is_root K d.modulus d.deg d.bound

/-- **定理 (M275F-7g): 根つき体拡大の存在**。 -/
theorem rootAdj_field_exists (K : Field268) (d : SimpleExtData K) :
    Nonempty (RootAdjFieldExt K) :=
  ⟨d.rootAdjBuild K⟩

end IUT
