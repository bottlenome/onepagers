/-
  IUT/WeilPairing.lean — M339F [実／本物]
  分類: 実 (Tate 曲線捻れ E_q[n]=ℤ/n×ℤ/n 上の Weil ペアリング e_n→μ_n)
  complete_pct 影響: 柱A を前進（Tate 一意化での E_q[n] の Weil ペアリング e_n(ζ^aQ^b,ζ^cQ^d)
    =ζ^{ad−bc} を本物で構成＝捻れ点を円分体 μ_n に結ぶ交代双線形形式。捻れ↔μ の IUT 中心対応の
    代数的核）。
  正直な限定: 非退化性は determinant 形式の代数的完全証明（本物、仮説不要）まで。ただし
    (i) 幾何的 Weil ペアリング（ℓ-進 Tate 加群・カップ積による定義）との一致、(ii) E_q[n]
    が真に ℤ/n×ℤ/n と同型であること（μ_n 方向と q^{1/n} 方向の直積分解の完全性、M314F の
    位数証明までで直積は骨組み）、(iii) ガロア同変性（G_K 作用との両立＝円分指標 χ_n との
    完全接続）は柱A/E 後続。ここでは座標 (a,b)↦ζ^aQ^b の下での交代双線形形式 e_n(a,b,c,d)
    =ad−bc∈ℤ/n を本物で構成し、双線形性・交代性・反対称性・（代数的）非退化性・μ_n 着地を
    core Lean のみで完全証明する（toy を主語にしない）。

  * M339F-1 補助: `weil_mul_mk` / `weil_zmul_mk` / `weil_inv_mk` / `weilPairing_mk`
    （ℤ/n=`zmod n` の加法・乗法・逆元の Quot.mk 上の計算則、ペアリングの代表計算）と
    整数恒等式 `weil_int_*`（分配・可換の core 恒等式）
  * M339F-2 `weilPairing` — e_n(a,b,c,d) = a·d − b·c ∈ ℤ/n（交代 determinant 形式、μ_n 着地）
  * M339F-3 `weil_bilinear_left` / `weil_bilinear_right` — 各引数での双線形性（加法群準同型）
  * M339F-4 `weil_alternating`（e(P,P)=0）・`weil_antisymmetric`（e(P,Q)=−e(Q,P)）
  * M339F-5 `weil_nondegenerate` — 代数的非退化性（∀Q, e(P,Q)=0 ⟹ P=0、仮説不要の本物）
  * M339F-6 `weil_values_in_mu` — 値は円分群 μ_n=⟨ζ⟩（M322F `cycMuStd`）の冪 ζ^k に着地
  * M339F-7 `WeilTorsion`（E_q[n]=ℤ/n×ℤ/n）・`weilPairingPt` の点版・点版非退化性
  * M339F-8 capstone `WeilPairingData` / `weil_exists` / `weil_example_n3`

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用。共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
  一般名は `weil` 接頭辞で衝突回避。
-/
import IUT.CyclotomicRigidity
import IUT.PrincipalUnits
import IUT.TateTorsion

namespace IUT

/-! ## M339F-1: ℤ/n = `zmod n` 上の計算則と整数恒等式 -/

/-- **加法群 ℤ/n の和の代表計算** class a + class b = class (a+b)。 -/
theorem weil_mul_mk (n : Nat) (a b : Int) :
    (zmod n).mul (Quot.mk (modCong n).rel a) (Quot.mk (modCong n).rel b)
      = Quot.mk (modCong n).rel (a + b) := rfl

/-- **環 ℤ/n の積の代表計算** class a · class b = class (a·b)。 -/
theorem weil_zmul_mk (n : Nat) (a b : Int) :
    zmodMul n (Quot.mk (modCong n).rel a) (Quot.mk (modCong n).rel b)
      = Quot.mk (modCong n).rel (a * b) := rfl

/-- **加法群 ℤ/n の逆元（マイナス）の代表計算** −class a = class (−a)。 -/
theorem weil_inv_mk (n : Nat) (a : Int) :
    (zmod n).inv (Quot.mk (modCong n).rel a) = Quot.mk (modCong n).rel (-a) := rfl

/-- 整数恒等式（第一引数双線形性の核・分配則）。 -/
theorem weil_int_bl (a a' b b' c d : Int) :
    (a + a') * d + -((b + b') * c)
      = (a * d + -(b * c)) + (a' * d + -(b' * c)) := by
  rw [Int.add_mul a a' d, Int.add_mul b b' c]
  generalize a * d = P
  generalize a' * d = Q
  generalize b * c = R
  generalize b' * c = S
  omega

/-- 整数恒等式（第二引数双線形性の核・分配則）。 -/
theorem weil_int_br (a b c c' d d' : Int) :
    a * (d + d') + -(b * (c + c'))
      = (a * d + -(b * c)) + (a * d' + -(b * c')) := by
  rw [Int.mul_add a d d', Int.mul_add b c c']
  generalize a * d = P
  generalize a * d' = Q
  generalize b * c = R
  generalize b * c' = S
  omega

/-- 整数恒等式（交代性の核）a·b − b·a = 0。 -/
theorem weil_int_alt (a b : Int) : a * b + -(b * a) = 0 := by
  rw [Int.mul_comm b a]
  generalize a * b = P
  omega

/-- 整数恒等式（反対称性の核）a·d − b·c = −(c·b − d·a)。 -/
theorem weil_int_anti (a b c d : Int) :
    a * d + -(b * c) = -(c * b + -(d * a)) := by
  rw [Int.mul_comm c b, Int.mul_comm d a]
  generalize a * d = P
  generalize b * c = Q
  omega

/-- 整数恒等式（非退化 c=0,d=1）a·1 − b·0 = a。 -/
theorem weil_int_nd1 (a b : Int) : a * 1 + -(b * 0) = a := by
  rw [Int.mul_one, Int.mul_zero]
  omega

/-- 整数恒等式（非退化 c=1,d=0）a·0 − b·1 = −b。 -/
theorem weil_int_nd2 (a b : Int) : a * 0 + -(b * 1) = -b := by
  rw [Int.mul_zero, Int.mul_one]
  omega

/-- 整数恒等式（二重マイナス）−(−b) = b。 -/
theorem weil_int_negneg (b : Int) : - -b = b := by omega

/-! ## M339F-2: Weil ペアリング e_n(a,b,c,d) = a·d − b·c -/

/-- **Weil ペアリング** e_n : E_q[n] × E_q[n] → μ_n。座標 (a,b) ↦ ζ_n^a·Q^b（Q=q^{1/n}）の
    下で e_n(ζ^aQ^b, ζ^cQ^d) = ζ^{ad−bc}。値は μ_n≅ℤ/n（加法表記）で、交代 determinant
    形式 a·d − b·c（乗法は環 `zmodMul`、減法は加法群 `zmod n` の inv）。 -/
def weilPairing (n : Nat) (a b c d : (zmod n).carrier) : (zmod n).carrier :=
  (zmod n).mul (zmodMul n a d) ((zmod n).inv (zmodMul n b c))

/-- **ペアリングの代表計算** e_n(class a, class b, class c, class d) = class (a·d + −(b·c))。 -/
theorem weilPairing_mk (n : Nat) (a b c d : Int) :
    weilPairing n (Quot.mk (modCong n).rel a) (Quot.mk (modCong n).rel b)
      (Quot.mk (modCong n).rel c) (Quot.mk (modCong n).rel d)
      = Quot.mk (modCong n).rel (a * d + -(b * c)) := rfl

/-! ## M339F-3: 双線形性（各引数で加法群準同型） -/

/-- **第一引数での双線形性** e_n((a,b)+(a',b'), (c,d)) = e_n(a,b,c,d) + e_n(a',b',c,d)。
    (a+a')·d − (b+b')·c = (a·d−b·c) + (a'·d−b'·c)（ℤ/n の分配則）。 -/
theorem weil_bilinear_left (n : Nat) (a a' b b' c d : (zmod n).carrier) :
    weilPairing n ((zmod n).mul a a') ((zmod n).mul b b') c d
      = (zmod n).mul (weilPairing n a b c d) (weilPairing n a' b' c d) := by
  induction a using Quot.ind; rename_i a
  induction a' using Quot.ind; rename_i a'
  induction b using Quot.ind; rename_i b
  induction b' using Quot.ind; rename_i b'
  induction c using Quot.ind; rename_i c
  induction d using Quot.ind; rename_i d
  rw [weil_mul_mk, weil_mul_mk, weilPairing_mk, weilPairing_mk, weilPairing_mk, weil_mul_mk,
    weil_int_bl a a' b b' c d]

/-- **第二引数での双線形性** e_n((a,b), (c,d)+(c',d')) = e_n(a,b,c,d) + e_n(a,b,c',d')。
    a·(d+d') − b·(c+c') = (a·d−b·c) + (a·d'−b·c')（ℤ/n の分配則）。 -/
theorem weil_bilinear_right (n : Nat) (a b c c' d d' : (zmod n).carrier) :
    weilPairing n a b ((zmod n).mul c c') ((zmod n).mul d d')
      = (zmod n).mul (weilPairing n a b c d) (weilPairing n a b c' d') := by
  induction a using Quot.ind; rename_i a
  induction b using Quot.ind; rename_i b
  induction c using Quot.ind; rename_i c
  induction c' using Quot.ind; rename_i c'
  induction d using Quot.ind; rename_i d
  induction d' using Quot.ind; rename_i d'
  rw [weil_mul_mk, weil_mul_mk, weilPairing_mk, weilPairing_mk, weilPairing_mk, weil_mul_mk,
    weil_int_br a b c c' d d']

/-! ## M339F-4: 交代性・反対称性 -/

/-- **交代性** e_n(P,P) = 0（同一元同士のペアリングは自明）。a·b − b·a = 0。 -/
theorem weil_alternating (n : Nat) (a b : (zmod n).carrier) :
    weilPairing n a b a b = (zmod n).one := by
  induction a using Quot.ind; rename_i a
  induction b using Quot.ind; rename_i b
  rw [weilPairing_mk]
  show Quot.mk (modCong n).rel (a * b + -(b * a)) = Quot.mk (modCong n).rel 0
  rw [weil_int_alt a b]

/-- **反対称性** e_n(P,Q) = −e_n(Q,P)。a·d − b·c = −(c·b − d·a)。 -/
theorem weil_antisymmetric (n : Nat) (a b c d : (zmod n).carrier) :
    weilPairing n a b c d = (zmod n).inv (weilPairing n c d a b) := by
  induction a using Quot.ind; rename_i a
  induction b using Quot.ind; rename_i b
  induction c using Quot.ind; rename_i c
  induction d using Quot.ind; rename_i d
  rw [weilPairing_mk, weilPairing_mk, weil_inv_mk, weil_int_anti a b c d]

/-! ## M339F-5: 非退化性（determinant 形式の代数的完全証明） -/

/-- **非退化性（本物・仮説不要）** — もし e_n(P,Q)=0 が全ての Q について成り立てば P=0。
    determinant 形式 a·d−b·c の非退化性: Q=(0,1)（c=0,d=1）で e=a、Q=(1,0)（c=1,d=0）で
    e=−b を取り、a=0 かつ b=0 を得る。円分体 μ_n への埋め込みが完全（各座標が μ_n の
    生成元 ζ を独立に検出）であることの代数的核。 -/
theorem weil_nondegenerate (n : Nat) (a b : (zmod n).carrier)
    (h : ∀ c d, weilPairing n a b c d = (zmod n).one) :
    a = (zmod n).one ∧ b = (zmod n).one := by
  induction a using Quot.ind; rename_i a
  induction b using Quot.ind; rename_i b
  refine ⟨?_, ?_⟩
  · have h1 := h (Quot.mk (modCong n).rel 0) (Quot.mk (modCong n).rel 1)
    rw [weilPairing_mk, weil_int_nd1 a b] at h1
    exact h1
  · have h2 := h (Quot.mk (modCong n).rel 1) (Quot.mk (modCong n).rel 0)
    rw [weilPairing_mk, weil_int_nd2 a b] at h2
    -- h2 : class (−b) = (zmod n).one
    show Quot.mk (modCong n).rel b = (zmod n).one
    have hb : Quot.mk (modCong n).rel b
        = (zmod n).inv (Quot.mk (modCong n).rel (-b)) := by
      rw [weil_inv_mk, weil_int_negneg b]
    rw [hb, h2]
    show (zmod n).inv (zmod n).one = (zmod n).one
    exact (Grp.inv_eq_of_mul_eq_one (zmod n) ((zmod n).one_mul (zmod n).one)).symm

/-! ## M339F-6: 値は円分群 μ_n = ⟨ζ⟩ に着地 -/

/-- **値は μ_n に着地** — Weil ペアリングの値は円分群 μ_n=⟨ζ⟩（M322F `cycMuStd`、
    本物の巡回群 ℤ/n）の生成元 ζ の冪 ζ^k として表せる（e_n(P,Q)=ζ^k）。捻れ点の
    ペアリングが円分体 μ_n の元（1 の n 乗根）であるという IUT の中心対応。 -/
theorem weil_values_in_mu (n : Nat) (hn : 1 ≤ n) (a b c d : (zmod n).carrier) :
    ∃ k, (cycMuStd n hn).μ.pow (cycMuStd n hn).ζ k = weilPairing n a b c d := by
  refine ⟨(cycMuStd n hn).log (weilPairing n a b c d), ?_⟩
  exact (cycMuStd n hn).pow_log (weilPairing n a b c d)

/-! ## M339F-7: E_q[n] = ℤ/n × ℤ/n の点版 -/

/-- **E_q[n] の点** — Tate 一意化での n-捻れ点を座標 (zExp, qExp) で表す。すなわち
    P = ζ_n^{zExp}·Q^{qExp}（Q=q^{1/n}）。E_q[n] ≅ ℤ/n × ℤ/n の各成分。 -/
structure WeilTorsion (n : Nat) where
  /-- ζ_n 方向の指数 a。 -/
  zExp : (zmod n).carrier
  /-- Q = q^{1/n} 方向の指数 b。 -/
  qExp : (zmod n).carrier

/-- **E_q[n] の加法**（座標ごとの ℤ/n 加法）。 -/
def weilTorAdd (n : Nat) (P Q : WeilTorsion n) : WeilTorsion n :=
  ⟨(zmod n).mul P.zExp Q.zExp, (zmod n).mul P.qExp Q.qExp⟩

/-- **E_q[n] の零点** [0] = ζ^0·Q^0。 -/
def weilTorZero (n : Nat) : WeilTorsion n :=
  ⟨(zmod n).one, (zmod n).one⟩

/-- **点版 Weil ペアリング** e_n(P,Q) : E_q[n] × E_q[n] → μ_n。 -/
def weilPairingPt (n : Nat) (P Q : WeilTorsion n) : (zmod n).carrier :=
  weilPairing n P.zExp P.qExp Q.zExp Q.qExp

/-- **点版交代性** e_n(P,P) = 0。 -/
theorem weil_pt_alternating (n : Nat) (P : WeilTorsion n) :
    weilPairingPt n P P = (zmod n).one :=
  weil_alternating n P.zExp P.qExp

/-- **点版反対称性** e_n(P,Q) = −e_n(Q,P)。 -/
theorem weil_pt_antisymmetric (n : Nat) (P Q : WeilTorsion n) :
    weilPairingPt n P Q = (zmod n).inv (weilPairingPt n Q P) :=
  weil_antisymmetric n P.zExp P.qExp Q.zExp Q.qExp

/-- **点版第一引数双線形性** e_n(P+P', Q) = e_n(P,Q) + e_n(P',Q)。 -/
theorem weil_pt_bilinear_left (n : Nat) (P P' Q : WeilTorsion n) :
    weilPairingPt n (weilTorAdd n P P') Q
      = (zmod n).mul (weilPairingPt n P Q) (weilPairingPt n P' Q) :=
  weil_bilinear_left n P.zExp P'.zExp P.qExp P'.qExp Q.zExp Q.qExp

/-- **点版非退化性（本物・仮説不要）** — ∀Q, e_n(P,Q)=0 ⟹ P=0。 -/
theorem weil_pt_nondegenerate (n : Nat) (P : WeilTorsion n)
    (h : ∀ Q : WeilTorsion n, weilPairingPt n P Q = (zmod n).one) :
    P = weilTorZero n := by
  have hcoord := weil_nondegenerate n P.zExp P.qExp
    (fun c d => h ⟨c, d⟩)
  obtain ⟨h1, h2⟩ := hcoord
  cases P with
  | mk z q =>
    show WeilTorsion.mk z q = ⟨(zmod n).one, (zmod n).one⟩
    have hz : z = (zmod n).one := h1
    have hq : q = (zmod n).one := h2
    rw [hz, hq]

/-! ## M339F-8: capstone -/

/-- **Weil ペアリングデータ** — E_q[n]（ℤ/n×ℤ/n）上の e_n とその双線形性・交代性・
    反対称性を束ねる。捻れ点を円分体 μ_n に結ぶ交代双線形形式の総括。 -/
structure WeilPairingData (n : Nat) where
  /-- ペアリング本体 e_n。 -/
  pairing : (zmod n).carrier → (zmod n).carrier → (zmod n).carrier → (zmod n).carrier
    → (zmod n).carrier
  /-- pairing = weilPairing。 -/
  is_pairing : ∀ a b c d, pairing a b c d = weilPairing n a b c d
  /-- 交代性 e(P,P)=0。 -/
  alternating : ∀ a b, pairing a b a b = (zmod n).one
  /-- 第一引数双線形性。 -/
  bilinear_left : ∀ a a' b b' c d,
    pairing ((zmod n).mul a a') ((zmod n).mul b b') c d
      = (zmod n).mul (pairing a b c d) (pairing a' b' c d)
  /-- 反対称性 e(P,Q)=−e(Q,P)。 -/
  antisymmetric : ∀ a b c d, pairing a b c d = (zmod n).inv (pairing c d a b)

/-- **証人** — 任意の n に対し Weil ペアリングデータを本物で組む。 -/
def weilData (n : Nat) : WeilPairingData n where
  pairing := weilPairing n
  is_pairing := fun _ _ _ _ => rfl
  alternating := weil_alternating n
  bilinear_left := weil_bilinear_left n
  antisymmetric := weil_antisymmetric n

/-- **capstone — Weil ペアリングの存在**（任意の n で E_q[n] 上に交代双線形 e_n が組める）。 -/
theorem weil_exists (n : Nat) : Nonempty (WeilPairingData n) :=
  ⟨weilData n⟩

/-- **実例 n=3** — e_3(ζ, Q) = e_3((1,0),(0,1)) = ζ^{1·1−0·0} = ζ^1 = class 1
    （ζ=(1,0) と Q=q^{1/3}=(0,1) のペアリングが μ_3 の生成元 ζ）。 -/
theorem weil_example_n3 :
    weilPairing 3 (Quot.mk (modCong 3).rel 1) (Quot.mk (modCong 3).rel 0)
      (Quot.mk (modCong 3).rel 0) (Quot.mk (modCong 3).rel 1)
      = Quot.mk (modCong 3).rel 1 := by
  rw [weilPairing_mk, weil_int_nd1 1 0]

/-- **実例 n=3（交代性）** — e_3(P,P)=0（任意の P）。 -/
theorem weil_example_n3_alt (a b : (zmod 3).carrier) :
    weilPairing 3 a b a b = (zmod 3).one :=
  weil_alternating 3 a b

end IUT
