/-
  IUT/RingLocalization.lean — M290F（柱 A 先行建設: 一般可換環の
  乗法系による**本物の局所化** R_S = (R×S)/~ の初構成）

  ── 分類 **[実]**（本物の数学的実体の新規建設。M266F 分数体 Frac(D)
  の構成を「整域 + 分母≠0」から「一般可換環 + 乗法系 S」へ一般化）。

  **complete_pct 影響: 実 IUT のスキーム論的前提（構造層 O_X の茎・
  局所環・開基 D(f) 上の切断環）の土台となる**一般可換環の局所化 R_S**
  を本物構成。整域限定の Frac(D)（M266F）を乗法系 S へ一般化し、
  零因子を許す一般環でも成立する局所化の同値関係
  (r,s)~(r',s') ⟺ ∃t∈S, t·(r·s' − r'·s)=0 の**推移律**、
  局所化環 R_S の**可換環公理全て**、普遍写像 R→R_S の**環準同型性**、
  **S の像の可逆性**を完全証明（sorry 無し・新規 choice 無し）。
  実例として R[1/f]（f のべき乗法系）を実体化（開基 D(f) の切断環の前提）。

  * M290F-1 `ringLocMulSet` — 乗法系（1∈S・積で閉じる）
  * M290F-2 `ringLocPre` / `ringLocRel` — 前分数（分母∈S）と
    局所化同値関係 ∃t∈S, t·(r·s'−r'·s)=0（`ringLocRel_iff_sub` で
    減算形と同値、内部は等式形 t·(r·s')=t·(r'·s)）。反射・対称・
    **推移**（witness t·u·s' の存在と乗法系の閉性が推移律の核）を完全証明
  * M290F-3 `ringLocAdd/Neg/Mul/Zero/One` と各演算の
    **well-definedness**（`ringLocRel_add_left/right`・`_neg`・
    `_mul_left/right`：witness 演算で関係を保つ）
  * M290F-4 `ringLocRing` — **R_S は可換環**（結合・交換・分配・零元・
    反元。左分配は分母スケール経由の Quot.sound、他は代表の外延等式）
  * M290F-5 `ringLocMap` / `ringLoc_map_isHom` — 普遍写像 r↦r/1 は
    **環準同型**（加法・乗法・1 保存）
  * M290F-6 `ringLoc_unit_of_S` — s∈S ⟹ r/1 の像は R_S で**単元**
    （逆元 1/s の witness 形）
  * M290F-7 `ringLocData` / `ringLoc_exists` / `ringLoc_universal` —
    総括レコード（R・S・R_S・普遍写像・S 可逆性）と存在・普遍性定理
  * M290F-8 `ringLocPow` / `ringLocPowers` / `ringLocRf` — 実例
    R[1/f]（S={1,f,f²,…}）。f-べきの積閉性 `ringLocPow_add` を証明

  **正直な限定（必守申告）**:
  1. 局所化の**完全な普遍性**（「S を単元へ送る任意の環準同型 R→A が
     R_S を一意に経由する」の存在・一意の factor 化）は本モジュールでは
     **「普遍写像が存在し S を可逆にする」まで**を完全証明し、一意
     factor 化 φ: R_S→A の構成は後続（M290F は局所化環そのものの構成と
     その環準同型的普遍写像・S 可逆性に限定）。
  2. 逆元は R_S 上で**代表 witness 形**（s∈S に対し 1/s を明示）。
     全域 inv は台の等号判定を要し一般環では非可判定のため採らない
     （局所化は逆を"付加"する構成なので witness 形が本来の姿）。
  3. 素イデアル P での局所化 R_P（S=R∖P）は M289F 素イデアルとの
     接続を要する後続。本モジュールは一般乗法系と f-べき R[1/f] まで。

  全て選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。
-/
import IUT.FractionField

namespace IUT

/-! ## M290F-0: 可換環の一般補題（AC 並べ替えの追加分） -/

/-- 左交換律 a·(b·c) = b·(a·c)（可換環の積に対する基本並べ替え）。 -/
theorem ringLoc_mlc (R : CRing) (a b c : R.carrier) :
    R.mul a (R.mul b c) = R.mul b (R.mul a c) := by
  rw [← R.mul_assoc, R.mul_comm a b, R.mul_assoc]

/-- a·(−b) = −(a·b)（右側の負号の引き出し）。 -/
theorem ringLoc_mul_neg (R : CRing) (a b : R.carrier) :
    R.mul a (R.neg b) = R.neg (R.mul a b) := by
  rw [R.mul_comm a (R.neg b), cring_neg_mul, R.mul_comm b a]

/-- 5 因子並べ替え P1: (t·(u·s'))·(a·s'') = (u·s'')·(t·(a·s'))。
    推移律の第 1 段（正準右結合形 t·(u·(s'·(a·s''))) 経由）。 -/
theorem ringLoc_perm1 (R : CRing) (t u s' a s'' : R.carrier) :
    R.mul (R.mul t (R.mul u s')) (R.mul a s'')
      = R.mul (R.mul u s'') (R.mul t (R.mul a s')) :=
  calc R.mul (R.mul t (R.mul u s')) (R.mul a s'')
      = R.mul t (R.mul (R.mul u s') (R.mul a s'')) := by
        rw [R.mul_assoc t (R.mul u s') (R.mul a s'')]
    _ = R.mul t (R.mul u (R.mul s' (R.mul a s''))) := by rw [R.mul_assoc u s' (R.mul a s'')]
    _ = R.mul t (R.mul u (R.mul a (R.mul s' s''))) := by rw [ringLoc_mlc R s' a s'']
    _ = R.mul t (R.mul u (R.mul a (R.mul s'' s'))) := by rw [R.mul_comm s' s'']
    _ = R.mul t (R.mul u (R.mul s'' (R.mul a s'))) := by rw [ringLoc_mlc R a s'' s']
    _ = R.mul u (R.mul t (R.mul s'' (R.mul a s'))) := by
        rw [ringLoc_mlc R t u (R.mul s'' (R.mul a s'))]
    _ = R.mul u (R.mul s'' (R.mul t (R.mul a s'))) := by rw [ringLoc_mlc R t s'' (R.mul a s')]
    _ = R.mul (R.mul u s'') (R.mul t (R.mul a s')) := by
        rw [R.mul_assoc u s'' (R.mul t (R.mul a s'))]

/-- 5 因子並べ替え P2: (u·s'')·(t·(b·s)) = (t·s)·(u·(b·s''))。推移律の第 2 段。 -/
theorem ringLoc_perm2 (R : CRing) (u s'' t b s : R.carrier) :
    R.mul (R.mul u s'') (R.mul t (R.mul b s))
      = R.mul (R.mul t s) (R.mul u (R.mul b s'')) :=
  calc R.mul (R.mul u s'') (R.mul t (R.mul b s))
      = R.mul u (R.mul s'' (R.mul t (R.mul b s))) := by
        rw [R.mul_assoc u s'' (R.mul t (R.mul b s))]
    _ = R.mul u (R.mul t (R.mul s'' (R.mul b s))) := by rw [ringLoc_mlc R s'' t (R.mul b s)]
    _ = R.mul t (R.mul u (R.mul s'' (R.mul b s))) := by
        rw [ringLoc_mlc R u t (R.mul s'' (R.mul b s))]
    _ = R.mul t (R.mul u (R.mul b (R.mul s'' s))) := by rw [ringLoc_mlc R s'' b s]
    _ = R.mul t (R.mul u (R.mul b (R.mul s s''))) := by rw [R.mul_comm s'' s]
    _ = R.mul t (R.mul u (R.mul s (R.mul b s''))) := by rw [← ringLoc_mlc R s b s'']
    _ = R.mul t (R.mul s (R.mul u (R.mul b s''))) := by rw [← ringLoc_mlc R s u (R.mul b s'')]
    _ = R.mul (R.mul t s) (R.mul u (R.mul b s'')) := by
        rw [← R.mul_assoc t s (R.mul u (R.mul b s''))]

/-- 5 因子並べ替え P3: (t·s)·(u·(c·s')) = (t·(u·s'))·(c·s)。推移律の第 3 段。 -/
theorem ringLoc_perm3 (R : CRing) (t s u c s' : R.carrier) :
    R.mul (R.mul t s) (R.mul u (R.mul c s'))
      = R.mul (R.mul t (R.mul u s')) (R.mul c s) :=
  calc R.mul (R.mul t s) (R.mul u (R.mul c s'))
      = R.mul t (R.mul s (R.mul u (R.mul c s'))) := by
        rw [R.mul_assoc t s (R.mul u (R.mul c s'))]
    _ = R.mul t (R.mul u (R.mul s (R.mul c s'))) := by rw [ringLoc_mlc R s u (R.mul c s')]
    _ = R.mul t (R.mul u (R.mul c (R.mul s s'))) := by rw [ringLoc_mlc R s c s']
    _ = R.mul t (R.mul u (R.mul c (R.mul s' s))) := by rw [R.mul_comm s s']
    _ = R.mul t (R.mul u (R.mul s' (R.mul c s))) := by rw [← ringLoc_mlc R s' c s]
    _ = R.mul t (R.mul (R.mul u s') (R.mul c s)) := by rw [← R.mul_assoc u s' (R.mul c s)]
    _ = R.mul (R.mul t (R.mul u s')) (R.mul c s) := by
        rw [← R.mul_assoc t (R.mul u s') (R.mul c s)]

/-! ## M290F-1: 乗法系 -/

/-- **M290F-1: 乗法系** — 部分集合 S ⊆ R で 1∈S かつ積で閉じる
    （局所化で可逆にする元の集まり）。 -/
structure ringLocMulSet (R : CRing) where
  /-- 台の述語。 -/
  set : R.carrier → Prop
  /-- 1 ∈ S。 -/
  one_mem : set R.one
  /-- 積で閉じる。 -/
  mul_mem : ∀ a b : R.carrier, set a → set b → set (R.mul a b)

/-! ## M290F-2: 前分数と局所化同値関係 -/

/-- **M290F-2a: 前分数**（分子任意・分母 ∈ S）。 -/
structure ringLocPre (R : CRing) (S : ringLocMulSet R) where
  /-- 分子。 -/
  num : R.carrier
  /-- 分母。 -/
  den : R.carrier
  /-- 分母は乗法系に属す。 -/
  den_mem : S.set den

/-- 前分数の外延性（den_mem は Prop なので proof irrelevance）。 -/
theorem ringLocPre_ext {R : CRing} {S : ringLocMulSet R} :
    ∀ {x y : ringLocPre R S}, x.num = y.num → x.den = y.den → x = y
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl => rfl

/-- **M290F-2b: 局所化同値関係**（等式形）
    (r,s)~(r',s') ⟺ ∃t∈S, t·(r·s') = t·(r'·s)。
    一般環では零因子がありうるため witness t が必須。 -/
def ringLocRel {R : CRing} (S : ringLocMulSet R) (x y : ringLocPre R S) : Prop :=
  ∃ t : R.carrier, S.set t ∧
    R.mul t (R.mul x.num y.den) = R.mul t (R.mul y.num x.den)

/-- **M290F-2c: 減算形との同値**（正直な地図: 数学の標準形
    ∃t∈S, t·(r·s' − r'·s)=0 と等式形が一致することを本物で証明）。 -/
theorem ringLocRel_iff_sub {R : CRing} (S : ringLocMulSet R) (x y : ringLocPre R S) :
    ringLocRel S x y ↔ ∃ t : R.carrier, S.set t ∧
      R.mul t (R.add (R.mul x.num y.den) (R.neg (R.mul y.num x.den))) = R.zero := by
  constructor
  · intro h
    obtain ⟨t, ht, e⟩ := h
    refine ⟨t, ht, ?_⟩
    rw [R.left_distrib t (R.mul x.num y.den) (R.neg (R.mul y.num x.den)),
      ringLoc_mul_neg R t (R.mul y.num x.den), e, cring_add_neg]
  · intro h
    obtain ⟨t, ht, e⟩ := h
    refine ⟨t, ht, ?_⟩
    apply cring_eq_of_sub_zero R
    rw [← ringLoc_mul_neg R t (R.mul y.num x.den),
      ← R.left_distrib t (R.mul x.num y.den) (R.neg (R.mul y.num x.den))]
    exact e

/-- 反射律（witness 1）。 -/
theorem ringLocRel_refl {R : CRing} {S : ringLocMulSet R} (x : ringLocPre R S) :
    ringLocRel S x x :=
  ⟨R.one, S.one_mem, rfl⟩

/-- 対称律（同一 witness）。 -/
theorem ringLocRel_symm {R : CRing} {S : ringLocMulSet R} {x y : ringLocPre R S}
    (h : ringLocRel S x y) : ringLocRel S y x := by
  obtain ⟨t, ht, e⟩ := h
  exact ⟨t, ht, e.symm⟩

/-- **M290F-2d: 推移律** — witness w = t·(u·y.den)（∈ S は乗法系の閉性）
    で t·(a·s')=t·(b·s) と u·(b·s'')=u·(c·s') を貼り合わせる。 -/
theorem ringLocRel_trans {R : CRing} {S : ringLocMulSet R} {x y z : ringLocPre R S}
    (h1 : ringLocRel S x y) (h2 : ringLocRel S y z) : ringLocRel S x z := by
  obtain ⟨t, ht, e1⟩ := h1
  obtain ⟨u, hu, e2⟩ := h2
  refine ⟨R.mul t (R.mul u y.den),
    S.mul_mem t (R.mul u y.den) ht (S.mul_mem u y.den hu y.den_mem), ?_⟩
  calc R.mul (R.mul t (R.mul u y.den)) (R.mul x.num z.den)
      = R.mul (R.mul u z.den) (R.mul t (R.mul x.num y.den)) :=
        ringLoc_perm1 R t u y.den x.num z.den
    _ = R.mul (R.mul u z.den) (R.mul t (R.mul y.num x.den)) := by rw [e1]
    _ = R.mul (R.mul t x.den) (R.mul u (R.mul y.num z.den)) :=
        ringLoc_perm2 R u z.den t y.num x.den
    _ = R.mul (R.mul t x.den) (R.mul u (R.mul z.num y.den)) := by rw [e2]
    _ = R.mul (R.mul t (R.mul u y.den)) (R.mul z.num x.den) :=
        ringLoc_perm3 R t x.den u z.num y.den

/-! ## M290F-3: 代表演算と well-definedness -/

/-- 加法の代表 (r,s)+(r',s') = (rs'+r's, ss')。 -/
def ringLocAdd {R : CRing} {S : ringLocMulSet R} (x y : ringLocPre R S) : ringLocPre R S :=
  ⟨R.add (R.mul x.num y.den) (R.mul y.num x.den), R.mul x.den y.den,
    S.mul_mem x.den y.den x.den_mem y.den_mem⟩

/-- 反元の代表 (−r, s)。 -/
def ringLocNeg {R : CRing} {S : ringLocMulSet R} (x : ringLocPre R S) : ringLocPre R S :=
  ⟨R.neg x.num, x.den, x.den_mem⟩

/-- 乗法の代表 (r,s)·(r',s') = (rr', ss')。 -/
def ringLocMul {R : CRing} {S : ringLocMulSet R} (x y : ringLocPre R S) : ringLocPre R S :=
  ⟨R.mul x.num y.num, R.mul x.den y.den,
    S.mul_mem x.den y.den x.den_mem y.den_mem⟩

/-- 0 の代表 0/1。 -/
def ringLocZero {R : CRing} {S : ringLocMulSet R} : ringLocPre R S :=
  ⟨R.zero, R.one, S.one_mem⟩

/-- 1 の代表 1/1。 -/
def ringLocOne {R : CRing} {S : ringLocMulSet R} : ringLocPre R S :=
  ⟨R.one, R.one, S.one_mem⟩

/-- S に属す c によるスケール (c·r, c·s)（左分配の Quot.sound 用）。 -/
def ringLocScale {R : CRing} {S : ringLocMulSet R} (c : R.carrier) (hc : S.set c)
    (x : ringLocPre R S) : ringLocPre R S :=
  ⟨R.mul c x.num, R.mul c x.den, S.mul_mem c x.den hc x.den_mem⟩

/-- スケールは関係を保つ（witness 1、両辺 c·(r·s)）。 -/
theorem ringLocRel_scale {R : CRing} {S : ringLocMulSet R} (c : R.carrier) (hc : S.set c)
    (x : ringLocPre R S) : ringLocRel S (ringLocScale c hc x) x := by
  refine ⟨R.one, S.one_mem, ?_⟩
  show R.mul R.one (R.mul (R.mul c x.num) x.den)
    = R.mul R.one (R.mul x.num (R.mul c x.den))
  rw [R.one_mul, R.one_mul, R.mul_assoc c x.num x.den, ringLoc_mlc R x.num c x.den]

/-- 乗法は第 2 引数の関係を保つ（witness t）。 -/
theorem ringLocRel_mul_left {R : CRing} {S : ringLocMulSet R} (x : ringLocPre R S)
    {y y' : ringLocPre R S} (h : ringLocRel S y y') :
    ringLocRel S (ringLocMul x y) (ringLocMul x y') := by
  obtain ⟨t, ht, e⟩ := h
  refine ⟨t, ht, ?_⟩
  show R.mul t (R.mul (R.mul x.num y.num) (R.mul x.den y'.den))
    = R.mul t (R.mul (R.mul x.num y'.num) (R.mul x.den y.den))
  rw [cring_mul_mul_swap' R x.num y.num x.den y'.den,
    ringLoc_mlc R t (R.mul x.num x.den) (R.mul y.num y'.den), e,
    ← ringLoc_mlc R t (R.mul x.num x.den) (R.mul y'.num y.den),
    cring_mul_mul_swap' R x.num x.den y'.num y.den]

/-- 乗法は第 1 引数の関係を保つ（witness t）。 -/
theorem ringLocRel_mul_right {R : CRing} {S : ringLocMulSet R} (y : ringLocPre R S)
    {x x' : ringLocPre R S} (h : ringLocRel S x x') :
    ringLocRel S (ringLocMul x y) (ringLocMul x' y) := by
  obtain ⟨t, ht, e⟩ := h
  refine ⟨t, ht, ?_⟩
  show R.mul t (R.mul (R.mul x.num y.num) (R.mul x'.den y.den))
    = R.mul t (R.mul (R.mul x'.num y.num) (R.mul x.den y.den))
  rw [cring_mul_mul_swap' R x.num y.num x'.den y.den,
    ← R.mul_assoc t (R.mul x.num x'.den) (R.mul y.num y.den), e,
    R.mul_assoc t (R.mul x'.num x.den) (R.mul y.num y.den),
    cring_mul_mul_swap' R x'.num x.den y.num y.den]

/-- 反元は関係を保つ（witness t）。 -/
theorem ringLocRel_neg {R : CRing} {S : ringLocMulSet R} {x x' : ringLocPre R S}
    (h : ringLocRel S x x') : ringLocRel S (ringLocNeg x) (ringLocNeg x') := by
  obtain ⟨t, ht, e⟩ := h
  refine ⟨t, ht, ?_⟩
  show R.mul t (R.mul (R.neg x.num) x'.den) = R.mul t (R.mul (R.neg x'.num) x.den)
  rw [cring_neg_mul, ringLoc_mul_neg R t (R.mul x.num x'.den), e,
    ← ringLoc_mul_neg R t (R.mul x'.num x.den), ← cring_neg_mul]

/-- 加法は第 2 引数の関係を保つ（witness t、分配 + 項別）。 -/
theorem ringLocRel_add_left {R : CRing} {S : ringLocMulSet R} (x : ringLocPre R S)
    {y y' : ringLocPre R S} (h : ringLocRel S y y') :
    ringLocRel S (ringLocAdd x y) (ringLocAdd x y') := by
  obtain ⟨t, ht, e⟩ := h
  refine ⟨t, ht, ?_⟩
  show R.mul t (R.mul (R.add (R.mul x.num y.den) (R.mul y.num x.den)) (R.mul x.den y'.den))
    = R.mul t (R.mul (R.add (R.mul x.num y'.den) (R.mul y'.num x.den)) (R.mul x.den y.den))
  have hA : R.mul t (R.mul (R.mul x.num y.den) (R.mul x.den y'.den))
      = R.mul t (R.mul (R.mul x.num y'.den) (R.mul x.den y.den)) := by
    apply congrArg (R.mul t)
    rw [cring_mul_mul_swap' R x.num y.den x.den y'.den,
      cring_mul_mul_swap' R x.num y'.den x.den y.den, R.mul_comm y.den y'.den]
  have hB : R.mul t (R.mul (R.mul y.num x.den) (R.mul x.den y'.den))
      = R.mul t (R.mul (R.mul y'.num x.den) (R.mul x.den y.den)) := by
    rw [cring_mul_mul_swap R y.num x.den x.den y'.den,
      ← R.mul_assoc t (R.mul y.num y'.den) (R.mul x.den x.den), e,
      R.mul_assoc t (R.mul y'.num y.den) (R.mul x.den x.den),
      cring_mul_mul_swap R y'.num y.den x.den x.den]
  rw [R.right_distrib, R.right_distrib, R.left_distrib t, R.left_distrib t, hA, hB]

/-- 加法は第 1 引数の関係を保つ（witness t、分配 + 項別）。 -/
theorem ringLocRel_add_right {R : CRing} {S : ringLocMulSet R} (y : ringLocPre R S)
    {x x' : ringLocPre R S} (h : ringLocRel S x x') :
    ringLocRel S (ringLocAdd x y) (ringLocAdd x' y) := by
  obtain ⟨t, ht, e⟩ := h
  refine ⟨t, ht, ?_⟩
  show R.mul t (R.mul (R.add (R.mul x.num y.den) (R.mul y.num x.den)) (R.mul x'.den y.den))
    = R.mul t (R.mul (R.add (R.mul x'.num y.den) (R.mul y.num x'.den)) (R.mul x.den y.den))
  have hA : R.mul t (R.mul (R.mul x.num y.den) (R.mul x'.den y.den))
      = R.mul t (R.mul (R.mul x'.num y.den) (R.mul x.den y.den)) := by
    rw [cring_mul_mul_swap' R x.num y.den x'.den y.den,
      ← R.mul_assoc t (R.mul x.num x'.den) (R.mul y.den y.den), e,
      R.mul_assoc t (R.mul x'.num x.den) (R.mul y.den y.den),
      cring_mul_mul_swap' R x'.num x.den y.den y.den]
  have hB : R.mul t (R.mul (R.mul y.num x.den) (R.mul x'.den y.den))
      = R.mul t (R.mul (R.mul y.num x'.den) (R.mul x.den y.den)) := by
    apply congrArg (R.mul t)
    exact cring_mul_mul_swap' R y.num x.den x'.den y.den
  rw [R.right_distrib, R.right_distrib, R.left_distrib t, R.left_distrib t, hA, hB]

/-! ## M290F-4: Quot 商 R_S と可換環構造 -/

/-- **M290F-4a: R_S の台** = ringLocPre / 局所化関係。 -/
def ringLocCarrier (R : CRing) (S : ringLocMulSet R) := Quot (ringLocRel S)

/-- 加法（二重 Quot.lift）。 -/
def ringLocQAdd {R : CRing} {S : ringLocMulSet R}
    (a b : ringLocCarrier R S) : ringLocCarrier R S :=
  Quot.lift
    (fun x => Quot.lift
      (fun y => Quot.mk (ringLocRel S) (ringLocAdd x y))
      (fun _ _ hy => Quot.sound (ringLocRel_add_left x hy)) b)
    (fun _ _ hx => by
      induction b using Quot.ind
      rename_i y
      exact Quot.sound (ringLocRel_add_right y hx)) a

/-- 反元。 -/
def ringLocQNeg {R : CRing} {S : ringLocMulSet R}
    (a : ringLocCarrier R S) : ringLocCarrier R S :=
  Quot.lift (fun x => Quot.mk (ringLocRel S) (ringLocNeg x))
    (fun _ _ hx => Quot.sound (ringLocRel_neg hx)) a

/-- 乗法（二重 Quot.lift）。 -/
def ringLocQMul {R : CRing} {S : ringLocMulSet R}
    (a b : ringLocCarrier R S) : ringLocCarrier R S :=
  Quot.lift
    (fun x => Quot.lift
      (fun y => Quot.mk (ringLocRel S) (ringLocMul x y))
      (fun _ _ hy => Quot.sound (ringLocRel_mul_left x hy)) b)
    (fun _ _ hx => by
      induction b using Quot.ind
      rename_i y
      exact Quot.sound (ringLocRel_mul_right y hx)) a

/-- 加法の結合律（代表の外延等式、分母は mul_assoc）。 -/
theorem ringLocAdd_assoc {R : CRing} {S : ringLocMulSet R} (x y z : ringLocPre R S) :
    ringLocAdd (ringLocAdd x y) z = ringLocAdd x (ringLocAdd y z) := by
  apply ringLocPre_ext
  · show R.add (R.mul (R.add (R.mul x.num y.den) (R.mul y.num x.den)) z.den)
        (R.mul z.num (R.mul x.den y.den))
      = R.add (R.mul x.num (R.mul y.den z.den))
        (R.mul (R.add (R.mul y.num z.den) (R.mul z.num y.den)) x.den)
    rw [R.right_distrib, R.right_distrib, R.add_assoc,
      R.mul_assoc x.num y.den z.den,
      cring_mul_right_swap R y.num x.den z.den,
      cring_mul_right_swap R z.num y.den x.den,
      R.mul_assoc z.num x.den y.den]
  · show R.mul (R.mul x.den y.den) z.den = R.mul x.den (R.mul y.den z.den)
    exact R.mul_assoc x.den y.den z.den

/-- 加法の可換律。 -/
theorem ringLocAdd_comm {R : CRing} {S : ringLocMulSet R} (x y : ringLocPre R S) :
    ringLocAdd x y = ringLocAdd y x := by
  apply ringLocPre_ext
  · show R.add (R.mul x.num y.den) (R.mul y.num x.den)
      = R.add (R.mul y.num x.den) (R.mul x.num y.den)
    exact R.add_comm _ _
  · exact R.mul_comm x.den y.den

/-- 左零元。 -/
theorem ringLocZero_add {R : CRing} {S : ringLocMulSet R} (x : ringLocPre R S) :
    ringLocAdd ringLocZero x = x := by
  apply ringLocPre_ext
  · show R.add (R.mul R.zero x.den) (R.mul x.num R.one) = x.num
    rw [cring_zero_mul, cring_mul_one, R.zero_add]
  · show R.mul R.one x.den = x.den
    exact R.one_mul x.den

/-- 左反元（分母 s² ≠ 1 のため Quot.sound 必須、witness 1）。 -/
theorem ringLocNeg_add_rel {R : CRing} {S : ringLocMulSet R} (x : ringLocPre R S) :
    ringLocRel S (ringLocAdd (ringLocNeg x) x) ringLocZero := by
  refine ⟨R.one, S.one_mem, ?_⟩
  show R.mul R.one (R.mul (R.add (R.mul (R.neg x.num) x.den) (R.mul x.num x.den)) R.one)
    = R.mul R.one (R.mul R.zero (R.mul x.den x.den))
  rw [R.one_mul, R.one_mul, cring_mul_one, cring_zero_mul, cring_neg_mul, R.neg_add]

/-- 乗法の結合律。 -/
theorem ringLocMul_assoc {R : CRing} {S : ringLocMulSet R} (x y z : ringLocPre R S) :
    ringLocMul (ringLocMul x y) z = ringLocMul x (ringLocMul y z) := by
  apply ringLocPre_ext
  · exact R.mul_assoc x.num y.num z.num
  · exact R.mul_assoc x.den y.den z.den

/-- 左単位元。 -/
theorem ringLocOne_mul {R : CRing} {S : ringLocMulSet R} (x : ringLocPre R S) :
    ringLocMul ringLocOne x = x := by
  apply ringLocPre_ext
  · exact R.one_mul x.num
  · exact R.one_mul x.den

/-- 乗法の可換律。 -/
theorem ringLocMul_comm {R : CRing} {S : ringLocMulSet R} (x y : ringLocPre R S) :
    ringLocMul x y = ringLocMul y x := by
  apply ringLocPre_ext
  · exact R.mul_comm x.num y.num
  · exact R.mul_comm x.den y.den

/-- 左分配（分母が真に異なるため「x.den 倍スケール」の外延等式 +
    ringLocRel_scale の Quot.sound 経由）。 -/
theorem ringLocLeftDistrib_scale {R : CRing} {S : ringLocMulSet R} (x y z : ringLocPre R S) :
    ringLocAdd (ringLocMul x y) (ringLocMul x z)
      = ringLocScale x.den x.den_mem (ringLocMul x (ringLocAdd y z)) := by
  apply ringLocPre_ext
  · show R.add (R.mul (R.mul x.num y.num) (R.mul x.den z.den))
        (R.mul (R.mul x.num z.num) (R.mul x.den y.den))
      = R.mul x.den (R.mul x.num
        (R.add (R.mul y.num z.den) (R.mul z.num y.den)))
    rw [R.left_distrib x.num, R.left_distrib x.den,
      cring_mul_mul_swap' R x.num y.num x.den z.den,
      cring_mul_mul_swap' R x.num z.num x.den y.den,
      ← R.mul_assoc x.den x.num (R.mul y.num z.den),
      ← R.mul_assoc x.den x.num (R.mul z.num y.den),
      R.mul_comm x.den x.num]
  · show R.mul (R.mul x.den y.den) (R.mul x.den z.den)
      = R.mul x.den (R.mul x.den (R.mul y.den z.den))
    rw [cring_mul_mul_swap' R x.den y.den x.den z.den, R.mul_assoc]

/-- **定理 (M290F-4b): R_S は可換環**（一般乗法系による本物の局所化環）。 -/
def ringLocRing (R : CRing) (S : ringLocMulSet R) : CRing where
  carrier := ringLocCarrier R S
  add := ringLocQAdd
  zero := Quot.mk (ringLocRel S) ringLocZero
  neg := ringLocQNeg
  mul := ringLocQMul
  one := Quot.mk (ringLocRel S) ringLocOne
  add_assoc := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    exact congrArg (Quot.mk (ringLocRel S)) (ringLocAdd_assoc x y z)
  zero_add := by
    intro a
    induction a using Quot.ind; rename_i x
    exact congrArg (Quot.mk (ringLocRel S)) (ringLocZero_add x)
  neg_add := by
    intro a
    induction a using Quot.ind; rename_i x
    exact Quot.sound (ringLocNeg_add_rel x)
  add_comm := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    exact congrArg (Quot.mk (ringLocRel S)) (ringLocAdd_comm x y)
  mul_assoc := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    exact congrArg (Quot.mk (ringLocRel S)) (ringLocMul_assoc x y z)
  one_mul := by
    intro a
    induction a using Quot.ind; rename_i x
    exact congrArg (Quot.mk (ringLocRel S)) (ringLocOne_mul x)
  mul_comm := by
    intro a b
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    exact congrArg (Quot.mk (ringLocRel S)) (ringLocMul_comm x y)
  left_distrib := by
    intro a b c
    induction a using Quot.ind; rename_i x
    induction b using Quot.ind; rename_i y
    induction c using Quot.ind; rename_i z
    show Quot.mk (ringLocRel S) (ringLocMul x (ringLocAdd y z))
      = Quot.mk (ringLocRel S) (ringLocAdd (ringLocMul x y) (ringLocMul x z))
    rw [ringLocLeftDistrib_scale x y z]
    exact (Quot.sound
      (ringLocRel_scale x.den x.den_mem (ringLocMul x (ringLocAdd y z)))).symm

/-! ## M290F-5: 普遍写像 R → R_S -/

/-- 元 a の代表 a/1。 -/
def ringLocOfElem {R : CRing} {S : ringLocMulSet R} (a : R.carrier) : ringLocPre R S :=
  ⟨a, R.one, S.one_mem⟩

/-- **M290F-5: 普遍写像 R → R_S は環準同型**（a ↦ a/1）。 -/
def ringLocMap (R : CRing) (S : ringLocMulSet R) : RingHom R (ringLocRing R S) where
  map := fun a => Quot.mk (ringLocRel S) (ringLocOfElem a)
  map_add := fun a b => by
    show Quot.mk (ringLocRel S) (ringLocOfElem (R.add a b))
      = Quot.mk (ringLocRel S) (ringLocAdd (ringLocOfElem a) (ringLocOfElem b))
    apply congrArg (Quot.mk (ringLocRel S))
    apply ringLocPre_ext
    · show R.add a b = R.add (R.mul a R.one) (R.mul b R.one)
      rw [cring_mul_one, cring_mul_one]
    · show R.one = R.mul R.one R.one
      rw [R.one_mul]
  map_mul := fun a b => by
    show Quot.mk (ringLocRel S) (ringLocOfElem (R.mul a b))
      = Quot.mk (ringLocRel S) (ringLocMul (ringLocOfElem a) (ringLocOfElem b))
    apply congrArg (Quot.mk (ringLocRel S))
    apply ringLocPre_ext
    · exact rfl
    · show R.one = R.mul R.one R.one
      rw [R.one_mul]
  map_one := rfl

/-- 普遍写像の名前付き別名（環準同型であることの明示）。 -/
def ringLoc_map_isHom (R : CRing) (S : ringLocMulSet R) : RingHom R (ringLocRing R S) :=
  ringLocMap R S

/-! ## M290F-6: S の像は R_S で可逆 -/

/-- **定理 (M290F-6): S 可逆性** — s∈S なら ringLocMap s = s/1 は
    R_S の単元（逆元 1/s、witness 形）。 -/
theorem ringLoc_unit_of_S (R : CRing) (S : ringLocMulSet R) (s : R.carrier) (hs : S.set s) :
    ∃ inv : (ringLocRing R S).carrier,
      (ringLocRing R S).mul ((ringLocMap R S).map s) inv = (ringLocRing R S).one := by
  refine ⟨Quot.mk (ringLocRel S) ⟨R.one, s, hs⟩, ?_⟩
  show Quot.mk (ringLocRel S)
      (ringLocMul (ringLocOfElem s) ⟨R.one, s, hs⟩)
    = Quot.mk (ringLocRel S) ringLocOne
  apply Quot.sound
  refine ⟨R.one, S.one_mem, ?_⟩
  show R.mul R.one (R.mul (R.mul s R.one) R.one)
    = R.mul R.one (R.mul R.one (R.mul R.one s))
  rw [R.one_mul, R.one_mul, cring_mul_one, cring_mul_one, R.one_mul, R.one_mul]

/-! ## M290F-7: 総括レコードと存在・普遍性 -/

/-- **M290F-7a: 局所化データ** — R・乗法系 S・局所化環 R_S・
    環準同型な普遍写像・S の像の可逆性の束。 -/
structure ringLocData (R : CRing) (S : ringLocMulSet R) where
  /-- 局所化環 R_S。 -/
  ring : CRing
  /-- 環準同型な普遍写像 R → R_S。 -/
  map : RingHom R ring
  /-- S の像は R_S で可逆（witness 形）。 -/
  unit_of_S : ∀ s : R.carrier, S.set s →
    ∃ inv : ring.carrier, ring.mul (map.map s) inv = ring.one

/-- **M290F-7b: witness**（全フィールドが本モジュールの完全証明）。 -/
def ringLocData_mk (R : CRing) (S : ringLocMulSet R) : ringLocData R S where
  ring := ringLocRing R S
  map := ringLocMap R S
  unit_of_S := ringLoc_unit_of_S R S

/-- **見出し定理 (M290F-7c)**: 任意の可換環 R と乗法系 S に対し
    局所化データが存在。 -/
theorem ringLoc_exists (R : CRing) (S : ringLocMulSet R) : Nonempty (ringLocData R S) :=
  ⟨ringLocData_mk R S⟩

/-- **M290F-7d: 普遍性（部分形）** — 普遍写像は環準同型であり
    S を単元に送る。完全な一意 factor 化は後続（正直申告 1）。 -/
theorem ringLoc_universal (R : CRing) (S : ringLocMulSet R) :
    ∀ s : R.carrier, S.set s →
      ∃ inv : (ringLocRing R S).carrier,
        (ringLocRing R S).mul ((ringLocMap R S).map s) inv = (ringLocRing R S).one :=
  ringLoc_unit_of_S R S

/-! ## M290F-8: 実例 R[1/f]（開基 D(f) 上の切断環の前提） -/

/-- f のべき f^n（構造層 O(D(f)) の分母集合）。 -/
def ringLocPow (R : CRing) (f : R.carrier) : Nat → R.carrier
  | 0 => R.one
  | n + 1 => R.mul f (ringLocPow R f n)

/-- f-べきの指数法則 f^(m+n) = f^m · f^n（積閉性の核）。 -/
theorem ringLocPow_add (R : CRing) (f : R.carrier) (m n : Nat) :
    ringLocPow R f (m + n) = R.mul (ringLocPow R f m) (ringLocPow R f n) := by
  induction n with
  | zero =>
    show ringLocPow R f m = R.mul (ringLocPow R f m) R.one
    rw [cring_mul_one]
  | succ k ih =>
    show R.mul f (ringLocPow R f (m + k)) = R.mul (ringLocPow R f m) (R.mul f (ringLocPow R f k))
    rw [ih, ringLoc_mlc R (ringLocPow R f m) f (ringLocPow R f k)]

/-- **M290F-8a: f-べき乗法系** S = {1, f, f², …}。 -/
def ringLocPowers (R : CRing) (f : R.carrier) : ringLocMulSet R where
  set := fun a => ∃ n : Nat, a = ringLocPow R f n
  one_mem := ⟨0, rfl⟩
  mul_mem := fun a b => by
    intro ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    rw [hm, hn, ringLocPow_add]

/-- **M290F-8b: R[1/f]** — f のべき乗法系による局所化（開基 D(f) の
    切断環 O_X(D(f)) の代数的前提）。 -/
def ringLocRf (R : CRing) (f : R.carrier) : CRing :=
  ringLocRing R (ringLocPowers R f)

/-- **見出し定理 (M290F-8c)**: R[1/f] は本物の局所化データを持つ
    （f の像は R[1/f] で可逆）。 -/
theorem ringLocRf_data (R : CRing) (f : R.carrier) :
    Nonempty (ringLocData R (ringLocPowers R f)) :=
  ringLoc_exists R (ringLocPowers R f)

/-- **系 (M290F-8d)**: R[1/f] で f 自身の像が単元（D(f) 上で f は可逆）。 -/
theorem ringLocRf_f_unit (R : CRing) (f : R.carrier) :
    ∃ inv : (ringLocRf R f).carrier,
      (ringLocRf R f).mul ((ringLocMap R (ringLocPowers R f)).map f) inv
        = (ringLocRf R f).one :=
  ringLoc_unit_of_S R (ringLocPowers R f) f ⟨1, by
    show f = R.mul f R.one
    rw [cring_mul_one]⟩

end IUT
