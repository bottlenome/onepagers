/-
  IUT/SplitFrobenioid.lean — M55F（split Frobenioid: 射の単数成分と
  (Ind2) 型不定性の在処）の形式化

  ## 動機

  [FrdI] の Frobenioid では、射は「Frobenius 次数 deg_Fr(φ)・効果的因子
  Div(φ)・単数 u(φ)」の三つ組データに分解される（**split Frobenioid**:
  因子モノイドの分裂 Φ ⊕ O^× を持つ Frobenioid）。M51F の
  `divisorFrobenioid`（IUT/FrobenioidModel.lean）は (deg_Fr, Div) の
  二成分だけの簿記であり、単数部分を持たなかった。本モジュールは
  単数群 U をパラメータとして射に単数成分を持たせた圏
  `splitFrobenioid U` を建設し、

  * **因子部分は剛的** — 同型は (d, c) = (1, 0) を強制し対象を動かせない
    （M51F-10/M53F-3 の議論がそのまま通る）、
  * **単数部分が不定性を担う** — 任意の単数 u に対し (1, 0, u) が同型に
    なり、同型全体は U.carrier と明示的全単射（U-トーソル）、

  という **M53F の二分法（Frobenius-like 剛性 vs étale-like トーソル）の
  精密化**を機械検証する。M53F では剛的な圏（divisorFrobenioid）と
  非剛的な圏（BG）が**別々の圏**だったが、ここでは**一つの圏の中で**
  「因子簿記成分は剛的・単数成分だけがトーソル」と分離される。これが
  [IUTchIII] 定理3.11 (i) の (Ind2)（各直和因子への Ism = 単数群の
  コピーの作用による不定性）が**単数成分にのみ宿る**ことの圏論的核で
  ある。忘却関手 `splitForget`（u を捨てる）で divisorFrobenioid に
  落とすと IsoUnique が回復する（`split_dichotomy_refined`）。

  ## 単数結合則の紙上検証（可換性の要否）

  合成の単数成分を u(f·g) = u(f)^{d(g)} · u(g)（第二射の Frobenius
  次数で捻る — Frobenius が単数を d 乗する [FrdI] の簿記）とすると、
  結合則の両辺は

      ((u₁,u₂),u₃) 側 = (u₁^{d₂} · u₂)^{d₃} · u₃
      (u₁,(u₂,u₃)) 側 = u₁^{d₂d₃} · (u₂^{d₃} · u₃)

  であり、一致には (ab)^n = a^n b^n が必要。これは**非可換群では偽**
  なので、U には可換性 `hU : ∀ a b, U.mul a b = U.mul b a` を仮定する
  （実際の O^× は可換なのでモデルとして正当）。

  ## 検証する定理（全て sorry なし・選択公理なし）

  * M55F-1 `gpow` / `gpow_one` / `gpow_one_base` / `gpow_add` /
    `gpow_mul` / `Grp.mul_mul_comm` / `gpow_mul_dist` —
    群の自然数冪 g^n（g^0 = 1, g^{n+1} = g^n·g）と指数法則。
    `gpow_add`・`gpow_mul` は可換性なしで成立、`gpow_mul_dist`
    （(ab)^n = a^n b^n）だけが可換性を要する（上の紙上検証の通り）
  * M55F-2 `SplitHom` / `SplitHom.ext` — 単数つき射
    (d ≥ 1, c : QDiv, u : U.carrier) with y = φ_d(x) + c。
    単数 u は線形条件に**関与しない**（因子簿記と単数の分裂 = split）
  * M55F-3 `splitFrobenioid U hU : Cat` — 対象 = QDiv、射 = SplitHom、
    恒等 = (1, 0, 1)、合成 = (d₁d₂, φ_{d₂}(c₁) + c₂, u₁^{d₂}·u₂)。
    圏公理の完全証明（単数成分の結合は gpow_mul_dist + gpow_mul +
    mul_assoc、因子成分は M51F の div_comp_linear と同じ）
  * M55F-4 `splitForget` / `unitEndo` / `unit_endo_comp` /
    `splitForget_unit` — 忘却関手 splitFrobenioid → divisorFrobenioid
    （u を捨てる）の関手性、＋各対象の自己射 (1, 0, u) の族が
    単数群のコピーを成す（合成 = U の積）こと、忘却関手が単数自己射を
    恒等に潰すこと
  * M55F-5 `split_iso_d_one` / `split_iso_c_zero` /
    `split_iso_objects_eq` / `splitFrobenioid_gaunt` / `unitIso` /
    `split_iso_unit_arbitrary` — 同型は d = 1・c = 0 を強制し対象を
    動かせない（因子部分の剛性、M51F-10 の踏襲）が、**u は任意**:
    任意の u に対し (1, 0, u) は同型（逆 = (1, 0, u⁻¹)）
  * M55F-6 `splitIsoToUnit` / `unit_iso_unit` / `iso_unit_iso` /
    `split_polyiso_torsor` — **自己同型全体と U.carrier の明示的全単射**
    （往復恒等の両向き証明。M53F-7 `deloop_aut_torsor` の split 版）。
    poly-isomorphism が U-トーソルになる = (Ind2) 型不定性の在処
  * M55F-7 `split_not_iso_unique` / `split_forget_iso_unique` /
    `split_forget_mapIso_eq` / `split_dichotomy_refined` —
    二分法の精密化: U 非自明なら splitFrobenioid は ¬IsoUnique だが、
    忘却関手で divisorFrobenioid に落とすと任意の二つの同型の像が一致
    （= 因子簿記レベルでは一意）。「不定性は単数成分に**のみ**宿る」
    を一つの定理に
  * M55F-8 `splitInd` / `splitInd0` / `splitInd_nontrivial` —
    M5 (Ind2) への型レベル接続: splitFrobenioid の自己同型型は
    `MultiradialRep` の `Ind`/`ind0`（不定性の選択肢の型と基点）が
    要求する形の点付き型を供給し、U 非自明なら基点以外の選択肢が実在
    （M53F-9 `deloopInd` の (Ind2) 版）

  ## 正直な申告（モデルと本物の差）

  * **U は抽象可換群であり O^× の実体ではない**: 本物の split
    Frobenioid の単数部分は局所体の単数群 O_K^×（M28–M30 の
    filtration・ℤ_p 加群構造を持つ位相群）だが、ここでは単数の
    「簿記としての運ばれ方」（Frobenius で d 乗されて合成される）
    だけを抽象群でモデル化した。位相・filtration は見ていない。
  * **theta 単数・単数積分の解析内容は未形式化**: (Ind2) が実際の
    定理3.11 で「Ism のコピーの作用」として発生する解析的構成
    （log-shell 上の単数作用）は M5 のインターフェース宣言に留まり、
    ここで検証したのは「不定性が単数成分にのみ宿る」という圏論的
    分離（基数レベルの事実）である。
  * **base 圏は一点**: M51F と同じく base 圏（素点の圏）上の
    ファイバー構造は未形式化。[FrdI] の分裂 Φ ⊕ O^× のうち
    「射データの三つ組分解」の部分の忠実な実装である。
  * 選択公理・追加公理は不使用（全定理 propext/Quot.sound 以下）。
-/
import IUT.PolyIsomorphism

namespace IUT

/-! ## M55F-1: 群の自然数冪 gpow と指数法則

    M9/M17 の `Grp.pow`（左再帰 g^{n+1} = g·g^n）と双対の右再帰版。
    合成則の単数捻り u^{d} がこの向きで現れるため、右再帰で定義して
    show による定義展開を素直にする。可換性なしで成立する法則
    （gpow_add・gpow_mul）と可換性が**必要**な法則（gpow_mul_dist）を
    区別して証明する。 -/

/-- 群の自然数冪 g^n（右再帰: g^0 = 1, g^{n+1} = g^n · g）。 -/
def gpow (G : Grp) (g : G.carrier) : Nat → G.carrier
  | 0 => G.one
  | n + 1 => G.mul (gpow G g n) g

/-- g^1 = g。 -/
theorem gpow_one (G : Grp) (g : G.carrier) : gpow G g 1 = g := by
  show G.mul G.one g = g
  exact G.one_mul g

/-- **単位元の冪は単位元**: 1^n = 1（右単位則 `Grp.mul_one` は
    左公理系からの導出定理、M9）。 -/
theorem gpow_one_base (G : Grp) (n : Nat) : gpow G G.one n = G.one := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show G.mul (gpow G G.one k) G.one = G.one
    rw [ih, G.mul_one]

/-- **指数の加法則**: g^{m+n} = g^m · g^n（可換性不要）。 -/
theorem gpow_add (G : Grp) (g : G.carrier) (m n : Nat) :
    gpow G g (m + n) = G.mul (gpow G g m) (gpow G g n) := by
  induction n with
  | zero =>
    show gpow G g m = G.mul (gpow G g m) G.one
    rw [G.mul_one]
  | succ k ih =>
    show G.mul (gpow G g (m + k)) g
        = G.mul (gpow G g m) (G.mul (gpow G g k) g)
    rw [ih, G.mul_assoc]

/-- **指数の乗法則**: g^{mn} = (g^m)^n（可換性不要）。 -/
theorem gpow_mul (G : Grp) (g : G.carrier) (m n : Nat) :
    gpow G g (m * n) = gpow G (gpow G g m) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show gpow G g (m * (k + 1)) = G.mul (gpow G (gpow G g m) k) (gpow G g m)
    rw [Nat.mul_succ, gpow_add, ih]

/-- **可換群の interchange 法則**: (A·B)·(C·D) = (A·C)·(B·D)。
    gpow_mul_dist の帰納段の算術核。 -/
theorem Grp.mul_mul_comm (G : Grp)
    (hG : ∀ a b : G.carrier, G.mul a b = G.mul b a)
    (A B C D : G.carrier) :
    G.mul (G.mul A B) (G.mul C D) = G.mul (G.mul A C) (G.mul B D) := by
  rw [G.mul_assoc A B (G.mul C D), ← G.mul_assoc B C D, hG B C,
    G.mul_assoc C B D, ← G.mul_assoc A C (G.mul B D)]

/-- **冪の積への分配（可換群でのみ成立）**: (ab)^n = a^n · b^n。
    非可換では偽（紙上検証: モジュールヘッダ参照）— これが
    splitFrobenioid のパラメータ U に可換性を仮定する理由である。 -/
theorem gpow_mul_dist (G : Grp)
    (hG : ∀ a b : G.carrier, G.mul a b = G.mul b a)
    (a b : G.carrier) (n : Nat) :
    gpow G (G.mul a b) n = G.mul (gpow G a n) (gpow G b n) := by
  induction n with
  | zero =>
    show G.one = G.mul G.one G.one
    rw [G.mul_one]
  | succ k ih =>
    show G.mul (gpow G (G.mul a b) k) (G.mul a b)
        = G.mul (G.mul (gpow G a k) a) (G.mul (gpow G b k) b)
    rw [ih, Grp.mul_mul_comm G hG]

/-! ## M55F-2: 単数つき射 SplitHom

    [FrdI] の射データ三つ組 (deg_Fr, Div, u) の実装。単数 u は
    線形条件（因子の変換則）に**関与しない** — 因子簿記と単数が
    分裂している（= split）のが本質である。 -/

/-- **単数つき射**: x → y は Frobenius 次数 d ≥ 1・効果的因子 c・
    単数 u : U の三つ組で、線形条件 y = φ_d(x) + c を満たすもの。
    u は線形条件に現れない（split 構造）。 -/
structure SplitHom (U : Grp) (x y : QDiv) where
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的因子部分 Div(φ)。 -/
  c : QDiv
  /-- 単数成分 u(φ)。 -/
  u : U.carrier
  d_pos : 1 ≤ d
  /-- 線形条件: y = φ_d(x) + c（u は関与しない）。 -/
  linear : y = qadd (qfrob d x) c

/-- 射の外延性: SplitHom は (d, c, u) 成分で決まる（linear は Prop）。 -/
theorem SplitHom.ext {U : Grp} {x y : QDiv} {f g : SplitHom U x y}
    (hd : f.d = g.d) (hc : f.c = g.c) (hu : f.u = g.u) : f = g := by
  cases f with | mk fd fc fu f1 f2 =>
  cases g with | mk gd gc gu g1 g2 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  have hu' : fu = gu := hu
  subst hd'
  subst hc'
  subst hu'
  rfl

/-! ## M55F-3: split Frobenioid の圏 -/

/-- **定理 (M55F-3): split Frobenioid** — 対象 = ℚ の有効因子、
    射 = (Frobenius 次数, 効果的因子, 単数)。恒等 = (1, 0, 1)、
    合成 = (d₁d₂, φ_{d₂}(c₁) + c₂, u₁^{d₂}·u₂)（単数は第二射の
    Frobenius 次数で捻られて運ばれる — Frobenius が単数を d 乗する
    [FrdI] の簿記）。因子成分の圏公理は M51F（div_id_linear・
    div_comp_linear・qfrob_*）の再利用、単数成分の結合則は
    gpow_mul_dist（**ここで可換性 hU が必要**）・gpow_mul・mul_assoc。 -/
def splitFrobenioid (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) : Cat where
  Obj := QDiv
  Hom := SplitHom U
  id := fun x => ⟨1, qzero, U.one, Nat.le_refl 1, div_id_linear x⟩
  comp := fun f g =>
    ⟨f.d * g.d, qadd (qfrob g.d f.c) g.c, U.mul (gpow U f.u g.d) g.u,
      Nat.mul_pos f.d_pos g.d_pos,
      div_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    SplitHom.ext (Nat.one_mul f.d)
      (by show qadd (qfrob f.d qzero) f.c = f.c
          rw [qfrob_zero, qzero_add])
      (by show U.mul (gpow U U.one f.d) f.u = f.u
          rw [gpow_one_base, U.one_mul])
  comp_id := fun f =>
    SplitHom.ext (Nat.mul_one f.d)
      (by show qadd (qfrob 1 f.c) qzero = f.c
          rw [qfrob_one, qadd_zero])
      (by show U.mul (gpow U f.u 1) U.one = f.u
          rw [gpow_one, U.mul_one])
  assoc := fun f g h =>
    SplitHom.ext (Nat.mul_assoc f.d g.d h.d)
      (by show qadd (qfrob h.d (qadd (qfrob g.d f.c) g.c)) h.c
            = qadd (qfrob (g.d * h.d) f.c) (qadd (qfrob h.d g.c) h.c)
          rw [qfrob_add, qfrob_frob, qadd_assoc])
      (by show U.mul (gpow U (U.mul (gpow U f.u g.d) g.u) h.d) h.u
            = U.mul (gpow U f.u (g.d * h.d))
                (U.mul (gpow U g.u h.d) h.u)
          rw [gpow_mul_dist U hU, ← gpow_mul, U.mul_assoc])

/-! ## M55F-4: 忘却関手と単数群の注入 -/

/-- **定理 (M55F-4a): 忘却関手** splitFrobenioid → divisorFrobenioid —
    単数成分 u を捨てる対応は関手（恒等・合成の因子成分は
    両圏で同一の式なので map_id・map_comp は外延性で即座）。 -/
def splitForget (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) :
    Functor (splitFrobenioid U hU) divisorFrobenioid where
  onObj := fun x => x
  onHom := fun f => ⟨f.d, f.c, f.d_pos, f.linear⟩
  map_id := fun _ => DivHom.ext rfl rfl
  map_comp := fun _ _ => DivHom.ext rfl rfl

/-- 単数自己射 (1, 0, u): 因子簿記は恒等、単数だけ u。 -/
def unitEndo (U : Grp) (x : QDiv) (u : U.carrier) : SplitHom U x x :=
  ⟨1, qzero, u, Nat.le_refl 1, div_id_linear x⟩

/-- **定理 (M55F-4b): 単数群の注入** — 各対象 x の単数自己射の族
    u ↦ (1, 0, u) は合成が U の積に一致する（U のコピーが
    自己射モノイドに埋まる）。 -/
theorem unit_endo_comp (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (x : QDiv) (u₁ u₂ : U.carrier) :
    (splitFrobenioid U hU).comp (unitEndo U x u₁) (unitEndo U x u₂)
      = unitEndo U x (U.mul u₁ u₂) :=
  SplitHom.ext (Nat.one_mul 1)
    (by show qadd (qfrob 1 qzero) qzero = qzero
        rw [qfrob_one, qadd_zero])
    (by show U.mul (gpow U u₁ 1) u₂ = U.mul u₁ u₂
        rw [gpow_one])

/-- 単数 1 の自己射は恒等射そのもの。 -/
theorem unit_endo_one (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) (x : QDiv) :
    unitEndo U x U.one = (splitFrobenioid U hU).id x :=
  rfl

/-- **定理 (M55F-4c): 忘却関手は単数自己射を恒等に潰す** —
    単数の情報は divisorFrobenioid 側には残らない
    （不定性が忘却で消えることの射レベルの実体）。 -/
theorem splitForget_unit (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (x : QDiv) (u : U.carrier) :
    (splitForget U hU).onHom (unitEndo U x u) = divisorFrobenioid.id x :=
  DivHom.ext rfl rfl

/-! ## M55F-5: 因子部分の剛性と単数部分の自由性 -/

/-- **定理 (M55F-5a): 同型の Frobenius 次数は 1** —
    splitFrobenioid の任意の同型の hom 成分は d = 1
    （d の積 = 1、M48F の `frob_mul_eq_one_left` を再利用。
    M53F-3a の split 版）。 -/
theorem split_iso_d_one (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {x y : QDiv} (i : CatIso (splitFrobenioid U hU) x y) :
    i.hom.d = 1 :=
  frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos
    (congrArg (SplitHom.d) i.hom_inv)

/-- **定理 (M55F-5b): 同型の因子部分は自明** — c = 0
    （有効因子の和 = 0 ⟹ max 上界 = 0 ⟹ 自明因子。M53F-3b の
    split 版）。 -/
theorem split_iso_c_zero (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {x y : QDiv} (i : CatIso (splitFrobenioid U hU) x y) :
    i.hom.c = qzero := by
  have hc : qadd (qfrob i.inv.d i.hom.c) i.inv.c = qzero :=
    congrArg (SplitHom.c) i.hom_inv
  have hb : max i.hom.c.bound i.inv.c.bound = 0 :=
    congrArg QDiv.bound hc
  have hb0 : i.hom.c.bound = 0 := nat_max_eq_zero_left hb
  exact QDiv.ext
    (funext fun k => i.hom.c.vanish k (by rw [hb0]; exact Nat.zero_le k))
    hb0

/-- **定理 (M55F-5c): 同型は対象を動かせない** — x ≅ y ⟹ x = y。
    単数を付け足しても因子部分の剛性（M51F-10）はそのまま生き残る。 -/
theorem split_iso_objects_eq (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {x y : QDiv} (i : CatIso (splitFrobenioid U hU) x y) : x = y := by
  have hd1 : i.hom.d = 1 := split_iso_d_one U hU i
  have hc0 : i.hom.c = qzero := split_iso_c_zero U hU i
  have hl := i.hom.linear
  rw [hd1, hc0, qfrob_one, qadd_zero] at hl
  exact hl.symm

/-- **系 (M55F-5c'): splitFrobenioid は gaunt**。 -/
theorem splitFrobenioid_gaunt (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) :
    IsGaunt (splitFrobenioid U hU) :=
  fun _ _ i => split_iso_objects_eq U hU i

/-- **定理 (M55F-5d): 単数は任意 — (1, 0, u) は同型**
    （逆 = (1, 0, u⁻¹)。右逆 `Grp.mul_inv` は左公理系からの導出定理、
    左逆 `Grp.inv_mul` は公理）。因子部分は (1,0) に固定されるのに
    単数部分は U 全体を走れる: 不定性の在処が単数成分であることの
    構成的半分。 -/
def unitIso (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (x : QDiv) (u : U.carrier) :
    CatIso (splitFrobenioid U hU) x x where
  hom := unitEndo U x u
  inv := unitEndo U x (U.inv u)
  hom_inv :=
    SplitHom.ext (Nat.one_mul 1)
      (by show qadd (qfrob 1 qzero) qzero = qzero
          rw [qfrob_one, qadd_zero])
      (by show U.mul (gpow U u 1) (U.inv u) = U.one
          rw [gpow_one]
          exact U.mul_inv u)
  inv_hom :=
    SplitHom.ext (Nat.one_mul 1)
      (by show qadd (qfrob 1 qzero) qzero = qzero
          rw [qfrob_one, qadd_zero])
      (by show U.mul (gpow U (U.inv u) 1) u = U.one
          rw [gpow_one]
          exact U.inv_mul u)

/-- **定理 (M55F-5e): 任意の単数が同型の hom 成分として実現される**
    （命題形）。 -/
theorem split_iso_unit_arbitrary (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (x : QDiv) (u : U.carrier) :
    ∃ i : CatIso (splitFrobenioid U hU) x x, i.hom.u = u :=
  ⟨unitIso U hU x u, rfl⟩

/-! ## M55F-6: 自己同型全体は U-トーソル

    M53F-7 `deloop_aut_torsor` と同じ往復写像方式。CatIso 全体の
    等号には M22-1a `CatIso.ext`（逆は hom で決まる）＋
    `SplitHom.ext`（d = 1・c = 0 が両者で一致）を使う。 -/

/-- 同型から単数の読み出し（hom の u 成分）。 -/
def splitIsoToUnit (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {x y : QDiv} (i : CatIso (splitFrobenioid U hU) x y) : U.carrier :=
  i.hom.u

/-- 往復 (unit → iso → unit) は恒等。 -/
theorem unit_iso_unit (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (x : QDiv) (u : U.carrier) :
    splitIsoToUnit U hU (unitIso U hU x u) = u :=
  rfl

/-- 往復 (iso → unit → iso) は恒等: 同型の d・c 成分は (1, 0) に
    固定されている（M55F-5a/5b）ので、u 成分の一致だけで hom が
    一致し、逆成分は M22-1a `CatIso.ext` で従う。 -/
theorem iso_unit_iso (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {x : QDiv} (i : CatIso (splitFrobenioid U hU) x x) :
    unitIso U hU x (splitIsoToUnit U hU i) = i :=
  CatIso.ext
    (SplitHom.ext (split_iso_d_one U hU i).symm
      (split_iso_c_zero U hU i).symm rfl)

/-- **定理 (M55F-6): splitFrobenioid の poly-isomorphism は
    U-トーソル** — 各対象の自己同型全体（= poly-isomorphism）は
    U.carrier と明示的全単射（往復写像が両向きとも恒等）。
    因子部分が (1, 0) に剛化された後に残る自由度がちょうど U 全体:
    **(Ind2) 型不定性（単数のコピーの作用）の在処**の機械検証。
    M53F-7（BG の G-トーソル）との違いは、ここでは**剛的な因子簿記と
    同居する一つの圏の中で**単数成分だけがトーソルになること。 -/
theorem split_polyiso_torsor (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) (x : QDiv) :
    (∀ i : CatIso (splitFrobenioid U hU) x x,
        unitIso U hU x (splitIsoToUnit U hU i) = i)
      ∧ (∀ u : U.carrier, splitIsoToUnit U hU (unitIso U hU x u) = u) :=
  ⟨fun i => iso_unit_iso U hU i, fun _ => rfl⟩

/-! ## M55F-7: 二分法の精密化 — 不定性は単数成分にのみ宿る -/

/-- **定理 (M55F-7a): U 非自明なら splitFrobenioid は剛的でない** —
    単位元以外の単数 u があれば (1,0,u) と (1,0,1) が異なる同型に
    なる（M53F-8a `deloop_not_iso_unique` の split 版。
    divisorFrobenioid は IsoUnique だった——単数を足した瞬間に
    剛性が壊れる）。 -/
theorem split_not_iso_unique (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (h : ∃ u : U.carrier, u ≠ U.one) :
    ¬ IsoUnique (splitFrobenioid U hU) := by
  intro hiso
  obtain ⟨u, hu⟩ := h
  exact hu (congrArg SplitHom.u
    (hiso qzero qzero (unitIso U hU qzero u) (unitIso U hU qzero U.one)))

/-- **定理 (M55F-7b): 忘却関手の像では同型は一意（IsoUnique の回復）**
    — 任意の同型 i, j : x ≅ y の hom の忘却像は一致する
    （d・c 成分がどちらも (1, 0) に固定されるから）。
    因子簿記レベルでは「貼り方の選択肢」が存在しない。 -/
theorem split_forget_iso_unique (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {x y : QDiv} (i j : CatIso (splitFrobenioid U hU) x y) :
    (splitForget U hU).onHom i.hom = (splitForget U hU).onHom j.hom :=
  DivHom.ext
    ((split_iso_d_one U hU i).trans (split_iso_d_one U hU j).symm)
    ((split_iso_c_zero U hU i).trans (split_iso_c_zero U hU j).symm)

/-- **系 (M55F-7b'): CatIso ごと忘却しても一意** — 同型の mapIso 像は
    divisorFrobenioid の剛性（M53F-3e）により完全に一致する。 -/
theorem split_forget_mapIso_eq (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    {x y : QDiv} (i j : CatIso (splitFrobenioid U hU) x y) :
    Functor.mapIso (splitForget U hU) i
      = Functor.mapIso (splitForget U hU) j :=
  divisorFrobenioid_rigid _ _

/-- **定理 (M55F-7c): 二分法の精密化（M53F の精密化）** —
    一つの圏 splitFrobenioid の中で:
    (1) 任意の二つの同型は忘却像（因子簿記）が一致する = 因子部分は
        剛的で不定性ゼロ、
    (2) U 非自明なら hom が異なる同型の対が実在する = 不定性は実在し、
        (1) と合わせてそれは**単数成分にのみ**宿る。
    [FrdI] の split 構造で (Ind2) 型不定性の在処が単数部分に分離される
    ことの一文形式化。 -/
theorem split_dichotomy_refined (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (h : ∃ u : U.carrier, u ≠ U.one) :
    (∀ (x y : QDiv) (i j : CatIso (splitFrobenioid U hU) x y),
        (splitForget U hU).onHom i.hom = (splitForget U hU).onHom j.hom)
      ∧ (∃ (x : QDiv) (i j : CatIso (splitFrobenioid U hU) x x),
          i.hom ≠ j.hom) := by
  constructor
  · exact fun x y i j => split_forget_iso_unique U hU i j
  · obtain ⟨u, hu⟩ := h
    exact ⟨qzero, unitIso U hU qzero u, unitIso U hU qzero U.one,
      fun heq => hu (congrArg SplitHom.u heq)⟩

/-! ## M55F-8: M5 (Ind2) への型レベル接続

    M5（IUT/Multiradial.lean）の `MultiradialRep` は不定性を
    「選択肢の型 `Ind` と基点 `ind0 : Ind`」として公理化している
    （(Ind1)×(Ind2)×(Ind3) の選択肢の型）。M53F-9 の `deloopInd` は
    (Ind1)（étale 側の自己同型）の供給源だった。本節はその (Ind2) 版:
    splitFrobenioid の自己同型型（= U-トーソル、M55F-6）が同じ形の
    点付き型を供給する。実際の定理3.11 で (Ind2) が log-shell 上の
    単数積分（Ism のコピーの作用）として発生する解析的内容は
    未形式化であり、M5 のインターフェース宣言に留まる（正直な申告）。 -/

/-- (Ind2) 型不定性の選択肢の型: splitFrobenioid の自明因子上の
    poly-isomorphism（M55F-6 により U-トーソル）。
    `MultiradialRep.Ind` フィールドに供給できる形。 -/
def splitInd (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) : Type :=
  CatIso (splitFrobenioid U hU) qzero qzero

/-- 不定性の基点（単数 1 の同型 = 恒等同型 = 「不定性を選ばない」
    選択肢）。`MultiradialRep.ind0` フィールドに供給できる形。 -/
def splitInd0 (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a) : splitInd U hU :=
  unitIso U hU qzero U.one

/-- **定理 (M55F-8): (Ind2) 型不定性の非自明性** — U が非自明なら、
    基点以外の選択肢が実在する。(Ind2) が「空回りの形式」でなく
    真の選択肢を持つことの split Frobenioid モデルでの検証
    （M53F-9 `deloopInd_nontrivial` の (Ind2) 版）。 -/
theorem splitInd_nontrivial (U : Grp)
    (hU : ∀ a b : U.carrier, U.mul a b = U.mul b a)
    (h : ∃ u : U.carrier, u ≠ U.one) :
    ∃ i : splitInd U hU, i ≠ splitInd0 U hU := by
  obtain ⟨u, hu⟩ := h
  exact ⟨unitIso U hU qzero u,
    fun heq => hu (congrArg SplitHom.u (congrArg CatIso.hom heq))⟩

end IUT
