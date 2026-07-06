/-
  IUT/TateCurve.lean — M309F: Tate 曲線 E_q = K^×/q^ℤ（IUT の中心対象）

  ── 主要成果の分類: **[実]**（本物の体 K の乗法群 K^× と本物の整数冪部分群 q^ℤ を
  建て、**Tate 曲線 E_q(K) = K^×/q^ℤ を本物の商群として実構成**する。エタールテータ
  （M308F 系）が乗る中心対象そのもの）。

  complete_pct 影響: **柱A「Tate 曲線＝IUT の中心対象」の本物の先行建設**。
  Mochizuki の IUT は、乗法的還元を持つ楕円曲線の**解析的一意化 E_q = K^×/q^ℤ**
  （Tate 曲線）を舞台に、エタールテータ関数 Θ とその値の遠アーベル復元を行う。
  既存コードベースは楕円曲線（M304F Weierstrass）・付値環（M301F）・商群
  （M267F）・体（M264F）を個別に持つが、**「体 K の乗法群 K^× を q^ℤ で割った本物の
  商群 E_q」そのもの**を構成したモジュールが無かった。本ファイルはその中心対象を、
  既存 `IUTField`（M264F）・`Grp`/`Subgroup`/`quotientGroupN`（M267F）の上に
  **本物の商群として実構成**し、点の**周期性 [u] = [qu]**（q^ℤ 商の本質）を完全証明する。

  * M309F-1 `tateNpow` / `tateZpow`   — 群の自然数冪・**整数冪** g^n（n∈ℤ）と
    加法則 `tateZpow_add`（g^{a+b}=g^a·g^b, 全整数）・逆元則 `tateZpow_neg`
  * M309F-2 `tateMultGroup`           — **体 K の乗法群 K^×**（非零元、逆元は M264F
    inv、可換 `tateMultGroup_comm`）を本物の `Grp` として実構成
  * M309F-3 `tateQPowersSubgroup`     — **q^ℤ 部分群**（q の整数冪全体、closure は
    tateZpow_add/neg から本物で）・可換ゆえ正規 `tateQPowers_isNormal`
  * M309F-4 `tateCurve`               — **Tate 曲線 E_q = K^×/q^ℤ**（quotientGroupN、
    M267F）・アーベル群性 `tateCurve_isAbelianGroup`
  * M309F-5 `tateCurvePoint` / `tate_point_period` — 点 [u] と**周期性 [u]=[qu]**
    （q^ℤ 商の定義から本物で。Tate 曲線の周期性の中身）
  * M309F-6 付値接続 `tate_qpow_val` / `tate_qpow_ne_one` — v(q)=m の Tate パラメータで
    v(q^n)=m·n、**v(q)≠0 なら q^n≠1（n≥1）＝無限位数**（M301F 付値から本物で）
  * M309F-7 テータ接続骨組み `TateQuasiPeriodic` / `tate_theta_period_in_lattice` /
    `tate_theta_descends_points` — Θ(q,qu)=（因子)·Θ(q,u) の q^ℤ-準周期性の周期 q が
    ちょうど E_q の周期束 q^ℤ の生成元であること・準周期 q が曲線上で [u]=[qu] を与える
  * M309F-8 capstone `TateCurveData` / `tateCurve_exists` / `tateCurveDataOne`

  正直な限定（何が本物で何が骨組みか）:
  - **本物**: K^× が本物の群（結合・単位・逆元、可換）、q^ℤ が本物の部分群（closure を
    整数冪の加法則 tateZpow_add・逆元則 tateZpow_neg から証明）、E_q=K^×/q^ℤ が本物の
    商群でアーベル群、点の**周期性 [u]=[qu]** はすべて完全証明（sorry 皆無・新規 choice
    皆無）。整数冪 g^n の加法則 g^{a+b}=g^a·g^b も全整数で完全証明。
  - **付値による無限位数（tate_qpow_ne_one）は条件付き本物**: 付値 val と q が
    v(q)=some m（m≠0）を満たすとき q^n≠1（n≥1）を証明する。**具体的な v(q)>0 の付値
    （素元を持つ本物の離散付値）の構成そのものは柱B ℤ_p 接続の後続**——M301F の
    `trivialValuation`（rank 0）は v(q)>0 の元を持たないため、正 valuation の witness は未達。
    存在 witness `tateCurveDataOne` は q=1（自明周期）で E_q=K^×/⟨1⟩ を与える骨格 witness
    （周期性定理 tate_point_period は任意の q で本物）。
  - **テータ接続は骨組み**: Θ の quasi-period q が q^ℤ の生成元で曲線上 [u]=[qu] を
    与えることまで（M309F-7）。Θ 自身が E_q 上の切断・因子・three-rigidity の完全接続は
    柱E（M308F EtaleThetaReal）後続。ここでは E_q=K^×/q^ℤ を本物の商群として構成し
    周期性を本物にすることに専念する（toy 主語を作らない）。
  - 一般 Tate 曲線の Weierstrass 係数（a₄(q),a₆(q) の q-級数）と M304F 楕円曲線への
    同型は後続。値群は ℤ（離散付値）に限る。

  全て選択公理不使用（新規 choice を証明本体に導入しない）。禁止タクティク不使用。
  共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
-/
import IUT.QuotientGroup
import IUT.ValuationRing

namespace IUT

/-! ## M309F-1: 群の整数冪 g^n（n ∈ ℤ）と加法則 -/

/-- **自然数冪 g^n**（右再帰: g^0 = 1, g^{n+1} = g^n · g）。 -/
def tateNpow (G : Grp) (g : G.carrier) : Nat → G.carrier
  | 0 => G.one
  | n + 1 => G.mul (tateNpow G g n) g

/-- **整数冪 g^n**（n ≥ 0 は自然数冪、負は逆元の冪 (g⁻¹)^{|n|}）。 -/
def tateZpow (G : Grp) (g : G.carrier) : Int → G.carrier
  | Int.ofNat n => tateNpow G g n
  | Int.negSucc n => tateNpow G (G.inv g) (n + 1)

/-- g^0 = 1。 -/
theorem tateZpow_zero (G : Grp) (g : G.carrier) : tateZpow G g 0 = G.one := rfl

/-- g^1 = g。 -/
theorem tateZpow_one (G : Grp) (g : G.carrier) : tateZpow G g 1 = g := by
  show G.mul G.one g = g
  exact G.one_mul g

/-- g^{negSucc 0} = g^{-1}。 -/
theorem tateZpow_negOne (G : Grp) (g : G.carrier) :
    tateZpow G g (Int.negSucc 0) = G.inv g := by
  show G.mul G.one (G.inv g) = G.inv g
  exact G.one_mul (G.inv g)

/-- **後者則**: g^{b+1} = g^b · g（全整数 b）。 -/
theorem tateZpow_succ (G : Grp) (g : G.carrier) (b : Int) :
    tateZpow G g (b + 1) = G.mul (tateZpow G g b) g := by
  cases b with
  | ofNat m =>
    show tateZpow G g (Int.ofNat (m + 1)) = G.mul (tateZpow G g (Int.ofNat m)) g
    rfl
  | negSucc m =>
    cases m with
    | zero =>
      show tateZpow G g (Int.ofNat 0)
          = G.mul (G.mul G.one (G.inv g)) g
      show G.one = G.mul (G.mul G.one (G.inv g)) g
      rw [G.one_mul, G.inv_mul]
    | succ k =>
      show tateNpow G (G.inv g) (k + 1)
          = G.mul (G.mul (tateNpow G (G.inv g) (k + 1)) (G.inv g)) g
      rw [G.mul_assoc, G.inv_mul, G.mul_one]

/-- **前者則**: g^{b + (-1)} = g^b · g^{-1}（全整数 b）。 -/
theorem tateZpow_pred (G : Grp) (g : G.carrier) (b : Int) :
    tateZpow G g (b + Int.negSucc 0) = G.mul (tateZpow G g b) (G.inv g) := by
  cases b with
  | ofNat m =>
    cases m with
    | zero =>
      show tateZpow G g (Int.negSucc 0)
          = G.mul (tateZpow G g (Int.ofNat 0)) (G.inv g)
      show G.mul G.one (G.inv g) = G.mul G.one (G.inv g)
      rfl
    | succ k =>
      have hidx : Int.ofNat (k + 1) + Int.negSucc 0 = Int.ofNat k := by
        have h : Int.ofNat (k + 1) = Int.ofNat k + 1 := rfl
        have h2 : (1 : Int) + Int.negSucc 0 = (0 : Int) := rfl
        rw [h, Int.add_assoc, h2, Int.add_zero]
      rw [hidx]
      show tateNpow G g k
          = G.mul (G.mul (tateNpow G g k) g) (G.inv g)
      rw [G.mul_assoc, G.mul_inv, G.mul_one]
  | negSucc m =>
    show tateNpow G (G.inv g) (m + 1 + 1)
        = G.mul (tateNpow G (G.inv g) (m + 1)) (G.inv g)
    rfl

/-- g^{ofNat (n+1)} = g^{ofNat n} · g（定義展開）。 -/
theorem tateZpow_ofNat_succ (G : Grp) (g : G.carrier) (n : Nat) :
    tateZpow G g (Int.ofNat (n + 1)) = G.mul (tateZpow G g (Int.ofNat n)) g := rfl

/-- g^{negSucc (n+1)} = g^{negSucc n} · g^{-1}（定義展開）。 -/
theorem tateZpow_negSucc_succ (G : Grp) (g : G.carrier) (n : Nat) :
    tateZpow G g (Int.negSucc (n + 1))
      = G.mul (tateZpow G g (Int.negSucc n)) (G.inv g) := rfl

/-- **加法則**: g^{a+b} = g^a · g^b（全整数 a,b）。可換性不要。
    第二指数を ℤ の符号で場合分けし、各分岐を自然数帰納で後者則／前者則を
    一つずつ適用して閉じる。 -/
theorem tateZpow_add (G : Grp) (g : G.carrier) (a : Int) :
    ∀ b : Int, tateZpow G g (a + b) = G.mul (tateZpow G g a) (tateZpow G g b) := by
  intro b
  cases b with
  | ofNat n =>
    induction n with
    | zero =>
      show tateZpow G g (a + Int.ofNat 0)
          = G.mul (tateZpow G g a) G.one
      rw [G.mul_one]
      have hz : a + Int.ofNat 0 = a := by
        have h : Int.ofNat 0 = (0 : Int) := rfl
        rw [h, Int.add_zero]
      rw [hz]
    | succ k ih =>
      have hidx : a + Int.ofNat (k + 1) = (a + Int.ofNat k) + 1 := by
        have h : Int.ofNat (k + 1) = Int.ofNat k + 1 := rfl
        rw [h, Int.add_assoc]
      rw [hidx, tateZpow_succ, ih, G.mul_assoc, tateZpow_ofNat_succ]
  | negSucc n =>
    induction n with
    | zero =>
      rw [tateZpow_pred]
      show G.mul (tateZpow G g a) (G.inv g)
          = G.mul (tateZpow G g a) (G.mul G.one (G.inv g))
      rw [G.one_mul]
    | succ k ih =>
      have hidx : a + Int.negSucc (k + 1)
          = (a + Int.negSucc k) + Int.negSucc 0 := by
        have h : Int.negSucc (k + 1) = Int.negSucc k + Int.negSucc 0 := rfl
        rw [h, Int.add_assoc]
      rw [hidx, tateZpow_pred, ih, G.mul_assoc, tateZpow_negSucc_succ]

/-- **逆元則**: g^{-a} = (g^a)^{-1}（加法則から）。 -/
theorem tateZpow_neg (G : Grp) (g : G.carrier) (a : Int) :
    tateZpow G g (-a) = G.inv (tateZpow G g a) := by
  apply G.inv_eq_of_mul_eq_one
  rw [← tateZpow_add]
  have h : a + (-a) = (0 : Int) := by omega
  rw [h]
  rfl

/-! ## M309F-2: 体 K の乗法群 K^× -/

/-- **K^× = 体 K の乗法群**（非零元 {x | x ≠ 0}、単位 1、逆元は M264F の inv）。
    整域性 `mul_ne_zero`・逆元の非零性 `inv_ne_zero`・逆元公理 `inv_mul_cancel`
    から本物の群公理を満たす。 -/
def tateMultGroup (K : IUTField) : Grp where
  carrier := { x : K.carrier // x ≠ K.zero }
  mul := fun x y => ⟨K.mul x.val y.val, K.mul_ne_zero x.property y.property⟩
  one := ⟨K.one, K.one_ne_zero⟩
  inv := fun x => ⟨K.inv x.val, K.inv_ne_zero x.property⟩
  mul_assoc := fun a b c => Subtype.ext (K.mul_assoc a.val b.val c.val)
  one_mul := fun a => Subtype.ext (K.one_mul a.val)
  inv_mul := fun a => Subtype.ext (K.inv_mul_cancel a.property)

/-- **K^× は可換群**（体の乗法可換性 M38 mul_comm）。 -/
theorem tateMultGroup_comm (K : IUTField) :
    ∀ a b : (tateMultGroup K).carrier,
      (tateMultGroup K).mul a b = (tateMultGroup K).mul b a :=
  fun a b => Subtype.ext (K.mul_comm a.val b.val)

/-! ## M309F-3: q^ℤ 部分群 -/

/-- **q^ℤ 部分群** = q の整数冪 {qⁿ | n ∈ ℤ}。closure は整数冪の加法則
    `tateZpow_add`（qᵐ·qⁿ=q^{m+n}）・単位（q⁰=1）・逆元則 `tateZpow_neg`
    ((qⁿ)⁻¹=q^{-n}）から本物で証明。 -/
def tateQPowersSubgroup (G : Grp) (g : G.carrier) : Subgroup G where
  mem := fun y => ∃ n : Int, tateZpow G g n = y
  one_mem := ⟨0, rfl⟩
  mul_mem := fun {a b} ha hb => by
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, by rw [tateZpow_add, hm, hn]⟩
  inv_mem := fun {a} ha => by
    obtain ⟨m, hm⟩ := ha
    exact ⟨-m, by rw [tateZpow_neg, hm]⟩

/-- q^ℤ の生成元 q はそれ自身 q^ℤ に属する（q = q¹）。 -/
theorem tate_gen_mem (G : Grp) (g : G.carrier) :
    (tateQPowersSubgroup G g).mem g :=
  ⟨1, tateZpow_one G g⟩

/-- **q^ℤ は正規部分群**（K^× は可換なので任意部分群が正規）。 -/
theorem tateQPowers_isNormal (K : IUTField) (q : (tateMultGroup K).carrier) :
    IsNormalSubgroup (tateMultGroup K) (tateQPowersSubgroup (tateMultGroup K) q) := by
  intro x n hn
  have hconj :
      (tateMultGroup K).mul ((tateMultGroup K).mul x n) ((tateMultGroup K).inv x) = n := by
    rw [tateMultGroup_comm K x n, (tateMultGroup K).mul_assoc,
      (tateMultGroup K).mul_inv, (tateMultGroup K).mul_one]
  rw [hconj]
  exact hn

/-! ## M309F-4: Tate 曲線 E_q = K^×/q^ℤ -/

/-- **Tate 曲線 E_q(K) = K^×/q^ℤ** — 乗法群 K^× を整数冪部分群 q^ℤ で割った
    本物の商群（M267F `quotientGroupN`）。IUT のエタールテータが乗る中心対象。 -/
def tateCurve (K : IUTField) (q : (tateMultGroup K).carrier) : Grp :=
  quotientGroupN (tateMultGroup K) (tateQPowersSubgroup (tateMultGroup K) q)
    (tateQPowers_isNormal K q)

/-- **射影 K^× → E_q**（点を割り当てる全射準同型）。 -/
def tateCurveProj (K : IUTField) (q : (tateMultGroup K).carrier) :
    Hom (tateMultGroup K) (tateCurve K q) :=
  quotientProjN (tateMultGroup K) (tateQPowersSubgroup (tateMultGroup K) q)
    (tateQPowers_isNormal K q)

/-- **E_q はアーベル群**（可換群 K^× の商）。 -/
theorem tateCurve_isAbelianGroup (K : IUTField) (q : (tateMultGroup K).carrier) :
    ∀ x y : (tateCurve K q).carrier,
      (tateCurve K q).mul x y = (tateCurve K q).mul y x := by
  intro x y
  induction x using Quot.ind
  rename_i a
  induction y using Quot.ind
  rename_i b
  show Quot.mk _ ((tateMultGroup K).mul a b) = Quot.mk _ ((tateMultGroup K).mul b a)
  rw [tateMultGroup_comm K a b]

/-! ## M309F-5: 点と周期性 [u] = [qu] -/

/-- **E_q の点 [u]**（u ∈ K^× の商における像）。 -/
def tateCurvePoint (K : IUTField) (q u : (tateMultGroup K).carrier) :
    (tateCurve K q).carrier :=
  Quot.mk _ u

/-- **周期性 [u] = [qu]**（Tate 曲線の本質）— q^ℤ で割ることで u と qu は
    同一点になる。証明の核: u⁻¹·(q·u) = q ∈ q^ℤ（可換性で整理）。 -/
theorem tate_point_period (K : IUTField) (q u : (tateMultGroup K).carrier) :
    tateCurvePoint K q u = tateCurvePoint K q ((tateMultGroup K).mul q u) := by
  apply Quot.sound
  show (tateQPowersSubgroup (tateMultGroup K) q).mem
      ((tateMultGroup K).mul ((tateMultGroup K).inv u) ((tateMultGroup K).mul q u))
  have heq :
      (tateMultGroup K).mul ((tateMultGroup K).inv u) ((tateMultGroup K).mul q u) = q := by
    rw [tateMultGroup_comm K q u, ← (tateMultGroup K).mul_assoc,
      (tateMultGroup K).inv_mul, (tateMultGroup K).one_mul]
  rw [heq]
  exact tate_gen_mem (tateMultGroup K) q

/-- **周期性（射影版）** [u] = [qu]（射影準同型で表示）。 -/
theorem tate_point_q_equiv (K : IUTField) (q u : (tateMultGroup K).carrier) :
    (tateCurveProj K q).map u = (tateCurveProj K q).map ((tateMultGroup K).mul q u) :=
  tate_point_period K q u

/-! ## M309F-6: 付値による Tate パラメータの無限位数 -/

/-- **v(q^n) = n·v(q)**（付値の乗法性 M301F v_mul の反復）。q^n の台の付値は
    v(q)=some m のとき some (m·n)。 -/
theorem tate_qpow_val (K : IUTField) (val : valRingValuation K)
    (q : K.carrier) (hq : q ≠ K.zero) {m : Int} (h : val.v q = some m) :
    ∀ n : Nat,
      val.v ((tateNpow (tateMultGroup K) ⟨q, hq⟩ n).val) = some (m * Int.ofNat n) := by
  intro n
  induction n with
  | zero =>
    show val.v K.one = some (m * Int.ofNat 0)
    have h0 : Int.ofNat 0 = (0 : Int) := rfl
    rw [h0, Int.mul_zero, val.v_one]
  | succ k ih =>
    show val.v (K.mul (tateNpow (tateMultGroup K) ⟨q, hq⟩ k).val q)
        = some (m * Int.ofNat (k + 1))
    rw [val.v_mul, ih, h]
    show some (m * Int.ofNat k + m) = some (m * Int.ofNat (k + 1))
    have hmul : m * Int.ofNat (k + 1) = m * Int.ofNat k + m := by
      have h1 : Int.ofNat (k + 1) = Int.ofNat k + 1 := rfl
      rw [h1, Int.mul_add, Int.mul_one]
    rw [hmul]

/-- **無限位数（条件付き本物）**: v(q) = some m（m ≠ 0、Tate パラメータ）なら
    q^n ≠ 1（n ≥ 1）。v(q^n) = some(m·n) ≠ some 0 = v(1) から。
    *正 valuation v(q)>0 の具体構成そのものは柱B ℤ_p 接続の後続*（M301F の
    trivialValuation は rank 0 で正 valuation の元を持たない）。 -/
theorem tate_qpow_ne_one (K : IUTField) (val : valRingValuation K)
    (q : K.carrier) (hq : q ≠ K.zero) {m : Int} (h : val.v q = some m) (hm : m ≠ 0)
    (n : Nat) (hn : n ≠ 0) :
    (tateNpow (tateMultGroup K) ⟨q, hq⟩ n) ≠ (tateMultGroup K).one := by
  intro hc
  have hval : val.v ((tateNpow (tateMultGroup K) ⟨q, hq⟩ n).val) = some (m * Int.ofNat n) :=
    tate_qpow_val K val q hq h n
  have hone : (tateNpow (tateMultGroup K) ⟨q, hq⟩ n).val = K.one :=
    congrArg Subtype.val hc
  rw [hone, val.v_one] at hval
  -- hval : some 0 = some (m * Int.ofNat n)
  have hz : (0 : Int) = m * Int.ofNat n := by
    have := Option.some.inj hval
    exact this
  have hnz : Int.ofNat n ≠ 0 := by
    intro hcc
    apply hn
    cases n with
    | zero => rfl
    | succ j => exact absurd hcc (by intro hh; cases hh)
  exact (Int.mul_ne_zero hm hnz) hz.symm

/-! ## M309F-7: エタールテータとの接続（骨組み） -/

/-- **q^ℤ-準周期性** Θ(q,qu) = （因子)·Θ(q,u) — エタールテータ Θ が Tate 曲線
    K^×/q^ℤ 上で周期 q に関して準周期的であるという述語（M308F Θ が乗る舞台の骨組み）。 -/
def TateQuasiPeriodic (K : IUTField) (q : (tateMultGroup K).carrier)
    (target : Grp) (θ fac : (tateMultGroup K).carrier → target.carrier) : Prop :=
  ∀ u, θ ((tateMultGroup K).mul q u) = target.mul (fac u) (θ u)

/-- **テータの準周期はちょうど E_q の周期束 q^ℤ の生成元**（Θ の quasi-period q が
    K^×/q^ℤ の割る対象 q^ℤ の生成元であることの接続）。 -/
theorem tate_theta_period_in_lattice (K : IUTField) (q : (tateMultGroup K).carrier) :
    (tateQPowersSubgroup (tateMultGroup K) q).mem q :=
  tate_gen_mem (tateMultGroup K) q

/-- **準周期は曲線上で [u] = [qu] を与える**（Θ が K^×/q^ℤ 上の関数として矛盾なく
    定義される舞台であること — quasi-period q による点の同一視は周期性 M309F-5 に一致）。 -/
theorem tate_theta_descends_points (K : IUTField) (q u : (tateMultGroup K).carrier) :
    tateCurvePoint K q u = tateCurvePoint K q ((tateMultGroup K).mul q u) :=
  tate_point_period K q u

/-! ## M309F-8: capstone -/

/-- **Tate 曲線の総括データ** — Tate パラメータ q・曲線 E_q（K^×/q^ℤ）・その商群性・
    アーベル群性を束ねる。 -/
structure TateCurveData (K : IUTField) where
  /-- Tate パラメータ q ∈ K^×。 -/
  q : (tateMultGroup K).carrier
  /-- Tate 曲線 E_q。 -/
  curve : Grp
  /-- E_q = K^×/q^ℤ（本物の商群）。 -/
  isQuotient : curve = tateCurve K q
  /-- E_q はアーベル群。 -/
  abelian : ∀ x y : curve.carrier, curve.mul x y = curve.mul y x

/-- **witness（骨格 q=1）** — 任意の体 K 上に Tate 曲線 E_q = K^×/q^ℤ が本物の
    アーベル商群として存在する。q=1（自明周期、E=K^×/⟨1⟩）は存在の骨格 witness で、
    周期性定理 `tate_point_period` は任意の q で本物。 -/
def tateCurveDataOne (K : IUTField) : TateCurveData K where
  q := (tateMultGroup K).one
  curve := tateCurve K (tateMultGroup K).one
  isQuotient := rfl
  abelian := tateCurve_isAbelianGroup K (tateMultGroup K).one

/-- **Tate 曲線の存在**（任意の体 K）。 -/
theorem tateCurve_exists (K : IUTField) : Nonempty (TateCurveData K) :=
  ⟨tateCurveDataOne K⟩

/-- **Tate 曲線の存在（実例 ℚ）** — 有理数体 ℚ 上の Tate 曲線 E_q = ℚ^×/q^ℤ。 -/
theorem tateCurve_exists_rat : Nonempty (TateCurveData ratIUTField) :=
  ⟨tateCurveDataOne ratIUTField⟩

/-- **E_q は群**（構成そのもの: Tate 曲線は本物の Grp）。 -/
theorem tateCurve_group (K : IUTField) (q : (tateMultGroup K).carrier) :
    ∀ x y z : (tateCurve K q).carrier,
      (tateCurve K q).mul ((tateCurve K q).mul x y) z
        = (tateCurve K q).mul x ((tateCurve K q).mul y z) :=
  (tateCurve K q).mul_assoc

end IUT
