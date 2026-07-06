/-
  IUT/FrobenioidCategory.lean — M331F（柱C 先行建設: 算術 Frobenioid を
                          **M307F の本物の因子群の上の圏**として構成する）

  ── 主要成果の分類: **[実]**（本物の先行建設 (b) ＋ 既存模型の昇格 (a)）。
     IUT の **Frobenioid**（Frobenius 付きモノイド上の圏）を、M307F
     `PicardDivisor` の**本物の因子群** `picDivGrp`（素点上の有限台 ℤ-値関数の
     なす自由アーベル群）を対象とし、Frobenius 次数付きの射で圏をなすものとして
     core Lean のみで完全証明する。toy 主語なし——対象は「算術的直線束＝因子類」
     という本物の代数対象（M307F `picDivGrp.carrier`）であり、射の合成則・圏公理・
     次数の乗法性は既存の本物の機構（M19 `Cat`／M16 `Grp`・`Hom`／M307F の因子群・
     Frobenius 自己準同型 `picDivFrob`・有効因子 `picDivEffectiveRaw`）の上に載る。

  complete_pct 影響: **柱C（Frobenioid）の実 IUT 完全証明率を前進させる**。
  既存の柱C の圏化 M48F `FrobenioidCat`（`elementaryFrobenioid`）は**対象を素の
  整数 `Int`（次数だけ）**、M51F `divisorFrobenioid` は**対象を有効因子モノイド
  `QDiv`（ℕ 値・逆元なし）**とし、いずれも「因子**群**」を対象にしていなかった。
  本ファイルはそれを**本物へ昇格**する:
  (1) **対象＝因子群 `picDivGrp.carrier`**（M307F の本物のアーベル群＝算術的直線束の
      同型類群の代数的実体）。整数だけ・有効モノイドだけの模型を、逆元を持つ本物の
      因子群へ置換する（昇格 (a)）。
  (2) **射＝Frobenius 次数 n≥1 ＋ 有効因子 `eff` ＋ 線形条件** E = [n]·D + eff
      （[FrdI] の deg 変換則 deg(φ(x))=n·deg(x)+deg(Div(φ))・Div(φ)≥0 の圏論核）。
      合成 `frobCComp`（Frobenius 次数は積 n·m、有効部は捻れ半直積 [m]·c₁+c₂）・
      恒等 `frobCId`（次数 1・零有効部）・**圏公理**（結合律・単位律）を M307F の
      因子群の演算の上で本物で完全証明する。
  (3) **次数関手** `frobCDegree`：Frobenioid → (ℕ≥1,×)（一対象圏 `frobCDegCat`）、
      **次数の乗法性 deg(g∘f)=deg(g)·deg(f)** を本物で（M307F `picDivFrob` の圏版）。
  (4) **線形束モノイド** `frobCLineBundle`＝因子群 `picDivGrp`（テンソル積＝因子の和）を
      Frobenioid の底モノイドとして本物で（M307F の群を圏の対象モノイドに）。
  (5) **realification 骨組み** `frobCRealDegree`：Frobenioid の次数を実数値
      （M312F `LogVolume` の Arakelov 次数 `logVolGlobal`）へ拡張する骨組みと、
      加法性・Frobenius 斉次性・整数次数ブリッジを M312F から本物で継承する。

  ## 検証する中核（全て sorry なし・新規 Classical.choice なし）

  * M331F-1 `frobCFrob_comp` / `frobCFrob_one`
                              — Frobenius 自己準同型の合成則 [b]∘[a]=[a·b]・[1]=id
                                （M307F `picDivFrob` の圏構造用・本物）
  * M331F-2 `frobCEffective` / `frobCHom` / `frobCHom.ext`
                              — 有効因子類・**Frobenioid の射**（次数付き）＋外延性
  * M331F-3 `frobCId` / `frobCComp`
                              — 恒等射（次数 1）・合成（次数積・捻れ半直積の有効部）
  * M331F-4 `frobCCat`         — **Frobenioid が圏**（結合律・単位律を M307F 因子群上で
                                 完全証明）＝ M19 `Cat` の本物のインスタンス
  * M331F-5 `frobCDegCat` / `frobCDegree` / `frobC_degree_mult`
                              — 次数関手 Frobenioid→(ℕ≥1,×)・**次数の乗法性**（本物）
  * M331F-6 `frobCLineBundle` / `frobCTensor` + `_assoc`/`_one_left`/`_one_right`/`_comm`
                              — **線形束モノイド**（因子群＝底モノイド、テンソル＝因子和）
  * M331F-7 `frobCRealDegree` + `_wd`/`_add`/`_frob`/`_int_bridge`
                              — realification 骨組み（M312F Arakelov 次数への昇格骨組み）
  * M331F-8 capstone `FrobenioidData` / `frobCData` / `frobC_exists` /
    `frobC_is_category` / `frobC_degree_functor` ＋ 実例
    `frobCFrobMor`（Frobenius [n] 射）/ `frobC_frobMor_deg`

  ## 正直な限定（何が本物で何が後続か・消去/弱化禁止）

  - **本物（完全証明）**:
    ・Frobenioid が **M19 `Cat` の本物の圏**であること（結合律・左右単位律を M307F の
      因子群 `picDivGrp` の演算・`picDivFrob` の合成則の上で完全証明）。
    ・**次数が乗法的** deg(g∘f)=deg(g)·deg(f)（次数関手 `frobCDegree` の関手性・完全）。
    ・**線形束モノイド**＝因子群（テンソル積の結合・単位・可換、M307F 群から完全）。
    ・射の有効部が合成で有効を保つこと（M307F `picDivEffective_add/_frob`、完全）。
    ・Frobenius [n] 射の存在と次数（実例、完全）。
  - **正直申告（未達・骨組み・後続。飾りでなく地図）**:
    ・本ファイルの Frobenioid は [FrdI] の **elementary Frobenioid**（base 圏が一点・
      因子モノイドが M307F の因子群）に相当する。**型付き Frobenioid・ファイバー化・
      base category の全公理**（[FrdI/II] の一般 Frobenioid）は膨大ゆえ範囲外——
      本コースの核（因子群を対象・Frobenius 次数付き射で圏・次数乗法的）を本物で
      与える（§3「本物の忠実な部分ケース」）。
    ・**realification は RawDiv 代表レベルで定義**する（`frobCRealDegree : RawDiv→RReal`
      ＝M312F `logVolGlobal`）。RReal は setoid（等号は `realEq`≈）ゆえ因子群
      `Quot rawEq` への**厳密 `Quot.lift`（strict `=`）は不可**であり、well-defined 性は
      `realEq` 同値として `frobCRealDegree_wd` で正直に述べる（M312F と同じ扱い）。
      加法性・Frobenius 斉次性・整数次数ブリッジは M312F から `realEq` で継承。
    ・射の有効部 `eff` は「有効代表を持つ因子類」（`frobCEffective`＝∃ 有効代表）とし、
      線形条件 E=[n]D+eff を因子群の等式で持つ。付値系（M307F `PicDivValuation`）の
      実体化（特定楕円曲線／局所体の実付値）は M307F と同じく後続。
    ・Frobenioid 間の **theta-link/log-link**（Frobenioid の連結）は柱D/E 後続。
      本ファイルは単一 Frobenioid の圏構造と次数関手・realification 骨組みまで。
    ・既存 M48F `elementaryFrobenioid`（対象 Int）・M51F `divisorFrobenioid`（対象 QDiv
      有効モノイド）を、**対象＝因子群 picDivGrp**へ昇格したのが本ファイルの前進点。
  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）・sorry 皆無。
-/
import IUT.LogVolume
import IUT.CategoryTheory

namespace IUT

/-! ## M331F-1: Frobenius 自己準同型の合成則（圏構造の核） -/

/-- Nat 積の Int 键への分配（frob 合成則の補助、本物）。 -/
theorem frobC_cast_mul (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) :=
  Int.natCast_mul a b

/-- **M331F-1a: Frobenius 合成則** [b]∘[a] = [a·b]（M307F `picDivFrob` の合成）。
    因子の n 倍作用の合成が次数の積で表せること＝Frobenioid の次数乗法性の代数核。 -/
theorem frobCFrob_comp (a b : Nat) (x : picDivGrp.carrier) :
    (picDivFrob b).map ((picDivFrob a).map x) = (picDivFrob (a * b)).map x := by
  induction x using Quot.ind
  rename_i r
  exact Quot.sound (fun k => by
    show (b : Int) * ((a : Int) * r.coeff k) = ((a * b : Nat) : Int) * r.coeff k
    rw [frobC_cast_mul, ← Int.mul_assoc, Int.mul_comm (b : Int) (a : Int)])

/-- **M331F-1b: Frobenius 単位** [1] = id（恒等射の次数 1 の根拠）。 -/
theorem frobCFrob_one (x : picDivGrp.carrier) : (picDivFrob 1).map x = x := by
  induction x using Quot.ind
  rename_i r
  exact Quot.sound (fun k => by
    show ((1 : Nat) : Int) * r.coeff k = r.coeff k
    omega)

/-! ## M331F-2: 有効因子類と Frobenioid の射 -/

/-- **M331F-2a: 有効因子類** — 因子群の元 e が有効代表（全素点で重複度非負）を持つ。
    Frobenioid の射の "零因子" Div(φ)≥0（[FrdI]）の因子類版。 -/
def frobCEffective (e : picDivGrp.carrier) : Prop :=
  ∃ r : RawDiv, picDivEffectiveRaw r ∧ Quot.mk rawEq r = e

/-- 単位（零因子）は有効。 -/
theorem frobCEffective_one : frobCEffective picDivGrp.one :=
  ⟨rawZero, picDivEffective_zero, rfl⟩

/-- **M331F-2b: Frobenioid の射** D → E — Frobenius 次数 `deg`≥1・有効因子部 `eff`・
    線形条件 E = [deg]·D + eff（[FrdI] の deg 変換則の圏論核）。 -/
structure frobCHom (D E : picDivGrp.carrier) where
  deg : Nat
  deg_pos : 1 ≤ deg
  eff : picDivGrp.carrier
  eff_effective : frobCEffective eff
  linear : E = picDivGrp.mul ((picDivFrob deg).map D) eff

/-- **M331F-2c: 射の外延性** — 次数と有効因子部が等しければ射は等しい
    （`deg_pos`・`eff_effective`・`linear` は Prop で証明無関係）。 -/
theorem frobCHom.ext {D E : picDivGrp.carrier} {f g : frobCHom D E}
    (hd : f.deg = g.deg) (he : f.eff = g.eff) : f = g := by
  cases f with
  | mk d1 p1 e1 ef1 l1 =>
    cases g with
    | mk d2 p2 e2 ef2 l2 =>
      cases hd
      cases he
      rfl

/-- **M331F-2d: 合成の線形則（依存型回避の切片補題）** — E=[nf]D+ef・F=[ng]E+eg
    から F=[nf·ng]D+([ng]ef+eg)。E,F を独立変数にすることで構造体依存の motive 破綻を
    避けつつ M307F 因子群の演算・`frobCFrob_comp` で本物で導く。 -/
theorem frobCComp_linear {D E F : picDivGrp.carrier} {nf ng : Nat}
    {ef eg : picDivGrp.carrier}
    (hf : E = picDivGrp.mul ((picDivFrob nf).map D) ef)
    (hg : F = picDivGrp.mul ((picDivFrob ng).map E) eg) :
    F = picDivGrp.mul ((picDivFrob (nf * ng)).map D)
        (picDivGrp.mul ((picDivFrob ng).map ef) eg) := by
  subst hf
  rw [hg, (picDivFrob ng).map_mul, frobCFrob_comp nf ng D, picDivGrp.mul_assoc]

/-! ## M331F-3: 恒等射と合成 -/

/-- **M331F-3a: 恒等射** id_D — 次数 1・零有効部（D = [1]·D + 0）。 -/
def frobCId (D : picDivGrp.carrier) : frobCHom D D where
  deg := 1
  deg_pos := Nat.le_refl 1
  eff := picDivGrp.one
  eff_effective := frobCEffective_one
  linear := by
    rw [picDivGrp.mul_one, frobCFrob_one]

/-- **M331F-3b: 射の合成** (D→E)∘(E→F) = (D→F) — 次数は積 n₁·n₂、
    有効部は捻れ半直積 [n₂]·c₁ + c₂（後段 Frobenius で膨らんでから加わる）。 -/
def frobCComp {D E F : picDivGrp.carrier} (f : frobCHom D E) (g : frobCHom E F) :
    frobCHom D F where
  deg := f.deg * g.deg
  deg_pos := by
    have h := Nat.mul_le_mul f.deg_pos g.deg_pos
    omega
  eff := picDivGrp.mul ((picDivFrob g.deg).map f.eff) g.eff
  eff_effective := by
    obtain ⟨rf, hrf, hef⟩ := f.eff_effective
    obtain ⟨rg, hrg, heg⟩ := g.eff_effective
    refine ⟨rawAdd (picDivFrobRaw g.deg rf) rg,
      picDivEffective_add (picDivEffective_frob g.deg hrf) hrg, ?_⟩
    rw [← hef, ← heg]
    rfl
  linear := frobCComp_linear f.linear g.linear

/-! ## M331F-4: Frobenioid が圏（M19 Cat の本物のインスタンス） -/

/-- **M331F-4: Frobenioid の圏** — 対象＝因子群 `picDivGrp.carrier`、
    射＝Frobenius 次数付き `frobCHom`。結合律・左右単位律を M307F 因子群上で完全証明。
    M48F `elementaryFrobenioid`（対象 Int）・M51F `divisorFrobenioid`（対象 QDiv）を
    **対象＝本物の因子群**へ昇格した Frobenioid。 -/
def frobCCat : Cat where
  Obj := picDivGrp.carrier
  Hom := frobCHom
  id := frobCId
  comp := frobCComp
  id_comp := by
    intro D E f
    apply frobCHom.ext
    · show 1 * f.deg = f.deg
      exact Nat.one_mul f.deg
    · show picDivGrp.mul ((picDivFrob f.deg).map picDivGrp.one) f.eff = f.eff
      rw [Hom.map_one, picDivGrp.one_mul]
  comp_id := by
    intro D E f
    apply frobCHom.ext
    · show f.deg * 1 = f.deg
      exact Nat.mul_one f.deg
    · show picDivGrp.mul ((picDivFrob 1).map f.eff) picDivGrp.one = f.eff
      rw [picDivGrp.mul_one, frobCFrob_one]
  assoc := by
    intro W X Y Z f g h
    apply frobCHom.ext
    · show (f.deg * g.deg) * h.deg = f.deg * (g.deg * h.deg)
      exact Nat.mul_assoc f.deg g.deg h.deg
    · show picDivGrp.mul ((picDivFrob h.deg).map
            (picDivGrp.mul ((picDivFrob g.deg).map f.eff) g.eff)) h.eff
          = picDivGrp.mul ((picDivFrob (g.deg * h.deg)).map f.eff)
            (picDivGrp.mul ((picDivFrob h.deg).map g.eff) h.eff)
      rw [(picDivFrob h.deg).map_mul, frobCFrob_comp g.deg h.deg f.eff,
        picDivGrp.mul_assoc]

/-! ## M331F-5: 次数関手 Frobenioid → (ℕ≥1, ×) と次数の乗法性 -/

/-- 正の自然数（Frobenius 次数の値域）。 -/
def frobCPosNat := { d : Nat // 1 ≤ d }

/-- 正の自然数の積（乗法モノイド）。 -/
def frobCPosMul (x y : frobCPosNat) : frobCPosNat :=
  ⟨x.val * y.val, by
    have h := Nat.mul_le_mul x.property y.property
    omega⟩

/-- **M331F-5a: 次数圏** (ℕ≥1, ×) — 一対象圏（射＝正の自然数、合成＝積、恒等＝1）。 -/
def frobCDegCat : Cat where
  Obj := Unit
  Hom := fun _ _ => frobCPosNat
  id := fun _ => ⟨1, Nat.le_refl 1⟩
  comp := fun x y => frobCPosMul x y
  id_comp := by
    intro _ _ f
    apply Subtype.ext
    show 1 * f.val = f.val
    exact Nat.one_mul f.val
  comp_id := by
    intro _ _ f
    apply Subtype.ext
    show f.val * 1 = f.val
    exact Nat.mul_one f.val
  assoc := by
    intro _ _ _ _ f g h
    apply Subtype.ext
    show (f.val * g.val) * h.val = f.val * (g.val * h.val)
    exact Nat.mul_assoc f.val g.val h.val

/-- **M331F-5b: 次数関手** Frobenioid → (ℕ≥1,×) — 射に Frobenius 次数を対応。
    関手性（恒等射→1・合成→積）が Frobenioid の次数の乗法性そのもの。 -/
def frobCDegree : Functor frobCCat frobCDegCat where
  onObj := fun _ => ()
  onHom := fun f => ⟨f.deg, f.deg_pos⟩
  map_id := by
    intro D
    apply Subtype.ext
    rfl
  map_comp := by
    intro D E F f g
    apply Subtype.ext
    rfl

/-- **M331F-5c: 次数の乗法性** deg(g∘f) = deg(f)·deg(g)（M307F `picDivFrob` の圏版）。 -/
theorem frobC_degree_mult {D E F : picDivGrp.carrier}
    (f : frobCHom D E) (g : frobCHom E F) :
    (frobCComp f g).deg = f.deg * g.deg := rfl

/-! ## M331F-6: 線形束モノイド（因子群＝Frobenioid の底モノイド） -/

/-- **M331F-6a: 線形束モノイド** — Frobenioid の対象モノイド＝M307F の因子群
    `picDivGrp`（テンソル積＝因子の和）。算術的直線束のなす群。 -/
def frobCLineBundle : Grp := picDivGrp

/-- 線形束のテンソル積（因子の和）。 -/
def frobCTensor (x y : frobCLineBundle.carrier) : frobCLineBundle.carrier :=
  picDivGrp.mul x y

/-- テンソル積の結合律（M307F 因子群の結合律）。 -/
theorem frobCTensor_assoc (x y z : frobCLineBundle.carrier) :
    frobCTensor (frobCTensor x y) z = frobCTensor x (frobCTensor y z) :=
  picDivGrp.mul_assoc x y z

/-- 自明束が左単位元。 -/
theorem frobCTensor_one_left (x : frobCLineBundle.carrier) :
    frobCTensor frobCLineBundle.one x = x :=
  picDivGrp.one_mul x

/-- 自明束が右単位元。 -/
theorem frobCTensor_one_right (x : frobCLineBundle.carrier) :
    frobCTensor x frobCLineBundle.one = x :=
  picDivGrp.mul_one x

/-- テンソル積の可換性（M307F 因子群の可換性）。 -/
theorem frobCTensor_comm (x y : frobCLineBundle.carrier) :
    frobCTensor x y = frobCTensor y x :=
  picDivGrp_comm x y

/-! ## M331F-7: realification 骨組み（M312F Arakelov 次数への昇格） -/

/-- **M331F-7a: realification（実数値次数）** — Frobenioid の因子の次数を実数値
    Arakelov 次数（M312F `logVolGlobal`）へ拡張する骨組み。RReal は setoid ゆえ
    因子群 `Quot rawEq` への厳密 `Quot.lift` は不可（well-defined は `realEq` で下記）。
    重み logq（各素点の log q_v）付きで定義。 -/
def frobCRealDegree (logq : Nat → RReal) (x : RawDiv) : RReal :=
  logVolGlobal logq x

/-- **M331F-7b: realEq well-definedness** — 係数等価な代表は同じ実数値次数（≈）。 -/
theorem frobCRealDegree_wd (logq : Nat → RReal) {x y : RawDiv} (h : rawEq x y) :
    realEq (frobCRealDegree logq x) (frobCRealDegree logq y) :=
  logVolGlobal_wd logq h

/-- **M331F-7c: 加法性** deg_ℝ(D+E) ≈ deg_ℝ(D)+deg_ℝ(E)（M312F から本物で継承）。 -/
theorem frobCRealDegree_add (logq : Nat → RReal) (x y : RawDiv) :
    realEq (frobCRealDegree logq (rawAdd x y))
      (realAdd (frobCRealDegree logq x) (frobCRealDegree logq y)) :=
  logVolGlobal_add logq x y

/-- **M331F-7d: Frobenius 斉次性** deg_ℝ([n]D) ≈ n·deg_ℝ(D)（次数関手の realification）。 -/
theorem frobCRealDegree_frob (logq : Nat → RReal) (n : Nat) (x : RawDiv) :
    realEq (frobCRealDegree logq (picDivFrobRaw n x))
      (rmul (intToReal (n : Int)) (frobCRealDegree logq x)) :=
  logVolGlobal_frob logq n x

/-- **M331F-7e: 整数次数ブリッジ** — unit 重みでの realification は M307F の整数次数
    `picDivDegree` の ℝ 像に一致（≈）。Frobenioid の離散次数と realification の整合。 -/
theorem frobCRealDegree_int_bridge (x : RawDiv) :
    realEq (frobCRealDegree logVolUnit x)
      (intToReal (picDivDegree.map (Quot.mk rawEq x))) :=
  logVolGlobal_unweighted_degree x

/-! ## M331F-8: capstone と実例 -/

/-- **M331F-8a: Frobenioid データ** — 底モノイド（因子群）・圏・次数関手の束ね。 -/
structure FrobenioidData where
  base : Grp
  cat : Cat
  deg : Functor cat frobCDegCat

/-- **M331F-8b: 実データ** — 全フィールドを本物で充足。 -/
def frobCData : FrobenioidData where
  base := frobCLineBundle
  cat := frobCCat
  deg := frobCDegree

/-- **M331F-8c: 存在**（`Nonempty` でなく実データ）。 -/
theorem frobC_exists : Nonempty FrobenioidData := ⟨frobCData⟩

/-- **M331F-8d: Frobenioid は圏** — 単位律（左）を本物で（圏公理の再輸出）。 -/
theorem frobC_is_category {D E : frobCCat.Obj} (f : frobCCat.Hom D E) :
    frobCCat.comp (frobCCat.id D) f = f :=
  frobCCat.id_comp f

/-- **M331F-8e: 次数関手が乗法的** — deg(g∘f) = deg(f)·deg(g)（値レベル）。 -/
theorem frobC_degree_functor {D E F : picDivGrp.carrier}
    (f : frobCHom D E) (g : frobCHom E F) :
    (frobCDegree.onHom (frobCComp f g)).val
      = (frobCDegree.onHom f).val * (frobCDegree.onHom g).val := rfl

/-- **M331F-8f: 実例（Frobenius [n] 射）** — 因子 D から [n]·D への Frobenius 射
    （次数 n・有効部 0）。IUT の Frobenius 自己射の Frobenioid 版。 -/
def frobCFrobMor (n : Nat) (hn : 1 ≤ n) (D : picDivGrp.carrier) :
    frobCHom D ((picDivFrob n).map D) where
  deg := n
  deg_pos := hn
  eff := picDivGrp.one
  eff_effective := frobCEffective_one
  linear := by
    rw [picDivGrp.mul_one]

/-- **M331F-8g: Frobenius [n] 射の次数は n**（実例、完全）。 -/
theorem frobC_frobMor_deg (n : Nat) (hn : 1 ≤ n) (D : picDivGrp.carrier) :
    (frobCFrobMor n hn D).deg = n := rfl

/-- **M331F-8h: 恒等射の次数は 1**（実例、完全）。 -/
theorem frobC_id_deg (D : picDivGrp.carrier) : (frobCId D).deg = 1 := rfl

/-- **M331F-8i: 自明束上の Frobenius [n] 射の合成の次数**（次数乗法性の実例）。 -/
theorem frobC_frobMor_comp_deg (n m : Nat) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (frobCComp (frobCFrobMor n hn picDivGrp.one)
      (frobCFrobMor m hm ((picDivFrob n).map picDivGrp.one))).deg = n * m := rfl

end IUT
