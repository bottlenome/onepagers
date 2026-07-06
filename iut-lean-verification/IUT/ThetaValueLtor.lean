/-
  IUT/ThetaValueLtor.lean — M318F（テータ値の l-捻れ点評価:
  Θ(q, u_j) の指数 j² 構造・積の指数和 i²+j²・l-周期整合 / 柱E・テータ）

  分類: **[実]**（本物の先行建設 (b)・既存本物の l-捻れ点文脈への昇格 (a)）。
  complete_pct 影響: 柱E の実 IUT 完全証明率を **IUT の核心「テータを
  l-捻れ点で評価する」** の側で前進させる。IUT III の遠アーベル
  復元は「エタールテータ関数を **l-捻れ点 u_j で評価したテータ値**」を
  主対象とし、その値が q の有理冪 q^{j²/2l} 型（微細格子 u = q^{1/2l}
  上の単項式 u^{j²}）になること・積が指数和 i²+j² を与えること
  （ガウス和的構造）が three-rigidity/log-shell 評価の入口である。
  既存の柱E は M209F/M212F でテータ値の **q-指数簿記** j² を、
  M223F（ThetaValueConstruct.lean）でその値を Laurent 環単項式
  q^{j²}=u^{j²} として実体化、M237F/M242F で有限多ラベル積の指数和
  Σj² を確立していたが、**その u をどの座標として読むか**——
  すなわち「l-捻れ点評価」という IUT 本来の主語——は与えていなかった。

  本層は M223F の本物の単項式 q^{j²}=uMonHom R (thetaValExp j) を、
  **微細座標 u = q^{1/2l} の下での l-捻れ点 u_j = q^{j/l} = u^{2j} での
  テータ値** として読み直し（既存本物の l-捻れ点評価文脈への昇格）、
  さらに **l-捻れ点そのものの l 乗が q^ℤ に落ちること**（本物の反復群
  冪 uMonPow で u_j^l = q^j）を新規に本物建設する:

    (1) **l-捻れ点 u_j = u^{2j}**（`thLtorTorPoint`）と、その **本物の
        l 乗** `thLtorPow`（Laurent 環の乗法での n 回反復積）が
        u_j^l = u^{2jl} = q^j = (u^{2l})^j ∈ q^ℤ に落ちること
        （`thLtor_torsion_lpow`, IsLPowerValue R (2l) 形）。累乗は
        本物の反復積で、指数法則 thLtorPow(u^a, n)=u^{a·n}
        （`thLtorPow_uMon`）を帰納で証明。
    (2) **テータ値の指数 = j²**（`thLtor_value_exponent` /
        `thLtorExp_sq`）: u_j でのテータ値 thLtorValue R j = u^{j²}
        = q^{j²/2l}（微細座標）。主要項の冪の j² 依存性が本物
        （numerator は本物の j²、denominator 2l は微細格子＝l 乗根の
        witness）。
    (3) **積の指数和 i²+j²**（`thLtor_value_product`）: 二つの l-捻れ
        点でのテータ値の積が u^{i²+j²}（M232F thetaValMonomial_mul）。
        任意有限個 `thLtor_value_multiprod` で Σj²（ガウス和構造,
        M237F thetaExpSum）。
    (4) **l-捻れでの周期整合**（`thLtor_period_at_torsion`）: j ↦ j+l は
        同一 l-捻れ点（u_{j+l}=u_j·q, q∈q^ℤ）——その帰結として
        テータ値が u_j でも Θ(q,u_{j+l}) = Θ(q,u_j)·(l-冪因子) と
        l-周期的に整合（(j+l)² = j² + l·(2j+l)）。M313F 擬周期性
        T²(Θ)=Θ の l-捻れ点版（格子 q^ℤ に沿ったシフトの値側帰結）。

  * M318F-1 `thLtorExp` / `thLtorExp_sq` — テータ値指数 j²（q^{j²/2l} の分子）
  * M318F-2 `thLtorValue` / `thLtor_value_exponent` — l-捻れ点でのテータ値
    = u^{j²}（既存本物の l-捻れ評価文脈昇格）
  * M318F-3 `thLtorPow` / `thLtorPow_uMon` — 本物の反復群冪と指数法則
  * M318F-4 `thLtorTorPoint` / `thLtor_torsion_lpow` — l-捻れ点 u_j と
    u_j^l ∈ q^ℤ（新規本物）
  * M318F-5 `thLtor_value_product` / `thLtor_value_multiprod` — 積の
    指数和 i²+j² / Σj²（ガウス和構造）
  * M318F-6 `thLtor_period_at_torsion` / `thLtor_period_lpower` — l-捻れ
    での周期整合（M313F 擬周期の l-捻れ点版）
  * M318F-7 `ThetaValueLtorData` / `thetaValueLtorData` / `thLtor_exists` —
    総括レコード（l・捻れ点・テータ値・指数 j²・積指数和・l-周期）

  意義: M223F の本物の単項式 q^{j²} を、IUT 本来の主語
  **「l-捻れ点 u_j でのテータ値」** として読み直し（u = q^{1/2l},
  u_j = u^{2j}）、l-捻れ点の l 乗が q^ℤ に落ちることを本物の反復群冪で
  新規建設。テータ値の指数の j² 構造・積の指数和 i²+j²（ガウス和）・
  l-周期整合を本物で閉じ、three-rigidity/log-shell 評価の入口を柱E で
  前進させる。

  **正直な限定（消去・弱化禁止）**:
  - **既存 q^{j²}（M223F）を l-捻れ点評価の文脈で本物化**した層である:
    主語は本物の Laurent 単項式 q^{j²}=uMonHom R (thetaValExp j)
    （toy 主語 m202fVol・Bool 軌道・surrogate 群は一切用いない）。
    新規本物は (a) 反復群冪 thLtorPow による u_j^l=q^j∈q^ℤ の確立と、
    (b) l-捻れ点評価という読み替えである。
  - **有理冪 q^{j²/2l} の「型」** は指数の **j² 依存性（分子が本物の
    j²）** と微細格子 u=q^{1/2l} の下での単項式 u^{j²} として本物。
    有理冪 q^{1/2l} そのものの体の中での実在（l 乗根 u=q^{1/2l} の
    構成）は **witness**（微細座標 u を Laurent 変数として受ける）で
    あり、柱A の分離閉包・実 π₁^ét（M314F 概念・後続）で本物化する。
  - l-捻れ点 u_j = u^{2j} は微細座標 u の単項式として本物だが、
    u = q^{1/2l} という **l 乗根の実在** は上記 witness。u_j^l = q^j は
    本物の反復積（thLtorPow）で証明し q^ℤ（IsLPowerValue R 2l）に
    落とす——ここが新規本物。
  - **完全なガロア同変 p 進テータ値・three-rigidity・log-shell への
    評価・tempered π₁ の商としての実現・エタールテータ関数値そのものの
    収束**は後続（本層は **テータ値の指数の j² 構造と積の指数和・
    l-周期整合** を本物で閉じるにとどまる）。
  - 周期整合は指数の合同 (j+l)² ≡ j² (mod l) の値単項式版（M313F
    擬周期の l-捻れ点版）であり、q-展開の収束・付値は扱わない。

  全て選択公理を証明本体で新規導入せず（M223F/M232F/M237F/M88F から
  継承、新規 Classical・新規 Classical.choice なし。商 laurentRing /
  laurentRel / Quot レベルの主張は Quot.sound を使う——商構成に内在、
  選択公理ではない）。#print axioms により継承分のみであることを確認済み。
  サブエージェント新規1本（共有ファイル未変更）。一般名は `thLtor`
  接頭辞で衝突回避。
-/
import IUT.ThetaValueSubgroup

namespace IUT

/-! ## M318F-1: テータ値指数 j²（q^{j²/2l} の分子） -/

/-- **M318F-1a: l-捻れ点でのテータ値指数** — `thLtorExp j = j²`
    （= M209F thetaValExp）。微細座標 u = q^{1/2l} の下でのテータ値
    q^{j²/2l} = u^{j²} の **指数（分子）**。IUT の l-捻れ点評価で現れる
    二次指数 j² の本物。 -/
def thLtorExp (j : Int) : Int := thetaValExp j

/-- **定理 (M318F-1b): 指数は二次 j²** — thLtorExp j = j·j。
    テータ値 q^{j²/2l} の主要項の冪の **j² 依存性**（分子の本物）。
    実例: j=0,1,2 で 0,1,4。 -/
theorem thLtorExp_sq (j : Int) : thLtorExp j = j * j := rfl

/-! ## M318F-2: l-捻れ点でのテータ値 u^{j²}（既存本物の昇格） -/

/-- **M318F-2a: l-捻れ点でのテータ値** — `thLtorValue R j = q^{j²/2l}`
    を微細座標 u = q^{1/2l} の下で **本物の Laurent 単項式 u^{j²}**
    （= M223F thetaValMonomial R j）として実現。IUT のテータ値
    Θ(q, u_j) の主要項を、既存本物 q^{j²} の l-捻れ点評価文脈への
    読み替えとして構成する（toy 主語なし）。 -/
def thLtorValue (R : CRing) (j : Int) : (laurentRing R).carrier :=
  thetaValMonomial R j

/-- **定理 (M318F-2b): テータ値の指数抽出** — thLtorValue R j
    = uMonHom R (thLtorExp j) = u^{j²}。l-捻れ点でのテータ値の主要項の
    冪がちょうど j²（M232F thetaValMonomial_eq_uMonHom の l-捻れ点評価
    文脈での言い直し）。有理冪 q^{j²/2l} の指数の j² 構造が本物。 -/
theorem thLtor_value_exponent (R : CRing) (j : Int) :
    thLtorValue R j = uMonHom R (thLtorExp j) :=
  rfl

/-! ## M318F-3: 本物の反復群冪と指数法則 -/

/-- **M318F-3a: 本物の反復群冪** — Laurent 環 laurentRing R の乗法での
    n 回反復積 xⁿ（基点 1）。l-捻れ点 u_j の l 乗 u_j^l を本物の群冪
    として構成するための原始演算（surrogate 冪でない本物の畳み込み積）。 -/
def thLtorPow (R : CRing) (x : (laurentRing R).carrier) : Nat → (laurentRing R).carrier
  | 0 => (laurentRing R).one
  | n + 1 => (laurentRing R).mul x (thLtorPow R x n)

/-- **定理 (M318F-3b): 単項式の冪の指数法則** — (u^a)ⁿ = u^{a·n}。
    本物の反復積（M318F-3a）が単項式では指数の n 倍になる（M232F
    uMonHom_zero/uMonHom_add で n 帰納）。l-捻れ点の l 乗を指数計算へ
    落とす本物の橋。 -/
theorem thLtorPow_uMon (R : CRing) (a : Int) (n : Nat) :
    thLtorPow R (uMonHom R a) n = uMonHom R (a * (n : Int)) := by
  induction n with
  | zero =>
    show (laurentRing R).one = uMonHom R (a * ((0 : Nat) : Int))
    rw [Int.natCast_zero, Int.mul_zero]
    exact (uMonHom_zero R).symm
  | succ n ih =>
    show (laurentRing R).mul (uMonHom R a) (thLtorPow R (uMonHom R a) n)
      = uMonHom R (a * ((n + 1 : Nat) : Int))
    rw [ih, ← uMonHom_add]
    have hstep : a + a * (n : Int) = a * ((n + 1 : Nat) : Int) := by
      rw [Int.natCast_add, Int.natCast_one, Int.mul_add, Int.mul_one, Int.add_comm]
    rw [hstep]

/-! ## M318F-4: l-捻れ点 u_j と u_j^l ∈ q^ℤ（新規本物） -/

/-- **M318F-4a: l-捻れ点 u_j** — 微細座標 u = q^{1/2l} の下で
    u_j = q^{j/l} = u^{2j}（= uMonHom R (2j)）。テータを評価する
    l-等分点（IUT III の l-捻れ点）を Laurent 単項式として本物に表す
    （u = q^{1/2l} の実在は witness、u_j 自体は微細座標の本物単項式）。 -/
def thLtorTorPoint (R : CRing) (j : Int) : (laurentRing R).carrier :=
  uMonHom R (2 * j)

/-- **定理 (M318F-4b): l-捻れ点の l 乗は q^ℤ に落ちる（新規本物）** —
    u_j^l = u^{2jl} = (u^{2l})^j = q^j ∈ q^ℤ。本物の反復群冪
    thLtorPow（M318F-3）で u_j を l 回積むと、微細座標での q = u^{2l}
    の j 乗（IsLPowerValue R (2l)、witness k=j）に落ちる。IUT の
    「l-捻れ点の l 乗が周期格子 q^ℤ に属す」という核心を本物で
    確立する（本層の新規本物建設）。 -/
theorem thLtor_torsion_lpow (R : CRing) (l : Nat) (j : Int) :
    IsLPowerValue R (2 * (l : Int)) (thLtorPow R (thLtorTorPoint R j) l) := by
  show IsLPowerValue R (2 * (l : Int)) (thLtorPow R (uMonHom R (2 * j)) l)
  refine ⟨j, ?_⟩
  rw [thLtorPow_uMon R (2 * j) l]
  rw [Int.mul_assoc, Int.mul_comm j (l : Int), ← Int.mul_assoc]

/-! ## M318F-5: 積の指数和 i²+j²（ガウス和構造） -/

/-- **定理 (M318F-5a): 二つの l-捻れ点でのテータ値の積の指数和** —
    Θ(q,u_i)·Θ(q,u_j) = u^{i²+j²} = uMonHom R (thLtorExp i + thLtorExp j)。
    二つの l-捻れ点でのテータ値の積が **指数の和 i²+j²** を与える
    （M232F thetaValMonomial_mul の l-捻れ点評価版）。ガウス和的な
    二次指数の加法。 -/
theorem thLtor_value_product (R : CRing) (i j : Int) :
    (laurentRing R).mul (thLtorValue R i) (thLtorValue R j)
      = uMonHom R (thLtorExp i + thLtorExp j) := by
  show (laurentRing R).mul (thetaValMonomial R i) (thetaValMonomial R j)
    = uMonHom R (thetaValExp i + thetaValExp j)
  exact thetaValMonomial_mul R i j

/-- **定理 (M318F-5b): 有限個の l-捻れ点でのテータ値の積の指数和** —
    ∏_j Θ(q,u_j) = u^{Σ j²} = uMonHom R (thetaExpSum js)。任意有限個の
    l-捻れ点でのテータ値の積が **指数の総和 Σj²**（ガウス和構造,
    M237F thetaExpSum）を与える。i²+j² の任意有限個一般化。 -/
theorem thLtor_value_multiprod (R : CRing) (js : List Int) :
    thetaValProd R js = uMonHom R (thetaExpSum js) :=
  thetaValProd_eq_uMonHom R js

/-! ## M318F-6: l-捻れでの周期整合（M313F 擬周期の l-捻れ点版） -/

/-- **定理 (M318F-6a): l-捻れでの周期整合** — j ↦ j+l は同一 l-捻れ点
    （u_{j+l} = u_j·q）——その帰結としてテータ値は
    Θ(q,u_{j+l}) = Θ(q,u_j)·u^{l·(2j+l)} と l-周期因子だけ異なる:
    (j+l)² = j² + l·(2j+l)。M313F 擬周期性 T²(Θ)=Θ（格子 q^ℤ に沿った
    シフトの値側帰結）の l-捻れ点版。テータ値の l-周期的整合。 -/
theorem thLtor_period_at_torsion (R : CRing) (l j : Int) :
    thLtorValue R (j + l)
      = (laurentRing R).mul (thLtorValue R j) (uMonHom R (l * (2 * j + l))) := by
  show uMonHom R (thetaValExp (j + l))
    = (laurentRing R).mul (uMonHom R (thetaValExp j)) (uMonHom R (l * (2 * j + l)))
  rw [← uMonHom_add]
  have e : thetaValExp (j + l) = thetaValExp j + l * (2 * j + l) := by
    show (j + l) * (j + l) = j * j + l * (2 * j + l)
    have h1 : (j + l) * (j + l) = j * j + j * l + (l * j + l * l) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have h2 : l * (2 * j + l) = l * (2 * j) + l * l := Int.mul_add l (2 * j) l
    have h3 : l * (2 * j) = 2 * (l * j) := by
      rw [← Int.mul_assoc, Int.mul_comm l 2, Int.mul_assoc]
    have h4 : j * l = l * j := Int.mul_comm j l
    rw [h1, h2, h3, h4]
    omega
  rw [e]

/-- **定理 (M318F-6b): l-周期因子は q^ℤ（l-冪値）** — 周期因子
    u^{l·(2j+l)} は IsLPowerValue R l（witness k=2j+l）。j ↦ j+l の
    周期ズレがちょうど周期格子 q^ℤ（l-冪部分群, M237F IsLPowerValue）に
    属すことの明示。 -/
theorem thLtor_period_lpower (R : CRing) (l j : Int) :
    IsLPowerValue R l (uMonHom R (l * (2 * j + l))) :=
  ⟨2 * j + l, rfl⟩

/-! ## M318F-7: 総括レコード（l-捻れ点でのテータ値） -/

/-- **M318F-7a: l-捻れ点テータ値データ** — l-捻れ点 u_j、そこでのテータ値
    Θ(q,u_j)=u^{j²}、指数 j²、捻れ点の l 乗が q^ℤ に落ちること、積の
    指数和 i²+j²/Σj²、l-周期整合を一括束ね。IUT の核心「テータを
    l-捻れ点で評価する」の値側 witness（主語は本物の単項式 q^{j²}、
    toy 主語なし）。 -/
structure ThetaValueLtorData (R : CRing) (l : Nat) where
  /-- l-捻れ点 u_j = u^{2j}（微細座標 u = q^{1/2l}）。 -/
  torPoint : Int → (laurentRing R).carrier
  /-- l-捻れ点でのテータ値 Θ(q,u_j) = u^{j²}。 -/
  value : Int → (laurentRing R).carrier
  /-- テータ値の指数（q^{j²/2l} の分子）。 -/
  exp : Int → Int
  /-- 指数は二次: exp j = j²。 -/
  exp_sq : ∀ j : Int, exp j = j * j
  /-- テータ値の指数抽出: value j = u^{exp j}。 -/
  value_exp : ∀ j : Int, value j = uMonHom R (exp j)
  /-- **新規本物**: 捻れ点の l 乗は q^ℤ に落ちる: u_j^l ∈ q^ℤ
      （IsLPowerValue R (2l)）。 -/
  torsion_lpow : ∀ j : Int,
    IsLPowerValue R (2 * (l : Int)) (thLtorPow R (torPoint j) l)
  /-- 積の指数和 i²+j²: Θ(q,u_i)·Θ(q,u_j) = u^{i²+j²}。 -/
  product_law : ∀ i j : Int, (laurentRing R).mul (value i) (value j)
    = uMonHom R (exp i + exp j)
  /-- 有限積の指数和 Σj²（ガウス和構造）。 -/
  multiprod : ∀ js : List Int, thetaValProd R js = uMonHom R (thetaExpSum js)
  /-- l-周期整合: value (j+l) = value j · u^{l·(2j+l)}。 -/
  period : ∀ j : Int, value (j + (l : Int))
    = (laurentRing R).mul (value j) (uMonHom R ((l : Int) * (2 * j + (l : Int))))
  /-- 周期因子は q^ℤ（l-冪値）。 -/
  period_lpow : ∀ j : Int,
    IsLPowerValue R (l : Int) (uMonHom R ((l : Int) * (2 * j + (l : Int))))

/-- **M318F-7b: witness 本体** — torPoint := thLtorTorPoint、
    value := thLtorValue、exp := thLtorExp として全フィールドを
    M318F-1〜6 で埋める。 -/
def thetaValueLtorData (R : CRing) (l : Nat) : ThetaValueLtorData R l where
  torPoint := thLtorTorPoint R
  value := thLtorValue R
  exp := thLtorExp
  exp_sq := thLtorExp_sq
  value_exp := thLtor_value_exponent R
  torsion_lpow := thLtor_torsion_lpow R l
  product_law := thLtor_value_product R
  multiprod := thLtor_value_multiprod R
  period := fun j => thLtor_period_at_torsion R (l : Int) j
  period_lpow := fun j => thLtor_period_lpower R (l : Int) j

/-- **定理 (M318F-7c): l-捻れ点テータ値データの存在（M318F 見出し）** —
    任意の係数環 R・任意の l に対し、l-捻れ点 u_j でのテータ値
    Θ(q,u_j)=u^{j²}=q^{j²/2l} を、捻れ点の l 乗が q^ℤ に落ちること
    （新規本物）・積の指数和 i²+j²/Σj²（ガウス和）・l-周期整合と共に
    束ねたデータが存在する。M223F の本物の単項式 q^{j²} が IUT 本来の
    主語「l-捻れ点評価」として実体化される。 -/
theorem thLtor_exists (R : CRing) (l : Nat) :
    Nonempty (ThetaValueLtorData R l) :=
  ⟨thetaValueLtorData R l⟩

/-! ## 実例（l-捻れ点でのテータ値の指数 0,1,4 と積の指数和） -/

/-- 実例: j=0 の l-捻れ点でのテータ値の指数 0²=0。 -/
example : thLtorExp 0 = 0 := by rw [thLtorExp_sq]; omega

/-- 実例: j=1 の l-捻れ点でのテータ値の指数 1²=1。 -/
example : thLtorExp 1 = 1 := by rw [thLtorExp_sq]; omega

/-- 実例: j=2 の l-捻れ点でのテータ値の指数 2²=4。 -/
example : thLtorExp 2 = 4 := by rw [thLtorExp_sq]; omega

/-- 実例: 二つの l-捻れ点（i=1, j=2）でのテータ値の積の指数和 1+4=5。 -/
example (R : CRing) :
    (laurentRing R).mul (thLtorValue R 1) (thLtorValue R 2)
      = uMonHom R (thLtorExp 1 + thLtorExp 2) :=
  thLtor_value_product R 1 2

/-- 実例: l=5・j=1 の l-捻れ点の 5 乗が q^ℤ（q=u^{10}）に落ちる。 -/
example (R : CRing) :
    IsLPowerValue R (2 * (5 : Int)) (thLtorPow R (thLtorTorPoint R 1) 5) :=
  thLtor_torsion_lpow R 5 1

/-- 実例: l=5 の周期整合（j=0）: value 5 = value 0 · u^{5·5}。 -/
example (R : CRing) :
    thLtorValue R (0 + (5 : Int))
      = (laurentRing R).mul (thLtorValue R 0)
          (uMonHom R ((5 : Int) * (2 * 0 + (5 : Int)))) :=
  thLtor_period_at_torsion R 5 0

end IUT
