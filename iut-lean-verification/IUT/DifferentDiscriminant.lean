/-
  IUT/DifferentDiscriminant.lean — M371F [実／本物]
  分類: 実 (二次体 ℚ(√d) の判別式 disc と分岐＝M366F の数論詳細化)
  complete_pct 影響: 柱C を前進（M366F 二次体を数論側で詳細化＝判別式 disc(ℚ(√d))=d(d≡1 mod4)
    /4d・素数 p が分岐⟺p∣disc・2 の分岐条件・split/inert/ramified の三分法を本物で。
    IUT の Szpiro 不等式の導手/判別式に直結）。
  正直な限定: 二次体のみ・different をイデアルとして/一般数体は後続。分岐は disc 整除で模型化。
-/
import IUT.QuadraticProductFormula

namespace IUT

/-! ## M371F-1: 二次体 ℚ(√d) の判別式 disc(K)

    d を平方因子を持たない整数とするとき、二次体 K=ℚ(√d) の判別式は
      disc(K) = d      （d ≡ 1 (mod 4)）
      disc(K) = 4·d    （d ≡ 2,3 (mod 4)）
    である（M366F `qpfField` の d と同じパラメータ）。Int の emod（非負剰余）で
    `d % 4 = 1` の場合分けにより本物に定義する。 -/

/-- **M371F-1a: 判別式** disc(ℚ(√d)) = if d≡1 (mod4) then d else 4·d（本物の Int）。
    Int.emod は非負剰余なので d<0 でも正しく分類する（例 d=−1 → (−1)%4=3 → 4·(−1)=−4）。 -/
def dscDisc (d : Int) : Int := if d % 4 = 1 then d else 4 * d

/-- **M371F-1b: 判別式の奇の場合** d ≡ 1 (mod4) ⟹ disc = d（`if_pos`）。 -/
theorem dsc_disc_odd (d : Int) (h : d % 4 = 1) : dscDisc d = d := if_pos h

/-- **M371F-1c: 判別式の偶の場合** d ≢ 1 (mod4) ⟹ disc = 4·d（`if_neg`）。
    d ≡ 2,3 (mod4)（すなわち 2 が分岐する場合）。 -/
theorem dsc_disc_even (d : Int) (h : d % 4 ≠ 1) : dscDisc d = 4 * d := if_neg h

/-- **M371F-1d: 判別式は非零**（d≠0 なら disc≠0）— disc は d か 4·d、どちらも d≠0 で非零。 -/
theorem dsc_disc_ne_zero (d : Int) (h : d ≠ 0) : dscDisc d ≠ 0 := by
  cases (inferInstance : Decidable (d % 4 = 1)) with
  | isTrue hd => rw [dsc_disc_odd d hd]; exact h
  | isFalse hd => rw [dsc_disc_even d hd]; omega

/-! ## M371F-2: 分岐＝判別式による整除 -/

/-- **M371F-2a: 分岐（模型）** 有理素数 p が K=ℚ(√d) で分岐する ⟺ p ∣ disc(K)。
    分岐する素数はちょうど判別式を割る素数（Dedekind の判別式定理の二次体版）。
    ここでは分岐を判別式整除で模型化する（正直な限定：different をイデアルとして扱うのは後続）。 -/
def dscRamified (p d : Int) : Prop := p ∣ dscDisc d

/-- **M371F-2b: 分岐の特徴づけ（定義的）** p 分岐 ⟺ p ∣ disc。 -/
theorem dsc_ramified_iff (p d : Int) : dscRamified p d ↔ p ∣ dscDisc d := Iff.rfl

/-- **M371F-2c: 2 の分岐条件** 素数 2 が K=ℚ(√d) で分岐する ⟺ d ≢ 1 (mod4)。
    d≡1 なら disc=d は奇（2∤disc、2 は分裂/惰性）；d≡2,3 なら disc=4d で 2∣disc（2 分岐）。
    本物の同値（omega が d%4 と 2 の整除から両方向を閉じる）。 -/
theorem dsc_ramified_two (d : Int) : dscRamified 2 d ↔ d % 4 ≠ 1 := by
  constructor
  · intro hdvd hd1
    have hdvd' : (2 : Int) ∣ dscDisc d := hdvd
    rw [dsc_disc_odd d hd1] at hdvd'
    omega
  · intro hd1
    show (2 : Int) ∣ dscDisc d
    rw [dsc_disc_even d hd1]
    omega

/-! ## M371F-3: 奇素数の分岐＝p∣d -/

/-- **M371F-3a: p ∣ d ⟹ p ∣ 4·d**（整除の乗法：d=p·k なら 4d=p·(4k)）。 -/
theorem dsc_dvd_four_mul (p d : Int) (h : p ∣ d) : p ∣ 4 * d := by
  obtain ⟨k, hk⟩ := h
  refine ⟨4 * k, ?_⟩
  rw [hk, Int.mul_comm 4 (p * k), Int.mul_assoc, Int.mul_comm k 4]

/-- **M371F-3b: p∣d ⟹ p 分岐（両場合とも本物）** — d を割る任意の素数 p は分岐する。
    disc=d の場合は直接、disc=4d の場合は `dsc_dvd_four_mul` で p∣4d。任意 p で成立
    （順方向は奇偶を問わない）。 -/
theorem dsc_ramified_of_dvd (p d : Int) (h : p ∣ d) : dscRamified p d := by
  show p ∣ dscDisc d
  cases (inferInstance : Decidable (d % 4 = 1)) with
  | isTrue hd => rw [dsc_disc_odd d hd]; exact h
  | isFalse hd => rw [dsc_disc_even d hd]; exact dsc_dvd_four_mul p d h

/-- **M371F-3c: 奇素数の分岐＝p∣d（d≡1 mod4 で完全同値）** — d≡1 (mod4) なら disc=d
    ゆえ p 分岐 ⟺ p∣disc=d ⟺ p∣d。
    正直な限定: d≡2,3 (mod4)（disc=4d）での逆向き「奇素数 p∣4d ⟹ p∣d」は gcd(p,4)=1
    の Bezout（Euclid の補題）を要すので後続。順方向 `dsc_ramified_of_dvd` は全 d で本物。 -/
theorem dsc_ramified_odd_iff (p d : Int) (hd : d % 4 = 1) :
    dscRamified p d ↔ p ∣ d := by
  show (p ∣ dscDisc d) ↔ p ∣ d
  rw [dsc_disc_odd d hd]

/-! ## M371F-4: 導手＝判別式（二次指標の導手） -/

/-- **M371F-4a: 導手（二次の場合）** — K=ℚ(√d) に付随する二次 Dirichlet 指標
    χ_K の導手は |disc(K)|。conductor-discriminant 関係の二次版（cond(χ_K)=|disc|）。 -/
def dscConductor (d : Int) : Nat := (dscDisc d).natAbs

/-- **M371F-4b: 導手＝|判別式|（定義的・本物）** — cond(χ_K) = |disc(K)|。
    正直な限定: |disc| が分岐素数冪の積であること（cond の素因数分解）は後続。 -/
theorem dsc_conductor_eq_disc (d : Int) : dscConductor d = (dscDisc d).natAbs := rfl

/-! ## M371F-5: split / inert / ramified の三分法（M366F `qpfFinSplit` 接続） -/

/-- **M371F-5a: 分解型の決定（模型）** — 奇素数 p の K=ℚ(√d) での分解型を、
    (i) p∣disc ⟹ ramified、(ii) p∤disc かつ Legendre 記号 (d/p)=1 ⟹ split、
    (iii) p∤disc かつ (d/p)=−1 ⟹ inert で定める。M366F `qpfFinSplit` へ値を返す。
    Legendre 記号 `legendre` は入力（(d/p)∈{1,−1}）；その本物の計算は後続。 -/
def dscSplitOf (p d legendre : Int) : qpfFinSplit :=
  if p ∣ dscDisc d then qpfFinSplit.ramified
  else if legendre = 1 then qpfFinSplit.split
  else qpfFinSplit.inert

/-- **M371F-5b: 分岐型** p∣disc ⟹ ramified（`if_pos`）。 -/
theorem dsc_split_ramified (p d legendre : Int) (h : p ∣ dscDisc d) :
    dscSplitOf p d legendre = qpfFinSplit.ramified := if_pos h

/-- **M371F-5c: 分裂型** p∤disc かつ (d/p)=1 ⟹ split。 -/
theorem dsc_split_split (p d legendre : Int) (h : ¬ p ∣ dscDisc d) (h2 : legendre = 1) :
    dscSplitOf p d legendre = qpfFinSplit.split := by
  show (if p ∣ dscDisc d then qpfFinSplit.ramified
        else if legendre = 1 then qpfFinSplit.split else qpfFinSplit.inert)
      = qpfFinSplit.split
  rw [if_neg h, if_pos h2]

/-- **M371F-5d: 惰性型** p∤disc かつ (d/p)≠1 ⟹ inert。 -/
theorem dsc_split_inert (p d legendre : Int) (h : ¬ p ∣ dscDisc d) (h2 : legendre ≠ 1) :
    dscSplitOf p d legendre = qpfFinSplit.inert := by
  show (if p ∣ dscDisc d then qpfFinSplit.ramified
        else if legendre = 1 then qpfFinSplit.split else qpfFinSplit.inert)
      = qpfFinSplit.inert
  rw [if_neg h, if_neg h2]

/-- **M371F-5e: 局所次数和＝[K:ℚ]=2（M366F 再輸出）** — どの分解型でも Σ_{v|p}[K_v:ℚ_p]=2。
    三分法が M366F の基本等式 `qpf_fin_degree_sum` と両立する。 -/
theorem dsc_split_degree_sum (s : qpfFinSplit) :
    qpfListSum (qpfFinMult s) = qpfDegree :=
  qpf_fin_degree_sum s

/-- **M371F-5f: 分岐指数・剰余次数・素点数 (e,f,g)** — split→(e=1,f=1,g=2)・
    inert→(e=1,f=2,g=1)・ramified→(e=2,f=1,g=1)（各分解型の (e,f,g)）。 -/
def dscEFG : qpfFinSplit → Nat × Nat × Nat
  | .split => (1, 1, 2)
  | .inert => (1, 2, 1)
  | .ramified => (2, 1, 1)

/-- **M371F-5g: 基本等式 e·f·g = [K:ℚ] = 2** — Σ e_i f_i = e·f·g（不分岐は g 個）＝2。
    三分法いずれでも e·f·g=2（二次体の Σ e_v f_v = [K:ℚ] の三分法版）。 -/
theorem dsc_efg_prod (s : qpfFinSplit) :
    (dscEFG s).1 * (dscEFG s).2.1 * (dscEFG s).2.2 = 2 := by
  cases s with
  | split => rfl
  | inert => rfl
  | ramified => rfl

/-! ## M371F-6: 具体例（ℚ(√2)・ℚ(√5)・ℚ(i)） -/

/-- **M371F-6a: disc(ℚ(√2)) = 8**（2≡2 mod4 ⟹ disc=4·2=8）。 -/
theorem dsc_example_sqrt2_disc : dscDisc 2 = 8 := by
  have h := dsc_disc_even 2 (show (2 : Int) % 4 ≠ 1 by omega)
  omega

/-- **M371F-6b: 2 は ℚ(√2) で分岐**（2∣disc=8）。 -/
theorem dsc_example_sqrt2_ram : dscRamified 2 2 :=
  (dsc_ramified_two 2).mpr (by omega)

/-- **M371F-6c: 導手(ℚ(√2)) = 8**。 -/
theorem dsc_example_sqrt2_conductor : dscConductor 2 = 8 := by
  show (dscDisc 2).natAbs = 8
  rw [dsc_example_sqrt2_disc]
  rfl

/-- **M371F-6d: disc(ℚ(√5)) = 5**（5≡1 mod4 ⟹ disc=5）。 -/
theorem dsc_example_sqrt5_disc : dscDisc 5 = 5 :=
  dsc_disc_odd 5 (by omega)

/-- **M371F-6e: 5 は ℚ(√5) で分岐**（5∣disc=5、奇素数 p∣d）。 -/
theorem dsc_example_sqrt5_ram : dscRamified 5 5 := by
  show (5 : Int) ∣ dscDisc 5
  rw [dsc_example_sqrt5_disc]
  omega

/-- **M371F-6f: disc(ℚ(i)) = disc(ℚ(√−1)) = −4**（−1≡3 mod4 ⟹ disc=4·(−1)=−4）。 -/
theorem dsc_example_gauss_disc : dscDisc (-1) = -4 := by
  have h := dsc_disc_even (-1) (show ((-1 : Int)) % 4 ≠ 1 by omega)
  omega

/-- **M371F-6g: 2 は ℚ(i) で分岐**（2∣disc=−4、−1≢1 mod4）。 -/
theorem dsc_example_gauss_ram : dscRamified 2 (-1) :=
  (dsc_ramified_two (-1)).mpr (by omega)

/-! ## M371F-7: capstone -/

/-- **M371F-7a: 判別式・分岐データ** — 二次体 K=ℚ(√d) の判別式 disc・導手 cond・
    2 の分岐条件を束ねる（全フィールド本物）。 -/
structure DifferentDiscriminantData where
  /-- 二次体パラメータ d（M366F `qpfField` と同じ）。 -/
  d : Int
  /-- 判別式 disc(K)。 -/
  disc : Int
  /-- disc = dscDisc d（本物）。 -/
  disc_eq : disc = dscDisc d
  /-- 導手 cond(χ_K) = |disc|。 -/
  conductor : Nat
  /-- conductor = |disc|（本物）。 -/
  conductor_eq : conductor = (dscDisc d).natAbs
  /-- 2 の分岐条件 2 分岐 ⟺ d≢1 mod4（本物の同値）。 -/
  two_ramified_iff : dscRamified 2 d ↔ d % 4 ≠ 1

/-- **M371F-7b: 実データ**（任意の d に対し全フィールド本物で充足）。 -/
def differentDiscriminantData (d : Int) : DifferentDiscriminantData where
  d := d
  disc := dscDisc d
  disc_eq := rfl
  conductor := (dscDisc d).natAbs
  conductor_eq := rfl
  two_ramified_iff := dsc_ramified_two d

/-- **M371F-7c: 存在**（任意の二次体 ℚ(√d) の判別式・分岐データは充足可能）。 -/
theorem dsc_exists (d : Int) : Nonempty DifferentDiscriminantData :=
  ⟨differentDiscriminantData d⟩

/-- **M371F-7d: 具体 capstone** — ℚ(√2)（disc=8,2分岐）・ℚ(√5)（disc=5,5分岐）・
    ℚ(i)（disc=−4,2分岐）の三例をまとめて充足。 -/
theorem dsc_examples :
    dscDisc 2 = 8 ∧ dscRamified 2 2 ∧
    dscDisc 5 = 5 ∧ dscRamified 5 5 ∧
    dscDisc (-1) = -4 ∧ dscRamified 2 (-1) :=
  ⟨dsc_example_sqrt2_disc, dsc_example_sqrt2_ram,
   dsc_example_sqrt5_disc, dsc_example_sqrt5_ram,
   dsc_example_gauss_disc, dsc_example_gauss_ram⟩

end IUT
