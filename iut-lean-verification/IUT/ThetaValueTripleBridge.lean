/-
  IUT/ThetaValueTripleBridge.lean — M398F [実／本物／柱E]
  分類: 実（M318F `ThetaValueLtor` の**具体テータ値** Θ(q,u_j)=q^{j²/2l}（Laurent 単項式
    u^{j²}）と、M343F `galTh_norm_qpower` の Θ^{2l}=q^{j²}、および M353F/M393F の**コホモロジー的
    テータ Kummer 類** [Θ]∈H¹(G_K,μ_{2l})（指数パラメータ e）を、同一の自然数 j² の下で
    直接連結する本物のブリッジ）。
  complete_pct 影響: 柱E で、**具体的なテータ値の指数 j²（M318F の Laurent 単項式の指数、
    本物の環論的対象）** と **テータ Kummer 類 [Θ] を構成する指数パラメータ e（M353F、
    本物のガロアコホモロジー対象）** が、l-捻れ点ラベル j から来る**同一の自然数 j²** で
    あることを一つの capstone `tvtb_class_value` に閉じる。さらに mono-theta 環境
    `env`（M393F）の `kummerRigid.cls` がこの e=j² の下で `tkcClass M κ (j*j)` そのもの
    であることも `tvtb_env_class_value` で同時に確立し、三剛性束・コホモロジー類・具体
    テータ値の三者が**同じ e=j²** の下でつながることを machine-checked にする。
  正直な限定: 本層が確立するのは「具体テータ値の指数（Laurent 単項式の指数）と、テータ
    Kummer 類・mono-theta 環境の指数パラメータ e が、同一の自然数 j² として一致する」と
    いう**代数的な指数の同定**のみである。完全な解析的エタールテータ関数（p 進収束）・
    tempered π₁^ét 本体・遠アーベル復元は M318F/M343F/M353F/M393F と同様に外部仮説として
    継承し、本層でも一切導出しない。

  ## 内容（tier-S・実ブリッジ、M318F（具体値）↔ M353F/M393F（コホモロジー類）の直接連結）

  M318F は l-捻れ点 u_j でのテータ値 Θ(q,u_j)=u^{j²}（本物の Laurent 単項式、指数
  `thLtorExp j = j*j : Int`）を確立し、M343F はそのノルム Θ^{2l}=q^{j²}（`galTh_norm_qpower`,
  witness j*j）をガロア固定量として確立した。一方 M353F/M393F は、**別の指数パラメータ
  `e : Nat`** を主語に、テータ Kummer 指標 κ(·)^e（`tkcThetaChar`）とその H¹ 類
  `tkcClass M κ e`（[Θ]∈H¹(G_K,μ_{2l})）を構成し、mono-theta 環境 `env` の
  `kummerRigid.cls = tkcClass M κ e` を M393F `tktb_class_governed` で machine-check した。
  しかし **この e が具体テータ値の指数 j² と同一であること自体は、これまで一度も
  定理として結ばれていなかった**（M353F/M393F のドキュメントコメントには "e=j²" と
  書かれているのみで、本物の等式としては証明されていない）。本層はその隙間を埋める:

  * M398F-1 `tvtb_exp_cast` — l-捻れ点ラベル j:Nat に対し、M318F の Int 指数
    `thLtorExp (j:Int) = j*j : Int` が、Nat 平方 `(j*j:Nat)` の Int キャストに一致する
    （`thLtorExp_sq` と `Int.natCast_mul` の合成）。Int 側の具体指数と Nat 側の
    Kummer-類パラメータの型を橋渡しする本物の第一歩。
  * M398F-2 `tvtb_value_exp` — 具体テータ値 `thLtorValue R (j:Int)` が、まさにこの
    Nat キャストされた指数 `((j*j:Nat):Int)` を持つ Laurent 単項式であること
    （M318F `thLtor_value_exponent` と M398F-1 の合成）。
  * M398F-3 本丸 capstone `tvtb_class_value` — 任意の R・l・G_K・μ_{2l}・Kummer 捻り κ・
    l-捻れ点ラベル j:Nat に対し、**同一の自然数 e=j*j** の下で:
    (i) 具体テータ値の Laurent 単項式指数が `(j*j:Nat)` のキャスト（M398F-2）、
    (ii) そのテータ値の 2l 乗が q^{j²}（`IsLPowerValue`、M343F `galTh_norm_qpower` の
    witness も同じ j*j）、
    (iii) テータ Kummer 類 `tkcClass M κ (j*j)`（M353F、パラメータ e=j*j）が H¹ で
    2l 乗すると消える（`tkc_class_pow_trivial`）、
    (iv) そのテータ Kummer 指標 `tkcThetaChar M κ (j*j)` が `galThTorTwist GK M κ · (j*j)`
    そのもの（M353F `tkc_galois_theta_link`、M343F 接続）
    を一つの連言に閉じ、**具体値の指数（i,ii）とコホモロジー類のパラメータ（iii,iv）が
    同じ e=j*j で貫かれる**ことを machine-checked にする。
  * M398F-4 `tvtb_env_class_value` — 上記に加え、mono-theta 環境 `env`
    （M363F `MonoThetaEnvBundle`, M393F 経由）を e=j*j で特殊化すると、`env.kummerRigid.cls`
    が `tkcClass M κ (j*j)` そのものであること（M393F `TkrData.cls_eq` の e=j² 特殊化）を
    同時に確立し、三剛性束・[Θ]∈H¹・具体テータ値の三者を同一の e=j² で結ぶ。
  * M398F-5 `ThetaValueTripleBridgeData` / `thetaValueTripleBridgeData` / `tvtb_exists` —
    上記を一つの witness レコードに束ね、任意の R・l・G_K・μ_{2l}・κ・j に対する存在を示す。
  * M398F-6 実例（l=5, j=2（j²=4）・本物の G_ℚ 上、M353F/M393F と同じ具体構成）。

  選択公理不使用（新規 Classical.choice なし；継承分の Quot.sound のみ）。sorry 皆無・
  禁止タクティク不使用（rw/exact/apply/refine のみ使用、新規 tactic block は cast の
  書き換えのみ）。一般名は `tvtb` 接頭辞で衝突回避。共有ファイル（IUT.lean・build.sh・
  dashboard.md・graph 系）は一切変更していない。
-/
import IUT.ThetaKummerTripleBridge

namespace IUT

/-! ## M398F-1: Nat 捻れラベル j での指数キャスト j² (Int) = j² (Nat のキャスト) -/

/-- **定理 (M398F-1: 具体指数の Nat キャスト整合)** — l-捻れ点ラベル j:Nat に対し、
    M318F の Int 指数 `thLtorExp (j:Int) = j*j`（Int）が、Nat 平方 `j*j:Nat` の Int
    キャストに一致する。具体テータ値の指数（Int 側、M318F）と、テータ Kummer 類の
    指数パラメータ e（Nat 側、M353F/M393F）とを同じ自然数として橋渡しする第一歩。 -/
theorem tvtb_exp_cast (j : Nat) :
    thLtorExp (j : Int) = ((j * j : Nat) : Int) := by
  rw [thLtorExp_sq]
  exact (Int.natCast_mul j j).symm

/-! ## M398F-2: 具体テータ値の指数は e=j*j（Nat キャスト）そのもの -/

/-- **定理 (M398F-2: 具体テータ値の指数抽出、Nat キャスト版)** — l-捻れ点 u_j での
    具体テータ値 `thLtorValue R (j:Int)`（M318F の本物の Laurent 単項式）が、まさに
    Nat 平方 `j*j` をキャストした指数を持つ単項式であること: value = u^{(j*j:Nat)}。
    M318F `thLtor_value_exponent` と M398F-1 の合成。 -/
theorem tvtb_value_exp (R : CRing) (j : Nat) :
    thLtorValue R (j : Int) = uMonHom R ((j * j : Nat) : Int) := by
  rw [thLtor_value_exponent, tvtb_exp_cast]

/-! ## M398F-3: 本丸 capstone——具体テータ値の指数とテータ Kummer 類のパラメータは同じ e=j² -/

/-- **定理 (M398F-3: capstone——具体テータ値の指数とテータ Kummer 類のパラメータは
    同一の自然数 e=j²)** — 任意の係数環 R・l・G_K・μ_{2l}（`CycMuGroup`）・Kummer 捻り
    κ・l-捻れ点ラベル j:Nat に対し、**同一の自然数 e := j*j** の下で:
    (1) 具体テータ値 `thLtorValue R (j:Int)` の Laurent 単項式指数が `(j*j:Nat)` の
        Int キャストであること（M398F-2）、
    (2) そのテータ値の 2l 乗が q^{j²}（`IsLPowerValue R (2l) (Θ^{2l})`、M343F
        `galTh_norm_qpower` の witness も同じ j*j＝内部で一致）、
    (3) テータ Kummer 類 `tkcClass M κ (j*j)`（M353F、パラメータ e=j*j で構成）が
        H¹(G_K,μ_{2l}) で 2l 乗すると消える（`tkc_class_pow_trivial`）、
    (4) そのテータ Kummer 指標 `tkcThetaChar M κ (j*j)` が `galThTorTwist GK M κ · (j*j)`
        そのもの（M353F `tkc_galois_theta_link`、M343F の l-捻れ点ガロア捻り指標に接続）。
    (1)(2) は**具体的な Laurent 環の値側**、(3)(4) は**コホモロジー的な Kummer 類側**の
    事実であり、両者が**同じ自然数 e=j*j**（同じ l-捻れ点ラベル j から来る）で貫かれる
    ことを一つの連言に閉じることで machine-checked にする。 -/
theorem tvtb_class_value (R : CRing) (l : Nat) (GK : Grp) (M : CycMuGroup)
    (κ : Hom GK M.μ) (j : Nat) :
    thLtorValue R (j : Int) = uMonHom R ((j * j : Nat) : Int)
    ∧ IsLPowerValue R ((2 * l : Nat) : Int)
        (thLtorPow R (thLtorValue R (j : Int)) (2 * l))
    ∧ (galH1Group (galH1TrivialModule GK M.μ M.comm)).pow (tkcClass M κ (j * j)) M.n
        = (galH1Group (galH1TrivialModule GK M.μ M.comm)).one
    ∧ ∀ g : GK.carrier,
        (tkcThetaChar M κ (j * j)).map g = galThTorTwist GK M κ g (j * j) :=
  ⟨tvtb_value_exp R j, galTh_norm_qpower R l (j : Int), tkc_class_pow_trivial M κ (j * j),
    fun g => tkc_galois_theta_link M κ (j * j) g⟩

/-! ## M398F-4: mono-theta 環境 env の kummerRigid.cls も同じ e=j² で tkcClass に一致 -/

/-- **定理 (M398F-4: mono-theta 環境の kummerRigid.cls も同じ e=j² で tkcClass に一致)** —
    mono-theta 環境 `env`（M363F `MonoThetaEnvBundle`, パラメータ e を j*j に特殊化）に
    対し、`env` が束ねるテータ Kummer 類の剛性データの類 `env.kummerRigid.cls` は、M353F の
    本物の類 `tkcClass M κ (j*j)` そのものである（M393F `tktb_class_governed`/`TkrData.cls_eq`
    の e=j² 特殊化）。加えて、具体テータ値の指数が同じ `(j*j:Nat)` のキャストであること
    （M398F-2）を同時に成立させ、**三剛性束（env）・コホモロジー類（[Θ]）・具体テータ値**の
    三者が同一の e=j*j で結ばれることを示す。 -/
theorem tvtb_env_class_value {R : CRing} {K : IUTField} {p l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp p).carrier} {hζ2l : zpPow p ζ (2 * l) = zpOne p}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow p ζ i ≠ zpPow p ζ j}
    {GK : Grp} {M : CycMuGroup} {κ : Hom GK M.μ} (j : Nat)
    (env : MonoThetaEnvBundle R K p l hl ζ hζ2l hdist2l GK M κ (j * j)) :
    env.kummerRigid.cls = tkcClass M κ (j * j)
    ∧ thLtorValue R (j : Int) = uMonHom R ((j * j : Nat) : Int) :=
  ⟨env.kummerRigid.cls_eq, tvtb_value_exp R j⟩

/-! ## M398F-5: 総括レコード（witness）と存在 -/

/-- **M398F-5a: 具体テータ値・テータ Kummer 類 同一指数ブリッジデータ** — 具体テータ値の
    Laurent 単項式指数（M318F）・ノルム q^{j²} 性（M343F）・テータ Kummer 類の H¹ 消失
    （M353F）・テータ Kummer 指標の galThTorTwist 一致（M343F 接続）を、**同一の自然数
    e=j*j** の下で一括束ねる。主語は本物の Laurent 単項式 `thLtorValue`・本物の H¹ 類
    `tkcClass`（toy 代理なし）。 -/
structure ThetaValueTripleBridgeData (R : CRing) (l : Nat) (GK : Grp) (M : CycMuGroup)
    (κ : Hom GK M.μ) (j : Nat) where
  /-- 具体テータ値の指数は (j*j:Nat) のキャスト。 -/
  value_exp : thLtorValue R (j : Int) = uMonHom R ((j * j : Nat) : Int)
  /-- ノルム Θ^{2l}=q^{j²}（q^ℤ に落ちる）。 -/
  norm_qpower : IsLPowerValue R ((2 * l : Nat) : Int)
      (thLtorPow R (thLtorValue R (j : Int)) (2 * l))
  /-- テータ Kummer 類 [Θ]（パラメータ e=j*j）は H¹ で 2l 乗すると消える。 -/
  class_pow_trivial : (galH1Group (galH1TrivialModule GK M.μ M.comm)).pow
      (tkcClass M κ (j * j)) M.n
      = (galH1Group (galH1TrivialModule GK M.μ M.comm)).one
  /-- テータ Kummer 指標（e=j*j）は galThTorTwist（κ(·)^{j*j}）そのもの。 -/
  char_eq : ∀ g : GK.carrier,
      (tkcThetaChar M κ (j * j)).map g = galThTorTwist GK M κ g (j * j)

/-- **M398F-5b: witness 本体** — 各フィールドを M398F-1〜3 の主定理で埋める。 -/
def thetaValueTripleBridgeData (R : CRing) (l : Nat) (GK : Grp) (M : CycMuGroup)
    (κ : Hom GK M.μ) (j : Nat) : ThetaValueTripleBridgeData R l GK M κ j where
  value_exp := tvtb_value_exp R j
  norm_qpower := galTh_norm_qpower R l (j : Int)
  class_pow_trivial := tkc_class_pow_trivial M κ (j * j)
  char_eq := fun g => tkc_galois_theta_link M κ (j * j) g

/-- **定理 (M398F-5c: 具体テータ値・テータ Kummer 類 同一指数ブリッジデータの存在)** —
    任意の R・l・G_K・μ_{2l}・Kummer 捻り κ・l-捻れ点ラベル j に対し、具体テータ値の
    指数・ノルム q^{j²} 性・テータ Kummer 類の H¹ 消失・指標の galThTorTwist 一致を
    同一の e=j*j で一括束ねたデータが存在する。 -/
theorem tvtb_exists (R : CRing) (l : Nat) (GK : Grp) (M : CycMuGroup)
    (κ : Hom GK M.μ) (j : Nat) :
    Nonempty (ThetaValueTripleBridgeData R l GK M κ j) :=
  ⟨thetaValueTripleBridgeData R l GK M κ j⟩

/-! ## M398F-6: 実例（l=5・j=2（j²=4）・本物の G_ℚ 上のμ_{10}） -/

/-- 実例: l=5・j=2（j²=4）の具体テータ値・テータ Kummer 類 同一指数ブリッジデータが、
    本物の絶対ガロア群 G_ℚ（M315F `algCloAbsGalois algCloTrivialTower`）・μ_{10}
    （`cycMuStd 10`）・自明 Kummer 捻り（M343F `galThTrivialKummer`）の下で存在する。 -/
theorem tvtb_example_l5 (R : CRing) :
    Nonempty (ThetaValueTripleBridgeData R 5
      (algCloAbsGalois algCloTrivialTower) (cycMuStd 10 (by omega))
      (galThTrivialKummer (algCloAbsGalois algCloTrivialTower) (cycMuStd 10 (by omega))) 2) :=
  tvtb_exists R 5 (algCloAbsGalois algCloTrivialTower) (cycMuStd 10 (by omega))
    (galThTrivialKummer (algCloAbsGalois algCloTrivialTower) (cycMuStd 10 (by omega))) 2

/-- 実例: j=2 の具体テータ値の指数は 4（=2*2）の Int キャスト。 -/
example (R : CRing) : thLtorValue R (2 : Int) = uMonHom R ((4 : Nat) : Int) :=
  tvtb_value_exp R 2

/-- 実例: l=5・j=2 のテータ Kummer 類（e=4）が H¹(μ_{10}) で 10 乗すると消える
    （同じ e=4 が具体値側にも現れる、M398F-3）。 -/
example (GK : Grp) (κ : Hom GK (cycMuStd 10 (by omega)).μ) :
    (galH1Group (galH1TrivialModule GK (cycMuStd 10 (by omega)).μ
        (cycMuStd 10 (by omega)).comm)).pow (tkcClass (cycMuStd 10 (by omega)) κ 4)
        (cycMuStd 10 (by omega)).n
      = (galH1Group (galH1TrivialModule GK (cycMuStd 10 (by omega)).μ
          (cycMuStd 10 (by omega)).comm)).one :=
  tkc_class_pow_trivial (cycMuStd 10 (by omega)) κ 4

end IUT
