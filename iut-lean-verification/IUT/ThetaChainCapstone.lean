/-
  IUT/ThetaChainCapstone.lean — M204F: 柱E テータ E-1 連鎖の総括 capstone
  — μ_l 同一視→Heisenberg→関数等式→作用素準同型（柱E・並行部品）

  柱E 残課題 E-1（#39）を構成する 4 本のキャンペーン
  （M162F μ_l 同一視・M187F Heisenberg リフト・M190F 解析↔群接合・
  M198F 作用素準同型）の総括 witness を、**一つの証明記録**に束ねる。
  M196F（MonoThetaEnv）が柱D Dα プログラムの入力として mono-theta
  環境全体（M92/M98F/M116F/M124F/M187F/M190F）を束ねたのに対し、
  本モジュールは**柱E E-1 の theta 連鎖そのもの**（μ_l ラベリング →
  Heisenberg 中心捻れ → 解析側関数等式接合 → 作用素準同型・値障害）を
  一つの型に固定する、異なる切り口の capstone である。

  本モジュールは新規の数学的主張を持たない（**新規証明ゼロ**）。
  4 フィールドはいずれも既存の直接 def（`muLIdentificationData` /
  `thetaHeisenbergLiftData` / `thetaFuneqBridgeData` /
  `thetaOperatorHomData`）を代入するだけで埋まる。パラメータ化は
  M187F/M190F の署名（R p l L・hp/hL/hodd/hdvd）に合わせ、μ_l 生成元
  ζ とその根拠（hζl・hdist・teich 形 ha）を `thetaChainData` の明示
  引数として受け取る（`thetaChain_exists` でのみ M121F
  `mu_l_zp_exists` から Nonempty の中で取り出す——choice 不要）。

  * M204F-1 `ThetaChainData` — E-1 theta 連鎖の単一インターフェース:
    muL（M162F μ_l 同一視・l⋇ ラベリング）・lift（M187F Heisenberg
    中心捻れ・μ_l ラベル同定）・bridge（M190F 解析↔群関数等式接合）・
    op（M198F 作用素準同型 T↦Φ(1)・値レベル障害）の 4 フィールド束
  * M204F-2 `thetaChainData` — witness 本体（ζ・hζl・hdist・ha を
    明示引数に取る choice-free コンストラクタ）
  * M204F-3 `thetaChain_exists` — 連鎖データの存在（Nonempty; μ_l
    生成元は M121F `mu_l_zp_exists` から Prop 内で取り出す）
  * M204F-4 `thetaChain_zeta_coherent` — witness 本体の全フィールドが
    **同一の生成元 ζ** を共有すること（muL.ζ = lift.ζ = bridge.ζ = ζ、
    定義的に rfl）——E-1 連鎖が単一の μ_l 生成元の上で首尾一貫して
    貼り合うことの確認
  * M204F-5 `thetaChain_closure` — **本丸（一括接合）**: 与えられた
    ThetaChainData と 0 < j < l に対し、(1) M162F の存在形 ±-接合
    ∃z（muL.theta_compat）、(2) μ_l 側の反転 ζ^j·ζ^{l−j}=1、
    (3) M187F の捻れの μ_l 像 = ラベル ζ^j（lift.twist_mu）、
    (4) M190F/M187F の商群反転等式（bridge.group_inversion）、
    (5) M198F 作用素準同型の J/ι_l-同変性（op.equivariant_group）
    の五者が**同一ラベル j で**貼り合うことを一括して確認する。
    M162F の存在量化（∃z）と M187F〜M198F の明示形・作用素形が
    同じ j の上で両立することを示す capstone の中心定理。

  意義: M162F→M187F→M190F→M198F という柱E E-1 の理論的連鎖
  （「μ_l 係数シクロトームの同一視」→「関数等式の中心捻れの明示化」→
  「解析側関数等式との接合」→「作用素レベルへの昇格と値障害の確定」）
  を、単一の証明記録・単一の一括接合定理として検証する。新規証明
  ゼロで、既存 4 モジュールの整合性そのものを機械的に再確認する。

  正直な限定: 本層が束ねるのは E-1 の**理論的連鎖の骨格**（μ_l
  ±-軌道分類・Heisenberg 中心捻れ・解析↔群接合・作用素準同型）の
  みであり、各モジュールが個別に申告した限定（ガロア同変な p 進
  テータ値の評価・tempered π₁ の商としての実現・級数環全体を定義域
  とする環準同型としての作用素の定式化）はいずれも未解決のまま
  E-1 残として持ち越される。M198F の値レベル障害定理
  （opHom 2 ≠ opHom 0 かつ thetaIter R 2 = thetaIter R 0）が示す通り、
  作用素準同型は反復指数モノイド上でのみ定義可能であり、本 capstone
  もこの限定を継承する。ThetaFuneqBridgeData・ThetaOperatorHomData の
  一部フィールドは thetaGrpMod / laurentRel の Quot 商上の言明であり、
  その構成は Quot.sound を用いる（商構成に内在、選択公理ではない）。
  全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.MuLIdentification
import IUT.ThetaHeisenbergLift
import IUT.ThetaFuneqBridge
import IUT.ThetaOperatorHom

namespace IUT

/-! ## M204F-1: E-1 theta 連鎖の単一インターフェース -/

/-- **M204F-1: E-1 theta 連鎖データ** — 柱E 残課題 E-1 の理論的連鎖
    （μ_l 同一視 → Heisenberg リフト → 解析↔群接合 → 作用素準同型）を
    一つの構造体に束ねる。

    パラメータ: `R` はテータ級数の係数環（解析側 M190F/M198F 用）、
    `p` は素数、`l = 2L+1` は奇数の捻れ次数（`l ∣ p−1`）——
    M187F/M190F の署名にそのまま合わせる。 -/
structure ThetaChainData (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) where
  /-- 柱E E-1: μ_l 同一視・l⋇ ラベリング（M162F — μ_l(O) 上の ±-軌道の
      orbitRep による完全分類、非単位軌道の l⋇ = (l−1)/2 ラベリング、
      テータ ± との接合）。 -/
  muL : MuLIdentificationData p l L hp hL hodd hdvd
  /-- 柱E E-1: 関数等式の Heisenberg リフト（M187F — 中心捻れ
      funeqTwist の明示形・閉形式・μ_l ラベル同定・商群での等式
      リフト・Heisenberg 積との μ_l 両立）。 -/
  lift : ThetaHeisenbergLiftData p l L hL hodd
  /-- 柱E E-1: 解析↔群 関数等式接合（M190F — 反転 J の反復伝播・
      解析側ラベル入替 J(T^j Θ) = T^{l−j}(Θ)・ガウス次数差 =
      funeqTwist・四者の一括接合）。 -/
  bridge : ThetaFuneqBridgeData R p l L hL hodd
  /-- 柱E E-1: 作用素準同型 T↦Φ(1)-乗算（M198F — 反復指数モノイド
      上の準同型・T^k ↔ Φ(1)^k の絡み合い・J/ι_l-同変性・値レベル
      障害 T²Θ=Θ ∧ opHom 2 ≠ opHom 0）。 -/
  op : ThetaOperatorHomData R l L hL hodd

/-! ## M204F-2/3: witness 本体と存在 -/

/-- **M204F-2: E-1 連鎖の witness 本体** — μ_l 生成元 ζ とその根拠
    （l 乗根性 hζl・冪の相異性 hdist・Teichmüller 形 ha）を明示引数に
    取り、全フィールドを既存の直接 def（`muLIdentificationData` /
    `thetaHeisenbergLiftData` / `thetaFuneqBridgeData` /
    `thetaOperatorHomData`）で埋める choice-free コンストラクタ。
    `op` フィールドは ζ に依存しない（M198F の作用素は thetaSectionMod
    のみで構成される）。 -/
def thetaChainData (R : CRing) (p l L : Nat) (hp : IsPrime p) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (ha : ∃ a : Int, ¬ ((p : Nat) : Int) ∣ a ∧ ζ = teich p hp a) :
    ThetaChainData R p l L hp hL hodd hdvd where
  muL := muLIdentificationData p l L hp hL hodd hdvd ζ hζl hdist ha
  lift := thetaHeisenbergLiftData p l L hL hodd ζ hζl
  bridge := thetaFuneqBridgeData R p l L hL hodd ζ hζl
  op := thetaOperatorHomData R l L hL hodd

/-- **定理 (M204F-3): E-1 連鎖データの存在（M204F 見出し）** — p 素数・
    l = 2L+1 ∣ p−1 なら柱E E-1 の theta 連鎖データが存在する（μ_l
    生成元は M121F `mu_l_zp_exists` から Prop（Nonempty）の中で
    取り出す——choice 不要）。 -/
theorem thetaChain_exists (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) :
    Nonempty (ThetaChainData R p l L hp hL hodd hdvd) := by
  obtain ⟨ζ, hζl, hdist, ha⟩ := mu_l_zp_exists p l hp (by omega) hdvd
  exact ⟨thetaChainData R p l L hp hL hodd hdvd ζ hζl hdist ha⟩

/-! ## M204F-4: 生成元の首尾一貫性 -/

/-- **定理 (M204F-4): witness 本体の生成元の首尾一貫性** — `thetaChainData`
    の 3 フィールド muL・lift・bridge はいずれも**同一の生成元 ζ**を
    保持する（各 def が同じ引数 ζ をそのまま代入するので定義的に
    rfl）。E-1 連鎖の 4 本のキャンペーンが単一の μ_l 生成元の上で
    首尾一貫して貼り合うことの確認。 -/
theorem thetaChain_zeta_coherent (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1)
    (ζ : (Zp p).carrier) (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (ha : ∃ a : Int, ¬ ((p : Nat) : Int) ∣ a ∧ ζ = teich p hp a) :
    (thetaChainData R p l L hp hL hodd hdvd ζ hζl hdist ha).muL.ζ = ζ
      ∧ (thetaChainData R p l L hp hL hodd hdvd ζ hζl hdist ha).lift.ζ = ζ
      ∧ (thetaChainData R p l L hp hL hodd hdvd ζ hζl hdist ha).bridge.ζ
          = ζ :=
  ⟨rfl, rfl, rfl⟩

/-! ## M204F-5: 一括接合（本丸） -/

/-- **定理 (M204F-5): E-1 連鎖の一括接合（本丸）** — 任意の
    `ThetaChainData` と 0 < j < l に対し、
    (1) M162F の存在形 ±-接合: ι のラベル入替 j ↔ l−j
        （∃z, thetaRelMod …）（muL.theta_compat）、
    (2) μ_l 側の反転: ζ_muL^j · ζ_muL^{l−j} = 1、
    (3) M187F の捻れの μ_l 像 = テータ値ラベル: centerToMu (funeqTwist)
        = ζ_lift^j（lift.twist_mu）、
    (4) M190F/M187F の商群反転等式:
        ι_l(Φ_l(j)) = Φ_l(l−j)·red(0,0,funeqTwist l j)
        （bridge.group_inversion）、
    (5) M198F 作用素準同型の J/ι_l-同変性:
        ι_l(opHom j) = opHom(l−j)·red(0,0,funeqTwist l j)
        （op.equivariant_group）
    の五者が**同一ラベル j で**貼り合う。M162F の存在量化（∃z）が
    M187F の明示捻れ・M190F/M198F の（商）群等式・作用素形と同じ
    j の上で両立することを一括して確認する capstone の中心定理。 -/
theorem thetaChain_closure (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1)
    (data : ThetaChainData R p l L hp hL hodd hdvd)
    (j : Nat) (hpos : 0 < j) (hj : j < l) :
    (∃ z : Int, thetaRelMod l (thetaNeg.map (thetaSection j))
        (thetaGrp.mul (thetaSection (l - j)) (0, 0, z)))
      ∧ zpMul p (zpPow p data.muL.ζ j) (zpPow p data.muL.ζ (l - j))
          = zpOne p
      ∧ centerToMu p l data.lift.ζ (funeqTwist l j) = zpPow p data.lift.ζ j
      ∧ (thetaNegMod l).map (thetaSectionMod l j)
          = (thetaGrpMod l).mul (thetaSectionMod l (l - j))
              ((thetaRed l).map (0, 0, funeqTwist l j))
      ∧ (thetaNegMod l).map (data.op.opHom j)
          = (thetaGrpMod l).mul (data.op.opHom (l - j))
              ((thetaRed l).map (0, 0, funeqTwist l j)) :=
  ⟨(data.muL.theta_compat j hpos hj).1, (data.muL.theta_compat j hpos hj).2,
    data.lift.twist_mu j hj, data.bridge.group_inversion j (by omega),
    data.op.equivariant_group j (by omega)⟩

end IUT
