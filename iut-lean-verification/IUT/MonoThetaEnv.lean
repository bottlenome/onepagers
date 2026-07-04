/-
  IUT/MonoThetaEnv.lean — M196F: mono-theta 環境の単一インターフェース
  （柱D A3β/D-α-1・並行部品）

  [EtTh] の mono-theta 環境（テータ群 = 離散 Heisenberg 群・その l-捻れ商・
  ±-構造・シクロトミック同期・関数等式の Heisenberg リフト・解析↔群接合）
  を構成する 7 本のキャンペーン（M92 / M98F / M116F / M124F / M137F /
  M187F / M190F）の総括 witness を、**一つの構造体**に束ねる。柱D の
  Dα プログラム（issue #38）の第一段: Dα-2〜7（log-shell・Ind・Kummer・
  splitMono 等）が入力として参照する mono-theta 環境の単一の型。

  本モジュールは新規の数学的主張をほぼ持たない（**新規証明ゼロに近い**）。
  全フィールドは既存の直接 def（`monoThetaWitness` / `thetaGroupModData`
  / `thetaPMData` / `cyclotomicSyncData` / `thetaHeisenbergLiftData` /
  `thetaFuneqBridgeData` — いずれも Nonempty ではなく具体的な項を返す）
  を代入するだけで埋まる。パラメータ化は M187F `thetaHeisenbergLift_exists`
  / M190F `thetaFuneqBridge_exists` の形（p l L と素数性・奇数分解・
  整除の仮定）に合わせ、μ_l 生成元 ζ とその l 乗根性 hζl を明示的な
  引数として受け取る（`thetaHeisenbergLiftData` 自身がそうであるように、
  ζ の存在からの取り出しは Prop 値の `Nonempty` 版 `monoThetaEnv_exists`
  でのみ行う——構造体本体の構成は choice 不要）。

  * M196F-1 `MonoThetaEnv` — mono-theta 環境の単一インターフェース:
    mono-theta witness（M92）・テータ群 mod l（M98F）・±-構造 ι（M116F）・
    シクロトミック同期 centerToMu（M124F）・関数等式 Heisenberg リフト
    + μ_l ラベル（M187F）・解析↔群接合（M190F）の 6 フィールド束
  * M196F-2 `monoThetaEnv` — witness 本体（ζ・hζl を明示引数に取る
    choice-free コンストラクタ）
  * M196F-3 `monoThetaEnv_exists` — 環境の存在（Nonempty; μ_l 生成元は
    M121F `mu_l_zp_exists` から Prop 内で取り出す）

  **意義**: Dα-1（issue #38 詳細化ラウンド）は「mono-theta 環境」を
  Dα-2〜7 の共通入力として単一の型に固定することが目的であり、本層は
  柱E の並行部品 M92/M98F/M116F/M124F/M137F/M187F/M190F を束ねるだけで
  達成される（bundling capstone）。特に Dα-5 の `splitMono`（分離
  mono-theta 環）は本構造体 `MonoThetaEnv` をパラメータとして受け取る
  設計を想定する。

  **正直な限定**: 本層が束ねるのは mono-theta 環境の**群論的・整数論的
  骨格**（Heisenberg 群・l-捻れ商・±-構造・cyclotomic 同期・関数等式
  リフト）のみ。log-shell（Dα-2）・Ind（Dα-3）・Kummer 同型（Dα-4）は
  次層であり、MultiradialRep の構成（柱D の本丸・定理3.11 充足）は
  柱D 本体（M97 Theorem311Premises 系列）・D-β の領分で本層の範囲外。
  ThetaGroupModData の rigidity フィールドと ThetaPMData の各フィールド
  はいずれも thetaGrpMod l の Quot 商上の言明であり、その構成
  （thetaModMul 等の Quot.lift）は Quot.sound を用いる
  （選択公理ではない、商の構成に内在）。全て選択公理不使用
  （`monoThetaEnv_exists` の μ_l 生成元取り出しも Nonempty という
  Prop への Exists 除去であり choice を要しない）。
-/
import IUT.MonoThetaWitness
import IUT.ThetaGroupMod
import IUT.ThetaPM
import IUT.CyclotomicSync
import IUT.ThetaHeisenbergLift
import IUT.ThetaFuneqBridge

namespace IUT

/-! ## M196F-1: mono-theta 環境の単一インターフェース -/

/-- **M196F-1: mono-theta 環境** — [EtTh] の mono-theta 環境の群論的・
    整数論的骨格を一つの構造体に束ねる。柱D Dα プログラムの入力として
    参照される単一の型（Dα-2〜7 が本構造体をパラメータに取る想定）。

    パラメータ: `R` はテータ級数の係数環（解析側 M190F 用）、`p` は
    素数、`l = 2L+1` は奇数の捻れ次数（`l ∣ p−1`）。 -/
structure MonoThetaEnv (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) where
  /-- 柱E: mono-theta witness（M92 — 切断・反復関数等式・ガウス値・
      cyclotomic rigidity・Tate 降下の束）。 -/
  monoTheta : MonoThetaWitness
  /-- 柱E: テータ群 mod l（M98F — 射影・交換子公式・mod-l cyclotomic
      rigidity・商標準切断とその周期 2l）。 -/
  thetaMod : ThetaGroupModData l
  /-- 柱E: ±-構造 ι（M116F — インバージョン自己同型・対合性・中心固定・
      ±-切断相互作用・mod-l 降下・ラベル j ↔ l−j の中心捻れ付き同一視）。 -/
  pm : ThetaPMData l
  /-- 柱E: シクロトミック同期 centerToMu（M124F — 中心 (0,0,z) ↦ ζ^z の
      well-definedness・準同型性・忠実性・mod-l 降下・±-両立）。 -/
  sync : CyclotomicSyncData p l hp (by omega) hdvd
  /-- 柱E: 関数等式の Heisenberg リフト（M187F — 中心捻れ funeqTwist の
      明示形・閉形式・μ_l ラベル同定・商群での等式リフト）。 -/
  lift : ThetaHeisenbergLiftData p l L hL hodd
  /-- 柱E: 解析↔群接合（M190F — 反転 J の反復伝播・解析側ラベル入替
      J(T^j Θ) = T^{l−j}(Θ)・ガウス次数差 = funeqTwist・四者の一括接合）。 -/
  bridge : ThetaFuneqBridgeData R p l L hL hodd

/-! ## M196F-2/3: witness 本体と存在 -/

/-- **M196F-2: mono-theta 環境の witness 本体** — μ_l 生成元 ζ とその
    l 乗根性 hζl を明示引数に取り、全フィールドを既存の直接 def
    （`monoThetaWitness` / `thetaGroupModData` / `thetaPMData` /
    `cyclotomicSyncData` / `thetaHeisenbergLiftData` /
    `thetaFuneqBridgeData`）で埋める choice-free コンストラクタ。 -/
def monoThetaEnv (R : CRing) (p l L : Nat) (hp : IsPrime p) (hL : 1 ≤ L)
    (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) :
    MonoThetaEnv R p l L hp hL hodd hdvd where
  monoTheta := monoThetaWitness
  thetaMod := thetaGroupModData l
  pm := thetaPMData l
  sync := cyclotomicSyncData p l hp (by omega) hdvd
  lift := thetaHeisenbergLiftData p l L hL hodd ζ hζl
  bridge := thetaFuneqBridgeData R p l L hL hodd ζ hζl

/-- **定理 (M196F-3): mono-theta 環境の存在（見出し）** — p 素数・
    l = 2L+1 ∣ p−1 なら mono-theta 環境が存在する（μ_l 生成元は M121F
    `mu_l_zp_exists` から Prop（Nonempty）の中で取り出す——choice 不要）。 -/
theorem monoThetaEnv_exists (R : CRing) (p l L : Nat) (hp : IsPrime p)
    (hL : 1 ≤ L) (hodd : l = 2 * L + 1) (hdvd : l ∣ p - 1) :
    Nonempty (MonoThetaEnv R p l L hp hL hodd hdvd) := by
  obtain ⟨ζ, hζl, _hdist, _ha⟩ := mu_l_zp_exists p l hp (by omega) hdvd
  exact ⟨monoThetaEnv R p l L hp hL hodd hdvd ζ hζl⟩

end IUT
