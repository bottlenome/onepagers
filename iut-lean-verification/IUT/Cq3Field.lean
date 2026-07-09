/-
  IUT/Cq3Field.lean — CQ2（A1 実数体 ℚ(ζ₃) = ℚ[x]/(x²+x+1) の
  体化・capstone。ℚ(∛2) の `CbrtTwoField`（CTF）の次数2版アナロジー）

  ── 分類 **[実／capstone]**（本物の先行建設の束ね。骨格でなく実 ℚ・実
  f = Φ₃ = x²+x+1（円分多項式）の本物の商環を本物のイデアル極大性
  （`cq1_bezout`）で体化する・sorry 皆無・新規 Classical.choice 皆無・
  模型ゼロ）。名前付き実ターゲット: A1「実数体 K = ℚ[x]/(f) を実際の
  商環として構成」の第二の本物のインスタンス **実二次数体 ℚ(ζ₃)**
  （CTF の実三次数体 ℚ(∛2) の次数2版アナロジー）。

  本層は下記の本物の部品を `SimpleExtData` に充填して `SimpleExtData.build`
  で体化する（新規証明はほぼゼロ・全 field が本物）:
   * modulus/deg/bound/lead/deg_pos/base_nontrivial — `Cq3Base`（CQ0）で
     実 ℚ・実 f = x²+x+1 に確定済みの本物のデータ。
   * **bezout** — `Cq3BezoutChain`（CQ1）の `cq1_bezout`（f のイデアル極大性
     = 次数2固定ユークリッド鎖で本物に証明済み）。honest 仮説を本物で充填。

  内容（CTF の次数2版）:
   * `cq2Data` — `SimpleExtData cq0Field`（全 field 本物・bezout = cq1_bezout）。
   * `cq2Field` — `SimpleFieldExt cq0Field`（= cq2Data.build）。
   * `cq2Ring` — 実商環 (quotCRing (polyCRing ratRing) cq0Modulus).carrier を
     持つ ℚ(ζ₃) = ℚ[x]/(x²+x+1)。
   * `cq2_has_inverses` — 非零元は逆元を持つ（∃ 形・体性）。
   * `cq2_nontrivial` — 1 ≠ 0。
   * `cq2_emb_injective` — ℚ ↪ ℚ(ζ₃) は単射。
   * `cq2_exists` — capstone: ℚ 上の実二次数体（体性込み）が存在する。

  **complete_pct 影響**: 本タスクでは complete_pct は**未設定（動かさない）**
  （親が A1 二軸の更新を統合時に判断する）。本層は本物の商環の本物の体化で
  あり、水増しの束ねではない——carrier は文字どおり実商環、体性は本物の
  イデアル極大性（cq1_bezout）に由来する。

  正直な限定（§4 規約により消さない）:
   - **単一 f = x²+x+1 のみ**。一般既約 f への Bezout・体化は未達
     （CTF と同じく名前付き後続）。
   - 逆元は ∃ 形（全域 inv 付き IUTField 昇格は別スライス）。
   - 次数 2 の完全抽出（1, ζ₃ の基底性）は本層に含めない（後続）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.Cq3Base
import IUT.Cq3BezoutChain
import IUT.SimpleExtension

namespace IUT

/-! ## CQ2-1: 単純体拡大の入力データ（全 field 本物） -/

/-- **CQ2-1: ℚ(ζ₃) の `SimpleExtData`** — 基礎体 ℚ（`cq0Field`）上の法多項式
    f = x²+x+1（`cq0PS`, deg 2）に、本物の有界性（`cq0_bound`）・先頭係数
    ≠ 0（`cq0_lead`）・deg ≥ 1・基礎体非自明性（`cq0_base_nontrivial`）、
    そして本丸のイデアル極大性 **`cq1_bezout`** を充填する。honest 仮説
    `SimpleExtData.bezout` を本物で埋める点が体化の要。型は全て defeq で
    一致（`cq0Field.ring ≡ ratRing`、`2 + 1 ≡ 3`、`simpleExtModulus
    cq0Field cq0PS 2 cq0_bound ≡ cq0Modulus`）。 -/
def cq2Data : SimpleExtData cq0Field where
  modulus := cq0PS
  deg := 2
  bound := cq0_bound
  lead := cq0_lead
  deg_pos := by omega
  base_nontrivial := cq0_base_nontrivial
  bezout := cq1_bezout

/-! ## CQ2-2: 体拡大レコード ℚ(ζ₃) -/

/-- **CQ2-2: 実二次数体 ℚ(ζ₃)**（`SimpleFieldExt cq0Field`）— 入力データ
    `cq2Data` を `SimpleExtData.build` に通し、拡大環・単射埋め込み・
    非自明性・逆元の存在を本物に組み上げる。 -/
def cq2Field : SimpleFieldExt cq0Field := cq2Data.build cq0Field

/-- **CQ2-3: 実商環 ℚ(ζ₃) = ℚ[x]/(x²+x+1)** — carrier は文字どおり
    `(quotCRing (polyCRing ratRing) cq0Modulus).carrier`（= 本物の単項
    イデアル商環）。 -/
def cq2Ring : CRing := cq2Field.ring

/-! ## CQ2-4: 射影定理（監査向け見出し） -/

/-- **CQ2-4a: 体性** — ℚ(ζ₃) の非零元は必ず乗法逆元を持つ（構成的 ∃ 形）。
    本物のイデアル極大性 `cq1_bezout` に由来する。 -/
theorem cq2_has_inverses :
    ∀ x : cq2Ring.carrier, x ≠ cq2Ring.zero →
      ∃ y, cq2Ring.mul x y = cq2Ring.one :=
  cq2Field.has_inverses

/-- **CQ2-4b: 非自明性** — ℚ(ζ₃) は 1 ≠ 0。 -/
theorem cq2_nontrivial : cq2Ring.one ≠ cq2Ring.zero :=
  cq2Field.nontrivial

/-- **CQ2-4c: 埋め込みの単射性** — ℚ ↪ ℚ(ζ₃) は単射（deg f = 2 ≥ 1）。 -/
theorem cq2_emb_injective :
    ∀ {c d : cq0Field.ring.carrier},
      cq2Field.emb.map c = cq2Field.emb.map d → c = d :=
  cq2Field.emb_injective

/-! ## CQ2-5: capstone — 実二次数体の存在 -/

/-- **CQ2-5（capstone）: ℚ 上の実二次数体 ℚ(ζ₃) の存在** — carrier が
    本物の商環 ℚ[x]/(x²+x+1) であり、非零元がすべて逆元を持つ（体性）
    `SimpleFieldExt cq0Field` が存在する。 -/
theorem cq2_exists :
    ∃ E : SimpleFieldExt cq0Field,
      (∀ x : E.ring.carrier, x ≠ E.ring.zero →
        ∃ y, E.ring.mul x y = E.ring.one) :=
  ⟨cq2Field, cq2Field.has_inverses⟩

end IUT

#print axioms IUT.cq2_exists
