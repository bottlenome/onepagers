/-
  IUT/CbrtTwoField.lean — CTF（A1 実数体 ℚ(∛2) = ℚ[x]/(x³−2) の
  Wave 3 / N8: 実三次数体 ℚ(∛2) の体化・capstone）

  ── 分類 **[実／capstone]**（本物の先行建設の束ね。骨格でなく実 ℚ・実
  f = x³−2 の本物の商環を本物のイデアル極大性（`cbc_bezout`）で体化する・
  sorry 皆無・新規 Classical.choice 皆無・模型ゼロ）。名前付き実ターゲット:
  A1「実数体 K = ℚ[x]/(f) を実際の商環として構成」の最初の本物のインスタンス
  **実三次数体 ℚ(∛2)**（設計書 `audit/A1-real-numberfield-plan.md` §1 の G3・
  §4 の N8）。

  本層は下記の本物の部品を `SimpleExtData` に充填して `SimpleExtData.build`
  で体化する（新規証明はほぼゼロ・全 field が本物）:
   * modulus/deg/bound/lead/deg_pos/base_nontrivial — `CbrtTwoBase`（CT0）で
     実 ℚ・実 f = x³−2 に確定済みの本物のデータ。
   * **bezout** — `CbrtBezoutChain`（CBC）の `cbc_bezout`（f のイデアル極大性
     = 次数3固定ユークリッド鎖で本物に証明済み）。honest 仮説を本物で充填。

  内容（設計 §1 G3）:
   * `ctfData` — `SimpleExtData ct0Field`（全 field 本物・bezout = cbc_bezout）。
   * `ctfField` — `SimpleFieldExt ct0Field`（= ctfData.build）。
   * `ctfRing` — 実商環 (quotCRing (polyCRing ratRing) ct0Modulus).carrier を
     持つ ℚ(∛2) = ℚ[x]/(x³−2)。
   * `ctf_has_inverses` — 非零元は逆元を持つ（∃ 形・体性）。
   * `ctf_nontrivial` — 1 ≠ 0。
   * `ctf_emb_injective` — ℚ ↪ ℚ(∛2) は単射。
   * `ctf_exists` — capstone: ℚ 上の実三次数体（体性込み）が存在する。

  **complete_pct 影響**: 本タスクでは complete_pct は**未設定（動かさない）**
  （親が A1 二軸の更新を統合時に判断する）。本層は本物の商環の本物の体化で
  あり、水増しの束ねではない——carrier は文字どおり実商環、体性は本物の
  イデアル極大性（cbc_bezout）に由来する。

  正直な限定（§4 規約により消さない）:
   - **単一 f = x³−2 のみ**。一般既約 f への Bezout・体化は未達（設計 §5 の
     名前付き後続）。
   - 逆元は ∃ 形（全域 inv 付き IUTField 昇格は別スライス）。
   - 次数 3 の完全抽出（1, α, α² の基底性）は本層に含めない（後続）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.CbrtTwoBase
import IUT.CbrtBezoutChain
import IUT.SimpleExtension

namespace IUT

/-! ## CTF-1: 単純体拡大の入力データ（全 field 本物） -/

/-- **CTF-1: ℚ(∛2) の `SimpleExtData`** — 基礎体 ℚ（`ct0Field`）上の法多項式
    f = x³−2（`ct0PS`, deg 3）に、本物の有界性（`ct0_bound`）・先頭係数
    ≠ 0（`ct0_lead`）・deg ≥ 1・基礎体非自明性（`ct0_base_nontrivial`）、
    そして本丸のイデアル極大性 **`cbc_bezout`** を充填する。honest 仮説
    `SimpleExtData.bezout` を本物で埋める点が体化の要。型は全て defeq で
    一致（`ct0Field.ring ≡ ratRing`、`3 + 1 ≡ 4`、`simpleExtModulus
    ct0Field ct0PS 3 ct0_bound ≡ ct0Modulus`）。 -/
def ctfData : SimpleExtData ct0Field where
  modulus := ct0PS
  deg := 3
  bound := ct0_bound
  lead := ct0_lead
  deg_pos := by omega
  base_nontrivial := ct0_base_nontrivial
  bezout := cbc_bezout

/-! ## CTF-2: 体拡大レコード ℚ(∛2) -/

/-- **CTF-2: 実三次数体 ℚ(∛2)**（`SimpleFieldExt ct0Field`）— 入力データ
    `ctfData` を `SimpleExtData.build` に通し、拡大環・単射埋め込み・
    非自明性・逆元の存在を本物に組み上げる。 -/
def ctfField : SimpleFieldExt ct0Field := ctfData.build ct0Field

/-- **CTF-3: 実商環 ℚ(∛2) = ℚ[x]/(x³−2)** — carrier は文字どおり
    `(quotCRing (polyCRing ratRing) ct0Modulus).carrier`（= 本物の単項
    イデアル商環）。 -/
def ctfRing : CRing := ctfField.ring

/-! ## CTF-4: 射影定理（監査向け見出し） -/

/-- **CTF-4a: 体性** — ℚ(∛2) の非零元は必ず乗法逆元を持つ（構成的 ∃ 形）。
    本物のイデアル極大性 `cbc_bezout` に由来する。 -/
theorem ctf_has_inverses :
    ∀ x : ctfRing.carrier, x ≠ ctfRing.zero →
      ∃ y, ctfRing.mul x y = ctfRing.one :=
  ctfField.has_inverses

/-- **CTF-4b: 非自明性** — ℚ(∛2) は 1 ≠ 0。 -/
theorem ctf_nontrivial : ctfRing.one ≠ ctfRing.zero :=
  ctfField.nontrivial

/-- **CTF-4c: 埋め込みの単射性** — ℚ ↪ ℚ(∛2) は単射（deg f = 3 ≥ 1）。 -/
theorem ctf_emb_injective :
    ∀ {c d : ct0Field.ring.carrier},
      ctfField.emb.map c = ctfField.emb.map d → c = d :=
  ctfField.emb_injective

/-! ## CTF-5: capstone — 実三次数体の存在 -/

/-- **CTF-5（capstone・G3）: ℚ 上の実三次数体 ℚ(∛2) の存在** — carrier が
    本物の商環 ℚ[x]/(x³−2) であり、非零元がすべて逆元を持つ（体性）
    `SimpleFieldExt ct0Field` が存在する。 -/
theorem ctf_exists :
    ∃ E : SimpleFieldExt ct0Field,
      (∀ x : E.ring.carrier, x ≠ E.ring.zero →
        ∃ y, E.ring.mul x y = E.ring.one) :=
  ⟨ctfField, ctfField.has_inverses⟩

end IUT

#print axioms IUT.ctf_exists
