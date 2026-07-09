/-
  IUT/CyclotomicField3.lean — A3/W-A1（CNF: 円分体 ℚ(ζ₃) = ℚ[x]/(Φ₃) の
  gefNF 体化・ℚ↪K₁ 拡大・Galois 群スロット）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・実
     円分多項式 Φ₃ = x²+x+1 の上で、全域 inv 付き実体 `gefNFIUTField`（F6）を
     円分体 ℚ(ζ₃) として実例化し、非自明有限体拡大 ℚ ⊂ ℚ(ζ₃) を本物に立てる。
     入力は全て実在資産（`cq0_bound`/`cq0_lead`/`cqi_irreducible`）で honest
     仮説パラメータ 0 本）。

  complete_pct 影響: A3（実 π₁^ét / G_K）への本物前進候補。「柱 A は非自明有限体
  拡大が 1 つも構成されておらず全 Galois 塔が trivialExtension 詰め」という欠落の
  初 discharge を、ζ_9・一般 n にスケールする gefNF 担体上で行う第一段。CNF は
  F6/F7 の一般エンジンの Φ₃ 実例化に徹し（車輪の再発明をしない）、車輪の
  再発明でない新規部品は `gefNFConst_inj`（定数埋め込みの単射性）のみ。
  本ファイル単体では complete_pct 未設定（監査確定待ち・Gal 完全決定は
  `CyclotomicGal3.lean` で）。

  内容:
   * `cnf_one_le_two` — 1 ≤ 2（nf = 2 の deg_pos）。
   * `cnfPhi3Field : IUTField` — ℚ(ζ₃) = ℚ[x]/(Φ₃)（`gefNFIUTField` の実例化）。
   * `cnfPhi3F268 : Field268` — 同・除法/根数え上げの入力型（`gefNF268` の実例化）。
   * `cnfExt3 : FieldExtension` — ℚ ⊂ ℚ(ζ₃)（F7 `gefFieldExtension` の実例化・
     incl = 定数埋め込み `gefIncl`）。
   * `cnfGal3 : Grp` — Gal(ℚ(ζ₃)/ℚ) の群スロット（`galoisGroupGrp cnfExt3`）。
   * `gefNFConst_inj` — 定数埋め込み `gefIncl` の単射性（0 次係数読み出し。
     `FieldExtension` に単射性公理が無い分の呼び出し側補題）。

  正直な限定（§4 規約により消さない・追記のみ）:
   (i)   p = 3・ℚ 上・1 段のみの忠実な部分ケース（一般 n 塔は後段）。
   (ii)  Gal(ℚ(ζ₃)/ℚ) の位数ちょうど 2 の完全決定は本ファイルには無く
         `CyclotomicGal3.lean`（CG3）で行う。本ファイルは体化・拡大・群スロット
         まで。
   (iii) K₁ = ℚ(ζ₃) は既存 `cq3Field`/`qdfField (−3)`/`gfiCq3Field` と**同型な
         第 4 の担体**（gefNF 表示）であり、同型による定理輸送は対象外。
   (iv)  res（制限準同型）・全射性・分離性・正規性の一般論は未形式化。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイルのみ（共有ファイル不更新）。
-/
import IUT.GenExtTower
import IUT.Cq3Irreducible
import IUT.FieldAutGroup

namespace IUT

/-! ## CNF-0: nf = 2 の次数正値 -/

/-- **CNF-0: 1 ≤ 2** — nf = deg Φ₃ = 2 の `deg_pos`。 -/
theorem cnf_one_le_two : (1 : Nat) ≤ 2 := by omega

/-! ## CNF-1: ℚ(ζ₃) = ℚ[x]/(Φ₃) の体化（F6 の実例化） -/

/-- **CNF-1a: 円分体 ℚ(ζ₃) = ℚ[x]/(Φ₃) （IUTField）** — 全域 inv 付き実体
    `gefNFIUTField`（F6）を Φ₃ = x²+x+1 で実例化。入力は全て実在資産:
    `cq0_bound`（deg ≤ 2）・`cq0_lead`（先頭係数 ≠ 0）・`cqi_irreducible`
    （既約性）。honest 仮説 0 本。 -/
def cnfPhi3Field : IUTField :=
  gefNFIUTField cq0PS 2 cq0_bound cq0_lead cnf_one_le_two cqi_irreducible

/-- **CNF-1b: ℚ(ζ₃) の `Field268` 表示** — 除法定理・根の個数上界（R1）の
    入力型。`gefNF268` の Φ₃ 実例化。 -/
def cnfPhi3F268 : Field268 :=
  gefNF268 cq0PS 2 cq0_bound cq0_lead cnf_one_le_two cqi_irreducible

/-! ## CNF-2: 非自明拡大 ℚ ⊂ ℚ(ζ₃)（F7 の実例化） -/

/-- **CNF-2a: 体拡大 ℚ ⊂ ℚ(ζ₃)** — F7 `gefFieldExtension`（ℚ↪K・incl = 定数
    埋め込み `gefIncl`・環準同型性は `psConstHom` から）を Φ₃ で実例化。
    「非自明有限体拡大が 1 つも構成されていない」欠落の初 discharge の主語。 -/
def cnfExt3 : FieldExtension :=
  gefFieldExtension cq0PS 2 cq0_bound cq0_lead cnf_one_le_two cqi_irreducible

/-- **CNF-2b: Gal(ℚ(ζ₃)/ℚ) の群スロット** — `galoisGroupGrp cnfExt3`。位数
    ちょうど 2 の完全決定は CG3（`CyclotomicGal3.lean`）で本物化する。 -/
def cnfGal3 : Grp := galoisGroupGrp cnfExt3

/-! ## CNF-3: 定数埋め込みの単射性 -/

/-- **CNF-3: `gefIncl` の単射性** — 定数埋め込み c ↦ psC c は 0 次係数の
    読み出しで単射。`FieldExtension` に単射性公理が無いので、呼び出し側で
    Galois 対象を扱う際に必要な補題（scout §2-1 の指摘の discharge）。 -/
theorem gefNFConst_inj (f : PS ratRing) (nf : Nat) (hn : 1 ≤ nf) (c1 c2 : QRat)
    (h : gefIncl f nf hn c1 = gefIncl f nf hn c2) : c1 = c2 := by
  have hval : (gefIncl f nf hn c1).val 0 = (gefIncl f nf hn c2).val 0 :=
    congrArg (fun z : GefNF f nf => z.val 0) h
  have h1 : (gefIncl f nf hn c1).val 0 = c1 := by
    show psC ratRing c1 0 = c1
    exact if_pos rfl
  have h2 : (gefIncl f nf hn c2).val 0 = c2 := by
    show psC ratRing c2 0 = c2
    exact if_pos rfl
  rw [h1, h2] at hval
  exact hval

end IUT
