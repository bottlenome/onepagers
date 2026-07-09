/-
  IUT/GenExtTower.lean — capstone/F7（A1 0.85 統合層）:
  一般既約 f に対する体拡大 ℚ ↪ K = ℚ[x]/(f) と冪基底の塔スロット接続

  ── 主要成果の分類: **[実／承認済み足場(c)]**（F6 の全域 inv 付き実体
     `gefNFIUTField : IUTField` と F9 の冪基底 `gefPowBasis` を、体拡大
     `FieldExtension`（ℚ↪K）と塔データ `TowerData.basisLK` スロットへ接続する
     統合層。定数埋め込み `psC` を環準同型 ℚ→K として本物に据え、F9 の
     ℚ-加群 `gefNFModule`（smul = 未簡約定数倍）を制限正則加群
     `towerLawRestrict E (towerLawRegModule K)`（smul = 掛けて f で簡約）へ
     smul の命題的一致で移送し、冪基底を basisLK スロット型で建てる）。

  **complete_pct 影響**: A1（実 ℚ[x]/(f)・全域 inv・冪基底）を FieldExtension
  ℚ↪K と TowerData.basisLK へ接続し、[K:ℚ]=n を体拡大次数として確定。前回 A1
  監査が名指しした残欠（基底・次数理論）を**体拡大の主語で**閉じる承認済み足場。
  complete_pct は独立再監査で確定（本層単体では未設定）。complete_pct 未設定。

  本物性: `gefIncl`（定数埋め込み ℚ→K）は `psConstHom ratRing`（環準同型 psC）を
  `gefNFRing` の add/mul/one へ落としたもので、mul は次数 0 の psC·psC が
  `pfdRed_of_bounded` で簡約恒等ゆえ本物に環準同型をなす。制限正則加群の
  smul c x = gefNFRing.mul (psC c) x = pfdRed(psMul(psC c) x) は、F9 の
  gefNFModule.smul c x = psMul(psC c) x（未簡約）と、psC c が次数 0・x が
  deg<nf ゆえ psMul(psC c) x が deg<nf → pfdRed 恒等（`pfdRed_of_bounded`）で
  命題的に一致する（`gefRestrictSmul_eq`）。よって F9 の span/indep を制限正則
  加群へ `towerLawSum_congr` で移送し、冪基底 `gefRegBasis` を
  `TowerData.basisLK` スロット型で本物に建てる。模型・代理・toy 主語なし。

  正直な限定:
   - 基礎体 ℚ 固定・既約性 hirr は f ごと手証明の入力。
   - 次元 well-defined 性（`TowerLawBasis` の honest 仮説 1・M281F と同精神）は
     未証明。次数 [K:ℚ] は基底 witness 依存の定義値 nf = deg f。
   - Gal・分離次数・塔法則の乗法性への流し込みは後段（本層は basisLK スロット
     への接続と [K:ℚ]=n の体拡大主語での確定まで）。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.GenExtFieldInv
import IUT.GenExtBasisAlpha

namespace IUT

/-! ## F7-1: 定数埋め込み ℚ → K（psC を担体 `GefNF` へ） -/

/-- **F7-1: 定数埋め込み** — 有理数 c を定数多項式 `psC c`（次数 0）として NF 担体
    `GefNF f nf` に据える。次数 0 < nf ゆえ簡約不要で有界（psC は index 0 以外 0）。 -/
def gefIncl (f : PS ratRing) (nf : Nat) (hn : 1 ≤ nf) (c : QRat) : GefNF f nf :=
  ⟨psC ratRing c, fun j hj => by
    show (if j = 0 then c else ratRing.zero) = ratRing.zero
    exact if_neg (by omega)⟩

/-! ## F7-2: 体拡大 ℚ ↪ K = ℚ[x]/(f) -/

/-- **F7-2: 体拡大 ℚ↪K** — base = ℚ（`ratIUTField`）、top = 全域 inv 付き実体
    K = `gefNFIUTField`（F6）、incl = 定数埋め込み `gefIncl`。incl が環準同型を
    なすことは `psConstHom ratRing`（psC の add/mul/one 保存）を `gefNFRing` の
    演算へ落として本物に閉じる。mul 保存は psC·psC が次数 0 で簡約恒等
    （`pfdRed_of_bounded`）である点を使う。 -/
def gefFieldExtension (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) : FieldExtension where
  base := ratIUTField
  top := gefNFIUTField f nf hb hl hn hirr
  incl := gefIncl f nf hn
  incl_add := fun x y => Subtype.ext ((psConstHom ratRing).map_add x y)
  incl_mul := fun x y => by
    apply Subtype.ext
    show psC ratRing (ratRing.mul x y)
        = pfdRed f nf nf (psMul ratRing (psC ratRing x) (psC ratRing y))
    have hmm : psMul ratRing (psC ratRing x) (psC ratRing y)
        = psC ratRing (ratRing.mul x y) := ((psConstHom ratRing).map_mul x y).symm
    rw [hmm]
    have hbc : IsPolyBounded ratRing (psC ratRing (ratRing.mul x y)) nf := by
      intro j hj
      show (if j = 0 then ratRing.mul x y else ratRing.zero) = ratRing.zero
      exact if_neg (by omega)
    funext j
    exact (pfdRed_of_bounded f nf hb hl nf (psC ratRing (ratRing.mul x y)) hbc j).symm
  incl_one := Subtype.ext (psConstHom ratRing).map_one

/-! ## F7-3: 制限正則加群と F9 加群の smul 一致（核心） -/

/-- **F7-3: smul 一致** — 制限正則加群
    `towerLawRestrict (gefFieldExtension) (towerLawRegModule K)` の
    smul c x = K.mul (gefIncl c) x = pfdRed(psMul(psC c) x.val)（掛けて簡約）と、
    F9 の ℚ-加群 `gefNFModule` の smul c x = psMul(psC c) x.val（未簡約）は
    命題的に等しい。psC c は次数 0・x.val は deg < nf ゆえ psMul(psC c) x.val は
    deg < nf → pfdRed が恒等（`pfdRed_of_bounded`）。有界性は F9 の smul の
    担体証明（`.property`）を再利用する。 -/
theorem gefRestrictSmul_eq (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) (c : QRat) (x : GefNF f nf) :
    (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
        (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))).smul c x
      = (gefNFModule f nf hb hl hn).smul c x := by
  apply Subtype.ext
  show pfdRed f nf nf (psMul ratRing (psC ratRing c) x.val)
      = psMul ratRing (psC ratRing c) x.val
  funext j
  exact pfdRed_of_bounded f nf hb hl nf (psMul ratRing (psC ratRing c) x.val)
    ((gefNFModule f nf hb hl hn).smul c x).property j

/-- **F7-3b: 有限和の加群間移送** — 制限正則加群と F9 加群 `gefNFModule` は
    add/zero がともに `gefNFRing` 由来で defeq。よって任意の族 g に対し
    `towerLawSum` は両加群で一致する（n 帰納・add/zero の defeq で各段が rfl）。
    smul が異なっても和は add/zero のみに依るため一致。 -/
theorem gefSumTransfer (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) :
    ∀ (n : Nat) (g : Fin n → GefNF f nf),
      towerLawSum
        (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
          (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) n g
      = towerLawSum (gefNFModule f nf hb hl hn) n g := by
  intro n
  induction n with
  | zero =>
    intro g
    rfl
  | succ m ih =>
    intro g
    rw [towerLawSum_succ
        (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
          (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) m g,
      towerLawSum_succ (gefNFModule f nf hb hl hn) m g,
      ih (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
    rfl

/-! ## F7-4: 冪基底を basisLK スロット型へ（span・indep の移送） -/

/-- **F7-4a: span 移送** — 任意の K の元 v は制限正則加群の上で冪
    {1, α, …, α^{n−1}} の ℚ-線形結合。F9 の `gefPow_spans`（gefNFModule 上）を
    smul 一致（`gefRestrictSmul_eq`）と `towerLawSum_congr` で制限正則加群へ移す
    （add/zero は両加群で `gefNFRing` 由来ゆえ defeq・towerLawSum は一致）。 -/
theorem gefRegSpans (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f)
    (v : GefNF f nf) :
    v = towerLawSum
        (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
          (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) nf
        (fun i : Fin nf =>
          (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
            (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))).smul (v.val i.val)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val)) := by
  have e1 : towerLawSum
        (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
          (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) nf
        (fun i : Fin nf =>
          (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
            (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))).smul (v.val i.val)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))
      = towerLawSum
        (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
          (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) nf
        (fun i : Fin nf =>
          (gefNFModule f nf hb hl hn).smul (v.val i.val)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val)) :=
    towerLawSum_congr _ nf _ _
      (fun i => gefRestrictSmul_eq f nf hb hl hn hirr (v.val i.val)
        (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))
  have e2 : towerLawSum
        (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
          (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) nf
        (fun i : Fin nf =>
          (gefNFModule f nf hb hl hn).smul (v.val i.val)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))
      = towerLawSum (gefNFModule f nf hb hl hn) nf
        (fun i : Fin nf =>
          (gefNFModule f nf hb hl hn).smul (v.val i.val)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val)) :=
    gefSumTransfer f nf hb hl hn hirr nf _
  rw [e1, e2]
  exact gefPow_spans f nf hb hl hn v

/-- **F7-4b: 一次独立 移送** — 制限正則加群の上で冪 {1, α, …, α^{n−1}} の
    ℚ-線形結合 = 0 ⟹ 全係数 0。F9 の `gefPow_indep`（gefNFModule 上）を
    smul 一致で制限正則加群へ移す。零も `gefNFRing` 由来ゆえ両加群で defeq。 -/
theorem gefRegIndep (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) (c : Fin nf → QRat)
    (h : towerLawSum
        (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
          (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) nf
        (fun i : Fin nf =>
          (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
            (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))).smul (c i)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))
        = (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
            (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))).zero) :
    ∀ i, c i = ratRing.zero := by
  have ec : towerLawSum
        (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
          (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) nf
        (fun i : Fin nf =>
          (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
            (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))).smul (c i)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))
      = towerLawSum
        (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
          (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) nf
        (fun i : Fin nf =>
          (gefNFModule f nf hb hl hn).smul (c i)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val)) :=
    towerLawSum_congr _ nf _ _
      (fun i => gefRestrictSmul_eq f nf hb hl hn hirr (c i)
        (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))
  have ed : towerLawSum
        (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
          (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) nf
        (fun i : Fin nf =>
          (gefNFModule f nf hb hl hn).smul (c i)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))
      = towerLawSum (gefNFModule f nf hb hl hn) nf
        (fun i : Fin nf =>
          (gefNFModule f nf hb hl hn).smul (c i)
            (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val)) :=
    gefSumTransfer f nf hb hl hn hirr nf _
  have h' : towerLawSum (gefNFModule f nf hb hl hn) nf
      (fun i : Fin nf =>
        (gefNFModule f nf hb hl hn).smul (c i)
          (gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val))
      = (gefNFModule f nf hb hl hn).zero :=
    ed.symm.trans (ec.symm.trans h)
  exact gefPow_indep f nf hb hl hn c h'

/-- **F7-4c: 冪基底（basisLK スロット型）** — 冪 {1, α, …, α^{n−1}} を、塔データ
    `TowerData.basisLK` の型
    `TowerLawBasis ext.base (towerLawRestrict ext (towerLawRegModule ext.top))`
    で建てる（dim = nf、vec = α の冪、repr = 担体元の係数）。span/indep は
    F9 の冪基底からの移送（`gefRegSpans`/`gefRegIndep`）。 -/
def gefRegBasis (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) :
    TowerLawBasis ratIUTField
      (towerLawRestrict (gefFieldExtension f nf hb hl hn hirr)
        (towerLawRegModule (gefNFIUTField f nf hb hl hn hirr))) where
  dim := nf
  vec := fun i => gefNFPow f nf hb hl hn (gefAlpha f nf hb hl hn) i.val
  repr := fun x i => x.val i.val
  spans := gefRegSpans f nf hb hl hn hirr
  indep := gefRegIndep f nf hb hl hn hirr

/-! ## F7-5: 拡大次数 [K:ℚ] = n = deg f（体拡大の主語で） -/

/-- **F7-5: [K:ℚ] = nf = deg f** — 制限正則加群（体拡大 ℚ↪K の basisLK スロット）
    上の冪基底の要素数。F9（gefNFModule 上の `gef_degree_eq`）を、体拡大
    `FieldExtension` の basisLK 主語で再確定。 -/
theorem gefTowerDegree (f : PS ratRing) (nf : Nat)
    (hb : IsPolyBounded ratRing f (nf + 1)) (hl : f nf ≠ ratRing.zero)
    (hn : 1 ≤ nf) (hirr : pibIrreducible ratRing f) :
    towerLawDegree (gefRegBasis f nf hb hl hn hirr) = nf := rfl

end IUT
