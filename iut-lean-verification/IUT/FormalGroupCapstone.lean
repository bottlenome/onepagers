/-
  # M224F: 柱C Lubin–Tate プログラムの総括 capstone（柱C・並行部品）

  柱C「形式群・Lubin–Tate」系列のうち、素数 p と ℤ_p-係数 a に共通に
  パラメータ化された一貫部分——**存在＋一意性（M49F/M42F）**・
  **End(F) 環パッケージ ℤ_p ≅ End(F)（M208F）**・**反復 [p^n] 系列の
  同定と可換性（M72F-5/7）**——を一つの証明記録に束ねる。本モジュールは
  新規の数学的主張を持たない（**新規証明ゼロ**）。全フィールドは既存
  定理 `lubin_tate` / `formalEndRingData` / `ltIter_eq_ltSol` /
  `ltIter_comm` をそのまま代入するだけで埋まる。

  * M224F-1（LT-1）`lt` — Lubin–Tate 補題（M49F 存在 + M42F 一意性の
    パッケージ）: F(0) = 0・F(1) = a・F∘f = π·F + F^p を満たす
    F が存在し、同じ境界条件を満たす任意の F' はこの F に一致する
    （`lubin_tate p hp a`）
  * M224F-2（LT-2）`endRing` — End(F) 環パッケージ（M208F）: End(F) を
    一個の `CRing`、包含 ι : ℤ_p → End(F) を一個の `RingHom` として
    実体化し、ι が単射かつ全射（= 環同型 ℤ_p ≅ End(F)）であることを
    束ねた `FormalEndRingData`（`formalEndRingData p hp`）
  * M224F-3（LT-3）`iterEqSol` — [p^n] 系列の同定（M72F-7）: LT 多項式
    f = πX + X^p の n 回反復 f^{∘n} が、Lubin–Tate 補題の一意解
    [π^n] = ltSol p hp (π^n) に一致する（`ltIter_eq_ltSol p hp`）
  * M224F-4（LT-4）`iterComm` — 反復の可換性（M72F-5d）: f^{∘n}∘f =
    f∘f^{∘n}（`ltIter_comm p hp.1`）
  * M224F-5 `formalGroupProgramData` / `formalGroupProgram_exists` —
    witness 本体と存在定理

  **意義**: Lubin–Tate 形式群論の柱C部分——(i) 形式群べき級数 F の
  構成的存在と境界条件下での一意性、(ii) その自己準同型環が ℤ_p と
  環同型であること、(iii) LT 多項式の反復が同じ一意解族 [π^n] に
  収束し、かつ f 自身と可換であること——を、共通パラメータ
  (p : Nat) (hp : IsPrime p) (a : (Zp p).carrier) の下で一つの型
  `FormalGroupProgramData` に固定し、new proof を一切追加せずに
  4 モジュール（M49F・M42F・M208F・M72F）の合流点として閉じることを
  機械的に証明する。

  **正直な限定**: (1) `lt` フィールドはパラメータ `a` ごとの
  Lubin–Tate 補題であり、`endRing`（ℤ_p ≅ End(F)）・`iterEqSol` /
  `iterComm`（[p^n] 系列）とは独立に成立する主張で、本 capstone は
  これらを同一パラメータ組の下で**並べて**束ねるのみ——`lt` の解 F が
  `endRing` の像の中で `a` に対応する元であることを結ぶ追加の等式は
  本モジュールには含まない（`oToEnd p hp |>.map a = ⟨ltSol p hp a, ...⟩`
  という定義上の対応は `FormalEndRing.lean` 側にあるが、ここでは
  re-export しない）。(2) 柱C の広いプログラム（形式群の点群
  `FormalGroupPoints*.lean`・O-加群構造 `FormalGroupOModule.lean`・
  合成の結合則 `LTIterate.lean` 前半の一般論等）はここでは束ねない
  ——本 capstone は「Lubin–Tate 本体 + End(F) 環化 + 反復の同定」という
  一貫した核のみをスコープとする。(3) `FormalEndRingData` の
  `incl_inj` / `incl_surj` は `oToEnd_injective` / `oToEnd_surjective`
  の直接引用であり、本モジュールでの新規証明はない。

  全て選択公理不使用（型継承除く）。サブエージェント並行部品。
-/
import IUT.LTIterate
import IUT.FormalEndRing

namespace IUT

/-! ## M224F-5: 柱C Lubin–Tate プログラムの総括データ -/

/-- **Lubin–Tate プログラムデータ（M224F-5）**: 素数 p・
    `hp : IsPrime p`・ℤ_p 元 a に対し、Lubin–Tate 補題（存在＋一意性）・
    End(F) 環パッケージ（ℤ_p ≅ End(F)）・LT 多項式反復の [p^n] 系列
    への同定・反復の可換性の 4 段を一つの証明記録に束ねる。「柱C
    Lubin–Tate プログラム: 存在一意性 → 環同型 → 反復の同定・可換性」
    の単一証人。 -/
structure FormalGroupProgramData (p : Nat) (hp : IsPrime p)
    (a : (Zp p).carrier) where
  /-- LT-1（M49F/M42F）: Lubin–Tate 補題——F(0) = 0・F(1) = a・
      F∘f = π·F + F^p を満たす F が存在し、同条件を満たす任意の F' は
      この F（= ltSol p hp a）に一致する。 -/
  lt : ∃ F : PS (zpRing p),
    (F 0 = (zpRing p).zero ∧ F 1 = a ∧
      psComp (zpRing p) F (ltPoly p)
        = (psRing (zpRing p)).add
            (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F)
            (psPow (zpRing p) F p)) ∧
    ∀ F' : PS (zpRing p),
      F' 0 = (zpRing p).zero → F' 1 = a →
      psComp (zpRing p) F' (ltPoly p)
        = (psRing (zpRing p)).add
            (psSmul (zpRing p) ((toZp p).map ((p : Nat) : Int)) F')
            (psPow (zpRing p) F' p) →
      F' = ltSol p hp a
  /-- LT-2（M208F）: End(F) 環パッケージ——End(F) を一個の `CRing`、
      ι : ℤ_p → End(F) を一個の `RingHom` とし、ι が単射かつ全射
      （環同型 ℤ_p ≅ End(F)）であることを束ねたレコード。 -/
  endRing : FormalEndRingData p hp
  /-- LT-3（M72F-7）: [p^n] 系列の同定——f^{∘n} = ltSol(π^n)（LT 多項式
      の n 回反復は、Lubin–Tate 補題の π^n に対する一意解に一致）。 -/
  iterEqSol : ∀ n, ltIter p n
    = ltSol p hp (rpow (zpRing p) ((toZp p).map ((p : Nat) : Int)) n)
  /-- LT-4（M72F-5d）: 反復の可換性——f^{∘n}∘f = f∘f^{∘n}。 -/
  iterComm : ∀ n, psComp (zpRing p) (ltIter p n) (ltPoly p)
    = psComp (zpRing p) (ltPoly p) (ltIter p n)

/-- **証人（M224F-5）**: 本モジュールが柱C Lubin–Tate プログラムの
    4 段（M49F/M42F・M208F・M72F-7・M72F-5d）を実際に一つのデータへ
    束ねる。全フィールドは既存 def/定理の代入のみ（新規証明ゼロ）。 -/
def formalGroupProgramData (p : Nat) (hp : IsPrime p)
    (a : (Zp p).carrier) : FormalGroupProgramData p hp a where
  lt := lubin_tate p hp a
  endRing := formalEndRingData p hp
  iterEqSol := ltIter_eq_ltSol p hp
  iterComm := fun n => ltIter_comm p hp.1 n

/-- **定理 (M224F-5): Lubin–Tate プログラムデータの存在** — 柱C
    Lubin–Tate プログラム: 存在＋一意性 → End(F) 環同型 → 反復の
    [p^n] 系列への同定・可換性の全段が無矛盾に存在する（完成した
    柱C 部分プログラムの単一証明記録としての締めくくり）。 -/
theorem formalGroupProgram_exists (p : Nat) (hp : IsPrime p)
    (a : (Zp p).carrier) : Nonempty (FormalGroupProgramData p hp a) :=
  ⟨formalGroupProgramData p hp a⟩

end IUT
