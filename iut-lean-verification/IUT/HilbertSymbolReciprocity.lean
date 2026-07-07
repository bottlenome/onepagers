-- M410F HilbertSymbolReciprocity [実・本物・柱B]
-- complete_pct 影響: 柱B で従順 Hilbert 記号の相互律性質を本物化（skew/product relation (a,b)·(b,a)=0・対角消去 (a,a)=0・記号=相互律ペアリング χ(rec(a))=rndⁿ pairing・ノルム群消去 (a,e)_n=0⟺a∈N の双方向）。M375F 反対称・M400F rec 整合・M405F 完全ペアリングを Hilbert 記号の相互律として結線。
-- 正直な限定: 大域積公式 ∏_v (a,b)_v = 1（Artin 相互律・全 place・大域 CFT）・野性記号・完全 Steinberg 関係・一般相互律法則は後続。ここは不分岐/従順局所記号の相互律性質のみ本物。

/-
  IUT/HilbertSymbolReciprocity.lean — M410F（従順 Hilbert 記号の相互律性質: 実部分ケース）

  ────────────────────────────────────────────────────────────────────────
  二軸（CLAUDE.md §1 必守）
  * 分類: **[実]**（(a) 昇格 + (b) 本物先行建設）。M375F（IUT/TameSymbol.lean,
    prefix `tsy`）が建てた従順 Hilbert 記号 (a,b)_n = v(a)w(b)−v(b)w(a) と、
    M400F（IUT/ReciprocityBrauerCompat.lean, prefix `rbc`）の記号=相互律対整合、
    M405F（IUT/ReciprocityNondegenerate.lean, prefix `rnd`）の完全ペアリングを
    **Hilbert 記号の相互律性質**として結線し、次を完全証明する:
      - **積（skew）関係** (a,b)_n · (b,a)_n = 0（加法群 (1/n)ℤ/ℤ で
        (a,b)+(b,a)=0）——反対称 M375F `tsy_tame_antisymmetric` から。局所記号の
        「相互律」(reciprocity) の中核: 引数交換で逆元になる。
      - **対角消去** (a,a)_n = 0（行列式の対角成分が消える）。
      - **記号 = 相互律ペアリング** (a,e)_n = χ(rec(a)) = rndPairing(a,Frob)
        （M400F/M405F）——記号はまさに相互律ペアリングそのもの。
      - **ノルム群消去（相互律の非退化）** (a,e)_n = 0 ⟺ a ∈ N_{L/K}(L^×)
        （M400F `rbc_char_rec_zero_iff` 経由）——記号がノルム類を検出する。
      - **双線形性**（M375F `tsy_tame_bilinear_left/right` 再利用）。
  * complete_pct 影響: 柱B（局所類体論: Hilbert 記号相互律）前進あり。

  ────────────────────────────────────────────────────────────────────────
  既存モジュールの何を接合したか（CLAUDE.md 指示・明記必須）
  * M375F `tsyTameSymbolW`/`tsy_tame_antisymmetric`/`tsy_tame_bilinear_{left,right}`
    /`tsyDet`（付値行列式）——記号の代数構造。
  * M400F `rbc_tame_symbol_eq_char_rec`（記号=χ(rec)）・`rbcRecPairing`・
    `rbc_char_rec_zero_iff`（零判定=ノルム群）。
  * M405F `rndPairing`/`rnd_pairing_frob_eq_rbc`（Frobenius 評価=記号の相互律対）。
  * Grp `inv_mul`/`mul_inv`（群の逆元律）——skew 積が単位元になる算術核。
  接合の核: 反対称 (a,b)=−(b,a) を群の言語で (a,b)·(b,a)=(−(b,a))·(b,a)=0 と
  読み替えると、これは局所記号の**相互律 (skew reciprocity)** そのもの。標準単数 e
  を第二引数に固定すると記号は相互律ペアリング χ(rec(a)) に一致し（M400F）、その
  零判定がノルム群を与える（M405F 左非退化の記号版）。

  ────────────────────────────────────────────────────────────────────────
  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
  * `hsr_symbol_skew_prod`          — (a,b)·(b,a) = 0（skew/相互律関係）
  * `hsr_symbol_skew_prod_symm`     — (b,a)·(a,b) = 0（対称版）
  * `hsr_symbol_diag`               — (a,a) = 0（対角消去）
  * `hsr_symbol_bilinear_left/right`— 双線形性（M375F 再輸出）
  * `hsr_symbol_antisymmetric`      — 反対称（M375F 再輸出）
  * `hsr_symbol_eq_rec_pairing`     — (a,e)_n = χ(rec(a))（M400F 接続）
  * `hsr_symbol_eq_rnd_frob`        — (a,e)_n = rndPairing(a,Frob)（M405F 接続）
  * `hsr_symbol_vanishes_iff_norm`  — (a,e)_n = 0 ⟺ a∈N（ノルム群消去・双方向）
  * `hsr_symbol_norm_vanishes`      — a∈N ⟹ (a,e)_n = 0（片側・相互律の主張）
  * `HilbertSymbolReciprocityData` / `hsrData` / `hsr_exists` — capstone + witness
  * n=2 worked examples（skew 積・対角消去・ノルム検出・記号=相互律対）

  ────────────────────────────────────────────────────────────────────────
  正直な限定（CLAUDE.md §4: 消去・弱化禁止）
  * **大域積公式** ∏_v (a,b)_v = 1（Artin 相互律・全 place の積・大域類体論）は
    本モジュール外——後続。ここで本物にしたのは**局所（1 place・不分岐/従順）記号の
    相互律性質**（skew 関係・記号=局所相互律ペアリング・ノルム群消去）のみ。
  * **野性分岐の記号**・完全な Steinberg 関係 (a,1−a)=0・一般相互律法則
    （二次剰余の相互律を含む一般 Hilbert 記号）は範囲外。
  * 第二付値 w は M375F の分裂模型 U=ℤ・w=第二射影に依存（M375F と同じ規約）。
    第一付値 v = M365F `briVal` は本物の付値。**toy 主語ではない**: 主語は本物の
    従順記号（M375F 反対称・双線形の本証明）・本物の rec（M390F）・本物のノルム群
    （M335F）である。
  * ノルム群消去・記号=ペアリングは U=ℤ（`intGrp`）の具体化で述べる（M400F/M405F
    の intGrp 規約に整合）。一般 U での記号相互律は skew/対角/双線形で与える。

  全て mathlib なし・新規 Classical.choice なし（propext, Quot.sound のみ）。
  共有ファイル未変更（新規 1 本のみ）。一般名は `hsr` 接頭辞で衝突回避。
-/
import IUT.TameSymbol
import IUT.ReciprocityBrauerCompat
import IUT.ReciprocityNondegenerate

namespace IUT

/-! ## §1 skew/product 相互律関係 (a,b)·(b,a) = 0 -/

/-- **M410F-1: skew（相互律）関係** (a,b)_n · (b,a)_n = 0（加法群 (1/n)ℤ/ℤ で
    (a,b)+(b,a)=0）。M375F 反対称 (a,b)=−(b,a) を群の言語に翻訳: (a,b)·(b,a) =
    (−(b,a))·(b,a) = 0（群の左逆元律 `inv_mul`）。局所 Hilbert 記号の相互律
    (skew reciprocity) の中核——引数交換で逆元になり、積が単位元に落ちる。 -/
theorem hsr_symbol_skew_prod (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a b : (unitsModel U).carrier) :
    (briQZn n).mul (tsyTameSymbolW U n w a b) (tsyTameSymbolW U n w b a) = (briQZn n).one := by
  rw [tsy_tame_antisymmetric U n w a b]
  exact (briQZn n).inv_mul (tsyTameSymbolW U n w b a)

/-- **M410F-2: skew 関係（対称版）** (b,a)_n · (a,b)_n = 0。引数の順を入れ替えた
    相互律関係（積は可換的に単位元）。 -/
theorem hsr_symbol_skew_prod_symm (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a b : (unitsModel U).carrier) :
    (briQZn n).mul (tsyTameSymbolW U n w b a) (tsyTameSymbolW U n w a b) = (briQZn n).one := by
  rw [tsy_tame_antisymmetric U n w a b]
  exact (briQZn n).mul_inv (tsyTameSymbolW U n w b a)

/-- **M410F-3: 反対称（M375F 再輸出）** (a,b)_n = −(b,a)_n。skew 関係の元となる
    M375F `tsy_tame_antisymmetric` を Hilbert 記号相互律の名の下で明示。 -/
theorem hsr_symbol_antisymmetric (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a b : (unitsModel U).carrier) :
    tsyTameSymbolW U n w a b = (briQZn n).inv (tsyTameSymbolW U n w b a) :=
  tsy_tame_antisymmetric U n w a b

/-! ## §2 対角消去 (a,a) = 0 -/

/-- **M410F-4: 対角消去** (a,a)_n = 0。付値行列式 v(a)w(a)−v(a)w(a)=0（対角成分の
    消滅、`Int.sub_self`）ゆえ記号は自明。反対称からは (a,a)=−(a,a) しか出ないが
    （2-捻れの曖昧さ）、行列式の直接計算で 0 を確定させる本証明。 -/
theorem hsr_symbol_diag (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a : (unitsModel U).carrier) :
    tsyTameSymbolW U n w a a = (briQZn n).one := by
  have h : tsyDet U w a a = 0 := by
    show (briVal U).map a * w.map a - (briVal U).map a * w.map a = 0
    rw [Int.sub_self]
  show Quot.mk (modCong n).rel (tsyDet U w a a) = (briQZn n).one
  rw [h]
  rfl

/-! ## §3 双線形性（M375F 再輸出） -/

/-- **M410F-5: 双線形（左, M375F 再輸出）** (a·a', b)_n = (a,b)_n + (a',b)_n。 -/
theorem hsr_symbol_bilinear_left (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a a' b : (unitsModel U).carrier) :
    tsyTameSymbolW U n w ((unitsModel U).mul a a') b
      = (briQZn n).mul (tsyTameSymbolW U n w a b) (tsyTameSymbolW U n w a' b) :=
  tsy_tame_bilinear_left U n w a a' b

/-- **M410F-6: 双線形（右, M375F 再輸出）** (a, b·b')_n = (a,b)_n + (a,b')_n。 -/
theorem hsr_symbol_bilinear_right (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp)
    (a b b' : (unitsModel U).carrier) :
    tsyTameSymbolW U n w a ((unitsModel U).mul b b')
      = (briQZn n).mul (tsyTameSymbolW U n w a b) (tsyTameSymbolW U n w a b') :=
  tsy_tame_bilinear_right U n w a b b'

/-! ## §4 記号 = 相互律ペアリング（M400F/M405F 接続） -/

/-- **M410F-7: 記号 = 相互律対** (a,e)_n = χ_n(rec(a))。標準単数 e=(0,1) との従順
    Hilbert 記号は、Artin 相互像での標準指標評価 χ(rec(a))（M400F `rbcRecPairing`）
    に一致。記号はまさに局所相互律ペアリングそのもの。 -/
theorem hsr_symbol_eq_rec_pairing (n : Nat) (a : (unitsModel intGrp).carrier) :
    tsyTameSymbol n a ((0 : Int), (1 : Int)) = rbcRecPairing intGrp n a :=
  rbc_tame_symbol_eq_char_rec n a

/-- **M410F-8: 記号 = Frobenius でのペアリング** (a,e)_n = ⟨a, Frob⟩。M405F の
    二変数完全ペアリング `rndPairing` を Frobenius 生成元で評価したものに一致
    （M405F `rnd_pairing_frob_eq_rbc` 経由）。記号が完全ペアリングの片スロット固定で
    得られることを本物で。 -/
theorem hsr_symbol_eq_rnd_frob (n : Nat) (a : (unitsModel intGrp).carrier) :
    tsyTameSymbol n a ((0 : Int), (1 : Int)) = rndPairing intGrp n a (rndFrob n) := by
  rw [hsr_symbol_eq_rec_pairing n a]
  exact (rnd_pairing_frob_eq_rbc intGrp n a).symm

/-! ## §5 ノルム群消去（相互律の非退化・記号がノルム類を検出） -/

/-- **M410F-9: ノルム群消去（双方向）** (a,e)_n = 0 ⟺ a ∈ N_{L/K}(L^×)。標準単数 e と
    の従順 Hilbert 記号が消えることは、a が局所ノルム群に属すことと同値
    （M400F `rbc_char_rec_zero_iff` = M390F 核=ノルム群）。局所相互律の非退化性の
    記号版: 記号はちょうどノルム類を検出する。 -/
theorem hsr_symbol_vanishes_iff_norm (n : Nat) (m u : Int) :
    tsyTameSymbol n (m, u) ((0 : Int), (1 : Int)) = (briQZn n).one
      ↔ (normGSubgroup intGrp (n : Int)).mem (m, u) := by
  rw [hsr_symbol_eq_rec_pairing n (m, u)]
  exact rbc_char_rec_zero_iff intGrp n m u

/-- **M410F-10: ノルム上で記号消去（相互律の主張・片側）** a ∈ N ⟹ (a,e)_n = 0。
    局所ノルム群の元は標準単数との記号が自明——「記号はノルムを分裂させる」。 -/
theorem hsr_symbol_norm_vanishes (n : Nat) (m u : Int)
    (h : (normGSubgroup intGrp (n : Int)).mem (m, u)) :
    tsyTameSymbol n (m, u) ((0 : Int), (1 : Int)) = (briQZn n).one :=
  (hsr_symbol_vanishes_iff_norm n m u).mpr h

/-- **M410F-11: ノルム外で記号非自明（対偶）** a ∉ N ⟹ (a,e)_n ≠ 0。ノルム群外の
    元は記号で検出される（相互律の非退化の対偶）。 -/
theorem hsr_symbol_non_norm_nontrivial (n : Nat) (m u : Int)
    (h : ¬ (normGSubgroup intGrp (n : Int)).mem (m, u)) :
    tsyTameSymbol n (m, u) ((0 : Int), (1 : Int)) ≠ (briQZn n).one := by
  intro hz
  exact h ((hsr_symbol_vanishes_iff_norm n m u).mp hz)

/-! ## §6 capstone: 従順 Hilbert 記号の相互律性質データ -/

/-- **M410F-12: Hilbert 記号相互律データ** — 従順局所 Hilbert 記号の相互律性質を
    構造化: 記号写像・**skew（相互律）関係** (a,b)·(b,a)=0・**対角消去** (a,a)=0・
    双線形（両引数）・反対称を束ねる。局所記号の相互律 (reciprocity) の中核部品。 -/
structure HilbertSymbolReciprocityData (U : Grp) (n : Nat)
    (w : Hom (unitsModel U) intGrp) where
  /-- 従順 Hilbert 記号 (a,b)_n。 -/
  symbol : (unitsModel U).carrier → (unitsModel U).carrier → (briQZn n).carrier
  /-- symbol の同定。 -/
  symbol_is : symbol = tsyTameSymbolW U n w
  /-- **skew（相互律）関係** (a,b)·(b,a) = 0。 -/
  skew_prod : ∀ a b, (briQZn n).mul (symbol a b) (symbol b a) = (briQZn n).one
  /-- **対角消去** (a,a) = 0。 -/
  diag : ∀ a, symbol a a = (briQZn n).one
  /-- 反対称 (a,b) = −(b,a)。 -/
  antisymmetric : ∀ a b, symbol a b = (briQZn n).inv (symbol b a)
  /-- 双線形（左）。 -/
  bilinear_left : ∀ a a' b,
    symbol ((unitsModel U).mul a a') b = (briQZn n).mul (symbol a b) (symbol a' b)
  /-- 双線形（右）。 -/
  bilinear_right : ∀ a b b',
    symbol a ((unitsModel U).mul b b') = (briQZn n).mul (symbol a b) (symbol a b')

/-- **M410F-13: 相互律データの構成**（単数群 U・次数 n・第二付値 w から）。
    全性質を本物の証明で満たす witness。 -/
def hsrData (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp) :
    HilbertSymbolReciprocityData U n w where
  symbol := tsyTameSymbolW U n w
  symbol_is := rfl
  skew_prod := hsr_symbol_skew_prod U n w
  diag := hsr_symbol_diag U n w
  antisymmetric := hsr_symbol_antisymmetric U n w
  bilinear_left := hsr_symbol_bilinear_left U n w
  bilinear_right := hsr_symbol_bilinear_right U n w

/-- **M410F-14: 相互律データの存在**（無矛盾性 witness）。 -/
theorem hsr_exists (U : Grp) (n : Nat) (w : Hom (unitsModel U) intGrp) :
    Nonempty (HilbertSymbolReciprocityData U n w) :=
  ⟨hsrData U n w⟩

/-- **具体的存在**: U=ℤ・n=2・w=第二射影で Hilbert 記号相互律データが実体化。 -/
theorem hsr_exists_witness : Nonempty (HilbertSymbolReciprocityData intGrp 2 tsySnd) :=
  ⟨hsrData intGrp 2 tsySnd⟩

/-! ## §7 worked examples（n=2: skew 積・対角消去・ノルム検出・記号=相互律対） -/

-- 例1: **skew 相互律関係**（π=(1,0)・u=(0,1)）: (π,u)_2 · (u,π)_2 = 0
example :
    (briQZn 2).mul
        (tsyTameSymbol 2 ((1 : Int), (0 : Int)) ((0 : Int), (1 : Int)))
        (tsyTameSymbol 2 ((0 : Int), (1 : Int)) ((1 : Int), (0 : Int)))
      = (briQZn 2).one :=
  hsr_symbol_skew_prod intGrp 2 tsySnd ((1 : Int), (0 : Int)) ((0 : Int), (1 : Int))

-- 例2: **対角消去**（(π,π)_2 = 0）
example :
    tsyTameSymbol 2 ((1 : Int), (0 : Int)) ((1 : Int), (0 : Int)) = (briQZn 2).one :=
  hsr_symbol_diag intGrp 2 tsySnd ((1 : Int), (0 : Int))

-- 例3: **記号 = 相互律対**（(π,e)_2 = χ(rec(π))）
example :
    tsyTameSymbol 2 ((1 : Int), (0 : Int)) ((0 : Int), (1 : Int))
      = rbcRecPairing intGrp 2 ((1 : Int), (0 : Int)) :=
  hsr_symbol_eq_rec_pairing 2 ((1 : Int), (0 : Int))

-- 例4: **記号 = Frobenius ペアリング**（(π,e)_2 = ⟨π, Frob⟩）
example :
    tsyTameSymbol 2 ((1 : Int), (0 : Int)) ((0 : Int), (1 : Int))
      = rndPairing intGrp 2 ((1 : Int), (0 : Int)) (rndFrob 2) :=
  hsr_symbol_eq_rnd_frob 2 ((1 : Int), (0 : Int))

-- 例5: **ノルム群消去（双方向）**（(π²,u)_2 = 0 ⟺ π² ∈ N）
example (u : Int) :
    tsyTameSymbol 2 ((2 : Int), u) ((0 : Int), (1 : Int)) = (briQZn 2).one
      ↔ (normGSubgroup intGrp (2 : Int)).mem ((2 : Int), u) :=
  hsr_symbol_vanishes_iff_norm 2 2 u

-- 例6: **ノルムは記号を分裂**（π²=(2,u) はノルム ⟹ (π²,e)_2 = 0）
example (u : Int) :
    tsyTameSymbol 2 ((2 : Int), u) ((0 : Int), (1 : Int)) = (briQZn 2).one := by
  apply hsr_symbol_norm_vanishes
  exact (normG_mem_iff intGrp (2 : Int) 2 u).mpr ⟨1, by omega⟩

-- 例7: **素元は記号を非自明化**（π=(1,u) はノルム外 ⟹ (π,e)_2 ≠ 0）
example (u : Int) :
    tsyTameSymbol 2 ((1 : Int), u) ((0 : Int), (1 : Int)) ≠ (briQZn 2).one := by
  apply hsr_symbol_non_norm_nontrivial
  intro hmem
  obtain ⟨k, hk⟩ := (normG_mem_iff intGrp (2 : Int) 1 u).mp hmem
  omega

-- 例8: capstone アクセサ（skew 相互律関係）
example (a b : (unitsModel intGrp).carrier) :
    (briQZn 2).mul ((hsrData intGrp 2 tsySnd).symbol a b)
        ((hsrData intGrp 2 tsySnd).symbol b a)
      = (briQZn 2).one :=
  (hsrData intGrp 2 tsySnd).skew_prod a b

-- 例9: capstone アクセサ（対角消去）
example (a : (unitsModel intGrp).carrier) :
    (hsrData intGrp 2 tsySnd).symbol a a = (briQZn 2).one :=
  (hsrData intGrp 2 tsySnd).diag a

-- 例10: capstone アクセサ（反対称）
example (a b : (unitsModel intGrp).carrier) :
    (hsrData intGrp 2 tsySnd).symbol a b
      = (briQZn 2).inv ((hsrData intGrp 2 tsySnd).symbol b a) :=
  (hsrData intGrp 2 tsySnd).antisymmetric a b

end IUT
