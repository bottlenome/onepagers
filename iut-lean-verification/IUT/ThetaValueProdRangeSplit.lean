/-
  IUT/ThetaValueProdRangeSplit.lean — M263F: テータ値多ラベル積の連続ラベル範囲の
  オフセット分割恒等式（offset range split identity・柱E E-1 並行部品）

  柱E 残課題 E-1（#39）の「値の代数構造」切片の続き。M242F
  （ThetaValueProdLaws.lean）は連続ラベル範囲 labelUpto n = [0,1,…,n−1] に
  沿った多ラベル積の指数和が下方平方和 sqSumBelow n / M93 の平方和 ssq n に
  一致すること（thetaExpSum_labelUpto / thetaExpSum_labelUpto_ssq）と、その
  積本体が平方和単項式 u^{ssq n} に一致すること（thetaValProd_labelUpto）を
  確立していた。ただし M242F の連続ラベル範囲は常に **0 起点**
  （[0,1,…,n−1]）に限られており、範囲を先頭からある位置 m で**分割**した
  ときに、後半部分が「0 起点ではなくオフセット m 起点の連続範囲
  [m, m+1, …, m+n−1]」として現れ、多ラベル積・指数和がこの分割に沿って
  連接則へちょうど分解できる、という接続は与えていなかった（M253F/M258F は
  隣接転置・ブロック入替・巡回置換という「並べ替え」側の一般化であり、この
  「範囲の起点分割」側は未着手だった）。

  本モジュールは M242F の labelUpto / thetaExpSum_append / thetaValProd_append
  を土台に、

    (A) **オフセット連続範囲 labelRange（新規）**: 起点 m から長さ n の連続
        ラベル列 [m, m+1, …, m+n−1] を、labelUpto と同じ「末尾追加」の
        構成で定義する（labelRange m 0 = []、labelRange m (n+1)
        = labelRange m n ++ [m+n]）;
    (B) **0 起点との整合（新規）**: labelRange 0 n = labelUpto n（起点 0 の
        オフセット範囲がもとの labelUpto に一致すること、Nat.zero_add に
        よる）;
    (C) **範囲のオフセット分割恒等式（新規・本丸）**: 長さ m+n の連続範囲は、
        長さ m の 0 起点部分と長さ n のオフセット m 部分へちょうど連接
        分解できる labelUpto (m+n) = labelUpto m ++ labelRange m n（n に
        関する帰納、List.append_assoc で結合を組み替える）;
    (D) **指数和・多ラベル積への分割接続（新規）**: (C) を M242F の連接
        加法性・連接則（thetaExpSum_append / thetaValProd_append）へ通し、
        thetaExpSum (labelUpto (m+n))
          = thetaExpSum (labelUpto m) + thetaExpSum (labelRange m n)、
        thetaValProd R (labelUpto (m+n))
          = (thetaValProd R (labelUpto m))·(thetaValProd R (labelRange m n))
        —— 連続ラベル範囲の多ラベル積・総指数を「先頭 m 個」と「残り n 個
        （オフセット付き）」の積・和へ厳密に分割する部分和差の恒等式

    を機械検証し、M242F の 0 起点連続範囲を「起点分割」の観点から精緻化する。

  * M263F-1 `labelRange` — オフセット連続ラベル範囲（新規）
  * M263F-2 `labelRange_zero` — 0 起点との整合（新規）
  * M263F-3 `labelUpto_append_labelRange` — 範囲のオフセット分割恒等式
    （新規・本丸）
  * M263F-4 `thetaExpSum_labelUpto_split` / `thetaValProd_labelUpto_split` —
    指数和・多ラベル積への分割接続（新規）
  * M263F-5 総括レコード `ThetaValueProdRangeSplitData` /
    `thetaValueProdRangeSplitData` / `thetaValueProdRangeSplit_exists` —
    capstone

  意義: M242F の連続ラベル範囲 labelUpto を「0 起点」という特殊な場合に
  限らず、任意の起点 m から始まるオフセット範囲 labelRange m n へ一般化し、
  0 起点の長い範囲がちょうど「先頭部分」と「オフセット付き残り部分」へ
  連接分解できることを機械検証する。これにより連続ラベル範囲に沿った
  多ラベル積・総指数の「部分和差」（先頭 m 個を除いた残りの寄与）を
  M242F の連接則のみから読み出せる。テータ値の連続ラベル積の範囲分割を
  代数化する E-1 の値代数側 witness。

  正直な限定（スライス A+B+C+D）: 扱うのはテータ値 q^{j²} が住む Laurent
  環単元群の**連続ラベル範囲 labelUpto の起点オフセット分割**のみ。ここで
  「オフセット範囲 labelRange m n」は [m, m+1, …, m+n−1] という**具体的な
  連続列**であり、任意の（連続でない）部分列の分割や、labelRange m n の
  指数和が M93 の平方和公式の**シフト版閉形式**（Σ_{k=0}^{n-1} (m+k)^2 の
  展開式）に一致することまでは本モジュールでは扱わない（それは別途二項
  展開が必要な計算で、ここでは連接則による構造的分割のみに留める）。
  テータ値がラベル上でなす**環準同型**や**ガロア同変な p 進テータ値**・
  **tempered π₁ の商としての実現**・**エタールテータ関数値そのものの
  構成**は M223F/M232F/M237F/M242F/M253F/M258F 同様 E-1 残として範囲外
  （本モジュールでは一切主張しない）。q の付値・q-展開の収束も扱わない。
  全て選択公理を証明本体で新規導入せず（M242F/M237F/M232F/M223F から継承、
  新規 Classical・新規 Classical.choice なし。商 laurentRing / laurentRel /
  Quot レベルの主張は Quot.sound を使う —— 商構成に内在、選択公理ではない。
  本モジュール自体の新規証明は List/Nat の帰納・書き換えのみで選択公理を
  一切用いない）。#print axioms により継承分のみであることを確認済み。
  サブエージェント並行部品。
-/
import IUT.ThetaValueProdLaws

namespace IUT

/-! ## M263F-1: オフセット連続ラベル範囲 -/

/-- **M263F-1: オフセット連続ラベル範囲 labelRange（新規）** — 起点 m から
    長さ n の連続ラベル列 [m, m+1, …, m+n−1]。M242F labelUpto と同じ
    「末尾追加」の構成で、起点をオフセット m へ一般化したもの。 -/
def labelRange (m : Nat) : Nat → List Int
  | 0 => []
  | n + 1 => labelRange m n ++ [((m + n : Nat) : Int)]

/-! ## M263F-2: 0 起点との整合 -/

/-- **定理 (M263F-2): 0 起点との整合（新規）** — オフセット範囲の起点を 0
    にすると M242F labelUpto に一致する labelRange 0 n = labelUpto n。
    n に関する帰納（succ 段は Nat.zero_add で 0+n=n を整える）。 -/
theorem labelRange_zero (n : Nat) : labelRange 0 n = labelUpto n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show labelRange 0 n ++ [((0 + n : Nat) : Int)] = labelUpto n ++ [(n : Int)]
    rw [ih, Nat.zero_add]

/-! ## M263F-3: 範囲のオフセット分割恒等式（本丸） -/

/-- **定理 (M263F-3): 範囲のオフセット分割恒等式（新規・本丸）** — 長さ m+n
    の 0 起点連続範囲は、長さ m の 0 起点部分と、長さ n のオフセット m 部分
    へちょうど連接分解できる: labelUpto (m + n)
      = labelUpto m ++ labelRange m n。n に関する帰納: 0 は末尾の空範囲の
    吸収（List.append_nil）、n+1 段は labelUpto (m+n) の末尾追加の定義
    段を帰納法の仮定で書き換えたのち List.append_assoc で結合を
    labelRange 側へ組み替える。 -/
theorem labelUpto_append_labelRange (m : Nat) :
    ∀ n : Nat, labelUpto (m + n) = labelUpto m ++ labelRange m n := by
  intro n
  induction n with
  | zero =>
    show labelUpto m = labelUpto m ++ []
    rw [List.append_nil]
  | succ n ih =>
    show labelUpto (m + n) ++ [((m + n : Nat) : Int)]
      = labelUpto m ++ (labelRange m n ++ [((m + n : Nat) : Int)])
    rw [ih, List.append_assoc]

/-! ## M263F-4: 指数和・多ラベル積への分割接続 -/

/-- **定理 (M263F-4a): 連続範囲の指数和のオフセット分割（新規）** — 長さ m+n
    の連続範囲の総指数は、先頭 m 個の総指数とオフセット m の残り n 個の
    総指数の和に等しい: thetaExpSum (labelUpto (m+n))
      = thetaExpSum (labelUpto m) + thetaExpSum (labelRange m n)。M263F-3
    （範囲のオフセット分割）と M242F thetaExpSum_append の合成。 -/
theorem thetaExpSum_labelUpto_split (m n : Nat) :
    thetaExpSum (labelUpto (m + n))
      = thetaExpSum (labelUpto m) + thetaExpSum (labelRange m n) := by
  rw [labelUpto_append_labelRange, thetaExpSum_append]

/-- **定理 (M263F-4b): 連続範囲の多ラベル積のオフセット分割（新規）** — 長さ
    m+n の連続範囲の多ラベル積は、先頭 m 個の積とオフセット m の残り n 個
    の積の積に等しい: thetaValProd R (labelUpto (m+n))
      = (thetaValProd R (labelUpto m))·(thetaValProd R (labelRange m n))。
    M263F-3 と M242F thetaValProd_append の合成。テータ値の連続ラベル積の
    「部分和差」（先頭 m 個を除いた残りの寄与）を連接則のみから読み出す。 -/
theorem thetaValProd_labelUpto_split (R : CRing) (m n : Nat) :
    thetaValProd R (labelUpto (m + n))
      = (laurentRing R).mul (thetaValProd R (labelUpto m))
          (thetaValProd R (labelRange m n)) := by
  rw [labelUpto_append_labelRange, thetaValProd_append]

/-! ## M263F-5: 総括レコード（連続範囲のオフセット分割） -/

/-- **M263F-5a: テータ値連続範囲オフセット分割データ** — M242F の連続
    ラベル範囲 labelUpto を起点 m のオフセット範囲 labelRange m n へ一般化
    し、0 起点との整合（labelRange 0 n = labelUpto n）と、長さ m+n の
    範囲が長さ m・n の二部分へ連接分解できること、およびその指数和・多
    ラベル積への分割接続を一括束ねる。M242F の連続ラベル範囲を「起点分割」
    の観点から精緻化した E-1 の値代数側 witness。 -/
structure ThetaValueProdRangeSplitData (R : CRing) where
  /-- オフセット連続ラベル範囲 m ↦ n ↦ [m,…,m+n−1]。 -/
  range : Nat → Nat → List Int
  /-- 多ラベル積写像 js ↦ ∏ q^{j²}。 -/
  prod : List Int → (laurentRing R).carrier
  /-- 指数簿記 js ↦ Σ j²。 -/
  expSum : List Int → Int
  /-- 0 起点との整合: range 0 n = labelUpto n。 -/
  range_zero : ∀ n : Nat, range 0 n = labelUpto n
  /-- 範囲のオフセット分割恒等式: labelUpto (m+n) = labelUpto m ++ range m n。 -/
  range_split : ∀ m n : Nat, labelUpto (m + n) = labelUpto m ++ range m n
  /-- 指数和のオフセット分割: Σ_{labelUpto (m+n)} = Σ_{labelUpto m} + Σ_{range m n}。 -/
  expSum_split : ∀ m n : Nat,
    expSum (labelUpto (m + n)) = expSum (labelUpto m) + expSum (range m n)
  /-- 多ラベル積のオフセット分割: ∏_{labelUpto (m+n)}
      = (∏_{labelUpto m})·(∏_{range m n})。 -/
  prod_split : ∀ m n : Nat,
    prod (labelUpto (m + n)) = (laurentRing R).mul (prod (labelUpto m)) (prod (range m n))

/-- **M263F-5b: witness 本体** — range := labelRange、prod := thetaValProd R、
    expSum := thetaExpSum として全フィールドを M263F-1〜4 で埋める。 -/
def thetaValueProdRangeSplitData (R : CRing) : ThetaValueProdRangeSplitData R where
  range := labelRange
  prod := thetaValProd R
  expSum := thetaExpSum
  range_zero := labelRange_zero
  range_split := labelUpto_append_labelRange
  expSum_split := thetaExpSum_labelUpto_split
  prod_split := thetaValProd_labelUpto_split R

/-- **定理 (M263F-5c): テータ値連続範囲オフセット分割データの存在
    （M263F 見出し）** — 任意の係数環 R に対し、テータ値 q^{j²} の連続
    ラベル範囲 labelUpto が任意の起点 m での分割 labelUpto (m+n)
      = labelUpto m ++ labelRange m n を持ち、その指数和・多ラベル積が
    この分割に沿って和・積へちょうど分解されることを束ねたデータが存在
    する。M242F の 0 起点連続範囲が「起点分割」の観点から精緻化される。 -/
theorem thetaValueProdRangeSplit_exists (R : CRing) :
    Nonempty (ThetaValueProdRangeSplitData R) :=
  ⟨thetaValueProdRangeSplitData R⟩

end IUT
