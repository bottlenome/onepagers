/-
  IUT/PolyDivModFn.lean — Wave1/F3（A1 0.80→0.85 設計 §1 F3）:
  多項式除法の Type 値関数 `pfdDivMod` と剰余の特徴付け

  ── 主要成果の分類: **[実]**（本物の先行建設。既存 `field_division_exists`
     の ∃ 定理の witness を choice-free な Type 値関数へ昇格）。

  **complete_pct 影響**: A1（実 ℚ[x]/(f)・全域 inv 付き実体）への承認済み足場。
  M268F-5 `field_division_exists` は商・剰余を N 帰納の各段で明示構成するが、
  結論が ∃（Prop）であるため witness を Type レベルで取り出せない。本層は
  **同じ帰納の witness をそのまま `def pfdDivMod`（Nat×PS の Type 値関数）に写経**し、
  剰余簡約 `pfdRed` を正規形担体（{g // deg g < m}）の乗法・inv の土台にする。
  Bezout/Euclid（F4）と NF 環（F5）の入力。complete_pct は本ファイル単体では
  未前進（A1 は F5/F6 完了後の独立再監査で確定）。complete_pct 未設定。

  本物性: `pfdDivMod` は `field_division_exists` の証明本体の各段 witness を
  名前付き def に転記したもので、**新規 Classical.choice を導入しない**
  （代表・上界は引数 N・g m として与えられる）。`pfdDivMod_spec` は M268F-5 と
  同一命題を同一帰納で（今度は関数の出力について）証明する。剰余の特徴付け
  `pfdRed_char` は M268F-7 の剰余一意性（`field_division_unique`）経由で
  「w ≡ v (mod g) かつ deg v < m ⟹ pfdRed w = v」を出す。

  正直な限定:
   - 多項式は有限台の係数列 PS = ℕ→ℚ として扱い、次数上界は明示パラメータ。
   - 対象体は実 ℚ（ratRing・qInv・ratIUTField.mul_inv_cancel）に固定。
     一般 Field268 への一般化は写経の反復で可能だが本層では ℚ 固定。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク不使用。
  サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyFieldDivision
import IUT.Field

namespace IUT

/-! ## F3-1: 除法関数（M268F-5 の witness をそのまま def に） -/

/-- **F3-1: 体上多項式除法の Type 値関数** — g（先頭係数 g m）で w を割る商・剰余の
    対を、次数超過分 N の Nat 構造再帰で明示構成する。`field_division_exists`
    （M268F-5）の証明本体の各段 witness をそのまま関数化したもの（choice-free）:
    N=0 は商 0・剰余 w、N+1 は頂点係数 c = w_{N+m}·(g m)⁻¹ で頂点を消し、
    残りを再帰、商に c·Y^N を積み上げる。 -/
def pfdDivMod (g : PS ratRing) (m : Nat) : Nat → PS ratRing → PS ratRing × PS ratRing
  | 0, w => (psZero ratRing, w)
  | N + 1, w =>
      let c := ratRing.mul (w (N + m)) (qInv (g m))
      let w' := psAdd ratRing w (psNeg ratRing (psMul ratRing (psSingle ratRing c N) g))
      let qr := pfdDivMod g m N w'
      (psAdd ratRing qr.1 (psSingle ratRing c N), qr.2)

/-! ## F3-2: 仕様（M268F-5 と同一命題・同一帰納で・関数の出力について） -/

/-- **F3-2: 除法関数の仕様** — g（m+1 有界・先頭係数 ≠ 0）で w（N+m 有界）を
    割ると、商 `(pfdDivMod g m N w).1` は N+1 有界、剰余 `.2` は m 有界
    （deg < deg g）、かつ **w = 商·g + 剰余**。M268F-5 と同一の N 帰納を、
    関数 `pfdDivMod` の実際の出力について展開して証明する。 -/
theorem pfdDivMod_spec (g : PS ratRing) (m : Nat)
    (hg : IsPolyBounded ratRing g (m + 1)) (hgl : g m ≠ ratRing.zero) :
    ∀ (N : Nat) (w : PS ratRing), IsPolyBounded ratRing w (N + m) →
      IsPolyBounded ratRing (pfdDivMod g m N w).1 (N + 1) ∧
      IsPolyBounded ratRing (pfdDivMod g m N w).2 m ∧
      ∀ j, w j = psAdd ratRing
        (psMul ratRing (pfdDivMod g m N w).1 g) (pfdDivMod g m N w).2 j := by
  intro N
  induction N with
  | zero =>
    intro w hw
    refine ⟨?_, ?_, ?_⟩
    · intro i _
      show psZero ratRing i = ratRing.zero
      rfl
    · intro i hi
      show w i = ratRing.zero
      exact hw i (by omega)
    · intro j
      show w j = ratRing.add (psMul ratRing (psZero ratRing) g j) (w j)
      have hz : psMul ratRing (psZero ratRing) g j = ratRing.zero := by
        show rsum ratRing (fun i => ratRing.mul (psZero ratRing i) (g (j - i))) (j + 1)
          = ratRing.zero
        have hc : rsum ratRing (fun i => ratRing.mul (psZero ratRing i) (g (j - i))) (j + 1)
            = rsum ratRing (fun _ => ratRing.zero) (j + 1) :=
          rsum_congr ratRing (j + 1) (fun i _ => CRing.zero_mul ratRing _)
        rw [hc]
        exact rsum_const_zero ratRing (j + 1)
      rw [hz, ratRing.zero_add]
  | succ N ih =>
    intro w hw
    have hw' : IsPolyBounded ratRing w (N + m + 1) := fun i hi => hw i (by omega)
    have hsub : IsPolyBounded ratRing
        (psAdd ratRing w (psNeg ratRing (psMul ratRing
          (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g))) (N + m) :=
      sub_top_bounded268 ratRing qInv ratIUTField.mul_inv_cancel g m hg hgl w N hw'
    obtain ⟨ihq, ihr, iheq⟩ := ih _ hsub
    refine ⟨?_, ?_, ?_⟩
    · -- 商の上界 (N+1)+1
      intro i hi
      show ratRing.add
          ((pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
            (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1 i)
          (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N i) = ratRing.zero
      rw [ihq i (by omega),
        show psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N i = ratRing.zero
          from if_neg (by omega),
        ratRing.zero_add]
    · -- 剰余の上界 m
      show IsPolyBounded ratRing
        (pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
          (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).2 m
      exact ihr
    · -- w = 商·g + 剰余
      intro j
      show w j = ratRing.add
        (psMul ratRing (psAdd ratRing
          (pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
            (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1
          (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N)) g j)
        ((pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
          (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).2 j)
      have h1 : ratRing.add (w j)
          (ratRing.neg (psMul ratRing
            (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g j))
          = ratRing.add
            (psMul ratRing
              (pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1 g j)
            ((pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
              (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).2 j) :=
        iheq j
      have hdist : psMul ratRing (psAdd ratRing
          (pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
            (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1
          (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N)) g j
          = ratRing.add
            (psMul ratRing
              (pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1 g j)
            (psMul ratRing
              (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g j) := by
        show rsum ratRing (fun i => ratRing.mul
            (ratRing.add
              ((pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1 i)
              (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N i))
            (g (j - i))) (j + 1)
          = ratRing.add
            (rsum ratRing (fun i => ratRing.mul
              ((pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1 i)
              (g (j - i))) (j + 1))
            (rsum ratRing (fun i => ratRing.mul
              (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N i)
              (g (j - i))) (j + 1))
        rw [← rsum_add ratRing _ _ (j + 1)]
        exact rsum_congr ratRing (j + 1) (fun i _ =>
          CRing.right_distrib ratRing
            ((pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
              (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1 i)
            (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N i) (g (j - i)))
      calc w j
          = ratRing.add (ratRing.add (w j)
              (ratRing.neg (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g j)))
              (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g j) := by
            rw [ratRing.add_assoc, ratRing.neg_add, CRing.add_zero ratRing]
        _ = ratRing.add (ratRing.add
              (psMul ratRing
                (pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                  (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1 g j)
              ((pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).2 j))
              (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g j) := by
            rw [h1]
        _ = ratRing.add (ratRing.add
              (psMul ratRing
                (pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                  (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1 g j)
              (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g j))
              ((pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).2 j) := by
            rw [ratRing.add_assoc, ratRing.add_comm
              ((pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).2 j)
              (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g j),
              ← ratRing.add_assoc]
        _ = ratRing.add
              (psMul ratRing (psAdd ratRing
                (pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                  (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).1
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N)) g j)
              ((pfdDivMod g m N (psAdd ratRing w (psNeg ratRing (psMul ratRing
                (psSingle ratRing (ratRing.mul (w (N + m)) (qInv (g m))) N) g)))).2 j) := by
            rw [hdist]

/-! ## F3-3: 剰余簡約関数と特徴付け -/

/-- **F3-3a: 剰余（正規形への簡約）** — w を g で割った剰余（deg < m）。
    正規形担体上の乗法・inv の土台。 -/
def pfdRed (g : PS ratRing) (m N : Nat) (w : PS ratRing) : PS ratRing :=
  (pfdDivMod g m N w).2

/-- **F3-3b: 剰余は m 有界（deg < deg g）** — 仕様の第2成分。 -/
theorem pfdRed_bound (g : PS ratRing) (m : Nat)
    (hg : IsPolyBounded ratRing g (m + 1)) (hgl : g m ≠ ratRing.zero)
    (N : Nat) (w : PS ratRing) (hw : IsPolyBounded ratRing w (N + m)) :
    IsPolyBounded ratRing (pfdRed g m N w) m :=
  (pfdDivMod_spec g m hg hgl N w hw).2.1

/-- **F3-3c: 剰余の特徴付け（NF 環法則の共通エンジン）** — w ≡ v (mod g)
    （すなわち w − v = h·g、h は多項式）かつ v が m 有界（deg < m）なら、
    `pfdRed g m N w = v`。M268F-7 の剰余一意性（`field_division_unique`）に
    帰着: w = 商·g + pfdRed w（仕様）と w = h·g + v（合同）の両除法の剰余は
    ともに deg < m なので一意で一致する。 -/
theorem pfdRed_char (g : PS ratRing) (m : Nat)
    (hg : IsPolyBounded ratRing g (m + 1)) (hgl : g m ≠ ratRing.zero)
    (N : Nat) (w v : PS ratRing)
    (hw : IsPolyBounded ratRing w (N + m)) (hv : IsPolyBounded ratRing v m)
    (hcong : ∃ (h : PS ratRing) (Nh : Nat), IsPolyBounded ratRing h Nh ∧
      ∀ j, psAdd ratRing w (psNeg ratRing v) j = psMul ratRing h g j) :
    ∀ j, pfdRed g m N w j = v j := by
  obtain ⟨h, Nh, hhb, hcongeq⟩ := hcong
  obtain ⟨hqb, hrb, heq⟩ := pfdDivMod_spec g m hg hgl N w hw
  -- w = h·g + v（合同から）
  have hwj : ∀ j, w j = psAdd ratRing (psMul ratRing h g) v j := by
    intro j
    show w j = ratRing.add (psMul ratRing h g j) (v j)
    have key : ratRing.add (w j) (ratRing.neg (v j)) = psMul ratRing h g j := hcongeq j
    rw [← key, ratRing.add_assoc, ratRing.neg_add, CRing.add_zero ratRing]
  have huniq := field_division_unique ratRing qInv ratIUTField.mul_inv_cancel g m hg hgl
    (pfdDivMod g m N w).1 h (pfdDivMod g m N w).2 v (N + 1) Nh hqb hhb hrb hv
    (fun j => (heq j).symm.trans (hwj j))
  exact huniq.2

/-- **F3-3d: 既に deg < m の w は剰余がそれ自身** — pfdRed の冪等的性質
    （特徴付けの v := w 特例、余因子 h := 0）。 -/
theorem pfdRed_of_bounded (g : PS ratRing) (m : Nat)
    (hg : IsPolyBounded ratRing g (m + 1)) (hgl : g m ≠ ratRing.zero)
    (N : Nat) (w : PS ratRing) (hw : IsPolyBounded ratRing w m) :
    ∀ j, pfdRed g m N w j = w j := by
  have hwN : IsPolyBounded ratRing w (N + m) := fun i hi => hw i (by omega)
  refine pfdRed_char g m hg hgl N w w hwN hw ?_
  refine ⟨psZero ratRing, 0, ?_, ?_⟩
  · intro i _
    show psZero ratRing i = ratRing.zero
    rfl
  · intro j
    show ratRing.add (w j) (ratRing.neg (w j)) = psMul ratRing (psZero ratRing) g j
    have hz : psMul ratRing (psZero ratRing) g j = ratRing.zero := by
      show rsum ratRing (fun i => ratRing.mul (psZero ratRing i) (g (j - i))) (j + 1)
        = ratRing.zero
      have hc : rsum ratRing (fun i => ratRing.mul (psZero ratRing i) (g (j - i))) (j + 1)
          = rsum ratRing (fun _ => ratRing.zero) (j + 1) :=
        rsum_congr ratRing (j + 1) (fun i _ => CRing.zero_mul ratRing _)
      rw [hc]
      exact rsum_const_zero ratRing (j + 1)
    rw [hz]
    exact CRing.add_neg ratRing (w j)

end IUT
