/-
  IUT/Q3NormSurjComplete.lean — 柱B・B2 T3-M3a: **完備性への可除性ブリッジ（level-k 判定・分離性）**
    （逐次近似塔 q9ncSeq の極限をとるための、実 ℤ₃ 上の level-k 3-可除性判定
     `q9cm_dvd_pow_iff`（∃e, x = 3^k·e ⟺ x のレベル k 成分が 0）と分離性
     `q9cm_sep`（∀k レベル k 成分が 0 ⟹ x = 0）を本物で建てる。M3 の梯子 M3a→M3b→M3c の
     第 1 段 M3a-1 = 「唯一の新しい機械」。）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**（T3-M3 完備性の可除性判定インフラを
     ゼロから積む・toy 主語なし）。主語は実 ℤ₃ = zpRing 3（M27 逆極限環）、その level-1
     可除判定 `zp_dvd_p_iff`（PadicDivision 実在）を level-k に一般化し、極限に必要な
     「深さ k の 3-可除性 ⟺ レベル k 成分消滅」の同値と、逆極限の分離性を本物で確立する。

  complete_pct 影響: **B2 T3-M3a-1 を前進**（監査次第・予測 s_B2 0.44→0.45）。本ラウンドで
    閉じるのは M3 梯子（audit/pillar-B2-T3-M2-M3-completeness-detail-2026-07-11.md §4）の
    **M3a-1**:
    (i) `q9cmMul3Pow`（3 倍の k 回反復＝ 3^k 乗）と level 上げ／下げの整合
        （`q9cm_mul3_up`: 3^k∣y ⟹ 3^{k+1}∣3y／`q9cm_div3_down`: 3^{k+1}∣x ⟹ 3^k∣(x/3)）、
    (ii) ★ **level-k 可除性判定** `q9cm_dvd_pow_iff`（(∃e, x=3^k·e) ⟺ z3vGe 3 x k・k 帰納。
         降下段は zpDivP［3 除算・total・choice-free・実在］の反復で witness をデータ供給）、
    (iii) **z3 分離性** `q9cm_sep`（∀k z3vGe 3 x k ⟹ x = 0・Subtype.ext + funext）。

  ── **正直な限定（§4 規約により消さない・弱めない）:**
  0. **本ファイルは M3a-1（level-k 判定＋分離性）のみ**を閉じる。M3 梯子の残りは未達:
     - **M3a-2（O_M 座標ブリッジ・未達）**: 「3^k∣z (O_M) ⟺ 6 個の z3 座標が各々 3^k∣」は
       q3k 環のスカラー 3 乗の座標展開を要し、本ファイルでは建てていない。
     - **M3a-3（π₉⇔3 変換・未達）**: 「π₉^{6k}∣z ⟺ 3^k∣z」（3=π₉⁶·u₆ 経由）は未達。
     - **M3b（極限構成 q9ncLim・未達）**: z3cLim の 6 座標適用による極限は未建設。
     - **M3c（N の連続性・分離・厳密等式 N(x)=u・未達）**: T3-core の厳密等式は未達。
     したがって本ファイルは「u はノルムである（N(x)=u）」を**主張しない**。極限の存在も
     まだ建てていない（level-k 判定という前提インフラのみ）。
  1. U^{(3)}⊆N の全体・index≤3（M4）は未達（T3 スコープ外）。
  2. q9nc/q9na/q9npg/q9ns/q9nf/q9gn/q9ps/q9rf/q9wr/q3k/q3rq/z3c の正直限定を全継承
     （可除性形式・total v_M 不使用・O_M と M^× のみ・体化なし・σ を超える Galois ゼロ・
      実テータ関数ゼロ・π₁ 同定ゼロ・兄弟担体・拡大 1 個 M/L₂/ℚ₃・
      完備性は modulus 形のみ・p=3 固定）。

  全て選択公理不使用（新規 Classical.choice なし・sorry 皆無・3 除算は zpDivP の ediv ベース・
  omega は Int/Nat atom のみ）。#print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3NormSurjApproxClose
import IUT.Zp3Complete

namespace IUT

/-! ## q9cm-1: 3^k 乗（3 倍の k 回反復）と要素 3 -/

/-- **q9cm-1a: 実 ℤ₃ の元 3**（対角埋め込み toZp 3 の値・zpDivP 機構と整合）。 -/
def q9cmThreeZ : z3.carrier := (toZp 3).map ((3 : Nat) : Int)

/-- **q9cm-1b: レベル n での 3 の代表**（toZp の定義から rfl）。 -/
theorem q9cm_threeZ_val (n : Nat) :
    q9cmThreeZ.val n = Quot.mk (modCong (3 ^ n)).rel ((3 : Nat) : Int) := rfl

/-- **q9cm-1c: 3^k 乗**（3 倍の k 回反復・data 関数）。 -/
def q9cmMul3Pow : Nat → z3.carrier → z3.carrier
  | 0, e => e
  | (k + 1), e => zpMul 3 q9cmThreeZ (q9cmMul3Pow k e)

/-! ## q9cm-2: level 上げ／下げの整合（3 倍と 3 除算のレベル移動） -/

/-- **q9cm-2a: 3 倍でレベルが 1 上がる** — 3^k∣y（z3vGe 3 y k）⟹ 3^{k+1}∣3y。
    y のレベル k+1 代表 b が 3^k∣b を満たすことをレベル k 整合で読み、3b = 3^{k+1}·t を得る。 -/
theorem q9cm_mul3_up (y : z3.carrier) (k : Nat) (h : z3vGe 3 y k) :
    z3vGe 3 (zpMul 3 q9cmThreeZ y) (k + 1) := by
  obtain ⟨b, hb⟩ := Quot.exists_rep (y.val (k + 1))
  have e1 : y.val k = Quot.mk (modCong (3 ^ k)).rel b := by
    have hp := y.property (Nat.le_succ k)
    rw [← hb] at hp
    exact hp.symm
  have hyk0 : Quot.mk (modCong (3 ^ k)).rel b = Quot.mk (modCong (3 ^ k)).rel 0 :=
    e1.symm.trans h
  obtain ⟨t, ht⟩ := quot_exact intGrp (modCong (3 ^ k)) hyk0
  have hbeq : b = ((3 ^ k : Nat) : Int) * t := by
    have h2 := ht
    rw [Int.sub_zero] at h2
    exact h2
  show (zpMul 3 q9cmThreeZ y).val (k + 1) = Quot.mk (modCong (3 ^ (k + 1))).rel 0
  show zmodMul (3 ^ (k + 1)) (q9cmThreeZ.val (k + 1)) (y.val (k + 1))
    = Quot.mk (modCong (3 ^ (k + 1))).rel 0
  rw [q9cm_threeZ_val (k + 1), ← hb]
  show Quot.mk (modCong (3 ^ (k + 1))).rel (((3 : Nat) : Int) * b)
    = Quot.mk (modCong (3 ^ (k + 1))).rel 0
  apply Quot.sound
  show ((3 ^ (k + 1) : Nat) : Int) ∣ ((3 : Nat) : Int) * b - 0
  refine ⟨t, ?_⟩
  rw [cast_pow_succ 3 k, Int.sub_zero, hbeq,
      ← Int.mul_assoc ((3 : Nat) : Int) ((3 ^ k : Nat) : Int) t,
      Int.mul_comm ((3 : Nat) : Int) ((3 ^ k : Nat) : Int)]

/-- **q9cm-2b: 3 除算でレベルが 1 下がる** — 3^{k+1}∣x（z3vGe 3 x (k+1)）⟹ 3^k∣(x/3)。
    x のレベル k+1 成分が 0 なら zpDivP の代表 ediv は 0/3 = 0 に潰れる。 -/
theorem q9cm_div3_down (x : z3.carrier) (k : Nat) (h : z3vGe 3 x (k + 1)) :
    z3vGe 3 (zpDivP 3 (by omega) x) k := by
  have hx : x.val (k + 1) = Quot.mk (modCong (3 ^ (k + 1))).rel 0 := h
  show (zpDivP 3 (by omega) x).val k = Quot.mk (modCong (3 ^ k)).rel 0
  show zmodDivP 3 k (by omega) (x.val (k + 1)) = Quot.mk (modCong (3 ^ k)).rel 0
  rw [hx]
  show Quot.mk (modCong (3 ^ k)).rel ((0 : Int) / ((3 : Nat) : Int))
    = Quot.mk (modCong (3 ^ k)).rel 0
  rw [Int.zero_ediv]

/-! ## q9cm-3: ★ level-k 可除性判定（M3a-1 の心臓） -/

/-- **q9cm-3a: 3^{k+1}·e = 3·(3^k·e)**（3^k 乗の 1 段展開）。 -/
theorem q9cm_mul3pow_succ (k : Nat) (e : z3.carrier) :
    q9cmMul3Pow (k + 1) e = zpMul 3 q9cmThreeZ (q9cmMul3Pow k e) := rfl

/-- **q9cm-3b（★ level-k 可除性判定）: (∃e, x = 3^k·e) ⟺ z3vGe 3 x k**。
    level-1 判定 zp_dvd_p_iff の k 一般化（k 帰納）。降下段は zpDivP（3 除算・total・
    choice-free）を 1 回消費して witness をデータで供給し、q9cm_div3_down でレベルを 1 下げ、
    q9cm_mul3_up で逆向きを上げる。x/3 の再帰で ∃ witness をデータ関数から構成するため
    可算選択を要さない。 -/
theorem q9cm_dvd_pow_iff (k : Nat) (x : z3.carrier) :
    (∃ e, x = q9cmMul3Pow k e) ↔ z3vGe 3 x k := by
  induction k generalizing x with
  | zero =>
    constructor
    · intro _
      exact z3vGe_zero 3 x
    · intro _
      exact ⟨x, rfl⟩
  | succ k ih =>
    constructor
    · intro ⟨e, he⟩
      rw [he, q9cm_mul3pow_succ k e]
      exact q9cm_mul3_up (q9cmMul3Pow k e) k ((ih (q9cmMul3Pow k e)).mp ⟨e, rfl⟩)
    · intro hx
      have hx1 : z3vGe 3 x 1 :=
        z3vGe_antitone 3 x (Nat.succ_le_succ (Nat.zero_le k)) hx
      have hxdiv : x = zpMul 3 ((toZp 3).map ((3 : Nat) : Int)) (zpDivP 3 (by omega) x) :=
        (zpDivP_mul_cancel 3 (by omega) x hx1).symm
      have hdown : z3vGe 3 (zpDivP 3 (by omega) x) k := q9cm_div3_down x k hx
      obtain ⟨e, he⟩ := (ih (zpDivP 3 (by omega) x)).mpr hdown
      refine ⟨e, ?_⟩
      rw [q9cm_mul3pow_succ k e, ← he]
      exact hxdiv

/-! ## q9cm-4: z3 の分離性（逆極限が Hausdorff = 完備性の分離条件） -/

/-- **q9cm-4a（★ 分離性）: (∀k, z3vGe 3 x k) ⟹ x = 0**。
    全レベルで x のレベル k 成分が 0 なら、x は 0（整合族の外延性）。
    完備性の極限一意性 z3c_lim_unique の分離条件を可除性形式で単独に取り出したもの。 -/
theorem q9cm_sep (x : z3.carrier) (h : ∀ k, z3vGe 3 x k) : x = z3.zero := by
  apply Subtype.ext
  funext n
  show x.val n = (z3.zero).val n
  have hn : x.val n = Quot.mk (modCong (3 ^ n)).rel 0 := h n
  have hz : (z3.zero).val n = Quot.mk (modCong (3 ^ n)).rel 0 := rfl
  rw [hn, hz]

/-- **q9cm-4b: 分離性の差版** — (∀k, z3vGe 3 (a − b) k) ⟹ a = b。 -/
theorem q9cm_sep_sub (a b : z3.carrier) (h : ∀ k, z3vGe 3 (z3.add a (z3.neg b)) k) :
    a = b := by
  have h0 : z3.add a (z3.neg b) = z3.zero := q9cm_sep (z3.add a (z3.neg b)) h
  have h1 : z3.add (z3.add a (z3.neg b)) b = z3.add z3.zero b := by rw [h0]
  rw [z3.add_assoc a (z3.neg b) b, z3.neg_add b, z3.add_zero a, z3.zero_add b] at h1
  exact h1

/-! ## q9cm-5: capstone（M3a-1 完了データ） -/

/-- **q9cm-5a: M3a-1 完了データ**（level-k 可除性判定 + 分離性）。 -/
structure Q3NormSurjM3aData where
  /-- ★ level-k 可除性判定（∃e, x=3^k·e ⟺ レベル k 成分消滅）。 -/
  dvd_pow_iff : ∀ (k : Nat) (x : z3.carrier),
    (∃ e, x = q9cmMul3Pow k e) ↔ z3vGe 3 x k
  /-- ★ z3 分離性（全レベル消滅 ⟹ 0）。 -/
  sep : ∀ (x : z3.carrier), (∀ k, z3vGe 3 x k) → x = z3.zero

/-- **q9cm-5b: 見出し実例** — 実 ℤ₃ 上の M3a-1（level-k 判定 + 分離性）。 -/
def q9cm_data : Q3NormSurjM3aData where
  dvd_pow_iff := q9cm_dvd_pow_iff
  sep := q9cm_sep

/-- **q9cm-5c: M3a-1 の存在**（level-k 可除性判定 + 分離性の実 Lean 化）。 -/
theorem q9cm_exists : Nonempty Q3NormSurjM3aData := ⟨q9cm_data⟩

end IUT
