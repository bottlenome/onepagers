/-
# M159F: 厳密評価障害の実数版 — Scholze–Stix 議論の実数値インターフェースへの持ち上げ（柱D）

M5-2（`strict_evaluation_obstruction`・Int 版）と M5-3
（`padding_necessary`・Int 版）を、M139 の実数値多輻的表現
`RealMultiradialRep` の土俵に持ち上げる。「不定性 (Ind1–3) が体積を
膨らませない（厳密テータ評価）」と読む限り、実数値の出力仕様も
充足不能であることを機械検証する。

  * M159F-1 `natConst_le_rBound` — 定数列 intToReal k の標準上界は
    k 自身を押さえる（rBound_spec + qLe_self_abs + 代表計算の反映）
  * M159F-2 `rLe_mul_const_seq` — **技術的本丸**: 非負整数定数
    c = intToReal k の左乗法が rLe を保つことの点ごと補題。
    rmul の添字が左右で異なる（K₁ = rBound c + rBound x ≠
    K₂ = rBound c + rBound y）ため点ごと直接比較は破綻するが、
    c が**定数列**であることを使い、M130 望遠鏡分解
    x_{s₁} − y_{s₂} = (x_{s₁} − x_j) + ((x_j − y_j) + (y_j − y_{s₂}))
    に k を掛けて qLe_mul_right で伝播し、s-添字項は相殺補題
    qFrac_two_bound で u_n に、j-項は ε-消去（c' = k + (k·2 + k)）で
    消す
  * M159F-3 `rLe_mul_natConst_left` — rLe の非負整数定数倍単調性
    （M159F-1 + M159F-2 の合成）
  * M159F-4 `StrictEvaluationReal` — 厳密テータ評価の実数版述語:
    ∀i, l⋇·vol(image i) ≈ intToReal(−Σj²·|log q|)（M5-2 の realEq 版）
  * M159F-5 `strict_evaluation_obstruction_real` — **本丸**:
    厳密評価の実数版障害。q_realized + vol_mono + vol_q 張り替え →
    l⋇ 倍（M159F-3）→ intToReal_mul（M142F）と hstrict で両端を
    intToReal 定数に等値変形 → intToReal_reflect（M139）で整数に降下
    → M5-2 後半と同じ Int 算術（sumSq_gt_int + hq）で矛盾
  * M159F-6 `padding_necessary_real` — 膨張の必然性の実数版:
    q-パイロットを実現する像の体積は −|log q| 以上（M5-3 の写し、
    掛け算不要）
  * M159F-7 `RealObstructionData` — 総括 + witness + 存在

## 意義

M5-2/M5-3（Int 版）が実数値の出力仕様でも成立: 「不定性が体積を
膨らませない」と読む限り実数値 RealMultiradialRep も充足不能で、
充足には −|log q| までの膨張が必然。二分法の精密化
（インターフェースは充足可能・厳密評価とは両立不能・膨張は必然）が
実数の土俵に移設された。Scholze–Stix 型の議論が Int 値の簿記の
人工物ではなく、Bishop 流構成的実数の体積理論でもそのまま働くことの
機械検証である。

正直申告: 乗法単調性（M159F-3）は非負整数定数 intToReal k の左乗法に
限定した形で証明した（本モジュールの用途 l⋇ ≥ 2 にはこれで十分）。
一般の非負実数 c に対する rLe の乗法単調性は次層に委ねる。
スコープ調整（StrictEvaluationReal の弱形への置き換え）は**不要**
だった — 課題指示の原形どおりの定義で障害が閉じている。

全て選択公理不使用。サブエージェント並行部品。
-/
import IUT.IntRealBridge

namespace IUT

/-! ## M159F-1: 定数の標準上界押さえ -/

/-- **M159F-1: 定数列の標準上界** — k ≤ rBound (intToReal k)。
    rBound_spec を添字 0 で読み、qLe_self_abs と合成して
    ι k ≤ ι (rBound)、代表計算（k·1 ≤ rBound·1）へ反映して omega。 -/
theorem natConst_le_rBound (k : Nat) : k ≤ rBound (intToReal (k : Int)) := by
  have h1 : qLe (ratOfInt.map (k : Int))
      (ratOfInt.map ((rBound (intToReal (k : Int)) : Nat) : Int)) :=
    qLe_trans _ _ _ (qLe_self_abs (ratOfInt.map (k : Int)))
      (rBound_spec (intToReal (k : Int)) 0)
  have h2 : (k : Int) * 1
      ≤ ((rBound (intToReal (k : Int)) : Nat) : Int) * 1 := h1
  omega

/-! ## M159F-2: 点ごと主補題（技術的本丸） -/

/-- **定理 (M159F-2): 定数倍単調性の点ごと核** — x ≤ y（rLe）のとき、
    左右で異なる添字加速 s₁ = mulIdx K₁ n・s₂ = mulIdx K₂ n を持つ
    積列 k·x_{s₁} と k·y_{s₂} の間の rLe 型不等式。

    証明: ε-消去 c' = k + (k·2 + k)。任意の比較点 j に対し望遠鏡
    x_{s₁} − y_{s₂} = (x_{s₁} − x_j) + ((x_j − y_j) + (y_j − y_{s₂})) を
    k 倍（qLe_mul_right）して分配・qFrac 化し、s-添字項
    k/(s_i + 1) は k ≤ K_i + K_i と相殺補題（qFrac_two_bound）で
    u_n に、j-添字項は c'/(j+1) に濃縮する。 -/
theorem rLe_mul_const_seq (k : Nat) {x y : RReal} (h : rLe x y)
    (K₁ K₂ : Nat) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂)
    (hk₁ : k ≤ K₁ + K₁) (hk₂ : k ≤ K₂ + K₂) (n : Nat) :
    qLe (qMul (ratOfInt.map (k : Int)) (x.seq (mulIdx K₁ n)))
      (qAdd (qMul (ratOfInt.map (k : Int)) (y.seq (mulIdx K₂ n)))
        (qAdd (qUnitFrac n) (qUnitFrac n))) := by
  apply qLe_of_forall_add_frac (k + (k * 2 + k))
  intro j
  -- 定数 ι k の非負性（代表計算）
  have hι : qLe ratRing.zero (ratOfInt.map (k : Int)) := by
    show (0 : Int) * 1 ≤ (k : Int) * 1
    omega
  -- 望遠鏡の 3 部品
  have t1 := reg_sub_le x (mulIdx K₁ n) j
  have t2 : qLe (qAdd (x.seq j) (qNeg (y.seq j))) (qFrac 2 j) :=
    qLe_trans _ _ _ (qSub_le_of_le (h j)) (qFrac_add 1 1 j)
  have t3 := reg_sub_le y j (mulIdx K₂ n)
  have esplit : qAdd (x.seq (mulIdx K₁ n)) (qNeg (y.seq (mulIdx K₂ n)))
      = qAdd (qAdd (x.seq (mulIdx K₁ n)) (qNeg (x.seq j)))
        (qAdd (qAdd (x.seq j) (qNeg (y.seq j)))
          (qAdd (y.seq j) (qNeg (y.seq (mulIdx K₂ n))))) := by
    rw [← qSub_split (x.seq j) (y.seq j) (y.seq (mulIdx K₂ n)),
      ← qSub_split (x.seq (mulIdx K₁ n)) (x.seq j) (y.seq (mulIdx K₂ n))]
  have tsum : qLe (qAdd (x.seq (mulIdx K₁ n)) (qNeg (y.seq (mulIdx K₂ n))))
      (qAdd (qAdd (qUnitFrac (mulIdx K₁ n)) (qUnitFrac j))
        (qAdd (qFrac 2 j)
          (qAdd (qUnitFrac j) (qUnitFrac (mulIdx K₂ n))))) :=
    qLe_trans _ _ _ (qLe_of_eq esplit)
      (qLe_add_two t1 (qLe_add_two t2 t3))
  -- k 倍（左乗法は可換で右単調性に還元）
  have hmul0 : qLe
      (qMul (ratOfInt.map (k : Int))
        (qAdd (x.seq (mulIdx K₁ n)) (qNeg (y.seq (mulIdx K₂ n)))))
      (qMul (ratOfInt.map (k : Int))
        (qAdd (qAdd (qUnitFrac (mulIdx K₁ n)) (qUnitFrac j))
          (qAdd (qFrac 2 j)
            (qAdd (qUnitFrac j) (qUnitFrac (mulIdx K₂ n)))))) := by
    rw [qMul_comm (ratOfInt.map (k : Int))
        (qAdd (x.seq (mulIdx K₁ n)) (qNeg (y.seq (mulIdx K₂ n)))),
      qMul_comm (ratOfInt.map (k : Int))
        (qAdd (qAdd (qUnitFrac (mulIdx K₁ n)) (qUnitFrac j))
          (qAdd (qFrac 2 j)
            (qAdd (qUnitFrac j) (qUnitFrac (mulIdx K₂ n)))))]
    exact qLe_mul_right tsum hι
  -- 右辺の分配と qFrac 化
  have eB : qMul (ratOfInt.map (k : Int))
      (qAdd (qAdd (qUnitFrac (mulIdx K₁ n)) (qUnitFrac j))
        (qAdd (qFrac 2 j)
          (qAdd (qUnitFrac j) (qUnitFrac (mulIdx K₂ n)))))
      = qAdd (qAdd (qFrac k (mulIdx K₁ n)) (qFrac k j))
        (qAdd (qFrac (k * 2) j)
          (qAdd (qFrac k j) (qFrac k (mulIdx K₂ n)))) := by
    rw [qMul_add (ratOfInt.map (k : Int))
        (qAdd (qUnitFrac (mulIdx K₁ n)) (qUnitFrac j))
        (qAdd (qFrac 2 j) (qAdd (qUnitFrac j) (qUnitFrac (mulIdx K₂ n)))),
      qMul_add (ratOfInt.map (k : Int)) (qUnitFrac (mulIdx K₁ n))
        (qUnitFrac j),
      qMul_add (ratOfInt.map (k : Int)) (qFrac 2 j)
        (qAdd (qUnitFrac j) (qUnitFrac (mulIdx K₂ n))),
      qMul_add (ratOfInt.map (k : Int)) (qUnitFrac j)
        (qUnitFrac (mulIdx K₂ n)),
      ratOfInt_mul_unitFrac k (mulIdx K₁ n), ratOfInt_mul_unitFrac k j,
      ratOfInt_mul_qFrac k 2 j, ratOfInt_mul_unitFrac k (mulIdx K₂ n)]
  rw [eB] at hmul0
  -- s-添字項の相殺: k/(s_i + 1) ≤ 1/(n+1)
  have hfrac₁ : qLe (qFrac k (mulIdx K₁ n)) (qUnitFrac n) :=
    qLe_trans _ _ _
      (qFrac_le (Int.mul_le_mul_of_nonneg_right
        (show (k : Int) ≤ ((K₁ + K₁ : Nat) : Int) by omega)
        (show (0 : Int) ≤ ((mulIdx K₁ n : Nat) : Int) + 1 by omega)))
      (qFrac_two_bound K₁ n hK₁)
  have hfrac₂ : qLe (qFrac k (mulIdx K₂ n)) (qUnitFrac n) :=
    qLe_trans _ _ _
      (qFrac_le (Int.mul_le_mul_of_nonneg_right
        (show (k : Int) ≤ ((K₂ + K₂ : Nat) : Int) by omega)
        (show (0 : Int) ≤ ((mulIdx K₂ n : Nat) : Int) + 1 by omega)))
      (qFrac_two_bound K₂ n hK₂)
  have hstep : qLe (qMul (ratOfInt.map (k : Int))
        (qAdd (x.seq (mulIdx K₁ n)) (qNeg (y.seq (mulIdx K₂ n)))))
      (qAdd (qAdd (qUnitFrac n) (qFrac k j))
        (qAdd (qFrac (k * 2) j) (qAdd (qFrac k j) (qUnitFrac n)))) :=
    qLe_trans _ _ _ hmul0
      (qLe_add_two (qLe_add_two hfrac₁ (qLe_refl (qFrac k j)))
        (qLe_add_two (qLe_refl (qFrac (k * 2) j))
          (qLe_add_two (qLe_refl (qFrac k j)) hfrac₂)))
  -- 定数側の並べ替えと濃縮
  have e1 : qAdd (qAdd (qUnitFrac n) (qFrac k j))
      (qAdd (qFrac (k * 2) j) (qAdd (qFrac k j) (qUnitFrac n)))
      = qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
        (qAdd (qFrac k j) (qAdd (qFrac (k * 2) j) (qFrac k j))) := by
    rw [qAdd_comm (qFrac k j) (qUnitFrac n),
      ← qAdd_assoc (qFrac (k * 2) j) (qUnitFrac n) (qFrac k j),
      qAdd_comm (qFrac (k * 2) j) (qUnitFrac n),
      qAdd_assoc (qUnitFrac n) (qFrac (k * 2) j) (qFrac k j),
      qAdd_swap_mid (qUnitFrac n) (qFrac k j) (qUnitFrac n)
        (qAdd (qFrac (k * 2) j) (qFrac k j))]
  have hfold : qLe (qAdd (qFrac k j) (qAdd (qFrac (k * 2) j) (qFrac k j)))
      (qFrac (k + (k * 2 + k)) j) :=
    qLe_trans _ _ _
      (qLe_add_two (qLe_refl (qFrac k j)) (qFrac_add (k * 2) k j))
      (qFrac_add k (k * 2 + k) j)
  have htotal : qLe (qMul (ratOfInt.map (k : Int))
        (qAdd (x.seq (mulIdx K₁ n)) (qNeg (y.seq (mulIdx K₂ n)))))
      (qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
        (qFrac (k + (k * 2 + k)) j)) :=
    qLe_trans _ _ _ hstep (qLe_trans _ _ _ (qLe_of_eq e1)
      (qLe_add_two (qLe_refl (qAdd (qUnitFrac n) (qUnitFrac n))) hfold))
  -- 因数分解 ι k·(x − y) = ι k·x − ι k·y と移項
  have efac : qMul (ratOfInt.map (k : Int))
      (qAdd (x.seq (mulIdx K₁ n)) (qNeg (y.seq (mulIdx K₂ n))))
      = qAdd (qMul (ratOfInt.map (k : Int)) (x.seq (mulIdx K₁ n)))
        (qNeg (qMul (ratOfInt.map (k : Int)) (y.seq (mulIdx K₂ n)))) := by
    rw [qMul_add (ratOfInt.map (k : Int)) (x.seq (mulIdx K₁ n))
        (qNeg (y.seq (mulIdx K₂ n))),
      qMul_neg_right (ratOfInt.map (k : Int)) (y.seq (mulIdx K₂ n))]
  rw [efac] at htotal
  have hx := qLe_sub_move htotal
  have e5 : qAdd (qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
        (qFrac (k + (k * 2 + k)) j))
      (qMul (ratOfInt.map (k : Int)) (y.seq (mulIdx K₂ n)))
      = qAdd (qAdd (qMul (ratOfInt.map (k : Int)) (y.seq (mulIdx K₂ n)))
          (qAdd (qUnitFrac n) (qUnitFrac n)))
        (qFrac (k + (k * 2 + k)) j) := by
    rw [qAdd_comm (qAdd (qAdd (qUnitFrac n) (qUnitFrac n))
        (qFrac (k + (k * 2 + k)) j))
        (qMul (ratOfInt.map (k : Int)) (y.seq (mulIdx K₂ n))),
      ← qAdd_assoc (qMul (ratOfInt.map (k : Int)) (y.seq (mulIdx K₂ n)))
        (qAdd (qUnitFrac n) (qUnitFrac n)) (qFrac (k + (k * 2 + k)) j)]
  exact qLe_trans _ _ _ hx (qLe_of_eq e5)

/-! ## M159F-3: rLe の非負整数定数倍単調性 -/

/-- **定理 (M159F-3): 左定数倍単調性** — x ≤ y なら
    intToReal k · x ≤ intToReal k · y（rLe）。intToReal k は定数列
    なので rmul の添字加速は x・y 側にのみ働き、M159F-2 の点ごと核が
    そのまま両辺の rmul の列に適用できる（k ≤ K_i + K_i は
    M159F-1 から）。 -/
theorem rLe_mul_natConst_left (k : Nat) {x y : RReal} (h : rLe x y) :
    rLe (rmul (intToReal (k : Int)) x) (rmul (intToReal (k : Int)) y) := by
  intro n
  have hkb : k ≤ rBound (intToReal (k : Int)) := natConst_le_rBound k
  exact rLe_mul_const_seq k h
    (rBound (intToReal (k : Int)) + rBound x)
    (rBound (intToReal (k : Int)) + rBound y)
    (rBound_pair_pos (intToReal (k : Int)) x)
    (rBound_pair_pos (intToReal (k : Int)) y)
    (by omega) (by omega) n

/-! ## M159F-4: 厳密テータ評価の実数版 -/

/-- **M159F-4: 厳密テータ評価（実数版）** — Scholze–Stix の読み:
    不定性込みの可能な像の実数値体積が、テータ値 {q^{j²}} の素朴な
    計算値 −(Σj²/l⋇)·|log q| に厳密に一致するという仮定。
    l⋇·vol(image i) ≈ intToReal(−Σj²·|log q|) と realEq で表す
    （M5-2 `StrictEvaluation` の realEq 版）。 -/
def StrictEvaluationReal {V : RealVolumeTheory} {s : Skeleton}
    (M : RealMultiradialRep V s) : Prop :=
  ∀ i, realEq (rmul (intToReal (s.lstar : Int)) (V.vol (M.image i)))
    (intToReal (-(sumSq s.lstar : Int) * s.logq))

/-! ## M159F-5: 厳密評価の実数版障害（本丸） -/

/-- **定理 (M159F-5): 厳密評価障害の実数版（本丸）** — M5-2 の
    実数の土俵への持ち上げ。可能な像の実数値体積がすべて素朴な
    テータ値計算に一致するなら、実数値多輻的表現は存在し得ない。

    証明: q_realized の像 i で vol(q像) ≤ vol(image i)（vol_mono）、
    vol_q の realEq で左辺を intToReal(−|log q|) に張り替え、
    l⋇ 倍（M159F-3）。左辺は intToReal_mul（M142F）で
    intToReal(l⋇·(−|log q|)) に、右辺は hstrict i で
    intToReal(−Σj²·|log q|) に realEq 張り替え（rLe_congr）、
    intToReal_reflect（M139）で整数に降下して M5-2 後半の
    Int 算術（Σj² > l⋇・|log q| > 0）で矛盾。 -/
theorem strict_evaluation_obstruction_real {V : RealVolumeTheory}
    {s : Skeleton} (M : RealMultiradialRep V s)
    (hstrict : StrictEvaluationReal M) : False := by
  obtain ⟨i, hi⟩ := M.q_realized
  -- q 体積 ≤ 像の体積（実数値）
  have h2 : rLe (V.vol M.qRegion) (V.vol (M.image i)) := V.vol_mono hi
  have h3 : rLe (intToReal (-s.logq)) (V.vol (M.image i)) :=
    rLe_congr M.vol_q (realEq_refl (V.vol (M.image i))) h2
  -- l⋇ 倍（実数の定数倍単調性）
  have h4 : rLe (rmul (intToReal (s.lstar : Int)) (intToReal (-s.logq)))
      (rmul (intToReal (s.lstar : Int)) (V.vol (M.image i))) :=
    rLe_mul_natConst_left s.lstar h3
  -- 両端を intToReal 定数に張り替え（M142F 乗法性 + 厳密評価）
  have h5 : rLe (intToReal ((s.lstar : Int) * -s.logq))
      (intToReal (-(sumSq s.lstar : Int) * s.logq)) :=
    rLe_congr (intToReal_mul (s.lstar : Int) (-s.logq)) (hstrict i) h4
  -- 整数に降下
  have h6 : (s.lstar : Int) * -s.logq ≤ -(sumSq s.lstar : Int) * s.logq :=
    intToReal_reflect h5
  -- M5-2 後半と同じ Int 算術
  have e1 : (s.lstar : Int) * -s.logq = -((s.lstar : Int) * s.logq) :=
    Int.mul_neg _ _
  have e2 : -(sumSq s.lstar : Int) * s.logq
      = -((sumSq s.lstar : Int) * s.logq) :=
    Int.neg_mul _ _
  rw [e1, e2] at h6
  have h7 : (s.lstar : Int) * s.logq < (sumSq s.lstar : Int) * s.logq :=
    Int.mul_lt_mul_of_pos_right (sumSq_gt_int s.lstar s.hl) s.hq
  omega

/-! ## M159F-6: 膨張の必然性の実数版 -/

/-- **定理 (M159F-6): 膨張の必然性（実数版）** — M5-3 の写し。
    実数値多輻的表現が存在するなら、q-パイロットを実現する可能な像の
    実数値体積は最低でも intToReal(−|log q|) まで「太って」いなければ
    ならない（厳密テータ値 −(Σj²/l⋇)|log q| はこれより真に小さいので
    不定性による膨張が必然）。 -/
theorem padding_necessary_real {V : RealVolumeTheory} {s : Skeleton}
    (M : RealMultiradialRep V s) :
    ∃ i, rLe (intToReal (-s.logq)) (V.vol (M.image i)) := by
  obtain ⟨i, hi⟩ := M.q_realized
  exact ⟨i, rLe_congr M.vol_q (realEq_refl (V.vol (M.image i)))
    (V.vol_mono hi)⟩

/-! ## M159F-7: 総括 -/

/-- **M159F-7a: 総括** — 厳密評価障害の実数版データ。 -/
structure RealObstructionData where
  /-- rLe の非負整数定数倍単調性。 -/
  mul_mono : ∀ (k : Nat) {x y : RReal}, rLe x y →
    rLe (rmul (intToReal (k : Int)) x) (rmul (intToReal (k : Int)) y)
  /-- 厳密評価障害（実数版）: 厳密テータ評価と実数値多輻的表現は
      両立不能。 -/
  strict_obstruction : ∀ {V : RealVolumeTheory} {s : Skeleton}
    (M : RealMultiradialRep V s), StrictEvaluationReal M → False
  /-- 膨張の必然性（実数版）: 実現像の体積は −|log q| 以上。 -/
  padding : ∀ {V : RealVolumeTheory} {s : Skeleton}
    (M : RealMultiradialRep V s),
    ∃ i, rLe (intToReal (-s.logq)) (V.vol (M.image i))

/-- **M159F-7b: witness**。 -/
def realObstructionData : RealObstructionData where
  mul_mono := rLe_mul_natConst_left
  strict_obstruction := strict_evaluation_obstruction_real
  padding := padding_necessary_real

/-- **M159F-7c: 存在**。 -/
theorem realObstruction_exists : Nonempty RealObstructionData :=
  ⟨realObstructionData⟩

end IUT
