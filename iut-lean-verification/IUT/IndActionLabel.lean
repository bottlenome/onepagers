/-
  IUT/IndActionLabel.lean — M254F（Dβ-5 拡張: (Ind1) ラベル置換・
  (Ind3) 上方包含膨張の QDiv 同時作用）

  D-β 詳細化ラウンド（軸1 = 模型忠実化）の続き。M241F
  `IUT/IndAction.lean` は不定性の QDiv 作用の器 `IndAction` を建て、
  居住する具体 witness は **(Ind2)（単数トーソル `unitIndAction`）のみ**
  であった（正直申告に「(Ind1) deloopInd・(Ind3) UpperCompat の同時作用は
  次段。IndAction は器として両者を差し込める設計」と明記）。本モジュールは
  その次段として、(Ind1) と (Ind3) を QDiv に**実際に作用**させる。

  ## 核心（何を honest に実装したか）

  ### (Ind1) ラベル/座標の置換の作用（本丸・強い形）

  * `swapMult` / `swapDiv` — 二つの座標ラベル a, b の**置換（互換）**を
    QDiv の重複度に作用させる（M53F `deloopInd` = BG poly-iso G-トーソル
    ＝「ラベル置換」の算術模型上の実体化。procession の自己同型が
    因子の素点添字を並べ替える作用）。
  * `nsum_pull_one` / `nsum_two_point_eq` — 有限和の一点抜き出しと、
    二点だけ食い違う和が「その二点の和が一致すれば」等しいという不変性。
    互換不変性の証明基盤（core のみ・omega の線形部分と if 剥がしで閉じる）。
  * `degZ_swap` — **本丸**: 二つの**等重み座標**（`w a = w b`、**正の重みも可**）
    の置換は大域次数 degZ を**厳密に保つ**。像は並べ替わるが次数は不変。
    これが (Ind1) の多輻性（軌道共変性・等次数葉上の軌道）の実体。
  * `PermIndAction` / `labelPermAction` / `labelPerm_orbit` /
    `label_indeterminacy_acts` — (Ind1) 作用データ（hull を課さない
    次数不変軌道の器）。`image true ≠ image false`（非定数軌道）かつ
    degZ 不変。**正の等重み座標**で成立するので、単数（重み0）に頼らない
    真の置換不定性である。

  ### (Ind3) 上方包含（上半両立）の膨張作用

  * `ExpandIndAction` / `upperExpandAction` — (Ind3) UpperCompat
    （M202F、片側包含 `lo ⊆ hi`）が像を**膨張**させる作用の器と witness。
    `base_le_image`（基点像 ⊆ 各像＝一方向包含）を課し、次数は
    **下界を保ったまま単調増加**（`deg_lower`）する。等号でなく
    ⊆ のみ・膨張のみという (Ind3) の一方向性をそのまま QDiv 作用にした。
  * `upperExpand_orbit` / `upperExpand_not_symm` — 膨張軌道は非定数
    （`image true ≠ image false`）かつ真に**一方向**（`image true ⊆ image false`
    は成り立たない）。M202F `upper_compat_not_symm` の QDiv 作用版。

  ### (Ind1)×(Ind2) の同時作用（合成）

  * `combImg` / `combPermAction` / `comb_indeterminacies_act` —
    (Ind1) 置換（等重み座標）と (Ind2) 単数（重み0座標のずらし）を
    `Bool × Bool` 軌道上で**同時に**QDiv へ作用させた `PermIndAction`。
    両不定性が像に独立な軌道を与え、いずれも degZ を保つ。複数の不定性が
    同時に像を動かす多輻性の芽（M241F unit 単独からの前進）。

  ### 既存 IndAction（M241F・hull 付き）への橋渡し

  * `labelIndAction` / `arith_transport_of_label_orbit` —
    (Ind1) 置換を**M241F の `IndAction`（hull 等次数付き）**に居住させる。
    重み0の二座標で置換すると hull も等次数に固定でき、`arithPreRepInd`
    経由で crux ⟹ Cor312 が (Ind1) 軌道を通しても従う。

  ## 正直な限定（どこまで作用させたか・crux は範囲外）

  * **degZ_swap（置換の次数不変）は正の等重み座標で成立する強い形**だが、
    hull を等次数に固定する `IndAction`（M241F）への居住は**重み0の二座標**
    に限る（正の重みでは互換の点毎上界＝pointwise max が厳密に大きい次数を
    持ち、等次数 hull が存在しない——これは (Ind3) の膨張スラック
    `padding_necessary` が必然である理由の因子レベルの影である）。正の重み
    置換の hull-free 軌道は `PermIndAction` として居住させた。
  * **同時作用は (Ind1)×(Ind2) まで**。(Ind3) 膨張を同じ `PermIndAction`
    に合流させる完全な (Ind1)×(Ind2)×(Ind3) 同時作用は、次数の等号と
    下界という二種の制約を一つの器に統合する必要があり**次段**である
    （本モジュールは (Ind3) を独立の器 `ExpandIndAction` として実装）。
  * **crux `q_realized` は依然として外部仮説 hq**（M238F/M241F と同じ）。
    crux の単一 Prop 化・鏡像定理・実データ証明は本モジュールでは構成しない。
  * ラベル置換は「素点添字 k の置換」であり、原論文の procession の
    自己同型（テータ被覆のデッキ変換）の解析的内容は写像しない（M53F の
    正直申告の継続）。
-/
import IUT.IndAction
import IUT.GaussianDivisor

namespace IUT

/-! ## Part 1: 有限和の一点抜き出しと二点入れ替え不変（互換不変性の基盤）

    互換（二座標の置換）が次数を保つことを、有限和 `nsum` の
    「二点だけ食い違い、その二点の値の和が一致すれば和は不変」という
    補題に帰着する。omega は線形部分のみ、if 剥がしは if_pos/if_neg で行う。 -/

/-- 添字 a で値を 0 に潰す関数（一点抜き出しの補助）。 -/
def nsZeroAt (a : Nat) (g : Nat → Nat) (k : Nat) : Nat :=
  if k = a then 0 else g k

/-- 潰した点以外では元の値。 -/
theorem nsZeroAt_eq (a : Nat) (g : Nat → Nat) (k : Nat) (h : ¬ k = a) :
    nsZeroAt a g k = g k := if_neg h

/-- 潰した点では 0。 -/
theorem nsZeroAt_self (a : Nat) (g : Nat → Nat) : nsZeroAt a g a = 0 :=
  if_pos rfl

/-- 束縛点毎に一致する二関数の有限和は等しい。 -/
theorem nsum_congr_lt (g h : Nat → Nat) :
    ∀ n, (∀ k, k < n → g k = h k) → nsum g n = nsum h n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ m ih =>
    intro hgh
    show nsum g m + g m = nsum h m + h m
    rw [ih (fun k hk => hgh k (Nat.lt_succ_of_lt hk)), hgh m (Nat.lt_succ_self m)]

/-- **一点抜き出し**: a < n なら Σ_{k<n} g k = Σ_{k<n}(g を a で 0 に潰した和) + g a。 -/
theorem nsum_pull_one (g : Nat → Nat) (a : Nat) :
    ∀ n, a < n → nsum g n = nsum (nsZeroAt a g) n + g a := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_lt_zero a)
  | succ m ih =>
    intro h
    show nsum g m + g m = nsum (nsZeroAt a g) m + nsZeroAt a g m + g a
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with
    | inl heq =>
      have hz : nsZeroAt a g m = 0 := by rw [← heq]; exact nsZeroAt_self a g
      have hns : nsum (nsZeroAt a g) m = nsum g m :=
        nsum_congr_lt _ _ m (fun k hk => nsZeroAt_eq a g k (by omega))
      have hga : g a = g m := by rw [heq]
      rw [hz, hns, hga]
      omega
    | inr hlt =>
      have hz : nsZeroAt a g m = g m := nsZeroAt_eq a g m (by omega)
      rw [ih hlt, hz]
      omega

/-- **二点入れ替え不変**: g と h が a, b の二点を除いて一致し、
    その二点の値の和が一致すれば、有限和は等しい。 -/
theorem nsum_two_point_eq (g h : Nat → Nat) (a b n : Nat)
    (hab : ¬ a = b) (ha : a < n) (hb : b < n)
    (hoff : ∀ k, ¬ k = a → ¬ k = b → g k = h k)
    (hpair : g a + g b = h a + h b) :
    nsum g n = nsum h n := by
  have pg1 := nsum_pull_one g a n ha
  have pg2 := nsum_pull_one (nsZeroAt a g) b n hb
  have ph1 := nsum_pull_one h a n ha
  have ph2 := nsum_pull_one (nsZeroAt a h) b n hb
  have zbg : nsZeroAt a g b = g b := nsZeroAt_eq a g b (fun hh => hab hh.symm)
  have zbh : nsZeroAt a h b = h b := nsZeroAt_eq a h b (fun hh => hab hh.symm)
  have hcong : nsum (nsZeroAt b (nsZeroAt a g)) n = nsum (nsZeroAt b (nsZeroAt a h)) n :=
    nsum_congr_lt _ _ n (fun k _ => by
      cases Nat.decEq k b with
      | isTrue hkb =>
        rw [show nsZeroAt b (nsZeroAt a g) k = 0 from by rw [hkb]; exact nsZeroAt_self b _,
            show nsZeroAt b (nsZeroAt a h) k = 0 from by rw [hkb]; exact nsZeroAt_self b _]
      | isFalse hkb =>
        rw [nsZeroAt_eq b (nsZeroAt a g) k hkb, nsZeroAt_eq b (nsZeroAt a h) k hkb]
        cases Nat.decEq k a with
        | isTrue hka =>
          rw [show nsZeroAt a g k = 0 from by rw [hka]; exact nsZeroAt_self a _,
              show nsZeroAt a h k = 0 from by rw [hka]; exact nsZeroAt_self a _]
        | isFalse hka =>
          rw [nsZeroAt_eq a g k hka, nsZeroAt_eq a h k hka]
          exact hoff k hka hkb)
  rw [pg2, zbg, hcong] at pg1
  rw [ph2, zbh] at ph1
  omega

/-! ## Part 2: (Ind1) ラベル置換の QDiv 作用と次数不変 -/

/-- **座標ラベルの置換（互換）を重複度に作用**: 添字 a と b を入れ替える。 -/
def swapMult (a b : Nat) (f : Nat → Nat) (k : Nat) : Nat :=
  if k = a then f b else if k = b then f a else f k

/-- 置換値 at a = f b。 -/
theorem swapMult_left (a b : Nat) (f : Nat → Nat) : swapMult a b f a = f b := by
  show (if a = a then f b else if a = b then f a else f a) = f b
  rw [if_pos rfl]

/-- 置換値 at b = f a（a ≠ b）。 -/
theorem swapMult_right (a b : Nat) (f : Nat → Nat) (hab : ¬ a = b) :
    swapMult a b f b = f a := by
  show (if b = a then f b else if b = b then f a else f b) = f a
  rw [if_neg (fun hh => hab hh.symm), if_pos rfl]

/-- 置換値 at k（k ≠ a, k ≠ b）= f k。 -/
theorem swapMult_other (a b : Nat) (f : Nat → Nat) (k : Nat)
    (hka : ¬ k = a) (hkb : ¬ k = b) : swapMult a b f k = f k := by
  show (if k = a then f b else if k = b then f a else f k) = f k
  rw [if_neg hka, if_neg hkb]

/-- **ラベル置換を QDiv に作用**: 添字 a, b を入れ替えた有効因子。 -/
def swapDiv (a b : Nat) (x : QDiv) : QDiv where
  mult := swapMult a b x.mult
  bound := max x.bound (max (a + 1) (b + 1))
  vanish := fun k hk => by
    show (if k = a then x.mult b else if k = b then x.mult a else x.mult k) = 0
    rw [if_neg (show ¬ k = a by omega), if_neg (show ¬ k = b by omega)]
    exact x.vanish k (by omega)

/-- **本丸 (M254F-a): 等重み座標の置換は次数 degN を保つ** —
    `w a = w b`（正の重みも可）なら、a, b を入れ替えても大域次数は不変。
    互換不変性 `nsum_two_point_eq` を、二点の重み付き値の和の一致
    （`w a·x_b + w b·x_a = w a·x_a + w b·x_b`、等重みなら可換）に帰着。 -/
theorem degN_swap (w : Nat → Nat) (a b : Nat) (x : QDiv)
    (hab : ¬ a = b) (hw : w a = w b) :
    degN w (swapDiv a b x) = degN w x := by
  have hN : x.bound ≤ max x.bound (max (a + 1) (b + 1)) := by omega
  have haN : a < max x.bound (max (a + 1) (b + 1)) := by omega
  have hbN : b < max x.bound (max (a + 1) (b + 1)) := by omega
  show nsum (fun k => w k * swapMult a b x.mult k) (max x.bound (max (a + 1) (b + 1)))
      = degN w x
  rw [← degN_stable w x (max x.bound (max (a + 1) (b + 1))) hN]
  refine nsum_two_point_eq (fun k => w k * swapMult a b x.mult k)
    (fun k => w k * x.mult k) a b _ hab haN hbN ?_ ?_
  · intro k hka hkb
    show w k * swapMult a b x.mult k = w k * x.mult k
    rw [swapMult_other a b x.mult k hka hkb]
  · show w a * swapMult a b x.mult a + w b * swapMult a b x.mult b
        = w a * x.mult a + w b * x.mult b
    rw [swapMult_left, swapMult_right a b x.mult hab, hw]
    exact Nat.add_comm _ _

/-- **本丸 (M254F-a', ℤ 値): 置換は degZ を保つ**。 -/
theorem degZ_swap (w : Nat → Nat) (a b : Nat) (x : QDiv)
    (hab : ¬ a = b) (hw : w a = w b) :
    degZ w (swapDiv a b x) = degZ w x := by
  show ((degN w (swapDiv a b x) : Nat) : Int) = ((degN w x : Nat) : Int)
  rw [degN_swap w a b x hab hw]

/-! ## Part 3: (Ind1) 作用データ PermIndAction（hull を課さない次数不変軌道） -/

/-- **(Ind1) 置換不定性の作用データ**: 像に軌道を与え、その軌道が
    大域次数 degZ を保つ器。M241F の `IndAction` から hull 等次数フィールド
    を落とした形——正の等重み座標の置換は等次数の共通 hull を持たない
    （膨張が必然）ため、次数不変性のみを課す。 -/
structure PermIndAction (w : Nat → Nat) (l : Nat) where
  /-- 軌道 index。 -/
  Ix : Type
  /-- 基点。 -/
  base : Ix
  /-- 像（非定数可）。 -/
  image : Ix → QDiv
  /-- 作用は大域次数を保つ。 -/
  deg_image : ∀ i, degZ w (image i) = degZ w (gaussDiv l)

/-- ラベル置換軌道の像: 基点は `gaussDiv l`、置換側は a, b を入れ替える。 -/
def labelImg (a b l : Nat) : Bool → QDiv
  | false => gaussDiv l
  | true  => swapDiv a b (gaussDiv l)

/-- **(Ind1) の作用実装**: 等重み座標 a, b の置換を QDiv に作用させた
    `PermIndAction`。像は置換で並べ替わる（非定数）が degZ は不変。 -/
def labelPermAction (w : Nat → Nat) (a b l : Nat)
    (hab : ¬ a = b) (hw : w a = w b) : PermIndAction w l where
  Ix := Bool
  base := false
  image := labelImg a b l
  deg_image := fun i => by
    cases i with
    | false => rfl
    | true => exact degZ_swap w a b (gaussDiv l) hab hw

/-- **像は定数でない（(Ind1) 軌道共変性）**: l ≥ 2 で座標 1, 2 を置換
    すると、座標 1 の重複度が 1²（基点）と 2²（置換）で真に食い違う。 -/
theorem labelPerm_orbit (w : Nat → Nat) (l : Nat) (hl : 2 ≤ l) (hw : w 1 = w 2) :
    (labelPermAction w 1 2 l (by omega) hw).image true
      ≠ (labelPermAction w 1 2 l (by omega) hw).image false := by
  intro heq
  have hk : (swapDiv 1 2 (gaussDiv l)).mult 1 = (gaussDiv l).mult 1 :=
    congrArg (fun d => d.mult 1) heq
  have hL : (swapDiv 1 2 (gaussDiv l)).mult 1 = 2 * 2 := by
    show swapMult 1 2 (gaussDiv l).mult 1 = 2 * 2
    rw [swapMult_left]
    show (if 2 ≤ l then 2 * 2 else 0) = 2 * 2
    rw [if_pos hl]
  have hR : (gaussDiv l).mult 1 = 1 * 1 := by
    show (if 1 ≤ l then 1 * 1 else 0) = 1 * 1
    rw [if_pos (show (1 : Nat) ≤ l by omega)]
  rw [hL, hR] at hk
  omega

/-- **capstone (M254F-b): (Ind1) ラベル置換が QDiv に作用する** —
    (1) 置換のもとで Θ-像の軌道は**非定数**、
    (2) しかし作用は**大域次数 degZ を保つ**（等次数葉上の軌道）。
    M241F の (Ind2) 単数（重み0のエタール座標に宿らせた）と異なり、
    (Ind1) は**正の等重み座標**の置換で degZ を保つ真の置換不定性である。 -/
theorem label_indeterminacy_acts (w : Nat → Nat) (l : Nat)
    (hl : 2 ≤ l) (hw : w 1 = w 2) :
    ((labelPermAction w 1 2 l (by omega) hw).image true
        ≠ (labelPermAction w 1 2 l (by omega) hw).image false)
      ∧ (∀ i, degZ w ((labelPermAction w 1 2 l (by omega) hw).image i)
          = degZ w (gaussDiv l)) :=
  ⟨labelPerm_orbit w l hl hw, (labelPermAction w 1 2 l (by omega) hw).deg_image⟩

/-! ## Part 4: (Ind3) 上方包含（上半両立）の膨張作用 -/

/-- **(Ind3) 膨張不定性の作用データ**: (Ind3) UpperCompat（片側包含
    `lo ⊆ hi`）が像を膨張させる器。`base_le_image`（基点像 ⊆ 各像＝
    一方向包含）を課し、次数は**下界を保ったまま単調増加**する
    （等号でなく ⊆ のみ・膨張のみという (Ind3) の一方向性）。 -/
structure ExpandIndAction (w : Nat → Nat) (l : Nat) where
  /-- 軌道 index。 -/
  Ix : Type
  /-- 基点。 -/
  base : Ix
  /-- 像（膨張していく）。 -/
  image : Ix → QDiv
  /-- 一方向包含: 基点像は各像に点毎包含される（膨張のみ）。 -/
  base_le_image : ∀ i, ∀ k, (image base).mult k ≤ (image i).mult k
  /-- 次数は基点像の次数を**下界として**保つ（単調増加）。 -/
  deg_lower : ∀ i, degZ w (image base) ≤ degZ w (image i)

/-- 膨張軌道の像: 基点は `gaussDiv l`、膨張側は座標 k₁ を +m 膨らませる。 -/
def expandOrbitImg (l k₁ m : Nat) : Bool → QDiv
  | false => gaussDiv l
  | true  => qadd (gaussDiv l) (singleDiv k₁ m)

/-- **(Ind3) の作用実装**: UpperCompat の一方向包含を QDiv に作用させた
    `ExpandIndAction`。像は座標 k₁ 方向へ膨張し、次数は下界
    `degZ (gaussDiv l)` を保ったまま w k₁·m だけ単調増加する。 -/
def upperExpandAction (w : Nat → Nat) (l k₁ m : Nat) : ExpandIndAction w l where
  Ix := Bool
  base := false
  image := expandOrbitImg l k₁ m
  base_le_image := fun i k => by
    cases i with
    | false => exact Nat.le_refl _
    | true =>
      show (gaussDiv l).mult k ≤ (gaussDiv l).mult k + (singleDiv k₁ m).mult k
      exact Nat.le_add_right _ _
  deg_lower := fun i => by
    cases i with
    | false => exact Int.le_refl _
    | true =>
      show degZ w (gaussDiv l) ≤ degZ w (qadd (gaussDiv l) (singleDiv k₁ m))
      rw [degZ_add, degZ_single]
      have hnn : (0 : Int) ≤ ((w k₁ * m : Nat) : Int) := Int.natCast_nonneg _
      omega

/-- **膨張軌道は非定数**: m ≥ 1 なら座標 k₁ の重複度が基点と膨張側で
    真に食い違う。 -/
theorem upperExpand_orbit (w : Nat → Nat) (l k₁ m : Nat) (hm : 1 ≤ m) :
    (upperExpandAction w l k₁ m).image true
      ≠ (upperExpandAction w l k₁ m).image false := by
  intro heq
  have hk : (gaussDiv l).mult k₁ + (singleDiv k₁ m).mult k₁ = (gaussDiv l).mult k₁ :=
    congrArg (fun d => d.mult k₁) heq
  have h1 : (singleDiv k₁ m).mult k₁ = m := by
    show (if k₁ = k₁ then m else 0) = m
    rw [if_pos rfl]
  rw [h1] at hk
  omega

/-- **(Ind3) は真に一方向**: 膨張側は基点側に**逆包含されない**
    （`image true ⊆ image false` は成り立たない）。M202F
    `upper_compat_not_symm`（片側 ⊆ のみで逆 ⊇ は破綻）の QDiv 作用版。 -/
theorem upperExpand_not_symm (w : Nat → Nat) (l k₁ : Nat) :
    ¬ (∀ k, ((upperExpandAction w l k₁ 1).image true).mult k
          ≤ ((upperExpandAction w l k₁ 1).image false).mult k) := by
  intro h
  have hk : (gaussDiv l).mult k₁ + (singleDiv k₁ 1).mult k₁ ≤ (gaussDiv l).mult k₁ :=
    h k₁
  have h1 : (singleDiv k₁ 1).mult k₁ = 1 := by
    show (if k₁ = k₁ then 1 else 0) = 1
    rw [if_pos rfl]
  rw [h1] at hk
  omega

/-- **capstone (M254F-c): (Ind3) 上方包含が QDiv に膨張作用する** —
    (1) 膨張軌道は**非定数**、(2) 一方向包含（基点像 ⊆ 各像）、
    (3) 逆包含は破綻（真に一方向）、(4) 次数は下界を保ち単調増加。 -/
theorem upper_indeterminacy_acts (w : Nat → Nat) (l k₁ : Nat) :
    ((upperExpandAction w l k₁ 1).image true
        ≠ (upperExpandAction w l k₁ 1).image false)
      ∧ (∀ i, ∀ k, ((upperExpandAction w l k₁ 1).image false).mult k
          ≤ ((upperExpandAction w l k₁ 1).image i).mult k)
      ∧ (¬ (∀ k, ((upperExpandAction w l k₁ 1).image true).mult k
              ≤ ((upperExpandAction w l k₁ 1).image false).mult k))
      ∧ (∀ i, degZ w ((upperExpandAction w l k₁ 1).image false)
          ≤ degZ w ((upperExpandAction w l k₁ 1).image i)) :=
  ⟨upperExpand_orbit w l k₁ 1 (Nat.le_refl 1),
   (upperExpandAction w l k₁ 1).base_le_image,
   upperExpand_not_symm w l k₁,
   (upperExpandAction w l k₁ 1).deg_lower⟩

/-! ## Part 5: (Ind1)×(Ind2) の同時作用（合成） -/

/-- 合成軌道の像（`Bool × Bool`）: 第一成分 = (Ind1) 置換の有無、
    第二成分 = (Ind2) 単数（重み0座標 k₀ の +1 ずらし）の有無。 -/
def combImg (a b l k₀ : Nat) : Bool × Bool → QDiv
  | (false, false) => gaussDiv l
  | (true,  false) => swapDiv a b (gaussDiv l)
  | (false, true)  => qadd (gaussDiv l) (singleDiv k₀ 1)
  | (true,  true)  => qadd (swapDiv a b (gaussDiv l)) (singleDiv k₀ 1)

/-- **(Ind1)×(Ind2) 同時作用**: 等重み置換（a, b）と単数ずらし（重み0の k₀）を
    `Bool × Bool` 軌道上で同時に QDiv へ作用させた `PermIndAction`。
    どちらの不定性も degZ を保つので合成も degZ 不変。 -/
def combPermAction (w : Nat → Nat) (a b l k₀ : Nat)
    (hab : ¬ a = b) (hw : w a = w b) (hw0 : w k₀ = 0) : PermIndAction w l where
  Ix := Bool × Bool
  base := (false, false)
  image := combImg a b l k₀
  deg_image := fun i => by
    cases i with
    | mk s u =>
      cases s with
      | false =>
        cases u with
        | false => exact rfl
        | true =>
          show degZ w (qadd (gaussDiv l) (singleDiv k₀ 1)) = degZ w (gaussDiv l)
          rw [degZ_add, degZ_single, hw0]
          show degZ w (gaussDiv l) + ((0 * 1 : Nat) : Int) = degZ w (gaussDiv l)
          omega
      | true =>
        cases u with
        | false => exact degZ_swap w a b (gaussDiv l) hab hw
        | true =>
          show degZ w (qadd (swapDiv a b (gaussDiv l)) (singleDiv k₀ 1))
              = degZ w (gaussDiv l)
          rw [degZ_add, degZ_single, hw0]
          show degZ w (swapDiv a b (gaussDiv l)) + ((0 * 1 : Nat) : Int)
              = degZ w (gaussDiv l)
          rw [degZ_swap w a b (gaussDiv l) hab hw]
          omega

/-- **capstone (M254F-d): (Ind1) と (Ind2) が同時に像を動かす** —
    合成 `PermIndAction` の軌道で、(Ind1) 置換成分（(true,false)）と
    (Ind2) 単数成分（(false,true)）が**それぞれ**基点像を動かし、
    かつ全軌道で degZ が不変。複数の不定性の同時軌道共変性。 -/
theorem comb_indeterminacies_act (w : Nat → Nat) (l k₀ : Nat)
    (hl : 2 ≤ l) (hw : w 1 = w 2) (hw0 : w k₀ = 0) :
    ((combPermAction w 1 2 l k₀ (by omega) hw hw0).image (true, false)
        ≠ (combPermAction w 1 2 l k₀ (by omega) hw hw0).image (false, false))
      ∧ ((combPermAction w 1 2 l k₀ (by omega) hw hw0).image (false, true)
          ≠ (combPermAction w 1 2 l k₀ (by omega) hw hw0).image (false, false))
      ∧ (∀ i, degZ w ((combPermAction w 1 2 l k₀ (by omega) hw hw0).image i)
          = degZ w (gaussDiv l)) := by
  refine ⟨?_, ?_, (combPermAction w 1 2 l k₀ (by omega) hw hw0).deg_image⟩
  · intro heq
    have hk : (swapDiv 1 2 (gaussDiv l)).mult 1 = (gaussDiv l).mult 1 :=
      congrArg (fun d => d.mult 1) heq
    have hL : (swapDiv 1 2 (gaussDiv l)).mult 1 = 2 * 2 := by
      show swapMult 1 2 (gaussDiv l).mult 1 = 2 * 2
      rw [swapMult_left]
      show (if 2 ≤ l then 2 * 2 else 0) = 2 * 2
      rw [if_pos hl]
    have hR : (gaussDiv l).mult 1 = 1 * 1 := by
      show (if 1 ≤ l then 1 * 1 else 0) = 1 * 1
      rw [if_pos (show (1 : Nat) ≤ l by omega)]
    rw [hL, hR] at hk
    omega
  · intro heq
    have hk : (gaussDiv l).mult k₀ + (singleDiv k₀ 1).mult k₀ = (gaussDiv l).mult k₀ :=
      congrArg (fun d => d.mult k₀) heq
    have h1 : (singleDiv k₀ 1).mult k₀ = 1 := by
      show (if k₀ = k₀ then 1 else 0) = 1
      rw [if_pos rfl]
    rw [h1] at hk
    omega

/-! ## Part 6: 既存 IndAction（M241F・hull 付き）への橋渡し

    (Ind1) 置換を M241F の `IndAction`（hull 等次数付き）に居住させる。
    正の重みでは互換の点毎上界が等次数 hull を持たない（膨張が必然）ため、
    ここでは**重み0の二座標**で置換し、hull を明示的に据えて等次数に固定する。 -/

/-- ガウス因子の重複度は k² を超えない（互換の hull 構成に使う）。 -/
theorem gaussMult_le (l k : Nat) : (gaussDiv l).mult k ≤ k * k := by
  show (if k ≤ l then k * k else 0) ≤ k * k
  cases Nat.decLe k l with
  | isTrue h => exact Nat.le_of_eq (if_pos h)
  | isFalse h => exact Nat.le_trans (Nat.le_of_eq (if_neg h)) (Nat.zero_le _)

/-- 置換軌道の上界包: 座標 a に b²、座標 b に a² を足して両像を点毎に覆う。
    重み0の a, b では次数増分が消えるので等次数に保たれる。 -/
def labelHull (a b l : Nat) : QDiv :=
  qadd (qadd (gaussDiv l) (singleDiv a (b * b))) (singleDiv b (a * a))

/-- 置換像は labelHull に点毎包含される。 -/
theorem swap_gauss_le_labelHull (a b l : Nat) (hab : ¬ a = b) (k : Nat) :
    swapMult a b (gaussDiv l).mult k ≤ (labelHull a b l).mult k := by
  show swapMult a b (gaussDiv l).mult k
      ≤ ((gaussDiv l).mult k + (singleDiv a (b * b)).mult k) + (singleDiv b (a * a)).mult k
  cases Nat.decEq k a with
  | isTrue hka =>
    rw [hka, swapMult_left]
    have hsa : (singleDiv a (b * b)).mult a = b * b := by
      show (if a = a then b * b else 0) = b * b
      rw [if_pos rfl]
    have hsb : (singleDiv b (a * a)).mult a = 0 := by
      show (if a = b then a * a else 0) = 0
      rw [if_neg hab]
    rw [hsa, hsb]
    have hg := gaussMult_le l b
    omega
  | isFalse hka =>
    cases Nat.decEq k b with
    | isTrue hkb =>
      rw [hkb, swapMult_right a b (gaussDiv l).mult hab]
      have hsa : (singleDiv a (b * b)).mult b = 0 := by
        show (if b = a then b * b else 0) = 0
        rw [if_neg (fun hh => hab hh.symm)]
      have hsb : (singleDiv b (a * a)).mult b = a * a := by
        show (if b = b then a * a else 0) = a * a
        rw [if_pos rfl]
      rw [hsa, hsb]
      have hg := gaussMult_le l a
      omega
    | isFalse hkb =>
      rw [swapMult_other a b (gaussDiv l).mult k hka hkb]
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

/-- **(Ind1) を M241F の IndAction（hull 等次数）に居住させる** —
    重み0の二座標 a, b の置換。像は非定数（`swapDiv` が座標を並べ替える）、
    hull は `labelHull`（両像を覆い、重み0ゆえ等次数）。 -/
def labelIndAction (w : Nat → Nat) (a b l : Nat)
    (hab : ¬ a = b) (hwa : w a = 0) (hwb : w b = 0) : IndAction w l where
  Ix := Bool
  base := false
  image := labelImg a b l
  hull := labelHull a b l
  image_le_hull := fun i k => by
    cases i with
    | false =>
      show (gaussDiv l).mult k
          ≤ ((gaussDiv l).mult k + (singleDiv a (b * b)).mult k)
            + (singleDiv b (a * a)).mult k
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    | true => exact swap_gauss_le_labelHull a b l hab k
  deg_image := fun i => by
    cases i with
    | false => rfl
    | true => exact degZ_swap w a b (gaussDiv l) hab (hwa.trans hwb.symm)
  deg_hull := by
    show degZ w (qadd (qadd (gaussDiv l) (singleDiv a (b * b))) (singleDiv b (a * a)))
        = degZ w (gaussDiv l)
    rw [degZ_add, degZ_add, degZ_single, degZ_single, hwa, hwb]
    show degZ w (gaussDiv l) + ((0 * (b * b) : Nat) : Int) + ((0 * (a * a) : Nat) : Int)
        = degZ w (gaussDiv l)
    omega

/-- **crux ⟹ Cor312（(Ind1) 置換軌道版）**: 重み0座標の置換で非定数化した
    (Ind1) 軌道を持つ `IndAction` を `arithPreRepInd` に差し込み、外部化した
    輸送仮説 hq（基点像 `gaussDiv l` への包含）から系3.12 が従う。 -/
theorem arith_transport_of_label_orbit (w : Nat → Nat) (n l B a b : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hab : ¬ a = b)
    (hwa : w a = 0) (hwb : w b = 0)
    (hq : (frobVol w).le (qPilotDiv n) (gaussDiv l)) :
    Cor312 (arithSkeleton w n l B hl hB) :=
  cor312_of_multiradial
    (arithPreRepInd w n l B hl hB (labelIndAction w a b l hab hwa hwb) ⟨false, hq⟩)

/-! ## Part 7: capstone（総括） -/

/-- **capstone (M254F): (Ind1) ラベル置換・(Ind3) 上方包含膨張の QDiv 作用** —
    (a) (Ind1) 等重み座標の置換は像を非定数化しつつ degZ を厳密に保つ、
    (b) (Ind3) 上方包含は像を一方向に膨張させ、逆包含は破綻し、degZ は下界を保つ、
    (c) (Ind1)×(Ind2) は同時軌道を与えいずれも degZ 不変、
    (d) (Ind1) は M241F の hull 付き IndAction にも居住し crux ⟹ Cor312 を通す。
    M241F の (Ind2) 単独作用から、(Ind1)・(Ind3) の QDiv 作用と (Ind1)×(Ind2)
    同時作用への前進が機械検証された（完全な (Ind1)×(Ind2)×(Ind3) 同時作用・
    crux 単一 Prop 化は次段）。 -/
theorem indActionLabel_wellDefined (w : Nat → Nat) (l k₀ : Nat)
    (hl : 2 ≤ l) (hw : w 1 = w 2) :
    ((labelPermAction w 1 2 l (by omega) hw).image true
        ≠ (labelPermAction w 1 2 l (by omega) hw).image false)
      ∧ (∀ i, degZ w ((labelPermAction w 1 2 l (by omega) hw).image i)
          = degZ w (gaussDiv l))
      ∧ ((upperExpandAction w l k₀ 1).image true
          ≠ (upperExpandAction w l k₀ 1).image false)
      ∧ (∀ i, degZ w ((upperExpandAction w l k₀ 1).image false)
          ≤ degZ w ((upperExpandAction w l k₀ 1).image i)) :=
  ⟨labelPerm_orbit w l hl hw,
   (labelPermAction w 1 2 l (by omega) hw).deg_image,
   upperExpand_orbit w l k₀ 1 (Nat.le_refl 1),
   (upperExpandAction w l k₀ 1).deg_lower⟩

end IUT
