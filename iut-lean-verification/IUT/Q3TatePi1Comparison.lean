/-
  IUT/Q3TatePi1Comparison.lean — A4b（柱A A4: 実 π₁^ét の比較・普遍性・surrogate 主語替え）

  ── 主要成果の分類: **[実／昇格(a)+本物建設(b)]**。A4a `Q3TatePi1Etale.lean`
     （実被覆塔のデッキ逆極限 ℤ_l = q3pePi1 が実曲線族 E_{q^{l^k}}(ℚ₃) へ作用する
     π₁^ét 対象）を土台に、(1) 離散デッキ ℤ（A5a q3tdDeck）と有限デッキ ℤ/l^k の
     等変性、(2) 完備化 ℤ → ℤ_l の作用両立、(3) 逆極限 π₁ 対象の普遍性（limit_universal
     の π₁ 主語への発火）、そして (4) **裸の代理 `tateProfinite = ẑ`（M188F/M195F）を
     Ẑ ↠ ℤ_l（ttwProfiniteToLadic・M374F）経由で実曲線 E_{q^{l^k}}(ℚ₃) に作用させる**
     surrogate 主語替えを本物化する。これは CLAUDE.md §2(a) が昇格例として名指しする
     「Tate surrogate → 実 π₁^ét」の literal な第一歩（作用レベル）。toy 主語なし——
     主語は実 q3tGrp・実 q3tQ・実 q3tCurve・実 ttwInverseLimit（=Zp l）・実 tateProfinite（=ẑ）。

  complete_pct 影響: **A4 comparison/universality/surrogate-promotion に寄与
  （最終数値は独立監査確定・A4a と束ねて §5 見込み 0.55）**。内容:
  (i)   普遍被覆等変性 q3pc_universal_cover_equivariant（離散 ℤ ↔ 有限 ℤ/l^k が q3tProj で
        両立・両辺 [qᵗ·x] の rfl 級）、
  (ii)  完備化作用両立 q3pc_completion_act（(ttwDiscreteComplete l).map t の逆極限作用 ＝
        有限デッキ mk t の作用・(toZp l t).val k = mk t 定義計算）、
  (iii) π₁ 対象の普遍性 q3pc_pi1_universal（limit_universal (padicSystem l) の特化）・
        分解の錐成分作用 q3pc_pi1_act_via_cone、
  (iv)  **surrogate 主語替え q3pcSurrogateAct: GAction tateProfinite**（裸 ẑ が実曲線に作用）・
        段間自然性 q3pc_surrogate_natural・非自明性 q3pc_surrogate_nontrivial、
  (v)   束ね Q3Pi1ComparisonData / q3pcData（m=1,l=2 見出し実例）/ q3pcComparison_exists。

  正直な限定（§4 準拠・消去/弱化しない・既存 surrogate は消さない）:
  (1) 依然 p=3・q=3^m 固定・単一 l の pro-l 切片のみ。ẑ 全体（Π_l ℤ_l）・一般素数・
      一般 Tate パラメータ（単数部つき q）は未達。
  (2) Tate 曲線のみ・しかも compact E_q。A4 title の双曲的曲線/Spec には遠い——IUT 本丸の
      once-punctured 楕円曲線の非可換 tempered π₁（θ-Heisenberg）は範囲外。可換な格子方向の切片。
  (3) π₁^ét の格子方向スライスのみ: μ 方向 ℤ₃(1)（=tmzLimit・A7 計上済み）との積 ẑ(1)×ẑ・
      Weil ペアリング・G_{ℚ₃} 外作用は本ステップで一切構成しない（意図的・二重計上回避）。
  (4) 位相・スキーム・エタールサイト皆無: 「被覆」は K-点群の全射準同型であり、スキームの
      有限エタール射・Berkovich/rigid 被覆理論そのものではない（A5a/A5c 恒久限定(3)(4) 継承）。
      担体は群提示 3^ℤ×ℤ₃^×（A2/A8 恒久限定の継承）。
  (5) Aut(F) 復元・遠アーベルは未接続: GrothendieckGalois の π₁=Aut(F)・M286F モノドロミー同型を
      本実例に適用すること、および TateCoverCat/GaloisCatData への実対象登録は行わない。
      π₁ からの逆再構成（anabelian 方向）はゼロのまま。
  (6) **surrogate は「主語替えの供給」で昇格するのであって、M188F/M195F の自己申告
      （tateProfinite := zhat・裸 ẑ）のヘッダ本文を書き換えない**。既存の正直申告・surrogate は
      全て残す（M374F 外部仮説・A5c ヘッダ限定 5 項・profPi1_trivialTower も消さず併設）。
  (7) A4 は 0.55 でもなお 0.5 帯: 上記 1–5 が残る限り「忠実な部分ケース(0.5) を質的に一歩
      超える最初の非自明実インスタンス」以上を主張しない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3TatePi1Etale
import IUT.Q3TateCoverTower
import IUT.Q3TateDeck
import IUT.TemperedTower
import IUT.TateCoverGroup
import IUT.Profinite
import IUT.Q3TateCurve

namespace IUT

/-! ## q3pc-1: 普遍被覆との比較（N6 前半・★） -/

/-- **q3pc-1（★）: 普遍被覆との等変性** — 普遍デッキ ℤ（A5a q3tdDeck）は各有限段の実デッキ
    ℤ/l^k（q3tcDeckFin）と実被覆 q3tProj を通じて等変。両辺とも代表計算で
    [qᵗ·x]（deck shift は両レベル共通の tateZpow q3tGrp (q3tQ m)）に畳まれる rfl 級。 -/
theorem q3pc_universal_cover_equivariant (m l k : Nat) (t : Int) (x : q3tGrp.carrier) :
    (q3tProj (m * l ^ k)).map ((q3tdDeck m).act t x)
      = (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l ^ k)).rel t)
          ((q3tProj (m * l ^ k)).map x) := by
  show (q3tProj (m * l ^ k)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) x)
     = (q3tProj (m * l ^ k)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) x)
  rfl

/-! ## q3pc-2: 完備化 ℤ → ℤ_l の作用両立（N6 後半・★） -/

/-- **q3pc-2（★）: 完備化の作用両立** — π₁^top 断片 ℤ の完備化像 (ttwDiscreteComplete l).map t
    ＝ toZp l t は、π₁^ét 断片 ℤ_l = q3pePi1 l の中で有限デッキ mk t と同じ幾何作用を与える
    （比較定理の作用レベル実現）。(toZp l t).val k = mk t は定義計算（LocalCFT toZp）。 -/
theorem q3pc_completion_act (m l k : Nat) (t : Int) (x : (q3tCurve (m * l ^ k)).carrier) :
    (q3peLimitAct m l k).act ((ttwDiscreteComplete l).map t) x
      = (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l ^ k)).rel t) x := by
  show (q3tcDeckFin m (l ^ k)).act (((ttwDiscreteComplete l).map t).val k) x
     = (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l ^ k)).rel t) x
  rfl

/-! ## q3pc-3: π₁ 対象の普遍性（limit_universal の π₁ 主語への発火） -/

/-- **q3pc-3a（★）: π₁ 対象 ℤ_l = q3pePi1 l の普遍性** — 各有限段 ℤ/l^k への整合錐を持つ
    任意の群 H は、逆極限 π₁ 断片 ℤ_l を一意に経由する。limit_universal (padicSystem l) の
    π₁ 主語への特化（機構は Profinite.lean で choice-free 済み・witness は閉形式）。 -/
theorem q3pc_pi1_universal (l : Nat) (H : Grp) (c : ∀ k, Hom H (zmod (l ^ k)))
    (hc : ∀ {i j : Nat} (h : i ≤ j) (x : H.carrier),
      (zmodTrans (pow_dvd_mono l h)).map ((c j).map x) = (c i).map x) :
    ∃ u : Hom H (q3pePi1 l),
      (∀ (k : Nat) (x : H.carrier), (ttwLimitProj l k).map (u.map x) = (c k).map x) ∧
      ∀ u' : Hom H (q3pePi1 l),
        (∀ (k : Nat) (x : H.carrier), (ttwLimitProj l k).map (u'.map x) = (c k).map x) →
        ∀ x, u'.map x = u.map x := by
  exact limit_universal (padicSystem l) H c hc

/-- **q3pc-3b: 分解 u の実塔作用 = 錐成分の作用** — 普遍性で得た u : H → ℤ_l を経由した
    実塔作用は、錐成分 c k の直接作用と一致する（(u.map h).val k = (c k).map h の錐条件）。 -/
theorem q3pc_pi1_act_via_cone (m l k : Nat) (H : Grp) (c : ∀ j, Hom H (zmod (l ^ j)))
    (u : Hom H (q3pePi1 l))
    (hu : ∀ (j : Nat) (y : H.carrier), (ttwLimitProj l j).map (u.map y) = (c j).map y)
    (h : H.carrier) (x : (q3tCurve (m * l ^ k)).carrier) :
    (q3peLimitAct m l k).act (u.map h) x = (q3tcDeckFin m (l ^ k)).act ((c k).map h) x := by
  show (q3tcDeckFin m (l ^ k)).act ((u.map h).val k) x
     = (q3tcDeckFin m (l ^ k)).act ((c k).map h) x
  have hv : (u.map h).val k = (c k).map h := hu k h
  rw [hv]

/-! ## q3pc-4: Tate surrogate の主語替え（N7・★ 昇格(a) の名指し例） -/

/-- **q3pc-4a（★）: Tate surrogate の主語替え** — 裸の代理 `tateProfinite = ẑ`（M188F/M195F）が
    Ẑ ↠ ℤ_l（ttwProfiniteToLadic・M374F 既存）を経由して実曲線 E_{q^{l^k}}(ℚ₃) に作用する。
    CLAUDE.md §2(a) 名指し昇格例「Tate surrogate → 実 π₁^ét」の literal な第一歩（作用レベル・
    圏登録 A5d とは別）。act_one/act_mul は ttwProfiniteToLadic が Hom（map_one/map_mul）＋
    q3peLimitAct 側の作用則から。 -/
def q3pcSurrogateAct (m l k : Nat) : GAction tateProfinite where
  carrier := (q3tCurve (m * l ^ k)).carrier
  act := fun σ x => (q3peLimitAct m l k).act ((ttwProfiniteToLadic l).map σ) x
  act_one := fun x => by
    have h1 : (ttwProfiniteToLadic l).map tateProfinite.one = (q3pePi1 l).one :=
      (ttwProfiniteToLadic l).map_one
    show (q3peLimitAct m l k).act ((ttwProfiniteToLadic l).map tateProfinite.one) x = x
    rw [h1]
    exact (q3peLimitAct m l k).act_one x
  act_mul := fun σ τ x => by
    have h2 : (ttwProfiniteToLadic l).map (tateProfinite.mul σ τ)
        = (q3pePi1 l).mul ((ttwProfiniteToLadic l).map σ) ((ttwProfiniteToLadic l).map τ) :=
      (ttwProfiniteToLadic l).map_mul σ τ
    show (q3peLimitAct m l k).act ((ttwProfiniteToLadic l).map (tateProfinite.mul σ τ)) x
       = (q3peLimitAct m l k).act ((ttwProfiniteToLadic l).map σ)
           ((q3peLimitAct m l k).act ((ttwProfiniteToLadic l).map τ) x)
    rw [h2]
    exact (q3peLimitAct m l k).act_mul _ _ x

/-- **q3pc-4b: surrogate 作用の段間自然性** — 裸 ẑ の作用も実被覆塔のファイバー関手の
    自然変換をなす。q3pe_limit_act_natural（A4a）に ttwProfiniteToLadic l σ を代入して帰着。 -/
theorem q3pc_surrogate_natural (m l k : Nat) (σ : tateProfinite.carrier)
    (x : (q3tCurve (m * l ^ (k + 1))).carrier) :
    (q3peStep m l k).map ((q3pcSurrogateAct m l (k + 1)).act σ x)
      = (q3pcSurrogateAct m l k).act σ ((q3peStep m l k).map x) := by
  show (q3peStep m l k).map
        ((q3peLimitAct m l (k + 1)).act ((ttwProfiniteToLadic l).map σ) x)
     = (q3peLimitAct m l k).act ((ttwProfiniteToLadic l).map σ) ((q3peStep m l k).map x)
  exact q3pe_limit_act_natural m l k ((ttwProfiniteToLadic l).map σ) x

/-- **q3pc-4c（★）: surrogate 作用は非自明** — σ = toZhat 1 の像・x = [1] で作用が動く
    （身代わりでない）。2 ≤ l^k のとき q3pe_fin_faithful（A4a）で l^k ∤ 1 を用いて分離。
    昇格された surrogate ẑ が実曲線を実際に動かす（非退化な実作用の）認証。 -/
theorem q3pc_surrogate_nontrivial (m l k : Nat) (hm : 1 ≤ m) (hlk : 2 ≤ l ^ k) :
    ∃ (σ : tateProfinite.carrier) (x : (q3pcSurrogateAct m l k).carrier),
      (q3pcSurrogateAct m l k).act σ x ≠ x := by
  refine ⟨toZhat.map 1, (q3tCurve (m * l ^ k)).one, ?_⟩
  intro hcontra
  have h : (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l ^ k)).rel 1)
      ((q3tCurve (m * l ^ k)).one) = (q3tCurve (m * l ^ k)).one := hcontra
  have hdvd : ((l ^ k : Nat) : Int) ∣ (1 : Int) := q3pe_fin_faithful m (l ^ k) hm 1 h
  have hdvd' : ((l ^ k : Nat) : Int) ∣ ((1 : Nat) : Int) := hdvd
  have hnat : (l ^ k) ∣ (1 : Nat) := Int.ofNat_dvd.mp hdvd'
  have hone : l ^ k = 1 := Nat.dvd_one.mp hnat
  omega

/-! ## q3pc-5: capstone -/

/-- **q3pc-5a: 実 π₁^ét 比較データ** — π₁ 断片 ℤ_l = q3pePi1・surrogate ẑ = tateProfinite・
    普遍被覆等変性・完備化作用両立（＋離散部の忠実埋め込み）・surrogate 段間自然性・
    surrogate 非自明性を束ねる。逆極限 π₁ 対象の普遍的・比較的特徴付けと、裸 surrogate の
    実曲線への主語替えの初の実現。 -/
structure Q3Pi1ComparisonData where
  /-- Tate パラメータの指数 m（q = 3^m）。 -/
  m : Nat
  /-- 被覆度 l（≥ 2）。 -/
  l : Nat
  /-- m ≥ 1（真の退化パラメータ）。 -/
  hm : 1 ≤ m
  /-- l ≥ 2（非自明塔・l 進分離性）。 -/
  hl : 2 ≤ l
  /-- π₁ 断片。 -/
  pi1 : Grp
  /-- pi1 ＝ 実被覆塔のデッキ逆極限 ℤ_l = q3pePi1 l。 -/
  pi1_eq : pi1 = q3pePi1 l
  /-- 裸の副有限代理（M188F/M195F の tateProfinite = ẑ）。 -/
  surrogate : Grp
  /-- surrogate ＝ tateProfinite（ヘッダ本文を書き換えず主語替えのみ供給）。 -/
  surrogate_eq : surrogate = tateProfinite
  /-- 普遍被覆 ℤ と有限デッキ ℤ/l^k は q3tProj を通じて等変。 -/
  universal_equivariant : ∀ (k : Nat) (t : Int) (x : q3tGrp.carrier),
      (q3tProj (m * l ^ k)).map ((q3tdDeck m).act t x)
        = (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l ^ k)).rel t)
            ((q3tProj (m * l ^ k)).map x)
  /-- 完備化 ℤ → ℤ_l の逆極限作用は有限デッキ mk t の作用に一致。 -/
  completion_act : ∀ (k : Nat) (t : Int) (x : (q3tCurve (m * l ^ k)).carrier),
      (q3peLimitAct m l k).act ((ttwDiscreteComplete l).map t) x
        = (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l ^ k)).rel t) x
  /-- 離散部の完備化 ℤ ↪ ℤ_l は単射（π₁^top 断片が π₁^ét 断片に忠実に埋まる）。 -/
  completion_inj : (ttwDiscreteComplete l).Injective
  /-- surrogate 作用は実被覆塔の段間で自然（ファイバー関手の自然変換）。 -/
  surrogate_natural : ∀ (k : Nat) (σ : tateProfinite.carrier)
      (x : (q3tCurve (m * l ^ (k + 1))).carrier),
      (q3peStep m l k).map ((q3pcSurrogateAct m l (k + 1)).act σ x)
        = (q3pcSurrogateAct m l k).act σ ((q3peStep m l k).map x)
  /-- surrogate 作用は非自明（2 ≤ l^k の各段で身代わりでない）。 -/
  surrogate_nontrivial : ∀ (k : Nat), 2 ≤ l ^ k →
      ∃ (σ : tateProfinite.carrier) (x : (q3pcSurrogateAct m l k).carrier),
        (q3pcSurrogateAct m l k).act σ x ≠ x

/-- **q3pc-5b: 見出し実例 m=1, l=2**（q=3・塔 E_9→E_3→…・逆極限 ℤ_2・surrogate ẑ）。 -/
def q3pcData : Q3Pi1ComparisonData where
  m := 1
  l := 2
  hm := Nat.le_refl 1
  hl := Nat.le_refl 2
  pi1 := q3pePi1 2
  pi1_eq := rfl
  surrogate := tateProfinite
  surrogate_eq := rfl
  universal_equivariant := fun k t x => q3pc_universal_cover_equivariant 1 2 k t x
  completion_act := fun k t x => q3pc_completion_act 1 2 k t x
  completion_inj := ttw_discrete_complete_injective 2 (Nat.le_refl 2)
  surrogate_natural := fun k σ x => q3pc_surrogate_natural 1 2 k σ x
  surrogate_nontrivial := fun k hlk => q3pc_surrogate_nontrivial 1 2 k (Nat.le_refl 1) hlk

/-- **q3pc-5c: 実 π₁^ét 比較データの存在**（実 ℚ₃^×・実 q=3^m・実逆極限 ℤ_2 作用・
    実 surrogate ẑ の主語替え）。 -/
theorem q3pcComparison_exists : Nonempty Q3Pi1ComparisonData := ⟨q3pcData⟩

end IUT
