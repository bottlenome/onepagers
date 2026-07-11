/-
  IUT/Q3TatePi1Etale.lean — A4a（柱A A4: 実 π₁^ét の格子方向 pro-l 切片）

  ── 主要成果の分類: **[実／昇格(a)+本物建設(b)]**。A5c `Q3TateCoverTower.lean`
     （実中間被覆 E_{qⁿ}(ℚ₃)→E_q(ℚ₃)・有限デッキ ℤ/n）と M374F `TemperedTower.lean`
     の裸 ℤ_l = lim ℤ/l^k を、**実 Tate 曲線の実被覆塔のデッキ群の逆極限が実曲線族へ
     作用する π₁^ét 対象**として本物化する。A5c 正直な限定(2) が明示 defer した
     「実逆極限の幾何的実現」・A5c 監査ディスカウント(1)「忠実性未証明」を正面で埋める。
     toy 主語なし——主語は実 q3tGrp・実 q3tQ・実 q3tCurve・実 ttwInverseLimit（=Zp l）。

  complete_pct 影響: **A4 0.5→（独立監査確定・§5 見込み 0.55）へ寄与**。realizes
  A5c-deferred「実逆極限の幾何的実現」。内容:
  (i)   塔の隣接段の実被覆 q3peStep: E_{q^{l^{k+1}}} → E_{q^{l^k}}（添字 m·l^{k+1}→m·l^k で
        直接 Quot.lift 降下・Nat 添字キャスト回避）・全射・核、
  (ii)  デッキ遷移の幾何的実現 q3pe_step_deck（段間実被覆が ℤ/l^{k+1} 作用を ℤ/l^k 作用へ運ぶ）、
  (iii) π₁ 対象＝逆極限 ℤ_l の実塔への作用 q3peLimitAct・段間自然性 q3pe_limit_act_natural・
        被覆変換性 q3pe_deck_over、
  (iv)  忠実性 q3pe_fin_faithful（有限段・A5c 監査(1) の discharge）・作用単射 q3pe_fin_act_inj・
        q3pe_limit_faithful（逆極限段・全段自明作用⟹γ=1・choice-free）、
  (v)   ファイバー＝軌道 q3pe_fiber_orbit（中間被覆の Galois 性の完成・A5c は片方向のみ）、
  (vi)  束ね Q3TatePi1EtaleData / q3peData（m=1,l=2 見出し実例）/ q3pePi1_exists。

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
  (6) 既存の正直申告・surrogate は全て残す（M374F 外部仮説・A5c ヘッダ限定 5 項・
      tateProfinite 系 surrogate 本体・profPi1_trivialTower は消さず併設）。
  (7) A4 は 0.55 でもなお 0.5 帯: 上記 1–5 が残る限り「忠実な部分ケース(0.5) を質的に一歩
      超える最初の非自明実インスタンス」以上を主張しない。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3TateCoverTower
import IUT.Q3TateDeck
import IUT.TemperedTower
import IUT.GaloisCategory
import IUT.Profinite
import IUT.Q3TateCurve

namespace IUT

/-! ## q3pe-1: 塔の隣接段の実被覆 E_{q^{l^{k+1}}} → E_{q^{l^k}}（N1） -/

/-- **q3pe-1a（★）: 塔の隣接段の実被覆** — 添字 m·l^{k+1} → m·l^k を直接取り、
    射影 q3tProj (m·l^k) を商 q3tCurve (m·l^{k+1}) を通じて Quot.lift で降下する。
    well-def は q3tc_tower_nested（既にこの添字対で証明済み）そのもの。q3tcHom の合成でなく
    直接添字を取ることで m·l^{k+1} = (m·l^k)·l の型レベル書換を完全回避する（§3.4-1）。 -/
def q3peStep (m l k : Nat) : Hom (q3tCurve (m * l ^ (k + 1))) (q3tCurve (m * l ^ k)) where
  map := Quot.lift (fun a => (q3tProj (m * l ^ k)).map a)
    (fun a b hab => Quot.sound (q3tc_tower_nested m l k (q3tGrp.mul (q3tGrp.inv a) b) hab))
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show (q3tProj (m * l ^ k)).map (q3tGrp.mul a b)
       = (q3tCurve (m * l ^ k)).mul ((q3tProj (m * l ^ k)).map a) ((q3tProj (m * l ^ k)).map b)
    exact (q3tProj (m * l ^ k)).map_mul a b

/-- **q3pe-1b: 塔の隣接段は全射**（q3tProj の全射性の降下）。 -/
theorem q3pe_step_surjective (m l k : Nat) :
    ∀ y, ∃ x, (q3peStep m l k).map x = y := by
  intro y
  induction y using Quot.ind; rename_i b
  exact ⟨Quot.mk _ b, rfl⟩

/-- **q3pe-1c: 段間被覆の核＝(q^{l^k})^ℤ の像**（quotientProjN_ker へ帰着）。 -/
theorem q3pe_step_ker (m l k : Nat) (a : q3tGrp.carrier) :
    (q3peStep m l k).map ((q3tProj (m * l ^ (k + 1))).map a) = (q3tCurve (m * l ^ k)).one
      ↔ (q3tSubgroup (m * l ^ k)).mem a := by
  show (q3tProj (m * l ^ k)).map a = (q3tCurve (m * l ^ k)).one
      ↔ (q3tSubgroup (m * l ^ k)).mem a
  exact quotientProjN_ker q3tGrp (q3tSubgroup (m * l ^ k))
    (q3t_normal (q3tSubgroup (m * l ^ k))) a

/-! ## q3pe-2: デッキ遷移の幾何的実現（N2・★） -/

/-- **q3pe-2（★）: デッキ遷移の幾何的実現** — 段間実被覆 q3peStep はデッキ作用 ℤ/l^{k+1} を
    ℤ/l^k 作用へ運ぶ。M14-6 level_transition_equivariant の実被覆初実例。代表元では両辺が
    同一項 (q3tProj (m·l^k)).map (q^j·a) に畳まれる rfl 級（deck shift は両レベル同じ
    tateZpow q3tGrp (q3tQ m) を使う）。 -/
theorem q3pe_step_deck (m l k : Nat) (j : Int) (x : (q3tCurve (m * l ^ (k + 1))).carrier) :
    (q3peStep m l k).map
        ((q3tcDeckFin m (l ^ (k + 1))).act (Quot.mk (modCong (l ^ (k + 1))).rel j) x)
      = (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l ^ k)).rel j) ((q3peStep m l k).map x) := by
  induction x using Quot.ind; rename_i a
  show (q3tProj (m * l ^ k)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) a)
     = (q3tProj (m * l ^ k)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) a)
  rfl

/-! ## q3pe-3: π₁ 対象＝逆極限 ℤ_l の実塔への作用（N3・★★ ヘッドライン） -/

/-- **q3pe-3a（★★）: π₁ 断片＝実被覆塔のデッキ逆極限 ℤ_l** = ttwInverseLimit l = lim ℤ/l^k。 -/
def q3pePi1 (l : Nat) : Grp := ttwInverseLimit l

/-- **q3pe-3b（★★ ヘッドライン）: 逆極限 ℤ_l の実塔第 k 段への作用** — γ ∈ ℤ_l は
    第 k 成分 γ.val k ∈ ℤ/l^k を通じて実曲線 E_{q^{l^k}}(ℚ₃) に作用する。M14-5 levelAction の
    実昇格（π₁^ét 対象そのものが実曲線族に作用する初実例）。 -/
def q3peLimitAct (m l k : Nat) : GAction (q3pePi1 l) where
  carrier := (q3tCurve (m * l ^ k)).carrier
  act := fun γ x => (q3tcDeckFin m (l ^ k)).act (γ.val k) x
  act_one := fun x => by
    show (q3tcDeckFin m (l ^ k)).act (zmod (l ^ k)).one x = x
    exact (q3tcDeckFin m (l ^ k)).act_one x
  act_mul := fun γ δ x => by
    show (q3tcDeckFin m (l ^ k)).act ((zmod (l ^ k)).mul (γ.val k) (δ.val k)) x
       = (q3tcDeckFin m (l ^ k)).act (γ.val k) ((q3tcDeckFin m (l ^ k)).act (δ.val k) x)
    exact (q3tcDeckFin m (l ^ k)).act_mul (γ.val k) (δ.val k) x

/-- **q3pe-3c（★）: 作用の段間自然性** — π₁ の作用は実被覆塔のファイバー関手の自然変換
    （M14-6 の実主語版）。γ.val k = (zmodTrans …).map (γ.val (k+1))（整合族）＋ Quot.ind で
    代表 j に落として q3pe_step_deck。 -/
theorem q3pe_limit_act_natural (m l k : Nat) (γ : (q3pePi1 l).carrier)
    (x : (q3tCurve (m * l ^ (k + 1))).carrier) :
    (q3peStep m l k).map ((q3peLimitAct m l (k + 1)).act γ x)
      = (q3peLimitAct m l k).act γ ((q3peStep m l k).map x) := by
  have hcompat : (zmodTrans (pow_dvd_mono l (Nat.le_succ k))).map (γ.val (k + 1)) = γ.val k :=
    γ.property (Nat.le_succ k)
  show (q3peStep m l k).map ((q3tcDeckFin m (l ^ (k + 1))).act (γ.val (k + 1)) x)
     = (q3tcDeckFin m (l ^ k)).act (γ.val k) ((q3peStep m l k).map x)
  rw [← hcompat]
  generalize γ.val (k + 1) = g
  induction g using Quot.ind; rename_i j
  exact q3pe_step_deck m l k j x

/-- **q3pe-3d: 極限作用も被覆変換**（E_q 上に恒等を覆う）。Quot.ind (γ.val k) → q3tc_deck_over。 -/
theorem q3pe_deck_over (m l k : Nat) (γ : (q3pePi1 l).carrier)
    (z : (q3tCurve (m * l ^ k)).carrier) :
    (q3tcHom m (l ^ k)).map ((q3peLimitAct m l k).act γ z) = (q3tcHom m (l ^ k)).map z := by
  show (q3tcHom m (l ^ k)).map ((q3tcDeckFin m (l ^ k)).act (γ.val k) z)
     = (q3tcHom m (l ^ k)).map z
  generalize γ.val k = g
  induction g using Quot.ind; rename_i j
  exact q3tc_deck_over m (l ^ k) j z

/-! ## q3pe-4: 忠実性（N4・★ A5c 監査ディスカウント(1) の正面 discharge） -/

/-- **q3pe-4a（★）: 有限段の忠実性** — act(mk j)[1]=[qʲ]=[1] ⟹ n ∣ j。
    quotientProjN_ker（添字 m·n）で qʲ·1 ∈ ⟨q3tQ(m·n)⟩、第1成分 q3td_zpow_fst で
    (m·n)·t = m·j（Int.natCast_mul）、m≥1 の左簡約で n·t = j ⟹ n ∣ j。A5c 監査の明示
    ディスカウント「忠実性/自由性未証明」の正面 discharge。 -/
theorem q3pe_fin_faithful (m n : Nat) (hm : 1 ≤ m) (j : Int)
    (h : (q3tcDeckFin m n).act (Quot.mk (modCong n).rel j) ((q3tCurve (m * n)).one)
           = (q3tCurve (m * n)).one) :
    ((n : Nat) : Int) ∣ j := by
  have hproj : (q3tProj (m * n)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) q3tGrp.one)
      = (q3tCurve (m * n)).one := h
  have hmem : (q3tSubgroup (m * n)).mem
      (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) q3tGrp.one) :=
    (quotientProjN_ker q3tGrp (q3tSubgroup (m * n)) (q3t_normal (q3tSubgroup (m * n)))
      (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) q3tGrp.one)).mp hproj
  obtain ⟨t, ht⟩ := hmem
  have hfst : (tateZpow q3tGrp (q3tQ (m * n)) t).1
      = (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) q3tGrp.one).1 := congrArg Prod.fst ht
  rw [q3td_zpow_fst (m * n) t] at hfst
  have hrfst : (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) q3tGrp.one).1 = (m : Int) * j := by
    show intGrp.mul (tateZpow q3tGrp (q3tQ m) j).1 q3tGrp.one.1 = (m : Int) * j
    rw [q3td_zpow_fst m j]
    show (m : Int) * j + (0 : Int) = (m : Int) * j
    omega
  have key : ((m * n : Nat) : Int) * t = (m : Int) * j := hfst.trans hrfst
  rw [Int.natCast_mul, Int.mul_assoc] at key
  have hnt : (n : Int) * t = j := Int.eq_of_mul_eq_mul_left (by omega) key
  exact ⟨t, hnt.symm⟩

/-- **q3pe-4b: 作用の単射版** — act(mk j)[1] = act(mk j')[1] ⟹ mk j = mk j'（ℤ/n 内）。
    quot_exact で (q^j·1)⁻¹·(q^{j'}·1) = q^{-j+j'} ∈ ⟨q^{mn}⟩ を得て第1成分で n ∣ (j−j')。 -/
theorem q3pe_fin_act_inj (m n : Nat) (hm : 1 ≤ m) (j j' : Int)
    (h : (q3tcDeckFin m n).act (Quot.mk (modCong n).rel j) ((q3tCurve (m * n)).one)
       = (q3tcDeckFin m n).act (Quot.mk (modCong n).rel j') ((q3tCurve (m * n)).one)) :
    Quot.mk (modCong n).rel j = Quot.mk (modCong n).rel j' := by
  have hproj : (q3tProj (m * n)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) q3tGrp.one)
      = (q3tProj (m * n)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j') q3tGrp.one) := h
  have hrel : (q3tSubgroup (m * n)).mem
      (q3tGrp.mul (q3tGrp.inv (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) q3tGrp.one))
        (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j') q3tGrp.one)) :=
    quot_exact q3tGrp
      (normalCong q3tGrp (q3tSubgroup (m * n)) (q3t_normal (q3tSubgroup (m * n)))) hproj
  have hinner :
      q3tGrp.mul (q3tGrp.inv (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) q3tGrp.one))
        (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j') q3tGrp.one)
      = tateZpow q3tGrp (q3tQ m) (-j + j') := by
    rw [q3tc_cancelR (tateZpow q3tGrp (q3tQ m) j) (tateZpow q3tGrp (q3tQ m) j') q3tGrp.one,
      ← tateZpow_neg q3tGrp (q3tQ m) j, ← tateZpow_add q3tGrp (q3tQ m) (-j) j']
  rw [hinner] at hrel
  obtain ⟨s, hs⟩ := hrel
  have hfst : (tateZpow q3tGrp (q3tQ (m * n)) s).1
      = (tateZpow q3tGrp (q3tQ m) (-j + j')).1 := congrArg Prod.fst hs
  rw [q3td_zpow_fst (m * n) s, q3td_zpow_fst m (-j + j'), Int.natCast_mul, Int.mul_assoc] at hfst
  have hcancel : (n : Int) * s = -j + j' := Int.eq_of_mul_eq_mul_left (by omega) hfst
  apply Quot.sound
  show ((n : Nat) : Int) ∣ (j - j')
  refine ⟨-s, ?_⟩
  rw [Int.mul_neg]
  omega

/-- **q3pe-4c（★）: 逆極限段の忠実性** — γ ∈ ℤ_l が全段で実塔に自明に作用するなら γ=1。
    Subtype.ext＋funext k。各段 γ.val k を Quot.ind で mk j に落とし q3pe_fin_faithful で
    l^k ∣ j、Quot.sound で mk j = mk 0 = (zmod (l^k)).one。choice-free（witness は閉形式）。
    ＝ RUBRIC「身代わりでない」: ℤ_l は実作用の群として非退化（実塔の対称性を実際に区別する）。 -/
theorem q3pe_limit_faithful (m l : Nat) (hm : 1 ≤ m) (γ : (q3pePi1 l).carrier)
    (h : ∀ k, (q3peLimitAct m l k).act γ ((q3tCurve (m * l ^ k)).one)
           = (q3tCurve (m * l ^ k)).one) :
    γ = (q3pePi1 l).one := by
  apply Subtype.ext
  funext k
  show γ.val k = (zmod (l ^ k)).one
  have hgen : ∀ (g : (zmod (l ^ k)).carrier),
      (q3tcDeckFin m (l ^ k)).act g ((q3tCurve (m * l ^ k)).one)
        = (q3tCurve (m * l ^ k)).one → g = (zmod (l ^ k)).one := by
    intro g
    induction g using Quot.ind; rename_i j
    intro hg
    have hdvd : ((l ^ k : Nat) : Int) ∣ j := q3pe_fin_faithful m (l ^ k) hm j hg
    apply Quot.sound
    show ((l ^ k : Nat) : Int) ∣ (j - 0)
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨c, by omega⟩
  exact hgen (γ.val k) (h k)

/-! ## q3pe-5: ファイバー＝軌道（N5・★ 中間被覆の Galois 性の完成） -/

/-- **q3pe-5（★）: ファイバー＝軌道** — 中間被覆 q3tcHom のファイバーは ℤ/n 軌道に一致
    （中間被覆が Galois 被覆であることの完成）。A5c は ← 方向（q3tc_deck_over）のみだった——
    → 方向を quot_exact（normalCong）＋ q3td_deck_transitive 写経で補い iff で閉じる。 -/
theorem q3pe_fiber_orbit (m n : Nat) (x y : (q3tCurve (m * n)).carrier) :
    (q3tcHom m n).map x = (q3tcHom m n).map y
      ↔ ∃ j : Int, (q3tcDeckFin m n).act (Quot.mk (modCong n).rel j) x = y := by
  constructor
  · induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    intro hxy
    have hrel : (q3tSubgroup m).mem (q3tGrp.mul (q3tGrp.inv a) b) :=
      quot_exact q3tGrp (normalCong q3tGrp (q3tSubgroup m) (q3t_normal (q3tSubgroup m))) hxy
    obtain ⟨t, ht⟩ := hrel
    refine ⟨t, ?_⟩
    have hb : q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) a = b := by
      rw [ht, q3tGrp.mul_assoc, q3t_comm b a, ← q3tGrp.mul_assoc, q3tGrp.inv_mul, q3tGrp.one_mul]
    show (q3tProj (m * n)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) t) a)
       = (q3tProj (m * n)).map b
    rw [hb]
  · intro hj
    obtain ⟨j, hj⟩ := hj
    rw [← hj]
    exact (q3tc_deck_over m n j x).symm

/-! ## q3pe-6: capstone -/

/-- **q3pe-6a: 実 Tate 曲線の実 π₁^ét 格子切片データ** — π₁ 断片＝実被覆塔のデッキ逆極限
    ℤ_l・実余過滤塔（隣接段全射）・デッキ遷移の幾何実現・逆極限作用の段間自然性・
    逆極限段の忠実性・中間被覆の Galois 性（ファイバー＝軌道）を束ねる。逆極限レベルの
    実 π₁ 断片の初の実現。 -/
structure Q3TatePi1EtaleData where
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
  /-- pi1 ＝ 実被覆塔のデッキ逆極限 ℤ_l = lim ℤ/l^k。 -/
  pi1_eq : pi1 = q3pePi1 l
  /-- 実余過滤塔: 隣接段の実被覆は全射。 -/
  step_surj : ∀ (k : Nat) (y : (q3tCurve (m * l ^ k)).carrier),
      ∃ x, (q3peStep m l k).map x = y
  /-- デッキ遷移の幾何的実現（段間実被覆が ℤ/l^{k+1} 作用を ℤ/l^k 作用へ運ぶ）。 -/
  step_deck : ∀ (k : Nat) (j : Int) (x : (q3tCurve (m * l ^ (k + 1))).carrier),
      (q3peStep m l k).map
          ((q3tcDeckFin m (l ^ (k + 1))).act (Quot.mk (modCong (l ^ (k + 1))).rel j) x)
        = (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l ^ k)).rel j) ((q3peStep m l k).map x)
  /-- 逆極限作用の段間自然性（π₁ 作用＝ファイバー関手の自然変換）。 -/
  act_natural : ∀ (k : Nat) (γ : (q3pePi1 l).carrier)
      (x : (q3tCurve (m * l ^ (k + 1))).carrier),
      (q3peStep m l k).map ((q3peLimitAct m l (k + 1)).act γ x)
        = (q3peLimitAct m l k).act γ ((q3peStep m l k).map x)
  /-- 逆極限段の忠実性（全段自明作用 ⟹ γ=1・非退化性の認証）。 -/
  faithful : ∀ γ : (q3pePi1 l).carrier,
      (∀ k, (q3peLimitAct m l k).act γ ((q3tCurve (m * l ^ k)).one)
              = (q3tCurve (m * l ^ k)).one) → γ = (q3pePi1 l).one
  /-- 中間被覆の Galois 性（ファイバー＝ℤ/l^k 軌道）。 -/
  fiber_orbit : ∀ (k : Nat) (x y : (q3tCurve (m * l ^ k)).carrier),
      (q3tcHom m (l ^ k)).map x = (q3tcHom m (l ^ k)).map y
        ↔ ∃ j : Int, (q3tcDeckFin m (l ^ k)).act (Quot.mk (modCong (l ^ k)).rel j) x = y

/-- **q3pe-6b: 見出し実例 m=1, l=2**（q=3・塔 E_9→E_3→…・デッキ逆極限 ℤ_2）。 -/
def q3peData : Q3TatePi1EtaleData where
  m := 1
  l := 2
  hm := Nat.le_refl 1
  hl := Nat.le_refl 2
  pi1 := q3pePi1 2
  pi1_eq := rfl
  step_surj := fun k y => q3pe_step_surjective 1 2 k y
  step_deck := fun k j x => q3pe_step_deck 1 2 k j x
  act_natural := fun k γ x => q3pe_limit_act_natural 1 2 k γ x
  faithful := fun γ h => q3pe_limit_faithful 1 2 (Nat.le_refl 1) γ h
  fiber_orbit := fun k x y => q3pe_fiber_orbit 1 (2 ^ k) x y

/-- **q3pe-6c: 実 Tate 曲線の実 π₁^ét 格子切片データの存在**（実 ℚ₃^×・実 q=3^m・
    実被覆塔・実逆極限 ℤ_l 作用）。 -/
theorem q3pePi1_exists : Nonempty Q3TatePi1EtaleData := ⟨q3peData⟩

end IUT
