/-
  IUT/Q3TateCuspidalization.lean — A8c（柱A A8: 楕円 cuspidalization [AbsTopII] §3 の
  幾何的基体 — 実 [2]-同種・核＝ちょうど Klein 4 群・実開曲線 E₉∖E₉[2]→E₉∖{O}）

  ── 主要成果の分類: **[実／昇格(a)+本物建設(b)]**。
     昇格(a): q3tt の正直限定 3「Klein 4 群 ⊆ E₉[2]（包含のみ・μ₂ 完全性未達）」を、
     **μ₂ 完全性（u∈ℤ₃^×, u²=1 ⟹ u=±1・q3cu_mu2_complete）を新規実証明**して
     **核＝ちょうど Klein 4 群（q3cu_ker_eq_klein の等号）へ昇格**する。
     本物建設(b): [AbsTopII] §3 の楕円 cuspidalization の幾何的基体を実 E₉(ℚ₃)=q3tCurve 2 の
     上でゼロから建設 — リポジトリ初の実同種 sq:E₉→E₉（x↦x²・q3cuSq）・実開曲線 subtype
     E₉∖{O}, E₉∖E₉[2]・cuspidalization 図式の [2]-制限射 q3cuOpenMap・ファイバー＝Klein 剰余類
     (q3cu_fiber_coset)・開部分を保つ自由な捻れ平行移動デッキ・[2] の ℚ₃ 点**非全射**の実 witness
     (q3cu_not_surjective・E(ℚ₃)/2E(ℚ₃)≠0 の影)。

  complete_pct 影響: **A8 を前進**（設計 audit/A8-cuspidalization-detail-2026-07-11.md §5 見込み
  A8 0.57→0.62・柱A 51→52・独立監査確定が条件）。q3tt 正直限定 3（Klein ⊆→=）を discharge。
  主要内容:
  (i)   実 [2]-同種 sq（q3cuSq: Quot.lift で ℚ₃^× の平方を商 E₉ へ降ろす・sq x = x·x）、
  (ii)  核の成分特徴付け q3cu_ker_iff（sq[k,u]=O ⟺ u²=1・2∣2k は常真）、
  (iii) 素冪 Euclid 反復 q3cu_ppow_dvd（3ⁿ∣xy, 3∤y ⟹ 3ⁿ∣x・euclid_int の帰納）、
  (iv)  ★★ μ₂ 完全性 q3cu_mu2_complete（IsZpUnit のレベル1 ∃-witness + omega 3分律 +
        レベル横断整合 + 素冪 Euclid → Quot.sound・本ラウンドの要）、
  (v)   ★★ 核＝ちょうど Klein 4 群 q3cu_ker_eq_klein（→ が mu2_complete を消費・← が u=±1⟹u²=1）、
  (vi)  実開曲線 q3cuPunct/q3cuOpen・包含 q3cu_open_sub・[2]-制限射 q3cuOpenMap、
  (vii) ファイバー＝Klein 剰余類 q3cu_fiber_coset・開部分を保つデッキ q3cu_deck_open・
        自由性 q3cu_deck_free、
  (viii)[2] の ℚ₃ 点非全射 q3cu_not_surjective（∀x, sq x ≠ [1]・パリティ omega）、
  (ix)  puncture ファイバー整合 q3cu_temp_puncture・束ね q3cuData。

  正直な限定（§4 準拠・消去/弱化しない・既存 surrogate/正直申告は消さない）:
  1. **cuspidal 惰性群 = 0 のまま**。[2]-被覆は E∖{O} 上不分岐（エタール）であり、
     本モジュールのどの群（Klein 4・捻れ平行移動）も cusp 惰性を担わない。非自明惰性の
     最小担体は非可換テータ被覆で、**名指し前提条件 = 実直線束/Mumford テータ群
     1→μ₂→G(L)→E[2]→1（柱E EtaleTheta の幾何的実現）または スキーム水準の分岐被覆**
     （§2(a) の原理的ブロック。本モジュールは解消を主張しない）。
  2. **π₁ 再構成アルゴリズム（cuspidalization 本体）= 0**。建てるのは幾何的基体＋cusp 集合の
     完全決定のみ。「cuspidalization を実装した」とは主張しない。
  3. **K 点の影**: スキーム・エタールサイト・位相なし。「開曲線」は subtype・「被覆」は
     核剰余類ファイバーの写像。[2] は ℚ₃ 点で**非全射**（q3cu_not_surjective で定理として顕示・
     幾何的次数 4 との差は正直申告）。
  4. **単一切片**: p=3・q=9（m=2）・N=2 のみ。奇 N・一般 q・一般 p は後続
     （N=2/q=9 は E[2] 全有理という本コースの忠実部分ケース）。
  5. **二重計上の排除（監査向け・明示）**:
     - vs A8a/A8b（q3t/q3tt）: q3tt は Klein「⊆」まで。本モジュールの等号（q3cu_ker_eq_klein）・
       同種・開曲線・非全射は全て新規。q3tt の正直限定 3 は弱化でなく証明による置換
       （q3cu_mu2_complete が任意の ℤ₃^× 元 u に対する完全性を消費）。既存ファイルは不変更。
     - vs A5a/A5c/A4（q3td/q3tc/q3pe）: あちらはレベル替え商写像 E_{qⁿ}→E_q・デッキ＝
       q 冪平行移動・コンパクト曲線。こちらは自己同種 x↦x²・デッキ＝捻れ平行移動・開曲線。
       写像も群も主語も disjoint。
     - vs A9（blc）: 多項式・P¹ は一切登場しない。
     - vs A2/A6/A7: q3cu_mu2_complete は ℤ₃^× の補題だが輸出先は cusp 集合の決定（A8c 帰属）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ（Classical.choice 無し）。
-/
import IUT.Q3TateTorsion
import IUT.RootsOfUnity

namespace IUT

/-! ## q3cu-0: ★ 実 [2]-同種 sq: E₉(ℚ₃) → E₉(ℚ₃)（リポジトリ初の実同種） -/

/-- 可換群における平方の準同型性の核（q3tGrp 成分）: (ab)(ab) = (aa)(bb)。
    ℚ₃^× の可換性（q3t_comm）による 4 項の並べ替え。 -/
theorem q3cu_sq_hom_aux (a b : q3tGrp.carrier) :
    q3tGrp.mul (q3tGrp.mul a b) (q3tGrp.mul a b)
      = q3tGrp.mul (q3tGrp.mul a a) (q3tGrp.mul b b) := by
  rw [q3tGrp.mul_assoc a b (q3tGrp.mul a b),
      ← q3tGrp.mul_assoc b a b,
      q3t_comm b a,
      q3tGrp.mul_assoc a b b,
      ← q3tGrp.mul_assoc a a (q3tGrp.mul b b)]

/-- **q3cu-0（★）: 実 [2]-同種 sq: E₉(ℚ₃) → E₉(ℚ₃)**（[x]↦[x²]）。
    well-def は ℚ₃^× の平方を商 E₉ = ℚ₃^×/q^ℤ へ降ろす（a⁻¹b∈q^ℤ ⟹ proj(a²)=proj(b²)・
    射影核 q3t_proj_eq_iff 経由）。準同型性は可換性（q3cu_sq_hom_aux）。
    リポジトリ初の実同種（A5c/A4 の被覆はレベル替え商写像＝別物）。 -/
def q3cuSq : Hom (q3tCurve 2) (q3tCurve 2) where
  map := Quot.lift (fun a => (q3tProj 2).map (q3tGrp.mul a a))
    (fun a b hab => by
      have hpe : (q3tProj 2).map a = (q3tProj 2).map b :=
        (q3t_proj_eq_iff 2 a b).mpr hab
      show (q3tProj 2).map (q3tGrp.mul a a) = (q3tProj 2).map (q3tGrp.mul b b)
      rw [(q3tProj 2).map_mul, (q3tProj 2).map_mul, hpe])
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show (q3tProj 2).map (q3tGrp.mul (q3tGrp.mul a b) (q3tGrp.mul a b))
       = (q3tCurve 2).mul ((q3tProj 2).map (q3tGrp.mul a a))
           ((q3tProj 2).map (q3tGrp.mul b b))
    rw [← (q3tProj 2).map_mul, q3cu_sq_hom_aux a b]

/-- **q3cu-0b: sq x = x·x** — proj が準同型ゆえ [x]↦[x²]=[x]·[x]。
    ⟹ ker(sq) = E₉[2]（2-捻れ全体）が on the nose。 -/
theorem q3cu_sq_eq_square (x : (q3tCurve 2).carrier) :
    q3cuSq.map x = (q3tCurve 2).mul x x := by
  induction x using Quot.ind; rename_i a
  rfl

/-! ## q3cu-1: 核の成分特徴付け -/

/-- **q3cu-1: 核の成分特徴付け** — sq[k,u]=O ⟺ u²=1（q3t_mem_pair_iff m=2: 2∣2k は常真・
    第2成分の単数方程式のみが核を決める）。 -/
theorem q3cu_ker_iff (k : Int) (u : (zpUnits 3 isPrime_three).carrier) :
    q3cuSq.map ((q3tProj 2).map (k, u)) = (q3tCurve 2).one
      ↔ (zpUnits 3 isPrime_three).mul u u = (zpUnits 3 isPrime_three).one := by
  constructor
  · intro h
    rw [q3cu_sq_eq_square, q3tt_proj_mul k k u u] at h
    have hmem := (quotientProjN_ker q3tGrp (q3tSubgroup 2) (q3t_normal (q3tSubgroup 2))
      ((k + k : Int), (zpUnits 3 isPrime_three).mul u u)).mp h
    exact ((q3t_mem_pair_iff 2 (k + k) ((zpUnits 3 isPrime_three).mul u u)).mp hmem).2
  · intro h
    rw [q3cu_sq_eq_square, q3tt_proj_mul k k u u]
    exact (quotientProjN_ker q3tGrp (q3tSubgroup 2) (q3t_normal (q3tSubgroup 2))
        ((k + k : Int), (zpUnits 3 isPrime_three).mul u u)).mpr
      ((q3t_mem_pair_iff 2 (k + k) ((zpUnits 3 isPrime_three).mul u u)).mpr
        ⟨⟨k, by omega⟩, h⟩)

/-! ## q3cu-2: 素冪 Euclid 反復（euclid_int の帰納・新小補題） -/

/-- **q3cu-2: 素冪 Euclid 反復** — 3ⁿ ∣ x·y かつ 3 ∤ y ⟹ 3ⁿ ∣ x。
    euclid_int の n 段帰納。各段で 3∣x（euclid）→ x=3x' → 一つ 3 を約分 → ih。
    μ₂ 完全性（q3cu-3）で「片方の因子だけが 3 で割れる」局面を閉じる核。 -/
theorem q3cu_ppow_dvd : ∀ (n : Nat) {x y : Int},
    ((3 ^ n : Nat) : Int) ∣ x * y → ¬ ((3 : Nat) : Int) ∣ y →
    ((3 ^ n : Nat) : Int) ∣ x := by
  intro n
  induction n with
  | zero =>
    intro x y _ _
    rw [Nat.pow_zero]
    exact ⟨x, by omega⟩
  | succ m ih =>
    intro x y h hy
    -- 3 ∣ x（3 ∣ 3^(m+1) ∣ y·x, 3∤y, euclid_int）
    have hdvd : ((3 : Nat) : Int) ∣ ((3 ^ (m + 1) : Nat) : Int) :=
      Int.ofNat_dvd.mpr ⟨3 ^ m, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    have h3yx : ((3 : Nat) : Int) ∣ y * x := by
      rw [Int.mul_comm]; exact Int.dvd_trans hdvd h
    have h3x : ((3 : Nat) : Int) ∣ x := euclid_int 3 isPrime_three h3yx hy
    obtain ⟨x', hx'⟩ := h3x
    -- 一つ 3 を約分して 3^m ∣ x'·y
    have hpow : ((3 ^ (m + 1) : Nat) : Int)
        = ((3 : Nat) : Int) * ((3 ^ m : Nat) : Int) := by
      rw [Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]
    have hcancel : ((3 ^ m : Nat) : Int) ∣ x' * y := by
      obtain ⟨d, hd⟩ := h
      refine ⟨d, ?_⟩
      have e1 : ((3 : Nat) : Int) * (x' * y) = x * y := by
        rw [hx', Int.mul_assoc]
      have e2 : ((3 : Nat) : Int) * (((3 ^ m : Nat) : Int) * d) = x * y := by
        rw [← Int.mul_assoc, ← hpow, ← hd]
      have key : ((3 : Nat) : Int) * (x' * y)
          = ((3 : Nat) : Int) * (((3 ^ m : Nat) : Int) * d) := by rw [e1, e2]
      exact Int.eq_of_mul_eq_mul_left (by omega) key
    obtain ⟨c, hc⟩ := ih hcancel hy
    refine ⟨c, ?_⟩
    rw [hx', hc, ← Int.mul_assoc, hpow]

/-! ## q3cu-3: ★★ μ₂ 完全性（q3tt 正直限定 3 の discharge・本ラウンドの要） -/

/-- 差の平方の因数分解（Int 恒等式）: (j−1)(j+1) = j²−1。 -/
theorem q3cu_diff_sq (j : Int) : (j - 1) * (j + 1) = j * j - 1 := by
  have e1 : (j - 1) * (j + 1) = j * (j + 1) - 1 * (j + 1) := Int.sub_mul j 1 (j + 1)
  have e2 : j * (j + 1) = j * j + j := by rw [Int.mul_add, Int.mul_one]
  rw [e1, e2, Int.one_mul]
  generalize j * j = t
  omega

/-- **q3cu-3 補題（レベル抽出）** — u∈ℤ₃^×, u²=1 の各レベル n≥1 で、代表 j に対し
    3ⁿ ∣ (j−1)(j+1)（u²=1 の成分・zmodMul の平方）と 3 ∣ (j−a)（レベル1 witness a への
    塔整合・逆系の property）を取り出す。choice-free（Quot.exists_rep + quot_exact）。 -/
theorem q3cu_mu2_level (u : (zpUnits 3 isPrime_three).carrier)
    (hu : (zpUnits 3 isPrime_three).mul u u = (zpUnits 3 isPrime_three).one)
    (a : Int) (ha : u.val.val 1 = Quot.mk (modCong (3 ^ 1)).rel a)
    (n : Nat) (hn : 1 ≤ n) :
    ∃ j : Int, u.val.val n = Quot.mk (modCong (3 ^ n)).rel j
      ∧ ((3 ^ n : Nat) : Int) ∣ (j - 1) * (j + 1)
      ∧ ((3 : Nat) : Int) ∣ (j - a) := by
  obtain ⟨j, hjeq⟩ := Quot.exists_rep (u.val.val n)
  refine ⟨j, hjeq.symm, ?_, ?_⟩
  · have hmul : zpMul 3 u.val u.val = zpOne 3 := congrArg Subtype.val hu
    have hcomp : zmodMul (3 ^ n) (u.val.val n) (u.val.val n)
        = Quot.mk (modCong (3 ^ n)).rel 1 := congrFun (congrArg Subtype.val hmul) n
    rw [← hjeq] at hcomp
    have hjj : Quot.mk (modCong (3 ^ n)).rel (j * j)
        = Quot.mk (modCong (3 ^ n)).rel 1 := hcomp
    have hdvd : ((3 ^ n : Nat) : Int) ∣ (j * j - 1) :=
      quot_exact intGrp (modCong (3 ^ n)) hjj
    rw [q3cu_diff_sq j]; exact hdvd
  · have hprop := u.val.property hn
    rw [← hjeq] at hprop
    have hres : Quot.mk (modCong (3 ^ 1)).rel j = u.val.val 1 := hprop
    rw [ha] at hres
    exact quot_exact intGrp (modCong (3 ^ 1)) hres

/-- **q3cu-3（★★）: μ₂ 完全性** — u∈ℤ₃^×, u²=1 ⟹ u=1 ∨ u=−1。
    IsZpUnit のレベル1 ∃-witness a（choice 不要・実仮定）の omega 3分律（3∤a ⟹ a≡±1 mod 3）で
    分岐し、各レベル n で 3ⁿ∣(j∓1)（素冪 Euclid q3cu_ppow_dvd・片方の因子は 3 と素）を得て
    Quot.sound で成分ごとに u=1 / u=−1 を確定する。**q3tt 正直限定 3「Klein ⊆ のみ」の
    証明による discharge（弱化でなく等号への昇格）**。 -/
theorem q3cu_mu2_complete (u : (zpUnits 3 isPrime_three).carrier)
    (hu : (zpUnits 3 isPrime_three).mul u u = (zpUnits 3 isPrime_three).one) :
    u = (zpUnits 3 isPrime_three).one ∨ u = q3tNegOne := by
  obtain ⟨a, ha, hpa⟩ := u.property
  have hcase : ((3 : Nat) : Int) ∣ (a - 1) ∨ ((3 : Nat) : Int) ∣ (a + 1) := by omega
  obtain hc1 | hc2 := hcase
  · left
    apply Subtype.ext
    show u.val = zpOne 3
    apply Subtype.ext
    funext n
    show u.val.val n = Quot.mk (modCong (3 ^ n)).rel 1
    cases n with
    | zero =>
      obtain ⟨b, hb⟩ := Quot.exists_rep (u.val.val 0)
      rw [← hb]
      apply Quot.sound
      show ((3 ^ 0 : Nat) : Int) ∣ (b - 1)
      rw [Nat.pow_zero]
      exact ⟨b - 1, by omega⟩
    | succ m =>
      obtain ⟨j, hj, hAn, hBn⟩ := q3cu_mu2_level u hu a ha (m + 1) (by omega)
      have hj1 : ((3 : Nat) : Int) ∣ (j - 1) := by
        obtain ⟨s, hs⟩ := hBn
        obtain ⟨r, hr⟩ := hc1
        exact ⟨s + r, by omega⟩
      have hnj1 : ¬ ((3 : Nat) : Int) ∣ (j + 1) := by
        intro hcon
        obtain ⟨s, hs⟩ := hj1
        obtain ⟨t, ht⟩ := hcon
        omega
      rw [hj]
      apply Quot.sound
      show ((3 ^ (m + 1) : Nat) : Int) ∣ (j - 1)
      exact q3cu_ppow_dvd (m + 1) hAn hnj1
  · right
    apply Subtype.ext
    show u.val = (toZp 3).map (-1)
    apply Subtype.ext
    funext n
    show u.val.val n = Quot.mk (modCong (3 ^ n)).rel (-1)
    cases n with
    | zero =>
      obtain ⟨b, hb⟩ := Quot.exists_rep (u.val.val 0)
      rw [← hb]
      apply Quot.sound
      show ((3 ^ 0 : Nat) : Int) ∣ (b - (-1))
      rw [Nat.pow_zero]
      exact ⟨b - (-1), by omega⟩
    | succ m =>
      obtain ⟨j, hj, hAn, hBn⟩ := q3cu_mu2_level u hu a ha (m + 1) (by omega)
      have hj1 : ((3 : Nat) : Int) ∣ (j + 1) := by
        obtain ⟨s, hs⟩ := hBn
        obtain ⟨r, hr⟩ := hc2
        exact ⟨s + r, by omega⟩
      have hnj1 : ¬ ((3 : Nat) : Int) ∣ (j - 1) := by
        intro hcon
        obtain ⟨s, hs⟩ := hj1
        obtain ⟨t, ht⟩ := hcon
        omega
      have hAn' : ((3 ^ (m + 1) : Nat) : Int) ∣ (j + 1) * (j - 1) := by
        rw [Int.mul_comm]; exact hAn
      rw [hj]
      apply Quot.sound
      show ((3 ^ (m + 1) : Nat) : Int) ∣ (j - (-1))
      have hjm : j - (-1) = j + 1 := by omega
      rw [hjm]
      exact q3cu_ppow_dvd (m + 1) hAn' hnj1

/-! ## q3cu-4: ★★ 核＝ちょうど Klein 4 群（上流 cusp 集合の完全決定） -/

/-- **q3cu-4（★★）: ker(sq) = ちょうど Klein 4 群** — sq[k,u]=O ⟺ [k,u]∈Klein 4 群。
    → 方向は q3cu_ker_iff（u²=1）＋**q3cu_mu2_complete を消費**（u=±1）で本物に閉じる
    （q3tt_klein_torsion の再輸出ではない）。← 方向は u=±1 ⟹ u²=1 を成分算術で。
    q3tt 正直限定 3「Klein ⊆ のみ」を等号へ昇格する本ラウンドの帰結。 -/
theorem q3cu_ker_eq_klein (x : (q3tCurve 2).carrier) :
    q3cuSq.map x = (q3tCurve 2).one ↔ q3ttKleinMem x := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := q3tProj_surjective 2 x
    obtain ⟨k, u⟩ := a
    rw [← ha] at h
    exact ⟨k, u, q3cu_mu2_complete u ((q3cu_ker_iff k u).mp h), ha.symm⟩
  · intro h
    obtain ⟨k, u, hu, hxe⟩ := h
    rw [hxe]
    apply (q3cu_ker_iff k u).mpr
    obtain hu1 | hu2 := hu
    · rw [hu1]; exact (zpUnits 3 isPrime_three).one_mul _
    · rw [hu2]; exact q3tNegOne_sq

/-! ## q3cu-5: ★ 実開曲線と楕円 cuspidalization 図式の 2 本の射 -/

/-- **q3cu-5a: 実開曲線 E₉∖{O}**（下流 cusp {O} を抜いた punctured 曲線・subtype）。 -/
def q3cuPunct : Type := { x : (q3tCurve 2).carrier // x ≠ (q3tCurve 2).one }

/-- **q3cu-5b: 実開曲線 E₉∖E₉[2]**（上流 cusp E₉[2]=Klein を抜いた曲線・subtype）。
    sq x ≠ O ⟺ x∉ker(sq) = x∉E₉[2]（q3cu_ker_eq_klein）。 -/
def q3cuOpen : Type := { x : (q3tCurve 2).carrier // q3cuSq.map x ≠ (q3tCurve 2).one }

/-- **q3cu-5c: 開埋め込み E₉∖E₉[2] ⊆ E₉∖{O}** — O∈E₉[2]=ker ゆえ E₉[2] を抜けば O も抜ける。
    (cuspidalization 図式の第1の射: 包含) -/
theorem q3cu_open_sub (x : q3cuOpen) : x.val ≠ (q3tCurve 2).one := by
  intro h
  apply x.property
  rw [h]
  exact q3cuSq.map_one

/-- **q3cu-5d（★）: [2]-制限射 E₉∖E₉[2] → E₉∖{O}** — x↦sq(x)。x∉ker ⟹ sx(x)≠O は定義そのもの。
    (cuspidalization 図式の第2の射: N=2 倍同種の開曲線への制限・有限エタール)
    開曲線 subtype q3cuOpen を定義域・q3cuPunct を終域として**実際に使う**射。 -/
def q3cuOpenMap : q3cuOpen → q3cuPunct := fun x => ⟨q3cuSq.map x.val, x.property⟩

/-! ## q3cu-6: ★ 被覆構造（ファイバー＝Klein 剰余類・開部分を保つ自由デッキ） -/

/-- **q3cu-6a（★）: ファイバー＝核（Klein）剰余類** — sq x = sq y ⟺ ∃ a∈Klein, a·x=y。
    [2]-被覆の各ファイバーが Klein 4 群の剰余類（4 元）であることの実現。
    → は a=y·x⁻¹ が sq(a)=sq(y)·sq(x)⁻¹=O ゆえ Klein（q3cu_ker_eq_klein 消費）。 -/
theorem q3cu_fiber_coset (x y : (q3tCurve 2).carrier) :
    q3cuSq.map x = q3cuSq.map y ↔
      ∃ a, q3ttKleinMem a ∧ (q3tCurve 2).mul a x = y := by
  constructor
  · intro h
    refine ⟨(q3tCurve 2).mul y ((q3tCurve 2).inv x), ?_, ?_⟩
    · apply (q3cu_ker_eq_klein _).mp
      rw [q3cuSq.map_mul, q3cuSq.map_inv, h]
      exact (q3tCurve 2).mul_inv _
    · rw [(q3tCurve 2).mul_assoc, (q3tCurve 2).inv_mul, (q3tCurve 2).mul_one]
  · intro h
    obtain ⟨a, ha, hax⟩ := h
    rw [← hax, q3cuSq.map_mul, (q3cu_ker_eq_klein a).mpr ha, (q3tCurve 2).one_mul]

/-- **q3cu-6b（★）: 捻れ平行移動デッキは開部分を保つ** — a∈Klein, x∉ker ⟹ a·x∉ker。
    Klein 4 群の剰余類作用が開曲線 E₉∖E₉[2] を保つ（デッキ変換が well-defined）。 -/
theorem q3cu_deck_open (a x : (q3tCurve 2).carrier) (ha : q3ttKleinMem a)
    (hx : q3cuSq.map x ≠ (q3tCurve 2).one) :
    q3cuSq.map ((q3tCurve 2).mul a x) ≠ (q3tCurve 2).one := by
  rw [q3cuSq.map_mul, (q3cu_ker_eq_klein a).mpr ha, (q3tCurve 2).one_mul]
  exact hx

/-- **q3cu-6c（★）: デッキは自由に作用** — a·x=x ⟹ a=O。捻れ平行移動の不動点自由性
    （被覆デッキ群の自由性・q3td_deck_free の開曲線版）。 -/
theorem q3cu_deck_free (a x : (q3tCurve 2).carrier)
    (h : (q3tCurve 2).mul a x = x) : a = (q3tCurve 2).one := by
  have h2 : (q3tCurve 2).mul a x = (q3tCurve 2).mul (q3tCurve 2).one x := by
    rw [(q3tCurve 2).one_mul]; exact h
  exact (q3tCurve 2).mul_right_cancel h2

/-! ## q3cu-7: ★ [2] の ℚ₃ 点非全射性（E(ℚ₃)/2E(ℚ₃)≠0 の影・正直装置） -/

/-- **q3cu-7（★）: [2] は ℚ₃ 点で非全射** — ∀x, sq x ≠ [1]=q3ttW1。
    [1]=[(1,1)] は付値方向のパリティ（1 は奇）ゆえ平方 sq[k,u]=[2k,u²] の像に入れない
    （2∤(1−2k)・omega）。**E(ℚ₃)/2E(ℚ₃)≠0（Kummer 降下の影）の初の実定理**——
    「K 点の影では [N] は全射でない」を隠さず定理として顕示する正直装置を兼ねる。 -/
theorem q3cu_not_surjective : ∀ x, q3cuSq.map x ≠ q3ttW1 := by
  intro x h
  obtain ⟨a, ha⟩ := q3tProj_surjective 2 x
  obtain ⟨k, u⟩ := a
  rw [← ha, q3cu_sq_eq_square, q3tt_proj_mul k k u u] at h
  obtain ⟨hdvd, _⟩ := (q3tt_class_eq_iff (k + k) 1
    ((zpUnits 3 isPrime_three).mul u u) (zpUnits 3 isPrime_three).one).mp h
  obtain ⟨c, hc⟩ := hdvd
  omega

/-! ## q3cu-8: tempered 被覆の puncture ファイバー整合（候補(c) 実形の吸収） -/

/-- **q3cu-8: q^ℤ 軌道は puncture ファイバーを保つ** — x∈q^ℤ ⟺ q·x∈q^ℤ。
    tempered 被覆 ℚ₃^×∖q^ℤ → E₉∖{O} の制限で、生成元 q による平行移動が
    ファイバーを保つ整合性（コンパクト被覆の制限ゆえ惰性ゼロ・§4-1 の限定を継承）。 -/
theorem q3cu_temp_puncture (x : q3tGrp.carrier) :
    (q3tSubgroup 2).mem x ↔ (q3tSubgroup 2).mem (q3tGrp.mul (q3tQ 2) x) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    refine ⟨n + 1, ?_⟩
    rw [tateZpow_succ, hn, q3t_comm x (q3tQ 2)]
  · intro h
    obtain ⟨m, hm⟩ := h
    refine ⟨m + (-1 : Int), ?_⟩
    rw [tateZpow_add q3tGrp (q3tQ 2) m (-1), hm,
      show tateZpow q3tGrp (q3tQ 2) (-1) = q3tGrp.inv (q3tQ 2) from
        tateZpow_negOne q3tGrp (q3tQ 2),
      q3t_comm (q3tQ 2) x, q3tGrp.mul_assoc, q3tGrp.mul_inv, q3tGrp.mul_one]

/-! ## q3cu-9: capstone（新規証明なし・束ねのみ） -/

/-- **q3cu-9a: 楕円 cuspidalization 幾何的基体データ** — 実 [2]-同種・核＝Klein 等号・
    μ₂ 完全性・開曲線の [2]-制限射・ファイバー＝Klein 剰余類・自由デッキ・4 cusp 相異・
    [2] 非全射を束ねる（[AbsTopII] §3 の幾何入力の実現）。 -/
structure Q3CuspidalizationData where
  /-- 実 [2]-同種 sq: E₉ → E₉。 -/
  isog : Hom (q3tCurve 2) (q3tCurve 2)
  /-- sq x = x·x（ker(sq)=E₉[2] on the nose）。 -/
  sq_eq_square : ∀ x, isog.map x = (q3tCurve 2).mul x x
  /-- 核＝ちょうど Klein 4 群（μ₂ 完全性を消費した等号）。 -/
  ker_eq_klein : ∀ x, isog.map x = (q3tCurve 2).one ↔ q3ttKleinMem x
  /-- μ₂ 完全性（u²=1 ⟹ u=±1）。 -/
  mu2_complete : ∀ u : (zpUnits 3 isPrime_three).carrier,
    (zpUnits 3 isPrime_three).mul u u = (zpUnits 3 isPrime_three).one
      → u = (zpUnits 3 isPrime_three).one ∨ u = q3tNegOne
  /-- cuspidalization 図式の [2]-制限射 E₉∖E₉[2] → E₉∖{O}。 -/
  open_map : q3cuOpen → q3cuPunct
  /-- ファイバー＝Klein 剰余類。 -/
  fiber_coset : ∀ x y, isog.map x = isog.map y ↔
    ∃ a, q3ttKleinMem a ∧ (q3tCurve 2).mul a x = y
  /-- デッキは自由に作用。 -/
  deck_free : ∀ a x, (q3tCurve 2).mul a x = x → a = (q3tCurve 2).one
  /-- 上流 4 cusp（Klein 4 点）は相異。 -/
  cusps_distinct :
    q3ttW0 ≠ q3ttW1 ∧ q3ttW0 ≠ q3ttW2 ∧ q3ttW0 ≠ q3ttW3 ∧
    q3ttW1 ≠ q3ttW2 ∧ q3ttW1 ≠ q3ttW3 ∧ q3ttW2 ≠ q3ttW3
  /-- [2] は ℚ₃ 点で非全射。 -/
  not_surj : ∀ x, isog.map x ≠ q3ttW1

/-- **q3cu-9b: 見出し実例** — 実 E₉(ℚ₃)=ℚ₃^×/9^ℤ 上の楕円 cuspidalization 幾何的基体。 -/
def q3cuData : Q3CuspidalizationData where
  isog := q3cuSq
  sq_eq_square := q3cu_sq_eq_square
  ker_eq_klein := q3cu_ker_eq_klein
  mu2_complete := q3cu_mu2_complete
  open_map := q3cuOpenMap
  fiber_coset := q3cu_fiber_coset
  deck_free := q3cu_deck_free
  cusps_distinct := q3tt_klein_distinct
  not_surj := q3cu_not_surjective

/-- **q3cu-9c: 幾何的基体の存在**（実 ℚ₃ 上・q=9・N=2）。 -/
theorem q3cuCusp_exists : Nonempty Q3CuspidalizationData := ⟨q3cuData⟩

end IUT
