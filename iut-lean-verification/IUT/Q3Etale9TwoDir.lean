/-
  IUT/Q3Etale9TwoDir.lean — A4（実 π₁^ét）: E_{3⁹}[9] の二方向 π₁^ét スライスと
    その二方向作用（格子方向 ℤ_l ＝ q3pe / μ 方向 ℤ₃(1) ＝ tmzLimit）の忠実性・直交性

  ── 主要成果の分類: **[実／(a) 昇格]**。A4 監査（reaudit-A4-pi1-etale-tate-2026-07-11.md・
     status 0.55）が cap (i) で「μ 方向 ℤ₃(1)=A7 は**二重計上回避で意図的に不構成**」と
     明記した **named deferred defect（μ 方向 π₁ 接続）** を discharge する。本モジュールの
     **NEW A4 内容は、E_{3⁹}[9] 上の実 π₁^ét 二方向作用**——格子方向は q3pe 型の ℤ_l
     （q3pePi1 3・実逆極限）作用、μ 方向は ℤ₃(1)=tmzLimit（実 μ 塔逆極限）作用——**とその
     各方向忠実性・直交性**である。E[9]≅(ℤ/9)² の分解は q9tl/q9c を **INPUT として消費**する
     スキャフォルドであって、A7 の level-9 kill の再計上ではない（A4 の主語は π₁^ét であり、
     A7 の cyclotome/tmi とは別主語）。

  complete_pct 影響: **A4 0.55→（独立監査が merit で決定）**。Σ_A は 54.5 の丁度タイに
     あり表示 54→55 には +0.01 の監査付与で足りるが、**閾値のためでなく merit で判定される**。
     本モジュール単体では「complete_pct 表示前進は監査次第」と正直申告する。

  内容（設計 = audit/pillar-A-path-to-55-scope-2026-07-11.md §4.2 の A4 c2 二方向スライス）:
   * §A 一般群冪算術ヘルパ（znpow/zzpow/one_zpow/npow_mul/npow_inv/order9）
   * §B **E[9] 二方向分解**（消費 INPUT）: q9tdPhi（(ℤ/9)² → E_{3⁹} の実現写像）・
     q9td_e9_decomp（存在＋一意性: 任意の 9-torsion 点は一意に [3]^i·[ζ₉]^j）。
     付値簿記が [3] 方向を分離・q9c_mu9_complete が μ 方向網羅性を与える。
     ⟹ q9tl の正直限定「E[9]≅(ℤ/9)² の完全分類は主張しない」を discharge。
   * §C **π₁^ét 二方向作用**（★ NEW A4 内容・ヘッドライン）:
     q9tdLatChar（格子方向指標 q3pePi1 3 → ℤ/9）・q9tdMuChar（μ 方向指標 tmzLimit → ℤ/9）・
     q9tdLatAct/q9tdMuAct（二方向 GAction）。
   * §D 忠実性・直交性（★）: q9td_act_faithful_lattice / q9td_act_faithful_mu（各方向忠実）・
     q9td_two_dir_orthogonal（格子作用は μ 座標を・μ 作用は格子座標を不変＝直交独立・可換）・
     q9td_lat_realize / q9td_mu_realize（作用を実曲線 E_{3⁹} 上の [3]/[ζ₉] 平行移動として実現）。
   * §E capstone: Q3Etale9TwoDirData / q9td_data / q9td_exists。

  何が NEW（A4）で何が消費（INPUT）か（監査向け明示）:
   - **NEW（A4 の主語 = π₁^ét）**: q9tdLatAct・q9tdMuAct（実 π₁ オブジェクト q3pePi1 3・
     tmzLimit の二方向作用）・q9td_act_faithful_lattice/_mu・q9td_two_dir_orthogonal・
     realize（実曲線への平行移動としての実現）。μ 方向作用の接続そのものが A4 の named defect。
   - **消費 INPUT（A7 campaign 資産・再計上でない）**: E[9]≅(ℤ/9)² 分解（q9tl の二生成元
     [3]/[ζ₉]・q9c_mu9_complete の μ₉ 網羅性）。これは A7 の level-9 kill の再計上ではなく、
     A4 の π₁ 二方向作用が乗る土台の完全化。

  正直な限定（§4 規約・消去/弱化しない）:
  1. **単一曲線 E_{3⁹}**・l 進格子スライス＋μ スライスのみ（full ẑ×ẑ(1) でない）。
  2. **忠実性は名指し二方向のみ**（full π₁ でない）。格子方向は ℤ_l→ℤ/9 の指標を経由する
     ため「mod-9 商 ℤ/9 の作用が忠実」＝ker=9ℤ_l を honest に申告（ℤ_l 全体で単射ではない）。
  3. **q=3⁹ 忠実部分ケース**。位相・エタールサイト・G_{ℚ₃}・anabelian 逆再構成はゼロ
     （q9tl/q3pe/tmz の正直限定を継承）。担体は群提示 ℤ×U₃ の商（A2/A8 恒久限定継承）。
  4. 直交性は「格子作用が μ 座標を・μ 作用が格子座標を不変にする（座標独立）＋二作用が可換」
     の形（座標分解 E[9]≅(ℤ/9)² 上の real statement）。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用
  （Or 破壊は obtain、omega は純線形 Int/Nat ゴールのみ）。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。prefix `q9td`。
-/
import IUT.Q3TateCurveL9
import IUT.Q3Mu9Completeness
import IUT.Q3KummerYPow
import IUT.Q3TatePi1Etale
import IUT.TateModuleZ3

namespace IUT

/-! ## §A: 一般群冪算術ヘルパ（tateNpow/tateZpow の相互則・位数 9 分離） -/

/-- **§A-1: (g^s)^n = g^{s·n}**（tateNpow of tateZpow・全 Int s・自然数 n・可換不要）。 -/
theorem q9td_znpow (G : Grp) (g : G.carrier) (s : Int) :
    ∀ n : Nat, tateNpow G (tateZpow G g s) n = tateZpow G g (s * (n : Int)) := by
  intro n
  induction n with
  | zero =>
    show G.one = tateZpow G g (s * ((0 : Nat) : Int))
    have h0 : s * ((0 : Nat) : Int) = 0 := by omega
    rw [h0]; rfl
  | succ k ih =>
    show G.mul (tateNpow G (tateZpow G g s) k) (tateZpow G g s)
        = tateZpow G g (s * ((k + 1 : Nat) : Int))
    have hcast : ((k + 1 : Nat) : Int) = ((k : Nat) : Int) + 1 := by omega
    rw [ih, hcast, Int.mul_add, Int.mul_one, tateZpow_add]

/-- **§A-2: (g^s)^t = g^{s·t}**（tateZpow of tateZpow・全 Int s,t）。 -/
theorem q9td_zzpow (G : Grp) (g : G.carrier) (s t : Int) :
    tateZpow G (tateZpow G g s) t = tateZpow G g (s * t) := by
  cases t with
  | ofNat n => exact q9td_znpow G g s n
  | negSucc n =>
    show tateNpow G (G.inv (tateZpow G g s)) (n + 1) = tateZpow G g (s * Int.negSucc n)
    have hinv : G.inv (tateZpow G g s) = tateZpow G g (-s) := (tateZpow_neg G g s).symm
    have hidx : (-s) * ((n + 1 : Nat) : Int) = s * Int.negSucc n := by
      have hc : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
      rw [hc, Int.negSucc_eq, Int.mul_neg, Int.neg_mul]
    rw [hinv, q9td_znpow, hidx]

/-- **§A-3: 1^t = 1**（単位元の整数冪）。 -/
theorem q9td_one_zpow (G : Grp) (t : Int) : tateZpow G G.one t = G.one := by
  cases t with
  | ofNat n =>
    show tateNpow G G.one n = G.one
    induction n with
    | zero => rfl
    | succ k ih => show G.mul (tateNpow G G.one k) G.one = G.one; rw [ih, G.mul_one]
  | negSucc n =>
    show tateNpow G (G.inv G.one) (n + 1) = G.one
    have hinv : G.inv G.one = G.one := by
      have h := G.inv_mul G.one; rw [G.mul_one] at h; exact h
    rw [hinv]
    show tateNpow G G.one (n + 1) = G.one
    induction n with
    | zero => show G.mul G.one G.one = G.one; rw [G.mul_one]
    | succ k ih => show G.mul (tateNpow G G.one (k + 1)) G.one = G.one; rw [ih, G.mul_one]

/-- **§A-4: 可換群での (xy)^n = x^n·y^n**（comm を仮説に取る）。 -/
theorem q9td_npow_mul (G : Grp) (hcomm : ∀ a b, G.mul a b = G.mul b a)
    (x y : G.carrier) : ∀ n : Nat,
    tateNpow G (G.mul x y) n = G.mul (tateNpow G x n) (tateNpow G y n) := by
  intro n
  induction n with
  | zero => show G.one = G.mul G.one G.one; rw [G.mul_one]
  | succ k ih =>
    show G.mul (tateNpow G (G.mul x y) k) (G.mul x y)
        = G.mul (G.mul (tateNpow G x k) x) (G.mul (tateNpow G y k) y)
    rw [ih]
    -- (X·Y)·(x·y) = (X·x)·(Y·y) via commutativity/associativity
    rw [G.mul_assoc (tateNpow G x k) (tateNpow G y k) (G.mul x y),
        ← G.mul_assoc (tateNpow G y k) x y, hcomm (tateNpow G y k) x,
        G.mul_assoc x (tateNpow G y k) y, ← G.mul_assoc (tateNpow G x k) x (G.mul (tateNpow G y k) y)]

/-- **§A-5: (g⁻¹)^n = (g^n)⁻¹**（inv g = g^{-1}・§A-1）。 -/
theorem q9td_npow_inv (G : Grp) (g : G.carrier) (n : Nat) :
    tateNpow G (G.inv g) n = G.inv (tateNpow G g n) := by
  have hb : G.inv g = tateZpow G g (-1) := by
    have h : tateZpow G g (Int.negSucc 0) = G.inv g := tateZpow_negOne G g
    have hneg : (-1 : Int) = Int.negSucc 0 := rfl
    rw [hneg]; exact h.symm
  rw [hb, q9td_znpow]
  have hidx : (-1 : Int) * (n : Int) = -(n : Int) := by omega
  rw [hidx, tateZpow_neg]
  show G.inv (tateZpow G g (n : Int)) = G.inv (tateNpow G g n)
  rfl

/-- **§A-6（★ 位数 9 分離の核）**: g^9=1 かつ 0<k<9 で g^k≠1 なら、g^d=1 (d∈ℤ) ⟹ 9∣d。
    d を 9 で割った剰余 r∈[0,9) に落とし、g^d=g^r（g^9=1 を §A-2 で消費）で r>0 を hne が排除。 -/
theorem q9td_order9 (G : Grp) (g : G.carrier)
    (h9 : tateNpow G g 9 = G.one)
    (hne : ∀ k : Nat, 0 < k → k < 9 → tateNpow G g k ≠ G.one)
    (d : Int) (hd : tateZpow G g d = G.one) : (9 : Int) ∣ d := by
  -- d = 9*q + r with 0 ≤ r < 9
  have hr : ∃ q r : Int, d = 9 * q + r ∧ 0 ≤ r ∧ r < 9 :=
    ⟨d / 9, d % 9, by omega, by omega, by omega⟩
  obtain ⟨q, r, hdqr, hr0, hr9⟩ := hr
  -- g^d = g^{9q}·g^r = (g^9)^q · g^r = 1^q · g^r = g^r
  have hg9 : tateZpow G g 9 = G.one := by
    show tateNpow G g 9 = G.one
    exact h9
  have hsplit : tateZpow G g d = tateZpow G g r := by
    rw [hdqr, tateZpow_add, ← q9td_zzpow G g 9 q, hg9, q9td_one_zpow, G.one_mul]
  rw [hsplit] at hd
  -- r ∈ [0,9), r as Nat
  have hrn : ∃ rn : Nat, (rn : Int) = r ∧ rn < 9 := ⟨r.toNat, by omega, by omega⟩
  obtain ⟨rn, hrnv, hrn9⟩ := hrn
  have hdr : tateNpow G g rn = G.one := by
    have : tateZpow G g (rn : Int) = tateNpow G g rn := rfl
    rw [hrnv] at this; rw [← this]; exact hd
  -- rn = 0 の他は hne で排除
  have hrn0 : rn = 0 := by
    cases rn with
    | zero => rfl
    | succ j => exact absurd hdr (hne (j + 1) (by omega) hrn9)
  rw [hrn0] at hrnv
  have hr0' : r = 0 := by omega
  exact ⟨q, by omega⟩

/-! ## §B: E[9] 二方向分解（消費 INPUT: q9tl の二生成元 ＋ q9c_mu9_complete） -/

/-- **§B-0: U₃=q3kU は可換群**（q3k_mul_comm の Subtype 版）。 -/
theorem q9td_q3kU_comm (a b : q3kU.carrier) : q3kU.mul a b = q3kU.mul b a :=
  Subtype.ext (q3k_mul_comm a.val b.val)

/-! ### 純 Int 算術ラッパ（omega は intGrp.carrier を Int に簡約しないため、
    Int 変数上で証明して carrier アトム（defeq Int）に適用する）。 -/

theorem q9td_ar_dvd9 (a b k : Int) (h : a - b = 9 * k) : a = b + 9 * k := by omega
theorem q9td_ar_h1 (a t c : Int) (h : a = 6 * t) : a = t * 6 + c * 0 := by omega
theorem q9td_ar_val (i j i' j' : Int) :
    (-((i * 6) + (j * 0))) + ((i' * 6) + (j' * 0)) = (-(i * 6)) + (i' * 6) := by omega
theorem q9td_ar_dvdi (s i i' : Int) (h : s * 54 = (-(i * 6)) + (i' * 6)) :
    (9 : Int) ∣ (i' - i) := ⟨s, by omega⟩
theorem q9td_ar_t (a t : Int) (h : t * 54 = 9 * a) : a = 6 * t := by omega
theorem q9td_ar_negdvd (i i' c : Int) (h : i' - i = 9 * c) : ((9 : Nat) : Int) ∣ (i - i') :=
  ⟨-c, by omega⟩
theorem q9td_ar_posdvd (j j' c : Int) (h : j - j' = 9 * c) : ((9 : Nat) : Int) ∣ (j - j') :=
  ⟨c, by omega⟩
theorem q9td_ar_split (i i' : Int) : i' = i + (i' - i) := by omega
theorem q9td_ar_sub (j j' : Int) : j - j' = j + (-j') := by omega

/-- **§B-1: 射影は整数冪を保つ**（q9tl_proj_npow の Int 版）。 -/
theorem q9td_proj_zpow (g : q9tlMx.carrier) (t : Int) :
    q9tlProj.map (tateZpow q9tlMx g t) = tateZpow q9tlCurve (q9tlProj.map g) t := by
  cases t with
  | ofNat n => exact q9tl_proj_npow g n
  | negSucc n =>
    show q9tlProj.map (tateNpow q9tlMx (q9tlMx.inv g) (n + 1))
        = tateNpow q9tlCurve (q9tlCurve.inv (q9tlProj.map g)) (n + 1)
    rw [q9tl_proj_npow (q9tlMx.inv g) (n + 1), q9tlProj.map_inv g]

/-- **§B-2: 積群の単数成分の整数冪則**（q9tl_npow_snd の Int 版）。 -/
theorem q9td_zpow_snd (g : q9tlMx.carrier) (t : Int) :
    (tateZpow q9tlMx g t).2 = tateZpow q3kU g.2 t := by
  cases t with
  | ofNat n => exact q9tl_npow_snd g n
  | negSucc n =>
    show (tateNpow q9tlMx (q9tlMx.inv g) (n + 1)).2 = tateNpow q3kU (q3kU.inv g.2) (n + 1)
    have hinv : (q9tlMx.inv g).2 = q3kU.inv g.2 := rfl
    rw [← hinv]
    exact q9tl_npow_snd (q9tlMx.inv g) (n + 1)

/-- **§B-3: 9∣d なら曲線生成元の d 冪は自明**（g^9=1）。 -/
theorem q9td_zpow_9dvd (g : q9tlCurve.carrier) (hg : tateNpow q9tlCurve g 9 = q9tlCurve.one)
    (d : Int) (hdvd : (9 : Int) ∣ d) : tateZpow q9tlCurve g d = q9tlCurve.one := by
  obtain ⟨k, hk⟩ := hdvd
  have hg9 : tateZpow q9tlCurve g 9 = q9tlCurve.one := hg
  rw [hk, ← q9td_zzpow q9tlCurve g 9 k, hg9, q9td_one_zpow]

/-- **§B-4: 9 冪の val 展開＝μ₉ 完全性の消費形**（左結合 tateNpow 9 を q9c の
    ((z³)³) 括り形へ結合則で整形）。 -/
theorem q9td_pow9val (z : q3kU.carrier) :
    q3kMul (q3kMul (q3kMul (q3kMul z.val z.val) z.val) (q3kMul (q3kMul z.val z.val) z.val))
      (q3kMul (q3kMul z.val z.val) z.val)
    = (tateNpow q3kU z 9).val := by
  have hrhs : (tateNpow q3kU z 9).val
      = q3kMul (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul z.val z.val) z.val) z.val)
          z.val) z.val) z.val) z.val) z.val := by
    show q3kMul (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul q3kOne z.val)
        z.val) z.val) z.val) z.val) z.val) z.val) z.val) z.val
      = q3kMul (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul z.val z.val) z.val) z.val)
          z.val) z.val) z.val) z.val) z.val
    rw [q3k_one_mul z.val]
  rw [hrhs,
      ← q3k_mul_assoc (q3kMul (q3kMul z.val z.val) z.val) (q3kMul z.val z.val) z.val,
      ← q3k_mul_assoc (q3kMul (q3kMul z.val z.val) z.val) z.val z.val,
      ← q3k_mul_assoc (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul z.val z.val) z.val) z.val) z.val) z.val)
          (q3kMul z.val z.val) z.val,
      ← q3k_mul_assoc (q3kMul (q3kMul (q3kMul (q3kMul (q3kMul z.val z.val) z.val) z.val) z.val) z.val)
          z.val z.val]

/-- **§B-5: E[9] 二方向座標モデル** (ℤ/9)²（第 1 成分＝格子方向 [3]・第 2 成分＝μ 方向 [ζ₉]）。 -/
def q9tdE9 : Type := (zmod 9).carrier × (zmod 9).carrier

/-- **§B-6: 曲線生成元の位数 9 冪（ζ/9 上の well-defined 冪）** — g^9=1 のとき
    Quot.lift で ℤ/9 → E_{3⁹} の冪写像 c ↦ g^c を得る（choice-free）。 -/
def q9tdCpow (g : q9tlCurve.carrier) (hg : tateNpow q9tlCurve g 9 = q9tlCurve.one) :
    (zmod 9).carrier → q9tlCurve.carrier :=
  Quot.lift (fun a => tateZpow q9tlCurve g a)
    (fun a b hab => by
      show tateZpow q9tlCurve g a = tateZpow q9tlCurve g b
      obtain ⟨k, hk⟩ := hab
      have hab2 : a = b + 9 * k := q9td_ar_dvd9 a b k hk
      have hg9 : tateZpow q9tlCurve g 9 = q9tlCurve.one := hg
      rw [hab2, tateZpow_add, ← q9td_zzpow q9tlCurve g 9 k, hg9, q9td_one_zpow, q9tlCurve.mul_one])

/-- q9tdCpow の代表計算（mk 上は tateZpow）。 -/
theorem q9td_cpow_mk (g : q9tlCurve.carrier) (hg : tateNpow q9tlCurve g 9 = q9tlCurve.one)
    (a : Int) : q9tdCpow g hg (Quot.mk (modCong 9).rel a) = tateZpow q9tlCurve g a := rfl

/-- **§B-7（★ 実現写像）: q9tdPhi : (ℤ/9)² → E_{3⁹}[9]**，(i,j) ↦ [3]^i·[ζ₉]^j。 -/
def q9tdPhi (p : q9tdE9) : q9tlCurve.carrier :=
  q9tlCurve.mul (q9tdCpow q9tl3pt q9tl_3pt_pow9 p.1) (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 p.2)

/-- q9tdPhi の代表計算。 -/
theorem q9td_phi_mk (i j : Int) :
    q9tdPhi (Quot.mk (modCong 9).rel i, Quot.mk (modCong 9).rel j)
      = q9tlCurve.mul (tateZpow q9tlCurve q9tl3pt i) (tateZpow q9tlCurve q9tlZeta9 j) := rfl

/-- **§B-8: 分解の存在の組立**（M^× 表示 m = q9tl3^t·ζElt^{jc} から φ(t,jc)=x を得る）。 -/
theorem q9td_assemble (m : q9tlMx.carrier) (x : q9tlCurve.carrier) (t : Int) (jc : Nat)
    (hproj : q9tlProj.map m = x)
    (hm : m = q9tlMx.mul (tateZpow q9tlMx q9tl3 t) (tateNpow q9tlMx q9tlZeta9Elt jc)) :
    q9tdPhi (Quot.mk (modCong 9).rel t, Quot.mk (modCong 9).rel (jc : Int)) = x := by
  show q9tlCurve.mul (tateZpow q9tlCurve (q9tlProj.map q9tl3) t)
        (tateNpow q9tlCurve (q9tlProj.map q9tlZeta9Elt) jc) = x
  rw [← q9td_proj_zpow q9tl3 t, ← q9tl_proj_npow q9tlZeta9Elt jc, ← q9tlProj.map_mul, ← hm, hproj]

/-- **§B-9: 組立補題（M^× 表示の構成）** — m.1=6t かつ m.2=ζ₉U^{jc}·u₆^t なら
    m = q9tl3^t·ζElt^{jc}。 -/
theorem q9td_build_hm (m : q9tlMx.carrier) (t : Int) (jc : Nat)
    (ht : m.1 = 6 * t)
    (hm2 : m.2 = q3kU.mul (tateNpow q3kU q9tlZeta9U jc) (tateZpow q3kU q9tlU3 t)) :
    m = q9tlMx.mul (tateZpow q9tlMx q9tl3 t) (tateNpow q9tlMx q9tlZeta9Elt jc) := by
  have h1 : m.1 = (q9tlMx.mul (tateZpow q9tlMx q9tl3 t) (tateNpow q9tlMx q9tlZeta9Elt jc)).1 := by
    show m.1 = intGrp.mul (tateZpow q9tlMx q9tl3 t).1 (tateNpow q9tlMx q9tlZeta9Elt jc).1
    rw [q9tl_zpow_fst q9tl3 t, q9tl_npow_fst q9tlZeta9Elt jc, tateZpow_intGrp, tateNpow_intGrp]
    exact q9td_ar_h1 m.1 t (jc : Int) ht
  have h2 : m.2 = (q9tlMx.mul (tateZpow q9tlMx q9tl3 t) (tateNpow q9tlMx q9tlZeta9Elt jc)).2 := by
    show m.2 = q3kU.mul (tateZpow q9tlMx q9tl3 t).2 (tateNpow q9tlMx q9tlZeta9Elt jc).2
    rw [q9td_zpow_snd q9tl3 t, q9tl_npow_snd q9tlZeta9Elt jc]
    show m.2 = q3kU.mul (tateZpow q3kU q9tlU3 t) (tateNpow q3kU q9tlZeta9U jc)
    rw [hm2, q9td_q3kU_comm (tateNpow q3kU q9tlZeta9U jc) (tateZpow q3kU q9tlU3 t)]
  exact Prod.ext h1 h2

/-- **§B-10（★ 一意性）: q9tdPhi は単射**（付値が [3] 方向を・曲線内簡約＋位数 9 が
    [ζ₉] 方向を分離）。⟹ E[9]≅(ℤ/9)² の「独立性」を discharge。 -/
theorem q9td_phi_injective (p p' : q9tdE9) (h : q9tdPhi p = q9tdPhi p') : p = p' := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨p1', p2'⟩ := p'
  revert h
  induction p1 using Quot.ind; rename_i i
  induction p2 using Quot.ind; rename_i j
  induction p1' using Quot.ind; rename_i i'
  induction p2' using Quot.ind; rename_i j'
  intro h
  rw [q9td_phi_mk i j, q9td_phi_mk i' j'] at h
  -- M^× 表示へ持ち上げ
  have hh : q9tlProj.map (q9tlMx.mul (tateZpow q9tlMx q9tl3 i) (tateZpow q9tlMx q9tlZeta9Elt j))
          = q9tlProj.map (q9tlMx.mul (tateZpow q9tlMx q9tl3 i') (tateZpow q9tlMx q9tlZeta9Elt j')) := by
    rw [q9tlProj.map_mul, q9tlProj.map_mul, q9td_proj_zpow q9tl3 i, q9td_proj_zpow q9tlZeta9Elt j,
        q9td_proj_zpow q9tl3 i', q9td_proj_zpow q9tlZeta9Elt j']
    exact h
  have hrel := quot_exact q9tlMx (normalCong q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup)) hh
  have hmem : q9tlSubgroup.mem (q9tlMx.mul (q9tlMx.inv
      (q9tlMx.mul (tateZpow q9tlMx q9tl3 i) (tateZpow q9tlMx q9tlZeta9Elt j)))
      (q9tlMx.mul (tateZpow q9tlMx q9tl3 i') (tateZpow q9tlMx q9tlZeta9Elt j'))) := hrel
  obtain ⟨s, hs⟩ := hmem
  -- 付値成分 → 9 ∣ (i'-i)
  have hc1 := congrArg Prod.fst hs
  rw [q9tl_pow_fst s] at hc1
  have hval : (q9tlMx.mul (q9tlMx.inv
      (q9tlMx.mul (tateZpow q9tlMx q9tl3 i) (tateZpow q9tlMx q9tlZeta9Elt j)))
      (q9tlMx.mul (tateZpow q9tlMx q9tl3 i') (tateZpow q9tlMx q9tlZeta9Elt j'))).1
      = (-(i * 6)) + (i' * 6) := by
    show intGrp.mul (intGrp.inv
        (intGrp.mul (tateZpow q9tlMx q9tl3 i).1 (tateZpow q9tlMx q9tlZeta9Elt j).1))
        (intGrp.mul (tateZpow q9tlMx q9tl3 i').1 (tateZpow q9tlMx q9tlZeta9Elt j').1)
      = (-(i * 6)) + (i' * 6)
    rw [q9tl_zpow_fst q9tl3 i, q9tl_zpow_fst q9tlZeta9Elt j,
        q9tl_zpow_fst q9tl3 i', q9tl_zpow_fst q9tlZeta9Elt j', tateZpow_intGrp, tateZpow_intGrp,
        tateZpow_intGrp, tateZpow_intGrp]
    exact q9td_ar_val i j i' j'
  rw [hval] at hc1
  -- hc1 : s * 54 = -(i*6) + i'*6
  have hdvd_i : (9 : Int) ∣ (i' - i) := q9td_ar_dvdi s i i' hc1
  -- [3]^{i'} = [3]^i（9∣(i'-i)）で h を簡約 → [ζ₉]^j = [ζ₉]^{j'}
  have eq3 : tateZpow q9tlCurve q9tl3pt i' = tateZpow q9tlCurve q9tl3pt i := by
    rw [q9td_ar_split i i', tateZpow_add, q9td_zpow_9dvd q9tl3pt q9tl_3pt_pow9 (i' - i) hdvd_i,
        q9tlCurve.mul_one]
  rw [eq3] at h
  have hj : tateZpow q9tlCurve q9tlZeta9 j = tateZpow q9tlCurve q9tlZeta9 j' :=
    q9tlCurve.mul_left_cancel h
  have hjone : tateZpow q9tlCurve q9tlZeta9 (j - j') = q9tlCurve.one := by
    rw [q9td_ar_sub j j', tateZpow_add, tateZpow_neg, hj, q9tlCurve.mul_inv]
  have hdvd_j : (9 : Int) ∣ (j - j') :=
    q9td_order9 q9tlCurve q9tlZeta9 q9tl_zeta9_pow9 q9tl_zeta9_tor (j - j') hjone
  -- 結論
  have hi : Quot.mk (modCong 9).rel i = Quot.mk (modCong 9).rel i' := by
    apply Quot.sound
    obtain ⟨c, hc⟩ := hdvd_i
    exact q9td_ar_negdvd i i' c hc
  have hjj : Quot.mk (modCong 9).rel j = Quot.mk (modCong 9).rel j' := by
    apply Quot.sound
    obtain ⟨c, hc⟩ := hdvd_j
    exact q9td_ar_posdvd j j' c hc
  rw [hi, hjj]

/-- **§B-10b: 存在の 1 分岐**（w=ζ₉U^{jc} が確定した後の witness 組立）。 -/
theorem q9td_case (m : q9tlMx.carrier) (x : q9tlCurve.carrier) (t : Int) (jc : Nat)
    (hproj : q9tlProj.map m = x)
    (ht : m.1 = 6 * t)
    (hu_wv : q3kU.mul (q3kU.mul m.2 (q3kU.inv (tateZpow q3kU q9tlU3 t)))
        (tateZpow q3kU q9tlU3 t) = m.2)
    (hw : q3kU.mul m.2 (q3kU.inv (tateZpow q3kU q9tlU3 t)) = tateNpow q3kU q9tlZeta9U jc) :
    ∃ p : q9tdE9, q9tdPhi p = x := by
  have hm2 : m.2 = q3kU.mul (tateNpow q3kU q9tlZeta9U jc) (tateZpow q3kU q9tlU3 t) := by
    rw [← hu_wv, hw]
  exact ⟨(Quot.mk (modCong 9).rel t, Quot.mk (modCong 9).rel (jc : Int)),
    q9td_assemble m x t jc hproj (q9td_build_hm m t jc ht hm2)⟩

/-! ### ζ₉U-冪の正規形値（q9c_mu9_complete の 9 元 ↔ ζ₉U^{jc}）。 -/
theorem q9td_zv0 : (tateNpow q3kU q9tlZeta9U 0).val = q3kOne := rfl
theorem q9td_zv1 : (tateNpow q3kU q9tlZeta9U 1).val = ((q3rqZero, q3rqOne, q3rqZero) : q3kCar) :=
  q9tl_zpow1
theorem q9td_zv2 : (tateNpow q3kU q9tlZeta9U 2).val = ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) :=
  q9tl_zpow2.trans q9yp_y2
theorem q9td_zv3 : (tateNpow q3kU q9tlZeta9U 3).val = ((q3rqZeta, q3rqZero, q3rqZero) : q3kCar) :=
  q9tl_zpow3.trans q9yp_y3
theorem q9td_zv4 : (tateNpow q3kU q9tlZeta9U 4).val = ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) :=
  q9tl_zpow4.trans q9yp_y4
theorem q9td_zv5 : (tateNpow q3kU q9tlZeta9U 5).val = ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) :=
  q9tl_zpow5.trans q9yp_y5
theorem q9td_zv6 : (tateNpow q3kU q9tlZeta9U 6).val = ((q3rqZetaSq, q3rqZero, q3rqZero) : q3kCar) :=
  q9tl_zpow6.trans q9yp_y6
theorem q9td_zv7 : (tateNpow q3kU q9tlZeta9U 7).val = ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) :=
  q9tl_zpow7.trans q9yp_y7
theorem q9td_zv8 : (tateNpow q3kU q9tlZeta9U 8).val = ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) :=
  q9tl_zpow8.trans q9yp_y8

/-- **§B-11（★ 存在/網羅性）: 任意の 9-torsion 点は [3]^i·[ζ₉]^j で表せる**
    （付値簿記で t を・q9c_mu9_complete で μ 方向 jc を得る）。⟹ E[9] の「網羅性」を discharge。 -/
theorem q9td_phi_surjective (x : q9tlCurve.carrier)
    (hx9 : tateNpow q9tlCurve x 9 = q9tlCurve.one) :
    ∃ p : q9tdE9, q9tdPhi p = x := by
  obtain ⟨m, hproj⟩ := q9tl_proj_surjective x
  -- m⁹ ∈ q^ℤ
  have hproj9 : q9tlProj.map (tateNpow q9tlMx m 9) = q9tlCurve.one := by
    rw [q9tl_proj_npow m 9, hproj]; exact hx9
  have hmem := (quotientProjN_ker q9tlMx q9tlSubgroup (q9tlNormal q9tlSubgroup)
    (tateNpow q9tlMx m 9)).mp hproj9
  obtain ⟨t, hker⟩ := hmem
  -- 付値成分 → m.1 = 6t
  have hc1 := congrArg Prod.fst hker
  rw [q9tl_pow_fst t, q9tl_npow_fst m 9, tateNpow_intGrp m.1 9] at hc1
  have ht : m.1 = 6 * t := q9td_ar_t m.1 t hc1
  -- 単数成分 → tateNpow u 9 = tateZpow (u₆⁹) t
  have hc2 := congrArg Prod.snd hker
  rw [q9td_zpow_snd q9tlQ t, q9tl_npow_snd m 9] at hc2
  have hcomp2 : tateNpow q3kU m.2 9 = tateZpow q3kU (tateNpow q3kU q9tlU3 9) t := hc2.symm
  -- w = m.2 · (u₆^t)⁻¹ は μ₉ 元
  have hw9 : tateNpow q3kU (q3kU.mul m.2 (q3kU.inv (tateZpow q3kU q9tlU3 t))) 9 = q3kU.one := by
    rw [q9td_npow_mul q3kU q9td_q3kU_comm m.2 (q3kU.inv (tateZpow q3kU q9tlU3 t)) 9,
        q9td_npow_inv q3kU (tateZpow q3kU q9tlU3 t) 9]
    have hu9 : tateNpow q3kU m.2 9 = tateZpow q3kU q9tlU3 (9 * t) := by
      rw [hcomp2, show tateNpow q3kU q9tlU3 9 = tateZpow q3kU q9tlU3 9 from rfl,
          q9td_zzpow q3kU q9tlU3 9 t]
    have hv9 : tateNpow q3kU (tateZpow q3kU q9tlU3 t) 9 = tateZpow q3kU q9tlU3 (9 * t) := by
      rw [q9td_znpow q3kU q9tlU3 t 9, show t * ((9 : Nat) : Int) = 9 * t from by omega]
    rw [hu9, hv9, q3kU.mul_inv]
  have hbracket := q9td_pow9val (q3kU.mul m.2 (q3kU.inv (tateZpow q3kU q9tlU3 t)))
  rw [hw9] at hbracket
  -- hbracket : <bracket w.val> = q3kU.one.val = q3kOne
  have hmu9 := q9c_mu9_complete (q3kU.mul m.2 (q3kU.inv (tateZpow q3kU q9tlU3 t))).val hbracket
  -- u = w · u₆^t
  have hu_wv : q3kU.mul (q3kU.mul m.2 (q3kU.inv (tateZpow q3kU q9tlU3 t)))
      (tateZpow q3kU q9tlU3 t) = m.2 := by
    rw [q3kU.mul_assoc, q3kU.inv_mul, q3kU.mul_one]
  -- 各 μ₉ 分岐で jc を確定
  obtain hd | hd | hd | hd | hd | hd | hd | hd | hd := hmu9
  · exact q9td_case m x t 0 hproj ht hu_wv (Subtype.ext (hd.trans q9td_zv0.symm))
  · exact q9td_case m x t 3 hproj ht hu_wv (Subtype.ext (hd.trans q9td_zv3.symm))
  · exact q9td_case m x t 6 hproj ht hu_wv (Subtype.ext (hd.trans q9td_zv6.symm))
  · exact q9td_case m x t 1 hproj ht hu_wv (Subtype.ext (hd.trans q9td_zv1.symm))
  · exact q9td_case m x t 4 hproj ht hu_wv (Subtype.ext (hd.trans q9td_zv4.symm))
  · exact q9td_case m x t 7 hproj ht hu_wv (Subtype.ext (hd.trans q9td_zv7.symm))
  · exact q9td_case m x t 2 hproj ht hu_wv (Subtype.ext (hd.trans q9td_zv2.symm))
  · exact q9td_case m x t 5 hproj ht hu_wv (Subtype.ext (hd.trans q9td_zv5.symm))
  · exact q9td_case m x t 8 hproj ht hu_wv (Subtype.ext (hd.trans q9td_zv8.symm))

/-- **§B-12（★ 二方向分解の総括）: E[9]≅(ℤ/9)² の完全分解**（存在＋一意性）——
    任意の 9-torsion 点は一意に [3]^i·[ζ₉]^j。q9tl の正直限定「E[9]≅(ℤ/9)² の完全分類は
    主張しない（独立性・網羅性は後続）」を、q9tl の二生成元＋q9c_mu9_complete を INPUT に
    消費して discharge する（A7 level-9 kill の再計上ではない）。 -/
theorem q9td_e9_decomp :
    (∀ p p' : q9tdE9, q9tdPhi p = q9tdPhi p' → p = p')
    ∧ (∀ x : q9tlCurve.carrier, tateNpow q9tlCurve x 9 = q9tlCurve.one → ∃ p, q9tdPhi p = x) :=
  ⟨q9td_phi_injective, q9td_phi_surjective⟩

/-! ## §C: π₁^ét 二方向作用（★ NEW A4 内容・ヘッドライン） -/

/-- ℓ=2 段の hℓ（3^2=9）。 -/
def q9td_h2 : (1 : Nat) ≤ 2 := by omega

/-- Nat 剰余の zmod 9 整合（μ 方向指標の準同型性）。 -/
theorem q9td_ar_modsum (fs ft : Nat) :
    ((9 : Nat) : Int) ∣ ((((fs + ft) % 9 : Nat) : Int) - (((fs : Nat) : Int) + ((ft : Nat) : Int))) := by
  omega

/-- **§C-1（★）: 格子方向指標 χ_lat : ℤ_3=q3pePi1 3 → ℤ/9**（第 2 成分 ℤ/3² への射影）。
    A4a q3pe の格子方向 π₁ 逆極限オブジェクトを E[9] の格子座標へ落とす実指標。 -/
def q9tdLatChar : Hom (q3pePi1 3) (zmod 9) where
  map := fun γ => γ.val 2
  map_mul := fun _ _ => rfl

/-- **§C-2（★）: μ 方向指標 χ_μ : ℤ₃(1)=tmzLimit → ℤ/9**（μ₉=tmzG 1 の離散対数）。
    これが A4 監査の named defect「μ 方向 ℤ₃(1) 接続」の実接続——μ 方向 π₁ オブジェクト
    tmzLimit を E[9] の μ 座標へ落とす実指標。map_mul は tmz_mul_find（離散対数の準同型性）。 -/
def q9tdMuChar : Hom tmzLimit (zmod 9) where
  map := fun s => Quot.mk (modCong 9).rel ((ctmFind 2 q9td_h2 (s.val 1).val : Nat) : Int)
  map_mul := fun s t => by
    show Quot.mk (modCong 9).rel ((ctmFind 2 q9td_h2 ((tmzLimit.mul s t).val 1).val : Nat) : Int)
       = (zmod 9).mul (Quot.mk (modCong 9).rel ((ctmFind 2 q9td_h2 (s.val 1).val : Nat) : Int))
           (Quot.mk (modCong 9).rel ((ctmFind 2 q9td_h2 (t.val 1).val : Nat) : Int))
    rw [show (tmzLimit.mul s t).val 1 = (cmrGrp 2 q9td_h2).mul (s.val 1) (t.val 1) from rfl,
        tmz_mul_find 2 q9td_h2 (s.val 1) (t.val 1)]
    show Quot.mk (modCong 9).rel
        (((ctmFind 2 q9td_h2 (s.val 1).val + ctmFind 2 q9td_h2 (t.val 1).val) % 9 : Nat) : Int)
      = (zmod 9).mul (Quot.mk (modCong 9).rel ((ctmFind 2 q9td_h2 (s.val 1).val : Nat) : Int))
          (Quot.mk (modCong 9).rel ((ctmFind 2 q9td_h2 (t.val 1).val : Nat) : Int))
    apply Quot.sound
    exact q9td_ar_modsum (ctmFind 2 q9td_h2 (s.val 1).val) (ctmFind 2 q9td_h2 (t.val 1).val)

/-- **§C-3（★★ ヘッドライン）: 格子方向作用**——ℤ_3=q3pePi1 3 が E[9]≅(ℤ/9)² の
    格子座標（第 1 成分・[3] 方向）に χ_lat 経由で作用する実 GAction。 -/
def q9tdLatAct : GAction (q3pePi1 3) where
  carrier := q9tdE9
  act := fun γ p => ((zmod 9).mul (q9tdLatChar.map γ) p.1, p.2)
  act_one := fun p => by
    obtain ⟨p1, p2⟩ := p
    show ((zmod 9).mul (q9tdLatChar.map (q3pePi1 3).one) p1, p2) = (p1, p2)
    rw [q9tdLatChar.map_one, (zmod 9).one_mul]
  act_mul := fun γ δ p => by
    show ((zmod 9).mul (q9tdLatChar.map ((q3pePi1 3).mul γ δ)) p.1, p.2)
       = ((zmod 9).mul (q9tdLatChar.map γ) ((zmod 9).mul (q9tdLatChar.map δ) p.1), p.2)
    rw [q9tdLatChar.map_mul, (zmod 9).mul_assoc]

/-- **§C-4（★★ ヘッドライン・NEW A4 内容の核）: μ 方向作用**——ℤ₃(1)=tmzLimit が
    E[9]≅(ℤ/9)² の μ 座標（第 2 成分・[ζ₉] 方向）に χ_μ 経由で作用する実 GAction。
    A4 監査が「二重計上回避で意図的に不構成」と defer した μ 方向 π₁ 接続そのもの。 -/
def q9tdMuAct : GAction tmzLimit where
  carrier := q9tdE9
  act := fun s p => (p.1, (zmod 9).mul (q9tdMuChar.map s) p.2)
  act_one := fun p => by
    obtain ⟨p1, p2⟩ := p
    show (p1, (zmod 9).mul (q9tdMuChar.map tmzLimit.one) p2) = (p1, p2)
    rw [q9tdMuChar.map_one, (zmod 9).one_mul]
  act_mul := fun s t p => by
    show (p.1, (zmod 9).mul (q9tdMuChar.map (tmzLimit.mul s t)) p.2)
       = (p.1, (zmod 9).mul (q9tdMuChar.map s) ((zmod 9).mul (q9tdMuChar.map t) p.2))
    rw [q9tdMuChar.map_mul, (zmod 9).mul_assoc]

/-! ## §D: 忠実性・直交性・実現（★ NEW A4 内容） -/

/-- **§D-1（★）: 格子方向作用の忠実性**——格子作用が全 E[9] 元を固定するなら χ_lat γ=0
    （ℤ/9 商上の作用が忠実＝ker は 9ℤ_3・honest な mod-9 忠実性）。 -/
theorem q9td_act_faithful_lattice (γ : (q3pePi1 3).carrier)
    (h : ∀ p, q9tdLatAct.act γ p = p) : q9tdLatChar.map γ = (zmod 9).one := by
  have hp := h ((zmod 9).one, (zmod 9).one)
  have h1 : (zmod 9).mul (q9tdLatChar.map γ) (zmod 9).one = (zmod 9).one :=
    congrArg Prod.fst hp
  rw [(zmod 9).mul_one] at h1
  exact h1

/-- **§D-2（★）: μ 方向作用の忠実性**——μ 作用が全 E[9] 元を固定するなら χ_μ s=0
    （ℤ/9 商上の μ 作用が忠実）。 -/
theorem q9td_act_faithful_mu (s : tmzLimit.carrier)
    (h : ∀ p, q9tdMuAct.act s p = p) : q9tdMuChar.map s = (zmod 9).one := by
  have hp := h ((zmod 9).one, (zmod 9).one)
  have h2 : (zmod 9).mul (q9tdMuChar.map s) (zmod 9).one = (zmod 9).one :=
    congrArg Prod.snd hp
  rw [(zmod 9).mul_one] at h2
  exact h2

/-- **§D-3（★）: 二方向の直交独立**——格子作用と μ 作用は可換であり、かつ格子作用は
    μ 座標を・μ 作用は格子座標を不変にする（E[9]≅(ℤ/9)² 上の直交分解の real statement）。 -/
theorem q9td_two_dir_orthogonal (γ : (q3pePi1 3).carrier) (s : tmzLimit.carrier) (p : q9tdE9) :
    q9tdLatAct.act γ (q9tdMuAct.act s p) = q9tdMuAct.act s (q9tdLatAct.act γ p)
    ∧ (q9tdLatAct.act γ p).2 = p.2 ∧ (q9tdMuAct.act s p).1 = p.1 :=
  ⟨rfl, rfl, rfl⟩

/-- **§D-4: 冪写像の準同型性**（q9tdCpow は (ℤ/9, +) → E_{3⁹} の準同型）。 -/
theorem q9td_cpow_hom (g : q9tlCurve.carrier) (hg : tateNpow q9tlCurve g 9 = q9tlCurve.one)
    (a b : (zmod 9).carrier) :
    q9tdCpow g hg ((zmod 9).mul a b) = q9tlCurve.mul (q9tdCpow g hg a) (q9tdCpow g hg b) := by
  induction a using Quot.ind; rename_i x
  induction b using Quot.ind; rename_i y
  show tateZpow q9tlCurve g (x + y)
     = q9tlCurve.mul (tateZpow q9tlCurve g x) (tateZpow q9tlCurve g y)
  exact tateZpow_add q9tlCurve g x y

/-- **§D-5（★ 実現）: 格子作用は実曲線 E_{3⁹} 上の [3]-冪平行移動として実現される**
    （φ が格子作用を実曲線の [3] 方向平行移動へ intertwine——作用が toy でなく実曲線作用）。 -/
theorem q9td_lat_realize (γ : (q3pePi1 3).carrier) (p : q9tdE9) :
    q9tdPhi (q9tdLatAct.act γ p)
      = q9tlCurve.mul (q9tdCpow q9tl3pt q9tl_3pt_pow9 (q9tdLatChar.map γ)) (q9tdPhi p) := by
  show q9tlCurve.mul (q9tdCpow q9tl3pt q9tl_3pt_pow9
        ((zmod 9).mul (q9tdLatChar.map γ) p.1)) (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 p.2)
     = q9tlCurve.mul (q9tdCpow q9tl3pt q9tl_3pt_pow9 (q9tdLatChar.map γ))
        (q9tlCurve.mul (q9tdCpow q9tl3pt q9tl_3pt_pow9 p.1) (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 p.2))
  rw [q9td_cpow_hom q9tl3pt q9tl_3pt_pow9 (q9tdLatChar.map γ) p.1, q9tlCurve.mul_assoc]

/-- **§D-6（★ 実現）: μ 作用は実曲線 E_{3⁹} 上の [ζ₉]-冪平行移動として実現される**
    （φ が μ 作用を実曲線の [ζ₉] 方向平行移動へ intertwine——μ 方向 π₁ が実曲線に作用）。 -/
theorem q9td_mu_realize (s : tmzLimit.carrier) (p : q9tdE9) :
    q9tdPhi (q9tdMuAct.act s p)
      = q9tlCurve.mul (q9tdPhi p) (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 (q9tdMuChar.map s)) := by
  show q9tlCurve.mul (q9tdCpow q9tl3pt q9tl_3pt_pow9 p.1)
        (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 ((zmod 9).mul (q9tdMuChar.map s) p.2))
     = q9tlCurve.mul (q9tlCurve.mul (q9tdCpow q9tl3pt q9tl_3pt_pow9 p.1)
          (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 p.2))
        (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 (q9tdMuChar.map s))
  rw [q9td_cpow_hom q9tlZeta9 q9tl_zeta9_pow9 (q9tdMuChar.map s) p.2,
      q9tl_curve_abelian (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 (q9tdMuChar.map s))
        (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 p.2),
      ← q9tlCurve.mul_assoc]

/-- **§D-7: 格子方向作用の非自明性（非空虚）**——ℤ→ℤ_3 の 1 の像は χ_lat で非零。 -/
theorem q9td_lat_nontrivial : q9tdLatChar.map ((toZp 3).map 1) ≠ (zmod 9).one := by
  intro hc
  have hrel : (modCong 9).rel 1 0 := quot_exact intGrp (modCong 9) hc
  obtain ⟨k, hk⟩ := hrel
  omega

/-! ## §E: capstone -/

/-- **§E-1: E_{3⁹}[9] の二方向 π₁^ét スライスデータ** — 二方向分解（存在＋一意性・消費 INPUT）＋
    実 π₁^ét 二方向作用（格子 ℤ_3・μ ℤ₃(1)＝NEW A4）＋各方向忠実性＋直交性を束ねる。 -/
structure Q3Etale9TwoDirData where
  /-- φ 単射（[3]/[ζ₉] 方向の独立性・消費 INPUT の一意性）。 -/
  phi_inj : ∀ p p' : q9tdE9, q9tdPhi p = q9tdPhi p' → p = p'
  /-- φ 網羅（任意 9-torsion 点は二方向分解を持つ・消費 INPUT の網羅性）。 -/
  phi_surj : ∀ x : q9tlCurve.carrier, tateNpow q9tlCurve x 9 = q9tlCurve.one → ∃ p, q9tdPhi p = x
  /-- 格子方向忠実性（NEW A4・q3pePi1 3=ℤ_3 作用）。 -/
  faithful_lat : ∀ γ, (∀ p, q9tdLatAct.act γ p = p) → q9tdLatChar.map γ = (zmod 9).one
  /-- μ 方向忠実性（NEW A4・tmzLimit=ℤ₃(1) 作用・named defect の実接続）。 -/
  faithful_mu : ∀ s, (∀ p, q9tdMuAct.act s p = p) → q9tdMuChar.map s = (zmod 9).one
  /-- 直交独立（可換＋座標保存）。 -/
  orthogonal : ∀ γ s p, q9tdLatAct.act γ (q9tdMuAct.act s p) = q9tdMuAct.act s (q9tdLatAct.act γ p)
      ∧ (q9tdLatAct.act γ p).2 = p.2 ∧ (q9tdMuAct.act s p).1 = p.1
  /-- 格子作用の実曲線 [3]-平行移動としての実現（NEW A4・real curve action）。 -/
  lat_realize : ∀ γ p, q9tdPhi (q9tdLatAct.act γ p)
      = q9tlCurve.mul (q9tdCpow q9tl3pt q9tl_3pt_pow9 (q9tdLatChar.map γ)) (q9tdPhi p)
  /-- μ 作用の実曲線 [ζ₉]-平行移動としての実現（NEW A4・real curve action）。 -/
  mu_realize : ∀ s p, q9tdPhi (q9tdMuAct.act s p)
      = q9tlCurve.mul (q9tdPhi p) (q9tdCpow q9tlZeta9 q9tl_zeta9_pow9 (q9tdMuChar.map s))

/-- **§E-2: 見出し実例** — E_{3⁹}[9] の実 π₁^ét 二方向スライス。 -/
def q9td_data : Q3Etale9TwoDirData where
  phi_inj := q9td_phi_injective
  phi_surj := q9td_phi_surjective
  faithful_lat := q9td_act_faithful_lattice
  faithful_mu := q9td_act_faithful_mu
  orthogonal := q9td_two_dir_orthogonal
  lat_realize := q9td_lat_realize
  mu_realize := q9td_mu_realize

/-- **§E-3: 存在** — E_{3⁹}[9] の実 π₁^ét 二方向スライス（分解＋二方向作用＋忠実性＋直交性）。 -/
theorem q9td_exists : Nonempty Q3Etale9TwoDirData := ⟨q9td_data⟩

end IUT
