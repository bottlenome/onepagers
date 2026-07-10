/-
  IUT/Q3TateCoverTower.lean — A5c（柱A A5: 実 tempered 被覆塔・有限中間被覆 E_{qⁿ}→E_q）

  ── 主要成果の分類: **[実／昇格(a)]**。M374F `TemperedTower.lean` の
     `ttwDeckTower l n = zmod (l^n)`（裸の ℤ/l^n・実曲線未接続）と M369F
     `ThetaCovering.lean` の `tcvDeckGroup`（裸の ℤ/l）を、**実 Tate 曲線の有限中間被覆
     E_{qⁿ}(ℚ₃) → E_q(ℚ₃) のデッキ群 ℤ/n として本物化する**。鍵は成分計算による恒等式
     **q3tQ (m·n) = (q3tQ m)ⁿ**（q3tc_q_pow）——中間被覆 ℚ₃^×/(qⁿ)^ℤ が**既存の
     q3tCurve (m·n) そのもの**として現れ、新しい商構成が不要になる。A8a/A5a で本物化した
     実 E_q(ℚ₃)・実射影 q3tProj・実デッキ作用（q3td）の上に、中間被覆準同型
     q3tcHom: E_{qⁿ} → E_q（q3tProj m の Quot.lift 降下）・その全射性・核＝q^ℤ/(qⁿ)^ℤ・
     有限デッキ作用 GAction (zmod n)（被覆変換性込み）・実被覆塔を積む。toy 主語なし——
     主語は実 q3tGrp・実 q3tQ・実 q3tCurve。

  complete_pct 影響: **A5 0.1→0.15（見込み・独立監査確定が条件）・柱A →49（上限寄与）**。内容:
  (i)   Grp 一般の新補題 tateZpow_npow: (gⁿ)ᵗ = g^{n·t}（tateZpow_add 帰納・唯一のやや新規な
        代数部品）、
  (ii)  恒等式 q3tc_q_pow: q3tQ (m·n) = (q3tQ m)ⁿ（Prod 成分計算）と入れ子
        q3tc_nested: (qⁿ)^ℤ ⊆ q^ℤ、
  (iii) 実中間被覆 q3tcHom: q3tCurve (m·n) → q3tCurve m（q3tProj m を Quot.lift で降下・
        well-def は q3tc_nested + Quot.sound）・全射性 q3tc_surjective・核特徴付け q3tc_ker、
  (iv)  有限デッキ作用 q3tcDeckFin: GAction (zmod n)（[j]·[x]=[qʲ·x]・j mod n で well-def・
        qⁿ の類が q3tCurve(m·n) で自明＝q3tc_q_pow）・被覆変換性 q3tc_deck_over、
  (v)   実被覆塔 q3tc_tower_nested（塔の入れ子）・q3tc_tower_deck（デッキ群塔 ℤ/l^k ＝
        ttwDeckTower l k の実曲線上実現 q3tcTowerDeck）、
  (vi)  束ね Q3TateCoverTowerData / q3tcData（m=1,n=2 見出し実例）/ q3tcCoverTower_exists。

  正直な限定（§5 準拠・消去/弱化しない・既存 surrogate は消さない）:
  (1) TateCoverCat/Galois 圏（M191F/M195F）への実対象登録（実ファイバー {[qʲ]}≅ℤ/n を
      tateLevelCover n と同定）は**本ファイルでは行わない**——圏側の主語替えは別ラウンド
      （A5d 後続）。
  (2) 塔の逆極限 ℤ_l との接続は M374F 既存機構（ttwDeckTower）の消費に留める（実逆極限の
      幾何的実現は後続）。
  (3) 位相・解析構造なし——tempered π₁ の定義（Berkovich/rigid 被覆理論）そのものではなく
      K-点の群論的・算術的な影（有限格子商）である。
  (4) p = 3 固定・q ∈ 3^ℤ（q = 3^m）固定・担体は群提示 3^ℤ×ℤ₃^×（A2/A8 恒久限定の継承）。
  (5) 既存 M374F/M369F の裸 ℤ/n 機構は消さず併設する（§2(a) 昇格の規約）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3TateCurve
import IUT.TateCurve
import IUT.GaloisCategory
import IUT.TemperedTower

namespace IUT

/-! ## q3tc-0: Grp 一般の新補題 (gⁿ)ᵗ = g^{n·t}（唯一のやや新しい代数部品） -/

/-- ↑n による整数冪は自然数冪（定義的一致・rfl）。 -/
theorem tateZpow_natCast (G : Grp) (g : G.carrier) (n : Nat) :
    tateZpow G g (n : Int) = tateNpow G g n := rfl

/-- 自然数指数版: (gⁿ)^{ofNat k} = g^{n·ofNat k}（k についての帰納）。 -/
theorem tateZpow_npow_ofNat (G : Grp) (g : G.carrier) (n : Nat) :
    ∀ k : Nat, tateZpow G (tateNpow G g n) (Int.ofNat k)
      = tateZpow G g ((n : Int) * Int.ofNat k) := by
  intro k
  induction k with
  | zero =>
    show tateZpow G (tateNpow G g n) (Int.ofNat 0)
       = tateZpow G g ((n : Int) * Int.ofNat 0)
    have h0 : (n : Int) * Int.ofNat 0 = Int.ofNat 0 := by
      show (n : Int) * (0 : Int) = (0 : Int)
      rw [Int.mul_zero]
    rw [h0]
    rfl
  | succ j ih =>
    show tateZpow G (tateNpow G g n) (Int.ofNat (j + 1))
       = tateZpow G g ((n : Int) * Int.ofNat (j + 1))
    have hcast : Int.ofNat (j + 1) = Int.ofNat j + 1 := rfl
    have harith : (n : Int) * Int.ofNat (j + 1)
        = (n : Int) * Int.ofNat j + (n : Int) := by
      rw [hcast, Int.mul_add, Int.mul_one]
    rw [tateZpow_ofNat_succ, ih, harith, tateZpow_add, tateZpow_natCast]

/-- **q3tc-0（★）: (gⁿ)ᵗ = g^{n·t}**（全整数 t）— tateZpow_add による帰納（自然数指数版）＋
    負指数の tateZpow_neg 変換。中間被覆の入れ子性 (qⁿ)^ℤ ⊆ q^ℤ の代数的核。 -/
theorem tateZpow_npow (G : Grp) (g : G.carrier) (n : Nat) (t : Int) :
    tateZpow G (tateNpow G g n) t = tateZpow G g ((n : Int) * t) := by
  cases t with
  | ofNat k => exact tateZpow_npow_ofNat G g n k
  | negSucc k =>
    have hneg : Int.negSucc k = -(Int.ofNat (k + 1)) := rfl
    rw [hneg, tateZpow_neg, tateZpow_npow_ofNat G g n (k + 1), ← tateZpow_neg,
      Int.mul_neg]

/-! ## q3tc-1: 恒等式 q3tQ (m·n) = (q3tQ m)ⁿ と入れ子 (qⁿ)^ℤ ⊆ q^ℤ -/

/-- **q3tc-1a（★）: q3tQ (m·n) = (q3tQ m)ⁿ**（成分計算）— 中間被覆の Tate パラメータ qⁿ が
    既存の q3tQ (m·n) と一致。第1成分 q3t_npow_fst（m·n）・第2成分 q3t_npow_snd_of（単数部=1）。 -/
theorem q3tc_q_pow (m n : Nat) : q3tQ (m * n) = tateNpow q3tGrp (q3tQ m) n := by
  apply Prod.ext
  · show ((m * n : Nat) : Int) = (tateNpow q3tGrp (q3tQ m) n).1
    rw [q3t_npow_fst m n, Int.natCast_mul]
  · exact (q3t_npow_snd_of (q3tQ m) rfl n).symm

/-- **q3tc-1b（★）: 入れ子 (qⁿ)^ℤ ⊆ q^ℤ** — q3tSubgroup (m·n) ⊆ q3tSubgroup m。
    x = (qⁿ)ᵗ なら x = q^{n·t}（tateZpow_npow ＋ q3tc_q_pow）で q^ℤ に属す。 -/
theorem q3tc_nested (m n : Nat) (x : q3tGrp.carrier)
    (hx : (q3tSubgroup (m * n)).mem x) : (q3tSubgroup m).mem x := by
  obtain ⟨t, ht⟩ := hx
  refine ⟨(n : Int) * t, ?_⟩
  rw [← tateZpow_npow q3tGrp (q3tQ m) n t, ← q3tc_q_pow m n]
  exact ht

/-! ## q3tc-2: 実中間被覆 q3tcHom: E_{qⁿ}(ℚ₃) → E_q(ℚ₃) -/

/-- **q3tc-2a（★）: 実中間被覆 E_{qⁿ}(ℚ₃) = q3tCurve (m·n) → q3tCurve m = E_q(ℚ₃)** —
    射影 q3tProj m を商 q3tCurve (m·n) = ℚ₃^×/(qⁿ)^ℤ を通じて Quot.lift で降下する。
    well-def: 代表が (qⁿ)^ℤ の元だけ違えば、q3tc_nested で q^ℤ の元でもあり
    q3tProj m の像は一致する（Quot.sound）。 -/
def q3tcHom (m n : Nat) : Hom (q3tCurve (m * n)) (q3tCurve m) where
  map := Quot.lift (fun a => (q3tProj m).map a)
    (fun a b hab => Quot.sound (q3tc_nested m n (q3tGrp.mul (q3tGrp.inv a) b) hab))
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i a
    induction y using Quot.ind; rename_i b
    show (q3tProj m).map (q3tGrp.mul a b)
       = (q3tCurve m).mul ((q3tProj m).map a) ((q3tProj m).map b)
    exact (q3tProj m).map_mul a b

/-- **q3tc-2b: 中間被覆は全射**（q3tProj m の全射性の降下）。 -/
theorem q3tc_surjective (m n : Nat) :
    ∀ y, ∃ x, (q3tcHom m n).map x = y := by
  intro y
  induction y using Quot.ind; rename_i b
  exact ⟨Quot.mk _ b, rfl⟩

/-- **q3tc-2c（★）: 中間被覆の核＝q^ℤ/(qⁿ)^ℤ の像** — [a] ∈ ker(q3tcHom) ⟺ a ∈ q^ℤ。
    q3tcHom の代表 a への値は q3tProj m の値なので、核は quotientProjN_ker（核＝ちょうど q^ℤ）
    に帰着する。 -/
theorem q3tc_ker (m n : Nat) (a : q3tGrp.carrier) :
    (q3tcHom m n).map ((q3tProj (m * n)).map a) = (q3tCurve m).one
      ↔ (q3tSubgroup m).mem a := by
  show (q3tProj m).map a = (q3tCurve m).one ↔ (q3tSubgroup m).mem a
  exact quotientProjN_ker q3tGrp (q3tSubgroup m) (q3t_normal (q3tSubgroup m)) a

/-! ## q3tc-3: 有限デッキ作用 GAction (zmod n) -/

/-- 左簡約（任意群）: (g·a)⁻¹·(g·b) = a⁻¹·b。 -/
theorem q3tc_cancelL (g a b : q3tGrp.carrier) :
    q3tGrp.mul (q3tGrp.inv (q3tGrp.mul g a)) (q3tGrp.mul g b)
      = q3tGrp.mul (q3tGrp.inv a) b := by
  rw [q3tGrp.inv_mul_rev, q3tGrp.mul_assoc,
    ← q3tGrp.mul_assoc (q3tGrp.inv g) g b, q3tGrp.inv_mul, q3tGrp.one_mul]

/-- 可換群での逆元の分配: (x·y)⁻¹ = x⁻¹·y⁻¹。 -/
theorem q3tc_inv_mul (x y : q3tGrp.carrier) :
    q3tGrp.inv (q3tGrp.mul x y) = q3tGrp.mul (q3tGrp.inv x) (q3tGrp.inv y) := by
  rw [q3tGrp.inv_mul_rev, q3t_comm (q3tGrp.inv y) (q3tGrp.inv x)]

/-- 右簡約（可換群）: (x·a)⁻¹·(y·a) = x⁻¹·y。 -/
theorem q3tc_cancelR (x y a : q3tGrp.carrier) :
    q3tGrp.mul (q3tGrp.inv (q3tGrp.mul x a)) (q3tGrp.mul y a)
      = q3tGrp.mul (q3tGrp.inv x) y := by
  rw [q3tc_inv_mul, q3tGrp.mul_assoc,
    ← q3tGrp.mul_assoc (q3tGrp.inv a) y a,
    q3t_comm (q3tGrp.inv a) y,
    q3tGrp.mul_assoc y (q3tGrp.inv a) a,
    q3tGrp.inv_mul, q3tGrp.mul_one]

/-- q3tGrp 元 g による E_{qⁿ}(ℚ₃) 上の左移動 [a] ↦ [g·a]（cosetAction の q3tCurve 内実現）。 -/
def q3tcShift (m n : Nat) (g : q3tGrp.carrier) (x : (q3tCurve (m * n)).carrier) :
    (q3tCurve (m * n)).carrier :=
  Quot.lift (fun a => (q3tProj (m * n)).map (q3tGrp.mul g a))
    (fun a b hab => by
      apply Quot.sound
      show (q3tSubgroup (m * n)).mem
          (q3tGrp.mul (q3tGrp.inv (q3tGrp.mul g a)) (q3tGrp.mul g b))
      rw [q3tc_cancelL g a b]
      exact hab) x

/-- q3tcShift の単位: [1·a] = [a]。 -/
theorem q3tcShift_one (m n : Nat) (x : (q3tCurve (m * n)).carrier) :
    q3tcShift m n q3tGrp.one x = x := by
  induction x using Quot.ind; rename_i a
  show (q3tProj (m * n)).map (q3tGrp.mul q3tGrp.one a) = (q3tProj (m * n)).map a
  rw [q3tGrp.one_mul]

/-- q3tcShift の合成: [(g·h)·a] = [g·(h·a)]。 -/
theorem q3tcShift_mul (m n : Nat) (g h : q3tGrp.carrier)
    (x : (q3tCurve (m * n)).carrier) :
    q3tcShift m n (q3tGrp.mul g h) x = q3tcShift m n g (q3tcShift m n h x) := by
  induction x using Quot.ind; rename_i a
  show (q3tProj (m * n)).map (q3tGrp.mul (q3tGrp.mul g h) a)
     = (q3tProj (m * n)).map (q3tGrp.mul g (q3tGrp.mul h a))
  rw [q3tGrp.mul_assoc]

/-- **q3tc-3a（★）: デッキ作用の j mod n well-def** — n ∣ (j−j') なら [qʲ·a] = [q^{j'}·a]。
    (qʲ·a)⁻¹·(q^{j'}·a) = q^{-j+j'} で、-j+j' = n·(-k)（n∣(j−j')）ゆえ q^{-j+j'} = (qⁿ)^{-k}
    ∈ (qⁿ)^ℤ = q3tSubgroup (m·n)（tateZpow_npow ＋ q3tc_q_pow）。 -/
theorem q3tcShift_wd (m n : Nat) (x : (q3tCurve (m * n)).carrier) (j j' : Int)
    (h : ((n : Nat) : Int) ∣ (j - j')) :
    q3tcShift m n (tateZpow q3tGrp (q3tQ m) j) x
      = q3tcShift m n (tateZpow q3tGrp (q3tQ m) j') x := by
  induction x using Quot.ind; rename_i a
  show (q3tProj (m * n)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) a)
     = (q3tProj (m * n)).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j') a)
  apply Quot.sound
  show (q3tSubgroup (m * n)).mem
    (q3tGrp.mul (q3tGrp.inv (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) a))
      (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j') a))
  rw [q3tc_cancelR (tateZpow q3tGrp (q3tQ m) j) (tateZpow q3tGrp (q3tQ m) j') a,
    ← tateZpow_neg q3tGrp (q3tQ m) j,
    ← tateZpow_add q3tGrp (q3tQ m) (-j) j']
  obtain ⟨k, hk⟩ := h
  refine ⟨-k, ?_⟩
  rw [q3tc_q_pow m n, tateZpow_npow q3tGrp (q3tQ m) n (-k)]
  have hexp : (n : Int) * (-k) = -j + j' := by
    rw [Int.mul_neg, ← hk]; omega
  rw [hexp]

/-- **q3tc-3b（★）: 有限デッキ作用** ℤ/n が E_{qⁿ}(ℚ₃) に作用 [j]·[x] = [qʲ·x]。
    M374F ttwDeckTower（=zmod (l^n)）/ M369F tcvDeckGroup の裸 ℤ/n を、実中間被覆
    E_{qⁿ}(ℚ₃) → E_q(ℚ₃) のデッキ群として実現する初の実曲線実例。 -/
def q3tcDeckFin (m n : Nat) : GAction (zmod n) where
  carrier := (q3tCurve (m * n)).carrier
  act := fun jc x =>
    Quot.lift
      (fun j => q3tcShift m n (tateZpow q3tGrp (q3tQ m) j) x)
      (fun j j' hjj' => q3tcShift_wd m n x j j' hjj')
      jc
  act_one := fun x => by
    show q3tcShift m n (tateZpow q3tGrp (q3tQ m) (0 : Int)) x = x
    rw [tateZpow_zero]
    exact q3tcShift_one m n x
  act_mul := fun g h x => by
    induction g using Quot.ind; rename_i i
    induction h using Quot.ind; rename_i j
    show q3tcShift m n (tateZpow q3tGrp (q3tQ m) (i + j)) x
       = q3tcShift m n (tateZpow q3tGrp (q3tQ m) i)
           (q3tcShift m n (tateZpow q3tGrp (q3tQ m) j) x)
    rw [tateZpow_add, q3tcShift_mul]

/-- **q3tc-3c（★）: 有限デッキ変換は被覆変換** — [j]·[x] は中間被覆 q3tcHom を保つ
    （E_q(ℚ₃) 上に恒等を覆う）。qʲ = q^j ∈ q^ℤ = q3tSubgroup m ゆえ [qʲ·a]=[a]（E_q 上）。 -/
theorem q3tc_deck_over (m n : Nat) (j : Int) (z : (q3tCurve (m * n)).carrier) :
    (q3tcHom m n).map ((q3tcDeckFin m n).act (Quot.mk (modCong n).rel j) z)
      = (q3tcHom m n).map z := by
  induction z using Quot.ind; rename_i a
  show (q3tProj m).map (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) a)
     = (q3tProj m).map a
  apply Quot.sound
  show (q3tSubgroup m).mem
    (q3tGrp.mul (q3tGrp.inv (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) a)) a)
  have heq : q3tGrp.mul (q3tGrp.inv (q3tGrp.mul (tateZpow q3tGrp (q3tQ m) j) a)) a
      = q3tGrp.inv (tateZpow q3tGrp (q3tQ m) j) := by
    rw [q3tGrp.inv_mul_rev, q3tGrp.mul_assoc,
      q3t_comm (q3tGrp.inv (tateZpow q3tGrp (q3tQ m) j)) a,
      ← q3tGrp.mul_assoc, q3tGrp.inv_mul, q3tGrp.one_mul]
  rw [heq]
  exact ⟨-j, tateZpow_neg q3tGrp (q3tQ m) j⟩

/-! ## q3tc-4: 実被覆塔（ttwDeckTower の実曲線上実現） -/

/-- **q3tc-4a: 塔の入れ子** — E_{q^{l^{k+1}}} = q3tCurve (m·l^{k+1}) の周期束は
    E_{q^{l^k}} のそれに含まれる（(q^{l^{k+1}})^ℤ ⊆ (q^{l^k})^ℤ）。q3tc_nested の
    m·l^{k+1} = (m·l^k)·l 特化。 -/
theorem q3tc_tower_nested (m l k : Nat) (x : q3tGrp.carrier)
    (hx : (q3tSubgroup (m * l ^ (k + 1))).mem x) : (q3tSubgroup (m * l ^ k)).mem x := by
  have he : m * l ^ (k + 1) = (m * l ^ k) * l := by
    rw [Nat.pow_succ, ← Nat.mul_assoc]
  rw [he] at hx
  exact q3tc_nested (m * l ^ k) l x hx

/-- **q3tc-4b（★）: デッキ群塔 ℤ/l^k ＝ M374F ttwDeckTower l k の実曲線上実現** —
    塔の第 k 段の有限デッキ作用は zmod (l^k) = ttwDeckTower l k が実曲線
    E_{q^{l^k}}(ℚ₃) = q3tCurve (m·l^k) に作用する形で実現される。 -/
def q3tcTowerDeck (m l k : Nat) : GAction (ttwDeckTower l k) :=
  q3tcDeckFin m (l ^ k)

/-- **q3tc-4c: 塔デッキの担体は実曲線 E_{q^{l^k}}(ℚ₃)** — ttwDeckTower l k（裸 ℤ/l^k）が
    作用する対象が実 Tate 曲線 q3tCurve (m·l^k) であることの明示。 -/
theorem q3tc_tower_deck (m l k : Nat) :
    (q3tcTowerDeck m l k).carrier = (q3tCurve (m * l ^ k)).carrier := rfl

/-! ## q3tc-5: capstone -/

/-- **q3tc-5a: 実 Tate 被覆塔データ** — 恒等式 q3tQ (m·n)=(q3tQ m)ⁿ・実中間被覆
    E_{qⁿ}→E_q（全射・核＝q^ℤ/(qⁿ)^ℤ）・有限デッキ作用 ℤ/n（被覆変換）を束ねる。
    M374F/M369F の裸 ℤ/n 被覆塔の初の実曲線実現。 -/
structure Q3TateCoverTowerData where
  /-- 基点 Tate パラメータの指数 m（q = 3^m）。 -/
  m : Nat
  /-- 被覆次数 n（中間被覆 E_{qⁿ}→E_q の degree）。 -/
  n : Nat
  /-- m ≥ 1（真の退化パラメータ）。 -/
  hm : 1 ≤ m
  /-- qⁿ = (q3tQ m)ⁿ = q3tQ (m·n)（中間被覆の Tate パラメータ）。 -/
  q_pow : q3tQ (m * n) = tateNpow q3tGrp (q3tQ m) n
  /-- 中間被覆 q3tcHom は全射。 -/
  cover_surj : ∀ y, ∃ x, (q3tcHom m n).map x = y
  /-- 中間被覆の核＝q^ℤ/(qⁿ)^ℤ。 -/
  cover_ker : ∀ a, (q3tcHom m n).map ((q3tProj (m * n)).map a) = (q3tCurve m).one
      ↔ (q3tSubgroup m).mem a
  /-- 有限デッキ作用 ℤ/n。 -/
  deck : GAction (zmod n)
  /-- デッキ変換は被覆変換（q3tcHom を保つ）。 -/
  deck_over : ∀ j z, (q3tcHom m n).map ((q3tcDeckFin m n).act (Quot.mk (modCong n).rel j) z)
      = (q3tcHom m n).map z

/-- **q3tc-5b: 見出し実例 m=1, n=2**（q=3・中間被覆 E_{9}(ℚ₃) → E_3(ℚ₃)・デッキ ℤ/2）。 -/
def q3tcData : Q3TateCoverTowerData where
  m := 1
  n := 2
  hm := Nat.le_refl 1
  q_pow := q3tc_q_pow 1 2
  cover_surj := q3tc_surjective 1 2
  cover_ker := q3tc_ker 1 2
  deck := q3tcDeckFin 1 2
  deck_over := q3tc_deck_over 1 2

/-- **q3tc-5c: 実 Tate 被覆塔データの存在**（実 ℚ₃^×・実 q=3^m・実中間被覆）。 -/
theorem q3tcCoverTower_exists : Nonempty Q3TateCoverTowerData := ⟨q3tcData⟩

end IUT
