/-
  IUT/Q3ThetaQPilotAsymL9.lean — E4 theta-pilot vs q-pilot の実非対称性（Θ 冪＝真正 q 冪・
    level-9 実スライス・prefix `q9tq`）

  ── 主要成果の分類: **[実／(a) 昇格]** — E4「実 theta の Kummer 理論」の前回モジュール
     `Q3ThetaKummerRealL9`（q9tk・監査 0.03）は Θ = ζ₉（**1 の冪根**・q 部自明・指数 0 の
     テータ群元 g_{[ζ₉]}）を主語にし、q 側は自明コサイクル `q9tk_q_cocycle_trivial` のみで、
     E4 の名指す内容 **Θ^{2l} = q^{j²}（theta pilot vs q pilot の非対称性）は不在**だった。
     本モジュールはその欠落主語を実対象上に建てる。主語は監査が名指した**まさにその退化を
     免れる側**——実 level-9 テータ群の**指数 −1・q 部非自明**の元 g_{[3]} = q9mtG3
     （w 部 3 = q^{1/9}・付値 6 ≠ 0）——であり、以下を実 M₉ = q9mtM／実 M^× = q9tlMx の
     等式として証明する:
     (i)   **二次コサイクル法則**（テータ関数等式 θ(qⁿu) = q^{−n(n−1)/2}(−u)^{−n}θ(u) の
           群論的核）: g_{[3]}ⁿ のスカラー成分は 3^{−Tri(n)}（Tri(n)=n(n−1)/2 三角数・
           `q9tq_g3_pow`）。二次指数は**手で入れず** M₉ の cocycle 積から帰納で出る。
     (ii)  **Θ 冪＝真正 q 冪**: g_{[3]}⁹ = (q⁻⁴, −9, q)（スカラーが真正 q 冪・`q9tq_g3_pow9`）、
           テータ値 Θ_j := 3^{j²} について **Θ_j⁹ = q^{j²}**（`q9tq_thetaVal_pow9`・
           Θ^{2l}=q^{j²} の level-9 実形）。Θ_j は 1 の冪根では**ない**: 全ての正冪 ≠ 1
           （`q9tq_thetaVal_npow_ne_one`・q9tk の Θ³ = ζ₃ との正反対）。
     (iii) **theta-pilot vs q-pilot 比較**: δ := g_{[3]}⁹·g_τ⁻¹ = 中心スカラー (q⁻³, 0, 1)
           （`q9tq_delta_eq`）・**δ ≠ 1**（付値 −162 の実 witness・`q9tq_delta_ne_one`）・
           δ は中心的（`q9tq_delta_central`）かつテータ群所属（`q9tq_delta_mem`）。
           q 側は自明でなく、theta 側 9 歩デッキと q 側降下元 g_τ の差が**非自明な真正
           q 冪 q⁻³** に等しい。tempered 実現との接続: Ψ₉(s 9) = δ·g_τ（`q9tq_deck9_pilot`）。
     (iv)  **j² 二分法**: Θ_j ∈ q^ℤ ⟺ 3 ∣ j（`q9tq_thetaVal_qpow_iff`）。二次指数族
           {j²} = {1,4,9,…} は q 格子（付値 54ℤ）と j ≡ 0 (mod 3) でのみ交わる:
           Θ₁ = 3・Θ₂ = 3⁴ は q 冪でない（付値 6・24）が Θ₃ = 3⁹ = q（付値 54）。
     (v)   **テータ群内の捩れ非対称**: g_{[ζ₉]}⁹ = 1（9-torsion・`q9tq_gz_pow9_one`）に対し
           g_{[3]}ⁿ ≠ 1（∀n≥1・無限位数・`q9tq_g3_npow_ne_one`）——q 部の有無が位数の
           有限/無限を分ける。Θ_j の出自はテータ群コサイクル: Θ_n = scalar(g_{[3]}ⁿ)⁻²·3ⁿ
           （`q9tq_theta_from_cocycle`・n² = 2·Tri(n) + n）。

  complete_pct 影響: **E4 0.03 → 予測 +0.07〜0.12（独立敵対監査確定が条件）**。
  q9tk に不在だった「Θ の相対冪が 1 の冪根でなく真正 q 冪に着地する」「q 側が非自明」の
  両方を実対象で埋める。監査要求への直答: (d-1) Θ の関連冪は真正 q 冪か——**Yes**
  （Θ_j⁹ = q^{j²}・g_{[3]}⁹ スカラー = q⁻⁴・Θ_j の全正冪 ≠ 1）。(d-2) q 側は非自明か——
  **Yes**（δ = (q⁻³,0,1) ≠ 1・witness 付値 −162 ≠ 0）。

  **消費（再主張しない・再証明しない）**: q9tl_ninth_elt（3⁹=q・`q9tq_theta3_qpow` は
  その transport と自己申告）・q9tl_zeta9_ninth_one・q9tl_pow_fst・q9tl_npow_fst_val・
  q9tl_npow_fst・tateNpow_intGrp（柱E/A 基盤）、q9mtG3/q9mtGZeta/q9mtTau/q9mtMul/q9mtInv/
  q9mtMem（q9mt 実テータ群）、q9ntScalar・q9nt_one_zpow・q9nt_psi_deck・q9nt_mem_npow
  （q9nt tempered 実現）、tateZpow_add/neg/natCast/npow（M309F/q3tc 冪基盤）、
  q9mt_zpow_inv_eq（q9mt）。`q9tq_scalar_central` は q9nt_Z_central の一般化
  （c 任意・q9nt_Z_central の主張は c = ζ₉⁻¹ の特殊例になる）と自己申告する。

  正直な限定（§4 規約により消さない・弱めない・q3k/q9tl/q9mt/q9nt/q9tk 継承の上に追記のみ）:
  1. **Θ_j = 3^{j²} はテータ値の q 冪部分のみ**。[EtTh] のテータ値 q^{j²/2l}·(単数因子) の
     単数部（符号 (−1)^j・u 依存因子）と p 進テータ級数（収束・解析接続）は依然ゼロ。
     Θ_j の「テータ出自」は M₉ コサイクルからの再構成（q9tq_theta_from_cocycle・
     二次指数の発生源は q9tq_g3_pow の帰納）であり、テータ関数の評価ではない。
  2. **「2l」は level 9 として実現**（q = 3⁹・q^{1/9} = 3 ∈ ℚ₃ の 9 乗トリック＝忠実部分
     ケースの 2 乗・q9tl 正直限定 2 継承）。l 素数 ≥ 5・F_l^* ラベル・|j| ≤ l* の範囲構造・
     ガウス分布 {q^{j²}}_{j=1..l*} の多重集合構造は未達（named future target）。
  3. **q 側の非自明性は乗法的・付値的**（δ ≠ 1・付値 witness）であって、**コホモロジー的
     q 側 Kummer 類は依然自明**（q = 3⁹ は基礎体元・σ-only Galois は 3 を固定——q9tk 正直
     限定・q9tk_q_cocycle_trivial の内容はそのまま真）。本モジュールは Galois/Kummer を
     主語にしない（Θ_j への実 Galois 作用は σ が付値部を固定するため κ が自明化する——
     真の q 側 Kummer には full G_{ℚ₃} と q^{1/9} 添加の非自明拡大が要る・named gap）。
  4. **ガウスモノイド・pilot 対象の Frobenioid 論的構造なし**: 「pilot」は本ファイルでは
     g_τ（q 側降下元）と g_{[3]}⁹（theta 側 9 歩デッキ）の M₉ 内比較の意味であり、
     Θ-pilot 領域/q-pilot 領域の Frobenioid・log-shell 措置は柱 C/D の主語。
  5. q3k/q9tl/q9mt/q9nt の恒久限定を継承: 群提示 ℤ×U₃ の K-point の影・実テータ関数 0・
     π₁ 同定 0・tempered π₁ の定義は外部・pro-3 スコープ。

  **anti-duplication rfl 検査（実施済み・結果の正直記録）**:
   * `q9tqThetaVal 1 = q9tl3 := rfl` — **通らない**（Θ₁ は新規の冪表示・非 rfl）。
   * `q9tqThetaVal 3 = q9tlQ := rfl` — **通る**（定義的・上記のとおり新規 0 計上と自己申告）。
   * `q9tqDelta = q9mtTau := rfl` / `q9tqDelta = q9ntZ9 := rfl` / `q9tqDelta = q9mtOne := rfl`
     / `tateNpow q9mtM q9mtG3 9 = q9mtTau := rfl` — **いずれも通らない**（δ・g_{[3]}⁹ は
     既存対象と定義的に別・δ ≠ 1 は定理 q9tq-4d）。
   * q9tk の Θ（`q9tkTheta : q3kCar`）と本モジュールの Θ_j（`q9tlMx.carrier`）は**型からして
     別対象**（前者は単数環内の ζ₉・後者は付値 6j² の非単数）。
   * `tateNpow q9mtM q9mtG3 9`・二次法則・δ を主語とする定理はリポジトリ内に存在しない
     （grep 実測: tateNpow/tateZpow q9mtM 系の既存使用は q9nt/q9ng の Z₉・Φ₉ 抽象冪のみで、
     g_{[3]} 冪の閉形式・スカラー成分計算はどこにも無い）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用
  （omega は Int/Nat 原子のみ・二次項は generalize/補題で原子化してから使用）。
  一般名は `q9tq` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.Q3TemperedThetaClassL9
import IUT.Q3TateCoverTower

namespace IUT

/-! ## q9tq-0: Nat 冪の加法・乗法則（tateZpow 基盤の Nat 化・汎用 Grp） -/

/-- **q9tq-0a: Nat 冪の加法則** g^{a+b} = g^a·g^b（tateZpow_add の Nat 化）。 -/
theorem q9tq_npow_add (G : Grp) (g : G.carrier) (a b : Nat) :
    tateNpow G g (a + b) = G.mul (tateNpow G g a) (tateNpow G g b) := by
  have h := tateZpow_add G g ((a : Nat) : Int) ((b : Nat) : Int)
  have hc : ((a : Nat) : Int) + ((b : Nat) : Int) = ((a + b : Nat) : Int) := by omega
  rw [hc, tateZpow_natCast, tateZpow_natCast, tateZpow_natCast] at h
  exact h

/-- **q9tq-0b: Nat 冪の乗法則** g^{a·b} = (g^a)^b（tateZpow_npow の Nat 化）。 -/
theorem q9tq_npow_mul (G : Grp) (g : G.carrier) (a b : Nat) :
    tateNpow G g (a * b) = tateNpow G (tateNpow G g a) b := by
  have h : tateZpow G (tateNpow G g a) ((b : Nat) : Int)
      = tateZpow G g (((a : Nat) : Int) * ((b : Nat) : Int)) :=
    tateZpow_npow G g a ((b : Nat) : Int)
  have hc : ((a : Nat) : Int) * ((b : Nat) : Int) = ((a * b : Nat) : Int) :=
    (Int.natCast_mul a b).symm
  rw [hc, tateZpow_natCast, tateZpow_natCast] at h
  exact h.symm

/-! ## q9tq-1: 三角数 Tri(n) = 0+1+…+(n−1) と n² = 2·Tri(n) + n -/

/-- **q9tq-1a: 三角数** Tri(0)=0・Tri(n+1)=Tri(n)+n（テータ等式の二次指数 n(n−1)/2）。 -/
def q9tqTri : Nat → Nat
  | 0 => 0
  | n + 1 => q9tqTri n + n

/-- Tri(9) = 36（g_{[3]}⁹ のスカラー指数・36 = 4·9 が q 冪着地の核）。 -/
theorem q9tq_tri9 : q9tqTri 9 = 36 := rfl

/-- **q9tq-1b: n² = Tri(n) + Tri(n) + n**（テータ値指数 j² とコサイクル指数 Tri の橋・
    (n+1)² 展開は Nat.succ_mul/Nat.mul_succ・二次項は omega 原子化）。 -/
theorem q9tq_tri_sq : ∀ n : Nat, q9tqTri n + q9tqTri n + n = n * n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (q9tqTri n + n) + (q9tqTri n + n) + (n + 1) = (n + 1) * (n + 1)
    have h1 : (n + 1) * (n + 1) = n * (n + 1) + (n + 1) := Nat.succ_mul n (n + 1)
    have h2 : n * (n + 1) = n * n + n := Nat.mul_succ n n
    rw [h1, h2]
    omega

/-! ## q9tq-2: ★★ 二次コサイクル法則 — g_{[3]}ⁿ = (3^{−Tri(n)}, −n, 3ⁿ) -/

/-- **q9tq-2a（★★ 旗艦・二次法則）: g_{[3]}ⁿ = (3^{−Tri(n)}, −n, 3ⁿ)** — 実テータ群の
    q 部非自明元 g_{[3]} = (1, −1, 3) の n 乗のスカラー成分に、M₉ の cocycle 積
    (c,a,w)(c',a',w') = (c·c'·w'^a, a+a', w·w') から**二次指数 Tri(n) = n(n−1)/2 が帰納で
    発生**する。テータ関数等式 θ(qⁿu) = q^{−n(n−1)/2}(−u)^{−n}θ(u) の cocycle 部の
    群論的実装（指数は手で入れない）。 -/
theorem q9tq_g3_pow : ∀ n : Nat,
    tateNpow q9mtM q9mtG3 n
      = ((tateZpow q9tlMx q9tl3 (-(q9tqTri n : Int)), -(n : Int)),
         tateNpow q9tlMx q9tl3 n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show q9mtMul (tateNpow q9mtM q9mtG3 n) q9mtG3
        = ((tateZpow q9tlMx q9tl3 (-(q9tqTri (n + 1) : Int)), -((n + 1 : Nat) : Int)),
           tateNpow q9tlMx q9tl3 (n + 1))
    rw [ih]
    show ((q9tlMx.mul
            (q9tlMx.mul (tateZpow q9tlMx q9tl3 (-(q9tqTri n : Int))) q9tlMx.one)
            (tateZpow q9tlMx q9tl3 (-(n : Int))),
          -(n : Int) + (-1 : Int)),
         q9tlMx.mul (tateNpow q9tlMx q9tl3 n) q9tl3)
       = ((tateZpow q9tlMx q9tl3 (-(q9tqTri (n + 1) : Int)), -((n + 1 : Nat) : Int)),
          tateNpow q9tlMx q9tl3 (n + 1))
    have hC : q9tlMx.mul
        (q9tlMx.mul (tateZpow q9tlMx q9tl3 (-(q9tqTri n : Int))) q9tlMx.one)
        (tateZpow q9tlMx q9tl3 (-(n : Int)))
        = tateZpow q9tlMx q9tl3 (-(q9tqTri (n + 1) : Int)) := by
      rw [q9tlMx.mul_one]
      have he : -(q9tqTri n : Int) + -(n : Int) = -(q9tqTri (n + 1) : Int) := by
        have ht : q9tqTri (n + 1) = q9tqTri n + n := rfl
        rw [ht]
        omega
      rw [← tateZpow_add, he]
    have hA : -(n : Int) + (-1 : Int) = -((n + 1 : Nat) : Int) := by omega
    rw [hC, hA]
    rfl

/-- **q9tq-2b: q 部の非自明性（監査の名指した対照点）** — g_{[3]} の指数は −1 ≠ 0
    （g_{[ζ₉]} の指数 0 = `q9tq_gz_qpart_trivial` と対照・q9tk が退化した a = 0 枝の外）。 -/
theorem q9tq_g3_qpart_nontrivial : q9mtG3.1.2 ≠ (0 : Int) := by
  intro h
  have h2 : (-1 : Int) = 0 := h
  omega

/-- g_{[ζ₉]} の指数は 0（q9tk の Θ = ζ₉ が乗っていた退化枝・対照の明示）。 -/
theorem q9tq_gz_qpart_trivial : q9mtGZeta.1.2 = (0 : Int) := rfl

/-! ## q9tq-3: ★★ Θ 冪＝真正 q 冪 — g_{[3]}⁹ = (q⁻⁴, −9, q) -/

/-- 3³⁶ = q⁴（36 = 9·4・q9tl_ninth_elt 消費）。 -/
theorem q9tq_pow36 : tateNpow q9tlMx q9tl3 36 = tateNpow q9tlMx q9tlQ 4 := by
  rw [← q9tl_ninth_elt, ← q9tq_npow_mul q9tlMx q9tl3 9 4]

/-- **q9tq-3a（★★ 旗艦）: g_{[3]}⁹ = (q⁻⁴, −9, q)** — テータ群の q 部非自明元の 9 乗は
    スカカラー成分が**真正 q 冪 q⁻⁴**（1 の冪根ではない・Tri(9) = 36 = 4·9）、w 部が q。
    q9tk の Θ³ = ζ₃（単数・冪根）と正反対の着地。 -/
theorem q9tq_g3_pow9 :
    tateNpow q9mtM q9mtG3 9
      = ((tateZpow q9tlMx q9tlQ (-4 : Int), (-9 : Int)), q9tlQ) := by
  rw [q9tq_g3_pow 9, q9tl_ninth_elt]
  have hs : tateZpow q9tlMx q9tl3 (-(q9tqTri 9 : Int)) = tateZpow q9tlMx q9tlQ (-4 : Int) := by
    have h36 : -(q9tqTri 9 : Int) = -((36 : Nat) : Int) := rfl
    rw [h36, tateZpow_neg, tateZpow_natCast, q9tq_pow36, ← tateZpow_natCast, ← tateZpow_neg]
    have h4 : -((4 : Nat) : Int) = (-4 : Int) := by omega
    rw [h4]
  have ha : -((9 : Nat) : Int) = (-9 : Int) := by omega
  rw [hs, ha]

/-! ## q9tq-4: ★★ theta-pilot vs q-pilot 比較 — δ = g_{[3]}⁹·g_τ⁻¹ = (q⁻³, 0, 1) ≠ 1 -/

/-- **q9tq-4a: 比較差 δ := g_{[3]}⁹·g_τ⁻¹** — theta 側 9 歩デッキと q 側降下元の差。 -/
def q9tqDelta : q9mtCar := q9mtMul (tateNpow q9mtM q9mtG3 9) (q9mtInv q9mtTau)

/-- **q9tq-4b（★★ 旗艦・pilot 比較）: δ = (q⁻³, 0, 1)** — 差は**中心スカラーの真正 q 冪**。
    theta pilot と q pilot は一致せず（δ ≠ 1・q9tq-4d）、その不一致は単数や冪根でなく
    q⁻³（付値 −162）が測る。 -/
theorem q9tq_delta_eq :
    q9tqDelta = ((tateZpow q9tlMx q9tlQ (-3 : Int), (0 : Int)), q9tlMx.one) := by
  show q9mtMul (tateNpow q9mtM q9mtG3 9) (q9mtInv q9mtTau)
      = ((tateZpow q9tlMx q9tlQ (-3 : Int), (0 : Int)), q9tlMx.one)
  rw [q9tq_g3_pow9]
  show ((q9tlMx.mul
          (q9tlMx.mul (tateZpow q9tlMx q9tlQ (-4 : Int))
            (q9tlMx.mul (q9tlMx.inv (q9tlMx.inv q9tlQ)) (tateZpow q9tlMx q9tlQ (-9 : Int))))
          (tateZpow q9tlMx (q9tlMx.inv q9tlQ) (-9 : Int)),
        (-9 : Int) + -(-9 : Int)),
       q9tlMx.mul q9tlQ (q9tlMx.inv q9tlQ))
     = ((tateZpow q9tlMx q9tlQ (-3 : Int), (0 : Int)), q9tlMx.one)
  have hB : q9tlMx.inv (q9tlMx.inv q9tlQ) = q9tlQ := Grp.inv_inv q9tlMx q9tlQ
  have hC3 : q9tlMx.mul q9tlQ (tateZpow q9tlMx q9tlQ (-9 : Int))
      = tateZpow q9tlMx q9tlQ (-8 : Int) := by
    have h1 : tateZpow q9tlMx q9tlQ ((1 : Int) + (-9 : Int))
        = q9tlMx.mul (tateZpow q9tlMx q9tlQ (1 : Int)) (tateZpow q9tlMx q9tlQ (-9 : Int)) :=
      tateZpow_add q9tlMx q9tlQ 1 (-9)
    rw [tateZpow_one] at h1
    have h2 : (1 : Int) + (-9 : Int) = (-8 : Int) := by omega
    rw [h2] at h1
    exact h1.symm
  have hC2 : tateZpow q9tlMx (q9tlMx.inv q9tlQ) (-9 : Int)
      = tateZpow q9tlMx q9tlQ (9 : Int) := by
    rw [q9mt_zpow_inv_eq q9tlQ (-9 : Int)]
    have h99 : -(-9 : Int) = (9 : Int) := by omega
    rw [h99]
  have hC4 : q9tlMx.mul (tateZpow q9tlMx q9tlQ (-4 : Int)) (tateZpow q9tlMx q9tlQ (-8 : Int))
      = tateZpow q9tlMx q9tlQ (-12 : Int) := by
    have h1 := (tateZpow_add q9tlMx q9tlQ (-4) (-8)).symm
    have h2 : (-4 : Int) + (-8 : Int) = (-12 : Int) := by omega
    rw [h2] at h1
    exact h1
  have hC5 : q9tlMx.mul (tateZpow q9tlMx q9tlQ (-12 : Int)) (tateZpow q9tlMx q9tlQ (9 : Int))
      = tateZpow q9tlMx q9tlQ (-3 : Int) := by
    have h1 := (tateZpow_add q9tlMx q9tlQ (-12) 9).symm
    have h2 : (-12 : Int) + (9 : Int) = (-3 : Int) := by omega
    rw [h2] at h1
    exact h1
  have hA : (-9 : Int) + -(-9 : Int) = (0 : Int) := by omega
  have hW : q9tlMx.mul q9tlQ (q9tlMx.inv q9tlQ) = q9tlMx.one := q9tlMx.mul_inv q9tlQ
  rw [hB, hC3, hC2, hC4, hC5, hA, hW]

/-- δ はスカラー像（q9ntScalar による表示・δ = scalar(q⁻³)）。 -/
theorem q9tq_delta_scalar :
    q9tqDelta = q9ntScalar (tateZpow q9tlMx q9tlQ (-3 : Int)) := q9tq_delta_eq

/-- **q9tq-4c: pilot 比較の乗法形** g_{[3]}⁹ = scalar(q⁻³)·g_τ — theta 側 9 歩は
    q 側降下元 g_τ に**中心 q⁻³ を掛けたもの**にちょうど等しい。 -/
theorem q9tq_pilot_comparison :
    tateNpow q9mtM q9mtG3 9
      = q9mtMul (q9ntScalar (tateZpow q9tlMx q9tlQ (-3 : Int))) q9mtTau := by
  have h : q9mtMul q9tqDelta q9mtTau = tateNpow q9mtM q9mtG3 9 := by
    show q9mtM.mul (q9mtM.mul (tateNpow q9mtM q9mtG3 9) (q9mtM.inv q9mtTau)) q9mtTau
        = tateNpow q9mtM q9mtG3 9
    rw [q9mtM.mul_assoc, q9mtM.inv_mul, q9mtM.mul_one]
  rw [← h, q9tq_delta_scalar]

/-- **q9tq-4d（★★★ 旗艦・q 側非自明性 witness）: δ ≠ 1** — theta pilot と q pilot の差は
    非自明。witness: δ のスカラー付値 = (−3)·54 = −162 ≠ 0（q9tl_pow_fst 消費）。
    q9tk の q 側（自明コサイクル）と正反対の実非自明性。 -/
theorem q9tq_delta_ne_one : q9tqDelta ≠ q9mtOne := by
  rw [q9tq_delta_eq]
  intro h
  have h3 : (tateZpow q9tlMx q9tlQ (-3 : Int)).1 = (0 : Int) :=
    congrArg (fun z : q9mtCar => z.1.1.1) h
  rw [q9tl_pow_fst (-3 : Int)] at h3
  have h4 : (-3 : Int) * 54 = (0 : Int) := h3
  omega

/-- **q9tq-4e: スカラーの中心性（一般形）** — 任意の c ∈ M^× で scalar(c) は M₉ 中心的
    （q9nt_Z_central の一般化・c = ζ₉⁻¹ が同定理の特殊例）。 -/
theorem q9tq_scalar_central (c : q9tlMx.carrier) (g : q9mtCar) :
    q9mtM.mul (q9ntScalar c) g = q9mtM.mul g (q9ntScalar c) := by
  obtain ⟨⟨d, a⟩, w⟩ := g
  show ((q9tlMx.mul (q9tlMx.mul c d) (tateZpow q9tlMx w 0), (0 : Int) + a),
          q9tlMx.mul q9tlMx.one w)
     = ((q9tlMx.mul (q9tlMx.mul d c) (tateZpow q9tlMx q9tlMx.one a), a + (0 : Int)),
          q9tlMx.mul w q9tlMx.one)
  have hA : (0 : Int) + a = a + (0 : Int) := by omega
  have hW : q9tlMx.mul q9tlMx.one w = q9tlMx.mul w q9tlMx.one := by
    rw [q9tlMx.one_mul, q9tlMx.mul_one]
  have hC : q9tlMx.mul (q9tlMx.mul c d) (tateZpow q9tlMx w 0)
      = q9tlMx.mul (q9tlMx.mul d c) (tateZpow q9tlMx q9tlMx.one a) := by
    rw [tateZpow_zero, q9nt_one_zpow, q9tlMx.mul_one, q9tlMx.mul_one, q9tlComm c d]
  rw [hA, hW, hC]

/-- **q9tq-4f: δ は中心的** — 比較差は M₉ の中心に落ちる（真正 q 冪の中心スカラー）。 -/
theorem q9tq_delta_central (g : q9mtCar) :
    q9mtM.mul q9tqDelta g = q9mtM.mul g q9tqDelta := by
  rw [q9tq_delta_scalar]
  exact q9tq_scalar_central (tateZpow q9tlMx q9tlQ (-3 : Int)) g

/-- **q9tq-4g: δ はテータ群の元**（mem 条件 q⁰·1⁹ = 1）。 -/
theorem q9tq_delta_mem : q9mtMem q9tqDelta := by
  rw [q9tq_delta_eq]
  show q9tlMx.mul (tateZpow q9tlMx q9tlQ (0 : Int)) (tateZpow q9tlMx q9tlMx.one 9)
      = q9tlMx.one
  rw [tateZpow_zero, q9nt_one_zpow, q9tlMx.one_mul]

/-- g_τ 自身もテータ群の元（q⁻⁹·q⁹ = 1・q 側 pilot の所属）。 -/
theorem q9tq_tau_mem : q9mtMem q9mtTau := by
  show q9tlMx.mul (tateZpow q9tlMx q9tlQ (-9 : Int)) (tateZpow q9tlMx q9tlQ 9) = q9tlMx.one
  rw [← tateZpow_add]
  have h : (-9 : Int) + 9 = 0 := by omega
  rw [h]
  rfl

/-- theta 側 9 歩 g_{[3]}⁹ もテータ群の元（q9nt_mem_npow 消費・transport と自己申告）。 -/
theorem q9tq_pilot_pow_mem : q9mtMem (tateNpow q9mtM q9mtG3 9) :=
  q9nt_mem_npow q9mtG3 q9mt_g3_mem 9

/-- **q9tq-4h: tempered 実現との接続** — Ψ₉(s 9)（tempered デッキの 9 歩）= scalar(q⁻³)·g_τ
    （q9nt_psi_deck 消費＋q9tq-4c）。theta pilot は tempered 実現のデッキ像として現れる。 -/
theorem q9tq_deck9_pilot :
    q9ntPsi.map (tpeSection.map (9 : Int))
      = q9mtMul (q9ntScalar (tateZpow q9tlMx q9tlQ (-3 : Int))) q9mtTau := by
  rw [q9nt_psi_deck]
  have h9 : tateZpow q9mtM q9mtG3 (9 : Int) = tateNpow q9mtM q9mtG3 9 := rfl
  rw [h9, q9tq_pilot_comparison]

/-! ## q9tq-5: テータ群内の捩れ非対称 — g_{[ζ₉]}⁹ = 1 vs g_{[3]}ⁿ ≠ 1 -/

/-- g_{[ζ₉]}ⁿ = (1, 0, ζ₉ⁿ)（指数 0 ゆえスカラーが増えない・二次法則の退化形）。 -/
theorem q9tq_gz_pow : ∀ n : Nat,
    tateNpow q9mtM q9mtGZeta n
      = ((q9tlMx.one, (0 : Int)), tateNpow q9tlMx q9tlZeta9Elt n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show q9mtMul (tateNpow q9mtM q9mtGZeta n) q9mtGZeta
        = ((q9tlMx.one, (0 : Int)), tateNpow q9tlMx q9tlZeta9Elt (n + 1))
    rw [ih]
    show ((q9tlMx.mul (q9tlMx.mul q9tlMx.one q9tlMx.one)
            (tateZpow q9tlMx q9tlZeta9Elt 0), (0 : Int) + 0),
          q9tlMx.mul (tateNpow q9tlMx q9tlZeta9Elt n) q9tlZeta9Elt)
       = ((q9tlMx.one, (0 : Int)), tateNpow q9tlMx q9tlZeta9Elt (n + 1))
    have hC : q9tlMx.mul (q9tlMx.mul q9tlMx.one q9tlMx.one)
        (tateZpow q9tlMx q9tlZeta9Elt 0) = q9tlMx.one := by
      rw [tateZpow_zero, q9tlMx.mul_one, q9tlMx.mul_one]
    have hA : (0 : Int) + 0 = (0 : Int) := by omega
    rw [hC, hA]
    rfl

/-- **q9tq-5a（対照・冪根側）: g_{[ζ₉]}⁹ = 1** — 指数 0（q 部自明）のテータ群元は
    9-torsion（q9tl_zeta9_ninth_one 消費）。q9tk の主語はこの枝に居た。 -/
theorem q9tq_gz_pow9_one : tateNpow q9mtM q9mtGZeta 9 = q9mtOne := by
  rw [q9tq_gz_pow 9, q9tl_zeta9_ninth_one]
  rfl

/-- **q9tq-5b（★ 対照・q 冪側）: g_{[3]}ⁿ ≠ 1（∀ n ≥ 1）** — 指数 −1（q 部非自明）の
    テータ群元は**無限位数**（指数成分 −n ≠ 0）。q 部の有無が捩れ/非捩れを分ける——
    「Θ の関連冪は 1 に戻らず q 冪に着地する」の群論形。 -/
theorem q9tq_g3_npow_ne_one (n : Nat) (hn : 0 < n) :
    tateNpow q9mtM q9mtG3 n ≠ q9mtOne := by
  intro h
  rw [q9tq_g3_pow n] at h
  have h2 : -(n : Int) = (0 : Int) := congrArg (fun z : q9mtCar => z.1.2) h
  omega

/-! ## q9tq-6: ★★ テータ値 Θ_j = 3^{j²} と Θ_j⁹ = q^{j²}・j² 二分法 -/

/-- **q9tq-6a: テータ値の q 冪骨格** Θ_j := 3^{j²} ∈ M^×（j 番目のテータ値 q^{j²/9} の
    実担体・付値 6j²）。出自は g_{[3]} コサイクル（q9tq-6f）。 -/
def q9tqThetaVal (j : Nat) : q9tlMx.carrier := tateNpow q9tlMx q9tl3 (j * j)

/-- Θ_j の付値 = j²·6（q9tl_npow_fst_val 消費）。 -/
theorem q9tq_thetaVal_fst (j : Nat) :
    (q9tqThetaVal j).1 = ((j * j : Nat) : Int) * 6 := q9tl_npow_fst_val (j * j)

/-- **q9tq-6b（★★★ 旗艦・Θ^{2l} = q^{j²} の実形）: Θ_j⁹ = q^{j²}** — テータ値の 9 乗
    （level-9 の「2l 乗」）は**指数が j² の真正 q 冪**。E4 が名指す theta-vs-q 非対称性の
    核等式を実 M^× = ℤ(v_π)×U₃ の等式として証明する。 -/
theorem q9tq_thetaVal_pow9 (j : Nat) :
    tateNpow q9tlMx (q9tqThetaVal j) 9 = tateNpow q9tlMx q9tlQ (j * j) := by
  show tateNpow q9tlMx (tateNpow q9tlMx q9tl3 (j * j)) 9 = tateNpow q9tlMx q9tlQ (j * j)
  rw [← q9tq_npow_mul q9tlMx q9tl3 (j * j) 9, ← q9tl_ninth_elt,
      ← q9tq_npow_mul q9tlMx q9tl3 9 (j * j), Nat.mul_comm (j * j) 9]

/-- **q9tq-6c（★★ 旗艦・冪根否定）: Θ_j は 1 の冪根ではない** — 全ての正冪 ≠ 1
    （付値 j²·6·k ≠ 0）。q9tk の Θ = ζ₉（Θ⁹ = 1）と正反対: 本物のテータ値の冪は
    1 に戻らず q^{j²} に届く。 -/
theorem q9tq_thetaVal_npow_ne_one (j k : Nat) (hj : 0 < j) (hk : 0 < k) :
    tateNpow q9tlMx (q9tqThetaVal j) k ≠ q9tlMx.one := by
  intro h
  have h1 : (tateNpow q9tlMx (q9tqThetaVal j) k).1 = (0 : Int) := congrArg Prod.fst h
  rw [q9tl_npow_fst (q9tqThetaVal j) k, tateNpow_intGrp] at h1
  have h2 : (q9tqThetaVal j).1 = ((j * j : Nat) : Int) * 6 := q9tq_thetaVal_fst j
  rw [h2] at h1
  have hjj : 0 < j * j := Nat.mul_pos hj hj
  obtain hzk | hzs := Int.mul_eq_zero.mp h1
  · omega
  · omega

/-- **q9tq-6d（★ 負例 j=1）: Θ₁ = 3 は q 冪ではない**（付値 6 ∉ 54ℤ・全整数指数で）。 -/
theorem q9tq_theta1_not_qpow (t : Int) :
    tateZpow q9tlMx q9tlQ t ≠ q9tqThetaVal 1 := by
  intro h
  have h1 : (tateZpow q9tlMx q9tlQ t).1 = (tateNpow q9tlMx q9tl3 (1 * 1)).1 :=
    congrArg Prod.fst h
  rw [q9tl_pow_fst t, q9tl_npow_fst_val (1 * 1)] at h1
  have h2 : t * 54 = ((1 * 1 : Nat) : Int) * 6 := h1
  omega

/-- **q9tq-6e（★ 負例 j=2）: Θ₂ = 3⁴ は q 冪ではない**（付値 24 ∉ 54ℤ・全整数指数で）。 -/
theorem q9tq_theta2_not_qpow (t : Int) :
    tateZpow q9tlMx q9tlQ t ≠ q9tqThetaVal 2 := by
  intro h
  have h1 : (tateZpow q9tlMx q9tlQ t).1 = (tateNpow q9tlMx q9tl3 (2 * 2)).1 :=
    congrArg Prod.fst h
  rw [q9tl_pow_fst t, q9tl_npow_fst_val (2 * 2)] at h1
  have h2 : t * 54 = ((2 * 2 : Nat) : Int) * 6 := h1
  omega

/-- 正例 j=3: Θ₃ = 3⁹ = q。**anti-dup 自己申告: この等式は rfl でも通る**（カーネルが
    u₆⁹ を計算する・`example : q9tqThetaVal 3 = q9tlQ := rfl` がコンパイルすることを確認済み）。
    よって本定理は新規 0 計上（q9tl_ninth_elt の transport 兼定義的事実）。二分法 q9tq-6f の
    逆方向は本定理でなく一般の q9tq_npow_mul 経路で証明している。 -/
theorem q9tq_theta3_qpow : q9tqThetaVal 3 = q9tlQ := q9tl_ninth_elt

/-- **q9tq-6f（★★ 旗艦・j² 二分法）: Θ_j ∈ q^ℕ ⟺ 3 ∣ j** — 二次指数族 {j²} は q 格子と
    j ≡ 0 (mod 3) でのみ交わる。順方向は付値 6j² = 54t ⟹ j² = 9t ⟹ 3 ∣ j
    （j² ≡ {0,1} mod 3 の場合分け・Nat.mul_mod・omega は原子化後のみ）、逆方向は
    Θ_{3m} = 3^{9m²} = q^{m²}。theta 側の指数構造（二次）と q 側（線形 54ℤ）の
    非対称性の完全な特徴付け。 -/
theorem q9tq_thetaVal_qpow_iff (j : Nat) :
    (∃ t : Nat, q9tqThetaVal j = tateNpow q9tlMx q9tlQ t) ↔ (∃ m : Nat, j = 3 * m) := by
  constructor
  · intro hex
    obtain ⟨t, ht⟩ := hex
    have hf : (q9tqThetaVal j).1 = (tateNpow q9tlMx q9tlQ t).1 := congrArg Prod.fst ht
    have hf2 : (tateNpow q9tlMx q9tl3 (j * j)).1 = (tateNpow q9tlMx q9tlQ t).1 := hf
    rw [q9tl_npow_fst_val (j * j), q9tl_npow_fst q9tlQ t, tateNpow_intGrp] at hf2
    have h54 : q9tlQ.1 = (54 : Int) := rfl
    rw [h54] at hf2
    have hf3 : ((j * j : Nat) : Int) * 6 = (t : Int) * 54 := hf2
    have hjj : j * j = 9 * t := by omega
    have hmod : (j * j) % 3 = ((j % 3) * (j % 3)) % 3 := Nat.mul_mod j j 3
    have hcase : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    obtain h0 | h1 | h2 := hcase
    · exact ⟨j / 3, by omega⟩
    · exfalso
      rw [h1] at hmod
      omega
    · exfalso
      rw [h2] at hmod
      omega
  · intro hex
    obtain ⟨m, hm⟩ := hex
    refine ⟨m * m, ?_⟩
    show tateNpow q9tlMx q9tl3 (j * j) = tateNpow q9tlMx q9tlQ (m * m)
    rw [hm]
    have hexp : (3 * m) * (3 * m) = 9 * (m * m) := by
      rw [Nat.mul_assoc 3 m (3 * m), ← Nat.mul_assoc m 3 m, Nat.mul_comm m 3,
          Nat.mul_assoc 3 m m, ← Nat.mul_assoc 3 3 (m * m)]
    rw [hexp, ← q9tl_ninth_elt, ← q9tq_npow_mul q9tlMx q9tl3 9 (m * m)]

/-- **q9tq-6g（★ コサイクル出自）: Θ_n = scalar(g_{[3]}ⁿ)⁻²·3ⁿ** — テータ値はテータ群
    コサイクル 3^{−Tri(n)} から n² = 2·Tri(n) + n（q9tq-1b）で再構成される
    （テータ等式のコサイクル部→テータ値の標準関係の実装・二次指数の出自の固定）。 -/
theorem q9tq_theta_from_cocycle (n : Nat) :
    q9tlMx.mul
      (q9tlMx.mul (q9tlMx.inv (tateNpow q9mtM q9mtG3 n).1.1)
        (q9tlMx.inv (tateNpow q9mtM q9mtG3 n).1.1))
      (tateNpow q9tlMx q9tl3 n)
    = q9tqThetaVal n := by
  rw [q9tq_g3_pow n]
  have hinv : q9tlMx.inv (tateZpow q9tlMx q9tl3 (-(q9tqTri n : Int)))
      = tateNpow q9tlMx q9tl3 (q9tqTri n) := by
    rw [tateZpow_neg, Grp.inv_inv]
    exact tateZpow_natCast q9tlMx q9tl3 (q9tqTri n)
  show q9tlMx.mul
      (q9tlMx.mul (q9tlMx.inv (tateZpow q9tlMx q9tl3 (-(q9tqTri n : Int))))
        (q9tlMx.inv (tateZpow q9tlMx q9tl3 (-(q9tqTri n : Int)))))
      (tateNpow q9tlMx q9tl3 n)
    = q9tqThetaVal n
  rw [hinv]
  show q9tlMx.mul
      (q9tlMx.mul (tateNpow q9tlMx q9tl3 (q9tqTri n)) (tateNpow q9tlMx q9tl3 (q9tqTri n)))
      (tateNpow q9tlMx q9tl3 n)
    = tateNpow q9tlMx q9tl3 (n * n)
  rw [← q9tq_npow_add q9tlMx q9tl3 (q9tqTri n) (q9tqTri n),
      ← q9tq_npow_add q9tlMx q9tl3 (q9tqTri n + q9tqTri n) n, q9tq_tri_sq n]

/-! ## q9tq-7: capstone（束ねのみ・新規証明ゼロ） -/

/-- **q9tq-7a: E4 theta-pilot vs q-pilot 非対称性データ** — 二次コサイクル法則・
    Θ 冪の真正 q 冪着地・pilot 比較 δ = (q⁻³,0,1) ≠ 1・捩れ非対称・j² 二分法・
    tempered デッキ接続を一括束ね。 -/
structure Q3ThetaQPilotAsymData where
  /-- ★ 二次コサイクル法則 g_{[3]}ⁿ = (3^{−Tri(n)}, −n, 3ⁿ)。 -/
  quad_law : ∀ n : Nat, tateNpow q9mtM q9mtG3 n
    = ((tateZpow q9tlMx q9tl3 (-(q9tqTri n : Int)), -(n : Int)), tateNpow q9tlMx q9tl3 n)
  /-- ★ g_{[3]}⁹ = (q⁻⁴, −9, q)（スカラーが真正 q 冪）。 -/
  pow9_scalar_qpow : tateNpow q9mtM q9mtG3 9
    = ((tateZpow q9tlMx q9tlQ (-4 : Int), (-9 : Int)), q9tlQ)
  /-- ★ pilot 比較 g_{[3]}⁹ = scalar(q⁻³)·g_τ。 -/
  pilot_comparison : tateNpow q9mtM q9mtG3 9
    = q9mtMul (q9ntScalar (tateZpow q9tlMx q9tlQ (-3 : Int))) q9mtTau
  /-- ★★ q 側非自明性 witness: δ ≠ 1（付値 −162）。 -/
  delta_ne_one : q9tqDelta ≠ q9mtOne
  /-- δ は中心的（真正 q 冪の中心スカラー）。 -/
  delta_central : ∀ g, q9mtM.mul q9tqDelta g = q9mtM.mul g q9tqDelta
  /-- δ・g_τ・g_{[3]}⁹ はテータ群の元。 -/
  delta_mem : q9mtMem q9tqDelta
  tau_mem : q9mtMem q9mtTau
  pilot_pow_mem : q9mtMem (tateNpow q9mtM q9mtG3 9)
  /-- ★★ Θ_j⁹ = q^{j²}（Θ^{2l} = q^{j²} の level-9 実形）。 -/
  theta_pow9_qpow : ∀ j : Nat,
    tateNpow q9tlMx (q9tqThetaVal j) 9 = tateNpow q9tlMx q9tlQ (j * j)
  /-- ★ Θ_j は 1 の冪根でない（全正冪 ≠ 1・q9tk の Θ = ζ₉ と対照）。 -/
  theta_not_root_of_unity : ∀ j k : Nat, 0 < j → 0 < k →
    tateNpow q9tlMx (q9tqThetaVal j) k ≠ q9tlMx.one
  /-- ★ j² 二分法 Θ_j ∈ q^ℕ ⟺ 3 ∣ j。 -/
  theta_qpow_iff : ∀ j : Nat,
    (∃ t : Nat, q9tqThetaVal j = tateNpow q9tlMx q9tlQ t) ↔ (∃ m : Nat, j = 3 * m)
  /-- 負例: Θ₁・Θ₂ は q 冪でない（全整数指数）。 -/
  theta1_not_qpow : ∀ t : Int, tateZpow q9tlMx q9tlQ t ≠ q9tqThetaVal 1
  theta2_not_qpow : ∀ t : Int, tateZpow q9tlMx q9tlQ t ≠ q9tqThetaVal 2
  /-- 捩れ非対称: g_{[ζ₉]}⁹ = 1 vs g_{[3]}ⁿ ≠ 1。 -/
  gz_torsion : tateNpow q9mtM q9mtGZeta 9 = q9mtOne
  g3_infinite : ∀ n : Nat, 0 < n → tateNpow q9mtM q9mtG3 n ≠ q9mtOne
  /-- q 部の対照: g_{[3]} 非自明・g_{[ζ₉]} 自明。 -/
  g3_qpart : q9mtG3.1.2 ≠ (0 : Int)
  gz_qpart : q9mtGZeta.1.2 = (0 : Int)
  /-- テータ値のコサイクル出自 Θ_n = scalar(g_{[3]}ⁿ)⁻²·3ⁿ。 -/
  theta_from_cocycle : ∀ n : Nat,
    q9tlMx.mul (q9tlMx.mul (q9tlMx.inv (tateNpow q9mtM q9mtG3 n).1.1)
      (q9tlMx.inv (tateNpow q9mtM q9mtG3 n).1.1)) (tateNpow q9tlMx q9tl3 n)
      = q9tqThetaVal n
  /-- tempered 接続 Ψ₉(s 9) = scalar(q⁻³)·g_τ。 -/
  deck9_pilot : q9ntPsi.map (tpeSection.map (9 : Int))
    = q9mtMul (q9ntScalar (tateZpow q9tlMx q9tlQ (-3 : Int))) q9mtTau

/-- **q9tq-7b: 見出し実例** — 実 level-9 テータ群上の theta-pilot vs q-pilot 非対称性。 -/
def q9tq_data : Q3ThetaQPilotAsymData where
  quad_law := q9tq_g3_pow
  pow9_scalar_qpow := q9tq_g3_pow9
  pilot_comparison := q9tq_pilot_comparison
  delta_ne_one := q9tq_delta_ne_one
  delta_central := q9tq_delta_central
  delta_mem := q9tq_delta_mem
  tau_mem := q9tq_tau_mem
  pilot_pow_mem := q9tq_pilot_pow_mem
  theta_pow9_qpow := q9tq_thetaVal_pow9
  theta_not_root_of_unity := q9tq_thetaVal_npow_ne_one
  theta_qpow_iff := q9tq_thetaVal_qpow_iff
  theta1_not_qpow := q9tq_theta1_not_qpow
  theta2_not_qpow := q9tq_theta2_not_qpow
  gz_torsion := q9tq_gz_pow9_one
  g3_infinite := q9tq_g3_npow_ne_one
  g3_qpart := q9tq_g3_qpart_nontrivial
  gz_qpart := q9tq_gz_qpart_trivial
  theta_from_cocycle := q9tq_theta_from_cocycle
  deck9_pilot := q9tq_deck9_pilot

/-- **q9tq-7c: E4 theta-pilot vs q-pilot 非対称性の存在**（実 M₉・実 M^×・実 q = 3⁹ の上）。 -/
theorem q9tq_exists : Nonempty Q3ThetaQPilotAsymData := ⟨q9tq_data⟩

end IUT
