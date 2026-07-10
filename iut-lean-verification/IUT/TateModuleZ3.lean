/-
  IUT/TateModuleZ3.lean — TMZ（柱A7 A7b: 実 Tate 加群 T = ℤ₃(1) = lim μ_{3^{n+1}}
  ——実 μ 塔 μ_{3¹} ← μ_{3²} ← μ_{3³} ← … の逆極限——と、実 profinite
  Gal(ℚ(ζ_{3^∞})/ℚ) の T への作用が円分指標 χ の冪で記述されること）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・実円分体
     ℚ(ζ_{3^{n+1}}) の中の実 μ_{3^{n+1}}=`cmrGrp (n+1)`（cmr で本物に構成）を Nat 添字
     n に並べ、**指数読み替え**の遷移射 `tmzT` で本物の逆系 `tmzSystem` を組み、その
     逆極限 `tmzLimit = T = ℤ₃(1)` を本物に構成する。各段の μ は別々の体
     ℚ(ζ_{3^{n+1}}) に住む（K̄ を持たない——§7 の正直な限定）ので、遷移は zps `zpsT`
     と同じ発想の**単発の指数読み替え**（y=ζ_{j+1}^e ↦ ζ_{i+1}^e・choice-free）で書き、
     それが本物の Tate 遷移（3 乗写像を実埋め込み ι で読んだもの）であることを
     `tmz_iota_cube`（ι(t y)=y³）で担保する。実 Gal の T への作用 `tmzActHom` は成分
     ごと実 Galois 作用 `cgarAct`（cgar で本物に構成）で与え、作用と遷移の可換
     `tmz_act_compat`（compat 正方形）を cli の指標 compat 正方形 `cli_char_restr` の
     再利用で本物に閉じ、作用が χ 冪であること `tmz_act_char` を確立する。

  **complete_pct 影響**: A7（実円分剛性）A7b——**実 Tate 加群 T = ℤ₃(1) = lim μ_{3^{n+1}}
  （実 μ 塔の逆極限）を本物に構成し、実 profinite Gal(ℚ(ζ_{3^∞})/ℚ)=`ctlProfinite`
  （ctl で本物に構成）の T への作用が実円分指標 χ の冪で記述されること**を確立する。
  χ : G ≅ ℤ₃^× の同型は cli の `cliIsoData`（既存・再証明しない）を capstone
  `tmzTateData` に束ねるだけ。設計見込み A7 → 0.4（上限・円分切片・K̄/幾何的
  cyclotome 不在・mono-theta 未達）。本ファイル単体では complete_pct は独立監査で反映。

  内容（設計 audit/A7-real-cyclotomic-rigidity-detail-2026-07-10.md §3.1・TMZ-1〜6）:
   * `tmzG n`            — 塔の各段 μ_{3^{n+1}} = `cmrGrp (n+1)`。
   * `tmzT h`            — 遷移射 μ_{3^{j+1}} → μ_{3^{i+1}}（指数読み替え y↦ζ_{i+1}^{find y}）。
   * `tmz_t_self`/`tmz_t_comp` — 逆系則（恒等保存・推移性）。
   * `tmzSystem`/`tmzLimit` — ★逆系と逆極限 T = ℤ₃(1)。
   * `tmz_proj_surjective` — 各段射影の全射性（zps ZPS-4 の写経・witness は定数指数族）。
   * `tmz_iota_cube`    — ★忠実性証明書: ι(t y) = y³（遷移が実 cube 写像）。
   * `tmzActHom`        — 実 Gal の T への成分ごと実作用。
   * `tmz_act_compat`   — ★compat 正方形（cli_char_restr 再利用で本物に閉じる）。
   * `tmz_act_char`     — 作用は χ 冪（cgar_rigidity の成分適用）。
   * `TmzGModule`/`tmzGModule` — T=ℤ₃(1) の実 G-加群構造。
   * `TmzTateData`/`tmzTateData` — ★capstone（T・作用・χ≅ℤ₃^×・忠実性を束ねる）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   **p = 3 専用**。一般の p 進 Tate 加群 T_p ではない。
   (ii)  T は **逆極限としての ℤ₃(1)** lim μ_{3^{n+1}}（整合族の定義そのもの）であって、
         幾何的 Tate 加群（楕円曲線・K̄ 上の μ_n(K̄) の逆極限・π₁ の幾何的 cyclotome）
         ではない。各段の μ は別々の体 ℚ(ζ_{3^{n+1}}) に住み、K̄ を持たない。
   (iii) 作用させる G は Gal(ℚ(ζ_{3^∞})/ℚ)（G_ℚ の可解商）であって実絶対 Galois 群
         G_ℚ そのものではない（cgar/cli/ctl 正直申告を継承）。
   (iv)  χ を π₁^ét 位相群の連続指標として抽出する本丸（mono-theta 環境の円分剛性）は
         依然後続——弱めず継承。χ ≅ ℤ₃^× は cli `cliIsoData` の再利用。

  全て選択公理不使用（新規 `Classical.choice` を証明本体に導入しない・propext/Quot.sound
  のみ・自分で `#print axioms` を確認済み）。禁止タクティク（simp/decide/by_cases/rcases/
  ring/nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。3^ℓ は omega 不可
  （`zpu_pow_dvd`/`zpu_pow_pos` 再利用）。新規ファイル 1 個のみ（共有ファイル
  IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。prefix `tmz`。
-/
import IUT.CyclotomicGKActionReal
import IUT.CyclotomicLimitIso
import IUT.CyclotomicTowerLimit
import IUT.CyclotomicMuTower
import IUT.CyclotomicResTower
import IUT.Zmod3PowUnitsSystem

namespace IUT

/-! ## TMZ-0: 部品補題（find/pow の橋・指数算術） -/

/-- **TMZ-0a: 離散対数の逆** — μ_{3^ℓ} の元 y は ζ_ℓ の冪 y = ζ_ℓ^{find y}
    （`ctmFind_spec` の 1 番目・担体条件 y.property を rpow 仮説に流す）。 -/
theorem tmz_val_find (ℓ : Nat) (hℓ : 1 ≤ ℓ) (y : (cmrGrp ℓ hℓ).carrier) :
    y.val = ctmPow ℓ hℓ (ctmFind ℓ hℓ y.val) :=
  (ctmFind_spec ℓ hℓ y.val y.property).1

/-- **TMZ-0b: find∘pow = mod** — `ctmFind ℓ (ζ_ℓ^e) = e % 3^ℓ`
    （`ctmFind_spec` ＋ `cci_indexG`・ζ_ℓ^e は 3^ℓ 乗根 `ctmr_rpow_pow`）。 -/
theorem tmz_find_pow (ℓ : Nat) (hℓ : 1 ≤ ℓ) (e : Nat) :
    ctmFind ℓ hℓ (ctmPow ℓ hℓ e) = e % 3 ^ ℓ := by
  have hspec := ctmFind_spec ℓ hℓ (ctmPow ℓ hℓ e) (ctmr_rpow_pow ℓ hℓ e)
  exact (cci_indexG ℓ hℓ e (ctmFind ℓ hℓ (ctmPow ℓ hℓ e)) hspec.2 hspec.1).symm

/-- **TMZ-0c: 冪の準同型（群レベル）** — ζ_ℓ^a·ζ_ℓ^b = ζ_ℓ^{a+b}（担体 val は
    `ctmPow_add`・cmrGrp の mul は体の積）。 -/
theorem tmz_pow_add (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a b : Nat) :
    (cmrGrp ℓ hℓ).mul ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) a) ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) b)
      = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (a + b) := by
  apply Subtype.ext
  show (cteField ℓ hℓ).toCRing.mul
        ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) a).val ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) b).val
     = ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (a + b)).val
  rw [cmr_pow_zeta ℓ hℓ a, cmr_pow_zeta ℓ hℓ b, cmr_pow_zeta ℓ hℓ (a + b)]
  exact (ctmPow_add ℓ hℓ a b).symm

/-- **TMZ-0d: 冪の周期性（群レベル）** — ζ_ℓ^a = ζ_ℓ^{a%3^ℓ}（`ctm_pow_mod`）。 -/
theorem tmz_pow_mod (ℓ : Nat) (hℓ : 1 ≤ ℓ) (a : Nat) :
    (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) a = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (a % 3 ^ ℓ) := by
  apply Subtype.ext
  rw [cmr_pow_zeta ℓ hℓ a, cmr_pow_zeta ℓ hℓ (a % 3 ^ ℓ)]
  exact ctm_pow_mod ℓ hℓ a

/-- **TMZ-0e: 積の離散対数** — `find(y·z) = (find y + find z) % 3^ℓ`
    （`tmz_val_find` ＋ `ctmPow_add` ＋ `tmz_find_pow`）。 -/
theorem tmz_mul_find (ℓ : Nat) (hℓ : 1 ≤ ℓ) (y z : (cmrGrp ℓ hℓ).carrier) :
    ctmFind ℓ hℓ ((cmrGrp ℓ hℓ).mul y z).val
      = (ctmFind ℓ hℓ y.val + ctmFind ℓ hℓ z.val) % 3 ^ ℓ := by
  have hmulval : ((cmrGrp ℓ hℓ).mul y z).val
      = ctmPow ℓ hℓ (ctmFind ℓ hℓ y.val + ctmFind ℓ hℓ z.val) := by
    rw [ctmPow_add ℓ hℓ (ctmFind ℓ hℓ y.val) (ctmFind ℓ hℓ z.val)]
    show (ctmR ℓ hℓ).mul y.val z.val
       = (ctmR ℓ hℓ).mul (ctmPow ℓ hℓ (ctmFind ℓ hℓ y.val)) (ctmPow ℓ hℓ (ctmFind ℓ hℓ z.val))
    rw [← tmz_val_find ℓ hℓ y, ← tmz_val_find ℓ hℓ z]
  rw [hmulval, tmz_find_pow ℓ hℓ (ctmFind ℓ hℓ y.val + ctmFind ℓ hℓ z.val)]

/-! ## TMZ-1: 塔の各段 μ_{3^{n+1}} -/

/-- **TMZ-1: レベル n の μ** `tmzG n = μ_{3^{n+1}}`（ctlGal n = Gal(ℚ(ζ_{3^{n+1}})/ℚ)
    と添字を合わせる）。 -/
def tmzG (n : Nat) : Grp := cmrGrp (n + 1) (by omega)

/-! ## TMZ-2: 遷移射（指数読み替え・単発・choice-free） -/

/-- **TMZ-2: 遷移射 `tmzT`** — μ_{3^{j+1}} → μ_{3^{i+1}}（i ≤ j）。y = ζ_{j+1}^{find y}
    を ζ_{i+1}^{find y} に送る（指数読み替え・反復/cast 不要）。map_mul は
    `tmz_mul_find` ＋ `tmz_pow_add` ＋ `tmz_pow_mod` ＋ `Nat.mod_mod_of_dvd`。 -/
def tmzT {i j : Nat} (h : i ≤ j) : Hom (tmzG j) (tmzG i) where
  map := fun y =>
    (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega)) (ctmFind (j + 1) (by omega) y.val)
  map_mul := fun y z => by
    show (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
          (ctmFind (j + 1) (by omega) ((cmrGrp (j + 1) (by omega)).mul y z).val)
       = (cmrGrp (i + 1) (by omega)).mul
           ((cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
             (ctmFind (j + 1) (by omega) y.val))
           ((cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
             (ctmFind (j + 1) (by omega) z.val))
    rw [tmz_mul_find (j + 1) (by omega) y z,
        tmz_pow_add (i + 1) (by omega)
          (ctmFind (j + 1) (by omega) y.val) (ctmFind (j + 1) (by omega) z.val),
        tmz_pow_mod (i + 1) (by omega)
          (ctmFind (j + 1) (by omega) y.val + ctmFind (j + 1) (by omega) z.val),
        tmz_pow_mod (i + 1) (by omega)
          ((ctmFind (j + 1) (by omega) y.val + ctmFind (j + 1) (by omega) z.val) % 3 ^ (j + 1)),
        Nat.mod_mod_of_dvd _ (zpu_pow_dvd (show i + 1 ≤ j + 1 by omega))]

/-- **TMZ-2a: 恒等保存** — 自層への遷移は恒等（`tmz_val_find`）。 -/
theorem tmz_t_self (i : Nat) (y : (tmzG i).carrier) : (tmzT (Nat.le_refl i)).map y = y := by
  show (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega)) (ctmFind (i + 1) (by omega) y.val)
     = y
  apply Subtype.ext
  rw [cmr_pow_zeta (i + 1) (by omega) (ctmFind (i + 1) (by omega) y.val)]
  exact (tmz_val_find (i + 1) (by omega) y).symm

/-- **TMZ-2b: 推移性** — 遷移の合成は合成の遷移（`tmz_find_pow` ＋ 冪の周期性
    ＋ `Nat.mod_mod_of_dvd`・単発指数読み替えゆえ結合律 cast 不要）。 -/
theorem tmz_t_comp {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) (x : (tmzG k).carrier) :
    (tmzT hij).map ((tmzT hjk).map x) = (tmzT (Nat.le_trans hij hjk)).map x := by
  have hmid : ((tmzT hjk).map x).val
      = ctmPow (j + 1) (by omega) (ctmFind (k + 1) (by omega) x.val) :=
    cmr_pow_zeta (j + 1) (by omega) (ctmFind (k + 1) (by omega) x.val)
  show (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
        (ctmFind (j + 1) (by omega) ((tmzT hjk).map x).val)
     = (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
        (ctmFind (k + 1) (by omega) x.val)
  rw [hmid, tmz_find_pow (j + 1) (by omega) (ctmFind (k + 1) (by omega) x.val),
      tmz_pow_mod (i + 1) (by omega) (ctmFind (k + 1) (by omega) x.val),
      tmz_pow_mod (i + 1) (by omega) (ctmFind (k + 1) (by omega) x.val % 3 ^ (j + 1)),
      Nat.mod_mod_of_dvd _ (zpu_pow_dvd (show i + 1 ≤ j + 1 by omega))]

/-! ## TMZ-3: 逆系と逆極限 T = ℤ₃(1) -/

/-- **TMZ-3: 実 μ 塔の逆系**（`natSystem` 経由・Nat 添字・(≤)）。 -/
@[reducible] def tmzSystem : InverseSystem := natSystem tmzG tmzT tmz_t_self tmz_t_comp

/-- **TMZ-3a: ★逆極限 T = ℤ₃(1) = lim μ_{3^{n+1}}**（実 μ 塔の逆極限）。 -/
def tmzLimit : Grp := limitGrp tmzSystem

/-! ## TMZ-4: 各段射影の全射性（zps ZPS-4 の写経・witness は定数指数族） -/

/-- **TMZ-4a: witness 族** — `y` の離散対数 `e = find y` を各段 ζ_{m+1}^e に載せる
    定数指数族（閉じた式・choice-free）。 -/
def tmzWitnessFam (n : Nat) (y : (tmzG n).carrier) (m : Nat) : (tmzG m).carrier :=
  (cmrGrp (m + 1) (by omega)).pow (cmrZeta (m + 1) (by omega)) (ctmFind (n + 1) (by omega) y.val)

/-- **TMZ-4b: witness 族の整合性** — `tmzWitnessFam` は `tmzSystem` の整合族
    （`tmz_find_pow` ＋ 冪の周期性 ＋ `Nat.mod_mod_of_dvd`）。 -/
theorem tmzWitnessFam_compat (n : Nat) (y : (tmzG n).carrier) :
    Compatible tmzSystem (tmzWitnessFam n y) := by
  intro a b h
  have hab : a ≤ b := h
  show (tmzT h).map (tmzWitnessFam n y b) = tmzWitnessFam n y a
  have hwb : (tmzWitnessFam n y b).val
      = ctmPow (b + 1) (by omega) (ctmFind (n + 1) (by omega) y.val) :=
    cmr_pow_zeta (b + 1) (by omega) (ctmFind (n + 1) (by omega) y.val)
  show (cmrGrp (a + 1) (by omega)).pow (cmrZeta (a + 1) (by omega))
        (ctmFind (b + 1) (by omega) (tmzWitnessFam n y b).val)
     = (cmrGrp (a + 1) (by omega)).pow (cmrZeta (a + 1) (by omega)) (ctmFind (n + 1) (by omega) y.val)
  rw [hwb, tmz_find_pow (b + 1) (by omega) (ctmFind (n + 1) (by omega) y.val),
      tmz_pow_mod (a + 1) (by omega) (ctmFind (n + 1) (by omega) y.val),
      tmz_pow_mod (a + 1) (by omega) (ctmFind (n + 1) (by omega) y.val % 3 ^ (b + 1)),
      Nat.mod_mod_of_dvd _ (zpu_pow_dvd (Nat.succ_le_succ hab))]

/-- **TMZ-4: 射影全射性** — 任意のレベル n・任意の μ_{3^{n+1}} の元 y に対し、
    極限 T の元 t で `(limitProj tmzSystem n).map t = y` となるものが存在する
    （witness は定数指数族・choice-free）。 -/
theorem tmz_proj_surjective (n : Nat) (y : (tmzG n).carrier) :
    ∃ t : tmzLimit.carrier, (limitProj tmzSystem n).map t = y := by
  refine ⟨⟨tmzWitnessFam n y, tmzWitnessFam_compat n y⟩, ?_⟩
  show tmzWitnessFam n y n = y
  apply Subtype.ext
  show ((cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
          (ctmFind (n + 1) (by omega) y.val)).val = y.val
  rw [cmr_pow_zeta (n + 1) (by omega) (ctmFind (n + 1) (by omega) y.val)]
  exact (tmz_val_find (n + 1) (by omega) y).symm

/-! ## TMZ-5: ★忠実性証明書 — 遷移は実 cube 写像を実埋め込み ι で読んだもの -/

/-- **TMZ-5: 忠実性証明書** — 段間埋め込み ι_{n+1}（cte `cteIota`・x̄↦x̄³）で
    遷移 `tmzT` の像を読むと、元の 3 乗になる: ι(t y) = y³。
    ι(ζ_{n+1}^{find y}) = ζ_{n+2}^{3·find y}（`ctr_map_pow`）= (ζ_{n+2}^{find y})³ = y³
    （`ctmr_rpow_ctmPow`）。⟹ tmzLimit を ℤ₃(1) と呼ぶ根拠（遷移が実 cube 写像）。 -/
theorem tmz_iota_cube (n : Nat) (y : (tmzG (n + 1)).carrier) :
    (cteIota (n + 1) (by omega)).map (((tmzT (Nat.le_succ n)).map y).val)
      = rpow (cteField (n + 2) (by omega)).toCRing y.val 3 := by
  have hv : ((tmzT (Nat.le_succ n)).map y).val
      = ctmPow (n + 1) (by omega) (ctmFind (n + 2) (by omega) y.val) :=
    cmr_pow_zeta (n + 1) (by omega) (ctmFind (n + 2) (by omega) y.val)
  have hiota : (cteIota (n + 1) (by omega)).map
        (ctmPow (n + 1) (by omega) (ctmFind (n + 2) (by omega) y.val))
      = ctmPow (n + 2) (by omega) (3 * ctmFind (n + 2) (by omega) y.val) :=
    ctr_map_pow (n + 1) (by omega) (ctmFind (n + 2) (by omega) y.val)
  have hyv : y.val = ctmPow (n + 2) (by omega) (ctmFind (n + 2) (by omega) y.val) :=
    tmz_val_find (n + 2) (by omega) y
  have hrhs : rpow (cteField (n + 2) (by omega)).toCRing y.val 3
      = ctmPow (n + 2) (by omega) (ctmFind (n + 2) (by omega) y.val * 3) :=
    (congrArg (fun w => rpow (cteField (n + 2) (by omega)).toCRing w 3) hyv).trans
      (ctmr_rpow_ctmPow (n + 2) (by omega) (ctmFind (n + 2) (by omega) y.val) 3)
  rw [hv, hiota, hrhs, Nat.mul_comm (ctmFind (n + 2) (by omega) y.val) 3]

/-! ## TMZ-6: ★compat 正方形（cli_char_restr 再利用で本物に閉じる） -/

/-- **TMZ-6: ★compat 正方形（作用と遷移の可換）** — 実 Gal の実 μ 塔への作用
    `cgarAct` と遷移 `tmzT` が可換: t(σ y) = (res σ)(t y)。
    両辺の指数を計算し（`ctr_sigma_powG`・`tmz_find_pow`）、指標の compat 正方形
    `cli_char_restr`（cli の i≤j 一般差分帰納・再利用）で χ_i(res σ) = χ_j(σ) % 3^{i+1}
    を得、`Nat.mul_mod` ＋ `Nat.mod_mod_of_dvd` で合流する。 -/
theorem tmz_act_compat {i j : Nat} (h : i ≤ j)
    (σ : (ctlGal j).carrier) (y : (tmzG j).carrier) :
    (tmzT h).map (((cgarAct (j + 1) (by omega)).act σ).map y)
      = ((cgarAct (i + 1) (by omega)).act ((ctlRestr h).map σ)).map ((tmzT h).map y) := by
  apply Subtype.ext
  -- σ(y) = ζ_{j+1}^{χ_j(σ)·find y}
  have hsy : σ.val.toFun y.val
      = ctmPow (j + 1) (by omega)
          (ctr_charG (j + 1) (by omega) σ.val * ctmFind (j + 1) (by omega) y.val) := by
    have h1 : σ.val.toFun (ctmPow (j + 1) (by omega) (ctmFind (j + 1) (by omega) y.val))
        = ctmPow (j + 1) (by omega)
            (ctr_charG (j + 1) (by omega) σ.val * ctmFind (j + 1) (by omega) y.val) :=
      ctr_sigma_powG (j + 1) (by omega) σ.val (ctmFind (j + 1) (by omega) y.val)
    rw [← tmz_val_find (j + 1) (by omega) y] at h1
    exact h1
  -- χ_i(res σ) = χ_j(σ) % 3^{i+1}（cli の compat 正方形の再利用）
  have hchar : ctr_charG (i + 1) (by omega) ((ctlRestr h).map σ).val
      = ctr_charG (j + 1) (by omega) σ.val % 3 ^ (i + 1) :=
    congrArg Subtype.val (cli_char_restr h σ)
  -- 指数算術
  have hmm : (ctr_charG (j + 1) (by omega) σ.val * ctmFind (j + 1) (by omega) y.val)
        % 3 ^ (j + 1) % 3 ^ (i + 1)
      = (ctr_charG (j + 1) (by omega) σ.val * ctmFind (j + 1) (by omega) y.val) % 3 ^ (i + 1) :=
    Nat.mod_mod_of_dvd _ (zpu_pow_dvd (show i + 1 ≤ j + 1 by omega))
  have harith : (ctr_charG (j + 1) (by omega) σ.val * ctmFind (j + 1) (by omega) y.val)
        % 3 ^ (i + 1)
      = (ctr_charG (j + 1) (by omega) σ.val % 3 ^ (i + 1) * ctmFind (j + 1) (by omega) y.val)
        % 3 ^ (i + 1) := by
    rw [Nat.mul_mod (ctr_charG (j + 1) (by omega) σ.val) (ctmFind (j + 1) (by omega) y.val)
          (3 ^ (i + 1)),
        Nat.mul_mod (ctr_charG (j + 1) (by omega) σ.val % 3 ^ (i + 1))
          (ctmFind (j + 1) (by omega) y.val) (3 ^ (i + 1)),
        Nat.mod_mod_of_dvd (ctr_charG (j + 1) (by omega) σ.val) (Nat.dvd_refl (3 ^ (i + 1)))]
  show ((cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
          (ctmFind (j + 1) (by omega) (σ.val.toFun y.val))).val
     = ((ctlRestr h).map σ).val.toFun
          (((cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
             (ctmFind (j + 1) (by omega) y.val)).val)
  rw [cmr_pow_zeta (i + 1) (by omega) (ctmFind (j + 1) (by omega) (σ.val.toFun y.val)),
      cmr_pow_zeta (i + 1) (by omega) (ctmFind (j + 1) (by omega) y.val),
      hsy,
      tmz_find_pow (j + 1) (by omega)
        (ctr_charG (j + 1) (by omega) σ.val * ctmFind (j + 1) (by omega) y.val),
      ctr_sigma_powG (i + 1) (by omega) ((ctlRestr h).map σ).val
        (ctmFind (j + 1) (by omega) y.val),
      hchar,
      ctm_pow_mod (i + 1) (by omega)
        ((ctr_charG (j + 1) (by omega) σ.val * ctmFind (j + 1) (by omega) y.val) % 3 ^ (j + 1)),
      ctm_pow_mod (i + 1) (by omega)
        (ctr_charG (j + 1) (by omega) σ.val % 3 ^ (i + 1) * ctmFind (j + 1) (by omega) y.val),
      hmm, harith]

/-! ## TMZ-7: 実 Gal の T への作用（成分ごと実作用） -/

/-- **TMZ-7: G = Gal(ℚ(ζ_{3^∞})/ℚ) の T への作用** — s ∈ ctlProfinite に対し、
    成分ごと実 Galois 作用 `cgarAct` を施す群自己準同型 T → T。整合性
    （compat）は `tmz_act_compat` ＋ s/y の整合族性、map_mul は成分ごと
    `cgarAct` の map_mul。 -/
def tmzActHom (s : ctlProfinite.carrier) : Hom tmzLimit tmzLimit where
  map := fun y => ⟨fun n => ((cgarAct (n + 1) (by omega)).act (s.val n)).map (y.val n), by
    intro a b h
    show (tmzT h).map (((cgarAct (b + 1) (by omega)).act (s.val b)).map (y.val b))
       = ((cgarAct (a + 1) (by omega)).act (s.val a)).map (y.val a)
    have hs : (ctlRestr h).map (s.val b) = s.val a := s.property h
    have hy : (tmzT h).map (y.val b) = y.val a := y.property h
    rw [tmz_act_compat h (s.val b) (y.val b), hs, hy]⟩
  map_mul := fun y z => by
    apply Subtype.ext
    funext n
    exact ((cgarAct (n + 1) (by omega)).act (s.val n)).map_mul (y.val n) (z.val n)

/-! ## TMZ-8: 作用は χ 冪（cgar_rigidity の成分適用） -/

/-- **TMZ-8: 作用は χ 冪** — T への G 作用の n 成分は ζ_{n+1}^{χ_n(s_n)·find(y_n)}
    （`cgar_rigidity` の成分適用・χ 抽出は `cgar_exp_eq`＝`cliChar` の指標）。
    「T への G 作用は χ で一意決定」の実内容。 -/
theorem tmz_act_char (s : ctlProfinite.carrier) (y : tmzLimit.carrier) (n : Nat) :
    ((tmzActHom s).map y).val n
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
          (((cliChar n).map (s.val n)).val * ctmFind (n + 1) (by omega) (y.val n).val) := by
  have hexp : cycRigExp (galoisGroupGrp (cteExt (n + 1) (by omega))) (cmrMu (n + 1) (by omega))
        (cgarAct (n + 1) (by omega)) (s.val n)
      = ((cliChar n).map (s.val n)).val :=
    cgar_exp_eq (n + 1) (by omega) (s.val n)
  show ((cgarAct (n + 1) (by omega)).act (s.val n)).map (y.val n)
     = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
         (((cliChar n).map (s.val n)).val * ctmFind (n + 1) (by omega) (y.val n).val)
  rw [cgar_rigidity (n + 1) (by omega) (s.val n) (y.val n), hexp]

/-! ## TMZ-9: 実 G-加群構造 -/

/-- **TMZ-9a: T = ℤ₃(1) の実 G-加群構造**（巡回でなく pro-巡回ゆえ CycGKAction 型
    ではなく act/act_one/act_mul を直接束ねる）。 -/
structure TmzGModule where
  /-- G = Gal(ℚ(ζ_{3^∞})/ℚ) の各元 s の T への群自己準同型。 -/
  act : ctlProfinite.carrier → Hom tmzLimit tmzLimit
  /-- 単位元の作用は恒等。 -/
  act_one : ∀ y, (act ctlProfinite.one).map y = y
  /-- 合成則。 -/
  act_mul : ∀ s t y, (act (ctlProfinite.mul s t)).map y = (act s).map ((act t).map y)

/-- **TMZ-9b: witness** — 成分ごと `cgarAct` の act_one/act_mul で全フィールド充填。 -/
def tmzGModule : TmzGModule where
  act := tmzActHom
  act_one := fun y => by
    apply Subtype.ext
    funext n
    exact (cgarAct (n + 1) (by omega)).act_one (y.val n)
  act_mul := fun s t y => by
    apply Subtype.ext
    funext n
    exact (cgarAct (n + 1) (by omega)).act_mul (s.val n) (t.val n) (y.val n)

/-! ## TMZ-10: capstone — T = ℤ₃(1)・作用・χ≅ℤ₃^×・忠実性 -/

/-- **TMZ-10a: 実 Tate 加群データ** — T = ℤ₃(1)=lim μ_{3^{n+1}}（実 μ 塔の逆極限）の
    実 G-加群構造・χ : G ≅ ℤ₃^×（cli 再利用）・作用の χ 冪記述・遷移の忠実性証明書
    （ι(t y)=y³）・各段射影の全射性を束ねる。 -/
structure TmzTateData where
  /-- T=ℤ₃(1) の実 G-加群構造。 -/
  module : TmzGModule
  /-- χ : Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^×（cli `cliIsoData` の再利用）。 -/
  char_iso : CliIsoData
  /-- 作用は χ 冪で記述される。 -/
  act_by_char : ∀ (s : ctlProfinite.carrier) (y : tmzLimit.carrier) (n : Nat),
    ((module.act s).map y).val n
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
          (((cliChar n).map (s.val n)).val * ctmFind (n + 1) (by omega) (y.val n).val)
  /-- 遷移の忠実性証明書 ι(t y) = y³。 -/
  iota_cube : ∀ (n : Nat) (y : (tmzG (n + 1)).carrier),
    (cteIota (n + 1) (by omega)).map (((tmzT (Nat.le_succ n)).map y).val)
      = rpow (cteField (n + 2) (by omega)).toCRing y.val 3
  /-- 各段射影の全射性。 -/
  proj_surj : ∀ (n : Nat) (y : (tmzG n).carrier),
    ∃ t : tmzLimit.carrier, (limitProj tmzSystem n).map t = y

/-- **TMZ-10b: witness** — 全フィールド既証明の純レコード。実 Tate 加群
    T = ℤ₃(1) の A7b 完全証明（構成＋作用の χ 記述＋忠実性）。 -/
def tmzTateData : TmzTateData where
  module := tmzGModule
  char_iso := cliIsoData
  act_by_char := tmz_act_char
  iota_cube := tmz_iota_cube
  proj_surj := tmz_proj_surjective

end IUT
