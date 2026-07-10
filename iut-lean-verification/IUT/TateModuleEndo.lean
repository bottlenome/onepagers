/-
  IUT/TateModuleEndo.lean — TME（柱A7 A7d: 実 Tate 加群 T = ℤ₃(1) = `tmzLimit` の
  自己準同型の完全分類——「T の任意の抽象群自己準同型は自動的に整合冪族（=ℤ₃ 元）で
  尽くされる」（自動連続性/線型性の代数版）——を本物に建設する）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、既存の実 Tate 加群
     T = ℤ₃(1) = `tmzLimit`（実 μ 塔 μ_{3^{n+1}} の逆極限・tmz で本物に構成）を主語に、
     **可除性フィルトレーション**（level n 自明 ⟺ T 内 3^{n+1} 乗・witness は Nat 除算の
     閉じた式 `tmeRootFam`）と、それに基づく**自動降下**（任意の抽象 Hom f: T→T は
     ker proj_n を保ち各レベルへ降下）を証明し、**End(ℤ₃(1)) = 整合指数族**という
     極限対象上の新定理を建設する。レベル ℓ 単位の初等剛性 `cra_endo_pow`（生成元の像で
     決まる古典）とは異なり、極限では「降下する」こと自体が可除性を要する本物の内容。

  **complete_pct 影響**: A7（実円分剛性）A7d——**実 ℤ₃(1) の抽象自己準同型が整合冪族で
  完全分類される**（`tme_endo_pow`＋`tme_char_compat`）ことを極限レベルで確立する。
  A7d 単体では complete_pct を親は独立監査に諮る（A7e = `TateModuleIndeterminacy` 到達で
  「不定性は正確に実 ℤ₃^×」まで昇格予定）。本ファイルは A7 の監査ディスカウント理由
  「剛性内容がレベル単位・初等」を極限剛性で正面から解消する。数値は独立監査が確定。

  内容（設計 audit/A7-real-cyclotomic-rigidity-deepen-2026-07-10.md §3.1・TME-0〜5）:
   * `tme_pow_level`      — 極限群の冪は成分ごと（k 帰納）。TME-0。
   * `tme_t_apply`        — 遷移射 `tmzT` の適用形（rfl 補題・本ファイル簿記の基盤）。
   * `tme_find_dvd`       — 核の可除性の指数側（level n 自明なら find は 3^{n+1} で割れる）。TME-1。
   * `tmeRootFam`/`tmeRootFam_compat` — ★可除性 witness（本ファイルの数学的本体・div/mod 簿記）。TME-2。
   * `tme_ker_pow`        — ★核の可除性（level n 自明 ⟺ 3^{n+1} 乗・choice-free witness）。TME-2。
   * `tme_ker_preserved`/`tme_ker_congr` — ★核の保存（自動降下の鍵）。TME-3。
   * `tmeLift`/`tme_lift_proj`/`tme_lift_diff_ker` — 標準 witness リフトと差の核性。TME-4。
   * `tmeLevel`/`tme_level_map` — 降下したレベル写像。TME-4。
   * `tmeChar`/`tme_endo_pow`/`tme_char_compat`/`tme_endo_ext` — ★End 完全分類。TME-5。
   * `TmeEndoData`/`tmeEndoData` — capstone。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (1) **mono-theta 円分剛性（[EtTh]）は依然 0**: 本ステップは ẑ^×（p=3: ℤ₃^×）不定性を
       殺さない。End/Aut を分類しその不定性を*特徴付ける*だけで、テータ環境がこの不定性を
       消す仕組み（IUT 本丸・柱 E/D 後続）は範囲外。A7=1 には依然遠い。
   (2) **p = 3 固定・円分切片限定**: T = ℤ₃(1)、G = Gal(ℚ(ζ_{3^∞})/ℚ)。実 G_{ℚ₃}・
       実 G_ℚ・一般素数 p は含めない（tmz/cra/cli の正直申告を継承）。
   (3) **「自動連続性」は代数版**: 可除性フィルトレーション（ker proj_n の保存）経由であり、
       `limitTopology` に対する連続写像の定理としては述べない（位相は未形式化）。
   (4) **End(ℤ₃(1)) ≅ ℤ₃ は指数族表示**: 分類先は整合 Nat 族（`tmeChar`＋`tme_char_compat`）
       であり、A2 の実 ℤ₃ 環オブジェクト（z3）との**環同型接続は未形式化**（End の環構造・
       合成=積も未・後続の昇格ターゲット）。
   (5) **幾何側は不在のまま**: μ 塔は各段別々の実円分体に住む（K̄ なし）。楕円曲線の
       幾何的 Tate 加群・π₁ の幾何的 cyclotome ではない（tmz の限定を継承）。
   (6) 既存の正直な限定（tmz (i)–(iv)・cra (i)–(iv)）は一切消さない・弱めない。並置＋昇格のみ。

  全て選択公理不使用（新規 `Classical.choice` を証明本体に導入しない・propext/Quot.sound
  のみ）。禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。3^ℓ は omega に生では渡さない（`zpu_pow_pos`/
  `zpu_pow_dvd`/`Nat.pow_add`/`Nat.mul_mod_mul_right` 経由）。∃ は Prop ゴール内のみ
  （`tme_ker_pow`）。新規ファイル 1 個のみ（共有ファイルは親が統合）。prefix `tme`。
-/
import IUT.TateModuleZ3
import IUT.CyclotomicRigidityAut
import IUT.CyclotomicCharIso
import IUT.Zmod3PowUnits

namespace IUT

/-! ## TME-0: 極限群の冪は成分ごと -/

/-- **TME-0: 極限群の冪は成分ごと** — `(tmzLimit.pow y k).val n = (tmzG n).pow (y.val n) k`
    （k 帰納・`limitGrp.mul` は成分ごと）。 -/
theorem tme_pow_level (y : tmzLimit.carrier) (k n : Nat) :
    (tmzLimit.pow y k).val n = (tmzG n).pow (y.val n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (tmzG n).mul (y.val n) ((tmzLimit.pow y k).val n)
       = (tmzG n).mul (y.val n) ((tmzG n).pow (y.val n) k)
    rw [ih]

/-- **TME-補: 遷移射 `tmzT` の適用形**（定義展開・rfl）。y = ζ_{j+1}^{find y} を
    ζ_{i+1}^{find y} に送る指数読み替えを明示形で取り出す（以降 rw で多用）。 -/
theorem tme_t_apply {i j : Nat} (h : i ≤ j) (v : (tmzG j).carrier) :
    (tmzT h).map v
      = (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
          (ctmFind (j + 1) (by omega) v.val) := rfl

/-! ## TME-1: 核の可除性の指数側 -/

/-- **TME-1: 核の可除性の指数側** — `y` が level n で自明（y.val n = 1）なら、上段
    `y.val (k+n+1)` の離散対数 `find` は 3^{n+1} で割り切れる。y.property で
    y.val n = tmzT(y.val (k+n+1)) = ζ_{n+1}^{find}、一方 one = ζ_{n+1}^0 ゆえ
    `cci_indexG` で find % 3^{n+1} = 0。 -/
theorem tme_find_dvd (n k : Nat) (y : tmzLimit.carrier) (hy : y.val n = (tmzG n).one) :
    3 ^ (n + 1) ∣ ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val) := by
  have hle : n ≤ k + n + 1 := by omega
  have hc : (tmzT hle).map (y.val (k + n + 1)) = (tmzG n).one := by
    have hp : (tmzT hle).map (y.val (k + n + 1)) = y.val n := y.property hle
    rw [hp]; exact hy
  rw [tme_t_apply hle (y.val (k + n + 1))] at hc
  -- hc : (cmrGrp (n+1)).pow ζ (find) = (tmzG n).one
  have hone : (tmzG n).one.val = ctmPow (n + 1) (by omega) 0 :=
    cmr_pow_zeta (n + 1) (by omega) 0
  have hval : ctmPow (n + 1) (by omega)
        (ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val))
      = ctmPow (n + 1) (by omega) 0 := by
    have h1 := congrArg Subtype.val hc
    rw [cmr_pow_zeta (n + 1) (by omega)
          (ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val)), hone] at h1
    exact h1
  have hmod : ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val) % 3 ^ (n + 1) = 0 :=
    cci_indexG (n + 1) (by omega)
      (ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val)) 0
      (by have := zpu_pow_pos (n + 1); omega) hval
  exact Nat.dvd_of_mod_eq_zero hmod

/-! ## TME-2: ★可除性フィルトレーションの witness（本ファイルの数学的本体） -/

/-- **TME-2 補（Nat 純算術）: div/mod 簿記** — e_i = e_j % 3^{i+n+2} かつ両者 3^{n+1}
    で割り切れるなら (e_j/3^{n+1}) % 3^{i+1} = (e_i/3^{n+1}) % 3^{i+1}。
    3^{i+n+2}=3^{i+1}·3^{n+1}（`Nat.pow_add`）＋ `Nat.mul_mod_mul_right`＋3^{n+1}>0 の約分。 -/
theorem tme_div_mod_helper (ei ej i n : Nat)
    (hdi : 3 ^ (n + 1) ∣ ei) (hdj : 3 ^ (n + 1) ∣ ej)
    (hstar : ei = ej % 3 ^ (i + n + 2)) :
    (ej / 3 ^ (n + 1)) % 3 ^ (i + 1) = (ei / 3 ^ (n + 1)) % 3 ^ (i + 1) := by
  have hp : (3 : Nat) ^ (i + n + 2) = 3 ^ (i + 1) * 3 ^ (n + 1) := by
    rw [show i + n + 2 = (i + 1) + (n + 1) by omega]
    exact Nat.pow_add 3 (i + 1) (n + 1)
  have haj : ej / 3 ^ (n + 1) * 3 ^ (n + 1) = ej := Nat.div_mul_cancel hdj
  have hai : ei / 3 ^ (n + 1) * 3 ^ (n + 1) = ei := Nat.div_mul_cancel hdi
  have hpos : 0 < 3 ^ (n + 1) := by have := zpu_pow_pos (n + 1); omega
  have hmm := Nat.mul_mod_mul_right (3 ^ (n + 1)) (ej / 3 ^ (n + 1)) (3 ^ (i + 1))
  rw [haj] at hmm
  -- hmm : ej % (3^{i+1} * 3^{n+1}) = (ej/3^{n+1}) % 3^{i+1} * 3^{n+1}
  have key : ei = (ej / 3 ^ (n + 1)) % 3 ^ (i + 1) * 3 ^ (n + 1) := by
    rw [hstar, hp]; exact hmm
  have hcancel : ei / 3 ^ (n + 1) = (ej / 3 ^ (n + 1)) % 3 ^ (i + 1) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hai]; exact key
  rw [hcancel]
  exact (Nat.mod_mod_of_dvd (ej / 3 ^ (n + 1)) (Nat.dvd_refl (3 ^ (i + 1)))).symm

/-- **TME-2a: 可除性の根 witness**（閉じた式・Nat 除算・choice-free） — level n 自明な
    `y` の各段 k に対し、ζ_{k+1}^{find(y_{k+n+1})/3^{n+1}}。3^{n+1} 乗すると y_k に戻る。 -/
def tmeRootFam (n : Nat) (y : tmzLimit.carrier) (k : Nat) : (tmzG k).carrier :=
  (cmrGrp (k + 1) (by omega)).pow (cmrZeta (k + 1) (by omega))
    (ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val) / 3 ^ (n + 1))

/-- **TME-2b（★本体）: 根 witness の整合性** — `tmeRootFam n y` は `tmzSystem` の整合族。
    指数側は `tme_div_mod_helper`（div/mod 簿記）＋ y の整合族性から来る
    e_i = e_j % 3^{i+n+2} と TME-1 の可除性、ζ 側は `tmz_find_pow`＋`cra_pow_reduce`。 -/
theorem tmeRootFam_compat (n : Nat) (y : tmzLimit.carrier)
    (hy : y.val n = (tmzG n).one) : Compatible tmzSystem (tmeRootFam n y) := by
  intro i j h
  have hij : i ≤ j := h
  -- (*) e_i = e_j % 3^{i+n+2}
  have hle2 : i + n + 1 ≤ j + n + 1 := Nat.add_le_add_right (Nat.add_le_add_right hij n) 1
  have hc2 : (tmzT hle2).map (y.val (j + n + 1)) = y.val (i + n + 1) := y.property hle2
  rw [tme_t_apply hle2 (y.val (j + n + 1))] at hc2
  have hstar : ctmFind (i + n + 2) (by omega) ((y.val (i + n + 1)).val)
             = ctmFind (j + n + 2) (by omega) ((y.val (j + n + 1)).val) % 3 ^ (i + n + 2) := by
    have hval2 : ctmPow (i + n + 2) (by omega)
          (ctmFind (j + n + 2) (by omega) ((y.val (j + n + 1)).val))
        = (y.val (i + n + 1)).val := by
      have h1 := congrArg Subtype.val hc2
      rw [← cmr_pow_zeta (i + n + 2) (by omega)
            (ctmFind (j + n + 2) (by omega) ((y.val (j + n + 1)).val))]
      exact h1
    rw [← hval2, tmz_find_pow (i + n + 2) (by omega)
          (ctmFind (j + n + 2) (by omega) ((y.val (j + n + 1)).val))]
  -- 可除性
  have hdi : 3 ^ (n + 1) ∣ ctmFind (i + n + 2) (by omega) ((y.val (i + n + 1)).val) :=
    tme_find_dvd n i y hy
  have hdj : 3 ^ (n + 1) ∣ ctmFind (j + n + 2) (by omega) ((y.val (j + n + 1)).val) :=
    tme_find_dvd n j y hy
  have hexp := tme_div_mod_helper
    (ctmFind (i + n + 2) (by omega) ((y.val (i + n + 1)).val))
    (ctmFind (j + n + 2) (by omega) ((y.val (j + n + 1)).val))
    i n hdi hdj hstar
  -- ζ 側翻訳
  show (tmzT h).map (tmeRootFam n y j) = tmeRootFam n y i
  rw [tme_t_apply h (tmeRootFam n y j)]
  have hrjval : (tmeRootFam n y j).val
      = ctmPow (j + 1) (by omega)
          (ctmFind (j + n + 2) (by omega) ((y.val (j + n + 1)).val) / 3 ^ (n + 1)) :=
    cmr_pow_zeta (j + 1) (by omega) _
  rw [hrjval, tmz_find_pow (j + 1) (by omega)
        (ctmFind (j + n + 2) (by omega) ((y.val (j + n + 1)).val) / 3 ^ (n + 1))]
  show (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
        ((ctmFind (j + n + 2) (by omega) ((y.val (j + n + 1)).val) / 3 ^ (n + 1)) % 3 ^ (j + 1))
     = (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
        (ctmFind (i + n + 2) (by omega) ((y.val (i + n + 1)).val) / 3 ^ (n + 1))
  rw [cra_pow_reduce (i + 1) (by omega) (cmrZeta (i + 1) (by omega))
        ((ctmFind (j + n + 2) (by omega) ((y.val (j + n + 1)).val) / 3 ^ (n + 1)) % 3 ^ (j + 1)),
      Nat.mod_mod_of_dvd _ (zpu_pow_dvd (Nat.succ_le_succ hij)),
      cra_pow_reduce (i + 1) (by omega) (cmrZeta (i + 1) (by omega))
        (ctmFind (i + n + 2) (by omega) ((y.val (i + n + 1)).val) / 3 ^ (n + 1)),
      hexp]

/-- **TME-2c: ★核の可除性フィルトレーション** — `y` が level n で自明ならば
    `y` は T 内の 3^{n+1} 乗（witness は `tmeRootFam`・choice-free・∃ は Prop ゴール内）。 -/
theorem tme_ker_pow (n : Nat) (y : tmzLimit.carrier) (hy : y.val n = (tmzG n).one) :
    ∃ z : tmzLimit.carrier, tmzLimit.pow z (3 ^ (n + 1)) = y := by
  refine ⟨⟨tmeRootFam n y, tmeRootFam_compat n y hy⟩, ?_⟩
  apply Subtype.ext
  funext k
  rw [tme_pow_level ⟨tmeRootFam n y, tmeRootFam_compat n y hy⟩ (3 ^ (n + 1)) k]
  have hdvd : 3 ^ (n + 1) ∣ ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val) :=
    tme_find_dvd n k y hy
  have hcancel :
      ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val) / 3 ^ (n + 1) * 3 ^ (n + 1)
        = ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val) := Nat.div_mul_cancel hdvd
  have hle : k ≤ k + n + 1 := Nat.le_add_right k (n + 1)
  have hyk : (cmrGrp (k + 1) (by omega)).pow (cmrZeta (k + 1) (by omega))
        (ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val)) = y.val k := by
    have hp : (tmzT hle).map (y.val (k + n + 1)) = y.val k := y.property hle
    rw [tme_t_apply hle (y.val (k + n + 1))] at hp
    exact hp
  show (cmrGrp (k + 1) (by omega)).pow
        ((cmrGrp (k + 1) (by omega)).pow (cmrZeta (k + 1) (by omega))
          (ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val) / 3 ^ (n + 1)))
        (3 ^ (n + 1)) = y.val k
  rw [← cycRig_pow_mul (cmrGrp (k + 1) (by omega)) (cmr_comm (k + 1) (by omega))
        (cmrZeta (k + 1) (by omega))
        (ctmFind (k + n + 2) (by omega) ((y.val (k + n + 1)).val) / 3 ^ (n + 1)) (3 ^ (n + 1)),
      hcancel]
  exact hyk

/-! ## TME-3: ★核の保存（自動降下の鍵） -/

/-- **TME-3a: 核の保存** — 任意の抽象 Hom f: T→T は ker proj_n を保つ。
    `tme_ker_pow` で y = z^{3^{n+1}}、f y = (f z)^{3^{n+1}}（`Hom.map_pow`）、成分 n で
    ((f z).val n)^{3^{n+1}} = 1（`cra_pow_ord`）。 -/
theorem tme_ker_preserved (f : Hom tmzLimit tmzLimit) (n : Nat) (y : tmzLimit.carrier)
    (hy : y.val n = (tmzG n).one) : (f.map y).val n = (tmzG n).one := by
  obtain ⟨z, hz⟩ := tme_ker_pow n y hy
  have hfz : f.map y = tmzLimit.pow (f.map z) (3 ^ (n + 1)) := by
    rw [← hz]; exact f.map_pow z (3 ^ (n + 1))
  rw [hfz, tme_pow_level (f.map z) (3 ^ (n + 1)) n]
  exact cra_pow_ord (n + 1) (by omega) ((f.map z).val n)

/-- **TME-3b: 核合同 → f の level n 一致** — a.val n = b.val n なら (f a).val n = (f b).val n
    （差 a·b⁻¹ が ker proj_n・`tme_ker_preserved`）。降下の骨。 -/
theorem tme_ker_congr (f : Hom tmzLimit tmzLimit) (n : Nat) (a b : tmzLimit.carrier)
    (hab : a.val n = b.val n) : (f.map a).val n = (f.map b).val n := by
  have hd : (tmzLimit.mul a (tmzLimit.inv b)).val n = (tmzG n).one := by
    show (tmzG n).mul (a.val n) ((tmzG n).inv (b.val n)) = (tmzG n).one
    rw [hab]
    exact (tmzG n).mul_inv (b.val n)
  have hfd : (f.map (tmzLimit.mul a (tmzLimit.inv b))).val n = (tmzG n).one :=
    tme_ker_preserved f n _ hd
  have hAdB : a = tmzLimit.mul (tmzLimit.mul a (tmzLimit.inv b)) b := by
    rw [tmzLimit.mul_assoc, tmzLimit.inv_mul, tmzLimit.mul_one]
  have hfa : f.map a
      = tmzLimit.mul (f.map (tmzLimit.mul a (tmzLimit.inv b))) (f.map b) := by
    have hh := f.map_mul (tmzLimit.mul a (tmzLimit.inv b)) b
    rw [← hAdB] at hh
    exact hh
  have hval : (f.map a).val n
      = (tmzG n).mul ((f.map (tmzLimit.mul a (tmzLimit.inv b))).val n) ((f.map b).val n) := by
    rw [hfa]
    rfl
  rw [hval, hfd, (tmzG n).one_mul]

/-! ## TME-4: 降下（標準 witness リフトとレベル写像） -/

/-- **TME-4a: 標準リフト** — level n の元 u を定数指数族 `tmzWitnessFam`（既存・閉じた式）で
    T へ持ち上げる。 -/
def tmeLift (n : Nat) (u : (tmzG n).carrier) : tmzLimit.carrier :=
  ⟨tmzWitnessFam n u, tmzWitnessFam_compat n u⟩

/-- **TME-4b: リフトの n 成分は元に戻る** — `(tmeLift n u).val n = u`（射影＝離散対数の逆）。 -/
theorem tme_lift_proj (n : Nat) (u : (tmzG n).carrier) : (tmeLift n u).val n = u := by
  show tmzWitnessFam n u n = u
  apply Subtype.ext
  show ((cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
        (ctmFind (n + 1) (by omega) u.val)).val = u.val
  rw [cmr_pow_zeta (n + 1) (by omega) (ctmFind (n + 1) (by omega) u.val)]
  exact (tmz_val_find (n + 1) (by omega) u).symm

/-- **TME-4c: リフトとの差は核** — y と「y_n を通る標準 witness」の差は ker proj_n。 -/
theorem tme_lift_diff_ker (n : Nat) (y : tmzLimit.carrier) :
    (tmzLimit.mul y (tmzLimit.inv (tmeLift n (y.val n)))).val n = (tmzG n).one := by
  show (tmzG n).mul (y.val n) ((tmzG n).inv ((tmeLift n (y.val n)).val n)) = (tmzG n).one
  rw [tme_lift_proj n (y.val n)]
  exact (tmzG n).mul_inv (y.val n)

/-- **TME-4d: 降下したレベル写像** — 抽象 Hom f を level n の群自己準同型へ降ろす。
    map_mul は `tme_ker_congr`（リフトの積差が ker proj_n）＋`tme_lift_proj`。 -/
def tmeLevel (f : Hom tmzLimit tmzLimit) (n : Nat) : Hom (tmzG n) (tmzG n) where
  map := fun u => (f.map (tmeLift n u)).val n
  map_mul := fun u v => by
    have hab : (tmeLift n ((tmzG n).mul u v)).val n
        = (tmzLimit.mul (tmeLift n u) (tmeLift n v)).val n := by
      rw [tme_lift_proj n ((tmzG n).mul u v)]
      show (tmzG n).mul u v
         = (tmzG n).mul ((tmeLift n u).val n) ((tmeLift n v).val n)
      rw [tme_lift_proj n u, tme_lift_proj n v]
    have hcong := tme_ker_congr f n (tmeLift n ((tmzG n).mul u v))
        (tmzLimit.mul (tmeLift n u) (tmeLift n v)) hab
    show (f.map (tmeLift n ((tmzG n).mul u v))).val n
       = (tmzG n).mul ((f.map (tmeLift n u)).val n) ((f.map (tmeLift n v)).val n)
    rw [hcong]
    show (f.map (tmzLimit.mul (tmeLift n u) (tmeLift n v))).val n
       = (tmzG n).mul ((f.map (tmeLift n u)).val n) ((f.map (tmeLift n v)).val n)
    rw [f.map_mul]
    rfl

/-- **TME-4e: 降下の整合** — f の level n 成分は `tmeLevel f n` で読める。 -/
theorem tme_level_map (f : Hom tmzLimit tmzLimit) (n : Nat) (y : tmzLimit.carrier) :
    (f.map y).val n = (tmeLevel f n).map (y.val n) := by
  show (f.map y).val n = (f.map (tmeLift n (y.val n))).val n
  apply tme_ker_congr f n y (tmeLift n (y.val n))
  exact (tme_lift_proj n (y.val n)).symm

/-! ## TME-5: ★End(ℤ₃(1)) の完全分類 -/

/-- **TME-5a: End の指数**（choice-free・`craEndoChar` の fuel 走査を降下写像に適用）。 -/
def tmeChar (f : Hom tmzLimit tmzLimit) (n : Nat) : Nat :=
  craEndoChar (n + 1) (by omega) (tmeLevel f n)

/-- **TME-5b（★分類）: 自己準同型は成分冪** — (f y)_n = (y_n)^{tmeChar f n}。
    `tme_level_map`＋`cra_endo_pow`（レベル分類の消費）で ζ 冪を経由し成分冪へ。 -/
theorem tme_endo_pow (f : Hom tmzLimit tmzLimit) (y : tmzLimit.carrier) (n : Nat) :
    (f.map y).val n
      = (cmrGrp (n + 1) (by omega)).pow (y.val n) (tmeChar f n) := by
  rw [tme_level_map f n y]
  show (tmeLevel f n).map (y.val n)
     = (cmrGrp (n + 1) (by omega)).pow (y.val n) (tmeChar f n)
  rw [cra_endo_pow (n + 1) (by omega) (tmeLevel f n) (y.val n)]
  have hy : (cmrGrp (n + 1) (by omega)).pow (y.val n) (tmeChar f n)
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
          (ctmFind (n + 1) (by omega) (y.val n).val * tmeChar f n) := by
    have e1 : (cmrGrp (n + 1) (by omega)).pow (y.val n) (tmeChar f n)
        = (cmrGrp (n + 1) (by omega)).pow
            ((cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
              (ctmFind (n + 1) (by omega) (y.val n).val)) (tmeChar f n) := by
      rw [cra_pow_log (n + 1) (by omega) (y.val n)]
    rw [e1, ← cycRig_pow_mul (cmrGrp (n + 1) (by omega)) (cmr_comm (n + 1) (by omega))
          (cmrZeta (n + 1) (by omega)) (ctmFind (n + 1) (by omega) (y.val n).val) (tmeChar f n)]
  rw [hy]
  show (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
        (tmeChar f n * ctmFind (n + 1) (by omega) (y.val n).val)
     = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
        (ctmFind (n + 1) (by omega) (y.val n).val * tmeChar f n)
  rw [Nat.mul_comm (tmeChar f n) (ctmFind (n + 1) (by omega) (y.val n).val)]

/-! ### TME-5 補: 整合 ζ 族（tme_char_compat の witness） -/

/-- **TME-5 補a: 整合 ζ 族** — 各段 ζ_{m+1}。 -/
def tmeZeta : (m : Nat) → (tmzG m).carrier := fun m => cmrZeta (m + 1) (by omega)

/-- **TME-5 補b: ζ 族の整合性**（遷移で ζ_{j+1} ↦ ζ_{i+1}・find ζ = 1）。 -/
theorem tmeZeta_compat : Compatible tmzSystem tmeZeta := by
  intro i j h
  show (tmzT h).map (cmrZeta (j + 1) (by omega)) = cmrZeta (i + 1) (by omega)
  rw [tme_t_apply h (cmrZeta (j + 1) (by omega)), cra_find_zeta (j + 1) (by omega)]
  exact (cmrGrp (i + 1) (by omega)).mul_one (cmrZeta (i + 1) (by omega))

/-- **TME-5 補c: 整合 ζ 極限元**。 -/
def tmeZetaLim : tmzLimit.carrier := ⟨tmeZeta, tmeZeta_compat⟩

/-- **TME-5c: 指数族の mod 整合**（＝ℤ₃ 元の指数表示） — tmeChar f j ≡ tmeChar f i mod 3^{i+1}。
    整合 ζ 極限元 `tmeZetaLim` に `tme_endo_pow` を level j・i で適用し、(f tmeZetaLim) の
    整合族性＋`tmz_find_pow`＋`cci_indexG` で合流。 -/
theorem tme_char_compat {i j : Nat} (h : i ≤ j) (f : Hom tmzLimit tmzLimit) :
    tmeChar f j % 3 ^ (i + 1) = tmeChar f i % 3 ^ (i + 1) := by
  have hj : (f.map tmeZetaLim).val j
      = (cmrGrp (j + 1) (by omega)).pow (cmrZeta (j + 1) (by omega)) (tmeChar f j) :=
    tme_endo_pow f tmeZetaLim j
  have hi : (f.map tmeZetaLim).val i
      = (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega)) (tmeChar f i) :=
    tme_endo_pow f tmeZetaLim i
  have hcompat : (tmzT h).map ((f.map tmeZetaLim).val j) = (f.map tmeZetaLim).val i :=
    (f.map tmeZetaLim).property h
  rw [hj, hi, tme_t_apply h
        ((cmrGrp (j + 1) (by omega)).pow (cmrZeta (j + 1) (by omega)) (tmeChar f j)),
      cmr_pow_zeta (j + 1) (by omega) (tmeChar f j),
      tmz_find_pow (j + 1) (by omega) (tmeChar f j)] at hcompat
  -- hcompat : pow ζ_{i+1} (χj % 3^{j+1}) = pow ζ_{i+1} χi
  have hval : ctmPow (i + 1) (by omega) (tmeChar f j % 3 ^ (j + 1))
      = ctmPow (i + 1) (by omega) (tmeChar f i) := by
    have h1 := congrArg Subtype.val hcompat
    rw [cmr_pow_zeta (i + 1) (by omega) (tmeChar f j % 3 ^ (j + 1)),
        cmr_pow_zeta (i + 1) (by omega) (tmeChar f i)] at h1
    exact h1
  rw [ctm_pow_mod (i + 1) (by omega) (tmeChar f i)] at hval
  have hidx := cci_indexG (i + 1) (by omega) (tmeChar f j % 3 ^ (j + 1))
      (tmeChar f i % 3 ^ (i + 1))
      (Nat.mod_lt _ (by have := zpu_pow_pos (i + 1); omega)) hval
  rw [Nat.mod_mod_of_dvd (tmeChar f j) (zpu_pow_dvd (show i + 1 ≤ j + 1 by omega))] at hidx
  exact hidx

/-- **TME-5d: 指数族が自己準同型を決める（外延性）** — 全 level で mod 一致なら f = g。
    `cra_hom_ext`（極限レベル）＋成分ごと `tme_endo_pow`＋`cra_pow_reduce`。 -/
theorem tme_endo_ext (f g : Hom tmzLimit tmzLimit)
    (h : ∀ n, tmeChar f n % 3 ^ (n + 1) = tmeChar g n % 3 ^ (n + 1)) : f = g := by
  refine cra_hom_ext f g ?_
  intro y
  apply Subtype.ext
  funext n
  rw [tme_endo_pow f y n, tme_endo_pow g y n,
      cra_pow_reduce (n + 1) (by omega) (y.val n) (tmeChar f n),
      cra_pow_reduce (n + 1) (by omega) (y.val n) (tmeChar g n), h n]

/-! ## TME-6: capstone -/

/-- **TME-6a: End 分類データ** — 可除性フィルトレーション・核保存・成分冪分類・指数族の
    mod 整合を束ねる（実 ℤ₃(1) の自己準同型の完全分類の証明書）。 -/
structure TmeEndoData where
  /-- 核の可除性フィルトレーション。 -/
  ker_pow : ∀ (n : Nat) (y : tmzLimit.carrier), y.val n = (tmzG n).one →
    ∃ z : tmzLimit.carrier, tmzLimit.pow z (3 ^ (n + 1)) = y
  /-- 任意の抽象 Hom は ker proj_n を保つ。 -/
  ker_preserved : ∀ (f : Hom tmzLimit tmzLimit) (n : Nat) (y : tmzLimit.carrier),
    y.val n = (tmzG n).one → (f.map y).val n = (tmzG n).one
  /-- 自己準同型は成分冪（自動降下・自動線型性）。 -/
  endo_pow : ∀ (f : Hom tmzLimit tmzLimit) (y : tmzLimit.carrier) (n : Nat),
    (f.map y).val n = (cmrGrp (n + 1) (by omega)).pow (y.val n) (tmeChar f n)
  /-- 指数族は mod 整合（=ℤ₃ 元）。 -/
  char_compat : ∀ {i j : Nat}, i ≤ j → ∀ (f : Hom tmzLimit tmzLimit),
    tmeChar f j % 3 ^ (i + 1) = tmeChar f i % 3 ^ (i + 1)
  /-- 指数族が自己準同型を決める。 -/
  endo_ext : ∀ (f g : Hom tmzLimit tmzLimit),
    (∀ n, tmeChar f n % 3 ^ (n + 1) = tmeChar g n % 3 ^ (n + 1)) → f = g

/-- **TME-6b: witness** — 全フィールド既証明の純レコード（実 ℤ₃(1) の End 完全分類）。 -/
def tmeEndoData : TmeEndoData where
  ker_pow := tme_ker_pow
  ker_preserved := tme_ker_preserved
  endo_pow := tme_endo_pow
  char_compat := fun {i j} hij f => tme_char_compat hij f
  endo_ext := tme_endo_ext

end IUT
