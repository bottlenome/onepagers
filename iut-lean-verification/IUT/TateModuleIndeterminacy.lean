/-
  IUT/TateModuleIndeterminacy.lean — TMI（柱A7 A7e: 実 Tate 加群 T = ℤ₃(1) = `tmzLimit`
  の自己準同型不定性の「正確な特徴付け」——Aut(ℤ₃(1)) ≅ 実 ℤ₃^× = `zpsLimit`・
  Galois 同変性条件が End(T) 上で空——を本物に建設し、`cra_indeterminacy` の
  「残存宣言」を極限実対象上の正確な特徴付けへ昇格する）

  ── 主要成果の分類: **[実／本物建設(b)＋昇格(a)]**（骨格・模型・代理でなく、既存の
     実 Tate 加群 T = ℤ₃(1) = `tmzLimit`（tmz で本物に構成）と、その自己準同型の完全
     分類 `tmeEndoData`（tme で本物に建設）の上で、(a) 整合冪族 `TmiExpFam` から自己
     準同型 `tmiPowHom` を作る A7d 分類の逆写像、(b) **任意の抽象自己準同型 f が実 Galois
     作用 `tmzActHom` と可換**（同変性条件が空・`tmi_endo_gal_commute`）という不定性の
     正確な意味、(c) **実 ℤ₃^× = `zpsLimit` を自己同型として実現**（`tmiFromUnits`・
     両側逆 `tmi_from_units_iso`）し、**任意の同型がちょうど 1 つの実単元から来る**
     （`tmi_aut_classify`＋`tmi_units_inj`）ことを証明する。これは
     Aut(ℤ₃(1)) ≅ `zpsLimit`（実 ℤ₃^×）を消去形で確立し、レベル ℓ 単位の残存宣言
     `cra_indeterminacy`（IUTchII の ẑ^× 不定性の p=3 切片の *残存* を可換 1 本で言う
     のみ）を、極限実対象上の *正確な特徴付け* へ昇格する。**旧定理 `cra_indeterminacy`
     は消さない・弱めない**（§4 規約）——本ファイルはその上に並置＋昇格するのみ。

  **complete_pct 影響**: A7（実円分剛性）A7e——**実 ℤ₃(1) の自己同型群がちょうど実
  ℤ₃^× = `zpsLimit`（A3 cli/zps で本物に構成した実対象）に同定され、Galois 同変性が
  End(T) を一切絞らない（＝不定性は正確に ℤ₃^× である）**ことを極限レベルで確立する。
  A7d（`TateModuleEndo`・End 分類）と合わせ、監査ディスカウント理由「剛性内容が
  レベル単位・初等」「不定性が残存宣言止まり」の両方を正面から解消する。数値は独立監査が
  確定（設計 audit/A7-real-cyclotomic-rigidity-deepen-2026-07-10.md §5: 保守見込み
  0.42–0.45・下振れ 0.40 も想定内）。

  内容（設計 §3.2・TMI-1〜6）:
   * `TmiExpFam`/`tmiPowHom`/`tmi_pow_char` — 整合冪族 → 自己準同型（A7d 分類の逆）。TMI-1。
   * `tmi_endo_gal_commute` — ★任意の自己準同型が Galois 作用と可換（同変性は空）。TMI-2。
   * `tmi_act_char`         — Galois 作用の指数族は χ（作用は End 中で χ の像）。TMI-3。
   * `tmi_inv_congr`/`tmi_unit_of_iso` — 単元逆の mod 整合・可逆⟹単元指標。TMI-4。
   * `tmiFromUnits`/`tmi_from_units_iso` — ★実 ℤ₃^× を自己同型として実現・両側逆。TMI-5。
   * `tmi_aut_classify`/`tmi_units_inj` — ★任意の同型は一意の実単元から来る。TMI-5。
   * `TmiIndeterminacyData`/`tmiIndeterminacyData` — capstone（正確な特徴付け）。TMI-6。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (1) **mono-theta 円分剛性（[EtTh]）は依然 0**: 本ステップは ẑ^×（p=3: ℤ₃^×）不定性を
       **殺さない**。「不定性は正確に実 ℤ₃^× である」と *特徴付ける* だけであり、テータ
       環境がこの不定性を消す仕組み（IUT 本丸・柱 E/D 後続）は範囲外。A7=1 には依然遠い。
       本定理群は不定性を CHARACTERIZE するのであって KILL しない。
   (2) **p = 3 固定・円分切片限定**: T = ℤ₃(1)、G = Gal(ℚ(ζ_{3^∞})/ℚ)。実 G_{ℚ₃}・
       実 G_ℚ・一般素数 p は含めない（tmz/cra/cli/tme の正直申告を継承）。
   (3) **位相は形式化しない**: 「自動連続性」は可除性フィルトレーション（tme の
       ker proj_n 保存）経由の代数版であり、`limitTopology` に対する連続写像の定理としては
       述べない（`tmiFromUnits` の連続性は後続・範囲外）。
   (4) **End(ℤ₃(1)) ≅ ℤ₃ は指数族表示**: 分類先は整合 Nat 族 `TmiExpFam`（＋単元部分の
       実 `zpsLimit`）であり、A2 の実 ℤ₃ 環オブジェクト（z3）との**環同型接続は未形式化**
       （End の環構造・合成=積も未・後続の昇格ターゲットとして名指し）。`tmi_endo_gal_commute`
       は加法圏的な意味での「同変」を言うが、環同型は述べない。
   (5) **幾何側は不在のまま**: μ 塔は各段別々の実円分体に住む（K̄ なし）。楕円曲線の
       幾何的 Tate 加群・π₁ の幾何的 cyclotome ではない（tmz の限定を継承）。
   (6) 既存の正直な限定（M322F・cra (i)-(iv)〔特に `cra_indeterminacy` の残存宣言〕・
       tmz (i)-(iv)・crr (i)-(iii)・tme (1)-(6)）は**一切消さない・弱めない**。本ステップは
       並置＋昇格のみ——`cra_indeterminacy` はレベル残存宣言のまま残り、本ファイルは
       極限の正確な特徴付けをその *隣に* 積む。

  全て選択公理不使用（新規 `Classical.choice` を証明本体に導入しない・propext/Quot.sound
  のみ）。witness は全て閉じた式（`tmeChar`・`zpuInvL`・成分 mod）で、∃ は Prop ゴール内
  （`tmi_aut_classify`）のみ。End(T)≅指数族の全単射を choice で総体化せず、
  「∀f ∃(明示 witness)＋一意性」の消去形で述べる。禁止タクティク（simp/decide/by_cases/
  rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。3^ℓ は omega に生で
  渡さない（`zpu_pow_pos`/`zpu_pow_dvd`/`Nat.mul_mod`/`Nat.mod_mod_of_dvd` 経由）。
  新規ファイル 1 個のみ（共有ファイルは親が統合）。prefix `tmi`。
-/
import IUT.TateModuleEndo
import IUT.TateModuleZ3
import IUT.Zmod3PowUnitsSystem
import IUT.CyclotomicLimitIso

namespace IUT

/-! ## TMI-1: 整合冪族 → T の自己準同型（A7d 分類の逆） -/

/-- **TMI-1a: 整合冪族** — mod-整合な指数族 `a : Nat → Nat`（＝ℤ₃ 元の指数表示）。
    `compat` は各段が下段と mod 3^{i+1} で合流すること（`tme_char_compat` と同型）。 -/
structure TmiExpFam where
  /-- 各レベル n の指数。 -/
  a : Nat → Nat
  /-- 指数族の mod 整合（i ≤ j で a j ≡ a i mod 3^{i+1}）。 -/
  compat : ∀ {i j : Nat}, i ≤ j → a j % 3 ^ (i + 1) = a i % 3 ^ (i + 1)

/-- **TMI-1b: 整合冪族から自己準同型** `tmiPowHom F` — 成分ごと y_n ↦ y_n^{F.a n}。
    整合は `Hom.map_pow`（遷移 `tmzT` が Hom）＋ y の整合族性 ＋ `cra_pow_reduce`
    ＋ `F.compat`。map_mul は成分ごと `cra_pow_mul_dist`（可換群の冪分配）。 -/
def tmiPowHom (F : TmiExpFam) : Hom tmzLimit tmzLimit where
  map := fun y => ⟨fun n => (tmzG n).pow (y.val n) (F.a n), by
    intro i j h
    show (tmzT h).map ((tmzG j).pow (y.val j) (F.a j)) = (tmzG i).pow (y.val i) (F.a i)
    rw [(tmzT h).map_pow (y.val j) (F.a j), y.property h]
    show (cmrGrp (i + 1) (by omega)).pow (y.val i) (F.a j)
       = (cmrGrp (i + 1) (by omega)).pow (y.val i) (F.a i)
    rw [cra_pow_reduce (i + 1) (by omega) (y.val i) (F.a j),
        cra_pow_reduce (i + 1) (by omega) (y.val i) (F.a i), F.compat h]⟩
  map_mul := fun y z => by
    apply Subtype.ext
    funext n
    show (tmzG n).pow ((tmzG n).mul (y.val n) (z.val n)) (F.a n)
       = (tmzG n).mul ((tmzG n).pow (y.val n) (F.a n)) ((tmzG n).pow (z.val n) (F.a n))
    exact cra_pow_mul_dist (tmzG n) (cmr_comm (n + 1) (by omega)) (y.val n) (z.val n) (F.a n)

/-- **TMI-1c: 構成と分類の往復** — `tmiPowHom F` を tme で分類し直すと指数は F.a に戻る
    （mod 3^{n+1}）。整合 ζ 極限元 `tmeZetaLim` に `tme_endo_pow` を適用し `cci_indexG`。 -/
theorem tmi_pow_char (F : TmiExpFam) (n : Nat) :
    tmeChar (tmiPowHom F) n % 3 ^ (n + 1) = F.a n % 3 ^ (n + 1) := by
  have hbase : (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (F.a n)
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar (tmiPowHom F) n) :=
    tme_endo_pow (tmiPowHom F) tmeZetaLim n
  have hval : ctmPow (n + 1) (by omega) (F.a n)
      = ctmPow (n + 1) (by omega) (tmeChar (tmiPowHom F) n) := by
    have h1 := congrArg Subtype.val hbase
    rw [cmr_pow_zeta (n + 1) (by omega) (F.a n),
        cmr_pow_zeta (n + 1) (by omega) (tmeChar (tmiPowHom F) n)] at h1
    exact h1
  have hval2 : ctmPow (n + 1) (by omega) (tmeChar (tmiPowHom F) n)
      = ctmPow (n + 1) (by omega) (F.a n % 3 ^ (n + 1)) := by
    rw [← ctm_pow_mod (n + 1) (by omega) (F.a n)]
    exact hval.symm
  exact cci_indexG (n + 1) (by omega) (tmeChar (tmiPowHom F) n) (F.a n % 3 ^ (n + 1))
    (Nat.mod_lt _ (by have := zpu_pow_pos (n + 1); omega)) hval2

/-! ## TMI-2: ★同変性条件は End(T) 上で空（不定性の総和・cra_indeterminacy の極限昇格） -/

/-- **TMI-2（★不定性の正確な意味）: 任意の自己準同型が Galois 作用と可換** —
    f ∈ End(T) と実 Galois 作用 `tmzActHom s` は必ず可換: f(σ·y) = σ·(f·y)。
    両 f・tmzActHom s とも Hom ゆえ tme で成分冪に分類され（`tme_endo_pow`）、
    指数は Nat の積で、`Nat.mul_comm` で合流する。**同変性は End(T) を一切絞らない**
    ——これが「純 Galois 加群としての cyclotome の不定性はちょうど End(T) の可逆部分
    ＝ℤ₃^× である」の正確な内容。`cra_indeterminacy`（レベル残存宣言）の極限昇格。 -/
theorem tmi_endo_gal_commute (f : Hom tmzLimit tmzLimit) (s : ctlProfinite.carrier)
    (y : tmzLimit.carrier) :
    f.map ((tmzActHom s).map y) = (tmzActHom s).map (f.map y) := by
  apply Subtype.ext
  funext n
  rw [tme_endo_pow f ((tmzActHom s).map y) n, tme_endo_pow (tmzActHom s) y n,
      tme_endo_pow (tmzActHom s) (f.map y) n, tme_endo_pow f y n,
      ← cycRig_pow_mul (cmrGrp (n + 1) (by omega)) (cmr_comm (n + 1) (by omega)) (y.val n)
        (tmeChar (tmzActHom s) n) (tmeChar f n),
      ← cycRig_pow_mul (cmrGrp (n + 1) (by omega)) (cmr_comm (n + 1) (by omega)) (y.val n)
        (tmeChar f n) (tmeChar (tmzActHom s) n),
      Nat.mul_comm (tmeChar (tmzActHom s) n) (tmeChar f n)]

/-! ## TMI-3: Galois 作用の指数族は χ（作用は End の中で χ の像として座る） -/

/-- **TMI-3: 作用の指数族 = χ** — `tmzActHom s` を tme で分類した指数 `tmeChar (tmzActHom s) n`
    は円分指標 χ_n(s_n)=`((cliChar n).map (s.val n)).val`（mod 3^{n+1}）に一致する。
    `tme_endo_pow` と `tmz_act_char` を整合 ζ 極限元 `tmeZetaLim` で突き合わせ `cci_indexG`。
    Galois 作用が Aut(T)=ℤ₃^× の中で χ の像として座ることの実内容。 -/
theorem tmi_act_char (s : ctlProfinite.carrier) (n : Nat) :
    tmeChar (tmzActHom s) n % 3 ^ (n + 1)
      = ((cliChar n).map (s.val n)).val % 3 ^ (n + 1) := by
  have hlt : ((cliChar n).map (s.val n)).val < 3 ^ (n + 1) :=
    ((cliChar n).map (s.val n)).property.1
  have hzz : tmeZetaLim.val n = cmrZeta (n + 1) (by omega) := rfl
  have h1 := tme_endo_pow (tmzActHom s) tmeZetaLim n
  have h2 := tmz_act_char s tmeZetaLim n
  rw [hzz] at h1 h2
  rw [cra_find_zeta (n + 1) (by omega), Nat.mul_one] at h2
  have hkey : (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
        (tmeChar (tmzActHom s) n)
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
        (((cliChar n).map (s.val n)).val) := h1.symm.trans h2
  have hval : ctmPow (n + 1) (by omega) (tmeChar (tmzActHom s) n)
      = ctmPow (n + 1) (by omega) (((cliChar n).map (s.val n)).val) := by
    have hv := congrArg Subtype.val hkey
    rw [cmr_pow_zeta (n + 1) (by omega) (tmeChar (tmzActHom s) n),
        cmr_pow_zeta (n + 1) (by omega) (((cliChar n).map (s.val n)).val)] at hv
    exact hv
  rw [Nat.mod_eq_of_lt hlt]
  exact cci_indexG (n + 1) (by omega) (tmeChar (tmzActHom s) n)
    (((cliChar n).map (s.val n)).val) hlt hval

/-! ## TMI-4: 可逆 ⟺ 単元指数族（単元逆の mod 一意性・可逆⟹単元指標） -/

/-- **TMI-4a: 単元逆の mod 整合** — 3∤a なら各段の Hensel 逆 `zpuInvL (·+1) a` は
    下段へ mod 整合する（zpuInvL (j+1) a ≡ zpuInvL (i+1) a mod 3^{i+1}）。
    逆元の一意性（b_j ≡ b_j·(a·b_i) = b_i·(a·b_j) ≡ b_i）の mod 簿記。 -/
theorem tmi_inv_congr {i j : Nat} (h : i ≤ j) (a : Nat) (ha : ¬ 3 ∣ a) :
    zpuInvL (j + 1) a % 3 ^ (i + 1) = zpuInvL (i + 1) a % 3 ^ (i + 1) := by
  have hi : a * zpuInvL (i + 1) a % 3 ^ (i + 1) = 1 :=
    zpuInvL_one (i + 1) (by omega) a ha
  have hj0 : a * zpuInvL (j + 1) a % 3 ^ (j + 1) = 1 :=
    zpuInvL_one (j + 1) (by omega) a ha
  have hj : a * zpuInvL (j + 1) a % 3 ^ (i + 1) = 1 := by
    rw [← Nat.mod_mod_of_dvd (a * zpuInvL (j + 1) a)
          (zpu_pow_dvd (show i + 1 ≤ j + 1 by omega)),
        hj0, Nat.mod_eq_of_lt (zpu_one_lt (i + 1) (by omega))]
  have hrearr : zpuInvL (j + 1) a * (a * zpuInvL (i + 1) a)
      = zpuInvL (i + 1) a * (a * zpuInvL (j + 1) a) := by
    rw [Nat.mul_comm a (zpuInvL (i + 1) a),
        ← Nat.mul_assoc (zpuInvL (j + 1) a) (zpuInvL (i + 1) a) a,
        Nat.mul_comm (zpuInvL (j + 1) a) (zpuInvL (i + 1) a),
        Nat.mul_comm a (zpuInvL (j + 1) a),
        ← Nat.mul_assoc (zpuInvL (i + 1) a) (zpuInvL (j + 1) a) a]
  calc zpuInvL (j + 1) a % 3 ^ (i + 1)
      = zpuInvL (j + 1) a * (a * zpuInvL (i + 1) a % 3 ^ (i + 1)) % 3 ^ (i + 1) := by
        rw [hi, Nat.mul_one]
    _ = zpuInvL (j + 1) a * (a * zpuInvL (i + 1) a) % 3 ^ (i + 1) :=
        zpu_mul_mod (zpuInvL (j + 1) a) (a * zpuInvL (i + 1) a) (3 ^ (i + 1))
    _ = zpuInvL (i + 1) a * (a * zpuInvL (j + 1) a) % 3 ^ (i + 1) := by rw [hrearr]
    _ = zpuInvL (i + 1) a * (a * zpuInvL (j + 1) a % 3 ^ (i + 1)) % 3 ^ (i + 1) :=
        (zpu_mul_mod (zpuInvL (i + 1) a) (a * zpuInvL (j + 1) a) (3 ^ (i + 1))).symm
    _ = zpuInvL (i + 1) a % 3 ^ (i + 1) := by rw [hj, Nat.mul_one]

/-- **TMI-4b: 可逆 ⟹ 単元指標** — f が両側逆 g を持つなら 3∤`tmeChar f n`。
    `tme_level_map` で左右逆を level n へ降ろし、レベル分類の `cra_unit_of_iso` を適用。 -/
theorem tmi_unit_of_iso (f g : Hom tmzLimit tmzLimit)
    (hl : ∀ y, g.map (f.map y) = y) (hr : ∀ y, f.map (g.map y) = y) (n : Nat) :
    ¬ 3 ∣ tmeChar f n := by
  have hlL : ∀ u, (tmeLevel g n).map ((tmeLevel f n).map u) = u := by
    intro u
    have e1 : (tmeLevel f n).map u = (f.map (tmeLift n u)).val n := by
      rw [tme_level_map f n (tmeLift n u), tme_lift_proj n u]
    rw [e1, ← tme_level_map g n (f.map (tmeLift n u)), hl (tmeLift n u), tme_lift_proj n u]
  have hrL : ∀ u, (tmeLevel f n).map ((tmeLevel g n).map u) = u := by
    intro u
    have e1 : (tmeLevel g n).map u = (g.map (tmeLift n u)).val n := by
      rw [tme_level_map g n (tmeLift n u), tme_lift_proj n u]
    rw [e1, ← tme_level_map f n (g.map (tmeLift n u)), hr (tmeLift n u), tme_lift_proj n u]
  exact cra_unit_of_iso (n + 1) (by omega) (tmeLevel f n) (tmeLevel g n) hlL hrL

/-! ## TMI-5: ★Aut(ℤ₃(1)) ≅ 実 ℤ₃^×（zpsLimit・A7e ヘッドライン） -/

/-- **TMI-5a: 実単元から自己同型** `tmiFromUnits u` — 実 ℤ₃^×=`zpsLimit` の元 u の
    各成分 (u.val n).val（∈(ℤ/3^{n+1})^×）を指数族とする `tmiPowHom`。整合は u の
    整合族性（`zpsT` の単発 mod）から。 -/
def tmiFromUnits (u : zpsLimit.carrier) : Hom tmzLimit tmzLimit :=
  tmiPowHom
    { a := fun n => (u.val n).val
      compat := fun {i j} h => by
        have hv : (u.val j).val % 3 ^ (i + 1) = (u.val i).val :=
          congrArg Subtype.val (u.property h)
        rw [hv, Nat.mod_eq_of_lt (u.val i).property.1] }

/-- **TMI-5b（★実現）: 実 ℤ₃^× は Aut(T) をなす** — u と実逆元 `zpsLimit.inv u` から
    作った `tmiFromUnits` は両側逆。成分の Hensel 逆則（`zpuInvL_one`）＋`cra_pow_reduce`
    ＋`cycRig_pow_mul`。可換群 μ ゆえ左右対称。 -/
theorem tmi_from_units_iso (u : zpsLimit.carrier) :
    (∀ y, (tmiFromUnits (zpsLimit.inv u)).map ((tmiFromUnits u).map y) = y) ∧
    (∀ y, (tmiFromUnits u).map ((tmiFromUnits (zpsLimit.inv u)).map y) = y) := by
  refine ⟨?_, ?_⟩
  · intro y
    apply Subtype.ext
    funext n
    show (cmrGrp (n + 1) (by omega)).pow
          ((cmrGrp (n + 1) (by omega)).pow (y.val n) ((u.val n).val))
          (zpuInvL (n + 1) (u.val n).val % 3 ^ (n + 1)) = y.val n
    rw [← cycRig_pow_mul (cmrGrp (n + 1) (by omega)) (cmr_comm (n + 1) (by omega)) (y.val n)
          ((u.val n).val) (zpuInvL (n + 1) (u.val n).val % 3 ^ (n + 1)),
        cra_pow_reduce (n + 1) (by omega) (y.val n)
          ((u.val n).val * (zpuInvL (n + 1) (u.val n).val % 3 ^ (n + 1))),
        zpu_mul_mod ((u.val n).val) (zpuInvL (n + 1) (u.val n).val) (3 ^ (n + 1)),
        zpuInvL_one (n + 1) (by omega) ((u.val n).val) (u.val n).property.2]
    show (cmrGrp (n + 1) (by omega)).mul (y.val n) ((cmrGrp (n + 1) (by omega)).one) = y.val n
    exact (cmrGrp (n + 1) (by omega)).mul_one (y.val n)
  · intro y
    apply Subtype.ext
    funext n
    show (cmrGrp (n + 1) (by omega)).pow
          ((cmrGrp (n + 1) (by omega)).pow (y.val n) (zpuInvL (n + 1) (u.val n).val % 3 ^ (n + 1)))
          ((u.val n).val) = y.val n
    rw [← cycRig_pow_mul (cmrGrp (n + 1) (by omega)) (cmr_comm (n + 1) (by omega)) (y.val n)
          (zpuInvL (n + 1) (u.val n).val % 3 ^ (n + 1)) ((u.val n).val),
        cra_pow_reduce (n + 1) (by omega) (y.val n)
          ((zpuInvL (n + 1) (u.val n).val % 3 ^ (n + 1)) * (u.val n).val),
        zpu_mod_mul (zpuInvL (n + 1) (u.val n).val) ((u.val n).val) (3 ^ (n + 1)),
        Nat.mul_comm (zpuInvL (n + 1) (u.val n).val) ((u.val n).val),
        zpuInvL_one (n + 1) (by omega) ((u.val n).val) (u.val n).property.2]
    show (cmrGrp (n + 1) (by omega)).mul (y.val n) ((cmrGrp (n + 1) (by omega)).one) = y.val n
    exact (cmrGrp (n + 1) (by omega)).mul_one (y.val n)

/-- **TMI-5c（★分類）: 任意の同型は実単元から来る** — f が両側逆 g を持つなら、実
    ℤ₃^×=`zpsLimit` の元 u で f が `tmiFromUnits u` に一致するものが（一意に）存在する。
    witness u は各段 `tmeChar f n % 3^{n+1}`（閉じた式・¬3∣は `tmi_unit_of_iso`、整合は
    `tme_char_compat` から）で明示。∃ は Prop ゴール内のみ・choice 不使用。 -/
theorem tmi_aut_classify (f g : Hom tmzLimit tmzLimit)
    (hl : ∀ y, g.map (f.map y) = y) (hr : ∀ y, f.map (g.map y) = y) :
    ∃ u : zpsLimit.carrier, ∀ y, f.map y = (tmiFromUnits u).map y := by
  have hcompat : Compatible zpsSystem (fun n =>
      (⟨tmeChar f n % 3 ^ (n + 1),
        Nat.mod_lt _ (zpu_pow_pos (n + 1)),
        zpu_mod_nd3 (n + 1) (by omega) (tmeChar f n)
          (tmi_unit_of_iso f g hl hr n)⟩ : (zpsG n).carrier)) := by
    intro i j h
    apply Subtype.ext
    show (tmeChar f j % 3 ^ (j + 1)) % 3 ^ (i + 1) = tmeChar f i % 3 ^ (i + 1)
    rw [Nat.mod_mod_of_dvd (tmeChar f j) (zpu_pow_dvd (Nat.succ_le_succ h)),
        tme_char_compat h f]
  refine ⟨⟨fun n =>
      ⟨tmeChar f n % 3 ^ (n + 1),
        Nat.mod_lt _ (zpu_pow_pos (n + 1)),
        zpu_mod_nd3 (n + 1) (by omega) (tmeChar f n)
          (tmi_unit_of_iso f g hl hr n)⟩, hcompat⟩, ?_⟩
  intro y
  apply Subtype.ext
  funext n
  rw [tme_endo_pow f y n]
  show (cmrGrp (n + 1) (by omega)).pow (y.val n) (tmeChar f n)
     = (cmrGrp (n + 1) (by omega)).pow (y.val n) (tmeChar f n % 3 ^ (n + 1))
  exact cra_pow_reduce (n + 1) (by omega) (y.val n) (tmeChar f n)

/-- **TMI-5d（★一意性）: 実単元は自己同型を一意に決める** — `tmiFromUnits u = tmiFromUnits v`
    なら u = v。生成元族 `tmeZetaLim` で読み `cci_indexG`・成分ごと `Subtype.ext`。
    `tmi_aut_classify` と合わせ Aut(ℤ₃(1)) ≅ `zpsLimit`（実 ℤ₃^×）の消去形同型を与える。 -/
theorem tmi_units_inj (u v : zpsLimit.carrier)
    (h : ∀ y, (tmiFromUnits u).map y = (tmiFromUnits v).map y) : u = v := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  have hcomp : ((tmiFromUnits u).map tmeZetaLim).val n
      = ((tmiFromUnits v).map tmeZetaLim).val n :=
    congrFun (congrArg Subtype.val (h tmeZetaLim)) n
  have hpow : (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) ((u.val n).val)
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) ((v.val n).val) := hcomp
  have hval : ctmPow (n + 1) (by omega) ((u.val n).val)
      = ctmPow (n + 1) (by omega) ((v.val n).val) := by
    have hv := congrArg Subtype.val hpow
    rw [cmr_pow_zeta (n + 1) (by omega) ((u.val n).val),
        cmr_pow_zeta (n + 1) (by omega) ((v.val n).val)] at hv
    exact hv
  have hidx := cci_indexG (n + 1) (by omega) ((u.val n).val) ((v.val n).val)
    (v.val n).property.1 hval
  rw [Nat.mod_eq_of_lt (u.val n).property.1] at hidx
  exact hidx

/-! ## TMI-6: capstone — 不定性の正確な特徴付け（正直: 消去ではない・特徴付け） -/

/-- **TMI-6a: 不定性特徴付けデータ** — End(T) の完全分類（tme）に、Galois 同変性の
    自明性（`tmi_endo_gal_commute`）・作用の χ 記述（`tmi_act_char`）・実 ℤ₃^× の
    自己同型としての実現（`tmi_from_units_iso`）・任意同型の実単元分類（`tmi_aut_classify`）・
    実単元の一意性（`tmi_units_inj`）を束ねる。**不定性を消去せず、正確に ℤ₃^× と
    特徴付ける** 証明書（§4-(1)(6)）。 -/
structure TmiIndeterminacyData where
  /-- End(ℤ₃(1)) の完全分類（tme・可除性フィルトレーション＋自動降下）。 -/
  endo : TmeEndoData
  /-- 任意の自己準同型が Galois 作用と可換（同変性条件は End(T) 上で空）。 -/
  gal_commute : ∀ (f : Hom tmzLimit tmzLimit) (s : ctlProfinite.carrier)
    (y : tmzLimit.carrier),
    f.map ((tmzActHom s).map y) = (tmzActHom s).map (f.map y)
  /-- Galois 作用の指数族は円分指標 χ に一致。 -/
  act_char : ∀ (s : ctlProfinite.carrier) (n : Nat),
    tmeChar (tmzActHom s) n % 3 ^ (n + 1)
      = ((cliChar n).map (s.val n)).val % 3 ^ (n + 1)
  /-- 実 ℤ₃^× の各元が両側逆を持つ自己同型を与える（実現）。 -/
  aut_realize : ∀ (u : zpsLimit.carrier),
    (∀ y, (tmiFromUnits (zpsLimit.inv u)).map ((tmiFromUnits u).map y) = y) ∧
    (∀ y, (tmiFromUnits u).map ((tmiFromUnits (zpsLimit.inv u)).map y) = y)
  /-- 任意の自己同型は実 ℤ₃^× の（一意の）元から来る。 -/
  aut_classify : ∀ (f g : Hom tmzLimit tmzLimit),
    (∀ y, g.map (f.map y) = y) → (∀ y, f.map (g.map y) = y) →
    ∃ u : zpsLimit.carrier, ∀ y, f.map y = (tmiFromUnits u).map y
  /-- 実 ℤ₃^× の元は自己同型を一意に決める。 -/
  aut_inj : ∀ (u v : zpsLimit.carrier),
    (∀ y, (tmiFromUnits u).map y = (tmiFromUnits v).map y) → u = v

/-- **TMI-6b: witness** — 全フィールド既証明の純レコード。実 ℤ₃(1) の自己同型不定性が
    ちょうど実 ℤ₃^×=`zpsLimit` である（正直: 消去ではなく特徴付け）ことの A7e 完全証明。 -/
def tmiIndeterminacyData : TmiIndeterminacyData where
  endo := tmeEndoData
  gal_commute := tmi_endo_gal_commute
  act_char := tmi_act_char
  aut_realize := tmi_from_units_iso
  aut_classify := tmi_aut_classify
  aut_inj := tmi_units_inj

end IUT
