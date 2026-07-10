/-
  IUT/CyclotomicLimitIso.lean — CLI（A3 M4b: 極限同型
  Gal(ℚ(ζ_{3^∞})/ℚ) ≅ lim_n (ℤ/3^{n+1})^× = ℤ₃^×）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・実円分塔
     の逆極限 profinite Galois 群 `ctlProfinite` = Gal(ℚ(ζ_{3^∞})/ℚ)（ctl・M3 で
     本物に構成）と、単数側の逆極限 `zpsLimit` = lim (ℤ/3^{n+1})^× = ℤ₃^×（zps で
     本物に構成）の間の **極限同型を本物に確立する**）。各レベル n の指標同型
     `cciToUnits`/`cciFromUnits`（cci・M4a）を添字 n ↦ (n+1) で並べ、Gal 側の
     反復制限 `ctlRestr` と単数側の単発剰余 `zpsT` に対する **compat 正方形**
     （`cli_char_restr`・単段 `cli_char_step` の差分帰納）で両逆系を橋渡しし、
     成分ごとの左右逆（cci_left_inv/right_inv）で逆極限の同型
     `cliTo`/`cliFrom`/`cli_left_inv`/`cli_right_inv` を完全証明する。

  **complete_pct 影響**: A3 M4b——**実 profinite Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^×
  （逆極限としての単数群）の同型を本物に確立**する。cci（各段 M4a）と zps
  （単数側逆極限 M4b）の二つの逆系を同型で結んだ極限。円分塔の逆極限が古典的に
  既知の ℤ₃^× と一致することを形式化した。本ファイル単体では complete_pct 未設定
  （独立監査で反映——設計は cli 到達で A3 0.73-0.74・柱A% 39→40 見込み）。

  内容（設計 audit/A3-m4-character-iso-detail-2026-07-09.md §3.2・CLI-0〜CLI-4）:
   * `cliChar`/`cliAut` — レベル橋（cci の (n+1) 段を Nat 添字 n に付け替え）。
   * `cli_res_char` — 制限の指標 = 上段指標 mod 3^m（csaSub_zeta ＋ cci_indexG）。
   * `cli_char_step` — 単段 compat 正方形（★橋補題は defeq: ctrChar (n+1) =
     ctr_charG (n+2)）。
   * `cli_char_restr_aux`/`cli_char_restr` — i ≤ j 一般の compat 正方形
     （ctl_restr_step 最上段 peel の差分帰納＋zpsT_comp 合流。ctl_restr_comp_aux 写経）。
   * `cli_char_aut`/`cli_aut_char` — 成分ごと左右逆（cci_right_inv/left_inv）。
   * `cliTo`/`cliFrom` — 逆極限間の準同型（媒介射は担体直接構成・limit_universal 不使用）。
   * `cli_left_inv`/`cli_right_inv` — 逆極限の左右逆（成分ごと ＋ funext）。
   * `CliIsoData`/`cliIsoData` — capstone: Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^×。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・ℚ 上・円分塔 ℚ(ζ_{3^{n+1}}) の忠実な部分ケース（一般 p は含めない）。
   (ii)  ℤ₃^× は **逆極限としての単数群** lim (ℤ/3^{n+1})^× であって、3 進桁列
         （a₀+a₁·3+a₂·3²+…）による構成ではない（zps 正直申告 (ii) を継承）。
   (iii) 射影全射性の束ねは cps（後続）の射程。本ファイルは各段同型の極限としての
         全単射（左右逆）まで。
   (iv)  これは円分切片 Gal(ℚ(ζ_{3^∞})/ℚ) であって実 G_ℚ そのものではない
         （G_ℚ の可解商・Kronecker–Weber 部分に対応する副有限商の一つ・ctl 正直申告 (iv)）。

  全て選択公理不使用（新規 `Classical.choice` を証明本体に導入しない・
  propext/Quot.sound のみ）。設計の choice-free 予防線に従い `limit_universal`
  （∃ 形）は使用せず、媒介射は担体の直接構成で与える。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/
  dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.CyclotomicCharIso
import IUT.Zmod3PowUnitsSystem
import IUT.CyclotomicTowerLimit

namespace IUT

/-! ## CLI-0: レベル橋 — cci の (n+1) 段を Nat 添字 n に付け替える -/

/-- **CLI-0a: レベル指標 χ_n** — Gal(ℚ(ζ_{3^{n+1}})/ℚ) → (ℤ/3^{n+1})^×。
    `cciToUnits (n+1)` は proof-irrelevance で `Hom (ctlGal n) (zpsG n)` の型に付く
    （ctlGal n = galoisGroupGrp (cteExt (n+1) _)・zpsG n = zpuGrp (n+1) _）。 -/
def cliChar (n : Nat) : Hom (ctlGal n) (zpsG n) := cciToUnits (n + 1) (by omega)

/-- **CLI-0b: レベル代入自己同型 σ_a** — (ℤ/3^{n+1})^× → Gal(ℚ(ζ_{3^{n+1}})/ℚ)。 -/
def cliAut (n : Nat) : Hom (zpsG n) (ctlGal n) := cciFromUnits (n + 1) (by omega)

/-- **CLI-0c: 成分右逆** χ_n(σ_a) = a（cci_right_inv の cli ラッパ）。 -/
theorem cli_char_aut (n : Nat) (a : (zpsG n).carrier) :
    (cliChar n).map ((cliAut n).map a) = a :=
  cci_right_inv (n + 1) (by omega) a

/-- **CLI-0d: 成分左逆** σ_{χ_n σ} = σ（cci_left_inv の cli ラッパ）。 -/
theorem cli_aut_char (n : Nat) (σ : (ctlGal n).carrier) :
    (cliAut n).map ((cliChar n).map σ) = σ :=
  cci_left_inv (n + 1) (by omega) σ

/-! ## CLI-1: compat 正方形（★本ファイルの中核） -/

/-- **CLI-1a: 制限の指標 = 上段指標 mod 3^m** — res_m(σ) = σ_{ctrChar σ % 3^m}
    （`ctrRes`）の指標は ctrChar σ % 3^m。res の生成元での像 ζ_m^{ctrChar σ % 3^m}
    （`csaSub_zeta`）と指標仕様 `ctr_charG_spec` を突き合わせ、両者 < 3^m で
    `cci_indexG` により合流。cci_charG_csaAut と同型の論法だが ctrRes（csaAut 直接）
    に対して書き下す。 -/
theorem cli_res_char (m : Nat) (hm : 1 ≤ m) (σ : FieldAut (cteField (m + 1) (by omega))) :
    ctr_charG m hm (ctrRes m hm σ) = ctrChar m hm σ % 3 ^ m := by
  have hzeta : (ctrRes m hm σ).toFun (ctmZeta m hm)
      = ctmPow m hm (ctrChar m hm σ % 3 ^ m) :=
    csaSub_zeta m hm (ctrChar m hm σ % 3 ^ m)
  have hspec : (ctrRes m hm σ).toFun (ctmZeta m hm)
      = ctmPow m hm (ctr_charG m hm (ctrRes m hm σ)) :=
    ctr_charG_spec m hm (ctrRes m hm σ)
  have heq : ctmPow m hm (ctr_charG m hm (ctrRes m hm σ))
      = ctmPow m hm (ctrChar m hm σ % 3 ^ m) := by rw [← hspec, hzeta]
  have hvlt : ctrChar m hm σ % 3 ^ m < 3 ^ m :=
    Nat.mod_lt _ (by have := zpu_pow_pos m; omega)
  have hidx := cci_indexG m hm (ctr_charG m hm (ctrRes m hm σ))
    (ctrChar m hm σ % 3 ^ m) hvlt heq
  rw [Nat.mod_eq_of_lt (ctr_charG_lt m hm (ctrRes m hm σ))] at hidx
  exact hidx

/-- **CLI-1b: 単段 compat 正方形** — χ_n(ctlStep n σ) = zpsT (χ_{n+1} σ)。
    LHS.val = ctr_charG (n+1) (ctrRes (n+1) σ) = ctrChar (n+1) σ % 3^{n+1}
    （`cli_res_char`）、RHS.val = ctr_charG (n+2) σ % 3^{n+1}。橋補題
    ctrChar (n+1) σ = ctr_charG (n+2) σ は定義一致（両者 ctmFind (n+2) (σ ζ_{n+2})）。 -/
theorem cli_char_step (n : Nat) (σ : (ctlGal (n + 1)).carrier) :
    (cliChar n).map ((ctlStep n).map σ)
      = (zpsT (Nat.le_succ n)).map ((cliChar (n + 1)).map σ) := by
  apply Subtype.ext
  show ctr_charG (n + 1) (by omega) (ctrRes (n + 1) (by omega) σ.val)
      = ctrChar (n + 1) (by omega) σ.val % 3 ^ (n + 1)
  rw [cli_res_char (n + 1) (by omega) σ.val]

/-- **CLI-1c: i ≤ j 一般 compat 正方形（差分明示・帰納）** — j = i+e で e 帰納。
    最上段 `ctl_restr_step` で peel し、`cli_char_step` の単段 compat と帰納仮説、
    `zpsT_comp`（`Nat.mod_mod_of_dvd`）の合流で閉じる（ctl_restr_comp_aux 写経）。 -/
theorem cli_char_restr_aux (i : Nat) :
    ∀ (e : Nat) (σ : (ctlGal (i + e)).carrier),
      (cliChar i).map ((ctlRestr (Nat.le_add_right i e)).map σ)
        = (zpsT (Nat.le_add_right i e)).map ((cliChar (i + e)).map σ) := by
  intro e
  induction e with
  | zero =>
    intro σ
    have hself : (ctlRestr (Nat.le_add_right i 0)).map σ = σ := ctl_restr_self i σ
    rw [hself]
    exact (zpsT_self i ((cliChar i).map σ)).symm
  | succ f ih =>
    intro σ
    have hpeel : (ctlRestr (Nat.le_add_right i (f + 1))).map σ
        = (ctlRestr (Nat.le_add_right i f)).map ((ctlStep (i + f)).map σ) :=
      ctl_restr_step i (i + f) (Nat.le_add_right i f) σ
    rw [hpeel, ih ((ctlStep (i + f)).map σ), cli_char_step (i + f) σ]
    exact zpsT_comp (Nat.le_add_right i f) (Nat.le_succ (i + f))
      ((cliChar (i + f + 1)).map σ)

/-- **CLI-1d′: 差分明示版の一般 k への輸送**（j = i+e の subst 1 回）。 -/
theorem cli_char_restrK (i j e : Nat) (he : i + e = j) :
    ∀ (h : i ≤ j) (σ : (ctlGal j).carrier),
      (cliChar i).map ((ctlRestr h).map σ) = (zpsT h).map ((cliChar j).map σ) := by
  subst he
  intro h σ
  exact cli_char_restr_aux i e σ

/-- **CLI-1d: compat 正方形（一般 i ≤ j）** — 差分 e = j−i と橋 i+(j−i)=j で
    差分明示版 `cli_char_restrK` に帰着（proof-irrelevance で proof 引数を吸収）。 -/
theorem cli_char_restr {i j : Nat} (h : i ≤ j) (σ : (ctlGal j).carrier) :
    (cliChar i).map ((ctlRestr h).map σ) = (zpsT h).map ((cliChar j).map σ) :=
  cli_char_restrK i j (j - i) (Nat.add_sub_cancel' h) h σ

/-! ## CLI-2: 媒介準同型（担体直接構成・limit_universal 不使用） -/

/-- **CLI-2a: 極限指標 χ : Gal(ℚ(ζ_{3^∞})/ℚ) → ℤ₃^×** — 成分ごと χ_n。compat は
    `cli_char_restr`（Gal 側整合 s.property を単数側整合へ移す）。map_mul は成分ごと。 -/
def cliTo : Hom ctlProfinite zpsLimit where
  map := fun s => ⟨fun n => (cliChar n).map (s.val n),
    fun {i j} h => (cli_char_restr h (s.val j)).symm.trans
      (congrArg (cliChar i).map (s.property h))⟩
  map_mul := fun s t => by
    apply Subtype.ext
    funext n
    exact (cliChar n).map_mul (s.val n) (t.val n)

/-- **CLI-2b: 極限代入自己同型 σ : ℤ₃^× → Gal(ℚ(ζ_{3^∞})/ℚ)** — 成分ごと σ_a。
    逆向き compat 正方形は「元は指標で決まる」で還元（設計 CLI-2 末尾）:
    両辺の χ_i を取ると `cli_char_restr`＋成分右逆＋u.property で一致し、
    成分左逆 `cli_aut_char` で元に戻して等号を得る（左右二重証明を避ける）。 -/
def cliFrom : Hom zpsLimit ctlProfinite where
  map := fun u => ⟨fun n => (cliAut n).map (u.val n), by
    intro i j h
    show (ctlRestr h).map ((cliAut j).map (u.val j)) = (cliAut i).map (u.val i)
    have hchar : (cliChar i).map ((ctlRestr h).map ((cliAut j).map (u.val j)))
        = (cliChar i).map ((cliAut i).map (u.val i)) := by
      rw [cli_char_restr h ((cliAut j).map (u.val j)), cli_char_aut j (u.val j),
          cli_char_aut i (u.val i)]
      exact u.property h
    calc (ctlRestr h).map ((cliAut j).map (u.val j))
        = (cliAut i).map ((cliChar i).map ((ctlRestr h).map ((cliAut j).map (u.val j)))) :=
          (cli_aut_char i _).symm
      _ = (cliAut i).map ((cliChar i).map ((cliAut i).map (u.val i))) :=
          congrArg (cliAut i).map hchar
      _ = (cliAut i).map (u.val i) := congrArg (cliAut i).map (cli_char_aut i (u.val i))⟩
  map_mul := fun u v => by
    apply Subtype.ext
    funext n
    exact (cliAut n).map_mul (u.val n) (v.val n)

/-! ## CLI-3: 左右逆（成分ごと ＋ funext） -/

/-- **CLI-3a: 左逆** σ ↦ χ ↦ σ = id（成分ごと `cli_aut_char`）。 -/
theorem cli_left_inv (s : ctlProfinite.carrier) : cliFrom.map (cliTo.map s) = s := by
  apply Subtype.ext
  funext n
  exact cli_aut_char n (s.val n)

/-- **CLI-3b: 右逆** χ ↦ σ ↦ χ = id（成分ごと `cli_char_aut`）。 -/
theorem cli_right_inv (u : zpsLimit.carrier) : cliTo.map (cliFrom.map u) = u := by
  apply Subtype.ext
  funext n
  exact cli_char_aut n (u.val n)

/-! ## CLI-4: capstone — Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^× -/

/-- **CLI-4a: 極限同型データ** Gal(ℚ(ζ_{3^∞})/ℚ) ≅ lim (ℤ/3^{n+1})^× = ℤ₃^×
    （双方向 Hom ＋ 左右逆）。 -/
structure CliIsoData where
  /-- 指標方向 χ : Gal(ℚ(ζ_{3^∞})/ℚ) → ℤ₃^×。 -/
  toU : Hom ctlProfinite zpsLimit
  /-- σ_a 方向 ℤ₃^× → Gal(ℚ(ζ_{3^∞})/ℚ)。 -/
  fromU : Hom zpsLimit ctlProfinite
  /-- 左逆。 -/
  left_inv : ∀ s, fromU.map (toU.map s) = s
  /-- 右逆。 -/
  right_inv : ∀ u, toU.map (fromU.map u) = u

/-- **CLI-4b: witness** — 全フィールド既証明の純レコード。極限同型
    Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^× の完全証明（M4b 本体）。 -/
def cliIsoData : CliIsoData where
  toU := cliTo
  fromU := cliFrom
  left_inv := cli_left_inv
  right_inv := cli_right_inv

/-- **CLI-4c: 同型の存在**（極限同型 Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^×）。 -/
theorem cliIso_exists : Nonempty CliIsoData := ⟨cliIsoData⟩

end IUT
