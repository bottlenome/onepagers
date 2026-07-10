/-
  IUT/Zmod3PowUnitsSystem.lean — ZPS（A3 M4b の単数側骨格: (ℤ/3^{n+1})^× の
  逆系と逆極限 ℤ₃^×、および射影全射性の先取り）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 IUT の
     指標同型 Gal(ℚ(ζ_{3ⁿ})/ℚ) ≅ (ℤ/3ⁿ)^× の**逆極限側**を本物に積む）。
     設計 `audit/A3-m4-character-iso-detail-2026-07-09.md` §3.1 の
     Zmod3PowUnitsSystem をそのまま実装する。ZPU（`Zmod3PowUnits.lean`）の
     乗法群 `zpuGrp ℓ hℓ`＝(ℤ/3^ℓ)^× を Nat 添字 n ↦ (ℤ/3^{n+1})^×（ctlGal n の
     添字整合）に並べ、`IUT/Profinite.lean`/`IUT/ProObject.lean` の既存
     `InverseSystem`/`natSystem`/`limitGrp`/`limitProj` 機構にそのまま載せる。
     単数側の遷移射は ctl の Gal 側（反復合成）と異なり**単発 `% 3^{i+1}`**
     で i ≤ j 一般に直接書け、cast・反復が一切不要——これが本ファイルが
     単数側で極限を先に組む理由。

  **complete_pct 影響**: A3 M4（指標同型 Gal(ℚ(ζ_{3ⁿ})/ℚ) ≅ (ℤ/3ⁿ)^×・逆極限
  ℤ₃^×）の M4b 単数側の逆系・逆極限を本物に構成し、**M4c の核（単数側の射影
  全射性 `zps_proj_surjective`）を純 Nat・choice-free で先取り**する。
  cli（`IUT/CyclotomicLimitIso.lean`・cci と zps を橋渡しする極限同型）が
  Gal 側の逆系 `ctlSystem` と本ファイルの `zpsSystem` を同型で結んだ時点で
  complete_pct（A3 全体の実 IUT 完全証明率）に反映される。**本ファイル単体
  では complete_pct 未設定**（cli 到達で反映、上記ヘッダ規約に準拠）。

  正直な限定（§4 規約により消去・弱化しない）:
   (i)   p = 3 専用。一般の p 進整数 ℤ_p ではない。
   (ii)  「逆極限としての ℤ₃^×」であって、桁列（3 進展開 a₀+a₁·3+a₂·3²+…）に
         よる ℤ₃^× の構成ではない。本ファイルの `zpsLimit` は
         `{ s : ∀ n, (zpuGrp (n+1) _).carrier // 整合族 }` という逆極限の
         定義そのものであり、桁列表現との同値は別途（後続、範囲外）。
   (iii) Gal 側の逆系（ctl）とのレベル橋・同型は本ファイルに含めない
         （`cli`・後続ファイルの射程）。本ファイルは単数側のみで閉じる。
   (iv)  `zps_proj_surjective` は各段 n の任意の元 a に対する ∃ 文だが、
         witness `u` は `a.val % 3^{m+1}`（m は任意添字）という閉じた式で
         直接与えており、選択公理（Classical.choice）は一切使用していない。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]・Classical.choice
  無し、自分で `#print axioms` を確認済み）。禁止タクティク（simp/decide/
  by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用。3^ℓ は omega 不可のため ZPU-0 の冪補題（`zpu_pow_pos`/`zpu_pow_dvd`）
  を利用。新規ファイル 1 個のみ（共有ファイルは親が統合）。
  数学的依存は `Zmod3PowUnits.lean`（zpu）のみ、機構依存は既存の
  `IUT.Profinite`（`InverseSystem`/`Compatible`/`limitGrp`/`limitProj`）・
  `IUT.ProObject`（`natSystem`）（いずれも既存 choice-free 部品の再利用）。
-/
import IUT.Profinite
import IUT.ProObject
import IUT.Zmod3PowUnits

namespace IUT

/-! ## ZPS-1: 添字整合 — U n := (ℤ/3^{n+1})^×（ctlGal n = Gal(cteExt(n+1)) に合わせる） -/

/-- **ZPS-1: レベル n の単数群** `zpsG n := zpuGrp (n+1) _`（(ℤ/3^{n+1})^×）。
    Gal 側 `ctlGal n = galoisGroupGrp (cteExt (n+1) _)` に添字を合わせる。 -/
def zpsG (n : Nat) : Grp := zpuGrp (n + 1) (by omega)

/-! ## ZPS-2: 遷移射（i ≤ j 一般を単発 mod で・反復不使用） -/

/-- **ZPS-2: 遷移射 `zpsT`** — `a ↦ a % 3^{i+1}`（単発。Gal 側の反復合成と
    異なり cast・帰納が一切不要）。担体条件は ZPU-3b `zpu_mod_nd3`。 -/
def zpsT {i j : Nat} (h : i ≤ j) : Hom (zpsG j) (zpsG i) where
  map := fun a =>
    ⟨a.val % 3 ^ (i + 1),
      Nat.mod_lt _ (by have := zpu_pow_pos (i + 1); omega),
      zpu_mod_nd3 (i + 1) (by omega) a.val a.property.2⟩
  map_mul := fun a b => by
    apply Subtype.ext
    show a.val * b.val % 3 ^ (j + 1) % 3 ^ (i + 1)
        = a.val % 3 ^ (i + 1) * (b.val % 3 ^ (i + 1)) % 3 ^ (i + 1)
    rw [Nat.mod_mod_of_dvd (a.val * b.val) (zpu_pow_dvd (show i + 1 ≤ j + 1 by omega)),
        Nat.mul_mod a.val b.val (3 ^ (i + 1))]

/-- **ZPS-2a: 恒等保存** — 自層への遷移射は恒等（`Nat.mod_eq_of_lt`）。 -/
theorem zpsT_self (i : Nat) (x : (zpsG i).carrier) :
    (zpsT (Nat.le_refl i)).map x = x := by
  apply Subtype.ext
  show x.val % 3 ^ (i + 1) = x.val
  exact Nat.mod_eq_of_lt x.property.1

/-- **ZPS-2b: 推移性** — 遷移射の合成は合成の遷移射（`Nat.mod_mod_of_dvd`・
    単発 mod のため反復展開が不要）。 -/
theorem zpsT_comp {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) (x : (zpsG k).carrier) :
    (zpsT hij).map ((zpsT hjk).map x) = (zpsT (Nat.le_trans hij hjk)).map x := by
  apply Subtype.ext
  show x.val % 3 ^ (j + 1) % 3 ^ (i + 1) = x.val % 3 ^ (i + 1)
  exact Nat.mod_mod_of_dvd x.val (zpu_pow_dvd (show i + 1 ≤ j + 1 by omega))

/-! ## ZPS-3: 逆系と逆極限 ℤ₃^× -/

/-- **ZPS-3: 単数側の逆系**（`natSystem` 経由・Nat 添字・(≤)）。 -/
@[reducible] def zpsSystem : InverseSystem := natSystem zpsG zpsT zpsT_self zpsT_comp

/-- **ZPS-3a: 逆極限群 `zpsLimit` = ℤ₃^×**（逆極限としての定義そのもの）。 -/
def zpsLimit : Grp := limitGrp zpsSystem

/-! ## ZPS-4: ★単数側の射影全射性（M4c の核・純 Nat 算術で先取り、choice-free） -/

/-- **ZPS-4a: witness 族**（トップレベル def・期待型を明示することで
    `refine` ネスト内の期待型伝播の曖昧さを避ける） — `a` の各段
    `3^{m+1}` での剰余。`ha : ¬3∣a` は担体条件の材料。 -/
def zpsWitnessFam (a : Nat) (ha : ¬ 3 ∣ a) (m : Nat) : (zpsG m).carrier :=
  ⟨a % 3 ^ (m + 1),
    Nat.mod_lt _ (by have := zpu_pow_pos (m + 1); omega),
    zpu_mod_nd3 (m + 1) (by omega) a ha⟩

/-- **ZPS-4b: witness 族の整合性** — `zpsWitnessFam` は `zpsSystem` の
    整合族をなす（`Nat.mod_mod_of_dvd`）。 -/
theorem zpsWitnessFam_compat (a : Nat) (ha : ¬ 3 ∣ a) :
    Compatible zpsSystem (zpsWitnessFam a ha) := by
  intro i j h
  apply Subtype.ext
  show a % 3 ^ (j + 1) % 3 ^ (i + 1) = a % 3 ^ (i + 1)
  exact Nat.mod_mod_of_dvd a (zpu_pow_dvd (Nat.succ_le_succ h))

/-- **ZPS-4: 射影全射性** — 任意のレベル n・任意の元 a に対し、極限
    `zpsLimit` の元 u で `(limitProj zpsSystem n).map u = a` となるものが
    存在する。witness `u` の各成分は `a.val % 3^{m+1}`（閉じた式）で直接
    与える——選択公理は不要。 -/
theorem zps_proj_surjective (n : Nat) :
    ∀ a : (zpsG n).carrier, ∃ u : zpsLimit.carrier, (limitProj zpsSystem n).map u = a := by
  intro a
  refine ⟨⟨zpsWitnessFam a.val a.property.2, zpsWitnessFam_compat a.val a.property.2⟩, ?_⟩
  apply Subtype.ext
  show a.val % 3 ^ (n + 1) = a.val
  exact Nat.mod_eq_of_lt a.property.1

/-! ## ZPS-5: 非退化（安い系） -/

/-- **ZPS-5a: 2 < 3^{m+1}**（各段で成立、`zpu_pow_pos` から）。 -/
theorem zpsTwoLt (m : Nat) : 2 < 3 ^ (m + 1) := by
  have h1 : 1 ≤ (3 : Nat) ^ m := zpu_pow_pos m
  have h2 : (3 : Nat) ^ (m + 1) = 3 ^ m * 3 := Nat.pow_succ 3 m
  omega

/-- **ZPS-5b: 3∤2**。 -/
theorem zpsTwoNd3 : ¬ 3 ∣ (2 : Nat) := by
  intro hd
  obtain ⟨k, hk⟩ := hd
  omega

/-- **ZPS-5c: 定数族 a=2**（トップレベル def・期待型明示）。 -/
def zpsConstFam (m : Nat) : (zpsG m).carrier := ⟨2, zpsTwoLt m, zpsTwoNd3⟩

/-- **ZPS-5d: 定数族の整合性**。 -/
theorem zpsConstFam_compat : Compatible zpsSystem zpsConstFam := by
  intro i j h
  apply Subtype.ext
  show (2 : Nat) % 3 ^ (i + 1) = 2
  exact Nat.mod_eq_of_lt (zpsTwoLt i)

/-- **ZPS-5: `zpsLimit` の非退化** — 定数族 a=2（各段 2 < 3^{m+1}・3∤2）が
    単位元でない元を与える。 -/
theorem zps_nontrivial : ∃ u : zpsLimit.carrier, u ≠ zpsLimit.one := by
  refine ⟨⟨zpsConstFam, zpsConstFam_compat⟩, ?_⟩
  intro h
  have h2 : (2 : Nat) = 1 := congrArg (fun x => (x.val 0).val) h
  omega

end IUT
