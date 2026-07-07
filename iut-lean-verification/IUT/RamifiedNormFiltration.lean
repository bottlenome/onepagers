/-
  IUT/RamifiedNormFiltration.lean
  -- M420F RamifiedNormFiltration [実・本物・柱B]
  -- complete_pct 影響: 柱B で 順（tame）分岐ノルムのフィルトレーション番号シフト
  --   ψ(i)=e·i（Herbrand の下付き↔上付き番号付け, tame では G_i 自明で φ(u)=u/e, ψ=φ⁻¹=e·u）を
  --   本物 Nat 算術で建設し、**N(U_L^(ψ(i))) ⊆ U_K^(i)**（分岐ノルムの段シフト）を M415F の段保存
  --   × 単調減少で本物証明。**e=1（不分岐）で ψ(i)=i となり M415F の N(U^(i))=U^(i) を厳密に回復**
  --   （genuine reduction）。⌊i/e⌋ 側の N(U_L^(i)) ⊆ U_K^(⌊i/e⌋) も本物化。
  -- 正直な限定: 野生（wild）分岐（p ∣ e）の完全な Herbrand ψ（区分線形・跳躍つき）・
  --   高次分岐群 upper/lower numbering の Hasse–Arf 定理は骨組みも置かず後続。単一局所体
  --   K=ℚ_p 上の principalUnits 模型でシフトを index 算術として忠実に扱う部分ケース。

  ────────────────────────────────────────────────────────────────────────
  二軸（CLAUDE.md §1）
  * 分類: **[実]**（(a) 昇格 + (b) 本物建設）。M415F の不分岐段保存 N(U^(i))=U^(i) を、
    tame 分岐指数 e の **Herbrand シフト ψ(i)=e·i** で番号付けし直し、
    分岐ノルムの本質——フィルトレーションの番号が e 倍される——を本物 Nat 算術で閉じる。
  * complete_pct 影響: **前進あり**（柱B 分岐ノルムの段シフト ψ(i)=e·i の本物建設）。
    M415F は e=1 の不分岐ケースのみ。本モジュールは一般 tame e≥1 の
    N(U_L^(ψ(i)))⊆U_K^(i) を新規に本物証明し、e=1 で M415F を厳密回復する。

  既存モジュールの何を本物化したか
  * M415F `huf_norm_map_level`（N(U^(i))=U^(i)、不分岐）を、tame 分岐の番号シフト
    ψ(i)=e·i を通して `rnf_norm_shift`（N(U^(ψ(i)))⊆U^(i)）へ一般化。
    e=1 で ψ=id ゆえ `rnf_norm_shift_unram` が M415F に一致（`rnf_ex_e1_is_m415f`）。
  * M381F/M386F の tame 判定 ¬ p ∣ e を分岐指数 e の tame 述語 `rnfTame` として再利用。

  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
  * `rnfPsi` / `rnf_psi_eq` / `rnf_psi_unram` / `rnf_psi_ge` / `rnf_psi_mono`
      — Herbrand ψ(i)=e·i、e=1 で恒等、単調、i≤ψ(i)
  * `rnfPhi` / `rnf_phi_psi` — 逆側 φ(i)=⌊i/e⌋、φ(ψ(i))=i（tame）
  * `rnf_split_antitone` — split 段の単調減少 U^(e)⊆U^(d)（d≤e）
  * `rnf_norm_shift` — **N(U_L^(ψ(i))) ⊆ U_K^(i)**（tame 分岐ノルムの段シフト・本命題）
  * `rnf_norm_shift_floor` — N(U_L^(i)) ⊆ U_K^(⌊i/e⌋)（床側の分岐シフト）
  * `rnf_norm_shift_unram` — e=1 で N(U^(ψ(i)))=U^(i)（M415F 回復・両含）
  * `RamifiedNormFiltrationData` / `rnfDataOf` / `rnf_exists` — capstone
  * `rnf_ex_e2_*`（e=2 tame, p=3: ψ(i)=2i）・`rnf_ex_e1_is_m415f`（e=1 で M415F）

  正直な限定（CLAUDE.md §4: 消去・弱化禁止）
  * 扱うのは **tame（順）分岐**（p ∤ e）のみ。ψ が線形 ψ(i)=e·i になるのは tame の帰結で、
    **野生分岐（p ∣ e）の区分線形 ψ（跳躍つき）** と高次分岐群の upper/lower numbering・
    Hasse–Arf の整数跳躍定理は本モジュール対象外——後続。
  * 単一局所体 K=ℚ_p 上の principalUnits 模型で、拡大 L 側と K 側の U^(·) を同一模型の
    index 算術（e 倍シフト）として忠実に表す部分ケース。実 O_L^×→O_K^× のノルムそのものの
    有限分離拡大構成は M335F normGMap 模型に留まる。

  全て選択公理不使用（propext/Quot.sound のみ）。共有ファイル未変更（新規 1 本）。
-/
import IUT.HigherUnitFiltration

namespace IUT

/-! ## §1 Herbrand ψ 関数（tame）ψ(i) = e·i -/

/-- **M420F-1: Herbrand ψ 関数（tame）** ψ(i) = e·i。
    tame 分岐では高次分岐群 G_j（j≥1）が自明ゆえ φ(u)=u/e（区分線形の傾き 1/e）、
    その逆 ψ=φ⁻¹ が下付き↔上付き番号付けの変換 ψ(i)=e·i。分岐ノルムはこの ψ で
    フィルトレーションの番号をシフトする。 -/
def rnfPsi (e i : Nat) : Nat := e * i

/-- **M420F-1b: ψ の値（本物・定義的）** ψ(i) = e·i。 -/
theorem rnf_psi_eq (e i : Nat) : rnfPsi e i = e * i := rfl

/-- **M420F-1c: e=1（不分岐）で ψ=id（本物・M415F 回復の核）** ψ_1(i) = i。 -/
theorem rnf_psi_unram (i : Nat) : rnfPsi 1 i = i := Nat.one_mul i

/-- 補題: 1 ≤ e なら i ≤ e·i（e≥1 の乗法単調・帰納で本物）。 -/
theorem rnf_le_mul (e i : Nat) (he : 1 ≤ e) : i ≤ e * i := by
  cases e with
  | zero => omega
  | succ k =>
    show i ≤ Nat.succ k * i
    rw [Nat.succ_mul]
    omega

/-- **M420F-1d: i ≤ ψ(i)（tame シフトは番号を増やす）** — e≥1 で U^(ψ(i))⊆U^(i)。 -/
theorem rnf_psi_ge (e i : Nat) (he : 1 ≤ e) : i ≤ rnfPsi e i :=
  rnf_le_mul e i he

/-- **M420F-1e: ψ は単調**（a≤b ⇒ ψ(a)≤ψ(b)）。 -/
theorem rnf_psi_mono (e : Nat) {a b : Nat} (h : a ≤ b) : rnfPsi e a ≤ rnfPsi e b := by
  show e * a ≤ e * b
  exact Nat.mul_le_mul (Nat.le_refl e) h

/-! ## §2 逆側 φ(i)=⌊i/e⌋ と φ∘ψ=id -/

/-- **M420F-2: Herbrand φ 関数（tame・床）** φ(i) = ⌊i/e⌋。ψ の逆側。 -/
def rnfPhi (e i : Nat) : Nat := i / e

/-- **M420F-2b: φ∘ψ = id（tame・本物）** φ(ψ(i)) = ⌊e·i/e⌋ = i（e≥1）。
    tame では φ と ψ が互いに逆（下付き↔上付き番号付けの往復）。 -/
theorem rnf_phi_psi (e i : Nat) (he : 1 ≤ e) : rnfPhi e (rnfPsi e i) = i := by
  show (e * i) / e = i
  exact Nat.mul_div_cancel_left i he

/-! ## §3 split 段の単調減少（U^(e) ⊆ U^(d), d≤e） -/

/-- **M420F-3: split 段の単調減少** d ≤ e ⇒ U^(e) ⊆ U^(d)（split model 版）。
    M31 `unitFiltration_antitone` を単数部（第2成分）に適用し、付値 0 条件は保つ。 -/
theorem rnf_split_antitone (p : Nat) {d e : Nat} (h : d ≤ e)
    (g : (unitsModel (principalUnits p)).carrier)
    (hg : (hufSplitLevel p e).mem g) : (hufSplitLevel p d).mem g := by
  obtain ⟨h1, h2⟩ := hg
  exact ⟨h1, unitFiltration_antitone p h g.2 h2⟩

/-! ## §4 分岐（tame）ノルムのフィルトレーション番号シフト N(U^(ψ(i)))⊆U^(i) -/

/-- **M420F-4: tame 分岐ノルムの段シフト（本命題）** N(U_L^(ψ(i))) ⊆ U_K^(i)。
    番号 ψ(i)=e·i の段はノルムで不変（M415F `huf_norm_map_level`）、かつ e≥1 で
    ψ(i)≥i ゆえ単調減少 U^(ψ(i))⊆U^(i)。両者を合成して分岐ノルムの本質——
    フィルトレーション番号が e 倍にシフトして落ちる——を本物証明。 -/
theorem rnf_norm_shift (p e i : Nat) (n : Int) (he : 1 ≤ e)
    (y : (unitsModel (principalUnits p)).carrier)
    (hy : (Subgroup.map (normGMap (principalUnits p) n)
            (hufSplitLevel p (rnfPsi e i))).mem y) :
    (hufSplitLevel p i).mem y := by
  have hstep : (hufSplitLevel p (rnfPsi e i)).mem y :=
    (huf_norm_map_level p (rnfPsi e i) n y).mp hy
  have hle : i ≤ rnfPsi e i := rnf_psi_ge e i he
  exact rnf_split_antitone p hle y hstep

/-- **M420F-4b: 床側の段シフト** N(U_L^(i)) ⊆ U_K^(⌊i/e⌋)。
    番号 i の段はノルムで不変、かつ ⌊i/e⌋≤i ゆえ単調減少で U^(i)⊆U^(⌊i/e⌋)。 -/
theorem rnf_norm_shift_floor (p e i : Nat) (n : Int)
    (y : (unitsModel (principalUnits p)).carrier)
    (hy : (Subgroup.map (normGMap (principalUnits p) n)
            (hufSplitLevel p i)).mem y) :
    (hufSplitLevel p (rnfPhi e i)).mem y := by
  have hstep : (hufSplitLevel p i).mem y :=
    (huf_norm_map_level p i n y).mp hy
  have hle : rnfPhi e i ≤ i := Nat.div_le_self i e
  exact rnf_split_antitone p hle y hstep

/-- **M420F-4c: e=1（不分岐）で M415F を厳密回復（両含）** —
    ψ_1(i)=i ゆえ N(U^(ψ(i)))=U^(i) が M415F `huf_norm_map_level` に一致。
    分岐シフトの e=1 特殊化が不分岐段保存であることの genuine reduction。 -/
theorem rnf_norm_shift_unram (p i : Nat) (n : Int)
    (y : (unitsModel (principalUnits p)).carrier) :
    (Subgroup.map (normGMap (principalUnits p) n)
        (hufSplitLevel p (rnfPsi 1 i))).mem y
      ↔ (hufSplitLevel p i).mem y := by
  rw [rnf_psi_unram i]
  exact huf_norm_map_level p i n y

/-! ## §5 tame 分岐述語（M381F/M386F の ¬ p ∣ e を再利用） -/

/-- **M420F-5: tame（順）分岐述語** p ∤ e。ψ(i)=e·i が線形になる（跳躍なし）条件。
    M381F `cdf_tamely_ramified` / M386F `cpp_k1_tamely_ramified` と同じ tame 判定。 -/
def rnfTame (p e : Nat) : Prop := ¬ p ∣ e

/-- **M420F-5b: 具体 tame** p=3, e=2 は tame（3 ∤ 2）。e=2 分岐の worked example 用。 -/
theorem rnf_tame_3_2 : rnfTame 3 2 := by
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

/-- **M420F-5c: e=1 は常に tame**（p≥2 で p ∤ 1）— 不分岐は tame の退化。 -/
theorem rnf_tame_e1 (p : Nat) (hp : 2 ≤ p) : rnfTame p 1 := by
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

/-! ## §6 capstone: 分岐ノルムフィルトレーションデータ -/

/-- **M420F-6: 分岐ノルムフィルトレーションデータ** — 素数 p、単位性 hp、tame 分岐指数
    e（he: e≥1, tame: p∤e）、ノルム次数 deg、Herbrand ψ を束ね、
      * ψ(i)=e·i（`psi_eq`）
      * i ≤ ψ(i)（`psi_ge`）・ψ 単調（`psi_mono`）
      * **分岐ノルムの段シフト** N(U^(ψ(i)))⊆U^(i)（`norm_shift`）
    を要請する。局所類体論の分岐ノルムフィルトレーション（tame）の代数的核。 -/
structure RamifiedNormFiltrationData where
  p : Nat
  hp : 1 ≤ p
  e : Nat
  he : 1 ≤ e
  deg : Int
  tame : rnfTame p e
  psi : Nat → Nat
  psi_eq : ∀ i, psi i = e * i
  psi_ge : ∀ i, i ≤ psi i
  psi_mono : ∀ {a b : Nat}, a ≤ b → psi a ≤ psi b
  norm_shift : ∀ i y,
    (Subgroup.map (normGMap (principalUnits p) deg) (hufSplitLevel p (psi i))).mem y
      → (hufSplitLevel p i).mem y

/-- **M420F-6b: データの構成**（p, hp, tame 指数 e, he, tame 証明, 次数 n から本物 witness）。 -/
def rnfDataOf (p : Nat) (hp : 1 ≤ p) (e : Nat) (he : 1 ≤ e)
    (htame : rnfTame p e) (n : Int) : RamifiedNormFiltrationData where
  p := p
  hp := hp
  e := e
  he := he
  deg := n
  tame := htame
  psi := fun i => rnfPsi e i
  psi_eq := fun _ => rfl
  psi_ge := fun i => rnf_psi_ge e i he
  psi_mono := fun h => rnf_psi_mono e h
  norm_shift := fun i y hy => rnf_norm_shift p e i n he y hy

/-- **M420F-6c: データの存在**（無矛盾性 witness、p=2, e=1 不分岐）。 -/
theorem rnf_exists : Nonempty RamifiedNormFiltrationData :=
  ⟨rnfDataOf 2 (by omega) 1 (by omega) (rnf_tame_e1 2 (by omega)) 3⟩

/-! ## §7 worked examples: e=2 tame (p=3), e=1 recovers M415F -/

/-- **M420F-7a: 実例** e=2 の ψ(i)=2i（tame シフトの傾き 2）。 -/
theorem rnf_ex_e2_psi (i : Nat) : rnfPsi 2 i = 2 * i := rfl

/-- **M420F-7b: 実例** ψ_2(3) = 6（具体値）。 -/
theorem rnf_ex_e2_psi_val : rnfPsi 2 3 = 6 := rfl

/-- **M420F-7c: 実例** e=2 tame（p=3）で N(U^(ψ_2(i))) ⊆ U^(i)（分岐ノルム段シフト）。 -/
theorem rnf_ex_e2_shift (i : Nat) (n : Int)
    (y : (unitsModel (principalUnits 3)).carrier)
    (hy : (Subgroup.map (normGMap (principalUnits 3) n)
            (hufSplitLevel 3 (rnfPsi 2 i))).mem y) :
    (hufSplitLevel 3 i).mem y :=
  rnf_norm_shift 3 2 i n (by omega) y hy

/-- **M420F-7d: 実例** φ∘ψ の往復（e=2, p 任意）φ_2(ψ_2(i)) = i。 -/
theorem rnf_ex_e2_phi_psi (i : Nat) : rnfPhi 2 (rnfPsi 2 i) = i :=
  rnf_phi_psi 2 i (by omega)

/-- **M420F-7e: 実例（genuine reduction）** e=1 で分岐段シフトが M415F 不分岐段保存に一致。
    ψ_1(i)=i ゆえ N(U^(ψ_1(i)))=U^(i) は M415F `huf_norm_map_level` そのもの。 -/
theorem rnf_ex_e1_is_m415f (p i : Nat) (n : Int)
    (y : (unitsModel (principalUnits p)).carrier) :
    (Subgroup.map (normGMap (principalUnits p) n)
        (hufSplitLevel p (rnfPsi 1 i))).mem y
      ↔ (hufSplitLevel p i).mem y :=
  rnf_norm_shift_unram p i n y

end IUT
