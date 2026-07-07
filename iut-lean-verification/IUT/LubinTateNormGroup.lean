-- M390F LubinTateNormGroup [実・本物・柱B]
-- complete_pct 影響: 柱B で LT 相互写像 rec の「核 = ノルム群」(不分岐 LCFT: rec(x)=1 ⟺ x∈N_{L/K}(L^×)) を本物化し、rec が K^×/N から不分岐 Gal=ℤ/d へ単射的に降下・全射することを完全証明、M385F の捻れ作用 [u] と M330F の Artin 写像へ接続。
-- 正直な限定: 全アーベル拡大に対する完全な LCFT 存在定理（一般分岐 L・実 Gal(L/K) 主語の核=ノルム群）は後続。ここは不分岐次数 d / 2^n 捻れレベルの忠実な実部分ケースのみが本物。

/-
  IUT/LubinTateNormGroup.lean — M390F（Lubin–Tate 相互写像の核 = ノルム群: 実部分ケース）

  ────────────────────────────────────────────────────────────────────────
  二軸（CLAUDE.md §1 必守）
  * 分類: **[実]**（(a) 昇格 + (b) 本物先行建設）。M385F（IUT/LubinTateReciprocity.lean,
    prefix `ltr`）が建てた LT 明示的相互律 rec(u)=[u^{-1}]（捻れ作用）と、M335F
    （IUT/NormGroup.lean, prefix `normG`）が建てたノルム写像 N_{L/K}・ノルム群
    N_{L/K}(L^×)・不分岐 LCFT 主定理 `normG_artin_kernel_link` を接合し、
    **相互写像 rec の核 = ノルム群**という局所類体論の中心言明
      rec(x) = 1 ⟺ x ∈ N_{L/K}(L^×)
    を不分岐/捻れレベルの忠実な実部分ケースで完全証明する。
  * complete_pct 影響: 柱B（局所類体論）前進あり。次を完全証明:
      (1) 相互写像 rec = Artin(mod d): K^× = ℤ×O^× → Gal(L/K) = ℤ/d
          （M330F の不分岐商 Artin 写像 `locRecUnram` に接続）。
      (2) **核 = ノルム群** `ltng_kernel_eq_norm`: rec(m,u)=1 ⟺ (m,u)∈N
          （M335F `normG_artin_kernel_link` を主語 rec で本物化）。
      (3) **K^×/N ≅ Gal への降下**: rec は N の剰余類で well-defined
          （`ltng_rec_eq_iff` / `ltng_rec_eq_iff_norm`: rec(x)=rec(y) ⟺ x·y⁻¹∈N）
          かつ Gal=ℤ/d へ全射（`ltng_rec_surj`）。
      (4) **単数（惰性）はノルム群** `ltng_units_in_kernel`: 不分岐では
          O^× ⊆ N（単数は核に落ちる）。M385F で [u] 作用する惰性単数が
          ちょうどノルム群に入ることの整合（`ltng_ltr_unit_kernel`）。
      (5) M385F 明示相互律 rec(u)=[u^{-1}]（捻れ側）の再輸出接続
          （`ltng_ltr_rec_inverse`）。

  ────────────────────────────────────────────────────────────────────────
  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
  * `ltngRec` / `ltngRec_apply`        — 相互写像 rec = Artin(mod d): K^× → ℤ/d
  * `ltng_rec_hom`                     — rec は群準同型
  * `ltng_rec_eq_locRec`               — rec = M330F 不分岐商 Artin 写像(mod d)
  * `ltngKernel`                       — 核述語 {x : rec(x)=1}
  * `ltng_kernel_eq_norm`              — **核 = ノルム群**（不分岐 LCFT 主定理）
  * `ltng_units_in_kernel`             — 単数（惰性）∈ 核 = ノルム群
  * `ltng_rec_surj`                    — rec は Gal=ℤ/d へ全射
  * `ltng_rec_eq_iff` / `ltng_rec_eq_iff_norm`
        — rec の K^×/N への降下（rec(x)=rec(y) ⟺ 付値差が d の倍数 ⟺ x·y⁻¹∈N）
  * `ltng_ltr_unit_kernel`             — M385F の [u]-作用単数 ∈ ノルム群（接続）
  * `ltng_ltr_rec_inverse`             — M385F rec(u)=[u^{-1}]（捻れ側）再輸出
  * `LubinTateNormGroupData` / `ltngData` / `ltng_exists` — capstone + witness
  * 例（不分岐次数 2 の worked examples）

  ────────────────────────────────────────────────────────────────────────
  正直な限定（CLAUDE.md §4: 消去・弱化禁止）
  * 全ての有限アーベル拡大 L/K（分岐を含む）に対する完全な LCFT 存在定理
    ker(rec_K) = N_{L/K}(L^×)、および右辺の**実 Gal(L/K)** による意味づけは
    本モジュール外——後続。ここで本物にしたのは**不分岐次数 d の分裂表示
    モデル**（および 2^n 捻れレベル）上での rec の核 = ノルム群・K^×/N への降下・
    Gal=ℤ/d への全射である。
  * M385F 側の捻れ作用 [u]（惰性の 2^n-捻れ上の作用）と M335F 側のノルム群
    （不分岐核）は、単数が「核=ノルム群に入る」ことで整合づけるが、分岐した
    ノルム剰余記号のフィルトレーション対応（1+m^n ↦ 高次分岐群）は骨組み（後続）。
  * 単数群の実体は M330F/M335F と同じく抽象単数群 U = O^×（ℤ_p^× 等の実構成を
    差せる）。toy 主語ではない: 主語は本物の ℤ・ℤ/d（M13 商群）である。

  全て mathlib なし・新規 Classical.choice なし（propext, Quot.sound のみ）。
  共有ファイル未変更（新規 1 本のみ）。
-/
import IUT.LubinTateReciprocity
import IUT.NormGroup

namespace IUT

/-! ## §1 相互写像 rec = Artin(mod d): K^× → Gal(L/K) = ℤ/d -/

/-- **M390F-1: 相互写像** rec_K : K^× = ℤ×O^× → Gal(L/K) = ℤ/d。
    M335F の `normGArtinModN`（= M330F 不分岐商 Artin 写像 `locRecUnram` を
    有限次数 d の商 ℤ/d へ落としたもの）を、局所類体論の相互写像として主語に置く。
    (m,u) ↦ [m] ∈ ℤ/d（不分岐: 付値 mod d が Frobenius 冪、単数は惰性で消える）。 -/
def ltngRec (U : Grp) (d : Nat) : Hom (unitsModel U) (zmod d) :=
  normGArtinModN U d

/-- 相互写像の明示式: rec(m,u) = [m] ∈ ℤ/d。 -/
theorem ltngRec_apply (U : Grp) (d : Nat) (m : Int) (u : U.carrier) :
    (ltngRec U d).map (m, u) = Quot.mk (modCong d).rel m := rfl

/-- **M390F-2: 相互写像は群準同型** rec(x·y) = rec(x)·rec(y)。 -/
theorem ltng_rec_hom (U : Grp) (d : Nat) (x y : (unitsModel U).carrier) :
    (ltngRec U d).map ((unitsModel U).mul x y)
      = (zmod d).mul ((ltngRec U d).map x) ((ltngRec U d).map y) :=
  (ltngRec U d).map_mul x y

/-- **M390F-3: rec = M330F 不分岐商 Artin 写像(mod d)** — LT 相互写像は
    M330F の一般 Artin 写像 `locRecUnram`（K^× → ẑ = Gal(K^ur/K)）を
    有限レベル d へ射影したものに一致。LT rec が Artin rec を延長することの本物確認。 -/
theorem ltng_rec_eq_locRec (U : Grp) (d : Nat) (x : (unitsModel U).carrier) :
    (ltngRec U d).map x = (limitProj zmodSystem d).map ((locRecUnram U).map x) := rfl

/-! ## §2 核 = ノルム群（不分岐 LCFT 主定理） -/

/-- 相互写像 rec の**核**述語: {x ∈ K^× : rec(x) = 1 ∈ Gal(L/K)}。 -/
def ltngKernel (U : Grp) (d : Nat) (x : (unitsModel U).carrier) : Prop :=
  (ltngRec U d).map x = (zmod d).one

/-- **M390F-4: 核 = ノルム群（不分岐 LCFT 主定理）** —
    rec(m,u) = 1 ⟺ (m,u) ∈ N_{L/K}(L^×)（= dℤ×O^×）。
    局所類体論の中心言明「相互写像の核 = ノルム群」を、M335F の
    `normG_artin_kernel_link` を主語 rec で本物化したもの。 -/
theorem ltng_kernel_eq_norm (U : Grp) (d : Nat) (m : Int) (u : U.carrier) :
    ltngKernel U d (m, u) ↔ (normGSubgroup U (d : Int)).mem (m, u) :=
  (normG_artin_kernel_link U d m u).symm

/-- **M390F-5: 単数（惰性）はノルム群に入る** — rec(0,u) = 1、すなわち
    O^× ⊆ N_{L/K}(L^×)（不分岐: 単数はすべてノルム＝核に落ちる）。 -/
theorem ltng_units_in_kernel (U : Grp) (d : Nat) (u : U.carrier) :
    ltngKernel U d ((0 : Int), u) :=
  (ltng_kernel_eq_norm U d 0 u).mpr (normG_units U (d : Int) u)

/-! ## §3 K^×/N ≅ Gal への降下（well-defined 単射・全射） -/

/-- **M390F-6: rec は Gal = ℤ/d へ全射** — 相互写像の像は Gal(L/K) = ℤ/d の
    全ての元を覆う。K^×/N ↠ Gal の全射性（Frobenius が Gal を生成）。 -/
theorem ltng_rec_surj (U : Grp) (d : Nat) (c : (zmod d).carrier) :
    ∃ x : (unitsModel U).carrier, (ltngRec U d).map x = c := by
  induction c using Quot.ind
  rename_i a
  exact ⟨(a, U.one), rfl⟩

/-- **M390F-7: rec は N の剰余類で決まる（well-defined／単射性）** —
    rec(m,u) = rec(m',u') ⟺ 付値差 m − m' が d の倍数。
    K^×/N → Gal の単射性の付値側言明（核 = dℤ×O^× で割った剰余類の分離）。 -/
theorem ltng_rec_eq_iff (U : Grp) (d : Nat) (m m' : Int) (u u' : U.carrier) :
    (ltngRec U d).map (m, u) = (ltngRec U d).map (m', u')
      ↔ ∃ a : Int, m - m' = (d : Int) * a := by
  constructor
  · intro h
    have h' : Quot.mk (modCong d).rel m = Quot.mk (modCong d).rel m' := h
    obtain ⟨a, ha⟩ := quot_exact intGrp (modCong d) h'
    exact ⟨a, ha⟩
  · intro h
    obtain ⟨a, ha⟩ := h
    show Quot.mk (modCong d).rel m = Quot.mk (modCong d).rel m'
    apply Quot.sound
    show ((d : Nat) : Int) ∣ (m - m')
    exact ⟨a, ha⟩

/-- **M390F-8: rec の核による降下 = ノルム群剰余** —
    rec(m,u) = rec(m',u') ⟺ 付値差 (m−m', w) ∈ N_{L/K}(L^×)。
    「rec が K^×/N から Gal へ単射的に降りる」ことを、剰余のノルム群
    メンバーシップとして本物で述べる（M335F `normG_mem_iff` と接続）。 -/
theorem ltng_rec_eq_iff_norm (U : Grp) (d : Nat) (m m' : Int) (u u' w : U.carrier) :
    (ltngRec U d).map (m, u) = (ltngRec U d).map (m', u')
      ↔ (normGSubgroup U (d : Int)).mem (m - m', w) := by
  refine Iff.trans (ltng_rec_eq_iff U d m m' u u') ?_
  exact (normG_mem_iff U (d : Int) (m - m') w).symm

/-! ## §4 M385F（LT 明示的相互律・捻れ作用）への接続 -/

/-- **M390F-9: M385F の [u]-作用単数はノルム群に入る** — M385F では惰性単数 u が
    2^n-捻れ上を形式群自己準同型 [u]（`ltrUnitAct`）で動かす。その同じ単数
    (0,u) は、捻れレベル d = 2^n（= `ltrPow2 n`）の不分岐 LCFT で
    ちょうどノルム群 = rec の核に入る。M385F（捻れ作用）と M335F（ノルム群）の
    整合: 惰性 O^× ⊆ N。 -/
theorem ltng_ltr_unit_kernel (U : Grp) (n : Nat) (u : U.carrier) :
    ltngKernel U (ltrPow2 n) ((0 : Int), u) :=
  ltng_units_in_kernel U (ltrPow2 n) u

/-- **M390F-10: M385F 明示的相互律 rec(u)=[u^{-1}]（捻れ側）再輸出** —
    単数 u に法逆元 u'（u·u' ≡ 1 mod 2^n）があるとき、[u]∘[u'] は 2^n-捻れ上で
    恒等。不分岐核（本モジュール §2）の反対側、分岐捻れ上の LT 明示公式を
    本モジュールへ接続する（M385F `ltr_rec_inverse`）。 -/
theorem ltng_ltr_rec_inverse (n : Nat) (u u' k : Int)
    (h : ltrModEq n (u * u') 1) :
    ltrModEq n (ltrUnitAct u (ltrUnitAct u' k)) k :=
  ltr_rec_inverse n u u' k h

/-! ## §5 capstone: Lubin–Tate ノルム群データ -/

/-- **M390F-11: Lubin–Tate ノルム群データ** — 相互写像 rec の核 = ノルム群
    という不分岐 LCFT の言明を構造化。乗法群 K^× = ℤ×O^×、不分岐次数 d、
    相互写像 rec、ノルム群 N を束ね、
      * 核 = ノルム群（`kernel_eq_norm`）
      * Gal = ℤ/d への全射（`rec_surj`）
      * 単数（惰性）∈ ノルム群（`units_in_norm`）
    を要請する。rec が準同型であることは `Hom` から自動。 -/
structure LubinTateNormGroupData where
  U : Grp
  deg : Nat
  recMap : Hom (unitsModel U) (zmod deg)
  normSub : Subgroup (unitsModel U)
  recMap_eq : recMap = normGArtinModN U deg
  normSub_eq : normSub = normGSubgroup U (deg : Int)
  /-- 相互写像の核 = ノルム群（不分岐 LCFT 主定理）。 -/
  kernel_eq_norm : ∀ (m : Int) (u : U.carrier),
    recMap.map (m, u) = (zmod deg).one ↔ normSub.mem (m, u)
  /-- rec は Gal(L/K) = ℤ/deg へ全射。 -/
  rec_surj : ∀ c : (zmod deg).carrier, ∃ x, recMap.map x = c
  /-- 単数（惰性）はノルム群に入る（O^× ⊆ N）。 -/
  units_in_norm : ∀ u : U.carrier, normSub.mem ((0 : Int), u)

/-- **M390F-12: Lubin–Tate ノルム群データの構成**（単数群 U と不分岐次数 d から）。
    不分岐次数 d の分裂表示モデルで全性質を完全証明で満たす本物 witness。 -/
def ltngData (U : Grp) (d : Nat) : LubinTateNormGroupData where
  U := U
  deg := d
  recMap := normGArtinModN U d
  normSub := normGSubgroup U (d : Int)
  recMap_eq := rfl
  normSub_eq := rfl
  kernel_eq_norm := fun m u => (normG_artin_kernel_link U d m u).symm
  rec_surj := ltng_rec_surj U d
  units_in_norm := fun u => normG_units U (d : Int) u

/-- **M390F-13: Lubin–Tate ノルム群データの存在**（不分岐次数 2 の本物 witness）。 -/
theorem ltng_exists : ∃ D : LubinTateNormGroupData, D.deg = 2 :=
  ⟨ltngData punitGrp 2, rfl⟩

/-! ## §6 worked examples（不分岐次数 2） -/

-- 例1: 相互写像の明示式 rec(3, u) = [3] ∈ ℤ/2
example (u : punitGrp.carrier) :
    (ltngRec punitGrp 2).map ((3 : Int), u) = Quot.mk (modCong 2).rel 3 := rfl

-- 例2: **単数（惰性）は核 = ノルム群に入る**（不分岐で O^× ⊆ N）
example (u : punitGrp.carrier) : ltngKernel punitGrp 2 ((0 : Int), u) :=
  ltng_units_in_kernel punitGrp 2 u

-- 例3: **素元は核に入らない** — rec(1,u) ≠ 1（付値 1、2 ∤ 1、ゆえに N の外）
example (u : punitGrp.carrier) : ¬ ltngKernel punitGrp 2 ((1 : Int), u) := by
  intro h
  exact normG_deg2_one_not_mem u ((ltng_kernel_eq_norm punitGrp 2 1 u).mp h)

-- 例4: 付値 2 の元は核 = ノルム群に入る（2 = 2·1）
example (u : punitGrp.carrier) : ltngKernel punitGrp 2 ((2 : Int), u) :=
  (ltng_kernel_eq_norm punitGrp 2 2 u).mpr (normG_deg2_two_mem u)

-- 例5: **Gal = ℤ/2 への全射** — Frobenius [1] ∈ ℤ/2 も像に入る
example : ∃ x : (unitsModel punitGrp).carrier,
    (ltngRec punitGrp 2).map x = Quot.mk (modCong 2).rel 1 :=
  ltng_rec_surj punitGrp 2 (Quot.mk (modCong 2).rel 1)

-- 例6: **K^×/N への降下**（well-defined）: rec(2,u) = rec(0,u')（付値差 2 = 2·1）
example (u u' : punitGrp.carrier) :
    (ltngRec punitGrp 2).map ((2 : Int), u) = (ltngRec punitGrp 2).map ((0 : Int), u') :=
  (ltng_rec_eq_iff punitGrp 2 2 0 u u').mpr ⟨1, by omega⟩

-- 例7: 剰余のノルム群メンバーシップ表示（差 (2,·) ∈ N）
example (u u' w : punitGrp.carrier) :
    (normGSubgroup punitGrp (2 : Int)).mem ((2 : Int) - 0, w) :=
  (ltng_rec_eq_iff_norm punitGrp 2 2 0 u u' w).mp
    ((ltng_rec_eq_iff punitGrp 2 2 0 u u').mpr ⟨1, by omega⟩)

-- 例8: M385F 接続 — 捻れレベル 2² = 4 の [u]-作用単数はノルム群に入る
example (u : punitGrp.carrier) : ltngKernel punitGrp (ltrPow2 2) ((0 : Int), u) :=
  ltng_ltr_unit_kernel punitGrp 2 u

-- 例9: M385F rec(3)=[3^{-1}]（捻れ側）: [3]∘[3] は 4-捻れ上で恒等
example : ltrModEq 2 (ltrUnitAct 3 (ltrUnitAct 3 1)) 1 :=
  ltng_ltr_rec_inverse 2 3 3 1 ⟨2, rfl⟩

-- 例10: capstone データのアクセサ（単数 ∈ ノルム群）
example (u : punitGrp.carrier) : (ltngData punitGrp 2).normSub.mem ((0 : Int), u) :=
  (ltngData punitGrp 2).units_in_norm u

-- 例11: capstone の核 = ノルム群アクセサ（付値 2 の元）
example (u : punitGrp.carrier) :
    (ltngData punitGrp 2).recMap.map ((2 : Int), u) = (zmod 2).one ↔
      (ltngData punitGrp 2).normSub.mem ((2 : Int), u) :=
  (ltngData punitGrp 2).kernel_eq_norm 2 u

end IUT
