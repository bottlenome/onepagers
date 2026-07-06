/-
  IUT/NormGroup.lean — M335F [実／本物]
  分類: 実 (ノルム写像 N_{L/K}: L^×→K^× とノルム群 N_{L/K}(L^×)⊆K^×)
  complete_pct 影響: 柱B を前進（M330F が残した「核=ノルム群の LCFT 主定理」へ向け、
    ノルム写像を本物の群準同型として建設・ノルム群を M267F 部分群で構成・Artin 核との接続）。
  正直な限定: ker(Artin)=N_{L/K}(L^×) の完全証明は、**不分岐次数 d の分裂表示モデル
    K^×=ℤ×O^×・L^×=ℤ×O^× 上で本物に閉じた**（`normG_artin_kernel_link`：
    Artin 写像を ℤ/d へ落とした核 = ノルム群 dℤ×O^× を完全証明）。一般の
    （分岐を含む任意の有限アーベル拡大・実 Gal(L/K) を主語にした）LCFT 主定理は
    後続（本モジュールでは一般命題を仮説束 `NormGReciprocity` として明示し、
    不分岐次数 d の実例でそれを**構成的に充足**する）。

  ────────────────────────────────────────────────────────────────────────
  既存モジュールの何を本物化したか
  * `LocalReciprocity`（M330F）が「核 = ノルム群 N_{L/K}(L^×) の完全証明」を
    骨組みとして残した。本モジュールは
      (1) ノルム写像 N_{L/K}: L^×→K^× を**本物の群準同型**として建設
          （`normGMap`＝分裂表示の付値部を ×d・単数部を恒等）、
      (2) ノルム群 N_{L/K}(L^×) を M267F `imSubgroup` で**本物の部分群**として構成
          （`normGSubgroup`）、
      (3) 不分岐次数 d の指数 = d（`normG_unramified`：像の付値は d の倍数）
          と単数群全体を含むこと（`normG_units`：N は単数へ全射）を本物証明、
      (4) M330F の不分岐商 Artin 写像 `locRecUnram` を ℤ/d へ落とし、
          その核 = ノルム群であることを**完全証明で接続**（`normG_artin_kernel_link`）。
    これにより M330F の残した「核 = ノルム群」骨組みの**不分岐一段が本物に**なる。

  ────────────────────────────────────────────────────────────────────────
  主定理（全て完全証明・sorry/新規 Classical.choice 皆無）
  * `normGScaleHom`      — 付値スケール準同型 ×n : ℤ→ℤ（群準同型）
  * `normGMap`           — ノルム写像 N_{L/K}: L^×=ℤ×O^× → K^×=ℤ×O^×
  * `normG_isHom`        — N(x·y)=N(x)·N(y)（群準同型）
  * `normGSubgroup`      — ノルム群 N_{L/K}(L^×)（M267F 像部分群）
  * `normG_mem_iff`      — (m,u)∈N ⟺ ∃a, m=n·a（ノルム群の完全特徴付け）
  * `normG_units`        — 単数 (0,u)∈N（不分岐: N は単数へ全射）
  * `normG_unramified`   — N の像の付値は d の倍数（指数 = d の一段）
  * `normGArtinModN`     — Artin 写像 ↠ ℤ/d（M330F `locRecUnram` に接続）
  * `normG_artin_kernel_link` — **ker(Artin mod d) = ノルム群**（不分岐 LCFT 主定理）
  * `NormGReciprocity` / `normGReciprocityUnram` — 相互律の仮説束と不分岐実例
  * `NormGroupData` / `normGroupDataOf` / `normG_exists` — capstone

  正直な限定（CLAUDE.md §4: 消去・弱化禁止）
  * 一般の（分岐を含む）有限アーベル拡大 L/K に対する LCFT 主定理
    ker(rec_K) = N_{L/K}(L^×)、および右辺の**実 Gal(L/K)** による意味づけは
    本モジュールの対象外（後続）。本物で閉じたのは**不分岐次数 d の分裂表示
    モデル**上でのノルム群の構成・特徴付けと、Artin(mod d) の核 = ノルム群である。
  * 単数部の実体は M330F と同じく抽象単数群 U = O^×（ℤ_p^× 等の実構成を差せる）。
    N の単数への作用は「恒等（全射像）」で不分岐性を忠実に写しているが、
    局所ノルム剰余記号のフィルトレーション対応は骨組み（後続）。

  全て選択公理不使用（propext/Quot.sound のみ）。共有ファイル未変更（新規 1 本）。
-/
import IUT.LocalReciprocity
import IUT.QuotientGroup

namespace IUT

/-! ## §1 付値スケール準同型 -/

/-- **M335F-1: 付値スケール準同型** ×n : ℤ→ℤ。不分岐次数 n の拡大で
    ノルム写像が付値を n 倍にする（v_K(N x) = f·v_L(x)、不分岐 f=n）
    ことの代数的核。(ℤ,+) 上で x ↦ n·x は群準同型（分配則）。 -/
def normGScaleHom (n : Int) : Hom intGrp intGrp where
  map := fun x => n * x
  map_mul := fun a b => by
    show n * (a + b) = n * a + n * b
    exact Int.mul_add n a b

/-- スケール準同型の明示式。 -/
theorem normGScaleHom_apply (n x : Int) : (normGScaleHom n).map x = n * x := rfl

/-! ## §2 ノルム写像 N_{L/K}: L^× → K^× -/

/-- **M335F-2: ノルム写像** N_{L/K}: L^× = ℤ×O^× → K^× = ℤ×O^×。
    不分岐次数 n の拡大の分裂表示上で、付値部を ×n（付値 ↦ n·付値）、
    単数部を恒等（不分岐では N: O_L^× ↠ O_K^× が全射）。M330F の
    `unitsModel U` を主語にした**本物の群準同型**。 -/
def normGMap (U : Grp) (n : Int) : Hom (unitsModel U) (unitsModel U) :=
  prodHom (normGScaleHom n) (idHom U)

/-- ノルム写像の明示式: N(m, u) = (n·m, u)。 -/
theorem normGMap_apply (U : Grp) (n : Int) (m : Int) (u : U.carrier) :
    (normGMap U n).map (m, u) = (n * m, u) := rfl

/-- **M335F-3: ノルム写像は群準同型** N(x·y) = N(x)·N(y)。 -/
theorem normG_isHom (U : Grp) (n : Int) (x y : (unitsModel U).carrier) :
    (normGMap U n).map ((unitsModel U).mul x y)
      = (unitsModel U).mul ((normGMap U n).map x) ((normGMap U n).map y) :=
  (normGMap U n).map_mul x y

/-! ## §3 ノルム群 N_{L/K}(L^×) ⊆ K^× -/

/-- **M335F-4: ノルム群** N_{L/K}(L^×) = im(N_{L/K})。M267F `imSubgroup` に
    より、ノルム写像の像が K^× の**本物の部分群**をなす。 -/
def normGSubgroup (U : Grp) (n : Int) : Subgroup (unitsModel U) :=
  imSubgroup (normGMap U n)

/-- **M335F-5: ノルム群の完全特徴付け** (m,u) ∈ N_{L/K}(L^×) ⟺ ∃a, m = n·a。
    すなわちノルム群 = nℤ × O^×（付値部が n の倍数・単数部は全体）。 -/
theorem normG_mem_iff (U : Grp) (n : Int) (m : Int) (u : U.carrier) :
    (normGSubgroup U n).mem (m, u) ↔ ∃ a : Int, m = n * a := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := h
    refine ⟨w.1, ?_⟩
    have hfst : n * w.1 = m := congrArg Prod.fst hw
    exact hfst.symm
  · intro h
    obtain ⟨a, ha⟩ := h
    refine ⟨(a, u), ?_⟩
    show ((n * a : Int), u) = (m, u)
    rw [ha]

/-- **M335F-6: 単数はノルム群に入る**（不分岐: N は O_K^× へ全射）—
    任意の単数 (0,u)（付値 0）はあるノルムに等しい。ノルム群 ⊇ O_K^×。 -/
theorem normG_units (U : Grp) (n : Int) (u : U.carrier) :
    (normGSubgroup U n).mem ((0 : Int), u) :=
  (normG_mem_iff U n 0 u).mpr ⟨0, (Int.mul_zero n).symm⟩

/-- **M335F-7: 不分岐次数 d の指数構造** — ノルム群の元の付値は d の倍数。
    [K^× : N_{L/K}(L^×)] = d = [L:K]（不分岐）の付値側の一段。 -/
theorem normG_unramified (U : Grp) (n : Int) (g : (unitsModel U).carrier)
    (hg : (normGSubgroup U n).mem g) : ∃ a : Int, g.1 = n * a := by
  obtain ⟨w, hw⟩ := hg
  exact ⟨w.1, (congrArg Prod.fst hw).symm⟩

/-! ## §4 Artin 核との接続（不分岐 LCFT 主定理） -/

/-- **M335F-8: Artin 写像 ↠ ℤ/d** — M330F の不分岐商 Artin 写像
    `locRecUnram : K^× → ẑ` を有限次数 d の商 ℤ/d = Gal(L/K) へ落とす。
    (m,u) ↦ (m mod d)。 -/
def normGArtinModN (U : Grp) (d : Nat) : Hom (unitsModel U) (zmod d) :=
  Hom.comp (limitProj zmodSystem d) (locRecUnram U)

/-- Artin(mod d) の明示式: (m,u) ↦ [m] ∈ ℤ/d。 -/
theorem normGArtinModN_apply (U : Grp) (d : Nat) (m : Int) (u : U.carrier) :
    (normGArtinModN U d).map (m, u) = Quot.mk (modCong d).rel m := rfl

/-- **M335F-9: 不分岐 LCFT 主定理（核 = ノルム群）** —
    不分岐次数 d の分裂表示モデルで、Artin 写像を Gal(L/K)=ℤ/d へ
    落とした核がちょうどノルム群 N_{L/K}(L^×) に一致する:
      Artin_d(m,u) = 1 ⟺ (m,u) ∈ N_{L/K}(L^×) (= dℤ×O^×)。
    M330F が残した「核 = ノルム群」骨組みの**不分岐一段を本物で閉じた**もの。 -/
theorem normG_artin_kernel_link (U : Grp) (d : Nat) (m : Int) (u : U.carrier) :
    (normGSubgroup U (d : Int)).mem (m, u)
      ↔ (normGArtinModN U d).map (m, u) = (zmod d).one := by
  rw [normG_mem_iff U (d : Int) m u, normGArtinModN_apply]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h
    show Quot.mk (modCong d).rel m = Quot.mk (modCong d).rel (0 : Int)
    apply Quot.sound
    show ((d : Nat) : Int) ∣ (m - 0)
    exact ⟨a, by rw [ha]; omega⟩
  · intro h
    have h' : Quot.mk (modCong d).rel m = Quot.mk (modCong d).rel (0 : Int) := h
    have hrel := quot_exact intGrp (modCong d) h'
    obtain ⟨a, ha⟩ := hrel
    refine ⟨a, ?_⟩
    rw [← ha]; omega

/-! ## §5 相互律の仮説束と不分岐実例 -/

/-- **M335F-10: 局所ノルム相互律データ**（仮説束）— ある Artin 型準同型
    `artin : K^× → A`（A = 有限アーベル商 Gal(L/K)）の核が**ちょうど
    ノルム群** N_{L/K}(L^×) に一致する、という LCFT 主定理の言明。
    一般の分岐拡大では外部入力（後続）だが、不分岐次数 d では下で構成的に充足する。 -/
structure NormGReciprocity (U : Grp) (n : Int) where
  A : Grp
  artin : Hom (unitsModel U) A
  ker_eq_norm : ∀ x : (unitsModel U).carrier,
    artin.map x = A.one ↔ (normGSubgroup U n).mem x

/-- **M335F-11: 不分岐次数 d の相互律の構成的充足** — A = ℤ/d、
    artin = `normGArtinModN`、核 = ノルム群を `normG_artin_kernel_link` で
    本物証明。仮説束 `NormGReciprocity` を**不分岐一段で実際に inhabit** する。 -/
def normGReciprocityUnram (U : Grp) (d : Nat) : NormGReciprocity U (d : Int) where
  A := zmod d
  artin := normGArtinModN U d
  ker_eq_norm := fun x => (normG_artin_kernel_link U d x.1 x.2).symm

/-! ## §6 capstone -/

/-- **M335F-12: ノルム群データ** — 乗法群 K^×＝L^×（分裂表示）、拡大次数、
    ノルム写像、ノルム群を構造化。 -/
structure NormGroupData where
  U : Grp
  deg : Int
  normMap : Hom (unitsModel U) (unitsModel U)
  normSub : Subgroup (unitsModel U)
  normMap_eq : normMap = normGMap U deg
  normSub_eq : normSub = normGSubgroup U deg

/-- **M335F-13: ノルム群データの構成**（単数群 U と次数 n から）。 -/
def normGroupDataOf (U : Grp) (n : Int) : NormGroupData where
  U := U
  deg := n
  normMap := normGMap U n
  normSub := normGSubgroup U n
  normMap_eq := rfl
  normSub_eq := rfl

/-- **M335F-14: ノルム群データの存在**（無矛盾性 witness）。 -/
theorem normG_exists : Nonempty NormGroupData :=
  ⟨normGroupDataOf punitGrp 2⟩

/-! ## §7 実例: 次数 2 の不分岐モデル -/

/-- **M335F-15: 次数 2 の不分岐実例** — ノルム群 = 2ℤ×O^×、
    Artin(mod 2) の核 = ノルム群を実例で確認。 -/
def normGReciprocityDeg2 : NormGReciprocity punitGrp (2 : Int) :=
  normGReciprocityUnram punitGrp 2

/-- 実例: 付値 2 の元 (2, u) はノルム群に入る（2 = 2·1）。 -/
theorem normG_deg2_two_mem (u : punitGrp.carrier) :
    (normGSubgroup punitGrp (2 : Int)).mem ((2 : Int), u) :=
  (normG_mem_iff punitGrp 2 2 u).mpr ⟨1, by omega⟩

/-- 実例: 付値 1 の素元 (1, u) はノルム群に**入らない**（2 ∤ 1）。 -/
theorem normG_deg2_one_not_mem (u : punitGrp.carrier) :
    ¬ (normGSubgroup punitGrp (2 : Int)).mem ((1 : Int), u) := by
  intro h
  obtain ⟨a, ha⟩ := (normG_mem_iff punitGrp 2 1 u).mp h
  omega

end IUT
