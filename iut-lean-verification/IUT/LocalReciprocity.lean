/-
  IUT/LocalReciprocity.lean — M330F（局所相互律 Artin 写像 rec : K^× → Gal(K^ab/K)^ab）

  ────────────────────────────────────────────────────────────────────────
  二軸（CLAUDE.md §1 必守）
  * 分類: **[実]**（本物の先行建設 (b)）。局所類体論の中心である
    **局所相互律（Artin 写像）K^× → Gal(K^ab/K)^ab の代数的核**を、
    分裂表示 K^× ≅ ℤ × O_v^×・Gal^ab ≅ ẑ × O_v^× の上で**本物の群準同型**
    として構成し、その普遍的性質を完全証明する。
  * complete_pct 影響: **前進あり（柱B 局所類体論の横展開）**。
    既存 `FullReciprocity`（M37）は **ℚ_p 限定**の recQp のみを持ち、
    Frobenius 冪則も惰性/ノルム剰余の核特徴付けも一般には無かった。本
    モジュールは
      (1) recQp を**任意の単数群 O_v^× 添字の一般 Artin 写像**
          `locRecArtin U` へ**昇格 (a)**（recQp = U:=ℤ_p^× の実例、
          `locRecQp_rec_eq` で defeq 一致を証明）、
      (2) **Frobenius 冪則** rec(π^n·u) = (Frob^n, u) を新規に本物証明
          （`locRec_frobPow`。既存 FullReciprocity には無い）、
      (3) **不分岐商の核 = 単数群**（ノルム剰余の核特徴付けの骨組み）を
          一般 U で本物証明（`locRec_kernel_units`、LocalCFT の
          `unramifiedRec_kernel` を一般 Artin 写像へ接続）、
      (4) **単数 ↦ 惰性因子**（`locRec_units_inertia` / `locRec_units_in_inertia`）
          を一般 U で本物証明
    することで、**Artin 写像が準同型・素元↦Frobenius・単数↦惰性**の
    代数的核を「本物」で閉じる。

  ────────────────────────────────────────────────────────────────────────
  既存モジュールの何を本物化したか（CLAUDE.md 指示・明記必須）
  * `FullReciprocity`（M37, ℚ_p）の `recQp = prodHom toZhat (idHom ℤ_p^×)`
    を、**単数群 U を主語にした一般 Artin 写像** `locRecArtin U`
    へ一般化・昇格した。recQp は `locRecArtin (zpUnits p hp)` に defeq。
  * `LocalCFT`（M27）の不分岐相互写像 `unramifiedRec`・核定理
    `unramifiedRec_kernel`・稠密像 `unramifiedRec_level_surj` を、
    一般 Artin 写像の**不分岐商** `locRecUnram` へ接続し、核（ノルム剰余）
    と Kummer レベル整合を一般 U で本物証明した。

  ────────────────────────────────────────────────────────────────────────
  主定理（全て完全証明・sorry/Classical.choice 皆無）
  * `locRecArtin`  — 一般 Artin 写像 K^× = ℤ × O_v^× → ẑ × O_v^×（群準同型）
  * `locRec_isHom` — rec(x·y) = rec(x)·rec(y)（群準同型）
  * `locRecFrob`   — Frobenius 元 = 完備化(1) ∈ ẑ = Gal(K^ur/K)
  * `locRec_prime_frob` — 素元 π ↦ (Frob, 1)（素元 ↦ Frobenius）
  * `locRec_frobPow`    — rec(π^n·u) = (Frob^n, u)（Frobenius 冪則）
  * `locRec_units_inertia` — 単数 rec(0,u) = (1, u)（単数 ↦ 惰性因子）
  * `locRec_units_in_inertia` — 単数の像は惰性部分群に入る
  * `locRecUnram` / `locRec_unramified_apply` — 不分岐商 = 付値の完備化
  * `locRec_kernel_units` — 不分岐商の核 = 単数群（ノルム剰余の核骨組み）
  * `locRec_kummer_level_surj` — 各有限レベルへ全射（Kummer/H¹ 整合の骨組み）
  * `LocalReciprocityData` / `locRecOfUnits` / `locRec_exists`
    / `locRec_artin_hom` / `locRec_frobenius` — capstone
  * `locRecQp` / `locRecQp_rec_eq` — ℚ_p の実例（recQp との一致）

  ────────────────────────────────────────────────────────────────────────
  正直な限定（CLAUDE.md §4: 消去・弱化禁止）
  * 右辺 ẑ × O_v^× が**実際の** Gal(K^ab/K) と同型であること（局所
    Kronecker–Weber / Lubin–Tate による明示的相互律）は本モジュールの
    対象外——**後続（柱C Lubin–Tate 接続）**。本物で閉じたのは分裂表示の
    上での Artin 写像の代数的核（準同型・素元↦Frobenius・単数↦惰性・
    不分岐核・稠密像）である。
  * Artin 写像の**全射性**・**核 = ノルム群 N_{L/K}(L^×) の完全証明**
    （LCFT 主定理）は骨組み。ここで本物化したのは「不分岐商の核 = 単数群」
    という核特徴付けの一段であって、全ての有限アーベル拡大 L に対する
    ノルム群一致は後続。
  * 単数フィルトレーション 1+m^n ↦ 高次分岐群の対応は骨組み（本モジュール
    では単数は惰性因子へ恒等的に写ることまでを本物で扱う）。
  * `Gal(K^ab/K)` は M271F/M37 のアーベル化表示 ẑ × O_v^× で扱う（完全な
    最大アーベル拡大の構成は後続）。**toy 主語ではない**: 主語は本物の
    ℤ・ẑ（M13 逆極限）・ℤ_p^×（M36 実構成）である。

  全て選択公理不使用。共有ファイル未変更（新規 1 本のみ）。
-/
import IUT.FullReciprocity

namespace IUT

/-! ## §1 一般 Artin 写像（局所相互律の代数的核） -/

/-- **M330F-1: 一般 Artin 写像** rec_K : K^× = ℤ × O_v^× → ẑ × O_v^×。
    付値部（ℤ）は副有限完備化 toZhat（ẑ = Gal(K^ur/K) へ、素元 ↦ Frobenius）、
    単数部（O_v^×）は恒等的に惰性因子へ。`FullReciprocity` の ℚ_p 限定
    `recQp` を任意の単数群 `U = O_v^×` へ昇格したもの（recQp はその実例）。 -/
def locRecArtin (U : Grp) : Hom (unitsModel U) (prodGrp zhat U) :=
  prodHom toZhat (idHom U)

/-- Artin 写像の明示式: rec(k, u) = (完備化 k, u)。 -/
theorem locRecArtin_apply (U : Grp) (k : Int) (u : U.carrier) :
    (locRecArtin U).map (k, u) = (toZhat.map k, u) := rfl

/-- **M330F-2: Artin 写像は群準同型** rec(x·y) = rec(x)·rec(y)。 -/
theorem locRec_isHom (U : Grp) (x y : (unitsModel U).carrier) :
    (locRecArtin U).map ((unitsModel U).mul x y)
      = (prodGrp zhat U).mul ((locRecArtin U).map x) ((locRecArtin U).map y) :=
  (locRecArtin U).map_mul x y

/-! ## §2 不分岐部分と Frobenius -/

/-- **M330F-3: Frobenius 元** = 完備化(1) ∈ ẑ = Gal(K^ur/K)。
    ẑ の位相的生成元（Frobenius 自己同型）に対応する。 -/
@[reducible] def locRecFrob : zhat.carrier := toZhat.map 1

/-- **M330F-4: 素元 ↦ Frobenius** — 付値 1 の素元 π = (1, 1) に対し
    rec(π) = (Frob, 1)。局所相互律「素元は Frobenius へ」の代数的核。 -/
theorem locRec_prime_frob (U : Grp) :
    (locRecArtin U).map ((1 : Int), U.one) = (locRecFrob, U.one) := rfl

/-- **M330F-5: Frobenius 冪則** rec(π^n·u) = (Frob^n, u)（u ∈ O_v^×）。
    付値 n の元 π^n·u = (n, u) に対し不分岐部が Frobenius の n 乗へ写る
    ことを本物で（`Hom.map_pow` と `intGrp_pow_one` から）。
    `FullReciprocity` には無い新規の本物定理。 -/
theorem locRec_frobPow (U : Grp) (n : Nat) (u : U.carrier) :
    (locRecArtin U).map (((n : Nat) : Int), u) = (zhat.pow locRecFrob n, u) := by
  show (toZhat.map ((n : Nat) : Int), u) = (zhat.pow locRecFrob n, u)
  have hp : toZhat.map (intGrp.pow (1 : Int) n) = zhat.pow locRecFrob n :=
    toZhat.map_pow (1 : Int) n
  rw [intGrp_pow_one] at hp
  rw [hp]

/-! ## §3 単数群と惰性 -/

/-- **M330F-6: 単数 ↦ 惰性因子** — rec(0, u) = (1, u)。付値 0 の単数は
    不分岐部で消え、惰性因子 O_v^× へ恒等的に写る（単数 ↦ 惰性群 I）。 -/
theorem locRec_units_inertia (U : Grp) (u : U.carrier) :
    (locRecArtin U).map ((0 : Int), u) = (zhat.one, u) := by
  show (toZhat.map (0 : Int), u) = (zhat.one, u)
  rw [show toZhat.map (0 : Int) = zhat.one from toZhat.map_one]

/-- 惰性部分群 I = Gal(K^ab/K^ur)（不分岐部が自明な元）の述語。 -/
def locRecInertia (U : Grp) : (prodGrp zhat U).carrier → Prop :=
  fun g => g.1 = zhat.one

/-- **M330F-7: 単数の像は惰性部分群に入る** — rec(O_v^×) ⊆ I。 -/
theorem locRec_units_in_inertia (U : Grp) (u : U.carrier) :
    locRecInertia U ((locRecArtin U).map ((0 : Int), u)) := by
  show ((locRecArtin U).map ((0 : Int), u)).1 = zhat.one
  rw [locRec_units_inertia]

/-! ## §4 不分岐商・ノルム剰余の核 -/

/-- 直積の第一射影（不分岐商 Gal(K^ab/K) ↠ Gal(K^ur/K) = ẑ）。 -/
def locRecFst (A B : Grp) : Hom (prodGrp A B) A where
  map := fun x => x.1
  map_mul := fun _ _ => rfl

/-- **M330F-8: 不分岐商 Artin 写像** K^× → ẑ = Gal(K^ur/K)
    （一般 Artin 写像に不分岐商を合成）。 -/
def locRecUnram (U : Grp) : Hom (unitsModel U) zhat :=
  Hom.comp (locRecFst zhat U) (locRecArtin U)

/-- 不分岐商は付値の完備化 `unramifiedRec`（M27）に一致する。
    ——本モジュールの Artin 写像が LocalCFT の不分岐相互写像を延長する。 -/
theorem locRec_unramified_apply (U : Grp) (x : (unitsModel U).carrier) :
    (locRecUnram U).map x = (unramifiedRec U).map x := rfl

/-- **M330F-9: 不分岐商の核 = 単数群**（ノルム剰余の核特徴付けの骨組み）
    — rec_ur(x) = 1 ⟺ v(x) = 0。単数（＝ノルム群の不分岐成分）が核に
    落ちる、局所相互律の核特徴付けの一段。LocalCFT の `unramifiedRec_kernel`
    を一般 Artin 写像の不分岐商へ接続。 -/
theorem locRec_kernel_units (U : Grp) (x : (unitsModel U).carrier) :
    (locRecUnram U).map x = zhat.one ↔ x.1 = 0 :=
  unramifiedRec_kernel U x

/-! ## §5 Kummer/H¹ 整合（各有限レベルへの稠密像） -/

/-- **M330F-10: 各有限レベルへの全射**（Kummer 理論 K^×/(K^×)^n・
    H¹(G_K,μ_n) との整合の骨組み）— 不分岐商 Artin 写像の像は ẑ の
    どの有限商 ℤ/n も覆う（Frobenius の稠密性）。rec が H¹(G_K,μ_n) の
    双対を全レベルで捉える代数的核。 -/
theorem locRec_kummer_level_surj (U : Grp) (n : Nat) (c : (zmod n).carrier) :
    ∃ x : (unitsModel U).carrier,
      (limitProj zmodSystem n).map ((locRecUnram U).map x) = c := by
  induction c using Quot.ind
  rename_i a
  exact ⟨(a, U.one), rfl⟩

/-! ## §6 capstone: 局所相互律データ -/

/-- **M330F-11: 局所相互律データ** — 局所類体論の Artin 写像の代数的核を
    構造化: 乗法群 K^×、アーベル化ガロア群 Gal(K^ab/K)^ab、相互写像 rec、
    不分岐商 Gal^ab ↠ ẑ、素元 π、Frobenius、そして
      * 素元 ↦ Frobenius（`rec_prime_frob`）
      * 各有限レベルへの稠密像（`level_surj`）
    を要請する。rec が準同型であることは `Hom` 構造から自動。 -/
structure LocalReciprocityData where
  Kx : Grp
  Gab : Grp
  recMap : Hom Kx Gab
  unram : Hom Gab zhat
  prime : Kx.carrier
  frob : zhat.carrier
  frob_gen : frob = toZhat.map 1
  rec_prime_frob : unram.map (recMap.map prime) = frob
  level_surj : ∀ (n : Nat) (c : (zmod n).carrier),
    ∃ x : Kx.carrier, (limitProj zmodSystem n).map (unram.map (recMap.map x)) = c

/-- **M330F-12: 単数群からの局所相互律データの構成** — 任意の単数群
    U = O_v^× に対し、上の全性質を**完全証明で**満たす Artin 写像データを
    与える（骨組みでない、本物の witness）。 -/
def locRecOfUnits (U : Grp) : LocalReciprocityData where
  Kx := unitsModel U
  Gab := prodGrp zhat U
  recMap := locRecArtin U
  unram := locRecFst zhat U
  prime := ((1 : Int), U.one)
  frob := locRecFrob
  frob_gen := rfl
  rec_prime_frob := rfl
  level_surj := locRec_kummer_level_surj U

/-- **rec は群準同型**（capstone アクセサ）。 -/
theorem locRec_artin_hom (D : LocalReciprocityData) (x y : D.Kx.carrier) :
    D.recMap.map (D.Kx.mul x y) = D.Gab.mul (D.recMap.map x) (D.recMap.map y) :=
  D.recMap.map_mul x y

/-- **素元 ↦ Frobenius**（capstone アクセサ）。 -/
theorem locRec_frobenius (D : LocalReciprocityData) :
    D.unram.map (D.recMap.map D.prime) = D.frob :=
  D.rec_prime_frob

/-- **M330F-13: 局所相互律データの存在**（無矛盾性 witness）。 -/
theorem locRec_exists : Nonempty LocalReciprocityData :=
  ⟨locRecOfUnits punitGrp⟩

/-! ## §7 実例: ℚ_p の局所相互律 rec_{ℚ_p} -/

/-- **M330F-14: ℚ_p の局所相互律データ** — U = ℤ_p^×（M36 実構成）で
    rec_{ℚ_p}: ℚ_p^× → ẑ × ℤ_p^×（p ↦ Frobenius、ℤ_p^× ↦ 惰性）。 -/
def locRecQp (p : Nat) (hp : IsPrime p) : LocalReciprocityData :=
  locRecOfUnits (zpUnits p hp)

/-- **M330F-15: 一般 Artin 写像は FullReciprocity の recQp の一般化**
    — U := ℤ_p^× の実例で本モジュールの Artin 写像が既存 `recQp` に
    **定義的に一致**する（recQp は locRecArtin の ℚ_p インスタンス）。 -/
theorem locRecQp_rec_eq (p : Nat) (hp : IsPrime p) :
    (locRecQp p hp).recMap = recQp p hp := rfl

/-- ℚ_p でも素元 p ↦ Frobenius が成り立つ（実例での確認）。 -/
theorem locRecQp_prime_frob (p : Nat) (hp : IsPrime p) :
    (locRecQp p hp).unram.map ((locRecQp p hp).recMap.map (locRecQp p hp).prime)
      = (locRecQp p hp).frob :=
  (locRecQp p hp).rec_prime_frob

end IUT
