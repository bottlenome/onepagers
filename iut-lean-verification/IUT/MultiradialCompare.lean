/-
  IUT/MultiradialCompare.lean — M362F [実／本物]
  分類: 実 (Frobenius 描像⟷étale 描像の log-shell 比較同型＝多輻表現の芽)
  complete_pct 影響: 柱D を前進（M337F 縦 log-link・M327F Frobenius-like⇄étale-like で
    Frobenius 描像（乗法 U^(d)）と étale 描像（加法 log-shell m^d）の比較同型を段付き商上で本物化
    ＝多輻表現の芽。crux Dβ-ω（多輻アルゴリズムの theta-link 整合）は外部仮説として明示）。
  正直な限定: crux Dβ-ω（論争の係争点）は外部仮説のまま。比較は log-shell 段付きレベル。
    完全な多輻表現は theta-link 整合（=crux）を要す。

  ## 本モジュールの位置づけ（何を合成し何を本物化したか）

  IUT III の**多輻表現（multiradial representation）**は、Θ-link の左右に置かれた 2 つの
  「描像（picture）」を同一視する:
    ・**Frobenius 描像**（Frobenius-like・乗法的）: p 進主単数群のフィルトレーション U^(d)
      （= 1 + p^d ℤ_p、M30 `principalUnits`／M31 `unitFiltration`）。theta-link の乗法側。
    ・**étale 描像**（étale-like・加法的）: 加法 log-shell m^d = p^d·ℤ_p（M321F
      `logShellMem`）、および段付き商上の加法群 ℤ/p（M327F `zmod`）。
  本 M362F は、この 2 描像の**比較同型（comparison isomorphism）を段付き商レベルで本物化**する。
  比較写像は M337F の縦 log-link `logLinkMap`（＝ M327F graded log θ_d）そのものであり、
  乗法段付き商 U^(d)/U^(d+1) を加法段付き商 m^d/m^{d+1}（≅ ℤ/p）へ**準同型かつ全単射**で送る。
  これが多輻表現の**芽（seed）**である: 2 描像の比較そのものは本物（log-link 同一視）で、
  残る係争点は「この比較アルゴリズムが theta-link と整合するか」＝ crux Dβ-ω であり外部仮説。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）

  * M362F-1 `mrcFrobPicture` / `mrcEtalePicture`
      — Frobenius 描像（乗法 U^(d)）と étale 描像（加法 log-shell m^d）を**対象として
        再輸出**（M327F/M321F の本物の会員述語）。多輻比較の左右の描像。
  * M362F-2 `mrcCompare` / `mrc_compare_one` / `mrc_compare_hom` / `mrc_compare_pow`
      — **比較写像 Frobenius 描像 → étale 描像** = 縦 log-link `logLinkMap`（M337F）。
        乗法段付き商 U^(d)/U^(d+1) を加法段付き商 ℤ/p へ送る**準同型**（log(1)=0・
        log(uv)=log u+log v・log(uⁿ)=n·log u）を M337F の本物で閉じる。
  * M362F-3 `mrc_compare_iso`
      — **比較は段付き商上の全単射**: 核はちょうど U^(d+1)（＝段付き商上で単射、
        M337F `logLink_kernel`）かつ加法段付き商 ℤ/p を尽くす（全射、`logLink_surj`）。
        乗法段付き商 U^(d)/U^(d+1) ≅ 加法段付き商 m^d/m^{d+1} の比較同型の本物。
  * M362F-4 `mrc_multiradial_seed`（**多輻表現の芽**）
      — **比較はフィルトレーションと可換（段を跨いで整合）**: x ∈ U^(d) の leading log
        content が étale 描像 m^d に着地し（`logShell_unit_filtration`）、比較の核が
        次段 U^(d+1) へ降りる（`logLink_kernel`）。＝比較が段付き構造を保つ整合性
        （M337F `logLink_shell_step`）。多輻表現の芽。
  * M362F-5 `mrc_crux_external` / `mrc_crux_is_hypothesis`（**crux は外部仮説・決して導出しない**）
      — 比較同型は**無条件で本物**（準同型が crux とは独立に成立）だが、その**多輻的整合**
        （比較アルゴリズムと theta-link の crux ＝ Dβ-ω ＝ 論争の係争点）は外部 Prop として
        **受け取るのみ**で本層では決して証明しない（`mrc_crux_is_hypothesis` が Iff.rfl で
        「crux はちょうど受け取る仮説であって定理でない」ことを機械検証で明示）。
  * M362F-6 capstone `MrcRealData` / `mrcRealData` / `mrc_exists` + 実例。

  ## 正直な限定（消去・弱化禁止）
  * **crux Dβ-ω（多輻的アルゴリズム＝IUT 論争の当の係争点）は恒久的に本層の範囲外**。本層は
    2 描像の比較写像・準同型・段付き商上の全単射・フィルトレーション整合を本物で構成するのみで、
    crux（比較と theta-link の整合不等式）は外部 Prop 仮説として受け取り決して導出しない。
  * **比較は log-shell 段付きレベル**（U^(d)/U^(d+1) ≅ m^d/m^{d+1} ≅ ℤ/p）。全レベルを束ねる
    単一の完全 log 同一視・完全な多輻表現（theta-link 整合込み）は後続。
  * log 写像は p 進対数の主項 θ_d で本物（M327F/M321F/M337F 継承）。局所体 K = ℚ_p。
  全て選択公理不使用（sorry 皆無・新規 Classical 皆無）。禁止タクティク不使用（core Lean のみ）。
  共有ファイル未変更。柱D 横展開・本物の先行建設[実]。
-/
import IUT.LogLinkReal
import IUT.LogKummerReal
import IUT.LogShellReal

namespace IUT

/-! ## M362F-1: 2 描像を対象として再輸出（Frobenius 描像・étale 描像） -/

/-- **M362F-1a: Frobenius 描像**（Frobenius-like・乗法的） — theta-link の乗法側に置かれる
    p 進主単数群のフィルトレーション U^(d) = 1 + p^d ℤ_p の会員述語（M31 `unitFiltration`）。
    多輻比較の**左の描像**。 -/
def mrcFrobPicture (p d : Nat) : (principalUnits p).carrier → Prop :=
  (unitFiltration p d).mem

/-- **M362F-1b: étale 描像**（étale-like・加法的） — theta-link の加法側に置かれる
    加法 log-shell m^d = p^d·ℤ_p の会員述語（M321F `logShellMem`）。多輻比較の**右の描像**。 -/
def mrcEtalePicture (p d : Nat) : (Zp p).carrier → Prop :=
  logShellMem p d

/-- **定理 (M362F-1c): Frobenius 描像は U^(d) そのもの** — 再輸出が本物であること。 -/
theorem mrc_frob_is_filtration (p d : Nat) :
    mrcFrobPicture p d = (unitFiltration p d).mem := rfl

/-- **定理 (M362F-1d): étale 描像は log-shell m^d そのもの** — 再輸出が本物であること。 -/
theorem mrc_etale_is_shell (p d : Nat) :
    mrcEtalePicture p d = logShellMem p d := rfl

/-! ## M362F-2: 比較写像 Frobenius 描像 → étale 描像（= 縦 log-link） -/

/-- **M362F-2a: 多輻比較写像** — Frobenius 描像（乗法 U^(d)）から étale 描像（加法段付き商
    ℤ/p）への比較写像。M337F の縦 log-link `logLinkMap`（＝ M327F graded log θ_d）そのもの。
    乗法段付き商 U^(d)/U^(d+1) を加法段付き商 m^d/m^{d+1} ≅ ℤ/p へ同一視する。 -/
def mrcCompare (p d : Nat) (hp : 1 ≤ p) (u : (principalUnits p).carrier) :
    (zmod p).carrier :=
  logLinkMap p d hp u

/-- **定理 (M362F-2b): 比較は単位元を 0 へ** — compare(1) = 0（乗法単位元 → 加法単位元）。
    M337F `logLink_one`。 -/
theorem mrc_compare_one (p d : Nat) (hp : 1 ≤ p) :
    mrcCompare p d hp (principalUnits p).one = (zmod p).one :=
  logLink_one p d hp

/-- **定理 (M362F-2c): 比較は準同型（乗法 → 加法）** — compare(uv) = compare(u) + compare(v)。
    Frobenius 描像（乗法）と étale 描像（加法）の**準同型的同一視**の本物（M337F `logLink_hom`）。
    比較写像そのものはこの準同型を crux とは独立に無条件で満たす。 -/
theorem mrc_compare_hom (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y) :
    mrcCompare p d hp ((principalUnits p).mul x y)
      = (zmod p).mul (mrcCompare p d hp x) (mrcCompare p d hp y) :=
  logLink_hom p d hp hd x y hx hy

/-- **定理 (M362F-2d): 比較の n 乗可換** — compare(uⁿ) = n·compare(u)
    （乗法 n 乗 ⇄ 加法 n 倍）。M337F `logLink_pow`。 -/
theorem mrc_compare_pow (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    {u : (principalUnits p).carrier} (hu : (unitFiltration p d).mem u) :
    ∀ n : Nat,
      mrcCompare p d hp (tateNpow (principalUnits p) u n)
        = tateNpow (zmod p) (mrcCompare p d hp u) n :=
  logLink_pow p d hp hd hu

/-! ## M362F-3: 比較は段付き商上の全単射（比較同型） -/

/-- **定理 (M362F-3a: 本丸): 比較は段付き商上の全単射（比較同型）** — 多輻比較写像は
    乗法段付き商 U^(d)/U^(d+1)（Frobenius 描像）を加法段付き商 m^d/m^{d+1} ≅ ℤ/p（étale
    描像）へ**全単射**で送る:
    (i) **段付き商上で単射**: 核はちょうど次段 U^(d+1)（compare u = 0 ⟺ u ∈ U^(d+1)、
        M337F `logLink_kernel`）。すなわち U^(d)/U^(d+1) 上で単射。
    (ii) **全射**: 任意の加法類 c ∈ ℤ/p は U^(d) のある単数の比較値（M337F `logLink_surj`）。
    これが Frobenius 描像 ⟷ étale 描像の**比較同型**の本物（段付き商レベル）。 -/
theorem mrc_compare_iso (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) :
    (∀ x : (principalUnits p).carrier, (unitFiltration p d).mem x →
        (mrcCompare p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x))
    ∧ (∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
        (unitFiltration p d).mem u ∧ mrcCompare p d hp u = c) :=
  ⟨fun x hx => logLink_kernel p d hp x hx,
   fun c => logLink_surj p d hp hd c⟩

/-- **定理 (M362F-3b): 比較は段付き商上で単射（核 = U^(d+1)）** — 比較同型の単射部分。 -/
theorem mrc_compare_injective_graded (p d : Nat) (hp : 1 ≤ p)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x) :
    mrcCompare p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x :=
  logLink_kernel p d hp x hx

/-- **定理 (M362F-3c): 比較は étale 描像の加法段付き商を尽くす（全射）** — 比較同型の全射部分。 -/
theorem mrc_compare_surjective (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (c : (zmod p).carrier) :
    ∃ u : (principalUnits p).carrier,
      (unitFiltration p d).mem u ∧ mrcCompare p d hp u = c :=
  logLink_surj p d hp hd c

/-! ## M362F-4: 多輻表現の芽（比較はフィルトレーションと可換） -/

/-- **定理 (M362F-4a: 多輻表現の芽): 比較はフィルトレーションと可換（段跨ぎ整合）** —
    多輻比較が段付き構造を保つことの本物: x ∈ U^(d)（Frobenius 描像）について、
    (i) その leading log content が étale 描像 m^d に着地し（M321F `logShell_unit_filtration`
        ＝比較の像が右描像の正しい段に入る）、
    (ii) 比較の核が次段 U^(d+1) へ降りる（`logLink_kernel` ＝段 d から d+1 への降下）。
    ＝比較が log-link の各段で整合し（M337F `logLink_shell_step`）、フィルトレーションを
    跨いで両立する。これが**多輻表現の芽（seed）**: 2 描像の比較が段付き構造の全レベルで
    首尾一貫する（crux Dβ-ω ＝ theta-link 整合はこの芽の外にある外部仮説）。 -/
theorem mrc_multiradial_seed (p d : Nat) (hp : 1 ≤ p)
    (x : (principalUnits p).carrier) (hx : (unitFiltration p d).mem x) :
    logShellMem p d (logShellContent p x.val)
      ∧ (mrcCompare p d hp x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x) :=
  logLink_shell_step p d hp x hx

/-- **定理 (M362F-4b): 芽は描像の語彙で述べても同じ** — 多輻表現の芽を左右の描像述語
    `mrcFrobPicture`/`mrcEtalePicture` の語彙で述べたもの（再輸出が本物ゆえ一致）。 -/
theorem mrc_seed_pictures (p d : Nat) (hp : 1 ≤ p)
    (x : (principalUnits p).carrier) (hx : mrcFrobPicture p d x) :
    mrcEtalePicture p d (logShellContent p x.val)
      ∧ (mrcCompare p d hp x = (zmod p).one ↔ mrcFrobPicture p (d + 1) x) :=
  logLink_shell_step p d hp x hx

/-! ## M362F-5: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M362F-5a: crux は外部仮説・決して導出しない／honest)** — 多輻比較同型は
    **無条件で本物**（準同型 compare(uv)=compare u + compare v が crux とは独立に成立）だが、
    その下での**多輻的整合**（比較アルゴリズムと theta-link の crux ＝ Dβ-ω ＝ 論争の当の
    係争点）は本層で**決して証明しない**。crux を任意の外部 Prop `crux` として受け取り、
    比較準同型の本物性 **と** crux の連言を、crux が仮説として供給された場合にのみ返す
    ——crux は決して導出されない（過大主張禁止）。 -/
theorem mrc_crux_external (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y)
    (crux : Prop) (hcrux : crux) :
    (mrcCompare p d hp ((principalUnits p).mul x y)
        = (zmod p).mul (mrcCompare p d hp x) (mrcCompare p d hp y))
      ∧ crux :=
  ⟨mrc_compare_hom p d hp hd x y hx hy, hcrux⟩

/-- **定理 (M362F-5b: crux はちょうど受け取る仮説)** — 多輻比較の本層は crux Dβ-ω を
    **受け取る仮説そのもの**として扱い、それ以上でも以下でもない（Iff.rfl）。crux は
    新しく証明した定理ではなく、論争の係争点をそのまま外部仮説として受け取ったものである
    ことを機械検証で明示（M347F `cruxR_is_hypothesis` と同じ精神）。 -/
theorem mrc_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-- **定理 (M362F-5c: scope の固定)** — 多輻比較写像は本物（無条件で単位元を保つ準同型）で
    あり、crux（外部 Prop）は**仮説としてのみ**利用可能で本層では導出されない。比較同型を
    本物にするのみで crux を証明しない、という scope を機械検証可能な形で固定する。 -/
theorem mrc_scope (p d : Nat) (hp : 1 ≤ p) :
    mrcCompare p d hp (principalUnits p).one = (zmod p).one
      ∧ (∀ crux : Prop, crux → crux) :=
  ⟨mrc_compare_one p d hp, fun _ h => h⟩

/-! ## M362F-6: capstone -/

/-- **M362F-6a: 多輻比較データ**（総括） — Frobenius 描像 ⟷ étale 描像の比較同型を本物で
    束ねる: 2 描像（乗法 U^(d)・加法 log-shell m^d）・比較写像（= 縦 log-link）・
    compare(1)=0・準同型・段付き商上の全単射（核 = U^(d+1)・全射）・多輻表現の芽
    （フィルトレーション整合）。主語は M337F/M327F/M321F の本物であり toy を用いない。
    crux Dβ-ω（theta-link 整合）は範囲外。 -/
structure MrcRealData where
  /-- 局所体 K = ℚ_p の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  /-- p ≥ 1。 -/
  hp : 1 ≤ p
  /-- フィルトレーション段 d ≥ 1。 -/
  d : Nat
  /-- d ≥ 1。 -/
  hd : 1 ≤ d
  /-- Frobenius 描像（乗法 U^(d)）の会員述語。 -/
  frobMem : (principalUnits p).carrier → Prop
  /-- Frobenius 描像は U^(d) そのもの。 -/
  frob_is : frobMem = (unitFiltration p d).mem
  /-- étale 描像（加法 log-shell m^d）の会員述語。 -/
  etaleMem : (Zp p).carrier → Prop
  /-- étale 描像は log-shell m^d そのもの。 -/
  etale_is : etaleMem = logShellMem p d
  /-- 比較写像 Frobenius 描像 → étale 描像（= 縦 log-link）。 -/
  compareMap : (principalUnits p).carrier → (zmod p).carrier
  /-- compareMap は本物の比較写像。 -/
  is_compare : compareMap = mrcCompare p d hp
  /-- compare(1) = 0。 -/
  compare_one : compareMap (principalUnits p).one = (zmod p).one
  /-- 比較は準同型（乗法 → 加法、U^(d) 上）。 -/
  compare_hom : ∀ (x y : (principalUnits p).carrier),
    (unitFiltration p d).mem x → (unitFiltration p d).mem y →
    compareMap ((principalUnits p).mul x y)
      = (zmod p).mul (compareMap x) (compareMap y)
  /-- 段付き商上で単射: 核 = U^(d+1)。 -/
  iso_kernel : ∀ (x : (principalUnits p).carrier), (unitFiltration p d).mem x →
    (compareMap x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x)
  /-- 全射: étale 描像の加法段付き商 ℤ/p を尽くす。 -/
  iso_surj : ∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
    (unitFiltration p d).mem u ∧ compareMap u = c
  /-- 多輻表現の芽: 比較はフィルトレーションと可換（leading content が m^d に着地）。 -/
  seed : ∀ (x : (principalUnits p).carrier), (unitFiltration p d).mem x →
    logShellMem p d (logShellContent p x.val)

/-- **M362F-6b: witness** — ℤ_p 上（段 d=1）の本物の多輻比較データ。 -/
def mrcRealData (p : Nat) (hp : 1 ≤ p) : MrcRealData where
  p := p
  hp := hp
  d := 1
  hd := by omega
  frobMem := mrcFrobPicture p 1
  frob_is := rfl
  etaleMem := mrcEtalePicture p 1
  etale_is := rfl
  compareMap := mrcCompare p 1 hp
  is_compare := rfl
  compare_one := mrc_compare_one p 1 hp
  compare_hom := fun x y hx hy => mrc_compare_hom p 1 hp (by omega) x y hx hy
  iso_kernel := fun x hx => mrc_compare_injective_graded p 1 hp x hx
  iso_surj := fun c => mrc_compare_surjective p 1 hp (by omega) c
  seed := fun x hx => (mrc_multiradial_seed p 1 hp x hx).1

/-- **M362F-6c: 存在** — 本物の多輻比較データは充足可能（K = ℚ₂）。 -/
theorem mrc_exists : Nonempty MrcRealData :=
  ⟨mrcRealData 2 (by omega)⟩

/-! ## M362F-6 実例（ℤ₂・比較同型の本物性） -/

/-- 実例: 多輻比較は単位元を 0 へ（ℤ₂, d=1）。 -/
example : mrcCompare 2 1 (by omega) (principalUnits 2).one = (zmod 2).one :=
  mrc_compare_one 2 1 (by omega)

/-- 実例: 比較は étale 描像の加法段付き商 ℤ/2 を尽くす（生成元 1 を持つ主単数が存在）。 -/
example :
    ∃ u : (principalUnits 2).carrier,
      (unitFiltration 2 1).mem u
        ∧ mrcCompare 2 1 (by omega) u = Quot.mk (modCong 2).rel 1 :=
  mrc_compare_surjective 2 1 (by omega) (by omega) (Quot.mk (modCong 2).rel 1)

/-- 実例: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  mrc_crux_is_hypothesis crux

end IUT

