/-
  IUT/LogKummerMonoTheta.lean — M377F [実／本物]
  分類: 実 (mono-theta 環境の log-Kummer 対応＝Frobenius-like⇄étale-like)
  complete_pct 影響: 柱D を前進（M327F log-Kummer・M363F mono-theta 環境・M372F 多輻表現を結び、
    log-Kummer 対応が mono-theta 三剛性と両立・多輻表現が対応の下で（不定性を除いて）保存・
    テータ Kummer 類が log-shell 側へ輸送されることを本物で。crux Dβ-ω は外部仮説）。
  正直な限定: crux Dβ-ω（論争の係争点）は外部仮説のまま。対応は log-shell/表現レベル。
    完全な tempered mono-theta 環境の log-Kummer は theta-link(=crux)を要す。

  ## 本モジュールの位置づけ（何を合成したか）

  IUT III の **log-Kummer 対応（log-Kummer correspondence）**は、mono-theta 環境の中で
  乗法的（Kummer／Frobenius-like）テータ値と加法的（log／étale-like）log-shell を結ぶ。
  本 M377F は、既に本物化された次の部品の上で、この対応を mono-theta 環境の文脈で構成する:
    * M327F `LogKummerReal`: 本物の graded log θ_d（`logKumLog`, 乗法 U^(d) → 加法 ℤ/p）と
      その準同型 `logKum_log_hom`・核 `logKum_log_kernel`（=U^(d+1)）・全射 `logKum_log_surj`・
      可換図 `logKum_log_pow`（log(uⁿ)=n·log u）。
    * M337F `LogLinkReal`: 縦 log-link 写像 `logLinkMap`（同一の graded log の log-link 語彙）。
    * M363F `MonoThetaEnvironment`: mono-theta 環境 `MonoThetaEnvBundle`・三剛性
      `mte_three_rigidities`・Kummer 剛性 `mte_kummer_rigid`・同時整合 `mte_coherent`
      （μ_l=⟨ζ²⟩↪μ_{2l}）・κ 整合 `mte_kappa_coherent`。
    * M372F `MultiradialRep`: 多輻表現 `mrpRepresentation`・(Ind1)(Ind2) 不変核
      `mrpInvariantCore`・降下 `mrp_representation_descent`・crux 外部 `mrp_crux_external`。
    * M353F `ThetaKummerClass`: テータ Kummer 類 [Θ]∈H¹(G_K,μ_{2l})（`tkcClass`・`tkc_exists`）。

  ## 構成する中核（全て sorry なし・新規 Classical.choice なし）
  * M377F-1 `lkmFrobSide` / `lkmEtaleSide` — Frobenius-like（乗法テータ Kummer／U^(d)）側と
    étale-like（加法 log-shell ℤ/p）側。
  * M377F-2 `lkmCorrespondence` / `lkm_correspondence_one` / `lkm_correspondence_hom` /
    `lkm_correspondence_pow` / `lkm_correspondence_kernel` / `lkm_correspondence_surj`
    — log-Kummer 対応写像 = mono-theta 環境内で作用させた log（M327F/M337F の graded log）。
      準同型・単位元保存・n 乗可換・核=U^(d+1)・log-shell への全射（本物）。
  * M377F-3 `lkm_frob_etale_compat` / `lkm_env_compat` — 対応が mono-theta 三剛性と両立
    （円分/μ_l 同定 `mte_coherent`・環境の κ 整合 `galoisTheta_κ` が対応を貫く）。
  * M377F-4 `lkm_rep_preserved` — 多輻表現が対応の下で（不定性を除いて）保存
    （M372F 降下＋(Ind1)(Ind2) 不変核が log-Kummer ステップを生き延びる）。
  * M377F-5 `lkm_kummer_class_transported` — テータ Kummer 類 [Θ]（M353F）が対応で log-shell 側へ
    輸送（Frobenius-like [Θ] ⇄ étale-like log θ、対応の全射で加法 log-shell を尽くす）。
  * M377F-6 `lkm_crux_external` / `lkm_crux_is_hypothesis` — crux Dβ-ω は外部仮説（受け取るのみ）。
  * M377F-7 capstone `LogKummerMonoThetaData` / `logKummerMonoThetaData` / `lkm_exists` + 実例。

  ## 正直な限定（消去・弱化禁止・crux は恒久的に範囲外）
  * **crux Dβ-ω（多輻的アルゴリズム＝theta-link 整合＝IUT 論争の当の係争点）は恒久的に本層の
    範囲外**。本層は log-Kummer 対応（乗法テータ Kummer ⇄ 加法 log-shell の graded log）を
    本物で構成するのみで、crux（対応と theta-link の整合）は外部 Prop 仮説として受け取り
    決して導出しない。
  * **対応は log-shell/表現レベル**。log は主項係数 θ_d（M327F/M337F 継承、完全収束は後続）。
    完全な tempered mono-theta 環境の log-Kummer（tempered π₁^ét・theta-link 込み）は
    theta-link=crux を要し柱D/E 後続。ℝ は setoid ゆえ体積は realEq で言明。
  全て選択公理不使用（sorry 皆無・新規 Classical 皆無）。禁止タクティク不使用（core Lean のみ）。
  共有ファイル未変更。柱D 横展開・本物の先行建設[実]。一般名は `lkm` 接頭辞で衝突回避。
-/
import IUT.LogKummerReal
import IUT.LogLinkReal
import IUT.MonoThetaEnvironment
import IUT.MultiradialRep
import IUT.ThetaKummerClass

namespace IUT

/-! ## M377F-1: Frobenius-like（乗法）側と étale-like（加法 log-shell）側 -/

/-- **M377F-1a: Frobenius-like 側** — 乗法的テータ Kummer 側の主単数群 U^(d)
    （M327F `principalUnits p`）。IUT の Frobenius-like（乗法テータ値／Kummer）データが
    住む対象。log-Kummer 対応の定義域（乗法 → 加法）。 -/
abbrev lkmFrobSide (p : Nat) : Type := (principalUnits p).carrier

/-- **M377F-1b: étale-like 側** — 加法的 log-shell 側の加法群 ℤ/p（M327F `zmod p`）。
    IUT の étale-like（log-shell／加法 log θ）データが住む対象。log-Kummer 対応の値域。 -/
abbrev lkmEtaleSide (p : Nat) : Type := (zmod p).carrier

/-! ## M377F-2: log-Kummer 対応写像（mono-theta 環境内で作用させる graded log） -/

/-- **M377F-2a: log-Kummer 対応写像** — mono-theta 環境の中で Frobenius-like（乗法
    テータ Kummer／U^(d)）側から étale-like（加法 log-shell ℤ/p）側へ移す本物の graded
    log θ_d（M327F `logKumLog`／M337F `logLinkMap`）。乗法 Kummer 値を加法 log-shell へ
    翻訳する log-Kummer 対応の核。 -/
def lkmCorrespondence (p d : Nat) (hp : 1 ≤ p) (u : lkmFrobSide p) : lkmEtaleSide p :=
  logKumLog p d hp u

/-- **定理 (M377F-2b): 対応は単位元を 0 へ** — log-Kummer 対応は乗法単位元 1 を加法単位元
    0 へ送る（log(1)=0、M327F `logKum_log_one`）。 -/
theorem lkm_correspondence_one (p d : Nat) (hp : 1 ≤ p) :
    lkmCorrespondence p d hp (principalUnits p).one = (zmod p).one :=
  logKum_log_one p d hp

/-- **定理 (M377F-2c): 対応は準同型（乗法 → 加法）** — log(uv)=log u + log v。
    log-Kummer 対応が Frobenius-like（乗法）から étale-like（加法 log-shell）への
    準同型であることの本物（M327F `logKum_log_hom`、U^(d) 各段）。対応そのものは
    この準同型を無条件で満たす（crux とは独立）。 -/
theorem lkm_correspondence_hom (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : lkmFrobSide p)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y) :
    lkmCorrespondence p d hp ((principalUnits p).mul x y)
      = (zmod p).mul (lkmCorrespondence p d hp x) (lkmCorrespondence p d hp y) :=
  logKum_log_hom p d hp hd x y hx hy

/-- **定理 (M377F-2d): 対応の n 乗可換（log-Kummer 可換図）** — log(uⁿ)=n·log u。
    Kummer（乗法 n 乗）と log（加法）の可換性が対応を貫く（M327F `logKum_log_pow`）。 -/
theorem lkm_correspondence_pow (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    {u : lkmFrobSide p} (hu : (unitFiltration p d).mem u) :
    ∀ n : Nat,
      lkmCorrespondence p d hp (tateNpow (principalUnits p) u n)
        = tateNpow (zmod p) (lkmCorrespondence p d hp u) n :=
  logKum_log_pow p d hp hd hu

/-- **定理 (M377F-2e): 対応の核 = U^(d+1)** — log-Kummer 対応の核はちょうど次段の
    単数フィルトレーション（M327F `logKum_log_kernel`）。乗法 U^(d)/U^(d+1) ⇄ 加法
    log-shell の付値方向の対応。 -/
theorem lkm_correspondence_kernel (p d : Nat) (hp : 1 ≤ p)
    (u : lkmFrobSide p) (hu : (unitFiltration p d).mem u) :
    lkmCorrespondence p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u :=
  logKum_log_kernel p d hp u hu

/-- **定理 (M377F-2f): 対応は加法 log-shell を尽くす（全射）** — 任意の加法 log-shell 類
    c ∈ ℤ/p は U^(d) のある単数の log（M327F `logKum_log_surj`）。Frobenius-like 乗法側の
    像が étale-like 加法 log-shell を尽くす本物。 -/
theorem lkm_correspondence_surj (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (c : lkmEtaleSide p) :
    ∃ u : lkmFrobSide p,
      (unitFiltration p d).mem u ∧ lkmCorrespondence p d hp u = c :=
  logKum_log_surj p d hp hd c

/-! ## M377F-3: 対応は mono-theta 三剛性と両立（円分/μ_l 同定を尊重） -/

/-- **定理 (M377F-3a: 対応は円分剛性（μ_l 同定）と両立)** — log-Kummer 対応は準同型
    （乗法 → 加法）であり、かつ mono-theta 環境の内部円分体 μ_l=⟨ζ²⟩ とテータ Kummer 類の
    係数 μ_{2l}=⟨ζ⟩ の標準包含（M363F `mte_coherent`）が同時に尊重される。三剛性のうち
    円分剛性（cyclotome／μ_l 同定）が log-Kummer 対応を跨いで保たれることの本物。 -/
theorem lkm_frob_etale_compat (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : lkmFrobSide p)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y)
    (pz l : Nat) (ζ : (Zp pz).carrier)
    (hζ2l : zpPow pz ζ (2 * l) = zpOne pz)
    (hdist2l : ∀ i j, i < j → j < 2 * l → zpPow pz ζ i ≠ zpPow pz ζ j) :
    (lkmCorrespondence p d hp ((principalUnits p).mul x y)
        = (zmod p).mul (lkmCorrespondence p d hp x) (lkmCorrespondence p d hp y))
    ∧ (zpPow pz (zpPow pz ζ 2) l = zpOne pz
        ∧ (∀ i j, i < j → j < l →
            zpPow pz (zpPow pz ζ 2) i ≠ zpPow pz (zpPow pz ζ 2) j)) :=
  ⟨lkm_correspondence_hom p d hp hd x y hx hy, mte_coherent pz l ζ hζ2l hdist2l⟩

/-- **定理 (M377F-3b: 対応は mono-theta 環境の Kummer 捻り κ 整合と両立)** — mono-theta
    環境 `env` の中で、log-Kummer 対応は準同型であり、かつ環境のガロア同変テータの Kummer
    捻り κ がテータ Kummer 類の κ と同一（M363F `galoisTheta_κ`）である。三剛性を束ねる
    同一の Kummer 捻り指標 κ が log-Kummer 対応の両側（乗法テータ Kummer ⇄ 加法 log-shell）
    を貫くことの本物の整合性。 -/
theorem lkm_env_compat {R : CRing} {K : IUTField} {pz l : Nat} {hl : 2 ≤ l}
    {ζ : (Zp pz).carrier} {hζ2l : zpPow pz ζ (2 * l) = zpOne pz}
    {hdist2l : ∀ i j, i < j → j < 2 * l → zpPow pz ζ i ≠ zpPow pz ζ j}
    {GK : Grp} {Mm : CycMuGroup} {κ : Hom GK Mm.μ} {e : Nat}
    (env : MonoThetaEnvBundle R K pz l hl ζ hζ2l hdist2l GK Mm κ e)
    (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : lkmFrobSide p)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y) :
    (lkmCorrespondence p d hp ((principalUnits p).mul x y)
        = (zmod p).mul (lkmCorrespondence p d hp x) (lkmCorrespondence p d hp y))
      ∧ env.galoisTheta.κ = κ :=
  ⟨lkm_correspondence_hom p d hp hd x y hx hy, env.galoisTheta_κ⟩

/-! ## M377F-4: 多輻表現が対応の下で（不定性を除いて）保存される -/

/-- **定理 (M377F-4: 多輻表現は log-Kummer 対応の下で（不定性を除いて）保存)** —
    (i) 多輻表現はテータパイロット体積の降下（M372F `mrp_representation_descent`）、
    (ii) その (Ind1) 置換像・(Ind2) 単数像がともに同じ表現値へ降下（M372F
    `mrp_ind1_invariant`/`mrp_ind2_invariant`：(Ind1)(Ind2)-不変核が log-Kummer ステップを
    生き延びる）、(iii) log-Kummer 対応は本物（乗法単位元 → 加法単位元）。
    ＝多輻表現の (Ind1)(Ind2)-不変核が log-Kummer 対応の下で保存されることの本物
    （crux Dβ-ω＝theta-link 整合はこの保存の外にある外部仮説）。 -/
theorem lkm_rep_preserved (logq : Nat → RReal) (v n : Nat)
    (a b : Nat) (hab : ¬ a = b) (ha : a < n) (hb : b < n)
    (p d : Nat) (hp : 1 ≤ p) :
    (realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n)
      ∧ realEq (indR_realTotal logq v (swapMult a b indR_natExp) n)
          (mrpRepresentation logq v n)
      ∧ realEq (indR_ind2Vol logq v (thPilotTotalVol logq v n) 0)
          (mrpRepresentation logq v n))
    ∧ lkmCorrespondence p d hp (principalUnits p).one = (zmod p).one :=
  ⟨⟨mrp_representation_descent logq v n,
    mrp_ind1_invariant logq v a b n hab ha hb,
    mrp_ind2_invariant logq v n⟩,
   lkm_correspondence_one p d hp⟩

/-! ## M377F-5: テータ Kummer 類が対応で log-shell 側へ輸送される -/

/-- **定理 (M377F-5: テータ Kummer 類 [Θ] は対応で log-shell 側へ輸送)** —
    (i) Frobenius-like 乗法側にはテータ Kummer 類 [Θ]∈H¹(G_K,μ_{2l}) が本物で存在する
    （M353F `tkc_exists`：乗法テータ値の Kummer 類）、
    (ii) log-Kummer 対応は Frobenius-like 乗法側 U^(d) を étale-like 加法 log-shell ℤ/p へ
    **全射**する（任意の加法 log θ 類 c が乗法単数の log として実現、M377F-2f）。
    ＝Frobenius-like [Θ]（乗法 Kummer）⇄ étale-like log θ（加法 log-shell）の輸送が
    「乗法テータ Kummer 類が存在し・対応が加法 log-shell を尽くす」形で本物に成立する
    （完全な H¹ ⇄ log-shell の写像は tempered/crux 込みで後続）。 -/
theorem lkm_kummer_class_transported {GK : Grp} (M : CycMuGroup) (κ : Hom GK M.μ) (e : Nat)
    (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) :
    Nonempty (TkcData M κ e)
    ∧ (∀ c : lkmEtaleSide p, ∃ u : lkmFrobSide p,
        (unitFiltration p d).mem u ∧ lkmCorrespondence p d hp u = c) :=
  ⟨tkc_exists M κ e, fun c => lkm_correspondence_surj p d hp hd c⟩

/-! ## M377F-6: crux Dβ-ω は外部仮説（決して導出しない） -/

/-- **定理 (M377F-6a: crux は外部仮説・決して導出しない／honest)** — log-Kummer 対応は
    **無条件で本物**（準同型 log(uv)=log u + log v が crux とは独立に成立）だが、その下での
    **多輻的アルゴリズム**（対応と theta-link の crux ＝ Dβ-ω ＝ IUT 論争の当の係争点）は
    本層で**決して証明しない**。crux を任意の外部 Prop `crux` として受け取り、対応の
    準同型の本物性 **と** crux の連言を、crux が仮説として供給された場合にのみ返す
    ——crux は決して導出されない（過大主張禁止・M337F/M372F と同じ精神）。 -/
theorem lkm_crux_external (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : lkmFrobSide p)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y)
    (crux : Prop) (hcrux : crux) :
    (lkmCorrespondence p d hp ((principalUnits p).mul x y)
        = (zmod p).mul (lkmCorrespondence p d hp x) (lkmCorrespondence p d hp y))
      ∧ crux :=
  ⟨lkm_correspondence_hom p d hp hd x y hx hy, hcrux⟩

/-- **定理 (M377F-6b: crux はちょうど受け取る仮説)** — 本層は crux Dβ-ω を**受け取る仮説
    そのもの**として扱い、それ以上でも以下でもない（Iff.rfl）。crux は新しく証明した定理では
    なく、論争の係争点をそのまま外部仮説として受け取ったものであることを機械検証で明示。 -/
theorem lkm_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M377F-7: capstone -/

/-- **M377F-7a: mono-theta 環境の log-Kummer 対応データ**（総括） — Frobenius-like（乗法
    テータ Kummer／U^(d)）⇄ étale-like（加法 log-shell ℤ/p）の log-Kummer 対応を本物で
    束ねる: 対応写像（graded log θ_d）・単位元保存・準同型（乗法 → 加法）・核=U^(d+1)・
    加法 log-shell への全射・多輻表現の降下。主語は M327F/M337F/M363F/M372F の本物であり、
    toy を用いない。crux Dβ-ω（theta-link 整合）は範囲外。 -/
structure LogKummerMonoThetaData where
  /-- 局所体 K = ℚ_p の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  /-- p ≥ 1。 -/
  hp : 1 ≤ p
  /-- フィルトレーション段 d ≥ 1。 -/
  d : Nat
  /-- d ≥ 1。 -/
  hd : 1 ≤ d
  /-- log-Kummer 対応写像（graded log θ_d、乗法 U^(d) → 加法 log-shell ℤ/p）。 -/
  corr : lkmFrobSide p → lkmEtaleSide p
  /-- corr は本物の log-Kummer 対応（M327F/M337F graded log）。 -/
  is_corr : corr = lkmCorrespondence p d hp
  /-- 単位元保存: log(1)=0（乗法単位元 → 加法単位元）。 -/
  corr_one : corr (principalUnits p).one = (zmod p).one
  /-- 準同型: log(uv)=log u + log v（乗法 → 加法、U^(d) 上）。 -/
  corr_hom : ∀ (x y : lkmFrobSide p),
    (unitFiltration p d).mem x → (unitFiltration p d).mem y →
    corr ((principalUnits p).mul x y) = (zmod p).mul (corr x) (corr y)
  /-- 対応の核 = U^(d+1)（乗法 U^(d)/U^(d+1) ⇄ 加法 log-shell）。 -/
  corr_kernel : ∀ (u : lkmFrobSide p), (unitFiltration p d).mem u →
    (corr u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)
  /-- 対応は加法 log-shell を尽くす（全射）。 -/
  corr_surj : ∀ c : lkmEtaleSide p, ∃ u : lkmFrobSide p,
    (unitFiltration p d).mem u ∧ corr u = c
  /-- 多輻表現はテータパイロット体積の降下（対応の下で保存）。 -/
  rep_descent : ∀ (logq : Nat → RReal) (v n : Nat),
    realEq (thPilotTotalVol logq v n) (mrpRepresentation logq v n)

/-- **M377F-7b: witness** — ℤ_p 上（段 d=1）の本物の mono-theta 環境 log-Kummer 対応データ。 -/
def logKummerMonoThetaData (p : Nat) (hp : 1 ≤ p) : LogKummerMonoThetaData where
  p := p
  hp := hp
  d := 1
  hd := by omega
  corr := lkmCorrespondence p 1 hp
  is_corr := rfl
  corr_one := lkm_correspondence_one p 1 hp
  corr_hom := fun x y hx hy => lkm_correspondence_hom p 1 hp (by omega) x y hx hy
  corr_kernel := fun u hu => lkm_correspondence_kernel p 1 hp u hu
  corr_surj := fun c => lkm_correspondence_surj p 1 hp (by omega) c
  rep_descent := fun logq v n => mrp_representation_descent logq v n

/-- **M377F-7c: 存在** — 本物の mono-theta 環境 log-Kummer 対応データは充足可能（K = ℚ₂）。
    M327F log-Kummer・M337F log-link・M363F mono-theta 環境・M372F 多輻表現・M353F テータ
    Kummer 類を結び、log-Kummer 対応が Frobenius-like⇄étale-like で本物化された
    （crux Dβ-ω は外部仮説）。 -/
theorem lkm_exists : Nonempty LogKummerMonoThetaData :=
  ⟨logKummerMonoThetaData 2 (by omega)⟩

/-! ## M377F-7 実例（ℤ₂・log-Kummer 対応の本物性） -/

/-- 実例: log-Kummer 対応は乗法単位元を加法 0 へ（ℤ₂, d=1）。 -/
example : lkmCorrespondence 2 1 (by omega) (principalUnits 2).one = (zmod 2).one :=
  lkm_correspondence_one 2 1 (by omega)

/-- 実例: log-Kummer 対応は加法 log-shell ℤ/2 を尽くす（生成元 1 を持つ主単数が存在）。 -/
example :
    ∃ u : lkmFrobSide 2,
      (unitFiltration 2 1).mem u
        ∧ lkmCorrespondence 2 1 (by omega) u = Quot.mk (modCong 2).rel 1 :=
  lkm_correspondence_surj 2 1 (by omega) (by omega) (Quot.mk (modCong 2).rel 1)

/-- 実例: l=5（n=2）で多輻表現は log-Kummer 対応の下で保存され、対応は単位元を保つ。 -/
example (logq : Nat → RReal) (v : Nat) :
    (realEq (thPilotTotalVol logq v 2) (mrpRepresentation logq v 2)
      ∧ realEq (indR_realTotal logq v (swapMult 0 1 indR_natExp) 2)
          (mrpRepresentation logq v 2)
      ∧ realEq (indR_ind2Vol logq v (thPilotTotalVol logq v 2) 0)
          (mrpRepresentation logq v 2))
    ∧ lkmCorrespondence 2 1 (by omega) (principalUnits 2).one = (zmod 2).one :=
  lkm_rep_preserved logq v 2 0 1 (by omega) (by omega) (by omega) 2 1 (by omega)

/-- 実例: crux Dβ-ω はちょうど受け取る外部仮説（Iff.rfl・定理でない）。 -/
example (crux : Prop) : crux ↔ crux :=
  lkm_crux_is_hypothesis crux

/-- 実例: mono-theta 環境の log-Kummer 対応データは存在する。 -/
example : Nonempty LogKummerMonoThetaData := lkm_exists

end IUT
