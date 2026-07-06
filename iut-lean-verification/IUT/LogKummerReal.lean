/-
  IUT/LogKummerReal.lean — M327F（本物の log-Kummer 対応:
  Frobenius-like 加法 log ⇄ étale-like 乗法単数群）

  ## 二軸
  * 主要成果の分類: **[実]**（本物の p 進主単数群 `principalUnits p`
    （= 1 + pℤ_p, ×）と本物の graded log `unitTheta`（θ_d = p 進対数の
    主項係数、M31）の上に、**log-Kummer 対応の核**を本物で建てる:
    (i) log が乗法 → 加法の**準同型** log(uv)=log u + log v、
    (ii) log-Kummer 可換図 **log(uⁿ)=n·log u**（Kummer=n 乗（乗法）と
    log（加法）の可換）、(iii) 単数フィルトレーション ⇄ 加法 shell の
    対応（1+m^d ⇄ m^d = 付値方向の対応、θ_d の核=U^(d+1)・全射）を
    完全証明する）。
  * complete_pct 影響: **前進**。既存 `IUT/LogKummer.lean`（M205F）は
    log-Kummer 対応を **toy 模型**（`m202fVol` 型体積・`Bool`/`Unit` の
    Frobenius データ・抽象 `VerticalKummerTower`）を主語にした**骨格**で
    あり、log 写像そのものも単数群そのものも p 進局所体の実体を持たない。
    本 M327F は log-Kummer 対応の主語を **toy → 本物**へ昇格させる:
    乗法側は**本物の主単数群 `principalUnits p`**（M30、étale-like/
    Kummer）、加法側は**本物の ℤ/p 加法群 `zmod p`**（Frobenius-like
    /log-shell）、log は**本物の graded log θ_d = `unitTheta`**（M31）。
    log の準同型性・log(uⁿ)=n·log u・フィルトレーション対応を本物で
    閉じることで、柱C（Frobenioid/log-link）の log-Kummer 対応の核を
    **代理 → 実**へ前進させる。

  ## 何を本物化したか（既存 LogKummer=模型 → 本物へ）
  M205F の log-Kummer 対応は次の点で toy/骨格だった:
  * 乗法側（Kummer/étale-like）が `Bool` 軌道の不定性・抽象 `frob : Int → α`。
  * 加法側（log-shell/Frobenius-like）が `m202fVol` の `V.Region`（= ℝ 代理）。
  * 「log 写像」が無く、対応は型レベルの述語 `LogKummerCompat`（包含 ⊆ の
    簿記）に留まり、log の準同型性・log(uⁿ)=n·log u が存在しない。
  本 M327F は次を**本物の対象**で新規に積む:
  * M327F-1 `logKumLog` — 本物の graded log θ_d（`unitTheta`, M31）を
    log-Kummer の log として採る。乗法群 U^(d) → 加法群 ℤ/p。
  * M327F-2 `logKum_log_one` / `logKum_log_hom` — **log(1)=0** と
    **log(uv)=log u + log v**（乗法 → 加法の準同型・`unitTheta_hom`）。
    Frobenius-like（加法）⇄ étale-like（乗法）の準同型的橋の本物。
  * M327F-3 `logKum_filtration_npow` / `logKum_log_pow` —
    **log-Kummer 可換図 log(uⁿ)=n·log u** を本物で（U^(d) が n 乗で閉じ、
    log の準同型からの帰納）。Kummer（n 乗・乗法）と log（加法）の可換。
  * M327F-4 `logKumMult` / `logKum_mult_hom` — 乗法側の Kummer 構造:
    n 乗写像 u↦uⁿ（`tateNpow`）とその乗法性 (uv)ⁿ=uⁿvⁿ
    （`tateTorMulPow`・可換群）＝ étale-like 単数群の n 乗（Kummer）。
  * M327F-5 `logKum_diagram` / `logKum_commute` — log∘(n 乗)=n·log の
    可換図（M327F-3 を Kummer n 乗写像 `logKumMult` の語彙で）。
  * M327F-6 `logKum_log_kernel` / `logKum_log_surj` / `logKum_frob_etale`
    — **単数フィルトレーション ⇄ 加法 shell 対応**: θ_d は U^(d) を ℤ/p
    へ全射し、核はちょうど U^(d+1)（`unitTheta_kernel`/`_surj`）。
    ＝ 1+m^d ⇄ m^d（付値方向の対応）・étale-like U^(d)/U^(d+1) ⇄
    Frobenius-like 加法 ℤ/p。
  * M327F-7 capstone `LogKummerRealData` / `logKummerRealData` /
    `logKum_exists`、実例 `logKum_example_two`（ℤ₂ 上、非自明な log 値）。

  ## 正直な限定（消去・弱化禁止）
  * **log 写像は p 進対数の主項（leading-coefficient）θ_d で本物**。
    完全な p 進対数の収束級数 log(1+t) = t − t²/2 + t³/3 − …（分母 1/k の
    整数性・逆極限上の収束）の構成は重く、ここでは M31 `unitTheta` =
    その主項 θ_d（= 1-jet の係数、log(1+p^d u) ≡ p^d u の u mod p）を採る。
    θ_d は**本物の準同型**（`unitTheta_hom`）であり toy ではない —— log の
    「乗法 → 加法」性の主項での本物の実現。完全収束級数は後続層。
  * **準同型 log(uv)=log u + log v・log(uⁿ)=n·log u は各段 U^(d) 上で本物**。
    θ_d は次数商 U^(d)/U^(d+1) ≅ ℤ/p を与える写像で、準同型性は
    x,y ∈ U^(d) を仮定する（filtration の各段での本物の準同型）。全 U^(1)
    上の単一の log 準同型（全レベルを束ねる完全な p 進 log）は完全収束級数を
    要し後続。log(uⁿ)=n·log u は U^(d) の各段で完全証明（帰納・sorry 皆無）。
  * **局所体は K = ℚ_p（O_v = ℤ_p, U^(d)=1+p^d ℤ_p）**。一般の局所体
    O_K^× の μ_{q−1}×(1+m) 分解・分数係数 log-shell は後続。μ_n（1 の
    n 乗根）そのものの構成は M320F/M314F と後続で接続する（本層は log の
    n 乗可換＝Kummer 側の n 乗写像に専念）。
  * **Frobenius-like/étale-like の完全な圏論的（Frobenioid）定式化は後続**。
    ここは log-Kummer 対応の**核**（乗法単数 ⇄ 加法 log の log 写像・その
    準同型性・n 乗可換・フィルトレーション対応）に徹する。IUT の log-link
    本丸（log-theta 格子の log-link・多輻での相互作用）は柱D 後続。
  * **既存 M205F（模型）は消さない**: 本層は M205F の toy 主語（体積代理・
    Bool 不定性）を**本物の主単数群と graded log で置換**した並行の本物版
    であり、M205F の型レベル簿記（包含 ⊆・Ind3 ゲート）は別の側面として
    残す。

  全て選択公理不使用（sorry 皆無・新規 Classical 皆無）。禁止タクティク
  不使用（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp なし）。共有ファイル（IUT.lean・build.sh・
  dashboard.md・graph 系）は一切変更なし。柱C 横展開・本物の先行建設[実]。
-/
import IUT.UnitFiltration
import IUT.TateTorsion

namespace IUT

/-! ## M327F-1: log-Kummer の log 写像 = graded log θ_d（本物） -/

/-- **M327F-1: log-Kummer の log 写像** — 本物の graded log θ_d
    （`unitTheta`, M31）。乗法群 U^(d)（étale-like/Kummer 側）から
    加法群 ℤ/p（Frobenius-like/log-shell 側）への写像。
    log(1+p^d u) = p^d u + O(p^{2d}) の主項係数 u mod p。 -/
def logKumLog (p d : Nat) (hp : 1 ≤ p) (u : (principalUnits p).carrier) :
    (zmod p).carrier :=
  unitTheta p d hp u

/-! ## M327F-2: log は準同型（乗法 → 加法）・log(1)=0 -/

/-- **定理 (M327F-2a): log(1) = 0** — 単位元 1 の graded log は加法単位元
    0（= (zmod p).one）。(1−1)/p^d = 0。 -/
theorem logKum_log_one (p d : Nat) (hp : 1 ≤ p) :
    logKumLog p d hp (principalUnits p).one = (zmod p).one := by
  show Quot.mk (modCong p).rel (((1 : Int) - 1) / ((p ^ d : Nat) : Int))
      = Quot.mk (modCong p).rel 0
  have h0 : (1 : Int) - 1 = 0 := by omega
  rw [h0, Int.zero_ediv]

/-- **定理 (M327F-2b): log は準同型** — log(uv) = log u + log v
    （乗法群 U^(d) から加法群 ℤ/p へ、各段で本物）。`unitTheta_hom`
    （M31）を log-Kummer の語彙で採る。log の「乗法 → 加法」性
    ＝ Frobenius-like（加法）⇄ étale-like（乗法）の準同型的橋の核。 -/
theorem logKum_log_hom (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (x y : (principalUnits p).carrier)
    (hx : (unitFiltration p d).mem x) (hy : (unitFiltration p d).mem y) :
    logKumLog p d hp ((principalUnits p).mul x y)
      = (zmod p).mul (logKumLog p d hp x) (logKumLog p d hp y) :=
  unitTheta_hom p d hp hd x y hx hy

/-! ## M327F-3: log-Kummer 可換図 log(uⁿ) = n·log u（本物） -/

/-- **定理 (M327F-3a): U^(d) は n 乗で閉じる** — u ∈ U^(d) なら
    uⁿ ∈ U^(d)（部分群は tateNpow で閉じる）。log(uⁿ) の帰納の土台。 -/
theorem logKum_filtration_npow (p d : Nat) {u : (principalUnits p).carrier}
    (hu : (unitFiltration p d).mem u) :
    ∀ n : Nat, (unitFiltration p d).mem (tateNpow (principalUnits p) u n) := by
  intro n
  induction n with
  | zero => exact (unitFiltration p d).one_mem
  | succ k ih => exact (unitFiltration p d).mul_mem ih hu

/-- **定理 (M327F-3b): log-Kummer 可換図 log(uⁿ) = n·log u** —
    graded log は n 乗を n 倍へ移す（乗法群での n 乗 ⇄ 加法群での n 倍）。
    帰納: log(u^{k+1}) = log(uᵏ·u) = log(uᵏ) + log(u) = k·log u + log u
    = (k+1)·log u（各段で U^(d)・log 準同型 `logKum_log_hom`）。
    これが **Kummer（n 乗・乗法）と log（加法）の対応の可換性**そのもの。 -/
theorem logKum_log_pow (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    {u : (principalUnits p).carrier} (hu : (unitFiltration p d).mem u) :
    ∀ n : Nat,
      logKumLog p d hp (tateNpow (principalUnits p) u n)
        = tateNpow (zmod p) (logKumLog p d hp u) n := by
  intro n
  induction n with
  | zero =>
    show logKumLog p d hp (principalUnits p).one = (zmod p).one
    exact logKum_log_one p d hp
  | succ k ih =>
    show logKumLog p d hp
        ((principalUnits p).mul (tateNpow (principalUnits p) u k) u)
      = (zmod p).mul (tateNpow (zmod p) (logKumLog p d hp u) k)
          (logKumLog p d hp u)
    rw [logKum_log_hom p d hp hd (tateNpow (principalUnits p) u k) u
        (logKum_filtration_npow p d hu k) hu, ih]

/-! ## M327F-4: 乗法側 Kummer 構造（n 乗写像・étale-like） -/

/-- **M327F-4a: Kummer n 乗写像** — 主単数群 U 上の u ↦ uⁿ（`tateNpow`）。
    étale-like（乗法的単数）の n 乗＝Kummer 理論の n 乗写像の主単数版。 -/
def logKumMult (p n : Nat) (u : (principalUnits p).carrier) :
    (principalUnits p).carrier :=
  tateNpow (principalUnits p) u n

/-- **定理 (M327F-4b): Kummer n 乗は乗法的** — (uv)ⁿ = uⁿ·vⁿ
    （主単数群は可換 `principalUnits_comm`、`tateTorMulPow`）。
    étale-like 単数群の n 乗写像が本物の準同型であること。 -/
theorem logKum_mult_hom (p n : Nat) (u v : (principalUnits p).carrier) :
    logKumMult p n ((principalUnits p).mul u v)
      = (principalUnits p).mul (logKumMult p n u) (logKumMult p n v) :=
  tateTorMulPow (principalUnits p) (principalUnits_comm p) u v n

/-! ## M327F-5: log-Kummer 可換図（Kummer n 乗写像の語彙で） -/

/-- **定理 (M327F-5a): 可換図 log∘(n 乗) = n·log** — Kummer n 乗写像
    `logKumMult` と log の可換: log(logKumMult n u) = n·log u。
    M327F-3b を Kummer n 乗写像の語彙で述べたもの。 -/
theorem logKum_diagram (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) (n : Nat)
    {u : (principalUnits p).carrier} (hu : (unitFiltration p d).mem u) :
    logKumLog p d hp (logKumMult p n u)
      = tateNpow (zmod p) (logKumLog p d hp u) n :=
  logKum_log_pow p d hp hd hu n

/-- **定理 (M327F-5b): log-Kummer 可換（capstone 別名）** — log∘n 乗 = n·log。 -/
theorem logKum_commute (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) (n : Nat)
    {u : (principalUnits p).carrier} (hu : (unitFiltration p d).mem u) :
    logKumLog p d hp (logKumMult p n u)
      = tateNpow (zmod p) (logKumLog p d hp u) n :=
  logKum_diagram p d hp hd n hu

/-! ## M327F-6: 単数フィルトレーション ⇄ 加法 shell 対応
    （Frobenius-like ⇄ étale-like: 1+m^d ⇄ m^d） -/

/-- **定理 (M327F-6a): log の核 = U^(d+1)** — u ∈ U^(d) について
    log u = 0 ⟺ u ∈ U^(d+1)（`unitTheta_kernel`）。乗法フィルトレーション
    U^(d)/U^(d+1) と加法 shell ℤ/p の対応の核: 次段 U^(d+1) が log の核
    ＝ 1+m^{d+1} ⇄ 0（m^d を法とした対応）。 -/
theorem logKum_log_kernel (p d : Nat) (hp : 1 ≤ p)
    (u : (principalUnits p).carrier) (hu : (unitFiltration p d).mem u) :
    (logKumLog p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u) :=
  unitTheta_kernel p d hp u hu

/-- **定理 (M327F-6b): log は全射** — 任意の加法類 c ∈ ℤ/p は U^(d) の
    ある単数の log（`unitTheta_surj`）。étale-like 乗法フィルトレーションが
    Frobenius-like 加法 shell ℤ/p を**尽くす**。 -/
theorem logKum_log_surj (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (c : (zmod p).carrier) :
    ∃ u : (principalUnits p).carrier,
      (unitFiltration p d).mem u ∧ logKumLog p d hp u = c :=
  unitTheta_surj p d hp hd c

/-- **定理 (M327F-6c): Frobenius-like ⇄ étale-like 対応** — graded log は
    乗法フィルトレーション U^(d)（étale-like）を加法 shell ℤ/p
    （Frobenius-like）へ**全射**し、その**核はちょうど U^(d+1)**。
    ＝ 単数フィルトレーション 1+m^d ⇄ 加法 m^d/m^{d+1} の付値方向の対応
    （U^(d)/U^(d+1) ≅ ℤ/p の log 写像による実現）。log-Kummer 対応の
    Frobenius-like（加法 log）⇄ étale-like（乗法単数）の核。 -/
theorem logKum_frob_etale (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) :
    (∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
        (unitFiltration p d).mem u ∧ logKumLog p d hp u = c)
    ∧ (∀ u : (principalUnits p).carrier, (unitFiltration p d).mem u →
        (logKumLog p d hp u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)) :=
  ⟨fun c => logKum_log_surj p d hp hd c,
   fun u hu => logKum_log_kernel p d hp u hu⟩

/-! ## M327F-7: capstone -/

/-- **M327F-7a: log-Kummer 対応データ**（総括） — 本物の p 進主単数群
    `principalUnits p`・graded log `logMap`・log(1)=0・準同型 log(uv)=…・
    可換図 log(uⁿ)=n·log u・フィルトレーション対応（核=U^(d+1)・全射）を束ねる。 -/
structure LogKummerRealData where
  /-- 局所体 K = ℚ_p の素数 p（O_v = ℤ_p）。 -/
  p : Nat
  /-- p ≥ 1。 -/
  hp : 1 ≤ p
  /-- フィルトレーション段 d ≥ 1。 -/
  d : Nat
  /-- d ≥ 1。 -/
  hd : 1 ≤ d
  /-- log-Kummer の log 写像（graded log θ_d）。 -/
  logMap : (principalUnits p).carrier → (zmod p).carrier
  /-- logMap は本物の graded log。 -/
  is_log : logMap = logKumLog p d hp
  /-- log(1) = 0。 -/
  log_one : logMap (principalUnits p).one = (zmod p).one
  /-- log は準同型（乗法 → 加法、U^(d) 上）。 -/
  log_hom : ∀ (x y : (principalUnits p).carrier),
    (unitFiltration p d).mem x → (unitFiltration p d).mem y →
    logMap ((principalUnits p).mul x y) = (zmod p).mul (logMap x) (logMap y)
  /-- 可換図 log(uⁿ) = n·log u。 -/
  log_pow : ∀ (u : (principalUnits p).carrier), (unitFiltration p d).mem u →
    ∀ n : Nat, logMap (tateNpow (principalUnits p) u n)
      = tateNpow (zmod p) (logMap u) n
  /-- フィルトレーション対応: log の核 = U^(d+1)。 -/
  kernel : ∀ (u : (principalUnits p).carrier), (unitFiltration p d).mem u →
    (logMap u = (zmod p).one ↔ (unitFiltration p (d + 1)).mem u)
  /-- フィルトレーション対応: log は加法 shell ℤ/p を尽くす（全射）。 -/
  surj : ∀ c : (zmod p).carrier, ∃ u : (principalUnits p).carrier,
    (unitFiltration p d).mem u ∧ logMap u = c

/-- **M327F-7b: witness** — ℤ_p 上（段 d=1）の本物の log-Kummer 対応データ。 -/
def logKummerRealData (p : Nat) (hp : 1 ≤ p) : LogKummerRealData where
  p := p
  hp := hp
  d := 1
  hd := by omega
  logMap := logKumLog p 1 hp
  is_log := rfl
  log_one := logKum_log_one p 1 hp
  log_hom := fun x y hx hy => logKum_log_hom p 1 hp (by omega) x y hx hy
  log_pow := fun u hu n => logKum_log_pow p 1 hp (by omega) hu n
  kernel := fun u hu => logKum_log_kernel p 1 hp u hu
  surj := fun c => logKum_log_surj p 1 hp (by omega) c

/-- **M327F-7c: 存在** — 本物の log-Kummer 対応データは充足可能（K = ℚ₂）。 -/
theorem logKum_exists : Nonempty LogKummerRealData :=
  ⟨logKummerRealData 2 (by omega)⟩

/-! ## M327F-7 実例 -/

/-- **定理 (M327F-7d): 実例（ℤ₂・非自明な log 値）** — p=2, d=1 で、
    加法 shell ℤ/2 の生成元 1 を graded log に持つ主単数 u ∈ U^(1) が
    存在する（`unitTheta_surj`）。Frobenius-like 加法値 1（≠ 0）に対応する
    étale-like 単数 u = 1 + 2·(…) の存在 ＝ log-Kummer 対応の非自明性。 -/
theorem logKum_example_two :
    ∃ u : (principalUnits 2).carrier,
      (unitFiltration 2 1).mem u
        ∧ logKumLog 2 1 (by omega) u = Quot.mk (modCong 2).rel 1 :=
  logKum_log_surj 2 1 (by omega) (by omega) (Quot.mk (modCong 2).rel 1)

end IUT
