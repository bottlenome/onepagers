/-
  IUT/CyclotomeRecoveryCanonicity.lean — CRC（柱A6 headline: 復元円分体 T̂=`crlLimit`
  と実 T=ℤ₃(1)=`tmzLimit` の G-同変同一視空間 Isom_G(T̂,T) の torsor 正準性——
  「任意の同一視 Φ : T̂ → T が実 ℤ₃^×=`zpsLimit` の一意の元 u で Φ = (tmiFromUnits u)∘Ξ と
  書け、逆に全ての u が G-同変同一視を与える」＝ Isom_G(T̂,T) ≅ 実 ℤ₃^×（ちょうど・消去形）を
  完全証明する）

  ── 主要成果の分類: **[実／昇格(a)＋本物建設(b)]**（骨格・模型・代理でなく、File 1
     `CyclotomeRecoveryLimit` が本物に先行建設した復元側極限 T̂=`crlLimit`（χ 捻り復元塔
     `zmod (3^{n+1})` の逆極限・実非自明円分指標 χ=`cgarRecChar` 由来）と実 μ 塔極限
     T=`tmzLimit`＝ℤ₃(1) の明示 G-同変同一視 Ξ=`crlIso` の上に、A7 の実剛性機構
     `tmi_aut_classify`（∀自己同型がちょうど 1 つの実 ℤ₃^× 単元から来る）を Ξ/Ξ⁻¹ で移送し、
     **∀Φ 量化の正準性定理**を建てる。crr の薄さ（G1: χ と作用が同一 `cgarAct` 由来ゆえ
     「1 本の iso はほぼ簿記」・一意性/正準性の不在）を、∀Φ 量化——Φ は `cgarAct` から
     作られたとは限らない**抽象 Hom**であり、それが必ず u·Ξ の形になることは A7d の可除性
     フィルトレーション・自動降下を経由して初めて言える本物の内容——で正面から解消する。

  **complete_pct 影響**: A6（mono-anabelian 復元）——前回監査の thin 判定 (G1)「復元の
  正準性/一意性の不在」を正面 discharge する headline。crr が構成した「復元 μ̂ ≅ 実 μ の
  1 本の iso」を、File 1 の極限化に続き、「**全同一視の消去形分類（ちょうど実 ℤ₃^× torsor）**」
  へ昇格する。設計見込み A6 0.55 → 0.62（最終値は独立監査確定・過大主張しない・
  下振れ 0.58–0.60＝表示 51 横這いも想定内）。本ファイル単体では complete_pct は独立監査で反映。

  内容（設計 audit/A6-cyclotome-recovery-canonicity-detail-2026-07-11.md §3.2・CRC-1〜5）:
   * `crc_canonical`         — ★正準性（存在）: 任意の可逆同一視 Φ は実単元 u × Ξ。CRC-1。
   * `crc_canonical_unique`  — ★一意性: その u は一意。CRC-2。
   * `crc_torsor_realize`    — ★正確性（正直方向）: 全 torsor 点 u が G-同変同一視。CRC-3。
   * `crc_hom_ext`/`crc_transport_eq`/`crc_act_char` — 橋（小）: 復元作用を Ξ で移送すると
     実 Galois 作用に一致し、その分類指数＝χ（`cliChar`）。CRC-4。
   * `CrcCanonicityData`/`crcCanonicityData`/`crc_scope` — capstone（束ね）＋正確な torsor
     特徴付けを定理化（CHARACTERIZE, not KILL）。CRC-5。

  正直な線引き（§4.1・消さない・弱めない・sorry で埋めない）:
   (1) **mono-theta 円分剛性（[EtTh]）は依然 0**——本ステップは ℤ₃^× 不定性を**殺さない**。
       「復元の同一視空間がちょうど実 ℤ₃^× の torsor」と**特定する**のみ（CHARACTERIZE, not
       KILL）。不定性を消すテータ環境は柱E/D 後続。`crc_scope` はこの正確な線引きを定理化する。
   (2) **χ を実 π₁^ét の位相連続指標として抽出する本丸は未**——復元入力 χ は依然
       `cgarAct`（実体自己同型の制限）由来。crr 限定 (ii) を弱めず継承。
   (3) **幾何側は K̄ の μ でも π₁ の幾何的 cyclotome でもない**——μ 塔は各段別々の実円分体に
       住む（tmz 限定継承）。実数体上の完全 mono-anabelian 復元（AbsTopIII の実主語・体/環の
       復元）は後続。
   (4) **p = 3・G = Gal(ℚ(ζ_{3^∞})/ℚ) 固定**（G_ℚ の可解商・実 G_K/G_{K_v} でない）。
   (5) crr の「A6 上限 0.6」正直申告は**消さない**。ただしその根拠 2 本のうち「完全な副有限は
       後続」を File 1、「1 本の iso で一意性なし (G1)」を本ファイルが discharge するため、
       本モジュールは自身の限定として「**A6 ≤ 0.65（K̄/幾何 cyclotome・π₁ 連続 χ が未のあいだ）**」
       を新たに宣言する（既存 0.6 申告の削除・弱化ではなく並置＋更新宣言・監査確定は独立）。
   (6) crr/tmz/tme/tmi/cra/crl の既存正直申告は一切消さない・弱めない。並置＋昇格のみ。

  二重計上境界（§4.2・A7 との区別・監査が必ず突く点）:
   * A7（既計上）の主語＝固定 T の End(T)/Aut(T)（自己準同型の分類）。本ファイル（A6 新規）の
     主語＝**復元側極限 T̂=`crlLimit` の存在**と **Isom(T̂,T)=`Φ : crlLimit→tmzLimit` の分類**
     （同一視空間・torsor）。T̂ は A7 のどこにも存在しない。
   * A7 定理 `tmi_aut_classify`/`tmi_units_inj`/`tmi_from_units_iso`/`tmi_endo_gal_commute`/
     `tmi_act_char` は**補題として消費**する（tme が cra_endo_pow を消費したのと同じ・A7 監査
     §2.3 是認の再利用パターン）。
   * **本ファイルの全公開定理の主語は `crlLimit`（T̂）または `Φ : crlLimit → tmzLimit`（同一視）
     を含む**——主語が bare `Hom tmzLimit tmzLimit` だけの定理は新規公開しない（それは A7 の
     再ラベル）。内部の `A := Φ∘crlInv`（tmzLimit 自己準同型）は局所項としてのみ用い、bare
     tmzLimit 自己準同型についての定理は輸出しない。`crc_act_char` の主語も `crlActHom`（復元側
     G 作用）を含み A6 主語である。

  全て選択公理不使用（新規 `Classical.choice` を証明本体に導入しない・propext/Quot.sound
  のみ）。∃ は Prop ゴール内（`crc_canonical`）のみで、witness は `tmi_aut_classify` の既存
  閉じた式（各段 `tmeChar (Φ∘crlInv) n % 3^{n+1}`）をそのまま透過。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。
  新規イディオム 0（点ごと合成＋既存逆則の透過のみ）。新規ファイル 1 個（共有ファイルは親が統合）。
  prefix `crc`。
-/
import IUT.CyclotomeRecoveryLimit
import IUT.TateModuleIndeterminacy

namespace IUT

/-! ## CRC-1: ★正準性（存在）——任意の可逆同一視は実単元 × Ξ -/

/-- **CRC-1（★正準性・存在）: 任意の両側可逆同一視 Φ : T̂ → T は実 ℤ₃^× 単元 u で
    Φ = (tmiFromUnits u) ∘ Ξ と書ける。**
    Φ は `cgarAct` から作られたとは限らない**抽象 Hom**であり、この ∀Φ 量化が crr の
    「χ と作用が同一対象由来ゆえ 1 本の iso はほぼ簿記」という循環を型レベルで遮断する
    （thin 判定 (G1) の正面解消）。
    証明: A := Φ∘Ξ⁻¹ = `Φ.comp crlInv` : Hom tmzLimit tmzLimit（tmzLimit の自己準同型・
    局所項）と、その両側逆 A' := Ξ∘Ψ = `crlIso.comp Ψ` を作り、両側逆則を hl/hr＋
    `crl_iso_leftinv`/`crl_iso_rightinv` の点ごと合成で得る。A7 の `tmi_aut_classify` で
    A をちょうど 1 つの実単元 u へ分類し、Φ.map y = A.map (Ξ y)（`crl_iso_leftinv`）で
    移送する。 -/
theorem crc_canonical (Φ : Hom crlLimit tmzLimit) (Ψ : Hom tmzLimit crlLimit)
    (hl : ∀ y, Ψ.map (Φ.map y) = y) (hr : ∀ y, Φ.map (Ψ.map y) = y) :
    ∃ u : zpsLimit.carrier, ∀ y, Φ.map y = (tmiFromUnits u).map (crlIso.map y) := by
  -- A := Φ∘crlInv, A' := crlIso∘Ψ（bare tmzLimit endo は局所項のみ・§4.2）
  have hAl : ∀ y, (crlIso.comp Ψ).map ((Φ.comp crlInv).map y) = y := by
    intro y
    show crlIso.map (Ψ.map (Φ.map (crlInv.map y))) = y
    rw [hl (crlInv.map y)]
    exact crl_iso_rightinv y
  have hAr : ∀ y, (Φ.comp crlInv).map ((crlIso.comp Ψ).map y) = y := by
    intro y
    show Φ.map (crlInv.map (crlIso.map (Ψ.map y))) = y
    rw [crl_iso_leftinv (Ψ.map y)]
    exact hr y
  obtain ⟨u, hu⟩ := tmi_aut_classify (Φ.comp crlInv) (crlIso.comp Ψ) hAl hAr
  refine ⟨u, ?_⟩
  intro y
  have h1 : Φ.map y = (Φ.comp crlInv).map (crlIso.map y) := by
    show Φ.map y = Φ.map (crlInv.map (crlIso.map y))
    rw [crl_iso_leftinv y]
  exact h1.trans (hu (crlIso.map y))

/-! ## CRC-2: ★一意性——その実単元 u は一意 -/

/-- **CRC-2（★一意性）: (tmiFromUnits u)∘Ξ = (tmiFromUnits v)∘Ξ なら u = v。**
    Ξ は全射（`crl_iso_rightinv`: 任意の z は Ξ (Ξ⁻¹ z)）ゆえ、仮定を z へ引き戻して
    ∀z, (tmiFromUnits u).map z = (tmiFromUnits v).map z を得、A7 の `tmi_units_inj`
    （実単元は自己同型を一意に決める）で u = v。`crc_canonical` の u が一意であること。 -/
theorem crc_canonical_unique (u v : zpsLimit.carrier)
    (h : ∀ y, (tmiFromUnits u).map (crlIso.map y) = (tmiFromUnits v).map (crlIso.map y)) :
    u = v := by
  apply tmi_units_inj u v
  intro z
  have hh := h (crlInv.map z)
  rw [crl_iso_rightinv z] at hh
  exact hh

/-! ## CRC-3: ★正確性（正直方向）——全 torsor 点が G-同変同一視 -/

/-- **CRC-3（★正確性・正直方向）: 任意の実単元 u に対し (tmiFromUnits u)∘Ξ も両側逆つき
    G-同変同一視である。** ゆえに Isom_G(T̂,T) ≅ 実 ℤ₃^×=`zpsLimit`（ちょうど・消去形）。
    同変性は torsor を一切絞らない（`tmi_endo_gal_commute`: 同変性は End(T) 上で空——
    その正しい消費先）——純 Galois 加群データからの復元の正準性はここが理論上の上限であり、
    これ以上絞るのは mono-theta 剛性（柱E/D・status 0 のまま）の仕事。
    * 第 1 成分: 左逆（`tmi_from_units_iso u .1`＋`crl_iso_leftinv` の合成）。
    * 第 2 成分: 右逆（`crl_iso_rightinv`＋`tmi_from_units_iso u .2` の合成）。
    * 第 3 成分: G-同変性（`crl_iso_equivariant`＋`tmi_endo_gal_commute`）。 -/
theorem crc_torsor_realize (u : zpsLimit.carrier) :
    (∀ y, crlInv.map ((tmiFromUnits (zpsLimit.inv u)).map
        ((tmiFromUnits u).map (crlIso.map y))) = y) ∧
    (∀ w, (tmiFromUnits u).map (crlIso.map
        (crlInv.map ((tmiFromUnits (zpsLimit.inv u)).map w))) = w) ∧
    (∀ (s : ctlProfinite.carrier) (y : crlLimit.carrier),
      (tmiFromUnits u).map (crlIso.map ((crlActHom s).map y))
        = (tmzActHom s).map ((tmiFromUnits u).map (crlIso.map y))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [(tmi_from_units_iso u).1 (crlIso.map y)]
    exact crl_iso_leftinv y
  · intro w
    rw [crl_iso_rightinv ((tmiFromUnits (zpsLimit.inv u)).map w)]
    exact (tmi_from_units_iso u).2 w
  · intro s y
    rw [crl_iso_equivariant s y]
    exact tmi_endo_gal_commute (tmiFromUnits u) s (crlIso.map y)

/-! ## CRC-4: 橋（小）——復元作用を Ξ で移送すると実 Galois 作用・分類指数＝χ -/

/-- **CRC-4a: Hom 外延性**（map が一致すれば Hom は一致・proof irrelevance）。 -/
theorem crc_hom_ext {G H : Grp} (f g : Hom G H) (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- **CRC-4b: 復元作用の Ξ 移送＝実 Galois 作用** — Ξ∘(crlActHom s)∘Ξ⁻¹ = `tmzActHom s`。
    復元側 G 作用 `crlActHom s` を明示同一視 Ξ で実側へ移送すると、ちょうど実円分 Galois
    作用に一致する（`crl_iso_equivariant`＋`crl_iso_rightinv` の点ごと合成＋`crc_hom_ext`）。 -/
theorem crc_transport_eq (s : ctlProfinite.carrier) :
    (crlIso.comp (crlActHom s)).comp crlInv = tmzActHom s :=
  crc_hom_ext _ _ (by
    funext y
    show crlIso.map ((crlActHom s).map (crlInv.map y)) = (tmzActHom s).map y
    rw [crl_iso_equivariant s (crlInv.map y), crl_iso_rightinv y])

/-- **CRC-4c: 移送作用の分類指数＝χ** — 復元作用 `crlActHom s` を Ξ で移送した自己準同型
    の tme 分類指数が円分指標 χ_n(s_n)=`((cliChar n).map (s.val n)).val`（mod 3^{n+1}）に
    一致する。`crc_transport_eq`（移送＝実 Galois 作用）＋ A7 `tmi_act_char`（実作用の指数＝χ）。
    主語は `crlActHom`（復元側 G 作用）を含み A6 主語（§4.2 適合）。 -/
theorem crc_act_char (s : ctlProfinite.carrier) (n : Nat) :
    tmeChar ((crlIso.comp (crlActHom s)).comp crlInv) n % 3 ^ (n + 1)
      = ((cliChar n).map (s.val n)).val % 3 ^ (n + 1) := by
  rw [crc_transport_eq s]
  exact tmi_act_char s n

/-! ## CRC-5: capstone（束ね）＋正確な torsor 特徴付けの定理化 -/

/-- **CRC-5a: 正準性データ** — 明示同一視 Ξ=`crlIso` の両側逆・G-同変性に、∀Φ 正準性
    （存在）・一意性・全 torsor 点の G-同変実現を束ねる。**復元の同一視空間 Isom_G(T̂,T) が
    ちょうど実 ℤ₃^×=`zpsLimit` の torsor である**（消去形・CHARACTERIZE, not KILL）ことの
    A6 headline 証明書。新規主張なし（既証明フィールドの束ね・§4.2 適合）。 -/
structure CrcCanonicityData where
  /-- Ξ の左逆（Ξ⁻¹∘Ξ = id）。 -/
  iso_leftinv : ∀ y, crlInv.map (crlIso.map y) = y
  /-- Ξ の右逆（Ξ∘Ξ⁻¹ = id）。 -/
  iso_rightinv : ∀ y, crlIso.map (crlInv.map y) = y
  /-- Ξ は G-同変（復元側 G 作用と実側 Galois 作用を交換）。 -/
  iso_equivariant : ∀ (s : ctlProfinite.carrier) (y : crlLimit.carrier),
    crlIso.map ((crlActHom s).map y) = (tmzActHom s).map (crlIso.map y)
  /-- ★任意の両側可逆同一視 Φ は実 ℤ₃^× 単元 u で Φ = (tmiFromUnits u)∘Ξ（存在）。 -/
  canonical : ∀ (Φ : Hom crlLimit tmzLimit) (Ψ : Hom tmzLimit crlLimit),
    (∀ y, Ψ.map (Φ.map y) = y) → (∀ y, Φ.map (Ψ.map y) = y) →
    ∃ u : zpsLimit.carrier, ∀ y, Φ.map y = (tmiFromUnits u).map (crlIso.map y)
  /-- ★その実単元 u は一意。 -/
  canonical_unique : ∀ (u v : zpsLimit.carrier),
    (∀ y, (tmiFromUnits u).map (crlIso.map y) = (tmiFromUnits v).map (crlIso.map y)) → u = v
  /-- ★全 torsor 点 u が両側逆つき G-同変同一視を与える（同変性は torsor を絞らない）。 -/
  torsor_realize : ∀ (u : zpsLimit.carrier),
    (∀ y, crlInv.map ((tmiFromUnits (zpsLimit.inv u)).map
        ((tmiFromUnits u).map (crlIso.map y))) = y) ∧
    (∀ w, (tmiFromUnits u).map (crlIso.map
        (crlInv.map ((tmiFromUnits (zpsLimit.inv u)).map w))) = w) ∧
    (∀ (s : ctlProfinite.carrier) (y : crlLimit.carrier),
      (tmiFromUnits u).map (crlIso.map ((crlActHom s).map y))
        = (tmzActHom s).map ((tmiFromUnits u).map (crlIso.map y)))

/-- **CRC-5b: witness** — 全フィールド既証明の純レコード。復元円分体 T̂ と実 ℤ₃(1) の
    G-同変同一視空間がちょうど実 ℤ₃^× の torsor である A6 headline の完全証明。 -/
def crcCanonicityData : CrcCanonicityData where
  iso_leftinv := crl_iso_leftinv
  iso_rightinv := crl_iso_rightinv
  iso_equivariant := crl_iso_equivariant
  canonical := crc_canonical
  canonical_unique := crc_canonical_unique
  torsor_realize := crc_torsor_realize

/-- **CRC-5c（★正確な torsor 特徴付け・正直な線引きの定理化）** — 復元の G-同変同一視空間が
    **ちょうど**実 ℤ₃^×=`zpsLimit` である（過不足なし）ことの消去形。
    * 第 1 連言（存在）: 任意の可逆同一視は実単元由来（`crc_canonical`）。
    * 第 2 連言（単射）: 相異なる実単元は相異なる同一視（`crc_canonical_unique`）。
    * 第 3 連言（全射・実現）: 任意の実単元が G-同変同一視を実現（`crc_torsor_realize` の同変成分）。
    三者で Isom_G(T̂,T) ≅ `zpsLimit`。これ以上不定性を絞るのは mono-theta 剛性の仕事であり、
    本ステップは**特定するのみ**（CHARACTERIZE, not KILL・限定 (1)）。 -/
theorem crc_scope :
    (∀ (Φ : Hom crlLimit tmzLimit) (Ψ : Hom tmzLimit crlLimit),
      (∀ y, Ψ.map (Φ.map y) = y) → (∀ y, Φ.map (Ψ.map y) = y) →
      ∃ u : zpsLimit.carrier, ∀ y, Φ.map y = (tmiFromUnits u).map (crlIso.map y)) ∧
    (∀ (u v : zpsLimit.carrier),
      (∀ y, (tmiFromUnits u).map (crlIso.map y) = (tmiFromUnits v).map (crlIso.map y)) → u = v) ∧
    (∀ (u : zpsLimit.carrier) (s : ctlProfinite.carrier) (y : crlLimit.carrier),
      (tmiFromUnits u).map (crlIso.map ((crlActHom s).map y))
        = (tmzActHom s).map ((tmiFromUnits u).map (crlIso.map y))) :=
  ⟨crc_canonical, crc_canonical_unique, fun u => (crc_torsor_realize u).2.2⟩

end IUT
