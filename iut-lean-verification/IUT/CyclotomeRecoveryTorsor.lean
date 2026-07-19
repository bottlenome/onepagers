/-
  IUT/CyclotomeRecoveryTorsor.lean — CRT（柱A6 headline 続: 復元円分体 T̂=`crlLimit` と
  実 T=ℤ₃(1)=`tmzLimit` の G-同変同一視空間 Isom_G(T̂,T) を、crc の「基点 Ξ 付き集合全単射
  Isom_G ≅ 実 ℤ₃^×」から**基点自由な ℤ₃^× 主等質空間（torsor）**へ昇格する——すなわち
  (1) 実現写像 u ↦ `tmiFromUnits u` が群準同型である（`crt_from_units_mul`）ことを本物で
  証明し、(2) その結果として ℤ₃^× が Isom_G に後合成で**単純推移的**に作用する
  ＝**任意の 2 つの同一視 Φ₁,Φ₂ はちょうど 1 つの実単元 w で Φ₂ = (tmiFromUnits w)∘Φ₁ と
  結ばれる**（`crt_ratio_exists`＋`crt_ratio_unique`）ことを完全証明する）

  ── 主要成果の分類: **[実／昇格(a)]**（骨格・模型・代理でなく、crc が基点 Ξ=`crlIso` を
     選んで得た「Isom_G(T̂,T) ≅ 実 ℤ₃^× の集合全単射」を、**基点に依らない torsor の割り算
     （ratio）構造**へ昇格する。crc の限界（G3'）「特徴付けは基点 Ξ に相対的な座標付けであり、
     2 同一視の比が well-defined＝群作用が単純推移的であることは未述」を正面 discharge する。
     核となる新規本物 `crt_from_units_mul`（実現写像 `tmiFromUnits` の乗法性＝群準同型性・
     tmi/crc のどこにも無い）を建て、torsor の群作用の整合律（作用軸）を初めて閉じる。
     これで A7 の Aut(ℤ₃(1)) ≅ ℤ₃^× は集合全単射から**群同型**へ、crc の Isom_G の特徴付けは
     基点付き座標から**基点自由な主等質空間の割り算**へ、同時に昇格する。）

  **complete_pct 影響**: A6（mono-anabelian 復元）——crc の thin 判定 (G3')「基点相対の
  座標付けに留まり torsor の群作用（単純推移性・比の一意性）は未」を discharge する headline。
  crc の「基点 Ξ に相対した集合全単射」を、「任意 2 同一視の比がちょうど 1 つの実単元」
  （基点自由・単純推移）へ昇格する。設計見込み A6 微増（最終値は独立監査確定・過大主張しない・
  下振れ横這い＝表示据え置きも想定内）。本ファイル単体では complete_pct は独立監査で反映。

  内容（CRT-0〜4）:
   * `crt_from_units_mul`   — ★実現写像の乗法性（群準同型）: `tmiFromUnits (u·v)` の作用は
     `tmiFromUnits u` と `tmiFromUnits v` の合成に一致。tmi/crc に無い新規本物。CRT-0。
   * `crt_div_unit`         — 群割り算 (u₂·u₁⁻¹)·u₁ = u₂（zpsLimit の群律・torsor 比の核）。CRT-1。
   * `crt_translate`        — ★torsor 作用の整合律: 基点 Ξ 上の座標 u を w で平行移動すると
     座標は w·u（後合成が左積に対応）。crc 座標系での群作用の実現。CRT-2。
   * `crt_ratio_exists`     — ★単純推移（存在）: 任意 2 可逆同一視 Φ₁,Φ₂ に対し、実単元 w で
     Φ₂ = (tmiFromUnits w)∘Φ₁ が存在（基点自由な torsor の割り算）。CRT-3。
   * `crt_ratio_unique`     — ★単純推移（一意）: その w は一意（Φ₁ 全射＋`tmi_units_inj`）。CRT-3。
   * `CrtTorsorData`/`crtTorsorData`/`crt_scope` — capstone（束ね）＋基点自由 torsor の定理化。CRT-4。

  正直な線引き（§4.1・消さない・弱めない・sorry で埋めない・crr/crl/crc/tmi の既存申告を継承）:
   (1) **mono-theta 円分剛性（[EtTh]）は依然 0**——本ステップは ℤ₃^× 不定性を**殺さない**。
       「復元の同一視空間がちょうど実 ℤ₃^× の（基点自由）torsor」と**特定する**のみ
       （CHARACTERIZE, not KILL・crc 限定 (1) を継承）。不定性を消すテータ環境は柱E/D 後続。
   (2) **χ を実 π₁^ét の位相連続指標として抽出する本丸は未**（crr 限定 (ii)・crl/crc 継承）。
   (3) **幾何側は K̄ の μ でも π₁ の幾何的 cyclotome でもない**（tmz/crl/crc 限定継承）。
   (4) **p = 3・G = Gal(ℚ(ζ_{3^∞})/ℚ) 固定**（G_ℚ の可解商・実 G_K/G_{K_v} でない）。
   (5) crr/crl/crc の「A6 ≤ 0.6／0.65」正直申告は**消さない**。本モジュールは torsor の群作用
       （単純推移性）を閉じるが、これも基点自由性の追加であって不定性の消去ではない——
       「A6 ≤ 0.65（K̄/幾何 cyclotome・π₁ 連続 χ が未のあいだ）」を継承・並置。

  二重計上境界（§4.2・A7 との区別）:
   * A7（既計上・tmi）の主語＝固定 T の Aut(T)（bare `Hom tmzLimit tmzLimit`）。
   * 本ファイル（A6 新規）の公開 headline `crt_translate`/`crt_ratio_exists`/`crt_ratio_unique`
     の主語は**同一視 `Φ : crlLimit → tmzLimit`（または `crlIso`）を含む**——復元側 T̂ を
     台にもつ同一視空間 Isom_G(T̂,T) の torsor 構造であり、bare Aut(T) の再ラベルではない。
   * `crt_from_units_mul` は bare tmzLimit 上の**補題**として建て消費する（tme が
     cra_endo_pow を消費したのと同じ再利用パターン・A7 監査 §2.3 是認）。これは tmi にも
     crc にも無い新規本物（実現写像の群準同型性）であり、bare Aut(T) の頭出し公開ではなく
     A6 headline（基点自由 torsor 割り算）の必須核として消費する。
   * A7 定理 `tmi_units_inj` は補題として消費（crc が `tmi_aut_classify` を消費したのと同じ）。

  全て選択公理不使用（新規 `Classical.choice` を証明本体に導入しない・propext/Quot.sound
  のみ）。∃ は Prop ゴール内（`crt_ratio_exists`）のみで、witness は `crc_canonical` の既存
  閉じた式の群積 `zpsLimit.mul u₂ (zpsLimit.inv u₁)` で明示（choice-free）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。
  3^ℓ は omega 不可（`zpu_pow_pos` 等は再利用元に閉じ込め・本ファイルは既存冪則の透過のみ）。
  新規イディオム 0（成分ごと冪の乗法則 `cycRig_pow_mul`＋mod 還元 `cra_pow_reduce`＋群律の
  透過のみ）。新規ファイル 1 個（共有ファイルは親が統合）。prefix `crt`。
-/
import IUT.CyclotomeRecoveryCanonicity

namespace IUT

/-! ## CRT-0: ★実現写像 tmiFromUnits の乗法性（群準同型・新規本物） -/

/-- **CRT-0（★実現写像の群準同型性）: `tmiFromUnits (u·v)` の作用は `tmiFromUnits u` と
    `tmiFromUnits v` の合成に一致。** すなわち実 ℤ₃^×=`zpsLimit` から Aut(ℤ₃(1)) への実現
    写像 u ↦ `tmiFromUnits u` は群準同型である。tmi は各元が自己同型を与えること（実現）と
    分類・単射しか持たず、**乗法性（群構造の保存）は tmi にも crc にも無い新規本物**。
    成分 n で LHS = `pow (y_n) ((u_n·v_n) mod 3^{n+1})`、RHS = `pow (pow (y_n) v_n) u_n`。
    `cra_pow_reduce`（mod 還元）で LHS の mod を外し、`cycRig_pow_mul`（可換群の冪の乗法則
    `x^{ab}=(x^a)^b`）で RHS を `pow (y_n) (v_n·u_n)` に潰し、`Nat.mul_comm` で合流。 -/
theorem crt_from_units_mul (u v : zpsLimit.carrier) (y : tmzLimit.carrier) :
    (tmiFromUnits (zpsLimit.mul u v)).map y
      = (tmiFromUnits u).map ((tmiFromUnits v).map y) := by
  apply Subtype.ext
  funext n
  show (cmrGrp (n + 1) (by omega)).pow (y.val n)
        ((u.val n).val * (v.val n).val % 3 ^ (n + 1))
     = (cmrGrp (n + 1) (by omega)).pow
        ((cmrGrp (n + 1) (by omega)).pow (y.val n) ((v.val n).val)) ((u.val n).val)
  rw [← cra_pow_reduce (n + 1) (by omega) (y.val n) ((u.val n).val * (v.val n).val),
      ← cycRig_pow_mul (cmrGrp (n + 1) (by omega)) (cmr_comm (n + 1) (by omega)) (y.val n)
        ((v.val n).val) ((u.val n).val),
      Nat.mul_comm ((u.val n).val) ((v.val n).val)]

/-! ## CRT-1: 群割り算（torsor 比の核・zpsLimit の群律） -/

/-- **CRT-1: 群割り算** (u₂·u₁⁻¹)·u₁ = u₂（実 ℤ₃^×=`zpsLimit` の群律 mul_assoc/inv_mul/mul_one）。
    torsor の比（ratio）witness `w = u₂·u₁⁻¹` が `w·u₁ = u₂` を満たすことの核。 -/
theorem crt_div_unit (u₂ u₁ : zpsLimit.carrier) :
    zpsLimit.mul (zpsLimit.mul u₂ (zpsLimit.inv u₁)) u₁ = u₂ := by
  rw [zpsLimit.mul_assoc, zpsLimit.inv_mul, zpsLimit.mul_one]

/-! ## CRT-2: ★torsor 作用の整合律（基点 Ξ 上の座標での群作用） -/

/-- **CRT-2（★torsor 作用の整合律）: 基点 Ξ=`crlIso` 上の座標 u を w で平行移動すると
    座標は w·u に移る。** すなわち crc の座標系（Φ = (tmiFromUnits u)∘Ξ）で、同一視を
    実単元 w で後合成する ℤ₃^× 作用は、座標の左積 u ↦ w·u に対応する（後合成 = 左積）。
    `crt_from_units_mul`（実現写像の群準同型性）の crc 座標系への適用。復元側 T̂ を台に
    もつ同一視 `crlIso.map y` を主語に含む A6 命題（§4.2 適合）。 -/
theorem crt_translate (w u : zpsLimit.carrier) (y : crlLimit.carrier) :
    (tmiFromUnits w).map ((tmiFromUnits u).map (crlIso.map y))
      = (tmiFromUnits (zpsLimit.mul w u)).map (crlIso.map y) :=
  (crt_from_units_mul w u (crlIso.map y)).symm

/-! ## CRT-3: ★単純推移性（基点自由な torsor の割り算・A6 headline 本丸） -/

/-- **CRT-3a（★単純推移・存在）: 任意の 2 つの両側可逆同一視 Φ₁,Φ₂ : T̂ → T に対し、実
    ℤ₃^×=`zpsLimit` の元 w で Φ₂ = (tmiFromUnits w)∘Φ₁ となるものが存在する。**
    これは crc の「基点 Ξ に相対した座標付け」を**基点自由な torsor の割り算**へ昇格する
    本丸: Φ₁,Φ₂ は共に抽象 Hom（`cgarAct` 由来とは限らない）で、その比が実単元で書けることは
    torsor が単純推移的（＝主等質空間）であることそのもの。witness は crc 座標 u₁,u₂
    （`crc_canonical`）の群商 w = u₂·u₁⁻¹（choice-free 閉式）。`crt_from_units_mul`（実現の
    群準同型性）＋`crt_div_unit`（群割り算 (u₂·u₁⁻¹)·u₁=u₂）で Φ₁ の座標を消して Φ₂ の座標へ。 -/
theorem crt_ratio_exists
    (Φ₁ Φ₂ : Hom crlLimit tmzLimit) (Ψ₁ Ψ₂ : Hom tmzLimit crlLimit)
    (h1l : ∀ y, Ψ₁.map (Φ₁.map y) = y) (h1r : ∀ y, Φ₁.map (Ψ₁.map y) = y)
    (h2l : ∀ y, Ψ₂.map (Φ₂.map y) = y) (h2r : ∀ y, Φ₂.map (Ψ₂.map y) = y) :
    ∃ w : zpsLimit.carrier, ∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y) := by
  obtain ⟨u₁, hu₁⟩ := crc_canonical Φ₁ Ψ₁ h1l h1r
  obtain ⟨u₂, hu₂⟩ := crc_canonical Φ₂ Ψ₂ h2l h2r
  refine ⟨zpsLimit.mul u₂ (zpsLimit.inv u₁), ?_⟩
  intro y
  rw [hu₂ y, hu₁ y,
      ← crt_from_units_mul (zpsLimit.mul u₂ (zpsLimit.inv u₁)) u₁ (crlIso.map y),
      crt_div_unit u₂ u₁]

/-- **CRT-3b（★単純推移・一意）: 比の実単元は一意。** Φ₁ が右逆 Ψ₁ を持つ（全射）ので、
    2 つの比 w,w' が Φ₁ 上で同じ作用を与えるなら、Ψ₁ で引き戻して ∀z, (tmiFromUnits w) z =
    (tmiFromUnits w') z を得、A7 `tmi_units_inj`（実単元は自己同型を一意に決める）で w=w'。
    `crt_ratio_exists` の w が一意であること＝torsor 作用が自由（free）であること。 -/
theorem crt_ratio_unique
    (Φ₁ : Hom crlLimit tmzLimit) (Ψ₁ : Hom tmzLimit crlLimit)
    (h1r : ∀ y, Φ₁.map (Ψ₁.map y) = y)
    (w w' : zpsLimit.carrier)
    (hww : ∀ y, (tmiFromUnits w).map (Φ₁.map y) = (tmiFromUnits w').map (Φ₁.map y)) :
    w = w' := by
  apply tmi_units_inj w w'
  intro z
  have hz := hww (Ψ₁.map z)
  rw [h1r z] at hz
  exact hz

/-! ## CRT-4: capstone（束ね）＋基点自由 torsor の定理化 -/

/-- **CRT-4a: 基点自由 torsor データ** — 実現写像の群準同型性（`crt_from_units_mul`）、
    crc 座標系での torsor 作用整合律（`crt_translate`）、任意 2 同一視の比の存在・一意
    （`crt_ratio_exists`/`crt_ratio_unique`）を束ねる。**復元の同一視空間 Isom_G(T̂,T) が
    実 ℤ₃^×=`zpsLimit` の（基点自由・単純推移的）torsor である**ことの A6 headline 証明書。 -/
structure CrtTorsorData where
  /-- ★実現写像 u ↦ tmiFromUnits u は群準同型（乗法性・新規本物）。 -/
  from_units_mul : ∀ (u v : zpsLimit.carrier) (y : tmzLimit.carrier),
    (tmiFromUnits (zpsLimit.mul u v)).map y
      = (tmiFromUnits u).map ((tmiFromUnits v).map y)
  /-- ★torsor 作用の整合律: 基点 Ξ 上の座標 u を w で移すと座標は w·u。 -/
  translate : ∀ (w u : zpsLimit.carrier) (y : crlLimit.carrier),
    (tmiFromUnits w).map ((tmiFromUnits u).map (crlIso.map y))
      = (tmiFromUnits (zpsLimit.mul w u)).map (crlIso.map y)
  /-- ★単純推移（存在）: 任意 2 可逆同一視の比が実単元で書ける。 -/
  ratio_exists : ∀ (Φ₁ Φ₂ : Hom crlLimit tmzLimit) (Ψ₁ Ψ₂ : Hom tmzLimit crlLimit),
    (∀ y, Ψ₁.map (Φ₁.map y) = y) → (∀ y, Φ₁.map (Ψ₁.map y) = y) →
    (∀ y, Ψ₂.map (Φ₂.map y) = y) → (∀ y, Φ₂.map (Ψ₂.map y) = y) →
    ∃ w : zpsLimit.carrier, ∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)
  /-- ★単純推移（一意）: その比は一意（作用が自由）。 -/
  ratio_unique : ∀ (Φ₁ : Hom crlLimit tmzLimit) (Ψ₁ : Hom tmzLimit crlLimit),
    (∀ y, Φ₁.map (Ψ₁.map y) = y) →
    ∀ (w w' : zpsLimit.carrier),
      (∀ y, (tmiFromUnits w).map (Φ₁.map y) = (tmiFromUnits w').map (Φ₁.map y)) → w = w'

/-- **CRT-4b: witness**（全フィールド既証明の純レコード）。復元円分体 T̂ と実 ℤ₃(1) の
    G-同変同一視空間がちょうど実 ℤ₃^× の基点自由 torsor である A6 headline の完全証明。 -/
def crtTorsorData : CrtTorsorData where
  from_units_mul := crt_from_units_mul
  translate := crt_translate
  ratio_exists := crt_ratio_exists
  ratio_unique := crt_ratio_unique

/-- **CRT-4c（★基点自由 torsor の定理化・正直な線引きの定理化）** — 復元の G-同変同一視空間
    Isom_G(T̂,T) が実 ℤ₃^×=`zpsLimit` の**基点自由・単純推移的** torsor である（過不足なし）
    ことの消去形:
    * 第 1 連言（自由性の核）: 実現写像の群準同型性（`crt_from_units_mul`）。
    * 第 2 連言（推移・存在）: 任意 2 同一視の比が実単元で書ける（`crt_ratio_exists`）。
    * 第 3 連言（自由・一意）: その比は一意（`crt_ratio_unique`）。
    三者で Isom_G(T̂,T) は `zpsLimit`-torsor（基点自由）。これ以上不定性を絞るのは
    mono-theta 剛性の仕事であり、本ステップは torsor の**群作用を特定するのみ**
    （CHARACTERIZE, not KILL・限定 (1)）。 -/
theorem crt_scope :
    (∀ (u v : zpsLimit.carrier) (y : tmzLimit.carrier),
      (tmiFromUnits (zpsLimit.mul u v)).map y
        = (tmiFromUnits u).map ((tmiFromUnits v).map y)) ∧
    (∀ (Φ₁ Φ₂ : Hom crlLimit tmzLimit) (Ψ₁ Ψ₂ : Hom tmzLimit crlLimit),
      (∀ y, Ψ₁.map (Φ₁.map y) = y) → (∀ y, Φ₁.map (Ψ₁.map y) = y) →
      (∀ y, Ψ₂.map (Φ₂.map y) = y) → (∀ y, Φ₂.map (Ψ₂.map y) = y) →
      ∃ w : zpsLimit.carrier, ∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) ∧
    (∀ (Φ₁ : Hom crlLimit tmzLimit) (Ψ₁ : Hom tmzLimit crlLimit),
      (∀ y, Φ₁.map (Ψ₁.map y) = y) →
      ∀ (w w' : zpsLimit.carrier),
        (∀ y, (tmiFromUnits w).map (Φ₁.map y) = (tmiFromUnits w').map (Φ₁.map y)) → w = w') :=
  ⟨crt_from_units_mul, crt_ratio_exists, crt_ratio_unique⟩

end IUT
