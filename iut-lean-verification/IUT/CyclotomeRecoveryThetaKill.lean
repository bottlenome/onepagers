/-
  IUT/CyclotomeRecoveryThetaKill.lean — CRK（柱A6: mono-theta KILL torsor-reduction 橋）
  ——crt の「復元円分体 T̂=`crlLimit` と実 T=ℤ₃(1)=`tmzLimit` の G-同変同一視空間
    Isom_G(T̂,T) はちょうど実 ℤ₃^×=`zpsLimit` の基点自由 torsor」（`crt_ratio_exists`/
    `crt_ratio_unique`）を、q9mb の level-9 テータ剛性 kill（`q9mb_kill_mod9`：テータ両立
    クラスでは (u.val 1).val = 1）に接続し、**theta-admissible な同一視の全体は torsor の
    構造群が部分群 S = { u : (u.val 1).val = 1 }（≅ 1+9ℤ₃ の mod-9 描像）へ縮小する
    （torsor reduction）**ことを完全証明する。crt の「CHARACTERIZE（torsor の特定）」限定 (1)
    「mono-theta 剛性は依然 0」を、**mod-9 スライスに限って正面から接続**する一手。

  ── 主要成果の分類: **[実／(c) 承認済み足場]**（骨格・模型・代理でなく、既に本物として
     建った crt torsor（`crt_ratio_exists`/`crt_ratio_unique`・実 `zpsLimit`/`tmiFromUnits`/
     `crlLimit`）と q9mb theta-kill（`q9mb_kill_mod9`・実 μ₉ 橋 β₉ 上）を、**新機構・新イディオム
     ゼロで接続**する橋。名前付き実ターゲット = A6 の「復元同一視の rigidification」の忠実 mod-9
     切片。後続本物化計画: level-27 kill 接続（第 2 層 {1,10,19}）→ 実 wild 円分塔での full
     ℤ₃^× kill、および π₁ 連続 χ 抽出。設計は audit/pillar-A6-monotheta-kill-detail-2026-07-11.md
     §2–§3。消費のみ・再証明ゼロ（`q9mb_kill_mod9`・`q9mb_kill_new_layer`・`crt_ratio_exists`・
     `crt_ratio_unique`・`crt_from_units_mul`・`crt_div_unit`・`crc_canonical`・
     `crc_canonical_unique`・`tmi_units_inj` 経由）。toy 主語なし——主語は実 Isom_G(T̂,T) と
     実 `zpsLimit`。）

  **complete_pct 影響**: A6（mono-anabelian cyclotome 復元）——crt 限定 (1)「mono-theta 剛性
  は 0（CHARACTERIZE, not KILL）」を **mod-9 スライスで discharge**: theta-admissible な同一視
  の比は S = 1+9ℤ₃（mod-9 で 1）へ落ちる。crt にも q9mb にも無い新言明（A6 主語 Isom_G(T̂,T)
  の torsor reduction）だが証明実質は transport/glue ゆえ設計見込みは控えめ（s_A6 現 0.60 →
  中央 0.61–0.62・敵対的下限 0.60 据え置きも想定内・過大主張しない）。最終値は独立監査確定。
  A7 側 kill 本体（q9mb）の status は本ファイルで再主張しない（二重計上境界・新規主張は A6 のみ）。

  内容（CRK-0〜4・設計 §3 の梯子）:
   * `crk_one_val1`/`crk_mul_val1` — level-1 成分算術（one の成分=1・mul の成分展開）。CRK-0。
   * `crk_S_mul`/`crk_S_inv` — 部分群述語 S(u) := (u.val 1).val=1 の mul/inv 閉性。CRK-0。
   * `CrkAdm`/`crk_adm_iff_coord`/`crk_base_adm` — theta-admissible 述語・crc 座標での well-defined
     （`crc_canonical_unique` 消費）・基点 Ξ=`crlIso`（座標 = zpsLimit.one）の admissibility。CRK-1。
   * `crk_ratio_kill`（★核）— 両側可逆 Φ₁,Φ₂ の比 w（`crt_ratio_exists`）を theta 両立 φ が
     橋輸送で実現するなら (w.val 1).val=1（`q9mb_kill_mod9` glue）。CRK-2。
   * `crk_ratio_kill_new_layer`（★核）— 同上＋新層 {4,7} 排除（`q9mb_kill_new_layer` glue）。CRK-2。
   * `crk_torsor_reduction`（★★ headline）— theta-admissible な 2 同一視の比は S に落ちる
     （torsor reduction・存在：w₁=1·1⁻¹=1）。`crt_from_units_mul`/`crt_div_unit`/CRK-0 glue。CRK-3。
   * `crk_ratio_unique`（★★ headline）— その比は一意（`crt_ratio_unique` 透過・torsor 作用自由）。CRK-3。
   * `CrkReductionData`/`crkReductionData`/`crk_scope` — capstone（束ね）＋消去形。CRK-4。

  正直な限定（設計 §3・消さない・弱めない・sorry で埋めない・crt/q9mb/tmi の既存申告を継承）:
   (1) **縮小は mod-9 スライスのみ**——縮小後も S ≅（mod-9 で）1+9ℤ₃ の torsor が**まるごと
       残存（SURVIVES）**する。**rigidified ≠ canonical trivialization**: 同一視は mod 9 で pin
       されるだけで一点には落ちない。full ℤ₃^× kill は実 wild 円分塔（named future target・
       level-27 の q27* 連鎖で第 2 層 {1,10,19} まで拡張可能）が担う後続。
   (2) **level-9 theta 両立クラス相対**（q9mb 正直限定 5 の継承）——縮小は「level-9 theta
       実現可能な比」に対する言明。tmi の残存宣言（full ℤ₃^× は Galois 同変性だけでは絞れない）
       は不変更。
   (3) crt 限定 (2)(3)(4)（χ を実 π₁^ét の位相連続指標として抽出は未・幾何側は K̄ の μ でも
       π₁ の幾何 cyclotome でもない・p=3 かつ G=Gal(ℚ(ζ_{3^∞})/ℚ) 固定）を全て継承・並置。
       crr/crl/crc の「A6 ≤ 0.65（K̄/幾何 cyclotome・π₁ 連続 χ が未のあいだ）」帽子も**維持**
       ——本スライスは帽子の内側での前進であり帽子を外さない。
   (4) q=3⁹ 忠実部分ケース・endo 定式化・実テータ関数/π₁ 同定/大域 Galois = 0
       （q9mr/q9mb 継承）。

  やってはいけないこと（過大主張禁止）:「ℤ₃^× 不定性を殺した」と書かない（殺したのは (ℤ/9)^×
  商の比のみ）・「復元が canonical になった」と書かない（mod-9 pin のみ）・crt の CHARACTERIZE
  言明を書き換えない（並置＋接続のみ）・A7 側 status を再主張しない（kill 本体は A7 計上済）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無・
  #print axioms は [propext, Quot.sound] のみ）。∃ は Prop ゴール内のみ・witness は crc 座標の
  群積（crt と同じ閉式 `zpsLimit.mul u₂ (zpsLimit.inv u₁)`）で choice-free。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。
  omega は Nat/Int atom ゴールのみ。新規イディオム 0（成分展開・群律透過・既存 kill の消費のみ）。
  新規ファイル 1 個（共有ファイルは親が統合）。prefix `crk`。
-/
import IUT.CyclotomeRecoveryTorsor
import IUT.Q3Mu9TmzBridge

set_option maxRecDepth 8000

namespace IUT

/-! ## CRK-0: level-1 成分算術と部分群 S(u) := (u.val 1).val = 1 の閉性 -/

/-- **CRK-0a: one の level-1 成分 = 1**（`zpsLimit.one.val 1 = (zpsG 1).one`・`.val = 1`・rfl）。 -/
theorem crk_one_val1 : (zpsLimit.one.val 1).val = 1 := rfl

/-- **CRK-0b: mul の level-1 成分展開**（極限群 `limitGrp` の成分ごと積・(ℤ/3^2)^× の
    `a·b mod 9`）。 -/
theorem crk_mul_val1 (u v : zpsLimit.carrier) :
    ((zpsLimit.mul u v).val 1).val = (u.val 1).val * (v.val 1).val % 3 ^ 2 := rfl

/-- **CRK-0c: (u.val 1).val = 1 なら u.val 1 = (zpsG 1).one**（Subtype.ext・one.val=1 は defeq）。
    S(u) を level-1 の群単位元条件へ持ち上げる橋（mul/inv 閉性を群律で閉じるための核）。 -/
theorem crk_val1_one_of (u : zpsLimit.carrier) (hu : (u.val 1).val = 1) :
    u.val 1 = (zpsG 1).one :=
  Subtype.ext hu

/-- **CRK-0d: S は mul で閉じる**——(u.val 1).val=1 かつ (v.val 1).val=1 なら
    ((u·v).val 1).val=1（level-1 で one·one=one・`one_mul`）。 -/
theorem crk_S_mul (u v : zpsLimit.carrier)
    (hu : (u.val 1).val = 1) (hv : (v.val 1).val = 1) :
    ((zpsLimit.mul u v).val 1).val = 1 := by
  have h : (zpsLimit.mul u v).val 1 = (zpsG 1).one := by
    show (zpsG 1).mul (u.val 1) (v.val 1) = (zpsG 1).one
    rw [crk_val1_one_of u hu, crk_val1_one_of v hv]
    exact (zpsG 1).one_mul (zpsG 1).one
  rw [h]; rfl

/-- **CRK-0e: S は inv で閉じる**——(u.val 1).val=1 なら ((u⁻¹).val 1).val=1
    （level-1 で inv one=one・`Grp.inv_one`）。 -/
theorem crk_S_inv (u : zpsLimit.carrier) (hu : (u.val 1).val = 1) :
    ((zpsLimit.inv u).val 1).val = 1 := by
  have h : (zpsLimit.inv u).val 1 = (zpsG 1).one := by
    show (zpsG 1).inv (u.val 1) = (zpsG 1).one
    rw [crk_val1_one_of u hu]
    exact Grp.inv_one (zpsG 1)
  rw [h]; rfl

/-! ## CRK-1: theta-admissible 述語 CrkAdm と基点 Ξ=`crlIso` の admissibility -/

/-- **CRK-1a: theta-admissible 述語** `CrkAdm Φ` := ∃u, (Φ の crc 座標が u) ∧ (u ∈ S)。
    すなわち Φ : Isom_G(T̂,T) が「crc 座標 u が mod-9 で 1」であること。`crc_canonical_unique`
    により座標 u は一意ゆえ、条件 (u.val 1).val=1 は Φ の well-defined な性質。 -/
def CrkAdm (Φ : Hom crlLimit tmzLimit) : Prop :=
  ∃ u : zpsLimit.carrier,
    (∀ y, Φ.map y = (tmiFromUnits u).map (crlIso.map y)) ∧ (u.val 1).val = 1

/-- **CRK-1b: CrkAdm は crc 座標で well-defined**——Φ が座標 u を持つ（`crc_canonical` 形）とき、
    CrkAdm Φ ⟺ (u.val 1).val=1。逆向きは自明、順向きは `crc_canonical_unique` で座標一意性を
    使い、CrkAdm の証人座標 u' を u と同定する。 -/
theorem crk_adm_iff_coord (Φ : Hom crlLimit tmzLimit) (u : zpsLimit.carrier)
    (hu : ∀ y, Φ.map y = (tmiFromUnits u).map (crlIso.map y)) :
    CrkAdm Φ ↔ (u.val 1).val = 1 := by
  constructor
  · intro h
    obtain ⟨u', hu', hs'⟩ := h
    have huu : u' = u :=
      crc_canonical_unique u' u (fun y => by rw [← hu' y, ← hu y])
    rw [← huu]; exact hs'
  · intro h; exact ⟨u, hu, h⟩

/-- **CRK-1c: 実現写像 tmiFromUnits の単位元は恒等**（成分冪 y↦y^1=y・`mul_one`）。
    基点 admissibility（座標 = zpsLimit.one）の核。 -/
theorem crk_from_units_one (z : tmzLimit.carrier) :
    (tmiFromUnits zpsLimit.one).map z = z := by
  apply Subtype.ext
  funext n
  show (cmrGrp (n + 1) (by omega)).pow (z.val n) ((zpsLimit.one.val n).val) = z.val n
  show (cmrGrp (n + 1) (by omega)).mul (z.val n) ((cmrGrp (n + 1) (by omega)).one) = z.val n
  exact (cmrGrp (n + 1) (by omega)).mul_one (z.val n)

/-- **CRK-1（★基点 admissibility）: 基点 Ξ=`crlIso` は theta-admissible**——座標は
    zpsLimit.one（`crk_from_units_one`）で、one ∈ S（`crk_one_val1`）。torsor reduction の
    基点（base-free だが admissibility の起点は明示できる）。 -/
theorem crk_base_adm : CrkAdm crlIso :=
  ⟨zpsLimit.one, fun y => (crk_from_units_one (crlIso.map y)).symm, crk_one_val1⟩

/-! ## CRK-2: ★核——比の kill（crt の比 w に q9mb の theta-kill を通す） -/

/-- **CRK-2a（★核・比の kill）: 両側可逆な Φ₁,Φ₂ : Isom_G(T̂,T) の比 w（`crt_ratio_exists`）を、
    テータ両立自己準同型 φ（所属限定 hom hHom・所属保存 hMem・E_{3⁹}[9] 上恒等 hE9）が
    橋輸送で実現（hreal：任意の比 w に対する level-9 実現）するならば、比 w は S に落ちる
    （(w.val 1).val = 1）。** 証明: `crt_ratio_exists` で比 w を取り、`q9mb_kill_mod9` を w に適用。
    crt torsor と q9mb theta-kill は同一の Lean 対象 `zpsLimit`/`tmiFromUnits`/`tmzLimit` の
    上に居るので、対象翻訳・比較準同型は不要（設計 §2.1–2.2）。 -/
theorem crk_ratio_kill
    (Φ₁ Φ₂ : Hom crlLimit tmzLimit) (Ψ₁ Ψ₂ : Hom tmzLimit crlLimit)
    (h1l : ∀ y, Ψ₁.map (Φ₁.map y) = y) (h1r : ∀ y, Φ₁.map (Ψ₁.map y) = y)
    (h2l : ∀ y, Ψ₂.map (Φ₂.map y) = y) (h2r : ∀ y, Φ₂.map (Ψ₂.map y) = y)
    (φ : q9mtCar → q9mtCar)
    (hHom : ∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g'))
    (hMem : ∀ g, q9mtMem g → q9mtMem (φ g))
    (hE9 : ∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2)
    (hreal : ∀ (w : zpsLimit.carrier),
        (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) →
        ∀ t : tmzLimit.carrier,
          φ (q9mbInt (t.val 1)) = q9mbInt (((tmiFromUnits w).map t).val 1)) :
    ∃ w : zpsLimit.carrier,
      (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) ∧ (w.val 1).val = 1 := by
  obtain ⟨w, hw⟩ := crt_ratio_exists Φ₁ Φ₂ Ψ₁ Ψ₂ h1l h1r h2l h2r
  exact ⟨w, hw, q9mb_kill_mod9 w φ hHom hMem hE9 (hreal w hw)⟩

/-- **CRK-2b（★核・比の kill＋新層排除）: 上と同じ仮定の下で、比 w は S に落ち、かつ新層
    {4,7}＝(1+3ℤ₃)/(1+9ℤ₃) の非自明元を排除する。** `q9mb_kill_new_layer` を比 w に適用。
    §1 標的（新層の非自明元）が復元同一視の比から実際に死んだことの機械可読形。 -/
theorem crk_ratio_kill_new_layer
    (Φ₁ Φ₂ : Hom crlLimit tmzLimit) (Ψ₁ Ψ₂ : Hom tmzLimit crlLimit)
    (h1l : ∀ y, Ψ₁.map (Φ₁.map y) = y) (h1r : ∀ y, Φ₁.map (Ψ₁.map y) = y)
    (h2l : ∀ y, Ψ₂.map (Φ₂.map y) = y) (h2r : ∀ y, Φ₂.map (Ψ₂.map y) = y)
    (φ : q9mtCar → q9mtCar)
    (hHom : ∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g'))
    (hMem : ∀ g, q9mtMem g → q9mtMem (φ g))
    (hE9 : ∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2)
    (hreal : ∀ (w : zpsLimit.carrier),
        (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) →
        ∀ t : tmzLimit.carrier,
          φ (q9mbInt (t.val 1)) = q9mbInt (((tmiFromUnits w).map t).val 1)) :
    ∃ w : zpsLimit.carrier,
      (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) ∧
        (w.val 1).val = 1 ∧ (w.val 1).val ≠ 4 ∧ (w.val 1).val ≠ 7 := by
  obtain ⟨w, hw⟩ := crt_ratio_exists Φ₁ Φ₂ Ψ₁ Ψ₂ h1l h1r h2l h2r
  exact ⟨w, hw, q9mb_kill_new_layer w φ hHom hMem hE9 (hreal w hw)⟩

/-! ## CRK-3: ★★ headline——torsor reduction（構造群 ℤ₃^× → S） -/

/-- **CRK-3a（★★ headline・torsor reduction・存在）: theta-admissible な 2 同一視 Φ₁,Φ₂ の比は
    S に落ちる。** すなわち復元同一視空間 Isom_G(T̂,T) の ℤ₃^×-torsor 構造は、theta-admissible な
    部分集合に制限すると**構造群が S = {u : (u.val 1).val=1}（≅ mod-9 で 1+9ℤ₃）へ縮小する**。
    比の witness は crc 座標の群商 w = u₂·u₁⁻¹（`crt_ratio_exists` と同じ閉式・choice-free）で、
    比の等式は `crt_from_units_mul`＋`crt_div_unit`、成分 w₁ = 1·1⁻¹ = 1 は CRK-0 の S 閉性で。 -/
theorem crk_torsor_reduction
    (Φ₁ Φ₂ : Hom crlLimit tmzLimit)
    (h1 : CrkAdm Φ₁) (h2 : CrkAdm Φ₂) :
    ∃ w : zpsLimit.carrier,
      (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) ∧ (w.val 1).val = 1 := by
  obtain ⟨u₁, hu₁, hs₁⟩ := h1
  obtain ⟨u₂, hu₂, hs₂⟩ := h2
  refine ⟨zpsLimit.mul u₂ (zpsLimit.inv u₁), ?_, ?_⟩
  · intro y
    rw [hu₂ y, hu₁ y,
        ← crt_from_units_mul (zpsLimit.mul u₂ (zpsLimit.inv u₁)) u₁ (crlIso.map y),
        crt_div_unit u₂ u₁]
  · exact crk_S_mul u₂ (zpsLimit.inv u₁) hs₂ (crk_S_inv u₁ hs₁)

/-- **CRK-3b（★★ headline・torsor reduction・新層排除）: theta-admissible な 2 同一視の比は
    S に落ち、新層 {4,7} を排除する。** `crk_torsor_reduction` の (w.val 1).val=1 から新層の
    非自明元 4・7 が実際に排除される機械可読形。 -/
theorem crk_torsor_reduction_new_layer
    (Φ₁ Φ₂ : Hom crlLimit tmzLimit)
    (h1 : CrkAdm Φ₁) (h2 : CrkAdm Φ₂) :
    ∃ w : zpsLimit.carrier,
      (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) ∧
        (w.val 1).val = 1 ∧ (w.val 1).val ≠ 4 ∧ (w.val 1).val ≠ 7 := by
  obtain ⟨w, hw, hs⟩ := crk_torsor_reduction Φ₁ Φ₂ h1 h2
  exact ⟨w, hw, hs, by omega, by omega⟩

/-- **CRK-3c（★★ headline・torsor reduction・一意）: その比は一意（torsor 作用は自由）。**
    Φ₁ が右逆 Ψ₁ を持つ（全射）ので、2 つの比 w,w' が Φ₁ 上で同じ作用なら `crt_ratio_unique`
    （`tmi_units_inj` 経由）で w=w'。縮小後も比の一意性は保たれる（自由性は不変）。 -/
theorem crk_ratio_unique
    (Φ₁ Φ₂ : Hom crlLimit tmzLimit) (Ψ₁ : Hom tmzLimit crlLimit)
    (h1r : ∀ y, Φ₁.map (Ψ₁.map y) = y)
    (w w' : zpsLimit.carrier)
    (hw : ∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y))
    (hw' : ∀ y, Φ₂.map y = (tmiFromUnits w').map (Φ₁.map y)) :
    w = w' :=
  crt_ratio_unique Φ₁ Ψ₁ h1r w w' (fun y => by rw [← hw y, ← hw' y])

/-! ## CRK-4: capstone（束ね）＋消去形 -/

/-- **CRK-4a: torsor reduction データ** — S の群閉性（one/mul/inv）、基点 admissibility、
    theta-admissible な 2 同一視の比の S 縮小（存在・新層排除）と一意性、φ 経由の比 kill を
    束ねる。**復元の同一視空間 Isom_G(T̂,T) の ℤ₃^×-torsor が theta 剛性の下で構造群 S へ縮小
    する（mod-9 スライス）**ことの A6 証明書。 -/
structure CrkReductionData where
  /-- S は one を含む。 -/
  s_one : (zpsLimit.one.val 1).val = 1
  /-- S は mul で閉じる。 -/
  s_mul : ∀ (u v : zpsLimit.carrier),
    (u.val 1).val = 1 → (v.val 1).val = 1 → ((zpsLimit.mul u v).val 1).val = 1
  /-- S は inv で閉じる。 -/
  s_inv : ∀ (u : zpsLimit.carrier),
    (u.val 1).val = 1 → ((zpsLimit.inv u).val 1).val = 1
  /-- 基点 Ξ=`crlIso` は theta-admissible。 -/
  base_adm : CrkAdm crlIso
  /-- ★★ torsor reduction（存在）: theta-admissible な 2 同一視の比は S に落ちる。 -/
  reduction : ∀ (Φ₁ Φ₂ : Hom crlLimit tmzLimit),
    CrkAdm Φ₁ → CrkAdm Φ₂ →
    ∃ w : zpsLimit.carrier,
      (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) ∧ (w.val 1).val = 1
  /-- ★ 新層排除: 縮小後の比は {4,7} を排除。 -/
  reduction_new_layer : ∀ (Φ₁ Φ₂ : Hom crlLimit tmzLimit),
    CrkAdm Φ₁ → CrkAdm Φ₂ →
    ∃ w : zpsLimit.carrier,
      (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) ∧
        (w.val 1).val = 1 ∧ (w.val 1).val ≠ 4 ∧ (w.val 1).val ≠ 7
  /-- ★★ torsor reduction（一意）: その比は一意（自由性）。 -/
  reduction_unique : ∀ (Φ₁ Φ₂ : Hom crlLimit tmzLimit) (Ψ₁ : Hom tmzLimit crlLimit),
    (∀ y, Φ₁.map (Ψ₁.map y) = y) →
    ∀ (w w' : zpsLimit.carrier),
      (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) →
      (∀ y, Φ₂.map y = (tmiFromUnits w').map (Φ₁.map y)) → w = w'

/-- **CRK-4b: witness**（全フィールド既証明の純レコード）。復元円分体 T̂ と実 ℤ₃(1) の
    G-同変同一視空間の ℤ₃^×-torsor が、level-9 theta 剛性の下で構造群 S へ縮小する
    （mod-9 スライス）A6 headline の完全証明。 -/
def crkReductionData : CrkReductionData where
  s_one := crk_one_val1
  s_mul := crk_S_mul
  s_inv := crk_S_inv
  base_adm := crk_base_adm
  reduction := crk_torsor_reduction
  reduction_new_layer := crk_torsor_reduction_new_layer
  reduction_unique := fun Φ₁ Φ₂ Ψ₁ h1r w w' hw hw' =>
    crk_ratio_unique Φ₁ Φ₂ Ψ₁ h1r w w' hw hw'

/-- **CRK-4c（★★ headline・torsor reduction の消去形・正直な線引きの定理化）** — 復元の
    G-同変同一視空間 Isom_G(T̂,T) の ℤ₃^×-torsor が、level-9 theta 剛性の下で構造群 S
    （={u : (u.val 1).val=1}・≅ mod-9 で 1+9ℤ₃）へ縮小する（過不足なし）ことの消去形:
    * 第 1 連言（縮小・存在）: theta-admissible な 2 同一視の比は S に落ちる（`crk_torsor_reduction`）。
    * 第 2 連言（縮小・一意）: その比は一意（`crk_ratio_unique`・torsor 作用自由）。
    * 第 3 連言（基点）: 基点 Ξ=`crlIso` は admissible（`crk_base_adm`）。
    これ以上不定性を絞る（S 内部の 1+9ℤ₃ を殺す）のは level-27 以降の wild 円分塔の仕事であり、
    本ステップは torsor の構造群を **mod-9 スライスで S へ縮小するのみ**（rigidified ≠ canonical
    trivialization・限定 (1)）。 -/
theorem crk_scope :
    (∀ (Φ₁ Φ₂ : Hom crlLimit tmzLimit),
      CrkAdm Φ₁ → CrkAdm Φ₂ →
      ∃ w : zpsLimit.carrier,
        (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) ∧ (w.val 1).val = 1) ∧
    (∀ (Φ₁ Φ₂ : Hom crlLimit tmzLimit) (Ψ₁ : Hom tmzLimit crlLimit),
      (∀ y, Φ₁.map (Ψ₁.map y) = y) →
      ∀ (w w' : zpsLimit.carrier),
        (∀ y, Φ₂.map y = (tmiFromUnits w).map (Φ₁.map y)) →
        (∀ y, Φ₂.map y = (tmiFromUnits w').map (Φ₁.map y)) → w = w') ∧
    CrkAdm crlIso :=
  ⟨crk_torsor_reduction, crk_ratio_unique, crk_base_adm⟩

end IUT
