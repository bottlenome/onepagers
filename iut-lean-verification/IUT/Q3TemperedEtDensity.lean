/-
  IUT/Q3TemperedEtDensity.lean — A5d′-N1（柱A A5: 実 tempered π₁ の π₁^ét における
    位相的稠密性 かつ 真部分性 — q3tpec 正直限定 (3) の正面 discharge）

  ── 主要成果の分類: **[実／(b) 本物の先行建設]**。A5d′ `Q3TemperedPi1Deepen.lean`（q3tpec）は
     実比較射 q3tpEtComp : π₁^{temp,(3)} = ℤ₃(1)×ℤ → π₁^{ét,(3)} = ℤ₃(1)×ℤ₃ を建て、
       (2) 各有限段 ℤ/3^n での全射（＝「稠密」の**代数的影**）、
       (3) 全体 ℤ₃ への非全射（tempered ⊊ étale）
     を実主語（tmzLimit・intGrp・実 Zp 3・実 toZp 3）の上で証明したが、そのヘッダ**正直限定
     (3)** は明示していた:「『稠密』は代数的影のみ——位相・p 進位相を本ファイルは一切使わない。
     …**位相的稠密性（閉包＝全体）は主張しない**（Zp の位相は M15/M25 にあるが本ファイルでは
     接続しない）」。本モジュールは M15 の実位相資産（`limitTopology`・`prodTopology`・近傍基
     定理 `cylinder_nbhd_basis`（M15-6）・開長方形近傍基 `prod_open_rect_basis`（M18-3））を
     **消費**して、その named defer を**正面から discharge** する:

       q3tpEtComp の像は π₁^{ét,(3)} の直積副有限位相
       `prodTopology (limitTopology tmzSystem) (limitTopology (padicSystem 3))` に関して
       **位相的に稠密**（＝任意の基本開近傍が像と交わる・各点近傍定式化）**かつ真部分**
       （witness (1, ω) が像に属さない）である —— headline `q3tpd_dense_proper`。

     すなわち q3tpec の「各有限商で全射」という**代数的影**を、M15 の実物の位相の上で
     **本物の位相文**「tempered π₁ は étale π₁ の**真の稠密部分群**」へ昇格させる。toy 主語なし。

  complete_pct 影響: **A5 N1（副・s_A5 0.23→・独立監査確定が条件・保守見込み +0.01〜+0.02）**。
  q3tpec 正直限定 (3) の named defer（位相的稠密性）の実 discharge。真水（新規主張）:
  (i)   有限レベル代表による柱到達 `q3tpd_toZp_hits_level`（∀ k c, ∃ a, (toZp a).val k = c・
        Quot.ind 代表元＝choice-free）、
  (ii)  toZp 像の Zp 位相稠密性 `q3tpd_toZp_dense`（cylinder_nbhd_basis の実消費・
        「∀ 開 U, ∀ x∈U, ∃ a, (toZp a)∈U」）、
  (iii) **新規一般補題**: 直積副有限位相の**二重柱状近傍基** `q3tpd_prod_nbhd_basis`
        （prod_open_rect_basis で開長方形へ、両因子で cylinder_nbhd_basis を回して
        「各因子で有限レベル一致 ⟹ 属する」二重柱に落とす・唯一のやや新しい一般補題）、
  (iv)  **比較射像の位相的稠密性** `q3tpd_image_dense`（μ 方向は恒等ゆえ y.1 で当たり・
        離散方向は q3tpd_toZp_hits_level で整数代表を当てる）、
  (v)   真部分性の witness `q3tpd_proper_witness`（(1, ω)∉像・q3tp_disc_not_surjective の実消費）、
  (vi)  **旗艦** `q3tpd_dense_proper`: 稠密（各基本開近傍が像と交わる）**かつ**真部分
        （像に属さない点が存在）——「tempered ⊊ étale・しかも位相的に稠密」の完全な位相文、
  (vii) 束ね `Q3TemperedEtDensityData` / `q3tpdData` / `q3tpd_exists`。

  正直な限定（§4 規約・消去/弱化しない・q3tpec/A5b/A4/A5c の既存限定を全て継承の上に追記のみ）:
  (1) **稠密性は cylinder / 開長方形（＝副有限極限位相）の基本開集合基に関する各点近傍定式化**
      であり、完全な metric / Berkovich 位相ではない。ここで使う位相は **étale 側の副有限
      （pro-3）位相**であって **tempered 位相ではない**——A5 恒久上限 **0.35–0.4**
      （Berkovich/rigid 被覆理論・tempered π₁ の「定義」は依然外部）は本スライスの後も**不変**。
  (2) ここで扱う tempered π₁ は既建設の **deck-ℤ / theta-class 構造**（tmzLimit×intGrp）であり、
      Berkovich 解析構造つきの full π₁^temp ではない（A5b 限定 (2) 継承）。
  (3) **稠密の正直文**: 「稠密」は「開集合ごとの交わり（各点近傍定式化）」であり、閉包演算子・
      完備性・コンパクト性の一般論は主張しない（M15 の正直申告を継承）。真部分は「像に属さない
      点が存在する」の集合論的言明（q3tpec-4 の witness を消費）。
  (4) q3tpec / tempered-π₁ の帽子を全継承: 依然 **pro-3**（full ẑ(1)・全素数 l は未達）・
      **σ-only Galois**（外 G_{ℚ₃} 作用・Weil ペアリング・anabelian 逆再構成はゼロ）・
      **q = 3 固定**・実テータ関数 0・cuspidalization 本体 0・担体は群提示（A2/A8 継承）。
  (5) 既存 q3tpec ヘッダ限定 (3) の本文は**書き換えない**（§4 規約）——本ファイル側で
      「その named defer を discharge した」と記す。q3tpec は稠密の代数的影までを正直に述べ、
      本モジュールが M15 位相を接続して位相文へ昇格させる、という積層関係を保つ。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  各主要 def/theorem の #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。
-/
import IUT.Q3TemperedPi1Deepen
import IUT.Topology
import IUT.Compactness

namespace IUT

/-! ## q3tpd-0: 有限レベル代表による柱到達（choice-free の核） -/

/-- **q3tpd-0a: 有限レベル到達** — 任意の有限商 c ∈ ℤ/p^k は toZp p の像のレベル k で当たる。
    c の整数代表 a（Quot.ind）に対し ((toZp p).map a).val k = c は定義計算（rfl）。
    q3tpec-3 の各有限段全射の位相稠密性への橋渡し核。 -/
theorem q3tpd_toZp_hits_level (p : Nat) (k : Nat) (c : (zmod (p ^ k)).carrier) :
    ∃ a : Int, ((toZp p).map a).val k = c := by
  induction c using Quot.ind
  rename_i a
  exact ⟨a, rfl⟩

/-- **q3tpd-0b（★）: toZp 像は Zp p の副有限位相で稠密** — 極限位相の任意の開集合 U と
    x ∈ U に対し、ある整数 a で (toZp p).map a ∈ U。M15-6 `cylinder_nbhd_basis` で
    レベル k の柱に落とし、x.val k の整数代表を q3tpd_toZp_hits_level で当てる。
    q3tpec が「代数的影」に留めた稠密性の、実位相 limitTopology 上での各点近傍定式化。 -/
theorem q3tpd_toZp_dense (p : Nat) (U : (Zp p).carrier → Prop)
    (hU : (limitTopology (padicSystem p)).IsOpen U)
    (x : (Zp p).carrier) (hx : U x) :
    ∃ a : Int, U ((toZp p).map a) := by
  obtain ⟨k, hk⟩ := cylinder_nbhd_basis (padicSystem p) 0 U hU x hx
  obtain ⟨a, ha⟩ := q3tpd_toZp_hits_level p k (x.val k)
  exact ⟨a, hk ((toZp p).map a) ha⟩

/-! ## q3tpd-1: 直積副有限位相の二重柱状近傍基（★ 唯一のやや新しい一般補題） -/

/-- **q3tpd-1（★）: 二重柱状近傍基** — 二つの逆極限の直積 `(limitGrp Sα)×(limitGrp Sβ)` の
    直積副有限位相の任意の開集合 W と点 p ∈ W に対し、あるレベル kα・kβ が存在して
    「第1因子でレベル kα・第2因子でレベル kβ が p と一致する元」はすべて W に入る。
    M18-3 `prod_open_rect_basis` で開長方形 U×V へ落とし、各因子で M15-6
    `cylinder_nbhd_basis` を回して柱状条件に還元する（両因子の有向性が核）。
    `cylinder_nbhd_basis` の直積版——q3tpec 限定 (3) の直積稠密性 discharge の土台。 -/
theorem q3tpd_prod_nbhd_basis (Sα Sβ : InverseSystem) (iα : Sα.Idx) (iβ : Sβ.Idx)
    (W : (limitGrp Sα).carrier × (limitGrp Sβ).carrier → Prop)
    (hW : (prodTopology (limitTopology Sα) (limitTopology Sβ)).IsOpen W)
    (p : (limitGrp Sα).carrier × (limitGrp Sβ).carrier) (hp : W p) :
    ∃ (kα : Sα.Idx) (kβ : Sβ.Idx),
      ∀ q : (limitGrp Sα).carrier × (limitGrp Sβ).carrier,
        q.1.val kα = p.1.val kα → q.2.val kβ = p.2.val kβ → W q := by
  obtain ⟨U, V, hU, hV, hpU, hpV, hsub⟩ :=
    prod_open_rect_basis (limitTopology Sα) (limitTopology Sβ) W hW p hp
  obtain ⟨kα, hkα⟩ := cylinder_nbhd_basis Sα iα U hU p.1 hpU
  obtain ⟨kβ, hkβ⟩ := cylinder_nbhd_basis Sβ iβ V hV p.2 hpV
  exact ⟨kα, kβ, fun q hq1 hq2 => hsub q (hkα q.1 hq1) (hkβ q.2 hq2)⟩

/-! ## q3tpd-2: 比較射像の位相的稠密性（★ q3tpec 限定 (3) の正面 discharge） -/

/-- **q3tpd-2（★）: 比較射像は π₁^ét の直積副有限位相で稠密** — 直積位相
    `prodTopology (limitTopology tmzSystem) (limitTopology (padicSystem 3))` の任意の開集合 W と
    点 y ∈ W に対し、tempered 群の元 x で q3tpEtComp.map x ∈ W。
    q3tpd_prod_nbhd_basis でレベル kα・kβ の二重柱へ落とし、
      μ 方向: 比較射は恒等（q3tpEtComp_mu）ゆえ x.1 = y.1 でレベル kα は自明に一致、
      離散方向: q3tpd_toZp_hits_level で y.2.val kβ の整数代表 a を当てる（x.2 = a）
    で像が W と交わる。q3tpec の「各有限商で全射」＝代数的影を、実物の位相の上での
    **各点近傍稠密性**へ昇格させる本モジュールの核。 -/
theorem q3tpd_image_dense
    (W : q3tpEtGroup.carrier → Prop)
    (hW : (prodTopology (limitTopology tmzSystem)
            (limitTopology (padicSystem 3))).IsOpen W)
    (y : q3tpEtGroup.carrier) (hy : W y) :
    ∃ x : q3tpGroup.carrier, W (q3tpEtComp.map x) := by
  obtain ⟨kα, kβ, hsub⟩ :=
    q3tpd_prod_nbhd_basis tmzSystem (padicSystem 3) 0 0 W hW y hy
  obtain ⟨a, ha⟩ := q3tpd_toZp_hits_level 3 kβ (y.2.val kβ)
  refine ⟨(y.1, a), hsub (q3tpEtComp.map (y.1, a)) ?_ ?_⟩
  · show y.1.val kα = y.1.val kα
    rfl
  · show ((toZp 3).map a).val kβ = y.2.val kβ
    exact ha

/-! ## q3tpd-3: 真部分性（tempered ⊊ étale の witness・q3tpec-4 の実消費） -/

/-- **q3tpd-3: 真部分性の witness** — (1, ω) ∈ ℤ₃(1)×ℤ₃ は q3tpEtComp の像に属さない
    （ω = q3tpEtWitness は幾何級数の整合族・値 −1/2 ∉ ℤ）。q3tpec-4 の
    q3tp_disc_not_surjective（実 3 進分離性の消費）をそのまま担う。像が π₁^ét 全体でない
    ＝ tempered ⊊ étale の真部分性。 -/
theorem q3tpd_proper_witness :
    ¬ ∃ x : q3tpGroup.carrier,
        q3tpEtComp.map x = (tmzLimit.one, q3tpEtWitness) := by
  intro h
  obtain ⟨x, hx⟩ := h
  have h2 : (toZp 3).map x.2 = q3tpEtWitness := congrArg Prod.snd hx
  exact q3tp_disc_not_surjective ⟨x.2, h2⟩

/-! ## q3tpd-4: 旗艦 — 稠密 かつ 真部分 -/

/-- **q3tpd-4（★・旗艦）: tempered 像は π₁^ét で稠密かつ真部分** —
    (稠密) 直積副有限位相の任意の基本開近傍は q3tpEtComp の像と交わる（q3tpd_image_dense）、
    (真部分) 像に属さない点 (1, ω) が存在する（q3tpd_proper_witness）。
    q3tpec 正直限定 (3) の named defer「位相的稠密性は主張しない」を M15 の実位相の上で
    正面 discharge し、「**tempered π₁ は étale π₁ の真の稠密部分群**」——IUT が étale でなく
    tempered を要する質的核心——を、代数的影でなく本物の位相文として実主語上で定理化する。 -/
theorem q3tpd_dense_proper :
    (∀ (W : q3tpEtGroup.carrier → Prop),
        (prodTopology (limitTopology tmzSystem)
          (limitTopology (padicSystem 3))).IsOpen W →
        ∀ y : q3tpEtGroup.carrier, W y →
          ∃ x : q3tpGroup.carrier, W (q3tpEtComp.map x))
    ∧ (∃ y : q3tpEtGroup.carrier,
          ¬ ∃ x : q3tpGroup.carrier, q3tpEtComp.map x = y) :=
  ⟨q3tpd_image_dense, ⟨(tmzLimit.one, q3tpEtWitness), q3tpd_proper_witness⟩⟩

/-! ## q3tpd-5: capstone — 実 tempered ⊊ 稠密 étale データ -/

/-- **q3tpd-5a: 実 tempered 像の位相的稠密・真部分データ** — 比較射・その像の直積副有限位相
    稠密性・真部分性を束ねる。主語は実 tmzLimit（実 ℤ₃(1)）・実 Zp 3・実 toZp 3・M15 実位相
    （toy 代理なし）。q3tpec の代数的影を位相文へ昇格した積層。 -/
structure Q3TemperedEtDensityData where
  /-- tempered 群 π₁^{temp,(3)} = ℤ₃(1)×ℤ。 -/
  temperedGroup : Grp
  /-- étale 群 π₁^{ét,(3)} = ℤ₃(1)×ℤ₃。 -/
  etaleGroup : Grp
  /-- tempered ＝ A5b の実 tempered 群。 -/
  tempered_isA5b : temperedGroup = q3tpGroup
  /-- étale ＝ q3tpec の実 π₁^ét 模型。 -/
  etale_isEt : etaleGroup = q3tpEtGroup
  /-- 実比較射 π₁^{temp} → π₁^{ét}。 -/
  comparison : Hom temperedGroup etaleGroup
  /-- étale 側の直積副有限位相。 -/
  etaleTopology : Topology etaleGroup.carrier
  /-- **位相的稠密性**（各基本開近傍が像と交わる）。 -/
  dense : ∀ (W : etaleGroup.carrier → Prop), etaleTopology.IsOpen W →
    ∀ y : etaleGroup.carrier, W y → ∃ x : temperedGroup.carrier, W (comparison.map x)
  /-- **真部分性**（像に属さない点が存在）。 -/
  proper : ∃ y : etaleGroup.carrier, ¬ ∃ x : temperedGroup.carrier, comparison.map x = y

/-- **q3tpd-5b: 見出し実例 q = 3**（pro-3）— 全フィールドを q3tpd-0〜4 の本物の証明で充填。
    稠密フィールドは q3tpd_image_dense・真部分フィールドは q3tpd_proper_witness で埋まる。 -/
def q3tpdData : Q3TemperedEtDensityData where
  temperedGroup := q3tpGroup
  etaleGroup := q3tpEtGroup
  tempered_isA5b := rfl
  etale_isEt := rfl
  comparison := q3tpEtComp
  etaleTopology := prodTopology (limitTopology tmzSystem) (limitTopology (padicSystem 3))
  dense := q3tpd_image_dense
  proper := ⟨(tmzLimit.one, q3tpEtWitness), q3tpd_proper_witness⟩

/-- **q3tpd-5c（★）: 実 tempered 稠密・真部分データは存在する** — 実比較射の像が実 π₁^ét の
    副有限位相で稠密かつ真部分であることが入力仮説なしで構成できる。q3tpec 限定 (3) の
    位相 discharge の実インスタンス。 -/
theorem q3tpd_exists : Nonempty Q3TemperedEtDensityData := ⟨q3tpdData⟩

/-! ## 実例（tempered ⊊ 稠密 étale の実部分ケース） -/

/-- 実例: toZp 像は Zp 3 の副有限位相で稠密。 -/
example (U : (Zp 3).carrier → Prop)
    (hU : (limitTopology (padicSystem 3)).IsOpen U)
    (x : (Zp 3).carrier) (hx : U x) :
    ∃ a : Int, U ((toZp 3).map a) :=
  q3tpd_toZp_dense 3 U hU x hx

/-- 実例: 比較射像は π₁^ét で稠密かつ真部分。 -/
example :
    (∀ (W : q3tpEtGroup.carrier → Prop),
        (prodTopology (limitTopology tmzSystem)
          (limitTopology (padicSystem 3))).IsOpen W →
        ∀ y : q3tpEtGroup.carrier, W y →
          ∃ x : q3tpGroup.carrier, W (q3tpEtComp.map x))
    ∧ (∃ y : q3tpEtGroup.carrier,
          ¬ ∃ x : q3tpGroup.carrier, q3tpEtComp.map x = y) :=
  q3tpd_dense_proper

end IUT
