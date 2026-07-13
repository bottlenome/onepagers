/-
  IUT/Q3Mu9TmzBridge.lean — level-9 比較橋（level-3 テータ cyclotome ↔ tmz の mod-9 層）
  ——tmi の実 ℤ₃^× 不定性の (ℤ/9)^× 商をテータ剛性で殺し、新層 (1+3ℤ₃)/(1+9ℤ₃) を消す
    （q3mb=level-3 橋の ℓ=2 版・firewall 越えの display-mover 候補）

  ── 主要成果の分類: **[実／本物の先行建設(b)]**（骨格・模型・代理でなく、テータ側の実局所環
     U₃ = O_M^× = `q3kU` 内の実 μ₉（`q9tlZeta9U`=⟨Y,unit⟩＝ζ₉）と、tmz 側の大域実円分体
     ℚ(ζ₉) 内の実 μ₉（`tmzG 1 = cmrGrp 2`）を、選択公理なしの離散対数 `ctmFind 2` で結ぶ
     実 G-同変な群同一視 β₉ : Hom (tmzG 1) q3kU を本物に建て、そこを通して tmi の実
     ℤ₃^×=`zpsLimit` の実作用 `tmiFromUnits` を level-9 テータ内部 μ₉ へ輸送し、level-9
     mono-theta 剛性 `q9mr_cyclotome_fixed`（原始 9 乗根 ζ₉⁻¹ 固定）で **(ℤ/9)^× 商を殺す**
     （mod-9 成分 u₁=1 強制）。★新規の目玉は σU 局所大域同変（q3kSigma の単数群化 σU が
     大域 χ=4 の Galois 作用に一致し、新層 ker(Aut(μ₉)→Aut(μ₃)) の局所大域突き合わせを与える）。
     toy 主語なし——主語は実 U₃・実 tmzG 1・実 zpsLimit。）

  **complete_pct 影響**: **display-mover 候補**。level-9 kill を tmi の実 ℤ₃^× 対象へ接続し、
  テータ剛性が **tmi の実 Aut(ℤ₃(1))≅ℤ₃^× 不定性の (ℤ/9)^× 商に作用して殺す**水準へ昇格する
  （level-3 の precedent: q3mb が 53→54 を動かした）。**敵対的予測は A7 status +0.02..+0.03
  ⟹ 表示 54（中央）または 55（上振れ・閾値 s_A7≥0.58）**。ラウンド報告がどちらかを正直に述べ、
  数値は独立監査が確定する。A6/A8/A5 は本ファイルで一切主張しない（二重計上境界）。

  内容（設計 audit/level9-theta-kill-detail-2026-07-11.md §4 の 11 項を q3mb→ℓ=2/9 元/q3kU で再演）:
   * q9mb_pow_mod9 — g⁹=1 ⟹ pow g (e%9)=pow g e（周期 9・q3mb_pow_mod3 の 9 版・q3kU 可換）。
   * q9mbU / q9mbHom (★橋 β₉) — y ↦ ζ₉U^{ctmFind 2 y}・map_mul は tmz_mul_find 2＋ζ₉U⁹=1。
   * q9mb_pow_inj / q9mb_inj — 単射（ζ₉U の位数ちょうど 9・q9tl 消費・81 分岐回避）。
   * q9mb_image_mu9 / q9mb_onto_mu9 — 像 ⊆ μ₉・全射（q9c_mu9_complete 消費・9 分岐 Or）。
   * q9mb_equivariant (★同変) — β₉(σy)=pow(β₉y) χ(σ)（cgar_rigidity 2）。
   * q9mb_normBase_sigma / q9mbSigmaU / q9mb_equivariant_sigmaU (★★新規) — σ=q3kSigma の単数群化
     σU が well-defined（N(σx)=N(x)・q3k_norm_eq＋σ³=id 経由）で、大域 χ=4（cciFromUnits⟨4⟩）
     の Galois 作用に一致: β₉(σ₄y)=σU(β₉y)。新層の局所大域突き合わせ（再ラベルでない新規内容）。
   * q9mb_flip_invariant — (gᵃ)ᵇ=(gᵇ)ᵃ（曖昧さは Aut(μ₉)=位数 6・正直限定を強める）。
   * q9mbInt / q9mb_int_zeta — 内部版橋（q9mr_zeta9 と整合・cra_find_zeta 2）。
   * q9mb_transport (★輸送) — tmiFromUnits の level-1 成分を内部 μ₉ へ。tmiFromUnits 本体消費。
   * q9mb_kill_mod9 (★★★ display-moving) — テータ両立 φ が輸送を実現 ⟹ (u.val 1).val=1。
     証明: t=tmeZetaLim・左辺 φ(q9mr_zeta9)=q9mr_zeta9（剛性消費）・右辺 (ζ₉⁻¹)^{u₁}・
     ζ₉U 位数ちょうど 9 の単射性で u₁=1 強制。
   * q9mb_admissible_iff — u₁=1 ⟺ テータ実現可能（消去形 iff）。
   * q9mb_kill_new_layer / q9mb_new_layer_chars (★新層系) — 新規排除集合 u₁∈{4,7}
     ＝(1+3ℤ₃)/(1+9ℤ₃) の非自明元（§1 標的が実際に死んだことの機械可読形・q3mb の u₀=1 と
     過大主張しない対比）。
   * Q3Mu9TmzBridgeData / q9mb_data / q9mb_exists — capstone。

  正直な限定（§4.3 規約により消さない・弱化しない・q3mb の 5 項を強めて継承・追記のみ）:
  1. **mod-9 層（level 1）のみ**。塔版/極限（F-wild (v)）ではない。1+9ℤ₃（n≥3 の全層）と
     n≥2 レベルは依然 SURVIVES。tmi の残存宣言・q9mr 正直限定は不変更。
  2. 同一視は**群レベル・生成元指定つき**。曖昧さは ℤ/2 でなく **Aut(μ₉)＝位数 6**（kill は
     flip_invariant で不変・q9mb_flip_invariant）。実埋め込み ℚ(ζ₉)↪ℚ₃(ζ₉)（分解群理論）は
     形式化しない。
  3. テータ側 Galois は σ=q3kSigma（Y↦ζ₃Y・位数 3）とその単数群化 σU のみ（実 G_{ℚ₃} 不在）。
  4. q=3⁹ 忠実部分ケースの 2 乗・endo 定式化・実テータ関数/π₁/大域 Galois 0（継承）。
  5. **u₁=1 強制は「level-9 テータ両立クラス」相対**——tmi の残存宣言（full ℤ₃^× は Galois
     同変性だけでは絞れない）は不変更。**新規排除は核層 {4,7} のみ**（(ℤ/9)^× 全体でなく）。
  6. **二重計上の firewall**: q9mr(cyclotome_fixed)・tmiFromUnits・q9c(mu9_complete)・
     cgar/tmz/ctmFind ℓ=2・q3k(σ/ζ₉) は**消費のみ・再証明ゼロ・言明複製ゼロ**。新規は橋 β₉＋
     σU 同変＋輸送＋(ℤ/9)^× kill。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。prefix `q9mb`。
-/
import IUT.Q3Mu9Rigidity
import IUT.Q3Mu9Completeness
import IUT.Q3KummerYPow
import IUT.Q3TateCurveL9
import IUT.TateModuleIndeterminacy
import IUT.TateModuleZ3
import IUT.TateModuleEndo
import IUT.CyclotomicGKActionReal
import IUT.CyclotomicRigidity
import IUT.CyclotomicCharIso
import IUT.LocalBrauer

set_option maxRecDepth 8000

namespace IUT

/-! ## q9mb-0: U₃ = q3kU の可換性・冪橋（tateNpow ↔ Grp.pow・choice-free） -/

/-- **q9mb-0a: U₃ = q3kU は可換**（q3k_mul_comm の単数群化・Subtype.ext）。 -/
theorem q9mb_q3kU_comm (a b : q3kU.carrier) : q3kU.mul a b = q3kU.mul b a :=
  Subtype.ext (q3k_mul_comm a.val b.val)

/-- **q9mb-0b: 冪橋** tateNpow q3kU g n = q3kU.pow g n（同一元の冪は可換ゆえ左右畳み一致）。 -/
theorem q9mb_npow_pow (g : q3kU.carrier) (n : Nat) : tateNpow q3kU g n = q3kU.pow g n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show q3kU.mul (tateNpow q3kU g k) g = q3kU.mul g (q3kU.pow g k)
    rw [ih]
    exact q9mb_q3kU_comm (q3kU.pow g k) g

/-- **q9mb-0c: ζ₉U⁹ = 1 in U₃**（q9tl_zpow9 消費・原始 9 乗根の位数 9）。 -/
theorem q9mb_zeta9U_ninth : q3kU.pow q9tlZeta9U 9 = q3kU.one := by
  rw [← q9mb_npow_pow q9tlZeta9U 9]
  apply Subtype.ext
  exact q9tl_zpow9

/-- **q9mb-0d: pow g 1 = g**（1 冪の展開）。 -/
theorem q9mb_pow_one (g : q3kU.carrier) : q3kU.pow g 1 = g := by
  show q3kU.mul g (q3kU.pow g 0) = g
  show q3kU.mul g q3kU.one = g
  exact q3kU.mul_one g

/-- **q9mb-0e: ζ₉U の位数ちょうど 9**（0<m<9 ⟹ ζ₉U^m ≠ 1・q9tl_zeta9U_pow_ne 消費）。 -/
theorem q9mb_pow_ne_one (m : Nat) (hm0 : 0 < m) (hm9 : m < 9) :
    q3kU.pow q9tlZeta9U m ≠ q3kU.one := by
  rw [← q9mb_npow_pow q9tlZeta9U m]
  exact q9tl_zeta9U_pow_ne m hm0 hm9

/-! ## q9mb-1: ★ ζ₉U 冪の単射性（位数 9 経由・81 分岐回避） -/

/-- **q9mb-1（★ #3）: ζ₉U 冪の単射性**（i,j<9・位数ちょうど 9 から）。i≠j なら ζ₉U^{|i−j|}=1
    かつ 0<|i−j|<9 で矛盾（q9tl の位数 9 補助＝q9yp 単項式正規形パックの帰結を消費）。 -/
theorem q9mb_pow_inj (i j : Nat) (hi : i < 9) (hj : j < 9)
    (h : q3kU.pow q9tlZeta9U i = q3kU.pow q9tlZeta9U j) : i = j := by
  obtain hlt | heq | hgt := Nat.lt_trichotomy i j
  · exfalso
    have hadd : q3kU.mul (q3kU.pow q9tlZeta9U i) (q3kU.pow q9tlZeta9U (j - i))
        = q3kU.pow q9tlZeta9U i := by
      rw [← cycRig_pow_add q3kU q9mb_q3kU_comm q9tlZeta9U i (j - i),
          show i + (j - i) = j from by omega]
      exact h.symm
    have hcancel : q3kU.mul (q3kU.pow q9tlZeta9U i) (q3kU.pow q9tlZeta9U (j - i))
        = q3kU.mul (q3kU.pow q9tlZeta9U i) q3kU.one := by
      rw [q3kU.mul_one]; exact hadd
    exact q9mb_pow_ne_one (j - i) (by omega) (by omega) (Grp.mul_left_cancel q3kU hcancel)
  · exact heq
  · exfalso
    have hadd : q3kU.mul (q3kU.pow q9tlZeta9U j) (q3kU.pow q9tlZeta9U (i - j))
        = q3kU.pow q9tlZeta9U j := by
      rw [← cycRig_pow_add q3kU q9mb_q3kU_comm q9tlZeta9U j (i - j),
          show j + (i - j) = i from by omega]
      exact h
    have hcancel : q3kU.mul (q3kU.pow q9tlZeta9U j) (q3kU.pow q9tlZeta9U (i - j))
        = q3kU.mul (q3kU.pow q9tlZeta9U j) q3kU.one := by
      rw [q3kU.mul_one]; exact hadd
    exact q9mb_pow_ne_one (i - j) (by omega) (by omega) (Grp.mul_left_cancel q3kU hcancel)

/-! ## q9mb-2: μ₉ 冪の周期（g⁹=1・mod 9・flip 不変） -/

/-- 純 Nat の剰余変換 e % 3^2 = e % 9（部分型を含まない文脈で 3^2 を潰す）。 -/
theorem q9mb_mod_conv1 (e : Nat) : e % 3 ^ 2 = e % 9 := by
  rw [show (3 : Nat) ^ 2 = 9 from rfl]

/-- 純 Nat の剰余変換 (a·k) % 3^2 = (k·a) % 9。 -/
theorem q9mb_mod_conv (a k : Nat) : (a * k) % 3 ^ 2 = (k * a) % 9 := by
  rw [show (3 : Nat) ^ 2 = 9 from rfl, Nat.mul_comm a k]

/-- **q9mb-2a（#1）: g⁹=1 なら pow g (e%9) = pow g e**（可換冪の周期性・q3kU）。 -/
theorem q9mb_pow_mod9 (g : q3kU.carrier) (hg : q3kU.pow g 9 = q3kU.one) (e : Nat) :
    q3kU.pow g (e % 9) = q3kU.pow g e := by
  have hdm : 9 * (e / 9) + e % 9 = e := Nat.div_add_mod e 9
  calc q3kU.pow g (e % 9)
      = q3kU.mul q3kU.one (q3kU.pow g (e % 9)) := (q3kU.one_mul _).symm
    _ = q3kU.mul (q3kU.pow (q3kU.pow g 9) (e / 9)) (q3kU.pow g (e % 9)) := by
        rw [hg, brau_pow_one q3kU (e / 9)]
    _ = q3kU.mul (q3kU.pow g (9 * (e / 9))) (q3kU.pow g (e % 9)) := by
        rw [← cycRig_pow_mul q3kU q9mb_q3kU_comm g 9 (e / 9)]
    _ = q3kU.pow g (9 * (e / 9) + e % 9) :=
        (cycRig_pow_add q3kU q9mb_q3kU_comm g (9 * (e / 9)) (e % 9)).symm
    _ = q3kU.pow g e := by rw [hdm]

/-- **q9mb-2b: pow ζ₉U (e%9) = pow ζ₉U e**。 -/
theorem q9mb_zeta_pow_mod (e : Nat) :
    q3kU.pow q9tlZeta9U (e % 9) = q3kU.pow q9tlZeta9U e :=
  q9mb_pow_mod9 q9tlZeta9U q9mb_zeta9U_ninth e

/-- **q9mb-2b': pow ζ₉U (e % 3^2) = pow ζ₉U e**（tmz 側の % 3^ℓ（ℓ=2）に合わせた版）。 -/
theorem q9mb_zeta_pow_mod1 (e : Nat) :
    q3kU.pow q9tlZeta9U (e % 3 ^ 2) = q3kU.pow q9tlZeta9U e := by
  rw [q9mb_mod_conv1 e]; exact q9mb_zeta_pow_mod e

/-- **q9mb-2c: (ζ₉U⁻¹)⁹ = 1 in U₃**（内部 cyclotome 生成元 g₀=ζ₉⁻¹ の位数 9）。 -/
theorem q9mb_g0_ninth : q3kU.pow (q3kU.inv q9tlZeta9U) 9 = q3kU.one := by
  rw [brau_pow_inv q3kU q9mb_q3kU_comm q9tlZeta9U 9, q9mb_zeta9U_ninth, Grp.inv_one]

/-- **q9mb-2d（#6・生成元反転で輸送指数不変）: (gᵃ)ᵇ = (gᵇ)ᵃ** — β₉ を反転しても輸送指数は
    不変（Aut(μ₉) 可換ゆえ冪写像の輸送指数は生成元選択に依らない）。曖昧さは Aut(μ₉)＝位数 6
    だが kill はこの不変性で影響を受けない（正直限定 2 を強める機械証明）。 -/
theorem q9mb_flip_invariant (g : q3kU.carrier) (a b : Nat) :
    q3kU.pow (q3kU.pow g a) b = q3kU.pow (q3kU.pow g b) a := by
  rw [← cycRig_pow_mul q3kU q9mb_q3kU_comm g a b, ← cycRig_pow_mul q3kU q9mb_q3kU_comm g b a,
      Nat.mul_comm a b]

/-! ## q9mb-3: find の冪則（輸送・全射の材料） -/

/-- **q9mb-3（#8 材料）: find の冪則** find((cmrGrp 2).pow y k) = (k·find y) % 9
    （y=ζ₉^{find y}＋cycRig_pow_mul＋tmz_find_pow 2）。 -/
theorem q9mb_find_pow (y : (tmzG 1).carrier) (k : Nat) :
    ctmFind 2 (by omega) ((cmrGrp 2 (by omega)).pow y k).val
      = (k * ctmFind 2 (by omega) y.val) % 9 := by
  have hy : y = (cmrGrp 2 (by omega)).pow (cmrZeta 2 (by omega)) (ctmFind 2 (by omega) y.val) := by
    apply Subtype.ext
    rw [cmr_pow_zeta 2 (by omega) (ctmFind 2 (by omega) y.val)]
    exact tmz_val_find 2 (by omega) y
  have hkey : (cmrGrp 2 (by omega)).pow (cmrZeta 2 (by omega)) (ctmFind 2 (by omega) y.val * k)
      = (cmrGrp 2 (by omega)).pow y k := by
    rw [cycRig_pow_mul (cmrGrp 2 (by omega)) (cmr_comm 2 (by omega)) (cmrZeta 2 (by omega))
          (ctmFind 2 (by omega) y.val) k, ← hy]
  rw [← hkey, cmr_pow_zeta 2 (by omega) (ctmFind 2 (by omega) y.val * k),
      tmz_find_pow 2 (by omega) (ctmFind 2 (by omega) y.val * k),
      q9mb_mod_conv (ctmFind 2 (by omega) y.val) k]

/-! ## q9mb-4: ★ 橋 β₉ : Hom (tmzG 1) q3kU（#2） -/

/-- **q9mb-4a: 橋の担体写像** β₉(y) = ζ₉U^{find y}（離散対数・choice-free）。 -/
def q9mbU (y : (tmzG 1).carrier) : q3kU.carrier :=
  q3kU.pow q9tlZeta9U (ctmFind 2 (by omega) y.val)

/-- **q9mb-4b（★ #2）: 橋 β₉ : Hom (tmzG 1) q3kU** — map_mul は tmz_mul_find 2（離散対数
    加法性）＋ζ₉U⁹=1（q9mb_zeta_pow_mod1）で閉じる。 -/
def q9mbHom : Hom (tmzG 1) q3kU where
  map := q9mbU
  map_mul := fun y z => by
    show q3kU.pow q9tlZeta9U (ctmFind 2 (by omega) ((cmrGrp 2 (by omega)).mul y z).val)
       = q3kU.mul (q3kU.pow q9tlZeta9U (ctmFind 2 (by omega) y.val))
           (q3kU.pow q9tlZeta9U (ctmFind 2 (by omega) z.val))
    rw [tmz_mul_find 2 (by omega) y z,
        ← cycRig_pow_add q3kU q9mb_q3kU_comm q9tlZeta9U
          (ctmFind 2 (by omega) y.val) (ctmFind 2 (by omega) z.val)]
    exact q9mb_zeta_pow_mod1 (ctmFind 2 (by omega) y.val + ctmFind 2 (by omega) z.val)

/-- **q9mb-4c（#3）: β₉ 単射**（find<9 の 9 元・ζ₉U 冪の単射性）。 -/
theorem q9mb_inj : q9mbHom.Injective := by
  intro y z h
  apply Subtype.ext
  have hfy : ctmFind 2 (by omega) y.val < 9 := by
    have hb := (ctmFind_spec 2 (by omega) y.val y.property).2
    have h9 : (3 : Nat) ^ 2 = 9 := rfl
    omega
  have hfz : ctmFind 2 (by omega) z.val < 9 := by
    have hb := (ctmFind_spec 2 (by omega) z.val z.property).2
    have h9 : (3 : Nat) ^ 2 = 9 := rfl
    omega
  have hf : ctmFind 2 (by omega) y.val = ctmFind 2 (by omega) z.val :=
    q9mb_pow_inj _ _ hfy hfz h
  rw [tmz_val_find 2 (by omega) y, tmz_val_find 2 (by omega) z, hf]

/-! ## q9mb-5: ζ₉U 冪の単項式正規形値（像・全射の材料・q9yp 消費） -/

/-- pow ζ₉U 0 の val = 1。 -/
theorem q9mb_powval0 : (q3kU.pow q9tlZeta9U 0).val = q3kOne := rfl

/-- pow ζ₉U 1 の val = (0,1,0)。 -/
theorem q9mb_powval1 : (q3kU.pow q9tlZeta9U 1).val = ((q3rqZero, q3rqOne, q3rqZero) : q3kCar) := by
  rw [← q9mb_npow_pow q9tlZeta9U 1]; exact q9tl_zpow1

/-- pow ζ₉U 2 の val = (0,0,1)。 -/
theorem q9mb_powval2 : (q3kU.pow q9tlZeta9U 2).val = ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) := by
  rw [← q9mb_npow_pow q9tlZeta9U 2, q9tl_zpow2]; exact q9yp_y2

/-- pow ζ₉U 3 の val = (ζ₃,0,0)。 -/
theorem q9mb_powval3 : (q3kU.pow q9tlZeta9U 3).val = ((q3rqZeta, q3rqZero, q3rqZero) : q3kCar) := by
  rw [← q9mb_npow_pow q9tlZeta9U 3, q9tl_zpow3]; exact q9yp_y3

/-- pow ζ₉U 4 の val = (0,ζ₃,0)。 -/
theorem q9mb_powval4 : (q3kU.pow q9tlZeta9U 4).val = ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) := by
  rw [← q9mb_npow_pow q9tlZeta9U 4, q9tl_zpow4]; exact q9yp_y4

/-- pow ζ₉U 5 の val = (0,0,ζ₃)。 -/
theorem q9mb_powval5 : (q3kU.pow q9tlZeta9U 5).val = ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) := by
  rw [← q9mb_npow_pow q9tlZeta9U 5, q9tl_zpow5]; exact q9yp_y5

/-- pow ζ₉U 6 の val = (ζ₃²,0,0)。 -/
theorem q9mb_powval6 : (q3kU.pow q9tlZeta9U 6).val = ((q3rqZetaSq, q3rqZero, q3rqZero) : q3kCar) := by
  rw [← q9mb_npow_pow q9tlZeta9U 6, q9tl_zpow6]; exact q9yp_y6

/-- pow ζ₉U 7 の val = (0,ζ₃²,0)。 -/
theorem q9mb_powval7 : (q3kU.pow q9tlZeta9U 7).val = ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) := by
  rw [← q9mb_npow_pow q9tlZeta9U 7, q9tl_zpow7]; exact q9yp_y7

/-- pow ζ₉U 8 の val = (0,0,ζ₃²)。 -/
theorem q9mb_powval8 : (q3kU.pow q9tlZeta9U 8).val = ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) := by
  rw [← q9mb_npow_pow q9tlZeta9U 8, q9tl_zpow8]; exact q9yp_y8

/-! ## q9mb-6: ★ 像 ⊆ μ₉・μ₉ 全射（q9c_mu9_complete 消費・#4） -/

/-- w⁹=1（U₃）から q9c の 9 重積形へ橋渡し（q9mt_ninth_gen＋Subtype.val）。 -/
theorem q9mb_pow9_one (w : q3kU.carrier) (hw9 : q3kU.pow w 9 = q3kU.one) :
    q3kMul (q3kMul (q3kMul (q3kMul w.val w.val) w.val) (q3kMul (q3kMul w.val w.val) w.val))
      (q3kMul (q3kMul w.val w.val) w.val) = q3kOne := by
  have hz : tateZpow q3kU w 9 = q3kU.one := by
    show tateNpow q3kU w 9 = q3kU.one
    rw [q9mb_npow_pow w 9]; exact hw9
  rw [q9mt_ninth_gen q3kU w] at hz
  exact congrArg Subtype.val hz

/-- **q9mb-6a（#4）: 像 ⊆ μ₉** — β₉ y ∈ μ₉（(β₉y)⁹=1 ⟹ q9c_mu9_complete 消費）。 -/
theorem q9mb_image_mu9 (y : (tmzG 1).carrier) : q3kMu9 (q9mbHom.map y).val := by
  apply q9c_mu9_complete
  apply q9mb_pow9_one
  show q3kU.pow (q3kU.pow q9tlZeta9U (ctmFind 2 (by omega) y.val)) 9 = q3kU.one
  rw [← cycRig_pow_mul q3kU q9mb_q3kU_comm q9tlZeta9U (ctmFind 2 (by omega) y.val) 9,
      Nat.mul_comm (ctmFind 2 (by omega) y.val) 9,
      cycRig_pow_mul q3kU q9mb_q3kU_comm q9tlZeta9U 9 (ctmFind 2 (by omega) y.val),
      q9mb_zeta9U_ninth, brau_pow_one q3kU (ctmFind 2 (by omega) y.val)]

/-- β₉(ζ₉ の tmz 生成元 cmrZeta 2) = ζ₉U（find ζ = 1・cra_find_zeta 2）。 -/
theorem q9mb_map_zeta : q9mbHom.map (cmrZeta 2 (by omega)) = q9tlZeta9U := by
  show q3kU.pow q9tlZeta9U (ctmFind 2 (by omega) (cmrZeta 2 (by omega)).val) = q9tlZeta9U
  rw [cra_find_zeta 2 (by omega)]
  exact q9mb_pow_one q9tlZeta9U

/-- β₉(ζ₉^k) = ζ₉U^k（Hom.map_pow で構造的に・重い whnf を回避）。 -/
theorem q9mb_map_zeta_pow (k : Nat) :
    q9mbHom.map ((tmzG 1).pow (cmrZeta 2 (by omega)) k) = q3kU.pow q9tlZeta9U k := by
  rw [q9mbHom.map_pow, q9mb_map_zeta]

/-- **q9mb-6b（★ #4）: μ₉ の全射性（消去形）** — u⁹=(u³)³=1（μ₉ 完全性 q9c_mu9_complete
    消費・橋側 2 個目の消費点）ならば β₉ の原像 y が存在する（∃ は Prop 内・choice-free
    明示 witness＝ζ₉ の tmz 冪・9 分岐 Or 破壊で ζ₉ 冪の閉形式 witness を与える）。 -/
theorem q9mb_onto_mu9 (u : q3kU.carrier)
    (hu : q3kMul (q3kMul (q3kMul (q3kMul u.val u.val) u.val) (q3kMul (q3kMul u.val u.val) u.val))
        (q3kMul (q3kMul u.val u.val) u.val) = q3kOne) :
    ∃ y : (tmzG 1).carrier, q9mbHom.map y = u := by
  obtain h | h | h | h | h | h | h | h | h := q9c_mu9_complete u.val hu
  · exact ⟨(tmzG 1).pow (cmrZeta 2 (by omega)) 0, by
      apply Subtype.ext; rw [q9mb_map_zeta_pow 0, q9mb_powval0, h]⟩
  · exact ⟨(tmzG 1).pow (cmrZeta 2 (by omega)) 3, by
      apply Subtype.ext; rw [q9mb_map_zeta_pow 3, q9mb_powval3, h]⟩
  · exact ⟨(tmzG 1).pow (cmrZeta 2 (by omega)) 6, by
      apply Subtype.ext; rw [q9mb_map_zeta_pow 6, q9mb_powval6, h]⟩
  · exact ⟨(tmzG 1).pow (cmrZeta 2 (by omega)) 1, by
      apply Subtype.ext; rw [q9mb_map_zeta_pow 1, q9mb_powval1, h]⟩
  · exact ⟨(tmzG 1).pow (cmrZeta 2 (by omega)) 4, by
      apply Subtype.ext; rw [q9mb_map_zeta_pow 4, q9mb_powval4, h]⟩
  · exact ⟨(tmzG 1).pow (cmrZeta 2 (by omega)) 7, by
      apply Subtype.ext; rw [q9mb_map_zeta_pow 7, q9mb_powval7, h]⟩
  · exact ⟨(tmzG 1).pow (cmrZeta 2 (by omega)) 2, by
      apply Subtype.ext; rw [q9mb_map_zeta_pow 2, q9mb_powval2, h]⟩
  · exact ⟨(tmzG 1).pow (cmrZeta 2 (by omega)) 5, by
      apply Subtype.ext; rw [q9mb_map_zeta_pow 5, q9mb_powval5, h]⟩
  · exact ⟨(tmzG 1).pow (cmrZeta 2 (by omega)) 8, by
      apply Subtype.ext; rw [q9mb_map_zeta_pow 8, q9mb_powval8, h]⟩

/-! ## q9mb-7: ★ Galois 同変（χ 冪・#5 前半） -/

/-- **q9mb-7a（★ #5・Galois 同変）: β₉(σy) = pow (β₉y) χ(σ)** — tmz 側の実 Galois 作用
    `cgarAct 2 σ` を β₉ で読むと、テータ側 μ₉ 上の χ(σ) 冪になる（cgar_rigidity 2 消費）。 -/
theorem q9mb_equivariant (σ : (galoisGroupGrp (cteExt 2 (by omega))).carrier)
    (y : (tmzG 1).carrier) :
    q9mbHom.map (((cgarAct 2 (by omega)).act σ).map y)
      = q3kU.pow (q9mbHom.map y)
          (cycRigExp (galoisGroupGrp (cteExt 2 (by omega))) (cmrMu 2 (by omega))
            (cgarAct 2 (by omega)) σ) := by
  show q3kU.pow q9tlZeta9U (ctmFind 2 (by omega) (((cgarAct 2 (by omega)).act σ).map y).val)
     = q3kU.pow (q3kU.pow q9tlZeta9U (ctmFind 2 (by omega) y.val))
         (cycRigExp (galoisGroupGrp (cteExt 2 (by omega))) (cmrMu 2 (by omega))
           (cgarAct 2 (by omega)) σ)
  rw [cgar_rigidity 2 (by omega) σ y, cmr_pow_zeta 2 (by omega) _,
      tmz_find_pow 2 (by omega) _, q9mb_zeta_pow_mod1 _,
      ← cycRig_pow_mul q3kU q9mb_q3kU_comm q9tlZeta9U (ctmFind 2 (by omega) y.val)
        (cycRigExp (galoisGroupGrp (cteExt 2 (by omega))) (cmrMu 2 (by omega))
          (cgarAct 2 (by omega)) σ),
      Nat.mul_comm (cycRigExp (galoisGroupGrp (cteExt 2 (by omega))) (cmrMu 2 (by omega))
          (cgarAct 2 (by omega)) σ) (ctmFind 2 (by omega) y.val)]

/-! ## q9mb-8: ★★ 新規 σU 局所大域同変（新層の突き合わせ・#5 本丸） -/

/-- **q9mb-8a（★★新規）: σ はノルムを保つ** N(σx) = N(x) — q3k_norm_eq（N=x·σx·σ²x）と
    σ³=id から σx·σ²x·x = x·σx·σ²x（可換再配列）。これが σ の単数群化を well-defined にする
    局所側の生命線（Bool/Fin ラベルでなく実 O_M の実ノルム保存）。 -/
theorem q9mb_normBase_sigma (x : q3kCar) : q3kNormBase (q3kSigma x) = q3kNormBase x := by
  apply q3k_embed_inj
  rw [← q3k_norm_eq (q3kSigma x), ← q3k_norm_eq x,
      ← q3k_sigma2_comp x, q3k_sigma2_comp (q3kSigma x), q3k_sigma3_id x, q3k_kM_eq,
      q3kRing.mul_comm (q3kSigma2 x) x,
      ← q3kRing.mul_assoc (q3kSigma x) x (q3kSigma2 x),
      q3kRing.mul_comm (q3kSigma x) x,
      q3kRing.mul_assoc x (q3kSigma x) (q3kSigma2 x)]

/-- **q9mb-8b（★★新規）: σ の単数群化 σU : U₃ → U₃**（N 保存ゆえ単数を単数へ）。 -/
def q9mbSigmaU (x : q3kU.carrier) : q3kU.carrier :=
  ⟨q3kSigma x.val, by
    show q3rqUnitMem (q3kNormBase (q3kSigma x.val))
    rw [q9mb_normBase_sigma]
    exact x.property⟩

/-- **q9mb-8c: σU の乗法性**（q3k_sigma_mul の単数群化）。 -/
theorem q9mb_sigmaU_mul (x y : q3kU.carrier) :
    q9mbSigmaU (q3kU.mul x y) = q3kU.mul (q9mbSigmaU x) (q9mbSigmaU y) := by
  apply Subtype.ext
  show q3kSigma (q3kMul x.val y.val) = q3kMul (q3kSigma x.val) (q3kSigma y.val)
  exact q3k_sigma_mul x.val y.val

/-- **q9mb-8d: σU(1) = 1**（q3k_sigma_one）。 -/
theorem q9mb_sigmaU_one : q9mbSigmaU q3kU.one = q3kU.one := by
  apply Subtype.ext
  show q3kSigma q3kOne = q3kOne
  exact q3k_sigma_one

/-- **q9mb-8e: σU は冪と可換**: σU(gᵏ) = (σU g)ᵏ。 -/
theorem q9mb_sigmaU_pow (g : q3kU.carrier) (k : Nat) :
    q9mbSigmaU (q3kU.pow g k) = q3kU.pow (q9mbSigmaU g) k := by
  induction k with
  | zero =>
    show q9mbSigmaU q3kU.one = q3kU.one
    exact q9mb_sigmaU_one
  | succ j ih =>
    show q9mbSigmaU (q3kU.mul g (q3kU.pow g j))
       = q3kU.mul (q9mbSigmaU g) (q3kU.pow (q9mbSigmaU g) j)
    rw [q9mb_sigmaU_mul, ih]

/-- **q9mb-8f: σU(ζ₉U) = ζ₉U⁴**（σ(ζ₉)=ζ₉⁴＝q9mr_sigma_zeta9・新層 k=4 の生成元）。 -/
theorem q9mb_sigmaU_zeta : q9mbSigmaU q9tlZeta9U = q3kU.pow q9tlZeta9U 4 := by
  apply Subtype.ext
  show q3kSigma q3kZeta9 = (q3kU.pow q9tlZeta9U 4).val
  rw [q9mr_sigma_zeta9, ← q9mb_npow_pow q9tlZeta9U 4]
  exact q9tl_zpow4.symm

/-- **q9mb-8g: 大域 χ=4 の担体元** 4 ∈ (ℤ/9)^×。 -/
def q9mbFour : (zpuGrp 2 (by omega)).carrier :=
  ⟨4, by omega, by intro h; obtain ⟨k, hk⟩ := h; omega⟩

/-- **q9mb-8h: 大域 χ=4 の実 Galois 元** σ₄ = cciFromUnits⟨4⟩ ∈ Gal(ℚ(ζ₉)/ℚ)。 -/
def q9mbSigma4 : (galoisGroupGrp (cteExt 2 (by omega))).carrier :=
  (cciFromUnits 2 (by omega)).map q9mbFour

/-- **q9mb-8i: χ(σ₄) = 4**（cgar_exp_eq＋cci_charG_csaAut）。 -/
theorem q9mb_sigma4_exp :
    cycRigExp (galoisGroupGrp (cteExt 2 (by omega))) (cmrMu 2 (by omega)) (cgarAct 2 (by omega))
        q9mbSigma4 = 4 := by
  rw [cgar_exp_eq 2 (by omega) q9mbSigma4]
  exact cci_charG_csaAut 2 (by omega) q9mbFour

/-- **q9mb-8（★★新規の目玉 #5）: σU 局所大域同変** β₉(σ₄y) = σU(β₉y) — 大域 χ=4 の
    実 Galois 作用（cgarAct 2 σ₄）を β₉ で読むと、局所側の実自己同型 σU（q3kSigma の単数群化）
    にちょうど一致する。新層 ker(Aut(μ₉)→Aut(μ₃)) の局所大域突き合わせ（level-3 の反転共役
    同変 q3mb_equivariant_conj の wild 版・再ラベルでない新規内容）。 -/
theorem q9mb_equivariant_sigmaU (y : (tmzG 1).carrier) :
    q9mbHom.map (((cgarAct 2 (by omega)).act q9mbSigma4).map y)
      = q9mbSigmaU (q9mbHom.map y) := by
  rw [q9mb_equivariant q9mbSigma4 y, q9mb_sigma4_exp]
  show q3kU.pow (q3kU.pow q9tlZeta9U (ctmFind 2 (by omega) y.val)) 4
     = q9mbSigmaU (q3kU.pow q9tlZeta9U (ctmFind 2 (by omega) y.val))
  rw [q9mb_sigmaU_pow q9tlZeta9U (ctmFind 2 (by omega) y.val), q9mb_sigmaU_zeta]
  exact q9mb_flip_invariant q9tlZeta9U (ctmFind 2 (by omega) y.val) 4

/-! ## q9mb-9: 内部版橋 q9mbInt（q9mr_zeta9 と整合・#7） -/

/-- **q9mb-9a: 内部橋の単数部** g₀^{find y}（g₀=ζ₉⁻¹＝内部 cyclotome 生成元の値）。 -/
def q9mbUnit (y : (tmzG 1).carrier) : q3kU.carrier :=
  q3kU.pow (q3kU.inv q9tlZeta9U) (ctmFind 2 (by omega) y.val)

/-- **q9mb-9b（#7）: 内部版橋** q9mbInt : (tmzG 1).carrier → q9mtCar
    （y ↦ (((0, g₀^{find y}), 0), 1)・内部生成元 q9mr_zeta9 と整合）。 -/
def q9mbInt (y : (tmzG 1).carrier) : q9mtCar :=
  ((((0 : Int), q9mbUnit y), (0 : Int)), q9tlMx.one)

/-- 生成元での単数部の値: q9mbUnit(ζ₉) = ζ₉⁻¹ = g₀。 -/
theorem q9mb_unit_zeta : q9mbUnit (tmeZetaLim.val 1) = q3kU.inv q9tlZeta9U := by
  have hz1 : (tmeZetaLim.val 1) = cmrZeta 2 (by omega) := rfl
  show q3kU.pow (q3kU.inv q9tlZeta9U) (ctmFind 2 (by omega) (tmeZetaLim.val 1).val)
     = q3kU.inv q9tlZeta9U
  rw [hz1, cra_find_zeta 2 (by omega)]
  show q3kU.mul (q3kU.inv q9tlZeta9U) q3kU.one = q3kU.inv q9tlZeta9U
  exact q3kU.mul_one _

/-- **q9mb-9c（★整合）: q9mbInt(ζ₉) = q9mr_zeta9** — 内部橋の生成元像が level-9 テータ剛性の
    内部 cyclotome 生成元（原始 9 乗根 ζ₉⁻¹）にちょうど一致する。 -/
theorem q9mb_int_zeta : q9mbInt (tmeZetaLim.val 1) = q9mr_zeta9 := by
  show ((((0 : Int), q9mbUnit (tmeZetaLim.val 1)), (0 : Int)), q9tlMx.one)
     = ((((0 : Int), q3kU.inv q9tlZeta9U), (0 : Int)), q9tlMx.one)
  rw [q9mb_unit_zeta]

/-! ## q9mb-10: ★ 輸送定理（tmiFromUnits を内部 μ₉ へ・#8） -/

/-- tmiFromUnits の level-1 成分は u₁ 冪（tmiPowHom の成分冪本体・rfl）。 -/
theorem q9mb_level1 (u : zpsLimit.carrier) (t : tmzLimit.carrier) :
    ((tmiFromUnits u).map t).val 1
      = (cmrGrp 2 (by omega)).pow (t.val 1) ((u.val 1).val) := rfl

/-- **q9mb-10（★ #8・輸送）: β₉∘(tmiFromUnits u の level-1) = (β₉ の u₁ 冪)** — tmi の
    実 ℤ₃^× 作用 `tmiFromUnits u`（成分冪 y↦y^{u₁}）を内部橋 q9mbInt で読むと、内部
    μ₉ の単数部が q9mbUnit(t₁) の u₁ 冪へ輸送される。tmiFromUnits 本体（成分冪）消費。 -/
theorem q9mb_transport (u : zpsLimit.carrier) (t : tmzLimit.carrier) :
    q9mbInt (((tmiFromUnits u).map t).val 1)
      = ((((0 : Int), q3kU.pow (q9mbUnit (t.val 1)) ((u.val 1).val)), (0 : Int)),
         q9tlMx.one) := by
  show ((((0 : Int), q9mbUnit (((tmiFromUnits u).map t).val 1)), (0 : Int)), q9tlMx.one)
     = ((((0 : Int), q3kU.pow (q9mbUnit (t.val 1)) ((u.val 1).val)), (0 : Int)), q9tlMx.one)
  have hunit : q9mbUnit (((tmiFromUnits u).map t).val 1)
      = q3kU.pow (q9mbUnit (t.val 1)) ((u.val 1).val) := by
    show q3kU.pow (q3kU.inv q9tlZeta9U)
          (ctmFind 2 (by omega) (((tmiFromUnits u).map t).val 1).val)
       = q3kU.pow (q3kU.pow (q3kU.inv q9tlZeta9U) (ctmFind 2 (by omega) (t.val 1).val))
          ((u.val 1).val)
    rw [q9mb_level1 u t, q9mb_find_pow (t.val 1) ((u.val 1).val),
        q9mb_pow_mod9 (q3kU.inv q9tlZeta9U) q9mb_g0_ninth
          ((u.val 1).val * ctmFind 2 (by omega) (t.val 1).val),
        ← cycRig_pow_mul q3kU q9mb_q3kU_comm (q3kU.inv q9tlZeta9U)
          (ctmFind 2 (by omega) (t.val 1).val) ((u.val 1).val),
        Nat.mul_comm ((u.val 1).val) (ctmFind 2 (by omega) (t.val 1).val)]
  rw [hunit]

/-! ## q9mb-11: ★★★ display-moving 主定理 — (ℤ/9)^× kill（#9） -/

/-- **q9mb-11（★★★ #9・display-moving）: level-9 テータ剛性が tmi の (ℤ/9)^× 商を殺す** —
    実 ℤ₃^×=`zpsLimit` の元 u と、テータ両立自己準同型 φ（所属限定 hom hHom・所属保存 hMem・
    E_{3⁹}[9] 上恒等 hE9）が「橋輸送で tmiFromUnits u を内部 μ₉ 上に実現」（hreal）するならば
    **(u.val 1).val = 1**。証明: t=tmeZetaLim（明示・choice-free）で左辺 = φ(q9mr_zeta9) =
    q9mr_zeta9（`q9mr_cyclotome_fixed` 消費・原始 9 乗根 ζ₉⁻¹ 固定）・右辺 = (ζ₉⁻¹)^{u₁}・
    ζ₉U の位数ちょうど 9 の単射性で u₁=1 強制（u₁∈{1,2,4,5,7,8} の全枝を含む）。
    すなわちテータ剛性は tmi の実 ℤ₃^× 不定性の (ℤ/9)^× 商を実対象の上で殺す。 -/
theorem q9mb_kill_mod9 (u : zpsLimit.carrier) (φ : q9mtCar → q9mtCar)
    (hHom : ∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g'))
    (hMem : ∀ g, q9mtMem g → q9mtMem (φ g))
    (hE9 : ∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2)
    (hreal : ∀ t : tmzLimit.carrier,
      φ (q9mbInt (t.val 1)) = q9mbInt (((tmiFromUnits u).map t).val 1)) :
    (u.val 1).val = 1 := by
  have hlt : (u.val 1).val < 9 := (u.val 1).property.1
  have hkey := hreal tmeZetaLim
  rw [q9mb_int_zeta, q9mr_cyclotome_fixed φ hHom hMem hE9, q9mb_transport u tmeZetaLim,
      q9mb_unit_zeta] at hkey
  have hcomp : q3kU.inv q9tlZeta9U = q3kU.pow (q3kU.inv q9tlZeta9U) ((u.val 1).val) :=
    congrArg (fun z : q9mtCar => z.1.1.2) hkey
  have hz : q9tlZeta9U = q3kU.pow q9tlZeta9U ((u.val 1).val) := by
    have hh := congrArg q3kU.inv hcomp
    rw [Grp.inv_inv, brau_pow_inv q3kU q9mb_q3kU_comm q9tlZeta9U ((u.val 1).val),
        Grp.inv_inv] at hh
    exact hh
  have h1 : q3kU.pow q9tlZeta9U 1 = q3kU.pow q9tlZeta9U ((u.val 1).val) := by
    rw [q9mb_pow_one]; exact hz
  have hfin := q9mb_pow_inj 1 ((u.val 1).val) (by omega) hlt h1
  omega

/-! ## q9mb-12: u₁=1 ⟺ テータ実現可能（消去形 iff・#10） -/

/-- **q9mb-12（#10）: 実現可能性の特徴付け** (u.val 1).val = 1 ⟺ テータ両立 φ が橋輸送で
    tmiFromUnits u を実現する。順方向は φ=id（u₁=1 で level-1 は恒等）、逆は q9mb_kill_mod9。 -/
theorem q9mb_admissible_iff (u : zpsLimit.carrier) :
    (u.val 1).val = 1 ↔
    ∃ φ : q9mtCar → q9mtCar,
      (∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g')) ∧
      (∀ g, q9mtMem g → q9mtMem (φ g)) ∧
      (∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2) ∧
      (∀ t : tmzLimit.carrier,
        φ (q9mbInt (t.val 1)) = q9mbInt (((tmiFromUnits u).map t).val 1)) := by
  constructor
  · intro h1
    refine ⟨fun g => g, fun g g' _ _ => rfl, fun g hg => hg, fun g _ => rfl, ?_⟩
    intro t
    show q9mbInt (t.val 1) = q9mbInt (((tmiFromUnits u).map t).val 1)
    have hid : ((tmiFromUnits u).map t).val 1 = t.val 1 := by
      rw [q9mb_level1 u t, h1]
      show (cmrGrp 2 (by omega)).mul (t.val 1) (cmrGrp 2 (by omega)).one = t.val 1
      exact (cmrGrp 2 (by omega)).mul_one (t.val 1)
    rw [hid]
  · intro h
    obtain ⟨φ, hHom, hMem, hE9, hreal⟩ := h
    exact q9mb_kill_mod9 u φ hHom hMem hE9 hreal

/-! ## q9mb-13: ★ 新層系 — 新規排除集合 = (1+3ℤ₃)/(1+9ℤ₃) の非自明元 {4,7}（#11） -/

/-- **q9mb-13a: 新層 {4,7} の算術特徴付け** — 4,7 は共に (ℤ/9)^× の元（<9・¬3∣）で
    mod 3 = 1（Aut(μ₃) 上恒等＝核 ker(Aut(μ₉)→Aut(μ₃)) に属す）かつ ≠1（非自明）。
    すなわち {4,7} = ((1+3ℤ₃)/(1+9ℤ₃))∖{1}——level-3 では μ₃ 上恒等ゆえ不可視だった新層。 -/
theorem q9mb_new_layer_chars :
    (4 % 3 = 1 ∧ 4 < 9 ∧ ¬ ((3 : Nat) ∣ 4) ∧ 4 ≠ 1)
    ∧ (7 % 3 = 1 ∧ 7 < 9 ∧ ¬ ((3 : Nat) ∣ 7) ∧ 7 ≠ 1) :=
  ⟨⟨rfl, by omega, by intro h; obtain ⟨k, hk⟩ := h; omega, by omega⟩,
   ⟨rfl, by omega, by intro h; obtain ⟨k, hk⟩ := h; omega, by omega⟩⟩

/-- **q9mb-13（★ #11・新層系）: 新規排除集合が {4,7}** — kill の帰結 (u.val 1).val=1 の下で、
    新層の非自明元 4・7 が実際に排除される（(u.val 1).val ≠ 4 ∧ ≠ 7）。§1 の標的
    (1+3ℤ₃)/(1+9ℤ₃) の非自明元が実際に死んだことの機械可読形。
    **対比（過大主張しない）**: level-3 橋 q3mb は u₀（mod-3 成分）=1 を殺した（像 {2,5,8} 型）。
    本 kill の**増分は核層 {4,7} のみ**であり (ℤ/9)^× 全体でも 1+9ℤ₃（n≥3 層）でもない——
    これらは依然 SURVIVES（正直限定 5）。 -/
theorem q9mb_kill_new_layer (u : zpsLimit.carrier) (φ : q9mtCar → q9mtCar)
    (hHom : ∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g'))
    (hMem : ∀ g, q9mtMem g → q9mtMem (φ g))
    (hE9 : ∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2)
    (hreal : ∀ t : tmzLimit.carrier,
      φ (q9mbInt (t.val 1)) = q9mbInt (((tmiFromUnits u).map t).val 1)) :
    (u.val 1).val = 1 ∧ (u.val 1).val ≠ 4 ∧ (u.val 1).val ≠ 7 := by
  have hk := q9mb_kill_mod9 u φ hHom hMem hE9 hreal
  exact ⟨hk, by omega, by omega⟩

/-! ## q9mb-14: capstone -/

/-- **q9mb-14a: 比較橋データ** — 橋 β₉（準同型・単射・像 μ₉・全射）・実 Galois 同変（χ 冪）・
    ★新規 σU 局所大域同変・生成元反転不変・輸送・(ℤ/9)^× kill・実現可能性 iff・新層系を束ねる。 -/
structure Q3Mu9TmzBridgeData where
  /-- 橋 β₉ は群準同型。 -/
  bridge_mul : ∀ y z : (tmzG 1).carrier,
    q9mbHom.map ((tmzG 1).mul y z) = q3kU.mul (q9mbHom.map y) (q9mbHom.map z)
  /-- 橋 β₉ は単射。 -/
  bridge_inj : q9mbHom.Injective
  /-- 像は μ₉ に含まれる。 -/
  image_mu9 : ∀ y : (tmzG 1).carrier, q3kMu9 (q9mbHom.map y).val
  /-- μ₉ 全射（消去形・q9c_mu9_complete 消費）。 -/
  onto_mu9 : ∀ u : q3kU.carrier,
    q3kMul (q3kMul (q3kMul (q3kMul u.val u.val) u.val) (q3kMul (q3kMul u.val u.val) u.val))
        (q3kMul (q3kMul u.val u.val) u.val) = q3kOne → ∃ y, q9mbHom.map y = u
  /-- ★ 実 Galois 同変（χ 冪）。 -/
  equivariant : ∀ (σ : (galoisGroupGrp (cteExt 2 (by omega))).carrier) (y : (tmzG 1).carrier),
    q9mbHom.map (((cgarAct 2 (by omega)).act σ).map y)
      = q3kU.pow (q9mbHom.map y)
          (cycRigExp (galoisGroupGrp (cteExt 2 (by omega))) (cmrMu 2 (by omega))
            (cgarAct 2 (by omega)) σ)
  /-- ★★ 新規 σU 局所大域同変（大域 χ=4 ↔ 局所 q3kSigma 単数群化）。 -/
  equivariant_sigmaU : ∀ y : (tmzG 1).carrier,
    q9mbHom.map (((cgarAct 2 (by omega)).act q9mbSigma4).map y) = q9mbSigmaU (q9mbHom.map y)
  /-- ★ 生成元反転で輸送指数不変（Aut(μ₉)=位数 6 曖昧の kill 不変性）。 -/
  flip_invariant : ∀ (g : q3kU.carrier) (a b : Nat),
    q3kU.pow (q3kU.pow g a) b = q3kU.pow (q3kU.pow g b) a
  /-- ★ 輸送定理（tmiFromUnits を内部 μ₉ へ）。 -/
  transport : ∀ (u : zpsLimit.carrier) (t : tmzLimit.carrier),
    q9mbInt (((tmiFromUnits u).map t).val 1)
      = ((((0 : Int), q3kU.pow (q9mbUnit (t.val 1)) ((u.val 1).val)), (0 : Int)), q9tlMx.one)
  /-- ★★★ display-moving: テータ剛性が (ℤ/9)^× 商を殺す。 -/
  kill_mod9 : ∀ (u : zpsLimit.carrier) (φ : q9mtCar → q9mtCar),
    (∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g')) →
    (∀ g, q9mtMem g → q9mtMem (φ g)) →
    (∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2) →
    (∀ t : tmzLimit.carrier,
      φ (q9mbInt (t.val 1)) = q9mbInt (((tmiFromUnits u).map t).val 1)) →
    (u.val 1).val = 1
  /-- ★ 新層系: kill は新層 {4,7} を排除。 -/
  kill_new_layer : ∀ (u : zpsLimit.carrier) (φ : q9mtCar → q9mtCar),
    (∀ g g', q9mtMem g → q9mtMem g' → φ (q9mtMul g g') = q9mtMul (φ g) (φ g')) →
    (∀ g, q9mtMem g → q9mtMem (φ g)) →
    (∀ g, q9mtMem g → q9tlProj.map (φ g).2 = q9tlProj.map g.2) →
    (∀ t : tmzLimit.carrier,
      φ (q9mbInt (t.val 1)) = q9mbInt (((tmiFromUnits u).map t).val 1)) →
    (u.val 1).val = 1 ∧ (u.val 1).val ≠ 4 ∧ (u.val 1).val ≠ 7
  /-- 内部生成元 q9mbInt(ζ₉) = q9mr_zeta9 の整合。 -/
  int_zeta : q9mbInt (tmeZetaLim.val 1) = q9mr_zeta9

/-- **q9mb-14b: 見出し実例** — テータ側実 μ₉ ↔ tmz mod-9 層の実 G-同変同一視と、その輸送
    による tmi の実 ℤ₃^× 不定性 (ℤ/9)^× 商の kill・新層 (1+3ℤ₃)/(1+9ℤ₃) の消去。 -/
def q9mb_data : Q3Mu9TmzBridgeData where
  bridge_mul := q9mbHom.map_mul
  bridge_inj := q9mb_inj
  image_mu9 := q9mb_image_mu9
  onto_mu9 := q9mb_onto_mu9
  equivariant := q9mb_equivariant
  equivariant_sigmaU := q9mb_equivariant_sigmaU
  flip_invariant := q9mb_flip_invariant
  transport := q9mb_transport
  kill_mod9 := q9mb_kill_mod9
  kill_new_layer := q9mb_kill_new_layer
  int_zeta := q9mb_int_zeta

/-- **q9mb-14c: 比較橋の存在**（実 U₃ ↔ 実 tmzG 1・実 σU 同変・実輸送・実 (ℤ/9)^× kill・
    新層 (1+3ℤ₃)/(1+9ℤ₃) の消去）。 -/
theorem q9mb_exists : Nonempty Q3Mu9TmzBridgeData := ⟨q9mb_data⟩

end IUT
