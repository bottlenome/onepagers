/-
  IUT/TripodTwinCover.lean — BLW-3: tripod の **twin 合成被覆**（単一環 K[u,v] 上の
  μ₃×μ₃ 合成デッキ）── 柱A・項目 A9（Belyi 化 / 遠アーベル幾何入力(実)）

  分類 **[実／(b) 本物の先行建設]**（骨格・模型・代理でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無・toy 模型を定理の主語にしない）。

  **complete_pct 影響（A9 BLW-3）**: BLW-2（`TripodKummerMu3`）の正直な限定 2
  「実現は商ごと——単一の (ℤ/3)² 被覆（ファイバー積）は未達」を一段前進させる。
  BLW-2 の μ₃×μ₃ 作用は「二つの環の直積集合」への成分ごとの作用だったが、本ファイルは
  **単一の実二変数多項式環 K[u,v] = (K[v])[u]**（二被覆のテンソル積 K[u]⊗_K K[v] =
  K 上の被覆の合成）を建て、その上に μ₃×μ₃ を**環自己同型**として同時作用させる:
   * 両方の Kummer 座標が同一環内に実在: **t = u³ は文字どおり u·(u·u)**
     （`ttc_T_cube`・BLW-2 では命名だけだった関係を環演算の定理に昇格、
     `ttc_kmuT_cube` で BLW-2 の kmuT = kmuVar³ も遡及証明）、
     **1−t′ = 1 − v·(v·v)**（`ttc_twinT_relation`）。
   * 合成デッキ (g,h)·F(u,v) = F(gu, hv) は **RingHom**（`ttcSigma`・加法/乗法/単位
     保存を psMap/psScale 汎用則から完全証明）かつ両側逆つき（`ttc_deck_inv_act`）
     = 環自己同型。genuine な `GAction kmuMu3Sq`（`ttcDeck`）。
   * **忠実性が単一環レベルで**成立（`ttc_deck_faithful`: 同じ環の 2 元 u, v への
     作用が (g,h) を復元）——BLW-2 の tkm-8c は直積集合上だった。
   * **合成 Kummer descent**（`ttc_composite_descent`）: μ₃×μ₃ **全体**の固定環 =
     台が 3ℕ×3ℕ の部分環 K[u³,v³]（両基礎座標 t=u³, 1−t′=v³ を含む）。BLW-2 の
     tkm-4h（一変数・生成元 ζ のみ）の真の二変数強化。
   * **F₂ との接続**（`ttcF2Deck`・`ttc_f2_deck_surjective`）: BLW-4 の実現準同型
     trbRealize を通じ、tripod π₁ の群論的内容 F₂ が**この単一被覆環にデッキ変換と
     して作用**し、a は u-デッキ・b は v-デッキに命中（`ttc_f2_act_a/b`）、全ての
     (ζⁱ,ζʲ) デッキ変換が F₂ の語で実現される（非自明性 `ttc_f2_act_a_ne_id`）。
  予測 s_A9 寄与は小さい前進（+0.00–0.02・独立監査確定が条件・bundle 全体の
  ~0.20 予測へ向けた深化）。graph-meta.json の更新は親が独立監査通過後に行う。

  **正直な限定**（消去・弱化禁止・BLW-1(tfg)・BLW-2(kmu)・BLW-4(trb)・blc・blr の
  限定を全文継承）:
   1. **「tripod の π₁ そのもの」ではない**: 位相ループの群 π₁^top・スキームの
      π₁^ét = F̂₂（副有限完備化）・π₁^temp との同定は不主張（ℂ・位相・被覆空間・
      エタールサイトが core に無いリポジトリ恒久限定の継承）。実現されるのは相変わらず
      有限 ℤ/3×ℤ/3 商のデッキであって F̂₂ ではない。
   2. **基底 ℙ¹ 上のファイバー積（真の twin 被覆）は未達**: 本環 K[u,v] は二つの
      Kummer 被覆の **K 上の**合成（テンソル積・A² の被覆）であり、二つの基礎座標
      t = u³ と t′ = 1−v³ は独立のまま。同一視 t = t′（イデアル (u³+v³−1) による商・
      Fermat 3 次曲線環 = tripod 上の真のファイバー積）は取っていない
      （named future target）。「tripod 性」は BLW-2 と同じく分岐値 ⊆ {0,1,∞} の
      対言明（kmu_branch_u/v）で顕示される。
   3. **π₁^ét = F̂₂・π₁^temp・residual finiteness・Belyi cuspidalization
      （[AbsTopII]）・noncritical Belyi（[GenEll]）は 0 のまま**（blc/blr の正直限定を
      全文継承・並置）。**A9 cap ≤ ~0.35**（これら本丸が 0 の間）。
   4. K = ℚ(ζ₃)・3 次 Kummer スライス固定（p=3 恒久限定の族）。位相・解析なし。
      K の担体は Cq3 系実商環 ℚ[x]/(x²+x+1)（BLW-2 の限定 5 の継承）。
   5. F₂ の合成作用（`ttcF2Deck`）は忠実でない（核 ⊇ 交換子・立方、BLW-4 の
      核観察のとおり）。忠実なのはデッキ群 μ₃×μ₃ の作用（`ttc_deck_faithful`）。

  二重計上の排除（監査向け）:
   - psScale/psMap/rsum_single/ringHom_rpow（M86F・M46・M40 等の汎用部品）は
     **消費のみ・再証明ゼロ**。単一二変数環・合成デッキ環自己同型・二変数 descent・
     u³/v³ の環演算的実現・F₂ 語によるデッキ全実現は全て本ファイルの新言明。
   - BLW-1/2/4（tfg/kmu/trb）の定理は消費のみ（kmu_kummer_descent は v 方向で消費、
     u 方向と二変数への束ねが新規）。

  全て選択公理不使用（`#print axioms` = [propext, Quot.sound]）。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用（omega は Nat 算術のみ）。共有ファイル（IUT.lean・build.sh・
  dashboard.md・graph 系）は一切変更しない。新規ファイル 1 個のみ。
-/
import IUT.TripodRealizationBundle
import IUT.PSFunctor
import IUT.Composition
import IUT.LTErrorDivisible

namespace IUT

/-! ## ttc-0: twin 合成被覆環 K[u,v] = (K[v])[u] と生成元・両 Kummer 座標 -/

/-- **ttc-0a: 内側の環 K[v]**（BLW-2 の被覆環そのもの）。 -/
abbrev ttcBase : CRing := polyCRing kmuK

/-- **ttc-0b: twin 合成被覆環 K[u,v] = (K[v])[u]**（二 Kummer 被覆の K 上の合成
    = K[u] ⊗_K K[v] の実装。単一の本物の可換環）。 -/
abbrev ttcRing : CRing := polyCRing ttcBase

/-- **ttc-0c: 生成元 u**（外側変数）。 -/
def ttcU : ttcRing.carrier := ⟨psX ttcBase, ⟨2, fun i hi => if_neg (by omega)⟩⟩

/-- **ttc-0d: 生成元 v**（内側変数 kmuVar の定数埋め込み）。u と同一環の元。 -/
def ttcV : ttcRing.carrier := (polyC ttcBase).map kmuVar

/-- **ttc-0e: u 側 Kummer 座標 t = u³** ∈ K[u,v]。 -/
def ttcT : ttcRing.carrier :=
  ⟨psSingle ttcBase ttcBase.one 3, ⟨4, fun i hi => if_neg (by omega)⟩⟩

/-- **ttc-0f: v 側 Kummer 座標 1 − v³**（BLW-2 の kmuTwin の埋め込み）∈ K[u,v]。
    両 Kummer 座標が**同一環**に共存する（BLW-2 では別々の環だった）。 -/
def ttcTwinT : ttcRing.carrier := (polyC ttcBase).map kmuTwin

/-! ## ttc-1: X³ = 単項式 X^3 の環演算的証明（「u³」を命名から定理へ） -/

/-- **ttc-1a: psX = psSingle 1**（定義の一致）。 -/
theorem ttc_psX_eq_single (R : CRing) : psX R = psSingle R R.one 1 := rfl

/-- **ttc-1b: X · X^m = X^(m+1)**（Cauchy 積の一点集中）。 -/
theorem ttc_psX_mul_single (R : CRing) (m : Nat) :
    psMul R (psX R) (psSingle R R.one m) = psSingle R R.one (m + 1) := by
  funext n
  show rsum R (fun k => R.mul (psX R k) (psSingle R R.one m (n - k))) (n + 1)
    = psSingle R R.one (m + 1) n
  cases Nat.decEq n (m + 1) with
  | isTrue he =>
    subst he
    rw [show psSingle R R.one (m + 1) (m + 1) = R.one from if_pos rfl,
      rsum_single R (fun k => R.mul (psX R k) (psSingle R R.one m (m + 1 - k))) 1
        (m + 1 + 1) (by omega)
        (fun j _ hne => by
          show R.mul (psX R j) (psSingle R R.one m (m + 1 - j)) = R.zero
          rw [show psX R j = R.zero from if_neg hne]
          exact CRing.zero_mul R (psSingle R R.one m (m + 1 - j)))]
    show R.mul (psX R 1) (psSingle R R.one m (m + 1 - 1)) = R.one
    rw [show psX R 1 = R.one from if_pos rfl,
      show psSingle R R.one m (m + 1 - 1) = R.one from if_pos rfl]
    exact R.one_mul R.one
  | isFalse hne =>
    rw [show psSingle R R.one (m + 1) n = R.zero from if_neg hne]
    have hz : rsum R (fun k => R.mul (psX R k) (psSingle R R.one m (n - k))) (n + 1)
        = rsum R (fun _ => R.zero) (n + 1) :=
      rsum_congr R (n + 1) (fun k hk => by
        show R.mul (psX R k) (psSingle R R.one m (n - k)) = R.zero
        cases Nat.decEq k 1 with
        | isTrue hk1 =>
          subst hk1
          rw [show psSingle R R.one m (n - 1) = R.zero from if_neg (by omega)]
          exact CRing.mul_zero R (psX R 1)
        | isFalse hk1 =>
          rw [show psX R k = R.zero from if_neg hk1]
          exact CRing.zero_mul R (psSingle R R.one m (n - k)))
    rw [hz]
    exact rsum_const_zero R (n + 1)

/-- **定理 (ttc-1c): X·(X·X) = X³（単項式）** — 「u³」という命名を実際の環乗法の
    定理に昇格させる核計算。 -/
theorem ttc_psX_cube (R : CRing) :
    psMul R (psX R) (psMul R (psX R) (psX R)) = psSingle R R.one 3 := by
  have h1 : psMul R (psX R) (psX R) = psSingle R R.one 2 := by
    have h := ttc_psX_mul_single R 1
    rw [← ttc_psX_eq_single R] at h
    exact h
  rw [h1]
  exact ttc_psX_mul_single R 2

/-- **定理 (ttc-1d): BLW-2 の基礎座標 kmuT は文字どおり kmuVar³** —
    BLW-2 が「t = u³」と命名していた関係の遡及的な環演算的証明（新規実内容）。 -/
theorem ttc_kmuT_cube :
    kmuT = (polyCRing kmuK).mul kmuVar ((polyCRing kmuK).mul kmuVar kmuVar) :=
  Subtype.ext (ttc_psX_cube kmuK).symm

/-- **定理 (ttc-1e): ttcT = u·(u·u)** — u 側 Kummer 座標は合成被覆環の環乗法で
    実際に u の 3 乗。 -/
theorem ttc_T_cube : ttcT = ttcRing.mul ttcU (ttcRing.mul ttcU ttcU) :=
  Subtype.ext (ttc_psX_cube ttcBase).symm

/-- **ttc-1f: kmuTwin = 1 + (−kmuT)**（K[v] の環演算形）。 -/
theorem ttc_kmuTwin_eq : kmuTwin = ttcBase.add ttcBase.one (ttcBase.neg kmuT) :=
  Subtype.ext rfl

/-- **定理 (ttc-1g): ttcTwinT = 1 − v·(v·v)** — v 側 Kummer 座標も同一環の
    環演算で実際に 1 − v³。両 Kummer 関係が単一環 K[u,v] 内で環演算的に成立。 -/
theorem ttc_twinT_relation :
    ttcTwinT = ttcRing.add ttcRing.one
      (ttcRing.neg (ttcRing.mul ttcV (ttcRing.mul ttcV ttcV))) := by
  have hv3 : ttcRing.mul ttcV (ttcRing.mul ttcV ttcV) = (polyC ttcBase).map kmuT := by
    show ttcRing.mul ((polyC ttcBase).map kmuVar)
        (ttcRing.mul ((polyC ttcBase).map kmuVar) ((polyC ttcBase).map kmuVar))
      = (polyC ttcBase).map kmuT
    rw [← (polyC ttcBase).map_mul kmuVar kmuVar,
      ← (polyC ttcBase).map_mul kmuVar (ttcBase.mul kmuVar kmuVar),
      ← ttc_kmuT_cube]
  show (polyC ttcBase).map kmuTwin = ttcRing.add ttcRing.one
      (ttcRing.neg (ttcRing.mul ttcV (ttcRing.mul ttcV ttcV)))
  rw [hv3, ttc_kmuTwin_eq,
    (polyC ttcBase).map_add ttcBase.one (ttcBase.neg kmuT),
    (polyC ttcBase).map_one, RingHom.map_neg (polyC ttcBase) kmuT]

/-! ## ttc-2: 合成デッキ写像 (g,h)·F(u,v) = F(gu, hv) は環準同型 -/

/-- **ttc-2a: 合成デッキ写像（係数実装）** — u 方向は外側 psScale（倍率 = 定数
    多項式 g）、v 方向は各係数への BLW-2 デッキ kmuSigma h。 -/
def ttcSigmaFun (g h : kmuK.carrier) (P : PS ttcBase) : PS ttcBase :=
  psScale ttcBase ((polyC kmuK).map g) (psMap (kmuSigma h) P)

/-- **ttc-2b: 合成デッキ写像は有界性（有限台）を保つ**。 -/
theorem ttc_sigmaFun_bounded (g h : kmuK.carrier) {P : PS ttcBase} {N : Nat}
    (hP : IsPolyBounded ttcBase P N) : IsPolyBounded ttcBase (ttcSigmaFun g h P) N := by
  intro i hi
  show ttcBase.mul (rpow ttcBase ((polyC kmuK).map g) i) (kmuPolyScale h (P i))
    = ttcBase.zero
  rw [hP i hi,
    show kmuPolyScale h ttcBase.zero = ttcBase.zero from RingHom.map_zero (kmuSigma h),
    CRing.mul_zero ttcBase (rpow ttcBase ((polyC kmuK).map g) i)]

/-- **定理 (ttc-2c): 合成デッキ変換は環準同型** K[u,v] → K[u,v] —
    加法・乗法・単位の保存を psMap（v 方向・M46-3）と psScale（u 方向・M86F）の
    汎用保存則から完全証明。 -/
def ttcSigma (g h : kmuK.carrier) : RingHom ttcRing ttcRing where
  map := fun F => ⟨ttcSigmaFun g h F.val, by
    obtain ⟨N, hN⟩ := F.property
    exact ⟨N, ttc_sigmaFun_bounded g h hN⟩⟩
  map_add := fun a b => Subtype.ext (by
    show psScale ttcBase ((polyC kmuK).map g)
        (psMap (kmuSigma h) (psAdd ttcBase a.val b.val))
      = psAdd ttcBase
          (psScale ttcBase ((polyC kmuK).map g) (psMap (kmuSigma h) a.val))
          (psScale ttcBase ((polyC kmuK).map g) (psMap (kmuSigma h) b.val))
    rw [psMap_add (kmuSigma h) a.val b.val,
      psScale_add ttcBase ((polyC kmuK).map g)
        (psMap (kmuSigma h) a.val) (psMap (kmuSigma h) b.val)])
  map_mul := fun a b => Subtype.ext (by
    show psScale ttcBase ((polyC kmuK).map g)
        (psMap (kmuSigma h) (psMul ttcBase a.val b.val))
      = psMul ttcBase
          (psScale ttcBase ((polyC kmuK).map g) (psMap (kmuSigma h) a.val))
          (psScale ttcBase ((polyC kmuK).map g) (psMap (kmuSigma h) b.val))
    rw [psMap_mul (kmuSigma h) a.val b.val,
      psScale_mul ttcBase ((polyC kmuK).map g)
        (psMap (kmuSigma h) a.val) (psMap (kmuSigma h) b.val)])
  map_one := Subtype.ext (by
    show psScale ttcBase ((polyC kmuK).map g) (psMap (kmuSigma h) (psOne ttcBase))
      = psOne ttcBase
    rw [show psMap (kmuSigma h) (psOne ttcBase) = psOne ttcBase from
        funext fun n => by
          cases n with
          | zero => exact (kmuSigma h).map_one
          | succ k => exact RingHom.map_zero (kmuSigma h)]
    exact psScale_one ttcBase ((polyC kmuK).map g))

/-! ## ttc-3: デッキ群 μ₃×μ₃ の genuine な作用（GAction） -/

/-- u 側デッキ生成元 (ζ, 1) ∈ μ₃×μ₃。 -/
def ttcGU : kmuMu3Sq.carrier := (kmuMu3Zeta, kmuMu3.one)

/-- v 側デッキ生成元 (1, ζ) ∈ μ₃×μ₃。 -/
def ttcGV : kmuMu3Sq.carrier := (kmuMu3.one, kmuMu3Zeta)

/-- **ttc-3a: v 方向デッキの合成則**（psMap レベル・BLW-2 psScale_comp から）。 -/
theorem ttc_psMap_sigma_comp (h h' : kmuK.carrier) (P : PS ttcBase) :
    psMap (kmuSigma (kmuK.mul h h')) P = psMap (kmuSigma h) (psMap (kmuSigma h') P) :=
  funext fun m => Subtype.ext (psScale_comp kmuK h h' ((P m).val)).symm

/-- **ttc-3b: u 方向 psScale と v 方向 psMap は可換**（デッキの独立性——
    定数多項式は kmuSigma で固定・rpow は環準同型で保存）。 -/
theorem ttc_map_scale_comm (g' h : kmuK.carrier) (P : PS ttcBase) :
    psMap (kmuSigma h) (psScale ttcBase ((polyC kmuK).map g') P)
      = psScale ttcBase ((polyC kmuK).map g') (psMap (kmuSigma h) P) := by
  funext m
  show (kmuSigma h).map (ttcBase.mul (rpow ttcBase ((polyC kmuK).map g') m) (P m))
    = ttcBase.mul (rpow ttcBase ((polyC kmuK).map g') m) ((kmuSigma h).map (P m))
  rw [(kmuSigma h).map_mul (rpow ttcBase ((polyC kmuK).map g') m) (P m),
    show (kmuSigma h).map (rpow ttcBase ((polyC kmuK).map g') m)
        = rpow ttcBase ((polyC kmuK).map g') m from by
      rw [ringHom_rpow (kmuSigma h) ((polyC kmuK).map g') m, kmu_sigma_fixes_const h g']]

/-- **定理 (ttc-3c): μ₃×μ₃ の実デッキ作用**（単一環 K[u,v] 上・genuine な
    `GAction kmuMu3Sq`）— 作用則 act_one/act_mul を完全証明。BLW-2 tkm-8b は
    二環の直積集合への作用だったが、本作用は**単一の環**への作用であり、しかも
    各元は環準同型（ttcSigma）として作用する。 -/
def ttcDeck : GAction kmuMu3Sq where
  carrier := ttcRing.carrier
  act := fun gh F => (ttcSigma gh.1.val gh.2.val).map F
  act_one := fun F => Subtype.ext (by
    show psScale ttcBase ((polyC kmuK).map kmuK.one) (psMap (kmuSigma kmuK.one) F.val)
      = F.val
    rw [show psMap (kmuSigma kmuK.one) F.val = F.val from
        funext fun m => Subtype.ext (psScale_one_base kmuK ((F.val m).val)),
      (polyC kmuK).map_one]
    exact psScale_one_base ttcBase F.val)
  act_mul := fun gh gh' F => Subtype.ext (by
    show psScale ttcBase ((polyC kmuK).map (kmuK.mul gh.1.val gh'.1.val))
        (psMap (kmuSigma (kmuK.mul gh.2.val gh'.2.val)) F.val)
      = psScale ttcBase ((polyC kmuK).map gh.1.val)
          (psMap (kmuSigma gh.2.val)
            (psScale ttcBase ((polyC kmuK).map gh'.1.val)
              (psMap (kmuSigma gh'.2.val) F.val)))
    rw [ttc_map_scale_comm gh'.1.val gh.2.val (psMap (kmuSigma gh'.2.val) F.val),
      psScale_comp ttcBase ((polyC kmuK).map gh.1.val) ((polyC kmuK).map gh'.1.val)
        (psMap (kmuSigma gh.2.val) (psMap (kmuSigma gh'.2.val) F.val)),
      ← (polyC kmuK).map_mul gh.1.val gh'.1.val,
      ttc_psMap_sigma_comp gh.2.val gh'.2.val F.val])

/-- **ttc-3d: 各デッキ変換は環の乗法を保つ**（環自己準同型としての作用）。 -/
theorem ttc_deck_mul_hom (gh : kmuMu3Sq.carrier) (a b : ttcRing.carrier) :
    ttcDeck.act gh (ttcRing.mul a b)
      = ttcRing.mul (ttcDeck.act gh a) (ttcDeck.act gh b) :=
  (ttcSigma gh.1.val gh.2.val).map_mul a b

/-- **ttc-3e: 各デッキ変換は両側逆を持つ**（逆元のデッキが逆写像）——
    合成デッキは環**自己同型**。 -/
theorem ttc_deck_inv_act (gh : kmuMu3Sq.carrier) (F : ttcRing.carrier) :
    ttcDeck.act gh (ttcDeck.act (kmuMu3Sq.inv gh) F) = F := by
  rw [← ttcDeck.act_mul gh (kmuMu3Sq.inv gh) F, kmuMu3Sq.mul_inv gh]
  exact ttcDeck.act_one F

/-! ## ttc-4: 二重係数公式（以降の全計算の核） -/

/-- **ttc-4a: 定数多項式倍は係数ごとのスカラー倍**（Cauchy 積の一点集中）。 -/
theorem ttc_psC_mul_coeff (c : kmuK.carrier) (q : PS kmuK) (n : Nat) :
    psMul kmuK (psC kmuK c) q n = kmuK.mul c (q n) := by
  show rsum kmuK (fun k => kmuK.mul (psC kmuK c k) (q (n - k))) (n + 1)
    = kmuK.mul c (q n)
  rw [rsum_single kmuK (fun k => kmuK.mul (psC kmuK c k) (q (n - k))) 0 (n + 1)
      (by omega)
      (fun j _ hne => by
        show kmuK.mul (psC kmuK c j) (q (n - j)) = kmuK.zero
        rw [show psC kmuK c j = kmuK.zero from if_neg hne]
        exact CRing.zero_mul kmuK (q (n - j)))]
  show kmuK.mul (psC kmuK c 0) (q (n - 0)) = kmuK.mul c (q n)
  rw [show psC kmuK c 0 = c from if_pos rfl]
  rfl

/-- **定理 (ttc-4b): 合成デッキの二重係数公式** —
    ((g,h)·F) の (u^m v^n) 係数 = g^m·h^n·F_{m,n}。 -/
theorem ttc_coeff (g h : kmuK.carrier) (P : PS ttcBase) (m n : Nat) :
    ((ttcSigmaFun g h P) m).val n
      = kmuK.mul (rpow kmuK g m) (kmuK.mul (rpow kmuK h n) ((P m).val n)) := by
  show (ttcBase.mul (rpow ttcBase ((polyC kmuK).map g) m) (kmuPolyScale h (P m))).val n
    = kmuK.mul (rpow kmuK g m) (kmuK.mul (rpow kmuK h n) ((P m).val n))
  rw [show rpow ttcBase ((polyC kmuK).map g) m = (polyC kmuK).map (rpow kmuK g m) from
      (ringHom_rpow (polyC kmuK) g m).symm]
  show psMul kmuK (psC kmuK (rpow kmuK g m)) ((kmuPolyScale h (P m)).val) n
    = kmuK.mul (rpow kmuK g m) (kmuK.mul (rpow kmuK h n) ((P m).val n))
  rw [ttc_psC_mul_coeff (rpow kmuK g m) ((kmuPolyScale h (P m)).val) n]
  rfl

/-- **ttc-4c: 作用の二重係数公式**（GAction 形）。 -/
theorem ttc_act_coeff (gh : kmuMu3Sq.carrier) (F : ttcRing.carrier) (m n : Nat) :
    ((ttcDeck.act gh F).val m).val n
      = kmuK.mul (rpow kmuK gh.1.val m)
          (kmuK.mul (rpow kmuK gh.2.val n) ((F.val m).val n)) :=
  ttc_coeff gh.1.val gh.2.val F.val m n

/-- rpow の指数 1。 -/
theorem ttc_rpow_one_exp (x : kmuK.carrier) : rpow kmuK x 1 = x := kmuK.one_mul x

/-- **ttc-4d: u 側生成元 (ζ,1) の係数公式**。 -/
theorem ttc_act_coeff_gu (F : ttcRing.carrier) (m n : Nat) :
    ((ttcDeck.act ttcGU F).val m).val n
      = kmuK.mul (rpow kmuK kmuZeta m) ((F.val m).val n) := by
  have h := ttc_act_coeff ttcGU F m n
  rw [show rpow kmuK ttcGU.2.val n = kmuK.one from rpow_one_base kmuK n,
    kmuK.one_mul ((F.val m).val n)] at h
  exact h

/-- **ttc-4e: v 側生成元 (1,ζ) の係数公式**。 -/
theorem ttc_act_coeff_gv (F : ttcRing.carrier) (m n : Nat) :
    ((ttcDeck.act ttcGV F).val m).val n
      = kmuK.mul (rpow kmuK kmuZeta n) ((F.val m).val n) := by
  have h := ttc_act_coeff ttcGV F m n
  rw [show rpow kmuK ttcGV.1.val m = kmuK.one from rpow_one_base kmuK m,
    kmuK.one_mul (kmuK.mul (rpow kmuK ttcGV.2.val n) ((F.val m).val n))] at h
  exact h

/-! ## ttc-5: 忠実性（単一環の 2 元 u, v への作用が (g,h) を復元） -/

/-- **定理 (ttc-5a): 合成デッキ作用は忠実** — **同一環内の** 2 元 u と v への作用が
    一致すれば (g,h) は一致する（u の係数 (1,0) が g を、v の係数 (0,1) が h を
    そのまま読み出す）。BLW-2 tkm-8c（二環の直積上）の単一環への強化。 -/
theorem ttc_deck_faithful (gh gh' : kmuMu3Sq.carrier)
    (hU : ttcDeck.act gh ttcU = ttcDeck.act gh' ttcU)
    (hV : ttcDeck.act gh ttcV = ttcDeck.act gh' ttcV) : gh = gh' := by
  have hg : gh.1.val = gh'.1.val := by
    have h1 : ((ttcDeck.act gh ttcU).val 1).val 0
        = ((ttcDeck.act gh' ttcU).val 1).val 0 :=
      congrFun (congrArg Subtype.val (congrFun (congrArg Subtype.val hU) 1)) 0
    rw [ttc_act_coeff gh ttcU 1 0, ttc_act_coeff gh' ttcU 1 0,
      show ((ttcU.val 1).val 0) = kmuK.one from rfl,
      show rpow kmuK gh.2.val 0 = kmuK.one from rfl,
      show rpow kmuK gh'.2.val 0 = kmuK.one from rfl,
      kmuK.one_mul kmuK.one,
      ttc_rpow_one_exp gh.1.val, ttc_rpow_one_exp gh'.1.val,
      CRing.mul_one kmuK gh.1.val, CRing.mul_one kmuK gh'.1.val] at h1
    exact h1
  have hh : gh.2.val = gh'.2.val := by
    have h2 : ((ttcDeck.act gh ttcV).val 0).val 1
        = ((ttcDeck.act gh' ttcV).val 0).val 1 :=
      congrFun (congrArg Subtype.val (congrFun (congrArg Subtype.val hV) 0)) 1
    rw [ttc_act_coeff gh ttcV 0 1, ttc_act_coeff gh' ttcV 0 1,
      show ((ttcV.val 0).val 1) = kmuK.one from rfl,
      show rpow kmuK gh.1.val 0 = kmuK.one from rfl,
      show rpow kmuK gh'.1.val 0 = kmuK.one from rfl,
      ttc_rpow_one_exp gh.2.val, ttc_rpow_one_exp gh'.2.val,
      CRing.mul_one kmuK gh.2.val, CRing.mul_one kmuK gh'.2.val,
      kmuK.one_mul gh.2.val, kmuK.one_mul gh'.2.val] at h2
    exact h2
  have e1 : gh.1 = gh'.1 := Subtype.ext hg
  have e2 : gh.2 = gh'.2 := Subtype.ext hh
  show (gh.1, gh.2) = (gh'.1, gh'.2)
  rw [e1, e2]

/-! ## ttc-6: 合成 Kummer descent（μ₃×μ₃ 全体の固定環 = K[u³,v³]） -/

/-- **ttc-6a: 二変数基礎台条件** — 台 ⊆ 3ℕ×3ℕ（= K[u³,v³] の像・両基礎座標
    t=u³, 1−t′=v³ を含む部分環）。 -/
def ttcBaseSupport (F : ttcRing.carrier) : Prop :=
  ∀ m n : Nat, (m % 3 ≠ 0 ∨ n % 3 ≠ 0) → (F.val m).val n = kmuK.zero

/-- ζ 係数の固定は零を強制（3∤e）——BLW-2 tkm-4f の核代数の再利用形。 -/
theorem ttc_scalar_fix (e : Nat) (he : e % 3 ≠ 0) (x : kmuK.carrier)
    (hfix : kmuK.mul (rpow kmuK kmuZeta e) x = x) : x = kmuK.zero := by
  have hne : rpow kmuK kmuZeta e ≠ kmuK.one := kmu_zeta_pow_ne_one e he
  have hsub : kmuK.add (rpow kmuK kmuZeta e) (kmuK.neg kmuK.one) ≠ kmuK.zero := by
    intro hz
    exact hne (CRing.eq_of_sub_eq_zero kmuK hz)
  apply kmu_no_zero_div (kmuK.add (rpow kmuK kmuZeta e) (kmuK.neg kmuK.one)) x _ hsub
  rw [CRing.right_distrib kmuK (rpow kmuK kmuZeta e) (kmuK.neg kmuK.one) x,
    CRing.neg_mul kmuK kmuK.one x, kmuK.one_mul x, hfix, CRing.add_neg kmuK x]

/-- 位数 3 の元の 3 の倍数冪は 1（帰納）。 -/
theorem ttc_rpow_cube_one (x : kmuK.carrier) (hx : rpow kmuK x 3 = kmuK.one) :
    ∀ q, rpow kmuK x (3 * q) = kmuK.one := by
  intro q
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 3 * (q + 1) = 3 * q + 3 from by omega, rpow_add kmuK x (3 * q) 3, ih, hx,
      kmuK.one_mul kmuK.one]

/-- 位数 3 の元の 3∣m 冪は 1。 -/
theorem ttc_rpow_mod0 (x : kmuK.carrier) (hx : rpow kmuK x 3 = kmuK.one)
    (m : Nat) (hm : m % 3 = 0) : rpow kmuK x m = kmuK.one := by
  rw [show m = 3 * (m / 3) from by omega]
  exact ttc_rpow_cube_one x hx (m / 3)

/-- **ttc-6b: 二生成元で固定 ⟹ 基礎台**（u 方向は ζ^m 消去・v 方向も ζ^n 消去）。 -/
theorem ttc_fixed_imp_base (F : ttcRing.carrier)
    (hU : ttcDeck.act ttcGU F = F) (hV : ttcDeck.act ttcGV F = F) :
    ttcBaseSupport F := by
  intro m n hor
  cases hor with
  | inl hm =>
    have h1 : ((ttcDeck.act ttcGU F).val m).val n = (F.val m).val n :=
      congrFun (congrArg Subtype.val (congrFun (congrArg Subtype.val hU) m)) n
    rw [ttc_act_coeff_gu F m n] at h1
    exact ttc_scalar_fix m hm ((F.val m).val n) h1
  | inr hn =>
    have h1 : ((ttcDeck.act ttcGV F).val m).val n = (F.val m).val n :=
      congrFun (congrArg Subtype.val (congrFun (congrArg Subtype.val hV) m)) n
    rw [ttc_act_coeff_gv F m n] at h1
    exact ttc_scalar_fix n hn ((F.val m).val n) h1

/-- **ttc-6c: 基礎台 ⟹ μ₃×μ₃ の全元で固定**（g³=h³=1 から g^{3a}=h^{3b}=1）。 -/
theorem ttc_base_imp_fixed (F : ttcRing.carrier) (hb : ttcBaseSupport F) :
    ∀ gh : kmuMu3Sq.carrier, ttcDeck.act gh F = F := by
  intro gh
  apply Subtype.ext
  funext m
  apply Subtype.ext
  funext n
  show ((ttcDeck.act gh F).val m).val n = (F.val m).val n
  rw [ttc_act_coeff gh F m n]
  cases Nat.decEq (m % 3) 0 with
  | isTrue hm =>
    cases Nat.decEq (n % 3) 0 with
    | isTrue hn =>
      rw [ttc_rpow_mod0 gh.1.val gh.1.property m hm,
        ttc_rpow_mod0 gh.2.val gh.2.property n hn,
        kmuK.one_mul ((F.val m).val n), kmuK.one_mul ((F.val m).val n)]
    | isFalse hn =>
      rw [hb m n (Or.inr hn), CRing.mul_zero kmuK (rpow kmuK gh.2.val n),
        CRing.mul_zero kmuK (rpow kmuK gh.1.val m)]
  | isFalse hm =>
    rw [hb m n (Or.inl hm), CRing.mul_zero kmuK (rpow kmuK gh.2.val n),
      CRing.mul_zero kmuK (rpow kmuK gh.1.val m)]

/-- **定理 (ttc-6d): 合成 Kummer descent** — F が **μ₃×μ₃ の全元**で固定される ⟺
    台 ⊆ 3ℕ×3ℕ（= 基礎環 K[u³,v³]）。BLW-2 tkm-4h（一変数・生成元 ζ のみ）の
    二変数・全群強化。デッキ群全体の固定環がちょうど両基礎座標の生成する側にある
    ことの単一環内での言明。 -/
theorem ttc_composite_descent (F : ttcRing.carrier) :
    (∀ gh : kmuMu3Sq.carrier, ttcDeck.act gh F = F) ↔ ttcBaseSupport F :=
  ⟨fun hfix => ttc_fixed_imp_base F (hfix ttcGU) (hfix ttcGV), ttc_base_imp_fixed F⟩

/-! ## ttc-7: 両 Kummer 座標のデッキ固定（μ₃×μ₃ 全体・descent 経由） -/

/-- u 側座標 t = u³ は基礎台。 -/
theorem ttc_T_base : ttcBaseSupport ttcT := by
  intro m n hor
  show (psSingle ttcBase ttcBase.one 3 m).val n = kmuK.zero
  cases Nat.decEq m 3 with
  | isTrue hm3 =>
    subst hm3
    rw [show psSingle ttcBase ttcBase.one 3 3 = ttcBase.one from if_pos rfl]
    cases hor with
    | inl hm => exact absurd rfl hm
    | inr hn =>
      show psOne kmuK n = kmuK.zero
      exact if_neg (by omega)
  | isFalse hm3 =>
    rw [show psSingle ttcBase ttcBase.one 3 m = ttcBase.zero from if_neg hm3]
    rfl

/-- v 側座標 1 − v³ は基礎台（BLW-2 kmu_twin_base の消費）。 -/
theorem ttc_twinT_base : ttcBaseSupport ttcTwinT := by
  intro m n hor
  show (psC ttcBase kmuTwin m).val n = kmuK.zero
  cases Nat.decEq m 0 with
  | isTrue hm0 =>
    subst hm0
    rw [show psC ttcBase kmuTwin 0 = kmuTwin from if_pos rfl]
    cases hor with
    | inl hm => exact absurd rfl hm
    | inr hn => exact kmu_twin_base n hn
  | isFalse hm0 =>
    rw [show psC ttcBase kmuTwin m = ttcBase.zero from if_neg hm0]
    rfl

/-- **定理 (ttc-7a): μ₃×μ₃ の全元が t = u³ を固定**（BLW-2 は生成元 ζ のみだった）。 -/
theorem ttc_deck_fixes_T (gh : kmuMu3Sq.carrier) : ttcDeck.act gh ttcT = ttcT :=
  ttc_base_imp_fixed ttcT ttc_T_base gh

/-- **定理 (ttc-7b): μ₃×μ₃ の全元が 1 − v³ を固定**。両基礎座標が同一環内で同時に
    デッキ不変——「基底を動かさない被覆変換」の合成版。 -/
theorem ttc_deck_fixes_twinT (gh : kmuMu3Sq.carrier) :
    ttcDeck.act gh ttcTwinT = ttcTwinT :=
  ttc_base_imp_fixed ttcTwinT ttc_twinT_base gh

/-- **ttc-7c: デッキは生成元 u を動かす**（作用の非自明性）。 -/
theorem ttc_deck_moves_u : ttcDeck.act ttcGU ttcU ≠ ttcU := by
  intro hfix
  apply kmu_zeta_ne_one
  have h1 : ((ttcDeck.act ttcGU ttcU).val 1).val 0 = ((ttcU.val 1).val 0) :=
    congrFun (congrArg Subtype.val (congrFun (congrArg Subtype.val hfix) 1)) 0
  rw [ttc_act_coeff_gu ttcU 1 0,
    show ((ttcU.val 1).val 0) = kmuK.one from rfl,
    ttc_rpow_one_exp kmuZeta, CRing.mul_one kmuK kmuZeta] at h1
  exact h1

/-! ## ttc-8: F₂ との接続（BLW-4 実現準同型の合成——tripod π₁ の群論的内容が
    単一被覆環にデッキ変換として作用する） -/

/-- **定理 (ttc-8a): F₂ の合成デッキ作用**（trbRealize 経由・genuine な
    `GAction tfgGrp`）。tripod π₁ の群論的内容 F₂ が単一の twin 合成被覆環
    K[u,v] に環自己同型として作用する。 -/
def ttcF2Deck : GAction tfgGrp where
  carrier := ttcRing.carrier
  act := fun w F => ttcDeck.act (trbRealize.map w) F
  act_one := fun F => by
    show ttcDeck.act (trbRealize.map tfgGrp.one) F = F
    rw [trbRealize.map_one]
    exact ttcDeck.act_one F
  act_mul := fun w w' F => by
    show ttcDeck.act (trbRealize.map (tfgGrp.mul w w')) F
      = ttcDeck.act (trbRealize.map w) (ttcDeck.act (trbRealize.map w') F)
    rw [trbRealize.map_mul w w']
    exact ttcDeck.act_mul (trbRealize.map w) (trbRealize.map w') F

/-- **ttc-8b: 生成元 a は u 側デッキ (ζ,1) として作用**（BLW-4 trb_realize_a の消費）。 -/
theorem ttc_f2_act_a (F : ttcRing.carrier) :
    ttcF2Deck.act tfgA F = ttcDeck.act ttcGU F :=
  congrArg (fun z => ttcDeck.act z F) trb_realize_a

/-- **ttc-8c: 生成元 b は v 側デッキ (1,ζ) として作用**。 -/
theorem ttc_f2_act_b (F : ttcRing.carrier) :
    ttcF2Deck.act tfgB F = ttcDeck.act ttcGV F :=
  congrArg (fun z => ttcDeck.act z F) trb_realize_b

/-- **ttc-8d: F₂ の作用は非自明**（a は u を動かす）。 -/
theorem ttc_f2_act_a_ne_id : ttcF2Deck.act tfgA ttcU ≠ ttcU := by
  intro hfix
  apply ttc_deck_moves_u
  rw [← ttc_f2_act_a ttcU]
  exact hfix

/-- **定理 (ttc-8e): F₂ の語が全デッキ変換を実現** — 任意の (ζⁱ,ζʲ) デッキ変換は
    F₂ のある語 w の作用に一致する（BLW-4 trb_surjective_pow の単一被覆環上への
    輸送）。tripod π₁ の群論的内容から twin 合成被覆の全被覆変換への全射。 -/
theorem ttc_f2_deck_surjective (i j : Nat) :
    ∃ w : tfgGrp.carrier, ∀ F : ttcRing.carrier,
      ttcF2Deck.act w F
        = ttcDeck.act
            ((trbPow kmuMu3 kmuMu3Zeta i, trbPow kmuMu3 kmuMu3Zeta j) : kmuMu3Sq.carrier)
            F := by
  obtain ⟨w, hw⟩ := trb_surjective_pow i j
  refine ⟨w, fun F => ?_⟩
  show ttcDeck.act (trbRealize.map w) F = _
  rw [hw]

/-! ## ttc-9: capstone — twin 合成被覆バンドル（grounded 構造） -/

/-- **twin 合成被覆バンドル** — 単一環 K[u,v] 上の (ℤ/3)² 合成デッキ構造の
    grounded 束ね（各 field が本物の証明を要求する）。 -/
structure TripodTwinCoverBundle where
  /-- u 側 Kummer 座標は環演算で実際に u³。 -/
  uCubed : ttcT = ttcRing.mul ttcU (ttcRing.mul ttcU ttcU)
  /-- v 側 Kummer 座標は環演算で実際に 1 − v³（同一環内）。 -/
  twinRel : ttcTwinT = ttcRing.add ttcRing.one
    (ttcRing.neg (ttcRing.mul ttcV (ttcRing.mul ttcV ttcV)))
  /-- 各デッキ変換は環の乗法を保つ（環自己準同型として作用）。 -/
  ringHomAct : ∀ (gh : kmuMu3Sq.carrier) (a b : ttcRing.carrier),
    ttcDeck.act gh (ttcRing.mul a b)
      = ttcRing.mul (ttcDeck.act gh a) (ttcDeck.act gh b)
  /-- 各デッキ変換は両側逆を持つ（環自己同型）。 -/
  autAct : ∀ (gh : kmuMu3Sq.carrier) (F : ttcRing.carrier),
    ttcDeck.act gh (ttcDeck.act (kmuMu3Sq.inv gh) F) = F
  /-- μ₃×μ₃ の全元が t = u³ を固定。 -/
  fixesT : ∀ gh : kmuMu3Sq.carrier, ttcDeck.act gh ttcT = ttcT
  /-- μ₃×μ₃ の全元が 1 − v³ を固定。 -/
  fixesTwin : ∀ gh : kmuMu3Sq.carrier, ttcDeck.act gh ttcTwinT = ttcTwinT
  /-- 作用は忠実（単一環の 2 元 u, v で (g,h) を復元）。 -/
  faithful : ∀ gh gh' : kmuMu3Sq.carrier,
    ttcDeck.act gh ttcU = ttcDeck.act gh' ttcU →
    ttcDeck.act gh ttcV = ttcDeck.act gh' ttcV → gh = gh'
  /-- 合成 Kummer descent: 全デッキ固定 ⟺ 基礎台（K[u³,v³]）。 -/
  descent : ∀ F : ttcRing.carrier,
    (∀ gh : kmuMu3Sq.carrier, ttcDeck.act gh F = F) ↔ ttcBaseSupport F
  /-- F₂ の語が全 (ζⁱ,ζʲ) デッキ変換を実現（BLW-4 との結線）。 -/
  f2Surj : ∀ i j : Nat, ∃ w : tfgGrp.carrier, ∀ F : ttcRing.carrier,
    ttcF2Deck.act w F
      = ttcDeck.act
          ((trbPow kmuMu3 kmuMu3Zeta i, trbPow kmuMu3 kmuMu3Zeta j) : kmuMu3Sq.carrier)
          F

/-- **twin 合成被覆バンドルの実証人** — 全 field が上で完全証明した本物の内容。 -/
def ttcBundle : TripodTwinCoverBundle where
  uCubed := ttc_T_cube
  twinRel := ttc_twinT_relation
  ringHomAct := ttc_deck_mul_hom
  autAct := ttc_deck_inv_act
  fixesT := ttc_deck_fixes_T
  fixesTwin := ttc_deck_fixes_twinT
  faithful := ttc_deck_faithful
  descent := ttc_composite_descent
  f2Surj := ttc_f2_deck_surjective

/-- **定理 (ttc-9): twin 合成被覆バンドルは存在する**。 -/
theorem ttc_bundle_exists : Nonempty TripodTwinCoverBundle := ⟨ttcBundle⟩

end IUT
