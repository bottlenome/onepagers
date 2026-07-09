/-
  IUT/PolyDivisibility.lean — M271F（体係数多項式環 K[X] 上の整除・次数・
  単元に関する汎用実補題: 一般 f の ℚ[X]/(f) 実体化で「既約 ⟹ gcd は単元」
  を支える土台）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無）。

  **complete_pct 影響**: 柱A「実 Galois 理論／実 π₁^ét」の本物の先行建設
  （承認済み足場(c)——名前付き実ターゲット「一般 f の ℚ[X]/(f) 実体化」
  への必要足場。後続本物化: これらの整除・次数・単元補題を土台に、
  `SimpleExtension.lean` の honest 仮説 `SimpleExtData.bezout`（f 既約 ⟹
  極大イデアル = 単元 gcd）を、素の既約性から拡張ユークリッド互除法
  `PolyBezoutQ.lean` 経由で本物に導く）。complete_pct は未設定
  （本層はグラフメタ不更新・模型厳禁で本物の K[X] 係数列の上でのみ議論）。

  * M271F-1 `pdv_dvd_refl` / `pdv_dvd_trans` — 割り切れ pbzDvd の反射律・
    推移律（推移は psMul 結合律 = `psRing` の mul_assoc へ降下）
  * M271F-2 `pdvIsUnit` / `pdv_unit_dvd` — **単元の特徴付け**（非零定数
    ＝多項式環の単元）と「単元は全てを割る」（逆元 psC(c⁻¹) を使うので
    体 `Field268` 版・逆元性は `psConstHom.map_mul` + `mul_inv_cancel`）
  * M271F-3 `pdv_mul_top_coeff` / `pdv_mul_top_ne` / `pdv_dvd_deg_le` —
    **次数上界（体係数・頂点係数論法）**: 積の頂点係数 (c·d)_{nc+nd}=c_nc·d_nd
    （既存 `psMul_g_top_coeff268` の再利用）が体の整域性（`mul_eq_zero_left268`）
    で非零、f の有界性で nc+nd ≤ nf、ゆえに nd ≤ nf（次数加法性から）
  * M271F-4 `pdvAssoc` / `pdv_assoc_dvd_trans` — **同伴**（相互整除）と
    「f∣a ∧ d~f ⟹ d∣a」（推移律の系）
  * M271F-5 `pdv_deg_zero_unit` — 次数 0 の非零多項式は単元（= psC(p 0)）

  正直な限定（何が本物で何が honest 仮説か）:
   - **本物**: 一般 `Field268`（従って実 ℚ）係数の多項式係数列 PS = ℕ→K
     の上で、pbzDvd の反射・推移、単元＝非零定数の割り切れ、積の頂点係数
     と次数加法性による次数上界、同伴の整除伝播、次数 0 の単元性は完全証明
     （sorry 皆無・新規 Classical.choice 皆無・`#print axioms` = propext,
     Quot.sound のみ）。
   - **honest 仮説（deferred）**: `pdv_dvd_deg_le` は割り切れの**商 c の
     先頭係数の位置 nc**（`c nc ≠ 0` かつ `IsPolyBounded c (nc+1)`）を
     explicit 仮説として受け取る。これは「d∣f の商 c の頂点係数論法」の
     忠実な形だが、bare な `pbzDvd`（∃ c, f = c·d）から nc を**抽出する
     には体の等号判定オラクル**（`PolyBezoutQ.lean` の `hlead_oracle` と
     同じ・抽象 `Field268` では等号判定が無い）が要る。よって商の先頭係数
     データは toy で誤魔化さず honest に explicit 引数として明示する
     （§4 準拠・消さない）。実体 ℚ での nc 抽出（QRat の num=0 判定）は
     次スライス。
   - 次数は明示上界パラメータとして受け取る（有限台性からの次数抽出は
     行わない・既存 M268F/M269F と同じ方針）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyBezoutQ

namespace IUT

/-! ## M271F-1: 割り切れ pbzDvd の反射律・推移律 -/

/-- **M271F-1a: 反射律** d ∣ d（商 = 1）。 -/
theorem pdv_dvd_refl (R : CRing) (d : PS R) : pbzDvd R d d :=
  ⟨psOne R, ((psRing R).one_mul d).symm⟩

/-- **M271F-1b: 推移律** d ∣ e ∧ e ∣ a ⟹ d ∣ a。e = c·d, a = c'·e より
    a = c'·(c·d) = (c'·c)·d（psMul 結合律 = `psRing` の mul_assoc）。 -/
theorem pdv_dvd_trans (R : CRing) {d e a : PS R}
    (h1 : pbzDvd R d e) (h2 : pbzDvd R e a) : pbzDvd R d a := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨c', hc'⟩ := h2
  refine ⟨psMul R c' c, ?_⟩
  rw [hc', hc]
  exact ((psRing R).mul_assoc c' c d).symm

/-! ## M271F-2: 単元の特徴付け（非零定数）と「単元は全てを割る」 -/

/-- **M271F-2a: 単元の特徴付け** — 多項式環 K[X] の単元は非零定数 psC(c)。 -/
def pdvIsUnit (R : CRing) (p : PS R) : Prop :=
  ∃ c : R.carrier, c ≠ R.zero ∧ p = psC R c

/-- **M271F-2b: 単元は全てを割る** — u = psC(c)（c ≠ 0）なら任意 a について
    u ∣ a。商 = a·psC(c⁻¹)：a·psC(c⁻¹)·psC(c) = a·psC(c⁻¹·c) = a·psC(1) = a。
    逆元 psC(c⁻¹) を要するので体 `Field268` 版（`mul_inv_cancel`）。 -/
theorem pdv_unit_dvd (K : Field268) {u a : PS K.ring}
    (h : pdvIsUnit K.ring u) : pbzDvd K.ring u a := by
  obtain ⟨c, hc, hu⟩ := h
  refine ⟨psMul K.ring a (psC K.ring (K.invf c)), ?_⟩
  have hcancel : K.ring.mul (K.invf c) c = K.ring.one := by
    rw [K.ring.mul_comm]
    exact K.mul_inv_cancel c hc
  have step : psMul K.ring (psMul K.ring a (psC K.ring (K.invf c))) u = a := by
    rw [hu]
    have e1 : psMul K.ring (psMul K.ring a (psC K.ring (K.invf c))) (psC K.ring c)
        = psMul K.ring a (psMul K.ring (psC K.ring (K.invf c)) (psC K.ring c)) :=
      (psRing K.ring).mul_assoc a (psC K.ring (K.invf c)) (psC K.ring c)
    have e2 : psMul K.ring (psC K.ring (K.invf c)) (psC K.ring c)
        = psC K.ring K.ring.one := by
      have hmm : psMul K.ring (psC K.ring (K.invf c)) (psC K.ring c)
          = psC K.ring (K.ring.mul (K.invf c) c) :=
        ((psConstHom K.ring).map_mul (K.invf c) c).symm
      rw [hmm, hcancel]
    rw [e1, e2]
    exact CRing.mul_one (psRing K.ring) a
  exact step.symm

/-! ## M271F-3: 次数上界（体係数・頂点係数論法） -/

/-- **M271F-3a: 積の頂点係数** — c が nc+1 有界・d が nd+1 有界なら
    (c·d)_{nc+nd} = c_nc · d_nd。既存 `psMul_g_top_coeff268` の再利用
    （w=c, g=d, M=nc, m=nd）。 -/
theorem pdv_mul_top_coeff (K : Field268) {c d : PS K.ring} {nc nd : Nat}
    (hc : IsPolyBounded K.ring c (nc + 1)) (hd : IsPolyBounded K.ring d (nd + 1)) :
    psMul K.ring c d (nc + nd) = K.ring.mul (c nc) (d nd) :=
  psMul_g_top_coeff268 K.ring d nd hd c nc hc

/-- **M271F-3b: 積の頂点係数は非零** — c_nc ≠ 0・d_nd ≠ 0 なら
    (c·d)_{nc+nd} ≠ 0。体の整域性（`mul_eq_zero_left268`）で
    c_nc·d_nd = 0 なら c_nc = 0 となり矛盾。 -/
theorem pdv_mul_top_ne (K : Field268) {c d : PS K.ring} {nc nd : Nat}
    (hc : IsPolyBounded K.ring c (nc + 1)) (hcl : c nc ≠ K.ring.zero)
    (hd : IsPolyBounded K.ring d (nd + 1)) (hdl : d nd ≠ K.ring.zero) :
    psMul K.ring c d (nc + nd) ≠ K.ring.zero := by
  rw [pdv_mul_top_coeff K hc hd]
  intro h
  exact hcl (mul_eq_zero_left268 K.ring K.invf K.mul_inv_cancel hdl h)

/-- **定理 (M271F-3c): 次数上界** — d ∣ f（f = c·d）で d が次数 nd
    （nd+1 有界・先頭 d_nd ≠ 0）、f が次数 nf（nf+1 有界・先頭 f_nf ≠ 0）
    なら nd ≤ nf。頂点係数論法: (c·d)_{nc+nd} = c_nc·d_nd ≠ 0 = f_{nc+nd}
    を強制、f の有界性で nc+nd ≤ nf、ゆえに nd ≤ nc+nd ≤ nf（次数加法性）。

    正直な限定: 商 c の先頭係数の位置 nc（c_nc ≠ 0・IsPolyBounded c (nc+1)）
    を explicit 仮説として受け取る。bare な pbzDvd（∃ c）からの nc 抽出は
    体の等号判定オラクル（`PolyBezoutQ` の `hlead_oracle` と同じ）を要する
    ため honest に明示する（toy 化しない・§4 準拠）。 -/
theorem pdv_dvd_deg_le (K : Field268) {c d f : PS K.ring} {nc nd nf : Nat}
    (hd : IsPolyBounded K.ring d (nd + 1)) (hdl : d nd ≠ K.ring.zero)
    (hc : IsPolyBounded K.ring c (nc + 1)) (hcl : c nc ≠ K.ring.zero)
    (hf : IsPolyBounded K.ring f (nf + 1)) (hfl : f nf ≠ K.ring.zero)
    (hdvd : f = psMul K.ring c d) : nd ≤ nf := by
  have hne : f (nc + nd) ≠ K.ring.zero := by
    rw [hdvd]
    exact pdv_mul_top_ne K hc hcl hd hdl
  have hle : nc + nd ≤ nf := by
    cases Nat.lt_or_ge nf (nc + nd) with
    | inl hlt => exact absurd (hf (nc + nd) (by omega)) hne
    | inr hge => exact hge
  omega

/-! ## M271F-4: 同伴（相互整除） -/

/-- **M271F-4a: 同伴** d ~ f := d ∣ f ∧ f ∣ d。 -/
def pdvAssoc (R : CRing) (d f : PS R) : Prop :=
  pbzDvd R d f ∧ pbzDvd R f d

/-- **M271F-4b: 同伴による整除の伝播** — f ∣ a ∧ d ~ f ⟹ d ∣ a
    （d ∣ f と f ∣ a の推移律）。 -/
theorem pdv_assoc_dvd_trans (R : CRing) {d f a : PS R}
    (hfa : pbzDvd R f a) (hassoc : pdvAssoc R d f) : pbzDvd R d a :=
  pdv_dvd_trans R hassoc.1 hfa

/-! ## M271F-5: 次数 0 の非零多項式は単元 -/

/-- **定理 (M271F-5): 次数 0 の非零多項式は単元** — p が 1 有界（次数 0）で
    p_0 ≠ 0 なら p = psC(p_0) は単元。i=0 で p_0、i≥1 で p の有界性から 0。 -/
theorem pdv_deg_zero_unit (K : Field268) {p : PS K.ring}
    (hb : IsPolyBounded K.ring p 1) (h0 : p 0 ≠ K.ring.zero) :
    pdvIsUnit K.ring p := by
  refine ⟨p 0, h0, ?_⟩
  funext i
  cases Nat.eq_zero_or_pos i with
  | inl hi =>
    rw [hi]
    show p 0 = if 0 = 0 then p 0 else K.ring.zero
    rw [if_pos rfl]
  | inr hi =>
    rw [hb i (by omega)]
    show K.ring.zero = if i = 0 then p 0 else K.ring.zero
    rw [if_neg (by omega)]

end IUT
