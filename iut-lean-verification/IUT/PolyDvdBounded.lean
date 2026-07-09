/-
  IUT/PolyDvdBounded.lean — M272F（有界余因子の多項式整除 `pdbDvd`
  ＝真の多項式整除: 一般 f の ℚ[X]/(f) 実体化の土台）

  ── 分類 **[実]**（承認済み足場(c)。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無・模型厳禁で本物の K[X] 係数列の上でのみ議論）。

  **complete_pct 影響**: 柱A「実 Galois 理論／実 π₁^ét」の承認済み足場(c)
  ——名前付き実ターゲット「一般 f の ℚ[X]/(f) 実体化」への必要足場。
  既存 `pbzDvd R d a := ∃ c, a = c·d`（`PolyBezoutQ.lean`）は余因子 c が
  **非有界**＝冪級数環 ℚ[[X]] の整除であり、定数項 ≠ 0 の多項式が単元に
  なるため実多項式の既約性に使えない。本層は **余因子 c を IsPoly（有界
  ＝真の多項式）に制限した整除 `pdbDvd`** を導入し、それが真の多項式整除
  であること（反射・推移・単元整除・同伴）と、有界版の**利点**——次数上界
  `pdb_dvd_deg_le` が **honest 仮説なしで**（余因子の先頭係数の位置を要求
  せずに）出る——を本物に確立する。後続本物化: これを土台に、一般 f の
  既約性を `pdbDvd` で定式化し、有界 Bezout クローンの gcd が `pdbDvd` で
  割ることと繋ぐ（別スライス）。complete_pct は未設定（本層はグラフメタ
  不更新）。

  * M272F-1 `pdbDvd` — **有界余因子の整除** d ∣ a := ∃ c, IsPoly c ∧ a=c·d
    （余因子が真の多項式＝有界。冪級数整除 `pbzDvd` との差がここ）
  * M272F-2 `pdb_dvd_refl` — 反射律（c=1、IsPoly psOne、one_mul）
  * M272F-3 `pdb_dvd_trans` — 推移律（余因子の積・IsPoly は
    `simpleExt_mul_bounded` で有界保存）
  * M272F-4 `pdb_to_pbz` — 有界版 ⟹ 非有界版（c をそのまま落とす）
  * M272F-5 `pdb_dvd_deg_le` — **次数上界（仮説なし・有界版の核）**:
    有界余因子なら次数上界 nd ≤ nf が **c の先頭係数データを要求せずに**
    出る。核: c は IsPoly＝有界（bound N）なので、f=c·d が次数 nd 以上で
    全て 0（f の nf+1 有界と nf<nd から）⟹ 正則性 `poly_mul_g_bounded_zero268`
    で c=0 ⟹ f=0 ⟹ f nf=0 が hfl に矛盾。**pdv 版の honest 仮説
    （余因子 c の先頭位置 nc）を余因子の有界性のみで解消**（頂点係数の
    位置探索＝体の等号判定オラクル不要）
  * M272F-6 `pdb_unit_dvd` — 単元は全てを割る（psC(c⁻¹)·a が有界余因子）
  * M272F-7 `pdbAssoc` / `pdb_assoc_dvd_trans` — 同伴と整除伝播

  正直な限定（何が本物で何が honest 仮説か）:
   - **本物**: 一般 `Field268`（従って実 ℚ）係数の多項式係数列 PS = ℕ→K
     の上で、`pdbDvd`（有界余因子整除）の反射・推移・pbzDvd への落とし・
     単元整除・同伴伝播、そして**有界版次数上界 `pdb_dvd_deg_le` が honest
     仮説なしで出ること**は完全証明（sorry 皆無・新規 Classical.choice 皆無・
     `#print axioms` = propext, Quot.sound のみ）。
   - **pdv 版との差（本層の成果）**: `PolyDivisibility.lean` の
     `pdv_dvd_deg_le` は余因子 c の先頭係数の位置 nc（`c nc ≠ 0` かつ
     `IsPolyBounded c (nc+1)`）を explicit honest 仮説として受け取っていた
     （bare な pbzDvd では nc 抽出に体の等号判定オラクルを要するため）。
     本層は整除の定義そのものに **IsPoly（有界余因子）** を組み込むことで、
     余因子の bound だけから正則性で次数上界を導き、**この honest 仮説を
     消去せずに解消**する（§4 準拠。定義を本物＝有界に置換して証明し直した）。
   - 次数は明示上界パラメータとして受け取る（有限台性からの次数抽出は
     行わない・既存 M268F/M269F/M271F と同じ方針）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyDivisibility

namespace IUT

/-! ## M272F-1: 有界余因子の多項式整除 -/

/-- **M272F-1: 有界余因子の整除（真の多項式整除）** — d ∣ a := ∃ c, c が
    真の多項式（IsPoly＝有界）で a = c·d。余因子 c が有界である点が、
    冪級数整除 `pbzDvd`（余因子非有界）との本質的な差。 -/
def pdbDvd (R : CRing) (d a : PS R) : Prop :=
  ∃ c : PS R, IsPoly R c ∧ a = psMul R c d

/-! ## M272F-2: 反射律 -/

/-- **M272F-2: 反射律** d ∣ d（余因子 = 1）。1 = psOne は有界（IsPoly）で
    psMul (psOne) d = d（one_mul）。 -/
theorem pdb_dvd_refl (R : CRing) (d : PS R) (hd : IsPoly R d) : pdbDvd R d d :=
  ⟨psOne R, ⟨1, fun i hi => if_neg (by omega)⟩, ((psRing R).one_mul d).symm⟩

/-! ## M272F-3: 推移律 -/

/-- **M272F-3: 推移律** d ∣ e ∧ e ∣ a ⟹ d ∣ a。e = c₁·d, a = c₂·e より
    a = (c₂·c₁)·d（psMul 結合律）。余因子の積 c₂·c₁ の有界性は
    `simpleExt_mul_bounded`（有界×有界=有界）で保存される。 -/
theorem pdb_dvd_trans (R : CRing) {d e a : PS R}
    (h1 : pdbDvd R d e) (h2 : pdbDvd R e a) : pdbDvd R d a := by
  obtain ⟨c1, hp1, he1⟩ := h1
  obtain ⟨c2, hp2, he2⟩ := h2
  refine ⟨psMul R c2 c1, ?_, ?_⟩
  · obtain ⟨N1, hN1⟩ := hp1
    obtain ⟨N2, hN2⟩ := hp2
    exact ⟨N2 + N1, simpleExt_mul_bounded R hN2 hN1⟩
  · rw [he2, he1]
    exact ((psRing R).mul_assoc c2 c1 d).symm

/-! ## M272F-4: 有界版 ⟹ 非有界版 -/

/-- **M272F-4: 有界余因子整除 ⟹ 冪級数整除** — `pdbDvd`（真の多項式整除）は
    `pbzDvd`（冪級数整除）を含意する。有界余因子 c をそのまま冪級数余因子
    として落とすだけ（IsPoly の情報を捨てる）。 -/
theorem pdb_to_pbz (R : CRing) {d a : PS R} (h : pdbDvd R d a) : pbzDvd R d a := by
  obtain ⟨c, _, hc⟩ := h
  exact ⟨c, hc⟩

/-! ## M272F-5: 次数上界（仮説なし・有界版の核） -/

/-- **定理 (M272F-5): 有界余因子なら次数上界が honest 仮説なしで出る** —
    d ∣ f（有界余因子、f = c·d）で d が次数 nd（nd+1 有界・先頭 d_nd ≠ 0）、
    f が次数 nf（nf+1 有界・先頭 f_nf ≠ 0）なら nd ≤ nf。

    **有界版の利点**: pdv 版 `pdv_dvd_deg_le` は余因子 c の先頭係数の位置
    nc（c_nc ≠ 0・IsPolyBounded c (nc+1)）を explicit honest 仮説として
    要求したが、`pdbDvd` は余因子 c が IsPoly（有界、bound N）である情報を
    定義に含むため、**その bound だけから**次数上界が出る（c の先頭位置の
    探索＝体の等号判定オラクルは不要）。

    証明: nf < nd を仮定して矛盾を導く。f = c·d は次数 nd 以上で全て 0
    （f の nf+1 有界かつ nf<nd ⟹ nd ≤ j なら nf+1 ≤ j）なので、正則性
    `poly_mul_g_bounded_zero268`（d の先頭 ≠ 0 + 体の整域性）で c = 0、
    ゆえに f = c·d = 0、特に f nf = 0 が hfl（f nf ≠ 0）に矛盾。 -/
theorem pdb_dvd_deg_le (K : Field268) {d f : PS K.ring} {nd nf : Nat}
    (hd : IsPolyBounded K.ring d (nd + 1)) (hdl : d nd ≠ K.ring.zero)
    (hf : IsPolyBounded K.ring f (nf + 1)) (hfl : f nf ≠ K.ring.zero)
    (hdvd : pdbDvd K.ring d f) : nd ≤ nf := by
  cases Nat.lt_or_ge nf nd with
  | inr hge => exact hge
  | inl hlt =>
    obtain ⟨c, hcpoly, hceq⟩ := hdvd
    obtain ⟨N, hcN⟩ := hcpoly
    have hlow : ∀ j, nd ≤ j → psMul K.ring c d j = K.ring.zero := by
      intro j hj
      rw [← congrFun hceq j]
      exact hf j (by omega)
    have hczero : ∀ i, c i = K.ring.zero :=
      poly_mul_g_bounded_zero268 K.ring K.invf K.mul_inv_cancel d nd hd hdl
        c N hcN hlow
    have hfnf : psMul K.ring c d nf = K.ring.zero := by
      show rsum K.ring (fun k => K.ring.mul (c k) (d (nf - k))) (nf + 1)
        = K.ring.zero
      have hz : rsum K.ring (fun k => K.ring.mul (c k) (d (nf - k))) (nf + 1)
          = rsum K.ring (fun _ => K.ring.zero) (nf + 1) :=
        rsum_congr K.ring (nf + 1) (fun k _ => by
          rw [hczero k]
          exact CRing.zero_mul K.ring (d (nf - k)))
      rw [hz]
      exact rsum_const_zero K.ring (nf + 1)
    have hfzero : f nf = K.ring.zero := by
      rw [congrFun hceq nf]
      exact hfnf
    exact absurd hfzero hfl

/-! ## M272F-6: 単元は全てを割る -/

/-- **定理 (M272F-6): 単元は全てを割る** — u = psC(c)（c ≠ 0、非零定数
    ＝多項式環の単元）なら、任意の多項式 a（IsPoly）について u ∣ a
    （有界余因子整除）。有界余因子は a·psC(c⁻¹)：これは a（有界）と
    psC(c⁻¹)（次数 0・有界）の積なので有界（`simpleExt_mul_bounded`）、
    かつ (a·psC(c⁻¹))·u = a·psC(c⁻¹)·psC(c) = a·psC(1) = a。 -/
theorem pdb_unit_dvd (K : Field268) {u a : PS K.ring}
    (hu : pdvIsUnit K.ring u) (ha : IsPoly K.ring a) : pdbDvd K.ring u a := by
  obtain ⟨c, hc, hu'⟩ := hu
  obtain ⟨N, hN⟩ := ha
  refine ⟨psMul K.ring a (psC K.ring (K.invf c)), ?_, ?_⟩
  · have hpc : IsPolyBounded K.ring (psC K.ring (K.invf c)) 1 :=
      fun i hi => if_neg (by omega)
    exact ⟨N + 1, simpleExt_mul_bounded K.ring hN hpc⟩
  · have hcancel : K.ring.mul (K.invf c) c = K.ring.one := by
      rw [K.ring.mul_comm]
      exact K.mul_inv_cancel c hc
    have step : psMul K.ring (psMul K.ring a (psC K.ring (K.invf c))) u = a := by
      rw [hu']
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

/-! ## M272F-7: 同伴（相互整除）と整除伝播 -/

/-- **M272F-7a: 同伴** d ~ f := d ∣ f ∧ f ∣ d（両方向とも有界余因子整除）。 -/
def pdbAssoc (R : CRing) (d f : PS R) : Prop :=
  pdbDvd R d f ∧ pdbDvd R f d

/-- **M272F-7b: 同伴による整除の伝播** — f ∣ a ∧ d ~ f ⟹ d ∣ a
    （d ∣ f と f ∣ a の推移律）。 -/
theorem pdb_assoc_dvd_trans (R : CRing) {d f a : PS R}
    (hfa : pdbDvd R f a) (hassoc : pdbAssoc R d f) : pdbDvd R d a :=
  pdb_dvd_trans R hassoc.1 hfa

end IUT
