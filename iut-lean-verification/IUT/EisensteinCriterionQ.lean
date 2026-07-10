/-
  IUT/EisensteinCriterionQ.lean — E3: 商 ℚ 上の一般 Eisenstein 既約性判定器

  分類: [実] / 本物建設(b)。
  complete_pct 影響: A3（Φ_9 の Eisenstein 既約性 → ℚ(ζ_9) 構成）への
    承認済み足場（設計書 audit/A3-cyclotomic-tower-detail-2026-07-09.md §1.2 E3）。
    E1（PadicUltrametricQ）で本物構成した超距離不等式、E2（GaussValuationQ）で
    本物構成した商付値 egvValQ と最小添字補題 egv_min_index_mul を土台に、
    **一般 Eisenstein 判定器**を本物に組む:
      「先頭 v = 0・中間 v ≥ 1・定数 v = 1（p² ∤ 定数）」を満たす有理係数多項式は
      ℚ[X] の多項式約元上で既約（`pibIrreducible ratRing f`）。
    証明は Newton 多項式（最小添字）の超距離帰納で、Gauss の補題・ℤ[X] 往復・
    content 議論を一切経由しない（有理係数のまま min の位置だけで閉じる）。
    他の既約性（一般の Eisenstein 型）にも再利用可能。本ファイル単体では
    complete_pct 未設定（E4′ で Φ_9 まで繋いだ時点で実 IUT 完全証明率に反映）。

  * 補助 `eisMinIndex` — 有界係数列 d の「付値最小・最小添字」i₀ を、下から
    有限走査で choice-free に構成（disjunction 形の帰納。`rzd_zero_or_ne` の
    構成的零判定と Int の全順序比較 `Int.lt_or_ge` だけを各段で使う）。
    Left（範囲内全零）/ Right（i₀ + 最小性 hgmin/hglt）の選言を返し、非零 witness を
    持つ呼出側で Right を取り出す。E2 の egv_min_index_mul が要求する 4 連言
    （i₀ の全域最小性 hgmin・最小添字性 hglt）をここで構成する（設計 E3 の「泥」）。
  * 補助 `eisMinMul` — E2 `egv_min_index_mul` の強化版（積係数の**非零性も同時に**
    返す）。egvSumDominant の結論 `≠ 0 ∧ 付値 = V` の両成分を露出する
    （E2 は付値のみ露出したため、hmid 適用に必要な非零を本ファイルで再取得）。
  * 主定理 `eis_irreducible` — f = c·d（IsPoly 両側・pdbDvd 展開）を仮定。
    plo_lead_oracle_Q で d, c の先頭次数 nd, nc を取り、d≡0/c≡0 は先頭係数矛盾で排除。
    nd = 0（余因子側）⟹ pdv_deg_zero_unit で単元（左枝）。nd = n ⟹ 余因子 c 定数単元
    ⟹ pdbAssoc（右枝、Cq3/Cbrt 写経）。**中間 1 ≤ nd ≤ n−1 の排除が Eisenstein 本体**:
    d, c の最小添字 md, mc を eisMinIndex で構成、eisMinMul で
    v(f_{mc+md}) = v(c_mc) + v(d_md) かつ f_{mc+md} ≠ 0。nc+nd = n（積の頂点次数、
    f_n ≠ 0 より）から v(c_nc)+v(d_nd) = v(f_n) = 0、min の性質 v(c_mc) ≤ v(c_nc)・
    v(d_md) ≤ v(d_nd) で v(f_{mc+md}) ≤ 0。mc+md < n なら hmid で v ≥ 1 と矛盾ゆえ
    mc+md = n ⟹ mc = nc, md = nd。すると最小添字性 hglt で v(c_0) > v(c_nc)・
    v(d_0) > v(d_nd)（0 < nc, nd）、定数項 v(f_0) = v(c_0)+v(d_0)
      ≥ (v(c_nc)+1)+(v(d_nd)+1) = 2 > 1 = v(f_0) で矛盾。

  正直な限定（§4 規約により消さない・最重要）:
  - **主定理は先頭係数 `f n ≠ ratRing.zero`（`hln`）を仮定に含む**。設計書の
    目標定理は `hlead : egvValQ p hp (f n) = 0` のみを書いていたが、egvValQ は零類を
    0 に写す total 付値なので `hlead` **単独では f n ≠ 0 を含意しない**（v(0) = 0）。
    実際 f が非零定数（f i = 0, i ≥ 1）でも hlead/hmid/hconst/hc0 を全て満たすが、
    このとき pibIrreducible の第1成分（∃ nf ≥ 1, f nf ≠ 0）が成立せず主定理は偽になる。
    ゆえに「先頭係数が非零（= 多項式の次数がちょうど n・モニック正規化の忠実な形）」
    という真に必要な仮定 `hln` を明示追加する（toy/fudge で塞がず、真の定理を述べる）。
    呼出側 E4′（Φ_9 シフト）は先頭係数 1（v = 0・≠ 0）なので `hln` を自明に満たす。
  - 判定器は「先頭 v = 0・定数 v = 1」の**正規化形**（モニック緩和）。一般スカラー
    正規化（先頭 v ≠ 0 等）は呼出側 E4′ が具体係数で正規化して満たす。
  - 有理係数のまま（v(c_i) < 0 もあり得る）min の位置だけで閉じる：Gauss の補題・
    content・ℤ[X] 往復は最後まで不要。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク不使用。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新）。
-/
import IUT.GaussValuationQ
import IUT.PolyIrreducibleBounded
import IUT.PolyLeadOracleQ

namespace IUT

/-! ## E3-補助1: 付値最小・最小添字の choice-free 構成 -/

/-- **付値最小・最小添字オラクル（choice-free）** — 係数列 d と走査上界 N に対し、
    「範囲 [0, N) が全て零」か、さもなくば「範囲内で付値が最小・かつその最小値を
    とる**最小の**添字 i₀」を返す（選言形）。下から N の帰納で、各段の係数 d M を
    `rzd_zero_or_ne` で零判定し、非零なら現行最小候補と付値を `Int.lt_or_ge` で
    比較して更新する。`egv_min_index_mul` が要求する全域最小性 hgmin と
    最小添字性 hglt を構成的に供給する（排中律なし）。 -/
theorem eisMinIndex (p : Nat) (hp : IsPrime p) (d : PS ratRing) : ∀ N,
    (∀ i, i < N → d i = ratRing.zero) ∨
    (∃ i₀, i₀ < N ∧ d i₀ ≠ ratRing.zero ∧
      (∀ i, i < N → d i ≠ ratRing.zero →
        egvValQ p hp (d i₀) ≤ egvValQ p hp (d i)) ∧
      (∀ i, i < i₀ → d i ≠ ratRing.zero →
        egvValQ p hp (d i₀) < egvValQ p hp (d i))) := by
  intro N
  induction N with
  | zero =>
    apply Or.inl
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  | succ M ih =>
    cases rzd_zero_or_ne (d M) with
    | inl hMz =>
      cases ih with
      | inl hall =>
        apply Or.inl
        intro i hi
        cases Nat.lt_or_ge i M with
        | inl hlt => exact hall i hlt
        | inr hge =>
          have hiM : i = M := by omega
          rw [hiM]; exact hMz
      | inr hex =>
        obtain ⟨i₀, hi0M, hi0ne, hmin, hltp⟩ := hex
        apply Or.inr
        refine ⟨i₀, by omega, hi0ne, ?_, hltp⟩
        intro i hi hine
        cases Nat.lt_or_ge i M with
        | inl hlt => exact hmin i hlt hine
        | inr hge =>
          have hiM : i = M := by omega
          exfalso; apply hine; rw [hiM]; exact hMz
    | inr hMne =>
      cases ih with
      | inl hall =>
        apply Or.inr
        refine ⟨M, by omega, hMne, ?_, ?_⟩
        · intro i hi hine
          cases Nat.lt_or_ge i M with
          | inl hlt => exact absurd (hall i hlt) hine
          | inr hge =>
            have hiM : i = M := by omega
            rw [hiM]; omega
        · intro i hi hine
          exact absurd (hall i hi) hine
      | inr hex =>
        obtain ⟨i₀, hi0M, hi0ne, hmin, hltp⟩ := hex
        cases Int.lt_or_le (egvValQ p hp (d M)) (egvValQ p hp (d i₀)) with
        | inl hnew =>
          apply Or.inr
          refine ⟨M, by omega, hMne, ?_, ?_⟩
          · intro i hi hine
            cases Nat.lt_or_ge i M with
            | inl hlt =>
              have hle := hmin i hlt hine
              omega
            | inr hge =>
              have hiM : i = M := by omega
              rw [hiM]; omega
          · intro i hi hine
            have hle := hmin i hi hine
            omega
        | inr hkeep =>
          apply Or.inr
          refine ⟨i₀, by omega, hi0ne, ?_, hltp⟩
          intro i hi hine
          cases Nat.lt_or_ge i M with
          | inl hlt => exact hmin i hlt hine
          | inr hge =>
            have hiM : i = M := by omega
            rw [hiM]; omega

/-! ## E3-補助2: 積係数の付値 + 非零（E2 egv_min_index_mul の強化版） -/

/-- **最小添字積補題（非零つき）** — E2 `egv_min_index_mul` と同じ Newton 対角論法で
    v((g·h)_{i₀+j₀}) = v(g_{i₀}) + v(h_{j₀}) を得るが、`egvSumDominant` の結論
    `rsum ≠ 0 ∧ egvValQ = V` の**第1成分（非零）も同時に露出**する（E2 は第2成分の
    付値のみ露出したため、Eisenstein 本体で hmid を適用するのに必要な
    「積係数 ≠ 0」を本補題で取得する）。対角 k = i₀ が付値 = 和・非零、対角以外は
    「零係数 or 付値が真に大」で egvSumDominant が閉じる。 -/
theorem eisMinMul (p : Nat) (hp : IsPrime p) (g h : PS ratRing)
    (i₀ j₀ : Nat)
    (hgi0 : g i₀ ≠ ratRing.zero) (hhj0 : h j₀ ≠ ratRing.zero)
    (hgmin : ∀ i, g i ≠ ratRing.zero →
      egvValQ p hp (g i₀) ≤ egvValQ p hp (g i))
    (hglt : ∀ i, i < i₀ → g i ≠ ratRing.zero →
      egvValQ p hp (g i₀) < egvValQ p hp (g i))
    (hhmin : ∀ j, h j ≠ ratRing.zero →
      egvValQ p hp (h j₀) ≤ egvValQ p hp (h j))
    (hhlt : ∀ j, j < j₀ → h j ≠ ratRing.zero →
      egvValQ p hp (h j₀) < egvValQ p hp (h j)) :
    psMul ratRing g h (i₀ + j₀) ≠ ratRing.zero ∧
    egvValQ p hp (psMul ratRing g h (i₀ + j₀))
      = egvValQ p hp (g i₀) + egvValQ p hp (h j₀) := by
  have hdN : i₀ < i₀ + j₀ + 1 := by omega
  have hidx0 : i₀ + j₀ - i₀ = j₀ := by omega
  have htd_ne : ratRing.mul (g i₀) (h (i₀ + j₀ - i₀)) ≠ ratRing.zero := by
    rw [hidx0]; exact egv_mul_ne_zero (g i₀) (h j₀) hgi0 hhj0
  have htd_val : egvValQ p hp (ratRing.mul (g i₀) (h (i₀ + j₀ - i₀)))
      = egvValQ p hp (g i₀) + egvValQ p hp (h j₀) := by
    rw [hidx0]; exact egvValQ_mul p hp (g i₀) (h j₀) hgi0 hhj0
  have hother : ∀ k, k < i₀ + j₀ + 1 → k ≠ i₀ →
      ratRing.mul (g k) (h (i₀ + j₀ - k)) = ratRing.zero ∨
      (ratRing.mul (g k) (h (i₀ + j₀ - k)) ≠ ratRing.zero ∧
        egvValQ p hp (g i₀) + egvValQ p hp (h j₀)
          < egvValQ p hp (ratRing.mul (g k) (h (i₀ + j₀ - k)))) := by
    intro k hk hki0
    cases rzd_zero_or_ne (g k) with
    | inl hgz =>
      apply Or.inl
      rw [hgz]; exact ratRing.zero_mul (h (i₀ + j₀ - k))
    | inr hgn =>
      cases rzd_zero_or_ne (h (i₀ + j₀ - k)) with
      | inl hhz =>
        apply Or.inl
        rw [hhz]; exact ratRing.mul_zero (g k)
      | inr hhn =>
        apply Or.inr
        have htk_ne : ratRing.mul (g k) (h (i₀ + j₀ - k)) ≠ ratRing.zero :=
          egv_mul_ne_zero (g k) (h (i₀ + j₀ - k)) hgn hhn
        refine ⟨htk_ne, ?_⟩
        have htk_val : egvValQ p hp (ratRing.mul (g k) (h (i₀ + j₀ - k)))
            = egvValQ p hp (g k) + egvValQ p hp (h (i₀ + j₀ - k)) :=
          egvValQ_mul p hp (g k) (h (i₀ + j₀ - k)) hgn hhn
        rw [htk_val]
        cases Nat.lt_or_ge k i₀ with
        | inl hklt =>
          have hgstrict : egvValQ p hp (g i₀) < egvValQ p hp (g k) :=
            hglt k hklt hgn
          have hhge : egvValQ p hp (h j₀) ≤ egvValQ p hp (h (i₀ + j₀ - k)) :=
            hhmin (i₀ + j₀ - k) hhn
          omega
        | inr hkge =>
          have hidx : i₀ + j₀ - k < j₀ := by omega
          have hgge : egvValQ p hp (g i₀) ≤ egvValQ p hp (g k) := hgmin k hgn
          have hhstrict : egvValQ p hp (h j₀) < egvValQ p hp (h (i₀ + j₀ - k)) :=
            hhlt (i₀ + j₀ - k) hidx hhn
          omega
  have hmain := egvSumDominant p hp
    (fun k => ratRing.mul (g k) (h (i₀ + j₀ - k)))
    (egvValQ p hp (g i₀) + egvValQ p hp (h j₀))
    i₀ (i₀ + j₀ + 1) hdN htd_ne htd_val hother
  exact ⟨hmain.1, hmain.2⟩

/-! ## E3-主定理: 一般 Eisenstein 既約性判定器 -/

/-- **E3（本丸）: 一般 Eisenstein 既約性判定器** — 有理係数多項式 f（次数 n・
    IsPolyBounded (n+1)・先頭 `f n ≠ 0`）が p 進付値で
    「先頭 v(f_n) = 0・中間 ∀ i<n, v(f_i) ≥ 1（非零のとき）・定数 v(f_0) = 1」を
    満たすなら、f は ℚ[X] の多項式約元上で既約（`pibIrreducible ratRing f`）。

    正直な限定（§4）: 先頭係数非零 `hln` は真に必要（設計書の hlead 単独では
    egvValQ の零類 → 0 規約により f n ≠ 0 を含意しない・ヘッダ参照）。呼出側 E4′ は
    先頭係数 1 で自明に満たす。Gauss の補題・content・ℤ[X] 往復は不要（min 位置のみ）。 -/
theorem eis_irreducible (f : PS ratRing) (n : Nat) (p : Nat) (hp : IsPrime p)
    (hb : IsPolyBounded ratRing f (n + 1)) (hn : 1 ≤ n)
    (hlead : egvValQ p hp (f n) = 0) (hln : f n ≠ ratRing.zero)
    (hmid : ∀ i, i < n → f i ≠ ratRing.zero → 1 ≤ egvValQ p hp (f i))
    (hconst : egvValQ p hp (f 0) = 1) (hc0 : f 0 ≠ ratRing.zero) :
    pibIrreducible ratRing f := by
  refine ⟨⟨n, hn, hb, hln⟩, ?_⟩
  intro d hd_poly hdvd
  obtain ⟨Nd, hdN⟩ := hd_poly
  obtain ⟨c, hc_poly, heq⟩ := hdvd
  -- heq : f = psMul ratRing c d
  cases plo_lead_oracle_Q d Nd hdN with
  | inl hd0 =>
    -- d ≡ 0 ⟹ f n = (c·d) n = 0、hln に矛盾
    exfalso
    apply hln
    have hprod : psMul ratRing c d n = ratRing.zero := by
      show rsum ratRing (fun k => ratRing.mul (c k) (d (n - k))) (n + 1) = ratRing.zero
      have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (n - k))) (n + 1)
          = rsum ratRing (fun _ => ratRing.zero) (n + 1) :=
        rsum_congr ratRing (n + 1) (fun k _ => by
          rw [hd0 (n - k)]
          exact CRing.mul_zero ratRing (c k))
      rw [hz]
      exact rsum_const_zero ratRing (n + 1)
    rw [congrFun heq n]
    exact hprod
  | inr hdlead =>
    obtain ⟨nd, hdl, hdbnd⟩ := hdlead
    have hle : nd ≤ n :=
      pdb_dvd_deg_le pbzRatField hdbnd hdl hb hln ⟨c, hc_poly, heq⟩
    cases Nat.lt_or_ge nd 1 with
    | inl hlt0 =>
      -- nd = 0: 次数 0 の非零 ⟹ 単元（左枝）
      have hnd0 : nd = 0 := by omega
      subst hnd0
      exact Or.inl (pdv_deg_zero_unit pbzRatField hdbnd hdl)
    | inr hge1 =>
      cases Nat.lt_or_ge nd n with
      | inl hltn =>
        -- ★ 中間 1 ≤ nd ≤ n−1: Eisenstein 本体（この枝は矛盾で空虚）
        exfalso
        obtain ⟨Nc, hcN⟩ := hc_poly
        cases plo_lead_oracle_Q c Nc hcN with
        | inl hc0 =>
          -- c ≡ 0 ⟹ f n = 0、hln に矛盾
          apply hln
          have hprod : psMul ratRing c d n = ratRing.zero := by
            show rsum ratRing (fun k => ratRing.mul (c k) (d (n - k))) (n + 1)
              = ratRing.zero
            have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (n - k))) (n + 1)
                = rsum ratRing (fun _ => ratRing.zero) (n + 1) :=
              rsum_congr ratRing (n + 1) (fun k _ => by
                rw [hc0 k]
                exact CRing.zero_mul ratRing (d (n - k)))
            rw [hz]
            exact rsum_const_zero ratRing (n + 1)
          rw [congrFun heq n]
          exact hprod
        | inr hclead =>
          obtain ⟨nc, hcl, hcbnd⟩ := hclead
          -- 頂点係数 (c·d)_{nc+nd} = c_nc·d_nd ≠ 0 ⟹ nc+nd ≤ n
          have htopne : psMul ratRing c d (nc + nd) ≠ ratRing.zero :=
            pdv_mul_top_ne pbzRatField hcbnd hcl hdbnd hdl
          have hsumle : nc + nd ≤ n := by
            cases Nat.lt_or_ge n (nc + nd) with
            | inl hgt =>
              exfalso
              apply htopne
              rw [← congrFun heq (nc + nd)]
              exact hb (nc + nd) (by omega)
            | inr hge => exact hge
          -- nc+nd < n なら (c·d)_n = 0（台の外）で f n = 0 矛盾 ⟹ n ≤ nc+nd
          have hncnd_ge : n ≤ nc + nd := by
            cases Nat.lt_or_ge (nc + nd) n with
            | inr hge => exact hge
            | inl hlt =>
              exfalso
              apply hln
              have hz2 : rsum ratRing (fun k => ratRing.mul (c k) (d (n - k))) (n + 1)
                  = rsum ratRing (fun _ => ratRing.zero) (n + 1) :=
                rsum_congr ratRing (n + 1) (fun k hk => by
                  cases Nat.lt_or_ge k (nc + 1) with
                  | inr hkge =>
                    rw [hcbnd k hkge]
                    exact CRing.zero_mul ratRing (d (n - k))
                  | inl hklt =>
                    rw [hdbnd (n - k) (by omega)]
                    exact CRing.mul_zero ratRing (c k))
              have hprodn : psMul ratRing c d n = ratRing.zero := by
                show rsum ratRing (fun k => ratRing.mul (c k) (d (n - k))) (n + 1)
                  = ratRing.zero
                rw [hz2]
                exact rsum_const_zero ratRing (n + 1)
              rw [congrFun heq n]
              exact hprodn
          have hncnd : nc + nd = n := by omega
          -- v(c_nc) + v(d_nd) = v(f_n) = 0
          have htopcoeff : f (nc + nd) = ratRing.mul (c nc) (d nd) := by
            rw [congrFun heq (nc + nd)]
            exact pdv_mul_top_coeff pbzRatField hcbnd hdbnd
          have htopval : egvValQ p hp (f (nc + nd))
              = egvValQ p hp (c nc) + egvValQ p hp (d nd) := by
            rw [htopcoeff]
            exact egvValQ_mul p hp (c nc) (d nd) hcl hdl
          have hcncdnd : egvValQ p hp (c nc) + egvValQ p hp (d nd) = 0 := by
            rw [← htopval, hncnd]
            exact hlead
          -- 最小添字 mc, md を eisMinIndex で構成
          have hcMinR : ∃ mc, mc < nc + 1 ∧ c mc ≠ ratRing.zero ∧
              (∀ i, i < nc + 1 → c i ≠ ratRing.zero →
                egvValQ p hp (c mc) ≤ egvValQ p hp (c i)) ∧
              (∀ i, i < mc → c i ≠ ratRing.zero →
                egvValQ p hp (c mc) < egvValQ p hp (c i)) := by
            cases eisMinIndex p hp c (nc + 1) with
            | inl hall => exact absurd (hall nc (by omega)) hcl
            | inr hR => exact hR
          obtain ⟨mc, hmclt, hmcne, hcmin, hclt⟩ := hcMinR
          have hdMinR : ∃ md, md < nd + 1 ∧ d md ≠ ratRing.zero ∧
              (∀ i, i < nd + 1 → d i ≠ ratRing.zero →
                egvValQ p hp (d md) ≤ egvValQ p hp (d i)) ∧
              (∀ i, i < md → d i ≠ ratRing.zero →
                egvValQ p hp (d md) < egvValQ p hp (d i)) := by
            cases eisMinIndex p hp d (nd + 1) with
            | inl hall => exact absurd (hall nd (by omega)) hdl
            | inr hR => exact hR
          obtain ⟨md, hmdlt, hmdne, hdmin, hdlt⟩ := hdMinR
          -- 全域最小性へ拡張（範囲外は有界性で零）
          have hcminU : ∀ i, c i ≠ ratRing.zero →
              egvValQ p hp (c mc) ≤ egvValQ p hp (c i) := by
            intro i hine
            cases Nat.lt_or_ge i (nc + 1) with
            | inl hlt => exact hcmin i hlt hine
            | inr hge => exact absurd (hcbnd i hge) hine
          have hdminU : ∀ i, d i ≠ ratRing.zero →
              egvValQ p hp (d md) ≤ egvValQ p hp (d i) := by
            intro i hine
            cases Nat.lt_or_ge i (nd + 1) with
            | inl hlt => exact hdmin i hlt hine
            | inr hge => exact absurd (hdbnd i hge) hine
          have hvc : egvValQ p hp (c mc) ≤ egvValQ p hp (c nc) := hcminU nc hcl
          have hvd : egvValQ p hp (d md) ≤ egvValQ p hp (d nd) := hdminU nd hdl
          -- 積係数 f_{mc+md}: 非零 & 付値
          have hmm2 := eisMinMul p hp c d mc md hmcne hmdne hcminU hclt hdminU hdlt
          have hfmcmd_ne : f (mc + md) ≠ ratRing.zero := by
            rw [congrFun heq (mc + md)]
            exact hmm2.1
          have hfmcmd_val : egvValQ p hp (f (mc + md))
              = egvValQ p hp (c mc) + egvValQ p hp (d md) := by
            rw [congrFun heq (mc + md)]
            exact hmm2.2
          have hfmcmd_le : egvValQ p hp (f (mc + md)) ≤ 0 := by
            rw [hfmcmd_val]; omega
          -- mc+md ≤ n。mc+md < n なら hmid で v ≥ 1 と矛盾 ⟹ mc+md = n
          have hmcmd_eq : mc + md = n := by
            cases Nat.lt_or_ge (mc + md) n with
            | inr hge => omega
            | inl hlt =>
              exfalso
              have h1 := hmid (mc + md) hlt hfmcmd_ne
              omega
          have hmc_eq : mc = nc := by omega
          have hmd_eq : md = nd := by omega
          -- 定数項 f_0 = c_0·d_0
          have hf0coeff : f 0 = ratRing.mul (c 0) (d 0) := by
            rw [congrFun heq 0]
            show ratRing.add ratRing.zero (ratRing.mul (c 0) (d 0))
              = ratRing.mul (c 0) (d 0)
            exact ratRing.zero_add (ratRing.mul (c 0) (d 0))
          have hc0ne : c 0 ≠ ratRing.zero := by
            intro hz
            apply hc0
            rw [hf0coeff, hz]
            exact ratRing.zero_mul (d 0)
          have hd0ne : d 0 ≠ ratRing.zero := by
            intro hz
            apply hc0
            rw [hf0coeff, hz]
            exact ratRing.mul_zero (c 0)
          -- 最小添字性: v(c_0) > v(c_nc)・v(d_0) > v(d_nd)
          have hvc0 : egvValQ p hp (c nc) < egvValQ p hp (c 0) := by
            have h1 := hclt 0 (by omega) hc0ne
            rw [hmc_eq] at h1
            exact h1
          have hvd0 : egvValQ p hp (d nd) < egvValQ p hp (d 0) := by
            have h1 := hdlt 0 (by omega) hd0ne
            rw [hmd_eq] at h1
            exact h1
          have hf0val : egvValQ p hp (f 0)
              = egvValQ p hp (c 0) + egvValQ p hp (d 0) := by
            rw [hf0coeff]
            exact egvValQ_mul p hp (c 0) (d 0) hc0ne hd0ne
          -- v(f_0) ≥ 2 > 1 = v(f_0) で矛盾
          rw [hf0val] at hconst
          omega
      | inr hgen =>
        -- nd = n: 余因子 c は定数単元 ⟹ pdbAssoc（右枝）
        have hndn : nd = n := by omega
        subst nd
        obtain ⟨Nc, hcN⟩ := hc_poly
        cases plo_lead_oracle_Q c Nc hcN with
        | inl hc0 =>
          exfalso
          apply hln
          have hprod : psMul ratRing c d n = ratRing.zero := by
            show rsum ratRing (fun k => ratRing.mul (c k) (d (n - k))) (n + 1)
              = ratRing.zero
            have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (n - k))) (n + 1)
                = rsum ratRing (fun _ => ratRing.zero) (n + 1) :=
              rsum_congr ratRing (n + 1) (fun k _ => by
                rw [hc0 k]
                exact CRing.zero_mul ratRing (d (n - k)))
            rw [hz]
            exact rsum_const_zero ratRing (n + 1)
          rw [congrFun heq n]
          exact hprod
        | inr hclead =>
          obtain ⟨nc, hcl, hcbnd⟩ := hclead
          -- 頂点係数 (c·d)_{nc+n} = c_nc·d_n ≠ 0 = f_{nc+n}（nc+n ≥ n+1 なら）⟹ nc = 0
          have hnc0 : nc = 0 := by
            cases Nat.lt_or_ge (nc + n) (n + 1) with
            | inl hlt => omega
            | inr hge =>
              exfalso
              have htop : psMul ratRing c d (nc + n) ≠ ratRing.zero :=
                pdv_mul_top_ne pbzRatField hcbnd hcl hdbnd hdl
              have hzero : psMul ratRing c d (nc + n) = ratRing.zero :=
                (congrFun heq (nc + n)).symm.trans (hb (nc + n) (by omega))
              exact htop hzero
          subst hnc0
          obtain ⟨c0, hc0ne, hceq⟩ := pdv_deg_zero_unit pbzRatField hcbnd hcl
          refine Or.inr ⟨⟨c, ⟨Nc, hcN⟩, heq⟩, ?_⟩
          refine ⟨psC ratRing (pbzRatField.invf c0),
            ⟨1, fun i hi => if_neg (by omega)⟩, ?_⟩
          have hcancel : ratRing.mul (pbzRatField.invf c0) c0 = ratRing.one := by
            rw [ratRing.mul_comm]
            exact pbzRatField.mul_inv_cancel c0 hc0ne
          have hmm : psMul ratRing (psC ratRing (pbzRatField.invf c0)) c = psOne ratRing := by
            rw [hceq]
            show psMul ratRing (psC ratRing (pbzRatField.invf c0)) (psC ratRing c0)
              = psOne ratRing
            have h3 : psMul ratRing (psC ratRing (pbzRatField.invf c0)) (psC ratRing c0)
                = psC ratRing (ratRing.mul (pbzRatField.invf c0) c0) :=
              ((psConstHom ratRing).map_mul (pbzRatField.invf c0) c0).symm
            rw [h3, hcancel]
            rfl
          have chain : psMul ratRing (psC ratRing (pbzRatField.invf c0)) f = d := by
            rw [heq]
            rw [show psMul ratRing (psC ratRing (pbzRatField.invf c0)) (psMul ratRing c d)
                  = psMul ratRing (psMul ratRing (psC ratRing (pbzRatField.invf c0)) c) d
                from ((psRing ratRing).mul_assoc _ _ _).symm]
            rw [hmm]
            exact (psRing ratRing).one_mul d
          exact chain.symm

end IUT
