/-
  IUT/EisensteinShiftTransport.lean — A3 一般 n 塔への足場（E5 の §2.3）:
  「シフト像既約性 ⟹ 元既約性」の輸送論法を f/n 一般に引数化した本丸。

  設計 audit/A3-inverse-limit-roadmap-2026-07-09.md §2.3 の実装:
  `IUT/Phi9Irreducible.lean` の `p9i_irreducible`（Φ_9 固定の既約性輸送）は
  Φ_9 固有なのは主語（cpdPhi9・p9eShifted・7 という打切数）だけで、輸送論法が
  使う部品（`p9i_shift_bounded`/`p9i_shift_deg`/`evalHom_mul`/`evalHom_stable`/
  `plo_lead_oracle_Q`/`pdv_deg_zero_unit`/`pdv_mul_top_ne`/`pdbAssoc`/`pdbDvd`/
  `pdb_dvd_deg_le`）は全て f 一般（`PS ratRing` の任意の元・任意の次数上界を
  受け取る形で既に定義・証明されている）。本ファイルは `p9i_irreducible` の
  証明体を f/n（次数上界）で引数化した実質クローンとして writing する:

   * `est_shift_factor` — Φ_9 版 `p9i_shift_factor` の f 一般版。Φ_9 版は
     Φ_9 固有の係数照合 `p9e_shift_eq`（シフト像 p9eShifted への具体係数の
     橋渡し）を経由していたが、本補題はシフト像 `p9eShift f (n+1)` を
     そのまま主語にするため、その橋渡しが不要になり Φ_9 版より短い
     （`evalHom_mul` + `evalHom_stable` の 2 段のみ）。
   * `est_transport` — 本丸。`p9i_irreducible` の証明体を f/n/hb/hl で
     引数化し、`hsh : pibIrreducible ratRing (p9eShift f (n + 1))`
     （シフト像の既約性）を直接受け取って `pibIrreducible ratRing f`
     （元の既約性）を返す。

  ── 分類 **[実／本物建設(b)（確立イディオムのクローン）]**。
  **complete_pct 影響**: A3 の一般 n 塔（Φ_{3ⁿ} 既約性 `eitPhi_irreducible`
  への到達）への足場——シフト像既約性 ⟹ 元既約性の輸送を f 一般化し、
  各段 Φ_{3ⁿ} の既約性証明（E5-4/E5-5、`IUT/CyclotomicStretch.lean` 系の
  完成後）が本補題 1 本の適用で閉じられるようにする。本ファイル単体では
  complete_pct は未設定（一般段の M2 で `eitPhi_irreducible` が完成した
  ラウンドで反映）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   - **本物**: `est_transport` は `PS ratRing` の任意の f・任意の次数上界 n に
     対する完全証明（模型・代理・toy 主語なし）。Φ_9 の場合と全く同じ論理を
     一般 f に対して繰り返し使える形に開いただけで、輸送論法そのものに
     手加減・弱化は一切ない。
   - **詰まりなし**: 設計書が懸念した「p9i 側補題が Φ_9 固有で一般化が
     重い場合」は該当しなかった。`p9i_shift_bounded`/`p9i_shift_deg` は
     `Phi9Irreducible.lean` の時点で既に f 一般（Φ_9 に依存しない）で
     証明されていたため、新設が必要だったのは `est_shift_factor`
     （Φ_9 版 `p9i_shift_factor` の f 一般化）のみ。
   - **部分ケースであること（消さない）**: 本補題はあくまで「シフト像の
     既約性が与えられれば」という条件付き輸送。シフト像 `p9eShift f (n+1)`
     自身の既約性（Eisenstein 判定への投入）は呼び出し側（E5-4/E5-5 や
     `p9i_shifted_irreducible` 相当）が別途用意する必要がある。

  全て選択公理不使用（propext/Quot.sound のみ）。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。
-/
import IUT.Phi9Irreducible

namespace IUT

/-! ## EST-1: シフト因数分解（f 一般版・Φ_9 版 `p9i_shift_factor` のクローン） -/

/-- **EST-1: シフト因数分解（f 一般）** — f = c·d（有界余因子・c は Bc 有界・d は
    Bd 有界）で f 自身が (n+1) 有界なら、シフト像は
    p9eShift f (n+1) = (p9eShift c Bc)·(p9eShift d Bd) に一致する。評価準同型の
    乗法性 `evalHom_mul`（打切 Bc+Bd+1）+ 打切安定 `evalHom_stable`（f は n+1
    有界・n+1 ≤ Bc+Bd+1）で閉じる。Φ_9 版 `p9i_shift_factor` と異なり、シフト像
    `p9eShift f (n+1)` をそのまま主語にするため、Φ_9 固有の係数照合
    `p9e_shift_eq` への依存が不要（その分 Φ_9 版より短い）。 -/
theorem est_shift_factor (f c d : PS ratRing) (n Bc Bd : Nat)
    (hb : IsPolyBounded ratRing f (n + 1))
    (hc : IsPolyBounded ratRing c Bc) (hd : IsPolyBounded ratRing d Bd)
    (hB : n + 1 ≤ Bc + Bd + 1) (heq : f = psMul ratRing c d) :
    p9eShift f (n + 1) = psMul ratRing (p9eShift c Bc) (p9eShift d Bd) := by
  have hmul := evalHom_mul (psConstHom ratRing) p9eXp1 c d Bc Bd hc hd
  have hstab := evalHom_stable (psConstHom ratRing) p9eXp1 f (n + 1) hb (Bc + Bd + 1) hB
  funext j
  have e2 : p9eShift f (n + 1) j = p9eShift f (Bc + Bd + 1) j := (congrFun hstab j).symm
  have e3 : p9eShift f (Bc + Bd + 1) j
      = p9eShift (psMul ratRing c d) (Bc + Bd + 1) j := by rw [heq]
  have e4 : p9eShift (psMul ratRing c d) (Bc + Bd + 1) j
      = psMul ratRing (p9eShift c Bc) (p9eShift d Bd) j := congrFun hmul j
  rw [e2, e3, e4]

/-! ## EST-2: 一般輸送本体（f 一般版・Φ_9 版 `p9i_irreducible` のクローン） -/

/-- **EST-2（本丸）: シフト像既約性 ⟹ 元既約性（f 一般輸送）** — f が (n+1) 有界
    かつ n 次係数 ≠ 0（n ≥ 1）で、シフト像 `p9eShift f (n + 1)` が既約
    （`pibIrreducible`）なら、f 自身も既約。任意の有界余因子約元 d（f = c·d）に
    対し、シフト像へ移して p9eShift f (n+1) = (p9eShift c)·(p9eShift d)
    （`est_shift_factor`）を得、シフト像の既約性で d の像を単元 or 同伴に分類。
    シフトは次数保存（`p9i_shift_deg`）なので、単元 ⟹ d 次数 0 ⟹ d 単元、
    同伴 ⟹ d 次数 n ⟹ 余因子 c 定数単元 ⟹ f ∣ d（`pdbAssoc`）。逆シフト・
    合成恒等式は不要（Φ_9 版 `p9i_irreducible` と同じ論法・f/n 引数化のみ）。 -/
theorem est_transport (f : PS ratRing) (n : Nat)
    (hb : IsPolyBounded ratRing f (n + 1)) (hl : f n ≠ ratRing.zero) (hn : 1 ≤ n)
    (hsh : pibIrreducible ratRing (p9eShift f (n + 1))) :
    pibIrreducible ratRing f := by
  refine ⟨⟨n, hn, hb, hl⟩, ?_⟩
  intro d hd_poly hdvd
  obtain ⟨Nd, hdN⟩ := hd_poly
  obtain ⟨c, hc_poly, heq⟩ := hdvd
  obtain ⟨Nc, hcN⟩ := hc_poly
  -- 打切点を n+1 以上にするための有界性拡大
  have hcB : IsPolyBounded ratRing c (Nc + (n + 1)) := fun i hi => hcN i (by omega)
  have hdB : IsPolyBounded ratRing d (Nd + (n + 1)) := fun i hi => hdN i (by omega)
  -- シフト因数分解
  have hCD : p9eShift f (n + 1)
      = psMul ratRing (p9eShift c (Nc + (n + 1))) (p9eShift d (Nd + (n + 1))) :=
    est_shift_factor f c d n (Nc + (n + 1)) (Nd + (n + 1)) hb hcB hdB (by omega) heq
  have hCpoly : IsPoly ratRing (p9eShift c (Nc + (n + 1))) :=
    ⟨Nc, p9i_shift_bounded c Nc (Nc + (n + 1)) hcN⟩
  have hDpoly : IsPoly ratRing (p9eShift d (Nd + (n + 1))) :=
    ⟨Nd, p9i_shift_bounded d Nd (Nd + (n + 1)) hdN⟩
  have hdvdD : pdbDvd ratRing (p9eShift d (Nd + (n + 1))) (p9eShift f (n + 1)) :=
    ⟨p9eShift c (Nc + (n + 1)), hCpoly, hCD⟩
  -- d の先頭次数を決定
  cases plo_lead_oracle_Q d Nd hdN with
  | inl hd0 =>
    -- d ≡ 0 ⟹ f n = (c·d) n = 0、n 次係数の非零性に矛盾
    exfalso
    apply hl
    have hprod : psMul ratRing c d n = ratRing.zero := by
      show rsum ratRing (fun k => ratRing.mul (c k) (d (n - k))) (n + 1) = ratRing.zero
      have hz : rsum ratRing (fun k => ratRing.mul (c k) (d (n - k))) (n + 1)
          = rsum ratRing (fun _ => ratRing.zero) (n + 1) :=
        rsum_congr ratRing (n + 1) (fun k _ => by
          rw [hd0 (n - k)]
          exact ratRing.mul_zero (c k))
      rw [hz]
      exact rsum_const_zero ratRing (n + 1)
    rw [congrFun heq n]
    exact hprod
  | inr hdlead =>
    obtain ⟨nd, hdl, hdbnd⟩ := hdlead
    have hle : nd ≤ n :=
      pdb_dvd_deg_le pbzRatField hdbnd hdl hb hl ⟨c, ⟨Nc, hcN⟩, heq⟩
    have hndlt : nd + 1 ≤ Nd + (n + 1) := by omega
    have hDdeg := p9i_shift_deg d nd (Nd + (n + 1)) hdbnd hndlt
    cases hsh.2 (p9eShift d (Nd + (n + 1))) hDpoly hdvdD with
    | inl hDunit =>
      -- 像が単元 ⟹ nd = 0 ⟹ d 単元
      obtain ⟨e, hene, hDe⟩ := hDunit
      have hnd0 : nd = 0 := by
        cases Nat.eq_zero_or_pos nd with
        | inl h0 => exact h0
        | inr hpos =>
          exfalso
          apply hdl
          rw [← hDdeg.1, hDe]
          show (if nd = 0 then e else ratRing.zero) = ratRing.zero
          exact if_neg (by omega)
      subst hnd0
      exact Or.inl (pdv_deg_zero_unit pbzRatField hdbnd hdl)
    | inr hDassoc =>
      -- 像が同伴 ⟹ nd = n ⟹ 余因子 c 定数単元 ⟹ pdbAssoc
      obtain ⟨E, hEpoly, hDeq⟩ := hDassoc.2
      obtain ⟨Ne, hEN⟩ := hEpoly
      have hfshDeg := p9i_shift_deg f n (n + 1) hb (by omega)
      have hnd_n : nd = n := by
        cases plo_lead_oracle_Q E Ne hEN with
        | inl hE0 =>
          -- E ≡ 0 ⟹ 像 ≡ 0 ⟹ 像 nd = 0、d nd ≠ 0 に矛盾
          exfalso
          apply hdl
          rw [← hDdeg.1, hDeq]
          show rsum ratRing (fun k => ratRing.mul (E k) (p9eShift f (n + 1) (nd - k))) (nd + 1)
            = ratRing.zero
          have hzz : rsum ratRing
              (fun k => ratRing.mul (E k) (p9eShift f (n + 1) (nd - k))) (nd + 1)
              = rsum ratRing (fun _ => ratRing.zero) (nd + 1) :=
            rsum_congr ratRing (nd + 1) (fun k _ => by
              rw [hE0 k]
              exact CRing.zero_mul ratRing (p9eShift f (n + 1) (nd - k)))
          rw [hzz]
          exact rsum_const_zero ratRing (nd + 1)
        | inr hElead =>
          obtain ⟨ne, hEl, hEbnd⟩ := hElead
          -- 像 = E·(p9eShift f (n+1)) の頂点 (ne+n) が非零 ⟹ (nd+1) 有界より
          -- ne+n ≤ nd ⟹ nd ≥ n
          have hshl : p9eShift f (n + 1) n ≠ ratRing.zero := by
            rw [hfshDeg.1]; exact hl
          have htop : psMul ratRing E (p9eShift f (n + 1)) (ne + n) ≠ ratRing.zero :=
            pdv_mul_top_ne pbzRatField hEbnd hEl hfshDeg.2 hshl
          have hge : ne + n ≤ nd := by
            cases Nat.lt_or_ge (ne + n) (nd + 1) with
            | inl h => omega
            | inr h =>
              exfalso
              apply htop
              have hval : psMul ratRing E (p9eShift f (n + 1)) (ne + n)
                  = p9eShift d (Nd + (n + 1)) (ne + n) := (congrFun hDeq (ne + n)).symm
              rw [hval]
              exact hDdeg.2 (ne + n) h
          omega
      rw [hnd_n] at hdbnd hdl
      -- 余因子 c の先頭次数 nc を決定 ⟹ nc = 0 ⟹ c 定数単元 ⟹ f ∣ d
      cases plo_lead_oracle_Q c Nc hcN with
      | inl hc0 =>
        exfalso
        apply hl
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
        have hnc0 : nc = 0 := by
          cases Nat.lt_or_ge (nc + n) (n + 1) with
          | inl hlt => omega
          | inr hge =>
            exfalso
            have htop2 : psMul ratRing c d (nc + n) ≠ ratRing.zero :=
              pdv_mul_top_ne pbzRatField hcbnd hcl hdbnd hdl
            have hzero : psMul ratRing c d (nc + n) = ratRing.zero :=
              (congrFun heq (nc + n)).symm.trans (hb (nc + n) hge)
            exact htop2 hzero
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
