/-
  IUT/TransportMirror.lean — M249F（Dβ-7: 鏡像定理 transport_iff_cor312）

  D-β 詳細化ラウンド（軸2 = crux 縮約）の **honestly-closeable な最終到達点**。
  M244F `IUT/ThetaLinkTransport.lean` は crux（`MultiradialRep.q_realized`）を
  ただ一つの名前付き Prop `ThetaLinkTransport`（q-パイロット因子 `qPilotDiv n`
  が不定性作用 `unitIndAction` の像の軌道のどれかに**点毎包含**される）に
  縮約し、順方向（transport ⟹ input ⟹ 系3.12）を機械検証した。本モジュールは
  その crux が**ちょうど係争中の数値不等式 `w 1 · n ≤ wssq w l` に同値**である
  ことを機械検証し、「この Prop はちょうど係争不等式であり、これ以上の還元は
  論争の裁定に等しい」を形式体系内の定理にする。

  ## 中心的知見: 鏡像定理は「次数レベル」でちょうど両側同値になる

  crux は二つの強さで現れる:

  * **点毎 transport**（`ThetaLinkTransport`, M244F）: `qPilotDiv n` が像の
    軌道に**座標毎に** ≤ で包含される（∀k, mult k ≤ mult k）。これが
    `MultiradialRep.q_realized` を実際に供給し、input 居住を与える強い形。
  * **次数 transport**（`ThetaLinkTransportDeg`, 本モジュール）: `qPilotDiv n`
    の大域次数 `degZ` が像の次数以下である（∃i, degZ ≤ degZ）という弱い形。

  degZ は単調（`degZ_mono`: 点毎 ≤ ⟹ 次数 ≤）なので **点毎 ⟹ 次数** は
  常に成り立つ（`transport_to_transportDeg`）。しかし逆（次数 ⟹ 点毎）は
  一般に**偽**である——点毎包含は index 1 で `n ≤ (像).mult 1 = 1` を要求し、
  次数不等式 `w 1 · n ≤ wssq w l`（重み付き和）よりも真に強い。この
  **次数 ⟹ 点毎の隔たりこそが log-Kummer 対応・Θ×μ_LGP-link 両立が供給
  すると主張される当の内容（Dβ-ω）**であり、`transport_strictly_stronger`
  で「次数側は成立するが点毎側は破れる」具体例を機械検証して隔たりの実在を
  示す。

  したがって honestly-closeable な**鏡像定理は次数レベルで両側同値**として
  閉じる:

      ThetaLinkTransportDeg w n l k₀ hw0
        ↔ w 1 · n ≤ wssq w l          （`transportDeg_iff_ineq`）
        ↔ Cor312 (arithSkeleton …)     （`transportDeg_iff_cor312` = 鏡像定理）

  ## 新規に閉じる中核（全て sorry なし・新規 Classical.choice なし）

  * `ThetaLinkTransportDeg` — 次数レベルの transport（crux の弱形）。
  * `transportDeg_iff_ineq` — **次数 transport ⟺ 係争不等式 w 1 · n ≤ wssq w l**
    （両方向）。すべての軌道像が等次数 wssq（`IndAction.deg_image`）であること
    が鍵——∃ は基点 `false` で実現・任意 i で必要条件が同じ値に潰れる。
  * `transportDeg_iff_cor312` — **鏡像定理（両方向）**: 次数 transport ⟺
    Cor312。`transportDeg_iff_ineq` と M238F `arithSkeleton_cor312_iff` の合成。
  * `transport_to_transportDeg` — **点毎 ⟹ 次数**（`degZ_mono`、honest な向き）。
  * `transport_forward` — 点毎 transport ⟹ Cor312 を**鏡像経由**で再導出
    （M244F `cor312_of_transport` の次数分解版）。
  * `transportDeg_of_ineq` / `transportDeg_fails_of_large` — 係争不等式の
    両側からの transport 制御（後者が n > wssq 側での**非居住**）。
  * `arith_mirror_independent` — **算術模型版の独立性**（`cor312_independent`
    の再現）: 固定 (w, l, k₀) 上で、小さい n で次数 transport は成立し、
    大きい n（n = wssq+1、w 1 ≥ 1）で成立しない。係争点が空洞化しないことの帰結。
  * `transport_strictly_stronger` — **点毎 transport は次数 transport より
    真に強い**の具体 witness（次数側成立・点毎側破れ）。次数 ⟹ 点毎の隔たり
    ＝ Dβ-ω の実在の機械検証。
  * `arith_input_forward` — 忠実模型上の入力居住 ⟹ 係争不等式（`iut_localized`
    の算術模型特殊化。逆は Dβ-ω、下記正直な限定参照）。
  * `transportMirror` — capstone（鏡像両方向・点毎⟹次数・点毎⟹Cor312・
    入力居住⟹Cor312・大 n 非居住 の総括）。

  ## 正直な限定（Dβ-ω = 恒久的範囲外）

  * **honestly-closeable な鏡像定理は次数レベルの両側同値である**。点毎
    `ThetaLinkTransport` については**順方向のみ**（点毎 ⟹ 次数 ⟹ Cor312）が
    証明可能で、**逆（Cor312 ⟹ 点毎 transport）は証明していない・一般に偽**。
    その逆＝「次数不等式から実際の座標毎包含（log-Kummer 輸送）を構成する」
    ことこそが Dβ-ω（多輻的アルゴリズムの構成本体・[AbsTopIII] 環復元・
    tempered π₁ エタールテータ剛性・全レベル log-Kummer・Θ×μ_LGP-link）で
    あり、Scholze–Stix–望月論争の当の係争点である。本モジュールは
    `transport_strictly_stronger` でこの隔たりが**空でない**ことまでを示す。
  * 同様に `arith_input_iff_cor312` は**完全な両側同値としては閉じない**:
    順方向 `arith_input_forward`（居住 ⟹ Cor312 = `iut_localized`）は成立するが、
    逆（Cor312 ⟹ 入力居住）は q_realized の点毎実現を要し Dβ-ω に帰着する。
  * 係争不等式 `w 1 · n ≤ wssq w l` の**真偽そのもの（Dβ-ω）は判定しない**。
    鏡像定理が確立するのは「crux は過不足なくこの不等式に同値（次数レベル）で
    あり、残るのは不等式を正しいと判定する数学的判断だけ」という局在の鋭さの
    最終形である。したがって「D-β 形式化可能部分」≠「IUT が正しい」。
  * 不定性は Ind2（単数トーソル `unitIndAction`）のみ・忠実算術模型
    （`arithVol` = frobVol の −B 正規化）上。Ind1（ラベル置換）・Ind3（上方
    包含）の同時作用は未実装（M241F の限定を継承）。点毎包含は正則包の組合せ
    代理上の代理条件であり、原論文の log-Kummer 対応の圏論的内容は写像しない。
  * `arithSkeleton` の順序は `arithVol w B` のものだが `frobVol w` と defeq
    （M238F `arithVol_le_frob`）で B 非依存。次数 transport は B に依存しない
    （degZ の比較のみ）ため `ThetaLinkTransportDeg` は B を引数に取らない。

  継承 Classical: 本モジュール自身は新規 Classical.choice を導入しない。
  sorry なし・禁止タクティク不使用（core Lean のみ）。tier M（opus）。
-/
import IUT.ThetaLinkTransport

namespace IUT

/-! ## Part 1: 次数レベルの transport（crux の弱形） -/

/-- **次数レベルの Θ-リンク輸送（Dβ-7 の鏡像の左辺）**: q-パイロット因子
    `qPilotDiv n` の大域次数 `degZ` が、不定性作用 `unitIndAction` の像の
    軌道のどれかの次数以下である、という単一 Prop。点毎 transport
    `ThetaLinkTransport`（M244F）の**次数への射影**——`degZ_mono` により
    点毎 ⟹ 次数 は常に成り立つが、逆は一般に偽（下記 `transport_strictly_stronger`）。
    B に依存しない（degZ の比較のみ）ため B は引数に取らない。 -/
def ThetaLinkTransportDeg (w : Nat → Nat) (n l k₀ : Nat) (hw0 : w k₀ = 0) : Prop :=
  ∃ i, degZ w (qPilotDiv n) ≤ degZ w ((unitIndAction w l k₀ hw0).image i)

/-! ## Part 2: 鏡像定理（次数 transport ⟺ 係争不等式 ⟺ Cor312） -/

/-- **鏡像定理の核（両方向）**: 次数 transport は係争中の数値不等式
    `w 1 · n ≤ wssq w l` に**ちょうど同値**。すべての軌道像が等次数
    `degZ (gaussDiv l) = wssq w l`（`IndAction.deg_image`・`gaussDiv_degZ`）で
    あることが鍵: ∃ は任意の i で同じ値 wssq に潰れ、基点で実現される。 -/
theorem transportDeg_iff_ineq (w : Nat → Nat) (n l k₀ : Nat) (hw0 : w k₀ = 0) :
    ThetaLinkTransportDeg w n l k₀ hw0 ↔ w 1 * n ≤ wssq w l := by
  have hp : degZ w (qPilotDiv n) = ((w 1 * n : Nat) : Int) := qPilotDiv_degZ w n
  have hg : degZ w (gaussDiv l) = ((wssq w l : Nat) : Int) := gaussDiv_degZ w l
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨i, hi⟩ := h
    have hd : degZ w ((unitIndAction w l k₀ hw0).image i) = degZ w (gaussDiv l) :=
      (unitIndAction w l k₀ hw0).deg_image i
    rw [hd, hg, hp] at hi
    omega
  · refine ⟨(unitIndAction w l k₀ hw0).base, ?_⟩
    have hd : degZ w ((unitIndAction w l k₀ hw0).image (unitIndAction w l k₀ hw0).base)
        = degZ w (gaussDiv l) :=
      (unitIndAction w l k₀ hw0).deg_image _
    rw [hd, hg, hp]
    omega

/-- **鏡像定理 (M249F, capstone の核): ThetaLinkTransportDeg ⟺ Cor312** —
    次数 transport がちょうど系3.12（当該骨格の数値不等式）に両側同値である
    ことの機械検証。`transportDeg_iff_ineq` と M238F `arithSkeleton_cor312_iff`
    の合成。crux（次数レベル）はちょうど係争不等式であり、これ以上の還元は
    論争の裁定（Dβ-ω）に等しい——`cor312_independent` の骨格レベル独立性の
    算術模型レベルでの再現。 -/
theorem transportDeg_iff_cor312 (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0) :
    ThetaLinkTransportDeg w n l k₀ hw0 ↔ Cor312 (arithSkeleton w n l B hl hB) :=
  (transportDeg_iff_ineq w n l k₀ hw0).trans
    (arithSkeleton_cor312_iff w n l B hl hB).symm

/-! ## Part 3: 点毎 transport との接続（honest な順方向） -/

/-- **点毎 ⟹ 次数（honest な向き）**: 点毎 transport（M244F、`arithVol` の
    座標毎包含）は次数 transport を含意する——`degZ_mono`（点毎 ≤ ⟹ 次数 ≤）。
    逆（次数 ⟹ 点毎）は一般に偽（`transport_strictly_stronger`）であり、
    それが Dβ-ω の実質。 -/
theorem transport_to_transportDeg (w : Nat → Nat) (n l B k₀ : Nat) (hw0 : w k₀ = 0)
    (h : ThetaLinkTransport w n l B k₀ hw0) :
    ThetaLinkTransportDeg w n l k₀ hw0 := by
  obtain ⟨i, hle⟩ := h
  have hle' : ∀ k, (qPilotDiv n).mult k
      ≤ ((unitIndAction w l k₀ hw0).image i).mult k := hle
  exact ⟨i, degZ_mono w hle'⟩

/-- **点毎 transport ⟹ Cor312（鏡像経由の再導出）**: M244F
    `cor312_of_transport` を、点毎 ⟹ 次数（`transport_to_transportDeg`）と
    鏡像定理（`transportDeg_iff_cor312`）の合成として次数レベルで分解した形。 -/
theorem transport_forward (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0)
    (h : ThetaLinkTransport w n l B k₀ hw0) :
    Cor312 (arithSkeleton w n l B hl hB) :=
  (transportDeg_iff_cor312 w n l B k₀ hl hB hw0).mp
    (transport_to_transportDeg w n l B k₀ hw0 h)

/-! ## Part 4: 係争不等式の両側からの transport 制御 -/

/-- 係争不等式が成り立てば次数 transport は成立（鏡像の mpr）。 -/
theorem transportDeg_of_ineq (w : Nat → Nat) (n l k₀ : Nat) (hw0 : w k₀ = 0)
    (h : w 1 * n ≤ wssq w l) :
    ThetaLinkTransportDeg w n l k₀ hw0 :=
  (transportDeg_iff_ineq w n l k₀ hw0).mpr h

/-- **n > wssq 側での非居住**: q-パイロットの次数が Θ-像の次数を超えると
    （wssq w l < w 1 · n）次数 transport は**成立しない**。`cor312_independent`
    の算術模型版（係争点が空洞化しない＝Cor312 が偽になり得ることの帰結）。 -/
theorem transportDeg_fails_of_large (w : Nat → Nat) (n l k₀ : Nat) (hw0 : w k₀ = 0)
    (h : wssq w l < w 1 * n) :
    ¬ ThetaLinkTransportDeg w n l k₀ hw0 := by
  intro hT
  have hle := (transportDeg_iff_ineq w n l k₀ hw0).mp hT
  omega

/-- **算術模型版の独立性（`cor312_independent` の再現・強化）**: 固定した
    重み w（w 1 ≥ 1）・レベル l（≥ 2）・単数座標 k₀（w k₀ = 0）のもとで、
    小さい n（n = 0）で次数 transport は**成立**し、大きい n（n = wssq+1）で
    **成立しない**。crux は骨格からは決定されず、係争不等式の真偽に過不足なく
    局在する——という独立性が忠実算術模型上で再現された。 -/
theorem arith_mirror_independent (w : Nat → Nat) (l k₀ : Nat)
    (_hl : 2 ≤ l) (hw0 : w k₀ = 0) (hw1 : 1 ≤ w 1) :
    (∃ n, ThetaLinkTransportDeg w n l k₀ hw0)
      ∧ (∃ n, ¬ ThetaLinkTransportDeg w n l k₀ hw0) := by
  refine ⟨⟨0, ?_⟩, ⟨wssq w l + 1, ?_⟩⟩
  · exact transportDeg_of_ineq w 0 l k₀ hw0 (by omega)
  · refine transportDeg_fails_of_large w (wssq w l + 1) l k₀ hw0 ?_
    have h1 : 1 * (wssq w l + 1) ≤ w 1 * (wssq w l + 1) :=
      Nat.mul_le_mul hw1 (Nat.le_refl (wssq w l + 1))
    rw [Nat.one_mul] at h1
    omega

/-! ## Part 5: 点毎 transport は次数 transport より真に強い（Dβ-ω の隔たり） -/

/-- **点毎 transport ⊋ 次数 transport の具体 witness**: 重み
    w = (k ↦ if k = 0 then 0 else 1)・n = 2・l = 2・k₀ = 0 において、
    次数 transport は成立する（w 1 · 2 = 2 ≤ wssq w 2 = 5）が、点毎 transport
    は**破れる**（index 1 で q-パイロットの重複度 2 は、いずれの軌道像の
    重複度 1 にも収まらない）。次数 ⟹ 点毎の隔たり＝ log-Kummer 輸送の実質
    ＝ Dβ-ω が**空でない**ことの機械検証。 -/
theorem transport_strictly_stronger :
    ∃ (w : Nat → Nat) (n l B k₀ : Nat) (hw0 : w k₀ = 0),
      ThetaLinkTransportDeg w n l k₀ hw0
        ∧ ¬ ThetaLinkTransport w n l B k₀ hw0 := by
  refine ⟨fun k => if k = 0 then 0 else 1, 2, 2, 3, 0, rfl, ?_, ?_⟩
  · -- 次数側: w 1 · 2 = 2 ≤ wssq w 2 = 5
    apply transportDeg_of_ineq
    show (if (1 : Nat) = 0 then 0 else 1) * 2
        ≤ wssq (fun k => if k = 0 then 0 else 1) 2
    rw [if_neg (show ¬(1 : Nat) = 0 by omega)]
    have hwssq : wssq (fun k => if k = 0 then 0 else 1) 2 = 5 := rfl
    rw [hwssq]
    omega
  · -- 点毎側: index 1 で破れる
    intro h
    obtain ⟨i, hi⟩ := h
    have hi' : ∀ k, (qPilotDiv 2).mult k
        ≤ ((unitIndAction (fun k => if k = 0 then 0 else 1) 2 0 rfl).image i).mult k :=
      hi
    have h1 := hi' 1
    have hq1 : (qPilotDiv 2).mult 1 = 2 := by
      show (if (1 : Nat) = 1 then 2 else 0) = 2
      rw [if_pos rfl]
    cases i with
    | false =>
      have himg :
          ((unitIndAction (fun k => if k = 0 then 0 else 1) 2 0 rfl).image false).mult 1
            = 1 := by
        show (if (1 : Nat) ≤ 2 then 1 * 1 else 0) = 1
        rw [if_pos (show (1 : Nat) ≤ 2 by omega)]
      rw [hq1, himg] at h1
      omega
    | true =>
      have himg :
          ((unitIndAction (fun k => if k = 0 then 0 else 1) 2 0 rfl).image true).mult 1
            = 1 := by
        show (if (1 : Nat) ≤ 2 then 1 * 1 else 0) + (if (1 : Nat) = 0 then 1 else 0) = 1
        rw [if_pos (show (1 : Nat) ≤ 2 by omega), if_neg (show ¬(1 : Nat) = 0 by omega)]
      rw [hq1, himg] at h1
      omega

/-! ## Part 6: 入力居住の順方向（逆は Dβ-ω） -/

/-- **忠実模型上の入力居住 ⟹ 係争不等式**: `MultiradialInput` が忠実算術模型
    `arithVol` 上で居住すれば Cor312（= 係争不等式）が従う（`iut_localized`
    の算術模型特殊化）。逆（Cor312 ⟹ 入力居住）は q_realized の点毎実現を要し
    Dβ-ω に帰着するため**両側同値としては閉じない**（正直な限定参照）。 -/
theorem arith_input_forward (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B)
    (h : Nonempty (MultiradialInput (arithVol w B) (arithSkeleton w n l B hl hB))) :
    Cor312 (arithSkeleton w n l B hl hB) :=
  iut_localized h

/-! ## Part 7: capstone（鏡像定理の総括） -/

/-- **capstone (M249F): 鏡像定理の well-defined 性** —
    (a) **鏡像（両方向）**: 次数 transport ⟺ Cor312、
    (b) 点毎 transport ⟹ 次数 transport（honest な向き）、
    (c) 点毎 transport ⟹ Cor312（鏡像経由）、
    (d) 入力居住 ⟹ Cor312（`iut_localized`）、
    (e) n > wssq 側での非居住（次数 transport が成立しない）。
    crux（次数レベル）が像・q-領域の実データ化・不定性の作用（軸1）と
    単一 Prop 化（軸2）を経て、ちょうど係争中の数値不等式に両側同値で局在した
    ことの機械検証。点毎 ⟹ 次数の逆（次数 ⟹ 点毎 = log-Kummer 輸送の実質）
    と不等式の真偽は Dβ-ω（恒久的範囲外）。 -/
theorem transportMirror (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0) :
    (ThetaLinkTransportDeg w n l k₀ hw0 ↔ Cor312 (arithSkeleton w n l B hl hB))
      ∧ (ThetaLinkTransport w n l B k₀ hw0 → ThetaLinkTransportDeg w n l k₀ hw0)
      ∧ (ThetaLinkTransport w n l B k₀ hw0 → Cor312 (arithSkeleton w n l B hl hB))
      ∧ (Nonempty (MultiradialInput (arithVol w B) (arithSkeleton w n l B hl hB))
          → Cor312 (arithSkeleton w n l B hl hB))
      ∧ (wssq w l < w 1 * n → ¬ ThetaLinkTransportDeg w n l k₀ hw0) :=
  ⟨transportDeg_iff_cor312 w n l B k₀ hl hB hw0,
   fun h => transport_to_transportDeg w n l B k₀ hw0 h,
   fun h => transport_forward w n l B k₀ hl hB hw0 h,
   fun h => arith_input_forward w n l B hl hB h,
   fun h => transportDeg_fails_of_large w n l k₀ hw0 h⟩

end IUT
