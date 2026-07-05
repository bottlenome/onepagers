/-
  IUT/ArithPilot.lean — M238F（Dβ-4: 像と q-領域の実データ化 = 前表現 arithPreRep）

  D-β 詳細化ラウンド（軸1 = 模型忠実化）の第二資産。M230F
  `IUT/FrobenioidVolume.lean` が構成した算術体積理論 `frobVol`
  （Region = 有効因子 QDiv・vol = 重み付き大域次数 degZ w）の上に、
  q-パイロット像・Θ-像・q-領域を**実際の Frobenioid 因子データ**で据え、
  `MultiradialRep` の 10 フィールドのうち **q_realized だけを外部仮説 hq に
  外部化した前表現** `arithPreRep` を構成する。

  ## 現行 gaussSkeletonW（logq = 1 固定）との違い＝係争点の非空洞化

  M141F/M158F の充足模型はスケルトンの logq を 1 に固定していたため
  Cor312（−logTheta ≥ −logq）が構成上ほぼ自動で真になり、係争点が
  空洞化していた。本モジュールの `arithSkeleton` は logq を **q-パイロット
  因子 `qPilotDiv n` の実次数**（degZ w、n で可変）から計算する。結果、
  `arithSkeleton_cor312_iff` が示すとおり Cor312 は

      Cor312 (arithSkeleton w n l B …) ↔ w 1 * n ≤ wssq w l

  という**実データの数値不等式**にちょうど同値になり、n を大きく取れば
  **偽になり得る**（空洞化しない）。これが Dβ-7 鏡像定理の算術模型版の
  芽である。

  ## 符号規約の整合（frobVol → arithVol、本モジュールの設計判断）

  frobVol の vol = degZ は ℕ 由来で常に ≥ 0 である。一方 `MultiradialRep`
  の `vol_q : vol qRegion = -s.logq` は Skeleton の `hq : logq > 0` と
  合わさると vol qRegion < 0 を要求する——**frobVol はそのままでは
  いかなる Skeleton の MultiradialRep も居住させられない**（M230F の
  正直な限定が予告したとおり）。そこで本モジュールは frobVol の
  順序・正則包を**そのまま継承**し（`arithVol_le_frob`/`arithVol_hull_frob`
  で defeq）、体積のみ procession 正規化の基準線 B だけ下駄を履かせた

      arithVol w B := { frobVol w with vol := fun x => degZ w x - B }

  を用いる。これは |log(·)| = −vol の符号規約（対数体積は負・|log| は
  正の次数）を効かせるための加法正規化であり、vol_mono は degZ_mono から
  そのまま従う（B は定数）。crux hq は依然 frobVol の順序で表現される
  （`arithVol_le_frob` より `(arithVol w B).le = (frobVol w).le`）。

  ## 新規に閉じる中核（全て sorry なし・新規 Classical.choice なし）

  * `qPilotDiv` — q-パイロット因子（単一素点 index 1・重複度 n）。
    `qPilotDiv_degZ`: degZ w (qPilotDiv n) = w 1 · n（degN_single 経由）。
  * `gaussDiv_degZ` — Θ-像因子 gaussDiv l の ℤ 次数 = wssq w l
    （M135F gaussDiv_deg_w の ℤ 化）。
  * `arithVol` — frobVol の順序を継承し vol を −B シフトした VolumeTheory。
  * `arithSkeleton` — logq := B − degZ(qPilotDiv n)（可変・> 0）、
    logTheta := B − degZ(gaussDiv l) とする Skeleton。
  * `arithPreRep` — **本タスクの主構成**: q_realized だけを外部仮説
    hq に取り、残る 9 フィールドを実データで充足した
    `MultiradialRep (arithVol w B) (arithSkeleton w n l B …)`。
  * `arithSkeleton_cor312_iff` — 係争点の非空洞化（Cor312 ⟺ 実不等式）。
  * `arith_input_transport` / `arith_rep_nonempty` — crux ⟹ Cor312 /
    crux ⟹ 表現の存在。
  * `arithPilot_wellDefined` — capstone（vol_q・logq 可変・非空洞化・
    transport の総括）。

  ## 正直な限定（これはまだ D-β 本丸ではない）

  * **q_realized は依然として外部仮説 hq**。crux は「係争点が単一の
    因子包含に縮約された」だけであり、その真偽（= 望月–Scholze–Stix
    論争の当の帰結、Dβ-ω）は本モジュールでは一切証明しない。
  * 不定性 A は最小限（Ind = Unit・image は定数 gaussDiv l）である。
    像が真に定数でない表現（軌道共変性）と不定性の作用 `IndAction` は
    **Dβ-5**、crux の単一 Prop 化 `ThetaLinkTransport` は **Dβ-6**、
    鏡像定理 `transport_iff_cor312` は **Dβ-7** の次段であり、本モジュールは
    それらを構成しない。ここで示した `arithSkeleton_cor312_iff` は
    Dβ-7 の算術模型版鏡像定理の**芽**にすぎない。
  * Unit 不定性のもとでは crux hq は素点ごとの重複度の点毎包含
    （qPilotDiv n ⊆ gaussDiv l）に退化する。これは正則包の組合せ代理
    （M230F の hull と同流）上の代理条件であり、原論文の log-Kummer 対応・
    Θ×μ_LGP-link 両立の圏論的内容は写像しない。
  * 正規化基準線 B は自由パラメータ（hB : w 1 · n < B で logq > 0 を担保）。
    その値の設計（IUT-IV の計算範囲との整合）は margin 定数トラックに委ねる。
-/
import IUT.FrobenioidVolume
import IUT.WeightedGauss

namespace IUT

/-! ## Part 1: q-パイロット因子と Θ-像因子の ℤ 次数 -/

/-- **q-パイロット因子**: 単一素点（index 1、bad place 代理）に重複度 n。
    IUT-III 系3.12 の q-パイロット対象 q の因子代理。degZ で次数 = w 1 · n。 -/
def qPilotDiv (n : Nat) : QDiv := singleDiv 1 n

/-- q-パイロット因子の ℤ 次数 = w 1 · n（degN_single の ℤ 化）。
    logq を n で可変にする実データ供給源。 -/
theorem qPilotDiv_degZ (w : Nat → Nat) (n : Nat) :
    degZ w (qPilotDiv n) = ((w 1 * n : Nat) : Int) := by
  show ((degN w (singleDiv 1 n) : Nat) : Int) = ((w 1 * n : Nat) : Int)
  rw [degN_single]

/-- Θ-像（ガウス）因子の ℤ 次数 = 重み付き平方和 wssq w l
    （M135F gaussDiv_deg_w の ℤ 化）。 -/
theorem gaussDiv_degZ (w : Nat → Nat) (l : Nat) :
    degZ w (gaussDiv l) = ((wssq w l : Nat) : Int) := by
  show ((degN w (gaussDiv l) : Nat) : Int) = ((wssq w l : Nat) : Int)
  rw [gaussDiv_deg_w]

/-! ## Part 2: 符号整合済み算術体積理論 arithVol -/

/-- **算術体積理論（符号整合版）**: frobVol の順序・正則包をそのまま継承し、
    体積を procession 正規化の基準線 B だけ下駄を履かせた
    vol x = degZ w x − B。|log(·)| = −vol の符号規約を効かせるための加法
    正規化。vol_mono は degZ_mono（B は定数）から従う。 -/
def arithVol (w : Nat → Nat) (B : Nat) : VolumeTheory :=
  { frobVol w with
    vol := fun x => degZ w x - (B : Int)
    vol_mono := by
      intro a b h
      have h2 : ∀ k, a.mult k ≤ b.mult k := h
      have hm : degZ w a ≤ degZ w b := degZ_mono w h2
      show degZ w a - (B : Int) ≤ degZ w b - (B : Int)
      omega }

/-- arithVol の順序は frobVol と同一（defeq）。crux hq が frobVol の
    包含順序で表現されることの裏付け。 -/
theorem arithVol_le_frob (w : Nat → Nat) (B : Nat) :
    (arithVol w B).le = (frobVol w).le := rfl

/-- arithVol の正則包は frobVol と同一（defeq）。 -/
theorem arithVol_hull_frob (w : Nat → Nat) (B : Nat) :
    (arithVol w B).hull = (frobVol w).hull := rfl

/-- arithVol の体積の展開（degZ w · − B）。 -/
theorem arithVol_vol_eq (w : Nat → Nat) (B : Nat) (x : QDiv) :
    (arithVol w B).vol x = degZ w x - (B : Int) := rfl

/-! ## Part 3: logq 可変な骨格 arithSkeleton -/

/-- **logq 可変な骨格**: logq := B − degZ(qPilotDiv n)（n で可変・> 0 を hB
    が担保）、logTheta := B − degZ(gaussDiv l)。現行 gaussSkeletonW の
    logq = 1 固定を廃し、係争点の空洞化を防ぐ（`arithSkeleton_cor312_iff`）。 -/
def arithSkeleton (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) : Skeleton where
  lstar := l
  hl := hl
  logq := (B : Int) - degZ w (qPilotDiv n)
  hq := by
    have hp : degZ w (qPilotDiv n) = ((w 1 * n : Nat) : Int) := qPilotDiv_degZ w n
    show (0 : Int) < (B : Int) - degZ w (qPilotDiv n)
    rw [hp]
    omega
  logTheta := (B : Int) - degZ w (gaussDiv l)

/-- arithSkeleton の logq の閉形式 = B − w 1 · n（n に明示的に依存する）。 -/
theorem arithSkeleton_logq_eq (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) :
    (arithSkeleton w n l B hl hB).logq = (B : Int) - ((w 1 * n : Nat) : Int) := by
  show (B : Int) - degZ w (qPilotDiv n) = (B : Int) - ((w 1 * n : Nat) : Int)
  rw [qPilotDiv_degZ]

/-- arithVol 上で q-領域の体積が −logq に一致（vol_q フィールドの供給源）。 -/
theorem arithVol_vol_qPilot (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) :
    (arithVol w B).vol (qPilotDiv n) = -(arithSkeleton w n l B hl hB).logq := by
  show degZ w (qPilotDiv n) - (B : Int) = -((B : Int) - degZ w (qPilotDiv n))
  omega

/-! ## Part 4: 前表現 arithPreRep（q_realized だけを外部化） -/

/-- **本タスクの主構成 (M238F): 算術前表現** —
    q_realized（q-パイロットが Θ-像に含まれる crux）だけを外部仮説 hq に
    取り、残る 9 フィールド（shell/image/hull・体積言明 vol_hull/vol_q）を
    実 Frobenioid 因子データ（qPilotDiv・gaussDiv・degZ 閉形式）で充足した
    `MultiradialRep (arithVol w B) (arithSkeleton w n l B …)`。

    不定性 A は最小限（Ind = Unit・image 定数）。crux hq は frobVol の
    包含順序で表現される（`arithVol_le_frob`）: q-パイロット因子が
    Θ-ガウス因子に点毎包含される、という log-Kummer 輸送の代理条件。 -/
def arithPreRep (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B)
    (hq : (arithVol w B).le (qPilotDiv n) (gaussDiv l)) :
    MultiradialRep (arithVol w B) (arithSkeleton w n l B hl hB) where
  Ind := Unit
  ind0 := ()
  shell := gaussDiv l
  image := fun _ => gaussDiv l
  image_in_shell := fun _ k => Nat.le_refl ((gaussDiv l).mult k)
  hullTheta := gaussDiv l
  image_in_hull := fun _ k => Nat.le_refl ((gaussDiv l).mult k)
  qRegion := qPilotDiv n
  q_realized := ⟨(), hq⟩
  vol_hull := by
    show degZ w (gaussDiv l) - (B : Int) = -((B : Int) - degZ w (gaussDiv l))
    omega
  vol_q := by
    show degZ w (qPilotDiv n) - (B : Int) = -((B : Int) - degZ w (qPilotDiv n))
    omega

/-! ## Part 5: 係争点の非空洞化と transport → Cor312 -/

/-- **係争点の非空洞化（Dβ-7 鏡像定理の芽）**: logq を実データで可変化した
    結果、Cor312 は実データの数値不等式 w 1 · n ≤ wssq w l に**ちょうど
    同値**になる。n を大きく取れば右辺を破れる（空洞化しない）。 -/
theorem arithSkeleton_cor312_iff (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) :
    Cor312 (arithSkeleton w n l B hl hB) ↔ w 1 * n ≤ wssq w l := by
  have hg : degZ w (gaussDiv l) = ((wssq w l : Nat) : Int) := gaussDiv_degZ w l
  have hp : degZ w (qPilotDiv n) = ((w 1 * n : Nat) : Int) := qPilotDiv_degZ w n
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : -((B : Int) - degZ w (gaussDiv l))
        ≥ -((B : Int) - degZ w (qPilotDiv n)) := h
    rw [hg, hp] at h'
    omega
  · show -((B : Int) - degZ w (gaussDiv l))
        ≥ -((B : Int) - degZ w (qPilotDiv n))
    rw [hg, hp]
    omega

/-- **crux ⟹ Cor312**: 外部化した輸送仮説から系3.12 が従う
    （`cor312_of_multiradial` を arithPreRep に適用）。 -/
theorem arith_input_transport (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B)
    (hq : (arithVol w B).le (qPilotDiv n) (gaussDiv l)) :
    Cor312 (arithSkeleton w n l B hl hB) :=
  cor312_of_multiradial (arithPreRep w n l B hl hB hq)

/-- **crux ⟹ 表現の存在**: 忠実算術模型上の MultiradialRep の居住が
    輸送仮説へ局在した。 -/
theorem arith_rep_nonempty (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B)
    (hq : (arithVol w B).le (qPilotDiv n) (gaussDiv l)) :
    Nonempty (MultiradialRep (arithVol w B) (arithSkeleton w n l B hl hB)) :=
  ⟨arithPreRep w n l B hl hB hq⟩

/-! ## Part 6: capstone -/

/-- **capstone (M238F): arithPreRep の well-defined 性** —
    (a) 体積言明: arithVol 上で q-領域の体積 = −logq、
    (b) logq 可変: logq = B − w 1 · n（n に依存）、
    (c) 非空洞化: Cor312 ⟺ 実不等式 w 1 · n ≤ wssq w l、
    (d) 輸送: crux ⟹ Cor312。
    忠実模型化トラック（軸1）が像・q-領域まで実データ化され、係争点が
    q_realized 一本に外部化されたことの機械検証。 -/
theorem arithPilot_wellDefined (w : Nat → Nat) (n l B : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) :
    ((arithVol w B).vol (qPilotDiv n) = -(arithSkeleton w n l B hl hB).logq)
      ∧ ((arithSkeleton w n l B hl hB).logq = (B : Int) - ((w 1 * n : Nat) : Int))
      ∧ (Cor312 (arithSkeleton w n l B hl hB) ↔ w 1 * n ≤ wssq w l)
      ∧ ((arithVol w B).le (qPilotDiv n) (gaussDiv l)
          → Cor312 (arithSkeleton w n l B hl hB)) :=
  ⟨arithVol_vol_qPilot w n l B hl hB,
   arithSkeleton_logq_eq w n l B hl hB,
   arithSkeleton_cor312_iff w n l B hl hB,
   fun hq => arith_input_transport w n l B hl hB hq⟩

end IUT
