/-
  # M240F: 効果性順序から実数値 log-volume の単調性へ（柱C・log-volume 橋の残件）

  柱C（issue #37）C-1。M131F（`LogVolBridge.lean`）は実数値 log-volume
  `rlogVol = qToReal ∘ qdegQ` を実体化したが、その正直申告 (2) で

    「因子の効果性順序（mult の点ごと比較）から degZ の比較を導く
     nsum の単調性簿記は本層では扱わない」

  と明記していた。その後 M230F（`FrobenioidVolume.lean`）が
  `degZ_mono`——各座標の重複度の点ごと比較 `∀ k, x.mult k ≤ y.mult k`
  から重み付き大域次数の比較 `degZ w x ≤ degZ w y` を導く簿記——を
  閉じた。本層はこの `degZ_mono`（M230F-1）を M131F の埋め込み単調性
  `qToReal_mono` / `ratOfInt_le` / `rlogVol_mono` と**合成**し、
  効果性順序を**有理数値次数 qdegQ・実数値 log-volume rlogVol の
  比較まで一気に持ち上げる**。これで M131F 正直申告 (2) の残件を
  回収し、効果的因子の格子順序が本物の ℝ の順序 rLe として作用する
  ことを機械検証する。

  * M240F-1 `qdegQ_effmono` — **効果性順序 ⟹ 有理数値次数の比較**
    （degZ_mono を ratOfInt_le で qLe に持ち上げ）
  * M240F-2 `rlogVol_effmono`（本丸）— **効果性順序 ⟹ 実数値
    log-volume の比較** `∀k x.mult k ≤ y.mult k → rLe (vol x) (vol y)`
    （degZ_mono を rlogVol_mono に投入）
  * M240F-3 `qdegQ_hull_left` / `rlogVol_hull_left` /
    `rlogVol_hull_right` — **正則包（qdivSup, 各座標 max）の膨張は
    log-volume を増やすのみ**: x ⊆ x⊔y ⟹ vol x ≤ vol(x⊔y)。
    M230F の `frobVol_expansion_monotone`（Int 値）を実数値 rlogVol へ
    持ち上げる（Ind3 の上方包含が本物の ℝ で体積を増やすだけ）
  * M240F-4 `frobVol_le_rlogVol_mono` — **抽象体積理論の順序橋**:
    算術体積理論 `frobVol w`（M230F-2）の包含順序 `(frobVol w).le` が
    実数値 log-volume rlogVol の順序 rLe に忠実に持ち上がる
  * M240F-5 `rlogVol_realify_effmono` — **M67F 実化側との合流**:
    形式実化次数 degR ∘ realify を比較射 nnqToQ で ℚ→ℝ に読んだ値も
    効果性順序で単調（qdegQ_compat_realify で rlogVol に同定）
  * M240F-6 `LogVolEffMonoData` — 総括データ束と存在

  ## 意義

  M131F の残件（正直申告 (2)）を M230F の `degZ_mono` の完成を機に回収
  する。因子の効果性順序（各素点での重複度の点ごと比較）という**幾何的
  に自然な半順序**が、有理数値・実数値の log-volume の順序に忠実に
  持ち上がることを固定し、正則包（holomorphic hull の組合せ代理）の
  膨張が体積を増やすだけであること（Ind3 の上半両立性の体積側裏付け）を
  本物の ℝ の言葉 rLe で機械検証する。

  ## 正直な限定

  * 本層は M230F の `degZ_mono`（Int 値の点ごと単調性）と M131F の
    埋め込み単調性 `qToReal_mono` / `ratOfInt_le` / `rlogVol_mono` の
    **合成のみ**であり、新規の算術核（nsum 単調性など）は追加しない。
    それらは M230F で既に閉じている。
  * 効果性順序は「各座標 mult の点ごと ≤」で表す。因子の効果性の
    本来の定義（有効因子 = 非負係数）との一致は QDiv の設計（重複度は
    ℕ 値）に組み込まれており、本層はその半順序を前提として使う。
  * 正則包 qdivSup は各座標 max の**組合せ代理**であり、原論文の
    holomorphic hull の複素幾何的内容は写像しない（M230F の限定を継承）。
  * 実数係数の一般スカラー作用・厳密不等式（strict <）は扱わない。
    本層は非狭義単調性（rLe）のみ。

  全て選択公理不使用（型継承除く）。`#print axioms` で実測。
  サブエージェント並行部品。
-/
import IUT.LogVolBridge
import IUT.FrobenioidVolume

namespace IUT

/-! ## M240F-1: 効果性順序 ⟹ 有理数値次数の比較 -/

/-- **定理 (M240F-1): 有理数値次数の効果性単調性** — 各座標の重複度が
    点ごとに ≤（`∀ k, x.mult k ≤ y.mult k`）なら有理数値次数も比較
    `qdegQ w x ≤ qdegQ w y`（qLe）。M230F の `degZ_mono` を M123F の
    埋め込み順序保存 `ratOfInt_le` で ℚ に持ち上げる。 -/
theorem qdegQ_effmono (w : Nat → Nat) {x y : QDiv}
    (h : ∀ k, x.mult k ≤ y.mult k) : qLe (qdegQ w x) (qdegQ w y) :=
  ratOfInt_le (degZ_mono w h)

/-! ## M240F-2: 効果性順序 ⟹ 実数値 log-volume の比較（本丸） -/

/-- **定理 (M240F-2): 実数値 log-volume の効果性単調性（本丸）** —
    各座標の重複度が点ごとに ≤ なら実数値 log-volume も本物の ℝ の順序
    `rLe (rlogVol w x) (rlogVol w y)`。M230F の `degZ_mono` を M131F の
    `rlogVol_mono` に投入する。M131F 正直申告 (2)（効果性順序からの
    単調性簿記）の回収の中核。 -/
theorem rlogVol_effmono (w : Nat → Nat) {x y : QDiv}
    (h : ∀ k, x.mult k ≤ y.mult k) : rLe (rlogVol w x) (rlogVol w y) :=
  rlogVol_mono w (degZ_mono w h)

/-! ## M240F-3: 正則包の膨張は log-volume を増やすのみ -/

/-- **定理 (M240F-3a): 正則包の有理数値次数下界（左）** —
    x ⊆ x⊔y なので `qdegQ w x ≤ qdegQ w (qdivSup x y)`（qLe）。
    正則包（各座標 max）の膨張は有理数値次数を増やすのみ。 -/
theorem qdegQ_hull_left (w : Nat → Nat) (x y : QDiv) :
    qLe (qdegQ w x) (qdegQ w (qdivSup x y)) :=
  qdegQ_effmono w (fun k => Nat.le_max_left (x.mult k) (y.mult k))

/-- **定理 (M240F-3b): 正則包の実数値 log-volume 下界（左）** —
    `rLe (rlogVol w x) (rlogVol w (qdivSup x y))`。正則包の膨張は本物の
    ℝ の順序で log-volume を増やすのみ（Ind3 の上半両立性の体積側
    裏付けの実数形、左因子）。 -/
theorem rlogVol_hull_left (w : Nat → Nat) (x y : QDiv) :
    rLe (rlogVol w x) (rlogVol w (qdivSup x y)) :=
  rlogVol_effmono w (fun k => Nat.le_max_left (x.mult k) (y.mult k))

/-- **定理 (M240F-3c): 正則包の実数値 log-volume 下界（右）** —
    `rLe (rlogVol w y) (rlogVol w (qdivSup x y))`。同上（右因子）。 -/
theorem rlogVol_hull_right (w : Nat → Nat) (x y : QDiv) :
    rLe (rlogVol w y) (rlogVol w (qdivSup x y)) :=
  rlogVol_effmono w (fun k => Nat.le_max_right (x.mult k) (y.mult k))

/-! ## M240F-4: 抽象体積理論 frobVol の順序橋 -/

/-- **定理 (M240F-4): 算術体積理論の順序橋** — M230F-2 の算術体積理論
    `frobVol w`（VolumeTheory インスタンス）の包含順序 `(frobVol w).le`
    が実数値 log-volume rlogVol の順序 rLe に忠実に持ち上がる:
    `(frobVol w).le x y → rLe (rlogVol w x) (rlogVol w y)`。
    抽象体積理論の格子順序と実数値 log-volume の合流。 -/
theorem frobVol_le_rlogVol_mono (w : Nat → Nat) {x y : QDiv}
    (h : (frobVol w).le x y) : rLe (rlogVol w x) (rlogVol w y) :=
  rlogVol_effmono w h

/-! ## M240F-5: M67F 実化側との合流 -/

/-- **定理 (M240F-5): 実化次数側の効果性単調性** — 形式実化次数
    degR ∘ realify を比較射 nnqToQ で ℚ→ℝ に読んだ値も効果性順序で
    単調: `∀k, x.mult k ≤ y.mult k` なら
    `rLe (qToReal (nnqToQ (degR w (realify x)))) (qToReal (nnqToQ (degR w (realify y))))`。
    M131F-5a の可換図式 `qdegQ_compat_realify` で rlogVol に同定し
    M240F-2 に帰着（M67F 実化側と橋の効果性単調性の合流）。 -/
theorem rlogVol_realify_effmono (w : Nat → Nat) {x y : QDiv}
    (h : ∀ k, x.mult k ≤ y.mult k) :
    rLe (qToReal (nnqToQ (degR w (realify x))))
      (qToReal (nnqToQ (degR w (realify y)))) := by
  rw [qdegQ_compat_realify, qdegQ_compat_realify]
  exact rlogVol_effmono w h

/-! ## M240F-6: 総括 -/

/-- **M240F-6a: 総括** — 効果性順序 → log-volume 単調性橋のデータ束。
    M131F 正直申告 (2) の残件（効果性順序からの単調性簿記）を M230F の
    `degZ_mono` の完成を機に回収し、効果的因子の格子順序が有理数値・
    実数値 log-volume の順序に忠実に持ち上がることの実定理のみを束ねる
    （新規算術核なし・合成のみ）。 -/
structure LogVolEffMonoData where
  /-- 効果性順序 ⟹ 有理数値次数の比較。 -/
  qdeg : ∀ (w : Nat → Nat) {x y : QDiv}, (∀ k, x.mult k ≤ y.mult k) →
    qLe (qdegQ w x) (qdegQ w y)
  /-- 効果性順序 ⟹ 実数値 log-volume の比較（本丸）。 -/
  rvol : ∀ (w : Nat → Nat) {x y : QDiv}, (∀ k, x.mult k ≤ y.mult k) →
    rLe (rlogVol w x) (rlogVol w y)
  /-- 正則包の膨張は実数値 log-volume を増やすのみ（左）。 -/
  hull_left : ∀ (w : Nat → Nat) (x y : QDiv),
    rLe (rlogVol w x) (rlogVol w (qdivSup x y))
  /-- 正則包の膨張は実数値 log-volume を増やすのみ（右）。 -/
  hull_right : ∀ (w : Nat → Nat) (x y : QDiv),
    rLe (rlogVol w y) (rlogVol w (qdivSup x y))
  /-- 抽象体積理論 frobVol の順序橋。 -/
  frobVol_bridge : ∀ (w : Nat → Nat) {x y : QDiv}, (frobVol w).le x y →
    rLe (rlogVol w x) (rlogVol w y)
  /-- M67F 実化側との合流（効果性単調性）。 -/
  realify : ∀ (w : Nat → Nat) {x y : QDiv}, (∀ k, x.mult k ≤ y.mult k) →
    rLe (qToReal (nnqToQ (degR w (realify x))))
      (qToReal (nnqToQ (degR w (realify y))))

/-- **M240F-6b: witness**。 -/
def logVolEffMonoData : LogVolEffMonoData where
  qdeg := qdegQ_effmono
  rvol := rlogVol_effmono
  hull_left := rlogVol_hull_left
  hull_right := rlogVol_hull_right
  frobVol_bridge := frobVol_le_rlogVol_mono
  realify := rlogVol_realify_effmono

/-- **capstone (M240F-6c): 存在** — 効果性順序 → log-volume 単調性橋の
    データが無矛盾に存在する。柱C log-volume 橋の M131F 正直申告 (2) を
    回収し、効果的因子の格子順序が実数値 log-volume の順序に忠実に
    持ち上がることの単一証明記録としての締めくくり。 -/
theorem logVolEffMono_exists : Nonempty LogVolEffMonoData :=
  ⟨logVolEffMonoData⟩

end IUT
