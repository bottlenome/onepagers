/-
  IUT/ThetaLinkTransport.lean — M244F（Dβ-6: crux の単一 Prop 化 ThetaLinkTransport）

  D-β 詳細化ラウンド（軸2 = crux 縮約）の到達点。M238F `IUT/ArithPilot.lean`
  の前表現 `arithPreRep`（q_realized だけを外部仮説 hq に外部化）と M241F
  `IUT/IndAction.lean` の作用付き前表現 `arithPreRepInd`（不定性が QDiv 領域へ
  実際に作用し image が非定数軌道を持つ）は、`MultiradialRep` の 10 フィールドの
  うち **q_realized（crux）だけ**を外部仮説として残していた。本モジュールは
  その最後の crux を、**単一の名前付き Prop `ThetaLinkTransport`** に縮約し、
  それが `MultiradialInput` の居住をちょうど与えることを機械検証する。

  ## 核心（crux が単一 Prop に縮約された）

  * `ThetaLinkTransport w n l B k₀ hw0`（Prop）: **Θ-リンク輸送** =
    「q-パイロット因子 `qPilotDiv n` が、不定性作用 `unitIndAction`（M241F、
    Ind2 単数トーソルの QDiv 上の作用）の像の**軌道のどれか**に点毎包含
    される」という単一命題
        ∃ i, (arithVol w B).le (qPilotDiv n) ((unitIndAction w l k₀ hw0).image i)
    IUT-III 系3.12 の (ii) log-Kummer + (iii) Θ×μ_LGP-link 両立 + Remark 3.12.2
    の閉ループが供給すると主張される帰結の、忠実算術模型上での抽出形。
    非定数軌道（`unitIndAction_orbit`）を持つ像に対する crux であり、M238F の
    定数像に対する crux hq の一般化。

  * `input_of_transport` — **本タスクの主定理（capstone）**: 単一 Prop
    `ThetaLinkTransport` から、`arithPreRepInd`（M241F）で
    `MultiradialRep (arithVol w B) (arithSkeleton w n l B …)` を居住させ、
    `inputOfRep`（M215F）で `MultiradialInput` へ持ち上げる。IUT の正否は
    「レコード `MultiradialInput` の居住」からさらに「単一 Prop
    `ThetaLinkTransport` の真偽」へ縮む。

  * `cor312_of_transport` — 順方向の閉じ（transport ⟹ input ⟹ 系3.12）。
    `input_of_transport` に `cor312_of_input`（M215F）を合成した一本道。

  * `thetaLinkTransport_of_base` — 逆向きの**弱形**（十分条件）: M238F/M241F の
    点毎 crux hq（`qPilotDiv n ⊆ gaussDiv l`）が `ThetaLinkTransport` を含意する
    （軌道の基点 `false` で成立）。前段の crux が本 Prop に確かに縮約されて
    いることの接続。

  * `thetaLinkTransport_wellDefined` — capstone（総括）: (a) transport ⟹ input、
    (b) transport ⟹ Cor312、(c) 点毎 crux ⟹ transport、を一つに束ねる。

  ## 正直な限定（これは D-β 本丸ではない）

  * **crux は単一 Prop `ThetaLinkTransport` に縮約されたが、その真偽は未証明**。
    `ThetaLinkTransport` を実際の数体・楕円曲線データから証明すること（= 望月
    –Scholze–Stix 論争の当の帰結、Dβ-ω = [AbsTopIII] 環復元・tempered π₁ 上の
    エタールテータ剛性・全レベル log-Kummer・Θ×μ_LGP-link の構成本体）は本
    モジュールでは**一切証明しない**。縮約したのは「crux をただ一つの命題に
    孤立させた」ことまでである。

  * **完全な逆向き `transport_of_input`（任意の入力から transport を回収）は
    証明できない・していない**。一般の `MultiradialInput (arithVol w B) …` は
    qRegion も image も自由であり、`qPilotDiv n`／`unitIndAction` の軌道に縛られ
    ないため、transport を一般に取り出せない。ここで与えるのは順方向
    （transport ⟹ input ⟹ Cor312）と、点毎 crux からの十分条件のみ。
    **鏡像定理 `transport_iff_cor312`（ThetaLinkTransport ⟺ 係争数値不等式
    w 1 · n ≤ wssq w l の両側同値）は Dβ-7 の次段**であり、本モジュールでは
    構成しない（M238F `arithSkeleton_cor312_iff` がその芽を Cor312 側で
    与えている）。

  * transport の定義は `arithVol w B` の順序を用いるが、これは `frobVol w` の
    順序と defeq（M238F `arithVol_le_frob`）であり、B に依存しない包含条件で
    ある。不定性は Ind2（単数）のみで、Ind1（ラベル置換）・Ind3（上方包含）の
    同時作用は未実装（M241F の限定を継承）。点毎包含は正則包の組合せ代理上の
    代理条件であり、原論文の log-Kummer 対応の圏論的内容は写像しない。

  継承 Classical: 本モジュール自身は新規 Classical.choice を導入しない。
  sorry なし・禁止タクティク不使用（core Lean のみ）。tier M（opus）。
-/
import IUT.IndAction
import IUT.MultiradialInput

namespace IUT

/-! ## Part 1: crux の単一 Prop 化 — ThetaLinkTransport -/

/-- **Θ-リンク輸送（Dβ-6 の中心命題）**: q-パイロット因子 `qPilotDiv n` が、
    不定性作用 `unitIndAction`（M241F、Ind2 単数トーソルの QDiv 上の作用・
    非定数軌道）の像の**軌道のどれか**に点毎包含される、という単一 Prop。

    `MultiradialRep` の crux フィールド `q_realized` を、名前付きの一つの命題に
    孤立させたもの——IUT-III 系3.12 の (ii)(iii) + Remark 3.12.2 の閉ループが
    供給すると主張される帰結の忠実算術模型版の抽出。順序は `arithVol w B` の
    もの（= `frobVol w` と defeq、B 非依存）。 -/
def ThetaLinkTransport (w : Nat → Nat) (n l B k₀ : Nat) (hw0 : w k₀ = 0) : Prop :=
  ∃ i, (arithVol w B).le (qPilotDiv n) ((unitIndAction w l k₀ hw0).image i)

/-! ## Part 2: 主定理 — 単一 Prop から入力レコードへ -/

/-- **本タスクの主構成 (M244F, capstone): crux の単一 Prop から入力へ** —
    単一命題 `ThetaLinkTransport` から、作用付き前表現 `arithPreRepInd`（M241F）
    で `MultiradialRep` を居住させ、`inputOfRep`（M215F）で `MultiradialInput`
    へ持ち上げる。IUT の正否が「入力レコードの居住」からさらに「ただ一つの
    命題 `ThetaLinkTransport` の真偽」へ縮約された、という機械検証。

    `ThetaLinkTransport` は `arithVol w B` の順序で述べられているが、
    `arithPreRepInd` が要求する `frobVol w` の順序と defeq（M238F
    `arithVol_le_frob`）であるため、そのまま crux 仮説として渡せる。 -/
theorem input_of_transport (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0)
    (h : ThetaLinkTransport w n l B k₀ hw0) :
    Nonempty (MultiradialInput (arithVol w B) (arithSkeleton w n l B hl hB)) :=
  ⟨inputOfRep (arithPreRepInd w n l B hl hB (unitIndAction w l k₀ hw0) h)⟩

/-- **順方向の閉じ (M244F): transport ⟹ input ⟹ 系3.12** —
    `input_of_transport` に `cor312_of_input`（M215F）を合成した一本道。
    単一 Prop `ThetaLinkTransport` が真であれば、忠実算術模型上で系3.12
    （−|log q| ≤ −|log Θ|）が直ちに従う。 -/
theorem cor312_of_transport (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0)
    (h : ThetaLinkTransport w n l B k₀ hw0) :
    Cor312 (arithSkeleton w n l B hl hB) :=
  cor312_of_input
    (inputOfRep (arithPreRepInd w n l B hl hB (unitIndAction w l k₀ hw0) h))

/-! ## Part 3: 逆向きの弱形（点毎 crux ⟹ transport = 前段との接続） -/

/-- **逆向きの弱形（十分条件・前段接続）**: M238F/M241F の点毎 crux hq
    （q-パイロット因子が基点像 `gaussDiv l` に点毎包含される）は
    `ThetaLinkTransport` を含意する——軌道の基点 `false`
    （`unitIndAction … .image false = gaussDiv l`）で成立するため。
    前段（arithPreRep/arithPreRepUnit）の crux が本 Prop へ確かに縮約されて
    いることの接続。**完全な逆（transport_iff_cor312 = 鏡像定理）は Dβ-7。** -/
theorem thetaLinkTransport_of_base (w : Nat → Nat) (n l B k₀ : Nat)
    (hw0 : w k₀ = 0)
    (hq : (arithVol w B).le (qPilotDiv n) (gaussDiv l)) :
    ThetaLinkTransport w n l B k₀ hw0 :=
  ⟨false, hq⟩

/-! ## Part 4: capstone（総括） -/

/-- **capstone (M244F): ThetaLinkTransport の well-defined 性** —
    (a) 縮約: 単一 Prop `ThetaLinkTransport` は `MultiradialInput` の居住を与える、
    (b) 順方向: transport ⟹ 系3.12、
    (c) 前段接続: 点毎 crux（qPilotDiv n ⊆ gaussDiv l）⟹ transport。
    crux（q_realized）が像・q-領域の実データ化・不定性の作用（軸1）を経て、
    ただ一つの名前付き命題 `ThetaLinkTransport`（軸2）に孤立したことの機械検証。
    その命題の真偽（Dβ-ω）・鏡像定理（Dβ-7）は本モジュールの範囲外。 -/
theorem thetaLinkTransport_wellDefined (w : Nat → Nat) (n l B k₀ : Nat)
    (hl : 2 ≤ l) (hB : w 1 * n < B) (hw0 : w k₀ = 0) :
    (ThetaLinkTransport w n l B k₀ hw0
        → Nonempty (MultiradialInput (arithVol w B) (arithSkeleton w n l B hl hB)))
      ∧ (ThetaLinkTransport w n l B k₀ hw0 → Cor312 (arithSkeleton w n l B hl hB))
      ∧ ((arithVol w B).le (qPilotDiv n) (gaussDiv l)
          → ThetaLinkTransport w n l B k₀ hw0) :=
  ⟨fun h => input_of_transport w n l B k₀ hl hB hw0 h,
   fun h => cor312_of_transport w n l B k₀ hl hB hw0 h,
   fun hq => thetaLinkTransport_of_base w n l B k₀ hw0 hq⟩

end IUT
