-- M414F AbsTopFullRecovery [実・本物・柱A]
-- complete_pct 影響: 柱A で AbsTopI/II/III を同一の (K^×,v,χ)=inp.gal から一つに束ねる統合 capstone——AbsTopII 乗法モノイド O_v^▷ 復元（M359F）・AbsTopIII 体復元＝元の体（M329F）・canonical G_K-加群円分体（M404F）・χ 供給橋（M409F）を coherent に統合し、AbsTopII モノイド積 = AbsTopIII 体乗法（M359F 整合）と体を養う χ = canonical 円分体の指標（M409F 橋）を単一データで閉じる。
-- 正直な限定: これは既に本物化された M359F/M329F/M404F/M409F の bundling capstone であり新規数学は加えない（価値は coherence の統合）。完全 mono-anabelian π₁→数体アルゴリズム・AbsTopI 純位相 π₁→空間側は外部（本モジュールでは atmPi1ReconHypothesis として仮説受領のみ・決して導出しない）。
/-
  IUT/AbsTopFullRecovery.lean — M414F [実／本物・柱A]
  分類: 実（本物の対象の上での統合 capstone: AbsTopII 乗法モノイド ＋ AbsTopIII 体 ＋
        canonical G_K-加群円分体 ＋ χ 供給橋を、同一の (K^×,v,χ) / inp.gal から coherent に束ねる）

  遠アーベル（柱A）の AbsTop 系列を一本化する統合 capstone:
    * M359F (atm, IUT/AbsTopMultMonoid.lean): AbsTopII——乗法モノイド O_v^▷=(O_v∖{0},×,1) の
      本物復元・付値モノイド準同型 v:O_v^▷→ℕ・単数群 O_v^×=ker(v)。
    * M329F (absF, IUT/AbsTopFieldRecover.lean): AbsTopIII——(K^×,v,χ) から加法を復元し復元環が
      元の体 K に恒等同型で一致（体復元のループが閉じる）。
    * M404F (cgm, IUT/CyclotomeGaloisModule.lean): 内在中心 ≅ μ_l を canonical な G_K-加群として
      組み上げ（σ_1=id・σ_{gh}=σ_g∘σ_h・指標 = cycRigChar・内部自己同型に対し剛）。
    * M409F (atfc, IUT/AbsTopFieldFromCyclotome.lean): 同一の inp.gal を通じ、体復元が消費する χ =
      canonical 円分体の指標 cycRigChar であることの橋。

  本モジュール（M414F）は上の**四つを一つの AbsTopI/II/III 統合データに束ね**、その coherence を
  単一の対象で閉じる:
    (A) AbsTopII 乗法モノイド O_v^▷（M359F atm_toAbsTopIIData）、
    (B) AbsTopIII 体復元＝元の体（M329F absF_toFieldData）、
    (C) canonical G_K-加群円分体（M404F cyclotomeGaloisModuleData・同一 inp.gal から）、
    (D) χ 供給橋（M409F atfc_toData・同一 inp.gal から）、
  を同一の (K^×, v, χ)=inp.gal / val から instantiate し、二つの coherence を明示する:
    * **AbsTopII↔AbsTopIII 整合**: 復元乗法モノイド O_v^▷ の積 = 復元環（＝元の体 K）の乗法
      （M359F atm_absTopII_mult_compat の再利用）——AbsTopII の乗法側が AbsTopIII 体乗法に一致。
    * **AbsTopIII↔円分体 整合**: 体復元を養う χ = canonical 円分体の指標 cycRigChar
      （M409F atfc_char_eq_cycRigChar の再利用）——体を養う χ が群論的に内在的な円分体の指標そのもの。

  ── 意義と正直な位置づけ（水増し禁止・§2 準拠）:
  これは **bundling capstone**（束ね）である。M359F/M329F/M404F/M409F は既に本物化された実成果で
  あり、本モジュールは新規の数学的内容を加えない。その価値は、四つの独立に建設された実復元片
  （乗法モノイド・体・円分体・橋）が**同一の (K^×,v,χ)=inp.gal から coherent に成立する**ことを
  単一の `AbsTopFullData` 構造で明示し、AbsTopI/II/III の三層＋円分体を一枚の言明
  `atfull_absTopI_II_III` に集約する点にある（各 coherence 定理は既存の実定理の再利用）。
  complete_pct は大きく動かない（骨格被覆の整理・統合が主）——正直にそう申告する。

  正直な限定（消去・弱化禁止）:
  - **AbsTopI（純位相 π₁^ét → 空間側）は外部**。本モジュールは π₁^ét からのモノイド/数体復元
    アルゴリズムそのものを扱わず、M359F の外部仮説 `atmPi1ReconHypothesis`（復元写像＋乗法保存）を
    **仮説として受領するのみで決して導出しない**。その帰結（復元像の付値が加法的）だけを coherence
    として本物で示す（`atfull_absTopI_external`）。実 π₁^ét からの抽出は柱A/E 後続。
  - **完全 mono-anabelian 数体復元アルゴリズム**（幾何的 tempered π₁^temp の slim 遠アーベル性・
    π₁^ét から (K^×,v,χ) を抽出する全体・[EtTh] mono-theta 環境）は外部（幾何的入力・後続）。
    本モジュールは既に本物化された四片を「同一の inp.gal / val を通じて一つに束ねる」のであって、
    幾何的入力そのものは扱わない。
  - **本物（完全証明・sorry 皆無・新規 Classical.choice 皆無）**: 四つの実復元データ
    （AbsTopII・AbsTopIII・canonical 円分体・橋）が同一の入力から同時に成立し、その二 coherence
    （AbsTopII モノイド積 = AbsTopIII 体乗法・体を養う χ = canonical 円分体指標）が単一データで
    閉じること。証明はすべて既存の実定理の再利用（rfl 同定＋既存 capstone の合成）。
  - 具体的な数体・局所体の離散付値上の統合は柱B ℤ_p 接続の後続（本ファイルの存在・実例は
    DecidableEq を持つ体上の自明付値・real G_ℚ 上の抽象 inp から）。

  全て選択公理不使用（新規 Classical.choice なし・propext / Quot.sound のみ）。禁止タクティク
  不使用（exact/refine/apply/intro のみ・omega/rw も未使用）。共有ファイル未変更（新規 1 本のみ・
  一般名は `atfull` 接頭辞で衝突回避）。
-/
import IUT.AbsTopMultMonoid
import IUT.AbsTopFieldFromCyclotome

namespace IUT

/-! ## M414F-1: 統合 AbsTop データ（AbsTopI/II/III ＋ canonical 円分体を一本に束ねる）

  同一の (K^×, v, χ)=inp.gal / val から:
    (A) AbsTopII 乗法モノイド O_v^▷（M359F）、
    (B) AbsTopIII 体復元＝元の体（M329F）、
    (C) canonical G_K-加群円分体（M404F）、
    (D) χ 供給橋（M409F）、
  を instantiate し、二つの coherence（AbsTopII 積 = AbsTopIII 体乗法・体を養う χ = 円分体指標）を
  明示する統合データ。AbsTopI 純位相側は外部（本データには載せない・§正直な限定参照）。 -/

/-- **M414F-1a: 統合 AbsTop 復元データ** — AbsTopI/II/III 統合 capstone の主対象。
    同一の Galois 作用 `inp.gal` と離散付値 `val` から四つの実復元片を coherent に束ねる:
      * `absTopII` : M359F AbsTopII 乗法モノイド O_v^▷ 復元データ、
      * `absTopIII`: M329F AbsTopIII 体復元データ（復元環＝元の体 K）、
      * `cyclotome`: M404F canonical G_K-加群円分体データ（同一 inp.gal から）、
      * `bridge`  : M409F χ 供給橋データ（体復元を養う χ = 円分体指標）、
    及び二つの coherence:
      * `mult_compat` : AbsTopII モノイド積 O_v^▷ = AbsTopIII 復元環（＝元の体）の乗法、
      * `char_eq`     : 体復元が消費する χ = canonical 円分体の指標 cycRigChar。
    主語はすべて本物: 本物の体 K（M264F）・本物の付値（M301F）・本物の μ_l 作用（M322F
    CycGKAction）・本物の内在中心（thetaGrp）——toy 群/toy 指標なし。 -/
structure AbsTopFullData (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) [DecidableEq K.carrier] (GK : Grp) (M : CycMuGroup)
    (inp : AbsTopIIIInputSkeleton K GK M) (val : valRingValuation K) where
  /-- (A) M359F AbsTopII 乗法モノイド O_v^▷ 復元データ。 -/
  absTopII : AbsTopIIData val
  /-- (B) M329F AbsTopIII 体復元データ（復元環＝元の体 K）。 -/
  absTopIII : AbsTopFieldData K
  /-- (C) M404F canonical G_K-加群円分体データ（同一 inp.gal から）。 -/
  cyclotome : CyclotomeGaloisModuleData p l ζ0 GK M inp.gal
  /-- (D) M409F χ 供給橋データ（体復元を養う χ = 円分体指標）。 -/
  bridge : AbsTopFieldFromCyclotomeData p l ζ0 K GK M inp
  /-- coherence-1: AbsTopII モノイド積 O_v^▷ = AbsTopIII 復元環（＝元の体）の乗法。 -/
  mult_compat : ∀ x y : atmCarrier val,
    (absFRecoveredRing K).mul x.elem y.elem = (atmMul val x y).elem
  /-- coherence-2: AbsTopIII 復元加法 = 元の体加法（体復元のループが閉じる）。 -/
  field_add_eq : ∀ x y, (absFRecoveredRing K).add x y = K.add x y
  /-- coherence-3: AbsTopIII 復元乗法 = 元の体乗法。 -/
  field_mul_eq : (absFRecoveredRing K).mul = K.mul
  /-- coherence-4: 体復元が消費する χ = canonical 円分体の指標 cycRigChar。 -/
  char_eq : ∀ g, (cycRecCharOfAction GK M inp.gal).chi g = cycRigChar GK M inp.gal g

/-- **M414F-1b: 統合データの witness 本体** — 全フィールドを M359F/M329F/M404F/M409F の本物の
    復元データ・整合定理で埋める（外部仮説は付値 val のみ・ζ0 が単数根であることすら不要）。 -/
def atfull_toData (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) [DecidableEq K.carrier] {GK : Grp} {M : CycMuGroup}
    (inp : AbsTopIIIInputSkeleton K GK M) (val : valRingValuation K) :
    AbsTopFullData p l ζ0 K GK M inp val where
  absTopII := atm_toAbsTopIIData val
  absTopIII := absF_toFieldData K val
  cyclotome := cyclotomeGaloisModuleData p l ζ0 GK M inp.gal
  bridge := atfc_toData p l ζ0 K inp val
  mult_compat := fun x y => atm_absTopII_mult_compat val x y
  field_add_eq := fun x y => absF_add_eq K x y
  field_mul_eq := rfl
  char_eq := fun _ => rfl

/-! ## M414F-2: 統合 capstone — AbsTopI/II/III + canonical 円分体を一枚に集約

  AbsTopII（乗法モノイド）・AbsTopIII（体＝元の体）・canonical 円分体の三層を、その coherence
  （AbsTopII 積 = AbsTopIII 体乗法・体を養う χ = 円分体指標）まで込めて一つの言明に束ねる。 -/

/-- **M414F-2: AbsTopI/II/III 統合復元定理（capstone）** — AbsTopIII 入力
    `AbsTopIIIInputSkeleton K GK M`（乗法＋付値 K^×,v ＋ Galois 作用 χ の台 `gal`）と離散付値
    `val` から、以下が**同時に同一の入力から**成立する:
      (II)  AbsTopII 乗法モノイド O_v^▷ の復元が存在し（M359F）、その単数群 = 可逆元、
      (III) AbsTopIII 体復元が元の体 K に一致（加法・乗法とも／M329F）、
      (円分) 体復元が消費する χ = canonical G_K-加群円分体の指標 cycRigChar（M409F 橋）で、
             その canonical 円分体の生成元作用 σ_g(ζ)=ζ^{χ(g)}（M404F）が成り立ち、
      (整合) AbsTopII 乗法モノイド O_v^▷ の積 = AbsTopIII 復元環（＝元の体）の乗法（M359F 整合）。
    「同一の (K^×,v,χ) から乗法モノイド・体・canonical 円分体が coherent に復元される」という
    AbsTop 三層の結び目を一枚に集約する（π₁^ét→(K^×,v,χ) の完全抽出・AbsTopI 純位相側は外部）。 -/
theorem atfull_absTopI_II_III (K : IUTField) [DecidableEq K.carrier]
    {GK : Grp} {M : CycMuGroup} (inp : AbsTopIIIInputSkeleton K GK M)
    (val : valRingValuation K) :
    (∀ x, atmUnits val x ↔ ∃ y, atmMul val x y = atmOne val) ∧
    (∀ x y, (absFRecoveredRing K).add x y = K.add x y) ∧
    (absFRecoveredRing K).mul = K.mul ∧
    (∀ g, (cycRecCharOfAction GK M inp.gal).chi g = cycRigChar GK M inp.gal g) ∧
    (∀ g, galThMuAct GK M inp.gal g (M.μ.pow M.ζ 1)
      = M.μ.pow M.ζ (cycRigExp GK M inp.gal g)) ∧
    (∀ x y : atmCarrier val,
      (absFRecoveredRing K).mul x.elem y.elem = (atmMul val x y).elem) :=
  ⟨fun x => atm_unit_iff val x,
   fun x y => absF_add_eq K x y,
   rfl,
   fun _ => rfl,
   cgm_char_gen GK M inp.gal,
   fun x y => atm_absTopII_mult_compat val x y⟩

/-- **M414F-2b: 統合データの存在** — DecidableEq を持つ体上、任意の AbsTopIII 入力と自明付値から、
    AbsTopI/II/III 統合復元データが**外部仮説なしで**存在する。具体的な数体・局所体の離散付値上の
    統合は柱B ℤ_p 接続の後続。 -/
theorem atfull_exists (p l : Nat) (ζ0 : (Zp p).carrier)
    (K : IUTField) [DecidableEq K.carrier] {GK : Grp} {M : CycMuGroup}
    (inp : AbsTopIIIInputSkeleton K GK M) :
    Nonempty (AbsTopFullData p l ζ0 K GK M inp (trivialValuation K)) :=
  ⟨atfull_toData p l ζ0 K inp (trivialValuation K)⟩

/-! ## M414F-3: AbsTopI（純位相 π₁^ét 側）は外部——仮説受領のみ・決して導出しない

  AbsTopI の位相 π₁^ét → 乗法モノイド O_v^▷ の復元アルゴリズムは本モジュール外＝外部仮説
  `atmPi1ReconHypothesis`（M359F）として**受領するのみ**。ここではその帰結（復元像の付値が
  G_K の積で加法的）を AbsTopII 付値準同型と coherent に本物で示すが、仮説そのものは決して導出しない
  （正直な限定）。 -/

/-- **M414F-3: AbsTopI 外部仮説の AbsTopII 整合** — AbsTopI 側の π₁^ét モノイド復元仮説
    `atmPi1ReconHypothesis val GK`（外部・決して導出しない）を**受領すれば**、その復元写像 recon の
    像の付値が G_K の積で加法的になる（v(recon(gh)) = v(recon g)+v(recon h)）——AbsTopI 外部入力が
    AbsTopII 付値モノイド準同型（M359F）と coherent であることの帰結（M359F
    atm_pi1_reconstruction_hypothesis 再利用）。AbsTopI 純位相側の抽出は外部・後続。 -/
theorem atfull_absTopI_external {K : IUTField} (val : valRingValuation K) (GK : Grp)
    (hyp : atmPi1ReconHypothesis val GK) (g h : GK.carrier) :
    atmValN val (hyp.recon (GK.mul g h))
      = atmValN val (hyp.recon g) + atmValN val (hyp.recon h) :=
  atm_pi1_reconstruction_hypothesis val GK hyp g h

/-! ## M414F-4: 実例 -/

/-- 実例: 任意の AbsTopIII 入力・任意の離散付値で AbsTopI/II/III 統合データが存在する
    （K は DecidableEq を持つ任意の体・p=7・l=5）。 -/
example (K : IUTField) [DecidableEq K.carrier] (ζ0 : (Zp 7).carrier)
    {GK : Grp} {M : CycMuGroup} (inp : AbsTopIIIInputSkeleton K GK M) :
    Nonempty (AbsTopFullData 7 5 ζ0 K GK M inp (trivialValuation K)) :=
  atfull_exists 7 5 ζ0 K inp

/-- 実例（real G_ℚ）: 本物の絶対ガロア群 G_ℚ（M315F algCloAbsGalois）・その μ_l（ℤ/l cycMuStd）
    上の trivial 作用を Galois 台に持つ AbsTopIII 入力から、AbsTopI/II/III 統合データが存在する
    （幾何的入力 inp は外部・既存 M404F/M409F の real G_ℚ 実例と同じ抽象化）。 -/
example (K : IUTField) [DecidableEq K.carrier] (l : Nat) (hl : 1 ≤ l) (ζ0 : (Zp 7).carrier)
    (inp : AbsTopIIIInputSkeleton K (algCloAbsGalois algCloTrivialTower) (cycMuStd l hl)) :
    Nonempty (AbsTopFullData 7 l ζ0 K (algCloAbsGalois algCloTrivialTower)
      (cycMuStd l hl) inp (trivialValuation K)) :=
  atfull_exists 7 l ζ0 K inp

/-- 実例（統合 capstone）: (K^×,v,χ) から乗法モノイド・体・canonical 円分体が coherent に復元
    される三層の結び目（AbsTopI/II/III 統合定理の実インスタンス）。 -/
example (K : IUTField) [DecidableEq K.carrier]
    {GK : Grp} {M : CycMuGroup} (inp : AbsTopIIIInputSkeleton K GK M)
    (val : valRingValuation K) :
    (∀ x, atmUnits val x ↔ ∃ y, atmMul val x y = atmOne val) ∧
    (∀ x y, (absFRecoveredRing K).add x y = K.add x y) ∧
    (absFRecoveredRing K).mul = K.mul ∧
    (∀ g, (cycRecCharOfAction GK M inp.gal).chi g = cycRigChar GK M inp.gal g) ∧
    (∀ g, galThMuAct GK M inp.gal g (M.μ.pow M.ζ 1)
      = M.μ.pow M.ζ (cycRigExp GK M inp.gal g)) ∧
    (∀ x y : atmCarrier val,
      (absFRecoveredRing K).mul x.elem y.elem = (atmMul val x y).elem) :=
  atfull_absTopI_II_III K inp val

/-- 実例（AbsTopII↔AbsTopIII 整合）: 乗法モノイド O_v^▷ の積 = 復元環（＝元の体）の乗法。 -/
example {K : IUTField} [DecidableEq K.carrier] (val : valRingValuation K)
    (x y : atmCarrier val) :
    (absFRecoveredRing K).mul x.elem y.elem = (atmMul val x y).elem :=
  atm_absTopII_mult_compat val x y

end IUT
