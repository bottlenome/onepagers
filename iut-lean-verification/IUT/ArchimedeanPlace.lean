/-
  IUT/ArchimedeanPlace.lean — M69F（アルキメデス素点と可除性の構造的二分法）の形式化

  ## 動機

  数体の素点には非アルキメデス（有限）素点とアルキメデス（無限）素点の
  二種類がある。[FrdI] の Frobenioid 理論では、有限素点の局所因子モノイドは
  離散な ℕ（付値の重複度）だが、**アルキメデス素点の局所因子モノイドは
  連続的（可除）**である: 無限素点での「因子」は log-volume 型の非負実数値
  であり、任意の n ≥ 1 で n 等分できる。Frobenioid 系譜（M48F/M51F/M55F/
  M57F/M59F〜M67F）が一貫して「アルキメデス素点は未形式化」と申告してきた
  最後の未達項目がこれである。

  本モジュールの核は**可除性の構造的二分法**の機械検証である:

  * **有限素点のファイバー**（M57F の localFrobenioid、対象 = ℕ）は
    生まれつき不可除 — 重複度 1 の対象への次数 2 の純 Frobenius 射は
    存在しない（2m = 1 の ℕ での矛盾）。
  * **アルキメデス素点のファイバー**（本モジュールの archFrobenioid、
    対象 = M67F の ℚ≥0 = NNQ）は生まれつき可除 — 任意の対象 q と
    任意の n ≥ 1 に対し「q の 1/n」対象と次数 n の純 Frobenius 射が
    実在する（witness は M67F の nnqDiv の明示構成）。
  * **実化は有限素点をアルキメデス素点に近づける操作** — 有限素点の
    局所圏は埋め込み関手 localArchFunctor（ι : ℕ → ℚ≥0 による係数拡張 =
    一素点版の実化）でアルキメデス局所圏に埋まり、埋め込んだ途端に
    それまで不可能だった n 等分が可能になる。M67F の realFrobenioid
    （大域・全素点同時の実化）の局所版であり、「アルキメデスファイバーは
    生まれつき可除・有限ファイバーは実化して初めて可除」という対比が
    両側の実定理として機械検証される。

  さらに [FrdI] の数体の Frobenioid に倣い、**有限・無限混合の因子**
  MixedDiv（有限部 = M51F の QDiv（整係数）・無限部 = NNQ 係数の
  有限サポート関数）とその次数・圏 mixedFrobenioid を建設し、総括定理
  `mixed_divisibility_dichotomy` — **混合因子が n 等分できる ⟺ 有限部が
  n 等分できる**（アルキメデス部は常に等分可能なので、可除性の障害は
  有限部だけ）— を両向きの明示構成で検証する。

  ## 検証する定理（全て sorry なし・選択公理なし）

  ### Part 1: アルキメデス局所 Frobenioid（M69F-1）
  * `ArchHom` / `archFrobenioid` — 対象 = NNQ（無限素点での log-volume 値）、
    射 q → q' = (d ≥ 1, c : NNQ) with q' = d·q + c。圏公理完全証明
    （恒等 (1, 0)・合成 (d₁d₂, d₂·c₁ + c₂)。M51F の div_comp_linear の
    NNQ 版 `arch_comp_linear`）

  ### Part 2: 可除性の構造的二分法（本丸、M69F-2）
  * `arch_divisible` — アルキメデスファイバーは生まれつき可除:
    ∀ q n ≥ 1, ∃ q', n·q' = q（witness = M67F の nnqDiv、choice-free）
  * `arch_pilot_division` — 圏レベルの等分: 任意の対象 q と n ≥ 1 に
    「q の 1/n」対象と次数 n の純 Frobenius 射 q/n → q が実在
  * `nonarch_pilot_obstruction` — 非アルキメデス局所圏（M57F の
    localFrobenioid）では重複度 1 の対象への次数 2 の純 Frobenius 射
    (2, 0) : m → 1 が存在しない（2m = 1 の ℕ での矛盾。M67F の
    qdiv_not_divisible の局所一素点版）
  * `arch_vs_nonarch` — **対比定理**: 上の両側を一つの命題に束ねた
    構造的二分法の機械検証
  * `localArchFunctor` / `local_realification_gains_divisibility` —
    **「実化は有限素点をアルキメデス素点に近づける操作」**: 有限素点の
    局所圏のアルキメデス局所圏への埋め込み関手（関手性完全証明）と、
    埋め込んだ像が常に可除になること（不可除だった対象 1 の像も含む）

  ### Part 3: 混合因子モノイド（M69F-3）
  * `MixedDiv` / `mixedAdd` / `mixedZero` / `mixedFrob` — 有限部
    （QDiv、整係数）と無限部（NNQ 係数・サポート上界つき）の対の
    モノイド法則（`mixedAdd_assoc` / `mixedAdd_comm` / `mixedZero_add` /
    `mixedAdd_zero`）と Frobenius 法則（`mixedFrob_add` / `mixedFrob_frob`）

  ### Part 4: 混合次数（M69F-4）
  * `degMixed` — 有限部の整次数（M51F の degN）の ι 像と無限部の
    NNQ 値重み付き和（M67F の nnqSum）の和。加法性 `degMixed_add`・
    Frobenius 斉次性 `degMixed_frob`

  ### Part 5: 混合圏と二分法の総括（M69F-5）
  * `mixedFrobenioid` — 対象 = MixedDiv、射 = (d ≥ 1, c) with
    y = φ_d(x) + c の圏公理完全証明
  * `mixed_iso_d_one` / `mixed_iso_c_zero` / `mixed_iso_objects_eq` /
    `mixed_gaunt_isoUnique` — 剛性: 同型は (d, c) = (1, 0) を強制され
    対象を動かせない（fin 部・arch 部とも bound 簿記）。可除な
    アルキメデス部を足しても Frobenius-like 剛性は壊れない
  * `mixed_divisibility_dichotomy` — **総括定理**: 混合因子 x が
    n 等分可能 ⟺ 有限部が n 等分可能（⟸ は witness 合成（arch 部は
    nnqDiv で常に割れる）、⟹ は fin 部の射影）
  * `mixed_pilot_division` / `mixed_fin_zero_divisible` /
    `mixed_single_not_divisible` — 具体的発動: 有限部が割れれば圏レベルの
    純 Frobenius 等分射が実在・fin 部 = 0 の混合因子（純アルキメデス因子）は
    常に可除・fin 部 = singleDiv 0 1 の混合因子は 2 等分不能

  ## 正直な申告（モデルと本物の差）

  * **NNQ は ℝ≥0 でなく ℚ≥0**: 本物のアルキメデス局所因子モノイドは
    ℝ≥0（order-complete）だが、本モジュールは M67F の ℚ≥0 で代用した。
    機械検証する本質（可除性）には ℚ≥0 で十分だが、上限の存在・連続性は
    形式化されていない。
  * **「アルキメデス」は構造的性質のモデル化**: 本モジュールの
    「アルキメデス素点」は「局所因子モノイドが可除」という [FrdI] の
    構造的特徴のみを実装したもので、絶対値・距離・完備化・複素埋め込み
    といった解析的実体は一切形式化していない。実素点と複素素点の区別も
    ない（無限素点は添字 k : ℕ のタグのみ）。
  * **順序構造なし**: NNQ 上の ≤ は定義しておらず、[FrdI] §2 の
    アルキメデス Frobenioid の角度成分（位相群 S¹）や上限による特徴付けは
    扱わない。
  * **サポート上界はデータ**: MixedDiv の無限部も QDiv / RDiv と同様、
    choice 回避のためサポート上界をデータとして持つ（M51F 以来の表示の
    自由度の正直な申告: 成分が同じで bound が違う MixedDiv は別対象）。
  * **混合圏の base は一点**: mixedFrobenioid は有限・無限の全素点の
    因子を一つの対象に束ねた base 一点の圏であり、素点の base 圏上の
    ファイバー構造（M57F）との合成は未形式化。
  * 選択公理・追加公理は不使用（全定理 propext / Quot.sound 以下、
    `#print axioms` で実測済み。∃ の witness は全て明示構成）。
-/
import IUT.Realification
import IUT.FiberedFrobenioid

namespace IUT

/-! ## Part 1: アルキメデス局所 Frobenioid（M69F-1）

    一つのアルキメデス素点の上の局所圏。対象はその素点での「log-volume」値
    q : NNQ（M67F の ℚ≥0）、射は Frobenius 次数と効果的因子部分の対。
    M57F の localFrobenioid（対象 ℕ）の係数を ℕ → ℚ≥0 に置き換えた形で、
    この置き換えこそが可除性（Part 2）の源泉である。 -/

/-- **アルキメデス局所 Frobenioid の射**: q → q' は Frobenius 次数 d ≥ 1 と
    効果的因子部分 c : NNQ の対で、線形条件 q' = d·q + c を満たすもの
    （M57F の LocalHom の NNQ 係数版）。 -/
structure ArchHom (q q' : NNQ) where
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的因子部分（その無限素点での log-volume の増分）。 -/
  c : NNQ
  d_pos : 1 ≤ d
  /-- 線形条件: q' = d·q + c。 -/
  linear : q' = nnqAdd (nnqSmul d q) c

/-- 射の外延性: ArchHom は (d, c) 成分で決まる（linear は Prop）。 -/
theorem ArchHom.ext {q q' : NNQ} {f g : ArchHom q q'}
    (hd : f.d = g.d) (hc : f.c = g.c) : f = g := by
  cases f with | mk fd fc f1 f2 =>
  cases g with | mk gd gc g1 g2 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  subst hd'
  subst hc'
  rfl

/-- 恒等射の線形条件: q = 1·q + 0。 -/
theorem arch_id_linear (q : NNQ) : q = nnqAdd (nnqSmul 1 q) nnqZero := by
  rw [nnqSmul_one, nnqAdd_zero]

/-- 合成射の線形条件: q₂ = a·q₁ + c₁, q₃ = b·q₂ + c₂ なら
    q₃ = (ab)·q₁ + (b·c₁ + c₂)。捻れ半直積型合成則の NNQ 版で、
    算術核は nnqSmul_add（分配）・nnqSmul_smul（作用）・nnqAdd_assoc
    （結合）という M67F の ℚ≥0 構造定理（M51F の div_comp_linear と
    同じ三段 rw）。 -/
theorem arch_comp_linear {a b : Nat} {q₁ q₂ q₃ c₁ c₂ : NNQ}
    (h₁ : q₂ = nnqAdd (nnqSmul a q₁) c₁)
    (h₂ : q₃ = nnqAdd (nnqSmul b q₂) c₂) :
    q₃ = nnqAdd (nnqSmul (a * b) q₁) (nnqAdd (nnqSmul b c₁) c₂) := by
  rw [h₂, h₁, nnqSmul_add, nnqSmul_smul, nnqAdd_assoc]

/-- **定理 (M69F-1): アルキメデス局所 Frobenioid 圏** — 対象 = NNQ
    （その無限素点での log-volume 値）、射 = (d ≥ 1, c) with
    q' = d·q + c。恒等 (1, 0)、合成 (d₁,c₁)·(d₂,c₂) = (d₁d₂, d₂·c₁+c₂)。
    圏公理は ℚ≥0 の可換モノイド + スカラー法則（M67F-1）から完全証明。
    [FrdI] のアルキメデス Frobenioid の「局所因子モノイドが可除モノイド」
    という構造的特徴の実装（解析的実体なし: 正直な申告参照）。 -/
def archFrobenioid : Cat where
  Obj := NNQ
  Hom := ArchHom
  id := fun q => ⟨1, nnqZero, Nat.le_refl 1, arch_id_linear q⟩
  comp := fun f g =>
    ⟨f.d * g.d, nnqAdd (nnqSmul g.d f.c) g.c,
      Nat.mul_pos f.d_pos g.d_pos,
      arch_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    ArchHom.ext (Nat.one_mul f.d)
      (by show nnqAdd (nnqSmul f.d nnqZero) f.c = f.c
          rw [nnqSmul_zero, nnqZero_add])
  comp_id := fun f =>
    ArchHom.ext (Nat.mul_one f.d)
      (by show nnqAdd (nnqSmul 1 f.c) nnqZero = f.c
          rw [nnqSmul_one, nnqAdd_zero])
  assoc := fun f g h =>
    ArchHom.ext (Nat.mul_assoc f.d g.d h.d)
      (by show nnqAdd (nnqSmul h.d (nnqAdd (nnqSmul g.d f.c) g.c)) h.c
            = nnqAdd (nnqSmul (g.d * h.d) f.c)
                (nnqAdd (nnqSmul h.d g.c) h.c)
          rw [nnqSmul_add, nnqSmul_smul, nnqAdd_assoc])

/-- 圏の中の純 Frobenius 射 q → e·q（次数 e、因子部分 0）。 -/
def archFrobMor (e : Nat) (he : 1 ≤ e) (q : NNQ) :
    ArchHom q (nnqSmul e q) :=
  ⟨e, nnqZero, he, (nnqAdd_zero (nnqSmul e q)).symm⟩

/-! ## Part 2: 可除性の構造的二分法（本丸、M69F-2）

    アルキメデスファイバーは生まれつき可除・有限ファイバーは不可除。
    そして実化（係数の ι : ℕ → ℚ≥0 拡張）が後者を前者に変える。 -/

/-- **定理 (M69F-2a): アルキメデスファイバーは生まれつき可除** —
    任意の q : NNQ と n ≥ 1 に対し n·q' = q なる q' が存在する
    （witness は M67F の nnqDiv の明示構成: 選択公理不使用）。
    M67F の rdiv_divisible が実化で**獲得した**可除性を、アルキメデス
    ファイバーは座標環の段階で最初から持っている。 -/
theorem arch_divisible (q : NNQ) (n : Nat) (hn : 1 ≤ n) :
    ∃ q' : NNQ, nnqSmul n q' = q :=
  ⟨nnqDiv q n hn, nnq_div_cancel q n hn⟩

/-- **定理 (M69F-2b): 圏レベルの等分（アルキメデス・パイロット等分）** —
    archFrobenioid では任意の対象 q と任意の n ≥ 1 に対し、
    「q の 1/n」にあたる対象 q'（n·q' = q）と次数 n の純 Frobenius 射
    (n, 0) : q' → q が実在する（M67F の real_pilot_division の局所版）。 -/
theorem arch_pilot_division (q : NNQ) (n : Nat) (hn : 1 ≤ n) :
    ∃ q' : NNQ, nnqSmul n q' = q ∧ Nonempty (ArchHom q' q) := by
  refine ⟨nnqDiv q n hn, nnq_div_cancel q n hn, ⟨⟨n, nnqZero, hn, ?_⟩⟩⟩
  rw [nnq_div_cancel q n hn, nnqAdd_zero]

/-- **定理 (M69F-2c): 非アルキメデスファイバーの不可除性** —
    有限素点の局所圏（M57F の localFrobenioid、対象 = 重複度 ℕ）では、
    重複度 1 の対象への次数 2 の純 Frobenius 射 (2, 0) : m → 1 が
    どの m からも存在しない（線形条件 1 = 2m + 0 の ℕ での矛盾。
    M67F の qdiv_not_divisible の局所一素点版を自前で検証）。 -/
theorem nonarch_pilot_obstruction (m : Nat) :
    ¬ ∃ f : LocalHom m 1, f.d = 2 ∧ f.c = 0 := by
  intro hex
  cases hex with
  | intro f hf =>
    have h : 1 = f.d * m + f.c := f.linear
    rw [hf.1, hf.2] at h
    omega

/-- アルキメデス側の存在（対比用の片割れ）: ι(1) への次数 n の
    純 Frobenius 射が常に存在する（witness は nnqDiv (ι 1) n）。 -/
theorem arch_pilot_exists (n : Nat) (hn : 1 ≤ n) :
    ∃ (q' : NNQ) (f : ArchHom q' (nnqOfNat 1)),
      f.d = n ∧ f.c = nnqZero := by
  refine ⟨nnqDiv (nnqOfNat 1) n hn, ⟨n, nnqZero, hn, ?_⟩, rfl, rfl⟩
  rw [nnq_div_cancel (nnqOfNat 1) n hn, nnqAdd_zero]

/-- **定理 (M69F-2d): 可除性の構造的二分法（対比定理）** —
    (i) 非アルキメデス局所圏では重複度 1 の対象への次数 2 の
    純 Frobenius 射がどの対象からも存在しない。
    (ii) アルキメデス局所圏では ι(1) への次数 n の純 Frobenius 射が
    任意の n ≥ 1 で存在する。
    有限素点と無限素点の局所構造の違い（離散 ℕ vs 可除 ℚ≥0）が
    圏レベルの実定理の対として機械検証される。 -/
theorem arch_vs_nonarch :
    (∀ m : Nat, ¬ ∃ f : LocalHom m 1, f.d = 2 ∧ f.c = 0)
      ∧ (∀ n : Nat, 1 ≤ n →
          ∃ (q' : NNQ) (f : ArchHom q' (nnqOfNat 1)),
            f.d = n ∧ f.c = nnqZero) :=
  ⟨nonarch_pilot_obstruction, fun n hn => arch_pilot_exists n hn⟩

/-- **定理 (M69F-2e): 局所実化関手** — 有限素点の局所圏のアルキメデス
    局所圏への埋め込み: m ↦ ι m、(d, c) ↦ (d, ι c)。線形条件の保存は
    ι の加法性（nnqOfNat_add）とスカラー両立（nnqSmul_ofNat）。
    M67F の realifyFunctor（大域・全素点同時）の一素点版であり、
    係数拡張 ℕ ⊆ ℚ≥0 が「実化」のファイバーレベルの内容である。 -/
def localArchFunctor : Functor localFrobenioid archFrobenioid where
  onObj := fun m => nnqOfNat m
  onHom := fun {m m'} f =>
    { d := f.d
      c := nnqOfNat f.c
      d_pos := f.d_pos
      linear := by
        have h := congrArg nnqOfNat f.linear
        rw [nnqOfNat_add, ← nnqSmul_ofNat] at h
        exact h }
  map_id := fun _ => ArchHom.ext rfl nnqOfNat_zero
  map_comp := fun f g =>
    ArchHom.ext rfl
      (by show nnqOfNat (g.d * f.c + g.c)
            = nnqAdd (nnqSmul g.d (nnqOfNat f.c)) (nnqOfNat g.c)
          rw [nnqOfNat_add, nnqSmul_ofNat])

/-- **定理 (M69F-2f): 「実化は有限素点をアルキメデス素点に近づける操作」**
    — 有限素点の局所対象 m はアルキメデス局所圏に埋め込んだ途端に
    任意の n ≥ 1 で n 等分可能になる（不可除の証人だった対象 1
    （nonarch_pilot_obstruction）の像 ι(1) も含む）。M67F の
    realification_gains_divisibility（大域版）の局所ファイバー版:
    アルキメデスファイバーが生まれつき持つ可除性を、有限ファイバーは
    実化（= localArchFunctor による係数拡張）で初めて獲得する。 -/
theorem local_realification_gains_divisibility :
    (∀ (m n : Nat), 1 ≤ n →
        ∃ q' : NNQ, nnqSmul n q' = localArchFunctor.onObj m)
      ∧ (∀ m : Nat, ¬ ∃ f : LocalHom m 1, f.d = 2 ∧ f.c = 0)
      ∧ (∃ q' : NNQ, nnqSmul 2 q' = localArchFunctor.onObj (1 : Nat)) :=
  ⟨fun m n hn => arch_divisible (nnqOfNat m) n hn,
   nonarch_pilot_obstruction,
   arch_divisible (nnqOfNat 1) 2 (by omega)⟩

/-! ## Part 3: 混合因子モノイド（M69F-3）

    数体の因子 = 有限素点部分（整係数、M51F の QDiv）⊕ 無限素点部分
    （ℚ≥0 係数の有限サポート関数）。[FrdI] の数体の Frobenioid の
    因子モノイド Φ = ⊕_{v fin} ℕ ⊕ ⊕_{v arch} ℝ≥0 の（ℝ≥0 を ℚ≥0 で
    代用した）実装。 -/

/-- **混合因子**: 有限素点部分（整係数重複度、M51F の QDiv）と
    無限素点部分（NNQ 値 log-volume、添字 k : ℕ・サポート上界つき）の対。
    サポート上界はデータとして持つ（choice 回避、M51F 以来の規約）。 -/
structure MixedDiv where
  /-- 有限素点部分（整係数の有効因子）。 -/
  fin : QDiv
  /-- k 番目の無限素点での ℚ≥0 値 log-volume。 -/
  arch : Nat → NNQ
  /-- 無限部のサポート上界。 -/
  archBound : Nat
  /-- 無限部の有限サポート性。 -/
  archVanish : ∀ k, archBound ≤ k → arch k = nnqZero

/-- 混合因子の外延性（archVanish は Prop）。 -/
theorem MixedDiv.ext {x y : MixedDiv} (hf : x.fin = y.fin)
    (ha : x.arch = y.arch) (hb : x.archBound = y.archBound) : x = y := by
  cases x with | mk xf xa xb xv =>
  cases y with | mk yf ya yb yv =>
  have hf' : xf = yf := hf
  have ha' : xa = ya := ha
  have hb' : xb = yb := hb
  subst hf'
  subst ha'
  subst hb'
  rfl

/-- 自明混合因子 0。 -/
def mixedZero : MixedDiv where
  fin := qzero
  arch := fun _ => nnqZero
  archBound := 0
  archVanish := fun _ _ => rfl

/-- 混合因子の和（有限部は QDiv の和、無限部は点ごとの ℚ≥0 加法）。 -/
def mixedAdd (x y : MixedDiv) : MixedDiv where
  fin := qadd x.fin y.fin
  arch := fun k => nnqAdd (x.arch k) (y.arch k)
  archBound := max x.archBound y.archBound
  archVanish := fun k hk => by
    rw [x.archVanish k (Nat.le_trans (Nat.le_max_left _ _) hk),
      y.archVanish k (Nat.le_trans (Nat.le_max_right _ _) hk)]
    exact nnqAdd_zero nnqZero

/-- 混合 Frobenius φ_e: 有限部・無限部の同時 e 倍。 -/
def mixedFrob (e : Nat) (x : MixedDiv) : MixedDiv where
  fin := qfrob e x.fin
  arch := fun k => nnqSmul e (x.arch k)
  archBound := x.archBound
  archVanish := fun k hk => by
    rw [x.archVanish k hk]
    exact nnqSmul_zero e

/-- **定理 (M69F-3a): 混合因子和の結合律**。 -/
theorem mixedAdd_assoc (x y z : MixedDiv) :
    mixedAdd (mixedAdd x y) z = mixedAdd x (mixedAdd y z) :=
  MixedDiv.ext (qadd_assoc x.fin y.fin z.fin)
    (funext fun k => nnqAdd_assoc (x.arch k) (y.arch k) (z.arch k))
    (nat_max_assoc x.archBound y.archBound z.archBound)

/-- **定理 (M69F-3b): 混合因子和の可換律**。 -/
theorem mixedAdd_comm (x y : MixedDiv) : mixedAdd x y = mixedAdd y x :=
  MixedDiv.ext (qadd_comm x.fin y.fin)
    (funext fun k => nnqAdd_comm (x.arch k) (y.arch k))
    (nat_max_comm x.archBound y.archBound)

/-- **定理 (M69F-3c): 左単位則** 0 + x = x。 -/
theorem mixedZero_add (x : MixedDiv) : mixedAdd mixedZero x = x :=
  MixedDiv.ext (qzero_add x.fin)
    (funext fun k => nnqZero_add (x.arch k))
    (nat_zero_max x.archBound)

/-- **定理 (M69F-3c'): 右単位則** x + 0 = x。 -/
theorem mixedAdd_zero (x : MixedDiv) : mixedAdd x mixedZero = x :=
  MixedDiv.ext (qadd_zero x.fin)
    (funext fun k => nnqAdd_zero (x.arch k))
    (nat_max_zero x.archBound)

/-- φ_1 は恒等。 -/
theorem mixedFrob_one (x : MixedDiv) : mixedFrob 1 x = x :=
  MixedDiv.ext (qfrob_one x.fin)
    (funext fun k => nnqSmul_one (x.arch k)) rfl

/-- φ_e は自明混合因子を固定する。 -/
theorem mixedFrob_zero (e : Nat) : mixedFrob e mixedZero = mixedZero :=
  MixedDiv.ext (qfrob_zero e) (funext fun _ => nnqSmul_zero e) rfl

/-- **Frobenius の加法分配**: φ_e(x + y) = φ_e(x) + φ_e(y)。 -/
theorem mixedFrob_add (e : Nat) (x y : MixedDiv) :
    mixedFrob e (mixedAdd x y) = mixedAdd (mixedFrob e x) (mixedFrob e y) :=
  MixedDiv.ext (qfrob_add e x.fin y.fin)
    (funext fun k => nnqSmul_add e (x.arch k) (y.arch k)) rfl

/-- **Frobenius の合成**: φ_{e₂}(φ_{e₁}(x)) = φ_{e₁e₂}(x)。 -/
theorem mixedFrob_frob (e₁ e₂ : Nat) (x : MixedDiv) :
    mixedFrob e₂ (mixedFrob e₁ x) = mixedFrob (e₁ * e₂) x :=
  MixedDiv.ext (qfrob_frob e₁ e₂ x.fin)
    (funext fun k => nnqSmul_smul e₁ e₂ (x.arch k)) rfl

/-! ## Part 4: 混合次数（M69F-4）

    数体の次数 deg = Σ_{v fin} w(v)·ord_v + Σ_{v arch} w(v)·logvol_v。
    有限部の整次数（M51F の degN）を ι で ℚ≥0 に持ち上げ、無限部の
    NNQ 値重み付き和（M67F の nnqSum）と足す。 -/

/-- 混合因子の無限部の重み付き次数（NNQ 値）。 -/
def archDeg (w : Nat → Nat) (x : MixedDiv) : NNQ :=
  nnqSum (fun k => nnqSmul (w k) (x.arch k)) x.archBound

/-- 無限部次数の安定性: サポート上界を超えて和を取っても変わらない。 -/
theorem archDeg_stable (w : Nat → Nat) (x : MixedDiv) (n : Nat)
    (hn : x.archBound ≤ n) :
    nnqSum (fun k => nnqSmul (w k) (x.arch k)) n = archDeg w x :=
  nnqSum_tail (fun k => nnqSmul (w k) (x.arch k)) x.archBound n hn
    (fun k hk => by
      show nnqSmul (w k) (x.arch k) = nnqZero
      rw [x.archVanish k hk]
      exact nnqSmul_zero (w k))

/-- **混合次数**（ℚ≥0 値）: deg(x) = ι(deg_N^{fin}(x.fin)) +
    Σ_{k<archBound} w_arch(k)·arch(k)。重み w_fin / w_arch はそれぞれ
    有限素点・無限素点の log-volume 正規化（M51F と同じ抽象化）。 -/
def degMixed (wfin warch : Nat → Nat) (x : MixedDiv) : NNQ :=
  nnqAdd (nnqOfNat (degN wfin x.fin)) (archDeg warch x)

/-- 自明混合因子の次数は 0。 -/
theorem degMixed_zero (wfin warch : Nat → Nat) :
    degMixed wfin warch mixedZero = nnqZero := by
  show nnqAdd nnqZero nnqZero = nnqZero
  exact nnqAdd_zero nnqZero

/-- **定理 (M69F-4a): 混合次数の加法性** deg(x+y) = deg x + deg y。
    有限部は M51F の degN_add + ι の加法性、無限部は M67F の
    nnqSum_add + 安定性、最後に和の入れ替え nnqAdd_shuffle。 -/
theorem degMixed_add (wfin warch : Nat → Nat) (x y : MixedDiv) :
    degMixed wfin warch (mixedAdd x y)
      = nnqAdd (degMixed wfin warch x) (degMixed wfin warch y) := by
  show nnqAdd (nnqOfNat (degN wfin (qadd x.fin y.fin)))
      (nnqSum (fun k => nnqSmul (warch k) (nnqAdd (x.arch k) (y.arch k)))
        (max x.archBound y.archBound))
    = nnqAdd (degMixed wfin warch x) (degMixed wfin warch y)
  have hpt : (fun k => nnqSmul (warch k) (nnqAdd (x.arch k) (y.arch k)))
      = fun k => nnqAdd (nnqSmul (warch k) (x.arch k))
          (nnqSmul (warch k) (y.arch k)) :=
    funext fun k => nnqSmul_add (warch k) (x.arch k) (y.arch k)
  rw [degN_add, nnqOfNat_add, hpt, nnqSum_add,
    archDeg_stable warch x (max x.archBound y.archBound)
      (Nat.le_max_left _ _),
    archDeg_stable warch y (max x.archBound y.archBound)
      (Nat.le_max_right _ _)]
  exact nnqAdd_shuffle (nnqOfNat (degN wfin x.fin))
    (nnqOfNat (degN wfin y.fin)) (archDeg warch x) (archDeg warch y)

/-- **定理 (M69F-4b): 混合次数の Frobenius 斉次性** deg(φ_e x) = e·deg x。
    有限部は M51F の degN_frob + ι のスカラー両立、無限部は M67F の
    nnqSum_smul、最後にスカラーの加法分配。 -/
theorem degMixed_frob (wfin warch : Nat → Nat) (e : Nat) (x : MixedDiv) :
    degMixed wfin warch (mixedFrob e x)
      = nnqSmul e (degMixed wfin warch x) := by
  show nnqAdd (nnqOfNat (degN wfin (qfrob e x.fin)))
      (nnqSum (fun k => nnqSmul (warch k) (nnqSmul e (x.arch k)))
        x.archBound)
    = nnqSmul e (degMixed wfin warch x)
  have hfin : nnqOfNat (degN wfin (qfrob e x.fin))
      = nnqSmul e (nnqOfNat (degN wfin x.fin)) := by
    rw [degN_frob]
    exact (nnqSmul_ofNat e (degN wfin x.fin)).symm
  have hpt : (fun k => nnqSmul (warch k) (nnqSmul e (x.arch k)))
      = fun k => nnqSmul e (nnqSmul (warch k) (x.arch k)) :=
    funext fun k => by
      rw [nnqSmul_smul e (warch k), nnqSmul_smul (warch k) e, Nat.mul_comm]
  rw [hfin, hpt, nnqSum_smul]
  exact (nnqSmul_add e (nnqOfNat (degN wfin x.fin)) (archDeg warch x)).symm

/-! ## Part 5: 混合 Frobenioid 圏と二分法の総括（M69F-5） -/

/-- **混合 Frobenioid の射**: x → y は Frobenius 次数 d ≥ 1 と
    混合因子 c の対で、線形条件 y = φ_d(x) + c を満たすもの。 -/
structure MixedHom (x y : MixedDiv) where
  /-- Frobenius 次数。 -/
  d : Nat
  /-- 効果的混合因子部分 Div(φ)。 -/
  c : MixedDiv
  d_pos : 1 ≤ d
  /-- 線形条件: y = φ_d(x) + c。 -/
  linear : y = mixedAdd (mixedFrob d x) c

/-- 射の外延性: MixedHom は (d, c) 成分で決まる（linear は Prop）。 -/
theorem MixedHom.ext {x y : MixedDiv} {f g : MixedHom x y}
    (hd : f.d = g.d) (hc : f.c = g.c) : f = g := by
  cases f with | mk fd fc f1 f2 =>
  cases g with | mk gd gc g1 g2 =>
  have hd' : fd = gd := hd
  have hc' : fc = gc := hc
  subst hd'
  subst hc'
  rfl

/-- 恒等射の線形条件: x = φ_1(x) + 0。 -/
theorem mixed_id_linear (x : MixedDiv) :
    x = mixedAdd (mixedFrob 1 x) mixedZero := by
  rw [mixedFrob_one, mixedAdd_zero]

/-- 合成射の線形条件（捻れ半直積型: 混合因子代数の構造定理から従う）。 -/
theorem mixed_comp_linear {a b : Nat} {x y z c₁ c₂ : MixedDiv}
    (h₁ : y = mixedAdd (mixedFrob a x) c₁)
    (h₂ : z = mixedAdd (mixedFrob b y) c₂) :
    z = mixedAdd (mixedFrob (a * b) x)
        (mixedAdd (mixedFrob b c₁) c₂) := by
  rw [h₂, h₁, mixedFrob_add, mixedFrob_frob, mixedAdd_assoc]

/-- **定理 (M69F-5a): 混合 Frobenioid 圏** — 対象 = 混合因子
    （有限素点 + 無限素点）、射 = (d ≥ 1, c) with y = φ_d(x) + c。
    恒等 (1, 0)、合成 (d₁d₂, φ_{d₂}(c₁) + c₂)。圏公理は混合因子モノイドの
    構造定理（M69F-3）から完全証明。[FrdI] の数体の Frobenioid
    （有限・無限の全素点の因子簿記）の base 一点での実装。 -/
def mixedFrobenioid : Cat where
  Obj := MixedDiv
  Hom := MixedHom
  id := fun x => ⟨1, mixedZero, Nat.le_refl 1, mixed_id_linear x⟩
  comp := fun f g =>
    ⟨f.d * g.d, mixedAdd (mixedFrob g.d f.c) g.c,
      Nat.mul_pos f.d_pos g.d_pos,
      mixed_comp_linear f.linear g.linear⟩
  id_comp := fun f =>
    MixedHom.ext (Nat.one_mul f.d)
      (by show mixedAdd (mixedFrob f.d mixedZero) f.c = f.c
          rw [mixedFrob_zero, mixedZero_add])
  comp_id := fun f =>
    MixedHom.ext (Nat.mul_one f.d)
      (by show mixedAdd (mixedFrob 1 f.c) mixedZero = f.c
          rw [mixedFrob_one, mixedAdd_zero])
  assoc := fun f g h =>
    MixedHom.ext (Nat.mul_assoc f.d g.d h.d)
      (by show mixedAdd (mixedFrob h.d (mixedAdd (mixedFrob g.d f.c) g.c))
              h.c
            = mixedAdd (mixedFrob (g.d * h.d) f.c)
                (mixedAdd (mixedFrob h.d g.c) h.c)
          rw [mixedFrob_add, mixedFrob_frob, mixedAdd_assoc])

/-! ### 剛性 — 可除なアルキメデス部を足しても同型は増えない -/

/-- 同型の hom 成分の Frobenius 次数は 1（M48F の算術核の再利用）。 -/
theorem mixed_iso_d_one {x y : MixedDiv}
    (i : CatIso mixedFrobenioid x y) : i.hom.d = 1 :=
  frob_mul_eq_one_left i.hom.d_pos i.inv.d_pos
    (congrArg MixedHom.d i.hom_inv)

/-- 同型の hom 成分の因子部分は 0（fin 部・arch 部とも bound 簿記:
    max bound = 0 から上界 0、有限サポート性から全成分消滅）。 -/
theorem mixed_iso_c_zero {x y : MixedDiv}
    (i : CatIso mixedFrobenioid x y) : i.hom.c = mixedZero := by
  have hc : mixedAdd (mixedFrob i.inv.d i.hom.c) i.inv.c = mixedZero :=
    congrArg MixedHom.c i.hom_inv
  -- fin 部の bound 簿記（M51F の divisor_iso_objects_eq と同じ）
  have hfb : max i.hom.c.fin.bound i.inv.c.fin.bound = 0 :=
    congrArg (fun z => QDiv.bound (MixedDiv.fin z)) hc
  have hfb0 : i.hom.c.fin.bound = 0 := nat_max_eq_zero_left hfb
  -- arch 部の bound 簿記（M67F の real_iso_c_zero と同じ）
  have hab : max i.hom.c.archBound i.inv.c.archBound = 0 :=
    congrArg MixedDiv.archBound hc
  have hab0 : i.hom.c.archBound = 0 := nat_max_eq_zero_left hab
  exact MixedDiv.ext
    (QDiv.ext
      (funext fun k =>
        i.hom.c.fin.vanish k (by rw [hfb0]; exact Nat.zero_le k))
      hfb0)
    (funext fun k =>
      i.hom.c.archVanish k (by rw [hab0]; exact Nat.zero_le k))
    hab0

/-- **定理 (M69F-5b): 混合圏の gaunt 性** — mixedFrobenioid の同型は
    対象を動かせない（x ≅ y ⟹ x = y）。可除なアルキメデス成分を
    足しても Frobenius-like 剛性は壊れない: n 等分の witness は対象
    レベルの構成であって圏の同型ではない（同型なら d の積 = 1 が必要）。 -/
theorem mixed_iso_objects_eq {x y : MixedDiv}
    (i : CatIso mixedFrobenioid x y) : x = y := by
  have hl := i.hom.linear
  rw [mixed_iso_d_one i, mixed_iso_c_zero i, mixedFrob_one,
    mixedAdd_zero] at hl
  exact hl.symm

/-- **定理 (M69F-5b'): gaunt + 同型の一意性**（M53F の剛性述語の充足）—
    混合 Frobenioid は IsGaunt かつ IsoUnique
    （poly-isomorphism は単集合以下に潰れる）。 -/
theorem mixed_gaunt_isoUnique :
    IsGaunt mixedFrobenioid ∧ IsoUnique mixedFrobenioid :=
  ⟨fun _ _ i => mixed_iso_objects_eq i,
   fun _ _ i j =>
     MixedHom.ext ((mixed_iso_d_one i).trans (mixed_iso_d_one j).symm)
       ((mixed_iso_c_zero i).trans (mixed_iso_c_zero j).symm)⟩

/-! ### 総括定理 — 混合因子の可除性は有限部だけが障害 -/

/-- **定理 (M69F-5c): 混合可除性の二分法（総括定理）** —
    混合因子 x が n 等分可能 ⟺ 有限部が n 等分可能。
    ⟸ 向き: 有限部の witness z と無限部の成分ごとの nnqDiv
    （アルキメデス部は常に割れる）を束ねた明示構成。
    ⟹ 向き: fin 部の射影。**可除性の障害は有限素点部分にのみ宿る**
    ことの機械検証であり、Part 2 の構造的二分法（有限ファイバー不可除・
    アルキメデスファイバー可除）の大域混合版。 -/
theorem mixed_divisibility_dichotomy (x : MixedDiv) (n : Nat)
    (hn : 1 ≤ n) :
    (∃ y : MixedDiv, mixedFrob n y = x)
      ↔ (∃ z : QDiv, qfrob n z = x.fin) := by
  constructor
  · intro hex
    match hex with
    | ⟨y, h⟩ => exact ⟨y.fin, congrArg MixedDiv.fin h⟩
  · intro hfin
    match hfin with
    | ⟨z, hz⟩ =>
      refine ⟨⟨z, fun k => nnqDiv (x.arch k) n hn, x.archBound,
        fun k hk => by
          show nnqDiv (x.arch k) n hn = nnqZero
          rw [x.archVanish k hk]
          exact nnqDiv_zero n hn⟩,
        MixedDiv.ext hz (funext fun k => nnq_div_cancel (x.arch k) n hn)
          rfl⟩

/-- **定理 (M69F-5d): 圏レベルの等分（混合版）** — 有限部が n 等分
    できる混合因子 x には「x の 1/n」対象 y と次数 n の純 Frobenius 射
    (n, 0) : y → x が実在する（M67F の real_pilot_division の混合版。
    アルキメデス部の等分は無条件、有限部の等分可能性だけが仮定）。 -/
theorem mixed_pilot_division (x : MixedDiv) (n : Nat) (hn : 1 ≤ n)
    (hfin : ∃ z : QDiv, qfrob n z = x.fin) :
    ∃ y : MixedDiv, mixedFrob n y = x ∧ Nonempty (MixedHom y x) := by
  match (mixed_divisibility_dichotomy x n hn).mpr hfin with
  | ⟨y, hy⟩ =>
    exact ⟨y, hy, ⟨⟨n, mixedZero, hn, by rw [hy, mixedAdd_zero]⟩⟩⟩

/-- **定理 (M69F-5e): 純アルキメデス混合因子は常に可除**（具体的発動 1）—
    有限部が 0 の混合因子（無限素点にのみ台を持つ因子）は任意の
    n ≥ 1 で n 等分できる（二分法の ⟸ 向きの発動: 有限部 0 は
    自明に割れる）。 -/
theorem mixed_fin_zero_divisible (x : MixedDiv) (hf : x.fin = qzero)
    (n : Nat) (hn : 1 ≤ n) :
    ∃ y : MixedDiv, mixedFrob n y = x :=
  (mixed_divisibility_dichotomy x n hn).mpr
    ⟨qzero, by rw [qfrob_zero, hf]⟩

/-- **定理 (M69F-5e'): 有限部に重複度 1 を持つ混合因子は 2 等分不能**
    （具体的発動 2）— fin 部 = singleDiv 0 1（M51F の単一有限素点・
    重複度 1）の混合因子は、無限部がどれだけ豊かでも 2 等分できない
    （二分法の ⟹ 向き + M67F の qdiv_not_divisible）。可除性の障害が
    本当に有限部に宿ることの具体的証人。 -/
theorem mixed_single_not_divisible (x : MixedDiv)
    (hf : x.fin = singleDiv 0 1) :
    ¬ ∃ y : MixedDiv, mixedFrob 2 y = x := by
  intro hex
  apply qdiv_not_divisible
  match hex with
  | ⟨y, h⟩ =>
    exact ⟨y.fin, by rw [← hf]; exact congrArg MixedDiv.fin h⟩

end IUT
