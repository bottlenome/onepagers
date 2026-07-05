/-
# M251F: 塔剰余射の核は極大イデアルを含む — (λₙ) ⊆ ker ρₙ
        （柱B B-1・ef=[L:K] 簿記の e 側 exact 付値と f 側 剰余全射を結ぶ構造的グルー）

M246F `IUT/LambdaTowerResidueSurj.lean`（f 側: 剰余射 ρₙ : Oₙ → ℤ/p が
全レベルで全射・剰余体拡大次数 f = 1・完全分岐塔）と
M235F `IUT/LambdaTowerPiValBound.lean`（e 側: 遷移像 ι(λₙ) の exact 付値
v(ι(λₙ)) = p を無条件確立、M235F-3
`towerGen_transition_val_exact_uncond`）の直上に立つ。

背景（M246F/M235F の正直な限定）:
  * M246F は f 側（剰余体拡大次数 f = 1）を ρₙ の**全射性**として無条件に
    閉じたが、これは剰余射の**値域**（= ℤ/p 全体）に関する主張であり、
    剰余射の**核**（ker ρₙ）の構造——とりわけ核が極大イデアル (λₙ) を
    含むこと——は「別枝」として明示的に残されていた（M246F 正直な限定
    第 2 段: 「核 = (λₙ) の等式は別枝」）。
  * M235F は e 側（遷移像 ι(λₙ) の exact 付値 = p、分岐指数 e = p の実現
    の一片）を無条件に閉じたが、それは (λ_{n+1}) フィルトレーション上の
    付値の主張であり、**剰余射との接続**（付値 ≥ 1 の元が剰余で消えること）
    は触れられていなかった。
  * すなわち M246F（f 側・剰余の値域）と M235F（e 側・付値フィルトレー
    ション）は、それぞれ独立に積み上げられ、両者を**同じ塔レベルで結ぶ
    構造的な橋**——「付値 ≥ 1（極大イデアル (λₙ)）の元は剰余射 ρₙ で 0 に
    落ちる」——が未接続だった。

本層はこの橋を無条件に架ける。すなわち各レベル n で、生成元 λₙ の
生成する極大イデアル (λₙ) は剰余射 ρₙ の核に含まれる:

  * **核 ⊇ 極大イデアル（本丸）**: 付値 ≥ 1 の元 a（a = h·λₙ、M151F-1
    `IsValAtLeast … 1`）は、ρₙ(a) = ρₙ(h·λₙ) = ρₙ(h)·ρₙ(λₙ)
    （`res.map_mul`）で、M111 の ρₙ(λₙ) = 0（`res_lam`）により
    ρₙ(h)·0 = 0（`CRing.mul_zero`）へ落ちる。すなわち
    **a ∈ (λₙ) ⟹ ρₙ(a) = 0**（(λₙ) ⊆ ker ρₙ）。
  * **e 側との接続**: 遷移像 ι(λₙ) は exact 付値 v(ι(λₙ)) = p（M235F-3、
    無条件）を持つので、とくに付値 ≥ 1。ゆえに上の本丸を ι(λₙ) に適用して
    ρ_{n+1}(ι(λₙ)) = 0。**exact に p 段沈む分岐方向（e 側）は、剰余体
    （f = 1・f 側）から見えない**——e 側 exact 付値と f 側 剰余核が
    同一の塔レベルで噛み合うことの構造的証拠。

内容:
  * M251F-1 `tower_res_kills_val_ge_one` — **核 ⊇ 極大イデアル（本丸）**:
    ∀ n a, 付値 ≥ 1（IsValAtLeast … (towerGen p n) a 1）なら ρₙ(a) = 0。
    (λₙ) ⊆ ker ρₙ の形式化。M111 `res_lam`（ρₙ(λₙ) = 0）を掛け算で吸収。
  * M251F-2 `tower_res_kills_transition_gen` — **e 側との接続**:
    ∀ n, ρ_{n+1}(ι(λₙ)) = 0。M235F-3 の exact 付値 v(ι(λₙ)) = p を
    `isValAtLeast_mono` で付値 ≥ 1 に落とし、M251F-1 に食わせる。exact に
    p 段沈む遷移分岐方向が剰余体で消えることの確定。
  * M251F-3 `TowerRamifResidueKernelData` / `towerRamifResidueKernelData` /
    `towerRamifResidueKernel_exists` — 総括レコード（核 ⊇ 極大イデアル・
    遷移像の消滅・e 側 exact 付値 M235F-3・f 側 剰余全射 M246F）と
    witness・存在。

意義: M246F（f = 1・剰余の値域）と M235F（e = p・付値フィルトレーション）
という ef=[L:K] 簿記の両側を、「極大イデアル (λₙ) ⊆ ker ρₙ」という
剰余核の構造で結ぶ。これは f 側では M246F の全射性（値域 = ℤ/p）を
補完し（値域だけでなく核の下界 (λₙ) ⊆ ker も押さえる）、e 側では
M235F の exact 付値（v(ι(λₙ)) = p）が剰余核へ写ることを示して、
「exact に沈む分岐方向は剰余体に逃げ場がない」という M246F 意義文の
主張（e 側の付値成長が丸ごと分岐指数 e に乗る）に核レベルの裏付けを
与える。

正直な限定:
  * 本層が確定するのは**核の下界** (λₙ) ⊆ ker ρₙ（付値 ≥ 1 ⟹ 剰余 0）
    のみである。**逆包含** ker ρₙ ⊆ (λₙ)（剰余 0 ⟹ 付値 ≥ 1、すなわち
    核 = (λₙ) の等式・剰余体の環同型 Oₙ/(λₙ) ≅ ℤ/p）は本層では扱わない
    （M246F 正直な限定の「核 = (λₙ) の等式は別枝」がそのまま残る）。
    逆包含には各レベルの整域性・付値の完全性を要し次層に残る。
  * したがって ef=[L:K] 簿記の**完成**（e·f = [Oₙ:O₀] の module 次数
    としての等式・分岐指数 e の完全値 v(π_{n+1}) = p·v(π_n)）は依然未達
    （M235F/M239F/M243F/M246F の正直申告どおり）。本層は e 側（M235F の
    exact 付値）と f 側（M246F の全射）を剰余核の下界で結ぶ**構造的
    グルー**を供給するのみで、両者の積 ef を module 次数として確定する
    ものではない。数値としての e = p（M235F-3）・f = 1（M246F）は
    レコードに併載するが、その積が拡大次数に一致することは形式化しない。

全て選択公理不使用（M246F/M235F/M111/LambdaValuation/LambdaTowerGen から
propext, Quot.sound を継承、新規 Classical.choice を証明本体で導入
しない）。サブエージェント並行部品（tier M）。
-/
import IUT.LambdaTowerResidueSurj
import IUT.LambdaTowerPiValBound

namespace IUT

/-! ## M251F-1: 核 ⊇ 極大イデアル（本丸）— 付値 ≥ 1 の元は剰余で消える -/

/-- **定理 (M251F-1, 本丸): 剰余核は極大イデアルを含む** — ∀ n、レベル n
    の元 a が付値 ≥ 1（a ∈ (λₙ)、`IsValAtLeast … (towerGen p n) a 1`）
    なら、剰余像 ρₙ(a) = (towerRes p hp n).res.map a は 0。
    a = h·λₙ（`IsValAtLeast … 1` の witness、`rpow_one` で λₙ^1 = λₙ）を
    `res.map_mul` で ρₙ(h)·ρₙ(λₙ) に開き、M111 `res_lam`（ρₙ(λₙ) = 0）で
    ρₙ(h)·0 = 0（`CRing.mul_zero`）へ。すなわち **(λₙ) ⊆ ker ρₙ**。
    M246F の全射性（剰余の値域 = ℤ/p）を核側から補完する。 -/
theorem tower_res_kills_val_ge_one (p : Nat) (hp : 2 ≤ p) (n : Nat)
    {a : (towerLevel p n).ring.carrier}
    (ha : IsValAtLeast (towerLevel p n).ring (towerGen p n) a 1) :
    (towerRes p hp n).res.map a = (zmodRing (p ^ 1)).zero := by
  obtain ⟨h, hx⟩ := ha
  rw [hx, rpow_one, (towerRes p hp n).res.map_mul]
  show (zmodRing (p ^ 1)).mul ((towerRes p hp n).res.map h)
      ((towerRes p hp n).res.map (towerLevel p n).lam)
    = (zmodRing (p ^ 1)).zero
  rw [(towerRes p hp n).res_lam]
  exact CRing.mul_zero (zmodRing (p ^ 1)) ((towerRes p hp n).res.map h)

/-! ## M251F-2: e 側との接続 — 遷移像 ι(λₙ) は剰余で消える -/

/-- **定理 (M251F-2): 遷移像の剰余消滅（e 側との接続）** — ∀ n、遷移像
    ι(λₙ) = (towerHom p n)(λₙ) の剰余像 ρ_{n+1}(ι(λₙ)) は 0。
    M235F-3 `towerGen_transition_val_exact_uncond` の exact 付値
    v(ι(λₙ)) = p（無条件）から、とくに付値 ≥ 1（`isValAtLeast_mono`、
    1 ≤ p）を取り、本丸 M251F-1 を ι(λₙ) に適用する。**exact に p 段
    沈む遷移分岐方向（e 側）が剰余体（f = 1・f 側）から見えない**ことの
    確定——M251F-1 を経由するので `towerRes_compat` を使う別証と異なり、
    e 側 exact 付値と f 側 剰余核が同一レベルで噛み合うことを示す。 -/
theorem tower_res_kills_transition_gen (p : Nat) (hp : 2 ≤ p) (n : Nat) :
    (towerRes p hp (n + 1)).res.map ((towerHom p n).map (towerGen p n))
      = (zmodRing (p ^ 1)).zero := by
  have hv : IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerHom p n).map (towerGen p n)) p :=
    (towerGen_transition_val_exact_uncond p hp n p).mpr (Nat.le_refl p)
  have hv1 : IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerHom p n).map (towerGen p n)) 1 :=
    isValAtLeast_mono (towerLevel p (n + 1)).ring (towerGen p (n + 1))
      ((towerHom p n).map (towerGen p n)) p 1 (by omega) hv
  exact tower_res_kills_val_ge_one p hp (n + 1) hv1

/-! ## M251F-3: 総括 -/

/-- **M251F-3a: 総括** — 塔剰余核データ（ef=[L:K] 簿記の e 側・f 側を
    剰余核で結ぶ）: 核 ⊇ 極大イデアル（付値 ≥ 1 ⟹ 剰余 0）・遷移像の
    剰余消滅・e 側 exact 付値（M235F-3, v(ι(λₙ)) = p）・f 側 剰余全射
    （M246F, f = 1）。 -/
structure TowerRamifResidueKernelData (p : Nat) (hp : 2 ≤ p) where
  /-- M251F-1（本丸）: 核 ⊇ 極大イデアル——付値 ≥ 1 の元は剰余で消える
      （(λₙ) ⊆ ker ρₙ）。 -/
  res_kills_max_ideal : ∀ (n : Nat) (a : (towerLevel p n).ring.carrier),
    IsValAtLeast (towerLevel p n).ring (towerGen p n) a 1 →
    (towerRes p hp n).res.map a = (zmodRing (p ^ 1)).zero
  /-- M251F-2: 遷移像 ι(λₙ) の剰余消滅 ρ_{n+1}(ι(λₙ)) = 0（e 側との
      接続）。 -/
  res_kills_transition : ∀ n,
    (towerRes p hp (n + 1)).res.map ((towerHom p n).map (towerGen p n))
      = (zmodRing (p ^ 1)).zero
  /-- e 側（M235F-3）: 遷移像 ι(λₙ) の exact 付値——ι(λₙ) ∈ (λ_{n+1}^k)
      ⇔ k ≤ p（v(ι(λₙ)) = p、分岐指数 e = p の実現の一片・無条件）。 -/
  e_exact : ∀ n k,
    IsValAtLeast (towerLevel p (n + 1)).ring (towerGen p (n + 1))
        ((towerHom p n).map (towerGen p n)) k
      ↔ k ≤ p
  /-- f 側（M246F）: 全レベルで剰余射 ρₙ : Oₙ → ℤ/p は全射（剰余体 = ℤ/p・
      f = 1・完全分岐塔）。 -/
  f_surjective : ∀ (n : Nat) (c : (zmodRing (p ^ 1)).carrier),
    ∃ x : (towerLevel p n).ring.carrier,
      (towerRes p hp n).res.map x = c

/-- **M251F-3b: witness** — 本層の M251F-1/M251F-2 と、e 側 M235F-3
    `towerGen_transition_val_exact_uncond`・f 側 M246F `tower_res_surjective`
    で純レコードを充填（選択公理不使用）。 -/
def towerRamifResidueKernelData (p : Nat) (hp : 2 ≤ p) :
    TowerRamifResidueKernelData p hp where
  res_kills_max_ideal := fun n _ ha => tower_res_kills_val_ge_one p hp n ha
  res_kills_transition := fun n => tower_res_kills_transition_gen p hp n
  e_exact := fun n k => towerGen_transition_val_exact_uncond p hp n k
  f_surjective := fun n c => tower_res_surjective p hp n c

/-- **M251F-3c: 存在定理（ヘッドライン）** — 塔剰余射 ρₙ の核は極大
    イデアル (λₙ) を含み（付値 ≥ 1 ⟹ 剰余 0）、とくに exact に p 段沈む
    遷移分岐方向 ι(λₙ)（e 側 M235F-3）は剰余体（f = 1・f 側 M246F）から
    見えない。ef=[L:K] 簿記の e 側 exact 付値と f 側 剰余全射を、剰余核の
    下界 (λₙ) ⊆ ker ρₙ で結ぶ構造的グルー——柱B B-1（λ-塔の剰余・分岐
    構造）の一段。 -/
theorem towerRamifResidueKernel_exists (p : Nat) (hp : 2 ≤ p) :
    Nonempty (TowerRamifResidueKernelData p hp) :=
  ⟨towerRamifResidueKernelData p hp⟩

end IUT
