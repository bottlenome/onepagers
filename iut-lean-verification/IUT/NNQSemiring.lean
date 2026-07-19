/-
  # M270F: 非負有理数 ℚ≥0 の分配律建設と順序半環への昇格
        （柱C・log-volume 橋の残件 F-準同型分配律 M100F を閉じ ℚ≥0 を
         本物の順序半環に昇格し、比較射 nnqToQ を順序半環準同型として束ねる）

  ## 二軸（§1）
  * 分類: **[実／(a)昇格]**。
  * complete_pct 影響: **C4 を前進**（真水）。M267F（`NNQMulHom.lean`）は
    ℚ≥0 上に本物の乗法 nnqMul（可換モノイド・零吸収・順序単調）を建設し
    比較射 nnqToQ を乗法・単位まで保つ順序半環準同型へ昇格したが、その
    正直な限定で **「左分配律（乗法の加法への分配 x·(y+z) = x·y + x·z）は
    本層では形式化しない……完全な順序半環（分配律込み）には未到達」** と
    明記していた。本層はその残件——F-準同型分配律 M100F tier-L 残件——を
    **本物化**する: 代表レベル（対）で左分配律の交差積多項式恒等式
    a·(b·R + c·Q)·((P·Q)·(P·R)) = (a·b·(P·R) + a·c·(P·Q))·(P·(Q·R)) を
    ring/simp 系タクティク不使用の逐次 rw で証明し、Quot で降下して
    ℚ≥0 の左右分配律を閉じる。これにより M67F 以来の ℚ≥0 が
    **完全な可換順序半環（加法可換モノイド・乗法可換モノイド・零吸収・
    左右分配律・順序両立・全順序）** に昇格し、比較射 nnqToQ が零・単位・
    加法・乗法・順序をすべて保つ**順序半環準同型**として束ねられる。
    log-volume 橋の ℚ≥0 → ℚ 比較射が Mochizuki の要求する「順序半環の
    忠実な埋め込み」に到達する（degR の実化次数が ℚ・ℝ の中で加法・
    乗法・分配・順序のすべてで忠実に読める）。

  ## 内容
  * M270F-1 `nnq_distrib_core` — 分配律の核となる Nat 交差積多項式恒等式。
    共通因子 a·P を括り出して両辺を a·(S)·(P·(P·(Q·R)))（S = b·R + c·Q）に
    正規化する。ring 禁止のため mul_assoc / mul_left_comm / mul_right_comm /
    mul_add / add_mul の逐次 rw で処理。
  * M270F-2 `nnq_left_distrib` — **ℚ≥0 の左分配律** a·(b+c) = a·b + a·c。
    代表 (a,b,c) で preMul p (preAdd q r) と preAdd (preMul p q)(preMul p r)
    の交差積を preDen_succ で展開し nnq_distrib_core に帰着、Quot.sound で降下。
    LHS の実分母は P·Q·R、RHS の実分母は P²·Q·R と真に異なる（P 倍）ため
    対の等式ではなく交差積の等式（nnqRel）でしか成立しない——ゆえに本物の
    分配律の証明である。
  * M270F-3 `nnq_right_distrib` — **右分配律** (a+b)·c = a·c + b·c
    （可換律 nnqMul_comm で左分配律に帰着）。
  * M270F-4 `NNQSemiring` / `nnqSemiring` / `nnqSemiring_exists` —
    **ℚ≥0 は可換順序半環**（分配律込みの完全な半環 + 全順序）。M67F の
    加法・M267F の乗法・順序に分配律を加えて実定理のみを束ねる。
  * M270F-5 `NNQtoQSemiringHom` / `nnqToQSemiringHom` /
    `nnqToQSemiringHom_exists` — **比較射 nnqToQ は順序半環準同型**
    （零・単位・加法・乗法・順序をすべて保つ）。M236F の加法性・M262F の
    順序性・M267F の乗法性を分配律の閉包の下で単一の順序半環準同型として束ねる。

  ## 意義
  M267F の正直申告（左分配律未形式化・完全な順序半環には未到達）を本物化で
  回収する。ℚ≥0 に完全な可換順序半環構造が入り、比較射 nnqToQ が
  「値の一致」だけでなく「半環構造（加法・乗法・分配・順序）の完全な両立」で
  ℚ に忠実に埋め込まれる。M67F の実化 log-volume 次数 degR（ℚ≥0 値）の
  加法・乗法・スケール合成・大小がすべて本物の ℚ・ℝ の中で読めるようになる。

  ## 正直な限定（§4：消さない・弱めない）
  * 分配律は閉じたが、**乗法逆元（体構造）は範囲外**——ℚ≥0 は半環であり
    体ではない（0 でない元の逆元・除法は形式化しない）。
  * 順序は全順序 nnqLe_total を持つが、**順序体の完備性・アルキメデス性・
    ℚ≥0 の一般スカラー作用は本層では扱わない**（M262F/M267F の限定を継承）。
  * **C4 の支配的ギャップ——本物の σ-加法的測度・積分（測度論的 log-volume の
    測度そのもの）は依然として未着手**。本層は log-volume の値域 ℚ≥0 の
    代数・順序構造を完全な順序半環まで固めたに留まり、測度の建設ではない。
  * 因子（RDiv）の効果性順序 → degR の乗法的単調性簿記は本層では扱わない。
  * 全て選択公理不使用（型継承除く）。Prop 値 Quot.lift の well-def に
    propext を使う。主要定理の公理は `[propext, Quot.sound]` のみ
    （`#print axioms` で実測、一時確認後に除去）。
  * サブエージェント並行部品。
-/
import IUT.NNQMulHom

namespace IUT

/-! ## M270F-1: 分配律の核となる Nat 交差積多項式恒等式 -/

/-- **補題 (M270F-1): 分配律の核**（Nat 恒等式）—
    a·(b·R + c·Q)·((P·Q)·(P·R)) = (a·b·(P·R) + a·c·(P·Q))·(P·(Q·R))。
    RHS 分子から共通因子 a·P を括り出し（hnum）、S = b·R + c·Q を一般化して
    両辺を正規形 a·(S·(P·(P·(Q·R)))) に落とす。ring 禁止ゆえ mul_assoc /
    mul_left_comm / mul_right_comm / mul_add / add_mul の逐次 rw で処理。 -/
theorem nnq_distrib_core (a b c P Q R : Nat) :
    a * (b * R + c * Q) * ((P * Q) * (P * R))
      = (a * b * (P * R) + a * c * (P * Q)) * (P * (Q * R)) := by
  -- 各単項式の付替（4 因子の再結合）
  have t1 : a * P * (b * R) = a * b * (P * R) := by
    rw [Nat.mul_assoc a P (b * R), Nat.mul_left_comm P b R,
      ← Nat.mul_assoc a b (P * R)]
  have t2 : a * P * (c * Q) = a * c * (P * Q) := by
    rw [Nat.mul_assoc a P (c * Q), Nat.mul_left_comm P c Q,
      ← Nat.mul_assoc a c (P * Q)]
  -- RHS 分子から共通因子 a·P を括り出す
  have hnum : a * b * (P * R) + a * c * (P * Q) = a * P * (b * R + c * Q) := by
    rw [Nat.mul_add (a * P) (b * R) (c * Q), t1, t2]
  rw [hnum]
  -- 共通の加法因子 S = b·R + c·Q を一般化
  generalize hS : b * R + c * Q = S
  -- LHS を正規形 a·(S·(P·(P·(Q·R)))) へ
  rw [Nat.mul_assoc a S ((P * Q) * (P * R)),
    Nat.mul_assoc P Q (P * R), Nat.mul_left_comm Q P R,
    -- RHS を同じ正規形へ
    Nat.mul_right_comm a P S,
    Nat.mul_assoc (a * S) P (P * (Q * R)),
    Nat.mul_assoc a S (P * (P * (Q * R)))]

/-! ## M270F-2: ℚ≥0 の左分配律 -/

/-- **定理 (M270F-2): ℚ≥0 の左分配律** — a·(b + c) = a·b + a·c。
    代表 (p,q,r) で preMul p (preAdd q r) と preAdd (preMul p q)(preMul p r) の
    交差積を preDen_succ で (p.2+1)(q.2+1)(r.2+1) の積に展開し
    nnq_distrib_core に帰着。左辺の実分母 P·Q·R と右辺の実分母 P²·Q·R は
    真に異なる（P 倍）ので、対の等式ではなく nnqRel（交差積）でのみ成立する
    ——本物の分配律の証明。 -/
theorem nnq_left_distrib (a b c : NNQ) :
    nnqMul a (nnqAdd b c) = nnqAdd (nnqMul a b) (nnqMul a c) := by
  induction a using Quot.ind; rename_i p
  induction b using Quot.ind; rename_i q
  induction c using Quot.ind; rename_i r
  show Quot.mk nnqRel (preMul p (preAdd q r))
      = Quot.mk nnqRel (preAdd (preMul p q) (preMul p r))
  apply Quot.sound
  show p.1 * (q.1 * (r.2 + 1) + r.1 * (q.2 + 1))
        * (preDen (preDen p.2 q.2) (preDen p.2 r.2) + 1)
      = ((p.1 * q.1) * (preDen p.2 r.2 + 1)
          + (p.1 * r.1) * (preDen p.2 q.2 + 1))
        * (preDen p.2 (preDen q.2 r.2) + 1)
  rw [preDen_succ (preDen p.2 q.2) (preDen p.2 r.2),
    preDen_succ p.2 (preDen q.2 r.2),
    preDen_succ p.2 q.2, preDen_succ p.2 r.2,
    preDen_succ q.2 r.2]
  exact nnq_distrib_core p.1 q.1 r.1 (p.2 + 1) (q.2 + 1) (r.2 + 1)

/-! ## M270F-3: ℚ≥0 の右分配律 -/

/-- **定理 (M270F-3): ℚ≥0 の右分配律** — (a + b)·c = a·c + b·c
    （可換律 nnqMul_comm で左分配律に帰着）。 -/
theorem nnq_right_distrib (a b c : NNQ) :
    nnqMul (nnqAdd a b) c = nnqAdd (nnqMul a c) (nnqMul b c) := by
  rw [nnqMul_comm (nnqAdd a b) c, nnq_left_distrib c a b,
    nnqMul_comm c a, nnqMul_comm c b]

/-! ## M270F-4: ℚ≥0 は可換順序半環 -/

/-- **M270F-4a: ℚ≥0 の可換順序半環データ束**。加法可換モノイド
    （結合・可換・両単位）・乗法可換モノイド（結合・可換・両単位）・
    零吸収・**左右分配律**・順序（半順序・最小元・全順序）・演算の順序
    両立（加法/乗法の単調性）を実定理のみで束ねる。M67F の加法・M267F の
    乗法・M262F の順序に本層の分配律を加えて完全な順序半環を構成する。 -/
structure NNQSemiring where
  /-- 加法の結合律。 -/
  add_assoc : ∀ x y z : NNQ, nnqAdd (nnqAdd x y) z = nnqAdd x (nnqAdd y z)
  /-- 加法の可換律。 -/
  add_comm : ∀ x y : NNQ, nnqAdd x y = nnqAdd y x
  /-- 加法の左単位 0 + x = x。 -/
  zero_add : ∀ x : NNQ, nnqAdd nnqZero x = x
  /-- 加法の右単位 x + 0 = x。 -/
  add_zero : ∀ x : NNQ, nnqAdd x nnqZero = x
  /-- 乗法の結合律。 -/
  mul_assoc : ∀ x y z : NNQ, nnqMul (nnqMul x y) z = nnqMul x (nnqMul y z)
  /-- 乗法の可換律。 -/
  mul_comm : ∀ x y : NNQ, nnqMul x y = nnqMul y x
  /-- 乗法の左単位 1·x = x。 -/
  one_mul : ∀ x : NNQ, nnqMul nnqOne x = x
  /-- 乗法の右単位 x·1 = x。 -/
  mul_one : ∀ x : NNQ, nnqMul x nnqOne = x
  /-- 右零吸収 x·0 = 0。 -/
  mul_zero : ∀ x : NNQ, nnqMul x nnqZero = nnqZero
  /-- 左零吸収 0·x = 0。 -/
  zero_mul : ∀ x : NNQ, nnqMul nnqZero x = nnqZero
  /-- **左分配律** a·(b + c) = a·b + a·c。 -/
  left_distrib : ∀ a b c : NNQ,
    nnqMul a (nnqAdd b c) = nnqAdd (nnqMul a b) (nnqMul a c)
  /-- **右分配律** (a + b)·c = a·c + b·c。 -/
  right_distrib : ∀ a b c : NNQ,
    nnqMul (nnqAdd a b) c = nnqAdd (nnqMul a c) (nnqMul b c)
  /-- 順序の反射律。 -/
  le_refl : ∀ x : NNQ, nnqLe x x
  /-- 順序の推移律。 -/
  le_trans : ∀ {x y z : NNQ}, nnqLe x y → nnqLe y z → nnqLe x z
  /-- 順序の反対称律。 -/
  le_antisym : ∀ {x y : NNQ}, nnqLe x y → nnqLe y x → x = y
  /-- 全順序性。 -/
  le_total : ∀ x y : NNQ, nnqLe x y ∨ nnqLe y x
  /-- 最小元 0 ≤ x（非負錐）。 -/
  zero_le : ∀ x : NNQ, nnqLe nnqZero x
  /-- 加法の順序単調性。 -/
  add_mono : ∀ {a b c d : NNQ}, nnqLe a b → nnqLe c d →
    nnqLe (nnqAdd a c) (nnqAdd b d)
  /-- 乗法の順序単調性。 -/
  mul_mono : ∀ (c : NNQ) {x y : NNQ}, nnqLe x y →
    nnqLe (nnqMul x c) (nnqMul y c)

/-- **M270F-4b: witness** — ℚ≥0 の可換順序半環構造。 -/
def nnqSemiring : NNQSemiring where
  add_assoc := nnqAdd_assoc
  add_comm := nnqAdd_comm
  zero_add := nnqZero_add
  add_zero := nnqAdd_zero
  mul_assoc := nnqMul_assoc
  mul_comm := nnqMul_comm
  one_mul := nnqOne_mul
  mul_one := nnqMul_one
  mul_zero := nnqMul_zero
  zero_mul := nnqZero_mul
  left_distrib := nnq_left_distrib
  right_distrib := nnq_right_distrib
  le_refl := nnqLe_refl
  le_trans := nnqLe_trans
  le_antisym := nnqLe_antisym
  le_total := nnqLe_total
  zero_le := nnqZero_le
  add_mono := nnqAdd_mono
  mul_mono := nnqMul_mono

/-- **capstone (M270F-4c): 存在** — ℚ≥0 が完全な可換順序半環（分配律込み・
    全順序）として無矛盾に存在する。M267F の正直申告（左分配律未形式化・
    完全な順序半環には未到達）を本物化で回収する単一証明記録。 -/
theorem nnqSemiring_exists : Nonempty NNQSemiring :=
  ⟨nnqSemiring⟩

/-! ## M270F-5: 比較射 nnqToQ は順序半環準同型 -/

/-- **M270F-5a: 比較射 nnqToQ の順序半環準同型データ束**。零・単位・加法・
    乗法・順序をすべて保つ。M236F の加法性・M262F の順序性・M267F の乗法性を
    ℚ≥0 の分配律閉包の下で単一の順序半環準同型として束ねる。 -/
structure NNQtoQSemiringHom where
  /-- 零の保存 nnqToQ(0) = 0。 -/
  map_zero : nnqToQ nnqZero = ratRing.zero
  /-- 単位元の保存 nnqToQ(1) = 1。 -/
  map_one : nnqToQ nnqOne = ratRing.one
  /-- 加法の保存 nnqToQ(x + y) = nnqToQ(x) + nnqToQ(y)。 -/
  map_add : ∀ x y : NNQ, nnqToQ (nnqAdd x y) = qAdd (nnqToQ x) (nnqToQ y)
  /-- 乗法の保存 nnqToQ(x·y) = nnqToQ(x)·nnqToQ(y)。 -/
  map_mul : ∀ x y : NNQ, nnqToQ (nnqMul x y) = qMul (nnqToQ x) (nnqToQ y)
  /-- 順序の保存 x ≤ y ⟹ nnqToQ(x) ≤ nnqToQ(y)。 -/
  map_le : ∀ {x y : NNQ}, nnqLe x y → qLe (nnqToQ x) (nnqToQ y)

/-- **M270F-5b: witness** — 比較射 nnqToQ の順序半環準同型構造。 -/
def nnqToQSemiringHom : NNQtoQSemiringHom where
  map_zero := nnqToQ_zero
  map_one := nnqToQ_one
  map_add := nnqToQ_add
  map_mul := nnqToQ_mul
  map_le := nnqToQ_mono

/-- **capstone (M270F-5c): 存在** — 比較射 nnqToQ : ℚ≥0 → ℚ が零・単位・
    加法・乗法・順序をすべて保つ順序半環準同型として無矛盾に存在する。
    ℚ≥0 の完全な順序半環構造（本層の分配律込み）が比較射を通して ℚ に
    忠実に埋め込まれる、log-volume 橋の ℚ≥0 → ℚ 比較射の完成記録。 -/
theorem nnqToQSemiringHom_exists : Nonempty NNQtoQSemiringHom :=
  ⟨nnqToQSemiringHom⟩

end IUT
