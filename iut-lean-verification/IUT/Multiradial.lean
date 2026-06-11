/-
  IUT/Multiradial.lean — M5（定理3.11: 多輻的表現アルゴリズム）の形式化

  IUT III 定理3.11（pp.153–157）の statement を原文から読み取り、
  その**論理構造**を形式化する。原文の構成:

  (i) 多輻的表現 — procession 付き D⊢-prime-strip の中に
      (a) 対数殻テンソルパケット I ⊆ I^Q（procession 正規化
          log-volume 付き、Prop 3.9）
      (b) bad place での splitting monoid Ψ⊥_LGP
          （テータ値 q^{j²} の源、∏_{j∈F_l⋇} I^Q に作用）
      (c) 数体 M_MOD_j ⊆ I^Q と大域 Frobenioid（次数は (a) の
          log-volume で計算される）
      を、次の不定性込みで構成する関手的アルゴリズム:
      (Ind1) procession の自己同型による不定性
      (Ind2) 各直和因子への Ism のコピーの作用による不定性
  (ii) log-Kummer 対応 — Frobenius 的データ (n,m) と エタール的
      コア・データ (n,◦) の間の Kummer 同型。log-volume と両立。
      m を動かすと (b)(c)-MOD は厳密に両立するが、(a) は
      (Ind3) 「上半両立性」(inclusions ⊆ / surjections ↠) のみ
  (iii) Θ×μ_LGP-link 両立性 — Kummer 同型は水平射（Θ-link）の
      full poly-isomorphism と両立する

  系3.12 の証明（p.174–175）はこの定理から
      「q-パイロット像は、不定性 (Ind1–3) 込みの Θ-パイロットの
        可能な像たちの合併の正則包に含まれる。log-volume は包含で
        単調だから −|log q| ≤ −|log Θ|」
  という形で従う。本ファイルはこの導出を機械検証する。

  **形式化の範囲（正直な申告）**:
  * 形式化するのは (i)(ii)(iii) の出力仕様（インターフェース）と
    不定性の構造、そして系3.12 の導出論理である
  * アルゴリズムの**構成そのもの**（遠アーベル復元・エタール
    テータ関数の剛性・mono-theta 環境・Frobenioid 論）は
    未形式化として `MultiradialRep` の充足問題に分離される
  * 中心的成果は二分法の精密化:
      - インターフェース自体は充足可能（`multiradial_consistent`）
      - しかし「厳密テータ評価」と「q-パイロット実現」は両立不能
        （`strict_evaluation_obstruction` — Scholze–Stix の議論の
          定理3.11 レベルへの持ち上げ）
      - 従って充足には不定性による体積の膨張が**必然**
        （`padding_necessary`）
    残る未決問題は「実際の IUT の構成が、膨張を IUT IV の計算が
    許す範囲に抑えたままインターフェースを充足するか」に集約される。
-/
import IUT.Skeleton
import IUT.Arithmetic
import IUT.Diophantine

namespace IUT

/-- **体積理論のインターフェース**（IUT III Prop 3.9 の
    procession 正規化 mono-analytic log-volume の公理化）:
    領域の包含順序・正則包（join）・包含で単調な log-volume。 -/
structure VolumeTheory where
  Region : Type
  /-- 包含 ⊆。 -/
  le : Region → Region → Prop
  le_refl : ∀ r, le r r
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  /-- 正則包（holomorphic hull / join）。 -/
  hull : Region → Region → Region
  le_hull_left : ∀ a b, le a (hull a b)
  le_hull_right : ∀ a b, le b (hull a b)
  hull_least : ∀ {a b c}, le a c → le b c → le (hull a b) c
  /-- procession 正規化 log-volume。 -/
  vol : Region → Int
  /-- 体積の単調性（Prop 3.9, (ii)）。 -/
  vol_mono : ∀ {a b}, le a b → vol a ≤ vol b

/-- **定理3.11 のインターフェース**: 多輻的表現が「出力として
    何を提供すると主張しているか」の形式化。

    フィールドと原文の対応:
    * `Ind` — 不定性 (Ind1)×(Ind2)×(Ind3) の選択肢の型
    * `shell` — (i)(a) の対数殻テンソルパケット（多輻的な入れ物）
    * `image i` — 不定性 i のもとでの Θ-パイロットの可能な像
      （(i)(b)(c) のデータの実現）
    * `image_in_shell` — 可能な像は対数殻に収まる（(i)(a) の
      「mono-analytic containers」性）
    * `hullTheta` — 可能な像の合併の正則包（系3.12 で −|log Θ| を
      測る対象）
    * `qRegion` — q-パイロット像（(ii) の Kummer 同型経由）
    * `q_realized` — **(ii)(iii) の核心**: log-Kummer 対応・
      Θ×μ_LGP-link 両立性・IPL/SHE（Remark 3.12.2 の閉ループ）に
      より、q-パイロット像は可能な像のいずれかに含まれる
    * `vol_hull`, `vol_q` — (ii)(a) 末尾の「log-volume との厳密な
      両立性」(Prop 3.9, (iv))（符号規約: |log(·)| = −vol(·)） -/
structure MultiradialRep (V : VolumeTheory) (s : Skeleton) where
  Ind : Type
  ind0 : Ind
  shell : V.Region
  image : Ind → V.Region
  image_in_shell : ∀ i, V.le (image i) shell
  hullTheta : V.Region
  image_in_hull : ∀ i, V.le (image i) hullTheta
  qRegion : V.Region
  q_realized : ∃ i, V.le qRegion (image i)
  vol_hull : V.vol hullTheta = -s.logTheta
  vol_q : V.vol qRegion = -s.logq

/-- **定理 (M5-1): 定理3.11 ⟹ 系3.12**。
    IUT III p.174–175 の証明の機械化: q-パイロット像 ⊆ 可能な像
    ⊆ 正則包、体積単調性より −|log q| ≤ −|log Θ|。

    これにより M6 の証明そのもの（定理3.11 を認めた上での導出）が
    形式検証されたことになる。未証明で残るのは
    `MultiradialRep` の充足（= 定理3.11 の構成の正しさ）のみ。 -/
theorem cor312_of_multiradial {V : VolumeTheory} {s : Skeleton}
    (M : MultiradialRep V s) : Cor312 s := by
  obtain ⟨i, hi⟩ := M.q_realized
  have h1 : V.le M.qRegion M.hullTheta := V.le_trans hi (M.image_in_hull i)
  have h2 : V.vol M.qRegion ≤ V.vol M.hullTheta := V.vol_mono h1
  rw [M.vol_q, M.vol_hull] at h2
  unfold Cor312
  omega

/-- **厳密テータ評価**（Scholze–Stix の読み）: 不定性込みの可能な
    像の体積が、テータ値 {q^{j²}} の素朴な計算値
    −(Σj²/l⋇)·|log q| に**厳密に一致**するという仮定。整数で
    l⋇·vol(image i) = −Σj²·|log q| と表す。 -/
def StrictEvaluation {V : VolumeTheory} {s : Skeleton}
    (M : MultiradialRep V s) : Prop :=
  ∀ i, (s.lstar : Int) * V.vol (M.image i) = -(sumSq s.lstar : Int) * s.logq

/-- **定理 (M5-2): 厳密評価の障害** — Scholze–Stix の議論の
    定理3.11 レベルへの持ち上げ。

    可能な像の体積がすべて素朴なテータ値計算に一致するなら、
    多輻的表現は存在し得ない（q_realized と両立しない）。
    すなわち「不定性 (Ind1–3) が体積を膨らませない」と読む限り、
    定理3.11 の主張する出力仕様は**充足不能**である。 -/
theorem strict_evaluation_obstruction {V : VolumeTheory} {s : Skeleton}
    (M : MultiradialRep V s) (hstrict : StrictEvaluation M) : False := by
  obtain ⟨i, hi⟩ := M.q_realized
  -- q 体積 ≤ 像の体積
  have h2 : V.vol M.qRegion ≤ V.vol (M.image i) := V.vol_mono hi
  rw [M.vol_q] at h2
  -- l⋇ 倍して厳密評価で書き換え
  have h4 : (s.lstar : Int) * -s.logq ≤ (s.lstar : Int) * V.vol (M.image i) :=
    Int.mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg s.lstar)
  rw [hstrict i] at h4
  -- 整理: −(l⋇·logq) ≤ −(Σj²·logq)、つまり Σj²·logq ≤ l⋇·logq
  have e1 : (s.lstar : Int) * -s.logq = -((s.lstar : Int) * s.logq) :=
    Int.mul_neg _ _
  have e2 : -(sumSq s.lstar : Int) * s.logq = -((sumSq s.lstar : Int) * s.logq) :=
    Int.neg_mul _ _
  rw [e1, e2] at h4
  -- しかし Σj² > l⋇ かつ logq > 0
  have h5 : (s.lstar : Int) * s.logq < (sumSq s.lstar : Int) * s.logq :=
    Int.mul_lt_mul_of_pos_right (sumSq_gt_int s.lstar s.hl) s.hq
  omega

/-- **定理 (M5-3): 膨張の必然性** — 望月側の読みの定量的内容。
    多輻的表現が存在するなら、q-パイロットを実現する可能な像の
    体積は最低でも −|log q| まで「太って」いなければならない。
    （厳密テータ値 −(Σj²/l⋇)|log q| はこれより真に小さいので、
    不定性 (Ind1–3) による膨張が必然となる。） -/
theorem padding_necessary {V : VolumeTheory} {s : Skeleton}
    (M : MultiradialRep V s) :
    ∃ i, -s.logq ≤ V.vol (M.image i) := by
  obtain ⟨i, hi⟩ := M.q_realized
  have h2 : V.vol M.qRegion ≤ V.vol (M.image i) := V.vol_mono hi
  rw [M.vol_q] at h2
  exact ⟨i, h2⟩

/-- **定理 (M5-4): インターフェースの充足可能性**（無矛盾性）。
    領域 = 整数（体積値そのもの）、包含 = ≤、正則包 = max とする
    モデルで `MultiradialRep` は充足できる。

    したがって定理3.11 の出力仕様そのものに形式的矛盾はなく
    （M5-2 と対照せよ: 矛盾は厳密評価を追加したときのみ生じる）、
    争点は「実際の IUT の構成がこの仕様を、IUT IV の計算が許す
    膨張の範囲内で充足するか」に正確に局在する。 -/
theorem multiradial_consistent :
    ∃ (V : VolumeTheory) (s : Skeleton), Nonempty (MultiradialRep V s) := by
  refine ⟨
    { Region := Int, le := (· ≤ ·),
      le_refl := Int.le_refl,
      le_trans := fun h1 h2 => Int.le_trans h1 h2,
      hull := fun a b => max a b,
      le_hull_left := fun a b => by omega,
      le_hull_right := fun a b => by omega,
      hull_least := fun h1 h2 => by omega,
      vol := id,
      vol_mono := fun h => h },
    { lstar := 2, hl := by omega, logq := 1, hq := by omega, logTheta := 1 },
    ⟨{ Ind := Unit, ind0 := (),
       shell := 0,
       image := fun _ => -1,
       image_in_shell := fun _ => by omega,
       hullTheta := -1,
       image_in_hull := fun _ => by omega,
       qRegion := -1,
       q_realized := ⟨(), by omega⟩,
       vol_hull := rfl,
       vol_q := rfl }⟩⟩

/-! ## Procession の正規化簿記（IUT III Prop 3.1–3.2, Remark 3.1.1）

定理3.11 (i) の多輻的表現は prime-strip の **procession**
{0} ↪ {0,1} ↪ … ↪ {0,…,l⋇} の上に構成され、log-volume は
各段のテンソル因子数 j+1 で正規化される（procession-normalized）。
その組合せ簿記を形式化する。 -/

/-- procession の総段数重み: `procTotal L = Σ_{j=0}^{L} (j+1)`
    （第 j 段は j+1 個の prime-strip からなる）。 -/
def procTotal : Nat → Nat
  | 0 => 1
  | n + 1 => procTotal n + (n + 2)

/-- **定理 (M5-6): procession 重みの閉形式** —
    2·Σ_{j=0}^{L}(j+1) = (L+1)(L+2)。procession 正規化の分母
    （Remark 3.1.1 の平均化）の正確な値。 -/
theorem two_mul_procTotal (L : Nat) :
    2 * procTotal L = (L + 1) * (L + 2) := by
  induction L with
  | zero => rfl
  | succ n ih =>
    have h1 : (n + 2) * (n + 3) = (n + 2) * (n + 2) + (n + 2) :=
      Nat.mul_succ (n + 2) (n + 2)
    have h2 : (n + 2) * (n + 2) = (n + 1) * (n + 2) + (n + 2) :=
      Nat.succ_mul (n + 1) (n + 2)
    show 2 * (procTotal n + (n + 2)) = (n + 2) * (n + 3)
    rw [Nat.mul_add, ih, h1, h2, Nat.two_mul, ← Nat.add_assoc]

/-- procession は空でない（正規化が well-defined）。 -/
theorem procTotal_pos (L : Nat) : 0 < procTotal L := by
  induction L with
  | zero => exact Nat.one_pos
  | succ n ih =>
    show 0 < procTotal n + (n + 2)
    omega

/-- **定理 (M5-5): 完全パイプライン** — 定理3.11 インターフェース
    ＋ IUT IV の体積計算 ⟹ Szpiro 型不等式。

    これで「定理3.11 の充足 → 系3.12 → Szpiro → （M8 経由で）
    ABC 型帰結」という IUT の主張の全論理経路が Lean 内で接続
    された。未形式化の実質は `MultiradialRep`・
    `LogVolumeComputation` の充足のみである。 -/
theorem szpiro_of_multiradial {V : VolumeTheory} {s : Skeleton}
    (M : MultiradialRep V s) (comp : LogVolumeComputation s) :
    (comp.a - 1) * s.logq ≤ comp.err :=
  szpiro_of_cor312_precise s (cor312_of_multiradial M) comp

end IUT
