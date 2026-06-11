/-
  IUT/Reconstruction.lean — M10（p進局所体の遠アーベル復元 [AbsTopIII]）の形式化

  M1（IUT/Anabelian.lean）は mono-anabelian 復元の**論理骨格**
  （mono ⟹ bi は公理なし、bi ⟹ mono は選択公理必須）を形式化した。
  本モジュールはその**実体側の第一歩**: p 進局所体 k の絶対ガロア群
  G_k から基本不変量 (p, d) = (剰余標数, 次数 [k:Q_p]) を復元する
  古典的アルゴリズム（[AbsTopIII] の出発点となる復元手続き）を
  実装し、その正しさを機械検証する。

  数学的内容: 局所類体論により G_k^ab ≅ (k^×)^∧ であり、
  k^× ≅ ℤ × μ(k) × ℤ_p^d から、各素数 l に対する Z/l-階数
      rank_l := dim_{F_l}(G_k^ab ⊗ Z/l)
  は次の形を取る（ε_l := 1 if μ_l ⊂ k else 0）:
      rank_l = 1 + ε_l          (l ≠ p)   ≤ 2
      rank_p = 1 + d + ε_p      (l = p)   ≥ 3   (d ≥ 2 のとき)
  したがって **p は「rank ≥ 3 となる唯一の素数」として、
  d は rank_p − 1 − ε_p として群論的に復元される**。
  （d ≥ 2 は開部分群（有限次拡大）に移れば常に達成できる。）

  検証する定理（全て sorry なし）:
  * M10-1 `rank_self_ge` / `rank_other_le` / `p_characterized` —
    復元レシピの根拠: rank は p でのみ 3 以上
  * M10-2 `findWitness_spec` — **witness 探索アルゴリズムの実装**。
    Nat.find は core Lean に存在しないため、整礎再帰（Acc 再帰）で
    自前実装し、正当性を証明（選択公理不使用 = 真にアルゴリズム）
  * M10-3 `reconCore_correct` — 復元アルゴリズム reconCore が
    G^ab データから (p, d, m) を正しく再構成する
  * M10-4 `abelianization_determines` — **復元の一意性**:
    (rank profile, 捩れ位数) は (p, d) を一意に決める
  * M10-5 `padic_recon_monoanabelian` — **MonoAnabelian の充足**:
    M1 の復元設定 `padicRecon` は mono-anabelian。M1 では述語として
    公理化されていた `MonoAnabelian` が、ここでは実際の復元
    アルゴリズムの構成によって**証明**される（M10 → M1 接続）
  * M10-6 `padic_recon_bianabelian` — 系: bi-anabelian も従う
    （M1-1 `mono_implies_bi` の適用）
  * M10-7 `padic_invariant_transport` — 系: (p, d, m) の任意の関数は
    G^ab データから計算できる（M1-7 転送原理の適用）

  **形式化の範囲（正直な申告）**: 局所類体論そのもの
  （G_k^ab ≅ (k^×)^∧）と「rank・捩れ位数が位相群 G_k から読める」
  ことは、入力データ型 `AbData` のフィールドとして公理化した。
  また [AbsTopIII] 本体の主結果（数体・双曲的曲線に対する**環構造**
  の復元）は未形式化であり、ここで機械化したのは局所体の数値的
  不変量の復元アルゴリズムとその mono-anabelian 性である。
-/
import IUT.Anabelian

namespace IUT

/-! ## witness 探索の整礎再帰による実装（Nat.find の自前版）

復元アルゴリズムは「rank ≥ 3 となる素数 l を探す」操作を含む。
この探索を選択公理なしの全域関数として実装するため、
「P が m で不成立なら m+1 へ進む」関係の到達可能性 (Acc) を
witness の存在から証明し、Acc 再帰で探索関数を定義する。 -/

/-- 探索ステップ関係: m' = m + 1 かつ P は m で不成立。 -/
def stepRel (P : Nat → Prop) (m' m : Nat) : Prop := m' = m + 1 ∧ ¬ P m

/-- witness が存在すれば探索開始点 0 は到達可能（Acc）。 -/
theorem acc_zero (P : Nat → Prop) (H : ∃ n, P n) : Acc (stepRel P) 0 := by
  obtain ⟨n, hn⟩ := H
  -- P が成り立つ点では先へ進めない（前者が存在しない）
  have vac : ∀ m, P m → Acc (stepRel P) m := by
    intro m hm
    constructor
    intro y hy
    exact absurd hm hy.2
  -- 一段下ろす: m+1 が到達可能なら m も到達可能
  have step : ∀ m, Acc (stepRel P) (m + 1) → Acc (stepRel P) m := by
    intro m h1
    constructor
    intro y hy
    rw [hy.1]
    exact h1
  -- witness n から下向きに 0 まで
  have down : ∀ k, Acc (stepRel P) (n - k) := by
    intro k
    induction k with
    | zero => exact vac n hn
    | succ i ih =>
      by_cases hni : n ≤ i
      · have h0 : n - (i + 1) = n - i := by omega
        rw [h0]
        exact ih
      · apply step
        have h1 : n - (i + 1) + 1 = n - i := by omega
        rw [h1]
        exact ih
  have h0 : (0 : Nat) = n - n := by omega
  rw [h0]
  exact down n

/-- 探索本体（Acc 再帰）: m から上に向かって P を満たす最初の
    点を返す。Acc.rec を直接使う（Prop の Acc から Type への大消去は
    Acc の特権として許される）。 -/
def findAux (P : Nat → Prop) [DecidablePred P] (m : Nat)
    (a : Acc (stepRel P) m) : Nat :=
  a.rec (motive := fun m _ => Nat)
    (fun m' _ ih => if hm : P m' then m' else ih (m' + 1) ⟨rfl, hm⟩)

/-- 探索の正当性: 返り値は P を満たす。 -/
theorem findAux_spec (P : Nat → Prop) [DecidablePred P] :
    ∀ (m : Nat) (a : Acc (stepRel P) m), P (findAux P m a) := by
  intro m a
  induction a with
  | intro m h ih =>
    show P (if hm : P m then m else findAux P (m + 1) (h (m + 1) ⟨rfl, hm⟩))
    by_cases hm : P m
    · rw [dif_pos hm]
      exact hm
    · rw [dif_neg hm]
      exact ih (m + 1) ⟨rfl, hm⟩

/-- **定理 (M10-2): witness 探索アルゴリズム** — P の witness が
    存在すれば、それを実際に見つける全域計算可能関数（選択公理
    不使用）。 -/
def findWitness (P : Nat → Prop) [DecidablePred P] (H : ∃ n, P n) : Nat :=
  findAux P 0 (acc_zero P H)

theorem findWitness_spec (P : Nat → Prop) [DecidablePred P] (H : ∃ n, P n) :
    P (findWitness P H) :=
  findAux_spec P 0 (acc_zero P H)

/-! ## 局所体の数値不変量と復元レシピ -/

/-- **p 進局所体の数値骨格**: 剰余標数 p ≥ 2、次数 d = [k:Q_p] ≥ 2
    （復元レシピの前提。開部分群 = 有限次拡大に移れば常に達成可能）、
    捩れ位数 m = #μ(k) ≥ 1（1 の冪根の個数）。 -/
structure LocalFieldInvariants where
  p : Nat
  hp : 2 ≤ p
  d : Nat
  hd : 2 ≤ d
  m : Nat
  hm : 1 ≤ m

/-- μ_l ⊂ k の指示関数: l | #μ(k) なら 1。 -/
def eps (l m : Nat) : Nat := if m % l = 0 then 1 else 0

theorem eps_le_one (l m : Nat) : eps l m ≤ 1 := by
  unfold eps
  split <;> omega

/-- **Z/l-階数のプロファイル**（局所類体論 G_k^ab ≅ (k^×)^∧ と
    k^× ≅ ℤ × μ × ℤ_p^d から従う群論的データ）:
    rank_l = 1 + ε_l（l ≠ p）、rank_p = 1 + d + ε_p。 -/
def rank (K : LocalFieldInvariants) (l : Nat) : Nat :=
  if l = K.p then 1 + K.d + eps l K.m else 1 + eps l K.m

theorem rank_self (K : LocalFieldInvariants) :
    rank K K.p = 1 + K.d + eps K.p K.m := by
  unfold rank
  rw [if_pos rfl]

/-- **定理 (M10-1a)**: p では rank ≥ 3（d ≥ 2 より）。 -/
theorem rank_self_ge (K : LocalFieldInvariants) : 3 ≤ rank K K.p := by
  rw [rank_self]
  have hd := K.hd
  omega

/-- **定理 (M10-1b)**: p 以外では rank ≤ 2。 -/
theorem rank_other_le (K : LocalFieldInvariants) {l : Nat} (h : l ≠ K.p) :
    rank K l ≤ 2 := by
  unfold rank
  rw [if_neg h]
  have he := eps_le_one l K.m
  omega

/-- **定理 (M10-1c): p の群論的特徴付け** — p は「rank ≥ 3 となる
    唯一の素数」。復元レシピの正当性の核。 -/
theorem p_characterized (K : LocalFieldInvariants) (l : Nat) :
    3 ≤ rank K l ↔ l = K.p := by
  constructor
  · intro h3
    by_cases h : l = K.p
    · exact h
    · have h2 := rank_other_le K h
      omega
  · intro h
    rw [h]
    exact rank_self_ge K

/-- **定理 (M10-4): 復元の一意性** — G^ab データ（rank profile と
    捩れ位数）は (p, d) を一意に決める。すなわち「二つの局所体の
    G^ab データが一致すれば剰余標数と次数も一致する」——
    bi-anabelian 方向の実体的内容。 -/
theorem abelianization_determines (K K' : LocalFieldInvariants)
    (hr : ∀ l, rank K l = rank K' l) (hm : K.m = K'.m) :
    K.p = K'.p ∧ K.d = K'.d := by
  have hp : K.p = K'.p := by
    have h1 : 3 ≤ rank K' K.p := by
      rw [← hr K.p]
      exact rank_self_ge K
    exact (p_characterized K' K.p).mp h1
  refine ⟨hp, ?_⟩
  have heq := hr K.p
  rw [rank_self K, hp, rank_self K', hm] at heq
  -- heq : 1 + K.d + eps K'.p K'.m = 1 + K'.d + eps K'.p K'.m
  revert heq
  generalize eps K'.p K'.m = e
  intro heq
  omega

/-! ## 復元アルゴリズムの実装と MonoAnabelian の充足 -/

/-- **G^ab データ**（群論的入力）: rank profile・捩れ位数・
    非退化性（rank ≥ 3 の点の存在 = 「G が d ≥ 2 の局所体の
    ガロア群である」ことの群論的に検査可能な帰結）。
    局所類体論によりこれらが G_k から読めることは未形式化の入力。 -/
structure AbData where
  r : Nat → Nat
  m : Nat
  nondeg : ∃ l, 3 ≤ r l

/-- **復元アルゴリズム本体**: G^ab データから (p, d, m) を再構成。
    p = 探索で見つかる「rank ≥ 3 の点」（M10-1c より一意）、
    d = rank(p) − 1 − ε_p。検査に失敗する入力（像の外）には既定値。 -/
def reconCore (r : Nat → Nat) (m : Nat) (h : ∃ l, 3 ≤ r l) : LocalFieldInvariants :=
  if hc : 2 ≤ findWitness (fun l => 3 ≤ r l) h ∧
      2 ≤ r (findWitness (fun l => 3 ≤ r l) h) - 1 -
        eps (findWitness (fun l => 3 ≤ r l) h) m ∧ 1 ≤ m then
    { p := findWitness (fun l => 3 ≤ r l) h, hp := hc.1,
      d := r (findWitness (fun l => 3 ≤ r l) h) - 1 -
        eps (findWitness (fun l => 3 ≤ r l) h) m, hd := hc.2.1,
      m := m, hm := hc.2.2 }
  else { p := 2, hp := Nat.le_refl 2, d := 2, hd := Nat.le_refl 2,
         m := 1, hm := Nat.le_refl 1 }

/-- 復元の算術核: rank_p − 1 − ε_p = d（∃ 仮定のないスコープで証明
    し、Classical.choice の混入を避ける）。 -/
theorem rank_sub_eq (K : LocalFieldInvariants) :
    rank K K.p - 1 - eps K.p K.m = K.d := by
  rw [rank_self]
  have he := eps_le_one K.p K.m
  have hd := K.hd
  revert he hd
  generalize eps K.p K.m = e
  intro he hd
  omega

/-- **定理 (M10-3): 復元アルゴリズムの正当性** — 実際の局所体の
    G^ab データ (rank K, K.m) に適用すると (p, d, m) を正しく
    再構成する。 -/
theorem reconCore_correct (K : LocalFieldInvariants) (h : ∃ l, 3 ≤ rank K l) :
    (reconCore (rank K) K.m h).p = K.p ∧
    (reconCore (rank K) K.m h).d = K.d ∧
    (reconCore (rank K) K.m h).m = K.m := by
  have hfind : findWitness (fun l => 3 ≤ rank K l) h = K.p := by
    have hspec : 3 ≤ rank K (findWitness (fun l => 3 ≤ rank K l) h) :=
      findWitness_spec (fun l => 3 ≤ rank K l) h
    exact (p_characterized K _).mp hspec
  have harith : rank K K.p - 1 - eps K.p K.m = K.d := rank_sub_eq K
  have hc : 2 ≤ findWitness (fun l => 3 ≤ rank K l) h ∧
      2 ≤ rank K (findWitness (fun l => 3 ≤ rank K l) h) - 1 -
        eps (findWitness (fun l => 3 ≤ rank K l) h) K.m ∧ 1 ≤ K.m := by
    rw [hfind, harith]
    exact ⟨K.hp, K.hd, K.hm⟩
  unfold reconCore
  rw [dif_pos hc]
  refine ⟨hfind, ?_, rfl⟩
  show rank K (findWitness (fun l => 3 ≤ rank K l) h) - 1 -
      eps (findWitness (fun l => 3 ≤ rank K l) h) K.m = K.d
  rw [hfind]
  exact harith

/-- **p 進局所体の復元設定**（M1 の `ReconSetting` の実体化）:
    F = 局所体の数値骨格、G = G^ab データ、π = 「G^ab データを読む」。 -/
def padicRecon : ReconSetting where
  F := LocalFieldInvariants
  G := AbData
  pi := fun K => ⟨rank K, K.m, ⟨K.p, rank_self_ge K⟩⟩
  isoF := fun K K' => K.p = K'.p ∧ K.d = K'.d ∧ K.m = K'.m
  isoG := fun g h => g.r = h.r ∧ g.m = h.m
  isoF_refl := fun _ => ⟨rfl, rfl, rfl⟩
  isoF_symm := fun h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  isoF_trans := fun h1 h2 => ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
  isoG_refl := fun _ => ⟨rfl, rfl⟩
  isoG_symm := fun h => ⟨h.1.symm, h.2.symm⟩
  isoG_trans := fun h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  pi_congr := by
    intro X Y h
    refine ⟨funext fun l => ?_, h.2.2⟩
    show rank X l = rank Y l
    unfold rank
    rw [h.1, h.2.1, h.2.2]

/-- **定理 (M10-5): MonoAnabelian の充足** — p 進局所体の復元設定は
    mono-anabelian である。M1 では `MonoAnabelian` は述語（公理化
    された仕様）だったが、ここでは復元アルゴリズム `reconCore` の
    構成によって**証明**される。選択公理不使用（`#print axioms` で
    確認可能）——すなわち復元は真にアルゴリズム的であり、これが
    [AbsTopIII] の「mono-anabelian = アルゴリズムの存在」の実例の
    機械検証である。 -/
theorem padic_recon_monoanabelian : MonoAnabelian padicRecon := by
  refine ⟨fun g => reconCore g.r g.m g.nondeg, ?_, ?_⟩
  · intro K
    exact reconCore_correct K ⟨K.p, rank_self_ge K⟩
  · intro g h hgh
    obtain ⟨gr, gm, gn⟩ := g
    obtain ⟨hr, hm, hn⟩ := h
    obtain ⟨h1, h2⟩ := hgh
    cases h1
    cases h2
    exact ⟨rfl, rfl, rfl⟩

/-- **定理 (M10-6)**: 系として bi-anabelian（同型の反映）も従う
    （M1-1 `mono_implies_bi` の適用、M10 → M1 接続）。 -/
theorem padic_recon_bianabelian : BiAnabelian padicRecon :=
  mono_implies_bi padicRecon padic_recon_monoanabelian

/-- **定理 (M10-7): 不変量転送** — (p, d, m) の任意の同型不変関数は
    G^ab データだけから計算できる（M1-7 `invariant_transport` の
    適用）。「群が体の数値情報を完全に知っている」ことの形式化。 -/
theorem padic_invariant_transport {α : Type}
    (φ : LocalFieldInvariants → α)
    (hφ : ∀ {K K' : LocalFieldInvariants},
      K.p = K'.p ∧ K.d = K'.d ∧ K.m = K'.m → φ K = φ K') :
    ∃ ψ : AbData → α, ∀ K, ψ (padicRecon.pi K) = φ K :=
  invariant_transport padicRecon padic_recon_monoanabelian φ hφ

end IUT
