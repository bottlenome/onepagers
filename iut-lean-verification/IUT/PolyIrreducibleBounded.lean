/-
  IUT/PolyIrreducibleBounded.lean — M273F（**有界整除 `pdbDvd` 上の既約性の
  忠実な定式化**と「既約 ⟹ gcd 単元」の橋: 一般 f の ℚ[X]/(f) 実体化の中核論理を
  **正しい多項式整除 `pdbDvd`（有界余因子）** の上で組む）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無・模型なし・toy 主語なし）。

  **complete_pct 影響**: 柱A「実 Galois 理論／実 π₁^ét」の本物の先行建設
  （承認済み足場(c)——名前付き実ターゲット「一般 f の ℚ[X]/(f) 実体化」への
  必要足場）。既存 `PolyIrreducible.lean`（M271F）の `pirIrreducible` /
  `pir_gcd_unit_of_not_dvd` は**非有界**の冪級数整除 `pbzDvd`（余因子が
  ℚ[[X]] の元＝定数項 ≠ 0 の多項式が単元になる）の上に組まれており、実
  多項式の既約性には**不適**（定数項 ≠ 0 の一次式が単元扱いになる）。本層は
  同じ論理核を **`PolyDvdBounded.lean`（M272F）の有界余因子整除 `pdbDvd`**
  ——余因子 c を IsPoly（真の多項式＝有界）に制限した本物の多項式整除——の
  上に忠実に組み直し、既約性 `pibIrreducible` と本丸の橋
  `pib_gcd_unit_of_not_dvd`（既約 f・gg∣f・gg∣a・f∤a ⟹ gg 単元）を、
  `pdb_dvd_trans`（本物の推移律・仮説引数なし）だけを使って証明する。

  * M273F-1 `pibIrreducible` — **`pdbDvd`/`pdbAssoc` 上の既約性の忠実な
    定式化**: (次数 ≥ 1) ∧ (∀ 有界約元 d, d は単元 or f と `pdbAssoc`)。
    非有界 pbzDvd の代わりに**本物の多項式整除 pdbDvd** を主語にする。
  * M273F-2 `pib_gcd_unit_of_not_dvd` — **本丸の橋**: 既約 f・gg∣f・gg∣a・
    f∤a（全て pdbDvd）⟹ gg 単元。既約性の二分を `hirr.2 gg hgf` に適用。
    gg が単元ならそのまま。gg が f と `pdbAssoc`（pdbDvd gg f ∧ pdbDvd f gg）
    なら、その**第2成分 pdbDvd f gg**（f∣gg）と hga（gg∣a）を `pdb_dvd_trans`
    で合成して pdbDvd f a（f∣a）を得、hnd（f∤a）と矛盾——ゆえ gg 単元。
    推移律は仮説引数でなく本物の `pdb_dvd_trans` を使う（依存を切らない）。
  * M273F-3 `pib_unit_eq_psC` — 単元の展開（gg = psC c, c ≠ 0）。
    `pdvIsUnit` の定義展開そのもの（M271F `pir_unit_eq_psC` と同一論理を
    有界層に再掲）。

  正直な限定（何が本物で何が honest か）:
   - **本物**: 有界余因子整除 `pdbDvd`（真の多項式整除）の上での既約性の
     忠実な定式化（有界約元 = 単元 or `pdbAssoc` を定義に内包）と、本丸
     **既約 ⟹ f∤a なら gcd は単元** の含意は、一般 `CRing R` 係数の多項式
     （有限台冪級数）環の上で完全証明（sorry 皆無・新規 Classical.choice 皆無・
     仮説引数なし・`#print axioms` = propext, Quot.sound のみ）。推移律を
     外部仮説で受けず本物の `pdb_dvd_trans`（M272F-3）を使うので、本丸の橋は
     整除性を誤魔化さない。
   - **M271F（非有界版）との差（本層の成果）**: M271F の
     `pir_gcd_unit_of_not_dvd` は非有界 `pbzDvd` 上に組まれ、余因子が
     冪級数（定数項 ≠ 0 の多項式が単元）になり得るため実多項式の既約性に
     不適だった。本層は主語を**有界余因子整除 `pdbDvd`** に置換して同じ橋を
     組み直す（§4 準拠・定義を本物＝有界に置換して証明し直す・弱化なし）。
   - 次数上界の witness は既約性の第1成分（∃ nf, 1 ≤ nf ∧ …）として受け取る
     （有限台性からの次数抽出は行わない・M268F/M269F/M271F/M272F と同精神）。
     complete_pct は未設定（本層はグラフメタ不更新）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyDvdBounded

namespace IUT

/-! ## M273F-1: 有界整除 `pdbDvd` 上の既約性の忠実な定式化 -/

/-- **M273F-1: 既約性（有界整除版）** — f が既約 :=
    (i) 次数 ≥ 1（∃ nf ≥ 1, f は nf+1 で有界かつ nf 次係数 ≠ 0）かつ
    (ii) f の任意の**有界約元** d（`pdbDvd R d f`、余因子が真の多項式）は
    **単元 `pdvIsUnit` or f と同伴 `pdbAssoc`**。
    非有界冪級数整除 `pbzDvd`（M271F `pirIrreducible`）ではなく、本物の
    多項式整除 `pdbDvd`（有界余因子）を主語にした忠実な既約性。toy 主語不使用。 -/
def pibIrreducible (R : CRing) (f : PS R) : Prop :=
  (∃ nf, 1 ≤ nf ∧ IsPolyBounded R f (nf + 1) ∧ f nf ≠ R.zero) ∧
  ∀ d, pdbDvd R d f → (pdvIsUnit R d ∨ pdbAssoc R d f)

/-! ## M273F-2: 本丸の橋（既約 ⟹ gcd は単元・有界整除版） -/

/-- **定理 (M273F-2): 既約 ⟹ f∤a なら公約元 gg は単元（有界整除版）** —
    f 既約・gg∣f・gg∣a・f∤a（全て有界整除 `pdbDvd`）のとき gg は単元。
    証明: 既約性の二分 `hirr.2 gg hgf` を適用。gg が単元 `pdvIsUnit` なら
    そのまま。gg が f と同伴 `pdbAssoc`（`pdbDvd R gg f ∧ pdbDvd R f gg`）なら、
    その**第2成分 `pdbDvd R f gg`**（f∣gg）と hga（gg∣a）を本物の推移律
    `pdb_dvd_trans`（M272F-3）で合成して `pdbDvd R f a`（f∣a）を得る。これは
    hnd（f∤a）に矛盾するので、この枝は起こらず gg は単元。 -/
theorem pib_gcd_unit_of_not_dvd (R : CRing) (f a gg : PS R)
    (hirr : pibIrreducible R f) (hgf : pdbDvd R gg f)
    (hga : pdbDvd R gg a) (hnd : ¬ pdbDvd R f a) : pdvIsUnit R gg := by
  cases hirr.2 gg hgf with
  | inl hu => exact hu
  | inr hassoc =>
    have hfgg : pdbDvd R f gg := hassoc.2
    have hfa : pdbDvd R f a := pdb_dvd_trans R hfgg hga
    exact absurd hfa hnd

/-! ## M273F-3: 単元の展開 -/

/-- **定理 (M273F-3): 単元 = 非零定数** — gg が単元なら ∃ c ≠ 0, gg = psC c。
    `pdvIsUnit` の定義展開そのもの（M271F `pir_unit_eq_psC` と同一論理を
    有界層に再掲）。親が `pdbBezout` の gcd gg にこれを適用し、Bezout=1
    へ繋ぐ形を明示する。 -/
theorem pib_unit_eq_psC (R : CRing) (gg : PS R) (h : pdvIsUnit R gg) :
    ∃ c : R.carrier, c ≠ R.zero ∧ gg = psC R c := h

end IUT
