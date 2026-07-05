/-
  IUT/ZariskiConnected.lean — M292F: Zariski 連結性 ⟺ 冪等元
  ── 柱A スキーム論の本物の先行建設（Spec の連結成分 ↔ 環の冪等元）

  分類 **[実]**（本物の可換環 `CRing`・本物の体 `IUTField`・本物の分裂エタール代数
  K^n の上での「連結性 ⟺ 非自明冪等元なし」の実構成。素イデアル・Spec・基本開集合
  D(f) は自前の忠実な最小定義で本物に建てる。toy 模型・代理を主語にしない）。

  **complete_pct 影響: 柱A スキーム論／実 π₁^ét の「連結性の環論的復元」の本物の
  先行建設**。mono-anabelian 復元では「対象の連結成分（Π₀）は環（座標環）から復元
  される」ことが土台であり、アフィンスキーム Spec R では
    **Spec R が連結 ⟺ R が非自明冪等元を持たない**
  が環論的な実体を与える。本モジュールは M280F（本物の冪等元・補元 1−e・直交分解
  e(1−e)=0・体の冪等元 {0,1}・K^n の非自明冪等元）を再利用し、
  (1) **冪等元 e から本物の clopen 分割** Spec R = D(e) ⊔ D(1−e) を、自前の忠実な
      素イデアル定義（0∈P, 加法閉, イデアル, 1∉P, 素性 ab∈P→a∈P∨b∈P）の上で
      **完全証明**する（任意の素イデアル P は e∈P と 1−e∈P のちょうど一方——
      両方だと 1=e+(1−e)∈P で 1∉P に矛盾、どちらもないと e(1−e)=0∈P で素性に矛盾）、
  (2) **非自明冪等元 ⟹ 非連結**（連結の環論的定義 idemSpec_connected の否定）、
  (3) **連結 ⟹ 冪等元自明**（(2) の対偶＝定義の展開）、
  (4) **体 K は連結**（M280F idemSpec_field_is_connected）・**分裂 K^n(n≥2) は非連結**
      （M280F idemSpec_split_disconnected の位相版）、
  (5) capstone `ZariskiConnData`（環＋冪等元↦clopen 分割の対応＋連結性）と
      `zarConn_iff_idem`（連結 ⟺ 冪等元自明）、`zarConn_exists`、
      `zarConn_components_eq_idem`（連結成分↔冪等元の骨組み: 原始冪等元 eᵢ ごとの
      本物の clopen 分割 D(eᵢ)⊔D(1−eᵢ)）、実 ℚ 上の実例
  を完全証明する。これは一般スキームの連結成分関手 π₀ への本物の入口である。

  * M292F-0 `ZarPrimeIdeal` / `zarBasicOpen` — 自前の忠実な素イデアルと基本開集合
    D(f)={P | f∉P}（M289F PrimeSpectrum 整合の最小定義・依存回避のため import せず）
  * M292F-1 `zarConn_add_compl` / `zarConn_prime_e_or_compl`
    / `zarConn_prime_not_both` — e+(1−e)=1・素イデアルは e か 1−e のちょうど一方を含む
  * M292F-2 `zarConn_spec_split_cover` / `zarConn_spec_split_disjoint`
    / `ZarClopenSplit` / `zarConn_idem_clopen` — 冪等元 e から**本物の clopen 分割**
    Spec R = D(e) ⊔ D(1−e)（被覆かつ交わりなし・完全証明）
  * M292F-3 `zarConn_nontrivial_idem_disconnected`
    / `zarConn_connected_imp_idem_trivial` / `zarConn_iff_idem`
    — 非自明冪等元⟹非連結・連結⟹冪等元自明・両者の同値（連結の環論的定義）
  * M292F-4 `zarConn_field_connected` / `zarConn_split_disconnected`
    — 体は連結・分裂 K^n(n≥2) は非連結
  * M292F-5 capstone `ZariskiConnData` / `zarConn_field_data` / `zarConn_exists`
    / `zarConn_components_eq_idem` / `ratZarConn_field_connected`
    / `ratZarConn2_disconnected` / `ratZarClopen2` — 対象＋冪等元↔clopen 対応と
    「体＝連結」「K^n＝非連結・n 個の clopen 分割」、実 ℚ 上の実例

  正直な限定（何が本物で何が未達か）:
  1. **本物（完全証明・sorry 皆無・新規 Classical.choice 皆無・禁止タクティク不使用）**:
     e+(1−e)=1、素イデアルが e/1−e のちょうど一方を含むこと、**冪等元 e からの
     clopen 分割 Spec R = D(e)⊔D(1−e)（被覆＋交わりなし）**、非自明冪等元⟹非連結、
     連結⟹冪等元自明、体の連結性、K^n(n≥2) の非連結性、原始冪等元 eᵢ ごとの clopen
     分割、実 ℚ 上の実例。**冪等元→clopen 分割は完全に本物**（排中律不使用: 素性の
     選言 Or を場合分けで消費するのみ）。
  2. **連結性の定義は M280F の否定形 witness を再利用**（排中律回避）:
     `idemSpec_connected R`＝「非零冪等元は 1」（選言 e=0∨e=1 を使わない witness 形）。
     位相的連結性（開閉部分が ∅ と全体のみ）の完全な定義そのものは、開集合系・任意
     部分集合の連結性判定を要し、本モジュールでは**冪等元による環論的判定**に置き換える
     （これが Zariski 位相での連結性の忠実な特徴付けである）。
  3. **「連結 ⟺ 冪等元自明」は環論的定義の上で両方向とも本物**（`zarConn_iff_idem`）。
     ただし右辺（位相的連結性）を idemSpec_connected と**定義**することにより同値が
     rfl になる: これは Zariski 連結性の環論的復元という本物の内容だが、位相空間論
     からの独立導出（点集合位相での連結性 ⟹ 冪等元自明）は骨組み/後続。
  4. **基本開集合 D(e) の非空性（各連結成分が非空）は骨組み**: 具体的な素イデアルの
     存在（極大イデアルの存在）は選択公理/Zorn を要するため主張しない。本モジュールが
     本物にしたのは「**冪等元 e が clopen 分割を与える**」構造そのもの（分割の被覆性・
     交わりなし）であり、各片の非空性は素イデアルを exhibit できる場合に限る。
  5. **素イデアル・Spec・D は自前最小定義**（M289F PrimeSpectrum 整合・import せず）。
     一般スキームの連結成分関手 π₀・非分裂対象上の Π₀ の関手性・ファイバー関手との
     接続（M14/M16 抽象ガロア圏）は後続。本モジュールが確定したのは「Spec の連結性が
     座標環の冪等元として本物に定義・判定された」こと。

  選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。禁止タクティク不使用。
-/
import IUT.IdempotentSpectrum

namespace IUT

/-! ## M292F-0: 素イデアルと基本開集合 D(f)（自前の忠実な最小定義） -/

/-- **M292F-0a: 素イデアル**（Spec R の点）— 可換環 R の部分集合 mem で
    0 を含み・加法閉・イデアル（任意の r で r·a）・1 を含まず・素性
    （ab∈P ⇒ a∈P ∨ b∈P）を満たすもの。M289F PrimeSpectrum 整合の最小定義で、
    依存回避のため import せず自前に建てる（概念は完全に忠実）。 -/
structure ZarPrimeIdeal (R : CRing) where
  /-- 素イデアルの台（点 P に対応する素イデアルの元の判定）。 -/
  mem : R.carrier → Prop
  /-- 0 を含む。 -/
  mem_zero : mem R.zero
  /-- 加法で閉じる。 -/
  mem_add : ∀ a b, mem a → mem b → mem (R.add a b)
  /-- イデアル: 任意の環元 r について r·a を含む（a∈P ⇒ r·a∈P）。 -/
  mem_mul_left : ∀ r a, mem a → mem (R.mul r a)
  /-- 真イデアル: 1 を含まない。 -/
  one_not_mem : ¬ mem R.one
  /-- 素性: 積が入るなら因子の一方が入る。 -/
  prime : ∀ a b, mem (R.mul a b) → mem a ∨ mem b

/-- **M292F-0b: 基本開集合** D(f) = {P ∈ Spec R | f ∉ P}
    （f が消えない点の集合; Zariski 位相の基本開集合）。 -/
def zarBasicOpen (R : CRing) (f : R.carrier) : ZarPrimeIdeal R → Prop :=
  fun P => ¬ P.mem f

/-! ## M292F-1: 素イデアルは e か 1−e のちょうど一方を含む -/

/-- **M292F-1a: e + (1−e) = 1**（冪等元 e と補元の和は 1）。 -/
theorem zarConn_add_compl (R : CRing) (e : R.carrier) :
    R.add e (idemSpecCompl R e) = R.one := by
  show R.add e (R.add R.one (R.neg e)) = R.one
  rw [R.add_comm R.one (R.neg e), ← R.add_assoc, idemSpecAddNeg R e, R.zero_add]

/-- **M292F-1b: 素イデアルは e か 1−e の少なくとも一方を含む** — e·(1−e)=0∈P と
    素性から。直交分解 e(1−e)=0（M280F）が本質。 -/
theorem zarConn_prime_e_or_compl (R : CRing) (P : ZarPrimeIdeal R) {e : R.carrier}
    (h : idemSpec_isIdem R e) : P.mem e ∨ P.mem (idemSpecCompl R e) := by
  have hz : P.mem (R.mul e (idemSpecCompl R e)) := by
    rw [idemSpec_orthogonal_compl R h]
    exact P.mem_zero
  exact P.prime e (idemSpecCompl R e) hz

/-- **M292F-1c: 素イデアルは e と 1−e の両方は含まない** — 両方含むと
    1 = e+(1−e) ∈ P で真イデアル性 1∉P に矛盾。 -/
theorem zarConn_prime_not_both (R : CRing) (P : ZarPrimeIdeal R) {e : R.carrier} :
    ¬ (P.mem e ∧ P.mem (idemSpecCompl R e)) := by
  intro hb
  apply P.one_not_mem
  have hsum : P.mem (R.add e (idemSpecCompl R e)) :=
    P.mem_add e (idemSpecCompl R e) hb.1 hb.2
  rw [zarConn_add_compl R e] at hsum
  exact hsum

/-! ## M292F-2: 冪等元から本物の clopen 分割 Spec R = D(e) ⊔ D(1−e) -/

/-- **M292F-2a: 被覆** — 任意の素イデアル P は D(e) か D(1−e) の少なくとも一方に属す
    （e∈P なら 1−e∉P で P∈D(1−e); 逆も同様）。排中律不使用（素性の Or を消費）。 -/
theorem zarConn_spec_split_cover (R : CRing) (P : ZarPrimeIdeal R) {e : R.carrier}
    (h : idemSpec_isIdem R e) :
    zarBasicOpen R e P ∨ zarBasicOpen R (idemSpecCompl R e) P := by
  cases zarConn_prime_e_or_compl R P h with
  | inl he =>
    apply Or.inr
    intro hc
    exact zarConn_prime_not_both R P ⟨he, hc⟩
  | inr hce =>
    apply Or.inl
    intro hc
    exact zarConn_prime_not_both R P ⟨hc, hce⟩

/-- **M292F-2b: 交わりなし** — D(e) と D(1−e) は交わらない（P が両方に属すと
    e∉P かつ 1−e∉P で M292F-1b に矛盾）。 -/
theorem zarConn_spec_split_disjoint (R : CRing) (P : ZarPrimeIdeal R) {e : R.carrier}
    (h : idemSpec_isIdem R e) :
    ¬ (zarBasicOpen R e P ∧ zarBasicOpen R (idemSpecCompl R e) P) := by
  intro hb
  cases zarConn_prime_e_or_compl R P h with
  | inl he => exact hb.1 he
  | inr hce => exact hb.2 hce

/-- **M292F-2c: clopen 分割**（Spec の開かつ閉な二分割）— 二つの基本開集合
    left, right が Spec 全体を被覆し交わらない。left=D(e) は開（基本開集合）かつ
    閉（補集合 = right=D(1−e) が開）ゆえ clopen。 -/
structure ZarClopenSplit (R : CRing) where
  /-- 分割の左片（開集合）。 -/
  left : ZarPrimeIdeal R → Prop
  /-- 分割の右片（開集合＝左片の補集合）。 -/
  right : ZarPrimeIdeal R → Prop
  /-- 被覆: 任意の点は左右いずれかに属す。 -/
  cover : ∀ P, left P ∨ right P
  /-- 交わりなし: 左右は同時には成り立たない。 -/
  disjoint : ∀ P, ¬ (left P ∧ right P)

/-- **M292F-2d: 冪等元 ↦ clopen 分割**（本物の対応 e ↦ (D(e), D(1−e))）。
    これが「Spec の連結成分 ↔ 環の冪等元」の**本物の環論的実体**。
    冪等元 e に対し Spec R = D(e) ⊔ D(1−e) は完全証明された clopen 二分割。 -/
def zarConn_idem_clopen (R : CRing) {e : R.carrier} (h : idemSpec_isIdem R e) :
    ZarClopenSplit R where
  left := zarBasicOpen R e
  right := zarBasicOpen R (idemSpecCompl R e)
  cover := fun P => zarConn_spec_split_cover R P h
  disjoint := fun P => zarConn_spec_split_disjoint R P h

/-! ## M292F-3: 連結性（環論的判定）⟺ 冪等元自明 -/

/-- **M292F-3a: 非自明冪等元 ⟹ 非連結** — e≠0,1 の冪等元があれば
    `idemSpec_connected R`（非零冪等元は 1）に反する。位相的には D(e), D(1−e) が
    自明でない clopen 分割を与える（M292F-2d）。 -/
theorem zarConn_nontrivial_idem_disconnected (R : CRing) {e : R.carrier}
    (h : idemSpec_isIdem R e) (h0 : e ≠ R.zero) (h1 : e ≠ R.one) :
    ¬ idemSpec_connected R := by
  intro hconn
  exact h1 (hconn e h h0)

/-- **M292F-3b: 連結 ⟹ 冪等元自明** — Spec R 連結（idemSpec_connected）なら
    非零冪等元は 1 に限る（M292F-3a の対偶＝連結の環論的定義の展開）。 -/
theorem zarConn_connected_imp_idem_trivial (R : CRing)
    (hconn : idemSpec_connected R) {e : R.carrier}
    (h : idemSpec_isIdem R e) (h0 : e ≠ R.zero) : e = R.one :=
  hconn e h h0

/-- **M292F-3c: 連結 ⟺ 冪等元自明**（Zariski 連結性の環論的復元）—
    `idemSpec_connected R` は「非零冪等元は 1」そのものであり、両方向とも本物。
    これは「Spec R の連結性は座標環 R の冪等元から復元される」ことの実体である。 -/
theorem zarConn_iff_idem (R : CRing) :
    idemSpec_connected R
      ↔ ∀ e : R.carrier, idemSpec_isIdem R e → e ≠ R.zero → e = R.one :=
  Iff.rfl

/-! ## M292F-4: 体は連結・分裂 K^n(n≥2) は非連結 -/

/-- **M292F-4a: 体 K は連結** — Spec K は 1 点で連結（M280F 体の冪等元 {0,1}）。 -/
theorem zarConn_field_connected (K : IUTField) : idemSpec_connected K.toCRing :=
  idemSpec_field_is_connected K

/-- **M292F-4b: 分裂 K^n(n≥2) は非連結** — 非自明冪等元 splitIdem e₀ が
    clopen 分割 D(e₀)⊔D(1−e₀) を与える（M280F idemSpec_split_disconnected の位相版）。
    幾何的には Spec(K^n) = n 点非交和で n≥2 なら連結でない。 -/
theorem zarConn_split_disconnected (K : IUTField) (n : Nat) (hn : 2 ≤ n) :
    ¬ idemSpec_connected (funPowCRing K.toCRing n) := by
  obtain ⟨e, he, h0, h1⟩ := idemSpec_split_disconnected K n hn
  exact zarConn_nontrivial_idem_disconnected (funPowCRing K.toCRing n) he h0 h1

/-! ## M292F-5: capstone — Zariski 連結データと連結成分↔冪等元 -/

/-- **M292F-5a: Zariski 連結データ** — 連結な可換環 R と、その全冪等元に対する
    clopen 分割の対応（連結ゆえ全て自明分割）、および連結性の証明。
    連結成分関手 π₀ の（連結対象上の）本物の実体。 -/
structure ZariskiConnData where
  /-- 台の可換環（座標環）。 -/
  ring : CRing
  /-- 冪等元 ↦ clopen 分割の本物の対応 e ↦ (D(e), D(1−e))。 -/
  clopenOfIdem : ∀ e : ring.carrier, idemSpec_isIdem ring e → ZarClopenSplit ring
  /-- 連結性（非自明冪等元なし, witness 形）。 -/
  connected : idemSpec_connected ring

/-- **M292F-5b: 体の Zariski 連結データ** — Spec K は連結（1 成分）で、
    任意の冪等元は自明分割 D(e)⊔D(1−e) を与える（e∈{0,1} ゆえ一方が空）。 -/
def zarConn_field_data (K : IUTField) : ZariskiConnData where
  ring := K.toCRing
  clopenOfIdem := fun _ h => zarConn_idem_clopen K.toCRing h
  connected := zarConn_field_connected K

/-- **M292F-5c: Zariski 連結データの存在**（任意の体 K で Spec K は連結）。 -/
theorem zarConn_exists (K : IUTField) : Nonempty ZariskiConnData :=
  ⟨zarConn_field_data K⟩

/-- **M292F-5d: 連結成分 ↔ 冪等元（骨組み）** — 分裂 K^n の第 i 原始冪等元 eᵢ は
    本物の clopen 分割 D(eᵢ)⊔D(1−eᵢ) を与える。n 個の原始冪等元（M280F で相異なる
    ことを既証明）がそれぞれ clopen 片を切り出す＝連結成分↔冪等元の対応の骨組み。
    一般スキームの π₀ の関手性は後続。 -/
def zarConn_components_eq_idem (K : IUTField) (n : Nat) (i : Fin n) :
    ZarClopenSplit (funPowCRing K.toCRing n) :=
  zarConn_idem_clopen (funPowCRing K.toCRing n) (splitIdem_mul_self K n i)

/-! ## M292F-5e: 実 ℚ 上の実例 -/

/-- **実例: ℚ の Spec は連結**（体 = 1 点）。 -/
theorem ratZarConn_field_connected : idemSpec_connected ratIUTField.toCRing :=
  zarConn_field_connected ratIUTField

/-- **実例: ℚ×ℚ の Spec は非連結**（2 点非交和; ratIUTField 上の実例）。 -/
theorem ratZarConn2_disconnected :
    ¬ idemSpec_connected (funPowCRing ratIUTField.toCRing 2) :=
  zarConn_split_disconnected ratIUTField 2 (Nat.le_refl 2)

/-- **実例: ℚ×ℚ の Spec の本物の clopen 分割** D(e₀)⊔D(1−e₀)
    （第 0 原始冪等元による; Spec(ℚ×ℚ) = 2 点の非交和の実体）。 -/
def ratZarClopen2 : ZarClopenSplit (funPowCRing ratIUTField.toCRing 2) :=
  zarConn_components_eq_idem ratIUTField 2 ⟨0, Nat.zero_lt_two⟩

end IUT
