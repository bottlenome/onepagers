/-
  IUT/PolyBezoutQ.lean — M270F（実 ℚ[X] 上の拡張ユークリッド互除法・
  Bezout 恒等式の構成エンジン）

  ── 分類 **[実]**（本物の先行建設。骨格でなく本物の証明・sorry 皆無・
  新規 Classical.choice 皆無）。

  **complete_pct 影響**: 柱A「実 Galois 理論／実 π₁^ét」の本物の先行建設。
  `SimpleExtension.lean`（M269F）の `quotField_of_bezout` は「割り切れない
  任意元 a が E と互いに素（∃ u v, u·E + v·a = 1）」という honest 仮説
  `SimpleExtData.bezout` を要求していた。本層はその **hBez を本物にする核**
  ——体係数多項式環 K[X]（実体 ℚ を含む一般 `Field268`）の上で、既存の
  本物の除法定理 `field_division_exists`（M268F）を**反復**して拡張
  ユークリッド互除法を回し、gcd と **本物の Bezout 恒等式 u·f + v·g = gcd**
  を構成的に（選択公理不使用・witness を各段で明示）与える。gcd が非零定数
  （単元）のとき 1 へ正規化して `∃ u v, u·f + v·g = 1` を得る補題まで積む。

  * M270F-1 `pbz_comb_sub` / `pbz_dvd_comb` / `pbz_sub_recover` /
    `pbz_scale_comb` — 一般可換環上の Bezout 用代数恒等式（組合せの差の
    係数、割り切れの合成、剰余復元、スカラー倍の分配）
  * M270F-2 `pbzBound_mono` — 有界性の単調性（次数上界の緩め）
  * M270F-3 `pbzDvd` / `pbzDvd_refl` — 多項式の割り切れ（d ∣ a := ∃c, a=c·d）
  * M270F-4 `pbzDivStep` — **互除法の 1 段（本丸その1）**: `field_division_exists`
    を 1 回使い w = q·g + r（deg r < deg g）を得、さらに剰余の 1 段 Bezout
    r = 1·w + (−q)·g を明示（次段への組合せ伝播の種）
  * M270F-5 `pbzExtGcdAux` — **拡張ユークリッド本体（本丸その2）**: fuel（=
    法多項式の先頭次数）に関する構造帰納で (a,b) の対を割り進め、gcd gg と
    その組合せ gg = s·f + t·g、および gg ∣ a・gg ∣ b（本物の最大公約性）を
    同時構成。各段で剰余の組合せ係数を `pbz_comb_sub` で更新し、割り切れを
    `pbz_dvd_comb` で上向き伝播する
  * M270F-6 `pbzBezout` — **Bezout 恒等式（頂点）**: f・g（g の先頭係数 ≠ 0）
    から gcd gg・係数 s,t を取り gg = s·f + t·g ∧ gg ∣ f ∧ gg ∣ g
  * M270F-7 `pbzBezout_one_of_unit` — **gcd が単元（非零定数 c）⟹ 1 の
    Bezout**: gg = psC c なら c⁻¹ 倍で ∃ u v, u·f + v·g = 1（→ hBez に直結）
  * M270F-8 `pbzRatField` / `pbzBezoutQ` — **実 ℚ への具体化**: `ratIUTField`
    を `Field268` として渡し、ℚ[X] 上の拡張ユークリッドを名指しで得る

  正直な限定（何が本物で何が honest 仮説か）:
   - **本物**: 一般 `Field268`（従って実 ℚ）係数の多項式環 K[X] 上で、除法の
     反復・剰余組合せの更新・割り切れの伝播・Bezout 恒等式 gg = s·f + t·g・
     gg が f,g の公約数であること（gg ∣ f ∧ gg ∣ g）は完全証明。ℚ への
     具体化 `pbzRatField`/`pbzBezoutQ` も本物（`ratIUTField` を土台）。
   - **honest 仮説（deferred）**: 拡張ユークリッドの停止・次数減少には、剰余
     多項式の**先頭係数の位置を見つける（または零判定する）オラクル**
     `hlead_oracle`（体の等号判定＝有限探索）を honest 仮説として受け取る。
     これは実体（ℚ 等の等号判定可能な体）では真だが、抽象 `Field268` 上
     では等号判定が無いため一般には成立せず、証明本体での Classical.choice
     禁止に触れないよう**仮説として明示**する（§4 準拠・消さない）。ℚ での
     `hlead_oracle` の充足（QRat の num=0 判定への帰着）は次スライス。
   - **hBez への接続（deferred）**: (i)「E 既約 ⟹ gcd(E,a) は非零定数（単元）」
     の既約性からの導出、(ii) PS 版 Bezout を `Poly`（部分型）版 hBez
     （`quotField_of_bezout` の型）へ包む plumbing は本層に含めない後続。
     本層は **gcd が単元なら Bezout=1** の正規化（M270F-7）まで到達し、
     既約性側は toy で誤魔化さず honest に次段へ回す。
   - 次数上界の witness は仮説（有界性）として受け取る（有限台性からの
     次数抽出は行わない）。complete_pct は未設定（本層はグラフメタ不更新）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.SimpleExtension
import IUT.Field

namespace IUT

/-! ## M270F-1: Bezout 用の一般可換環代数恒等式 -/

/-- **M270F-1a: 組合せの差** — (sp·F + tp·G) − q·(sc·F + tc·G)
    = (sp − q·sc)·F + (tp − q·tc)·G。拡張ユークリッドの係数更新の核。 -/
theorem pbz_comb_sub (P : CRing) (F G q sp tp sc tc : P.carrier) :
    P.add (P.add (P.mul sp F) (P.mul tp G))
      (P.neg (P.mul q (P.add (P.mul sc F) (P.mul tc G))))
    = P.add (P.mul (P.add sp (P.neg (P.mul q sc))) F)
        (P.mul (P.add tp (P.neg (P.mul q tc))) G) := by
  rw [P.left_distrib q (P.mul sc F) (P.mul tc G),
    CRing.neg_add_dist P (P.mul q (P.mul sc F)) (P.mul q (P.mul tc G)),
    ← P.mul_assoc q sc F, ← P.mul_assoc q tc G,
    ← CRing.neg_mul P (P.mul q sc) F, ← CRing.neg_mul P (P.mul q tc) G,
    CRing.right_distrib P sp (P.neg (P.mul q sc)) F,
    CRing.right_distrib P tp (P.neg (P.mul q tc)) G,
    CRing.add_add_add_comm P (P.mul sp F) (P.mul tp G)
      (P.mul (P.neg (P.mul q sc)) F) (P.mul (P.neg (P.mul q tc)) G)]

/-- **M270F-1b: 割り切れの合成** — q·(cb·d) + cr·d = (q·cb + cr)·d。
    a = q·b + r で b = cb·d, r = cr·d のとき a = (q·cb + cr)·d を与える。 -/
theorem pbz_dvd_comb (P : CRing) (q cb cr d : P.carrier) :
    P.add (P.mul q (P.mul cb d)) (P.mul cr d)
    = P.mul (P.add (P.mul q cb) cr) d := by
  rw [CRing.right_distrib P (P.mul q cb) cr d, P.mul_assoc q cb d]

/-- **M270F-1c: 剰余復元** — (x + r) + (−x) = r（r = w − q·g の代数）。 -/
theorem pbz_sub_recover (P : CRing) (x r : P.carrier) :
    P.add (P.add x r) (P.neg x) = r := by
  rw [P.add_comm x r, P.add_assoc r x (P.neg x), CRing.add_neg P x,
    CRing.add_zero P r]

/-- **M270F-1d: スカラー倍の分配** — (ic·s)·F + (ic·t)·G = ic·(s·F + t·G)。
    Bezout を単元 ic で正規化する際に使う。 -/
theorem pbz_scale_comb (P : CRing) (ic s t F G : P.carrier) :
    P.add (P.mul (P.mul ic s) F) (P.mul (P.mul ic t) G)
    = P.mul ic (P.add (P.mul s F) (P.mul t G)) := by
  rw [P.mul_assoc ic s F, P.mul_assoc ic t G,
    P.left_distrib ic (P.mul s F) (P.mul t G)]

/-! ## M270F-2: 有界性の単調性 -/

/-- **M270F-2: 有界性の単調性** — N で有界なら N ≤ M で M でも有界。 -/
theorem pbzBound_mono (R : CRing) {f : PS R} {N M : Nat}
    (h : IsPolyBounded R f N) (hNM : N ≤ M) : IsPolyBounded R f M :=
  fun i hi => h i (Nat.le_trans hNM hi)

/-! ## M270F-3: 多項式の割り切れ -/

/-- **M270F-3a: 割り切れ** d ∣ a := ∃ c, a = c·d。 -/
def pbzDvd (R : CRing) (d a : PS R) : Prop := ∃ c : PS R, a = psMul R c d

/-- **M270F-3b: 反射律** d ∣ d（c = 1）。 -/
theorem pbzDvd_refl (R : CRing) (d : PS R) : pbzDvd R d d :=
  ⟨psOne R, ((psRing R).one_mul d).symm⟩

/-! ## M270F-4: 互除法の 1 段 -/

/-- **定理 (M270F-4): 互除法の 1 段** — `field_division_exists` を 1 回使い
    w = q·g + r（deg r < deg g）を得、さらに剰余の 1 段 Bezout
    **r = 1·w + (−q)·g** を明示する。後者は拡張ユークリッドで剰余の
    組合せ係数を伝播させる種（本層は係数を直接更新するので参考実装だが、
    「1 段の除法＋次数減少＋組合せ」を名指しで確定する）。 -/
theorem pbzDivStep (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    (g : PS R) (m : Nat) (hg : IsPolyBounded R g (m + 1)) (hlead : g m ≠ R.zero)
    (w : PS R) (N : Nat) (hw : IsPolyBounded R w (N + m)) :
    ∃ (q r : PS R), IsPolyBounded R q (N + 1) ∧ IsPolyBounded R r m ∧
      w = psAdd R (psMul R q g) r ∧
      r = psAdd R (psMul R (psOne R) w) (psMul R (psNeg R q) g) := by
  obtain ⟨q, r, hq, hr, hdiv⟩ :=
    field_division_exists R invf hinv g m hg hlead N w hw
  have hw_eq : w = psAdd R (psMul R q g) r := funext hdiv
  refine ⟨q, r, hq, hr, hw_eq, ?_⟩
  rw [show psMul R (psOne R) w = w from (psRing R).one_mul w,
    show psMul R (psNeg R q) g = psNeg R (psMul R q g)
      from CRing.neg_mul (psRing R) q g, hw_eq]
  exact (pbz_sub_recover (psRing R) (psMul R q g) r).symm

/-! ## M270F-5: 拡張ユークリッド本体 -/

/-- **定理 (M270F-5): 拡張ユークリッド互除法（本体）** — 固定した f, g に
    対し、対 (a, b)（各々 f,g の既知の組合せ）を b で割り進め、gcd gg と
    その組合せ **gg = s·f + t·g**、および **gg ∣ a ∧ gg ∣ b** を構成する。
    停止は fuel（= 現在の除数 b の先頭次数の上界）に関する構造帰納で保証し、
    各段で `field_division_exists`（M268F 除法）を 1 回適用、剰余の組合せ
    係数を `pbz_comb_sub` で更新、割り切れを `pbz_dvd_comb` で上向き伝播する。
    剰余の先頭次数の探索（または零判定）は honest 仮説 `hlead_oracle`
    （実体では真・抽象体では等号判定を要する）として受け取る。 -/
theorem pbzExtGcdAux (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    (hlead_oracle : ∀ (p : PS R) (n : Nat), IsPolyBounded R p n →
      (∀ i, p i = R.zero) ∨
      (∃ d, p d ≠ R.zero ∧ IsPolyBounded R p (d + 1)))
    (f g : PS R) :
    ∀ (fuel : Nat) (a b sa ta sb tb : PS R) (Na mb : Nat),
      IsPolyBounded R a Na → IsPolyBounded R b (mb + 1) → b mb ≠ R.zero →
      mb < fuel →
      a = psAdd R (psMul R sa f) (psMul R ta g) →
      b = psAdd R (psMul R sb f) (psMul R tb g) →
      ∃ (s t gg : PS R) (mg : Nat),
        gg = psAdd R (psMul R s f) (psMul R t g) ∧
        IsPolyBounded R gg (mg + 1) ∧ gg mg ≠ R.zero ∧
        pbzDvd R gg a ∧ pbzDvd R gg b := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b sa ta sb tb Na mb _ _ _ hfuel _ _
    exact absurd hfuel (Nat.not_lt_zero mb)
  | succ k ih =>
    intro a b sa ta sb tb Na mb hNa hb hbl hfuel hac hbc
    have haN : IsPolyBounded R a (Na + mb) :=
      pbzBound_mono R hNa (Nat.le_add_right Na mb)
    obtain ⟨q, r, hq, hr', hdiv⟩ :=
      field_division_exists R invf hinv b mb hb hbl Na a haN
    have ha : a = psAdd R (psMul R q b) r := funext hdiv
    have hrc : r = psAdd R (psMul R (psAdd R sa (psNeg R (psMul R q sb))) f)
        (psMul R (psAdd R ta (psNeg R (psMul R q tb))) g) := by
      have hr_eq : r = psAdd R a (psNeg R (psMul R q b)) := by
        rw [ha]
        exact (pbz_sub_recover (psRing R) (psMul R q b) r).symm
      rw [hr_eq, hac, hbc]
      exact pbz_comb_sub (psRing R) f g q sa ta sb tb
    cases hlead_oracle r mb hr' with
    | inl hrz =>
      refine ⟨sb, tb, b, mb, hbc, hb, hbl, ⟨q, ?_⟩, pbzDvd_refl R b⟩
      have hrz' : r = psZero R := by
        funext i
        exact hrz i
      rw [ha, hrz']
      exact CRing.add_zero (psRing R) (psMul R q b)
    | inr hex =>
      obtain ⟨dr, hdr_ne, hdr_bound⟩ := hex
      have hdrlt : dr < mb := by
        cases Nat.lt_or_ge dr mb with
        | inl h => exact h
        | inr h => exact absurd (hr' dr h) hdr_ne
      have hdrk : dr < k := by omega
      obtain ⟨s, t, gg, mg, hgc, hgbd, hgld, hdvd_gb, hdvd_gr⟩ :=
        ih b r sb tb (psAdd R sa (psNeg R (psMul R q sb)))
          (psAdd R ta (psNeg R (psMul R q tb))) (mb + 1) dr hb hdr_bound
          hdr_ne hdrk hbc hrc
      refine ⟨s, t, gg, mg, hgc, hgbd, hgld, ?_, hdvd_gb⟩
      obtain ⟨cb, hcb⟩ := hdvd_gb
      obtain ⟨cr, hcr⟩ := hdvd_gr
      refine ⟨psAdd R (psMul R q cb) cr, ?_⟩
      rw [ha, hcb, hcr]
      exact pbz_dvd_comb (psRing R) q cb cr gg

/-! ## M270F-6: Bezout 恒等式（頂点） -/

/-- **定理 (M270F-6): Bezout 恒等式** — f・g（g の先頭係数 ≠ 0）から
    gcd gg と係数 s, t を取り、**gg = s·f + t·g ∧ gg ∣ f ∧ gg ∣ g** を得る。
    初期対 (f, g) を組合せ f = 1·f + 0·g, g = 0·f + 1·g で与え、fuel =
    deg g + 1 で `pbzExtGcdAux` を回す。 -/
theorem pbzBezout (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    (hlead_oracle : ∀ (p : PS R) (n : Nat), IsPolyBounded R p n →
      (∀ i, p i = R.zero) ∨
      (∃ d, p d ≠ R.zero ∧ IsPolyBounded R p (d + 1)))
    (f g : PS R) (Nf mg0 : Nat)
    (hf : IsPolyBounded R f Nf) (hg : IsPolyBounded R g (mg0 + 1))
    (hgl : g mg0 ≠ R.zero) :
    ∃ (s t gg : PS R) (mg : Nat),
      gg = psAdd R (psMul R s f) (psMul R t g) ∧
      IsPolyBounded R gg (mg + 1) ∧ gg mg ≠ R.zero ∧
      pbzDvd R gg f ∧ pbzDvd R gg g := by
  have hfc : f = psAdd R (psMul R (psOne R) f) (psMul R (psZero R) g) := by
    rw [show psMul R (psOne R) f = f from (psRing R).one_mul f,
      show psMul R (psZero R) g = psZero R from CRing.zero_mul (psRing R) g]
    exact (CRing.add_zero (psRing R) f).symm
  have hgc : g = psAdd R (psMul R (psZero R) f) (psMul R (psOne R) g) := by
    rw [show psMul R (psZero R) f = psZero R from CRing.zero_mul (psRing R) f,
      show psMul R (psOne R) g = g from (psRing R).one_mul g]
    exact ((psRing R).zero_add g).symm
  exact pbzExtGcdAux R invf hinv hlead_oracle f g (mg0 + 1) f g
    (psOne R) (psZero R) (psZero R) (psOne R) Nf mg0 hf hg hgl
    (Nat.lt_succ_self mg0) hfc hgc

/-! ## M270F-7: gcd が単元 ⟹ Bezout = 1 -/

/-- **定理 (M270F-7): 単元正規化** — Bezout gg = s·f + t·g で gg が非零定数
    c（単元）なら、両辺に c⁻¹ を掛けて **∃ u v, u·f + v·g = 1**。
    u = c⁻¹·s, v = c⁻¹·t。c⁻¹·gg = c⁻¹·(c) = 1（定数の環準同型 psC と
    `mul_inv_cancel` を使用）。既約 E で E∤a のとき gcd(E,a) が単元と分かれば
    これがそのまま `quotField_of_bezout` の hBez を与える形。 -/
theorem pbzBezout_one_of_unit (R : CRing) (invf : R.carrier → R.carrier)
    (hinv : ∀ a, a ≠ R.zero → R.mul a (invf a) = R.one)
    (f g s t gg : PS R) (c : R.carrier) (hc : c ≠ R.zero)
    (hcomb : gg = psAdd R (psMul R s f) (psMul R t g))
    (hunit : gg = psC R c) :
    ∃ (u v : PS R),
      psAdd R (psMul R u f) (psMul R v g) = psOne R := by
  refine ⟨psMul R (psC R (invf c)) s, psMul R (psC R (invf c)) t, ?_⟩
  have h1 : psAdd R (psMul R (psMul R (psC R (invf c)) s) f)
        (psMul R (psMul R (psC R (invf c)) t) g)
      = psMul R (psC R (invf c)) (psAdd R (psMul R s f) (psMul R t g)) :=
    pbz_scale_comb (psRing R) (psC R (invf c)) s t f g
  have h2 : psAdd R (psMul R s f) (psMul R t g) = psC R c :=
    hcomb.symm.trans hunit
  have h3 : psMul R (psC R (invf c)) (psC R c) = psC R (R.mul (invf c) c) :=
    ((psConstHom R).map_mul (invf c) c).symm
  have h4 : R.mul (invf c) c = R.one := by
    rw [R.mul_comm]
    exact hinv c hc
  rw [h1, h2, h3]
  exact congrArg (psC R) h4

/-! ## M270F-8: 実 ℚ への具体化 -/

/-- **M270F-8a: 実体 ℚ を `Field268` として渡す** — `ratIUTField`（M264F・
    本物の体）の逆元と逆元公理をそのまま `Field268` の invf / mul_inv_cancel
    へ。以降 ℚ[X] 上の拡張ユークリッドが名指しで使える。 -/
def pbzRatField : Field268 where
  ring := ratIUTField.toCRing
  invf := ratIUTField.inv
  mul_inv_cancel := ratIUTField.mul_inv_cancel

/-- **定理 (M270F-8b): 実 ℚ[X] の Bezout** — `pbzBezout` を実体 ℚ
    （`ratIUTField`）へ具体化。先頭係数探索オラクル `hlead_oracle` は
    honest 仮説として残る（ℚ の等号判定＝分子零判定への帰着は次スライス）。 -/
theorem pbzBezoutQ
    (hlead_oracle : ∀ (p : PS ratIUTField.toCRing) (n : Nat),
      IsPolyBounded ratIUTField.toCRing p n →
      (∀ i, p i = ratIUTField.toCRing.zero) ∨
      (∃ d, p d ≠ ratIUTField.toCRing.zero ∧
        IsPolyBounded ratIUTField.toCRing p (d + 1)))
    (f g : PS ratIUTField.toCRing) (Nf mg0 : Nat)
    (hf : IsPolyBounded ratIUTField.toCRing f Nf)
    (hg : IsPolyBounded ratIUTField.toCRing g (mg0 + 1))
    (hgl : g mg0 ≠ ratIUTField.toCRing.zero) :
    ∃ (s t gg : PS ratIUTField.toCRing) (mg : Nat),
      gg = psAdd ratIUTField.toCRing (psMul ratIUTField.toCRing s f)
        (psMul ratIUTField.toCRing t g) ∧
      IsPolyBounded ratIUTField.toCRing gg (mg + 1) ∧
      gg mg ≠ ratIUTField.toCRing.zero ∧
      pbzDvd ratIUTField.toCRing gg f ∧ pbzDvd ratIUTField.toCRing gg g :=
  pbzBezout ratIUTField.toCRing ratIUTField.inv ratIUTField.mul_inv_cancel
    hlead_oracle f g Nf mg0 hf hg hgl

end IUT
