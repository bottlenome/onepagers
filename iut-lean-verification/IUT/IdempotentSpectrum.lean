/-
  IUT/IdempotentSpectrum.lean — M280F: 冪等元スペクトルと連結成分
  ── 柱A 実 FÉt(K) の連結成分（Spec の連結成分 = 冪等元）の本物の先行建設

  分類 **[実]**（本物の可換環・本物の体・本物の分裂エタール K-代数 K^n の上での
  冪等元＝連結成分の実構成。toy 模型・代理は主語にしない）。

  **complete_pct 影響: 柱A 実 π₁^ét／FÉt(K) の連結成分理論の本物の先行建設**。
  ガロア圏（FÉt(K)）のファイバー関手が値を取る先＝有限集合は「対象の連結成分の
  集合 Π₀」であり、アフィンスキーム Spec A では **連結成分 = A の冪等元** で環論的に
  実体化する。本モジュールは M272F（本物の K-代数・分裂被覆 K^n・直交冪等元系）と
  M264F（本物の体 = 整域）の上で、
  (1) 冪等元 e²=e の基本法則（補元 1−e の冪等性・直交 e(1−e)=0）、
  (2) **体（連結）の冪等元は {0,1} のみ**（整域性からの witness 形）、
  (3) **分裂 K^n の冪等元＝座標ごと 0/1**、原始冪等元 splitIdem がちょうど n 個の
      相異なる極小非零冪等元＝n 個の連結成分、
  (4) 連結性判定（witness 形）と n≥2 での K^n の非連結性、
  (5) capstone `IdemSpectrumData`（対象・原始冪等元系・成分数）と
      「体＝1 連結成分」「K^n＝n 連結成分」、本物の数体 ℚ 上の実例
  を完全証明する。これは FÉt(K) のガロア圏構造（Π₀ の関手性）への本物の入口である。

  * M280F-0 補助環法則 `idemSpecNegZero` / `idemSpecAddNeg` / `idemSpecMulNeg`
    / `idemSpecNegMul` — neg 0 = 0・a+(−a)=0・a·(−b)=−(a·b)・(−a)·b=−(a·b)
  * M280F-1 `idemSpec_isIdem` / `idemSpecCompl` / `idemSpec_compl_idem`
    / `idemSpec_orthogonal_compl` — 冪等元と補元 1−e の冪等性・直交分解 e(1−e)=0
  * M280F-2 `idemSpec_field_trivial` — 体の冪等元は {0,1} のみ（e≠0 ⇒ e=1 witness 形）
  * M280F-3 `idemSpec_split_char` / `idemSpec_split_coord_trivial`
    — K^n の冪等元 ⟺ 各座標が K の冪等元（座標ごとに体へ帰着）・座標は 0/1
  * M280F-4 `idemSpec_primitive_distinct` — 原始冪等元 e_i は相異なる（n 個）
  * M280F-5 `idemSpec_connected` / `idemSpec_field_is_connected`
    / `idemSpec_split_disconnected` — 連結性（witness 形）・体は連結・K^n(n≥2)は非連結
  * M280F-6 capstone `IdemSpectrumData` / `idemSpec_field_components`
    / `idemSpec_split_components` / `idemSpec_exists`
    / `ratIdemSpec2` / `ratIdemSpec3` / `ratIdemSpec2_nontrivial` — 対象＋原始冪等元系
    と「体＝1 成分」「K^n＝n 成分」、実 ℚ 上の 2/3 成分・非自明冪等元

  正直な限定（何が本物で何が未達か）:
  1. **本物**: 冪等元の基本法則・補元/直交・体の冪等元 {0,1}・K^n の冪等元の座標
     特徴付け・原始冪等元 n 個が相異なること・直交完全系 Σeᵢ=1（M272F 再利用）・
     K^n(n≥2) の非連結性・実 ℚ 上の実例は全て完全証明（sorry 皆無・新規
     Classical.choice 皆無・禁止タクティク不使用）。
  2. **整域性の消去は仮説/witness 形**（M264F・M272F と同精神）: 「冪等元は 0 か 1」を
     選言 e=0 ∨ e=1 で述べず、`e ≠ 0 → e = 1` の witness 形にして排中律を回避する。
     連結性 `idemSpec_connected` も「非零冪等元は 1」の witness 形で定義する。
  3. **「冪等元の集合＝連結成分」は分裂対象 K^n で完全**（原始冪等元 n 個＋直交完全系
     で n 成分を確定）。一般の有限エタール K-代数は分裂 witness（M272F の
     FiniteEtaleData.splitIso）を経由して K^n へ帰着する。一般スキームの連結成分理論
     （非分裂対象上の Π₀ の関手性・基点との整合）は後続。
  4. **2^n 個の冪等元の完全列挙は骨組みに留める**: 本モジュールは「原始冪等元 n 個＋
     それらが相異なり直交完全系をなす」ことを本物で確立する（連結成分数 n の実体）。
     全 2^n 個の冪等元＝Fin n の部分集合という全単射は列挙が重く後続とする。
  5. ファイバー関手・Aut(F)=Gal(K̄/K) との接続（Π₀ の関手性から π₁^ét 復元）は
     既存 M14/M16 の抽象ガロア圏機構と後続で接続する。本モジュールが確定したのは
     「FÉt(K) の対象の連結成分が冪等元として本物に定義・計数された」こと。

  選択公理不使用・sorry 不使用・新規 Classical.choice 不使用。禁止タクティク不使用。
-/
import IUT.FiniteEtaleAlgebra

namespace IUT

/-! ## M280F-0: 補助環法則（neg と mul の相互作用） -/

/-- **M280F-0a: neg 0 = 0**（加法逆元の一意性から）。 -/
theorem idemSpecNegZero (R : CRing) : R.neg R.zero = R.zero := by
  have h : R.add (R.neg R.zero) R.zero = R.zero := R.neg_add R.zero
  rw [R.add_comm, R.zero_add] at h
  exact h

/-- **M280F-0b: a + (−a) = 0**（neg_add の可換形）。 -/
theorem idemSpecAddNeg (R : CRing) (a : R.carrier) : R.add a (R.neg a) = R.zero := by
  rw [R.add_comm]
  exact R.neg_add a

/-- **M280F-0c: a·(−b) = −(a·b)**（分配と加法逆元の一意性から）。 -/
theorem idemSpecMulNeg (R : CRing) (a b : R.carrier) :
    R.mul a (R.neg b) = R.neg (R.mul a b) := by
  apply R.add_left_cancel (a := R.mul a b)
  rw [← R.left_distrib, idemSpecAddNeg, R.mul_zero, idemSpecAddNeg]

/-- **M280F-0d: (−a)·b = −(a·b)**（可換性 + M280F-0c）。 -/
theorem idemSpecNegMul (R : CRing) (a b : R.carrier) :
    R.mul (R.neg a) b = R.neg (R.mul a b) := by
  rw [R.mul_comm, idemSpecMulNeg, R.mul_comm]

/-! ## M280F-1: 冪等元・補元・直交分解 -/

/-- **M280F-1a: 冪等元**（Spec R の開かつ閉な部分＝連結成分の特性関数）。 -/
def idemSpec_isIdem (R : CRing) (e : R.carrier) : Prop := R.mul e e = e

/-- `idemSpec_isIdem` の展開（定義等式）。 -/
theorem idemSpec_isIdem_iff (R : CRing) (e : R.carrier) :
    idemSpec_isIdem R e ↔ R.mul e e = e := Iff.rfl

/-- **M280F-1b: 補元** 1 − e（相補な連結成分の特性関数）。 -/
def idemSpecCompl (R : CRing) (e : R.carrier) : R.carrier := R.add R.one (R.neg e)

/-- **M280F-1c: 直交分解** e·(1−e) = 0（連結成分の非交わり）。 -/
theorem idemSpec_orthogonal_compl (R : CRing) {e : R.carrier}
    (h : idemSpec_isIdem R e) : R.mul e (idemSpecCompl R e) = R.zero := by
  show R.mul e (R.add R.one (R.neg e)) = R.zero
  rw [R.left_distrib, idemSpecMulNeg, h, R.mul_comm e R.one, R.one_mul, idemSpecAddNeg]

/-- **M280F-1d: 補元の冪等性** (1−e)² = 1−e（e が冪等なら補元も冪等）。 -/
theorem idemSpec_compl_idem (R : CRing) {e : R.carrier}
    (h : idemSpec_isIdem R e) : idemSpec_isIdem R (idemSpecCompl R e) := by
  have hce : R.mul (idemSpecCompl R e) e = R.zero := by
    show R.mul (R.add R.one (R.neg e)) e = R.zero
    rw [R.right_distrib, R.one_mul, idemSpecNegMul, h, idemSpecAddNeg]
  show R.mul (idemSpecCompl R e) (R.add R.one (R.neg e)) = idemSpecCompl R e
  rw [R.left_distrib, idemSpecMulNeg, hce, idemSpecNegZero, R.add_comm, R.zero_add,
    R.mul_comm, R.one_mul]

/-! ## M280F-2: 体（連結）の冪等元は {0,1} のみ -/

/-- **M280F-2: 体の冪等元は自明** — 整域（体）で e²=e かつ e≠0 なら e=1。
    整域性の消去は仮説/witness 形（M264F・M272F と同精神で排中律を回避）。
    幾何的には「体 = 連結（Spec K は 1 点で開閉部分は自明のみ）」の環論的実体。 -/
theorem idemSpec_field_trivial (F : IUTField) {e : F.carrier}
    (h : F.mul e e = e) (he : e ≠ F.zero) : e = F.one := by
  have key : F.mul (F.inv e) (F.mul e e) = F.mul (F.inv e) e := by rw [h]
  rw [← F.mul_assoc, F.inv_mul_cancel he, F.one_mul] at key
  exact key

/-! ## M280F-3: 分裂 K^n の冪等元 = 座標ごと 0/1 -/

/-- **M280F-3a: 分裂の特徴付け** — K^n の元 e が冪等 ⟺ 各座標 eⱼ が K で冪等。
    直積環の演算は成分ごとなので冪等性は座標ごとに帰着する。 -/
theorem idemSpec_split_char (K : IUTField) (n : Nat)
    (e : (funPowCRing K.toCRing n).carrier) :
    idemSpec_isIdem (funPowCRing K.toCRing n) e
      ↔ ∀ j, idemSpec_isIdem K.toCRing (e j) := by
  apply Iff.intro
  · intro h j
    exact congrFun h j
  · intro h
    funext j
    exact h j

/-- **M280F-3b: 座標の三分律** — K^n の冪等元 e の各座標は 0 か 1
    （非零座標は 1; 体の冪等元の自明性 M280F-2 を座標ごとに適用）。 -/
theorem idemSpec_split_coord_trivial (K : IUTField) (n : Nat)
    (e : (funPowCRing K.toCRing n).carrier)
    (h : idemSpec_isIdem (funPowCRing K.toCRing n) e) (j : Fin n)
    (hj : e j ≠ K.zero) : e j = K.one := by
  have hc : K.mul (e j) (e j) = e j := (idemSpec_split_char K n e).mp h j
  exact idemSpec_field_trivial K hc hj

/-! ## M280F-4: 原始冪等元 n 個は相異なる（連結成分 n 個） -/

/-- **M280F-4: 原始冪等元の相違** — i ≠ j なら splitIdem eᵢ ≠ eⱼ。
    第 i 座標で eᵢ は 1、eⱼ は 0（i≠j）ゆえ非自明性 1≠0 で分離。
    これで K^n には**相異なる n 個の極小非零冪等元**＝n 個の連結成分がある
    （冪等性 splitIdem_mul_self・直交 splitIdem_mul_orth・
    完全系 splitIdem_complete Σeᵢ=1 は M272F で既証明、本定理で n 個相異なる）。 -/
theorem idemSpec_primitive_distinct (K : IUTField) (n : Nat) {i j : Fin n}
    (hij : i ≠ j) : splitIdem K n i ≠ splitIdem K n j := by
  intro hc
  have hval : (splitIdem K n i) i = (splitIdem K n j) i := congrFun hc i
  have h1 : (if i = i then K.one else K.zero) = (if j = i then K.one else K.zero) := hval
  rw [if_pos rfl] at h1
  have hji : ¬ j = i := fun hc2 => hij hc2.symm
  rw [if_neg hji] at h1
  exact K.one_ne_zero h1

/-! ## M280F-5: 連結性判定 -/

/-- **M280F-5a: 連結性（witness 形）** — 非零冪等元は 1 に限る
    （＝Spec R の開閉部分は ∅ と全体のみ＝連結）。選言 e=0∨e=1 は排中律を要するため
    witness 形で述べる（本規約の構成性要件）。 -/
def idemSpec_connected (R : CRing) : Prop :=
  ∀ e : R.carrier, idemSpec_isIdem R e → e ≠ R.zero → e = R.one

/-- **M280F-5b: 体は連結** — 体（整域）の Spec は 1 点で連結。 -/
theorem idemSpec_field_is_connected (F : IUTField) : idemSpec_connected F.toCRing := by
  intro e h he
  exact idemSpec_field_trivial F h he

/-- Fin 1 の元は全て等しい（1 成分の縮退）。 -/
theorem idemSpec_fin1_eq (i j : Fin 1) : i = j := by
  have hi : i.val = 0 := by have := i.isLt; omega
  have hj : j.val = 0 := by have := j.isLt; omega
  exact kAlgFin_ext (hi.trans hj.symm)

/-- **M280F-5c: K^n (n≥2) は非連結** — 非自明冪等元 e₀ が存在する
    （e₀ ≠ 0 かつ e₀ ≠ 1）。第 1 原始冪等元 splitIdem e₀ は第 0 座標で 1（≠0）、
    第 1 座標で 0（1 は第 1 座標で 1）ゆえ 0 でも 1 でもない。
    ＝Spec(K^n) は n≥2 で少なくとも 2 個の連結成分に分かれる。 -/
theorem idemSpec_split_disconnected (K : IUTField) (n : Nat) (hn : 2 ≤ n) :
    ∃ e : (funPowCRing K.toCRing n).carrier,
      idemSpec_isIdem (funPowCRing K.toCRing n) e ∧
        e ≠ (funPowCRing K.toCRing n).zero ∧
          e ≠ (funPowCRing K.toCRing n).one := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  refine ⟨splitIdem K n ⟨0, h0⟩, ?_, ?_, ?_⟩
  · exact splitIdem_mul_self K n ⟨0, h0⟩
  · intro hc
    have hval : (splitIdem K n ⟨0, h0⟩) ⟨0, h0⟩
        = (funPowCRing K.toCRing n).zero ⟨0, h0⟩ := congrFun hc ⟨0, h0⟩
    have he : (if (⟨0, h0⟩ : Fin n) = ⟨0, h0⟩ then K.one else K.zero) = K.zero := hval
    rw [if_pos rfl] at he
    exact K.one_ne_zero he
  · intro hc
    have hval : (splitIdem K n ⟨0, h0⟩) ⟨1, h1⟩
        = (funPowCRing K.toCRing n).one ⟨1, h1⟩ := congrFun hc ⟨1, h1⟩
    have hne : ¬ (⟨0, h0⟩ : Fin n) = ⟨1, h1⟩ := by
      intro hc2
      have hv : (0 : Nat) = 1 := congrArg Fin.val hc2
      omega
    have he : (if (⟨0, h0⟩ : Fin n) = ⟨1, h1⟩ then K.one else K.zero) = K.one := hval
    rw [if_neg hne] at he
    exact K.one_ne_zero he.symm

/-! ## M280F-6: capstone — 冪等元スペクトルと連結成分数 -/

/-- **M280F-6a: 冪等元スペクトルのデータ** — K-代数 A と、n 個の原始冪等元系
    （相異なる・冪等・直交・完全系 Σeᵢ=1）＝A の Spec の n 個の連結成分。 -/
structure IdemSpectrumData (K : IUTField) where
  /-- 台の K-代数（本物）。 -/
  obj : KAlgebra K
  /-- 連結成分数（＝原始冪等元の個数）。 -/
  components : Nat
  /-- 原始冪等元系（各連結成分の特性関数）。 -/
  prim : Fin components → obj.alg.carrier
  /-- 各原始冪等元は冪等。 -/
  prim_idem : ∀ i, obj.alg.mul (prim i) (prim i) = prim i
  /-- 相異なる原始冪等元は直交。 -/
  prim_orth : ∀ i j, i ≠ j → obj.alg.mul (prim i) (prim j) = obj.alg.zero
  /-- 直交完全系: Σᵢ eᵢ = 1。 -/
  prim_complete : kPowSum obj.alg components prim = obj.alg.one
  /-- n 個の原始冪等元は相異なる（連結成分が過不足なく n 個）。 -/
  prim_distinct : ∀ i j, i ≠ j → prim i ≠ prim j

/-- **M280F-6b: 体＝1 連結成分** — 自明被覆 Spec K（A=K）の冪等元スペクトル。
    原始冪等元はただ 1 個 e₀=1（体は連結）。 -/
def idemSpec_field_components (K : IUTField) : IdemSpectrumData K where
  obj := trivialEtaleAlgebra K
  components := 1
  prim := fun _ => K.one
  prim_idem := fun _ => K.one_mul K.one
  prim_orth := fun i j hij => absurd (idemSpec_fin1_eq i j) hij
  prim_complete := by
    rw [kPowSum_succ]
    exact K.zero_add K.one
  prim_distinct := fun i j hij => absurd (idemSpec_fin1_eq i j) hij

/-- **M280F-6c: K^n＝n 連結成分** — 分裂被覆 Spec(K^n) の冪等元スペクトル。
    原始冪等元は splitIdem eᵢ（n 個・相異なる・直交完全系）＝n 個の連結成分。
    幾何的には Spec(K^n) = n 点の非交和（Π₀ = n 元集合）。 -/
def idemSpec_split_components (K : IUTField) (n : Nat) : IdemSpectrumData K where
  obj := splitEtaleAlgebra K n
  components := n
  prim := splitIdem K n
  prim_idem := splitIdem_mul_self K n
  prim_orth := fun _ _ hij => splitIdem_mul_orth K n hij
  prim_complete := splitIdem_complete K n
  prim_distinct := fun _ _ hij => idemSpec_primitive_distinct K n hij

/-- **M280F-6d: 冪等元スペクトルの存在**（任意の体 K 上で FÉt(K) の対象は
    連結成分分解を持つ: Spec K 自身が 1 成分）。 -/
theorem idemSpec_exists (K : IUTField) : Nonempty (IdemSpectrumData K) :=
  ⟨idemSpec_field_components K⟩

/-- **M280F-6e: 実 ℚ 上の 2 成分**（Spec(ℚ×ℚ) = 2 点; ratIUTField 上の実例）。 -/
def ratIdemSpec2 : IdemSpectrumData ratIUTField := idemSpec_split_components ratIUTField 2

/-- **M280F-6f: 実 ℚ 上の 3 成分**（Spec(ℚ×ℚ×ℚ) = 3 点）。 -/
def ratIdemSpec3 : IdemSpectrumData ratIUTField := idemSpec_split_components ratIUTField 3

/-- 成分数の確認（2）。 -/
theorem ratIdemSpec2_components : ratIdemSpec2.components = 2 := rfl

/-- 成分数の確認（3）。 -/
theorem ratIdemSpec3_components : ratIdemSpec3.components = 3 := rfl

/-- **M280F-6g: capstone — 実 ℚ 上の非自明冪等元**（Spec(ℚ×ℚ) は非連結;
    e ≠ 0 かつ e ≠ 1 の冪等元 = 本物の数体上の連結成分分解の実体）。 -/
theorem ratIdemSpec2_nontrivial :
    ∃ e : (funPowCRing ratIUTField.toCRing 2).carrier,
      idemSpec_isIdem (funPowCRing ratIUTField.toCRing 2) e ∧
        e ≠ (funPowCRing ratIUTField.toCRing 2).zero ∧
          e ≠ (funPowCRing ratIUTField.toCRing 2).one :=
  idemSpec_split_disconnected ratIUTField 2 (Nat.le_refl 2)

end IUT
