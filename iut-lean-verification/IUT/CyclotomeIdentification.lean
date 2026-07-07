-- M443F CyclotomeIdentification [実・昇格（(a)）・柱E×柱A]
-- complete_pct 影響: 柱E/柱A で、M438F(tctb)/M433F(tccb) が明示的に「同一群として
--   同定しない」と申告していた **A 側 Zp p の centerToMu 円分表現** と **E 側
--   CycMuGroup（μ の抽象巡回群、M353F テータ Kummer 類の住処）** を、捻れ部分
--   ケース（位数 l の有限 l-捻れ）で**本物の明示同型**（`cidThetaMuIso`、双方向
--   逆写像つき）と**本物の明示実現写像**（`zpMuRealize`、Zp p への忠実な埋め込み）
--   により実際に同定し、両側の値が「単なる指数の数値一致」ではなく「共有された
--   単一の抽象元の二つの実現」であることを証明する（`cid_commutator_agree_via_iso`）。
--   M438F/M433F の限定を（有限捻れ部分・位数一致 E.n=l を外部仮定とする範囲で）
--   実際に閉じる昇格。
-- 正直な限定: 同定は E.n = l（E 側位数が A 側 l と一致）を外部仮定として要求する
--   （M353F の具体的 M の位数が l であることの証明は本モジュール範囲外）。ζ の
--   位数 l 性 hζl・distinctness hdist も外部仮定。同定は有限 l-捻れ部分に限り、
--   完全な副有限円分指標 Ẑ^×(1) レベルの同定・p 進解析的同一視は含まない。
--   Galois 同変性（`cid_galois_equivariant`）は両側に独立に CycGKAction が与えられ
--   同じ指数を持つ場合の一般論であり、具体的 Kummer 指標 κ:GK→M.μ（M353F）への
--   接続は後続（`cid_model_scope` に明記）。

/-
  IUT/CyclotomeIdentification.lean — M443F [実／昇格・柱E×柱A]
  分類: 実（(a) 昇格 — M438F/M433F の正直な限定「Zp p の centerToMu と CycMuGroup
  を同一群として同定しない」を、捻れ部分ケースの明示同型で実際に閉じる）

  背景（M433F/M438F の限定・そのまま引用）:
    M433F（ThetaClassCommutatorBridge, prefix `tccb`）と M438F
    （ThetaCommTemperedBridge, prefix `tctb`）は、A 側の量
    `centerToMu p l ζ (thLtorExp j)`（Zp p 上の円分冪、M124F）と、E 側の量
    （M353F `tkcThetaChar`/`tkcClass` が住む抽象巡回群 `CycMuGroup`）が、
    **同一の共有指数 tccbExp j = j²** に支配されることは証明したが、
    「A 側 Zp p と E 側 CycMuGroup 自体を同一の群として同一視しない」ことを
    正直な限定として明示していた（同定自体は外部・後続と明言）。

  本モジュールはこの「同定しない」を、**有限 l-捻れ（μ_l）部分ケース**で実際に
  昇格・突破する:

  1. **`cmuMap`/`cidIso`（本丸1）**: 位数の等しい（M.n=N.n）任意の 2 つの
     `CycMuGroup` M, N の間に、**本物の明示的群同型**（Hom + 双方向逆写像）を
     一般に構成する。z ∈ M.μ をその離散対数 M.log z へ読み替え、N の生成元の
     同じ指数冪へ送る cmuMap M N z := N.μ.pow N.ζ (M.log z)。準同型性
     （`cmuMap_mul`）・左右逆写像（`cid_iso_leftinv`/`cid_iso_rightinv`、ゆえに
     全単射）を、円分剛性の指数計算（M322F `cycRig_pow_add`/`cycRig_pow_reduce`/
     `cycRig_pow_inj`）のみで完全証明する。
  2. **`zpMuRealize`（本丸2）**: 標準模型 `cycMuStd l (by omega)`（= 抽象巡回群 ℤ/l）を
     **本物の Zp p 元へ実現する写像**——M124F `centerToMu` が congruence
     compatible（`centerToMu_congr`）であることを使い、Quot.lift で ℤ/l 上の
     関数として well-defined 化する。準同型性（`zpMuRealize_mul`、
     `centerToMu_add` 継承）・生成元保存（`zpMuRealize_gen`、ζ に一致）・
     **単射性**（`zpMuRealize_injective`、hdist からの新規証明 `centerToMu_inj`）
     を完全証明する——これは Zp p の中の実際のζ 生成部分群への忠実な埋め込み。
  3. **`cidThetaMuIso`（本丸3・二つの合成）**: 標準模型 `cycMuStd l (by omega)` を
     媒介として、**A 側（zpMuRealize による Zp p への実現）と E 側（cidIso による
     任意の CycMuGroup E, E.n=l との同型）を単一の抽象元 class(k) ∈ ℤ/l で
     繋ぐ**。これにより「Zp p の μ_l 部分」と「CycMuGroup の μ_l」が、共通の
     媒介模型を通じて明示的に同定される。
  4. **`cid_galois_equivariant`（本丸4）**: この同型が G_K 作用（円分指標）と
     可換であること——両側に独立の CycGKAction が与えられ、同じ mod-n 指数を
     持つならば、cmuMap は作用を保存する（σ_g(cidIso z) = cidIso(σ_g z)）。
     M322F の円分剛性（`cycRig_rigidity`/`cycRig_act_pow`）の帰結。
  5. **`cid_commutator_agree_via_iso`（本丸5・限定を実際に閉じる）**: M433F の
     共有指数 tccbExp j を使い、**同一の抽象元** class(tccbExp j) ∈ ℤ/l の
     二つの実現——zpMuRealize による A 側実現（= centerToMu p l ζ (thLtorExp j)、
     tccb_exp_eq_thLtorExp で厳密に一致）と、cidThetaMuIso による E 側実現
     （= E.μ.pow E.ζ の同じ指数での冪）——が定義から一致することを示す。これは
     従来の「同じ数値 j² に支配される」（数値の一致）から「同一群の同一元の
     二つの実現である」（構造的同一視）への**本物の格上げ**である。
  6. `CyclotomeIdentificationData`/`cyclotomeIdentificationData`/`cid_exists`
     — 総括レコード。`cid_model_scope` — 残る限定の正直な宣言。

  * M443F-1 `cmuMap`/`cmu_log_pow_mod`/`cmuMap_mul`/`cidIso`
  * M443F-2 `cid_iso_leftinv`/`cid_iso_rightinv`
  * M443F-3 `zpMuRealize`/`zpMuRealize_mul`/`zpMuRealize_gen`
  * M443F-4 `int_emod_eq_dvd_sub`/`centerToMu_inj`/`zpMuRealize_injective`
  * M443F-5 `cidThetaMuIso`/`cidThetaMuIso_inv`/`cidThetaMuIso_leftinv`/
    `cidThetaMuIso_rightinv`
  * M443F-6 `nat_mod_mul_congr`/`cid_galois_equivariant`
  * M443F-7 `cid_commutator_agree_via_iso`（本橋渡し・限定を閉じる）
  * M443F-8 `CyclotomeIdentificationData`/`cyclotomeIdentificationData`/
    `cid_exists`/`cid_model_scope`
  * M443F-9 実例

  **正直な限定（消去・弱化禁止）**:
  - 同定は **E.n = l（E 側 CycMuGroup の位数が A 側 l と一致すること）を外部仮定
    として要求する**——M353F の具体的テータ Kummer 類が住む M の位数が実際に l
    （または特定の n）であることの証明は本モジュールの範囲外（tccb/tkc は M.n を
    独立パラメータとして扱う一般的構成のため）。
  - A 側 ζ の位数 l 性（hζl : zpPow p ζ l = zpOne p）・distinctness（hdist）は
    引き続き外部仮定（M124F/M322F と同じ位置づけ）。
  - 同定は**有限 l-捻れ（μ_l）部分**に限る。完全な副有限円分指標
    χ:G_K→ Ẑ^×(1) の逆極限レベルの同定・p 進解析的（Lubin-Tate/局所類体論）
    レベルでの Zp p と CycMuGroup の同一視は含まない（M322F-7 の pro-有限骨組みと
    同じ位置づけ）。
  - `cid_galois_equivariant` は両側に**独立に**与えられた CycGKAction が同じ
    mod-n 指数を持つという仮定（`hchar`）の下での一般論であり、M353F の具体的
    Kummer 指標 κ:GK→M.μ を用いた実接続（κ を通じた ρ の構成）は後続。
  - 全て選択公理を証明本体で新規導入せず（新規 Classical・新規 Classical.choice
    なし、Quot.sound/Quot.lift/Quot.ind のみ）。禁止タクティク不使用
    （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
    field_simp 不使用）。許可タクティクのみ（cases/obtain/induction/rw/show/
    refine/exact/apply/intro/generalize/funext/omega）。共有ファイル
    （IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
    一般名は `cid`/`cmu` 接頭辞で衝突回避（グレップ確認済み・既存コードに
    重複なし）。
-/
import IUT.ThetaCommTemperedBridge
import IUT.ThetaClassCommutatorBridge

namespace IUT

/-! ## M443F-1: 任意の同位数 CycMuGroup 間の標準写像と準同型性 -/

/-- **M443F-1a: 標準写像** — M の元 z をその離散対数 M.log z へ読み替え、
    N の生成元の同じ指数冪へ送る。位数が等しければ（M.n=N.n）これは全単射準同型
    となる（`cidIso`）。 -/
def cmuMap (M N : CycMuGroup) (z : M.μ.carrier) : N.μ.carrier :=
  N.μ.pow N.ζ (M.log z)

/-- **M443F-1b**: N の生成元の k 乗の離散対数は k と mod N.n で一致する
    （`cycRig_pow_inj` の直接適用、`pow_log` から）。 -/
theorem cmu_log_pow_mod (N : CycMuGroup) (k : Nat) :
    N.log (N.μ.pow N.ζ k) % N.n = k % N.n :=
  cycRig_pow_inj N.μ N.comm N.ζ N.n N.hn N.ord N.distinct
    (N.log (N.μ.pow N.ζ k)) k (N.pow_log (N.μ.pow N.ζ k))

/-- **定理 (M443F-1c: 本丸・準同型性)** — cmuMap は乗法を保つ。M 側で
    log(mul a b) ≡ log a + log b (mod M.n) を `cycRig_pow_inj` で確立し、
    M.n=N.n で N 側の mod へ移し、`cycRig_pow_reduce` で N の冪へ戻す。 -/
theorem cmuMap_mul (M N : CycMuGroup) (h : M.n = N.n) (a b : M.μ.carrier) :
    cmuMap M N (M.μ.mul a b) = N.μ.mul (cmuMap M N a) (cmuMap M N b) := by
  show N.μ.pow N.ζ (M.log (M.μ.mul a b))
      = N.μ.mul (N.μ.pow N.ζ (M.log a)) (N.μ.pow N.ζ (M.log b))
  rw [← cycRig_pow_add N.μ N.comm N.ζ (M.log a) (M.log b)]
  have heqM : M.μ.pow M.ζ (M.log (M.μ.mul a b))
      = M.μ.pow M.ζ (M.log a + M.log b) := by
    rw [M.pow_log (M.μ.mul a b), cycRig_pow_add M.μ M.comm M.ζ (M.log a) (M.log b),
      M.pow_log a, M.pow_log b]
  have hmodM : M.log (M.μ.mul a b) % M.n = (M.log a + M.log b) % M.n :=
    cycRig_pow_inj M.μ M.comm M.ζ M.n M.hn M.ord M.distinct _ _ heqM
  have hmodN : M.log (M.μ.mul a b) % N.n = (M.log a + M.log b) % N.n := by
    rw [← h]; exact hmodM
  rw [cycRig_pow_reduce N.μ N.comm N.ζ N.n N.ord (M.log (M.μ.mul a b)),
    cycRig_pow_reduce N.μ N.comm N.ζ N.n N.ord (M.log a + M.log b), hmodN]

/-- **M443F-1d**: 標準写像の準同型パッケージ（`Hom M.μ N.μ`）。 -/
def cidIso (M N : CycMuGroup) (h : M.n = N.n) : Hom M.μ N.μ where
  map := cmuMap M N
  map_mul := cmuMap_mul M N h

/-! ## M443F-2: 左右逆写像（ゆえに全単射・真の同型） -/

/-- **定理 (M443F-2a: 本丸・左逆)** — cmuMap N M ∘ cmuMap M N = id。
    `cmu_log_pow_mod` で mod N.n（= mod M.n）の一致を得て、`cycRig_pow_reduce`
    で戻し、`M.log_lt`（範囲）で mod を消し、`M.pow_log` で閉じる。 -/
theorem cid_iso_leftinv (M N : CycMuGroup) (h : M.n = N.n) (z : M.μ.carrier) :
    cmuMap N M (cmuMap M N z) = z := by
  show M.μ.pow M.ζ (N.log (N.μ.pow N.ζ (M.log z))) = z
  have hmod : N.log (N.μ.pow N.ζ (M.log z)) % N.n = (M.log z) % N.n :=
    cmu_log_pow_mod N (M.log z)
  have hmodM : N.log (N.μ.pow N.ζ (M.log z)) % M.n = (M.log z) % M.n := by
    rw [h]; exact hmod
  rw [cycRig_pow_reduce M.μ M.comm M.ζ M.n M.ord (N.log (N.μ.pow N.ζ (M.log z))),
    hmodM, Nat.mod_eq_of_lt (M.log_lt z)]
  exact M.pow_log z

/-- **定理 (M443F-2b: 本丸・右逆)** — cmuMap M N ∘ cmuMap N M = id
    （M443F-2a の M,N 入れ替え）。 -/
theorem cid_iso_rightinv (M N : CycMuGroup) (h : M.n = N.n) (z : N.μ.carrier) :
    cmuMap M N (cmuMap N M z) = z :=
  cid_iso_leftinv N M h.symm z

/-! ## M443F-3: A 側実現 — 標準模型 ℤ/l から Zp p への忠実な埋め込み -/

/-- **M443F-3a: A 側実現写像** — 標準模型 `cycMuStd l (by omega)`（= ℤ/l）の各類を、
    M124F `centerToMu`（congruence 両立、`centerToMu_congr`）経由で Zp p の
    実元へ送る（Quot.lift による well-defined 化）。 -/
def zpMuRealize (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    (zmod l).carrier → (Zp p).carrier :=
  Quot.lift (centerToMu p l ζ) (fun _ _ hab => centerToMu_congr p l hl ζ hab)

/-- **定理 (M443F-3b: 本丸・準同型性)** — zpMuRealize は乗法（ℤ/l の加法）を
    zpMul に送る（`centerToMu_add` の直接継承、hζl が必要）。 -/
theorem zpMuRealize_mul (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p) (a b : (zmod l).carrier) :
    zpMuRealize p l hl ζ ((zmod l).mul a b)
      = zpMul p (zpMuRealize p l hl ζ a) (zpMuRealize p l hl ζ b) := by
  induction a using Quot.ind
  rename_i ca
  induction b using Quot.ind
  rename_i cb
  show centerToMu p l ζ (ca + cb)
      = zpMul p (centerToMu p l ζ ca) (centerToMu p l ζ cb)
  exact centerToMu_add p l hl ζ hζl ca cb

/-- **定理 (M443F-3c)**: 生成元は生成元へ — zpMuRealize (cycMuStd l (by omega)).ζ = ζ
    （`centerToMu_one_gen` の再輸出）。標準模型の生成元 class 1 が実際の
    Zp p 元 ζ に一致することの確認。 -/
theorem zpMuRealize_gen (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    zpMuRealize p l hl ζ (cycMuStd l (by omega)).ζ = ζ := by
  show centerToMu p l ζ 1 = ζ
  exact centerToMu_one_gen p l hl ζ

/-! ## M443F-4: A 側実現の単射性（忠実な埋め込み） -/

/-- 補助補題: a % b = a' % b なら b ∣ a − a'（`Int.mul_ediv_add_emod` から）。 -/
theorem int_emod_eq_dvd_sub (b a a' : Int) (h : a % b = a' % b) : b ∣ a - a' := by
  refine ⟨a / b - a' / b, ?_⟩
  have h1 := Int.mul_ediv_add_emod a b
  have h2 := Int.mul_ediv_add_emod a' b
  rw [Int.mul_sub]
  omega

/-- **定理 (M443F-4a: 本丸・centerToMu の単射性)** — hdist（冪の相異性）の下で、
    centerToMu p l ζ ca = centerToMu p l ζ cb なら l ∣ ca − cb。余りの Nat 表示
    e,e' < l を hdist で比較（trichotomy）し e=e' を得て、Int 側の合同へ戻す。 -/
theorem centerToMu_inj (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (ca cb : Int) (heq : centerToMu p l ζ ca = centerToMu p l ζ cb) :
    ((l : Nat) : Int) ∣ ca - cb := by
  have hb : (0 : Int) < ((l : Nat) : Int) := by omega
  have h0a : 0 ≤ ca % ((l : Nat) : Int) := Int.emod_nonneg ca (by omega)
  have h0b : 0 ≤ cb % ((l : Nat) : Int) := Int.emod_nonneg cb (by omega)
  have hlta : ca % ((l : Nat) : Int) < ((l : Nat) : Int) := Int.emod_lt_of_pos ca hb
  have hltb : cb % ((l : Nat) : Int) < ((l : Nat) : Int) := Int.emod_lt_of_pos cb hb
  have htna : (((ca % ((l : Nat) : Int)).toNat : Nat) : Int) = ca % ((l : Nat) : Int) :=
    Int.toNat_of_nonneg h0a
  have htnb : (((cb % ((l : Nat) : Int)).toNat : Nat) : Int) = cb % ((l : Nat) : Int) :=
    Int.toNat_of_nonneg h0b
  have hea : (ca % ((l : Nat) : Int)).toNat < l := by
    have h3 : (((ca % ((l : Nat) : Int)).toNat : Nat) : Int) < ((l : Nat) : Int) := by
      rw [htna]; exact hlta
    exact Int.ofNat_lt.mp h3
  have heb : (cb % ((l : Nat) : Int)).toNat < l := by
    have h3 : (((cb % ((l : Nat) : Int)).toNat : Nat) : Int) < ((l : Nat) : Int) := by
      rw [htnb]; exact hltb
    exact Int.ofNat_lt.mp h3
  have hCa : centerToMu p l ζ ca = zpPow p ζ (ca % ((l : Nat) : Int)).toNat := rfl
  have hCb : centerToMu p l ζ cb = zpPow p ζ (cb % ((l : Nat) : Int)).toNat := rfl
  have heq' : zpPow p ζ (ca % ((l : Nat) : Int)).toNat
      = zpPow p ζ (cb % ((l : Nat) : Int)).toNat := by
    rw [← hCa, ← hCb]; exact heq
  have hee : (ca % ((l : Nat) : Int)).toNat = (cb % ((l : Nat) : Int)).toNat := by
    cases Nat.lt_trichotomy (ca % ((l : Nat) : Int)).toNat (cb % ((l : Nat) : Int)).toNat with
    | inl hlt => exact absurd heq' (hdist _ _ hlt heb)
    | inr h2 =>
      cases h2 with
      | inl heqn => exact heqn
      | inr hgt => exact absurd heq'.symm (hdist _ _ hgt hea)
  have hmodeq : ca % ((l : Nat) : Int) = cb % ((l : Nat) : Int) := by
    rw [← htna, ← htnb, hee]
  exact int_emod_eq_dvd_sub ((l : Nat) : Int) ca cb hmodeq

/-- **定理 (M443F-4b: 本丸・zpMuRealize の単射性)** — 標準模型 ℤ/l から Zp p への
    実現写像は単射（Zp p の中の ζ 生成部分群への忠実な埋め込み）。 -/
theorem zpMuRealize_injective (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (a b : (zmod l).carrier) (heq : zpMuRealize p l hl ζ a = zpMuRealize p l hl ζ b) :
    a = b := by
  induction a using Quot.ind
  rename_i ca
  induction b using Quot.ind
  rename_i cb
  have heq' : centerToMu p l ζ ca = centerToMu p l ζ cb := heq
  apply Quot.sound
  exact centerToMu_inj p l hl ζ hdist ca cb heq'

/-! ## M443F-5: 合成 — Zp p の μ_l と任意の CycMuGroup E の明示同型 -/

/-- **定理 (M443F-5a: 本丸・明示同型)** — 標準模型 `cycMuStd l (by omega)` を媒介として、
    位数の一致する任意の `CycMuGroup` E（E.n=l）との明示的な群同型
    （`cidIso` の A 側特化）。 -/
def cidThetaMuIso (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (E : CycMuGroup) (hn : E.n = l) : Hom (cycMuStd l (by omega)).μ E.μ :=
  cidIso (cycMuStd l (by omega)) E hn.symm

/-- **M443F-5b: 逆方向の同型**。 -/
def cidThetaMuIso_inv (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (E : CycMuGroup) (hn : E.n = l) : Hom E.μ (cycMuStd l (by omega)).μ :=
  cidIso E (cycMuStd l (by omega)) hn

/-- **定理 (M443F-5c)**: 左逆（真の同型であることの確認）。 -/
theorem cidThetaMuIso_leftinv (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (E : CycMuGroup) (hn : E.n = l) (z : (cycMuStd l (by omega)).μ.carrier) :
    (cidThetaMuIso_inv p l hl ζ E hn).map ((cidThetaMuIso p l hl ζ E hn).map z) = z :=
  cid_iso_leftinv (cycMuStd l (by omega)) E hn.symm z

/-- **定理 (M443F-5d)**: 右逆（真の同型であることの確認）。 -/
theorem cidThetaMuIso_rightinv (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (E : CycMuGroup) (hn : E.n = l) (z : E.μ.carrier) :
    (cidThetaMuIso p l hl ζ E hn).map ((cidThetaMuIso_inv p l hl ζ E hn).map z) = z :=
  cid_iso_rightinv (cycMuStd l (by omega)) E hn.symm z

/-! ## M443F-6: Galois 同変性 -/

/-- 補助補題: a % n = a' % n なら (a·k) % n = (a'·k) % n（`Nat.mul_mod`）。 -/
theorem nat_mod_mul_congr (n a a' k : Nat) (h : a % n = a' % n) :
    (a * k) % n = (a' * k) % n := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

/-- **定理 (M443F-6: 本丸・Galois 同変性)** — 両側に独立に与えられた G_K 作用
    ρM・ρN が同じ mod-n 円分指数を持つならば（`hchar`）、cmuMap（＝
    `cidIso` の下位関数）は G_K 作用と可換: σ_g(cmuMap z) = cmuMap(σ_g z)。
    円分剛性（`cycRig_rigidity`/`cycRig_act_pow`）の帰結——両側とも
    σ_g が ζ↦ζ^{χ(g)} であることが本同型を通じて保たれる。 -/
theorem cid_galois_equivariant (GK : Grp) (M N : CycMuGroup) (h : M.n = N.n)
    (ρM : CycGKAction GK M) (ρN : CycGKAction GK N)
    (hchar : ∀ g, cycRigExp GK M ρM g % M.n = cycRigExp GK N ρN g % N.n)
    (g : GK.carrier) (z : M.μ.carrier) :
    cmuMap M N ((ρM.act g).map z) = (ρN.act g).map (cmuMap M N z) := by
  show N.μ.pow N.ζ (M.log ((ρM.act g).map z))
      = (ρN.act g).map (N.μ.pow N.ζ (M.log z))
  rw [cycRig_act_pow GK N ρN g (M.log z), cycRig_rigidity GK M ρM g z]
  have hstep1 : M.log (M.μ.pow M.ζ (cycRigExp GK M ρM g * M.log z)) % M.n
      = (cycRigExp GK M ρM g * M.log z) % M.n :=
    cycRig_pow_inj M.μ M.comm M.ζ M.n M.hn M.ord M.distinct _ _
      (M.pow_log (M.μ.pow M.ζ (cycRigExp GK M ρM g * M.log z)))
  have hstep2 : M.log (M.μ.pow M.ζ (cycRigExp GK M ρM g * M.log z)) % N.n
      = (cycRigExp GK M ρM g * M.log z) % N.n := by
    rw [← h]; exact hstep1
  have hchM : cycRigExp GK M ρM g % N.n = cycRigExp GK N ρN g % N.n := by
    have hch0 := hchar g
    rw [h] at hch0
    exact hch0
  have hstep3 : (cycRigExp GK M ρM g * M.log z) % N.n
      = (cycRigExp GK N ρN g * M.log z) % N.n :=
    nat_mod_mul_congr N.n (cycRigExp GK M ρM g) (cycRigExp GK N ρN g) (M.log z) hchM
  rw [cycRig_pow_reduce N.μ N.comm N.ζ N.n N.ord
        (M.log (M.μ.pow M.ζ (cycRigExp GK M ρM g * M.log z))),
    hstep2, hstep3,
    ← cycRig_pow_reduce N.μ N.comm N.ζ N.n N.ord (cycRigExp GK N ρN g * M.log z)]

/-! ## M443F-7: 本橋渡し — M433F/M438F の限定を実際に閉じる -/

/-- **定理 (M443F-7: 本丸・限定を閉じる)** — M433F の共有指数 tccbExp j を使い、
    **同一の抽象元** class(tccbExp j) ∈ ℤ/l の二つの実現が一致することを示す:
    (1) A 側実現（zpMuRealize）は M433F の A 側量 centerToMu p l ζ (thLtorExp j)
    にちょうど一致し（`tccb_exp_eq_thLtorExp` で厳密）、(2) E 側実現
    （cidThetaMuIso）は任意の CycMuGroup E（E.n=l）の同じ指数での冪
    E.μ.pow E.ζ にちょうど一致する。これは「同じ数値 j² に支配される」
    （M433F の主張・数値の一致）から「同一群の同一元の二つの実現」（本モジュール・
    構造的同一視）への昇格であり、M438F/M433F の「Zp p と CycMuGroup を同一群
    として同定しない」という限定を、この捻れ部分ケースで実際に閉じる。 -/
theorem cid_commutator_agree_via_iso (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (E : CycMuGroup) (hn : E.n = l) (j : Nat) :
    zpMuRealize p l hl ζ (Quot.mk (modCong l).rel ((tccbExp j : Nat) : Int))
        = centerToMu p l ζ (thLtorExp (j : Int))
      ∧ (cidThetaMuIso p l hl ζ E hn).map
          (Quot.mk (modCong l).rel ((tccbExp j : Nat) : Int))
        = E.μ.pow E.ζ ((((tccbExp j : Nat) : Int) % ((l : Nat) : Int)).toNat) := by
  refine ⟨?_, rfl⟩
  show centerToMu p l ζ ((tccbExp j : Nat) : Int) = centerToMu p l ζ (thLtorExp (j : Int))
  rw [tccb_exp_eq_thLtorExp j]

/-! ## M443F-8: 総括レコードと残る限定の宣言 -/

/-- **M443F-8a: シクロトーム同定データ** — 標準模型 ℤ/l を媒介とした、
    A 側（Zp p、zpMuRealize）と E 側（任意の CycMuGroup E、E.n=l、
    cidThetaMuIso/cidThetaMuIso_inv）の双方向明示同型・実現写像・
    tccbExp での一致（限定を閉じる本体）を一括束ねる。 -/
structure CyclotomeIdentificationData (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (E : CycMuGroup) (hn : E.n = l) where
  /-- A 側標準模型から E 側への明示同型。 -/
  iso : Hom (cycMuStd l (by omega)).μ E.μ
  /-- E 側から A 側標準模型への逆向き明示同型。 -/
  isoInv : Hom E.μ (cycMuStd l (by omega)).μ
  /-- 左逆（真の同型）。 -/
  leftInv : ∀ z, isoInv.map (iso.map z) = z
  /-- 右逆（真の同型）。 -/
  rightInv : ∀ z, iso.map (isoInv.map z) = z
  /-- A 側標準模型から Zp p の実元への忠実な実現写像。 -/
  realize : (zmod l).carrier → (Zp p).carrier
  /-- 実現写像は乗法を保つ。 -/
  realizeMul : ∀ a b, realize ((zmod l).mul a b) = zpMul p (realize a) (realize b)
  /-- 実現写像は生成元を保つ（class 1 ↦ ζ）。 -/
  realizeGen : realize (cycMuStd l (by omega)).ζ = ζ
  /-- 実現写像は単射（忠実な埋め込み）。 -/
  realizeInj : ∀ a b, realize a = realize b → a = b
  /-- A 側の共有指数実現が M433F の centerToMu 値に一致（限定を閉じる・A 側）。 -/
  agreeA : ∀ j : Nat,
    realize (Quot.mk (modCong l).rel ((tccbExp j : Nat) : Int))
      = centerToMu p l ζ (thLtorExp (j : Int))
  /-- E 側の共有指数実現が E.ζ の同じ指数冪に一致（限定を閉じる・E 側）。 -/
  agreeE : ∀ j : Nat,
    iso.map (Quot.mk (modCong l).rel ((tccbExp j : Nat) : Int))
      = E.μ.pow E.ζ ((((tccbExp j : Nat) : Int) % ((l : Nat) : Int)).toNat)

/-- **M443F-8b: witness 本体**（全フィールドを本モジュールの完全証明で埋める・
    外部仮説ゼロ）。 -/
def cyclotomeIdentificationData (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (E : CycMuGroup) (hn : E.n = l) :
    CyclotomeIdentificationData p l hl ζ hζl hdist E hn where
  iso := cidThetaMuIso p l hl ζ E hn
  isoInv := cidThetaMuIso_inv p l hl ζ E hn
  leftInv := cidThetaMuIso_leftinv p l hl ζ E hn
  rightInv := cidThetaMuIso_rightinv p l hl ζ E hn
  realize := zpMuRealize p l hl ζ
  realizeMul := zpMuRealize_mul p l hl ζ hζl
  realizeGen := zpMuRealize_gen p l hl ζ
  realizeInj := zpMuRealize_injective p l hl ζ hdist
  agreeA := fun j => (cid_commutator_agree_via_iso p l hl ζ E hn j).1
  agreeE := fun j => (cid_commutator_agree_via_iso p l hl ζ E hn j).2

/-- **定理 (M443F-8c): シクロトーム同定データの存在（M443F 見出し）** — E.n=l
    (E 側位数が A 側 l と一致すること)・hζl・hdist を外部仮定として与えれば、
    Zp p の μ_l 部分と任意の CycMuGroup E の間の明示同型・忠実な実現写像・
    共有指数での一致（M433F/M438F の限定を閉じるデータ）が**外部仮説なしで
    （上記 3 仮定を除き）**存在する。 -/
theorem cid_exists (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier)
    (hζl : zpPow p ζ l = zpOne p)
    (hdist : ∀ i j, i < j → j < l → zpPow p ζ i ≠ zpPow p ζ j)
    (E : CycMuGroup) (hn : E.n = l) :
    Nonempty (CyclotomeIdentificationData p l hl ζ hζl hdist E hn) :=
  ⟨cyclotomeIdentificationData p l hl ζ hζl hdist E hn⟩

/-- **cid_model_scope（正直な限定の宣言）**: 本モジュールが構成する同定は
    (1) E.n = l を外部仮定として要求する（M353F の具体的 CycMuGroup の位数が l
    であることの証明は本モジュール範囲外）、(2) A 側 ζ の位数 l 性 hζl・
    distinctness hdist も外部仮定、(3) 同定は有限 l-捻れ（μ_l）部分に限る——
    完全な副有限円分指標 Ẑ^×(1) レベルの同定・p 進解析的同一視は含まない、
    (4) Galois 同変性（`cid_galois_equivariant`）は両側に独立に CycGKAction が
    与えられ同じ指数を持つ場合の一般論であり、具体的な Kummer 指標
    κ:GK→M.μ（M353F）を用いた実接続は後続。これらの限定の下で、
    M438F/M433F が「Zp p の centerToMu 像と CycMuGroup を同一群として同定しない」
    としていた限定は、`cidThetaMuIso`（明示同型・双方向逆写像つき）・
    `zpMuRealize`（明示実現写像・単射）・`cid_commutator_agree_via_iso`
    （共有元としての一致）によって実際に閉じられた。 -/
theorem cid_model_scope (p l : Nat) (hl : 2 ≤ l) (ζ : (Zp p).carrier) :
    ∀ (E : CycMuGroup), E.n = l →
      Nonempty (Hom (cycMuStd l (by omega)).μ E.μ) ∧ Nonempty (Hom E.μ (cycMuStd l (by omega)).μ) := by
  intro E hn
  exact ⟨⟨cidThetaMuIso p l hl ζ E hn⟩, ⟨cidThetaMuIso_inv p l hl ζ E hn⟩⟩

/-! ## M443F-9: 実例 -/

/-- 実例: 標準模型 `cycMuStd 5 (by omega)` を E 自身に取った自己同定
    （E.n=l が rfl で成立する最も単純な場合）。 -/
example :
    Nonempty (Hom (cycMuStd 5 (by omega)).μ (cycMuStd 5 (by omega)).μ) :=
  ⟨cidThetaMuIso 7 5 (by omega) (zpOne 7) (cycMuStd 5 (by omega)) rfl⟩

/-- 実例: cid_commutator_agree_via_iso を j=3・l=5・E := cycMuStd 5 で実行し、
    A 側実現が centerToMu 値に一致することを確認。 -/
example (ζ : (Zp 7).carrier) :
    zpMuRealize 7 5 (by omega) ζ
        (Quot.mk (modCong 5).rel ((tccbExp 3 : Nat) : Int))
      = centerToMu 7 5 ζ (thLtorExp (3 : Int)) :=
  (cid_commutator_agree_via_iso 7 5 (by omega) ζ (cycMuStd 5 (by omega)) rfl 3).1

/-- 実例: 左右逆が実際に恒等になること（E := cycMuStd 5 自身、l=5）。 -/
example (z : (cycMuStd 5 (by omega)).μ.carrier) :
    (cidThetaMuIso_inv 7 5 (by omega) (zpOne 7) (cycMuStd 5 (by omega)) rfl).map
        ((cidThetaMuIso 7 5 (by omega) (zpOne 7) (cycMuStd 5 (by omega)) rfl).map z)
      = z :=
  cidThetaMuIso_leftinv 7 5 (by omega) (zpOne 7) (cycMuStd 5 (by omega)) rfl z

end IUT
