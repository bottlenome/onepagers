/-
  IUT/CyclotomicTowerLimit.lean — CTL（A3 本丸 M3: Nat 円分塔を
  `ProfinitePi1Tower` に嵌めて逆極限 profinite Gal(ℚ(ζ_{3^∞})/ℚ) を構成）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・
     実円分塔 ℚ(ζ₃) ⊂ ℚ(ζ_9) ⊂ ℚ(ζ_{27}) ⊂ … ⊂ ℚ(ζ_{3^{n+1}}) ⊂ … の
     各段の実 Galois 群 Gal(ℚ(ζ_{3^{n+1}})/ℚ)（`ctlGal`）と、任意段間の実制限
     準同型 `ctrResHom`（ctr で本物に構成済み）を、`ProfinitePi1Tower` の
     逆系データとして本物に嵌め、逆極限 profinite 群
     lim Gal(ℚ(ζ_{3^{n+1}})/ℚ) = Gal(ℚ(ζ_{3^∞})/ℚ) を構成する）。

  **complete_pct 影響**: A3——従来 witness 仮説だった
  `ProfinitePi1Tower.restr`／`restr_self`／`restr_comp` の **初の本物 discharge**。
  M287F（ProfinitePi1）は制限準同型を塔の witness データとして受け取り、
  非自明塔の実例は自明塔 lim Gal(ℚ/ℚ)=1 に留まっていた（正直申告 2・4）。
  本モジュールは、実 2 段以上の非自明円分塔（∀n・全段本物）の実制限準同型
  `ctrResHom`（compat ＋ 群準同型を ctr で完全証明済み）を反復合成して逆系則
  （恒等保存 `restr_self`・推移性 `restr_comp`）を **本物に証明**し、
  `ctlTower : ProfinitePi1Tower` を構成する（★witness の初 discharge）。
  これで逆極限 `ctlProfinite := profPi1Limit ctlTower`（実 profinite
  Gal(ℚ(ζ_{3^∞})/ℚ)）と副有限性 `ctl_is_profinite`（開核＋近傍基）が
  一般の M287F 定理からそのまま従う。監査残欠 (iii)（塔詰め未接続）を解消。
  本ファイル単体では complete_pct 未設定（独立監査で反映）。

  内容（設計 audit/A3-inverse-limit-roadmap-2026-07-09.md §4.2）:
   * `ctlExt n`/`ctlGal n` — L_n = ℚ(ζ_{3^{n+1}}) と実 Gal(L_n/ℚ)。
   * `ctlStep n` — 単段制限 res: Gal(L_{n+1}/ℚ) → Gal(L_n/ℚ)（= ctrResHom (n+1)）。
   * `ctlRestrAux i d` — 反復制限（差分 d の cast-free 再帰）。
   * `ctlRestrD`/`ctlRestr` — i ≤ j への制限（j = i+(j−i) の subst 1 回）。
   * `ctl_restr_self` — 恒等保存（d=0 帰着）。
   * `ctl_restr_step`/`ctl_restr_comp_aux`/`ctl_restr_comp` — 推移性
     （単段 peel ＋ 差分帰納。**結合律 cast を完全に回避**する形で証明）。
   * `ctlTower` — 塔詰め（★witness の初 discharge）。
   * `ctlProfinite`/`ctl_is_profinite` — 逆極限 profinite 群と副有限性。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・ℚ 上・円分塔 ℚ(ζ_{3^{n+1}}) の忠実な部分ケース。
   (ii)  射影の全射性（整合族の持ち上げ）は本ファイルに含めない——一般 σ_a
         整合族の極限持ち上げ（ctr_surjective の帰納極限）は M4 の射程。
   (iii) レベル同型 Gal(L_n/ℚ) ≅ (ℤ/3^{n+1})^× ／ 極限同型
         Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^× は未証明（M4 の射程）。
   (iv)  これは円分切片であって実 G_ℚ そのものではない（G_ℚ の可解商・
         Kronecker–Weber 部分に対応する副有限商の一つ）。

  全て選択公理不使用（新規 `Classical.choice` を証明本体に導入しない・
  propext/Quot.sound のみ）。禁止タクティク（simp/decide/by_cases/rcases/
  ring/nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。新規ファイル
  1 個のみ（共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新・
  親が統合）。
-/
import IUT.CyclotomicResTower
import IUT.ProfinitePi1

namespace IUT

/-! ## CTL-1: 塔の各段 L_n = ℚ(ζ_{3^{n+1}}) と実 Gal(L_n/ℚ) -/

/-- **CTL-1a: 塔の各段の体拡大** — L_n = ℚ(ζ_{3^{n+1}})（cte の第 (n+1) 段。
    全 n で本物・E5 が既約性を供給）。 -/
def ctlExt (n : Nat) : FieldExtension := cteExt (n + 1) (by omega)

/-- **CTL-1b: 各段の実 Galois 群** Gal(L_n/ℚ) = Gal(ℚ(ζ_{3^{n+1}})/ℚ)。 -/
def ctlGal (n : Nat) : Grp := galoisGroupGrp (ctlExt n)

/-- **CTL-1c: 単段制限準同型** res: Gal(L_{n+1}/ℚ) → Gal(L_n/ℚ)
    （= ctrResHom (n+1)・ctr で本物に構成した実制限）。 -/
def ctlStep (n : Nat) : Hom (ctlGal (n + 1)) (ctlGal n) :=
  ctrResHom (n + 1) (by omega)

/-! ## CTL-2: 反復制限（差分 d の cast-free 再帰） -/

/-- **CTL-2a: 反復制限の差分再帰** — 塔の i 段から i+d 段への合成制限
    Gal(L_{i+d}/ℚ) → Gal(L_i/ℚ)。差分 d の再帰は cast-free
    （i+0=i・i+(d+1)=(i+d)+1 が definitional・型が完全に一致する）。 -/
def ctlRestrAux (i : Nat) : (d : Nat) → Hom (ctlGal (i + d)) (ctlGal i)
  | 0     => profPi1IdHom (ctlGal i)
  | d + 1 => Hom.comp (ctlRestrAux i d) (ctlStep (i + d))

/-! ## CTL-3: i ≤ j への制限（j = i+(j−i) の subst 1 回） -/

/-- **CTL-3a: 差分明示版の制限** — i + d = j の証拠 h で反復制限の余域を j 段へ
    キャストする（subst を 1 箇所に固定するための道具）。 -/
def ctlRestrD (i j d : Nat) (h : i + d = j) : Hom (ctlGal j) (ctlGal i) :=
  h ▸ ctlRestrAux i d

/-- **CTL-3b: 制限準同型** res: Gal(L_j/ℚ) → Gal(L_i/ℚ)（i ≤ j）。
    差分 d = j − i と橋 i + (j − i) = j（`Nat.add_sub_cancel'`）で嵌める。 -/
def ctlRestr {i j : Nat} (h : i ≤ j) : Hom (ctlGal j) (ctlGal i) :=
  ctlRestrD i j (j - i) (Nat.add_sub_cancel' h)

/-- **CTL-3c: 差分の付替** — 差分値が等しければ制限は等しい（proof-irrelevance
    で proof 引数は無視できる）。 -/
theorem ctlRestrD_congr (i j d d' : Nat) (hdd : d = d') (h : i + d = j) (h' : i + d' = j) :
    ctlRestrD i j d h = ctlRestrD i j d' h' := by
  subst hdd
  rfl

/-! ## CTL-4: 恒等保存（restr_self・d = 0 帰着） -/

/-- **CTL-4a: 差分 0 の制限は恒等** — ctlRestrD i i 0 h の作用は恒等
    （i + 0 = i は definitional・proof-irrelevance で transport 消滅）。 -/
theorem ctl_restr_selfD (i d : Nat) (hd : d = 0) (h : i + d = i)
    (x : (ctlGal i).carrier) :
    (ctlRestrD i i d h).map x = x := by
  subst hd
  rfl

/-- **CTL-4b: 恒等保存** — 同一段への制限は恒等（i − i = 0 の帰着）。
    塔の `restr_self` フィールドを本物に discharge する。 -/
theorem ctl_restr_self (i : Nat) (x : (ctlGal i).carrier) :
    (ctlRestr (Nat.le_refl i)).map x = x :=
  ctl_restr_selfD i (i - i) (Nat.sub_self i) (Nat.add_sub_cancel' (Nat.le_refl i)) x

/-! ## CTL-5: 単段 peel 補題（結合律 cast を回避する要） -/

/-- **CTL-5a: 差分明示版の単段展開** — i+d 段までの制限に最上段の単段制限
    `ctlStep` を前置すると i+(d+1) 段までの制限になる。差分再帰の定義から
    subst 後 rfl（結合律 cast 不要——最上段を peel するだけ）。 -/
theorem ctl_restr_stepD (i d m : Nat) (h : i + d = m) (h1 : i + (d + 1) = m + 1)
    (x : (ctlGal (m + 1)).carrier) :
    (ctlRestrD i (m + 1) (d + 1) h1).map x
      = (ctlRestrD i m d h).map ((ctlStep m).map x) := by
  subst h
  rfl

/-- **CTL-5b: 単段 peel** — Gal(L_{m+1}/ℚ) → Gal(L_i/ℚ)（i ≤ m+1）の制限は、
    最上段の単段制限 `ctlStep m` を施してから Gal(L_m/ℚ) → Gal(L_i/ℚ)（i ≤ m）
    の制限を施すことに等しい。(m+1)−i = (m−i)+1 の付替（`ctlRestrD_congr`）で
    差分明示版 `ctl_restr_stepD` に帰着。**結合律を一切使わない**。 -/
theorem ctl_restr_step (i m : Nat) (him : i ≤ m) (x : (ctlGal (m + 1)).carrier) :
    (ctlRestr (Nat.le_succ_of_le him)).map x
      = (ctlRestr him).map ((ctlStep m).map x) :=
  (congrArg (fun H => Hom.map H x)
    (ctlRestrD_congr i (m + 1) ((m + 1) - i) ((m - i) + 1) (by omega)
      (Nat.add_sub_cancel' (Nat.le_succ_of_le him)) (by omega))).trans
    (ctl_restr_stepD i (m - i) m (Nat.add_sub_cancel' him) (by omega) x)

/-! ## CTL-6: 推移性（restr_comp・差分帰納で結合律 cast を回避） -/

/-- **CTL-6a: 推移性（正規形・差分帰納）** — i ≤ j 固定、j 段から j+e 段への
    制限との合成。e の帰納で、各段 `ctl_restr_step` の単段 peel と帰納法だけで
    閉じる（**結合律も subst の輸送も不要**——最上段の単段 `ctlStep (j+f)` を
    peel し帰納仮説に落とす形）。 -/
theorem ctl_restr_comp_aux (i j : Nat) (hij : i ≤ j) :
    ∀ (e : Nat) (x : (ctlGal (j + e)).carrier),
      (ctlRestr hij).map ((ctlRestr (Nat.le_add_right j e)).map x)
        = (ctlRestr (Nat.le_trans hij (Nat.le_add_right j e))).map x := by
  intro e
  induction e with
  | zero =>
    intro x
    exact congrArg (ctlRestr hij).map (ctl_restr_self j x)
  | succ f ih =>
    intro x
    exact (congrArg (ctlRestr hij).map
        (ctl_restr_step j (j + f) (Nat.le_add_right j f) x)).trans
      ((ih ((ctlStep (j + f)).map x)).trans
        (ctl_restr_step i (j + f) (Nat.le_trans hij (Nat.le_add_right j f)) x).symm)

/-- **CTL-6b: 推移性（正規形の一般 k への輸送）** — j + e = k の橋で任意の k に
    移す（subst 1 回）。 -/
theorem ctl_restr_compK (i j k e : Nat) (hij : i ≤ j) (he : j + e = k) :
    ∀ (hjk : j ≤ k) (x : (ctlGal k).carrier),
      (ctlRestr hij).map ((ctlRestr hjk).map x)
        = (ctlRestr (Nat.le_trans hij hjk)).map x := by
  subst he
  intro hjk x
  exact ctl_restr_comp_aux i j hij e x

/-- **CTL-6c: 推移性** — 制限の合成は合成の制限（塔の `restr_comp` フィールド）。
    差分 e = k − j と橋 j + (k − j) = k で正規形へ帰着。 -/
theorem ctl_restr_comp {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k)
    (x : (ctlGal k).carrier) :
    (ctlRestr hij).map ((ctlRestr hjk).map x)
      = (ctlRestr (Nat.le_trans hij hjk)).map x :=
  ctl_restr_compK i j k (k - j) hij (Nat.add_sub_cancel' hjk) hjk x

/-! ## CTL-7: 塔詰め（★`ProfinitePi1Tower.restr` witness の初の本物 discharge） -/

/-- **CTL-7: 円分塔 → ProfinitePi1Tower** — 実 2 段以上の非自明円分塔
    ℚ ⊂ ℚ(ζ₃) ⊂ ℚ(ζ_9) ⊂ … の実 Galois 群と実制限準同型を逆系データとして
    嵌める。`restr`＝反復制限 `ctlRestr`、`restr_self`／`restr_comp`＝本物の証明
    `ctl_restr_self`／`ctl_restr_comp`。**従来 witness 仮説だった逆系則の初の
    本物 discharge**。 -/
def ctlTower : ProfinitePi1Tower where
  K := ratIUTField
  ext := ctlExt
  restr := fun h => ctlRestr h
  restr_self := ctl_restr_self
  restr_comp := fun hij hjk x => ctl_restr_comp hij hjk x

/-! ## CTL-8: 逆極限 profinite Gal(ℚ(ζ_{3^∞})/ℚ) と副有限性 -/

/-- **CTL-8a: 逆極限 profinite 群** — lim Gal(ℚ(ζ_{3^{n+1}})/ℚ)
    = Gal(ℚ(ζ_{3^∞})/ℚ)（本物の副有限 π₁^ét・M287F-3 `profPi1Limit`）。
    実 profinite 円分ガロア群を、実塔の逆極限として本物に構成。 -/
def ctlProfinite : Grp := profPi1Limit ctlTower

/-- **CTL-8b: 副有限性** — 逆極限の各射影核が開部分群であり、開部分群系が
    1 の近傍基をなす（M287F-6e `profPi1_is_profinite` の適用）。円分塔の
    逆極限が本来の意味で副有限群であることの機械検証。 -/
theorem ctl_is_profinite :
    (∀ n, (limitTopology (profPi1System ctlTower)).IsOpen
        (profPi1KernelSubgroup ctlTower n).mem)
      ∧ (∀ (i₀ : Nat) (U : (profPi1Limit ctlTower).carrier → Prop),
          (limitTopology (profPi1System ctlTower)).IsOpen U →
          U (profPi1Limit ctlTower).one →
          ∃ k, ∀ y, projKernel (profPi1System ctlTower) k y → U y) :=
  profPi1_is_profinite ctlTower

end IUT
