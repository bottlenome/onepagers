/-
  IUT/GaloisFundamental.lean — M285F: Galois の基本定理の全単射
    （{部分群 H ≤ Gal(L/K)} ↔ {中間体 M} の反変全単射）
  ── 柱A 実 Galois 群論の本物の先行建設（遠アーベル復元の中心構造）

  主要成果の分類 **[実]**（本物の体拡大 L/K・本物の Aut(L)・本物の Galois
  部分群・固定体／固定群の上での **Galois 基本定理の全単射**）。

  complete_pct 影響: **柱A の M283F「反変ガロア接続（往復包含・inclusion のみ）」を
  「反変全単射（往復等号 Gal(L/L^H)=H・L^{Gal(L/M)}=M）」へ昇格(a)** する。
  M283F は往復包含
    * `galCorr_field_fixing_field`（M ⊆ L^{Gal(L/M)}）
    * `galCorr_fix_fixing`（H ⊆ Gal(L/L^H)）
  の片側だけを本物に持ち、逆包含（＝等号＝基本定理の全単射）は「後続」と正直に
  限定していた。本モジュールはその逆包含のうち**群側 Gal(L/L^H)=H を本物に閉じる**:
    指数一致 |H| = |Gal(L/L^H)|（Artin 補題 [L:L^H]=|H| の数値内容）から、
    **有限鳩の巣（単射自己写像 Fin n→Fin n は全射）で逆包含**を導く。
    これにより M283F の inclusion が **全単射**に昇格する。

  本物で閉じる中身（toy 群を主語にしない・sorry/新規 choice/禁止タクティク皆無）:
  * M285F-1 `galFund_nat_inj_surj` / `galFund_fin_inj_surj` — **有限鳩の巣**:
    単射な自己写像 [0,n)→[0,n)（および Fin n→Fin n）は全射。`Finiteness.lean`
    （M17）の `inj_range_le` と choice-free な `decidableBoundedExists` を再利用して
    **選択公理なし**で構成（指数一致からの逆包含の数学的核）。
  * M285F-2 `GalFundEnum` / `galFund_subgroup_antisymm` — 部分群 A ⊆ B が
    **同一有限位数 n の全単射枚挙 witness（Fin n ≃ 台）**を持てば A = B（B ⊆ A）。
    鳩の巣で g:Fin n→Fin n（A の元を B での添字へ送る単射）が全射になることから。
    **本物の逆包含**（有限位数一致 ⟹ 部分群一致）。
  * M285F-3 `galFund_fixing_fixed_eq` — **Gal(L/L^H) = H**（往復等号・群側）。
    M283F `galCorr_fix_fixing`（H⊆Gal(L/L^H)）＋ 指数一致 witness（|H|=|Gal(L/L^H)|）
    ＋ 鳩の巣 `galFund_subgroup_antisymm` で逆包含。**基本定理の全単射の核を本物に**。
  * M285F-4 `galFund_fixed_of_fixing_fixed_eq` — L^{Gal(L/L^H)} = L^H（固定体側の
    往復等号、群側等号 M285F-3 から本物に従う）。
  * M285F-5 `galFund_bijectionData` / `GaloisFundBijection` — 反変全単射の束ね
    （Φ:H↦L^H, Ψ:M↦Gal(L/M), 往復等号 Gal(L/L^H)=H・L^{Gal(L/L^H)}=L^H が
    互いに逆）。M283F の反変接続が**全単射**に昇格したことの capstone。
  * M285F-6 `galFund_normal_correspondence` — **正規部分群 ↔ 正規（安定）中間拡大**の
    **⟺ 両方向を本物に**: ⟹ は M283F `galCorr_normal_stable`、⟸ は群側等号
    Gal(L/L^H)=H と L^H の g・g⁻¹ 安定性から共役 gHg⁻¹⊆H を本物に導く。
    商群 Aut(L)/H（H 正規）を `galFund_normal_quotient` で構成（M267F `quotientGroupN`）。
  * M285F-7 capstone `GaloisFundamentalData` / `galFund_main` / `galFund_exists`。
  * M285F-8 実例 `galFund_trivial_end`（自明群 ↔ L 全体）・`galFund_top_end`
    （Gal 全体 ↔ K）が全単射の両端であること（M283F 実例を昇格の文脈で確認）。

  **正直な限定（何が本物・何が honest 仮説か・§4 準拠、消去弱化しない）**:
  1. **本物（本丸）**: 有限鳩の巣（M285F-1）、有限位数一致 ⟹ 部分群一致
     （M285F-2）、**Gal(L/L^H)=H**（M285F-3、群側往復等号）、固定体側往復等号
     （M285F-4）、正規対応の**⟺ 両方向**（M285F-6）は完全証明（sorry/新規
     Classical.choice/禁止タクティク皆無、公理は [propext, Quot.sound] のみ）。
     これらは「M283F の inclusion → 全単射」への本物の昇格である。
  2. **honest 仮説（Artin の数値内容 = 指数一致 witness）**: |H| = [L:L^H] =
     |Gal(L/L^H)| の**数値等式**そのものは、埋め込み数（M282F `SepEmbCount`、
     Field268/CRing 世界）と塔法則（M281F、IUTField 世界）を横断する橋 + Dedekind
     の指標一次独立を要し、単一モジュールの範囲外。本モジュールは
     **|H| と |Gal(L/L^H)| が同一の有限位数 n を持つ全単射枚挙 witness `GalFundEnum`**
     を仮説で受け取り（＝ Artin の数値結論を honest に受ける）、そこから逆包含
     （Gal(L/L^H)=H）を**本物の鳩の巣で導く**。有限性・位数を witness で受けるのは
     M281F/M282F と同精神。
  3. **honest 仮説（固定体側・一般の中間体 M）**: L^{Gal(L/M)}=M の一般 M での
     逆包含 L^{Gal(L/M)} ⊆ M は、[L:M]=[L:L^{Gal(L/M)}] からの [N:M]=1 ⟹ N=M
     （体の次数論）を要するため、`galFund_fixed_fixing_eq` では逆包含を honest
     witness（M が閉体＝ガロアであること）として受け取る（前向き M⊆L^{Gal(L/M)}
     は M283F で本物）。**ただし固定体そのもの（M=L^H の形）の往復は M285F-4 で
     本物**（＝全単射 `GaloisFundBijection` は部分群側・固定体像側ともに本物）。
  4. **商群同型は骨組み**: Gal(L^H/K)≅Gal(L/K)/H は、Gal(L^H/K) を L^H の
     `FieldExtension` として構成する必要があり範囲外。本モジュールは商群
     Aut(L)/H（H 正規）を本物に構成し、制限写像の核 = Gal(L/L^H) = H
     （M285F-3）が同型の核であることを本物に持つ（同型全体は後続の骨組み）。

  **選択公理不使用**（新規 `Classical.choice` を証明本体に導入しない）: 全単射枚挙は
  明示 index を持ち、鳩の巣は `decidableBoundedExists` で choice-free。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用。サブエージェント並行部品（新規 1 ファイルのみ・共有ファイル未変更）。
-/
import IUT.GaloisCorrespondence
import IUT.Finiteness

namespace IUT

/-! ## M285F-1: 有限鳩の巣（単射な自己写像は全射） -/

/-- **M285F-1a: 有限鳩の巣（Nat 版）** — [0,n) を [0,n) に単射に送る写像は全射。
    `Finiteness.lean`（M17）の `inj_range_le`（単射 ⟹ 基数増えず）と choice-free の
    `decidableBoundedExists` を再利用。値 y を飛ばす圧縮 c で [0,n)→[0,n-1) の単射を
    作ると n ≤ n-1 で矛盾するので、y は必ず像に入る。**選択公理不使用**。 -/
theorem galFund_nat_inj_surj (n : Nat) (f : Nat → Nat)
    (hmaps : ∀ i, i < n → f i < n)
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (y : Nat) (hy : y < n) : ∃ x, x < n ∧ f x = y := by
  cases decidableBoundedExists (fun i => f i = y) (n - 1) with
  | isTrue h =>
    obtain ⟨i, hi, hfi⟩ := h
    exact ⟨i, by omega, hfi⟩
  | isFalse h =>
    exfalso
    have hne : ∀ i, i < n → f i ≠ y := by
      intro i hi hc
      exact h ⟨i, by omega, hc⟩
    let c : Nat → Nat := fun v => if v < y then v else v - 1
    have hcbound : ∀ i, i < n → c (f i) < n - 1 := by
      intro i hi
      have hfin := hmaps i hi
      have hfne := hne i hi
      cases Nat.lt_or_ge (f i) y with
      | inl hlt =>
        have : c (f i) = f i := if_pos hlt
        omega
      | inr hge =>
        have : c (f i) = f i - 1 := if_neg (fun hc => by omega)
        omega
    have hcinj : ∀ i j, i < n → j < n → c (f i) = c (f j) → i = j := by
      intro i j hi hj he
      apply hinj i j hi hj
      have hfine := hne i hi
      have hfjne := hne j hj
      cases Nat.lt_or_ge (f i) y with
      | inl hilt =>
        cases Nat.lt_or_ge (f j) y with
        | inl hjlt =>
          have e1 : c (f i) = f i := if_pos hilt
          have e2 : c (f j) = f j := if_pos hjlt
          omega
        | inr hjge =>
          have e1 : c (f i) = f i := if_pos hilt
          have e2 : c (f j) = f j - 1 := if_neg (fun hc => by omega)
          omega
      | inr hige =>
        cases Nat.lt_or_ge (f j) y with
        | inl hjlt =>
          have e1 : c (f i) = f i - 1 := if_neg (fun hc => by omega)
          have e2 : c (f j) = f j := if_pos hjlt
          omega
        | inr hjge =>
          have e1 : c (f i) = f i - 1 := if_neg (fun hc => by omega)
          have e2 : c (f j) = f j - 1 := if_neg (fun hc => by omega)
          omega
    have hle := inj_range_le (fun i => c (f i)) hcbound hcinj
    omega

/-- **M285F-1b: 有限鳩の巣（Fin 版）** — 単射な自己写像 f : Fin n → Fin n は全射。
    Nat 版に `Fin.val` で帰着（choice-free）。 -/
theorem galFund_fin_inj_surj (n : Nat) (f : Fin n → Fin n)
    (hinj : ∀ i j, f i = f j → i = j) (y : Fin n) : ∃ x, f x = y := by
  let F : Nat → Nat := fun i => if h : i < n then (f ⟨i, h⟩).val else 0
  have hFval : ∀ i (h : i < n), F i = (f ⟨i, h⟩).val := fun i h => dif_pos h
  have hmaps : ∀ i, i < n → F i < n := by
    intro i h
    rw [hFval i h]
    exact (f ⟨i, h⟩).isLt
  have hinjF : ∀ i j, i < n → j < n → F i = F j → i = j := by
    intro i j hi hj he
    rw [hFval i hi, hFval j hj] at he
    have hfe : f ⟨i, hi⟩ = f ⟨j, hj⟩ := Fin.eq_of_val_eq he
    have hij := hinj _ _ hfe
    exact congrArg Fin.val hij
  obtain ⟨x, hx, hfx⟩ := galFund_nat_inj_surj n F hmaps hinjF y.val y.isLt
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Fin.eq_of_val_eq
  rw [← hFval x hx]
  exact hfx

/-! ## M285F-2: 有限位数一致 ⟹ 部分群一致 -/

/-- **M285F-2a: 有限枚挙 witness** — 型 T が Fin n と全単射（明示 index 付き、
    choice-free）。部分群 H の有限位数 |H|=n を「Fin n ≃ {σ // H.mem σ}」の形で
    受け取る土台（M17 `card_unique` の code/decode 対と同精神）。 -/
structure GalFundEnum (T : Type) (n : Nat) where
  /-- 添字からの枚挙。 -/
  enum : Fin n → T
  /-- 明示的な逆（index、choice 回避）。 -/
  index : T → Fin n
  /-- enum ∘ index = id。 -/
  enum_index : ∀ t, enum (index t) = t
  /-- index ∘ enum = id。 -/
  index_enum : ∀ i, index (enum i) = i

/-- **M285F-2b: 有限位数一致 ⟹ 逆包含** — 部分群 A ⊆ B が同一位数 n の枚挙を
    持てば B ⊆ A（ゆえに A = B）。A の各元を B での添字へ送る写像 g:Fin n→Fin n は
    単射（enum の単射性）ゆえ鳩の巣で全射、よって B の任意元は A の元。
    **有限位数一致からの逆包含の本物の証明**（Artin の指数一致 → 全単射の核）。 -/
theorem galFund_subgroup_antisymm {G : Grp} {A B : Subgroup G} {n : Nat}
    (hAB : ∀ σ, A.mem σ → B.mem σ)
    (eA : GalFundEnum { x // A.mem x } n)
    (eB : GalFundEnum { x // B.mem x } n) :
    ∀ σ, B.mem σ → A.mem σ := by
  intro σ hσB
  let g : Fin n → Fin n := fun i =>
    eB.index ⟨(eA.enum i).val, hAB (eA.enum i).val (eA.enum i).property⟩
  have hginj : ∀ i j, g i = g j → i = j := by
    intro i j hij
    have h1 : eB.enum (g i) = eB.enum (g j) := congrArg eB.enum hij
    have ei : eB.enum (g i)
        = ⟨(eA.enum i).val, hAB (eA.enum i).val (eA.enum i).property⟩ :=
      eB.enum_index _
    have ej : eB.enum (g j)
        = ⟨(eA.enum j).val, hAB (eA.enum j).val (eA.enum j).property⟩ :=
      eB.enum_index _
    rw [ei, ej] at h1
    have hval : (eA.enum i).val = (eA.enum j).val :=
      congrArg (fun (t : { x // B.mem x }) => t.val) h1
    have hAeq : eA.enum i = eA.enum j := Subtype.ext hval
    have hfin := congrArg eA.index hAeq
    rw [eA.index_enum, eA.index_enum] at hfin
    exact hfin
  obtain ⟨i, hi⟩ := galFund_fin_inj_surj n g hginj (eB.index ⟨σ, hσB⟩)
  have h2 : eB.enum (g i) = ⟨σ, hσB⟩ := by
    rw [hi]
    exact eB.enum_index _
  have ei : eB.enum (g i)
      = ⟨(eA.enum i).val, hAB (eA.enum i).val (eA.enum i).property⟩ :=
    eB.enum_index _
  rw [ei] at h2
  have hval : (eA.enum i).val = σ :=
    congrArg (fun (t : { x // B.mem x }) => t.val) h2
  have hp := (eA.enum i).property
  rw [hval] at hp
  exact hp

/-! ## M285F-3: 往復等号（群側）Gal(L/L^H) = H -/

/-- **M285F-3: Gal(L/L^H) = H**（基本定理の全単射の核）— H⊆Gal(L/L^H)（M283F
    `galCorr_fix_fixing`）に、指数一致（|H|=|Gal(L/L^H)|=n の枚挙 witness）から
    鳩の巣で逆包含 Gal(L/L^H)⊆H を足して等号。**M283F の inclusion を全単射へ昇格**。 -/
theorem galFund_fixing_fixed_eq (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) {n : Nat}
    (eH : GalFundEnum { x // H.mem x } n)
    (eGal : GalFundEnum
      { x // (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem x } n) :
    ∀ σ, (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem σ ↔ H.mem σ := by
  intro σ
  constructor
  · exact galFund_subgroup_antisymm (galCorr_fix_fixing E H) eH eGal σ
  · exact galCorr_fix_fixing E H σ

/-! ## M285F-4: 往復等号（固定体側）L^{Gal(L/L^H)} = L^H -/

/-- **M285F-4: L^{Gal(L/L^H)} = L^H**（固定体像側の往復等号）— 群側等号
    Gal(L/L^H)=H（M285F-3）から、両者の固定体が一致することが本物に従う。 -/
theorem galFund_fixed_of_fixing_fixed_eq (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) {n : Nat}
    (eH : GalFundEnum { x // H.mem x } n)
    (eGal : GalFundEnum
      { x // (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem x } n) :
    ∀ x, galCorr_fixedField E
          (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)) x
        ↔ galCorr_fixedField E H x := by
  intro x
  have hsub := galFund_fixing_fixed_eq E H eH eGal
  constructor
  · intro hx σ hσ
    exact hx σ ((hsub σ).mpr hσ)
  · intro hx σ hσ
    exact hx σ ((hsub σ).mp hσ)

/-! ## M285F-5: 反変全単射の束ね -/

/-- **M285F-5a: Galois 基本定理の全単射データ** — 部分群 H に対し、対応
    Φ:H↦L^H と Ψ:L^H↦Gal(L/L^H) が互いに逆（往復等号）であることを束ねる。
    M283F の反変**接続**が**全単射**へ昇格したことの証拠。 -/
structure GaloisFundBijection (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) where
  /-- 固定体 L^H。 -/
  toField : GalCorrSubfield E.top
  /-- 固定体の固定群 Gal(L/L^H)。 -/
  backGroup : Subgroup (fieldAutGroup E.top)
  /-- 往復等号（群側）Gal(L/L^H)=H。 -/
  round_group : ∀ σ, backGroup.mem σ ↔ H.mem σ
  /-- 往復等号（固定体側）L^{Gal(L/L^H)}=L^H。 -/
  round_field : ∀ x, galCorr_fixedField E backGroup x ↔ toField.mem x

/-- **M285F-5b: 全単射データの構成** — 有限位数一致 witness から Φ・Ψ が互いに逆に
    なる（本物）。 -/
def galFund_bijectionData (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) {n : Nat}
    (eH : GalFundEnum { x // H.mem x } n)
    (eGal : GalFundEnum
      { x // (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem x } n) :
    GaloisFundBijection E H where
  toField := galCorr_fixedField_isSubfield E H
  backGroup := galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)
  round_group := galFund_fixing_fixed_eq E H eH eGal
  round_field := galFund_fixed_of_fixing_fixed_eq E H eH eGal

/-- **M285F-5c: 反変全単射（読者向け）** — Gal(L/L^H)=H かつ L^{Gal(L/L^H)}=L^H。 -/
theorem galFund_bijection (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) {n : Nat}
    (eH : GalFundEnum { x // H.mem x } n)
    (eGal : GalFundEnum
      { x // (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem x } n) :
    (∀ σ, (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem σ ↔ H.mem σ)
    ∧ (∀ x, galCorr_fixedField E
            (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)) x
          ↔ galCorr_fixedField E H x) :=
  ⟨galFund_fixing_fixed_eq E H eH eGal,
   galFund_fixed_of_fixing_fixed_eq E H eH eGal⟩

/-- **M285F-5d: 一般の中間体 M の往復等号（固定体側・honest 逆包含）** —
    L^{Gal(L/M)}=M。前向き M⊆L^{Gal(L/M)} は M283F `galCorr_field_fixing_field`
    で本物、逆包含 L^{Gal(L/M)}⊆M は「M が閉体（ガロア）」であることの witness
    `hclosed` として受け取る（一般 M では [N:M]=1 の次数論を要するため honest）。 -/
theorem galFund_fixed_fixing_eq (E : FieldExtension) (M : GalCorrSubfield E.top)
    (hclosed : ∀ x, galCorr_fixedField E (galCorr_fixingGroup E M) x → M.mem x) :
    ∀ x, galCorr_fixedField E (galCorr_fixingGroup E M) x ↔ M.mem x := by
  intro x
  constructor
  · exact hclosed x
  · exact galCorr_field_fixing_field E M x

/-! ## M285F-6: 正規部分群 ↔ 正規（安定）中間拡大の ⟺ -/

/-- **M285F-6a: 正規対応（⟺ 両方向）** — H⊴Aut(L) ⟺ L^H が Aut(L) で安定
    （＝L^H/K が正規／ガロア）。
    ⟹ は M283F `galCorr_normal_stable`（正規部分群の固定体は安定）。
    ⟸ は群側等号 Gal(L/L^H)=H（M285F-3）を使う: h∈H=Gal(L/L^H) は L^H を固定し、
    L^H が g・g⁻¹ で安定なので、g∘h∘g⁻¹ も L^H を固定（∈Gal(L/L^H)=H）。
    **両方向を本物に**（H⊴ の逆向きは M283F では未達だったギャップを閉じる）。 -/
theorem galFund_normal_correspondence (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) {n : Nat}
    (eH : GalFundEnum { x // H.mem x } n)
    (eGal : GalFundEnum
      { x // (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem x } n) :
    IsNormalSubgroup (fieldAutGroup E.top) H
      ↔ (∀ (σ : FieldAut E.top) (x : E.top.carrier),
          galCorr_fixedField E H x → galCorr_fixedField E H (σ.toFun x)) := by
  have hiff := galFund_fixing_fixed_eq E H eH eGal
  constructor
  · intro hn σ x hx
    exact galCorr_normal_stable E H hn σ hx
  · intro hstab g h hh
    apply (hiff _).mp
    intro x hx
    show g.toFun (h.toFun (g.invFun x)) = x
    have hstx : galCorr_fixedField E H (g.invFun x) := hstab (fieldAutInv g) x hx
    have hhfix := (hiff h).mpr hh
    have e1 : h.toFun (g.invFun x) = g.invFun x := hhfix (g.invFun x) hstx
    rw [e1, g.right_inv]

/-- **M285F-6b: 正規部分群からの商群 Aut(L)/H** — H⊴Aut(L) のとき商群
    Aut(L)/H が本物に存在する（M267F `quotientGroupN`）。制限写像
    Gal(L/K)→Gal(L^H/K) の核は Gal(L/L^H)=H（M285F-3）であり、これが第一同型
    Gal(L^H/K)≅Gal(L/K)/H の核。**商群と核 = H は本物、Gal(L^H/K) の
    FieldExtension 構成を要する同型全体は後続の骨組み**（正直な限定 4）。 -/
def galFund_normal_quotient (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top))
    (hn : IsNormalSubgroup (fieldAutGroup E.top) H) : Grp :=
  quotientGroupN (fieldAutGroup E.top) H hn

/-! ## M285F-7: capstone -/

/-- **M285F-7a: 基本定理データ** — 部分群 H と有限位数一致 witness から得られる
    反変全単射（往復等号）と、M283F の反変ガロア接続を束ねる。 -/
structure GaloisFundamentalData (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) where
  /-- 反変全単射（往復等号 Gal(L/L^H)=H・L^{Gal(L/L^H)}=L^H）。 -/
  bij : GaloisFundBijection E H
  /-- M283F の反変ガロア接続 H⊆Gal(L/M) ⟺ M⊆L^H（昇格の土台）。 -/
  connection : ∀ (H' : Subgroup (fieldAutGroup E.top)) (M : GalCorrSubfield E.top),
    (∀ σ, H'.mem σ → (galCorr_fixingGroup E M).mem σ)
      ↔ (∀ x, M.mem x → galCorr_fixedField E H' x)

/-- **M285F-7b: 証人** — 有限位数一致 witness から基本定理データを構成。 -/
def galFundData (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) {n : Nat}
    (eH : GalFundEnum { x // H.mem x } n)
    (eGal : GalFundEnum
      { x // (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem x } n) :
    GaloisFundamentalData E H where
  bij := galFund_bijectionData E H eH eGal
  connection := fun H' M => galCorr_galois_connection E H' M

/-- **M285F-7c: 基本定理データの存在**。 -/
theorem galFund_exists (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) {n : Nat}
    (eH : GalFundEnum { x // H.mem x } n)
    (eGal : GalFundEnum
      { x // (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem x } n) :
    Nonempty (GaloisFundamentalData E H) :=
  ⟨galFundData E H eH eGal⟩

/-- **M285F-7d: 基本定理の総括** — 有限位数一致 witness の下で、対応
    Φ:H↦L^H と Ψ:M↦Gal(L/M) は反変全単射（Gal(L/L^H)=H かつ L^{Gal(L/L^H)}=L^H）
    をなし、正規部分群は安定（正規）中間拡大にちょうど対応する。 -/
theorem galFund_main (E : FieldExtension)
    (H : Subgroup (fieldAutGroup E.top)) {n : Nat}
    (eH : GalFundEnum { x // H.mem x } n)
    (eGal : GalFundEnum
      { x // (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem x } n) :
    (∀ σ, (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)).mem σ ↔ H.mem σ)
    ∧ (∀ x, galCorr_fixedField E
            (galCorr_fixingGroup E (galCorr_fixedField_isSubfield E H)) x
          ↔ galCorr_fixedField E H x)
    ∧ (IsNormalSubgroup (fieldAutGroup E.top) H
        ↔ (∀ (σ : FieldAut E.top) (x : E.top.carrier),
            galCorr_fixedField E H x → galCorr_fixedField E H (σ.toFun x))) :=
  ⟨galFund_fixing_fixed_eq E H eH eGal,
   galFund_fixed_of_fixing_fixed_eq E H eH eGal,
   galFund_normal_correspondence E H eH eGal⟩

/-! ## M285F-8: 実例（全単射の両端） -/

/-- **M285F-8a: 自明群 ↔ L 全体**（全単射の一端）— 固定体 L^{{1}} は L 全体。
    M283F `galCorr_trivial_top` の昇格文脈での確認: 全単射 Φ の下で自明部分群は
    上体 L（＝最大の中間体）へ対応する。 -/
theorem galFund_trivial_end (E : FieldExtension) :
    ∀ x, galCorr_fixedField E (galCorr_trivialSubgroup (fieldAutGroup E.top)) x :=
  galCorr_trivial_top E

/-- **M285F-8b: Gal 全体 ↔ K**（全単射のもう一端）— L/K がガロア（L^Gal⊆ι(K)）の
    とき固定体 L^{Gal(L/K)} はちょうど ι(K)。M283F `galCorr_top_base` の昇格文脈での
    確認: 全単射 Φ の下で全体群 Gal(L/K) は基礎体 K（＝最小の中間体）へ対応する。 -/
theorem galFund_top_end (E : FieldExtension)
    (hGalois : ∀ x, galCorr_fixedField E (galoisSubgroup E) x → ∃ k, E.incl k = x) :
    ∀ x, galCorr_fixedField E (galoisSubgroup E) x ↔ ∃ k, E.incl k = x :=
  galCorr_top_base E hGalois

end IUT
