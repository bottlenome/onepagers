/-
  # M189F: ガロア対象による支配（抽象公理版）— ファイバー冪の SGA1 構成と
  抽象連結性の特徴づけ（柱A A-2/A-3α・並行部品）

  A-2/A-3α の残余「ガロア対象の十分性」（任意の連結対象はガロア対象に
  支配される — pro-表現可能性のゲート補題）に対し、(i) SGA1 の
  ガロア閉包構成の**抽象公理側の土台**（ファイバー冪 A^n・射影・
  SGA1 対角点、任意の `GaloisCatData` で choice 不要）と、(ii) 支配定理
  そのものの**抽象語彙での完結**（全てのモデル実例 `gsetGaloisData G` に
  対し、仮定を M21 の抽象 `Connected` にとった支配の導出）を与える:

  * M189F-1 `powObj` / `powProj` — **有限ファイバー冪 A^n と射影**:
    公理 G1（終対象・ファイバー積）だけから n 重積 A^n = A ×_T ⋯ ×_T A
    と n 本の射影 A^n → A を Nat 再帰で構成（SGA1 V.4 のガロア閉包
    構成の第一歩。任意の抽象ガロア圏で成立）
  * M189F-2 `powPt_ext` / `powPt_exists` — **F はファイバー冪を保つ**:
    F(A^n) の点は n 本の射影値で一意に決まり（外延性、G4 の
    ファイバー積単射性の反復）、任意の値の列 v : Nat → F(A) に対し
    射影値がちょうど v になる点が存在する（G4 の全射性の反復）。
    すなわち F(A^n) ≅ F(A)^n の全単射対応が公理のみから出る
  * M189F-3 `powProj_fiber_surj` / `sga1Point_exists` — **射影の被覆性と
    SGA1 対角点**: 各射影 A^n → A は F-全射（= 支配射の候補）であり、
    ファイバーの有限枚挙 e が与えられれば「射影値がファイバー全体を
    走る」点 w ∈ F(A^n)（SGA1 のガロア閉包構成で連結成分をとるべき
    対角型の点）が存在する
  * M189F-4 `ptHom` / `gset_mono_fiber_injective` — **モデルで抽象モノは
    ファイバー単射**: 正則作用 regAction（M14）をテスト対象に取り、
    圏論的モノ性からファイバー単射性を choice 不要で導出（軌道写像
    g ↦ g·e のモノ性テスト）
  * M189F-5 `orbitIncl` / `abstract_connected_transitive` — **抽象
    Connected ⟹ 推移性**: 軌道の包含はファイバー単射なのでモノ
    （M21-5）、抽象連結性により同型、よって軌道 = 全体で推移的
  * M189F-6 `transitive_abstract_connected` / `abstract_connected_iff` —
    **逆向きと特徴づけ**: 基点 + 推移性から抽象 Connected を導出
    （モノ ⟹ ファイバー単射は M189F-4、全射は推移性、同型化は G6）。
    合わせて「抽象 Connected ⟺ 非空 + 推移的」の完全な特徴づけ。
    M160F の正直な限定 (1)（「E 自身の抽象 Connected の導出は範囲外」）
    はここで**解消**された（choice の新規使用ゼロ — G6 は公理
    フィールドの適用であり構成ではない）
  * M189F-7 `connected_dominated_by_galois_abstract` — **主定理**:
    任意の群 G のモデル実例 D = `gsetGaloisData G` において、
    **仮定・結論とも抽象語彙**（D.Connected / D.IsGalois / D.F の全射）
    の支配定理: D.Connected A ならガロア対象 B と F-全射 B → A が
    存在する。M189F-5 で抽象連結性から推移性を取り出し、M160F-3
    （モデル側閉包 G/core(Stab e₀)）に接続する
  * M189F-8 `AbstractGaloisDominationData` / `gsetGaloisDominationWitness`
    / `abstractGaloisDomination_exists` — 総括データ（`GaloisCatData` 上の
    支配ステートメントの構造体）・モデル実例の証人・存在定理

  **意義**: pro-表現可能性（A-3）のゲート補題「十分多くのガロア対象」の
  ステートメントが `GaloisCatData` の語彙で構造体化され（M189F-8）、
  全てのモデル実例で充足された（M189F-7）。さらに将来の純公理側導出の
  ために、SGA1 閉包構成の前半（ファイバー冪と対角点）が任意の抽象
  ガロア圏で choice 不要で準備された（M189F-1〜3）。M160F（モデル語彙の
  閉包）と M161F/M186F（抽象本質的全射性）の間に残っていた語彙の溝
  — 「モデルの推移性」対「抽象の Connected」— は M189F-6 の特徴づけで
  埋まった。

  **正直な限定**: (1) 本モジュールはスライス 2+3 である: 任意の抽象
  `GaloisCatData` に対する純公理側の支配定理（M189F-8 の構造体を
  **任意の** D で充たすこと）は未達成のまま残る。SGA1 の残りの一歩
  「対角点を通る連結成分をとり、それがガロアであることを示す」には
  連結成分分解の公理（G2 後半の有限和分解・Noether 性）が必要で、
  現行の `GaloisCatData` のフィールドには含まれない（公理拡張は共有
  ファイルの変更を要するため本並行部品の範囲外）。ファイバー冪・
  対角点まで（M189F-1〜3）が現公理系で到達可能な純抽象部分である。
  (2) よって A-2/A-3α は「閉じた」のではなく、**ゲート補題の抽象
  ステートメント化 + 全モデル実例での充足 + 純抽象側の構成の前半**
  まで進んだ、が正確な現状である。(3) `sga1Point_exists` の枚挙仮定
  （ファイバーの有限性）は仮定として受け取る — 現公理系はファイバーの
  有限性公理を持たないため。(4) M189F-4〜8 は型が `gsetGaloisData G`
  （M21-8、G6 フィールドに Classical.choice）に言及するため公理リストに
  Classical.choice を**型経由で継承**する（M160F と同じ事情、継承であり
  本モジュールでの新規使用はゼロ）。M189F-1〜3（powObj/powProj/
  powPt/sga1Point 系）は任意の D でパラメトリックであり継承もない。

  全て選択公理不使用（型継承を除く）。サブエージェント並行部品。
-/
import IUT.GaloisClosureLift

namespace IUT

universe u v

namespace GaloisCatData

variable (D : GaloisCatData.{u, v})

/-! ## M189F-1: 有限ファイバー冪 A^n と射影（公理 G1 のみ） -/

/-- **ファイバー冪 A^n**（M189F-1a）: A^0 = T（終対象）、
    A^(n+1) = A ×_T A^n。公理 G1 の選択されたファイバー積データ
    （`prodObj`）の Nat 反復。SGA1 のガロア閉包構成
    「連結対象 A の |F(A)| 重積の連結成分」の積の部分。 -/
def powObj (A : D.C.Obj) : Nat → D.C.Obj
  | 0 => D.T
  | n + 1 => D.prodObj A (powObj A n)

/-- **射影 A^n → A**（M189F-1b）: i 番目の成分への射影
    （i < n）。第一射影と第二射影の反復合成。 -/
def powProj (A : D.C.Obj) : (n i : Nat) → i < n → D.C.Hom (D.powObj A n) A
  | 0, i, h => absurd h (Nat.not_lt_zero i)
  | n + 1, 0, _ => D.pr₁ A (D.powObj A n)
  | n + 1, i + 1, h =>
    D.C.comp (D.pr₂ A (D.powObj A n))
      (powProj A n i (Nat.lt_of_succ_lt_succ h))

/-! ## M189F-2: F はファイバー冪を保つ（G4 の反復） -/

/-- **点の外延性（M189F-2a）**: F(A^n) の二点は全ての射影値が
    一致すれば等しい。G4（F はファイバー積を保つ）の単射部と
    終対象の一点性（fT_unique）の Nat 帰納。
    「F(A^n) → F(A)^n は単射」の抽象形。 -/
theorem powPt_ext (A : D.C.Obj) (n : Nat) :
    ∀ w w' : D.F.onObj (D.powObj A n),
      (∀ (i : Nat) (h : i < n),
        D.F.onHom (D.powProj A n i h) w = D.F.onHom (D.powProj A n i h) w') →
      w = w' := by
  induction n with
  | zero =>
    intro w w' _
    exact D.fT_unique w w'
  | succ n ih =>
    intro w w' h
    refine D.fpb_inj (D.toT A) (D.toT (D.powObj A n)) w w' ?_ ?_
    · exact h 0 (Nat.succ_pos n)
    · apply ih
      intro i hi
      rw [← D.fmap_comp, ← D.fmap_comp]
      exact h (i + 1) (Nat.succ_lt_succ hi)

/-- **組点の存在（M189F-2b）**: 任意の値の列 v : Nat → F(A) に対し、
    i 番目の射影値が v i になる点 w ∈ F(A^n) が存在する。
    G4 の全射部（fpb_surj）の Nat 帰納。choice 不要（点は ∃ で
    渡し、帰納の各段で fpb_surj が witness を供給する）。
    「F(A^n) → F(A)^n は全射」の抽象形であり、M189F-2a と併せて
    **F はファイバー冪を保つ**（F(A^n) ≅ F(A)^n）。 -/
theorem powPt_exists (A : D.C.Obj) (n : Nat) :
    ∀ v : Nat → D.F.onObj A,
      ∃ w : D.F.onObj (D.powObj A n),
        ∀ (i : Nat) (h : i < n), D.F.onHom (D.powProj A n i h) w = v i := by
  induction n with
  | zero =>
    intro v
    refine ⟨D.fT, ?_⟩
    intro i h
    exact absurd h (Nat.not_lt_zero i)
  | succ n ih =>
    intro v
    obtain ⟨w', hw'⟩ := ih (fun i => v (i + 1))
    obtain ⟨w, hw1, hw2⟩ := D.fpb_surj (D.toT A) (D.toT (D.powObj A n))
      (v 0) w' (D.fT_unique _ _)
    refine ⟨w, ?_⟩
    intro i h
    cases i with
    | zero => exact hw1
    | succ i =>
      show D.F.onHom (D.C.comp (D.pb₂ (D.toT A) (D.toT (D.powObj A n)))
        (D.powProj A n i (Nat.lt_of_succ_lt_succ h))) w = v (i + 1)
      rw [D.fmap_comp, hw2]
      exact hw' i (Nat.lt_of_succ_lt_succ h)

/-! ## M189F-3: 射影の被覆性と SGA1 対角点 -/

/-- **射影の F-全射性（M189F-3a）**: 各射影 A^n → A（i < n）は
    ファイバー全射である — ファイバー冪から A への**支配射の候補**。
    定値列 (a, a, …) の組点（M189F-2b）が原像を与える。 -/
theorem powProj_fiber_surj (A : D.C.Obj) (n i : Nat) (h : i < n)
    (a : D.F.onObj A) :
    ∃ w : D.F.onObj (D.powObj A n), D.F.onHom (D.powProj A n i h) w = a := by
  obtain ⟨w, hw⟩ := D.powPt_exists A n (fun _ => a)
  exact ⟨w, hw i h⟩

/-- **SGA1 対角点の存在（M189F-3b）**: ファイバー F(A) の有限枚挙
    e : Nat → F(A)（∀ a, ∃ i < n, e i = a）が与えられれば、
    **射影値がファイバー全体を走る**点 w ∈ F(A^n) が存在する。
    これは SGA1 V.4 のガロア閉包構成で「その点を通る連結成分をとる」
    べき対角型の点 (a₁, …, aₙ) ∈ F(A)^n の抽象形である。残る一歩
    （w を通る連結成分の抽出とそのガロア性）には連結成分分解の公理が
    必要で、現行の `GaloisCatData` の範囲外（正直な限定 (1)）。 -/
theorem sga1Point_exists (A : D.C.Obj) (n : Nat) (e : Nat → D.F.onObj A)
    (henum : ∀ a : D.F.onObj A, ∃ i : Nat, i < n ∧ e i = a) :
    ∃ w : D.F.onObj (D.powObj A n),
      ∀ a : D.F.onObj A, ∃ (i : Nat) (h : i < n),
        D.F.onHom (D.powProj A n i h) w = a := by
  obtain ⟨w, hw⟩ := D.powPt_exists A n e
  refine ⟨w, ?_⟩
  intro a
  obtain ⟨i, hi, he⟩ := henum a
  exact ⟨i, hi, (hw i hi).trans he⟩

end GaloisCatData

/-! ## M189F-4: モデルで抽象モノはファイバー単射（正則作用テスト） -/

/-- **軌道写像（M189F-4a）**: 点 e ∈ E に対する評価写像
    g ↦ g·e : G_reg → E は同変（正則作用 `regAction`（M14）を
    テスト対象とするモノ性テストの道具）。 -/
def ptHom (G : Grp) (E : GAction G) (e : E.carrier) :
    ActHom (regAction G) E where
  map := fun g => E.act g e
  equivariant := fun g x => E.act_mul g x e

/-- **補題（M189F-4b）: 抽象モノ ⟹ ファイバー単射（モデル）** —
    `GSetCat G` で圏論的モノ射はファイバー（台集合）単射である。
    m(e) = m(e') なら軌道写像 g ↦ g·e と g ↦ g·e' の m との合成が
    一致し、モノ性で軌道写像自体が一致、単位元での値をとれば e = e'。
    choice 不要（テスト対象は正則作用という明示構成）。 -/
theorem gset_mono_fiber_injective (G : Grp) {E A : GAction G}
    (m : ActHom E A) (hm : (gsetGaloisData G).Mono m) :
    ∀ e e', m.map e = m.map e' → e = e' := by
  intro e e' h
  have hcomp : (GSetCat G).comp (ptHom G E e) m
      = (GSetCat G).comp (ptHom G E e') m := by
    apply ActHom.ext
    intro g
    show m.map (E.act g e) = m.map (E.act g e')
    rw [m.equivariant, m.equivariant, h]
  have heq := hm (ptHom G E e) (ptHom G E e') hcomp
  have he : E.act G.one e = E.act G.one e' :=
    congrFun (congrArg ActHom.map heq) G.one
  rw [E.act_one, E.act_one] at he
  exact he

/-! ## M189F-5: 抽象 Connected ⟹ 推移性 -/

/-- **軌道の包含（M189F-5a）**: 軌道 orbitOf A x₀（M16-3）から A への
    包含は同変（値の包含は作用と可換）。 -/
def orbitIncl (G : Grp) (A : GAction G) (x₀ : A.carrier) :
    ActHom (orbitOf A x₀) A where
  map := fun p => p.val
  equivariant := fun _ _ => rfl

/-- **定理（M189F-5b）: 抽象 Connected ⟹ 推移的** — A が M21 の
    抽象連結性を満たせばモデルの語彙で推移的である。x の軌道の包含は
    ファイバー単射なのでモノ（M21-5 `mono_of_fiber_injective`）、
    軌道は x を含むので非空、よって抽象連結性により同型 — すなわち
    軌道 = 全体であり、任意の y が x の軌道に入る。choice 不要。 -/
theorem abstract_connected_transitive (G : Grp) {A : GAction G}
    (hA : (gsetGaloisData G).Connected A) : A.Transitive := by
  intro x y
  have hmono : (gsetGaloisData G).Mono (orbitIncl G A x) :=
    (gsetGaloisData G).mono_of_fiber_injective (orbitIncl G A x)
      (fun a b hab => Subtype.ext hab)
  have hne : Nonempty ((gsetGaloisData G).F.onObj (orbitOf A x)) :=
    ⟨⟨x, orbitRel_refl A x⟩⟩
  obtain ⟨ginv, _, hg2⟩ := hA.2 (orbitIncl G A x) hmono hne
  have hy : (orbitIncl G A x).map (ginv.map y) = y :=
    congrFun (congrArg ActHom.map hg2) y
  obtain ⟨g, hgx⟩ := (ginv.map y).property
  refine ⟨g, ?_⟩
  rw [hgx]
  exact hy

/-! ## M189F-6: 逆向きと特徴づけ（M160F 正直な限定 (1) の解消） -/

/-- **定理（M189F-6a）: 基点 + 推移的 ⟹ 抽象 Connected** —
    M160F の正直な限定 (1) が範囲外としていた向き。非空ファイバーを
    持つモノ部分対象 m : E' → A について、ファイバー単射は
    M189F-4b（正則作用テスト、choice 不要）、ファイバー全射は
    A の推移性（e₀ の像を任意の点へ運ぶ）から従い、G6
    （`reflect_iso`、公理フィールドの適用）で m は同型になる。
    本証明での choice の新規使用はゼロ（G6 は `gsetGaloisData` の
    既存フィールド）。 -/
theorem transitive_abstract_connected (G : Grp) {A : GAction G}
    (a₀ : A.carrier) (htrans : A.Transitive) :
    (gsetGaloisData G).Connected A := by
  refine ⟨⟨a₀⟩, ?_⟩
  intro E m hm hne
  obtain ⟨e₀⟩ := hne
  have hsurj : ∀ a, ∃ e, m.map e = a := by
    intro a
    obtain ⟨g, hg⟩ := htrans (m.map e₀) a
    refine ⟨E.act g e₀, ?_⟩
    rw [m.equivariant]
    exact hg
  exact (gsetGaloisData G).reflect_iso m
    (gset_mono_fiber_injective G m hm) hsurj

/-- **系（M189F-6b）: 抽象連結性の完全な特徴づけ（モデル）** —
    `gsetGaloisData G` において、M21 の抽象 Connected はモデルの語彙
    「台が非空かつ作用が推移的」と同値である。抽象公理側（M161F/M186F
    の Connected）とモデル側（M160F の基点 + 推移性）の語彙の溝を
    埋める橋。 -/
theorem abstract_connected_iff (G : Grp) (A : GAction G) :
    (gsetGaloisData G).Connected A ↔ Nonempty A.carrier ∧ A.Transitive := by
  refine ⟨fun h => ⟨h.1, abstract_connected_transitive G h⟩, fun h => ?_⟩
  obtain ⟨⟨a₀⟩, htrans⟩ := h
  exact transitive_abstract_connected G a₀ htrans

/-! ## M189F-7: 主定理 — 抽象語彙での支配（モデル実例） -/

/-- **主定理（M189F-7）: ガロア対象による支配・抽象語彙版（モデル
    実例）** — 任意の群 G のモデル実例 D = `gsetGaloisData G` において、
    仮定・結論とも M21 の抽象語彙で: D.Connected A ならば、
    D.IsGalois を満たす対象 B と D.F が全射に送る射 φ : B → A が
    存在する。M189F-5b で抽象連結性から基点と推移性を取り出し、
    M160F-3 `connected_dominated_by_galois`（閉包 G/core(Stab a₀)）に
    接続する。これは A-2/A-3α のゲート補題「十分多くのガロア対象」の
    抽象ステートメントを全てのモデル実例で充足するものである
    （任意の抽象 D での純公理側導出は正直な限定 (1) 参照）。 -/
theorem connected_dominated_by_galois_abstract (G : Grp)
    (A : (gsetGaloisData G).C.Obj)
    (hA : (gsetGaloisData G).Connected A) :
    ∃ B : (gsetGaloisData G).C.Obj,
      (gsetGaloisData G).IsGalois B ∧
      ∃ φ : (gsetGaloisData G).C.Hom B A,
        ∀ y : (gsetGaloisData G).F.onObj A,
          ∃ x : (gsetGaloisData G).F.onObj B,
            (gsetGaloisData G).F.onHom φ x = y := by
  obtain ⟨a₀⟩ := hA.1
  obtain ⟨B, hB, φ, hφ⟩ := connected_dominated_by_galois G A a₀
    (abstract_connected_transitive G hA)
  exact ⟨B, hB, φ, hφ⟩

/-! ## M189F-8: 総括 -/

/-- **総括データ（M189F-8a）**: 抽象ガロア圏 D に対する「十分多くの
    ガロア対象」（ガロア対象による支配）のステートメントの構造体化 —
    pro-表現可能性（A-3、M24 `GaloisTower` の塔の供給）のゲート補題の
    `GaloisCatData` 語彙での定式化。 -/
structure AbstractGaloisDominationData (D : GaloisCatData.{u, v}) where
  /-- 支配: 任意の抽象連結対象 A に対し、ガロア対象 B と
      F-全射な射 B → A が存在する。 -/
  dominates : ∀ A : D.C.Obj, D.Connected A →
    ∃ B : D.C.Obj, D.IsGalois B ∧
      ∃ φ : D.C.Hom B A,
        ∀ y : D.F.onObj A, ∃ x : D.F.onObj B, D.F.onHom φ x = y

/-- **証人（M189F-8b）**: 任意の群 G のモデル実例 `gsetGaloisData G` は
    支配ステートメントを充足する（M189F-7）。 -/
def gsetGaloisDominationWitness (G : Grp) :
    AbstractGaloisDominationData (gsetGaloisData G) where
  dominates := fun A hA => connected_dominated_by_galois_abstract G A hA

/-- **定理（M189F-8c）: 抽象支配データの存在**（無矛盾性）—
    全てのモデル実例で。任意の抽象 D での充足は残余（正直な限定 (1)）。 -/
theorem abstractGaloisDomination_exists (G : Grp) :
    Nonempty (AbstractGaloisDominationData (gsetGaloisData G)) :=
  ⟨gsetGaloisDominationWitness G⟩

end IUT
