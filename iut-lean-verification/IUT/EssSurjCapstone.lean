/-
  # M194F: 柱A 本質的全射性・ガロア支配プログラムの総括 capstone —
  M161F→M186F→M189F→M160F の一括証人（柱A・並行部品）

  柱A の SGA1 本質的全射性・ガロア支配のプログラムは 4 本の並行部品に
  分かれて進んだ: M161F（推移的 Aut(A)-集合の抽象的実現）、M186F
  （有限非推移的への拡張）、M189F（ファイバー冪の SGA1 構成・抽象
  Connected の特徴づけ・抽象語彙での支配）、M160F（モデル側ガロア
  閉包のリフト）。本モジュールはこの 4 本の主要定理を**新規証明ゼロ**
  で単一の総括レコードへ束ね、「連結対象 E を一つ与えれば、その
  ガロア閉包 base 上に本質的全射性プログラム全体（推移的実現・有限和
  実現・抽象連結性の特徴づけ・支配・ファイバー冪構成）が一括で載る」
  ことを証明する:

  * M194F-1 `EssSurjCapstoneData` — 総括データ: 群 G・連結対象 E・
    基点 e₀ を固定したときの、ガロア閉包 base とその上の本質的
    全射性プログラム全部品（フィールド一覧は個々の意義参照）
  * M194F-2 `essSurjCapstoneData` — 証人: `connected_dominated_by_galois`
    系（M160F）の閉包 base = G/core(Stab e₀) を舞台に、`gsetSumData G`
    を経由した M161F/M186F の実現定理と、`gsetGaloisData G` 上の
    M189F の特徴づけ・支配・ファイバー冪構成をすべて代入するのみ
  * M194F-3 `essSurjCapstone_exists` — 存在定理

  **意義**: `EssSurjCapstoneData` の各フィールドは M161F
  `abstract_ess_surj_transitive`・M186F `abstract_ess_surj_finite`・
  M189F `abstract_connected_iff` / `connected_dominated_by_galois_abstract`
  / `powProj_fiber_surj` / `sga1Point_exists`・M160F
  `connected_dominated_by_galois` の**そのままの witness 代入**であり、
  本モジュールで新規に証明された数学的命題はゼロである。4 本の並行
  部品が「同じガロア対象 base 上で同時に成立する」ことを型として
  一箇所に固定した点が本モジュールの内容のすべてである。鍵となる
  接続は `(gsetSumData G).toGaloisCatData` と `gsetGaloisData G` が
  構造体フィールド代入の iota 簡約により**定義上等しい**こと
  （`rfl` で検証可能）——これにより M161F/M186F（`SumData`/
  `QuotientData` をパラメータに取る抽象定理）と M189F/M160F
  （`gsetGaloisData G` に固有のモデル定理）が同一の base 上で
  シームレスに合成できる。

  **正直な限定**: (1) 束ねたのは M161F-4・M186F-6・M189F-1〜3/6/7・
  M160F-3 の 7 定理（+ 従属する dom_surj）。M186F-7 の軌道版・
  M160F-4/5 の軌道系・塔系はこの総括レコードのフィールドには含めて
  いない（同じ witness から容易に導けるが、レコードを本質的全射性の
  中核 6 フィールドに絞るため割愛。束ねられなかったわけではなく、
  スコープ外に留めた）。(2) `basept` は G/core(Stab e₀) の標準代表元
  [1]（`Quot.mk _ G.one`）であり、Classical.choice を要する
  `Nonempty.some` 経由の抽出は一切行っていない。(3) M160F-3・M189F-7・
  M189F-6 の型は `gsetGaloisData G`（M21-8、G6 フィールドに
  Classical.choice）に言及するため、公理リストは Classical.choice を
  **型経由で継承**する（M160F・M189F 自身の正直な限定と同じ事情の
  再継承であり、本モジュール自体の証明ステップでの新規使用はゼロ）。
  M189F-1〜3（powObj/powProj/sga1Point 系）は任意の `GaloisCatData` で
  パラメトリックであり choice を継承しないが、本モジュールでは
  `gsetGaloisData G` に特殊化しているため、型全体としては
  Classical.choice を含む公理リストになる。

  全て新規証明ゼロ（bundling のみ）。サブエージェント並行部品。
-/
import IUT.AbstractEssSurjSum
import IUT.AbstractGaloisDomination

namespace IUT

/-! ## M194F-1: 総括データ -/

/-- **総括データ（M194F-1）**: 群 G・連結対象 E（GAction）・基点
    e₀ : E.carrier を固定したときの、E のガロア閉包 base 上に載る
    本質的全射性・ガロア支配プログラムの全部品。

    * `base`/`galois`/`basept`/`dom`/`dom_surj` — M160F のガロア
      閉包リフト（G/core(Stab e₀) が base、`closureHom` が支配射）
    * `realizeTransitive` — M161F: base 上の任意の基点付き推移的
      Aut(base)-集合の比較関手像へのスパン同型実現
    * `realizeFiniteSum` — M186F: 基点付き推移的 Aut(base)-集合の
      任意の有限リストの直和の実現（M161F の有限和拡張）
    * `connectedIff` — M189F-6: 抽象 Connected ⟺ 非空 + 推移的
      （`gsetGaloisData G` の全対象に対して）
    * `dominates` — M189F-7: 抽象語彙での支配定理（任意の連結対象は
      ガロア対象にファイバー全射で支配される）
    * `powProjSurj`/`diagPoint` — M189F-1〜3: ファイバー冪 A^n の
      射影の F-全射性と SGA1 対角点の存在（任意の対象・任意の n） -/
structure EssSurjCapstoneData (G : Grp) (E : GAction G) (e₀ : E.carrier) where
  /-- ガロア閉包対象（M160F-2a: G/core(Stab e₀)）。 -/
  base : (GSetCat G).Obj
  /-- base は抽象 IsGalois を満たす（M160F-3 / M154F-6b）。 -/
  galois : (gsetGaloisData G).IsGalois base
  /-- base の標準基点 [1]（M160F-2b、choice 不使用）。 -/
  basept : (gsetGaloisData G).F.onObj base
  /-- 閉包支配射 base → E（M160F-2a）。 -/
  dom : (GSetCat G).Hom base E
  /-- 支配射のファイバー全射性（M160F-2c）。 -/
  dom_surj : ∀ y, ∃ x, dom.map x = y
  /-- **M161F**: base 上の任意の基点付き推移的 Aut(base)-集合は
      ある対象の Hom(base,−) 値とスパン同型で実現される。 -/
  realizeTransitive : ∀ X : GAction ((gsetGaloisData G).autGrp base),
    X.Transitive → X.carrier →
    ∃ Xo : (gsetGaloisData G).C.Obj,
      SpanIso X ((gsetGaloisData G).homGAction base Xo)
  /-- **M186F**: base 上の基点付き推移的 Aut(base)-集合の任意の有限
      リストの直和もある対象の Hom(base,−) 値とスパン同型で
      実現される（M161F の有限和拡張）。 -/
  realizeFiniteSum : ∀ L : List (PointedTransitive ((gsetGaloisData G).autGrp base)),
    ∃ Xo : (gsetGaloisData G).C.Obj,
      SpanIso
        (sumListAction ((gsetGaloisData G).autGrp base) (L.map (fun P => P.space)))
        ((gsetGaloisData G).homGAction base Xo)
  /-- **M189F-6**: `gsetGaloisData G` において抽象 Connected は
      「台が非空かつ作用が推移的」と同値（完全な特徴づけ）。 -/
  connectedIff : ∀ A : (gsetGaloisData G).C.Obj,
    (gsetGaloisData G).Connected A ↔ Nonempty A.carrier ∧ A.Transitive
  /-- **M189F-7**: 抽象語彙での支配定理 — 任意の連結対象 A に対し、
      ガロア対象 B と F-全射な射 B → A が存在する。 -/
  dominates : ∀ A : (gsetGaloisData G).C.Obj, (gsetGaloisData G).Connected A →
    ∃ B : (gsetGaloisData G).C.Obj, (gsetGaloisData G).IsGalois B ∧
      ∃ φ : (gsetGaloisData G).C.Hom B A,
        ∀ y : (gsetGaloisData G).F.onObj A,
          ∃ x : (gsetGaloisData G).F.onObj B, (gsetGaloisData G).F.onHom φ x = y
  /-- **M189F-3a**: 任意の対象 A・任意の n・射影 i < n に対し、
      射影 A^n → A は F-全射（支配射の候補）。 -/
  powProjSurj : ∀ (A : (gsetGaloisData G).C.Obj) (n i : Nat) (h : i < n)
      (a : (gsetGaloisData G).F.onObj A),
    ∃ w : (gsetGaloisData G).F.onObj ((gsetGaloisData G).powObj A n),
      (gsetGaloisData G).F.onHom ((gsetGaloisData G).powProj A n i h) w = a
  /-- **M189F-3b**: ファイバーの有限枚挙 e が与えられれば、射影値が
      ファイバー全体を走る SGA1 対角点 w ∈ F(A^n) が存在する。 -/
  diagPoint : ∀ (A : (gsetGaloisData G).C.Obj) (n : Nat)
      (e : Nat → (gsetGaloisData G).F.onObj A),
    (∀ a : (gsetGaloisData G).F.onObj A, ∃ i : Nat, i < n ∧ e i = a) →
    ∃ w : (gsetGaloisData G).F.onObj ((gsetGaloisData G).powObj A n),
      ∀ a : (gsetGaloisData G).F.onObj A, ∃ (i : Nat) (h : i < n),
        (gsetGaloisData G).F.onHom ((gsetGaloisData G).powProj A n i h) w = a

/-! ## M194F-2: 証人 -/

/-- **証人（M194F-2）**: 群 G・連結対象 E・基点 e₀・E の推移性
    htrans が与えられれば、E のガロア閉包 base = G/core(Stab e₀)
    （M160F-3）を舞台に全フィールドが構成できる。

    - `base`/`galois`/`basept`/`dom`/`dom_surj` は M160F-2/3 の
      構成そのもの（`closureHom` とその全射性、標準基点 [1]）
    - `realizeTransitive`/`realizeFiniteSum` は `gsetSumData G`
      （M26-5、`(gsetSumData G).toGaloisCatData = gsetGaloisData G`
      が iota 簡約で成立、`rfl` で検証可能）を経由した M161F-4・
      M186F-6 の適用
    - `connectedIff`/`dominates` は M189F-6/7 の適用
    - `powProjSurj`/`diagPoint` は M189F-3a/3b の適用
      （`gsetGaloisData G` に特殊化） -/
noncomputable def essSurjCapstoneData (G : Grp) (E : GAction G) (e₀ : E.carrier)
    (htrans : E.Transitive) : EssSurjCapstoneData G E e₀ where
  base := cosetGSet G (coreSubgroup G (stabilizer G E e₀))
  galois := cosetGSet_core_galois G (stabilizer G E e₀)
  basept := Quot.mk (cosetRel G (coreSubgroup G (stabilizer G E e₀))) G.one
  dom := closureHom G E e₀
  dom_surj := closureHom_surjective G E e₀ htrans
  realizeTransitive := fun X hX x₀ =>
    (gsetSumData G).toQuotientData.abstract_ess_surj_transitive
      (cosetGSet_core_galois G (stabilizer G E e₀))
      (Quot.mk (cosetRel G (coreSubgroup G (stabilizer G E e₀))) G.one) X hX x₀
  realizeFiniteSum := fun L =>
    (gsetSumData G).abstract_ess_surj_finite
      (cosetGSet_core_galois G (stabilizer G E e₀))
      (Quot.mk (cosetRel G (coreSubgroup G (stabilizer G E e₀))) G.one) L
  connectedIff := abstract_connected_iff G
  dominates := fun A hA => connected_dominated_by_galois_abstract G A hA
  powProjSurj := fun A n i h a => (gsetGaloisData G).powProj_fiber_surj A n i h a
  diagPoint := fun A n e henum => (gsetGaloisData G).sga1Point_exists A n e henum

/-! ## M194F-3: 存在定理 -/

/-- **定理（M194F-3）: 本質的全射性・ガロア支配 capstone データの
    存在**（無矛盾性）— 任意の群 G の任意の連結対象（基点付き推移的
    GAction）に対して。M161F→M186F→M189F→M160F の 4 本の並行部品が
    単一のガロア対象 base 上に同時に載ることの証明。 -/
theorem essSurjCapstone_exists (G : Grp) (E : GAction G) (e₀ : E.carrier)
    (htrans : E.Transitive) :
    Nonempty (EssSurjCapstoneData G E e₀) :=
  ⟨essSurjCapstoneData G E e₀ htrans⟩

end IUT
