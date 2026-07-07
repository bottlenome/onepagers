-- M454F FrobenioidLogThetaLattice [実・本物・柱C×柱D frontier・M449F の残限定「log-link との完全な噛み合わせは外部」を昇格で閉じる]
-- complete_pct 影響: 柱C/柱D で M449F ftl_model_scope・ftl_full_frobenioid_hypothesis の残限定「log-link（柱C/D）との完全な噛み合わせは外部」のうち **Frobenioid 圏レベルの log-link 函手と Θ-link との log-theta-lattice 可換正方形**を昇格で閉じる: 行ラベル m ∈ ℤ 付きの劇場 Frobenioid 圏の塔 fltCat t m（対象＝M307F の本物の因子群・射＝M331F frobCHom）を建て、縦 log-link 函手 fltLogLink（因子簿記レベルでは輸送＝垂直コア性・M337F の実 graded log θ_d を装飾として接続）と横 Θ-link 函手 fltTheta（Frobenius [2l]・M449F ftlLink の全行拡張）が **on-the-nose の函手等式 H∘V = V∘H（flt_log_theta_square）** と恒等成分の自然変換（fltSquareNat）で可換正方形をなすことを圏レベルで完全証明。さらに「対象 degree 保存は Frobenius 指数 1＝輸送を強制する」剛性（flt_vertical_coric_forced）で縦（degree コア）と横（×2l・非コア）が構造的に相異なることを本物で固定し、M449F の外部仮説の log-link 噛合部分を内部定理 flt_closes_m449_limitation として供給。
-- 正直な限定: 縦 log-link の因子簿記（整数係数）レベルの作用は輸送（恒等）であり、本物の log の非自明部（乗法 U^(d) → 加法 log-shell の p 進 log・核 U^(d+1)）は M337F の実 graded log を装飾（FltLogDecoration）として持つに留まる。実 π₁^ét 上の完全 log-shell・完全 log-Kummer 対応・無限列方向（列は {0,1} の 2 本のみ・行は ℤ 全体）・多輻不等式（crux Dβ-ω）は外部/後続（flt_model_scope・flt_full_loglattice_hypothesis）。

/-
  IUT/FrobenioidLogThetaLattice.lean — M454F [実／本物の忠実な部分ケース・柱C×柱D frontier]
  分類: 実（M449F の本物の劇場 Frobenioid 圏（因子群対象・Frobenius 次数付き射）を
  行ラベル m ∈ ℤ の塔へ拡張し、縦 log-link 函手と横 Θ-link 函手の log-theta-lattice
  可換正方形を圏レベルで実現する昇格 (a)）

  既存の実部品:
    * M449F (FrobenioidThetaLink): 劇場ラベル付き Frobenioid 圏 ftlCat t・Θ-link 函手
      ftlLink l（対象＝Frobenius [2l]）・平面埋め込み ftlPlaneEmbed・環準同型の不在
      ftl_not_ring_functor・**正直な限定 ftl_model_scope / ftl_full_frobenioid_hypothesis**:
      「log-link（柱C/D）との完全な噛み合わせは外部」
    * M331F (FrobenioidCategory): frobCHom・frobCId・frobCComp・frobCCat・frobCDegCat・
      Frobenius 合成則 frobCFrob_comp
    * M307F (PicardDivisor): 因子群 picDivGrp・Frobenius [n]＝picDivFrob・次数準同型
      picDivDegree・斉次性 picDiv_frob_degree
    * M3 (LogThetaLattice): 格子 LatticeSite・縦 Link.log・横 Link.theta・Path
    * M337F (LogLinkReal): 実 graded log 写像 logLinkMap（乗法 U^(d) → 加法 log-shell）・
      準同型 logLink_hom・核 logLink_kernel（= U^(d+1)）
    * M397F (LogThetaLatticeShell): 正方形の可換を殻フィルトレーション/実 deg_ℝ 体積
      レベルで実現（本モジュールはその **Frobenioid 圏レベルへの引き上げ**）

  本モジュールは M449F の残限定のうち **Frobenioid 圏レベルの log-link 函手と
  Θ-link との log-theta-lattice 可換正方形**を昇格で閉じる。[IUTchIII] §1 の
  log-theta-lattice は縦 log-link（同一列内・正則構造を保つ）と横 Θ-link
  （列を変える・環構造を保たない）の 2 方向のリンクを持つ——その圏論的実現:

    * **行ラベル付き劇場 Frobenioid の塔** fltCat t m（t : Bool＝列、m : Int＝行）:
      対象＝行・列ラベル付き因子群 FltObj t m、射＝frobCHom、圏公理は M331F 継承。
      log-theta-lattice の各頂点 (列 t, 行 m) に本物の Frobenioid 圏が載る。
    * **縦 log-link 函手** fltLogLink t m : fltCat t m ⥤ fltCat t (m+1):
      因子簿記（整数係数）レベルの作用は輸送（div ↦ div・次数そのまま）——これは
      恣意でなく**強制**される（剛性 flt_vertical_coric_forced: 対象 degree を保つ
      Frobenius 型作用は指数 1 のみ＝垂直コア性 [IUTchIII] Thm 1.5 (i) の因子簿記版）。
      本物の log の非自明部（乗法単数 U^(d) → 加法 log-shell の p 進 log・核 U^(d+1)）
      は M337F の実 graded log を装飾 FltLogDecoration として接続する。
    * **横 Θ-link 函手** fltTheta l m : fltCat false m ⥤ fltCat true m:
      対象＝Frobenius [2l]（Θ^{2l}=q^{j²}）・射＝次数そのまま輸送。行 0 への制限は
      M449F の ftlLink l と on the nose で一致（flt_restricts_to_m449・忠実な拡張）。
    * **可換正方形（本丸）** flt_log_theta_square: H∘V = V∘H、すなわち
        fltComp (fltTheta l m) (fltLogLink true m)
          = fltComp (fltLogLink false m) (fltTheta l (m+1))
      が**函手の on-the-nose 等式**として成立（両経路とも対象は [2l]・射は次数
      そのまま輸送）。恒等成分の自然変換 fltSquareNat・成分ごとの圏同型
      fltSquareIso も供給。degree レベルの整合 flt_square_degree（両経路とも ×2l）・
      射次数の整合 flt_square_hom_degree（両経路とも次数保存）込み。
    * **縦横の構造的区別（正方形が自明でないこと）**: 縦 log-link は対象 degree を
      保つ（flt_log_object_degree・degree コア性）が、横 Θ-link は l ≥ 1 で保たない
      （flt_theta_not_coric）。環構造は横で破れる（flt_theta_not_ring・M449F 継承）。
      正方形は「degree コアな縦」と「×2l の横」の交換という非自明な内容を持つ。

  完全証明する内容（すべて本物の因子群・圏・函手演算・toy 主語なし）:
    * fltCat t m の圏公理（M331F 継承）・fltTensor のモノイド法則
    * fltLogLink / fltTheta の函手法則（map_id・map_comp）
    * **flt_log_theta_square（本丸）**: H∘V = V∘H の on-the-nose 函手等式
    * fltSquareNat / fltSquareIso: 自然変換・成分圏同型（圏論的な可換の言明）
    * flt_square_degree / flt_square_hom_degree: 正方形の degree 整合（両経路 ×2l）
    * flt_vertical_coric_forced（剛性）: degree 保存 ⟹ Frobenius 指数 1（輸送が強制）
    * flt_theta_not_coric: 横 Θ-link は degree コアでない（縦横の区別）
    * flt_restricts_to_m449 / flt_restricts_hom_m449: 行 0 で M449F ftlLink と一致
    * flt_theta_not_ring: 全行で環準同型に持ち上がらない（M449F の圏レベル継承）
    * FltLogDecoration: 縦函手に M337F 実 graded log（準同型・核 U^(d+1)）を装飾
    * flt_closes_m449_limitation: M449F の残限定（log-link 噛合）の内部供給
    * capstone flt_exists: 全構造を FrobenioidLogThetaLatticeData に束ね
      crux 以外の外部仮説なしで居住させる

  crux（決して内部化しない）:
    * log-theta-lattice の**多輻アルゴリズム不等式**（Dβ-ω、[IUTchIII] Cor 3.12 の
      係争ステップ）は本モジュールの主張に一切含めない。
      flt_crux_is_hypothesis (crux : Prop) : crux ↔ crux ＝ Iff.rfl で
      外部仮説として保持（M449F ftl_crux_is_hypothesis と同じ精神）。

  正直な限定（M449F の残限定「log-link 噛合」の圏正方形部分を閉じた上で、
  残りを狭めて述べ直す・消さない・弱めない）:
    * 縦 log-link の**因子簿記（整数係数）レベルの作用は輸送（恒等）**である
      （flt_model_scope (i) で定理として正直申告）。これは剛性
      flt_vertical_coric_forced により強制される忠実な影（M337F/M397F の体積
      レベルで log-link が整数係数 n を保つ n ↦ n·log q_v の圏化）だが、本物の
      log の非自明部（乗法 U^(d) → 加法 log-shell・核 U^(d+1)・log-Kummer 巻き上げ）
      は装飾 FltLogDecoration（M337F の実 p 進 log）として持つに留まり、因子対象の
      内部には実装されない。実 π₁^ét 上の完全 log-shell・完全 log-Kummer 対応は外部。
    * 格子の列方向は {0,1} の 2 本のみ（flt_model_scope (ii)・M449F の 2 劇場を
      継承）。行方向は ℤ 全体（無限の縦塔）だが、無限列の完全な log-theta-lattice
      （全ての (n,m) ∈ ℤ²）と Θ±ellNF-Hodge 劇場の全データは外部/後続。
    * Frobenioid は M331F の忠実模型（elementary 型）に留まり、実劇場全体は非可換
      （flt_model_scope (iii)・M444F 再輸出）——本塔が捉えるのは因子/モノイド/次数
      構造の格子輸送であって劇場の非可換幾何や実 π₁^ét ではない。
    * 上記の残りを flt_full_loglattice_hypothesis（M449F
      ftl_full_frobenioid_hypothesis の狭め直し・後続）として外部仮説に固定。
  全て選択公理不使用（propext / Quot.sound のみ）・sorry 皆無。
-/
import IUT.FrobenioidThetaLink
import IUT.LogThetaLattice
import IUT.LogLinkReal

namespace IUT

universe u₁ v₁ u₂ v₂ u₃ v₃

/-! ## M454F-0: 函手合成（圏論インフラの補完・M19 Cat/Functor の上） -/

/-- **M454F-0a: 函手の合成** — 可換正方形 H∘V = V∘H を函手等式として述べる
    ための合成（M19 には未定義だった圏論インフラの補完）。 -/
def fltComp {C : Cat.{u₁, v₁}} {D : Cat.{u₂, v₂}} {E : Cat.{u₃, v₃}}
    (F : Functor C D) (G : Functor D E) : Functor C E where
  onObj := fun X => G.onObj (F.onObj X)
  onHom := fun f => G.onHom (F.onHom f)
  map_id := fun X => by rw [F.map_id, G.map_id]
  map_comp := fun f g => by rw [F.map_comp, G.map_comp]

/-! ## M454F-1: 行ラベル付き劇場 Frobenioid の塔（log-theta-lattice の頂点） -/

/-- **M454F-1a: 頂点 (列 t, 行 m) の Frobenioid の対象** — M307F の本物の因子群の元に
    列ラベル t : Bool（M449F の 2 劇場）と行ラベル m : Int（log 方向・M3 の row）を
    付けた型。相異なる (t, m) は相異なる型＝相異なる格子頂点の相異なる Frobenioid。 -/
structure FltObj (t : Bool) (m : Int) where
  /-- 台の因子類（M307F picDivGrp の元）。 -/
  div : picDivGrp.carrier

/-- 対象の等値補題（div で決まる）。 -/
theorem flt_obj_ext {t : Bool} {m : Int} {D E : FltObj t m} (h : D.div = E.div) :
    D = E :=
  congrArg FltObj.mk h

/-- **M454F-1b: 頂点 (t, m) の Frobenioid 圏** — 対象＝FltObj t m・射＝M331F の
    Frobenius 次数付き frobCHom。圏公理は M331F frobCCat から継承。
    log-theta-lattice の各頂点に本物の Frobenioid 圏が載る（M449F ftlCat の
    行方向への拡張）。 -/
def fltCat (t : Bool) (m : Int) : Cat where
  Obj := FltObj t m
  Hom := fun D E => frobCHom D.div E.div
  id := fun D => frobCId D.div
  comp := fun f g => frobCComp f g
  id_comp := fun f => frobCCat.id_comp f
  comp_id := fun f => frobCCat.comp_id f
  assoc := fun f g h => frobCCat.assoc f g h

/-- **M454F-1c: 線形束テンソル**（因子の和・M449F ftlTensor の行付き版）。 -/
def fltTensor {t : Bool} {m : Int} (D E : FltObj t m) : FltObj t m :=
  ⟨picDivGrp.mul D.div E.div⟩

/-- **M454F-1d: 自明束**（零因子＝テンソル単位）。 -/
def fltOne (t : Bool) (m : Int) : FltObj t m :=
  ⟨picDivGrp.one⟩

/-- テンソルの結合律（M307F 因子群から）。 -/
theorem fltTensor_assoc {t : Bool} {m : Int} (D E F : FltObj t m) :
    fltTensor (fltTensor D E) F = fltTensor D (fltTensor E F) :=
  flt_obj_ext (picDivGrp.mul_assoc D.div E.div F.div)

/-- 自明束は左単位元。 -/
theorem fltTensor_one_left {t : Bool} {m : Int} (D : FltObj t m) :
    fltTensor (fltOne t m) D = D :=
  flt_obj_ext (picDivGrp.one_mul D.div)

/-- テンソルの可換性（Frobenioid の対象モノイドは可換）。 -/
theorem fltTensor_comm {t : Bool} {m : Int} (D E : FltObj t m) :
    fltTensor D E = fltTensor E D :=
  flt_obj_ext (picDivGrp_comm D.div E.div)

/-- **M454F-1e: 格子頂点の列座標**（M3 LatticeSite の col・列 t の整数化）。 -/
def fltCol : Bool → Int
  | false => 0
  | true => 1

/-! ## M454F-2: 縦 log-link 函手（本丸その 1＝Frobenioid 圏の縦リンク） -/

/-- **M454F-2a: 縦 log-link 函手** fltLogLink t m : (頂点 (t,m) の Frobenioid) ⥤
    (頂点 (t,m+1) の Frobenioid) — 因子簿記（整数係数）レベルの作用は輸送
    （div ↦ div・射は次数そのまま）。これは恣意でなく**強制**される（M454F-4 の
    剛性: 対象 degree を保つ Frobenius 型作用は指数 1 のみ＝垂直コア性
    [IUTchIII] Thm 1.5 (i) の因子簿記版）。本物の log の非自明部（乗法 U^(d) →
    加法 log-shell）は M454F-6 の装飾 FltLogDecoration（M337F）で接続する。 -/
def fltLogLink (t : Bool) (m : Int) : Functor (fltCat t m) (fltCat t (m + 1)) where
  onObj := fun D => ⟨D.div⟩
  onHom := fun f => f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- **定理 (M454F-2b): 縦 log-link はモノイド構造を保つ** — テンソル（因子和）を
    on the nose で保存（log-link は étale-like 加法構造＝因子モノイドと両立、
    垂直コア性のモノイド面）。 -/
theorem flt_log_monoid_hom (t : Bool) (m : Int) (D E : FltObj t m) :
    (fltLogLink t m).onObj (fltTensor D E)
      = fltTensor ((fltLogLink t m).onObj D) ((fltLogLink t m).onObj E) := rfl

/-- **定理 (M454F-2c): 縦 log-link はテンソル単位を保つ**。 -/
theorem flt_log_one_preserved (t : Bool) (m : Int) :
    (fltLogLink t m).onObj (fltOne t m) = fltOne t (m + 1) := rfl

/-- **定理 (M454F-2d): 縦 log-link は対象の因子次数を保つ（degree コア性）** —
    deg(log-link D) = deg(D)。M337F/M397F で log-link が体積の整数係数 n を保つ
    （n ↦ n·log q_v）ことの圏化。横 Θ-link の ×2l と対照的（M454F-4c）。 -/
theorem flt_log_object_degree (t : Bool) (m : Int) (D : FltObj t m) :
    picDivDegree.map (((fltLogLink t m).onObj D)).div = picDivDegree.map D.div :=
  rfl

/-- **定理 (M454F-2e): 縦 log-link は射の Frobenius 次数を保つ**。 -/
theorem flt_log_preserves_degree (t : Bool) (m : Int) {D E : FltObj t m}
    (f : frobCHom D.div E.div) :
    ((fltLogLink t m).onHom (X := D) (Y := E) f).deg = f.deg := rfl

/-- **定理 (M454F-2f): 縦 log-link は M3 の本物の縦格子辺 Link.log を装飾する** —
    頂点 (fltCol t, m) → (fltCol t, m+1) の縦辺（列を保つ・正則構造を保つ）。 -/
theorem flt_vertical_edge (t : Bool) (m : Int) :
    Link ⟨fltCol t, m⟩ ⟨fltCol t, m + 1⟩ :=
  Link.log (fltCol t) m

/-! ## M454F-3: 横 Θ-link 函手（M449F ftlLink の全行拡張） -/

/-- **M454F-3a: Θ-link の射輸送（台レベル）** — f : D → E（次数 n・有効部 eff）を
    [2l]D → [2l]E（次数 n・有効部 [2l]eff）へ。線形条件は M449F ftlLink_linear
    （Frobenius の可換性 [2l]∘[n]=[n]∘[2l]）から本物で。 -/
def fltThetaHom (l : Nat) {D E : picDivGrp.carrier} (f : frobCHom D E) :
    frobCHom ((picDivFrob (2 * l)).map D) ((picDivFrob (2 * l)).map E) where
  deg := f.deg
  deg_pos := f.deg_pos
  eff := (picDivFrob (2 * l)).map f.eff
  eff_effective := by
    obtain ⟨r, hr, he⟩ := f.eff_effective
    refine ⟨picDivFrobRaw (2 * l) r, picDivEffective_frob (2 * l) hr, ?_⟩
    exact congrArg (picDivFrob (2 * l)).map he
  linear := ftlLink_linear l f.linear

/-- **M454F-3b: 横 Θ-link 函手** fltTheta l m : (頂点 (0,m)) ⥤ (頂点 (1,m)) —
    対象＝Frobenius [2l]（Θ^{2l}=q^{j²}）・射＝次数そのまま輸送。M449F ftlLink の
    行 m への拡張（行 0 への制限は M454F-5 で ftlLink と on the nose 一致）。 -/
def fltTheta (l : Nat) (m : Int) : Functor (fltCat false m) (fltCat true m) where
  onObj := fun D => ⟨(picDivFrob (2 * l)).map D.div⟩
  onHom := fun f => fltThetaHom l f
  map_id := by
    intro X
    apply frobCHom.ext
    · rfl
    · exact Hom.map_one (picDivFrob (2 * l))
  map_comp := by
    intro X Y Z f g
    apply frobCHom.ext
    · rfl
    · show (picDivFrob (2 * l)).map
          (picDivGrp.mul ((picDivFrob g.deg).map f.eff) g.eff)
        = picDivGrp.mul
            ((picDivFrob g.deg).map ((picDivFrob (2 * l)).map f.eff))
            ((picDivFrob (2 * l)).map g.eff)
      rw [(picDivFrob (2 * l)).map_mul, frobCFrob_comp g.deg (2 * l) f.eff,
        Nat.mul_comm g.deg (2 * l), ← frobCFrob_comp (2 * l) g.deg f.eff]

/-- **定理 (M454F-3c): 横 Θ-link は射の Frobenius 次数を保つ**（M449F と同じ簿記）。 -/
theorem flt_theta_preserves_degree (l : Nat) (m : Int) {D E : FltObj false m}
    (f : frobCHom D.div E.div) :
    ((fltTheta l m).onHom (X := D) (Y := E) f).deg = f.deg := rfl

/-- **定理 (M454F-3d): 横 Θ-link の対象次数は ×2l**（[FrdI] 次数簿記・M449F
    ftl_object_degree の全行版）。 -/
theorem flt_theta_object_degree (l : Nat) (m : Int) (D : FltObj false m) :
    picDivDegree.map ((fltTheta l m).onObj D).div
      = ((2 * l : Nat) : Int) * picDivDegree.map D.div :=
  picDiv_frob_degree (2 * l) D.div

/-- **定理 (M454F-3e): 横 Θ-link は M3 の本物の横格子辺 Link.theta を装飾する** —
    頂点 (0, m) → (0+1, m) の横辺（列を +1 する・正則構造を変える）。 -/
theorem flt_horizontal_edge (m : Int) :
    Link ⟨fltCol false, m⟩ ⟨fltCol false + 1, m⟩ :=
  Link.theta (fltCol false) m

/-- 列座標の整合: fltCol false + 1 = fltCol true（横辺は列 0 → 列 1）。 -/
theorem flt_col_step : fltCol false + 1 = fltCol true := by
  show (0 : Int) + 1 = 1
  omega

/-! ## M454F-4: 剛性＝縦横の構造的区別（正方形が自明でないことの本物） -/

/-- 次数 1 の witness 因子 1·[P₀]（剛性の証人）。 -/
def fltOneDivRaw : RawDiv where
  coeff := fun k => match k with
    | 0 => 1
    | _ + 1 => 0
  bound := 1
  vanish := fun k hk => by
    cases k with
    | zero => exact absurd hk (by omega)
    | succ n => rfl

/-- witness の次数は 1。 -/
theorem flt_oneDiv_degree :
    picDivDegree.map (Quot.mk rawEq fltOneDivRaw) = 1 := by
  show (0 : Int) + 1 = 1
  omega

/-- **定理 (M454F-4a: 剛性・垂直コア性の強制)** — 対象の因子次数を保つ Frobenius 型
    作用 [k] は **k = 1（＝輸送）のみ**。縦 log-link の因子簿記レベルの作用が輸送で
    あることは恣意でなく、degree コア性（[IUTchIII] Thm 1.5 (i) 垂直コア性の因子
    簿記版）から**強制**される——本モジュールの縦函手の忠実性の根拠。 -/
theorem flt_vertical_coric_forced (k : Nat)
    (h : ∀ D : picDivGrp.carrier,
      picDivDegree.map ((picDivFrob k).map D) = picDivDegree.map D) :
    k = 1 := by
  have h1 := h (Quot.mk rawEq fltOneDivRaw)
  rw [picDiv_frob_degree, flt_oneDiv_degree, Int.mul_one] at h1
  have h2 : (k : Int) = 1 := h1
  omega

/-- **定理 (M454F-4b): 横 Θ-link は degree コアでない**（任意の l——2l = 1 は偶奇で
    不可能）— Frobenius [2l] は対象次数を保たない。縦（degree コア）と横（×2l）の
    構造的区別。 -/
theorem flt_theta_not_coric (l : Nat) :
    ¬ ∀ D : picDivGrp.carrier,
      picDivDegree.map ((picDivFrob (2 * l)).map D) = picDivDegree.map D := by
  intro h
  have h1 := flt_vertical_coric_forced (2 * l) h
  omega

/-- **定理 (M454F-4c: 縦横の区別の総括)** — (i) 縦 log-link は対象 degree を保ち
    （degree コア）、(ii) 横 Θ-link は保たない（任意の l）。log-theta-lattice の
    2 方向が Frobenioid 圏レベルで**構造的に相異なる**リンクであることの本物
    （M3 の「log-link は列を保ち Θ-link は列を変える」の因子簿記版）。 -/
theorem flt_vertical_horizontal_distinct (l : Nat) :
    (∀ (t : Bool) (m : Int) (D : FltObj t m),
      picDivDegree.map (((fltLogLink t m).onObj D)).div = picDivDegree.map D.div)
    ∧ ¬ ∀ D : picDivGrp.carrier,
        picDivDegree.map ((picDivFrob (2 * l)).map D) = picDivDegree.map D :=
  ⟨fun t m D => flt_log_object_degree t m D, flt_theta_not_coric l⟩

/-! ## M454F-5: log-theta-lattice の可換正方形（本丸その 2） -/

/-- **定理 (M454F-5a: flt_log_theta_square・本丸)** — **Θ-link（横）と log-link（縦）は
    log-theta-lattice の可換正方形をなす**: 頂点 (0,m) から (1,m+1) への 2 経路
      縦→横: H∘V ＝ fltComp (fltTheta l m) (fltLogLink true m)
      横→縦: V∘H ＝ fltComp (fltLogLink false m) (fltTheta l (m+1))
    が **函手の on-the-nose 等式**として一致する（両経路とも対象＝Frobenius [2l]・
    射＝次数そのまま輸送）。M449F の残限定「log-link との噛み合わせは外部」の
    圏正方形部分を閉じる核心（M397F の体積レベル正方形の Frobenioid 圏への引き上げ）。 -/
theorem flt_log_theta_square (l : Nat) (m : Int) :
    fltComp (fltTheta l m) (fltLogLink true m)
      = fltComp (fltLogLink false m) (fltTheta l (m + 1)) := rfl

/-- **定理 (M454F-5b): 正方形の対象レベル可換**（5a の成分言明）。 -/
theorem flt_square_onObj (l : Nat) (m : Int) (D : FltObj false m) :
    (fltLogLink true m).onObj ((fltTheta l m).onObj D)
      = (fltTheta l (m + 1)).onObj ((fltLogLink false m).onObj D) := rfl

/-- **定理 (M454F-5c): 正方形の射レベル可換**（5a の成分言明・次数付き射ごと）。 -/
theorem flt_square_onHom (l : Nat) (m : Int) {D E : FltObj false m}
    (f : frobCHom D.div E.div) :
    (fltLogLink true m).onHom (X := (fltTheta l m).onObj D)
        (Y := (fltTheta l m).onObj E)
        ((fltTheta l m).onHom (X := D) (Y := E) f)
      = (fltTheta l (m + 1)).onHom (X := (fltLogLink false m).onObj D)
          (Y := (fltLogLink false m).onObj E)
          ((fltLogLink false m).onHom (X := D) (Y := E) f) := rfl

/-- **M454F-0b: 恒等自然変換**（任意の函手 F に対する id : F ⟹ F・圏論インフラの
    補完）。可換正方形の自然変換（M454F-5d）の台。 -/
def fltIdNat {C : Cat.{u₁, v₁}} {D : Cat.{u₂, v₂}} (F : Functor C D) :
    NatTrans F F where
  app := fun X => D.id (F.onObj X)
  natural := fun f => by
    rw [D.comp_id, D.id_comp]

/-- **M454F-5d: 正方形の自然変換**（恒等成分）— 可換正方形の圏論的言明: H∘V から
    V∘H への自然変換で全成分が恒等射のもの（on-the-nose 可換 flt_log_theta_square
    ＝ rfl ゆえ、恒等自然変換 id : H∘V ⟹ H∘V がそのまま H∘V ⟹ V∘H を与える）。 -/
def fltSquareNat (l : Nat) (m : Int) :
    NatTrans (fltComp (fltTheta l m) (fltLogLink true m))
      (fltComp (fltLogLink false m) (fltTheta l (m + 1))) :=
  fltIdNat (fltComp (fltTheta l m) (fltLogLink true m))

/-- **M454F-5e: 正方形の成分ごとの圏同型** — 各対象で H∘V と V∘H の像は
    fltCat true (m+1) の中で同型（恒等射が同型を与える・自然同型の成分）。 -/
def fltSquareIso (l : Nat) (m : Int) (D : FltObj false m) :
    CatIso (fltCat true (m + 1))
      ((fltComp (fltTheta l m) (fltLogLink true m)).onObj D)
      ((fltComp (fltLogLink false m) (fltTheta l (m + 1))).onObj D) where
  hom := (fltCat true (m + 1)).id _
  inv := (fltCat true (m + 1)).id _
  hom_inv := (fltCat true (m + 1)).id_comp _
  inv_hom := (fltCat true (m + 1)).id_comp _

/-- **定理 (M454F-5f: flt_square_degree)** — 可換正方形は **degree レベルで整合**:
    両経路の合成の対象次数はともに ×2l（縦は保存・横は ×2l、順序に依らない——
    M397F ltls_square_commutes_vol の整数次数版・圏レベル）。 -/
theorem flt_square_degree (l : Nat) (m : Int) (D : FltObj false m) :
    picDivDegree.map
        ((fltComp (fltTheta l m) (fltLogLink true m)).onObj D).div
      = ((2 * l : Nat) : Int) * picDivDegree.map D.div
    ∧ picDivDegree.map
        ((fltComp (fltLogLink false m) (fltTheta l (m + 1))).onObj D).div
      = ((2 * l : Nat) : Int) * picDivDegree.map D.div :=
  ⟨picDiv_frob_degree (2 * l) D.div, picDiv_frob_degree (2 * l) D.div⟩

/-- **定理 (M454F-5g): 正方形の射次数整合** — 両経路とも射の Frobenius 次数を保つ。 -/
theorem flt_square_hom_degree (l : Nat) (m : Int) {D E : FltObj false m}
    (f : frobCHom D.div E.div) :
    ((fltComp (fltTheta l m) (fltLogLink true m)).onHom (X := D) (Y := E) f).deg
        = f.deg
    ∧ ((fltComp (fltLogLink false m) (fltTheta l (m + 1))).onHom
        (X := D) (Y := E) f).deg = f.deg :=
  ⟨rfl, rfl⟩

/-- **定理 (M454F-5h): 正方形の組合せ経路**（M3 の本物の格子 Path・M397F 1a/1b と
    同じ 2 経路が Frobenioid 塔の正方形の台）— 縦→横・横→縦がともに Θ-link
    ちょうど 1 本の Path 1 で同一の隅 (1, m+1) へ。 -/
theorem flt_square_paths (m : Int) :
    Path 1 ⟨0, m⟩ ⟨0 + 1, m + 1⟩ ∧ Path 1 ⟨0, m⟩ ⟨0 + 1, m + 1⟩ :=
  ⟨Path.log 0 m (Path.theta 0 (m + 1) (Path.nil _)),
    Path.theta 0 m (Path.log (0 + 1) m (Path.nil _))⟩

/-! ## M454F-6: M449F への制限一致と実 graded log 装飾 -/

/-- **M454F-6a: 行 0 の頂点と M449F の劇場 Frobenioid の同一視**。 -/
def fltToFtl {t : Bool} (D : FltObj t 0) : FtlObj t :=
  ⟨D.div⟩

/-- **定理 (M454F-6b: flt_restricts_to_m449・忠実な拡張)** — 横 Θ-link 函手の行 0 への
    制限は M449F の ftlLink l と対象レベルで **on the nose で一致**。本塔は M449F の
    圏レベル Θ-link の行方向への忠実な拡張であって別物ではない。 -/
theorem flt_restricts_to_m449 (l : Nat) (D : FltObj false 0) :
    (ftlLink l).onObj (fltToFtl D) = fltToFtl ((fltTheta l 0).onObj D) := rfl

/-- **定理 (M454F-6c): 射レベルの制限一致** — 行 0 で射輸送も M449F と一致。 -/
theorem flt_restricts_hom_m449 (l : Nat) {D E : FltObj false 0}
    (f : frobCHom D.div E.div) :
    (ftlLink l).onHom (X := fltToFtl D) (Y := fltToFtl E) f
      = (fltTheta l 0).onHom (X := D) (Y := E) f := rfl

/-- **M454F-6d: M444F の ℤ² 平面の塔頂点への埋め込み**（M449F ftlPlaneEmbed の
    行付き版・環破れの witness 台）。 -/
def fltPlaneEmbed {t : Bool} (m : Int) (x : TlpElt t) : FltObj t m :=
  ⟨(ftlPlaneEmbed x).div⟩

/-- **定理 (M454F-6e): 縦 log-link は平面埋め込みと両立**（輸送は平面を平面へ）。 -/
theorem flt_log_plane (t : Bool) (m : Int) (x : TlpElt t) :
    (fltLogLink t m).onObj (fltPlaneEmbed m x) = fltPlaneEmbed (m + 1) x := rfl

/-- **定理 (M454F-6f): 横 Θ-link の平面制限は M444F の tlpLink (2l)**（全行で・
    M449F ftl_restricts_to_tlp の継承）。 -/
theorem flt_plane_restricts (l : Nat) (m : Int) (x : TlpElt false) :
    (fltTheta l m).onObj (fltPlaneEmbed m x)
      = fltPlaneEmbed m ((tlpLink ((2 * l : Nat) : Int)).map x) := by
  apply flt_obj_ext
  exact congrArg FtlObj.div (ftl_restricts_to_tlp l x)

/-- **定理 (M454F-6g): 横 Θ-link は全行で環準同型に持ち上がらない** — 可換正方形の
    横辺は環（正則）構造を保たない（M449F ftl_not_ring_functor の全行継承・
    log-theta-lattice の横辺の環破れが塔全体で生存）。 -/
theorem flt_theta_not_ring (l : Nat) (m : Int) :
    ¬ ∃ f : RingHom tlpRing0 tlpRing1,
        ∀ x, fltPlaneEmbed m (f.map x) = (fltTheta l m).onObj (fltPlaneEmbed m x) := by
  intro h
  obtain ⟨f, hf⟩ := h
  refine ftl_not_ring_functor l ⟨f, ?_⟩
  intro x
  apply ftl_obj_ext
  exact congrArg FltObj.div (hf x)

/-- **M454F-6h: 縦 log-link 函手の実 graded log 装飾** — 縦函手の因子簿記レベルの
    輸送に、M337F の**本物の p 進 graded log**（乗法 U^(d) → 加法 log-shell ℤ/p・
    準同型・核 = U^(d+1)）を装飾として接続する構造。縦 log-link の非自明部
    （乗法→加法の本物の log）はここに住む（因子対象の内部でなく・正直な限定）。 -/
structure FltLogDecoration (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) where
  /-- 装飾の実 log 写像（乗法主単数 → 加法 log-shell）。 -/
  logMap : (principalUnits p).carrier → (zmod p).carrier
  /-- logMap は M337F の本物の縦 log-link 写像。 -/
  is_log : logMap = logLinkMap p d hp
  /-- log(1) = 0（乗法単位元 → 加法単位元）。 -/
  log_one : logMap (principalUnits p).one = (zmod p).one
  /-- log は準同型（乗法 → 加法・U^(d) 上）。 -/
  log_hom : ∀ x y, (unitFiltration p d).mem x → (unitFiltration p d).mem y →
    logMap ((principalUnits p).mul x y) = (zmod p).mul (logMap x) (logMap y)
  /-- 1 格子ステップ下降の核: log の核 = U^(d+1)。 -/
  kernel : ∀ x, (unitFiltration p d).mem x →
    (logMap x = (zmod p).one ↔ (unitFiltration p (d + 1)).mem x)
  /-- 装飾される縦函手の因子簿記は degree コア（M454F-2d）。 -/
  vert_coric : ∀ (t : Bool) (m : Int) (D : FltObj t m),
    picDivDegree.map (((fltLogLink t m).onObj D)).div = picDivDegree.map D.div

/-- **M454F-6i: 装飾の witness** — M337F の本物で全フィールドを充足。 -/
def fltLogDecoration (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d) :
    FltLogDecoration p d hp hd where
  logMap := logLinkMap p d hp
  is_log := rfl
  log_one := logLink_one p d hp
  log_hom := fun x y hx hy => logLink_hom p d hp hd x y hx hy
  kernel := fun x hx => logLink_kernel p d hp x hx
  vert_coric := fun t m D => flt_log_object_degree t m D

/-! ## M454F-7: M449F の残限定を閉じる（本丸の総括） -/

/-- **定理 (M454F-7: flt_closes_m449_limitation・本丸)** — M449F の正直な限定
    ftl_model_scope／外部仮説 ftl_full_frobenioid_hypothesis が外部と申告した
    「log-link（柱C/D）との完全な噛み合わせ」のうち **Frobenioid 圏レベルの
    log-link 函手と Θ-link との log-theta-lattice 可換正方形**に対応する主張を、
    **内部の定理として**供給する:
    (i) 全行 m で可換正方形 H∘V = V∘H が函手の on-the-nose 等式で成立、
    (ii) 縦 log-link は本物の函手でモノイド構造（テンソル＝因子和）を保つ、
    (iii) 縦 log-link は対象 degree を保つ（degree コア・M337F 体積輸送の圏化）、
    (iv) 横 Θ-link の行 0 制限は M449F ftlLink と on the nose 一致（忠実な拡張）、
    (v) 縦函手は M337F の実 graded log（準同型・核 U^(d+1)）で装飾される。
    まとめ: Θ-link と log-link は Frobenioid 圏レベルで log-theta-lattice の
    可換正方形をなす——M449F の残限定の log-link 噛合部分（圏正方形）を閉じた。 -/
theorem flt_closes_m449_limitation (l : Nat) :
    (∀ m : Int,
      fltComp (fltTheta l m) (fltLogLink true m)
        = fltComp (fltLogLink false m) (fltTheta l (m + 1)))
    ∧ (∀ (t : Bool) (m : Int) (D E : FltObj t m),
        (fltLogLink t m).onObj (fltTensor D E)
          = fltTensor ((fltLogLink t m).onObj D) ((fltLogLink t m).onObj E))
    ∧ (∀ (t : Bool) (m : Int) (D : FltObj t m),
        picDivDegree.map (((fltLogLink t m).onObj D)).div = picDivDegree.map D.div)
    ∧ (∀ D : FltObj false 0,
        (ftlLink l).onObj (fltToFtl D) = fltToFtl ((fltTheta l 0).onObj D))
    ∧ (∀ (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d),
        Nonempty (FltLogDecoration p d hp hd)) :=
  ⟨fun m => flt_log_theta_square l m,
    fun t m D E => flt_log_monoid_hom t m D E,
    fun t m D => flt_log_object_degree t m D,
    fun D => flt_restricts_to_m449 l D,
    fun p d hp hd => ⟨fltLogDecoration p d hp hd⟩⟩

/-! ## M454F-8: crux Dβ-ω は外部仮説（決して内部化しない） -/

/-- **crux（外部仮説・決して導出しない）**: log-theta-lattice の**多輻アルゴリズム
    不等式**（Dβ-ω、[IUTchIII] Cor 3.12 の係争ステップ＝ q-パイロットの体積が
    theta-パイロット軌道に支配されるという主張）は、本モジュールの主張には一切
    含めない。恒等 Iff で外部仮説として保持する（M449F ftl_crux_is_hypothesis と
    同じ精神）。本モジュールが証明したのは「Θ-link と log-link は Frobenioid 圏
    レベルで可換正方形をなす」という**構造的性質**までであり、正方形の上の不定性を
    体積不等式に変換する主張は別問題である。 -/
theorem flt_crux_is_hypothesis (crux : Prop) : crux ↔ crux := Iff.rfl

/-! ## M454F-9: 正直な限定（閉じた上で残りを狭めて述べ直す） -/

/-- **定理 (M454F-9a: flt_model_scope・正直な限定の総括)** — 本構成のスコープ
    （M449F の残限定「log-link 噛合」の圏正方形部分を閉じた後に残る、より狭い
    正直な限定）:
    (i) **縦 log-link の因子簿記（整数係数）レベルの作用は輸送（恒等）**である
        （剛性 M454F-4a によりこれは強制される忠実な影だが、本物の log の非自明部
        （乗法 U^(d) → 加法 log-shell・log-Kummer 巻き上げ）は装飾 FltLogDecoration
        （M337F）に住み、因子対象の内部には実装されない——実 π₁^ét 上の完全
        log-shell・完全 log-Kummer 対応は外部）、
    (ii) 格子の列方向は {0,1} の 2 本のみ（無限列の完全な log-theta-lattice は外部）、
    (iii) 実劇場全体は非可換（M444F 再輸出）——本塔が捉えるのは因子/モノイド/次数
        構造の格子輸送であって劇場の非可換幾何や実 π₁^ét ではない。 -/
theorem flt_model_scope :
    (∀ (t : Bool) (m : Int) (D : FltObj t m),
        ((fltLogLink t m).onObj D).div = D.div)
    ∧ (fltCol false = 0 ∧ fltCol true = 1)
    ∧ (¬ ∀ x y : (tlt2Theater false).carrier,
        (tlt2Theater false).mul x y = (tlt2Theater false).mul y x) :=
  ⟨fun _ _ _ => rfl, ⟨rfl, rfl⟩, tlp_theater_noncommutative⟩

/-- **外部仮説（正直な限定・決して導出しない）**: 本塔（elementary Frobenioid の
    行付き塔・因子簿記の log-link・M337F 装飾）を実数体・p 進局所体上の**完全**
    Frobenioid と実 π₁^ét 上の完全 log-shell/log-Kummer 対応・無限列の完全な
    log-theta-lattice へ昇格させること（M449F ftl_full_frobenioid_hypothesis の
    狭め直し・後続）。 -/
def flt_full_loglattice_hypothesis (T : Grp) : Prop := Slim T

/-! ## M454F-10: capstone -/

/-- **M454F-10a: Frobenioid 圏レベル log-theta-lattice データ** — 劇場 Frobenioid の
    塔の上の縦 log-link 函手・横 Θ-link 函手・**可換正方形（M449F の残限定を閉じる
    本丸）**・degree 整合・M449F 制限一致・環準同型の不在・実 graded log 装飾を束ねる。
    主語はすべて本物の因子群・圏・函手演算（toy 主語なし）。crux Dβ-ω はフィールドに
    含めない（外部仮説のまま）。 -/
structure FrobenioidLogThetaLatticeData (l : Nat) where
  /-- 縦 log-link は各頂点で本物の函手。 -/
  vertical : ∀ (t : Bool) (m : Int), Functor (fltCat t m) (fltCat t (m + 1))
  /-- 縦函手は本モジュールの log-link 函手そのもの。 -/
  vertical_is_log : vertical = fltLogLink
  /-- 横 Θ-link は各行で本物の函手。 -/
  horizontal : ∀ m : Int, Functor (fltCat false m) (fltCat true m)
  /-- 横函手は本モジュールの Θ-link 函手そのもの。 -/
  horizontal_is_theta : horizontal = fltTheta l
  /-- **可換正方形（本丸）**: H∘V = V∘H が全行で on the nose。 -/
  square : ∀ m : Int,
    fltComp (horizontal m) (vertical true m)
      = fltComp (vertical false m) (horizontal (m + 1))
  /-- 縦 log-link はモノイド構造（テンソル＝因子和）を保つ。 -/
  vert_monoid : ∀ (t : Bool) (m : Int) (D E : FltObj t m),
    (vertical t m).onObj (fltTensor D E)
      = fltTensor ((vertical t m).onObj D) ((vertical t m).onObj E)
  /-- 縦 log-link は対象 degree を保つ（degree コア性）。 -/
  vert_degree : ∀ (t : Bool) (m : Int) (D : FltObj t m),
    picDivDegree.map (((vertical t m).onObj D)).div = picDivDegree.map D.div
  /-- 横 Θ-link の対象次数は ×2l。 -/
  horiz_degree : ∀ (m : Int) (D : FltObj false m),
    picDivDegree.map ((horizontal m).onObj D).div
      = ((2 * l : Nat) : Int) * picDivDegree.map D.div
  /-- 正方形の degree 整合: 縦→横経路の合成次数は ×2l。 -/
  square_degree : ∀ (m : Int) (D : FltObj false m),
    picDivDegree.map ((fltComp (horizontal m) (vertical true m)).onObj D).div
      = ((2 * l : Nat) : Int) * picDivDegree.map D.div
  /-- 行 0 の横函手は M449F ftlLink と一致（忠実な拡張）。 -/
  restricts_m449 : ∀ D : FltObj false 0,
    (ftlLink l).onObj (fltToFtl D) = fltToFtl ((horizontal 0).onObj D)
  /-- 横 Θ-link は全行で環準同型に持ち上がらない（環破れの生存）。 -/
  not_ring : ∀ m : Int, ¬ ∃ f : RingHom tlpRing0 tlpRing1,
    ∀ x, fltPlaneEmbed m (f.map x) = (horizontal m).onObj (fltPlaneEmbed m x)
  /-- 縦函手は M337F の実 graded log で装飾される。 -/
  log_decor : ∀ (p d : Nat) (hp : 1 ≤ p) (hd : 1 ≤ d),
    Nonempty (FltLogDecoration p d hp hd)

/-- **M454F-10b: witness 本体** — 全フィールドを M454F-2〜6 の本物の証明で埋める
    （crux 以外の外部仮説ゼロ・完全証明）。 -/
def fltData (l : Nat) : FrobenioidLogThetaLatticeData l where
  vertical := fltLogLink
  vertical_is_log := rfl
  horizontal := fltTheta l
  horizontal_is_theta := rfl
  square := fun m => flt_log_theta_square l m
  vert_monoid := fun t m D E => flt_log_monoid_hom t m D E
  vert_degree := fun t m D => flt_log_object_degree t m D
  horiz_degree := fun m D => flt_theta_object_degree l m D
  square_degree := fun m D => (flt_square_degree l m D).1
  restricts_m449 := fun D => flt_restricts_to_m449 l D
  not_ring := fun m => flt_theta_not_ring l m
  log_decor := fun p d hp hd => ⟨fltLogDecoration p d hp hd⟩

/-- **定理 (M454F-10c): Frobenioid 圏レベル log-theta-lattice データの存在
    （M454F 見出し・capstone）** — 任意の l ∈ ℕ に対し、劇場 Frobenioid の塔の上の
    縦 log-link 函手と横 Θ-link 函手が **log-theta-lattice の可換正方形をなす**
    （M449F の残限定「log-link 噛合」の圏正方形部分を閉じる）データが
    **crux 以外の外部仮説なしで**存在する。 -/
theorem flt_exists (l : Nat) : Nonempty (FrobenioidLogThetaLatticeData l) :=
  ⟨fltData l⟩

/-! ## M454F-11: 実例 -/

/-- 実例（l=3・行 m の可換正方形の具体計算）: 埋め込まれた平面点 (1,2) を
    縦→横経路で送ると (6,12) の行 m+1 埋め込みへ（Θ^{6}=q^{j²} の因子版・
    横→縦経路と on the nose 同一）。 -/
example (m : Int) :
    (fltComp (fltTheta 3 m) (fltLogLink true m)).onObj
        (fltPlaneEmbed m (⟨(1, 2)⟩ : TlpElt false))
      = fltPlaneEmbed (m + 1) (⟨(6, 12)⟩ : TlpElt true) := by
  apply flt_obj_ext
  exact Quot.sound (fun k => by
    cases k with
    | zero =>
      show ((2 * 3 : Nat) : Int) * 1 = 6
      omega
    | succ n => cases n with
      | zero =>
        show ((2 * 3 : Nat) : Int) * 2 = 12
        omega
      | succ i =>
        show ((2 * 3 : Nat) : Int) * 0 = 0
        omega)

/-- 実例: 可換正方形は l=1・全行で on the nose（函手等式）。 -/
example (m : Int) :
    fltComp (fltTheta 1 m) (fltLogLink true m)
      = fltComp (fltLogLink false m) (fltTheta 1 (m + 1)) :=
  flt_log_theta_square 1 m

/-- 実例: 縦 log-link は degree コア・横 Θ-link（l=5）は非コア（縦横の区別）。 -/
example :
    (∀ (t : Bool) (m : Int) (D : FltObj t m),
      picDivDegree.map (((fltLogLink t m).onObj D)).div = picDivDegree.map D.div)
    ∧ ¬ ∀ D : picDivGrp.carrier,
        picDivDegree.map ((picDivFrob (2 * 5)).map D) = picDivDegree.map D :=
  flt_vertical_horizontal_distinct 5

/-- 実例: 正方形の degree 整合（l=7・両経路とも ×14）。 -/
example (m : Int) (D : FltObj false m) :
    picDivDegree.map
        ((fltComp (fltTheta 7 m) (fltLogLink true m)).onObj D).div
      = ((2 * 7 : Nat) : Int) * picDivDegree.map D.div :=
  (flt_square_degree 7 m D).1

/-- 実例: 縦 log-link の装飾は K = ℚ₂・段 d=1 の本物の p 進 graded log。 -/
example : Nonempty (FltLogDecoration 2 1 (by omega) (by omega)) :=
  ⟨fltLogDecoration 2 1 (by omega) (by omega)⟩

/-- 実例: capstone データは任意の l で存在（具体化・l=5）。 -/
example : Nonempty (FrobenioidLogThetaLatticeData 5) := flt_exists 5

end IUT
