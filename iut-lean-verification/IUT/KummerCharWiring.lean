-- M448F KummerCharWiring [実・昇格（(a)）・柱E×柱A]
-- complete_pct 影響: 柱E/柱A で、M443F(cid)が残した 2 つの正直な限定
--   (1)「E.n = l（E 側 CycMuGroup の位数が A 側 l と一致すること）を外部仮定とする」
--   (4)「Galois 同変性 cid_galois_equivariant は両側に独立に与えられた CycGKAction が
--       同じ mod-n 指数を持つという一般論であり、M353F の具体的 Kummer 指標
--       κ:GK→M.μ を用いた実接続は後続」
--   を、標準模型 cycMuStd l とトリビアル Galois 作用（M353F-3b が明示する
--   「μ_{2l}⊂K の本物のケース」＝ G_K が μ_{2l} に自明作用する場合）で実際に
--   昇格・接続する。(1) は標準模型で外部仮説なしに `rfl` で導出（`kcwStdOrder`）。
--   (4) は、M353F の κ が実際に住む G_K-加群 `galH1TrivialModule`（tkcThetaCocycle/
--   tkcClass の係数加群）の作用が M322F/M443F の `cycTrivialAction`（恒等作用）と
--   各点で literally 一致すること（`kcwKummerAction`）を確認した上で、
--   `cid_galois_equivariant` をこの具体的な作用ペアに実インスタンス化し
--   （`kcwTrivialExpMod` で hchar を外部仮説でなく証明）、cidThetaMuIso が
--   κ の住む加群構造の下で G_K 同変であることを本物で示す（`kcw_galois_equivariant_concrete`/
--   `'`）。さらに κ が生成元を撃つ（κ.map g0 = E.ζ）という 1 点校正の下で、
--   tkcThetaChar の具体的な値が cidThetaMuIso の実現と一致すること
--   （`kcw_commutator_agree_concrete`）を証明し、M443F-7 の「同一元の 2 実現」を
--   具体 Kummer 指標のレベルまで下ろす。
-- 正直な限定: 本モジュールが閉じるのは (i) 標準模型 cycMuStd l 自身の位数（一般の
--   M353F 具体 Kummer 群 E で E.n=l を示したのではなく、E.n=l は引き続き外部仮説として
--   受け取る）、(ii) G_K が μ_l に**自明作用する**場合（μ_l⊂K、trivial CycGKAction）の
--   Galois 同変性——非自明な円分指標（真のガロア作用、χ≢1）を持つ一般ケースへの配線は
--   引き続き後続、(iii) κ が生成元を撃つ校正 κ.map g0 = E.ζ を外部の 1 点仮説として要求
--   する（この仮説自体は自然だが本モジュールでは導出しない）。完全副有限円分指標
--   Ẑ^×(1) レベルの同定は引き続き外部（M443F cid_model_scope (2)(3) をそのまま継承）。

/-
  IUT/KummerCharWiring.lean — M448F [実／昇格・柱E×柱A]
  分類: 実（(a) 昇格 — M443F(cid)の限定 (1) E.n=l 外部仮説・(4) generic な G_K 同変
  を、標準模型・trivial Galois 作用ケースで実際に閉じる）

  背景（M443F の限定・そのまま引用）:
    M443F（CyclotomeIdentification, prefix `cid`）は、標準模型 `cycMuStd l` を媒介に
    A 側（Zp p の μ_l 実現）と E 側（任意の CycMuGroup E, E.n=l）を明示同型
    `cidThetaMuIso` で同定し、Galois 同変性 `cid_galois_equivariant` を
    「両側に独立に与えられた CycGKAction が同じ mod-n 指数を持つ」という**一般論**
    として証明した。しかし cid_model_scope は正直に以下を限定として残した:
      (1) E.n = l（E 側 CycMuGroup の位数が A 側 l と一致すること）は外部仮定。
      (4) cid_galois_equivariant の「両側の CycGKAction が同じ指数を持つ」仮定
          hchar は一般論の仮説であり、M353F の具体的 Kummer 指標
          κ:GK→M.μ（ThetaKummerClass, prefix `tkc`）を用いた実接続は後続。

  本モジュールはこの 2 点を、**標準模型・trivial Galois 作用ケース**で実際に閉じる:

  1. **`kcwStdOrder`（本丸1・(1) を標準模型で閉じる）**: `(cycMuStd l hl).n = l` は
     `cycMuStd` の定義（構造体リテラルの `n := n` フィールド）から**外部仮説なしで
     `rfl`**。M443F の限定 (1) を、E := cycMuStd l 自身（標準模型）のケースで
     実際に外部仮説から解放する。
  2. **`kcwZetaLogOne`/`kcwTrivialExpMod`（本丸2・trivial 作用の円分指数）**:
     任意の CycMuGroup M で `M.log M.ζ % M.n = 1 % M.n`（`cycRig_pow_inj` と
     `M.μ.pow M.ζ 1 = M.ζ` の定義展開から）。ゆえに trivial CycGKAction
     （M322F `cycTrivialAction`）の円分指数 `cycRigExp` は mod n で恒等的に 1。
  3. **`kcwKummerAction`（本丸3・κ の住む加群 = cycTrivialAction、`rfl`）**:
     M353F-3b が明示する「μ_{2l}⊂K の本物のケース」（G_K が μ_{2l} に自明作用）の
     具体的な G_K-加群 `galH1TrivialModule GK M.μ M.comm`（tkcThetaCocycle/tkcClass
     が実際に係数として使う加群）の作用が、各点で M322F/M443F の
     `cycTrivialAction GK M`（恒等作用）と literally 一致することを `rfl` で確認する。
     これにより「κ が定める G_K 作用」は抽象的な仮説ではなく、**既存の具体的対象
     cycTrivialAction そのもの**であることが実際に判明する。
  4. **`kcw_galois_equivariant_concrete`/`kcw_galois_equivariant_concrete'`
     （本丸4・(4) を trivial 作用ケースで閉じる）**: `cid_galois_equivariant` を
     M := cycMuStd l・N := E（E.n=l）・ρM := ρN := cycTrivialAction に**実インスタンス化**
     し、hchar（両側の指数の mod-n 一致）を `kcwTrivialExpMod` で**外部仮説でなく証明**
     する。`kcwKummerAction` で書き換えれば、これは cidThetaMuIso が κ の実際の住む
     加群 `galH1TrivialModule` の作用と可換であることの本物の定理になる——
     M443F (4) の「generic な G_K 同変」を、M353F の κ が実際に生きる具体的な
     trivial 作用ケースへ実際に配線し、閉じる。
  5. **`kcw_nat_mod_toNat`/`kcw_commutator_agree_concrete`（本丸5・具体 κ の値との一致）**:
     M353F のテータ Kummer 指標 `tkcThetaChar E κ e`（κ(g)^e）の値が、κ が生成元を
     撃つ校正点 g0（κ.map g0 = E.ζ、1 点の外部仮定）で、M443F の
     `cid_commutator_agree_via_iso` の E 側実現（cidThetaMuIso の共有指数での像）と
     **ちょうど一致する**ことを、`tkc_galois_theta_link`（κ_Θ=κ(·)^e の定義展開）と
     `cycRig_pow_reduce`（E.n での周期還元）・Nat/Int mod の toNat 往復のみで完全証明する。
     これは M443F-7「同一の抽象元の 2 つの実現」を、抽象的な CycGKAction ではなく
     **M353F の具体的 Kummer 指標 κ のレベル**まで実際に下ろした接続である。
  6. `KummerCharWiringData`/`kummerCharWiringData`/`kcw_exists` — 総括レコード。
     `kcw_model_scope` — 残る限定の正直な宣言。

  * M448F-1 `kcwStdOrder`
  * M448F-2 `kcwZetaLogOne`/`kcwTrivialExpMod`
  * M448F-3 `kcwKummerAction`
  * M448F-4 `kcw_galois_equivariant_concrete`/`kcw_galois_equivariant_concrete'`
  * M448F-5 `kcw_nat_mod_toNat`/`kcw_commutator_agree_concrete`
  * M448F-6 `KummerCharWiringData`/`kummerCharWiringData`/`kcw_exists`/`kcw_model_scope`
  * M448F-7 実例

  **正直な限定（消去・弱化禁止）**:
  - `kcwStdOrder` が外部仮説なしに閉じるのは**標準模型 cycMuStd l 自身**の位数のみ
    ——M353F の一般の具体的 Kummer 群 E（特定の楕円曲線・特定のテータ関数から来る
    CycMuGroup）で E.n=l を証明したわけではない。一般の E については引き続き
    `hn : E.n = l` を外部仮定として受け取る（M443F と同じ位置づけ）。
  - `kcw_galois_equivariant_concrete`/`'` が閉じるのは **G_K が μ_l に自明作用する
    trivial ケース**（M353F-3b「μ_{2l}⊂K」）のみ。真に非自明な円分指標
    （χ≢1、不分岐でない一般の局所体上の実ガロア作用）を持つ CycGKAction どうしの
    Galois 同変性の κ への接続は、本モジュールでは扱わない（`cid_galois_equivariant`
    自体は一般論として引き続き利用可能だが、trivial 以外のケースでの κ との
    具体的接続は後続）。
  - `kcw_commutator_agree_concrete` は κ が校正点で生成元を撃つという
    **1 点の外部仮定 `hg0 : κ.map g0 = E.ζ`** を必要とする——この仮定自体は自然
    （κ の正規化）だが本モジュールの証明本体では導出しない（外部から受け取る）。
  - 完全な副有限円分指標 Ẑ^×(1) レベルの同定・p 進解析的同一視・A 側 ζ の位数 l 性
    hζl・distinctness hdist の外部仮定という M443F cid_model_scope の (2)(3) の限定は
    そのまま継承する（本モジュールは解消しない）。
  - 全て選択公理を証明本体で新規導入せず（新規 Classical・新規 Classical.choice なし）。
    禁止タクティク不使用（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
    nth_rewrite/field_simp 不使用）。許可タクティクのみ（cases/obtain/induction/rw/show/
    refine/exact/apply/intro/generalize/funext/omega）。共有ファイル
    （IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
    一般名は `kcw` 接頭辞で衝突回避（グレップ確認済み・既存コードに重複なし）。
-/
import IUT.CyclotomeIdentification
import IUT.ThetaKummerClass
import IUT.CyclotomicRigidity

namespace IUT

/-! ## M448F-1: 標準模型の位数——M443F (1) を標準模型で閉じる -/

/-- **定理 (M448F-1: 本丸・標準模型の位数)** — `cycMuStd l hl` の位数はちょうど l。
    `cycMuStd` の定義（構造体リテラルの `n := n` フィールド）から**外部仮説なしで
    `rfl`**。M443F cid_model_scope (1)「E.n=l を外部仮定とする」を、標準模型
    E := cycMuStd l 自身のケースで実際に閉じる。 -/
theorem kcwStdOrder (l : Nat) (hl : 1 ≤ l) : (cycMuStd l hl).n = l := rfl

/-! ## M448F-2: trivial Galois 作用の円分指数——恒等的に 1 -/

/-- **定理 (M448F-2a)** — 任意の CycMuGroup M で `M.log M.ζ % M.n = 1 % M.n`。
    ζ=ζ^1 と ζ^{log ζ}=ζ の相異性（`cycRig_pow_inj`）から、生成元自身の離散対数は
    mod n で 1 に一致する。 -/
theorem kcwZetaLogOne (M : CycMuGroup) : M.log M.ζ % M.n = 1 % M.n := by
  apply cycRig_pow_inj M.μ M.comm M.ζ M.n M.hn M.ord M.distinct (M.log M.ζ) 1
  rw [M.pow_log M.ζ]
  show M.ζ = M.μ.mul M.ζ (M.μ.pow M.ζ 0)
  show M.ζ = M.μ.mul M.ζ M.μ.one
  exact (M.μ.mul_one M.ζ).symm

/-- **定理 (M448F-2b: 本丸・trivial 作用の円分指数 ≡ 1)** — M322F `cycTrivialAction`
    （恒等作用）の円分指数 `cycRigExp` は、任意の g で mod n 1 に一致する
    （`cycRigExp GK M ρ g := M.log ((ρ.act g).map M.ζ)` が恒等作用で `M.log M.ζ` に
    定義展開され、M448F-2a に帰着）。trivial ケース（μ_n⊂K）の円分指標 χ≡1 の
    Nat-mod 版。 -/
theorem kcwTrivialExpMod (GK : Grp) (M : CycMuGroup) (g : GK.carrier) :
    cycRigExp GK M (cycTrivialAction GK M) g % M.n = 1 % M.n := by
  show M.log M.ζ % M.n = 1 % M.n
  exact kcwZetaLogOne M

/-! ## M448F-3: κ の住む G_K-加群は cycTrivialAction そのもの -/

/-- **定理 (M448F-3: 本丸・κ の作用の具体同定)** — M353F-3b が明示する
    「μ_{2l}⊂K の本物のケース」の G_K-加群 `galH1TrivialModule GK M.μ M.comm`
    （M353F の `tkcThetaCocycle`/`tkcClass` が実際に係数として使う加群）の
    各点作用は、M322F/M443F の `cycTrivialAction GK M`（恒等作用）と literally
    一致する（両者とも `fun _ => {map := fun z => z, ...}`、`rfl`）。
    「κ が定める G_K 作用」は抽象的な仮説対象ではなく、既存の具体的対象
    `cycTrivialAction` そのものであることの確認——M443F (4) を具体化する第一歩。 -/
theorem kcwKummerAction (GK : Grp) (M : CycMuGroup) (g : GK.carrier) (z : M.μ.carrier) :
    ((galH1TrivialModule GK M.μ M.comm).act g).map z = ((cycTrivialAction GK M).act g).map z :=
  rfl

/-! ## M448F-4: Galois 同変性を trivial 作用ケースへ実インスタンス化——M443F (4) を閉じる -/

/-- **定理 (M448F-4a: 本丸・trivial 作用での具体的 Galois 同変性)** — 標準模型
    `cycMuStd l` と任意の CycMuGroup E（E.n=l）の間の同型 `cidThetaMuIso`
    （の下位関数 `cmuMap`）は、両側に `cycTrivialAction` を取れば G_K 同変である。
    `cid_galois_equivariant` を ρM=ρN=cycTrivialAction という**具体的なペア**へ
    実インスタンス化し、hchar（両側の指数の mod-n 一致）を `kcwTrivialExpMod`
    （外部仮説でなく証明済み）で満たす。 -/
theorem kcw_galois_equivariant_concrete (GK : Grp) (l : Nat) (hl : 2 ≤ l)
    (E : CycMuGroup) (hn : E.n = l) (g : GK.carrier)
    (z : (cycMuStd l (by omega)).μ.carrier) :
    cmuMap (cycMuStd l (by omega)) E
        (((cycTrivialAction GK (cycMuStd l (by omega))).act g).map z)
      = ((cycTrivialAction GK E).act g).map (cmuMap (cycMuStd l (by omega)) E z) :=
  cid_galois_equivariant GK (cycMuStd l (by omega)) E hn.symm
    (cycTrivialAction GK (cycMuStd l (by omega))) (cycTrivialAction GK E)
    (fun g' => by
      rw [kcwTrivialExpMod GK (cycMuStd l (by omega)) g', kcwTrivialExpMod GK E g', hn]
      rfl)
    g z

/-- **定理 (M448F-4b: 本丸・κ の実加群での Galois 同変性——M443F (4) を閉じる)** —
    M448F-4a を `kcwKummerAction` で書き換え、cidThetaMuIso（の下位関数 cmuMap）が
    M353F の κ が実際に住む G_K-加群 `galH1TrivialModule`（tkcThetaCocycle/tkcClass
    の係数加群、trivial ケース）の作用と可換であることを本物で示す。M443F (4)
    「generic な G_K 同変」を、M353F の κ が生きる具体的な trivial 作用ケースへ
    実際に配線し、閉じる。 -/
theorem kcw_galois_equivariant_concrete' (GK : Grp) (l : Nat) (hl : 2 ≤ l)
    (E : CycMuGroup) (hn : E.n = l) (g : GK.carrier)
    (z : (cycMuStd l (by omega)).μ.carrier) :
    cmuMap (cycMuStd l (by omega)) E
        (((galH1TrivialModule GK (cycMuStd l (by omega)).μ (cycMuStd l (by omega)).comm).act g).map z)
      = ((galH1TrivialModule GK E.μ E.comm).act g).map
          (cmuMap (cycMuStd l (by omega)) E z) := by
  rw [kcwKummerAction GK (cycMuStd l (by omega)) g z,
    kcwKummerAction GK E g (cmuMap (cycMuStd l (by omega)) E z)]
  exact kcw_galois_equivariant_concrete GK l hl E hn g z

/-! ## M448F-5: 具体 Kummer 指標 κ の値との一致——校正点での実現の一致 -/

/-- 補助補題: Nat 剰余は Int 剰余の toNat に一致する（`Int.ofNat_mod_ofNat` と
    `Int.toNat_natCast` の合成）。 -/
theorem kcw_nat_mod_toNat (a l : Nat) : a % l = (((a : Int) % (l : Int)).toNat) := by
  rw [Int.ofNat_mod_ofNat, Int.toNat_natCast]

/-- **定理 (M448F-5: 本丸・具体 Kummer 指標との一致——M443F-7 を κ のレベルへ)** —
    M353F のテータ Kummer 指標 `tkcThetaChar E κ (tccbExp j)`（κ(g)^{tccbExp j}）の
    校正点 g0（κ.map g0 = E.ζ、κ が生成元を撃つという 1 点の外部校正）での値は、
    M443F の `cidThetaMuIso` が共有指数 tccbExp j で与える E 側実現に**ちょうど
    一致する**。`tkc_galois_theta_link`（κ_Θ の定義展開）・`cycRig_pow_reduce`
    （E.n での周期還元）・Nat/Int mod の toNat 往復のみで完全証明する。M443F-7
    「同一の抽象元の 2 つの実現」を、抽象的な CycGKAction ではなく M353F の
    具体的 Kummer 指標 κ のレベルまで実際に下ろす。 -/
theorem kcw_commutator_agree_concrete (GK : Grp) (l : Nat) (hl : 2 ≤ l)
    (E : CycMuGroup) (hn : E.n = l) (κ : Hom GK E.μ) (g0 : GK.carrier)
    (hg0 : κ.map g0 = E.ζ) (p : Nat) (ζ0 : (Zp p).carrier) (j : Nat) :
    (tkcThetaChar E κ (tccbExp j)).map g0
      = (cidThetaMuIso p l hl ζ0 E hn).map
          (Quot.mk (modCong l).rel ((tccbExp j : Nat) : Int)) := by
  rw [(cid_commutator_agree_via_iso p l hl ζ0 E hn j).2,
    tkc_galois_theta_link E κ (tccbExp j) g0]
  show E.μ.pow (κ.map g0) (tccbExp j)
      = E.μ.pow E.ζ (((tccbExp j : Nat) : Int) % ((l : Nat) : Int)).toNat
  rw [hg0, ← kcw_nat_mod_toNat (tccbExp j) l, ← hn]
  exact cycRig_pow_reduce E.μ E.comm E.ζ E.n E.ord (tccbExp j)

/-! ## M448F-6: 総括レコードと残る限定の宣言 -/

/-- **M448F-6a: Kummer 指標配線データ** — 標準模型の位数（外部仮説なし）・κ の
    住む加群と cycTrivialAction の一致・trivial ケースでの具体的 Galois 同変性・
    校正点での κ 値と cidThetaMuIso 実現の一致を一括束ねる（M443F (1)(4) を
    trivial 作用・標準模型ケースで閉じるデータ）。 -/
structure KummerCharWiringData (GK : Grp) (l : Nat) (hl : 2 ≤ l)
    (E : CycMuGroup) (hn : E.n = l) (κ : Hom GK E.μ) (g0 : GK.carrier)
    (hg0 : κ.map g0 = E.ζ) (p : Nat) (ζ0 : (Zp p).carrier) where
  /-- 標準模型自身の位数は外部仮説なしに l。 -/
  stdOrder : (cycMuStd l (by omega)).n = l
  /-- κ の住む trivial 加群の作用は cycTrivialAction と各点一致。 -/
  kummerAction : ∀ (g : GK.carrier) (z : E.μ.carrier),
    ((galH1TrivialModule GK E.μ E.comm).act g).map z = ((cycTrivialAction GK E).act g).map z
  /-- trivial ケースでの具体的 Galois 同変性（κ の加群レベル）。 -/
  galoisEquivariant : ∀ (g : GK.carrier) (z : (cycMuStd l (by omega)).μ.carrier),
    cmuMap (cycMuStd l (by omega)) E
        (((galH1TrivialModule GK (cycMuStd l (by omega)).μ (cycMuStd l (by omega)).comm).act g).map z)
      = ((galH1TrivialModule GK E.μ E.comm).act g).map
          (cmuMap (cycMuStd l (by omega)) E z)
  /-- 校正点 g0 での κ の値と cidThetaMuIso 実現の一致（全ての共有指数 j で）。 -/
  commutatorAgree : ∀ j : Nat,
    (tkcThetaChar E κ (tccbExp j)).map g0
      = (cidThetaMuIso p l hl ζ0 E hn).map
          (Quot.mk (modCong l).rel ((tccbExp j : Nat) : Int))

/-- **M448F-6b: witness 本体**（全フィールドを本モジュールの完全証明で埋める）。 -/
def kummerCharWiringData (GK : Grp) (l : Nat) (hl : 2 ≤ l)
    (E : CycMuGroup) (hn : E.n = l) (κ : Hom GK E.μ) (g0 : GK.carrier)
    (hg0 : κ.map g0 = E.ζ) (p : Nat) (ζ0 : (Zp p).carrier) :
    KummerCharWiringData GK l hl E hn κ g0 hg0 p ζ0 where
  stdOrder := kcwStdOrder l (by omega)
  kummerAction := kcwKummerAction GK E
  galoisEquivariant := kcw_galois_equivariant_concrete' GK l hl E hn
  commutatorAgree := fun j => kcw_commutator_agree_concrete GK l hl E hn κ g0 hg0 p ζ0 j

/-- **定理 (M448F-6c: capstone — Kummer 指標配線データの存在)** — E.n=l・κ の校正
    κ.map g0=E.ζ を外部仮定として与えれば、標準模型の位数（外部仮説なし）・κ の
    trivial 加群作用と cycTrivialAction の一致・trivial ケースでの具体的 Galois
    同変性・校正点での実現一致（M443F (1)(4) を trivial 作用・標準模型ケースで
    閉じるデータ）が存在する。 -/
theorem kcw_exists (GK : Grp) (l : Nat) (hl : 2 ≤ l)
    (E : CycMuGroup) (hn : E.n = l) (κ : Hom GK E.μ) (g0 : GK.carrier)
    (hg0 : κ.map g0 = E.ζ) (p : Nat) (ζ0 : (Zp p).carrier) :
    Nonempty (KummerCharWiringData GK l hl E hn κ g0 hg0 p ζ0) :=
  ⟨kummerCharWiringData GK l hl E hn κ g0 hg0 p ζ0⟩

/-- **kcw_model_scope（正直な限定の宣言）**: 本モジュールが実際に閉じるのは
    (i) 標準模型 cycMuStd l 自身の位数（一般の M353F 具体 Kummer 群 E での E.n=l は
    引き続き外部仮説）、(ii) G_K が μ_l に自明作用する trivial ケース（μ_l⊂K）での
    cidThetaMuIso の Galois 同変性を κ が実際に住む加群 galH1TrivialModule へ配線
    したもの（非自明な円分指標を持つ一般ケースへの κ 接続は後続）、(iii) κ が生成元
    を撃つという 1 点の外部校正 hg0 の下での、tkcThetaChar の値と cidThetaMuIso
    実現の一致——である。完全副有限円分指標 Ẑ^×(1) レベルの同定・A 側 hζl・hdist の
    外部仮定という M443F cid_model_scope (2)(3) の限定はそのまま継承する。 -/
theorem kcw_model_scope (GK : Grp) (l : Nat) (hl : 2 ≤ l) :
    (cycMuStd l (by omega)).n = l ∧
    ∀ (E : CycMuGroup), E.n = l →
      ∀ (g : GK.carrier) (z : (cycMuStd l (by omega)).μ.carrier),
        cmuMap (cycMuStd l (by omega)) E
            (((cycTrivialAction GK (cycMuStd l (by omega))).act g).map z)
          = ((cycTrivialAction GK E).act g).map (cmuMap (cycMuStd l (by omega)) E z) :=
  ⟨kcwStdOrder l (by omega), fun E hn g z => kcw_galois_equivariant_concrete GK l hl E hn g z⟩

/-! ## M448F-7: 実例 -/

/-- 実例: 標準模型 cycMuStd 5 自身の位数が外部仮説なしに 5。 -/
example : (cycMuStd 5 (by omega)).n = 5 := kcwStdOrder 5 (by omega)

/-- 実例: 標準模型 cycMuStd 5 の自己同定（E := cycMuStd 5 自身）で、κ の trivial
    加群作用と cycTrivialAction が具体的に Galois 同変であることを、
    本物の絶対ガロア群 G_ℚ 上で確認する。 -/
example (g : (algCloAbsGalois algCloTrivialTower).carrier)
    (z : (cycMuStd 5 (by omega)).μ.carrier) :
    cmuMap (cycMuStd 5 (by omega)) (cycMuStd 5 (by omega))
        (((galH1TrivialModule (algCloAbsGalois algCloTrivialTower)
            (cycMuStd 5 (by omega)).μ (cycMuStd 5 (by omega)).comm).act g).map z)
      = ((galH1TrivialModule (algCloAbsGalois algCloTrivialTower)
          (cycMuStd 5 (by omega)).μ (cycMuStd 5 (by omega)).comm).act g).map
          (cmuMap (cycMuStd 5 (by omega)) (cycMuStd 5 (by omega)) z) :=
  kcw_galois_equivariant_concrete' (algCloAbsGalois algCloTrivialTower) 5 (by omega)
    (cycMuStd 5 (by omega)) rfl g z

/-- 実例: κ := 恒等 Hom（E.μ 自身を G_K とする最も単純な校正インスタンス）・
    g0 := E.ζ（κ.map g0 = E.ζ が rfl で成立）で、tkcThetaChar の値と
    cidThetaMuIso 実現が一致することを確認する。 -/
example (j : Nat) :
    (tkcThetaChar (cycMuStd 5 (by omega))
        ({ map := fun z => z, map_mul := fun _ _ => rfl } :
          Hom (cycMuStd 5 (by omega)).μ (cycMuStd 5 (by omega)).μ)
        (tccbExp j)).map (cycMuStd 5 (by omega)).ζ
      = (cidThetaMuIso 7 5 (by omega) (zpOne 7) (cycMuStd 5 (by omega)) rfl).map
          (Quot.mk (modCong 5).rel ((tccbExp j : Nat) : Int)) :=
  kcw_commutator_agree_concrete (cycMuStd 5 (by omega)).μ 5 (by omega)
    (cycMuStd 5 (by omega)) rfl
    ({ map := fun z => z, map_mul := fun _ _ => rfl } :
      Hom (cycMuStd 5 (by omega)).μ (cycMuStd 5 (by omega)).μ)
    (cycMuStd 5 (by omega)).ζ rfl 7 (zpOne 7) j

end IUT
