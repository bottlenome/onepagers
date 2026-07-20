/-
  IUT/TateModuleEndoRing.lean — TMER（柱A7 A7f: 実 Tate 加群 T = ℤ₃(1) = `tmzLimit`
  の自己準同型の**環構造**——合成 = 指数族の積・点ごとの積 = 指数族の和・恒等 = 1・
  自明 = 0——を本物に建設し、`TateModuleIndeterminacy` の正直な限定 (4)
  「End(ℤ₃(1)) ≅ ℤ₃ は指数族表示・**End の環構造・合成=積も未**（後続の昇格ターゲット）」
  を本物へ昇格する）

  ── 主要成果の分類: **[実／(a)昇格＋(b)先行建設]**（骨格・模型・代理でなく、既存の実
     Tate 加群 T = ℤ₃(1) = `tmzLimit`（tmz で本物に構成）と、その自己準同型の完全分類
     `tmeEndoData`（tme で本物に建設・各 End f を指数族 `tmeChar f` に落とす）の上で、
     **End(T) の環演算がその指数表示（ℤ₃ 元）でどう振る舞うか**を本物に確立する:
      (i)  **合成 = 積**: `tmeChar (Hom.comp f g) n ≡ tmeChar f n · tmeChar g n (mod 3^{n+1})`
           ——End(T) の乗法（＝合成）が指数族の積に一致する（`tmer_char_comp`）。
      (ii) **点ごとの積 = 和**: 可換群 μ 上の点ごとの積 `tmerAdd f g`（(f·g)(y)=f(y)·g(y)・
           可換ゆえ群自己準同型）は指数族の**和**に落ちる
           `tmeChar (tmerAdd f g) n ≡ tmeChar f n + tmeChar g n`（`tmer_char_add`）。
      (iii)**単位元と零元**: 恒等自己準同型 `tmerId` は指数 1（`tmer_char_id`）、
           自明自己準同型 `tmerZero`（y↦1）は指数 0（`tmer_char_zero`）。
      (iv) **可換性**: 合成が指数の積 = 積の可換性ゆえ `tmeChar (Hom.comp f g)
           ≡ tmeChar (Hom.comp g f)`——End(ℤ₃(1)) は可換環（`tmer_comp_comm`）。
     これは TMI 限定 (4) が名指しした「End の環構造・合成=積」の本物の建設であり、指数表示
     `tmeChar : End(T) → ℤ₃`（整合冪族）が**環準同型（+,·,0,1 を保つ）**であることを
     消去形（各演算ごとの合同定理）で確立する。

  **complete_pct 影響**: A7（実円分剛性）A7f——**実 ℤ₃(1) の自己準同型環 End(T) の
  乗法（合成）が指数族の積に、点ごとの積が指数族の和に一致し、指数表示が環演算を保つ**
  ことを極限レベルで本物に確立する。TMI 限定 (4)「End の環構造・合成=積も未」の昇格。
  A7 予測 0.56→0.57 級（真水・小幅・数値は独立監査が確定）。**正直な限定は消さない**——
  A2 の実 ℤ₃ 環オブジェクト z3 との環同型接続・全射性・distributivity の環公理としての
  別束ねは依然未形式化であり、本ファイルは指数表示上の +,·,0,1 保存のみを主張する。

  内容（TMER-0〜3）:
   * `tmer_mul4`         — 可換群の 4 項入れ替え（点ごと積 endo の map_mul の核）。TMER-0。
   * `tmer_char_comp`    — ★合成 = 指数族の積。TMER-1。
   * `tmer_comp_comm`    — ★End(ℤ₃(1)) は可換環（合成の指数可換性）。TMER-1。
   * `tmerId`/`tmer_char_id`   — 恒等 = 指数 1。TMER-2。
   * `tmerZero`/`tmer_char_zero` — 自明 = 指数 0。TMER-2。
   * `tmerAdd`/`tmer_char_add`  — ★点ごと積 = 指数族の和。TMER-2。
   * `TmerEndoRingData`/`tmerEndoRingData` — capstone（指数表示が環演算を保つ）。TMER-3。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (1) **A2 の実 ℤ₃ 環 z3 との環同型接続は依然未形式化**: 本ファイルは End(T) の演算が
       指数族（整合 Nat 族 mod 3^{n+1}）の +,·,0,1 に落ちることを言うが、その指数族を
       実 ℤ₃ 環オブジェクト z3 と環同型で同定する接続は建てない（TMI 限定 (4) の残り半分・
       後続の昇格ターゲットとして依然名指しのまま残す）。
   (2) **distributivity・環公理の別束ねは未**: +,· が指数族の +,· に一致することは示すが、
       End(T) を抽象環として full ring axioms（分配則を End の演算自身で）で束ねる capstone は
       作らない。指数表示が既知の可換環 ℤ₃（の Nat 剰余モデル）の演算を保つ、という消去形で
       述べる（環公理は像側 ℤ₃ から従うが、それは本ファイルの主張でない）。
   (3) **mono-theta 円分剛性（[EtTh]）は依然 0**: End/Aut の環構造を特徴付けるだけであり、
       ẑ^×（p=3: ℤ₃^×）不定性を殺す仕組み（IUT 本丸・柱 E/D 後続）は範囲外。A7=1 には遠い。
   (4) **p = 3 固定・円分切片限定・位相未形式化・幾何側不在**: T=ℤ₃(1)・G=Gal(ℚ(ζ_{3^∞})/ℚ)。
       実 G_{ℚ₃}・実 G_ℚ・一般素数 p・limitTopology 連続性・K̄/幾何的 cyclotome は含めない
       （tmz/cra/cli/tme/tmi の正直申告を継承）。
   (5) 既存の正直な限定（M322F・cra (i)-(iv)・tmz (i)-(iv)・tme (1)-(6)・tmi (1)-(6)）は
       **一切消さない・弱めない**。本ステップは並置＋昇格のみ——tmi 限定 (4) の「合成=積」
       部分を本物にし、z3 環同型接続部分は限定 (1) として明示的に残す。

  全て選択公理不使用（新規 `Classical.choice` を証明本体に導入しない・propext/Quot.sound
  のみ）。witness は全て閉じた式（`tmeChar`・成分 mul/pow）。禁止タクティク（simp/decide/
  by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。3^ℓ は
  omega に生で渡さない（`zpu_pow_pos`/`zpu_one_lt`/`cci_indexG` 経由）。新規ファイル 1 個のみ
  （共有ファイル IUT.lean/build.sh/dashboard/graph/tools は不更新・親が統合）。prefix `tmer`。
-/
import IUT.TateModuleEndo
import IUT.TateModuleZ3
import IUT.CyclotomicCharIso
import IUT.Zmod3PowUnits

namespace IUT

/-! ## TMER-0: 可換群の 4 項入れ替え（点ごと積 endo の map_mul の核） -/

/-- **TMER-0: 可換群の 4 項入れ替え** — (a·b)·(c·d) = (a·c)·(b·d)（結合律＋b,c の可換）。
    点ごとの積 endo `tmerAdd` の準同型性 (f·g)(y·z) = ((f·g)y)·((f·g)z) の核。 -/
theorem tmer_mul4 (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a) (a b c d : G.carrier) :
    G.mul (G.mul a b) (G.mul c d) = G.mul (G.mul a c) (G.mul b d) := by
  rw [G.mul_assoc a b (G.mul c d), ← G.mul_assoc b c d, hc b c, G.mul_assoc c b d,
      ← G.mul_assoc a c (G.mul b d)]

/-! ## TMER-1: ★合成 = 指数族の積（End(T) の乗法構造） -/

/-- **TMER-1a（★合成 = 積）: `tmeChar (Hom.comp f g) n ≡ tmeChar f n · tmeChar g n (mod 3^{n+1})`**
    ——End(ℤ₃(1)) の乗法（＝合成）が指数族の積に一致する。整合 ζ 極限元 `tmeZetaLim` を
    (Hom.comp f g)（＝f∘g）で送り、`tme_endo_pow` を三度（合成・g・f∘の順）適用し
    `cycRig_pow_mul` で指数を積へ集約、`cci_indexG` で mod 合流。TMI 限定 (4)「合成=積」の昇格。 -/
theorem tmer_char_comp (f g : Hom tmzLimit tmzLimit) (n : Nat) :
    tmeChar (Hom.comp f g) n % 3 ^ (n + 1)
      = tmeChar f n * tmeChar g n % 3 ^ (n + 1) := by
  have hz : tmeZetaLim.val n = cmrZeta (n + 1) (by omega) := rfl
  -- g(ζ)_n = ζ^{χ_g}
  have hg' : (g.map tmeZetaLim).val n
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar g n) := by
    have h := tme_endo_pow g tmeZetaLim n
    rw [hz] at h
    exact h
  -- (f∘g)(ζ)_n = ζ^{χ_{f∘g}}
  have e1 : ((Hom.comp f g).map tmeZetaLim).val n
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar (Hom.comp f g) n) := by
    have h := tme_endo_pow (Hom.comp f g) tmeZetaLim n
    rw [hz] at h
    exact h
  -- (f∘g)(ζ)_n = f(g(ζ))_n = (ζ^{χ_g})^{χ_f} = ζ^{χ_g·χ_f}
  have e2 : ((Hom.comp f g).map tmeZetaLim).val n
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
          (tmeChar g n * tmeChar f n) := by
    show (f.map (g.map tmeZetaLim)).val n
       = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega))
          (tmeChar g n * tmeChar f n)
    rw [tme_endo_pow f (g.map tmeZetaLim) n, hg',
        ← cycRig_pow_mul (cmrGrp (n + 1) (by omega)) (cmr_comm (n + 1) (by omega))
          (cmrZeta (n + 1) (by omega)) (tmeChar g n) (tmeChar f n)]
  -- ctmPow レベルで突き合わせ、cci_indexG
  have hval : ctmPow (n + 1) (by omega) (tmeChar (Hom.comp f g) n)
      = ctmPow (n + 1) (by omega) (tmeChar g n * tmeChar f n) := by
    have hh := e1.symm.trans e2
    have hv := congrArg Subtype.val hh
    rw [cmr_pow_zeta (n + 1) (by omega) (tmeChar (Hom.comp f g) n),
        cmr_pow_zeta (n + 1) (by omega) (tmeChar g n * tmeChar f n)] at hv
    exact hv
  rw [ctm_pow_mod (n + 1) (by omega) (tmeChar g n * tmeChar f n)] at hval
  have hidx := cci_indexG (n + 1) (by omega) (tmeChar (Hom.comp f g) n)
    ((tmeChar g n * tmeChar f n) % 3 ^ (n + 1))
    (Nat.mod_lt _ (zpu_pow_pos (n + 1))) hval
  rw [hidx, Nat.mul_comm (tmeChar g n) (tmeChar f n)]

/-- **TMER-1b（★可換環）: End(ℤ₃(1)) は可換環** — 合成の指数族は積の可換性ゆえ
    `tmeChar (Hom.comp f g) n ≡ tmeChar (Hom.comp g f) n (mod 3^{n+1})`。実 ℤ₃ が可換環
    であることの End 側の反映（合成が可換に見える＝Aut は可換群）。 -/
theorem tmer_comp_comm (f g : Hom tmzLimit tmzLimit) (n : Nat) :
    tmeChar (Hom.comp f g) n % 3 ^ (n + 1)
      = tmeChar (Hom.comp g f) n % 3 ^ (n + 1) := by
  rw [tmer_char_comp f g n, tmer_char_comp g f n, Nat.mul_comm (tmeChar f n) (tmeChar g n)]

/-! ## TMER-2: 単位元・零元・点ごとの積（End(T) の加法構造） -/

/-- **TMER-2a: 恒等自己準同型** `tmerId`（y↦y・map_mul は rfl）。 -/
def tmerId : Hom tmzLimit tmzLimit where
  map := fun y => y
  map_mul := fun _ _ => rfl

/-- **TMER-2b: 恒等の指数は 1** — `tmeChar tmerId n ≡ 1 (mod 3^{n+1})`（乗法の単位元）。 -/
theorem tmer_char_id (n : Nat) : tmeChar tmerId n % 3 ^ (n + 1) = 1 := by
  have hz : tmeZetaLim.val n = cmrZeta (n + 1) (by omega) := rfl
  have e1 : cmrZeta (n + 1) (by omega)
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar tmerId n) := by
    have h := tme_endo_pow tmerId tmeZetaLim n
    rw [hz] at h
    exact h
  have hone : (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) 1
      = cmrZeta (n + 1) (by omega) :=
    (cmrGrp (n + 1) (by omega)).mul_one (cmrZeta (n + 1) (by omega))
  have hval : ctmPow (n + 1) (by omega) (tmeChar tmerId n) = ctmPow (n + 1) (by omega) 1 := by
    have hh : (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar tmerId n)
        = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) 1 := by
      rw [hone]; exact e1.symm
    have hv := congrArg Subtype.val hh
    rw [cmr_pow_zeta (n + 1) (by omega) (tmeChar tmerId n),
        cmr_pow_zeta (n + 1) (by omega) 1] at hv
    exact hv
  exact cci_indexG (n + 1) (by omega) (tmeChar tmerId n) 1 (zpu_one_lt (n + 1) (by omega)) hval

/-- **TMER-2c: 自明自己準同型** `tmerZero`（y↦1・map_mul は 1=1·1）。 -/
def tmerZero : Hom tmzLimit tmzLimit where
  map := fun _ => tmzLimit.one
  map_mul := fun _ _ => (tmzLimit.one_mul tmzLimit.one).symm

/-- **TMER-2d: 自明の指数は 0** — `tmeChar tmerZero n ≡ 0 (mod 3^{n+1})`（加法の零元）。 -/
theorem tmer_char_zero (n : Nat) : tmeChar tmerZero n % 3 ^ (n + 1) = 0 := by
  have hz : tmeZetaLim.val n = cmrZeta (n + 1) (by omega) := rfl
  have e1 : (tmzG n).one
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar tmerZero n) := by
    have h := tme_endo_pow tmerZero tmeZetaLim n
    rw [hz] at h
    exact h
  have hpow0 : (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) 0 = (tmzG n).one := rfl
  have hval : ctmPow (n + 1) (by omega) (tmeChar tmerZero n) = ctmPow (n + 1) (by omega) 0 := by
    have hh : (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar tmerZero n)
        = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) 0 := by
      rw [hpow0]; exact e1.symm
    have hv := congrArg Subtype.val hh
    rw [cmr_pow_zeta (n + 1) (by omega) (tmeChar tmerZero n),
        cmr_pow_zeta (n + 1) (by omega) 0] at hv
    exact hv
  exact cci_indexG (n + 1) (by omega) (tmeChar tmerZero n) 0 (zpu_pow_pos (n + 1)) hval

/-- **TMER-2e 補: T = ℤ₃(1) は可換群** — `tmzLimit.mul a b = tmzLimit.mul b a`（成分ごと
    `cmr_comm`）。点ごと積 endo の準同型性の核。 -/
theorem tmer_limit_comm (a b : tmzLimit.carrier) : tmzLimit.mul a b = tmzLimit.mul b a := by
  apply Subtype.ext
  funext n
  exact cmr_comm (n + 1) (by omega) (a.val n) (b.val n)

/-- **TMER-2e: 点ごとの積自己準同型** `tmerAdd f g`（(f·g)(y)=f(y)·g(y)）。可換群 T ゆえ
    群自己準同型（map_mul は極限レベルの 4 項入れ替え `tmer_mul4`）。End(T) の加法（＝点ごと積）。 -/
def tmerAdd (f g : Hom tmzLimit tmzLimit) : Hom tmzLimit tmzLimit where
  map := fun y => tmzLimit.mul (f.map y) (g.map y)
  map_mul := fun y z => by
    rw [f.map_mul y z, g.map_mul y z]
    exact tmer_mul4 tmzLimit tmer_limit_comm (f.map y) (f.map z) (g.map y) (g.map z)

/-- **TMER-2f（★点ごと積 = 和）: `tmeChar (tmerAdd f g) n ≡ tmeChar f n + tmeChar g n (mod 3^{n+1})`**
    ——End(T) の加法（点ごと積）が指数族の和に落ちる。整合 ζ 極限元で読み、成分ごと
    `tmz_pow_add`（ζ^a·ζ^b=ζ^{a+b}）と `cci_indexG`。 -/
theorem tmer_char_add (f g : Hom tmzLimit tmzLimit) (n : Nat) :
    tmeChar (tmerAdd f g) n % 3 ^ (n + 1)
      = (tmeChar f n + tmeChar g n) % 3 ^ (n + 1) := by
  have hz : tmeZetaLim.val n = cmrZeta (n + 1) (by omega) := rfl
  have hf : (f.map tmeZetaLim).val n
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar f n) := by
    have h := tme_endo_pow f tmeZetaLim n
    rw [hz] at h
    exact h
  have hg : (g.map tmeZetaLim).val n
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar g n) := by
    have h := tme_endo_pow g tmeZetaLim n
    rw [hz] at h
    exact h
  have e1 : ((tmerAdd f g).map tmeZetaLim).val n
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar (tmerAdd f g) n) := by
    have h := tme_endo_pow (tmerAdd f g) tmeZetaLim n
    rw [hz] at h
    exact h
  have e2 : ((tmerAdd f g).map tmeZetaLim).val n
      = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar f n + tmeChar g n) := by
    show (cmrGrp (n + 1) (by omega)).mul ((f.map tmeZetaLim).val n) ((g.map tmeZetaLim).val n)
       = (cmrGrp (n + 1) (by omega)).pow (cmrZeta (n + 1) (by omega)) (tmeChar f n + tmeChar g n)
    rw [hf, hg, tmz_pow_add (n + 1) (by omega) (tmeChar f n) (tmeChar g n)]
  have hval : ctmPow (n + 1) (by omega) (tmeChar (tmerAdd f g) n)
      = ctmPow (n + 1) (by omega) (tmeChar f n + tmeChar g n) := by
    have hh := e1.symm.trans e2
    have hv := congrArg Subtype.val hh
    rw [cmr_pow_zeta (n + 1) (by omega) (tmeChar (tmerAdd f g) n),
        cmr_pow_zeta (n + 1) (by omega) (tmeChar f n + tmeChar g n)] at hv
    exact hv
  rw [ctm_pow_mod (n + 1) (by omega) (tmeChar f n + tmeChar g n)] at hval
  exact cci_indexG (n + 1) (by omega) (tmeChar (tmerAdd f g) n)
    ((tmeChar f n + tmeChar g n) % 3 ^ (n + 1))
    (Nat.mod_lt _ (zpu_pow_pos (n + 1))) hval

/-! ## TMER-3: capstone — 指数表示が環演算を保つ -/

/-- **TMER-3a: End 環データ** — 実 ℤ₃(1) の自己準同型の指数表示 `tmeChar : End(T) → ℤ₃`
    （整合 Nat 族 mod 3^{n+1}）が環演算を保つ証明書: 合成 = 積・点ごと積 = 和・恒等 = 1・
    自明 = 0・合成の可換性。TMI 限定 (4)「End の環構造・合成=積」の本物の建設。
    **正直: z3 との環同型接続・distributivity の別束ねは含まない（限定 (1)(2)）。** -/
structure TmerEndoRingData where
  /-- 合成 = 指数族の積（End(T) の乗法構造）。 -/
  char_comp : ∀ (f g : Hom tmzLimit tmzLimit) (n : Nat),
    tmeChar (Hom.comp f g) n % 3 ^ (n + 1) = tmeChar f n * tmeChar g n % 3 ^ (n + 1)
  /-- 恒等 = 指数 1（乗法の単位元）。 -/
  char_id : ∀ (n : Nat), tmeChar tmerId n % 3 ^ (n + 1) = 1
  /-- 点ごとの積 = 指数族の和（End(T) の加法構造）。 -/
  char_add : ∀ (f g : Hom tmzLimit tmzLimit) (n : Nat),
    tmeChar (tmerAdd f g) n % 3 ^ (n + 1) = (tmeChar f n + tmeChar g n) % 3 ^ (n + 1)
  /-- 自明 = 指数 0（加法の零元）。 -/
  char_zero : ∀ (n : Nat), tmeChar tmerZero n % 3 ^ (n + 1) = 0
  /-- 合成の指数は可換（End(ℤ₃(1)) は可換環）。 -/
  comp_comm : ∀ (f g : Hom tmzLimit tmzLimit) (n : Nat),
    tmeChar (Hom.comp f g) n % 3 ^ (n + 1) = tmeChar (Hom.comp g f) n % 3 ^ (n + 1)

/-- **TMER-3b: witness** — 全フィールド既証明の純レコード。実 ℤ₃(1) の自己準同型環
    End(T) の指数表示が環演算（+,·,0,1）を保つことの A7f 本物の建設。 -/
def tmerEndoRingData : TmerEndoRingData where
  char_comp := tmer_char_comp
  char_id := tmer_char_id
  char_add := tmer_char_add
  char_zero := tmer_char_zero
  comp_comm := tmer_comp_comm

end IUT
