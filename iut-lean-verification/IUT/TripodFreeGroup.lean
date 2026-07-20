/-
  IUT/TripodFreeGroup.lean — BLW-1: tripod π₁ の第一データ = 自由群 F₂ の実 Grp
  ── 柱A・項目 A9（Belyi 化 / 遠アーベル幾何入力(実)）の本物の先行建設

  分類 **[実／(b) 本物の先行建設]**（簡約語 reduced words による本物の無限非可換群 F₂
  を core Lean だけでゼロから構成する。toy 群・surrogate・Bool 軌道を主語にしない。
  さらに F₂ を本物の対称群 `galPi1SymGrp`（M286F・明示両側逆 witness・choice 回避済）
  へ **忠実に**（左正則表現で単射に）埋め込み、非退化性＝真に自由であることを本物で示す）。

  **complete_pct 影響（A9 BLW-1）**: A9 の第 2 系統（遠アーベル入力・[AbsTopII] 側）で
  「自由群 F₂ の実 Grp（結合律・単位元・逆元を完全証明）＋ その `galPi1SymGrp` への
  忠実実現」を初建設する。**ただし設計監査（audit/pillar-A9-…-2026-07-20.md §2.3）の
  敵対的評価どおり、bare F₂ 単独の s_A9 寄与は +0.00–0.01 に留まる**——値は BLW-2
  （実 Kummer 被覆デッキ `TripodKummerMu3`・実装済）との束ね、および後続 BLW-4
  （実現準同型 F₂ ↠ ℤ/3×ℤ/3）で初めて立つ。本ファイル単独では
  「complete_pct 0 前進（柱横断の本物の群論インフラの新設）」として正直に報告する。

  ## 建設内容（全 choice-free・sorry なし・禁止タクティク不使用）
  * 文字 `tfgLtr = Bool × Bool`（生成元 × 符号）・Bool 値の簡約判定 `tfgRed`（Markov 不要）・
    相殺つき prepend `tfgLcons`（データ関数）。核補題 `tfg_lcons_cancel`
    （簡約語上で `lcons x ∘ lcons (linv x) = id`）は設計付録 A のスパイクを本実装で再検証。
  * 乗法 `tfgRmul u v = foldr lcons v u`（連結してから簡約）。**結合律 `tfg_rmul_assoc`**
    は crux 補題 `tfg_rmul_lcons` 経由で場合分け爆発を回避し完全証明（van der Waerden 型の
    核イディオムを直接使用）。逆元 `tfgIw`（逆順・逆文字）と **`tfg_rmul_iw_self`
    （rmul (inv w) w = []）** も完全証明。担体は簡約語の Subtype `tfgCarrier`。
  * **`tfgGrp : Grp`**（F₂）——群公理（結合律・左単位元・左逆元）を Subtype 上で完全証明。
  * **忠実実現**: 左正則表現 `tfgRegHom : Hom tfgGrp (galPi1SymGrp tfgCarrier)`
    （map_mul は結合律から・逆写像成分は `Grp.inv_mul_rev`）と、その**単射性
    `tfg_reg_injective`**（w ↦ (v ↦ w·v) の [] 上での値が w を復元）。これが F₂ の
    非退化性（真に自由・collapsing でない）の本物の witness。
  * 生成元 `tfgA`,`tfgB` と非可換 witness `tfg_ab_ne_ba`（ab ≠ ba）・distinctness
    （`tfg_a_ne_b`・`tfg_asq_ne_bsq` 等・簡約語のリスト計算）。
  * **普遍性（BONUS・存在＋生成元値＋一意性）**: 任意の `G : Grp` と `g₁ g₂ : G.carrier`
    に対し `tfgLift : Hom tfgGrp G`（語 ↦ 生成元の像の積）・`tfg_lift_a/b`（生成元へ値）・
    `tfg_lift_unique`（生成元を固定する準同型は tfgLift に一致）。⟹ F₂ の普遍性
    ∀ G g₁ g₂ ∃! hom が本物で閉じる。

  接続する既存部品（精読して再利用・再証明ゼロ）:
  * M286F GaloisPi1Iso: `galPi1Perm`（明示両側逆 witness の全単射）・`galPi1Perm.ext`・
    `galPi1PermComp`・`galPi1SymGrp`（本物の対称群 Grp）。van der Waerden 埋め込みの受け皿。
  * M16 SGA1 / FundamentalGroup: `Grp`・`Hom`・`Hom.Injective`・`Grp.mul_one`/`mul_inv`/
    `inv_mul_rev`/`inv_inv`（逆元計算・公理ゼロ導出）。

  **正直な限定**（何が本物で何が未達か・消去/弱化禁止・設計書 §3 の限定 1–6 を継承）:
  1. **「tripod の π₁ そのもの」ではない**: F₂ は簡約語による組合せ群であり、位相ループの
     群 π₁^top・スキームのエタール基本群 π₁^ét = F̂₂（副有限完備化）・π₁^temp との
     同定は不主張（ℂ・位相・被覆空間・エタールサイト皆無のリポジトリ恒久限定の継承）。
     機械可検証内容は「自由群 F₂（tripod π₁ の群論的内容）＋その `galPi1SymGrp` への
     忠実実現」であって「tripod の π₁」ではない。
  2. **本ファイルは F₂ の群論的建設のみ**。ℤ/3×ℤ/3 商の {0,1,∞} 外不分岐実被覆デッキ
     としての実現（`TripodKummerMu3`＝BLW-2 の実 Kummer 被覆・実現準同型 BLW-4）との
     束ねが値の本体であり、bare F₂ 単独では A9 を動かさない（設計 §2.3・§4）。
  3. **π₁^ét = F̂₂（副有限完備化）・π₁^temp・residual finiteness F₂ ↪ F̂₂ は 0**
     （設計 §2.5・blocked / named future target）。副有限完備化・cofinal 鎖の choice-free
     索引は未整備。
  4. **tripod の座標環（局所化 K[t,1/t,1/(1−t)]）不在**: 「被覆」は環の拡大で語る（BLW-2）。
  5. **Belyi cuspidalization（[AbsTopII]・strictly Belyi type）・noncritical Belyi
     （[GenEll]・IUT IV 高さ制御）は 0 のまま**: blc/blr の正直限定 1–2 を全文継承・並置。
  6. 生成数 2 の自由群に固定（F₂）。位相・解析なし。

  選択公理不使用・sorry 不使用・新規 Classical.choice 不使用（全単射性は明示両側逆
  witness、場合分けは Bool 値関数の構成的 `cases`）。禁止タクティク（simp/decide/
  by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）不使用；
  `omega` 不使用。共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系・report.html）は
  一切変更しない。新規 1 本のみ。目標公理 `[propext, Quot.sound]`。
-/
import IUT.GaloisPi1Iso

namespace IUT

/-! ## 1. 文字・簡約・相殺乗法（Bool 値・Markov 不要） -/

/-- 文字（生成元インデックス × 符号）。`(true,·)`=生成元 a、`(false,·)`=生成元 b、
    符号 `·.2` が向き。 -/
abbrev tfgLtr := Bool × Bool

/-- 逆文字（符号反転）。 -/
def tfgLinv (x : tfgLtr) : tfgLtr := (x.1, !x.2)

/-- 相殺する文字対か（同じ生成元・逆符号）。 -/
def tfgCancels (x y : tfgLtr) : Bool := (x.1 == y.1) && (x.2 == !y.2)

/-- 簡約語判定（隣接する相殺対がない）。Bool 値・`decide` 不要。 -/
def tfgRed : List tfgLtr → Bool
  | [] => true
  | [_] => true
  | x :: y :: r => (!(tfgCancels x y)) && tfgRed (y :: r)

/-- 相殺つき prepend（データ関数）。 -/
def tfgLcons (x : tfgLtr) : List tfgLtr → List tfgLtr
  | [] => [x]
  | y :: r =>
    match tfgCancels x y with
    | true => r
    | false => x :: y :: r

/-- 乗法: u の文字を右から相殺 prepend して v に連結（= 連結してから簡約）。 -/
def tfgRmul (u v : List tfgLtr) : List tfgLtr := List.foldr tfgLcons v u

/-- 逆元（逆順・逆文字）。 -/
def tfgIw (w : List tfgLtr) : List tfgLtr := List.reverse (List.map tfgLinv w)

/-! ## 2. 文字レベルの計算補題 -/

theorem tfg_cancels_symm (x y : tfgLtr) : tfgCancels x y = tfgCancels y x := by
  cases x with
  | mk x1 x2 => cases y with
    | mk y1 y2 => cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> rfl

theorem tfg_cancels_linv_linv (x y : tfgLtr) :
    tfgCancels (tfgLinv x) (tfgLinv y) = tfgCancels x y := by
  cases x with
  | mk x1 x2 => cases y with
    | mk y1 y2 => cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> rfl

theorem tfg_cancels_linv_self (x : tfgLtr) : tfgCancels x (tfgLinv x) = true := by
  cases x with
  | mk x1 x2 => cases x1 <;> cases x2 <;> rfl

theorem tfg_cancels_linv_left (x : tfgLtr) : tfgCancels (tfgLinv x) x = true := by
  cases x with
  | mk x1 x2 => cases x1 <;> cases x2 <;> rfl

theorem tfg_linv_linv (x : tfgLtr) : tfgLinv (tfgLinv x) = x := by
  cases x with
  | mk x1 x2 => cases x1 <;> cases x2 <;> rfl

/-- 相殺したなら第二文字は第一文字の逆文字。 -/
theorem tfg_cancels_eq_linv {x y : tfgLtr} (h : tfgCancels x y = true) : y = tfgLinv x := by
  have h' : ((x.1 == y.1) && (x.2 == !y.2)) = true := h
  have h2 := (Bool.and_eq_true _ _).mp h'
  have e1 : x.1 = y.1 := eq_of_beq h2.1
  have e2 : x.2 = !y.2 := eq_of_beq h2.2
  have f1 : y.1 = x.1 := e1.symm
  have f2 : y.2 = (!x.2) := by
    have hh : (!x.2) = (!(!y.2)) := congrArg Bool.not e2
    rw [Bool.not_not] at hh
    exact hh.symm
  calc y = (y.1, y.2) := rfl
    _ = (x.1, !x.2) := by rw [f1, f2]

/-! ## 3. 簡約の保存と核となる相殺補題 -/

/-- 簡約語の tail は簡約語。 -/
theorem tfg_red_tail {y : tfgLtr} {r : List tfgLtr} (hw : tfgRed (y :: r) = true) :
    tfgRed r = true := by
  cases r with
  | nil => rfl
  | cons z r' =>
    have hh : ((!(tfgCancels y z)) && tfgRed (z :: r')) = true := hw
    exact (Bool.and_eq_true _ _).mp hh |>.2

/-- `lcons` は簡約を保存（第二引数の簡約性のみ必要）。 -/
theorem tfg_red_lcons (x : tfgLtr) (w : List tfgLtr) (hw : tfgRed w = true) :
    tfgRed (tfgLcons x w) = true := by
  cases w with
  | nil => rfl
  | cons y r =>
    show tfgRed (match tfgCancels x y with | true => r | false => x :: y :: r) = true
    cases hc : tfgCancels x y with
    | true => exact tfg_red_tail hw
    | false =>
      show tfgRed (x :: y :: r) = true
      have hh : tfgRed (x :: y :: r) = ((!(tfgCancels x y)) && tfgRed (y :: r)) := rfl
      rw [hh, hc]
      exact hw

/-- **核補題（設計付録 A の再検証）**: 簡約語上で `lcons x (lcons (linv x) w) = w`。 -/
theorem tfg_lcons_cancel (x : tfgLtr) (w : List tfgLtr) (hw : tfgRed w = true) :
    tfgLcons x (tfgLcons (tfgLinv x) w) = w := by
  cases w with
  | nil =>
    show tfgLcons x [tfgLinv x] = []
    show (match tfgCancels x (tfgLinv x) with | true => [] | false => x :: [tfgLinv x]) = []
    rw [tfg_cancels_linv_self]
  | cons y r =>
    show tfgLcons x (match tfgCancels (tfgLinv x) y with
                      | true => r | false => (tfgLinv x) :: y :: r) = y :: r
    cases hc : tfgCancels (tfgLinv x) y with
    | true =>
      have hyx : y = tfgLinv (tfgLinv x) := tfg_cancels_eq_linv hc
      rw [tfg_linv_linv] at hyx
      subst hyx
      cases r with
      | nil => rfl
      | cons z r' =>
        have hred : ((!(tfgCancels y z)) && tfgRed (z :: r')) = true := hw
        have hcz : tfgCancels y z = false := by
          cases hh2 : tfgCancels y z with
          | false => rfl
          | true => rw [hh2] at hred; exact Bool.noConfusion hred
        show (match tfgCancels y z with | true => r' | false => y :: z :: r') = y :: z :: r'
        rw [hcz]
    | false =>
      show (match tfgCancels x (tfgLinv x) with
             | true => y :: r | false => x :: (tfgLinv x) :: y :: r) = y :: r
      rw [tfg_cancels_linv_self]

/-- `rmul` は簡約を保存（第二引数の簡約性のみ必要）。 -/
theorem tfg_red_rmul (u v : List tfgLtr) (hv : tfgRed v = true) :
    tfgRed (tfgRmul u v) = true := by
  induction u with
  | nil => exact hv
  | cons x u' ih => exact tfg_red_lcons x (tfgRmul u' v) ih

/-! ## 4. 結合律・単位元・逆元（群公理） -/

/-- crux: `rmul (lcons x w) c = lcons x (rmul w c)`（相殺分岐は核補題で閉じる）。 -/
theorem tfg_rmul_lcons (x : tfgLtr) (w c : List tfgLtr)
    (hw : tfgRed w = true) (hc : tfgRed c = true) :
    tfgRmul (tfgLcons x w) c = tfgLcons x (tfgRmul w c) := by
  cases w with
  | nil => rfl
  | cons y r =>
    show tfgRmul (match tfgCancels x y with | true => r | false => x :: y :: r) c
       = tfgLcons x (tfgRmul (y :: r) c)
    cases hxy : tfgCancels x y with
    | true =>
      have hylx : y = tfgLinv x := tfg_cancels_eq_linv hxy
      show tfgRmul r c = tfgLcons x (tfgRmul (y :: r) c)
      have hrc : tfgRed (tfgRmul r c) = true := tfg_red_rmul r c hc
      show tfgRmul r c = tfgLcons x (tfgLcons y (tfgRmul r c))
      rw [hylx]
      exact (tfg_lcons_cancel x (tfgRmul r c) hrc).symm
    | false =>
      show tfgRmul (x :: y :: r) c = tfgLcons x (tfgRmul (y :: r) c)
      rfl

/-- **結合律**。 -/
theorem tfg_rmul_assoc (a b c : List tfgLtr) (hb : tfgRed b = true) (hc : tfgRed c = true) :
    tfgRmul (tfgRmul a b) c = tfgRmul a (tfgRmul b c) := by
  induction a with
  | nil => rfl
  | cons x a' ih =>
    show tfgRmul (tfgLcons x (tfgRmul a' b)) c = tfgLcons x (tfgRmul a' (tfgRmul b c))
    have hrab : tfgRed (tfgRmul a' b) = true := tfg_red_rmul a' b hb
    rw [tfg_rmul_lcons x (tfgRmul a' b) c hrab hc, ih]

/-- 左単位元（定義的）。 -/
theorem tfg_nil_rmul (v : List tfgLtr) : tfgRmul [] v = v := rfl

/-- **左逆元**: `rmul (inv w) w = []`。 -/
theorem tfg_rmul_iw_self (w : List tfgLtr) : tfgRmul (tfgIw w) w = [] := by
  induction w with
  | nil => rfl
  | cons x r ih =>
    show tfgRmul (List.reverse (List.map tfgLinv (x :: r))) (x :: r) = []
    rw [List.map_cons, List.reverse_cons]
    show List.foldr tfgLcons (x :: r) (List.reverse (List.map tfgLinv r) ++ [tfgLinv x]) = []
    rw [List.foldr_append]
    show List.foldr tfgLcons (tfgLcons (tfgLinv x) (x :: r)) (List.reverse (List.map tfgLinv r)) = []
    have hcx : tfgLcons (tfgLinv x) (x :: r) = r := by
      show (match tfgCancels (tfgLinv x) x with | true => r | false => (tfgLinv x) :: x :: r) = r
      rw [tfg_cancels_linv_left]
    rw [hcx]
    exact ih

/-! ## 5. 逆元が簡約語であること（担体 Subtype 用） -/

/-- 末尾の相殺判定（`redEnd L v` = L の最終文字と v が相殺しないか）。 -/
def tfgRedEnd : List tfgLtr → tfgLtr → Bool
  | [], _ => true
  | x :: [], v => !(tfgCancels x v)
  | _ :: y :: r, v => tfgRedEnd (y :: r) v

theorem tfg_redEnd_snoc : ∀ (B : List tfgLtr) (u v : tfgLtr),
    tfgRedEnd (B ++ [u]) v = (!(tfgCancels u v))
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: y :: r, u, v => tfg_redEnd_snoc (y :: r) u v

theorem tfg_red_snoc : ∀ (L : List tfgLtr) (v : tfgLtr),
    tfgRed (L ++ [v]) = (tfgRed L && tfgRedEnd L v)
  | [], _ => rfl
  | [x], v => by
    show ((!(tfgCancels x v)) && true) = (true && (!(tfgCancels x v)))
    cases h : tfgCancels x v <;> rfl
  | x :: y :: r, v => by
    show tfgRed (x :: ((y :: r) ++ [v]))
       = ((!(tfgCancels x y) && tfgRed (y :: r)) && tfgRedEnd (y :: r) v)
    have ih := tfg_red_snoc (y :: r) v
    show ((!(tfgCancels x y)) && tfgRed ((y :: r) ++ [v]))
       = ((!(tfgCancels x y) && tfgRed (y :: r)) && tfgRedEnd (y :: r) v)
    rw [ih]
    generalize (!(tfgCancels x y)) = A
    generalize tfgRed (y :: r) = B
    generalize tfgRedEnd (y :: r) v = C
    cases A <;> cases B <;> cases C <;> rfl

/-- 逆元は簡約語。 -/
theorem tfg_red_iw : ∀ (w : List tfgLtr), tfgRed w = true → tfgRed (tfgIw w) = true
  | [], _ => rfl
  | x :: r, hw => by
    have hr : tfgRed r = true := tfg_red_tail hw
    have ih : tfgRed (tfgIw r) = true := tfg_red_iw r hr
    have h1 : tfgRed (List.reverse (List.map tfgLinv r)) = true := ih
    show tfgRed (List.reverse (List.map tfgLinv (x :: r))) = true
    rw [List.map_cons, List.reverse_cons, tfg_red_snoc, h1]
    show tfgRedEnd (List.reverse (List.map tfgLinv r)) (tfgLinv x) = true
    cases r with
    | nil => rfl
    | cons y r' =>
      rw [List.map_cons, List.reverse_cons, tfg_redEnd_snoc, tfg_cancels_linv_linv]
      have hw' : ((!(tfgCancels x y)) && tfgRed (y :: r')) = true := hw
      have hxy : (!(tfgCancels x y)) = true := (Bool.and_eq_true _ _).mp hw' |>.1
      rw [tfg_cancels_symm]
      exact hxy

/-! ## 6. F₂ の実 Grp -/

/-- 担体: 簡約語の Subtype。 -/
def tfgCarrier := {w : List tfgLtr // tfgRed w = true}

/-- **自由群 F₂ の実 Grp**（結合律・左単位元・左逆元を完全証明）。 -/
def tfgGrp : Grp where
  carrier := tfgCarrier
  mul a b := ⟨tfgRmul a.val b.val, tfg_red_rmul a.val b.val b.property⟩
  one := ⟨[], rfl⟩
  inv a := ⟨tfgIw a.val, tfg_red_iw a.val a.property⟩
  mul_assoc a b c := Subtype.ext (tfg_rmul_assoc a.val b.val c.val b.property c.property)
  one_mul a := Subtype.ext rfl
  inv_mul a := Subtype.ext (tfg_rmul_iw_self a.val)

/-! ## 7. 忠実実現: 左正則表現 F₂ ↪ Sym(F₂)（`galPi1SymGrp`） -/

/-- w による左移動（全単射・逆は inv w による左移動）。 -/
def tfgRegPerm (w : tfgCarrier) : galPi1Perm tfgCarrier where
  toFun v := tfgGrp.mul w v
  invFun v := tfgGrp.mul (tfgGrp.inv w) v
  left_inv v := by rw [← tfgGrp.mul_assoc, tfgGrp.inv_mul, tfgGrp.one_mul]
  right_inv v := by rw [← tfgGrp.mul_assoc, tfgGrp.mul_inv, tfgGrp.one_mul]

/-- **左正則表現 F₂ → Sym(F₂)**（本物の対称群 `galPi1SymGrp` への準同型）。
    map_mul は F₂ の結合律から、逆写像成分は `Grp.inv_mul_rev` から降りる。 -/
def tfgRegHom : Hom tfgGrp (galPi1SymGrp tfgCarrier) where
  map := tfgRegPerm
  map_mul a b := galPi1Perm.ext
    (funext fun v => tfgGrp.mul_assoc a b v)
    (funext fun v => by
      show tfgGrp.mul (tfgGrp.inv (tfgGrp.mul a b)) v
         = tfgGrp.mul (tfgGrp.inv b) (tfgGrp.mul (tfgGrp.inv a) v)
      rw [tfgGrp.inv_mul_rev, tfgGrp.mul_assoc])

/-- **忠実性（非退化性の本物の witness）**: 左正則表現は単射。
    ⟹ F₂ は collapsing でなく真に自由に `galPi1SymGrp` の中で実現される。 -/
theorem tfg_reg_injective (a b : tfgCarrier) (h : tfgRegHom.map a = tfgRegHom.map b) : a = b := by
  have h1 : tfgGrp.mul a tfgGrp.one = tfgGrp.mul b tfgGrp.one :=
    congrFun (congrArg galPi1Perm.toFun h) tfgGrp.one
  rw [tfgGrp.mul_one, tfgGrp.mul_one] at h1
  exact h1

/-- `Hom.Injective` 形。 -/
theorem tfg_regHom_injective : tfgRegHom.Injective := tfg_reg_injective

/-! ## 8. 生成元・非可換性・distinctness -/

/-- 生成元 a の文字。 -/
def tfgAletter : tfgLtr := (true, true)
/-- 生成元 b の文字。 -/
def tfgBletter : tfgLtr := (false, true)

/-- 生成元 a ∈ F₂。 -/
def tfgA : tfgCarrier := ⟨[tfgAletter], rfl⟩
/-- 生成元 b ∈ F₂。 -/
def tfgB : tfgCarrier := ⟨[tfgBletter], rfl⟩

/-- a ≠ b。 -/
theorem tfg_a_ne_b : tfgA ≠ tfgB := by
  intro h
  have hv : ([tfgAletter] : List tfgLtr) = [tfgBletter] := congrArg Subtype.val h
  rw [List.cons.injEq] at hv
  exact Bool.noConfusion (congrArg Prod.fst hv.1)

/-- **非可換性**: ab ≠ ba（真に非可換な自由群）。 -/
theorem tfg_ab_ne_ba : tfgGrp.mul tfgA tfgB ≠ tfgGrp.mul tfgB tfgA := by
  intro h
  have hv : (tfgGrp.mul tfgA tfgB).val = (tfgGrp.mul tfgB tfgA).val := congrArg Subtype.val h
  have e1 : (tfgGrp.mul tfgA tfgB).val = [tfgAletter, tfgBletter] := rfl
  have e2 : (tfgGrp.mul tfgB tfgA).val = [tfgBletter, tfgAletter] := rfl
  rw [e1, e2, List.cons.injEq] at hv
  exact Bool.noConfusion (congrArg Prod.fst hv.1)

/-- a² ≠ b²。 -/
theorem tfg_asq_ne_bsq : tfgGrp.mul tfgA tfgA ≠ tfgGrp.mul tfgB tfgB := by
  intro h
  have hv : (tfgGrp.mul tfgA tfgA).val = (tfgGrp.mul tfgB tfgB).val := congrArg Subtype.val h
  have e1 : (tfgGrp.mul tfgA tfgA).val = [tfgAletter, tfgAletter] := rfl
  have e2 : (tfgGrp.mul tfgB tfgB).val = [tfgBletter, tfgBletter] := rfl
  rw [e1, e2, List.cons.injEq] at hv
  exact Bool.noConfusion (congrArg Prod.fst hv.1)

/-- a ≠ e（生成元は非自明）。 -/
theorem tfg_a_ne_one : tfgA ≠ tfgGrp.one := by
  intro h
  have hv : ([tfgAletter] : List tfgLtr) = [] := congrArg Subtype.val h
  exact List.cons_ne_nil tfgAletter [] hv

/-! ## 9. 普遍性（BONUS）: F₂ の普遍写像 ∀ G g₁ g₂ ∃! hom -/

/-- 生成元割当（符号込み）。`(true,·)`↦g₁ 系、`(false,·)`↦g₂ 系。 -/
def tfgGenOf (G : Grp) (g1 g2 : G.carrier) (x : tfgLtr) : G.carrier :=
  match x.1, x.2 with
  | true, true => g1
  | true, false => G.inv g1
  | false, true => g2
  | false, false => G.inv g2

theorem tfg_genOf_linv (G : Grp) (g1 g2 : G.carrier) (x : tfgLtr) :
    tfgGenOf G g1 g2 (tfgLinv x) = G.inv (tfgGenOf G g1 g2 x) := by
  cases x with
  | mk x1 x2 => cases x1 <;> cases x2 <;> first | rfl | exact (G.inv_inv _).symm

/-- 語 ↦ 生成元の像の積。 -/
def tfgEvalW (G : Grp) (g1 g2 : G.carrier) : List tfgLtr → G.carrier :=
  List.foldr (fun x acc => G.mul (tfgGenOf G g1 g2 x) acc) G.one

theorem tfg_eval_lcons (G : Grp) (g1 g2 : G.carrier) (x : tfgLtr) (w : List tfgLtr) :
    tfgEvalW G g1 g2 (tfgLcons x w) = G.mul (tfgGenOf G g1 g2 x) (tfgEvalW G g1 g2 w) := by
  cases w with
  | nil => rfl
  | cons y r =>
    show tfgEvalW G g1 g2 (match tfgCancels x y with | true => r | false => x :: y :: r)
       = G.mul (tfgGenOf G g1 g2 x) (tfgEvalW G g1 g2 (y :: r))
    cases hc : tfgCancels x y with
    | true =>
      have hy : y = tfgLinv x := tfg_cancels_eq_linv hc
      show tfgEvalW G g1 g2 r
         = G.mul (tfgGenOf G g1 g2 x) (G.mul (tfgGenOf G g1 g2 y) (tfgEvalW G g1 g2 r))
      rw [hy, tfg_genOf_linv, ← G.mul_assoc, G.mul_inv, G.one_mul]
    | false =>
      show tfgEvalW G g1 g2 (x :: y :: r)
         = G.mul (tfgGenOf G g1 g2 x) (tfgEvalW G g1 g2 (y :: r))
      rfl

theorem tfg_eval_rmul (G : Grp) (g1 g2 : G.carrier) (u v : List tfgLtr) :
    tfgEvalW G g1 g2 (tfgRmul u v)
      = G.mul (tfgEvalW G g1 g2 u) (tfgEvalW G g1 g2 v) := by
  induction u with
  | nil =>
    show tfgEvalW G g1 g2 v = G.mul (tfgEvalW G g1 g2 []) (tfgEvalW G g1 g2 v)
    rw [show tfgEvalW G g1 g2 [] = G.one from rfl, G.one_mul]
  | cons x u' ih =>
    show tfgEvalW G g1 g2 (tfgLcons x (tfgRmul u' v))
       = G.mul (tfgEvalW G g1 g2 (x :: u')) (tfgEvalW G g1 g2 v)
    have e : tfgEvalW G g1 g2 (x :: u')
        = G.mul (tfgGenOf G g1 g2 x) (tfgEvalW G g1 g2 u') := rfl
    rw [tfg_eval_lcons, ih, e, ← G.mul_assoc]

/-- **普遍写像 F₂ → G**（生成元 a↦g₁, b↦g₂）。 -/
def tfgLift (G : Grp) (g1 g2 : G.carrier) : Hom tfgGrp G where
  map w := tfgEvalW G g1 g2 w.val
  map_mul a b := tfg_eval_rmul G g1 g2 a.val b.val

theorem tfg_lift_a (G : Grp) (g1 g2 : G.carrier) : (tfgLift G g1 g2).map tfgA = g1 := by
  show G.mul g1 G.one = g1
  exact G.mul_one g1

theorem tfg_lift_b (G : Grp) (g1 g2 : G.carrier) : (tfgLift G g1 g2).map tfgB = g2 := by
  show G.mul g2 G.one = g2
  exact G.mul_one g2

/-! ### 一意性 -/

/-- 単一文字 `[x]` を担体に。 -/
def tfgSingle (x : tfgLtr) : tfgCarrier := ⟨[x], rfl⟩

/-- 簡約語の先頭を分離: `⟨x::r⟩ = ⟨[x]⟩ · ⟨r⟩`。 -/
theorem tfg_rmul_single (x : tfgLtr) (r : List tfgLtr) (h : tfgRed (x :: r) = true) :
    tfgRmul [x] r = x :: r := by
  cases r with
  | nil => rfl
  | cons y r' =>
    show tfgLcons x (y :: r') = x :: y :: r'
    have h' : ((!(tfgCancels x y)) && tfgRed (y :: r')) = true := h
    have hxy : tfgCancels x y = false := by
      have := (Bool.and_eq_true _ _).mp h' |>.1
      cases hh : tfgCancels x y with
      | false => rfl
      | true => rw [hh] at this; exact Bool.noConfusion this
    show (match tfgCancels x y with | true => r' | false => x :: y :: r') = x :: y :: r'
    rw [hxy]

/-- 任意の準同型 h が生成文字上で `genOf` に一致するなら、全語で `evalW` に一致。 -/
theorem tfg_hom_eval (G : Grp) (g1 g2 : G.carrier) (h : Hom tfgGrp G)
    (hs : ∀ x : tfgLtr, h.map (tfgSingle x) = tfgGenOf G g1 g2 x) :
    ∀ (w : List tfgLtr) (hw : tfgRed w = true),
      h.map ⟨w, hw⟩ = tfgEvalW G g1 g2 w
  | [], _ => by
      show h.map tfgGrp.one = G.one
      exact h.map_one
  | x :: r, hw => by
      have hr : tfgRed r = true := tfg_red_tail hw
      have key : (⟨x :: r, hw⟩ : tfgCarrier) = tfgGrp.mul (tfgSingle x) ⟨r, hr⟩ :=
        Subtype.ext (tfg_rmul_single x r hw).symm
      have ih : h.map ⟨r, hr⟩ = tfgEvalW G g1 g2 r := tfg_hom_eval G g1 g2 h hs r hr
      have e : tfgEvalW G g1 g2 (x :: r)
          = G.mul (tfgGenOf G g1 g2 x) (tfgEvalW G g1 g2 r) := rfl
      rw [key, h.map_mul, hs x, ih, e]

/-- **一意性**: 生成元 a↦g₁, b↦g₂ を満たす準同型は `tfgLift` に一致。
    ⟹ F₂ の普遍性 ∀ G g₁ g₂ ∃! hom（存在 = tfgLift, 一意 = 本定理）が閉じる。 -/
theorem tfg_lift_unique (G : Grp) (g1 g2 : G.carrier) (h : Hom tfgGrp G)
    (ha : h.map tfgA = g1) (hb : h.map tfgB = g2)
    (w : tfgCarrier) : h.map w = (tfgLift G g1 g2).map w := by
  have hs : ∀ x : tfgLtr, h.map (tfgSingle x) = tfgGenOf G g1 g2 x := by
    intro x
    cases x with
    | mk x1 x2 =>
      cases x1 <;> cases x2
      · -- (false,false) : [x] = inv b
        show h.map (tfgSingle (false, false)) = G.inv g2
        have e : tfgSingle (false, false) = tfgGrp.inv tfgB := Subtype.ext rfl
        rw [e, h.map_inv, hb]
      · -- (false,true) : b
        show h.map (tfgSingle (false, true)) = g2
        have e : tfgSingle (false, true) = tfgB := Subtype.ext rfl
        rw [e, hb]
      · -- (true,false) : inv a
        show h.map (tfgSingle (true, false)) = G.inv g1
        have e : tfgSingle (true, false) = tfgGrp.inv tfgA := Subtype.ext rfl
        rw [e, h.map_inv, ha]
      · -- (true,true) : a
        show h.map (tfgSingle (true, true)) = g1
        have e : tfgSingle (true, true) = tfgA := Subtype.ext rfl
        rw [e, ha]
  have hthis := tfg_hom_eval G g1 g2 h hs w.val w.property
  show h.map w = tfgEvalW G g1 g2 w.val
  exact hthis

end IUT
