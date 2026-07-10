# A3 M4 詳細化 — 指標同型 Gal(ℚ(ζ_{3ⁿ})/ℚ) ≅ (ℤ/3ⁿ)^×・逆極限 ℤ₃^×・射影全射性（A3 0.7 → 0.75 級）

日付: 2026-07-10（ファイル名は起票ラウンド 2026-07-09 の継続）／ 種別: **設計ドキュメントのみ**
（実装コード無し・共有ファイル不更新）
分類: **[実／本物建設(b) の設計]** — `audit/A3-inverse-limit-roadmap-2026-07-09.md` §4.3（M4 の
薄いスケッチ 9 行）を opus 実装枠に渡せる粒度へ段階分解する詳細化ラウンド。
台帳確認: `target_ledger.json` A3 = { weight 12, status **0.7** }（本日実測・
`reaudit-A3-ctl-2026-07-09.md` で監査確定済み）。柱 A の Σ(w·s) = **39.2**/100 → complete_pct 39。
**complete_pct 影響: 本ドキュメント自体は 0（設計のみ）**。実装マイルストーンの保守的予測は
§5（最終判定は独立監査）。

前段からの**差分**（本ドキュメントの存在理由）: M3（ctl・逆極限 profinite Gal(ℚ(ζ_{3^∞})/ℚ)）は
**完成・監査確定**した（A3 0.65→0.7）。監査 `reaudit-A3-ctl` が 0.7 上限の理由として名指しした
残欠は正確に 2 つ——**(ii) 射影の全射性（整合族の持ち上げ）未証明＝極限の非退化未形式化**、
**(iii) レベル同型 Gal(L_n/ℚ)≅(ℤ/3^{n+1})^× と極限同型 ≅ℤ₃^× 未達**。本ドキュメントは
この 2 つを M4a（レベル同型）・M4b（逆系＋極限同型）・M4c（射影全射性）に分解し、
各に新規ファイル・prefix・主要シグネチャ・依存・禁止タクティク回避・tier を与える。

**本設計の中心的発見（§4 で詳述）**: M4c（射影全射性）は **choice-free に閉じられる**。
一般の有限群逆系の Mittag-Leffler 論法は「各段の原像を整合的に選ぶ」無限回の選択
（従属選択）を要するが、本塔は**指標で明示的に分裂している**——`ctmFind`（データ）・
`zpuInv`（本設計で新設する mod 3^ℓ 逆元**関数**）・`csaAut`（データ）だけで、
「同一整数指数 a を全レベルで使う」正準切断が**関数として**書ける。∃ からの witness
取り出しは一切不要。よってロードマップ §4.3 が仮置きした「choice を要するなら M4a+M4b
止まり」の分岐は**不要**と設計判断する（fallback は §4.4 に保存）。

---

## 0. 既存資産の再監査（本日 read 済み・シグネチャ実在確認）

| 資産 | 実在シグネチャ（ファイル:行・本日確認） | M4 での役割 |
|---|---|---|
| 群・準同型 | `Grp`（`FundamentalGroup.lean:74`・carrier/mul/one/inv＋左公理）・`Hom G H`（:125・map/map_mul）・`Hom.comp`（:146）・`Hom.map_one/map_inv/map_pow`。**`GrpIso` は存在しない**（grep 全域 0 件） | 同型は `MuUnitsIsoData`（`MuUnits.lean:454`）型の**レコード（to/from/left_inv/right_inv）**で表す——確立イディオム。汎用 GrpIso の新設はしない（共有インフラ改変は本ラウンドの範囲外） |
| 逆系・極限 | `InverseSystem`（`Profinite.lean:150`・Idx 任意型）・`Compatible`（:163）・`limitGrp`（:167・担体 = 整合族 subtype）・`limitProj`（:195）・`limit_universal`（:209・**実在**・∃ 形） | M4b の受け皿。**媒介射は ∃ 取り出しを避け limit_universal の証明体と同型の直接定義で書く**（§3.2） |
| Nat 逆系構成子 | `natSystem (G : Nat → Grp) (P : ∀ {i j}, i ≤ j → Hom (G j) (G i)) (hself) (hcomp) : InverseSystem`（`ProObject.lean:72`・@[reducible]） | (ℤ/3^{n+1})^× 逆系の組み立て（§3.1） |
| M3 完成塔 | `ctlExt n := cteExt (n+1) (by omega)`・`ctlGal n := galoisGroupGrp (ctlExt n)`・`ctlStep n := ctrResHom (n+1)`・`ctlRestrAux/ctlRestrD/ctlRestr`・`ctl_restr_self/step/comp`・`ctlTower`・`ctlProfinite := profPi1Limit ctlTower`（`CyclotomicTowerLimit.lean:60–202`） | M4b の左辺・M4c の主語。射影は `profPi1_proj ctlTower n : Hom ctlProfinite (ctlGal n)`（`ProfinitePi1.lean:127`） |
| 指標（ℓ 一般） | `ctr_charG ℓ hℓ σ := ctmFind ℓ hℓ (σ.toFun (ctmZeta ℓ hℓ))`（`CyclotomicResTower.lean:467`）・`ctr_charG_spec`（σζ=ζ^a・:471）・`ctr_charG_lt`（a<3^ℓ・:476）・`ctr_charG_nd3`（3∤a・:494）・`ctr_sigma_powG`（σ(ζ^k)=ζ^{ak}・:481）・`ctr_sigma_injG`（:487） | M4a の写像本体。**指標は既に choice-free なデータ**（fuel 走査 `ctmFindGo`・`CyclotomicMuTower.lean:611`） |
| 段間指標 | `ctrChar n hn σ := ctmFind (n+1) _ (σ.toFun (ctmZeta (n+1) _))`（:127）＝ **`ctr_charG (n+1)` と定義一致**（proof-irrelevance で defeq・橋は rfl 級） | §3.2 の compat 補題 |
| σ_a | `csaAut n hn a a' (ha : ¬3∣a) (ha' : ¬3∣a') (haa' : a*a' % 3^n = 1) : FieldAut (cteField n hn)`（`CyclotomicSubAut.lean:459`・**逆元 a' は明示データ引数**）・`csaAut_mem`（:471）・`csaAut_zeta`（σ_a ζ = ζ^a・:477） | M4a 全射方向の原像。**a' をデータで供給する関数が必要**（§1 の zpuInv） |
| 冪の一意性 | `ctm_pow_mod`（ζ^k=ζ^{k%3ⁿ}・`CyclotomicSubAut.lean:99`）・`ctm_powers_distinct`（`CyclotomicMuTower.lean:266`）・`ctm_order`（:235）・`ctr_index_one`（ζ^k=ζ¹⟹k%3^{n+1}=1・`CyclotomicResTower.lean:185`＝一般化の写経元） | 指標の積公式（§2.2） |
| 逆元の存在 | `ctr_inv_exists : ∀ m a, ¬3∣a → ∃ b, ¬3∣b ∧ a*b % 3^(m+1) = 1`（`CyclotomicResTower.lean:525`・Hensel 帰納・choice-free だが **∃ 形**）・`ctr_tex`（:517・t の明示式 `(3−q%3)%3` / `q%3`） | §1 で**関数へ脱存在化**（zpuInv）。証明スクリプトは再利用 |
| res・全射性 | `ctrRes`（:260）・`ctrResHom`（:436）・`ctr_res_haa`（:241）・`ctr_surjective`（:585・有限段） | M4c は**これの極限版**。有限段証明の構造（指標持ち上げ）が §4 の写経元 |
| 決定補題 | `cae_aut_ext n hn σ τ (hσ hτ : mem) (h : σζ=τζ) : σ = τ`（`CyclotomicAutExt.lean:221`） | M4a 単射方向・全域で使う「元は指標で決まる」 |
| Gal の積の向き | `fieldAutGroup.mul σ τ = fieldAutComp σ τ`＝**先に τ 次に σ**（toFun = σ.toFun∘τ.toFun・`FieldAutGroup.lean:113,165`）。`galoisGroupGrp E := subgroupGrp (galoisSubgroup E)`（:209・担体は mem の subtype） | 積公式の向き: (σ·τ)(ζ) = σ(ζ^{char τ}) = ζ^{char σ · char τ}（§2.2） |
| 既存 (ℤ/p)^× | `zmodUnits (p) (hp : IsPrime p) : Grp`（`MuUnits.lean:391`・**素数 p 限定**・担体 Quot・逆元 Fermat c^{p−2}）・`zmodSystem`（`LocalReciprocity.lean` 使用・**加法** ẑ 系） | **再利用不可**（3ⁿ は素数でない・Fermat 逆元は φ(3ⁿ) 一般に届かない・Quot 担体上の逆元関数化には Euler 定理が要る）。名前衝突回避のため新設は別名 `zpuGrp`（§1.1 で設計比較） |

依存 DAG（本設計の 5 新規ファイル）:

```
zpu (単数群+逆元関数) ──→ cci (レベル同型 M4a) ──→ cli (極限同型 M4b) ──→ cps (射影全射性 M4c)
        └────────────→ zps (逆系+極限+単数側全射性) ──┘
```

---

## 1. 問い 1: (ℤ/3^ℓ)^× の群構成 — `IUT/Zmod3PowUnits.lean`（prefix `zpu`・依存: なし〔Nat 算術のみ〕）

### 1.1 設計判断（担体と逆元の供給）

**候補比較**（結論: (A) を採る）:

| 案 | 担体 | 逆元 | 判定 |
|---|---|---|---|
| **(A) Nat subtype（採用）** | `{ a : Nat // a < 3^ℓ ∧ ¬ 3 ∣ a }` | Hensel 逆元**関数** `zpuInv`（`ctr_inv_exists` の脱存在化） | ○ 指標側（`ctmFind`/`ctr_charG`）が Nat を返すので**橋が恒等的**。choice-free 逆元は既存 Hensel 証明の写経。遷移射が単発 `% 3^{i+1}` で書け cast 簿記ゼロ（§3.1） |
| (B) Quot 担体（`zmodUnits` 写経） | `zmod (3^ℓ)` の単数 subtype | Quot 上の関数化には冪 `c^{φ(3^ℓ)−1}`＝**Euler 定理が新規に必要**（Lagrange 級の位数理論・高価） | × 素数版 Fermat（p−2 乗）は 3ⁿ に届かない。指標側との橋にも代表元取り出しが挟まる |
| (C) 既存 `zmodUnits` 流用 | — | — | × 素数 p 限定（`IsPrime p`・p^1 固定）。**名前衝突注意: `zmodUnits` は取られている**ので新設名は `zpuGrp` |
| (D) `zmodSystem` 流用 | — | — | × 加法群 ẑ の系であり乗法単数群ではない（ロードマップ §4.3 の指摘どおり別物） |

### 1.2 Lean スケッチ

```lean
/- ZPU-0: 冪の整除・正値の小補題（omega は 3^n を扱えない・本ファイルに集約） -/
theorem zpu_pow_pos (k : Nat) : 1 ≤ (3:Nat) ^ k          -- cte_pow3_pos の再輸出 or 再証明
theorem zpu_pow_dvd {i j : Nat} (h : i ≤ j) : (3:Nat) ^ i ∣ 3 ^ j
-- 差分 d := j−i の帰納（3^{i+d+1} = 3^{i+d}·3）。§3 の t_comp・M4c の整合族が多用

/- ZPU-1: Hensel 逆元の関数化（ctr_inv_exists の脱存在化・★本ファイルの中核） -/
def zpuInv : Nat → Nat → Nat
  | 0,     a => a % 3                      -- 基底: mod 3 では a·a ≡ 1（a≡1,2 とも）
  | m + 1, a =>
      let b := zpuInv m a
      let q := a * b / 3 ^ (m + 1)
      let t := if a % 3 = 1 then (3 - q % 3) % 3 else q % 3   -- ctr_tex の witness を式化
      b + t * 3 ^ (m + 1)
-- ★if は Nat の decEq 上の項レベル ite（タクティク by_cases ではない・許容）。
--   spec 証明では `cases Nat.decEq (a % 3) 1 with` で分岐（既存イディオム）。

theorem zpuInv_spec : ∀ m a, ¬ 3 ∣ a →
    ¬ 3 ∣ zpuInv m a ∧ a * zpuInv m a % 3 ^ (m + 1) = 1
-- 証明は ctr_inv_exists（CyclotomicResTower.lean:525–576）の帰納をそのまま写経し、
-- 「obtain ⟨b,…⟩ := ih」を「b := zpuInv m a・ih の spec」に置換するだけ。
-- t が ctr_tex の witness 式と一致するので (q + a*t) % 3 = 0 も同計算（omega）。

theorem zpuInv_lt : ∀ m a, zpuInv m a < 3 ^ (m + 1)
-- 基底 a%3 < 3。段: b < 3^{m+1}・t ≤ 2 ⟹ b + t·3^{m+1} < 3·3^{m+1} = 3^{m+2}。

/- ZPU-2: レベル ℓ ラッパ（ℓ ≥ 1・m := ℓ−1 の添字合わせをここで一元化） -/
def zpuInvL (ℓ : Nat) (a : Nat) : Nat := zpuInv (ℓ - 1) a
theorem zpuInvL_nd3 (ℓ) (hℓ : 1 ≤ ℓ) (a) (ha : ¬3∣a) : ¬ 3 ∣ zpuInvL ℓ a
theorem zpuInvL_one (ℓ) (hℓ : 1 ≤ ℓ) (a) (ha : ¬3∣a) : a * zpuInvL ℓ a % 3 ^ ℓ = 1
-- ℓ = (ℓ−1)+1 の書き換え 1 回（Nat.succ_pred_eq_of_pos 級・omega 不可の pow は触らない）

/- ZPU-3: 群 (ℤ/3^ℓ)^×（既存 zmodUnits と別名・素数冪版） -/
def zpuGrp (ℓ : Nat) (hℓ : 1 ≤ ℓ) : Grp where
  carrier := { a : Nat // a < 3 ^ ℓ ∧ ¬ 3 ∣ a }
  mul := fun a b => ⟨a.val * b.val % 3 ^ ℓ, Nat.mod_lt _ (zpu_pow_pos ℓ …), zpu_mul_nd3 …⟩
  one := ⟨1, zpu_one_lt ℓ hℓ, by intro ⟨k,hk⟩; omega⟩
  inv := fun a => ⟨zpuInvL ℓ a.val % 3 ^ ℓ, Nat.mod_lt …, zpu_mod_nd3 …⟩
  mul_assoc := …   -- Nat.mul_mod で両辺を a*b*c % 3^ℓ に正規化（rw 直線・ring 不使用）
  one_mul := …     -- 1*a = a・Nat.mod_eq_of_lt a.property.1
  inv_mul := …     -- Nat.mul_mod + zpuInvL_one + Nat.mul_comm（Subtype.ext）
-- 部品補題: zpu_mul_nd3（3∤a・3∤b ⟹ 3∤(a*b % 3^ℓ)）は ctr_mod_not_dvd3
-- （CyclotomicResTower.lean:218）と同型の mod-mod 論法＋「3∤a,3∤b⟹3∤ab」
-- （a%3,b%3 ∈{1,2} の 4 分岐 omega・euclid 不要の初等形）。

theorem zpuGrp_comm (ℓ hℓ) (a b) : (zpuGrp ℓ hℓ).mul a b = (zpuGrp ℓ hℓ).mul b a
-- Subtype.ext + Nat.mul_comm
```

**禁止タクティク回避**: 分岐は全て `cases Nat.decEq … with` / 項レベル ite・
算術は `Nat.mul_mod`/`Nat.mod_mod_of_dvd`/`Nat.mod_eq_of_lt`/omega（線形部のみ）・
3^ℓ の非線形は ZPU-0 の小補題経由。simp/decide/by_cases/ring 不使用で全て書ける
（既存 ctr/ctm が同じ材料で書けている実証あり）。

工数: **300–450 行**。tier **M（opus）**（zpuInv_spec の写経が主・新イディオム無し）。
complete_pct 単体寄与: 無し（M4a/b/c の必要部品・ヘッダに明記）。

---

## 2. 問い 2: レベル指標同型 Gal(ℚ(ζ_{3^ℓ})/ℚ) ≅ (ℤ/3^ℓ)^× — `IUT/CyclotomicCharIso.lean`（prefix `cci`・依存: zpu・ctr・csa・cae・ctm）

### 2.1 一般化指標一意性（ctr_index_one の ℓ・一般ターゲット版・新規補題）

```lean
-- CCI-1: ζ_ℓ^k = ζ_ℓ^a・a < 3^ℓ ⟹ k % 3^ℓ = a
theorem cci_indexG (ℓ : Nat) (hℓ : 1 ≤ ℓ) (k a : Nat) (halt : a < 3 ^ ℓ)
    (h : ctmPow ℓ hℓ k = ctmPow ℓ hℓ a) : k % 3 ^ ℓ = a
-- ctm_pow_mod で左辺を k%3^ℓ に・cases Nat.decEq (k%3^ℓ) a with・
-- isFalse 枝は ctm_powers_distinct（両者 < 3^ℓ）で absurd。
-- ctr_index_one（:185・n+1 段・a=1 固定）の忠実な一般化＝写経元あり。
```

### 2.2 指標の積公式（★M4a の新規数学・ロードマップ §4.3 が名指しした欠落）

```lean
-- CCI-2: char(σ·τ) = char σ · char τ mod 3^ℓ
-- Gal の積は fieldAutComp（先に τ 次に σ・§0 の表確認済み）:
--   (σ·τ)(ζ) = σ(τ ζ) = σ(ζ^{b})           （ctr_charG_spec τ）
--            = ζ^{a·b}                      （ctr_sigma_powG σ b）
--   一方 (σ·τ)(ζ) = ζ^{char(σ·τ)}           （ctr_charG_spec (σ·τ)）
--   char(σ·τ) < 3^ℓ（ctr_charG_lt）⟹ cci_indexG の対称使用で確定
theorem cci_charG_mul (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ τ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) :
    ctr_charG ℓ hℓ ((galoisGroupGrp (cteExt ℓ hℓ)).mul σ τ).val
      = ctr_charG ℓ hℓ σ.val * ctr_charG ℓ hℓ τ.val % 3 ^ ℓ
-- 注意: subgroupGrp の mul の val が fieldAutComp σ.val τ.val に defeq であること
-- （subgroupGrp の定義確認は実装冒頭で show により固定）。
```

### 2.3 双方向 Hom と同型レコード

```lean
-- CCI-3: 指標方向 χ_ℓ
def cciToUnits (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    Hom (galoisGroupGrp (cteExt ℓ hℓ)) (zpuGrp ℓ hℓ) where
  map := fun σ => ⟨ctr_charG ℓ hℓ σ.val, ctr_charG_lt ℓ hℓ σ.val, ctr_charG_nd3 ℓ hℓ σ.val⟩
  map_mul := fun σ τ => Subtype.ext (cci_charG_mul ℓ hℓ σ τ)

-- CCI-4: σ_a 方向（逆元 witness は zpuInvL がデータで供給・choice-free）
def cciAut (ℓ hℓ) (a : (zpuGrp ℓ hℓ).carrier) : FieldAut (cteField ℓ hℓ) :=
  csaAut ℓ hℓ a.val (zpuInvL ℓ a.val) a.property.2
    (zpuInvL_nd3 ℓ hℓ a.val a.property.2) (zpuInvL_one ℓ hℓ a.val a.property.2)
def cciFromUnits (ℓ hℓ) : Hom (zpuGrp ℓ hℓ) (galoisGroupGrp (cteExt ℓ hℓ)) where
  map := fun a => ⟨cciAut ℓ hℓ a, csaAut_mem …⟩
  map_mul := …
-- map_mul は cae_aut_ext の生成元一点比較:
--   σ_{ab%3^ℓ}(ζ) = ζ^{ab%3^ℓ} = ζ^{ab}（ctm_pow_mod）
--   (σ_a·σ_b)(ζ) = σ_a(ζ^b) = ζ^{ab}（csaAut_zeta + ctr_sigma_powG or csa_subst_pow）
--   両者 mem（csaAut_mem・mul_mem）⟹ cae_aut_ext ⟹ Subtype.ext

-- CCI-5: 左右逆（各 1 本・どちらも一点比較）
theorem cci_left_inv (ℓ hℓ) (σ) : (cciFromUnits ℓ hℓ).map ((cciToUnits ℓ hℓ).map σ) = σ
-- cae_aut_ext: σ_{char σ}(ζ) = ζ^{char σ} = σ(ζ)（csaAut_zeta vs ctr_charG_spec）
theorem cci_right_inv (ℓ hℓ) (a) : (cciToUnits ℓ hℓ).map ((cciFromUnits ℓ hℓ).map a) = a
-- charG(σ_a) = a: csaAut_zeta + ctr_charG_spec + cci_indexG + Nat.mod_eq_of_lt a.property.1
-- （この向きは §3.2 compat・§4 でも独立に使うので補題 cci_charG_csaAut として単離）
theorem cci_charG_csaAut (ℓ hℓ) (a : (zpuGrp ℓ hℓ).carrier) :
    ctr_charG ℓ hℓ (cciAut ℓ hℓ a) = a.val

-- CCI-6: 同型レコード（GrpIso は存在しないので MuUnitsIsoData:454 の確立イディオム）
structure CciIsoData (ℓ : Nat) (hℓ : 1 ≤ ℓ) where
  toUnits  : Hom (galoisGroupGrp (cteExt ℓ hℓ)) (zpuGrp ℓ hℓ)
  fromUnits : Hom (zpuGrp ℓ hℓ) (galoisGroupGrp (cteExt ℓ hℓ))
  left_inv : ∀ σ, fromUnits.map (toUnits.map σ) = σ
  right_inv : ∀ a, toUnits.map (fromUnits.map a) = a
def cciIsoData (ℓ hℓ) : CciIsoData ℓ hℓ    -- 全フィールド既証明の純レコード

-- CCI-7（無償の系・正直な副産物）: Gal(ℚ(ζ_{3^ℓ})/ℚ) はアーベル
theorem cci_gal_comm (ℓ hℓ) (σ τ) : mul σ τ = mul τ σ
-- cae_aut_ext + 一点比較 ζ^{ab} = ζ^{ba}（Nat.mul_comm）。Kronecker–Weber 円分切片の
-- 可換性が本物に出る（M4a の非空虚性の見せ所・監査向け）
```

工数: **350–500 行**。tier **M（opus）**。詰まりどころは subgroupGrp/mul の defeq 展開
（show で固定すれば直線）と cci_charG_mul の書き換え順のみ——fable 不要と判断。

---

## 3. 問い 3: (ℤ/3^{n+1})^× の逆系と極限同型 ctlProfinite ≅ lim (ℤ/3^{n+1})^×

### 3.1 逆系＋単数側極限 — `IUT/Zmod3PowUnitsSystem.lean`（prefix `zps`・依存: zpu のみ）

**設計の要点**: ctl の遷移射は反復合成（cast 簿記が最大の泥だった）が、単数側の遷移射は
**単発の `% 3^{i+1}`** で i ≤ j 一般に直接書ける——**反復も cast も一切不要**。
これが Gal 側でなく単数側で極限を先に組む最大の理由。

```lean
-- ZPS-1: 添字整合（ctlGal n = Gal(cteExt (n+1)) に合わせ U n := (ℤ/3^{n+1})^×）
def zpsG (n : Nat) : Grp := zpuGrp (n + 1) (by omega)

-- ZPS-2: 遷移射（i ≤ j 一般を単発 mod で・反復不使用）
def zpsT {i j : Nat} (h : i ≤ j) : Hom (zpsG j) (zpsG i) where
  map := fun a => ⟨a.val % 3 ^ (i + 1), Nat.mod_lt _ …, zpu 側の nd3-mod 補題⟩
  map_mul := …
-- map_mul: ((a*b) % 3^{j+1}) % 3^{i+1} = ((a%3^{i+1})*(b%3^{i+1})) % 3^{i+1}
--   Nat.mod_mod_of_dvd（zpu_pow_dvd (i+1 ≤ j+1)）で左辺 = (a*b) % 3^{i+1}、
--   Nat.mul_mod で右辺同値。Subtype.ext。
theorem zpsT_self (i) (x) : (zpsT (Nat.le_refl i)).map x = x       -- Nat.mod_eq_of_lt
theorem zpsT_comp (hij hjk) (x) : …                                 -- Nat.mod_mod_of_dvd
def zpsSystem : InverseSystem := natSystem zpsG (fun h => zpsT h) zpsT_self zpsT_comp
def zpsLimit : Grp := limitGrp zpsSystem     -- ＝ ℤ₃^×（逆極限としての定義そのもの）

-- ZPS-3: ★単数側の射影全射性（M4c の核・純 Nat 算術で先取り）
theorem zps_proj_surjective (n : Nat) :
    ∀ a : (zpsG n).carrier, ∃ u : zpsLimit.carrier, (limitProj zpsSystem n).map u = a
-- witness（データ・choice-free）: u := ⟨fun m => ⟨a.val % 3^{m+1}, …⟩, hcompat⟩
--   hcompat: (a % 3^{j+1}) % 3^{i+1} = a % 3^{i+1}（zps_pow_dvd + mod_mod_of_dvd・一様）
--   射影: u.val n = a % 3^{n+1} = a（Nat.mod_eq_of_lt a.property.1・Subtype.ext）
-- 全射性はここでは ∃ 文だが witness は閉じた式——選択は不要。約 40 行。

-- ZPS-4（安い系）: 非退化 — zpsLimit に単位元以外の元が在る
theorem zps_nontrivial : ∃ u : zpsLimit.carrier, u ≠ zpsLimit.one
-- u := 定数族 a=2（各段 2 < 3^{m+1}・3∤2・compat は 2%3^{i+1}=2）。第 0 成分 2 ≠ 1。
```

工数: **200–300 行**。tier **S–M（sonnet 可・純 Nat 算術）**。

### 3.2 極限同型 — `IUT/CyclotomicLimitIso.lean`（prefix `cli`・依存: cci・zps・ctl）

```lean
-- CLI-0: レベル橋（defeq 確認）
-- ctlGal n := galoisGroupGrp (ctlExt n)・ctlExt n := cteExt (n+1) (by omega)。
-- hn 引数は Prop なので proof-irrelevance で cciToUnits (n+1) _ がそのまま
-- Hom (ctlGal n) (zpsG n) の型に付く（cast 不要・実装冒頭に検算 def を置く）:
def cliChar (n : Nat) : Hom (ctlGal n) (zpsG n) := cciToUnits (n + 1) (by omega)
def cliAut  (n : Nat) : Hom (zpsG n) (ctlGal n) := cciFromUnits (n + 1) (by omega)

-- CLI-1: ★compat 正方形（本ファイル最大の泥・fable スポット予約）
-- 単段: char(ctlStep n σ) = char σ % 3^{n+1}
theorem cli_char_step (n : Nat) (σ : (ctlGal (n+1)).carrier) :
    (cliChar n).map ((ctlStep n).map σ) = (zpsT (Nat.le_succ n)).map ((cliChar (n+1)).map σ)
-- ctlStep n = ctrResHom (n+1)・(ctrRes σ) = csaAut (ctrChar (n+1) _ σ % 3^{n+1}) …
-- ⟹ charG(ctrRes σ) = ctrChar % 3^{n+1}（cci_charG_csaAut・CCI-5）
-- ⟹ ctrChar (n+1) hn σ = ctr_charG (n+2) _ σ は定義一致（§0・rfl 級の橋補題
--    cli_char_bridge を 1 本置く。万一 defeq が通らなければ ctmFind の引数照合 5 行）
-- i ≤ j 一般: ctl_restr_step（CyclotomicTowerLimit.lean:130）で最上段を peel する
-- 差分帰納——ctl_restr_comp_aux（:144）と同じ骨格の写経:
theorem cli_char_restr {i j : Nat} (h : i ≤ j) (σ : (ctlGal j).carrier) :
    (cliChar i).map ((ctlRestr h).map σ) = (zpsT h).map ((cliChar j).map σ)
-- 帰納の各段は cli_char_step + Nat.mod_mod_of_dvd（3^{i+1} ∣ 3^{m+1}）で合流。
-- Gal 側の cast は ctl_restr_step が既に吸収済み——новых subst は入れない方針。

-- CLI-2: 媒介準同型（∃ 取り出し禁止 ⟹ limit_universal は使わず直接定義。
--   limit_universal の証明体（Profinite.lean:217）と同じ構成をその場で書く）
def cliTo : Hom ctlProfinite zpsLimit where
  map := fun s => ⟨fun n => (cliChar n).map (s.val n),
                   fun {i j} h => by rw [← s.property h]; exact (cli_char_restr h _).symm⟩
  map_mul := fun s t => Subtype.ext (funext fun n => (cliChar n).map_mul _ _)
def cliFrom : Hom zpsLimit ctlProfinite where
  map := fun u => ⟨fun n => (cliAut n).map (u.val n), hcompat⟩
  map_mul := …
-- cliFrom の hcompat（逆向き正方形）は CLI-1 を左右逆で書き直すのでなく、
-- 「元は指標で決まる」で還元する:
--   ctlRestr h (cliAut (u j)) は cci_left_inv により cliAut(char(ctlRestr h (cliAut u_j)))、
--   char(…) = char(cliAut u_j) % … = u_j % … = u_i（cli_char_restr + cci_charG_csaAut +
--   u.property h）⟹ = cliAut u_i。左右の正方形を 1 本の補題で共有し二重証明を避ける。

-- CLI-3: 左右逆（成分ごと・Subtype.ext + funext + CCI-5）
theorem cli_left_inv  : ∀ s, cliFrom.map (cliTo.map s) = s      -- 各成分 cci_left_inv
theorem cli_right_inv : ∀ u, cliTo.map (cliFrom.map u) = u      -- 各成分 cci_right_inv

-- CLI-4: capstone レコード（M4b 本体）: Gal(ℚ(ζ_{3^∞})/ℚ) ≅ lim (ℤ/3^{n+1})^× = ℤ₃^×
structure CliIsoData where
  toU : Hom ctlProfinite zpsLimit
  fromU : Hom zpsLimit ctlProfinite
  left_inv : ∀ s, fromU.map (toU.map s) = s
  right_inv : ∀ u, toU.map (fromU.map u) = u
def cliIsoData : CliIsoData
-- （任意）limit_universal との整合検算: cliTo が錐 (cliChar n ∘ proj n) の媒介射である
-- ことは定義から rfl——∃ 版 limit_universal は使用しない（choice-free 規約の予防線）
```

**`limit_universal` が無い／使えない場合の代替**（問いの要求・ここでは「使わない」が正解）:
`limit_universal` は実在するが ∃ 形なので、witness 取り出しは Prop 外で不可。
上記のとおり**媒介射は担体の直接構成**（limit_universal の証明体と同じ式）で定義し、
一意性が要る箇所は成分ごとの funext で置換する。よって limit_universal への依存はゼロ。

工数: cli **400–600 行**（うち CLI-1 が半分）。tier **M（opus）・CLI-1 で詰まった場合のみ
fable スポット**（ctl_restr_comp_aux の写経で回る見込みだが、Gal 側 subst と単数側 mod の
合流順で簿記が絡む可能性を 1 スポット予約）。

---

## 4. 問い 4: 射影全射性 — choice 必要性の厳密評価（★本設計の中心）

### 4.1 なぜ素朴な Mittag-Leffler は choice を要するか（正直な分析）

主張したいのは `∀ τ : (ctlGal n).carrier, ∃ s : ctlProfinite.carrier, proj n s = τ`。
`s` の担体は `∀ m, (ctlGal m).carrier` の整合族＝**無限個のデータ**。素朴な構成は
「各 m ≥ n で `ctr_surjective` の原像を取り帰納的に持ち上げる」だが、`ctr_surjective` は
**∃ 文**であり、そこから関数 `∀ m, …` を作るのは可算従属選択（DC）そのもの。
有限群だから各ファイバーは有限だが、`FieldAut` 担体には走査可能な列挙構造が無く、
「最小 witness を取る」Nat 流の脱選択も直接は書けない。**一般の有限群逆系に対する
Mittag-Leffler 定理そのものを choice-free に形式化する道は、本コードベースの機構では無い**
——これは正直に限定として残す（§6 (iv)）。

### 4.2 本塔での脱出路: 指標による明示的分裂（choice-free・本設計の答え）

本塔は一般の逆系ではない。**全ての段が指標で (ℤ/3^{m+1})^× と同型であり、
その同型はデータ（`ctmFind`・`zpuInv`・`csaAut`）で書かれている**。したがって
「τ の指標 a を取り、**同じ整数 a を全レベルで使う**」正準切断が関数として書ける:

```
τ ∈ Gal(L_n/ℚ) → a := ctr_charG (n+1) τ.val（データ・fuel 走査）
             → 単数側整合族 u := (a % 3^{m+1})_m（閉じた式・ZPS-3）
             → s := cliFrom.map u（データ）・proj n s = cliAut(u n) = cliAut(a) = τ（cci_left_inv）
```

どの段でも ∃ から witness を取り出さない。**M4c は choice-free に閉じられる——判定 Yes**。
ロードマップ §4.3 の懸念（「choice を要するなら M4a+M4b 止まりで 0.73 級」）は解消され、
その分岐は §4.4 の fallback（cli が難航した場合の独立ルート）としてのみ保存する。

### 4.3 新規ファイル `IUT/CyclotomicProjSurj.lean`（prefix `cps`・依存: cli・zps・ctl）

```lean
-- CPS-1: ★射影全射性（監査残欠 (ii) の discharge・M4c 本丸）
theorem cps_proj_surjective (n : Nat) :
    ∀ τ : (ctlGal n).carrier,
      ∃ s : ctlProfinite.carrier, (profPi1_proj ctlTower n).map s = τ
-- 証明（全てデータ・choice-free）:
--   a := (cliChar n).map τ ∈ (zpsG n).carrier
--   obtain ⟨u, hu⟩ := zps_proj_surjective n a   -- ∃ の使用は Prop ゴール内・witness は閉式
--   refine ⟨cliFrom.map u, ?_⟩
--   proj n (cliFrom u) = (cliAut n).map (u.val n) は定義（成分 n）で rfl 級、
--   hu: u.val n = a、cci_left_inv: cliAut(cliChar τ) = τ。60–100 行。

-- CPS-2: 極限の非退化（監査文言「恒等以外の整合族の存在」への直接回答・安い系）
theorem cps_nontrivial : ∃ s : ctlProfinite.carrier, s ≠ ctlProfinite.one
-- s := cliFrom.map（zps_nontrivial の定数族 2）。第 0 成分の指標が 2 ≠ 1
--（cci_charG_csaAut + Hom.map_one）で分離。

-- CPS-3（検算・監査向け）: n=0 実例の非空虚性
theorem cps_example0 : … -- ctlGal 0 = Gal(ℚ(ζ₃)/ℚ) の非自明元（σ_2）に実際の原像を与える
```

工数: **100–180 行**。tier **S–M（sonnet 可・cli/zps の束ね）**。

### 4.4 fallback（cli の CLI-1 が予算超過した場合のみ・事前確認の上）

M4b を経ない**直接ルート**も choice-free に存在する: 族
`s m := ⟨csaAut (m+1) _ (a % 3^{m+1}) (zpuInvL (m+1) (a % 3^{m+1})) …⟩` を Gal 側で直接定義し、
compat を「char の一致＋cae_aut_ext」の d 帰納で示す（CLI-1 と同じ簿記を cps 内に内製）。
この場合 M4c（残欠 ii）だけが閉じ、極限同型（残欠 iii）は未達のまま——A3 は 0.72–0.73 級
の申告に留める。**主線はあくまで zpu→cci→zps→cli→cps の順**（同じ簿記を 1 回しか書かない）。

---

## 5. 問い 5: 最小 complete_pct 前進ステップ — マイルストーン分割・寄与見積り・優先順位

台帳: A3 = weight 12・status **0.7**（本日実測）。柱 A Σ(w·s) = 39.2/100・complete_pct 39。
丸めは `tools/compute_complete_pct.py` の `round(Σ(w·s)/Σw·100)`（Python round・本日実測）:

| A3 status | 柱 A 数値 | round | 柱%動くか |
|---|---|---|---|
| 0.70（現在） | 39.20 | **39** | — |
| 0.72（M4a のみ） | 39.44 | **39** | 動かない（正直申告） |
| 0.73（M4a+M4b） | 39.56 | **40** | **+1**（丸め閾 39.5 をここで越える） |
| 0.75（M4 完遂） | 39.80 | **40** | +1 |

各候補への自問「この一手は実 IUT 完全証明率を上げるか？」:

| 分割 | 内容（新規ファイル） | 実 IUT を進めるか | status 見積り（保守・監査確定が最終） | 工数・tier | 依存 |
|---|---|---|---|---|---|
| **M4a** | zpu＋cci（レベル同型 Gal≅(ℤ/3^ℓ)^×・指標積公式・Gal 可換性） | **Yes**——残欠 (iii) の前半（レベル同型）。円分 Galois 理論の教科書定理が ∀ℓ 本物で立つ | 0.7→**0.71–0.72**（残欠 (ii)・(iii) 後半が残るため小幅。**柱A% 39 据え置きを正直申告**） | zpu 300–450 [**M**]＋cci 350–500 [**M**] | zpu→cci 直列 |
| **M4b** | zps＋cli（逆系・lim (ℤ/3^{n+1})^×・極限同型 ≅ℤ₃^×） | **Yes**——残欠 (iii) の完全 discharge。「実プロファイナイト群の群同型による同定」の初到達 | 0.72→**0.73–0.74**（**柱A% 39→40 の丸め前進はここで発生する見込み**——0.75 を待たない） | zps 200–300 [**S–M**]＋cli 400–600 [**M**・CLI-1 に fable スポット 1 予約] | zpu→zps・cci→cli |
| **M4c** | cps（射影全射性＋極限の非退化） | **Yes**——残欠 (ii) の discharge。監査が「0.7 を超えない主因」と明記した項目 | 0.73–0.74→**0.75**（前々段設計 §6-1 の円分打ち止め上限・**A3=1 にはしない**） | cps 100–180 [**S–M**] | cli+zps→cps |

**どれが単独で A3 を動かすか（自問への答え）**: M4a 単独は status を 0.71–0.72 に上げるが
**柱A% は 39 のまま動かない**（39.44 → 39）。柱% の丸め前進（39→40）が起きる最小到達点は
**M4b（0.73）**。M4c まで揃えば 0.75 で確定的に 40。ゆえに「M4a だけ切り出して報告」は
complete_pct 主指標では 0 前進ラウンドになる——報告時にその旨を正直に書く。

**優先順位（結論）**:

1. **zpu**（逆元関数・単数群）[M・opus]——全ての前提。ctr_inv_exists の脱存在化が本体。
2. **cci**（レベル同型 M4a）[M・opus] と **zps**（逆系＋単数側全射性）[S–M・sonnet]——
   zpu 完了後に**並列可**（zps は cci に依存しない）。
3. **cli**（極限同型 M4b）[M・opus・CLI-1 fable スポット]——cci・zps 合流後。
4. **cps**（射影全射性 M4c）[S–M・sonnet]——cli 完了後。ここで **A3 0.75 申告→独立監査**。

5 並列編成案（CLAUDE.md tier 配分規則準拠・水増し枠埋めをしない）:
- **ラウンド 1**: zpu [opus] 1 本＋（依存の都合で M4 枠は 1 本のみ——残り 4 枠は
  他柱の complete_pct 前進案件で埋める。M4 のための空虚な先行 capstone は作らない）。
- **ラウンド 2**: cci [opus]＋zps [sonnet]＋（残枠は他柱）。
- **ラウンド 3**: cli [opus・fable スポット待機]＋cps 準備検算 [sonnet]＋（残枠は他柱）。
- **ラウンド 4**: cps [sonnet→詰まれば opus]＋独立監査 [独立枠]。

総工数見積り: **1350–2000 行・実装 3–4 ラウンド**。fable は CLI-1 の詰まり解決のみに限定。

---

## 6. 実装規約（全 5 新規ファイル共通・ロードマップ §6 を継承・opus/sonnet への指示に含める）

- **ヘッダ二軸**: 分類 [実]・complete_pct 影響を 1 行明記。cps のみ「A3 complete_pct 前進
  候補（M4c・監査確定待ち）」、cli は「M4b・同上」、zpu/cci/zps は「M4 の必要部品
  （単体では status 未設定・cli/cps 到達時に親が更新）」。
- **禁止タクティク**: simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp 不使用。分岐は `cases Nat.decEq … with`・項レベル ite。
  **新規 Classical.choice 禁止**（`#print axioms` = propext, Quot.sound 維持）。witness は
  すべてデータで持つ: 逆元は `zpuInv`（関数）・整合族は閉じた式・∃ の使用は Prop ゴール
  内のみ（zps_proj_surjective の適用など）。`limit_universal`（∃ 形）から**取り出さない**
  ——媒介射は直接定義（§3.2 CLI-2）。
- **新規ファイルのみ**・共有ファイル（IUT.lean/build.sh/dashboard/graph 系/target_ledger）
  不更新（親が統合時に一括・`tools/gen_graph.py` 再生成も親）。既存モジュールの改変禁止
  （ctr_inv_exists は消さず並存させる——∃ 版は Prop 内利用で今後も有用）。
- **3^n 算術**: omega は冪を扱えない。`zpu_pow_pos`/`zpu_pow_dvd` を zpu に集約し
  全ファイルで輸入（cte_pow3_pos・ctm_pow3_split の再輸出で済むならそれを優先し再証明
  しない）。
- **名前衝突**: `zmodUnits`（MuUnits.lean・素数版）と衝突しないこと。新設名は
  zpu/zps/cci/cli/cps prefix（本日 grep で全て未使用を確認済み）。
- 正直な限定を各ヘッダに**追記のみ**（§7 の (i)–(v) を該当ファイルへ配布）。

## 7. 正直な限定(本設計自身のもの・消さない・弱めない)

1. 本ドキュメントは設計であり complete_pct を動かさない。status 数値は全て保守的見積りで、
   確定は独立監査（reaudit-A 系・AUDIT_RUBRIC 準拠）。柱A% の 39→40 も監査確定後のみ反映。
2. **ℤ₃^× は「逆極限 lim (ℤ/3^{n+1})^×」としての定義そのもの**であり、p 進整数環 ℤ₃ の
   単数群としての独立構成（桁列・付値位相との同定）は行わない。zpsLimit をもって
   ℤ₃^× と**呼称**する根拠は逆極限定義の一致であり、これを超える主張はしない。
3. **一般の Mittag-Leffler 定理（任意の有限群逆系の射影全射性）は形式化しない**。
   M4c は「指標で明示的に分裂した本円分系」に固有の choice-free 構成であり、一般定理の
   代替ではない（§4.1 の分析を各ヘッダ限定 (iv) として配布）。
4. M4 完遂（0.75）でも A3 = 1 にしない: 建つのは可換な円分切片 Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^×
   であり**実絶対 Galois 群 G_ℚ ではない**（前々段設計 §6-1・M3 監査限定 (iv) の継承）。
   p = 3・ℚ 上固定・分離性/正規性の一般論未形式化も継続。
5. 本設計の 2 大リスク: (a) CLI-1（cli_char_restr の差分帰納と mod 簿記の合流）——
   fable スポット 1 予約・fallback は §4.4 の直接ルート（その場合 M4b 未達・0.72–0.73 止まり
   を正直申告）。(b) subgroupGrp/fieldAutComp の defeq 展開が show で固定できない場合、
   cci_charG_mul に展開補題数本の追加（+50 行級・設計変更なし）。
6. `zmodUnits`（素数版・Quot 担体）と `zpuGrp`（素数冪版・Nat subtype 担体）の同型は
   張らない（用途が交わらないため）。将来 p 一般化する際は zpu を p 引数化する方が
   本線であり、その時点で本ファイルの p=3 固定を正直な限定として引き継ぐ。
