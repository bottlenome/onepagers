# A7 詳細化 — 実円分剛性: 実 Gal(ℚ(ζ_{3^ℓ})/ℚ) の実 μ_{3^ℓ} への作用による代理/模型の §2(a) 昇格（A7 0 → 0.2〜0.45 級）

日付: 2026-07-10 ／ 種別: **設計ドキュメントのみ**（実装コード無し・共有ファイル不更新）
分類: **[実／昇格(a) の設計]** — 既存 A7 代理/模型（M322F 抽象 GK＋ℤ/n 模型・M334F 抽象 χ データ・
M404F テータ中心模型上の加群）の**主語を本物へ置換**する昇格ステップを、opus 実装枠に渡せる粒度
（新規ファイル・prefix・主要シグネチャ・依存・tier）へ段階分解する詳細化ラウンド。
台帳確認: `target_ledger.json` A7 = { weight 12, status **0** }（本日実測）。
柱 A の Σ(w·s) = **39.8**/100 → complete_pct 40（`graph-meta.json` と整合・本日実測）。
A7=0 の監査根拠は `graph-meta.json` A complete_note の文言「**円分剛性は抽象GK+ℤ/n模型**」。
**complete_pct 影響: 本ドキュメント自体は 0（設計のみ）**。実装マイルストーンの保守的予測は §5
（最終判定は独立監査・AUDIT_RUBRIC 準拠）。

**本設計の中心的発見（§0 で裏取り）**: 今セッションの A3 実円分塔機構は、A7 が必要とする
「実 Galois 作用の実 μ への降下」の**全部品を既にデータ（choice-free）で持っている**——
`ctr_pow_rpow`（ctmPow = rpow・`CyclotomicResTower.lean:79`）・`ctr_rpow_hom_gen`
（σ は冪を保つ・:448）・`ctm_root_in_powers`＋`ctmFind_spec`（3^ℓ 乗根は全て ζ の冪・指標抽出は
fuel 走査の関数・`CyclotomicMuTower.lean:577,687`）・`cae_aut_ext`（元は生成元の像で決まる・
`CyclotomicAutExt.lean:221`）・`cteIota`（段間埋め込み x̄↦x̄³・`CyclotomicEmbedTower.lean:224`）。
M322F `CycMuGroup`/`CycGKAction` の**全フィールドが実対象で埋まる**ため、A7a は新イディオム
ゼロの組み立てで閉じる。M322F 自身が正直申告していた後続課題
「**非自明な χ（σ(ζ)=ζ^a, a≠1）を与える実 Galois 自己同型の μ_n への降下は後続**」
（`CyclotomicRigidity.lean:71-73`）が、まさに本設計で discharge される対象である。

---

## 0. 既存資産の再監査（本日 read 済み・シグネチャ実在確認）

### 0.1 置換対象 = A7 の既存代理/模型（**消さない・主語を本物で置換**）

| 代理/模型 | 何が surrogate か（本日精読） | 本設計での扱い |
|---|---|---|
| `CyclotomicRigidity.lean`（M322F・cycRig） | 定理群（χ 準同型・単元性・剛性 σ_g(z)=ζ^{χ·log z}・同期）は抽象 `GK : Grp`（任意群）＋抽象 `CycMuGroup`（任意巡回群）＋抽象 `CycGKAction`（作用は外部データ）の上。実例 `cycRigGaloisExample` は μ_n=**ℤ/n 模型**（`cycMuStd`=zmod n）＋**trivial 作用**（χ≡1）のみ。complete_note の「抽象GK+ℤ/n模型」の本体 | **§1-§2（A7a）**: 抽象定理は消さず、`CycMuGroup`/`CycGKAction` の**実インスタンス**（実 μ_{3^ℓ}⊂ℚ(ζ_{3^ℓ})・実 Gal(ℚ(ζ_{3^ℓ})/ℚ) の制限作用・非自明 χ=σ₂）を供給して主語を昇格 |
| `CyclotomeRecovery.lean`（M334F・cycRec） | χ を `cycRecCharacter`（抽象データ）で受け、復元 μ̂ は **ℤ/n 模型**（zmod n に χ 捻り）。正直申告「χ 自体を実対象から抽出する本丸は骨組み」 | **§2 末尾（A7a-2 内）**: 実 χ（`ctr_charG` 由来）から `cycRecCharacter` の実 witness を供給（抽象データ→実データの昇格・約 40 行） |
| `CyclotomeGaloisModule.lean`（M404F・cgm） | G_K-加群公理・canonical 性は本物だが、引数 (GK, M, ρ) は抽象・中心 μ_l の実体は**テータ群 thetaGrp（Heisenberg 模型）の中心**＋`centerToMu`（Zp p 模型・M124F） | 引数 (GK,M,ρ) へ実インスタンスを代入する実例追加は**任意**（§5・水増し判定に注意）。thetaGrp 中心模型そのものは柱 E4 の射程で本設計 scope 外 |
| `CyclotomicSync.lean`（M124F・centerToMu） | テータ群 mod l の中心 (0,0,z) → μ_l⊂ℤ_p の同期写像。主語はテータ中心であって G_K 作用でない（M322F ヘッダが明記） | **scope 外**（柱 E4/mono-theta の射程・§7） |
| `CyclotomeIdentification.lean`（M443F・cid） | A 側 Zp p と E 側 CycMuGroup の同定。E.n=l・hζl・hdist を**外部仮定**で受ける | 後続候補: `cmrMu`（§1）が hζl/hdist を**定理として**持つため外部仮定の一部を discharge できる。本設計の最小ステップには含めない（§5 追記） |
| `KummerCharReal.lean`（M349F・kcr） | κ_α(σ)=σ(α)/α は本物だが、K は抽象 `IUTField`・準同型性は自明作用仮説 `htriv`・a の n 乗根存在は外部 | **§4 で scope 判定**（結論: A7 の最小範囲に含めない・A6/E4 境界） |

### 0.2 土台 = 今セッション完成の実機構（全て `#print axioms` = [propext, Quot.sound]）

| 資産 | 実在シグネチャ（本日確認） | A7 での役割 |
|---|---|---|
| 実円分体・実 Gal | `cteField ℓ hℓ : IUTField`＝ℚ(ζ_{3^ℓ})=ℚ[x]/(Φ_{3^ℓ})（`CyclotomicEmbedTower.lean:94`）・`cteExt`（:100）・`galoisGroupGrp (cteExt ℓ hℓ)`＝実 Gal(ℚ(ζ_{3^ℓ})/ℚ)（担体は mem subtype・mul の val は `fieldAutComp` に defeq——cci 実装で実証済み） | A7 の実 G_K（円分切片） |
| 実 μ_{3^ℓ} の素材 | `ctmZeta ℓ hℓ`（ζ=x̄・`CyclotomicMuTower.lean:78`）・`ctmPow`（:82）・`ctm_zeta_pow`（ζ^{3^ℓ}=1・:179）・`ctm_order`（:235）・`ctm_powers_distinct`（:266 近傍）・`ctm_root_in_powers`（y^{3^ℓ}=1⟹∃a<3^ℓ, y=ζ^a・:577）・`ctmFind`（fuel 走査の**関数**・:616）・`ctmFind_spec`（y=ζ^{find y}∧find y<3^ℓ・:687） | §1 の実 CycMuGroup の全フィールド。log=`ctmFind` は choice-free データ |
| rpow 橋 | `ctr_pow_rpow`（ctmPow k = rpow (cteField).toCRing ζ k・`CyclotomicResTower.lean:79`）・`ctr_rpow_hom_gen`（rpow(σz)m=σ(rpow z m)・:448）・`ctr_zeta_pow_gen`（(σζ)^{3^ℓ}=1・:460）・`rpow_mul_dist`（`PSFunctor.lean:62`）・`rpow_one_mul_closed`（`EisensteinGalois.lean:260`）・`rpow_add`（`FormalGroupExists.lean:50`） | §1 の μ 部分群の閉性・逆元・§2 の作用の well-defined 性 |
| 実指標 | `ctr_charG ℓ hℓ σ := ctmFind ℓ hℓ (σ.toFun (ctmZeta ℓ hℓ))`（:467）・`ctr_charG_spec/lt/nd3`（:471,476,494）・`ctr_sigma_powG`（σ(ζ^k)=ζ^{ak}・:481）・`ctr_sigma_injG`（:487） | §2 の χ。**M322F `cycRigExp` と定義が合流する**（両者 ctmFind(σζ)・§2.2） |
| レベル同型 | `cciToUnits/cciFromUnits/cciIsoData`（Gal≅(ℤ/3^ℓ)^×・`CyclotomicCharIso.lean`）・`cci_charG_mul`（積公式）・`cci_charG_csaAut`（char(σ_a)=a）・`cci_indexG`（ζ^k=ζ^a・a<3^ℓ⟹k%3^ℓ=a）・`cae_aut_ext` | §2 の非自明 χ 供給（σ₂）・§3 の Aut 分類・全射方向 |
| 極限機構 | `ctlGal n`＝Gal(ℚ(ζ_{3^{n+1}})/ℚ)・`ctlStep/ctlRestr`・`ctlProfinite`（実 profinite Gal(ℚ(ζ_{3^∞})/ℚ)・`CyclotomicTowerLimit.lean`）・`cliChar/cli_res_char/cli_char_restr/cliIsoData`（Gal(ℚ(ζ_{3^∞})/ℚ)≅ℤ₃^×・`CyclotomicLimitIso.lean`）・`zpsG/zpsT/zpsLimit`＝ℤ₃^×・`natSystem/limitGrp/limitProj` | §3(A7b) の T=ℤ₃(1) の受け皿。χ の極限同型は**再利用**（再証明しない） |
| 段間埋め込み | `cteIota n hn : RingHom (cteField n).toCRing (cteField (n+1)).toCRing`＝**x̄↦x̄³**（`CyclotomicEmbedTower.lean:224`・map_add/map_mul/map_one 済み） | §3 の Tate 遷移の忠実性証明書 ι(t y)=y³ |
| M322F 抽象枠 | `CycMuGroup`（μ/comm/ζ/n/hn/ord/log/log_lt/pow_log/distinct）・`CycGKAction`（act/act_one/act_mul）・`cycRigExp/cycRigChar/cycRig_rigidity/cycRig_sync/cycRigData` | **消さずに再利用**——実インスタンスを代入すれば全定理が実主語で回る設計（M322F 自身のヘッダが明言） |

新規 prefix 衝突チェック（本日 grep）: `cmr`・`cgar`・`tmz`・`cra` はいずれも未使用。

依存 DAG（本設計の 4 新規ファイル）:

```
cmr (実 μ_{3^ℓ} 群)──→ cgar (実 GK 作用+非自明 χ = A7a)──→ cra (剛性定理 = A7c)
                              └──────────────────────────→ tmz (T=ℤ₃(1) = A7b)   [cli/zps/ctl を輸入]
```

---

## 1. 問い 1 前半: 実 μ_{3^ℓ} の CycMuGroup 化 — `IUT/CyclotomicMuGroupReal.lean`（prefix `cmr`・依存: ctm・ctr・PSFunctor・EisensteinGalois・CyclotomicRigidity〔CycMuGroup の型のみ〕）

### 1.1 設計判断

μ_{3^ℓ} の担体は**実円分体の中の実部分群** `{ y : (cteField ℓ hℓ).carrier // rpow … y (3^ℓ) = one }`
とする（ℤ/n 模型でも指数の抽象群でもない・§3 toy 主語禁止の遵守）。閉性・逆元・生成元・
離散対数の全てが §0.2 の既存補題のデータで埋まる:

- 積の閉性 = `rpow_one_mul_closed`（既存・EisensteinGalois:260）。
- 逆元 = **データ** `y ↦ y^{3^ℓ−1}`（y·y^{3^ℓ−1} = y^{3^ℓ} = 1・`rpow_add`。choice 不要）。
- 生成元 ζ = `ctmZeta`（root 性は `ctr_pow_rpow`＋`ctm_zeta_pow`）。
- **離散対数 log = `ctmFind`（fuel 走査の関数・choice-free）**、仕様は `ctmFind_spec`。
- 全射性（μ=⟨ζ⟩）= `ctm_root_in_powers`（3^ℓ 乗根は全て ζ の冪——多項式の根の個数
  `prc_roots_le_degree` による本物の定理であり、これが「担体を root 全体に取ってよい」根拠）。

### 1.2 Lean スケッチ

```lean
/- CMR-1: 実 μ_{3^ℓ} の担体と群 -/
def cmrCarrier (ℓ : Nat) (hℓ : 1 ≤ ℓ) : Type :=
  { y : (cteField ℓ hℓ).carrier // rpow (cteField ℓ hℓ).toCRing y (3 ^ ℓ)
      = (cteField ℓ hℓ).toCRing.one }

def cmrGrp (ℓ : Nat) (hℓ : 1 ≤ ℓ) : Grp where
  carrier := cmrCarrier ℓ hℓ
  mul := fun y z => ⟨(cteField ℓ hℓ).toCRing.mul y.val z.val,
                     rpow_one_mul_closed _ (3 ^ ℓ) y.property z.property⟩
  one := ⟨(cteField ℓ hℓ).toCRing.one, rpow_one_base _ (3 ^ ℓ)⟩
  inv := fun y => ⟨rpow _ y.val (3 ^ ℓ - 1), …⟩   -- (y^{3^ℓ−1})^{3^ℓ} = (y^{3^ℓ})^{3^ℓ−1} = 1
  -- 群公理: 全て Subtype.ext + CRing 公理（mul_assoc/one_mul/…）。
  -- inv_mul: y^{3^ℓ−1}·y = y^{3^ℓ} = 1（rpow_add + 3^ℓ = (3^ℓ−1)+1・zpu_pow_pos で 1 ≤ 3^ℓ）。
  -- ※ Grp のフィールド名・公理の向き（mul_one/mul_inv 等）は FundamentalGroup.lean:74 の
  --   定義に実装時に合わせる（cycRig の証明群が使用例）。

theorem cmr_comm (ℓ hℓ) (y z) : (cmrGrp ℓ hℓ).mul y z = (cmrGrp ℓ hℓ).mul z y
  -- Subtype.ext + CRing.mul_comm

/- CMR-2: Grp.pow ↔ rpow ↔ ctmPow の三者橋（★本ファイル最大の簿記） -/
-- Grp.pow は左乗算の反復（pow g (k+1) = mul g (pow g k)・cycRig_pow_add の証明で確認済み）、
-- rpow は右乗算の反復（rpow (k+1) = mul (rpow k) a・LubinTateUnique.lean:46）。
-- 可換性（cmr_comm / CRing.mul_comm）で k 帰納の両向きを合流させる:
theorem cmr_pow_val (ℓ hℓ) (y : cmrCarrier ℓ hℓ) (k : Nat) :
    ((cmrGrp ℓ hℓ).pow y k).val = rpow (cteField ℓ hℓ).toCRing y.val k
theorem cmr_pow_zeta (ℓ hℓ) (k : Nat) :
    ((cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) k).val = (ctmPow ℓ hℓ k).val
  -- cmr_pow_val + ctr_pow_rpow（既存）を .val で連結

/- CMR-3: 生成元 -/
def cmrZeta (ℓ : Nat) (hℓ : 1 ≤ ℓ) : cmrCarrier ℓ hℓ :=
  ⟨(ctmZeta ℓ hℓ : …), by rw [← ctr_pow_rpow ℓ hℓ (3 ^ ℓ)]; exact congrArg _ (ctm_zeta_pow ℓ hℓ)⟩
  -- ※ ctmZeta の型 GefNF (ctsPhi ℓ) (2·3^{ℓ-1}) と (cteField ℓ hℓ).carrier は defeq
  --   （cteField := gefNFIUTField …、担体は同じ GefNF）。実装冒頭に検算 def を置く。
  -- ※ ctmFind_spec の仮定は rpow (ctmK ℓ hℓ).ring y (3^ℓ) = one（ctmK=gefNF268）。
  --   CTM-5a コメントが「(ctmK n hn).ring は ctmR n hn に定義等値」と明記。cteField.toCRing
  --   との defeq も同根（いずれも gefNFRing）。万一 defeq が通らない場合は val 等式の
  --   付替補題 1 本（+20 行・設計変更なし）。

/- CMR-4: 実 CycMuGroup インスタンス（★A7a の中核・M322F 抽象枠の実充填） -/
def cmrMu (ℓ : Nat) (hℓ : 1 ≤ ℓ) : CycMuGroup where
  μ := cmrGrp ℓ hℓ
  comm := cmr_comm ℓ hℓ
  ζ := cmrZeta ℓ hℓ
  n := 3 ^ ℓ
  hn := zpu_pow_pos ℓ                       -- 1 ≤ 3^ℓ
  ord := …                                   -- cmr_pow_zeta + ctm_zeta_pow + Subtype.ext
  log := fun y => ctmFind ℓ hℓ y.val         -- ★choice-free データ
  log_lt := fun y => (ctmFind_spec ℓ hℓ y.val y.property).2
  pow_log := fun y => …                       -- (ctmFind_spec …).1 + cmr_pow_zeta + Subtype.ext
  distinct := …                               -- ctm_powers_distinct + cmr_pow_zeta +
                                              -- 「val が異なれば subtype 元も異なる」
```

**禁止タクティク回避**: 全て Subtype.ext・k 帰納・rw 直線。分岐なし。3^ℓ 算術は
`zpu_pow_pos`/`ctm_pow3_split` 再利用（omega に冪を渡さない）。

工数: **300–450 行**。tier **M（opus）**（CMR-2 の pow 方向橋が唯一の簿記・新イディオム無し）。
complete_pct 単体寄与: 無し（A7a の必要部品・ヘッダに「cgar 到達で反映」と明記）。

---

## 2. 問い 1 後半+問い 3 の入口: 実 Galois 作用と非自明 χ — `IUT/CyclotomicGKActionReal.lean`（prefix `cgar`・依存: cmr・cci・ctr・CyclotomicRigidity・CyclotomeRecovery）

### 2.1 実 G の実 μ への作用（σ の制限・模型でなく実作用）

σ ∈ Gal(ℚ(ζ_{3^ℓ})/ℚ) は体自己同型だから 3^ℓ 乗根を 3^ℓ 乗根に送る
（`ctr_rpow_hom_gen`＋`map_one`）——μ_{3^ℓ} への制限が**実 Galois 作用**そのもの:

```lean
/- CGAR-1: σ の μ_{3^ℓ} への制限（G-同変な群準同型） -/
def cgarRestrict (ℓ hℓ) (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) :
    Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ) where
  map := fun y => ⟨σ.val.toFun y.val, by
    rw [ctr_rpow_hom_gen ℓ hℓ σ.val y.val (3 ^ ℓ), y.property]; exact σ.val.map_one⟩
  map_mul := fun y z => Subtype.ext (σ.val.map_mul y.val z.val)

/- CGAR-2: 実 CycGKAction（★M322F CycGKAction の実充填・A7a 本丸） -/
def cgarAct (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    CycGKAction (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) where
  act := cgarRestrict ℓ hℓ
  act_one := fun y => Subtype.ext rfl      -- one.val = fieldAutId（galoisSubgroup の one）
                                            -- ⟹ toFun = id。show で defeq を固定
  act_mul := fun σ τ y => Subtype.ext rfl  -- mul.val = fieldAutComp（cci で実証済みの defeq）
                                            -- ⟹ toFun = σ∘τ。同上
  -- ※ defeq が rfl で閉じない場合も cci_charG_mul 実装冒頭と同じ show 1 行で閉じる。

/- CGAR-3: 指標の合流 — M322F の抽象 χ 抽出が実指標 ctr_charG に一致する -/
theorem cgar_exp_eq (ℓ hℓ) (σ) :
    cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ
      = ctr_charG ℓ hℓ σ.val
  -- 両辺とも ctmFind ℓ hℓ (σ.val.toFun (ctmZeta ℓ hℓ))：LHS = M.log((act σ).map M.ζ) の
  -- 展開が RHS の定義（ctr_charG:467）に一致——rfl 級（cmrZeta.val = ctmZeta の defeq 経由）
theorem cgar_char_eq (ℓ hℓ) (σ) :
    cycRigChar … σ = Quot.mk (modCong (3 ^ ℓ)).rel ((ctr_charG ℓ hℓ σ.val : Int))

/- CGAR-4: ★非自明 χ（M322F 正直申告 :71-73 の discharge・A7a のヘッドライン） -/
def cgarSigma2 (ℓ : Nat) (hℓ : 1 ≤ ℓ) : (galoisGroupGrp (cteExt ℓ hℓ)).carrier :=
  (cciFromUnits ℓ hℓ).map ⟨2, ⟨(2 < 3^ℓ の zpu 補題), (by intro ⟨k,hk⟩; omega)⟩⟩
theorem cgar_sigma2_exp (ℓ hℓ) : cycRigExp … (cgarSigma2 ℓ hℓ) = 2
  -- cgar_exp_eq + cci_charG_csaAut（char(σ_a)=a・既存）
theorem cgar_nontrivial (ℓ hℓ) :
    cycRigExp … (cgarSigma2 ℓ hℓ) ≠ cycRigExp … (galoisGroupGrp (cteExt ℓ hℓ)).one
  -- 2 ≠ 1（one 側は act_one + ctmFind の一意性 or cgar_exp_eq + ctr_charG(id) = 1 補題）。
  -- Nat 指数レベルで述べ zmod 類の分離補題を避ける。

/- CGAR-5: 剛性・同期の実主語インスタンス化（M322F 定理の主語昇格・各 1 行） -/
theorem cgar_rigidity (ℓ hℓ) (σ) (y : cmrCarrier ℓ hℓ) :
    ((cgarAct ℓ hℓ).act σ).map y
      = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (cycRigExp … σ * ctmFind ℓ hℓ y.val) :=
  cycRig_rigidity … -- 実 Gal(ℚ(ζ_{3^ℓ})/ℚ) の実 μ_{3^ℓ} への作用が実 χ で一意決定
def cgarRigidityData (ℓ hℓ) :
    CyclotomicRigidityData (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) :=
  cycRigData … (cgarAct ℓ hℓ)   -- M322F capstone の実主語版（旧実例 = 模型+trivial の置換）

/- CGAR-6: M334F 抽象 χ データの実 witness（CyclotomeRecovery の入力昇格・約 40 行） -/
def cgarRecChar (ℓ hℓ) : cycRecCharacter (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) where
  chi := cycRigChar … (cgarAct ℓ hℓ)
  chi_hom := cycRig_char_isHom …
  chi_one := cycRig_char_one …
  chi_unit := cycRig_char_unit …
-- これにより M334F の復元機構（cycRecAction 等）が実 χ を入力に持つ。
-- （M334F の「χ を π₁^ét 位相群の連続指標として抽出」は依然後続——弱めず継承）
```

工数: **250–400 行**。tier **M（opus）**。詰まりどころは CGAR-2 の defeq（show 固定で
既存実証あり）と CGAR-3 の rfl 級合流のみ——fable 不要と判断。

**A7a（cmr+cgar）で何が「模型→本物」に変わるか（差分の明示）**:

| | 従来（M322F 実例・M334F 入力） | A7a 後 |
|---|---|---|
| G_K | 抽象 `GK : Grp`／実例は G_ℚ だが trivial 塔 | **実 Gal(ℚ(ζ_{3^ℓ})/ℚ)**（担体=実体自己同型・∀ℓ） |
| μ_n | 抽象 `CycMuGroup`／実例は **ℤ/n 模型**（zmod n） | **実 μ_{3^ℓ} ⊂ ℚ(ζ_{3^ℓ})^×**（多項式の根の実部分群） |
| 作用 | 外部データ `CycGKAction`／実例は **trivial（χ≡1）** | **実 σ の制限**（体自己同型の実作用） |
| χ | 抽象 log 抽出／実例は χ≡1 のみ | **実 ctr_charG に一致・非自明値 χ(σ₂)=2 を実現** |

---

## 3. 問い 2+3: 実 cyclotome ℤ₃(1) と剛性定理

### 3.1 問い 2（A7b）: Tate 加群 T = ℤ₃(1) = lim μ_{3^{n+1}} — `IUT/TateModuleZ3.lean`（prefix `tmz`・依存: cmr・cgar・cli・zps・ctl・Profinite/ProObject・cte）

**設計の要点**: 各段の μ は別々の体 ℚ(ζ_{3^{n+1}}) に住む（K̄ を持たない——§7 の正直な限定）。
遷移射は zpsT と同じ発想で**単発の指数読み替え**（反復・cast 不要）で書き、それが本物の
Tate 遷移（3 乗写像）であることを**実埋め込み ι との整合証明書**で担保する:

```lean
/- TMZ-1: 添字整合（ctlGal n = Gal(ℚ(ζ_{3^{n+1}})/ℚ) に合わせる） -/
def tmzG (n : Nat) : Grp := cmrGrp (n + 1) (by omega)     -- μ_{3^{n+1}} ⊂ ℚ(ζ_{3^{n+1}})

/- TMZ-2: 遷移射（指数読み替え・単発・choice-free） -/
def tmzT {i j : Nat} (h : i ≤ j) : Hom (tmzG j) (tmzG i) where
  map := fun y => ⟨(ctmPow (i+1) (by omega) (ctmFind (j+1) (by omega) y.val)).…, root 証明⟩
  map_mul := …
-- 部品補題（いずれも既存材料の合成）:
--   tmz_find_pow : ctmFind ℓ hℓ (ctmPow ℓ hℓ e).… = e % 3^ℓ        （ctmFind_spec+cci_indexG）
--   tmz_find_mul : find(y·z) = (find y + find z) % 3^ℓ               （ctmPow_add+tmz_find_pow）
--   map_mul は tmz_find_mul + ctm_pow_mod + zpu_pow_dvd(i+1 ≤ j+1) で合流
theorem tmz_t_self (i) (y) : (tmzT (Nat.le_refl i)).map y = y        -- ctmFind_spec.1
theorem tmz_t_comp …                                                  -- tmz_find_pow+ctm_pow_mod
def tmzSystem : InverseSystem := natSystem tmzG (fun h => tmzT h) tmz_t_self tmz_t_comp
def tmzLimit : Grp := limitGrp tmzSystem      -- ★T = ℤ₃(1)（実 μ 塔の逆極限）

/- TMZ-3: ★忠実性証明書 — 遷移射は実 3 乗写像を実埋め込み ι で読んだもの -/
theorem tmz_iota_zeta (n) : (cteIota (n+1) _).map (ctmZeta (n+1) _).… = (ctmPow (n+2) _ 3).…
  -- cteIota は x̄↦x̄³（CTE-5・:221-229）。gefNFMon の像の計算 1 本（無ければ +30 行）
theorem tmz_iota_cube (n : Nat) (y : (tmzG (n+1)).carrier) :
    (cteIota (n+1) (by omega)).map ((tmzT (Nat.le_succ n)).map y).val.…
      = rpow (cteField (n+2) (by omega)).toCRing y.val 3
  -- ι(t y) = ι(ζ_{n+1}^{find y}) = (ι ζ_{n+1})^{find y} = ζ_{n+2}^{3·find y} = y³
  -- （RingHom は rpow を保つ——ctr_rpow_hom_gen の RingHom 版・既存に無ければ同型の帰納 +20 行。
  --   3·(e%3^{n+1}) と 3e % 3^{n+2} の合流は Nat 算術補題 1 本）
-- ⟹ tmzLimit を ℤ₃(1) と呼称する根拠: 逆極限の定義一致 + 遷移が実 cube 写像（ι 読み）

/- TMZ-4: G = Gal(ℚ(ζ_{3^∞})/ℚ) の T への作用（成分ごと実作用） -/
def tmzActHom (s : ctlProfinite.carrier) : Hom tmzLimit tmzLimit where
  map := fun y => ⟨fun n => ((cgarAct (n+1) (by omega)).act (s.val n)).map (y.val n), compat⟩
  map_mul := …    -- 成分ごと cgarRestrict.map_mul
-- ★compat（作用と遷移の可換・fable スポット予約）:
theorem tmz_act_compat {i j} (h : i ≤ j) (σ : (ctlGal j).carrier) (y : (tmzG j).carrier) :
    (tmzT h).map (((cgarAct (j+1) _).act σ).map y)
      = ((cgarAct (i+1) _).act ((ctlRestr h).map σ)).map ((tmzT h).map y)
  -- 両辺の指数: LHS = χ_j(σ)·find y % 3^{i+1}、RHS = χ_i(res σ)·(find y % 3^{i+1}) % 3^{i+1}。
  -- cli_res_char（χ_i(res σ) = χ_j(σ) % 3^{i+1}・既存）+ Nat.mul_mod で合流。
  -- 単段→差分帰納は cli_char_restr_aux の写経（ctl_restr_step で peel）。
def tmzAction : CycGKAction 型ではなく（T は CycMuGroup でない——巡回でなく pro-巡回）、
  act/act_one/act_mul を直接束ねた構造 TmzGModule として定義:
structure TmzGModule where
  act : ctlProfinite.carrier → Hom tmzLimit tmzLimit
  act_one : ∀ y, (act ctlProfinite.one).map y = y
  act_mul : ∀ s t y, (act (ctlProfinite.mul s t)).map y = (act s).map ((act t).map y)
-- 成分ごと cgarAct.act_one/act_mul で全フィールド充填（witness tmzGModule）

/- TMZ-5: 作用は χ で記述され χ : G ≅ ℤ₃^× は cli の再利用（★A7b のヘッドライン） -/
theorem tmz_act_char (s : ctlProfinite.carrier) (y : tmzLimit.carrier) (n : Nat) :
    ((tmzActHom s).map y).val n
      = (tmzG n).pow (cmrZeta (n+1) _) (((cliChar n).map (s.val n)).val * ctmFind (n+1) _ (y.val n).val)
  -- 成分ごと cgar_rigidity（cycRig_rigidity の実主語版）——「T への G 作用は χ で一意決定」
-- χ の同型性は cliIsoData（既存・再証明しない）を capstone レコードに束ねるだけ:
structure TmzTateData where
  module : TmzGModule                    -- T=ℤ₃(1) の実 G-加群構造
  char_iso : CliIsoData                  -- χ : G ≅ ℤ₃^×（cli 再利用）
  act_by_char : ∀ s y n, …               -- tmz_act_char
  iota_cube : ∀ n y, …                   -- tmz_iota_cube（遷移の忠実性証明書）
def tmzTateData : TmzTateData
/- TMZ-6（安い系）: T の各段射影の全射性（zps ZPS-3 の写経・witness は定数指数族） -/
theorem tmz_proj_surjective (n) (y : (tmzG n).carrier) :
    ∃ t : tmzLimit.carrier, (limitProj tmzSystem n).map t = y
  -- witness: t := ⟨fun m => ζ_{m+1}^{find y}, …⟩（閉じた式・choice-free）
```

工数: **450–650 行**（うち tmz_act_compat が 1/3）。tier **M（opus）・tmz_act_compat の
差分帰納で詰まった場合のみ fable スポット 1**（cli_char_restr_aux という写経元があるため
回る見込み）。

### 3.2 問い 3（A7c）: 剛性定理の実内容 — `IUT/CyclotomicRigidityAut.lean`（prefix `cra`・依存: cmr・cgar・cci・zpu）

**本物に閉じられる最小の rigidity の特定**（IUT の mono-theta 円分剛性は scope 外・§7）:

1. **自己準同型分類**: 実 μ_{3^ℓ} の任意の群自己準同型は冪写像 y↦y^a である
   （e(ζ) ∈ μ ゆえ e(ζ)=ζ^a・e(y)=e(ζ^{log y})=ζ^{a·log y}——**Galois 由来でない任意の e**
   に対する剛性。ここが M322F cycRig_rigidity〔作用の χ 決定〕からの真の強化）。
2. **Gal ≅ Aut(μ_{3^ℓ})**: 自然な作用写像 Gal → End(μ) は単射（`cae_aut_ext`）で、像は
   可逆自己準同型全体（1 の分類 + `cciFromUnits`）——「**円分体の自己同型群がちょうど
   Galois 群で尽くされる**」= 円分剛性の教科書形。
3. **χ の canonical 性**: χ は生成元 ζ の取り替えに依存しない（同一視 μ≅ℤ/3^ℓ の選択に
   よらず χ が内在的）——「円分同一視の剛性」の実内容。
4. **正直な不定性定理**: 純群論の μ には (ℤ/3^ℓ)^× 不定性が**残る**（可換ゆえ全冪写像が
   Galois 作用と可換）——IUT が mono-theta 環境で殺す ẑ^× 不定性の実在を定理として明示。

```lean
/- CRA-0: Hom の外延性（map 一致 ⟹ Hom 一致・cases+funext・map_mul は Prop） -/
theorem cra_hom_ext {G H : Grp} (e e' : Hom G H) (h : ∀ y, e.map y = e'.map y) : e = e'

/- CRA-1: 自己準同型の指標と分類（★任意の e——Galois 仮定なし） -/
def craEndoChar (ℓ hℓ) (e : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ)) : Nat :=
  ctmFind ℓ hℓ (e.map (cmrZeta ℓ hℓ)).val
theorem cra_endo_pow (ℓ hℓ) (e) (y) :
    e.map y = (cmrGrp ℓ hℓ).pow (cmrZeta ℓ hℓ) (craEndoChar ℓ hℓ e * ctmFind ℓ hℓ y.val)
  -- y = ζ^{log y}（cmrMu.pow_log）→ Hom.map_pow → e ζ = ζ^{char e}（ctmFind_spec・
  -- e ζ ∈ μ は担体の subtype 性で自動）→ cycRig_pow_mul（既存・可換群の冪法則）
theorem cra_endo_ext (ℓ hℓ) (e e') (h : craEndoChar ℓ hℓ e = craEndoChar ℓ hℓ e') : e = e'

/- CRA-2: 可逆性 ⟺ 単元指標 -/
def craPowHom (ℓ hℓ) (a : Nat) : Hom (cmrGrp ℓ hℓ) (cmrGrp ℓ hℓ)   -- y ↦ y^a（データ）
theorem cra_iso_of_unit (ℓ hℓ) (a) (ha : ¬ 3 ∣ a) :
    (craPowHom … a) と (craPowHom … (zpuInvL ℓ a)) は左右逆    -- zpuInvL_one（既存）
theorem cra_unit_of_iso (ℓ hℓ) (e e') (hl : 左逆) (hr : 右逆) : ¬ 3 ∣ craEndoChar ℓ hℓ e
  -- e∘e' = id を ζ で読み a·a' ≡ 1 mod 3^ℓ（tmz_find_pow 系）⟹ 3∤a

/- CRA-3: ★Gal ≅ Aut(μ_{3^ℓ})（円分剛性の教科書形・A7c 本丸） -/
theorem cra_gal_inj (ℓ hℓ) (σ τ)
    (h : ∀ y, ((cgarAct ℓ hℓ).act σ).map y = ((cgarAct ℓ hℓ).act τ).map y) : σ = τ
  -- 生成元で読む + cae_aut_ext（既存の決定補題）
theorem cra_gal_realize (ℓ hℓ) (e : Hom …) (he : e は可逆〔左右逆 Hom の存在〕) :
    ∃ σ, ∀ y, ((cgarAct ℓ hℓ).act σ).map y = e.map y
  -- witness σ := (cciFromUnits ℓ hℓ).map ⟨craEndoChar e % 3^ℓ, …⟩（データ・choice-free。
  --   ∃ は Prop ゴール内のみ）。一意性は cra_gal_inj。
-- 束ね: 「作用写像 Gal → End(μ) は単射・像 = 可逆元全体」＝ Gal ≅ Aut(μ_{3^ℓ})。
-- Aut(μ) を Grp として新設はしない（Hom レコードの群化は共有インフラ級・範囲外）——
-- 単射性+実現+分類の 3 定理で同型を消去形で述べる（cci の Gal≅(ℤ/3^ℓ)^× と合成可能）。

/- CRA-4: χ の canonical 性（生成元非依存・同一視の剛性） -/
theorem cra_full_order_iff (ℓ hℓ) (y) : (y が位数ちょうど 3^ℓ) ↔ ¬ 3 ∣ ctmFind ℓ hℓ y.val
theorem cra_char_canonical (ℓ hℓ) (σ) (y' : cmrCarrier ℓ hℓ) (hy' : ¬ 3 ∣ ctmFind ℓ hℓ y'.val) :
    ((cgarAct ℓ hℓ).act σ).map y' = (cmrGrp ℓ hℓ).pow y' (ctr_charG ℓ hℓ σ.val)
  -- σ(y') = σ(ζ^b) = ζ^{ab} = (ζ^b)^a = y'^a：どの原始根で読んでも同じ指数 a = χ(σ)。
  -- 「μ ≅ ℤ/3^ℓ の同一視の選択に χ が依存しない」＝円分指標の内在性

/- CRA-5: 正直な不定性（消さない・IUT 本丸との距離の明示） -/
theorem cra_indeterminacy (ℓ hℓ) (a : Nat) (σ) (y) :
    ((cgarAct ℓ hℓ).act σ).map ((craPowHom ℓ hℓ a).map y)
      = (craPowHom ℓ hℓ a).map (((cgarAct ℓ hℓ).act σ).map y)
  -- 全冪写像が Galois 作用と可換 ⟹ 純 Galois 加群としての μ は (ℤ/3^ℓ)^× 不定性を持つ。
  -- この不定性を殺すのが mono-theta 環境の円分剛性（[EtTh]）——柱E/D 後続（本設計 scope 外）

/- CRA-6: capstone -/
structure CraRigidityData (ℓ : Nat) (hℓ : 1 ≤ ℓ) where
  endo_pow : …          -- CRA-1（自己準同型分類）
  endo_ext : …          -- 指標が自己準同型を決める
  gal_inj : …           -- CRA-3 単射
  gal_realize : …       -- CRA-3 実現
  char_canonical : …    -- CRA-4
def craRigidityData (ℓ hℓ) : CraRigidityData ℓ hℓ
```

工数: **350–500 行**。tier **M（opus）**（cra_hom_ext と CRA-2 の左右逆が簿記の中心・
写経元は cci の左右逆イディオム）。

---

## 4. 問い 4: Kummer 理論との接続 — **判定: A7 の最小範囲に含めない（A6/E4 境界・scope 外）**

精読結果: `KummerCharReal.lean`（M349F）の κ_α(σ)=σ(α)/α は**本物**（抽象 IUTField 上の
実コサイクル）だが、(i) 準同型性は「G が指標値に自明に作用する」仮説 `htriv`（=μ_n⊆K で
σ が μ_n を固定する状況、つまり **G_K が K を固定する絶対 Galois 側の設定**）を外部で受け、
(ii) a の n 乗根 α∈K̄ の存在も外部。一方 A7 の台帳項目は「実円分剛性（実 G_K **加群**上）」
——**cyclotome そのものの G-加群構造と剛性**が主語であり、κ（係数が cyclotome の Kummer 類）
はその**消費者**である。IUT 上の対応でも、円分剛性 [AbsTopIII/EtTh] と Kummer 理論
（theta の Kummer 類・柱 E4／mono-anabelian 復元の Kummer 部・A6）は別項目として台帳化
されている（E complete_note「E4 theta Kummer(主対象が悉く代理…)=0」）。

**よって A7 には含めない**。ただし実円分塔上で本物に閉じられる後続ターゲットを名指しして
おく（着手時は §2(c) 承認 or A6/E4 枠で起票）:
**相対 Kummer の忠実な部分ケース** — K := ℚ(ζ_{3^{ℓ+1}})・α := ζ_{ℓ+1}・a := α³ = ι(ζ_ℓ)・
G := Gal(ℚ(ζ_{3^{ℓ+1}})/ℚ(ζ_{3^ℓ}))（ι の像を各点固定する実部分群——**新機構: 相対 Galois
部分群**が必要）に対し κ_α : G → μ₃ を実構成する。`htriv`/`hfix` が本物の定理として落ち、
M349F の外部仮説 2 本を部分ケースで discharge する。工数 400 行級・A7 でなく A6 の
status に寄与する見込み。本設計の 4 ファイルには含めない。

---

## 5. 問い 5: 最小 complete_pct 前進ステップ — 分割・寄与見積り・優先順位

台帳: A7 = weight 12・status **0**。柱 A Σ(w·s) = 39.8/100 → 40。
丸めは `tools/compute_complete_pct.py` の round(Σ(w·s))（A3-m4 設計 §5 と同じ換算）:

| A7 status | 柱 A 数値 | round | 柱%の動き |
|---|---|---|---|
| 0（現在） | 39.8 | **40** | — |
| 0.2（A7a のみ） | 42.2 | **42** | **+2** |
| 0.3（A7a+A7c） | 43.4 | **43** | +3 |
| 0.4（A7a+A7c+A7b） | 44.6 | **45** | +5 |

**A7 は weight 12・status 0 のため、本物の第一歩でも柱%が確実に動く**（A7a 単独で +2 見込み
——A3 M4a のときのような「status は動くが柱%据え置き」ではない）。ただし以下の見積りは
**保守値・最終確定は独立監査**。過大主張しない: 到達しても A7 ≤ 0.4–0.45 で打ち止め
（上限理由は §7——円分切片限定・p=3・K̄/幾何的 cyclotome 不在・mono-theta 剛性未達）。

| 分割 | 内容（新規ファイル） | 実 IUT を進めるか（自問） | status 見積り（保守） | 工数・tier | 依存 |
|---|---|---|---|---|---|
| **A7a** | cmr＋cgar（実 μ_{3^ℓ} 群・実 Gal 作用・非自明 χ(σ₂)=2・M322F/M334F の主語/入力昇格） | **Yes**——complete_note の「抽象GK+ℤ/n模型」を名指しで置換。M322F 正直申告（非自明 χ の実降下は後続）の discharge | 0 → **0.15–0.2**（実だが各レベル・作用の枠は M322F 再利用） | cmr 300–450 [**M**]＋cgar 250–400 [**M**] | cmr→cgar 直列 |
| **A7c** | cra（自己準同型分類・Gal≅Aut(μ)・χ の canonical 性・不定性の正直定理） | **Yes**——台帳項目名の「剛性」本体。作用の χ 決定（M322F）を超える「任意自己準同型の分類＋Galois で尽くされる」を実で | 0.2 → **0.3**（±0.05） | cra 350–500 [**M**] | cgar→cra |
| **A7b** | tmz（T=ℤ₃(1)=lim 実μ・遷移の ι∘t=cube 証明書・G 作用・作用=χ 冪・χ≅ℤ₃^× は cli 再利用） | **Yes**——「実 G_K 加群」の極限形。ℤ₃(1) が実 G-加群として立つ | 0.3 → **0.4**（±0.05） | tmz 450–650 [**M**・tmz_act_compat に fable スポット 1 予約] | cgar＋cli/zps/ctl→tmz |

**優先順位（結論）**: **cmr → cgar →（cra ∥ tmz）**。

1. **cmr**［M・opus］——全ての前提。CMR-2 の pow 三者橋が本体。
2. **cgar**［M・opus］——A7a 完成点。**ここで初めて A7 status 申告→独立監査**（0.15–0.2・
   柱A% 40→42 見込み）。
3. **cra**［M・opus］と **tmz**［M・opus・fable スポット 1］——cgar 後に**並列可**
   （互いに依存しない）。安い cra を先に確定させたければ cra→tmz の直列でも可。
4. 任意の tier-S 枠埋め候補（§2 完全証明ファースト規則の自問つき）: cgar 実例の
   M404F `cgm_exists` への実引数代入・M443F cid の外部仮定（hζl/hdist）への `cmrMu` 供給。
   いずれも**単体では A7 status を動かさない**ため、並列枠が余る場合のみ・ヘッダに
   「complete_pct 単体寄与なし」を明記して投入（水増しで枠を埋めない）。

5 並列編成案（CLAUDE.md tier 配分規則準拠）:
- **ラウンド 1**: cmr [opus] 1 本（A7 枠は依存の都合で 1 本のみ——残り枠は他柱の
  complete_pct 前進案件で埋める）。
- **ラウンド 2**: cgar [opus]＋（残枠は他柱）。完了時 A7a 監査。
- **ラウンド 3**: cra [opus]＋tmz [opus・fable スポット待機]（A7 で 2 枠・残 3 枠は他柱）。
  完了時 A7 再監査（0.4 級申告）。

総工数見積り: **1350–2000 行・実装 3 ラウンド**。fable は tmz_act_compat の詰まり解決のみに
限定（新イディオムは無し——全て cci/cli/zps の確立イディオムの写経＋M322F 抽象枠の実充填）。

---

## 6. 実装規約（全 4 新規ファイル共通・A3-m4 設計 §6 を継承・opus への指示に含める）

- **ヘッダ二軸**: 分類 [実／昇格(a)] と complete_pct 影響を 1 行明記。cmr は「A7a の必要部品
  （単体では status 未設定・cgar 到達で親が反映）」、cgar は「A7a 本体・監査確定待ち」、
  cra/tmz は「A7c/A7b・同上」。**置換対象の代理/模型（M322F 実例・M334F 入力・
  complete_note 文言）をヘッダで名指し**する（§2(a) 昇格の証跡）。
- **既存モジュールの改変禁止**: `CyclotomicRigidity.lean` 等の抽象定理・正直申告は
  **消さない・弱めない**。昇格は「実インスタンスの供給」で行う（M322F ヘッダ自身が
  「作用データを供給すれば χ・準同型・剛性は即座に本物で回る」と設計している通り）。
- **禁止タクティク**: simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp 不使用。**新規 Classical.choice 禁止**（`#print axioms` =
  [propext, Quot.sound] 維持）。witness は全てデータ: log=`ctmFind`（fuel 走査）・
  逆元=`zpuInvL`/`y^{3^ℓ−1}`・整合族=閉じた式。∃ の使用は Prop ゴール内のみ
  （cra_gal_realize・tmz_proj_surjective）。
- **3^ℓ 算術**: omega に冪を渡さない（`zpu_pow_pos`/`zpu_pow_dvd`/`ctm_pow3_split` 経由）。
- **defeq の予防線**: (i) ctmZeta の型 GefNF vs (cteField).carrier、(ii) (ctmK).ring vs
  (cteField).toCRing、(iii) galoisGroupGrp の one/mul の val（fieldAutId/fieldAutComp）——
  いずれも実装冒頭に show/検算 def で固定。通らなければ付替補題 1 本ずつ（各 +20 行・
  設計変更なし）。
- **新規ファイルのみ**・共有ファイル（IUT.lean/build.sh/dashboard/graph 系/target_ledger）
  不更新（親が統合・`tools/gen_graph.py` 再生成も親）。prefix cmr/cgar/tmz/cra
  （本日 grep で未使用確認済み）。

## 7. 正直な限定（本設計自身のもの・消さない・弱めない）

1. 本ドキュメントは設計であり complete_pct を動かさない。status 数値は保守的見積りで、
   確定は独立監査（AUDIT_RUBRIC 準拠・reaudit-A 系）。
2. **円分切片限定**: 実現する G は Gal(ℚ(ζ_{3^ℓ})/ℚ) と Gal(ℚ(ζ_{3^∞})/ℚ)（G_ℚ の可解商）
   であって、**実絶対 Galois 群 G_K そのもの・実局所体 G_{K_v} 上の円分指標ではない**
   （IUT の実際の使用文脈は局所体・A2/A3 後続）。p = 3・基礎体 ℚ 固定。
3. **μ は円分体自身の中の μ**: 分離閉包 K̄ の μ_n（本来の G_K-加群 μ_{n}(K̄)）でも、
   π₁ の幾何的 cyclotome（Λ = π₁ の捻れ部分）でもない。「実 G_K 加群上」の忠実な部分
   ケース（G が μ を含む体の Galois 群として作用）に留まる。
4. **ℤ₃(1) の限定**: tmzLimit は「逆極限としての群＋G 作用」であり、(i) 遷移は指数読み替え
   （実 3 乗写像であることは ι∘t=cube の証明書で担保・単一の周囲体 K̄ 内の冪写像ではない）、
   (ii) **ℤ₃ スカラー作用（位相 ℤ₃-加群構造）は形式化しない**（群＋作用＋χ 記述まで）、
   (iii) Tate「捻り (1)」の名は χ 作用の実装により正当化されるが、コホモロジー的捻りの
   一般論は無い。
5. **IUT の円分剛性本体（mono-theta 環境の剛性・[EtTh]）は scope 外**: 本設計が閉じるのは
   「円分体の G-加群構造は χ で一意決定・χ は同型・自己同型は Galois で尽くされる・χ は
   同一視の選択に依らない」まで。**(ℤ/3^ℓ)^×（極限で ℤ₃^×）不定性は純 Galois 加群レベルでは
   残存する**ことを定理（cra_indeterminacy）として正直に固定する。この不定性の消去
   （テータ環境の cyclotome と基礎体の cyclotome の canonical 同一視）は柱 E/D 後続であり、
   A7 を本設計のみで 1 にはしない（上限 0.4–0.45 目安・監査確定）。
6. リスク 2 点: (a) tmz_act_compat（作用×遷移の compat 正方形）の指数簿記——fable スポット
   1 予約・fallback は A7b を「単段 compat＋成分作用のみ（natSystem 詰めを保留）」の
   0.35 級申告に留める。(b) Grp.pow（左乗算反復）と rpow（右乗算反復）の橋——可換性で
   回る見込みだが、CMR-2 で詰まった場合は cycRig_pow_* 側の向きに合わせた補助補題を
   cmr 内に追加（+30 行・設計変更なし）。
