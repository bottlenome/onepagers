# A6 詳細化ラウンド: mono-anabelian 円分体復元の「正準性（canonicity）」昇格設計（2026-07-11）

- 種別: **詳細化ラウンド（設計ドキュメントのみ・Lean 実装なし）**
- 対象: `target_ledger.json` 柱A **A6**「mono-anabelian 復元（π₁ から体/環を復元・実）」weight **14**・現 status **0.55**
- 主要成果の分類（本設計が指示する後続実装の分類）: **[実／昇格(a)＋本物建設(b)]**
- **complete_pct 影響**: A6 0.55 → 見込み 0.62（監査確定）。crr の「薄い discharge」（χ と作用が同一対象由来・復元の一意性未証明）を、A7d/A7e（tme/tmi）の実剛性機構で**復元の正準性定理**（∀同一視の分類・実 ℤ₃^× 上のちょうど torsor）へ昇格する。柱A 51 → 52 の丸め境界は §5 で厳密計算。
- 判定方針: 全て def/theorem の**本体**精読による（ヘッダ主張は不採用）。敵対的デフォルト＝模型。

---

## §1 現状実測 — crr（A6・0.55）が実際に何を復元し、なぜ「薄い」のか

### 1.1 crr が実際に持っているもの（本体精読）

`IUT/CyclotomeRecoveryReal.lean`（crr）の実体は次の通り:

1. **復元機構の実主語化**: M334F `cycRec_mu_from_chi`（χ から μ̂=(ℤ/n, χ捻り) を復元する抽象機構）に、実円分指標 `cgarRecChar ℓ hℓ`（実 Gal(ℚ(ζ_{3^ℓ})/ℚ) の実 μ_{3^ℓ}=`cmrMu` への実作用 `cgarAct` から抽出・σ₂→2 で非自明）を代入して `crrRecovered`（crr:142-144）を得る。
2. **G-同変同型 1 本**: `crrIso := cidIso (cycMuStd 3^ℓ) (cmrMu ℓ hℓ) rfl`（crr:179-181）は復元 μ̂ の台と実 μ_{3^ℓ} の間の**特定の 1 つの**同型で、`crr_iso_equivariant`（crr:194-204）が M443F 一般定理 `cid_galois_equivariant` への実主語代入で G-同変性を与える。
3. **外部仮説の discharge**: `crr_geo_compatible`（crr:223-233）は M334F の外部仮説 `cycRecGeoCompatible`（「真の幾何作用が χ 捻りに一致」）を型どおり定理化する。ただし「真の幾何作用」`crrGeoAct`（crr:211-215）は `cgarAct` を `crrIso` で読み戻したもの。

### 1.2 なぜ 0.55 で止まっているか（前回監査の thin 判定の正確な内容）

`audit/reaudit-A6-real-cyclotome-recovery-2026-07-10.md` 核心判定（本設計者も本体精読で追認）:

> `crrGeoAct`（真の幾何作用 side）と χ=`cgarRecChar` は**同一の実 Gal 作用 `cgarAct` 由来**であり（χ は作用の円分指数として抽出）、discharge の実質は「巡回群 μ 上の実 Gal 作用＝その作用から取った指標での冪」という **M322F 円分剛性の再表現**である。

薄さの構造を分解すると、A6 の主語「mono-anabelian **復元**」に対して crr が欠いているのは次の 2 点:

- **(G1) 正準性/一意性の不在**: crr は復元 μ̂ と実 μ の同一視を**1 本**（`crrIso`）構成しただけで、「その同一視が正準（canonical）である」——すなわち **G-同変同一視の全体がどれだけあるか・どの不定性でちょうど尽くされるか**——を一切述べていない。χ と作用が同一対象由来である以上、「1 本ある」ことはほぼ簿記であり、mono-anabelian 復元の実内容（復元結果が選択に依らず一意に決まる、決まらないなら不定性が正確に何かを特定する）が抜けている。
- **(G2) 副有限（極限）レベルの不在**: crr は各 ℓ 固定の有限切片 Gal(ℚ(ζ_{3^ℓ})/ℚ)・μ_{3^ℓ} 上で閉じており、復元対象の極限（ℤ₃(1) 相当）・極限 Galois 群 Gal(ℚ(ζ_{3^∞})/ℚ)=`ctlProfinite` 上の復元は存在しない。crr 正直な限定 (iii) が「**A6 上限は 0.6（完全な副有限・K̄ レベルは後続）**」と自ら明記している通り。

### 1.3 A6 資産表（本体基準の実/代理判定）

| 資産 | ファイル | 実体（本体） | 判定 |
|---|---|---|---|
| `cycRecCharacter`/`cycRec_mu_from_chi`/`cycRec_rigidity_iso` | CyclotomeRecovery.lean (M334F) | 抽象 GK・抽象 χ 上の復元機構。作用則は本物の証明 | 機構は実・主語は抽象（surrogate 入力） |
| `cycRecGeoCompatible`/`cycRec_geo_recovery_hypothesis` | 同上 | 外部仮説 Prop＋仮説適用のみ（「決して導出しない」） | 仮説枠 |
| `cycRecGaloisCyclotome` | 同上 (M334F-9) | 実 G_ℚ・**trivial χ≡1**（恒等作用）実例 | 実だが自明 |
| `crrRecovered`/`crr_recovered_nontrivial` | CyclotomeRecoveryReal.lean | 実非自明 χ（σ₂→2）からの復元・非自明性分離 | 実 |
| `crrIso`/`crr_iso_equivariant` | 同上 | 復元 μ̂ ≅ 実 μ_{3^ℓ} の **1 本の** G-同変同型 | 実・ただし一意性なし (G1) |
| `crr_geo_compatible`/`crr_geo_recovery` | 同上 | 外部仮説の実 discharge・ただし χ と幾何側が同一 `cgarAct` 由来 | 実・薄い（前回監査 thin 判定） |
| 極限レベルの復元対象・復元同一視 | — | **存在しない** (G2) | 未着手 |
| 復元同一視の一意性/分類定理 | — | **存在しない** (G1) | 未着手 |

### 1.4 A7 が新規に提供した機構（tme/tmi・監査確定 A7=0.40）

- `tme_endo_pow`/`tme_char_compat`/`tme_endo_ext`（TateModuleEndo.lean）: **任意の**抽象 Hom f : T→T（T=ℤ₃(1)=`tmzLimit`・実 μ 塔の真の逆極限）が整合指数族 `tmeChar f` で完全分類される。鍵は可除性フィルトレーション `tme_ker_pow` による**自動降下**（連続性仮定なし）。
- `tmi_aut_classify`＋`tmi_units_inj`（TateModuleIndeterminacy.lean）: 両側可逆な f はちょうど 1 つの実単元 u ∈ `zpsLimit`（実 ℤ₃^×）から来る＝**Aut(ℤ₃(1)) ≅ 実 ℤ₃^× の消去形同型**。
- `tmi_endo_gal_commute`: 任意の f が実 Galois 作用 `tmzActHom s` と可換＝**同変性条件は End(T) 上で空**。
- `tmi_act_char`: Galois 作用の分類指数族＝χ（`cliChar`）。

この「∀f を分類する」機構が、crr に欠けていた (G1)「**任意の**同一視の分類＝正準性」を初めて可能にする。A7 以前は「1 本の iso の構成」しか書けなかった（∀Hom を統制する定理が無かった）。

---

## §2 中心判定 — 復元を正準にする最小の実新規内容は何か

### 2.0 A6 と A7 の主語の区別（二重計上判定の基準・先に固定する）

- **A7 の主語（既計上・weight 12・0.40）**: 固定された 1 つの実対象 T=ℤ₃(1) の **End(T)/Aut(T)**——「T の自己準同型・自己同型の群がどう分類されるか」。
- **A6 の主語（本設計）**: **復元**——π₁/Galois 側データ（χ）から円分体を復元する写像と、**復元結果と本物の間の同一視の空間 Isom_G(T̂, T)**。「復元は正準か（選択に依らないか）・依らないならどの不定性でちょうど尽くされるか」。

Isom(T̂,T) は群でなく（空間として）Aut(T)-torsor であり、T̂ 自体（χ 捻りで組んだ復元側極限対象）は A7 のどこにも存在しない。A7 の Aut 分類を**補題として消費**して Isom を分類するのは、tme が `cra_endo_pow`（レベル剛性）を消費して極限分類を建てたのと同じ「正当な再利用」パターン（A7 監査 reaudit-A7-tatemodule-endo-indet §2.3 が明示的に是認）。**二重計上になるのは**: 主語が `Hom tmzLimit tmzLimit` のままの定理を A6 名義で再輸出すること（本設計はこれを実装者に明示的に禁止する・§4.2）。

### 2.1 候補 A（採用）: 復元円分体の極限化＋同一視空間の torsor 正準性

**主張したい数学**: 実非自明 χ から mono-anabelian に復元した円分体の極限 T̂ = lim μ̂_{3^{n+1}}（χ 捻り ℤ/3^{n+1} の逆極限・G=`ctlProfinite` 作用付き）は実 T=ℤ₃(1) と G-同変に同型であり、**その同一視は実 ℤ₃^×=`zpsLimit` の分だけ・ちょうどその分だけ不定**:

1. （存在）明示同一視 Ξ : T̂ ≅ T（G-同変・両側逆つき）が構成できる。
2. （★分類=正準性）**任意の**両側可逆 Hom Φ : T̂ → T に対し、ちょうど 1 つの u ∈ `zpsLimit` があって Φ = (tmiFromUnits u) ∘ Ξ。
3. （★正確性・正直方向）逆に任意の u に対し (tmiFromUnits u) ∘ Ξ も **G-同変な**同一視である（`tmi_endo_gal_commute` により同変性は torsor を一切絞らない）。ゆえに Isom_G(T̂,T) ≅ `zpsLimit`（消去形）。純 Galois 加群データからの復元の正準性はここが理論上の上限であり、これ以上絞るのは mono-theta 剛性（柱E/D・status 0 のまま）の仕事——という**正直な線引きを定理の形にする**。

**thin 判定 (G1) への正面回答になる理由**: crr の薄さは「χ と作用が同一対象由来ゆえ、1 本の iso はほぼ簿記」だった。候補 A の中核定理 2 は **∀Φ（cgarAct から作られたとは限らない任意の同一視）** を量化する。∀ 形は「同一対象由来」の循環を型レベルで遮断する——Φ は抽象 Hom であり、それが必ず u·Ξ の形になることは A7d の可除性フィルトレーション・自動降下を経由して初めて言える本物の内容。同時に (G2)（副有限レベル不在・0.6 上限の名指し根拠の半分）を T̂/Ξ の建設で discharge する。

**新規 Lean 内容（A7 に存在しないもの）**:
- T̂ そのもの: 復元側の塔 `zmod (3^{n+1})`（χ 捻り作用つき）を `zmodTrans` 遷移で逆系化し `limitGrp` で極限化した対象。crr は各 ℓ 固定・M334F は抽象 n 固定で、**復元側の極限対象は柱A のどこにも無い**。
- 塔の貼り合わせ: 復元指標の遷移整合（χ_{j} を `zmodTrans` で落とすと χ_i・`cli_char_restr`＋Int/Nat cast 簿記）と、捻り作用の遷移同変性（`cycRec_action_change_n` イディオムの実 χ 系列への適用）。
- Ξ の遷移整合: レベルごと `crrIso`（=cidIso）が `zmodTrans` と `tmzT` の四角を可換にすること（`tmz_find_pow`/`cra_pow_reduce` 簿記）。
- Isom の torsor 分類（∀Φ 量化・上記 2・3）。

**分類**: T̂/Ξ の建設は **§2(b) 本物の先行建設**（実 μ 塔極限 T に対する復元側極限と実同一視）＋ crr 限定 (iii) の副有限部分の **§2(a) 昇格**。torsor 定理は A6 の主語（復元の正準性）の新定理で、A7 の再ラベルではない（消費のみ）。

### 2.2 候補 B（不採用・headline としては A7/cra の再消費）: χ の正準性（選択非依存）

「復元入力 χ 自体が生成元の取り方に依らない」——だが**レベル ℓ ではすでに `cra_char_canonical`（CRA-4・A7c で計上済み）が証明済み**（任意の原始根 y' で σ(y')=y'^{χ(σ)}）。極限版を A6 名義で立てても、実体は cra 定理の成分ごと再輸出＋极限束ねであり、AUDIT_RUBRIC の「代理/橋（再輸出・束ね）＝算入しない」に該当する危険が高い。**headline にしない**。ただし候補 A の内部で「復元作用の tme 分類指数＝`cliChar`」（`tmi_act_char` の T̂ 側移送・1 定理）を橋として置くのは可（新規内容は移送の可換図のみ・小）。

### 2.3 候補 C（不採用・単体では A7 そのもの）: 復元写像が実 Galois 作用と一意に可換

「復元が実 Galois 作用と可換であることが同一視を一意化する」——**しない**、が A7e の実証明済み内容（`tmi_endo_gal_commute`: 同変性は End(T) 上で空）。この事実を単体で A6 名義にするのは主語が End(T) のままの再ラベル＝二重計上。ただし候補 A の定理 3 の**内部**では、この空性こそが「torsor は G-同変性で絞れない＝不定性はちょうど ℤ₃^×」という正直な正確性宣言の根拠になる（正しい消費先）。

### 2.4 判定

**候補 A を採用**。候補 B・C は単体では A7 再消費（設計として明示的に却下し、実装者へ§4.2 の禁止事項として渡す）。

---

## §3 選定ステップ — 2 ファイル対（丸め保険つき）

依存が一直線なので実装は 1 エージェント直列（file 1 → file 2）。2 ファイルに割るのは監査に対する成果の可分性（file 2 が万一「transport」と減点されても file 1 単独で (G2) を discharge する）のため。

### 3.1 File 1: `IUT/CyclotomeRecoveryLimit.lean` — prefix `crl`（衝突なし・grep 確認済み）

**内容**: 復元円分体の極限 T̂ と実 T=ℤ₃(1) の G-同変明示同一視 Ξ。約 280 行・tier **M (opus)**。

imports: `IUT.CyclotomeRecoveryReal`, `IUT.TateModuleZ3`, `IUT.CyclotomicLimitIso`

公開名（正確な形）:

```
-- CRL-0: 復元側逆系と極限（zmodSystem は割り切り添字なので natSystem で新設）
def crlG (n : Nat) : Grp := zmod (3 ^ (n + 1))
def crlT {i j : Nat} (h : i ≤ j) : Hom (crlG j) (crlG i)   -- zmodTrans (zpu_pow_dvd …)
theorem crl_t_self / crl_t_comp                             -- Quot.ind + rfl
@[reducible] def crlSystem : InverseSystem := natSystem crlG crlT crl_t_self crl_t_comp
def crlLimit : Grp := limitGrp crlSystem                    -- ★T̂ = 復元 ℤ₃(1)

-- CRL-1: 復元指標の遷移整合（本ファイルの貼り合わせ核・実新規）
theorem crl_char_compat {i j : Nat} (h : i ≤ j) (s : ctlProfinite.carrier) :
    (crlT h).map ((cgarRecChar (j+1) (by omega)).chi (s.val j))
      = (cgarRecChar (i+1) (by omega)).chi (s.val i)
-- 証明経路: cgarRecChar.chi σ = Quot.mk (modCong 3^ℓ) (cycRigExp … σ : Int)（cycRigChar 定義）
--   ＋ cgar_exp_eq（= ctr_charG）＋ cli_char_restr（E_i = E_j % 3^{i+1}・s.property h 経由）
--   ＋ Quot.sound / quot_exact の Int/Nat cast 簿記（crr_nat_mod_toNat イディオム）

-- CRL-2: ★T̂ 上の復元 G 作用（成分ごと χ 捻り・tmzActHom の復元側鏡像）
def crlActHom (s : ctlProfinite.carrier) : Hom crlLimit crlLimit
-- map compat は crl_char_compat ＋ cycRec_zmodTrans_mul、map_mul は crr_zmodMul_add
theorem crl_act_one / crl_act_mul                           -- cgarRecChar.chi_one / chi_hom 成分ごと
structure CrlGModule / def crlGModule                       -- TmzGModule の復元側対応物

-- CRL-3: ★明示同一視 Ξ とその G-同変性
theorem crl_iso_compat {i j} (h : i ≤ j) (x : (crlG j).carrier) :
    (tmzT h).map (cmuMap (cycMuStd (3^(j+1)) _) (cmrMu (j+1) _) x)
      = cmuMap (cycMuStd (3^(i+1)) _) (cmrMu (i+1) _) ((crlT h).map x)
-- tmz_find_pow / cra_pow_reduce / ctm_pow_mod 簿記（tme_t_apply イディオム）
def crlIso : Hom crlLimit tmzLimit                          -- ★Ξ（成分ごと crrIso=cidIso）
def crlInv : Hom tmzLimit crlLimit                          -- 成分ごと逆向き cmuMap（compat は対称）
theorem crl_iso_leftinv : ∀ y, crlInv.map (crlIso.map y) = y      -- cid_iso_leftinv 成分ごと
theorem crl_iso_rightinv : ∀ y, crlIso.map (crlInv.map y) = y
theorem crl_iso_equivariant (s : ctlProfinite.carrier) (y : crlLimit.carrier) :
    crlIso.map ((crlActHom s).map y) = (tmzActHom s).map (crlIso.map y)
-- crr_iso_equivariant (ℓ := n+1) の成分適用
```

### 3.2 File 2: `IUT/CyclotomeRecoveryCanonicity.lean` — prefix `crc`（衝突なし・grep 確認済み）

**内容**: ★A6 headline——同一視空間の torsor 正準性。約 200 行・tier **M (opus)**。

imports: `IUT.CyclotomeRecoveryLimit`, `IUT.TateModuleIndeterminacy`

公開名（正確な形）:

```
-- CRC-1: ★正準性（存在）: 任意の可逆同一視は実単元 × Ξ
theorem crc_canonical (Φ : Hom crlLimit tmzLimit) (Ψ : Hom tmzLimit crlLimit)
    (hl : ∀ y, Ψ.map (Φ.map y) = y) (hr : ∀ y, Φ.map (Ψ.map y) = y) :
    ∃ u : zpsLimit.carrier, ∀ y, Φ.map y = (tmiFromUnits u).map (crlIso.map y)
-- 証明: A := ⟨fun y => Φ.map (crlInv.map y), map_mul 合成⟩ : Hom tmzLimit tmzLimit、
--   両側逆 A' := ⟨fun y => crlIso.map (Ψ.map y), …⟩（hl/hr＋crl_iso_left/rightinv の点ごと合成）
--   → tmi_aut_classify A A' → u。Φ.map y = A.map (crlIso.map y)（crl_iso_leftinv）で移送。

-- CRC-2: ★一意性: u は一意
theorem crc_canonical_unique (u v : zpsLimit.carrier)
    (h : ∀ y, (tmiFromUnits u).map (crlIso.map y) = (tmiFromUnits v).map (crlIso.map y)) :
    u = v
-- crl_iso_rightinv で ∀z (tmiFromUnits u).map z = (tmiFromUnits v).map z へ引き戻し → tmi_units_inj

-- CRC-3: ★正確性（正直方向）: 全 torsor 点が G-同変同一視（同変性は torsor を絞らない）
theorem crc_torsor_realize (u : zpsLimit.carrier) :
    (両側逆の存在: tmi_from_units_iso＋crl_iso_*inv の合成) ∧
    (∀ s y, (tmiFromUnits u).map (crlIso.map ((crlActHom s).map y))
          = (tmzActHom s).map ((tmiFromUnits u).map (crlIso.map y)))
-- 同変性: crl_iso_equivariant ＋ tmi_endo_gal_commute（空性の正しい消費先）

-- CRC-4: 橋（小・任意）: 復元作用の分類指数＝χ
theorem crc_act_char (s : ctlProfinite.carrier) (n : Nat) : （crlActHom s を Ξ で移送した
    tmeChar が cliChar に mod 一致——tmi_act_char＋crl_iso_equivariant の可換図 1 枚）

-- CRC-5: capstone（新規証明ゼロ・束ねのみ）＋正直な限定宣言
structure CrcCanonicityData / def crcCanonicityData / theorem crc_scope
```

### 3.3 選択自由（choice-free）戦略

全 witness は閉じた式: torsor の u は `tmi_aut_classify` の witness（各段 `tmeChar f n % 3^{n+1}`・既存の消去形）をそのまま透過。∃ は Prop ゴール内のみ。新規 `Classical.choice` 禁止・禁止タクティク（simp/decide/…）不使用・`3^ℓ` は `zpu_pow_pos`/`zpu_pow_dvd` 経由——tme/tmi/crr と同一の規約を継承。**新イディオム 0**（極限貼り合わせ=tmz、cast 簿記=crr、分類消費=tmi の既確立イディオムのみ）。ゆえに tier M で足りる（詳細化=段階分解は本ドキュメントが済ませた）。

---

## §4 正直な線引き（過大主張の禁止・二重計上境界の明文化）

### 4.1 本ステップがやらないこと（実装ヘッダに必ず書く・消さない・弱めない）

1. **mono-theta 円分剛性（[EtTh]）は依然 0**: 本ステップは ℤ₃^× 不定性を**殺さない**。「復元の同一視空間がちょうど実 ℤ₃^× の torsor」と特定するのみ（CHARACTERIZE, not KILL）。不定性を消すテータ環境は柱E/D 後続。
2. **χ を実 π₁^ét の位相連続指標として抽出する本丸は未**: 復元入力 χ は依然 `cgarAct`（実体自己同型の制限）由来。crr 限定 (ii) を弱めず継承。
3. **幾何側は K̄ の μ でも π₁ の幾何的 cyclotome でもない**: μ 塔は各段別々の実円分体に住む（tmz 限定 (5) 継承）。実数体上の完全 mono-anabelian 復元（AbsTopIII の実主語・体/環の復元）は後続。
4. **p=3・G=Gal(ℚ(ζ_{3^∞})/ℚ) 固定**（G_ℚ の可解商・実 G_K/G_{K_v} でない）。
5. crr の「A6 上限 0.6」正直申告は**消さない**。ただしその根拠 2 本のうち「完全な副有限は後続」を本ステップが discharge するため、新モジュールは自身の限定として「**A6 ≤ 0.65（K̄/幾何 cyclotome・π₁ 連続 χ が未のあいだ）**」を新たに宣言する（既存申告の削除・弱化ではなく並置＋更新宣言。監査が旧 0.6 を維持する可能性は §5 で織り込む）。
6. crr/tmz/tme/tmi/cra の既存正直申告は一切消さない・弱めない。並置＋昇格のみ。

### 4.2 二重計上 vs A7 の境界（監査が必ず突く点・実装への禁止事項つき）

| | A7（既計上 0.40） | 本ステップ（A6 新規） |
|---|---|---|
| 主語 | 固定 T の End(T)/Aut(T)（自己準同型の分類） | **復元側極限 T̂ の存在**・**Isom(T̂,T) の分類**（同一視空間・torsor） |
| 新対象 | なし（T は A7b 既存） | T̂=`crlLimit`（χ 捻り復元塔の極限・柱A に不存在だった）・Ξ=`crlIso` |
| A7 定理の扱い | — | `tmi_aut_classify`/`tmi_units_inj`/`tmi_endo_gal_commute` を**補題として消費**（tme が cra_endo_pow を消費したのと同じ・A7 監査 §2.3 是認パターン） |
| 負担点 | 可除性フィルトレーション・自動降下 | `crl_char_compat`（χ の塔整合）・`crl_iso_compat`（Ξ の遷移整合）・∀Φ 量化の torsor 定理 |

**実装への禁止事項**: (i) 主語が `Hom tmzLimit tmzLimit` だけの定理を新規公開しない（それは A7 の再ラベル）。公開定理は必ず T̂（`crlLimit`）または Isom（`Φ : crlLimit → tmzLimit` 型）を主語に含むこと。(ii) `cra_char_canonical` の極限再輸出を「χ 正準性」として headline 化しない（§2.2 却下済み）。(iii) capstone は束ねのみで新規主張を作らない。

**それでも監査が「file 2 は formal transport」と減点した場合**: file 1 単独でも crr 限定 (iii) の名指し後続「完全な副有限」の discharge（復元の極限化＋極限 G-同変同一視）であり、A6 の実前進として立つ——これが 2 ファイル分割の保険設計。

### 4.3 後続に残るもの（名前つき実ターゲット）

- A6 本丸残: 実数体/実局所体の体・環復元の実主語化（AbsTopIII `cycRec_absTopIII_cyclotome` の trivial 付値を実離散付値へ・柱B 接続）、χ の π₁^ét 位相連続抽出、K̄ レベルの μ。
- A7 側接続残: End(T)≅A2 実 ℤ₃ の環同型（tmi 限定 (4) の名指しターゲット・本設計の範囲外）。

---

## §5 status 見込みと柱A% 算術（丸め境界の厳密計算）

### 5.1 Σ_A 定数の検証（target_ledger.json 実測・2026-07-11 時点）

| item | weight | status | w·s |
|---|---|---|---|
| A1 | 8 | 0.85 | 6.80 |
| A2 | 8 | 0.65 | 5.20 |
| A3 | 12 | 0.75 | 9.00 |
| A4 | 14 | 0.55 | 7.70 |
| A5 | 10 | 0.15 | 1.50 |
| **A6** | **14** | **0.55** | **7.70** |
| A7 | 12 | 0.40 | 4.80 |
| A8 | 12 | 0.57 | 6.84 |
| A9 | 10 | 0.10 | 1.00 |
| Σ | 100 | | **50.54** |

- 現 Σ_A = **50.54** → `compute_complete_pct.py` は `round(50.54)` = **51**（現表示と一致・graph-meta 確認済み）。
- A6 以外の定数 = 50.54 − 14×0.55 = **42.84**。∴ Σ_A(s) = 42.84 + 14·s。

### 5.2 表示 52 の丸め境界

`compute_complete_pct.py` は Python 組み込み `round`（banker's）。**round(51.5) = 52**（52 が偶数側・実行確認済み: `round(51.5)→52`）。よって表示 52 の条件は Σ_A ≥ 51.5:

- s_A6 ≥ (51.5 − 42.84) / 14 = 8.66 / 14 = **0.618571… ≈ 0.6186**
- 台帳粒度（0.01 刻み慣行）での最小値は **s_A6 = 0.62** → Σ_A = 42.84 + 8.68 = **51.52** → round = **52** ✓

### 5.3 見込みシナリオ（正直に）

| 監査結果 | Σ_A | 表示 | 備考 |
|---|---|---|---|
| 0.62（設計目標） | 51.52 | **52** | (G1)+(G2) 両 discharge・∀Φ 正準性を full credit |
| 0.60 | 51.24 | 51 | 旧 0.6 上限を尊重（K̄ 未のため）・十分あり得る |
| 0.58 | 50.96 | 51 | file 2 を transport と減点した場合 |
| 0.55 据置 | 50.54 | 51 | 全部 A7 再消費と判定（§4.2 の境界設計で防ぐが 0 でない） |

**0.62 の根拠**（監査への提示材料・数値確定は独立監査）: 質的前進 2 本——(1) 復元の副有限化（crr 0.6 上限の名指し根拠の半分を正面 discharge）、(2) 「1 本の同一視」→「全同一視の消去形分類（ちょうど実 ℤ₃^× torsor）」＝ thin 判定 (G1) の正面解消（∀Φ 量化で「同一対象由来」循環を遮断）。一方 K̄・π₁ 連続 χ・環復元は未のため 0.65 以上は主張しない。**下振れ（0.58–0.60 → 表示 51 のまま）は想定内であり、その場合ラウンド報告は「A6 実前進・柱A 表示は横這い」と正直に書く。**

---

## §6 実装計画（親向け）

1. **実装枠**: opus（tier M）×1、file 1 → file 2 直列（file 2 は file 1 に依存・並列不可）。新規ファイル 2 個のみ作成・共有ファイル不触。行数目安 280+200。手詰まりスポットが出たら本体（親/fable）が HELP 解決に限定介入（tier 規約どおり）。
   - 予見リスク最大点: `crl_char_compat` の Int/Nat cast 簿記（`cycRigChar`=Quot.mk(Int cast) vs `cliChar`=Nat subtype の突き合わせ）。イディオムは crr_nat_mod_toNat＋quot_exact＋cli_char_restr で全部既存。ここで詰まったら fable スポット。
   - 第 2 リスク: `crlInv` の compat（逆向き cmuMap の遷移整合）。対称簿記だが `cycMuStd.log` の toNat が絡む。
2. **同ラウンドの残 4 並列枠**: 本設計の範囲外（親が別途 complete_pct 優先で選定。枠埋めの骨格追加は §2 規約により不可）。
3. **親の統合作業（実装完了後に一括）**:
   - `IUT.lean` に 2 import 追記・`build.sh` 登録・フルビルド＋`#print axioms`（propext/Quot.sound のみ確認）。
   - `tools/gen_graph.py` の `PILLAR` 辞書に `CyclotomeRecoveryLimit`/`CyclotomeRecoveryCanonicity` → 'A' を追記・`python3 tools/gen_graph.py` 再生成。
   - **独立監査を発注**（opus・敵対的・AUDIT_RUBRIC・自己申告非共有）。監査には §4.2 の境界表を渡さない（本体 .lean のみ）。
   - 監査確定後: `target_ledger.json` A6 status・`graph-meta.json` pillars.A.complete_pct/complete_note・`dashboard.md` 二軸表を監査値で更新（0.62 なら柱A 52・それ未満なら 51 のまま正直記載）。コミット。
4. **ラウンド報告**: 主指標 complete_pct（A6 の動き・柱A 表示の 51/52）・副指標 progress_pct。tier 配分（M×1）を明記。

---

*本ドキュメントは詳細化ラウンドの成果物であり Lean 実装を含まない。判定はすべて対象 .lean の def/theorem 本体精読による（crr 全文・M334F 全文・tme/tmi 全文・cra CRA-3〜6・tmz TMZ-7〜10・cgar 全文・Profinite InverseSystem/limitGrp/zmodTrans・cli_char_restr・監査 2 通・台帳/丸めツール実測）。*
