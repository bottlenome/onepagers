# 独立敵対再監査: A6 円分体復元 canonicity（crl + crc）（2026-07-11）

- 監査者: 独立・敵対的（親の自己申告・設計 doc `A6-cyclotome-recovery-canonicity-detail-2026-07-11.md`・ヘッダ `[実/…]` 主張・dashboard/report 自己分類は非採用。def/structure/theorem 実体のみで判定）
- 対象項目: `target_ledger.json` 柱A **A6**「mono-anabelian 復元（π₁ から体/環を復元・実）」weight 14
- 前回 status: **0.55**（reaudit-A6-real-cyclotome-recovery-2026-07-10.md・thin-discharge 判定=(G1) canonicity 不在＋χ と作用が同一 cgarAct 由来ゆえ 1 本の iso はほぼ簿記／(G2) 完全な副有限は後続＝0.6 cap の一因）
- 契機: 2 新規モジュール `IUT/CyclotomeRecoveryLimit.lean`（crl）と `IUT/CyclotomeRecoveryCanonicity.lean`（crc）が (G1)(G2) を discharge したとの主張。設計見込み A6 0.55→0.62。

## 判定（監査者独自）

**A6 status 0.55 → 0.58（+0.03・小幅上げ）。柱A complete_pct 51 据え置き**（Σ_A = 42.84 + 14×0.58 = 50.96 → banker's round 51）。
設計目標 0.62（＝柱A 52）は採らない。理由: 新規実質は crl の副有限レベル復元（real）に集約され、headline の crc canonicity は A7（既計上 0.40）の transport ゆえ full credit しない。

## 0. 検証方法（自走・親申告に依拠せず）

- `export PATH="/root/lean4/bin:$PATH" && bash build.sh` フル実行。
- crl/crc の Lean 定義本体を全文精読。依存の A7 実基盤（tmi/tme）・crr・tmz も精読。
- A6 load-bearing 13 対象の `#print axioms` を**監査者自作 scratch（IUT/AxA6Scratch.lean・`lake env lean` で独立実行）**。実行後 scratch/olean 削除・git clean。

### 検証結果（自走証跡）

- **`bash build.sh` → `OK: all theorems verified, no sorry.`（EXIT=0）**。末尾抜粋:
```
'IUT.crlLimit' depends on axioms: [propext, Quot.sound]
'IUT.crl_char_compat' depends on axioms: [propext, Quot.sound]
'IUT.crlIso' depends on axioms: [propext, Quot.sound]
'IUT.crl_iso_leftinv' depends on axioms: [propext, Quot.sound]
'IUT.crl_iso_equivariant' depends on axioms: [propext, Quot.sound]
'IUT.crc_canonical' depends on axioms: [propext, Quot.sound]
'IUT.crc_canonical_unique' depends on axioms: [propext, Quot.sound]
'IUT.crc_torsor_realize' depends on axioms: [propext, Quot.sound]
'IUT.crc_scope' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```

- **監査者自作 #print axioms（13/13 = [propext, Quot.sound] のみ）**:
```
'IUT.crlLimit'             depends on axioms: [propext, Quot.sound]
'IUT.crl_char_compat'      depends on axioms: [propext, Quot.sound]
'IUT.crlActHom'            depends on axioms: [propext, Quot.sound]
'IUT.crlIso'               depends on axioms: [propext, Quot.sound]
'IUT.crl_iso_leftinv'      depends on axioms: [propext, Quot.sound]
'IUT.crl_iso_rightinv'     depends on axioms: [propext, Quot.sound]
'IUT.crl_iso_equivariant'  depends on axioms: [propext, Quot.sound]
'IUT.crc_canonical'        depends on axioms: [propext, Quot.sound]
'IUT.crc_canonical_unique' depends on axioms: [propext, Quot.sound]
'IUT.crc_torsor_realize'   depends on axioms: [propext, Quot.sound]
'IUT.crc_act_char'         depends on axioms: [propext, Quot.sound]
'IUT.crcCanonicityData'    depends on axioms: [propext, Quot.sound]
'IUT.crc_scope'            depends on axioms: [propext, Quot.sound]
```
**Classical.choice / sorryAx は 13 対象すべての推移的閉包に皆無。** 禁止タクティク未使用。scratch/olean 削除・git clean 確認。

## 1. 構造化ルーブリック出力

### crl = `IUT/CyclotomeRecoveryLimit.lean`
- **classification**: real（副有限レベルの genuine 新規建設）
- **principal_object**: crlLimit = T̂ = χ 捻り復元塔 `crlG n = zmod (3^{n+1})`（`zmodTrans` 遷移）の逆極限 `limitGrp crlSystem`＋G-同変両側逆つき明示同一視 Ξ=`crlIso : Hom crlLimit tmzLimit`。
- **is_it_a_stand_in**: 半分 yes だが A6 の性質上許容。担体 crlG n=zmod(3^{n+1}) は標準模型 ℤ/3^{n+1}（実 μ でない）——ただし mono-anabelian 復元では「復元された対象」は本来抽象再構成であり、それを実 μ 塔 tmzLimit と G-同変同一視する（Ξ）ことが内容。crlLimit と Ξ は柱A に不在だった新主語（crr は各 ℓ 固定切片で停止）。
- **self_declared_external**: なし（`_model_scope` で核対象を外部化していない）。honest 限定 (i)-(vi) は scope 明示。
- **moves_complete_pct**: yes（副有限レベルの復元対象＋G-同変同一視＝crr の (G2) 0.6-cap 理由を副有限で discharge）。
- **evidence**: `crlLimit`(84)／`crl_char_compat`(95・cli_char_restr＋cast 簿記の実証明・非空虚)／`crlActHom`(121・χ捻り G 作用)／`crlIso`(235)＋`crl_iso_leftinv`(323)/`crl_iso_rightinv`(334)（cid_iso_leftinv/rightinv の成分適用・両側逆）／`crl_iso_equivariant`(347・crr_iso_equivariant 成分適用・G 同変）。

### crc = `IUT/CyclotomeRecoveryCanonicity.lean`
- **classification**: surrogate/橋（A6 主語だが数学的エンジンは A7 transport）
- **principal_object**: 同一視空間 Isom_G(T̂,T)=`Φ : Hom crlLimit tmzLimit` の torsor 分類（存在 crc_canonical・一意 crc_canonical_unique・実現 crc_torsor_realize）。
- **is_it_a_stand_in / re-export**: **substantially A7 transport**。全公開定理の数学的エンジンが A7 tmi_*:
  - `crc_canonical`(86): A := Φ∘crlInv を bare tmzLimit endo の**局所項**として作り `tmi_aut_classify`（A7）を適用・`crl_iso_leftinv` で移送。
  - `crc_canonical_unique`(114): `crl_iso_rightinv` で引き戻し `tmi_units_inj`（A7）。
  - `crc_torsor_realize`(133): `tmi_from_units_iso`（A7）＋`tmi_endo_gal_commute`（A7・同変性は End 上で空）＋crl の Ξ 諸性質。
  - `crc_act_char`(175): `crc_transport_eq`＋`tmi_act_char`（A7）。主語は `crlActHom` を含む（A6 主語）。
  固定 iso Ξ が存在する以上 Isom(T̂,T)↔Aut(T) は compose-with-fixed-iso の**自明全単射**で、crc は A7 の Aut(T)≅ℤ₃^× を超える数学内容を持たない。
- **self_declared_external**: なし。honest 限定 (1)-(6)＝CHARACTERIZE not KILL・χ 依然 cgarAct 由来・K̄/体復元は後続。
- **moves_complete_pct**: 部分的 no（新規実対象建設なし・A7 transport）。ただし主語が A6 の Isom(T̂,T) であり literal A7 再ラベルでないため、crl と束ねて thin canonicity として僅少 credit。
- **evidence**: 上記 crc_* 各行＋`crcCanonicityData`(214)／`crc_scope`(229)。

## 2. 決定的プローブ: A6 vs A7 二重計上（本監査の主判定）

**問**: crc_canonical は ∀Φ:T̂→T（主語=同一視空間 Isom(T̂,T)＝torsor）を genuinely 新規に分類するのか、それとも A7 の tmi_aut_classify（Aut(T)≅ℤ₃^×・既計上）を iso 越しに transport しただけか。

**判定: substantially A7 transport（ただし literal 再ラベルではない）。**

1. **エンジンは全て A7**: §1 の通り crc の全公開定理の証明本体は tmi_*（A7）を Ξ で前後合成するのみ。crc_canonical 本体は `Φ.comp crlInv` を bare tmzLimit endo として tmi_aut_classify に渡す（100 行目）——A7 の Aut 分類がそのまま働く。
2. **∀Φ は循環を破らない**: 「Φ は cgarAct 由来と限らない抽象 Hom ゆえ ∀Φ が循環を破る」の主張は、固定 iso Ξ の存在下では誇大。Φ ↦ Φ∘Ξ⁻¹（=A7 の A）と A ↦ A∘Ξ が互いに逆の自明全単射を与えるため、∀Φ の量化は A7 の「∀ Aut(T)」を超えない。crr の (G1) 循環（χ と作用が同一 cgarAct 由来）は**破れていない**——χ は依然 `cgarRecChar`（cgarAct 由来）で、crl 限定 (ii)・crc 限定 (2) が明示保持。torsor が「ちょうど ℤ₃^×」であること（絞られない）も A7 の `tmi_endo_gal_commute`（同変性が End を絞らない）＋`tmi_aut_classify`（Aut=ℤ₃^×）の transport。
3. **literal A7 再ラベルではない**: crc は主語が bare `Hom tmzLimit tmzLimit` の公開定理を一切輸出しない（§4.2 遵守を精読確認・A:=Φ∘crlInv は局所項のみ）。crc_canonical の主語は Φ:crlLimit→tmzLimit、crc_act_char の主語は crlActHom を含む＝いずれも A6 の主語（T̂/Ξ/復元作用）を含む。ゆえに tmi_aut_classify の単純な再輸出（＝再ラベル）ではなく、A6 の同一視空間へ写した torsor 特徴付けである。

**結論**: 新規実質は crl の副有限レベル復元（T̂＋Ξ・real・(G2) discharge）に集約。crc の canonicity は A7-transport であり、full な新規復元定理として credit しない。thin-discharge の (G1) は crc により**形式的に**埋まる（uniqueness/torsor 特徴付けが入る）が、循環の本質（χ が独立に π₁ から復元されていない）は未解消ゆえ thin のまま。

## 3. 非 crl 内容の本物性

- `crl_char_compat`(95): cli 側の遷移整合正方形 `cli_char_restr`＋`s.property`＋`zpsT` mod 還元＋`cycRig_nat_mod_dvd`＋`Quot.sound` の実証明。sorry/choice/∃-仮説でない。非空虚。
- `crlIso`(235) / `crlInv`(299): 成分ごと `cmuMap`（M443F 明示同型）・両側逆 `crl_iso_leftinv`/`crl_iso_rightinv` は `cid_iso_leftinv`/`cid_iso_rightinv` の成分適用で実証明。G-同変性 `crl_iso_equivariant`(347) は `crr_iso_equivariant`（M443F cid_galois_equivariant の実主語適用）。＝genuine な G-同変両側逆同一視。

## 4. 過大主張チェック（honest 限定の妥当性）

- 不定性を **KILL しない**（mono-theta 剛性は依然 0・crl (i)・crc (1)）を明記。`crc_scope`(229)/`crc_torsor_realize`(133) は「torsor=ちょうど実 ℤ₃^×」の CHARACTERIZE を定理化（KILL でない）。
- **χ を π₁^ét から位相連続に抽出しない**（crl (ii)・crc (2)・依然 cgarRecChar）。
- **実数体/環の復元（AbsTopIII 実主語）・K̄ の μ は皆無**（crl (iii)・crc (3)）。A6 title の本丸『π₁ から体/環を復元』は未到達。
- p=3・G=Gal(ℚ(ζ_{3^∞})/ℚ) 固定（crl (iv)・crc (4)）。
- crr の「A6 上限 0.6」正直申告は消さず並置（crl (v)・crc (5)）。
- **過大主張なし・二重計上は crc につき substantial だが literal でない（§2）。**

## 5. status 判定（0.58）と根拠

**0.55 → 0.58（+0.03）。**
- **+ の根拠**: crl は柱A に不在だった副有限レベルの復元対象 T̂＋G-同変明示同一視 Ξ を genuinely・axiom-clean・非空虚に建設し、crr の 0.6-cap 理由の一つ（(G2) 完全な副有限は後続）を副有限レベルで discharge した。これは 0 前進でも token でもない real 前進。
- **設計目標 0.62（柱A 52）を採らない敵対的理由**:
  1. headline の crc canonicity は A7（既計上 0.40）の transport（compose-with-fixed-iso）で、A7 の Aut(T)≅ℤ₃^× を超える数学内容を持たない（§2）。thin-discharge の (G1) は形式的にしか埋まらず、循環の本質は未解消。
  2. 支配的ギャップ（実数体/環の復元・K̄・π₁^ét 位相 χ）は完全に不変で、A6 title の本丸に一歩も近づいていない。
  3. crl の T̂ は標準模型 zmod 上に建てられた「復元/抽象側」対象で、実 μ の新規建設ではない。
- **0.55 据え置き（0 前進）を採らない理由**: crl の副有限復元＋G-同変同一視は crr（各 ℓ 固定）を質的に超える real 前進で、これを過小評価しない。0.57 でなく 0.58 は、crc が literal 再ラベルでなく A6 主語の torsor 特徴付け（thin canonicity）を追加した分を僅少反映。

Σ_A = 42.84 + 14×0.58 = 50.96 → banker's round 51。**柱A は 51 据え置き**（status は 0.55→0.58 だが Σ_A が 51.5 未満ゆえ丸めは 51・正直に横這い）。

## 6. 反映（本監査で更新した共有ファイル）

- `target_ledger.json`: 柱A A6 status 0.55 → **0.58**。
- `python3 tools/compute_complete_pct.py` → `{"A": 51, "B": 18, "C": 41, "D": 18, "E": 42}`（Σ_A=50.96・round 51）。
- `graph-meta.json`: 柱A `complete_pct` 51 据え置き・`complete_note` に本 A6 ラウンド注記を prepend（何が real か・A6-vs-A7 二重計上判定・thin-discharge は transport 止まりで本質未解消・honest scope・status 根拠・全 axiom clean を明記）。progress_pct 99 据え置き。
- `python3 tools/gen_graph.py` で `graph.json` 再生成（pillars=A:209 …）。
- `dashboard.md` 二軸表 柱A: 51% 据え置き＋A6 ラウンド注記を prepend。
- `IUT/*.lean` は不変更（監査は数字のみ触る）。

**柱A% 新値: 51（据え置き・status は 0.55→0.58 だが Σ_A=50.96 で round 51・正直に横這い）。**
