# 独立敵対再監査: A5 実 tempered π₁^temp — Q3TemperedThetaClass (q3nt)

- **日付**: 2026-07-11
- **監査対象**: `IUT/Q3TemperedThetaClass.lean`（prefix q3nt）
- **消費依存（本ラウンド不計上）**: `IUT/Q3ThetaGroup.lean`（q3th=A8・0.65）, `IUT/EtaleTheta.lean`（thetaGrp 代理）, `IUT/TemperedPi1Etale.lean`（M424F tpeGroup 代理）, `IUT/TemperedThetaCommutator.lean`（M384F）, `IUT/Q3TemperedPi1.lean`（q3tp=A5b・0.15 内）, `IUT/Q3TateDeck.lean`（q3td=A5a）
- **前 status**: A5 = 0.15（weight 10）
- **確定 status**: **A5 = 0.20**（+0.05）
- **柱A complete_pct**: 52 据え置き（`compute_complete_pct.py` 出力 `{"A":52,"B":18,"C":41,"D":18,"E":42}`）。Σ_A = 50.42 + 10×0.20 = 52.42 → banker's round 52。

---

## 1. ルーブリック分類（q3nt）

- `classification`: **model→realized（bridge 寄り・非 promote）** — real 判定は下さない。純 surrogate/bridge でもない（新準同型 Φ/Ψ は本物建設）。正味 `moves_complete_pct: yes（+0.05）` だが real-promotion の満額ではない。
- `principal_object`: 代理 Heisenberg thetaGrp（ℤ³）・代理 tempered π₁ tpeGroup（ℤ³⋊ℤ）を、実 E₉(ℚ₃) 上の実 Mumford テータ群 q3thM 内へ実現する準同型 Φ/Ψ と、その旗艦（代理 ω=実 Weil・deck×θ=実 −1・v(q)=2 復元）。
- `is_it_a_stand_in`: 部分的 yes — 定義域 thetaGrp/tpeGroup は依然 ℤ³/半直積の代理（`EtaleTheta.thetaGrp`, `TemperedPi1Etale.tpeGroup`）。q3nt はそれらを実対象へ**置換**せず、実群 q3thM への**写像を建設**する（realize であって promote でない）。値域・旗艦の主語は実 q3thM/実 ℚ₃^× 元。
- `self_declared_external`: ヘッダ正直限定を本体で確認 — Ψ 非単射（`q3nt_psi_level2_collapse`: Ψ(ι(0,0,2))=1）・χ 不可視（`q3nt_chi_invisible`）・位相/Galois/テータ関数/cuspidalization は外部。
- `moves_complete_pct`: **yes, +0.05**（2 名指し A5b ブロッカーの level-2 discharge・本物の新準同型経由）。real-promotion 満額でも bridge ゼロでもない中間。
- `evidence`: `q3nt_braid`(245), `q3ntPhi`(432)/`q3nt_phi_prod`(357), `q3ntPsi`(502), `q3nt_symplectic_real`(481), `q3nt_deck_theta_real`(547)/`q3nt_deck_theta_ne_one`(557), `q3nt_deck_halfperiod`(589)/`q3nt_deck_sq_period`(596)/`q3nt_vq_two`(619)。

---

## 2. build.sh 末尾（EXIT=0・no sorry）

```
'IUT.q3ntPhi' depends on axioms: [propext, Quot.sound]
'IUT.q3ntPsi' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_symplectic_real' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_deck_theta_real' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_vq_two' depends on axioms: [propext, Quot.sound]
'IUT.q3ntClass_exists' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```

## 3. 監査者自作 #print axioms（scratch を `lake env lean` で実行・全 14 対象・逐語）

```
'IUT.q3nt_braid' depends on axioms: [propext, Quot.sound]
'IUT.q3ntPhi' depends on axioms: [propext, Quot.sound]
'IUT.q3ntPsi' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_phi_prod' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_symplectic_real' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_weil_eq_form' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_deck_theta_real' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_deck_theta_ne_one' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_split_contrast' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_deck_halfperiod' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_deck_sq_period' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_vq_recover' depends on axioms: [propext, Quot.sound]
'IUT.q3nt_vq_two' depends on axioms: [propext, Quot.sound]
'IUT.q3ntClass_exists' depends on axioms: [propext, Quot.sound]
```

Classical.choice / sorryAx **皆無**。scratch (`IUT/ScratchA5Audit.lean`) と生成 olean は削除・`git status` clean を確認。

---

## 4. プローブ所見

### 4.1 map_mul は genuinely 証明されているか（新イディオムの検証）
- **q3nt_braid（245）**: 一般 Grp で z 中心・x·y=z·(y·x) から xᵃyᵇ=z^{ab}yᵇxᵃ を **Int 二重帰納で実証明**（`grp_braid_one_nat`→`grp_braid_one`→`q3nt_braid_nat`→`q3nt_braid`・postulate/sorry なし）。三角数閉形式を回避する新イディオムで、リポジトリの既存 q3th 定理の再述ではない。
- **q3ntPhi.map_mul（432-439）**: `(q3nt_phi_prod a b c a' b' c').symm` で駆動。`q3nt_phi_prod`（357）は Y-first 正規形 (Yᵇ Xᵃ Zᶜ)(…)=Yᵇ⁺ᵇ' Xᵃ⁺ᵃ' Z^{c+c'+ab'} を braiding + Z 中心性のみで 6 ステップ正規化＝**本物の準同型性証明**。
- **q3ntPsi.map_mul（502-523）**: `q3nt_phi_prod (a+n) … (a'+n') …` を a↦a+n で再利用し、tpe の第3成分コサイクル c+c'+(a+n)b' と Z 指数の一致を omega で締める＝**本物**。
- 結論: Φ/Ψ は **genuine な準同型（proved map_mul）**。A8 は「ℤ³ thetaGrp への比較準同型は今回作らない（A5/A7 後続へ意図的 defer）」と明記（Q3ThetaGroup ヘッダ §6）——Φ/Ψ はその defer 仕事の実装で A8 に存在しない。

### 4.2 【DECISIVE】A5 固有主語か A8 re-label か
- **q3nt_symplectic_real（481）**の証明本体: `rw [q3nt_comm_eq, ← q3ntPhi.map_grp_comm, theta_comm, q3nt_phi_center, q3nt_Z_zpow]`。
  - `← q3ntPhi.map_grp_comm`: 実 q3thComm(Φv,Φw)=Φ(comm_{thetaGrp}(v,w))＝**Φ が hom であること**を使用。
  - `theta_comm`（EtaleTheta:206）: **代理** thetaGrp の交換子 = (0,0,ω(v,w))。
  - `q3nt_phi_center`+`q3nt_Z_zpow`: Φ(0,0,ω)=Zω=((−1)^ω,0,1)。
  - ⇒ **左辺主語は代理 thetaGrp の交換子（Φ 経由）**・Φ を消すと言明消滅。A8 の単一対 [g₃,g₋₁] でなく代理 thetaGrp 全域の族。**pure A8 re-label ではない**。
- **q3nt_deck_theta_real（547）**の証明: `rw [q3nt_comm_eq, ← q3ntPsi.map_grp_comm, tpe_deck_theta_commutator, q3nt_psi_incl, q3nt_phi_center, q3nt_Z_zpow]`。M424F 代理の deck×θ 交換子 [s(n),ι(a,b,c)]=ι(0,0,nb)（`tpe_deck_theta_commutator`）を Ψ で実 μ₂ 値 (−1)^{nb} へ transport。主語は Ψ（tempered-π₁ 代理）・Ψ を消すと言明消滅。
- **q3nt_deck_theta_ne_one（557）**: [Ψ(s1),Ψ(ι(0,1,0))]=実 −1≠1＝**初の実 level-2 非可換 tempered 対象**（A5b の分裂直積「非可換性ゼロ」ブロッカーの level-2 discharge）。
- **敵対的裁定**: q3nt は A8 テータ交換子の cosmetic 再標識**ではない**（新 hom Φ/Ψ が主語・A8 未所持・A8 が明示 defer した仕事）。**但し** 旗艦の μ₂ 値エンジンは A8 `q3th_comm_eq_weil` を map_grp_comm で pull-back し代理 `theta_comm` を transport するのみ＝**新規交換子数学ゼロ・値一致 bridge の性格が濃い**。

### 4.3 v(q)=2 は tempered 側か g_τ（A8）か
- `q3nt_deck_halfperiod`（589）: (Ψ(s n)).w = (Ψ(s n) = X^n = g_{[3]}^n の w 成分) = q3tQ 1 の n 乗（半周期 3ⁿ）。証明は `q3nt_psi_deck`（Ψ(s n)=q3thG3^n）+ `hom_map_zpow q3ntW`。**g_τ を経由しない**。
- `q3nt_deck_sq_period`（596）: 半周期の平方 = q3tQ 1^{2n} = q3tQ 2^n = qⁿ = (q3tdPeriodHom 2)(n)（A5a の実周期 hom へ着地）。
- `q3nt_vq_two`（619）: (Ψ(s1)).w の第1成分 = 1（half-period 3 の付値 1）⇒ v(q)=2·1=2。
- **裁定**: v(q)=2 は **tempered-π₁ 側 deck 切断 s(n) の Ψ 像**（＝A8 witness g_{[3]}）から復元・g_τ（A8 降下元）を通らない。A5b「q 不可視」ブロッカーの level-2 discharge として **genuine**。**但し** q=9（v=2）は A5a/A8a で既に実固定済＝q3nt は**再露出であり発見ではない**。

### 4.4 「bridge/値一致確認」か「代理の real 昇格」か
- ルーブリック: 代理/橋（値一致確認・束ね）は不計上。real は代理を**実対象へ置換**（promote）。
- q3nt は thetaGrp/tpeGroup を実対象へ置換**しない**（代理は代理のまま）。実群 q3thM への**準同型を建設**する（realize）。実現は level 2（Ψ 非単射・μ₂ 影）のみ。
- 旗艦 q3nt_symplectic_real は本質「代理 ω = 実 (−1)^ω」の値一致（新 hom で媒介）。q3nt_deck_theta_ne_one / v(q) 復元は代理 tempered 構造の実 level-2 実現＝bridge を超える A5 固有前進だが mod-2/μ₂ 影に留まる。

### 4.5 過大主張チェック（正直限定の存否）
本体で確認: `q3nt_psi_level2_collapse`（Ψ 非単射・実現 mod2 のみ）・`q3nt_chi_invisible`（χ level2 不可視）・`q3nt_split_contrast`（A5b 分裂直積の自明可換性を Φ/Ψ 無関係の純対照として可視化）。ヘッダ正直限定 1–5（位相なし＝A5 上限 0.35–0.4 不変・Galois 0・テータ関数 0・cuspidalization 0）は本体と整合・A8/q3th/A5b の正直限定は不変更。A8 status はファイル内で不主張（q3th 定理は消費のみ・q3th ファイル不変更）。**過大主張なし・隠れ choice なし**。

---

## 5. status 判定と根拠

**A5 = 0.20（+0.05）。**

genuine A5 前進（+0.05 相当）:
1. Φ/Ψ は本物の新準同型（proved map_mul via 新イディオム q3nt_braid）＝A8 が明示 defer した A5/A7 比較写像の実装。
2. q3nt_deck_theta_ne_one＝初の実 level-2 非可換 tempered 対象（A5b 分裂直積「非可換性ゼロ」ブロッカーの level-2 discharge）。
3. v(q)=2 の tempered-π₁ 側（deck 切断）復元（A5b「q 不可視」ブロッカーの level-2 discharge・g_τ 非経由）。

設計の +0.10（0.25）を採らない理由（割引）:
1. 旗艦 q3nt_symplectic_real の μ₂ 値エンジンは A8 `q3th_comm_eq_weil` の transport＝新規交換子数学ゼロ・値一致 bridge 性が濃い。
2. 代理 thetaGrp/tpeGroup は実対象へ**非昇格**（写像建設 realize であって置換 promote でない）。
3. Ψ 非単射・mod-2/μ₂ 影のみ（level 2）。
4. v(q)=2 は A5a/A8a で既実固定（再露出）。
5. 位相なしで A5 恒久上限 0.35–0.4 不変・Galois/テータ関数/cuspidalization 全 0。

敵対的既定（立証責任は「real」側）と honest cap を踏まえ、**0.20 が保守かつ公正**。柱A は 52 据え置き（Σ_A=52.42・round 52）。

---

## 6. 結果集約

- Σ_A = 50.42 + 10×0.20 = 52.42 → **柱A = 52**（`compute_complete_pct.py`: `{"A":52,...}`）。
- 更新ファイル: `target_ledger.json`（A5 status 0.15→0.2）, `graph-meta.json`（pillars.A complete_note に A5 note prepend・complete_pct=52 据え置き・progress_pct=99 据え置き）, `dashboard.md`（柱A 二軸行に A5 note prepend・52% 据え置き）, `graph.json`（gen_graph.py 再実行・ノード既登録で内容不変）。
- コミット/プッシュは行わない。
