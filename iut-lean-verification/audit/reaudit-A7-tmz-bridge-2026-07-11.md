# 独立敵対監査: A7 実円分剛性 — 比較橋 Q3Mu3TmzBridge (q3mb)

日付: 2026-07-11
対象: `IUT/Q3Mu3TmzBridge.lean`（prefix `q3mb`）
監査種別: 独立・敵対的（default = model/surrogate・立証責任は「real」側）
前提: A7 現状 0.47（level-3 kill キャンペーン後・reaudit-A7-level3-kill-2026-07-11.md）。
その監査が名指しした上限 #1（level-3 kill は **機構レベル止まり**——テータ群内部 μ₃ を固定するが
tmi の実 ℤ₃^× 不定性対象には未接続・tmzLimit への比較橋なし）を本橋が discharge すると主張。

## 決定: A7 status = **0.49**（0.47 → 0.49・+0.02）

柱A complete_pct: **53 → 54**（Σ_A = 47.62 + 12×0.49 = 53.50・Python `round(53.50)=54`
＝銀行丸めで偶数側 54・`compute_complete_pct.py` 出力 `{"A":54}`）。

## 監査ルーブリック出力（AUDIT_RUBRIC.md）

- `classification`: **real（本物建設(b) + 昇格(a)・到達の昇格）**
- `principal_object`: G-同変な実群同一視 β = q3mbHom : Hom (tmzG 0) q3rqU（tmz 側実 μ₃ ↔
  テータ側実 μ₃）と、それを通した tmi の実 ℤ₃^×=zpsLimit の作用 tmiFromUnits の輸送・
  level-3 テータ剛性による (ℤ/3)^× 商 kill。
- `is_it_a_stand_in`: **no**。tmzG 0 = cmrGrp 1 ＝実円分体 ℚ(ζ₃) 内の実 μ₃、q3rqU ＝
  実局所整数環 O_{ℚ₃(ζ₃)}^× 内の実単数群、u : zpsLimit.carrier ＝実 ℤ₃^×。Bool/Nat/Fin の
  身代わりでない。β は離散対数 ctmFind による実群準同型（Nat/Bool stand-in map でない）。
- `self_declared_external`: header 正直限定 5 項（mod-3 のみ・群レベル+ℤ/2・R1 継承 order-2 Galois・
  q=27・firewall）は保持。核となる実対象（tmzG 0・zpsLimit・q3rqU）は外部/後続/模型と自認していない。
- `moves_complete_pct`: **yes**（real かつ到達の実昇格＝内部テータ cyclotome → tmi の実 (ℤ/3)^× 商）。
- `evidence`: q3mbHom (:227)・q3mb_equivariant (:283)・q3mb_transport (:371)・q3mb_kill_mod3 (:400)・
  q3mb_admissible_iff (:440)・q3mb_flip_invariant (:133)。

## build.sh tail（EXIT=0・no sorry）

```
'IUT.q3m3r_cyclotome_fixed' depends on axioms: [propext, Quot.sound]
'IUT.q3m3r_aut_mu3_nontrivial' depends on axioms: [propext, Quot.sound]
'IUT.q3mbHom' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_equivariant' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_transport' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_kill_mod3' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_admissible_iff' depends on axioms: [propext, Quot.sound]
OK: all theorems verified, no sorry.
```

## 監査者独立 #print axioms（scratch を lake env lean で実行・scratch/olean 削除済）

```
'IUT.q3mbHom' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_equivariant' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_equivariant_conj' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_transport' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_kill_mod3' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_admissible_iff' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_flip_invariant' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_onto_mu3' depends on axioms: [propext, Quot.sound]
'IUT.q3mb_exists' depends on axioms: [propext, Quot.sound]
```

全 9 対象 clean（[propext, Quot.sound] のみ・新規 Classical.choice/sorryAx 皆無）。

## 決定プローブの所見

### プローブ 1: kill は tmi の実対象上か・re-label/vacuous でないか — **YES（genuine）**

`q3mb_kill_mod3 (u : zpsLimit.carrier) (φ : q3m3Car → q3m3Car) (hHom)(hMem)(hE3)(hreal) :
(u.val 0).val = 1`。

- **u は tmi の実 ℤ₃^×**: u : zpsLimit.carrier ＝tmiFromUnits が作用する同一の実 zpsLimit。
  結論 (u.val 0).val = 1 は tmi の実単元 u の mod-3 成分（∈(ℤ/3)^×={1,2}）への実制約。
- **証明が実剛性・実 tmi 作用を消費**: 証明は t = tmeZetaLim（明示 witness・choice-free）で
  hreal を実体化し、(i) `q3m3r_cyclotome_fixed φ hHom hMem hE3` を φ に消費（左辺 φ(q3m3rZeta)
  = q3m3rZeta）、(ii) `q3mb_transport u tmeZetaLim` を消費（右辺 = pow(q3mbUnit(tmeZetaLim.val 0))
  ^{u₀}）。q3mb_transport は `q3mb_level0` = `rfl` で `tmiFromUnits u` の level-0 作用（成分冪
  y↦y^{u₀}）を直接展開＝tmi の実作用へ到達。両辺の .1.1.2 成分比較で inv ζU = pow(inv ζU)^{u₀}、
  u₀=2 ⟹ inv ζU = (inv ζU)² ⟹ ζU = 1 ⟹ ζ₃=1（q3rq_zeta_ne_one）矛盾。∴ u₀=1。
- **非空虚**: `q3mb_admissible_iff` が (u.val 0).val=1 ⟺ ∃φ（剛性仮説＋hreal）を証明。順方向は
  φ=id を構成（u₀=1 で level-0 が恒等＝hreal 成立）＝仮説充足元が実在。ゆえに定理は真の二分
  （u₀=1 のみ theta-両立）で、vacuous な ∀ でない。
- **re-label でない**: tmi の ℤ₃^× 特徴付け（tmi_aut_classify 等）は消費のみ・再証明ゼロ・言明複製
  ゼロ（tmiFromUnits をブラックボックスとして使用）。level-3 kill の re-label でもない——q3m3r は
  内部 q3m3rZeta を固定するのみ・q3mb は新たに外部の実単元 u に制約を課す（到達の質的昇格）。

### プローブ 2: β は実・G-同変・新規か — **YES**

- **実 Hom**: q3mbHom : Hom (tmzG 0) q3rqU。担体写像 q3mbU y = pow ζU^{ctmFind y}（離散対数・
  choice-free）。map_mul は tmz_mul_find（離散対数加法性）＋ζU³=1 で証明。単射（q3mb_inj）・
  像 ⊆ μ₃（q3mb_image_mu3）・onto μ₃（q3mb_onto_mu3・q3mc_mu3_complete 消費）。tmzG 0 も q3rqU も
  実対象（実円分体/実局所環内の実群）。
- **実 G-同変**: q3mb_equivariant は β(σ·y) = pow(β y)^{χ(σ)} を証明し、`cgar_rigidity`（実 Galois
  群 galoisGroupGrp(cteExt 1) の実円分体自己同型作用）を消費。q3mb_equivariant_conj は代入自己同型
  σ₂（χ=2）を実共役 q3rqConj に接続し `cgar_sigma2_exp` を消費。Nat/Bool stand-in でない実同変。
- **新規**: grep 実測——テータ側 import（q3rq/q3m3/q3tl）を持つモジュールで円分側（tmz/tmi/cgar）
  を共に import する先行モジュールはゼロ。q3mb がコードベース初の cross-side（テータ↔円分）橋。

### プローブ 3: ℤ/2 flip 曖昧 — **実証明あり**

q3mb_flip_invariant : pow(pow g a) b = pow(pow g b) a（cycRig_pow_mul + Nat.mul_comm）。
生成元 ζ↔ζ² の非正準選択の下でも輸送指数 a が不変＝橋の生成元選択が kill を無効化しない
ことの機械証明。

## 過大主張・二重計上・隠れた選択のチェック

- **full ℤ₃^× kill を主張していない**: 殺すのは mod-3 の (ℤ/3)^× 商（2 元）のみ。1+3ℤ₃ pro-3 bulk
  と n≥2 レベルは F-wild まで残存（header 正直限定 1・保持）。q3m3r/tmi の残存宣言不変更を確認。
- **群レベル・実埋め込みなし**: 橋は位数 3 巡回群の同型（生成元指定＋ℤ/2 曖昧）で実体埋め込み
  ℚ(ζ₃)↪ℚ₃(ζ₃)（局所大域体比較・分解群理論）は形式化せず（header 正直限定 2・保持）。両側とも
  実 μ₃ ゆえ real だが「二つの μ₃ コピーの同型」であり、意味は同変性（cgar_rigidity 消費）が担保。
- **二重計上なし**: q3m3r_cyclotome_fixed・tmiFromUnits・tmz・q3rq・q3mc は消費のみ・再証明ゼロ・
  言明複製ゼロ。新規内容は 橋 β＋輸送＋(ℤ/3)^× kill = 到達の昇格。
- **隠れた選択なし**: 全 witness は明示閉式（tmeZetaLim・ctmFind 走査・pow）。#print axioms で
  新規 Classical.choice 皆無を確認。

## status 決定の正当化

**0.49（+0.02）**: 本橋は監査上限 #1 を genuine・非空虚に discharge する到達の質的昇格である——
level-3 剛性の主語を「テータ環境の内部 μ₃」から「tmi の実 ℤ₃^× 不定性の (ℤ/3)^× 商」へ橋渡しし、
テータ剛性が tmi の実単元 u の mod-3 成分を 1 に強制することを、実・G-同変・新規な橋 β ＋ 実輸送
（tmiFromUnits 消費）＋ 実剛性（q3m3r_cyclotome_fixed 消費）で証明する。非空虚（admissible_iff）・
flip 不変（flip_invariant）・全 axiom clean。**0.50–0.51 に上げない**のは、殺す対象が (ℤ/3)^× 商
（2 元）のみで広大な ℤ₃^× の bulk が残存し、橋が群レベル位数 3 同型（実体埋め込みなし・ℤ/2 曖昧）で
テータ側 Galois も order-2 実共役のみ（実 G_{ℚ₃} 不在）だから。**0.47/0.48 に据え置かない**のは、
橋が vacuous でも re-label でもなく（tmi の特徴付けは消費のみ・level-3 kill とは別の外部対象 u に
新規制約）、名指しの #1 cap を正面から答える reach-upgrade だから。0.49 が丸め境界 53→54 を越える
のは偶然でなく、genuine な到達昇格を反映した閾越えとして妥当。

**算術訂正（追記のみ・旧 0.47 値記録は不改変）**: 直前 reaudit-A7-level3-kill 注記の
「54 には A7≥0.54 が要る」は算術誤り。Σ_A = 47.62 + 12·s_A7 ゆえ s_A7=0.49 で 53.50 → round 54 に
到達（s_A7=0.48 では 53.38 → 53）。監査者が `compute_complete_pct.py` を自ら実行して {"A":54} を確認。

## 帰結

- Σ_A = 47.62 + 12×0.49 = 53.50 → round(53.50) = 54。
- 柱A complete_pct: 53 → **54**。
- target_ledger.json A7 status: 0.47 → 0.49。graph-meta.json pillars.A complete_pct: 53 → 54（注記 prepend）。
- dashboard.md 二軸表 柱A: 53% → 54%（注記 prepend）。gen_graph.py 再生成済。
