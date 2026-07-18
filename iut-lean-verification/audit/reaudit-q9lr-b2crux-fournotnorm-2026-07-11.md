# 決定的独立敵対監査記録: B2 CRUX 4∉N（M1 q9rf + M2 q9gn + M3 q9lr）— 2026-07-11

**種別**: 独立敵対監査（opus・フレッシュ文脈・report-only・**decisive**——weight-20 の B2 を初めて 0 から動かす）
**対象**: 3モジュール鎖 `IUT/Q3ResidueFieldReal.lean`(q9rf・M1)・`IUT/Q3GradedNormBreak.lean`(q9gn・M2)・`IUT/Q3LocalReciprocityReal.lean`(q9lr・M3・crux)
**審査**: 柱B B2「実局所類体論(相互写像・ノルム群)」（w20・status 0）

## 判定: s_B2 = 0.22（+0.22）

実で稼いだ bump。ただし設計文書 forecast 中点（0.30）未満に抑えた——開示された 2 限定が cosmetic でなく genuine だから: cokernel は**非自明のみ**証明（ℤ/3 でない）・M^× 自体が未形式化（integral O_M のみ）。

## 1. 根拠（具体定理＋外部数学検査）
crux `q9lr_four_not_norm : ¬ ∃ x : q3kCar, q3kUnitMem x ∧ q3kNormBase x = q9lrFour` は**実・非空虚**。`q9lrFour := q3rqAdd q3rqOne q3rqThreeElt` = (4,0) ∈ O_{L₂}（q3rqThree=(1+1)+1=3）・実 ℤ₃ 単数（q3rqNorm(4,0)=16）。等式は 2 つの O_{L₂} 元の well-typed 同一性・`q3kNormBase`（実 3 次ノルム a³+ζ₃b³+ζ₃²c³−3ζ₃abc）は L₂ 元に genuine に当たる（N(1)=1）——型不整合で空虚でない。`q3kUnitMem` は非空（x=1）——空述語で空虚でない。**外部検査で 4 は真の非ノルム確認**: N_{L₂/ℚ₃}(4)=16≡7 mod 9 ∉ 1+9ℤ₃・設計文書は 1458 単数類で 0 hits。証明は実 3 段降下: step0（res∘N⟹U¹）→ step1（break-cancel 先頭項⟹U²・M2 q9gn_norm_U1_sharp 消費）→ contra（U²⟹N(x)∈U⁹⊆U⁷ via q9gn_norm_U2・q9nf_retarget_sharp 矛盾）。矛盾エンジンは genuine に `q9nf_retarget_sharp`（contra 最終行 `exact q9nf_retarget_sharp h7`・π₉⁷∤embed(3) の実定理）。全対象実: O_M=q3kRing・O_{L₂}=q3rqRing・𝔽₃=zmodRing 3・z3=zpRing 3——toy 主語なし。

**強化点**: 単位仮説 `hu` は**未使用**（step0 は `_hu`）。よって鎖は実際にはより強い「**integral x∈O_M で N(x)=4 なし**」を証明（整合: N(x)=4 ⟹ res_M(x)=1≠0 ⟹ x 自動的に単数）。非空虚性に安心材料。

## 2. 非空虚判定: CONFIRMED
q9lr_four_not_norm は genuine な実非ノルム主張・非空虚・（未使用単位仮説により）宣伝よりわずかに強い。

## 3. 軸チェック（4 主定理）: PASS
ソースから再ビルド・`#print axioms` は `q9lr_four_not_norm`・step0・step1・contra すべて厳密 `[propext, Quot.sound]`（sorryAx/Classical.choice なし）。3 モジュールに禁止タクティクなし。`lake build IUT.Q3LocalReciprocityReal` 成功（155 ジョブ）。

## 4. T2（ℤ/3 cokernel 下界）はどこまで閉じたか
**部分——非自明性のみ**。T2 は非ノルム単数**位数 3** を要す（ℤ/3 ↪ L₂^×/N）。crux は非ノルム元 **1 個**——cokernel **非自明**（位数≥2・N(M^×)≠L₂^×）を証明するが [4] 位数 3 は未証明（=M4「4²∉N」未実装）。よって ℤ/3 **下界は未確立**、「cokernel≠自明」のみ。T3（指数≤3/Artin・B2 の ~0.55）は完全に未着手（research）。T1（値群全射）は既存。

## 5. integral-x 限定: 実 cap か cosmetic か
**穏当な実 cap（~0.03–0.05）・致命的でない**。数学的還元は airtight: M^× の 4 の preimage は v_{L₂}(N(x))=v_M(x)・v_{L₂}(4)=0 ⟹ v_M(x)=0 ⟹ x integral 単数——「integral 元で N(x)=4 なし」は 4∉N(M^×) を確立する。だがこの付値還元は**未形式化**: q3kCar は O_M のみ・M^×（π₉^{-k} 分数元）は Lean 未建設。よって literal cokernel L₂^×/N(M^×) が形式化主語でなく integral shadow のみ。欠落ステップ（unit-norm⟹integral 単数）が routine なので小 cap 扱い・支配的 cap は order-3/T2-partial。

## 6. 二重計上・足場正直: クリーン
M1(q9rf)・M2(q9gn) ヘッダは両方 s_B2=0 自己申告（足場）・status mover は M3 で 1 回のみ。他柱 re-bank なし（M1 は B1 note 更新可能性のみ・「complete_pct 表示は動かない見込み」明記）。

## 7. 次の増分
M4 を形式化——4²∉N（[4] 位数 3・T2 の genuine ℤ/3 下界）＋ M^× value-group bookkeeping（N(x) 単数⟹x integral 単数）を配線し非ノルム主張を literal に L₂^×/N(M^×) にする。
