# 独立敵対再監査記録: B2 M4 — [4] 位数3・ℤ/3 余核下界（q9rc）— 2026-07-11

**種別**: 独立敵対監査（opus・フレッシュ文脈・report-only）
**対象**: `IUT/Q3ReciprocityCokernelReal.lean`（q9rc・230行・M4）
**審査**: 柱B B2（現 0.22・weight 20・M3 crux の後）

## 判定: s_B2 = 0.30（+0.08）

名指しの増分が着地。M4 は M3 crux（4∉N・「余核非自明のみ」）を実**元レベル ℤ/3 下界**（[4] 位数ちょうど3）へ昇格——T2 下界の実数学的内容。前監査が order-3 gap を理由に据えた 0.30 の天井を越えるが、(a) 商群オブジェクト無し・(b) 正規化 Gal(M/L₂)≅ℤ/3（q9kdG/Artin 4↦σ）対応無し・(c) integral-x 継続・T3（~0.55）未着手ゆえ、旧 forecast 上限 0.35–0.40 には及ばない。

## 2. 根拠（具体定理＋外部検査）
`q9rc_foursq_not_norm`（16=4²∉N）は genuine・**非空虚**。⟨x,hx,N(x)=16⟩ を仮定・y=q3kMul(embed 4)(q3kInv x hx)・単数（q3k_unit_mul/q3k_unit_inv）・N(y)=q9rcFour を rw[q3k_normBase_mul, q9ps_normBase_embed, q3k_normBase_inv] + q9rc_mul_cube_inv（(A·A·A)·(A·A)⁻¹=A ＝ N(y)=4³·4⁻²=4）で計算・q9lr_four_not_norm に矛盾。群事実 [4]=[4³]·[4²]⁻¹ そのもの（非循環）。`q9rc_fourcube_is_norm`（4³∈N）実: witness embed 4・N(embed 4)=4³（q9ps_normBase_embed）・embed(4) 単数（q9rc_four_unit: 4=(1+3,0) が ℤ₃ 単数・N=16=4²・q3rq_pair_unit + q9wr_embed_unit）。**外部検査 CONFIRMED**: 16 は O_{L₂} 単数（3∤4）・cyclic cubic M/L₂ で余核 ℤ/3・4∉N（4≡7 mod 9）ゆえ 4²=16 は非自明剰余類＝16∉N。Lean 証明は cokernel=ℤ/3 を仮定せず 16∉N を 4∉N + 4³∈N へ還元。

## 3. 非空虚判定: CONFIRMED
`q9rc_order3`=(4∉N ∧ 4²∉N ∧ 4³∈N) は正しい元レベル「位数ちょうど3」（位数∣3 via 4³∈N・位数≠1 via 4∉N ⟹ 位数=3）。`q9rcCongMod a b := ∃x, q3kUnitMem x ∧ q3rqMul a (q3kNormBase x)=b` は忠実・非循環な剰余類関係（b·a⁻¹=N(x)∈N の genuine「N(M^×) を法として同一剰余類」・trivially true でない）。対毎相異 3 本は実還元: not_cong_01→q9lr_four_not_norm・not_cong_02→q9rc_foursq_not_norm・not_cong_12→q9rc_four_cancel（4 単数・左簡約）→q9lr_four_not_norm。[4³]=[1]（cong_cube_one）と併せ {[1],[4],[4²]} 対毎相異＝**ℤ/3 ↪ 余核 元レベル忠実**。

## 4. 軸チェック: PASS
156 ジョブ clean。`#print axioms` = `[propext, Quot.sound]`（q9rc_order3・q9rc_foursq_not_norm・q9rc_z3_injects・q9rc_fourcube_is_norm・q9rc_exists）。sorryAx/Classical/禁止タクティクなし。二重計上なし（M4 は q9lr_four_not_norm を import 消費・M3 crux を再証明せず・status mover 1 回）。

## 5. T2（ℤ/3 下界）: 閉じた分 vs 残
**閉じた**: order-3 core——前監査が <0.30 の支配的理由に挙げた gap。元レベル [4] 位数ちょうど3 ＋対毎相異＝ℤ/3 injects の実数学的内容。
**残**: (a) 商群オブジェクト無し（N(M^×) 部分群未建設・q9rcCongMod の同値律未証明）、(b) 正規化 Gal-iso 無し（q9kdG 未参照・Artin 未配線）、(c) cap(ii) integral-x 不変（q3kCar=O_M のみ・分数元 π₉^{-k}u の value-group bookkeeping 未形式化・M3 継承）。全て正直開示・消去せず。

## 6. 次の増分
M5/T3: M^× value-group bookkeeping 形式化（integral-x を literal L₂^×/N(M^×) へ・商群オブジェクト＋q9kdG への Gal-iso）→ T2→T3 上界（指数≤3・U_{L₂}^(3)⊆N・Artin 相互律）＝残 ~0.55 research。
