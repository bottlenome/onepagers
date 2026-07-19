# 独立敵対再監査記録（まとめ）: A2 / A8 / B3 + peel 失敗の正直申告 — 2026-07-11

report-only・opus・フレッシュ文脈。全モジュール full library 671 ジョブ clean・全主要定理 [propext, Quot.sound]。

## A2 — Q3RatFieldEmbed（s_A2 0.67→0.69・+0.02・sub-display）
ℚ↪ℚ₃ を ℚ-像上 genuine 体準同型へ: q3re_map_inv（逆元保存=image of qInv・実体公理 qMul_inv 消費）・q3reMap_injective（単射・trivial kernel）。A2c-3 の named 限定「∃逆元 CRing で体写像でない」を昇格。非空虚 PASS・非再包装（q3re に逆元保存なし）・正直（ℚ-像に scope・ℚ₃ 体主張なし・Markov 障害保持）。light new math ゆえ +0.02（+0.01 も defensible）。次: A2d／ℤ₃-単数逆元／ℚ₃ 位相・付値計量。

## A8 — Q3TateCubeIsogeny（s_A8 0.65→0.66・+0.01・sub-display）
実 [3]-isogeny on E₉=ℚ₃^×/9^ℤ・**E₉[3](ℚ₃)={O}**（q3c3_ker_eq_trivial・μ₃∉ℚ₃/q^{1/3}∉ℚ₃・3∤v(q)=2 の帰結・数学的に正しい）・trivial-deck cube-cuspidalization。q3tt/q3cu の奇 l/N 限定を昇格（[2] Klein-4 と対の奇 N=3 パリティ完成）。非空虚 PASS・二重計上 CLEAN（q3cuSq は component 消費・μ₃ は 3行 thin lift で非再証明・q9tl と disjoint）・正直（cuspidal inertia=0・π₁-reconstruction=0・単一 slice 保持）。core 新規は実質 1 定理・reused engine ゆえ +0.01。次: 実 cuspidal inertia≠0（非可換 theta cover・柱E）／π₁-reconstruction／slice 一般化。

## B3 — Q3DifferentValuation + Q3DifferentIdeal（s_B3 0.27→0.29・+0.02・sub-display）
q9dv: v_M(D)=6 defined 値（q9dv_val_pinned+q9v_wellDef で実 different に pin・非空虚）。q9di: 𝔡=(π₉⁶) genuine primeSpecIdeal 対象（実イデアル公理・両包含 via 実逆元）。★正直監査: exponent d=6 は q9ac/q9tw/q9tf に続く**第4回目再導出**で新規クレジットなし・新規は「イデアル対象＋付値値」formalization（~1/3）のみ→ stingy +0.02。次: codifferent/inverse different（trace pairing・新構造・d=6 の第5視点でない）。

## ★ peel（T3-M1 存在証明）— 今ラウンド未達（正直申告・§5）
`Q3NormSurjPeel.lean` を opus に委譲したが、エージェントは per-level 全射性の**存在証明そのもの**（∀u∃a）を閉じられず、~14h 停滞した 418 行の broken draft（5 errors: rewrite 失敗×2・type mismatch・unknown tactic・unsolved goals）を残して stall。§34（親が引き継ぐ）だが、この存在証明は T3-M3 詳細化が interface-critical と flag した最難所（M1 は def-form で landing 必須・∃-only 不可）で、broken draft の inline 救済に無制限の労力を投じない判断。**broken uncommitted draft を削除**（失敗試行・非コンパイル・非commit）。**T3-M1 peel は未達＝s_B2 前進なし（0.36 据え置き）**と正直申告。foundation（Q3NormSurjGraded・committed 4edcfe8）と T3-M3 詳細化（completeness 到達可能・committed e989ceb）は健在。次ラウンドで peel を def-form 制約付きで再挑戦（M1→M2∥M3a→M3b→M3c で s_B2 0.36→0.52 の見通しは維持）。
