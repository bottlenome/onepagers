# 独立敵対再監査記録: B2 M4b — Gal↪余核 相互律埋込（q9rg）— 2026-07-11

**種別**: 独立敵対監査（opus・フレッシュ文脈・report-only）
**対象**: `IUT/Q3ReciprocityGalReal.lean`（q9rg・212行・M4b）
**審査**: 柱B B2（現 0.30・weight 20・M4 の後）

## 判定: s_B2 = 0.34（+0.04）

前監査が名指しした cap(a) の健全な着地。cap(a) の 2 サブ gap——「q9rcCongMod が同値律未証明」「正規化 Gal→余核 対応なし」——の**両方**を、実 Galois 群 q9kdG に配線した実群論的内容で閉じ、全健全性検査に合格。+0.02–0.05 帯の中央に抑えたのは、対応が subgroup-level 埋込のみ（LCFT iso でない）・literal Quotient 型未建設・残質量（T3 ~0.55・cap(b) integral-x）未着手ゆえ。

## 根拠（具体定理）
- **同値律 genuine（検査1 PASS）**: q9rg_cong_refl（witness q3kOne・q3k_normBase_one N(1)=1）・q9rg_cong_symm（witness q3kInv・N(x)N(x⁻¹)=N(1)=1）・q9rg_cong_trans（witness q3kMul x y・N(xy)=NxNy）＋q9rg_cong_mul（q3rq_mmmc）。実ノルム群閉包（Q3KummerCubic 856–915・非 sorry）に依拠。「同値律未証明」半分を閉じる。
- **群準同型 mod N genuine（検査2 PASS）**: q9rgPhi = e↦1,s↦4,s2↦16 = 4^index。q9rg_hom 全9ケース・巻き戻し4本確認: s·s=s2（16 def・refl）・s·s2=e（1≡64 via q9rg_mul_comm+q9rc_cong_cube_one）・s2·s=e（cong_cube_one 直接）・s2·s2=s（256=4·64・h256 assoc+q9rg_cong_mul(refl-4,cube_one)）。64≡1 collapse を正しく使用。非空虚。
- **単射 genuine（検査3 PASS）**: q9rg_inj 対角 rfl・非対角は q9rc_not_cong_01/02/12（+symm）へ還元。非循環（4∉N・16∉N に接地）。

## overclaim 検査: CONFIRMED（正直な ↪・≅ overclaim なし）
q9rg_gal_embeds は正確に (∀ hom-mod-N) ∧ (∀ inj) ∧ (φ(e)=1)＝単射群準同型（埋込）。全射性・同型・「余核=ちょうどℤ/3」・index 主張は**ファイル内どこにもない**。ヘッダ(30–32行)明記「これは Gal↪cokernel であって Gal≅cokernel ではない・全射性は T3/research 範囲外・主張しない・φ の像は ⟨[4]⟩ に限る」。正直限定#3 が literal Quotient 未建設・#2 が integral-x を明記。不正なし。

## 軸チェック: PASS
`#print axioms`（q9rg_hom・inj・cong_trans・gal_embeds・cong_refl/symm/mul・exists）全て `[propext, Quot.sound]`。sorryAx/Classical.choice なし。158 ジョブ clean。

## 二重計上（検査5）: genuine 新規・非再包装
q9rc は q9rcCongMod を**定義**し孤立インスタンス（cong_cube_one・pairwise not_cong）を証明したのみ——同値性は未証明・q9kdG を余核に未配線。M4b の新規＝(1) 同値律＋乗法互換証明、(2) 単射群準同型 q9kdG(=Gal)→余核 via q9rgPhi。前監査が「不在」と名指しした正規化 Gal 対応。正当に新規だが有界（像は位数3部分群 ⟨[4]⟩={[1],[4],[16]} のみ）。

## cap 状況
- **cap(a) 閉**: (i) q9rcCongMod は genuine 同値律、(ii) 正規化 Gal↪余核 単射群準同型 q9kdG→L₂^×/N(M^×) 存在。
- **cap(a) 残**: literal Quotient 型オブジェクトなし・全射性なし＝像は ⟨[4]⟩ 部分群のみ（Gal≅全余核でない・T3 要）。
- **cap(b) 不変**: 量化 x∈O_M のみ・M^× 分数元/value-group 未配線。
- **T3 不変（~0.55 research）**: 指数≤3・U_{L₂}^(3)⊆N・Artin 正規化/全射 未着手。

## 次の増分
literal 商群オブジェクト L₂^×/N(M^×)（Quot/Grp）を建て q9rgPhi がそれを経由する bona-fide 群準同型と証明→ T3 指数≤3 上界で埋込を full LCFT iso へ格上げ。
