# 独立敵対監査: IUT/Q3Mu9Rigidity.lean（q9mr・level-9 mono-theta 剛性・機構レベル kill）

- 監査日: 2026-07-11
- 監査者: 独立敵対監査者（本コードを書いていない・既定スタンス=懐疑）
- 対象: `IUT/Q3Mu9Rigidity.lean`（prefix `q9mr`・472 行・commit 4dca299）
- 申告分類: **[実／本物の先行建設(b)] FOUNDATION・complete_pct 0 前進（mechanism-level・display 移動は未建設の橋 q9mb）**
- 判定: **申告どおり承認**。新層 kill 機構は本物・payoff の 5 連言すべて genuine・axiom clean・**0 前進**（A=54 据え置き）。

---

## 0. 結論（先出し）

| 項目 | 結果 |
|---|---|
| 新層 kill 機構は genuine か | **YES**（σ が ker(Aut(μ₉)→Aut(μ₃)) の非自明元の実 witness・剛性がそれを排除） |
| σ payoff（q9mr_aut_mu9_new_layer）5 連言すべて genuine か | **YES**（(i)乗法的・(ii)σ(1)=1・(iii)μ₃対角各点固定・(iv)σ(ζ₉)=ζ₉⁴・(v)σ(ζ₉)≠ζ₉ 全て実証明） |
| q9mr_rigidity / q9mr_cyclotome_fixed | genuine clone・非空虚 |
| q9mr_weil_fails_on_M | load-bearing・非空虚（membership 仮定が本物に効く） |
| q3m3r の re-label か | **NO**（新層は別対象 ker(Aut(μ₉)→Aut(μ₃))） |
| axioms | 全対象 `[propext, Quot.sound]` のみ |
| 禁止タクティク | なし（omega ×13 は純 Int のみ） |
| lake build | EXIT=0（102 jobs・no sorry） |
| 台帳判定 | target_ledger.json **不変**・A=**54** 据え置き・compute_complete_pct.py `{"A":54,...}` |

---

## 1. payoff `q9mr_aut_mu9_new_layer` の genuine 性（本監査の crux）

文（:370-376）は次の 5 連言:

```
(∀ x y, σ(xy)=σx·σy) ∧ σ(1)=1 ∧ (∀ n, σ(embed n)=embed n)
 ∧ σ(ζ₉)=ζ₉⁴ ∧ σ(ζ₉)≠ζ₉
```
証明本体は `⟨q3k_sigma_mul, q3k_sigma_one, q9mr_sigma_fixes_mu3, q9mr_sigma_zeta9, q9mr_sigma_zeta9_ne⟩`。各連言子を実定義まで降りて確認した。**断定（honest 仮説）は 1 つも無い。**

- **(i) 乗法的** — `q3k_sigma_mul`（Q3KummerCubic.lean:518）。σ=q3kSigma は `σ(a,b,c)=(a, ζ₃b, ζ₃²c)`（:504）。乗法保存は 3 成分すべて `q3k_ext` で分解し、ねじれ積 Y³=ζ₃ 上で ζ₃·ζ₃²=1（`q3k_z_zsqR1` 等）を実 rewrite で潰す**本物の環準同型証明**。断定でない。
- **(ii) σ(1)=1** — `q3k_sigma_one`（:511）。ζ₃·0=0・ζ₃²·0=0 で実証。
- **(iii) μ₃ 対角を各点固定（kill 対象が新層である核心）** — `q9mr_sigma_fixes_mu3`（Q3Mu9Rigidity.lean:318）。`q3kEmbed n=(n,0,0)`（Q3KummerCubic.lean:689）を σ が各点固定: 定数部 rfl・Y 部 `ζ₃·0=0`・Y² 部 `ζ₃²·0=0` の実証明。∀n なので**基礎体 q3rqCar=ℚ(ζ₃) 対角全体を固定**、特に μ₃=⟨ζ₃⟩（ζ₃=Y³ は定数）を固定。すなわち σ∈ker(Aut(μ₉)→Aut(μ₃))。
- **(iv) σ(ζ₉)=ζ₉⁴** — `q9mr_sigma_zeta9`（:327）。ζ₉=Y=q3kZeta9=(0,1,0)（:929）。σ(Y)=(0,ζ₃·1,ζ₃²·0)=(0,ζ₃,0)。`q9yp_y4`（Q3KummerYPow.lean:128）が Y⁴=(0,ζ₃,0) を実証（Y⁴=Y³·Y=ζ₃·Y）。ゆえに σ(ζ₉)=ζ₉⁴。ζ₉⁴ は**真の 4 乗**（Y は位数ちょうど 9: Y³=ζ₃・Y⁶=ζ₃²・q9yp Yᵏ≠1 k=1..8）。指数 4=1+3∈(ℤ/9)^× は 4≡1 mod 3 ゆえまさに ker の元。
- **(v) σ(ζ₉)≠ζ₉（μ₉ 上非恒等）** — `q9mr_sigma_zeta9_ne`（:338）。σ(ζ₉)=ζ₉⁴ の第 2 成分 ζ₃ と ζ₉ の第 2 成分 1 を congrArg で比較、`q3rq_zeta_ne_one`（Q3RamifiedQuadratic.lean:644・ζ₃≠1）で矛盾。

**(iii) と (v) が同時に本物**ゆえ σ は「μ₃ 上は恒等に見えるのに μ₉ 上非恒等」な実自己同型＝ker(Aut(μ₉)→Aut(μ₃))∖{id}=(1+3ℤ₃)/(1+9ℤ₃) の非自明元の機械可読 witness。level-9 剛性の内部 cyclotome {id} 固定（q9mr_cyclotome_fixed）がこの σ を排除する。**payoff は genuine。**

---

## 2. q9mr_rigidity / q9mr_cyclotome_fixed（clone・非空虚）

- `q9mr_rigidity`（:251）— endo 剛性（単射仮定なし・全交換子保存）。証明は φ を交換子語に貫通（`hHom`/`q9mr_hom_inv` 経由）→ Weil 値を E[9] 決定性 `q9mr_weil_e9_left`/`_right` で不変化。q3m3r_rigidity の語彙置換だが機構は完全に再実行されており **vacuous でない**。
- `q9mr_cyclotome_fixed`（:305）— テータ両立 endo は内部 μ₉ cyclotome を固定。固定対象 `q9mr_zeta9=((0,ζ₉⁻¹),0,1)`（:282）は `q9mr_zeta_eq_comm`（:286）で comm(g₃,g_ζ) に一致し、`q9mt_weil_g3_gz`（Q3Mu9ThetaGroup.lean:577）で値が ζ₉⁻¹（原始 9 乗根・=inv(q9tlZeta9U)）と確定。非退化性は `q9mt_nonabelian`（q9mr_zeta9≠q9mtOne）で担保。固定対象は**自明でない原始 9 乗根**。level-3 の ζ₃⁻¹ 固定を ζ₉⁻¹ に置換した genuine clone。

---

## 3. q9mr_weil_fails_on_M は load-bearing（非空虚）

`q9mr_weil_fails_on_M`（:390）は 4 連言:
```
q9mtMem g₁ ∧ ¬q9mtMem g₂ ∧ proj(g₁.2)=proj(g₂.2) ∧ e₉(g₁,g_ζ)≠e₉(g₂,g_ζ)
```
witness: g₁=`q9mrWit1`=((1,0),1)・g₂=`q9mrWit2`=((1,1),1)。

- `q9mtMem` は実述語 `qᵃ·w⁹=1`（Q3Mu9ThetaGroup.lean:366）で、`q9mt_mem_iff`（:459）が付値方程式 **6a+v=0** に同値化する（恒真でない・本物の制約）。g₁: a=0⟹mem（`q9mt_mem_one`）。g₂: a=1・v=0⟹6·1+0=6≠0⟹**not mem**（証明は omega で矛盾）。
- 同 E_{3⁹}[9] 像: 両者 w=q9tlMx.one ゆえ proj 一致（rfl）。
- Weil 値差: e₉(g₁,g_ζ)=1（a=0 で自明）・e₉(g₂,g_ζ)=ζ₉（a=1）。ζ₉≠1 は `q3k_zeta9_ne_one` に帰着。

すなわち「同 E[9] 像・membership を落とすと決定性が崩れる」実反例。q9mr_weil_e9_left の membership 仮定は**本物に効いており**、鍵補題は q9mt_comm_eq_weil（値の式）の系ではない。**load-bearing 確認。**

---

## 4. q3m3r の re-label でないこと

- clone 部（E[9] 決定性・endo 剛性・cyclotome 固定）はヘッダ §3.1 で「テンプレ再インスタンス・新規数学ゼロ」と**正直申告**されており、実際 q3m3r の level-9 定数替え（cube→9 乗・6k→54k）。
- payoff（§3.2）は別対象: q3m3r_aut_mu3_nontrivial は**反転 ζ₃↦ζ₃²・位数 2・μ₃ 上非恒等**。q9mr の新層は **ker(Aut(μ₉)→Aut(μ₃))**＝μ₃ 上恒等・μ₉ 上非恒等の σ で、位数 3 巡回 (1+3ℤ₃)/(1+9ℤ₃) の元。両者は数学的に異なる kernel 層を主語にする。**re-label でない・質的新規。**

---

## 5. axioms / 禁止タクティク / build

`lake env lean` で全対象を列挙（推移閉包）:

```
q9mr_rigidity          : [propext, Quot.sound]
q9mr_cyclotome_fixed   : [propext, Quot.sound]
q9mr_zeta9_fixed       : [propext, Quot.sound]
q9mr_aut_mu9_new_layer : [propext, Quot.sound]
q9mr_weil_e9_left      : [propext, Quot.sound]
q9mr_weil_e9_right     : [propext, Quot.sound]
q9mr_weil_fails_on_M   : [propext, Quot.sound]
q9mr_exists            : [propext, Quot.sound]
q9mr_sigma_fixes_mu3   : [propext, Quot.sound]
q9mr_sigma_zeta9       : [propext, Quot.sound]
q9mr_sigma_zeta9_ne    : [propext, Quot.sound]
```
全対象ちょうど `[propext, Quot.sound]`（新規 Classical.choice 皆無）。

禁止タクティク grep: `sorry/admit/simp/decide/by_cases/rcases/ring/nlinarith` の唯一のヒットは日本語コメント `sorry 皆無`。omega は 13 箇所・すべて純 Int 付値/指数方程式（`q9mr_aexp` の 6a+v=0・シフト 54k・指数 hexp0/hng 等）で pure-Int OK。

`lake build IUT.Q3Mu9Rigidity`: EXIT=0（102 jobs replayed successfully・no sorry）。

---

## 6. 台帳判定（0 前進・pre-credit しない）

level-3 precedent（graph-meta A complete_note に記録済）: q3m3r は kill 機構を持つが「機構レベル止まり」で tmi の実 ℤ₃^× 不定性には未接続だった＝A7 監査上限 #1。実際に display を動かしたのは**橋 q3mb（Q3Mu3TmzBridge）**で、A7 0.47→0.49・柱A 53→54 を移した。

q9mr は同一規律の level-9 版: **機構レベルの新層 kill**を建てるが、display を動かす**橋 q9mb は未建設**。kill を tmi 側の実対象に接続する橋がまだ無い以上、kill の成果を display に**先取り計上（pre-credit）しない**。

- `target_ledger.json`: **不変**（A1..A9 の status いずれも変更なし）。
- `compute_complete_pct.py`: `{"A": 54, "B": 18, "C": 41, "D": 18, "E": 42}`（実行確認）。A=**54** 据え置き。
- `graph-meta.json` pillar-A `complete_note`: 本監査の landing（real+axiom-clean・新層 kill 機構 genuine・σ=q3kSigma が killed automorphism・0 前進）を**追記のみ**（既存記録は改変せず）。

---

## 7. 正直な限定（消さない・弱めない・本ファイルヘッダ §4 継承）

本監査はヘッダの正直申告を確認・支持する:
1. 殺す新スライスは核 {1,4,7}∖{1}（位数 3・(1+3ℤ₃)/(1+9ℤ₃)）のみ。1+9ℤ₃（n≥3 全層）は SURVIVES。
2. 機構レベル止まり（tmzLimit への比較橋を含まず・display は q9mb 待ち）。
3. q=3⁹ は忠実部分ケースの 2 乗トリック（[EtTh] の q^{1/l} 添加そのものでない）。
4. 位数 2 側 M 上共役 τ は named non-goal（re-label ゆえ建てない）。
5. 実テータ関数・π₁ 同定・Galois 作用はゼロ（q3m3r/q9mt 系の限定を継承）。

以上、q9mr は申告どおり **real + axiom-clean の新層 kill 機構の先行建設**であり、**complete_pct 0 前進**が正しい。
