# 独立再監査: `IUT/Q3KummerDualityReal.lean`（q9kd・B6）— 2026-07-11

**監査者**: 独立敵対的監査（本コードを書いていない・既定＝懐疑）。**対象**: `IUT/Q3KummerDualityReal.lean`（prefix `q9kd`・593 行・commit 53fe075）。**申告**: [実／(a) 昇格]・柱B B6（Kummer 理論・weight=10・現 status=0）・予測 0→0.15–0.25。**判定方針**: .lean 定理本体の読解のみを根拠にする。**本記録は report-only**（target_ledger.json / graph-meta.json は編集しない・並走監査と親が一括適用）。

---

## 0. 結論（3 文）

(a) 正確性は全軸 YES: q9kdG は実環 O_M の**実環自己同型** ⟨σ⟩（σ=q3kSigma・位数ちょうど 3・L₂ を固定）を担う本物の 3 元群であり、Kummer 双対は非自明類＋両側非退化＋Hom 完全枚挙＋全単射まで**この拡大で完全**に閉じている。
(b) 二重計上なし: q9ci_no_cbrt_zeta（柱A）と q9c_m_mu3_complete（柱A）は `exact`/`obtain` で**消費**され再証明・再主張されていない（本モジュールの新規内容は群提示 ℤ×U₂ 上の Kummer 類定式化と有限商 Gal の完全双対に限定）。lake build EXIT=0（98 jobs）・主要 8 定理＋補助すべて #print axioms=[propext, Quot.sound]（q9kdG は無公理）・禁止タクティク 0・sorry 0。
(c) **s_B6 = 0.15** を採る（敵対的中心）。第一級の実 Galois 群＋完全双対という質的前進で 0.10 の「cocycle 1 実例」床を上回るが、単一拡大・n=3・有限商のみ（副有限 G_{L₂} 不在）・⟨[ζ₃]⟩ 側が索引模型・H¹ 形式論ゼロの上限で 0.20–0.25 に届かない。B1 が 0.5 据え置きなら Σ_B=19.0 → 表示 18→19（+1）。

---

## 1. 正確性検査

### 1.1 実 Galois 群は本物か → YES

- **σ=q3kSigma は実環 O_M の実環自己同型**。`Q3KummerCubic.lean:504` 定義 σ(a,b,c)=(a, ζ₃b, ζ₃²c)（実 ℤ₃=zpRing 3 由来の実 O_M=L₂[Y]/(Y³−ζ₃) 上）。乗法性 `q3k_sigma_mul`（:518・ζ₃·ζ₃²=1 の実簡約で完全証明）・加法性 `q9kd_sigma_add`（q9kd:64・成分分配）・σ(1)=1（`q3k_sigma_one`）＝形式群でも代理でもない**本物の環自己同型**。
- **L₂ を固定（相対 Galois）**: `q9kd_sigma_fixes_base`（:55）σ(embed n)=embed n を q3k_ext で証明（第 0 成分不動・第 1,2 成分は ζ·0=0）。⟨σ⟩=Gal(M/L₂) の相対性が本物。
- **位数ちょうど 3**: σ³=id（`q9kd_sigma3_id`＝q3k_sigma3_id 消費）・σ≠id（`q9kd_sigma_ne_id`:82・σζ₉=ζ₃ζ₉≠ζ₉）・σ²≠id（`q9kd_sigma2_ne_id`:91）。3 条件で位数厳密 3。
- **q9kdG は本物の 3 元群**: inductive q9kdGCar（e,s,s2）＋Cayley 表 q9kdGMul＋逆元＋群公理（結合律は全 27 ケース cases、`#print axioms q9kdG` は**無公理**）。
- **q9kdAct が実作用の準同型**: `q9kd_act_mul`（:160）act(gh)=act(g)∘act(h) を全 9 ケースで証明（e↦id, s↦σ, s2↦σ²、q3k_sigma2_comp・q3k_sigma3_id 消費）＝⟨σ⟩ が実 O_M に忠実作用。
- **q9kdMu3=μ₃(O_M) は本物の実 Grp**: carrier={x:q3kCar // x³=1}（実 O_M の実部分集合）・乗法閉性 q9kd_mu3_mul_closed（(xy)³=x³y³ の実 6 因子再配置）・逆元 x⁻¹=x²・群公理充填。索引 ℤ/3 模型でない。

### 1.2 Kummer 双対は完全かつ本物か → YES

- **cocycle**: `q9kd_cocycle`（:102）σζ₉=embed(ζ₃)·ζ₉（＋σ²版 :112）＝実コサイクルの座標計算。
- **指標 χ:Hom**: `q9kdChi`（:305）Gal(M/L₂)→μ₃(O_M) が map_mul 付き本物の群準同型（Hom は map+map_mul の genuine 群準同型構造・:125）。
- **忠実性**: `q9kd_chi_faithful`（:328）ker χ={e}（s,s2 は embed ζ₃・ζ₃²≠1）。
- **類の非自明性（消費であり再証明でない・後述 §2）**: `q9kd_class_nontrivial`（:340）¬∃ g∈q3rqLx, g³=(0,ζ₃U)。q3rqLx=prodGrp intGrp q3rqU=**実 L₂^×=ℤ×U₂**（実群提示）。証明は第 2 成分へ射影→単数 val 抽出→`q9ci_no_cbrt_zeta g.2.val hval`（:350）で柱A 定理に帰着。新規は群提示上への持ち上げ（付値成分 3n=0 処理＋単数成分の O 帰着）と Kummer 類定式化のみ。
- **両側非退化**: `q9kd_pairing_nondeg_left`（:413）σʲζ₉=ζ₉⟹j=e／`q9kd_pairing_nondeg_right`（:421）σ(ζ₉ᵏ)=ζ₉ᵏ⟹k=e。両方向とも実 σ 作用の値で判定・空虚でない。
- **Hom 完全枚挙（消費・後述 §2）**: `q9kd_hom_exhaust`（:465）任意 φ の φ(s) は μ₃ 3 元のいずれか＝`q9c_m_mu3_complete (φ.map s).val (φ.map s).property`（:470）を消費。`q9kd_hom_complete`（:496）Hom(⟨σ⟩,μ₃)={χ⁰,χ¹,χ²}。
- **Kummer 同型＝全単射**: `q9kd_kummer_iso`（:553）＝surj（`q9kd_kummer_iso_surj`・hom_complete の束ね）∧ inj（`q9kd_kummer_iso_inj`・χᵏ の σ 値 q9kdSVal の相異＝z_ne_one/zsq_ne_one/z_ne_zsq）。**空虚でない真の全単射**（定義域 q9kdGCar・値域 Hom 双方ちょうど 3 元）。

### 1.3 axiom / 禁止タクティク → CLEAN

- `lake build IUT.Q3KummerDualityReal` EXIT=0（98 jobs・監査者が /root/lean4/bin/lake で自ら実行）。
- `lake env lean` で列挙: q9kd_chi_hom / q9kd_chi_faithful / q9kd_class_nontrivial / q9kd_pairing_nondeg_left / q9kd_pairing_nondeg_right / q9kd_hom_exhaust / q9kd_hom_complete / q9kd_kummer_iso / q9kd_kummer_iso_surj / q9kd_kummer_iso_inj / q9kd_exists / q9kdChi / q9kdMu3 / q9kd_act_mul **すべて [propext, Quot.sound]**（q9kdG は無公理）＝新規 Classical.choice 皆無。
- 禁止タクティク grep（sorry/admit/decide/simp/nlinarith/ring/by_cases/rcases/omega/native_decide）: ヒットは日本語コメント「sorry 皆無」1 件のみ＝実タクティク 0。

---

## 2. 二重計上検査（消費 vs 再主張）— 独立評決

scope doc `pillar-B-kummer-ramification-scope-2026-07-11.md` §4.1 の評決を本体読解で独立再検証:

| 論点 | 独立評決 |
|---|---|
| ζ₃ の 3 乗根非存在（`q9ci_no_cbrt_zeta`・柱A・Q3KummerCubeIdent:628） | **消費で確定**。q9kd:350 で `exact q9ci_no_cbrt_zeta ...`。3 乗根非存在そのものは再証明せず、群提示 ℤ×U₂ 上への持ち上げのみが新規。ヘッダ（:19-20）に「消費・本モジュールの新規主張ではない」と明記済み。 |
| O_M 内 μ₃ 完全性（`q9c_m_mu3_complete`・柱A・Q3Mu9Completeness:1176） | **消費で確定**。q9kd:470 で `obtain ... := q9c_m_mu3_complete ...`。μ₃/μ₉ 完全性は一切再主張しない。 |
| 実指標 T3–T5 vs KummerCharReal（M349F）/KummerTheory（M320F） | **新**。既存は抽象 IUTField K＋FieldAut K＋witness n 乗根の上（KummerCharReal ヘッダの正直限定「完全 Kummer 双対は外部仮説」）。q3k は total inverse を持たず IUTField でない（A2 恒久限定）ため既存抽象機構は M/L₂ を型として受け取れない。実 Galois 群上の実指標のインスタンスはコードベース初。 |
| 完全対・同型 T8–T10 vs KummerExact（M345F） | **新**。M345F は全射性を明示仮説 hsurj で受ける（ヘッダ確認）。q9kd は有限具体ケースで全射側を無仮説に閉じる（Hom 枚挙＝q9c 消費）。 |
| σ(ζ₉) 値 vs Q3Mu9Rigidity（q9mr） | **クリア**。素材 σ(Y)=ζ₃Y は共通だが q9mr は剛性 kill 機構・q9kd は Kummer 双対＝別定理。重複補題を作らず q9yp/q3k を import。 |

**総合**: 二重計上なし。柱B 既存 Kummer チェーン（M320F/M345F/M349F=抽象体＋witness/仮説形）に実 Galois 群上のインスタンスは存在せず、q9kd が初。scope §4.1 の評決に同意する。

---

## 3. s_B6 の敵対的決定

### 3.1 上げ要因

1. **コードベース初の「Galois 群＝実際の環自己同型の群」**（AUDIT_RUBRIC 準拠）。graph-meta 柱B note が B2–B6=0 の根拠とした「コード全体を通じて実 Galois 群が一つも存在しない」を**偽にした**——q3kSigma（実 O_M の実環自己同型・位数厳密 3・L₂ 固定）が Gal(M/L₂) の実生成元。これが本項の decisive fact。
2. **cocycle 1 実例に留まらず完全双対**: 非自明類（実 L₂^×=ℤ×U₂ 上）＋両側非退化＋Hom 完全枚挙＋真の全単射＝この拡大での Kummer 同型の完全証明。全軸 clean・非空虚・実定理消費。0.10（cocycle 1 実例）床を質的に上回る。

### 3.2 下げ要因

1. **単一拡大・n=3・類 1 個**。忠実な部分ケース 1 個であり L₂^×/(L₂^×)³ の全体構造は未計算。
2. **Galois は有限商 ⟨σ⟩≅ℤ/3 のみ**。副有限 G_{L₂}・絶対 Galois 群・逆極限ゼロ。一般 H¹ 形式論（galH1Module）への接続なし（ヘッダ正直限定 1）。「実 Galois コホモロジー」という B6 題目の cohomology 形式は不在（H¹(ℤ/3,μ₃) 相当の具体対まで）。
3. **⟨[ζ₃]⟩ 側が索引模型**: `q9kd_kummer_iso` の定義域 q9kdChiPow:q9kdGCar→Hom は抽象索引群 q9kdGCar（指数 k）を ⟨[ζ₃]⟩ の代用にしている。類の非自明性は実 L₂^× 上で別途証明されるが、双対の「⟨[ζ₃]⟩≅Hom」は index↔Hom の全単射＋別立ての類非自明性であって、L₂^×/(L₂^×)³ の部分商として literally 構成した ⟨[ζ₃]⟩ ではない。
4. O_M のみ（体化なし・A2 恒久限定継承）・実テータ関数ゼロ・π₁ 同定ゼロ。weight 10（柱B 最小項目）。

### 3.3 決定と算術

**s_B6 = 0.15**（敵対的中心）。

理由: §3.1 の完全双対＋初の実 Galois 群は 0.10 床を明確に超えるが、§3.2（最小ケース単発・有限商のみ・⟨[ζ₃]⟩ 索引模型・H¹/副有限/体ゼロ）が 0.20–0.25 を阻む。特に「完全双対」の completeness は 3 元群×μ₃ という**最小非自明対象**に対する完全性であり、かつ双対の class 側が索引模型である点が 0.20 以上への昇格を許さない（0.25 は「complete duality を満点で信用」した場合だが、class 側の literal 構成不在と単発 n=3 でそこまでは信用できない）。0.10 に落とさないのは、両側非退化＋Hom 完全枚挙＋真の全単射＋実定理 2 本消費が「cocycle 1 実例」を質的に超える完結した実数学だから。

**表示含意（B1=0.5 据え置き時）**: Σ_B = 20·0.5 + 20·0 + 20·0 + 15·0 + 15·0.5 + 10·s_B6 = 10.0 + 7.5 + 10·s_B6 = 17.5 + 10·s_B6。
- s_B6=0.10 → Σ=18.5 → round-half-even → **18（不動）**
- **s_B6=0.15 → Σ=19.0 → 19（+1）** ← 本決定
- s_B6=0.25 → Σ=20.0 → 20（+2）

本決定 s_B6=0.15 は、B1 が 0.5 のままなら**柱B 表示 18→19（+1）**を含意する。B1 の値は並走監査が決めるため、combined Σ_B は親が両決定を合算して確定する（本記録は s_B6 のみを決定）。

---

## 4. 評決サマリ

- 実 Galois 群 genuine? **YES**（実環自己同型 ⟨σ⟩・位数厳密 3・L₂ 固定・q9kdMu3 実群）
- 双対 complete? **YES**（非自明類＋両側非退化＋Hom 完全枚挙＋真の全単射）
- 消費であり再主張でない? **YES**（q9ci_no_cbrt_zeta・q9c_m_mu3_complete とも `exact`/`obtain` 消費）
- axiom clean? **YES**（全対象 [propext, Quot.sound]・q9kdG 無公理・禁止タクティク 0・sorry 0・build EXIT=0）
- **s_B6 = 0.15**（B1=0.5 なら Σ_B=19.0 → 表示 18→19 +1）
