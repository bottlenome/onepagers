# 数学的厳密さビュー — 索引

論文の記号法に準拠し、定義・定理・証明の骨格を厳密に記述する。

---

## ファイル構成

```
rigorous/
├── 00_index.md                 ← いまここ
├── 01_initial_theta_data.md    ← 初期シータデータ [IUT I, Def 3.1]
├── 02_hodge_theater.md         ← ホッジシアターの構成 [IUT I, §3–§6]
├── 03_theta_link.md            ← Θ-リンクと Θ_gau^{×μ}-リンク [IUT I–II]
├── 04_log_theta_lattice.md     ← 対数テータ格子 [IUT III, §1]
├── 05_multiradial.md           ← マルチラジアルアルゴリズム [IUT III, §2–§3]
├── 06_main_theorems.md         ← 主定理群 [IUT III 定理A,B / IUT IV 定理A]
├── 07_proof_skeleton.md        ← 証明の論理的骨格（全巻を通じた依存関係）
└── 08_corollary_3_12.md        ← 系3.12の争点（学会が受容していない核心）
```

---

## 証明の全体的な論理フロー

```
初期シータデータ [IUT I, Def 3.1]
    ↓
ホッジシアターの構成 [IUT I, §3–§6]
    ↓
Θ-リンクの構成 [IUT I, Def 3.8]
    ↓
Θ_gau^{×μ}-リンクの構成 [IUT II, §3–§4]
    ↓
マルチラジアリティの確立 [IUT II, §1–§2]
    ↓
共役同期の確立 [IUT II, §2]
    ↓
対数テータ格子の構成 [IUT III, §1]
    ↓
LGP-モノイドの構成 [IUT III, §3]
    ↓
★ マルチラジアル分裂モノイドの構成 [IUT III, Thm A]
    ↓
★★ 対数体積の見積もり [IUT III, Thm B / Cor 3.12]  ← 争点
    ↓
具体的な対数体積計算 [IUT IV, §1, Thm 1.10]
    ↓
一般楕円曲線への帰着 [IUT IV, §2 + GenEll]
    ↓
ディオファンタス不等式 [IUT IV, Cor 2.3 = Thm A]
    ↓
ABC予想 / Szpiro予想 / Vojta予想
```

★ = 理論の技術的頂点、★★ = 論争の焦点
