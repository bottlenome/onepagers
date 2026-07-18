# 独立敵対再監査記録: Q3HerbrandReal (q9hb) — 柱B B4（2026-07-11）

**種別**: 独立敵対監査（opus・フレッシュ文脈・report-only）
**対象**: `IUT/Q3HerbrandReal.lean`（q9hb・195行）
**審査**: 柱B B4「実 Hasse–Arf / 上付き番号」（現 0.10・weight 15・正直に薄い）

## 判定: s_B4 = 0.13（+0.03）

Herbrand φ 逆関数は q9ha に無かった genuine な新規対象（q9ha は ψ のみ）・ψ↔φ 往復完成は実の狭い深化。だが σ² 側と「Hasse-Arf」/「全群」の大半は re-bank か空虚。ℤ/3 単一 break の退化インスタンス・ハードコード Nat ψ/φ ゆえ +0.03 が正直な増分。

## 根拠（真水）
`q9hbPhi`（Herbrand φ・up→down 逆・q9ha に不在）・`q9hb_phi_psi`（φ∘ψ=id on v≤3・実 4 点有限逆検査・例 φ(ψ(3))=φ(5)=3 が slope-3/slope-1/3 双対を行使・非タウトロジー）・`q9hb_psi_phi`（ψ∘φ=id・像 {0,1,2,5} 上に正直制限）。`q9hb_upper_sigma2_real` が q9ha の σ 限定を σ² へ拡張・q9ha 限定#4 を正当に解除。真水はこれだけ。

## 二重計上・空虚
- `q9hb_upper_sigma2_G2_real` = `q9wr_G2_mem.2` **verbatim**（B1 re-bank・新規ゼロ）。
- `q9hb_upper_sigma2_G3_trivial_real` — 実質は `q9ac_sigma2_G3_trivial`（B3 既計上）を `q9ha_not_dvd_descent` で上付き π₉⁶ に relabel。genuine だが極小。
- `q9hb_hasse_arf_integer_jumps` — **公理なし（全 rfl）**確認。実 ψ/φ 上の Nat 計算だが数学的に空虚（Nat リテラル 2 の「整数着地」は ψ(2)=2 以上の内容なし）＝padding。
- `q9hb_upper_full_group` — σ(q9ha)+σ²(新)+恒等（`q9hb_dvd_self_sub` 0=d·0 空虚）の束ね。
- slope 恒等 — ハードコード関数上の trivial rfl。

## 正直性: ほぼ懸念なし
ヘッダが「単一 ℤ/3 拡大・単一 break のみ」「一般 Hasse–Arf 定理でない低次元インスタンス」「整数性の数値内容は退化的」「ψ/φ は明示 Nat 区分線形（一般 filtration-jump 理論でない）」「ψ∘φ は像上のみ」を前面明記。CONSUMED リストが σ²∈G^2→q9wr・σ² break→q9ac・ψ→q9ha を正しく帰属。軽微: `q9hb_hasse_arf_integer_jumps` の名は退化 rfl に対し grand だが docstring が退化を明記＝過大主張でない。

## 軸チェック: クリーン
`q9hb_phi_psi`・`q9hb_upper_sigma2_real`・`q9hb_upper_full_group`・`q9hb_exists` → `[propext, Quot.sound]`；`q9hb_psi_phi`・`q9hb_hasse_arf_integer_jumps` → 公理なし。

## 次の 0.1
非退化 Hasse-Arf インスタンス（複数 break または ℤ/3 より大きい群で ψ/φ が真に非整数中間 slope を持ち整数性が実定理になる）・ハードコード Nat でなく実 v_M/filtration-jump 理論駆動・literal {1,σ,σ²} でなく任意群元上の抽象上付き番号。
