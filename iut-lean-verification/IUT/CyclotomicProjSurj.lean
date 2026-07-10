/-
  IUT/CyclotomicProjSurj.lean — CPS（A3 M4c: 逆極限
  Gal(ℚ(ζ_{3^∞})/ℚ) の各段への射影の全射性・choice-free・指標分裂）

  ── 主要成果の分類: **[実／本物建設(b)]**（骨格・模型・代理でなく、実 ℚ・実円分塔
     の逆極限 profinite Galois 群 `ctlProfinite` = Gal(ℚ(ζ_{3^∞})/ℚ)（ctl・M3）
     の各段 n への射影 `profPi1_proj ctlTower n` が**全射である**ことを本物に
     確立する）。設計 `audit/A3-m4-character-iso-detail-2026-07-09.md` §4.2–4.3
     の指標分裂ルートに従う: τ の指標 a := (cliChar n).map τ を取り（cci・M4a）、
     単数側の射影全射性 `zps_proj_surjective`（zps・M4b、witness は閉じた式
     `a % 3^{m+1}`）で単数側整合族 u を得て、`cliFrom.map u`（cli・M4b の逆極限
     同型）を Gal 側の原像として提出する。射影成分 = `cliAut n (u.val n)` は
     `cliFrom`/`profPi1_proj` の定義から rfl 級で開き、`u.val n = a`（zps の
     witness の性質）と `cci_left_inv` の cli ラッパ `cli_aut_char` で閉じる。
     **どの段階でも ∃ から witness を取り出さない**——witness は全て閉じた式
     （zps 側は `a % 3^{m+1}`、Gal 側は `cliAut n` による像）であり、素朴な
     Mittag-Leffler が要求する可算従属選択（DC）を、本塔固有の指標同型による
     正準切断で回避する（設計 §4.1–4.2 の分析どおり）。

  **complete_pct 影響**: A3 M4c——**逆極限 profinite Gal(ℚ(ζ_{3^∞})/ℚ) の各段
  Gal(ℚ(ζ_{3^{n+1}})/ℚ) への射影 `profPi1_proj ctlTower n` が全射（choice-free・
  指標分裂）**であることを確立し、極限の非退化を本物に閉じる。これで
  M4（指標同型 cci ＋ 逆極限同型 cli ＋ 射影全射性 cps）が完成——円分切片
  Gal(ℚ(ζ_{3^∞})/ℚ) ≅ ℤ₃^× の逆極限側の建設が打ち止めになる（監査残欠 (ii)
  の discharge）。本ファイル単体では complete_pct 未設定（M4 完成として
  独立監査で反映・設計見込み A3 0.75）。

  内容（設計 audit/A3-m4-character-iso-detail-2026-07-09.md §4.2–4.3）:
   * `cps_proj_surjective` — ★本丸: 各段 n への射影の全射性（指標分裂・
     choice-free）。監査残欠 (ii)（逆極限射影全射性）の discharge。
   * `cps_nontrivial` — 極限の非退化（`cliFrom` による `zps_nontrivial` の
     定数族 2 の押し出し、`cli_right_inv`＋`Hom.map_one` で分離）。
   * `cps_example0` — n=0 実例（検算）: `ctlGal 0 = Gal(ℚ(ζ₃)/ℚ)` の非自明元
     σ_2（char=2）に `cps_proj_surjective` が実際に原像を与えることの確認、
     かつ σ_2 ≠ 1 の分離（`cli_char_aut`＋`Hom.map_one`）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (i)   p = 3・ℚ 上・円分塔 ℚ(ζ_{3^{n+1}}) の忠実な部分ケース（一般 p は含めない）。
   (ii)  **一般の有限群逆系に対する Mittag-Leffler 定理そのもの**は choice-free
         に形式化していない（設計 §4.1 の正直な分析どおり、本コードベースの
         機構では一般には道が無い）。本ファイルが closed に閉じるのは、**本塔が
         全段で指標により (ℤ/3^{n+1})^× と同型**であり、その同型がデータ
         （cci/cli）で書かれているという**本塔固有の性質**に依存する
         正準切断による——一般化はしない。
   (iii) これは円分切片 Gal(ℚ(ζ_{3^∞})/ℚ) であって実 G_ℚ そのものではない
         （G_ℚ の可解商・Kronecker–Weber 部分に対応する副有限商の一つ・
         ctl/cli 正直申告を継承）。

  全て選択公理不使用（新規 `Classical.choice` を証明本体に導入しない・
  propext/Quot.sound のみ）。`obtain` によるパターンマッチは**目標が Prop
  （∃ 文）である場合の Exists.elim 相当**であり choice を要しない（zps/cli
  で既に踏襲済みの規約）——witness 自体は全て閉じた式（`zpsWitnessFam`・
  `cliFrom`/`cliAut` の像）で与える。禁止タクティク（simp/decide/by_cases/
  rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）不使用。
  新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/dashboard/graph/tools
  は不更新・親が統合）。
-/
import IUT.CyclotomicLimitIso
import IUT.Zmod3PowUnitsSystem
import IUT.CyclotomicTowerLimit
import IUT.CyclotomicCharIso

namespace IUT

/-! ## CPS-1: ★射影全射性（監査残欠 (ii) の discharge・M4c 本丸） -/

/-- **CPS-1: 射影全射性** — 逆極限 `ctlProfinite` = Gal(ℚ(ζ_{3^∞})/ℚ) の各段
    n への射影 `profPi1_proj ctlTower n` は全射。指標分裂（choice-free）:
    τ の指標 `a := (cliChar n).map τ` を取り、`zps_proj_surjective` で単数側
    整合族 u（witness は閉じた式 `a % 3^{m+1}`）を得て、`cliFrom.map u` を
    Gal 側の原像として提出する。射影成分は `(cliFrom.map u).val n =
    (cliAut n).map (u.val n)`（`cliFrom`/`profPi1_proj`/`limitProj` の定義から
    rfl 級）、`u.val n = a`（`hu`）で `(cliAut n).map a` に、
    `cli_aut_char`（= cci_left_inv の cli ラッパ）で `τ` に一致する。 -/
theorem cps_proj_surjective (n : Nat) :
    ∀ τ : (ctlGal n).carrier,
      ∃ s : ctlProfinite.carrier, (profPi1_proj ctlTower n).map s = τ := by
  intro τ
  obtain ⟨u, hu⟩ := zps_proj_surjective n ((cliChar n).map τ)
  refine ⟨cliFrom.map u, ?_⟩
  show (cliAut n).map (u.val n) = τ
  have hu' : u.val n = (cliChar n).map τ := hu
  rw [hu']
  exact cli_aut_char n τ

/-! ## CPS-2: 極限の非退化（監査文言「恒等以外の整合族の存在」への直接回答） -/

/-- **CPS-2: `ctlProfinite` の非退化** — 恒等以外の整合族が存在する
    （`cliFrom` による `zps_nontrivial` の定数族 2 の押し出し）。もし
    `cliFrom.map u = ctlProfinite.one` なら、両辺に `cliTo` を施し
    `cli_right_inv`（`cliTo.map (cliFrom.map u) = u`）と `Hom.map_one`
    （`cliTo.map ctlProfinite.one = zpsLimit.one`）で `u = zpsLimit.one` が
    従い、`zps_nontrivial` の非自明性に反する。 -/
theorem cps_nontrivial : ∃ s : ctlProfinite.carrier, s ≠ ctlProfinite.one := by
  obtain ⟨u, hu⟩ := zps_nontrivial
  refine ⟨cliFrom.map u, ?_⟩
  intro heq
  apply hu
  have h1 : cliTo.map (cliFrom.map u) = cliTo.map ctlProfinite.one :=
    congrArg cliTo.map heq
  rw [cli_right_inv u, Hom.map_one cliTo] at h1
  exact h1

/-! ## CPS-3: n=0 実例（検算・監査向け） -/

/-- **CPS-3: n=0 実例（検算）** — `ctlGal 0 = Gal(ℚ(ζ₃)/ℚ)` の非自明元 σ_2
    （char=2、`cliAut 0` による `zpsConstFam 0`（値 2）の像）に対し、
    `cps_proj_surjective` が実際に原像 s を与えることを確認する。あわせて
    σ_2 ≠ 1（`cli_char_aut`＋`Hom.map_one` で char を比較し 2 ≠ 1 に帰着）を
    示し、`cps_proj_surjective` が空虚でない非自明ケースをカバーすることを
    検算する。 -/
theorem cps_example0 :
    ∃ s : ctlProfinite.carrier,
      (profPi1_proj ctlTower 0).map s = (cliAut 0).map (zpsConstFam 0)
        ∧ (cliAut 0).map (zpsConstFam 0) ≠ (ctlGal 0).one := by
  obtain ⟨s, hs⟩ := cps_proj_surjective 0 ((cliAut 0).map (zpsConstFam 0))
  refine ⟨s, hs, ?_⟩
  intro heq
  have h1 : (cliChar 0).map ((cliAut 0).map (zpsConstFam 0))
      = (cliChar 0).map (ctlGal 0).one := congrArg (cliChar 0).map heq
  rw [cli_char_aut 0 (zpsConstFam 0), Hom.map_one (cliChar 0)] at h1
  have h2 : (2 : Nat) = 1 := congrArg (fun x => x.val) h1
  omega

end IUT
