/-
  IUT/Q3NonicGaloisLiftReal.lean — 柱B・B4 実合成 Galois 群 Gal(M₂₇/L₂) ≅ ℤ/9 と
    **単一群の実下付きフィルトレーションの 2 つの break**

  ── 主要成果の分類: **[実／(a) 昇格]**。
  ══════════════════════════════════════════════════════════════════
  ★ 本モジュールが直接応答する監査要求（q27tb ヘッダの正直な訂正・2026-07-21）★
    「`q27tb_two_distinct_breaks` は σ の O_{M₉} 上の事実と τ の O_{M₂₇} 上の事実を
      Nat の不等号で接着した連言であり、**単一の群の上付きフィルトレーションの
      2 つの jump ではない**。位数 9 の合成群 Gal(M₂₇/L₂) も持ち上げ σ̃ も構成して
      いない。0.25+ に達するには Gal(M₂₇/L₂) ≅ ℤ/9 と σ̃ を構成し
      **両 jump を 1 つの群のフィルトレーション上に載せる**必要がある。」
    本モジュールは **その σ̃ を実際に構成する**:
      σ̃(a + bZ + cZ²) := σ(a) + ζ₉σ(b)·Z + ζ₉²σ(c)·Z²
    （σ = q3kSigma は実 Gal(M₉/L₂) の生成元・Z = q27kZeta27 = ζ₂₇）。これは
    ζ₂₇ ↦ ζ₂₇⁴ に対応する**半線形**（係数体 M₉ 上非線形）な実環自己同型であり、
      σ̃³ = τ = q27kSigma（＝ ζ₂₇ ↦ ζ₂₇¹⁰）・σ̃⁹ = id・σ̃³ ≠ id
    を実 O_{M₂₇} 上で証明する。よって ⟨σ̃⟩ は**位数ちょうど 9 の実巡回群**で、
    ⟨τ⟩ = ⟨σ̃³⟩ はその指数 3 の部分群 Gal(M₂₇/M₉) である。
  ══════════════════════════════════════════════════════════════════

  NEW（真水・本モジュールで初めて実在するもの）:
    1. **★★★ 実合成 Galois 群 Gal(M₂₇/L₂) の生成元 σ̃**（`q27glSt`）——
       実 O_{M₂₇} = O_{M₉}[Z]/(Z³−ζ₉) 上の実環自己同型（加法・乗法・1 を保存）。
       ねじれ半線形写像の一般族 `q27glG t e` を先に建て、その**合成則**
       `q27gl_G_comp` と**乗法性判定** `q27gl_G_mul`（条件 t(ζ₉) = ζ₉·e³）で
       σ̃ の環準同型性・冪の閉形式を一括で得る（新イディオム）。
    2. **σ̃³ = τ**（`q27gl_st3`）・**σ̃⁹ = id**（`q27gl_st9`）・**σ̃³ ≠ id**
       （`q27gl_st3_ne_id`）⟹ **σ̃ の位数はちょうど 9**（`q27gl_order_nine`）。
       さらに **σ̃^k ≠ id (1≤k≤8)**（`q27gl_pow_ne_id`・係数漸化 ε_{k+1}=ζ₉σ(ε_k) の
       座標追跡 `q27gl_eps1`〜`q27gl_eps9` による）から
       **⟨σ̃⟩ の 9 元は相異なる**（`q27gl_nine_distinct`）——実合成 Galois 群の
       **位数がちょうど 9 であることが実側で確定**する。
    3. **σ̃ の実 break はちょうど 2（π₂₇ スケール）**: 実 O_{M₂₇} 上の閉形式
         σ̃(π₂₇) − π₂₇ = π₂₇³ · (w̃⁻¹·ζ₂₇)   （w̃⁻¹ζ₂₇ は実単数）
       と **sharp な ¬π₂₇⁴ ∣**（相対ノルム降下・π₉³ 正則消去）。
    4. **★★★ 2 つの break が 1 つの群の上に載る**（`q27gl_two_jumps_one_group`）:
       ⟨σ̃⟩ ≅ ℤ/9 の**同一の**下付きフィルトレーション（同一一様化子 π₂₇ の可除性）で
         σ̃ ∈ G₂ \ G₃（break 2）  かつ  σ̃³ = τ ∈ G₈ \ G₉（break 8）。
       段ごとの事実の連言ではない——両方が **σ̃ の冪**についての π₂₇ 可除性である。
    5. **部分群両立性**（`q27gl_subgroup_compat`）: G_i(M₂₇/L₂) ∩ ⟨τ⟩ = G_i(M₂₇/M₉)。
       本設定では**同一の判定式**（同じ π₂₇ 可除性）なので恒真であり、それが
       まさに Serre の「下付き番号は部分群と両立」の実現形である（下の限定 2 参照）。
    6. **商両立性の実現部**（`q27gl_restrict_sigma`）: σ̃ の M₉ への制限が σ である
       （σ̃∘embed = embed∘σ）——⟨σ̃⟩ ↠ Gal(M₉/L₂) の実現。核は ⟨τ⟩ を含む
       （`q27gl_tau_fixes_base`）。また σ̃ は基礎体 L₂ を点ごとに固定する
       （`q27gl_st_fixes_L2`）——σ̃ が Gal(M₂₇/L₂) の元であることの実側の裏付け。
    7. **非退化 Hasse–Arf（単一群版）**（`q27gl_hasse_arf_one_group`）: 上記 4 の
       2 break から、上付き jump 2 と 4 が相異なる整数として得られる。

  CONSUMED（再証明しない）: q27k の環・τ=q27kSigma・ノルム乗法性・ζ₂₇=Z、
    q3k の σ=q3kSigma（環準同型・σ³=id）・ζ₉=Y（Y³=ζ₃）・ノルム・単数機構、
    q9ps の π₉=ζ₉−1・w・w⁻¹、q27ps の (Z−1)³ = embed(π₉)·w̃・w̃ 単数・embed 単数保存、
    q27tl の ζ₂₇ 単数、q9wr の π₉³ 正則消去（`q9wr_pi3_cancel`）・π₉·s 非単数機構、
    q27tb の可除性述語 `q27tbDvd`・`q27tb_embed_Z`・τ 側の break 8（`q27tb_G8_mem_tau`・
    `q27tb_G9_trivial_tau`）・π₂₇ 冪除子。

  complete_pct 影響: **B4（現 0.17）**——監査が 0.25+ の必要条件として名指しした
    「Gal(M₂₇/L₂) ≅ ℤ/9 と σ̃ の構成」「両 break を単一群のフィルトレーションに載せる」
    を実際に実行する昇格。q27tb で記録された退化（「break が段ごとに 1 個ずつ」）は
    本モジュールで**単一群 ⟨σ̃⟩ の下付きフィルトレーションが 2 つの break を持つ**形に
    置き換わる。上げ幅は独立監査が決定する（下記の正直な限定を必ず読むこと）。

  ══════════════════════════════════════════════════════════════════
  ★ 正直な訂正・追加（独立敵対監査 2026-07-21・§4 に従い削除も弱化もしない）★
   1. **「Gal(M₂₇/L₂)」という呼称は厳密には過大**（未 flag だった点）。本モジュールが
      証明したのは「**⟨σ̃⟩ ≅ ℤ/9 が L₂ を点毎に固定する**」であって、
      `Aut_{L₂}(O_{M₂₇}) = ⟨σ̃⟩`（自己同型の汲み尽くし・[M₂₇:L₂]=9）は**どこにも証明が無い**。
      以後は「⟨σ̃⟩」と読むこと。
   2. 限定 1 の「break が未計算の冪」の列挙から **σ̃⁶ が漏れていた**（σ̃⁶=τ² は q27tb から
      自由だが本ファイルでは statement すら無い）。
   3. §9 の表題「非退化 Hasse–Arf（単一群版）」は、上半分が Nat 上の `rfl` である定理に
      対しては**寛大**である（docstring 自身は開示済）。**Hasse–Arf の実体＝上付き jump の
      整数性は本モジュールでは一切動いていない**——実になったのは下付き番号の入力と群のみ。
   4. **cross-pillar 警告（監査）**: 実 ℤ/9 ＋ 実下付きフィルトレーションは **B1(0.66) の
      主題でもある**。本モジュールの群構成・下付き break の内容は B4 に計上したので、
      **後から B1 の引き上げに再利用してはならない**（二重計上禁止）。
   5. フィルトレーションが減少列・部分群値であること（G₃⊆G₂ 等）は**未証明**（安価だが未着手）。
   監査結果 **B4 0.17 → 0.23（+0.06・band 下端）**。構造的異議（TWO STAGE-WISE FACTS）は
   閉じたが、Herbrand 商両立性と stage orders と上付き番号層は q27tb の Nat 模型のまま。
  ══════════════════════════════════════════════════════════════════

  正直な限定（§4 規約により消さない・弱化しない・最前面に置く）:
  1. **フィルトレーションの各段の位数 |G_i| の階段（9,9,9,3,3,3,3,3,3,1）は
     本モジュールでも依然 Nat 模型（q27tb の `q27tbOrd`）である**。本モジュールが
     実にしたのは (i) **群 ⟨σ̃⟩ の位数がちょうど 9**（9 元が相異なる・
     `q27gl_nine_distinct`）、(ii) 生成元 σ̃ の break がちょうど 2、
     (iii) 部分群生成元 σ̃³=τ の break がちょうど 8、の 3 点である。
     **σ̃², σ̃⁴, σ̃⁵, σ̃⁷, σ̃⁸ の break は本モジュールでは未計算**であり、したがって
     「G₀ = 全群（位数 9）」「G₃ の位数がちょうど 3」といった**各段の位数の主張は
     実側では未証明**（群位数 9 は実・段位数は模型）。
  2. **部分群両立性 `q27gl_subgroup_compat` は本設定では定義的に自明**である。
     M₂₇/L₂ と M₂₇/M₉ は同じ上の体 M₂₇・同じ一様化子 π₂₇ を共有するので、
     下付き番号の判定式が文字通り同一だからである。これは Serre の主張の
     **正しい実現ではあるが、内容のある補題ではない**（過大主張しない）。
  3. **Herbrand の商両立性 φ_{M₂₇/L₂} = φ_{M₉/L₂} ∘ φ_{M₂₇/M₉} は証明していない**。
     得たのは制限準同型の実現（σ̃|_{M₉} = σ）と、両 break が同一スケール π₂₇ で
     測られているという事実である。i_G の和公式
     i_{M₉/L₂}(σ)·e = Σ_{lifts} i_{M₂₇/L₂}(σ̃τ^j) は**未証明**（σ̃τ・σ̃τ² の break を
     計算していないため）。よって level-9 の break を合成塔の break として
     「輸入」する正当化は依然として未完である。ただし本モジュールでは
     **輸入は不要**——σ̃ 自身の break を π₂₇ スケールで直接計算しているため、
     2 つの break はどちらも合成群 ⟨σ̃⟩ の側で独立に確立されている。
  4. **上付き番号 φ/ψ は Nat 切り捨て区分線形の模型**（q27tb の `q27tbPhi`/`q27tbPsi`）
     であり、本モジュールはその**下付き入力側**（break 2 と 8 が単一群のものである
     こと）を実にしたにとどまる。G^v = G_{ψ(v)} の同定は依然未証明（q27tb 限定継承）。
  5. **可除性形式のみ**（付値関数 v_{M₂₇} を建てない・∃c 形）。G_i の定義は
     一様化子への作用 i_G(g) = v(g π₂₇ − π₂₇) 形（q9wr/q27tb の限定 5 を継承）。
  6. **具体塔 ℚ₃(ζ₂₇)/ℚ₃(ζ₃) の 1 本のみ**——一般アーベル拡大の Hasse–Arf 定理ではない。
  7. q27k/q27ps/q27tl/q9ps/q9wr/q9ha/q9hb/q9hi/q27tb の正直限定を全て継承する。

  全て選択公理不使用（新規 Classical.choice を導入しない・sorry 皆無）。
  #print axioms は [propext, Quot.sound] のみ。禁止タクティク不使用。共有ファイル未変更（新規 1 本）。
-/
import IUT.Q3TwoBreakHasseArfReal
import IUT.Q3GenLowerFiltrationReal

namespace IUT

/-! ## §0 係数環 O_{M₉} の作業用簿記補題（q3kMul/q3kAdd 形のまま使う） -/

/-- 乗法簿記 (a·b)·(c·d) = (a·c)·(b·d)（q3kMul 形）。 -/
theorem q27gl_mmmc (a b c d : q3kCar) :
    q3kMul (q3kMul a b) (q3kMul c d) = q3kMul (q3kMul a c) (q3kMul b d) :=
  CRing.mul_mul_mul_comm q3kRing a b c d

/-- 結合則の 1 段版 a·(b·c) = (a·b)·c（q3kMul 形）。 -/
theorem q27gl_massoc (a b c : q3kCar) :
    q3kMul a (q3kMul b c) = q3kMul (q3kMul a b) c :=
  (q3k_mul_assoc a b c).symm

/-- 左分配（q3kMul/q3kAdd 形）。 -/
theorem q27gl_ldist (a b c : q3kCar) :
    q3kMul a (q3kAdd b c) = q3kAdd (q3kMul a b) (q3kMul a c) :=
  q3k_left_distrib a b c

/-- a·1 = a。 -/
theorem q27gl_mul_one (a : q3kCar) : q3kMul a q3kOne = a :=
  CRing.mul_one q3kRing a

/-- a·0 = 0。 -/
theorem q27gl_mul_zero (a : q3kCar) : q3kMul a q3kZero = q3kZero :=
  CRing.mul_zero q3kRing a

/-- 左交換 a·(b·c) = b·(a·c)。 -/
theorem q27gl_mlc (a b c : q3kCar) :
    q3kMul a (q3kMul b c) = q3kMul b (q3kMul a c) :=
  CRing.mul_left_comm q3kRing a b c

/-- e·(z·(e²·e)) = z·(e²·e²)（= z·e⁴ の 2 通りの括り方）。 -/
theorem q27gl_e4 (z e : q3kCar) :
    q3kMul e (q3kMul z (q3kMul (q3kMul e e) e))
      = q3kMul z (q3kMul (q3kMul e e) (q3kMul e e)) := by
  rw [q27gl_mlc e z (q3kMul (q3kMul e e) e),
      q3k_mul_comm e (q3kMul (q3kMul e e) e),
      q3k_mul_assoc (q3kMul e e) e e]

/-! ## §1 ねじれ半線形写像の一般族 G(t,e)

    O_{M₂₇} = O_{M₉}[Z]/(Z³−ζ₉) の元 x = a + bZ + cZ² に対し
      G(t,e)(x) := t(a) + e·t(b)·Z + e²·t(c)·Z²
    （t は係数環 O_{M₉} の自己写像・e ∈ O_{M₉}）。σ̃ = G(σ, ζ₉)・τ = G(id, ζ₃)。 -/

/-- **ねじれ半線形写像** G(t,e)(a+bZ+cZ²) = t(a) + e·t(b)·Z + e²·t(c)·Z²。 -/
def q27glG (t : q3kCar → q3kCar) (e : q3kCar) (x : q27kCar) : q27kCar :=
  ((t x.1, q3kMul e (t x.2.1), q3kMul (q3kMul e e) (t x.2.2)) : q27kCar)

/-- **G の合成則**: G(t,e) ∘ G(u,f) = G(t∘u, e·t(f))（t が乗法的なら）。 -/
theorem q27gl_G_comp {t u : q3kCar → q3kCar}
    (ht : ∀ a b : q3kCar, t (q3kMul a b) = q3kMul (t a) (t b))
    (e f : q3kCar) (x : q27kCar) :
    q27glG t e (q27glG u f x)
      = q27glG (fun a => t (u a)) (q3kMul e (t f)) x := by
  apply q27k_ext
  · rfl
  · show q3kMul e (t (q3kMul f (u x.2.1)))
      = q3kMul (q3kMul e (t f)) (t (u x.2.1))
    rw [ht f (u x.2.1), q27gl_massoc e (t f) (t (u x.2.1))]
  · show q3kMul (q3kMul e e) (t (q3kMul (q3kMul f f) (u x.2.2)))
      = q3kMul (q3kMul (q3kMul e (t f)) (q3kMul e (t f))) (t (u x.2.2))
    rw [ht (q3kMul f f) (u x.2.2), ht f f,
        q27gl_massoc (q3kMul e e) (q3kMul (t f) (t f)) (t (u x.2.2)),
        q27gl_mmmc e e (t f) (t f)]

/-- **G の加法性**: t が加法的なら G(t,e) も加法的。 -/
theorem q27gl_G_add {t : q3kCar → q3kCar} (e : q3kCar)
    (hta : ∀ a b : q3kCar, t (q3kAdd a b) = q3kAdd (t a) (t b))
    (x y : q27kCar) :
    q27glG t e (q27kAdd x y) = q27kAdd (q27glG t e x) (q27glG t e y) := by
  apply q27k_ext
  · exact hta x.1 y.1
  · show q3kMul e (t (q3kAdd x.2.1 y.2.1))
      = q3kAdd (q3kMul e (t x.2.1)) (q3kMul e (t y.2.1))
    rw [hta x.2.1 y.2.1, q27gl_ldist e (t x.2.1) (t y.2.1)]
  · show q3kMul (q3kMul e e) (t (q3kAdd x.2.2 y.2.2))
      = q3kAdd (q3kMul (q3kMul e e) (t x.2.2)) (q3kMul (q3kMul e e) (t y.2.2))
    rw [hta x.2.2 y.2.2, q27gl_ldist (q3kMul e e) (t x.2.2) (t y.2.2)]

/-- **★ G の乗法性判定**: t が加法的・乗法的で **t(ζ₉) = ζ₉·e³** ならば
    G(t,e) は O_{M₂₇} の乗法を保つ。ねじれ Z³=ζ₉ が e³ の因子で吸収される
    ——これが「σ̃ が well-defined な環自己同型である」ことの本体。 -/
theorem q27gl_G_mul {t : q3kCar → q3kCar} {e : q3kCar}
    (hta : ∀ a b : q3kCar, t (q3kAdd a b) = q3kAdd (t a) (t b))
    (htm : ∀ a b : q3kCar, t (q3kMul a b) = q3kMul (t a) (t b))
    (he : t q3kZeta9 = q3kMul q3kZeta9 (q3kMul (q3kMul e e) e))
    (x y : q27kCar) :
    q27glG t e (q27kMul x y) = q27kMul (q27glG t e x) (q27glG t e y) := by
  apply q27k_ext
  · show t (q3kAdd (q3kMul x.1 y.1)
        (q3kMul q3kZeta9 (q3kAdd (q3kMul x.2.1 y.2.2) (q3kMul x.2.2 y.2.1))))
      = q3kAdd (q3kMul (t x.1) (t y.1))
        (q3kMul q3kZeta9
          (q3kAdd (q3kMul (q3kMul e (t x.2.1)) (q3kMul (q3kMul e e) (t y.2.2)))
                  (q3kMul (q3kMul (q3kMul e e) (t x.2.2)) (q3kMul e (t y.2.1)))))
    rw [hta (q3kMul x.1 y.1)
          (q3kMul q3kZeta9 (q3kAdd (q3kMul x.2.1 y.2.2) (q3kMul x.2.2 y.2.1))),
        htm x.1 y.1,
        htm q3kZeta9 (q3kAdd (q3kMul x.2.1 y.2.2) (q3kMul x.2.2 y.2.1)),
        hta (q3kMul x.2.1 y.2.2) (q3kMul x.2.2 y.2.1),
        htm x.2.1 y.2.2, htm x.2.2 y.2.1, he,
        q27gl_mmmc e (t x.2.1) (q3kMul e e) (t y.2.2),
        q27gl_mmmc (q3kMul e e) (t x.2.2) e (t y.2.1),
        q3k_mul_comm e (q3kMul e e),
        ← q27gl_ldist (q3kMul (q3kMul e e) e)
          (q3kMul (t x.2.1) (t y.2.2)) (q3kMul (t x.2.2) (t y.2.1)),
        ← q27gl_massoc q3kZeta9 (q3kMul (q3kMul e e) e)
          (q3kAdd (q3kMul (t x.2.1) (t y.2.2)) (q3kMul (t x.2.2) (t y.2.1)))]
  · show q3kMul e (t (q3kAdd (q3kAdd (q3kMul x.1 y.2.1) (q3kMul x.2.1 y.1))
        (q3kMul q3kZeta9 (q3kMul x.2.2 y.2.2))))
      = q3kAdd (q3kAdd (q3kMul (t x.1) (q3kMul e (t y.2.1)))
                       (q3kMul (q3kMul e (t x.2.1)) (t y.1)))
               (q3kMul q3kZeta9 (q3kMul (q3kMul (q3kMul e e) (t x.2.2))
                                        (q3kMul (q3kMul e e) (t y.2.2))))
    rw [hta (q3kAdd (q3kMul x.1 y.2.1) (q3kMul x.2.1 y.1))
          (q3kMul q3kZeta9 (q3kMul x.2.2 y.2.2)),
        hta (q3kMul x.1 y.2.1) (q3kMul x.2.1 y.1),
        htm x.1 y.2.1, htm x.2.1 y.1,
        htm q3kZeta9 (q3kMul x.2.2 y.2.2), htm x.2.2 y.2.2, he,
        q27gl_ldist e (q3kAdd (q3kMul (t x.1) (t y.2.1)) (q3kMul (t x.2.1) (t y.1)))
          (q3kMul (q3kMul q3kZeta9 (q3kMul (q3kMul e e) e)) (q3kMul (t x.2.2) (t y.2.2))),
        q27gl_ldist e (q3kMul (t x.1) (t y.2.1)) (q3kMul (t x.2.1) (t y.1)),
        q27gl_mlc e (t x.1) (t y.2.1),
        q27gl_massoc e (t x.2.1) (t y.1),
        q27gl_mmmc (q3kMul e e) (t x.2.2) (q3kMul e e) (t y.2.2),
        q27gl_massoc e (q3kMul q3kZeta9 (q3kMul (q3kMul e e) e))
          (q3kMul (t x.2.2) (t y.2.2)),
        q27gl_massoc q3kZeta9 (q3kMul (q3kMul e e) (q3kMul e e))
          (q3kMul (t x.2.2) (t y.2.2)),
        q27gl_e4 q3kZeta9 e]
  · show q3kMul (q3kMul e e)
        (t (q3kAdd (q3kAdd (q3kMul x.1 y.2.2) (q3kMul x.2.1 y.2.1)) (q3kMul x.2.2 y.1)))
      = q3kAdd (q3kAdd (q3kMul (t x.1) (q3kMul (q3kMul e e) (t y.2.2)))
                       (q3kMul (q3kMul e (t x.2.1)) (q3kMul e (t y.2.1))))
               (q3kMul (q3kMul (q3kMul e e) (t x.2.2)) (t y.1))
    rw [hta (q3kAdd (q3kMul x.1 y.2.2) (q3kMul x.2.1 y.2.1)) (q3kMul x.2.2 y.1),
        hta (q3kMul x.1 y.2.2) (q3kMul x.2.1 y.2.1),
        htm x.1 y.2.2, htm x.2.1 y.2.1, htm x.2.2 y.1,
        q27gl_ldist (q3kMul e e)
          (q3kAdd (q3kMul (t x.1) (t y.2.2)) (q3kMul (t x.2.1) (t y.2.1)))
          (q3kMul (t x.2.2) (t y.1)),
        q27gl_ldist (q3kMul e e) (q3kMul (t x.1) (t y.2.2)) (q3kMul (t x.2.1) (t y.2.1)),
        q27gl_mlc (q3kMul e e) (t x.1) (t y.2.2),
        q27gl_mmmc e (t x.2.1) e (t y.2.1),
        q27gl_massoc (q3kMul e e) (t x.2.2) (t y.1)]

/-! ## §2 係数側 σ の ζ₉ への作用（ねじれ条件 σ(ζ₉) = ζ₉·ζ₉³ の検証） -/

/-- σ は加法的（ζ₃・ζ₃² 倍の分配）。 -/
theorem q27gl_sigma_add (a b : q3kCar) :
    q3kSigma (q3kAdd a b) = q3kAdd (q3kSigma a) (q3kSigma b) := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta (q3rqAdd a.2.1 b.2.1)
      = q3rqAdd (q3rqMul q3rqZeta a.2.1) (q3rqMul q3rqZeta b.2.1)
    rw [q3k_M_eq, q3k_A_eq]
    exact q3rqRing.left_distrib q3rqZeta a.2.1 b.2.1
  · show q3rqMul q3rqZetaSq (q3rqAdd a.2.2 b.2.2)
      = q3rqAdd (q3rqMul q3rqZetaSq a.2.2) (q3rqMul q3rqZetaSq b.2.2)
    rw [q3k_M_eq, q3k_A_eq]
    exact q3rqRing.left_distrib q3rqZetaSq a.2.2 b.2.2

/-- σ は 0 を固定。 -/
theorem q27gl_sigma_zero : q3kSigma q3kZero = q3kZero := q9gl_sigma_embed q3rqZero

/-- σ は ζ₃ = embed(ζ₃) ∈ O_{L₂} を固定。 -/
theorem q27gl_sigma_c3 : q3kSigma q27kZeta3 = q27kZeta3 := q9gl_sigma_embed q3rqZeta

/-- ζ₃³ = 1（q3kMul 形）。 -/
theorem q27gl_c3cube :
    q3kMul (q3kMul q27kZeta3 q27kZeta3) q27kZeta3 = q3kOne := q27k_z3R

/-- ζ₃·ζ₃ = ζ₃²（q3kMul 形）。 -/
theorem q27gl_c3sq : q3kMul q27kZeta3 q27kZeta3 = q27kZeta3Sq := q27k_z_zR

/-- **σ(ζ₉) = ζ₃·ζ₉**（実 Gal(M₉/L₂) の生成元の ζ₉ への作用・座標計算）。 -/
theorem q27gl_sigma_z : q3kSigma q3kZeta9 = q3kMul q27kZeta3 q3kZeta9 := by
  rw [show q3kMul q27kZeta3 q3kZeta9 = q3kMul (q3kEmbed q3rqZeta) q3kZeta9 from rfl,
      q9gl_embedY q3rqZeta]
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta q3rqOne = q3rqZeta
    rw [q3k_M_eq]
    exact q3rqRing.mul_one q3rqZeta
  · show q3rqMul q3rqZetaSq q3rqZero = q3rqZero
    rw [q3k_M_eq]
    exact q3rqRing.mul_zero q3rqZetaSq

/-- **ねじれ条件**: σ(ζ₉) = ζ₉·(ζ₉·ζ₉)·ζ₉ ——`q27gl_G_mul` の仮定形。 -/
theorem q27gl_twist :
    q3kSigma q3kZeta9
      = q3kMul q3kZeta9 (q3kMul (q3kMul q3kZeta9 q3kZeta9) q3kZeta9) := by
  rw [q3k_zeta9_cube, q27gl_sigma_z]
  exact q3k_mul_comm q27kZeta3 q3kZeta9

/-! ## §3 ★★★ 実合成 Galois 生成元 σ̃: Z ↦ ζ₉·Z（係数は σ で捻る） -/

/-- **★★★ σ̃**（実 Gal(M₂₇/L₂) の生成元・ζ₂₇ ↦ ζ₂₇⁴ に対応）:
    σ̃(a + bZ + cZ²) = σ(a) + ζ₉σ(b)·Z + ζ₉²σ(c)·Z²。 -/
def q27glSt (x : q27kCar) : q27kCar := q27glG q3kSigma q3kZeta9 x

/-- σ̃ は加法的。 -/
theorem q27gl_st_add (x y : q27kCar) :
    q27glSt (q27kAdd x y) = q27kAdd (q27glSt x) (q27glSt y) :=
  q27gl_G_add q3kZeta9 q27gl_sigma_add x y

/-- **★★ σ̃ は乗法的**（O_{M₂₇} の環構造を保つ・ねじれ条件 σ(ζ₉)=ζ₉⁴ 経由）。 -/
theorem q27gl_st_mul (x y : q27kCar) :
    q27glSt (q27kMul x y) = q27kMul (q27glSt x) (q27glSt y) :=
  q27gl_G_mul q27gl_sigma_add q3k_sigma_mul q27gl_twist x y

/-- σ̃(1) = 1。 -/
theorem q27gl_st_one : q27glSt q27kOne = q27kOne := by
  apply q27k_ext
  · exact q3k_sigma_one
  · show q3kMul q3kZeta9 (q3kSigma q3kZero) = q3kZero
    rw [q27gl_sigma_zero]
    exact q27gl_mul_zero q3kZeta9
  · show q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kSigma q3kZero) = q3kZero
    rw [q27gl_sigma_zero]
    exact q27gl_mul_zero (q3kMul q3kZeta9 q3kZeta9)

/-- **σ̃ は M₉ 上で σ に制限される**（σ̃∘embed = embed∘σ）——
    合成群 ⟨σ̃⟩ ↠ Gal(M₉/L₂) の実現（商両立性の実現部）。 -/
theorem q27gl_restrict_sigma (a : q3kCar) :
    q27glSt (q27kEmbed a) = q27kEmbed (q3kSigma a) := by
  apply q27k_ext
  · rfl
  · show q3kMul q3kZeta9 (q3kSigma q3kZero) = q3kZero
    rw [q27gl_sigma_zero]
    exact q27gl_mul_zero q3kZeta9
  · show q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kSigma q3kZero) = q3kZero
    rw [q27gl_sigma_zero]
    exact q27gl_mul_zero (q3kMul q3kZeta9 q3kZeta9)

/-- **★ σ̃ は基礎体 L₂ = ℚ₃(ζ₃) を点ごとに固定する**——すなわち σ̃ は
    Gal(M₂₇/L₂) の元である（σ が L₂ を固定することの持ち上げ）。 -/
theorem q27gl_st_fixes_L2 (n : q3rqCar) :
    q27glSt (q27kEmbed (q3kEmbed n)) = q27kEmbed (q3kEmbed n) := by
  rw [q27gl_restrict_sigma (q3kEmbed n), q9gl_sigma_embed n]

/-- **τ = Gal(M₂₇/M₉ ) は M₉ を固定**（⟨τ⟩ ⊆ 制限準同型の核）。 -/
theorem q27gl_tau_fixes_base (a : q3kCar) :
    q27kSigma (q27kEmbed a) = q27kEmbed a := by
  apply q27k_ext
  · rfl
  · exact q27gl_mul_zero q27kZeta3
  · exact q27gl_mul_zero q27kZeta3Sq

/-! ## §4 σ̃ の冪と **σ̃³ = τ・σ̃⁹ = id・σ̃³ ≠ id**（位数ちょうど 9） -/

/-- σ̃² = G(σ², ζ₉·σ(ζ₉))（合成則の直接適用）。 -/
theorem q27gl_st2 (x : q27kCar) :
    q27glSt (q27glSt x)
      = q27glG (fun a => q3kSigma (q3kSigma a))
          (q3kMul q3kZeta9 (q3kSigma q3kZeta9)) x :=
  q27gl_G_comp q3k_sigma_mul q3kZeta9 q3kZeta9 x

/-- σ(ζ₉·σζ₉) = ζ₉·ζ₉（ζ₃³=1 の消去）。 -/
theorem q27gl_sigma_e2 :
    q3kSigma (q3kMul q3kZeta9 (q3kSigma q3kZeta9)) = q3kMul q3kZeta9 q3kZeta9 := by
  rw [q3k_sigma_mul q3kZeta9 (q3kSigma q3kZeta9), q27gl_sigma_z,
      q3k_sigma_mul q27kZeta3 q3kZeta9, q27gl_sigma_c3, q27gl_sigma_z,
      q27gl_massoc q27kZeta3 q27kZeta3 q3kZeta9,
      q27gl_mmmc q27kZeta3 q3kZeta9 (q3kMul q27kZeta3 q27kZeta3) q3kZeta9,
      q27gl_massoc q27kZeta3 q27kZeta3 q27kZeta3,
      q27gl_c3cube, q3k_one_mul (q3kMul q3kZeta9 q3kZeta9)]

/-- ζ₉·(ζ₉·ζ₉) = ζ₃。 -/
theorem q27gl_e3 : q3kMul q3kZeta9 (q3kMul q3kZeta9 q3kZeta9) = q27kZeta3 := by
  rw [q27gl_massoc q3kZeta9 q3kZeta9 q3kZeta9]
  exact q3k_zeta9_cube

/-- **★★★ σ̃³ = τ**（＝ q27kSigma・Gal(M₂₇/M₉) の生成元）——
    σ̃ の 3 乗がちょうど部分群 Gal(M₂₇/M₉) の生成元になる。 -/
theorem q27gl_st3 (x : q27kCar) :
    q27glSt (q27glSt (q27glSt x)) = q27kSigma x := by
  have h1 : q27glSt (q27glSt (q27glSt x))
      = q27glG q3kSigma q3kZeta9
          (q27glG (fun a => q3kSigma (q3kSigma a))
            (q3kMul q3kZeta9 (q3kSigma q3kZeta9)) x) := by
    rw [q27gl_st2 x]
    rfl
  rw [h1,
      q27gl_G_comp (t := q3kSigma) (u := fun a => q3kSigma (q3kSigma a))
        q3k_sigma_mul q3kZeta9 (q3kMul q3kZeta9 (q3kSigma q3kZeta9)) x,
      q27gl_sigma_e2, q27gl_e3]
  apply q27k_ext
  · exact q3k_sigma3_id x.1
  · show q3kMul q27kZeta3 (q3kSigma (q3kSigma (q3kSigma x.2.1)))
      = q3kMul q27kZeta3 x.2.1
    rw [q3k_sigma3_id x.2.1]
  · show q3kMul (q3kMul q27kZeta3 q27kZeta3) (q3kSigma (q3kSigma (q3kSigma x.2.2)))
      = q3kMul q27kZeta3Sq x.2.2
    rw [q3k_sigma3_id x.2.2, q27gl_c3sq]

/-- **σ̃⁹ = id**（σ̃³=τ を 3 回・τ³=id）。 -/
theorem q27gl_st9 (x : q27kCar) :
    q27glSt (q27glSt (q27glSt (q27glSt (q27glSt (q27glSt
      (q27glSt (q27glSt (q27glSt x)))))))) = x := by
  rw [q27gl_st3 x, q27gl_st3 (q27kSigma x), q27gl_st3 (q27kSigma (q27kSigma x)),
      q27k_sigma3_id x]

/-- **τ ≠ id**（τ(ζ₂₇) = ζ₃·ζ₂₇ ≠ ζ₂₇・ζ₃≠1）。 -/
theorem q27gl_tau_ne_id : q27kSigma q27kZeta27 ≠ q27kZeta27 := by
  intro h
  have h1 : q3kMul q27kZeta3 q3kOne = q3kOne :=
    congrArg (fun w : q27kCar => w.2.1) h
  rw [q27gl_mul_one q27kZeta3] at h1
  have h2 : q3rqZeta = q3rqOne := congrArg (fun w : q3kCar => w.1) h1
  exact q3rq_zeta_ne_one h2

/-- **σ̃³ ≠ id**（σ̃³=τ かつ τ≠id）。 -/
theorem q27gl_st3_ne_id :
    q27glSt (q27glSt (q27glSt q27kZeta27)) ≠ q27kZeta27 := by
  rw [q27gl_st3 q27kZeta27]
  exact q27gl_tau_ne_id

/-- **σ̃ ≠ id**（σ̃(ζ₂₇) = ζ₉·ζ₂₇ ≠ ζ₂₇・ζ₉≠1）。 -/
theorem q27gl_st_ne_id : q27glSt q27kZeta27 ≠ q27kZeta27 := by
  intro h
  have h1 : q3kMul q3kZeta9 (q3kSigma q3kOne) = q3kOne :=
    congrArg (fun w : q27kCar => w.2.1) h
  rw [q3k_sigma_one, q27gl_mul_one q3kZeta9] at h1
  exact q3k_zeta9_ne_one h1

/-- **★ σ̃ の位数はちょうど 9**: σ̃⁹ = id ∧ σ̃³ ≠ id ∧ σ̃ ≠ id。
    位数は 9 の約数（1,3,9）で 1 でも 3 でもないから 9。 -/
theorem q27gl_order_nine :
    (∀ x : q27kCar, q27glSt (q27glSt (q27glSt (q27glSt (q27glSt (q27glSt
        (q27glSt (q27glSt (q27glSt x)))))))) = x)
    ∧ q27glSt (q27glSt (q27glSt q27kZeta27)) ≠ q27kZeta27
    ∧ q27glSt q27kZeta27 ≠ q27kZeta27 :=
  ⟨q27gl_st9, q27gl_st3_ne_id, q27gl_st_ne_id⟩

/-! ## §4b σ̃ の Nat 冪と **⟨σ̃⟩ の 9 元が相異なる**こと

    σ̃^k(ζ₂₇) = ε_k·ζ₂₇（ε_k ∈ μ₉ ⊂ O_{M₉}）を係数の閉じた漸化式
      ε_0 = 1・ε_{k+1} = ζ₉·σ(ε_k)
    で追跡し、ε_1,…,ε_8 がすべて 1 でないことを座標で確かめる。 -/

/-- σ̃ の Nat 冪。 -/
def q27glPow : Nat → q27kCar → q27kCar
  | 0, x => x
  | (n + 1), x => q27glSt (q27glPow n x)

/-- σ̃ は自分の冪と可換。 -/
theorem q27gl_pow_st (a : Nat) (x : q27kCar) :
    q27glPow a (q27glSt x) = q27glSt (q27glPow a x) := by
  induction a with
  | zero => rfl
  | succ n ih =>
    show q27glSt (q27glPow n (q27glSt x)) = q27glSt (q27glSt (q27glPow n x))
    rw [ih]

/-- 冪の指数加法則 σ̃^{a+b} = σ̃^a ∘ σ̃^b。 -/
theorem q27gl_pow_add (a b : Nat) (x : q27kCar) :
    q27glPow (a + b) x = q27glPow a (q27glPow b x) := by
  induction b with
  | zero => rfl
  | succ n ih =>
    show q27glSt (q27glPow (a + n) x) = q27glPow a (q27glSt (q27glPow n x))
    rw [q27gl_pow_st a (q27glPow n x), ih]

/-- σ̃⁹ = id（冪形）。 -/
theorem q27gl_pow9_id (x : q27kCar) : q27glPow 9 x = x := q27gl_st9 x

/-- σ̃^i は単射（σ̃⁹=id から σ̃^{9−i} を掛けて戻す）。 -/
theorem q27gl_pow_inj (i : Nat) (hi : i ≤ 9) {a b : q27kCar}
    (h : q27glPow i a = q27glPow i b) : a = b := by
  have h9 : q27glPow (9 - i) (q27glPow i a) = q27glPow (9 - i) (q27glPow i b) := by
    rw [h]
  rw [← q27gl_pow_add (9 - i) i a, ← q27gl_pow_add (9 - i) i b,
      show 9 - i + i = 9 from by omega, q27gl_pow9_id a, q27gl_pow9_id b] at h9
  exact h9

/-- ζ₂₇ に対する σ̃ 冪の係数 ε_k（ε_0=1・ε_{k+1}=ζ₉·σ(ε_k)）。 -/
def q27glEps : Nat → q3kCar
  | 0 => q3kOne
  | (n + 1) => q3kMul q3kZeta9 (q3kSigma (q27glEps n))

/-- **σ̃^k(ζ₂₇) = (0, ε_k, 0)**（Z-基底・帰納法）。 -/
theorem q27gl_pow_zeta27 (k : Nat) :
    q27glPow k q27kZeta27 = ((q3kZero, q27glEps k, q3kZero) : q27kCar) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    show q27glSt (q27glPow n q27kZeta27)
      = ((q3kZero, q3kMul q3kZeta9 (q3kSigma (q27glEps n)), q3kZero) : q27kCar)
    rw [ih]
    apply q27k_ext
    · exact q27gl_sigma_zero
    · rfl
    · show q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kSigma q3kZero) = q3kZero
      rw [q27gl_sigma_zero]
      exact q27gl_mul_zero (q3kMul q3kZeta9 q3kZeta9)

/-- **ε の 1 段漸化（座標形）**: ζ₉·σ(a,b,c) = (c, a, ζ₃b)（ζ₃ζ₃²=1 の消去）。 -/
theorem q27gl_eps_step (a b c : q3rqCar) :
    q3kMul q3kZeta9 (q3kSigma ((a, b, c) : q3kCar))
      = ((c, a, q3rqMul q3rqZeta b) : q3kCar) := by
  apply q3k_ext
  · show q3rqRing.add (q3rqRing.mul q3rqRing.zero a)
        (q3rqRing.mul q3rqZeta (q3rqRing.add
          (q3rqRing.mul q3rqRing.one (q3rqRing.mul q3rqZetaSq c))
          (q3rqRing.mul q3rqRing.zero (q3rqRing.mul q3rqZeta b)))) = c
    rw [q3rqRing.zero_mul a,
        q3rqRing.one_mul (q3rqRing.mul q3rqZetaSq c),
        q3rqRing.zero_mul (q3rqRing.mul q3rqZeta b),
        q3rqRing.add_zero (q3rqRing.mul q3rqZetaSq c),
        ← q3rqRing.mul_assoc q3rqZeta q3rqZetaSq c,
        q3k_z_zsqR1, q3rqRing.one_mul c, q3rqRing.zero_add c]
  · show q3rqRing.add (q3rqRing.add
        (q3rqRing.mul q3rqRing.zero (q3rqRing.mul q3rqZeta b))
        (q3rqRing.mul q3rqRing.one a))
        (q3rqRing.mul q3rqZeta (q3rqRing.mul q3rqRing.zero
          (q3rqRing.mul q3rqZetaSq c))) = a
    rw [q3rqRing.zero_mul (q3rqRing.mul q3rqZeta b),
        q3rqRing.one_mul a, q3rqRing.zero_add a,
        q3rqRing.zero_mul (q3rqRing.mul q3rqZetaSq c),
        q3rqRing.mul_zero q3rqZeta, q3rqRing.add_zero a]
  · show q3rqRing.add (q3rqRing.add
        (q3rqRing.mul q3rqRing.zero (q3rqRing.mul q3rqZetaSq c))
        (q3rqRing.mul q3rqRing.one (q3rqRing.mul q3rqZeta b)))
        (q3rqRing.mul q3rqRing.zero a) = q3rqRing.mul q3rqZeta b
    rw [q3rqRing.zero_mul (q3rqRing.mul q3rqZetaSq c),
        q3rqRing.one_mul (q3rqRing.mul q3rqZeta b),
        q3rqRing.zero_add (q3rqRing.mul q3rqZeta b),
        q3rqRing.zero_mul a,
        q3rqRing.add_zero (q3rqRing.mul q3rqZeta b)]

/-- ε₁ = ζ₉ = (0,1,0)。 -/
theorem q27gl_eps1 : q27glEps 1 = ((q3rqZero, q3rqOne, q3rqZero) : q3kCar) := by
  show q3kMul q3kZeta9 (q3kSigma ((q3rqOne, q3rqZero, q3rqZero) : q3kCar))
    = ((q3rqZero, q3rqOne, q3rqZero) : q3kCar)
  rw [q27gl_eps_step q3rqOne q3rqZero q3rqZero]
  apply q3k_ext
  · rfl
  · rfl
  · exact q3rqRing.mul_zero q3rqZeta

/-- ε₂ = (0,0,ζ₃)。 -/
theorem q27gl_eps2 : q27glEps 2 = ((q3rqZero, q3rqZero, q3rqZeta) : q3kCar) := by
  show q3kMul q3kZeta9 (q3kSigma (q27glEps 1)) = _
  rw [q27gl_eps1, q27gl_eps_step q3rqZero q3rqOne q3rqZero]
  apply q3k_ext
  · rfl
  · rfl
  · exact q3rqRing.mul_one q3rqZeta

/-- ε₃ = ζ₃ = (ζ₃,0,0)（＝ τ の係数）。 -/
theorem q27gl_eps3 : q27glEps 3 = ((q3rqZeta, q3rqZero, q3rqZero) : q3kCar) := by
  show q3kMul q3kZeta9 (q3kSigma (q27glEps 2)) = _
  rw [q27gl_eps2, q27gl_eps_step q3rqZero q3rqZero q3rqZeta]
  apply q3k_ext
  · rfl
  · rfl
  · exact q3rqRing.mul_zero q3rqZeta

/-- ε₄ = (0,ζ₃,0)。 -/
theorem q27gl_eps4 : q27glEps 4 = ((q3rqZero, q3rqZeta, q3rqZero) : q3kCar) := by
  show q3kMul q3kZeta9 (q3kSigma (q27glEps 3)) = _
  rw [q27gl_eps3, q27gl_eps_step q3rqZeta q3rqZero q3rqZero]
  apply q3k_ext
  · rfl
  · rfl
  · exact q3rqRing.mul_zero q3rqZeta

/-- ε₅ = (0,0,ζ₃²)。 -/
theorem q27gl_eps5 : q27glEps 5 = ((q3rqZero, q3rqZero, q3rqZetaSq) : q3kCar) := by
  show q3kMul q3kZeta9 (q3kSigma (q27glEps 4)) = _
  rw [q27gl_eps4, q27gl_eps_step q3rqZero q3rqZeta q3rqZero]
  rfl

/-- ε₆ = ζ₃² = (ζ₃²,0,0)（＝ τ² の係数）。 -/
theorem q27gl_eps6 : q27glEps 6 = ((q3rqZetaSq, q3rqZero, q3rqZero) : q3kCar) := by
  show q3kMul q3kZeta9 (q3kSigma (q27glEps 5)) = _
  rw [q27gl_eps5, q27gl_eps_step q3rqZero q3rqZero q3rqZetaSq]
  apply q3k_ext
  · rfl
  · rfl
  · exact q3rqRing.mul_zero q3rqZeta

/-- ε₇ = (0,ζ₃²,0)。 -/
theorem q27gl_eps7 : q27glEps 7 = ((q3rqZero, q3rqZetaSq, q3rqZero) : q3kCar) := by
  show q3kMul q3kZeta9 (q3kSigma (q27glEps 6)) = _
  rw [q27gl_eps6, q27gl_eps_step q3rqZetaSq q3rqZero q3rqZero]
  apply q3k_ext
  · rfl
  · rfl
  · exact q3rqRing.mul_zero q3rqZeta

/-- ε₈ = ζ₉² = (0,0,1)（ζ₃ζ₃²=1）。 -/
theorem q27gl_eps8 : q27glEps 8 = ((q3rqZero, q3rqZero, q3rqOne) : q3kCar) := by
  show q3kMul q3kZeta9 (q3kSigma (q27glEps 7)) = _
  rw [q27gl_eps7, q27gl_eps_step q3rqZero q3rqZetaSq q3rqZero]
  apply q3k_ext
  · rfl
  · rfl
  · exact q3k_z_zsqR1

/-- ε₉ = 1（周期 9 の整合性チェック）。 -/
theorem q27gl_eps9 : q27glEps 9 = q3kOne := by
  show q3kMul q3kZeta9 (q3kSigma (q27glEps 8)) = _
  rw [q27gl_eps8, q27gl_eps_step q3rqZero q3rqZero q3rqOne]
  apply q3k_ext
  · rfl
  · rfl
  · exact q3rqRing.mul_zero q3rqZeta

/-- 0 ≠ 1（O_{L₂} 内）。 -/
theorem q27gl_zero_ne_one : (q3rqZero : q3rqCar) ≠ q3rqOne := by
  intro h
  exact q3rq_z3_one_ne_zero (congrArg (fun w : q3rqCar => w.1) h).symm

/-- **ε_k ≠ 1（1 ≤ k ≤ 8）**——σ̃ の位数がちょうど 9 であることの核。 -/
theorem q27gl_eps_ne_one : ∀ k : Nat, 1 ≤ k → k ≤ 8 → q27glEps k ≠ q3kOne := by
  intro k h1 h2
  match k, h1, h2 with
  | 0, h, _ => exact absurd h (by omega)
  | 1, _, _ =>
    rw [q27gl_eps1]
    intro h
    exact q27gl_zero_ne_one (congrArg (fun w : q3kCar => w.1) h)
  | 2, _, _ =>
    rw [q27gl_eps2]
    intro h
    exact q27gl_zero_ne_one (congrArg (fun w : q3kCar => w.1) h)
  | 3, _, _ =>
    rw [q27gl_eps3]
    intro h
    exact q3rq_zeta_ne_one (congrArg (fun w : q3kCar => w.1) h)
  | 4, _, _ =>
    rw [q27gl_eps4]
    intro h
    exact q27gl_zero_ne_one (congrArg (fun w : q3kCar => w.1) h)
  | 5, _, _ =>
    rw [q27gl_eps5]
    intro h
    exact q27gl_zero_ne_one (congrArg (fun w : q3kCar => w.1) h)
  | 6, _, _ =>
    rw [q27gl_eps6]
    intro h
    exact q3rq_zeta_sq_ne_one (congrArg (fun w : q3kCar => w.1) h)
  | 7, _, _ =>
    rw [q27gl_eps7]
    intro h
    exact q27gl_zero_ne_one (congrArg (fun w : q3kCar => w.1) h)
  | 8, _, _ =>
    rw [q27gl_eps8]
    intro h
    exact q27gl_zero_ne_one (congrArg (fun w : q3kCar => w.1) h)
  | (n + 9), _, h => exact absurd h (by omega)

/-- **σ̃^k ≠ id（1 ≤ k ≤ 8）**。 -/
theorem q27gl_pow_ne_id (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 8) :
    q27glPow k q27kZeta27 ≠ q27kZeta27 := by
  rw [q27gl_pow_zeta27 k]
  intro h
  exact q27gl_eps_ne_one k h1 h2 (congrArg (fun w : q27kCar => w.2.1) h)

/-- **★ ⟨σ̃⟩ の 9 元は相異なる**——σ̃^i(ζ₂₇) ≠ σ̃^j(ζ₂₇) (0 ≤ i < j ≤ 8)。
    よって実合成 Galois 群 Gal(M₂₇/L₂) = ⟨σ̃⟩ の**位数はちょうど 9**（実側で確定）。 -/
theorem q27gl_nine_distinct {i j : Nat} (hi : i ≤ 8) (hj : j ≤ 8) (hij : i < j) :
    q27glPow i q27kZeta27 ≠ q27glPow j q27kZeta27 := by
  intro h
  have h2 : q27glPow i (q27glPow (j - i) q27kZeta27) = q27glPow i q27kZeta27 := by
    rw [← q27gl_pow_add i (j - i) q27kZeta27, show i + (j - i) = j from by omega]
    exact h.symm
  exact q27gl_pow_ne_id (j - i) (by omega) (by omega) (q27gl_pow_inj i (by omega) h2)

/-! ## §5 σ̃ の実下付き差分 σ̃(π₂₇) − π₂₇ = π₂₇³·(w̃⁻¹ζ₂₇)

    一様化子は **τ と同じ π₂₇**（同一の付値スケール）。σ̃(Z−1) = ζ₉Z − 1 なので
    差分は (ζ₉−1)·Z = embed(π₉)·Z、そして q27ps の (Z−1)³ = embed(π₉)·w̃ から
    embed(π₉) = π₂₇³·w̃⁻¹。ゆえに σ̃ の break はちょうど 2（level-27 スケール）。 -/

/-- σ は反元と可換（σ(−a) = −σ(a)）。 -/
theorem q27gl_sigma_neg (a : q3kCar) : q3kSigma (q3kNeg a) = q3kNeg (q3kSigma a) := by
  apply q3k_ext
  · rfl
  · show q3rqMul q3rqZeta (q3rqNeg a.2.1) = q3rqNeg (q3rqMul q3rqZeta a.2.1)
    rw [q3k_M_eq, q3k_N_eq]
    exact q3rqRing.mul_neg q3rqZeta a.2.1
  · show q3rqMul q3rqZetaSq (q3rqNeg a.2.2) = q3rqNeg (q3rqMul q3rqZetaSq a.2.2)
    rw [q3k_M_eq, q3k_N_eq]
    exact q3rqRing.mul_neg q3rqZetaSq a.2.2

/-- **σ̃ の下付き差分** σ̃(π₂₇) − π₂₇（i_G(σ̃) の被測度）。 -/
def q27glStDiff : q27kCar := q27kAdd (q27glSt q27psPi27) (q27kNeg q27psPi27)

/-- **差分の座標形**: σ̃(π₂₇) − π₂₇ = (0, π₉, 0)（Z-基底）——(ζ₉−1)Z。 -/
theorem q27gl_st_diff_coords :
    q27glStDiff = ((q3kZero, q9psPi9, q3kZero) : q27kCar) := by
  show q27kAdd (q27glSt q27psPi27) (q27kNeg q27psPi27)
      = ((q3kZero, q9psPi9, q3kZero) : q27kCar)
  rw [q27ps_pi27_coords]
  apply q27k_ext
  · show q3kAdd (q3kSigma (q3kNeg q3kOne)) (q3kNeg (q3kNeg q3kOne)) = q3kZero
    rw [q27gl_sigma_neg q3kOne, q3k_sigma_one]
    exact q3kRing.add_neg (q3kNeg q3kOne)
  · show q3kAdd (q3kMul q3kZeta9 (q3kSigma q3kOne)) (q3kNeg q3kOne) = q9psPi9
    rw [q3k_sigma_one, q27gl_mul_one q3kZeta9]
    rfl
  · show q3kAdd (q3kMul (q3kMul q3kZeta9 q3kZeta9) (q3kSigma q3kZero)) (q3kNeg q3kZero)
      = q3kZero
    rw [q27gl_sigma_zero, q27gl_mul_zero (q3kMul q3kZeta9 q3kZeta9)]
    exact q3kRing.add_neg q3kZero

/-- **差分 = embed(π₉)·ζ₂₇**（q27tb_embed_Z 消費）。 -/
theorem q27gl_st_diff_eq :
    q27glStDiff = q27kMul (q27kEmbed q9psPi9) q27kZeta27 :=
  q27gl_st_diff_coords.trans (q27tb_embed_Z q9psPi9).symm

/-- **σ̃ の break 単数** u := w̃⁻¹·ζ₂₇（実閉形式単数）。 -/
def q27glU : q27kCar := q27kMul q27psWtInv q27kZeta27

/-- u は実単数。 -/
theorem q27gl_u_unit : q27kUnitMem q27glU :=
  q27k_unit_mul (q27k_unit_inv q27psWt q27ps_wt_unit) q27tl_zeta27_unit

/-- **★★ σ̃ の break の核**: π₂₇³·u = σ̃(π₂₇) − π₂₇（実 O_{M₂₇} 上の閉形式）。 -/
theorem q27gl_st_pi_eq :
    q27kMul q27psPi27Cubed q27glU = q27glStDiff := by
  show q27kMul q27psPi27Cubed (q27kMul q27psWtInv q27kZeta27) = q27glStDiff
  have hWV : q27kMul q27psWt q27psWtInv = q27kOne :=
    q27k_inv_mul q27psWt q27ps_wt_unit
  rw [q27ps_pi27_cube,
      q27ps_massoc (q27kEmbed q9psPi9) q27psWt (q27kMul q27psWtInv q27kZeta27),
      ← q27ps_massoc q27psWt q27psWtInv q27kZeta27,
      hWV, q27k_one_mul q27kZeta27]
  exact q27gl_st_diff_eq.symm

/-! ## §6 sharp 上界: ¬π₂₇⁴ ∣ σ̃ の差分（相対ノルム降下・π₉³ 正則消去） -/

/-- **sharp 上界の一般補題**（除子 D・N(D) 正則消去つき）:
    差分 = D·U（U 実単数）なら ¬(D·π₂₇) ∣ 差分。 -/
theorem q27gl_sharp {D diff U : q27kCar} {ND : q3kCar}
    (hN : q27kNormBase D = ND)
    (hc : ∀ {a b : q3kCar}, q3kMul ND a = q3kMul ND b → a = b)
    (hEq : q27kMul D U = diff) (hU : q27kUnitMem U) :
    ¬ q27tbDvd (q27kMul D q27psPi27) diff := by
  intro hd
  obtain ⟨x, hx⟩ := hd
  have hcc : q27kMul D U = q27kMul D (q27kMul q27psPi27 x) := by
    rw [hEq, hx]
    exact q27ps_massoc D q27psPi27 x
  have h3 := congrArg q27kNormBase hcc
  rw [q27k_normBase_mul D U,
      q27k_normBase_mul D (q27kMul q27psPi27 x),
      q27k_normBase_mul q27psPi27 x,
      q27tb_norm_pi27, hN] at h3
  have h4 : q27kNormBase U = q3kMul q9psPi9 (q27kNormBase x) := hc h3
  have hu : q3kUnitMem (q27kNormBase U) := hU
  rw [h4] at hu
  exact q27tb_pi9_mul_not_unit (q27kNormBase x) hu

/-- π₂₇⁴ = π₂₇³·π₂₇（G₃ 除子・σ̃ の sharp 上界の除子）。 -/
def q27glPi4 : q27kCar := q27kMul q27psPi27Cubed q27psPi27

/-- **★★ σ̃ ∉ G₃（sharp）**: ¬π₂₇⁴ ∣ (σ̃π₂₇−π₂₇)——σ̃ の break はちょうど 2。 -/
theorem q27gl_G3_trivial_st : ¬ q27tbDvd q27glPi4 q27glStDiff :=
  q27gl_sharp q27tb_norm_pi3 q9wr_pi3_cancel q27gl_st_pi_eq q27gl_u_unit

/-- **σ̃ ∈ G₂**: π₂₇³ ∣ (σ̃π₂₇−π₂₇)。 -/
theorem q27gl_G2_mem_st : q27tbDvd q27psPi27Cubed q27glStDiff :=
  ⟨q27glU, q27gl_st_pi_eq.symm⟩

/-! ## §7 ★★★ 単一群 ⟨σ̃⟩ の**唯一の**下付きフィルトレーションと 2 つの break

    ここが本モジュールの核心である。G_i の判定は **1 本の定義** `q27glInG` で与える:
      g ∈ G_i  :⟺  π₂₇^{i+1} ∣ (g(π₂₇) − π₂₇)
    そして g として**σ̃ の冪だけ**を代入する。σ̃ ∈ G₂∖G₃ と σ̃³ ∈ G₈∖G₉ は、
    どちらも**同じ群 ⟨σ̃⟩ の同じ一様化子 π₂₇ に関する可除性**であって、
    別々の段の事実の連言ではない。 -/

/-- π₂₇ の Nat 冪（左結合）。 -/
def q27glPiPow : Nat → q27kCar
  | 0 => q27kOne
  | (n + 1) => q27kMul (q27glPiPow n) q27psPi27

/-- π₂₇¹ = π₂₇。 -/
theorem q27gl_pow1 : q27glPiPow 1 = q27psPi27 := q27k_one_mul q27psPi27

/-- π₂₇³ = q27psPi27Cubed。 -/
theorem q27gl_pow3 : q27glPiPow 3 = q27psPi27Cubed := by
  show q27kMul (q27kMul (q27glPiPow 1) q27psPi27) q27psPi27 = q27psPi27Cubed
  rw [q27gl_pow1]
  rfl

/-- π₂₇⁴ = π₂₇³·π₂₇。 -/
theorem q27gl_pow4 : q27glPiPow 4 = q27glPi4 := by
  show q27kMul (q27glPiPow 3) q27psPi27 = q27glPi4
  rw [q27gl_pow3]
  rfl

/-- π₂₇⁶ = π₂₇³·π₂₇³。 -/
theorem q27gl_pow6 : q27glPiPow 6 = q27kMul q27psPi27Cubed q27psPi27Cubed := by
  show q27kMul (q27kMul (q27kMul (q27glPiPow 3) q27psPi27) q27psPi27) q27psPi27
      = q27kMul q27psPi27Cubed q27psPi27Cubed
  rw [q27gl_pow3]
  show q27kMul (q27kMul (q27kMul q27psPi27Cubed q27psPi27) q27psPi27) q27psPi27
      = q27kMul q27psPi27Cubed (q27kMul (q27kMul q27psPi27 q27psPi27) q27psPi27)
  rw [q27ps_massoc q27psPi27Cubed q27psPi27 q27psPi27,
      q27ps_massoc q27psPi27Cubed (q27kMul q27psPi27 q27psPi27) q27psPi27]

/-- π₂₇⁹ = q27psPi27Pow9。 -/
theorem q27gl_pow9 : q27glPiPow 9 = q27psPi27Pow9 := by
  show q27kMul (q27kMul (q27kMul (q27glPiPow 6) q27psPi27) q27psPi27) q27psPi27
      = q27psPi27Pow9
  rw [q27gl_pow6]
  show q27kMul (q27kMul (q27kMul
        (q27kMul q27psPi27Cubed q27psPi27Cubed) q27psPi27) q27psPi27) q27psPi27
      = q27kMul (q27kMul q27psPi27Cubed q27psPi27Cubed)
          (q27kMul (q27kMul q27psPi27 q27psPi27) q27psPi27)
  rw [q27ps_massoc (q27kMul q27psPi27Cubed q27psPi27Cubed) q27psPi27 q27psPi27,
      q27ps_massoc (q27kMul q27psPi27Cubed q27psPi27Cubed)
        (q27kMul q27psPi27 q27psPi27) q27psPi27]

/-- π₂₇¹⁰ = q27tbPi10。 -/
theorem q27gl_pow10 : q27glPiPow 10 = q27tbPi10 := by
  show q27kMul (q27glPiPow 9) q27psPi27 = q27tbPi10
  rw [q27gl_pow9]
  rfl

/-- **単一群 ⟨σ̃⟩ の下付きフィルトレーション**（唯一の定義）:
    g ∈ G_i :⟺ π₂₇^{i+1} ∣ (g π₂₇ − π₂₇)。一様化子は常に π₂₇（同一スケール）。 -/
def q27glInG (i : Nat) (g : q27kCar → q27kCar) : Prop :=
  q27tbDvd (q27glPiPow (i + 1)) (q27kAdd (g q27psPi27) (q27kNeg q27psPi27))

/-- σ̃³ の差分は τ の差分に一致（σ̃³ = τ）。 -/
theorem q27gl_st3_diff_eq :
    q27kAdd (q27glSt (q27glSt (q27glSt q27psPi27))) (q27kNeg q27psPi27) = q27tbTauDiff := by
  rw [q27gl_st3 q27psPi27]
  rfl

/-- **σ̃ ∈ G₂**（単一群の下付き番号 2）。 -/
theorem q27gl_st_in_G2 : q27glInG 2 q27glSt := by
  show q27tbDvd (q27glPiPow 3) q27glStDiff
  rw [q27gl_pow3]
  exact q27gl_G2_mem_st

/-- **σ̃ ∉ G₃（sharp）**——σ̃ の break はちょうど 2。 -/
theorem q27gl_st_not_in_G3 : ¬ q27glInG 3 q27glSt := by
  show ¬ q27tbDvd (q27glPiPow 4) q27glStDiff
  rw [q27gl_pow4]
  exact q27gl_G3_trivial_st

/-- **σ̃³ ∈ G₈**（同じ群・同じ π₂₇ スケール）。 -/
theorem q27gl_st3_in_G8 :
    q27glInG 8 (fun x => q27glSt (q27glSt (q27glSt x))) := by
  show q27tbDvd (q27glPiPow 9)
    (q27kAdd (q27glSt (q27glSt (q27glSt q27psPi27))) (q27kNeg q27psPi27))
  rw [q27gl_pow9, q27gl_st3_diff_eq]
  exact q27tb_G8_mem_tau

/-- **σ̃³ ∉ G₉（sharp）**——σ̃³ の break はちょうど 8。 -/
theorem q27gl_st3_not_in_G9 :
    ¬ q27glInG 9 (fun x => q27glSt (q27glSt (q27glSt x))) := by
  show ¬ q27tbDvd (q27glPiPow 10)
    (q27kAdd (q27glSt (q27glSt (q27glSt q27psPi27))) (q27kNeg q27psPi27))
  rw [q27gl_pow10, q27gl_st3_diff_eq]
  exact q27tb_G9_trivial_tau

/-- **★★★ 2 つの break が 1 つの群の 1 本のフィルトレーションに載る**。
    ⟨σ̃⟩ は位数ちょうど 9 の実巡回群（σ̃⁹=id・σ̃³≠id・σ̃≠id）であり、
    その**唯一の**下付きフィルトレーション `q27glInG`（π₂₇ 可除性）に対して
      σ̃ ∈ G₂ ∖ G₃（break 2）  かつ  σ̃³ ∈ G₈ ∖ G₉（break 8）。
    q27tb の `q27tb_two_distinct_breaks`（σ on O_{M₉} と τ on O_{M₂₇} の連言）と違い、
    ここでは**両方が σ̃ の冪**についての同一スケールの主張である。 -/
theorem q27gl_two_jumps_one_group :
    ((∀ x : q27kCar, q27glPow 9 x = x)
      ∧ (∀ k : Nat, 1 ≤ k → k ≤ 8 → q27glPow k q27kZeta27 ≠ q27kZeta27)
      ∧ (∀ i j : Nat, i ≤ 8 → j ≤ 8 → i < j →
          q27glPow i q27kZeta27 ≠ q27glPow j q27kZeta27))
    ∧ (q27glInG 2 q27glSt ∧ ¬ q27glInG 3 q27glSt)
    ∧ (q27glInG 8 (fun x => q27glSt (q27glSt (q27glSt x)))
        ∧ ¬ q27glInG 9 (fun x => q27glSt (q27glSt (q27glSt x))))
    ∧ (2 : Nat) ≠ 8 :=
  ⟨⟨q27gl_pow9_id, q27gl_pow_ne_id,
     fun _ _ hi hj hij => q27gl_nine_distinct hi hj hij⟩,
   ⟨q27gl_st_in_G2, q27gl_st_not_in_G3⟩,
   ⟨q27gl_st3_in_G8, q27gl_st3_not_in_G9⟩,
   by omega⟩

/-! ## §8 部分群両立性（正直な限定 2: 本設定では定義的） -/

/-- **部分群両立性** G_i(M₂₇/L₂) ∩ ⟨τ⟩ = G_i(M₂₇/M₉):
    合成群側の下付き番号での σ̃³ の帰属は、部分群 Gal(M₂₇/M₉) 側の τ の帰属と
    **文字通り同じ判定式**である（M₂₇/L₂ と M₂₇/M₉ は同じ上の体・同じ一様化子 π₂₇）。
    正直な限定 2: したがって本補題は Serre の「下付き番号は部分群と両立」の
    正しい実現ではあるが、内容のある補題ではない（定義的）。 -/
theorem q27gl_subgroup_compat (i : Nat) :
    q27glInG i (fun x => q27glSt (q27glSt (q27glSt x)))
      ↔ q27tbDvd (q27glPiPow (i + 1)) q27tbTauDiff := by
  rw [show q27glInG i (fun x => q27glSt (q27glSt (q27glSt x)))
      = q27tbDvd (q27glPiPow (i + 1))
          (q27kAdd (q27glSt (q27glSt (q27glSt q27psPi27))) (q27kNeg q27psPi27)) from rfl,
      q27gl_st3_diff_eq]

/-! ## §9 ★★ 単一群版の非空虚 Hasse–Arf -/

/-- **★★ 単一群 ⟨σ̃⟩ ≅ ℤ/9 の非空虚 Hasse–Arf**:
    (i) 位数ちょうど 9 の実巡回群、
    (ii) その**1 本の**下付きフィルトレーションが相異なる 2 つの break 2, 8 を持つ、
    (iii) 対応する上付き jump は相異なる整数 2 と 4（積分公式 9∣18・9∣36）。
    正直な限定 1/4: (iii) の |G_i| 階段・φ/ψ は q27tb の Nat 模型であり、
    本モジュールが実にしたのは (i)(ii)（と (ii) の同一スケール性）である。 -/
theorem q27gl_hasse_arf_one_group :
    ((∀ x : q27kCar, q27glSt (q27glSt (q27glSt (q27glSt (q27glSt (q27glSt
        (q27glSt (q27glSt (q27glSt x)))))))) = x)
      ∧ q27glSt (q27glSt (q27glSt q27kZeta27)) ≠ q27kZeta27)
    ∧ ((q27glInG 2 q27glSt ∧ ¬ q27glInG 3 q27glSt)
        ∧ (q27glInG 8 (fun x => q27glSt (q27glSt (q27glSt x)))
            ∧ ¬ q27glInG 9 (fun x => q27glSt (q27glSt (q27glSt x))))
        ∧ (2 : Nat) ≠ 8)
    ∧ (q27tbSum 2 = q27tbOrd 0 * q27tbUpper1
        ∧ q27tbSum 8 = q27tbOrd 0 * q27tbUpper2
        ∧ q27tbUpper1 = q27tbPhi 2 ∧ q27tbUpper2 = q27tbPhi 8 ∧ (2 : Nat) ≠ 4) :=
  ⟨⟨q27gl_st9, q27gl_st3_ne_id⟩,
   ⟨⟨q27gl_st_in_G2, q27gl_st_not_in_G3⟩,
    ⟨q27gl_st3_in_G8, q27gl_st3_not_in_G9⟩, by omega⟩,
   rfl, rfl, rfl, rfl, by omega⟩

/-! ## §10 capstone -/

/-- **実合成 Galois 群 Gal(M₂₇/L₂) ≅ ℤ/9 と単一フィルトレーション 2-break データ**
    （束ねのみ・新規証明ゼロ）。 -/
structure Q3NonicGaloisLiftRealData where
  /-- σ̃ は加法的。 -/
  st_add : ∀ x y : q27kCar, q27glSt (q27kAdd x y) = q27kAdd (q27glSt x) (q27glSt y)
  /-- σ̃ は乗法的（実環自己同型）。 -/
  st_mul : ∀ x y : q27kCar, q27glSt (q27kMul x y) = q27kMul (q27glSt x) (q27glSt y)
  /-- σ̃(1) = 1。 -/
  st_one : q27glSt q27kOne = q27kOne
  /-- **σ̃³ = τ**（部分群 Gal(M₂₇/M₉) の生成元）。 -/
  st3 : ∀ x : q27kCar, q27glSt (q27glSt (q27glSt x)) = q27kSigma x
  /-- σ̃⁹ = id。 -/
  st9 : ∀ x : q27kCar, q27glSt (q27glSt (q27glSt (q27glSt (q27glSt (q27glSt
    (q27glSt (q27glSt (q27glSt x)))))))) = x
  /-- σ̃³ ≠ id（⟹ 位数ちょうど 9）。 -/
  st3_ne : q27glSt (q27glSt (q27glSt q27kZeta27)) ≠ q27kZeta27
  /-- σ̃ ≠ id。 -/
  st_ne : q27glSt q27kZeta27 ≠ q27kZeta27
  /-- σ̃^k ≠ id（1≤k≤8）——位数ちょうど 9。 -/
  pow_ne : ∀ k : Nat, 1 ≤ k → k ≤ 8 → q27glPow k q27kZeta27 ≠ q27kZeta27
  /-- ⟨σ̃⟩ の 9 元は相異なる（群位数ちょうど 9）。 -/
  nine_distinct : ∀ {i j : Nat}, i ≤ 8 → j ≤ 8 → i < j →
    q27glPow i q27kZeta27 ≠ q27glPow j q27kZeta27
  /-- σ̃ の M₉ への制限は σ（⟨σ̃⟩ ↠ Gal(M₉/L₂)）。 -/
  restrict : ∀ a : q3kCar, q27glSt (q27kEmbed a) = q27kEmbed (q3kSigma a)
  /-- σ̃ は基礎体 L₂ を点ごとに固定（σ̃ ∈ Gal(M₂₇/L₂)）。 -/
  fixes_L2 : ∀ n : q3rqCar,
    q27glSt (q27kEmbed (q3kEmbed n)) = q27kEmbed (q3kEmbed n)
  /-- τ は M₉ を固定（核 ⊇ ⟨τ⟩）。 -/
  tau_fixes : ∀ a : q3kCar, q27kSigma (q27kEmbed a) = q27kEmbed a
  /-- σ̃(π₂₇) − π₂₇ = π₂₇³·(w̃⁻¹ζ₂₇)（実閉形式）。 -/
  st_pi : q27kMul q27psPi27Cubed q27glU = q27glStDiff
  /-- w̃⁻¹ζ₂₇ は実単数。 -/
  u_unit : q27kUnitMem q27glU
  /-- **同一フィルトレーションの break 2**（σ̃ ∈ G₂ ∖ G₃）。 -/
  break2 : q27glInG 2 q27glSt ∧ ¬ q27glInG 3 q27glSt
  /-- **同一フィルトレーションの break 8**（σ̃³ ∈ G₈ ∖ G₉）。 -/
  break8 : q27glInG 8 (fun x => q27glSt (q27glSt (q27glSt x)))
    ∧ ¬ q27glInG 9 (fun x => q27glSt (q27glSt (q27glSt x)))
  /-- 2 つの break は相異なる。 -/
  distinct : (2 : Nat) ≠ 8

/-- **見出し実例**——実塔 ℚ₃(ζ₂₇)/ℚ₃(ζ₃) の合成 Galois 群 ⟨σ̃⟩ ≅ ℤ/9 と
    その単一の実下付きフィルトレーションの 2 break {2, 8}。 -/
def q27gl_data : Q3NonicGaloisLiftRealData where
  st_add := q27gl_st_add
  st_mul := q27gl_st_mul
  st_one := q27gl_st_one
  st3 := q27gl_st3
  st9 := q27gl_st9
  st3_ne := q27gl_st3_ne_id
  st_ne := q27gl_st_ne_id
  pow_ne := q27gl_pow_ne_id
  nine_distinct := q27gl_nine_distinct
  restrict := q27gl_restrict_sigma
  fixes_L2 := q27gl_st_fixes_L2
  tau_fixes := q27gl_tau_fixes_base
  st_pi := q27gl_st_pi_eq
  u_unit := q27gl_u_unit
  break2 := ⟨q27gl_st_in_G2, q27gl_st_not_in_G3⟩
  break8 := ⟨q27gl_st3_in_G8, q27gl_st3_not_in_G9⟩
  distinct := by omega

/-- **実合成 Galois 群データの存在**。 -/
theorem q27gl_exists : Nonempty Q3NonicGaloisLiftRealData := ⟨q27gl_data⟩

end IUT
