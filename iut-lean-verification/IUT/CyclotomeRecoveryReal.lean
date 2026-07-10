/-
  IUT/CyclotomeRecoveryReal.lean — CRR（柱A6 実 mono-anabelian 円分体復元の本丸 A6a:
  実 χ による mono-anabelian 円分体復元と、M334F が「決して導出しない」とした外部仮説
  cycRecGeoCompatible の実 discharge）

  ── 主要成果の分類: **[実／昇格(a)]**（骨格・模型・代理でなく、実 Gal(ℚ(ζ_{3^ℓ})/ℚ)
     の実 μ_{3^ℓ}=`cmrMu` 上の**非自明**な実円分指標 χ=`cgarRecChar`（σ₂→2≠1）を主語に、
     M334F の復元機構 `cycRecCharacter`→`cycRec_mu_from_chi`（χ からの円分体 μ̂ の復元）を
     実 χ で回し、さらに M443F `cid_galois_equivariant`（同位数 CycMuGroup 間の明示同型の
     Galois 同変性・一般定理）へ **実主語（実 Gal・実 μ_{3^ℓ}・実 χ）を代入**することで、
     M334F の外部仮説 `cycRecGeoCompatible`（真の幾何作用が χ 捻りに一致するという「決して
     導出しない」仮説）を、**実円分体 ℚ(ζ_{3^ℓ}) を幾何側とする忠実な部分ケースで定理化
     （discharge）**する）。

  **complete_pct 影響**: A6（mono-anabelian 復元）——**M334F の trivial-χ 実例
  （`cycRecGaloisCyclotome`・χ≡1 恒等作用）と、M334F が外部仮説として明示的に受け取り
  「決して導出しない」とした `cycRecGeoCompatible` を、実非自明 χ（`cgarRecChar`・σ₂→2）・
  実 μ_{3^ℓ}（`cmrMu`）・実 Gal 作用（`cgarAct`）で discharge**（`crr_geo_compatible`）する。
  復元作用が σ₂ で非自明（`crr_recovered_nontrivial`）であることで、M334F trivial 実例
  （恒等作用）との対比を実現。設計見込み A6 0.5→0.55・柱A 44→45 を独立監査に諮る
  （A6a 本体・監査確定待ち）。既存 surrogate（M334F trivial 実例）は消さない・弱めない。

  内容（設計 audit/A-next-leverage-scope-2026-07-10.md §6.1・CRR-0〜6）:
   * `crr_zmodMul_add`/`crr_zmodMul_one` — zmod 分配則・右単位（χ 捻り Hom 化の簿記）。CRR-0。
   * `crrAction`      — M334F 抽象 χ 入力を `CycGKAction`（Hom 化）へ。CRR-1。
   * `crr_exp_eq`     — ★実 χ での指数計算（χ(σ)·class 1 = χ(σ)・Int/Nat cast 簿記）。CRR-2。
   * `crrRecovered`   — 実 χ からの復元円分体 μ̂（`cycRec_mu_from_chi` の実主語版）。CRR-3。
   * `crr_recovered_nontrivial` — ★復元作用が σ₂ で非自明（trivial χ≡1 実例との対比）。CRR-3。
   * `crrIso`/`crr_iso_leftinv`/`crr_iso_equivariant` — 復元 μ̂ ≅ 実 μ_{3^ℓ} の G-同変同型
     （M443F cid の実主語適用・再証明しない）。CRR-4。
   * `crrGeoAct`      — 実 Galois 作用を同定で読んだ「真の幾何作用」side。CRR-5。
   * `crr_geo_compatible` — ★M334F 外部仮説 cycRecGeoCompatible の実 discharge。CRR-5。
   * `crr_geo_recovery` — 既存の仮説依存定理が本物の入力で発火する瞬間。CRR-5。
   * `CrrRealCyclotomeData`/`crrRealCyclotomeData`/`crr_scope` — capstone・正直な限定宣言。CRR-6。

  正直な限定（§4/§8 規約により消さない・弱めない・sorry で埋めない）:
   (i)   **幾何側は K̄ の μ でなく ℚ(ζ_{3^ℓ}) 自身の中の μ_{3^ℓ}**（`cmrMu`）である。
         分離閉包 K̄ の μ_n(K̄) でも π₁ の幾何的 cyclotome でもない（cmr/cgar と同じ限定を継承）。
   (ii)  **χ を π₁^ét 位相群の連続指標として抽出する本丸は依然後続**——本モジュールは χ を
         M322F 作用からの `cycRigChar`（実 Gal 作用 `cgarAct` からの抽出）として受ける。
         χ の位相連続性（mono-theta 環境の円分剛性の本丸）は M334F 同様に後続——弱めず継承。
   (iii) **p = 3・円分切片 Gal(ℚ(ζ_{3^ℓ})/ℚ) 固定**——実絶対 Galois 群 G_K・実局所体
         G_{K_v} 上ではない（G_ℚ の可解商）。A6 上限は 0.6（完全な副有限・K̄ レベルは後続）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない・propext/Quot.sound
  のみ）。禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。許可タクティク（cases/obtain/induction/rw/show/
  refine/exact/apply/intro/generalize/funext/Subtype.ext/omega）のみ使用。3^ℓ は
  omega 不可（`zpu_pow_pos` 再利用）。新規イディオム 0（cid の一般定理へ実主語代入＋
  zmod/Int cast 簿記のみ）。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/
  dashboard/graph/tools は不更新・親が統合）。prefix `crr`。
-/
import IUT.CyclotomeIdentification
import IUT.CyclotomicGKActionReal

namespace IUT

/-! ## CRR-0: zmod 簿記（χ 捻りの Hom 化に必要な分配則・右単位・cast） -/

/-- **CRR-0a: zmod 分配則** — c·(x+y) = c·x + c·y（zmod の群演算は加法・zmodMul は環の積）。
    χ 捻り x ↦ zmodMul n c x が `Hom (zmod n) (zmod n)` の map_mul を満たすための核。 -/
theorem crr_zmodMul_add (n : Nat) (c x y : (zmod n).carrier) :
    zmodMul n c ((zmod n).mul x y)
      = (zmod n).mul (zmodMul n c x) (zmodMul n c y) := by
  induction c using Quot.ind; rename_i a
  induction x using Quot.ind; rename_i b
  induction y using Quot.ind; rename_i d
  show Quot.mk (modCong n).rel (a * (b + d))
     = Quot.mk (modCong n).rel (a * b + a * d)
  rw [Int.mul_add]

/-- **CRR-0b: zmod 右単位** — c·(class 1) = c（`zmodMul_one` の再輸出）。指数計算で
    χ(σ)·(生成元 class 1) = χ(σ) を出すのに使う。 -/
theorem crr_zmodMul_one (n : Nat) (c : (zmod n).carrier) :
    zmodMul n c (Quot.mk (modCong n).rel 1) = c :=
  zmodMul_one n c

/-- **CRR-0c: Nat 剰余 = Int 剰余の toNat**（`Int.ofNat_mod_ofNat`＋`Int.toNat_natCast`）。
    cycMuStd.log の toNat（Int 側）と Nat 指数の突き合わせ（`crr_exp_eq` の cast 簿記）。 -/
theorem crr_nat_mod_toNat (a l : Nat) :
    a % l = (((a : Int) % (l : Int)).toNat) := by
  rw [Int.ofNat_mod_ofNat, Int.toNat_natCast]

/-! ## CRR-1: χ 捻りの CycGKAction 化（M334F 抽象 χ を Hom 化） -/

/-- **CRR-1: χ 捻りの `CycGKAction`** — 円分指標 χ から、g ∈ G_K が ℤ/n=`zmod n` に
    x ↦ χ(g)·x（zmodMul）で作用する `CycGKAction`（各 g ↦ `Hom (zmod n) (zmod n)`）を組む。
    M334F の `cycRecGKModule`（raw 関数）と違い、M443F cid が要求する Hom 付き作用。 -/
def crrAction (GK : Grp) (n : Nat) (hn : 1 ≤ n) (χ : cycRecCharacter GK n) :
    CycGKAction GK (cycMuStd n hn) where
  act := fun g => { map := fun x => zmodMul n (χ.chi g) x,
                    map_mul := fun x y => crr_zmodMul_add n (χ.chi g) x y }
  act_one := fun z => by
    show zmodMul n (χ.chi GK.one) z = z
    rw [χ.chi_one]
    exact zmodOne_mul n z
  act_mul := fun g h z => by
    show zmodMul n (χ.chi (GK.mul g h)) z
       = zmodMul n (χ.chi g) (zmodMul n (χ.chi h) z)
    rw [χ.chi_hom, zmodMul_assoc]

/-! ## CRR-2: 実 χ での指数計算（本ファイル最大の簿記） -/

/-- **CRR-2（★実 χ 指数計算・cast 簿記）** — 実円分指標 χ=`cgarRecChar` を捻りに持つ
    `crrAction` の円分指数（`cycRigExp`）は、実 Gal 作用 `cgarAct` の円分指数と mod 3^ℓ で
    一致する。LHS: χ(σ)·(生成元 class 1)=χ(σ)（`crr_zmodMul_one`）、cycMuStd.log=(·%n).toNat、
    cgarRecChar.chi σ = class(cycRigExp cgarAct σ : Int) ⟹ LHS = (E % 3^ℓ)（`crr_nat_mod_toNat`）。
    E<3^ℓ ではないので `Nat.mod_eq_of_lt`（E%3^ℓ<3^ℓ）で両側 mod を合流。 -/
theorem crr_exp_eq (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) :
    cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ))
        (crrAction (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) (zpu_pow_pos ℓ)
          (cgarRecChar ℓ hℓ)) σ % 3 ^ ℓ
      = cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ % 3 ^ ℓ := by
  have hLHS : cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ))
        (crrAction (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) (zpu_pow_pos ℓ)
          (cgarRecChar ℓ hℓ)) σ
      = cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ % 3 ^ ℓ := by
    show (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ)).log
        (((crrAction (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) (zpu_pow_pos ℓ)
            (cgarRecChar ℓ hℓ)).act σ).map (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ)).ζ)
      = cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ % 3 ^ ℓ
    rw [show ((crrAction (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) (zpu_pow_pos ℓ)
              (cgarRecChar ℓ hℓ)).act σ).map (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ)).ζ
          = (cgarRecChar ℓ hℓ).chi σ from
        zmodMul_one (3 ^ ℓ) ((cgarRecChar ℓ hℓ).chi σ)]
    show (((cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ : Int)
          % ((3 ^ ℓ : Nat) : Int)).toNat)
      = cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ % 3 ^ ℓ
    exact (crr_nat_mod_toNat
      (cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ) (3 ^ ℓ)).symm
  rw [hLHS]
  exact Nat.mod_eq_of_lt
    (Nat.mod_lt (cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ) σ)
      (by have := zpu_pow_pos ℓ; omega))

/-! ## CRR-3: 実 χ の復元円分体（M334F trivial 実例の実主語版・併設） -/

/-- **CRR-3a: 実 χ からの復元円分体 μ̂** — 実円分指標 χ=`cgarRecChar`（非自明）から
    `cycRec_mu_from_chi` で復元した円分体（G_K-加群、位数 3^ℓ）。M334F の trivial 実例
    `cycRecGaloisCyclotome`（χ≡1・恒等作用）の実主語（非自明 χ）版・併設。 -/
def crrRecovered (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    cycRecGKModule (galoisGroupGrp (cteExt ℓ hℓ)) :=
  cycRec_mu_from_chi (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) (cgarRecChar ℓ hℓ)

/-- **CRR-3b（★非自明性・trivial 実例との対比）: 復元作用が σ₂ で非自明** — 復元円分体の
    G_K 作用は代入自己同型 σ₂ で class 1 を class 2（=χ(σ₂)）に送る（≠ class 1）。
    M334F trivial-χ 実例（恒等作用 σ_g(x)=x）との明示的対比。χ(σ₂)=2（`cgar_sigma2_exp`）・
    class 2 ≠ class 1（2−1=1・3^ℓ∤1・`quot_exact`）で分離。 -/
theorem crr_recovered_nontrivial (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    (crrRecovered ℓ hℓ).act (cgarSigma2 ℓ hℓ) (Quot.mk (modCong (3 ^ ℓ)).rel 1)
      ≠ Quot.mk (modCong (3 ^ ℓ)).rel 1 := by
  intro heq
  have hact : (crrRecovered ℓ hℓ).act (cgarSigma2 ℓ hℓ) (Quot.mk (modCong (3 ^ ℓ)).rel 1)
      = Quot.mk (modCong (3 ^ ℓ)).rel ((2 : Nat) : Int) := by
    show zmodMul (3 ^ ℓ) ((cgarRecChar ℓ hℓ).chi (cgarSigma2 ℓ hℓ))
        (Quot.mk (modCong (3 ^ ℓ)).rel 1)
      = Quot.mk (modCong (3 ^ ℓ)).rel ((2 : Nat) : Int)
    rw [zmodMul_one (3 ^ ℓ) ((cgarRecChar ℓ hℓ).chi (cgarSigma2 ℓ hℓ))]
    show Quot.mk (modCong (3 ^ ℓ)).rel
        ((cycRigExp (galoisGroupGrp (cteExt ℓ hℓ)) (cmrMu ℓ hℓ) (cgarAct ℓ hℓ)
            (cgarSigma2 ℓ hℓ) : Int))
      = Quot.mk (modCong (3 ^ ℓ)).rel ((2 : Nat) : Int)
    rw [cgar_sigma2_exp ℓ hℓ]
  rw [hact] at heq
  have hrel : ((3 ^ ℓ : Nat) : Int) ∣ (((2 : Nat) : Int) - (1 : Int)) :=
    quot_exact intGrp (modCong (3 ^ ℓ)) heq
  have he : ((2 : Nat) : Int) - (1 : Int) = ((1 : Nat) : Int) := by omega
  rw [he] at hrel
  have hdn : (3 ^ ℓ) ∣ 1 := Int.ofNat_dvd.mp hrel
  have h1 : 3 ^ ℓ = 1 := Nat.dvd_one.mp hdn
  have := cgar_two_lt ℓ hℓ
  omega

/-! ## CRR-4: 復元 μ̂ ≅ 実 μ_{3^ℓ} の G-同変同型（M443F cid の実主語適用） -/

/-- **CRR-4a: 復元 μ̂ ≅ 実 μ_{3^ℓ} の明示同型** — 標準模型 `cycMuStd (3^ℓ)`（復元 μ̂ の台）と
    実 μ_{3^ℓ}=`cmrMu`（両者とも位数 3^ℓ）の間の M443F `cidIso`（双方向逆写像つき同型）。 -/
def crrIso (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    Hom (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ)).μ (cmrMu ℓ hℓ).μ :=
  cidIso (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ)) (cmrMu ℓ hℓ) rfl

/-- **CRR-4b: 逆写像で往復消去** — `cid_iso_leftinv` の実主語適用
    （cmuMap (cmrMu)(cycMuStd) ∘ crrIso.map = id）。`crr_geo_compatible` で往復を消す核。 -/
theorem crr_iso_leftinv (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (w : (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ)).μ.carrier) :
    cmuMap (cmrMu ℓ hℓ) (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ)) ((crrIso ℓ hℓ).map w) = w :=
  cid_iso_leftinv (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ)) (cmrMu ℓ hℓ) rfl w

/-- **CRR-4c（★G-同変同型・A6a ヘッドライン前半）: crrIso は Gal 作用と可換** — χ 捻り側
    （復元 μ̂ の `crrAction`）と実 Gal 側（`cgarAct`）が同じ mod-3^ℓ 指数を持つ（`crr_exp_eq`）
    ので、M443F 一般定理 `cid_galois_equivariant` に実主語（実 Gal・実 μ・実 χ）を代入する
    だけで σ_g(crrIso z)=crrIso(σ_g z) を得る（再証明しない）。 -/
theorem crr_iso_equivariant (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier)
    (x : (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ)).μ.carrier) :
    (crrIso ℓ hℓ).map
        (((crrAction (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) (zpu_pow_pos ℓ)
            (cgarRecChar ℓ hℓ)).act σ).map x)
      = ((cgarAct ℓ hℓ).act σ).map ((crrIso ℓ hℓ).map x) :=
  cid_galois_equivariant (galoisGroupGrp (cteExt ℓ hℓ))
    (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ)) (cmrMu ℓ hℓ) rfl
    (crrAction (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) (zpu_pow_pos ℓ) (cgarRecChar ℓ hℓ))
    (cgarAct ℓ hℓ) (fun g => crr_exp_eq ℓ hℓ g) σ x

/-! ## CRR-5: ★cycRecGeoCompatible の実 discharge（A6a のヘッドライン本丸） -/

/-- **CRR-5a: 「真の幾何作用」side** — 実 Gal 作用（体自己同型 σ の実 μ_{3^ℓ} への制限）を
    crrIso で復元 μ̂ の台 ℤ/3^ℓ に読み戻したもの。M334F の外部仮説 `geoAct` に相当する
    「真の幾何 μ 上の Galois 作用」を、実円分体 ℚ(ζ_{3^ℓ}) の中で実現した側。 -/
def crrGeoAct (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    (galoisGroupGrp (cteExt ℓ hℓ)).carrier
      → (zmod (3 ^ ℓ)).carrier → (zmod (3 ^ ℓ)).carrier :=
  fun σ x => cmuMap (cmrMu ℓ hℓ) (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ))
    (((cgarAct ℓ hℓ).act σ).map ((crrIso ℓ hℓ).map x))

/-- **CRR-5b（★M334F 外部仮説の実 discharge・A6a のヘッドライン本丸）** — M334F が
    「決して導出しない」とした外部仮説 `cycRecGeoCompatible`（真の幾何作用が χ 捻りに一致）を、
    実円分体 ℚ(ζ_{3^ℓ}) を幾何側とする忠実な部分ケースで**定理化**する:
      ∀ σ x, crrGeoAct σ x = zmodMul (3^ℓ) (χ(σ)) x。
    `crr_iso_equivariant` で作用を χ 捻り側へ移送し、`crr_iso_leftinv` で crrIso の往復を消す。
    （正直な限定 §8: 幾何側は K̄ の μ でなく ℚ(ζ) 自身の μ・χ の位相連続性は未・p=3/ℚ 固定。） -/
theorem crr_geo_compatible (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    cycRecGeoCompatible (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ)
      (cgarRecChar ℓ hℓ) (crrGeoAct ℓ hℓ) := by
  intro σ x
  show cmuMap (cmrMu ℓ hℓ) (cycMuStd (3 ^ ℓ) (zpu_pow_pos ℓ))
      (((cgarAct ℓ hℓ).act σ).map ((crrIso ℓ hℓ).map x))
    = zmodMul (3 ^ ℓ) ((cgarRecChar ℓ hℓ).chi σ) x
  rw [← crr_iso_equivariant ℓ hℓ σ x]
  exact crr_iso_leftinv ℓ hℓ
    (((crrAction (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) (zpu_pow_pos ℓ)
        (cgarRecChar ℓ hℓ)).act σ).map x)

/-- **CRR-5c: 仮説依存定理が本物の入力で発火** — M334F の `cycRec_geo_recovery_hypothesis`
    （仮説スロットに `crr_geo_compatible` を差す）— 真の幾何作用 `crrGeoAct` が復元円分体
    `crrRecovered` の作用に一致する。外部仮説が本物の入力で発火する瞬間。 -/
theorem crr_geo_recovery (ℓ : Nat) (hℓ : 1 ≤ ℓ)
    (σ : (galoisGroupGrp (cteExt ℓ hℓ)).carrier) (x : (zmod (3 ^ ℓ)).carrier) :
    crrGeoAct ℓ hℓ σ x = (crrRecovered ℓ hℓ).act σ x :=
  cycRec_geo_recovery_hypothesis (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ)
    (cgarRecChar ℓ hℓ) (crrGeoAct ℓ hℓ) (crr_geo_compatible ℓ hℓ) σ x

/-! ## CRR-6: capstone（束ね・新規証明ゼロ）と正直な限定宣言 -/

/-- **CRR-6a: 実 mono-anabelian 円分体復元データ** — 実 χ からの復元円分体 μ̂、その σ₂ での
    非自明性、復元 μ̂ ≅ 実 μ_{3^ℓ} の G-同変同型、M334F 外部仮説 cycRecGeoCompatible の実
    discharge を束ねる（A6a の総括）。 -/
structure CrrRealCyclotomeData (ℓ : Nat) (hℓ : 1 ≤ ℓ) where
  /-- 実 χ から復元した円分体 μ̂（G_K-加群）。 -/
  recovered : cycRecGKModule (galoisGroupGrp (cteExt ℓ hℓ))
  /-- 復元は `crrRecovered`（実 χ=`cgarRecChar` から）に一致。 -/
  recovered_eq : recovered = crrRecovered ℓ hℓ
  /-- 復元作用が σ₂ で非自明（trivial χ≡1 実例との対比）。 -/
  nontrivial : (crrRecovered ℓ hℓ).act (cgarSigma2 ℓ hℓ) (Quot.mk (modCong (3 ^ ℓ)).rel 1)
    ≠ Quot.mk (modCong (3 ^ ℓ)).rel 1
  /-- 復元 μ̂ ≅ 実 μ_{3^ℓ} の G-同変同型。 -/
  iso_equivariant : ∀ σ x, (crrIso ℓ hℓ).map
      (((crrAction (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ) (zpu_pow_pos ℓ)
          (cgarRecChar ℓ hℓ)).act σ).map x)
    = ((cgarAct ℓ hℓ).act σ).map ((crrIso ℓ hℓ).map x)
  /-- M334F 外部仮説 cycRecGeoCompatible の実 discharge。 -/
  geo_discharge : cycRecGeoCompatible (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ)
    (cgarRecChar ℓ hℓ) (crrGeoAct ℓ hℓ)

/-- **CRR-6b: witness 本体**（全フィールドを本モジュールの完全証明で埋める・新規証明ゼロ）。 -/
def crrRealCyclotomeData (ℓ : Nat) (hℓ : 1 ≤ ℓ) : CrrRealCyclotomeData ℓ hℓ where
  recovered := crrRecovered ℓ hℓ
  recovered_eq := rfl
  nontrivial := crr_recovered_nontrivial ℓ hℓ
  iso_equivariant := crr_iso_equivariant ℓ hℓ
  geo_discharge := crr_geo_compatible ℓ hℓ

/-- **CRR-6c: A6a の要約と正直な限定宣言** — (1) M334F 外部仮説 cycRecGeoCompatible の実
    discharge（`crr_geo_compatible`）、(2) 真の幾何作用 = 復元円分体作用（`crr_geo_recovery`）。
    正直な限定（ヘッダ §8）: 幾何側は K̄ の μ でなく ℚ(ζ_{3^ℓ}) 自身の μ_{3^ℓ}、χ の位相
    連続性は未（π₁^ét 連続指標抽出は後続）、p=3・Gal(ℚ(ζ_{3^ℓ})/ℚ) 固定（A6 上限 0.6）。 -/
theorem crr_scope (ℓ : Nat) (hℓ : 1 ≤ ℓ) :
    cycRecGeoCompatible (galoisGroupGrp (cteExt ℓ hℓ)) (3 ^ ℓ)
        (cgarRecChar ℓ hℓ) (crrGeoAct ℓ hℓ)
      ∧ crrGeoAct ℓ hℓ (cgarSigma2 ℓ hℓ) (Quot.mk (modCong (3 ^ ℓ)).rel 1)
          = (crrRecovered ℓ hℓ).act (cgarSigma2 ℓ hℓ) (Quot.mk (modCong (3 ^ ℓ)).rel 1) :=
  ⟨crr_geo_compatible ℓ hℓ, crr_geo_recovery ℓ hℓ (cgarSigma2 ℓ hℓ)
    (Quot.mk (modCong (3 ^ ℓ)).rel 1)⟩

end IUT
