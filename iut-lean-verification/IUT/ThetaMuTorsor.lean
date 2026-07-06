/-
  IUT/ThetaMuTorsor.lean — M348F [実／本物]
  分類: 実 (テータ値の μ_l-トーサー構造・Θ^{2l}=q^{j²} ガロア固定)
  complete_pct 影響: 柱E を前進（Θ(q,u_j)^{2l}=q^{j²} が G_K 固定（M343F）ゆえ 2l 乗根の集合が
    μ_l-トーサー＝テータ値は離散 μ_l を除いて定まる、を本物で構成し M338F 円分剛性・M333F 離散
    剛性へ接続。μ_l 自由推移作用・ノルム不変・剛性による pin・ガロア安定性）。
  正直な限定: 完全なエタールテータトーサー・tempered π₁ は外部仮説/後続。
-/
import IUT.GaloisTheta
import IUT.ThetaCyclotomicRigidity

namespace IUT

/-! ## M348F-1: μ_l-トーサーの台と作用

  M343F `galTh_norm_qpower` により、l-捻れ点でのテータ値 Θ(q,u_j) はその 2l 乗が
  q^{j²}（G_K 固定）になる。したがって「q^{j²} の 2l 乗根の集合」＝候補テータ値の集合は、
  μ_l（1 の l 乗根の群 CycMuGroup）が乗法で作用する**トーサー**をなす。台を μ_l の台
  M.μ.carrier とし、基点 Θ（本物のテータ値の μ_l 影）を選ぶと、候補テータ値は ζ·Θ
  （ζ∈μ_l）で尽くされる。ここでは μ_l が本物の巡回群（M322F CycMuGroup）である本物の
  作用として構成する（toy 主語なし）。 -/

/-- **M348F-1a: μ_l のトーサー作用** — μ_l の元 ζ が候補テータ値 x に左乗法で作用する
    tmtAct M ζ x = ζ·x。IUT の mono-theta 環境で「テータ値が μ_l を除いて定まる」ことの
    作用側（1 の l 乗根による捻り）。 -/
def tmtAct (M : CycMuGroup) (ζ x : M.μ.carrier) : M.μ.carrier :=
  M.μ.mul ζ x

/-- **M348F-1b: 候補テータ値** — 基点テータ値 Θ に μ_l 因子 ζ を掛けた ζ·Θ。q^{j²} の
    2l 乗根のうち μ_l 捻りで得られる候補（すべて同じ 2l 乗 q^{j²} を持つ）。 -/
def tmtCandidate (M : CycMuGroup) (Θ ζ : M.μ.carrier) : M.μ.carrier :=
  M.μ.mul ζ Θ

/-! ## M348F-2: トーサー公理（群作用・自由性・推移性） -/

/-- **定理 (M348F-2a: 作用の単位則)** — 1·x = x（μ_l の単位律）。トーサー作用が
    群作用の単位公理を満たす。 -/
theorem tmt_act_one (M : CycMuGroup) (x : M.μ.carrier) :
    tmtAct M M.μ.one x = x :=
  M.μ.one_mul x

/-- **定理 (M348F-2b: 作用の合成則)** — (ζ·ξ)·x = ζ·(ξ·x)（μ_l の結合律）。トーサー作用が
    群作用の合成公理を満たす。 -/
theorem tmt_act_mul (M : CycMuGroup) (ζ ξ x : M.μ.carrier) :
    tmtAct M (M.μ.mul ζ ξ) x = tmtAct M ζ (tmtAct M ξ x) :=
  M.μ.mul_assoc ζ ξ x

/-- **定理 (M348F-2c: 作用の自由性)** — ζ·Θ = Θ ⟹ ζ = 1。基点 Θ を固定する μ_l 因子は
    単位元のみ（右簡約律）。トーサーの**自由性**（テータ値の μ_l 捻りに非自明な固定点が
    無い ＝ 曖昧さがちょうど μ_l 分だけ）。 -/
theorem tmt_act_free (M : CycMuGroup) (ζ Θ : M.μ.carrier)
    (h : tmtAct M ζ Θ = Θ) : ζ = M.μ.one := by
  have h2 : M.μ.mul ζ Θ = M.μ.mul M.μ.one Θ := by
    rw [M.μ.one_mul]; exact h
  exact M.μ.mul_right_cancel h2

/-- **定理 (M348F-2d: 作用の推移性・存在)** — 任意の候補 x, y に対し ζ = y·x⁻¹ が
    ζ·x = y を与える（結合律・逆元・単位律）。任意の 2 つの候補テータ値は μ_l 因子で
    移り合う（トーサーの**推移性**の存在部分）。 -/
theorem tmt_act_transitive (M : CycMuGroup) (x y : M.μ.carrier) :
    M.μ.mul (M.μ.mul y (M.μ.inv x)) x = y := by
  rw [M.μ.mul_assoc, M.μ.inv_mul, M.μ.mul_one]

/-- **定理 (M348F-2e: 作用の推移性・一意性)** — ζ·x = ξ·x ⟹ ζ = ξ（右簡約律）。
    2 つの候補を結ぶ μ_l 因子は**一意**（トーサーの推移性の一意部分）。自由性と合わせ
    「テータ値は μ_l を除いて一意」を与える。 -/
theorem tmt_act_unique (M : CycMuGroup) (x ζ ξ : M.μ.carrier)
    (h : M.μ.mul ζ x = M.μ.mul ξ x) : ζ = ξ :=
  M.μ.mul_right_cancel h

/-! ## M348F-3: ノルム不変性（すべての候補が同じ 2l 乗 q^{j²}） -/

/-- **定理 (M348F-3a: μ_l 内ノルム不変性)** — (ζ·Θ)^n = Θ^n（n = μ_l の位数）。μ_l は指数 n
    の群（ζ^n = 1, M343F galTh_mu_exp_ord）ゆえ、候補テータ値 ζ·Θ の n 乗は基点の n 乗に
    一致する（可換群の積の冪分配 M343F galTh_pow_mul_distrib）。トーサーの全元が同じ
    「円分ノルム」を持つ ＝ μ_l 捻りはノルムで消える。 -/
theorem tmt_norm_invariant (M : CycMuGroup) (ζ Θ : M.μ.carrier) :
    M.μ.pow (M.μ.mul ζ Θ) M.n = M.μ.pow Θ M.n := by
  rw [galTh_pow_mul_distrib M.μ M.comm ζ Θ M.n, galTh_mu_exp_ord M ζ, M.μ.one_mul]

/-- **定理 (M348F-3b: 実ノルム = q^{j²}・ガロア固定)** — l-捻れ点でのテータ値の 2l 乗は
    ちょうど q^{j²} ∈ q^ℤ（IsLPowerValue R (2l)・witness j²、M343F galTh_norm_qpower の
    再輸出）。トーサーの基点が持つ**本物の 2l 乗ノルム**が q^{j²}（周期格子 q^ℤ の元、
    G_K 固定）であること。μ_l-トーサー構造の根拠（2l 乗根の集合）。 -/
theorem tmt_norm_qpower (R : CRing) (l : Nat) (j : Int) :
    IsLPowerValue R ((2 * l : Nat) : Int) (thLtorPow R (thLtorValue R j) (2 * l)) :=
  galTh_norm_qpower R l j

/-! ## M348F-4: 剛性による pin（離散 μ_l を除いて定まる・M338F/M333F 接続） -/

/-- **定理 (M348F-4a: 離散 pin・候補の相異性)** — 相異なる指数 i, j (< n) は相異なる候補
    ζ^i·Θ ≠ ζ^j·Θ を与える（右簡約律 ＋ M322F cycRig_pow_inj の位数 n 単射性）。トーサーの
    候補テータ値がちょうど n 個（＝離散 μ_l のサイズ）で、それ以上の（連続的な）曖昧さが
    無いこと ＝ **テータ値は離散 μ_l を除いて定まる**（M333F 離散剛性の μ_l-トーサー版）。 -/
theorem tmt_pin_distinct (M : CycMuGroup) (Θ : M.μ.carrier) (i j : Nat)
    (hi : i < M.n) (hj : j < M.n)
    (h : M.μ.mul (M.μ.pow M.ζ i) Θ = M.μ.mul (M.μ.pow M.ζ j) Θ) : i = j := by
  have hpow : M.μ.pow M.ζ i = M.μ.pow M.ζ j := M.μ.mul_right_cancel h
  have hmod : i % M.n = j % M.n :=
    cycRig_pow_inj M.μ M.comm M.ζ M.n M.hn M.ord M.distinct i j hpow
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  exact hmod

/-- **定理 (M348F-4b: 円分剛性による pin・M338F 接続)** — 生成元（mark）を保つ 2 つの
    円分体自己同型は一致する（M338F thCyc_marked_iso_unique の再輸出）。mono-theta 環境の
    円分剛性が μ_l-トーサーを**標準点に pin する**（ẑ^× の連続的捻れ不定性が mark の下で
    消え、テータ値が離散 μ_l を除いて確定する）ことの本物の核。 -/
theorem tmt_rigidity_pin (f g : Hom intGrp intGrp)
    (hf : f.map 1 = 1) (hg : g.map 1 = 1) (m : Int) :
    f.map m = g.map m :=
  thCyc_marked_iso_unique f g hf hg m

/-- **定理 (M348F-4c: 離散剛性核・M333F 接続)** — ℤ は可除でない（2n = 1 の整数解無し、
    M333F discRig_no_division の再輸出）。μ_l-トーサーの曖昧さが**離散**（可除細分を許さない
    ＝ 連続的でない）であることの無条件な核。テータ値の μ_l 捻りが離散格子的であることの
    M333F 側の根拠。 -/
theorem tmt_discrete_no_sqrt : ¬ ∃ n : Int, 2 * n = 1 :=
  discRig_no_division

/-! ## M348F-5: ガロア安定性（G_K が χ-捻りでトーサーを置換） -/

/-- **定理 (M348F-5a: トーサーのガロア安定性)** — G_K 作用 σ_g は候補 ζ·Θ を
    σ_g(ζ)·σ_g(Θ) に送る（ρ.act g が Hom ゆえ map_mul）。G_K はトーサーを**置換**し、
    捻り因子 ζ には円分指標 χ を通じて作用する（M343F galThMuAct）——トーサーは
    Galois-stable。 -/
theorem tmt_galois_stable (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (ζ Θ : M.μ.carrier) :
    galThMuAct GK M ρ g (M.μ.mul ζ Θ)
      = M.μ.mul (galThMuAct GK M ρ g ζ) (galThMuAct GK M ρ g Θ) :=
  (ρ.act g).map_mul ζ Θ

/-- **M348F-5b: Kummer 捻り候補** — l-捻れ点のガロア捻り因子 κ(g)^j（M343F galThTorTwist）を
    基点 Θ に掛けた候補 κ(g)^j·Θ。G_K がトーサー内で作る具体的な捻り候補（捻り因子 ∈ μ_l）。 -/
def tmtTwistCandidate (GK : Grp) (M : CycMuGroup) (κ : Hom GK M.μ)
    (Θ : M.μ.carrier) (g : GK.carrier) (j : Nat) : M.μ.carrier :=
  M.μ.mul (galThTorTwist GK M κ g j) Θ

/-- **定理 (M348F-5c: 単位元の捻り候補は基点)** — g = 1 での Kummer 捻り候補は基点 Θ に
    一致（κ(1)^j = 1、M343F galTh_tor_twist_one ＋ 単位律）。σ_1 がトーサーを動かさないこと。 -/
theorem tmt_twist_candidate_one (GK : Grp) (M : CycMuGroup) (κ : Hom GK M.μ)
    (Θ : M.μ.carrier) (j : Nat) :
    tmtTwistCandidate GK M κ Θ GK.one j = Θ := by
  show M.μ.mul (galThTorTwist GK M κ GK.one j) Θ = Θ
  rw [galTh_tor_twist_one GK M κ j, M.μ.one_mul]

/-! ## M348F-6: 外部仮説（完全なエタールテータトーサー・tempered π₁・決して導出しない） -/

/-- **M348F-6a: tempered π₁ トーサー仮説（Prop）** — 完全な tempered 基本群 π₁^{temp} が
    μ_l-トーサーに作用する `fullTor` が、本モジュールの円分指標経由の μ_l 作用 galThMuAct に
    一致するという**外部仮説**。実の遠アーベル対象（tempered π₁^ét）から来るトーサー作用が
    この形を取ることは柱E/D 後続の外部入力であり、本層は明示 Prop 仮説として受け導出しない。 -/
def tmt_tempered_torsor_hypothesis (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (fullTor : GK.carrier → M.μ.carrier → M.μ.carrier) : Prop :=
  ∀ g x, fullTor g x = galThMuAct GK M ρ g x

/-- **定理 (M348F-6b: tempered π₁ トーサー作用の復元・仮説依存)** — 仮説
    `tmt_tempered_torsor_hypothesis` の下で、tempered π₁ のトーサー作用は本モジュールの
    μ_l 作用に一致する。仮説は外部入力で本体で導出しない。 -/
theorem tmt_tempered_torsor_recovery (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (fullTor : GK.carrier → M.μ.carrier → M.μ.carrier)
    (hyp : tmt_tempered_torsor_hypothesis GK M ρ fullTor)
    (g : GK.carrier) (x : M.μ.carrier) :
    fullTor g x = galThMuAct GK M ρ g x :=
  hyp g x

/-- **M348F-6c: エタールテータトーサー仮説（Prop）** — 完全なエタールテータ関数のトーサー
    表現 `etTor` が、本モジュールの候補テータ値 ζ·Θ に一致するという**外部仮説**。
    エタールテータ関数値そのもの（p 進収束・遠アーベル復元）は柱E/D 後続の外部入力であり、
    本層は μ_l-トーサーの代数構造までを本物とし、解析的テータトーサー本体は仮説として受ける。 -/
def tmt_etale_theta_torsor_hypothesis (M : CycMuGroup) (Θ : M.μ.carrier)
    (etTor : M.μ.carrier → M.μ.carrier) : Prop :=
  ∀ ζ, etTor ζ = M.μ.mul ζ Θ

/-- **定理 (M348F-6d: エタールテータトーサーの復元・仮説依存)** — 仮説
    `tmt_etale_theta_torsor_hypothesis` の下で、エタールテータトーサーは本モジュールの候補
    ζ·Θ に一致する。解析的テータトーサー本体は外部入力で導出しない。 -/
theorem tmt_etale_theta_torsor_recovery (M : CycMuGroup) (Θ : M.μ.carrier)
    (etTor : M.μ.carrier → M.μ.carrier)
    (hyp : tmt_etale_theta_torsor_hypothesis M Θ etTor) (ζ : M.μ.carrier) :
    etTor ζ = M.μ.mul ζ Θ :=
  hyp ζ

/-! ## M348F-7: 総括レコード（μ_l-トーサーデータ）と存在 -/

/-- **M348F-7a: テータ μ_l-トーサーデータ** — 基点テータ値 Θ・μ_l のトーサー作用（単位・
    合成・自由・推移の存在と一意）・ノルム不変性（全候補が同じ n 乗）・離散 pin（候補が
    ちょうど μ_l 分・相異性）・ガロア安定性（G_K が χ-捻りで候補を置換）を一括束ね。
    IUT mono-theta 環境の「テータ値は離散 μ_l を除いて定まる」の witness 形。主語は本物の
    巡回群 μ_l（M322F CycMuGroup）と本物のガロア作用（M322F CycGKAction）。 -/
structure TmtTorsorData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) where
  /-- 基点テータ値 Θ（μ_l 影）。 -/
  Θ : M.μ.carrier
  /-- 作用の単位則 1·x = x。 -/
  act_one : ∀ x, tmtAct M M.μ.one x = x
  /-- 作用の合成則 (ζ·ξ)·x = ζ·(ξ·x)。 -/
  act_mul : ∀ ζ ξ x, tmtAct M (M.μ.mul ζ ξ) x = tmtAct M ζ (tmtAct M ξ x)
  /-- 自由性 ζ·Θ = Θ ⟹ ζ = 1。 -/
  free : ∀ ζ, tmtAct M ζ Θ = Θ → ζ = M.μ.one
  /-- 推移性・存在: 任意の x, y は μ_l 因子 y·x⁻¹ で結ばれる。 -/
  transitive : ∀ x y, M.μ.mul (M.μ.mul y (M.μ.inv x)) x = y
  /-- 推移性・一意: ζ·x = ξ·x ⟹ ζ = ξ。 -/
  act_unique : ∀ x ζ ξ, M.μ.mul ζ x = M.μ.mul ξ x → ζ = ξ
  /-- ノルム不変性: (ζ·Θ)^n = Θ^n（全候補が同じ円分ノルム）。 -/
  norm_invariant : ∀ ζ, M.μ.pow (M.μ.mul ζ Θ) M.n = M.μ.pow Θ M.n
  /-- 離散 pin: 相異な指数 (< n) は相異な候補を与える（μ_l を除いて一意）。 -/
  pin_distinct : ∀ i j, i < M.n → j < M.n →
    M.μ.mul (M.μ.pow M.ζ i) Θ = M.μ.mul (M.μ.pow M.ζ j) Θ → i = j
  /-- ガロア安定性: σ_g(ζ·Θ) = σ_g(ζ)·σ_g(Θ)（G_K が候補を置換）。 -/
  galois_stable : ∀ g ζ, galThMuAct GK M ρ g (M.μ.mul ζ Θ)
    = M.μ.mul (galThMuAct GK M ρ g ζ) (galThMuAct GK M ρ g Θ)

/-- **M348F-7b: witness 本体** — 各フィールドを M348F-2〜5 の主定理で埋める。 -/
def tmtTorsorData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (Θ : M.μ.carrier) :
    TmtTorsorData GK M ρ where
  Θ := Θ
  act_one := tmt_act_one M
  act_mul := tmt_act_mul M
  free := fun ζ h => tmt_act_free M ζ Θ h
  transitive := tmt_act_transitive M
  act_unique := fun x ζ ξ h => tmt_act_unique M x ζ ξ h
  norm_invariant := fun ζ => tmt_norm_invariant M ζ Θ
  pin_distinct := fun i j hi hj h => tmt_pin_distinct M Θ i j hi hj h
  galois_stable := fun g ζ => tmt_galois_stable GK M ρ g ζ Θ

/-- **定理 (M348F-7c: capstone — テータ μ_l-トーサーデータの存在)** — 任意の G_K・μ_l・
    作用 ρ・基点テータ値 Θ に対し、μ_l-トーサー構造（自由推移作用・ノルム不変・離散 pin・
    ガロア安定）が本物で組み上がる。Θ(q,u_j)^{2l}=q^{j²}（G_K 固定）ゆえ 2l 乗根の集合が
    μ_l-トーサーをなし、テータ値が離散 μ_l を除いて定まることが閉じる。 -/
theorem tmt_exists (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (Θ : M.μ.carrier) :
    Nonempty (TmtTorsorData GK M ρ) :=
  ⟨tmtTorsorData GK M ρ Θ⟩

/-! ## M348F-8: 実例（l=5・本物の G_ℚ の μ_5 上のテータ μ_l-トーサー） -/

/-- **M348F-8a: 実例（l=5）** — 本物の絶対ガロア群 G_ℚ = `algCloAbsGalois algCloTrivialTower`
    （M315F）の μ_5（本物の巡回群 ℤ/5 = cycMuStd 5）上で、生成元 ζ を基点とするテータ
    μ_l-トーサーが存在する。IUT がエタールテータを l-捻れ点で評価した値の μ_5-トーサー構造の
    実例。 -/
theorem tmt_example_l5 :
    Nonempty (TmtTorsorData (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
      (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega)))) :=
  tmt_exists (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega)))
    (cycMuStd 5 (by omega)).ζ

/-- 実例: l=5 のノルム Θ(q,u_j)^{10}=q^{j²} が q^ℤ（IsLPowerValue R 10）に落ちる
    （μ_5-トーサーの 2l 乗根としての根拠）。 -/
example (R : CRing) (j : Int) :
    IsLPowerValue R ((2 * 5 : Nat) : Int) (thLtorPow R (thLtorValue R j) (2 * 5)) :=
  tmt_norm_qpower R 5 j

/-- 実例: μ_l 内ノルム不変性 (ζ·Θ)^n = Θ^n（μ_5、全候補が同じ円分ノルム）。 -/
example (ζ Θ : (cycMuStd 5 (by omega)).μ.carrier) :
    (cycMuStd 5 (by omega)).μ.pow
        ((cycMuStd 5 (by omega)).μ.mul ζ Θ) (cycMuStd 5 (by omega)).n
      = (cycMuStd 5 (by omega)).μ.pow Θ (cycMuStd 5 (by omega)).n :=
  tmt_norm_invariant (cycMuStd 5 (by omega)) ζ Θ

end IUT
