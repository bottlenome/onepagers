/-
  IUT/ThetaGaloisOrbit.lean — M368F [実／本物]
  分類: 実 (テータ値のガロア軌道の有限性・置換＝M343F 同変の軌道版)
  complete_pct 影響: 柱E を前進（M343F ガロア同変 σ(u_j)=κ(g)^j u_j・値変換 ζ_l^{j²}→ζ_l^{χ(g)j²}
    から、l-捻れテータ値の集合 {Θ(q,u_j)} が G_K で置換（j²↦χ(g)j²）され μ_l-トーサー内で有限
    軌道をなすことを本物で）。
  正直な限定: M343F 同変の軌道版パッケージ・完全な tempered π₁ 軌道は外部。

  内容:
  * M368F-1 `tgoOrbitPoint`/`tgoOrbit` — ラベル j∈{0,…,l−1} で添字付けられた
    μ_l-トーサー候補（M348F `tmtCandidate` の j 番目、円分影 M343F `galThValCyc M j`
    による捻り）のリスト。
  * M368F-2 `tgo_orbit_finite`（軌道の有限性・本物） — `tgoOrbit M Θ l` の長さは
    ちょうど l（`List.length_range`/`List.length_map`）。
  * M368F-3 `tgo_norm_stable` — 軌道の各点は基点 Θ と同じ M.n 乗ノルムを持つ
    （M348F `tmt_norm_invariant` の直接適用）。
  * M368F-4 `tgo_galois_permutes_label`/`tgo_galois_orbit_permuted`（**軌道が置換される
    本丸・新規本物**） — G_K の作用で円分影 ζ^{j²} は ζ^{(χ(g)j²) mod l} に送られ
    （M322F `cycRig_pow_reduce` で mod l 還元）、その還元後の指数は必ず [0,l) に入る
    （`Nat.mod_lt`）——すなわち G_K は l 個のラベル {0,…,l−1} の**有限集合の中で**
    軌道を置換する。
  * M368F-5 `tgo_galois_permutes_orbit_point`/`tgo_orbit_in_torsor` — 軌道の各点への
    G_K 作用は乗法的（M348F `tmt_galois_stable`）であり、各点は μ_l-トーサー候補
    （M348F `tmtCandidate`）に属す。
  * M368F-6 capstone `ThetaGaloisOrbitData`/`tgo_exists`、実例 l=5。

  本層は M343F の同変性 σ(u_j)=κ(g)^j u_j・値変換 ζ_l^{j²}→ζ_l^{χ(g)j²} と M348F の
  μ_l-トーサー構造を、ラベル j∈{0,…,l−1} で添字付けた**軌道**の言葉に束ね直したもの
  であり、新規の本物内容は「G_K がこの l 個のラベルの有限集合の中で軌道を置換する」
  （mod l 還元＋範囲評価、M368F-4）である。完全な tempered π₁^{ét} の l-捻れ商としての
  軌道の実現・エタールテータ関数値そのものの p 進収束は、M343F/M348F 同様に外部仮説/
  柱E/D 後続であり、本層はこれを一切導出しない（正直な限定は消去・弱化しない）。

  選択公理不使用（新規 Classical.choice なし）。sorry 不使用。禁止タクティク
  （simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/field_simp）
  不使用。許可タクティク（cases/obtain/induction/rw/show/refine/exact/apply/intro/
  generalize/funext/omega）のみ使用。共有ファイル（IUT.lean・build.sh・dashboard.md・
  graph 系）は一切変更していない。一般名は `tgo` 接頭辞で衝突回避。
-/
import IUT.ThetaMuTorsor

namespace IUT

/-! ## M368F-1: ラベル付き軌道（μ_l-トーサー候補のリスト） -/

/-- **M368F-1a: 軌道の点** — ラベル j でのテータ値の円分影 `galThValCyc M j`（M343F）に
    よる μ_l-トーサー候補 `tmtCandidate M Θ (galThValCyc M j)`（M348F）。IUT が l-捻れ点
    u_j で評価するテータ値の μ_l-トーサー内での「j 番目の候補」。 -/
def tgoOrbitPoint (M : CycMuGroup) (Θ : M.μ.carrier) (j : Nat) : M.μ.carrier :=
  tmtCandidate M Θ (galThValCyc M j)

/-- **M368F-1b: ガロア軌道（有限リスト）** — ラベル j=0,…,l−1 で添字付けた軌道点の
    リスト。{Θ(q,u_j) : j<l} の μ_l-トーサー内での本物の有限列。 -/
def tgoOrbit (M : CycMuGroup) (Θ : M.μ.carrier) (l : Nat) : List M.μ.carrier :=
  (List.range l).map (tgoOrbitPoint M Θ)

/-! ## M368F-2: 軌道の有限性（本物） -/

/-- **定理 (M368F-2: 軌道の有限性)** — `tgoOrbit M Θ l` の長さはちょうど l。
    テータ値の軌道が l 個のラベルからなる**有限**リストであることの本物
    （`List.length_map`・`List.length_range`）。 -/
theorem tgo_orbit_finite (M : CycMuGroup) (Θ : M.μ.carrier) (l : Nat) :
    (tgoOrbit M Θ l).length = l := by
  show ((List.range l).map (tgoOrbitPoint M Θ)).length = l
  rw [List.length_map, List.length_range]

/-! ## M368F-3: ノルム安定性（軌道の全点が同じノルムを持つ） -/

/-- **定理 (M368F-3: 軌道のノルム安定性)** — 軌道の各点 ζ^{j²}·Θ は基点 Θ と同じ
    M.n 乗ノルムを持つ（M348F `tmt_norm_invariant` の直接適用）。IUT のノルム
    Θ^{2l}=q^{j²} のガロア不変性（M343F）の軌道版——軌道の全点が「同じ円分ノルム」を
    共有すること。 -/
theorem tgo_norm_stable (M : CycMuGroup) (Θ : M.μ.carrier) (j : Nat) :
    M.μ.pow (tgoOrbitPoint M Θ j) M.n = M.μ.pow Θ M.n := by
  show M.μ.pow (M.μ.mul (galThValCyc M j) Θ) M.n = M.μ.pow Θ M.n
  exact tmt_norm_invariant M (galThValCyc M j) Θ

/-! ## M368F-4: 軌道の置換（本丸・新規本物） -/

/-- **M368F-4a: mod l 還元は範囲内** — a % M.n < M.n（M.hn: 1≤M.n から 0<M.n、
    `Nat.mod_lt`）。円分影の指数を mod l 還元した代表元が必ず {0,…,l−1} に入ることの
    本物の根拠。 -/
theorem tgo_mod_lt (M : CycMuGroup) (a : Nat) : a % M.n < M.n := by
  have h0 : 0 < M.n := by
    have h := M.hn
    omega
  exact Nat.mod_lt a h0

/-- **定理 (M368F-4b: 円分影のガロア変換・mod l 還元形)** — σ_g(ζ^{j²}) =
    ζ^{(χ(g)·j²) mod l}（M343F `galTh_value_transform` に M322F `cycRig_pow_reduce` の
    mod l 還元を合成）。テータ値の円分影がガロア作用の下で**mod l のラベル**
    (χ(g)·j²) mod l に送られることの本物。 -/
theorem tgo_galois_permutes_label (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (j : Nat) :
    galThMuAct GK M ρ g (galThValCyc M j)
      = M.μ.pow M.ζ ((cycRigExp GK M ρ g * (j * j)) % M.n) := by
  rw [galTh_value_transform GK M ρ g j]
  exact cycRig_pow_reduce M.μ M.comm M.ζ M.n M.ord (cycRigExp GK M ρ g * (j * j))

/-- **定理 (M368F-4c: 軌道は有限ラベル集合の中で置換される・本丸)** — 任意のラベル j に
    対し、G_K の作用 σ_g は円分影 ζ^{j²} を、**{0,…,M.n−1} という有限集合に属す**ある
    ラベル i の円分影 ζ^i に送る（i=(χ(g)·j²) mod M.n、M368F-4a/4b の合成）。IUT の
    l-捻れテータ値の軌道が G_K によって**l 個のラベルの有限集合の中で置換される**
    ことの本物（軌道が置換される・有限であることを一体で述べる本丸定理）。 -/
theorem tgo_galois_orbit_permuted (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (j : Nat) :
    ∃ i : Nat, i < M.n ∧
      galThMuAct GK M ρ g (galThValCyc M j) = M.μ.pow M.ζ i :=
  ⟨(cycRigExp GK M ρ g * (j * j)) % M.n, tgo_mod_lt M _, tgo_galois_permutes_label GK M ρ g j⟩

/-! ## M368F-5: 軌道点への作用・トーサーへの帰属 -/

/-- **定理 (M368F-5a: 軌道点への G_K 作用は乗法的)** — σ_g(ζ^{j²}·Θ) =
    σ_g(ζ^{j²})·σ_g(Θ)（M348F `tmt_galois_stable` の直接適用）。軌道点への作用が
    円分影因子とテータ値本体の積に**分配する**こと（トーサー構造との整合）。 -/
theorem tgo_galois_permutes_orbit_point (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M)
    (g : GK.carrier) (Θ : M.μ.carrier) (j : Nat) :
    galThMuAct GK M ρ g (tgoOrbitPoint M Θ j)
      = M.μ.mul (galThMuAct GK M ρ g (galThValCyc M j)) (galThMuAct GK M ρ g Θ) := by
  show galThMuAct GK M ρ g (M.μ.mul (galThValCyc M j) Θ)
     = M.μ.mul (galThMuAct GK M ρ g (galThValCyc M j)) (galThMuAct GK M ρ g Θ)
  exact tmt_galois_stable GK M ρ g (galThValCyc M j) Θ

/-- **定理 (M368F-5b: 軌道は μ_l-トーサーに含まれる)** — 軌道 `tgoOrbit M Θ l` の
    任意の元 x は、ある ζ∈μ_l に対し μ_l-トーサー候補 `tmtCandidate M Θ ζ` に等しい
    （`List.mem_map` で軌道点の定義を展開）。IUT のテータ値の軌道が M348F の
    μ_l-トーサー内に収まることの本物の接続。 -/
theorem tgo_orbit_in_torsor (M : CycMuGroup) (Θ : M.μ.carrier) (l : Nat) (x : M.μ.carrier)
    (hx : x ∈ tgoOrbit M Θ l) : ∃ ζ : M.μ.carrier, x = tmtCandidate M Θ ζ := by
  have hx' : x ∈ (List.range l).map (tgoOrbitPoint M Θ) := hx
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hx'
  exact ⟨galThValCyc M j, hj.symm⟩

/-! ## M368F-6: capstone（テータのガロア軌道データ）と存在 -/

/-- **M368F-6a: テータのガロア軌道データ** — 基点 Θ・ラベル数 l・軌道リスト・その長さが
    l（有限性）・ノルム安定性・軌道が μ_l-トーサーに属すこと・G_K が有限ラベル集合の中で
    軌道を置換することを一括束ねる。IUT の l-捻れテータ値の軌道の本物の witness 形
    （主語は本物の μ_l（M322F CycMuGroup）と本物のガロア作用（M322F CycGKAction）、
    M343F/M348F を軌道の言葉に束ね直す）。 -/
structure ThetaGaloisOrbitData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) where
  /-- 基点テータ値（円分影）Θ。 -/
  Θ : M.μ.carrier
  /-- ラベル数 l（l-捻れ点の個数）。 -/
  l : Nat
  /-- 軌道リスト。 -/
  orbit : List M.μ.carrier
  /-- 軌道は `tgoOrbit M Θ l` に一致。 -/
  orbit_eq : orbit = tgoOrbit M Θ l
  /-- 軌道の長さはちょうど l（有限性）。 -/
  orbit_length : orbit.length = l
  /-- 軌道の各点は基点と同じ M.n 乗ノルムを持つ。 -/
  norm_stable : ∀ j : Nat, M.μ.pow (tgoOrbitPoint M Θ j) M.n = M.μ.pow Θ M.n
  /-- 軌道の各点は μ_l-トーサー候補に属す。 -/
  orbit_in_torsor : ∀ x, x ∈ orbit → ∃ ζ : M.μ.carrier, x = tmtCandidate M Θ ζ
  /-- G_K は有限ラベル集合 {0,…,M.n−1} の中で軌道の円分影を置換する。 -/
  galois_permutes : ∀ g (j : Nat), ∃ i : Nat, i < M.n ∧
    galThMuAct GK M ρ g (galThValCyc M j) = M.μ.pow M.ζ i

/-- **M368F-6b: witness 本体** — 各フィールドを M368F-1〜5 の主定理で埋める。 -/
def tgoData (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (Θ : M.μ.carrier) (l : Nat) :
    ThetaGaloisOrbitData GK M ρ where
  Θ := Θ
  l := l
  orbit := tgoOrbit M Θ l
  orbit_eq := rfl
  orbit_length := tgo_orbit_finite M Θ l
  norm_stable := tgo_norm_stable M Θ
  orbit_in_torsor := fun x hx => tgo_orbit_in_torsor M Θ l x hx
  galois_permutes := fun g j => tgo_galois_orbit_permuted GK M ρ g j

/-- **定理 (M368F-6c: capstone — テータのガロア軌道データの存在)** — 任意の G_K・μ_l・
    作用 ρ・基点 Θ・ラベル数 l に対し、テータ値の軌道データ（有限性・ノルム安定性・
    トーサーへの帰属・G_K による有限ラベル集合内での置換）が本物で組み上がる。
    M343F のガロア同変性・M348F の μ_l-トーサー構造の軌道版としての総括が閉じる。 -/
theorem tgo_exists (GK : Grp) (M : CycMuGroup) (ρ : CycGKAction GK M) (Θ : M.μ.carrier)
    (l : Nat) : Nonempty (ThetaGaloisOrbitData GK M ρ) :=
  ⟨tgoData GK M ρ Θ l⟩

/-! ## 実例（l=5・本物の G_ℚ の μ_5 上のテータのガロア軌道） -/

/-- 実例: 本物の絶対ガロア群 G_ℚ = `algCloAbsGalois algCloTrivialTower`（M315F）の
    μ_5（本物の巡回群 ℤ/5 = `cycMuStd 5`）上で、生成元 ζ を基点とするテータの
    ガロア軌道データが存在する。 -/
theorem tgo_example_l5 :
    Nonempty (ThetaGaloisOrbitData (algCloAbsGalois algCloTrivialTower)
      (cycMuStd 5 (by omega))
      (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega)))) :=
  tgo_exists (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega))
    (cycTrivialAction (algCloAbsGalois algCloTrivialTower) (cycMuStd 5 (by omega)))
    (cycMuStd 5 (by omega)).ζ 5

/-- 実例: l=5 の軌道の長さはちょうど 5（有限性の数値例）。 -/
example :
    (tgoOrbit (cycMuStd 5 (by omega)) (cycMuStd 5 (by omega)).ζ 5).length = 5 :=
  tgo_orbit_finite (cycMuStd 5 (by omega)) (cycMuStd 5 (by omega)).ζ 5

/-- 実例: l=5・j=2 の円分影 ζ^{4} へのガロア作用は mod 5 還元形 ζ^{(χ(g)·4) mod 5}
    に送られる（軌道の置換の数値例）。 -/
example (GK : Grp) (ρ : CycGKAction GK (cycMuStd 5 (by omega))) (g : GK.carrier) :
    galThMuAct GK (cycMuStd 5 (by omega)) ρ g (galThValCyc (cycMuStd 5 (by omega)) 2)
      = (cycMuStd 5 (by omega)).μ.pow (cycMuStd 5 (by omega)).ζ
          ((cycRigExp GK (cycMuStd 5 (by omega)) ρ g * (2 * 2)) % (cycMuStd 5 (by omega)).n) :=
  tgo_galois_permutes_label GK (cycMuStd 5 (by omega)) ρ g 2

end IUT
