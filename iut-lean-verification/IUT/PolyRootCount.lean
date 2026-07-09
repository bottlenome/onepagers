/-
  IUT/PolyRootCount.lean — A3 円分塔 Wave1/R1（体上の多項式: 因子定理と
  「相異なる根の個数 ≤ 次数」の完全証明）

  ── 分類 **[実]**（本物の先行建設(b)。骨格でなく本物の一般体論・sorry 皆無・
  新規 Classical.choice 皆無）。

  **complete_pct 影響**: 柱A「実 Galois 理論」の本物の先行建設。A3 円分塔
  設計書（audit/A3-cyclotomic-tower-plan.md）R1 の土台。制限準同型 res_n
  （自己同型が ≤n 個の根を置換）を語るための一般補題「体 K 上の非零多項式
  の相異なる根は次数以下」を、既存の体上多項式除法（M268F
  `field_division_exists`・整域性 `mul_eq_zero_left268`・頂点係数
  `psMul_g_top_coeff268`）と評価準同型（M274F `evalSum`/`evalHom_mul`/
  `evalHom_add`/`evalHom_stable`）の上で本物に証明する。円分に非依存の
  一般体論であり、A1 エンジン非依存で今すぐ実装可（後続の分裂体・分離性の
  柱A資産としても再利用可能）。complete_pct は本モジュール単独では未確定
  （A3 の R1 土台・E := gefNF268 への適用は A1 Wave2+ 到着後）。

  * prcXsub / prc_Xsub_bounded / prc_Xsub_lead / prc_eval_Xsub —
    一次因子 X − r（= psSingle 1 1 + psC (−r)）とその有界性・先頭係数・
    評価値（ev_α(X−r) = α − r）
  * prcIsRoot — 根の定義（評価準同型 evalSum で p(r) = 0、任意の有界打切）
  * prc_root_of_eval — 一つの有界点での p(r)=0 から prcIsRoot（打切安定性）
  * prc_one_ne_zero — 非零元の存在から 1 ≠ 0（自明環でないこと）
  * **prc_root_factor（因子定理）** — r が根 ⟹ (X−r) が因子:
    field_division_exists で p を (X−r) で割り、剰余が定数、根で剰余 = p(r)
    = 0（evalHom_mul で ev(X−r)(r) = 0 を使う）、余因子の次数は頂点係数
    （psMul_g_top_coeff268）＋整域性で一段下がる
  * **prc_roots_le_degree（本丸）** — 相異なる根のリストは次数以下:
    次数 n の帰納。根を一つ剥がして (X−r)·q へ分解、余因子 q は次数 n−1・
    先頭係数非零、残る相異なる根 r'（≠r）は整域性（(r'−r)≠0）で q の根

  正直な限定（§4 準拠・消さない）:
   - 多項式は有限台の係数列（PS）として扱い、次数は明示上界パラメータで
     受け取る（有限台性からの次数抽出は行わない）。
   - 根の重複度・分裂体（全根の存在）は本層に含めない（除法と個数上界の
     みを扱う土台）。
   - 体 K の非自明性（1 ≠ 0）は必要な仮説として明示的に受け取るか、
     先頭係数非零から導く（自明環では (X−r) が一次でなく主張が崩れるため
     本質的に必要な honest 前提）。

  全て選択公理不使用（新規 Classical.choice を証明本体に導入しない）。
  禁止タクティク不使用。サブエージェント新規部品（共有ファイル不更新）。
-/
import IUT.PolyFieldDivision
import IUT.SimpleExtension
import IUT.EvaluationHom

namespace IUT

/-! ## 一次因子 X − r -/

/-- **一次因子** X − r = 1·X + (−r)（psSingle 1 1 と定数 −r の和）。 -/
def prcXsub (K : Field268) (r : K.ring.carrier) : PS K.ring :=
  psAdd K.ring (psSingle K.ring K.ring.one 1) (psC K.ring (K.ring.neg r))

/-- X − r は 2 で有界（次数 1）。 -/
theorem prc_Xsub_bounded (K : Field268) (r : K.ring.carrier) :
    IsPolyBounded K.ring (prcXsub K r) 2 := by
  intro j hj
  show K.ring.add (psSingle K.ring K.ring.one 1 j) (psC K.ring (K.ring.neg r) j)
    = K.ring.zero
  rw [show psSingle K.ring K.ring.one 1 j = K.ring.zero from if_neg (by omega),
    show psC K.ring (K.ring.neg r) j = K.ring.zero from if_neg (by omega),
    K.ring.zero_add]

/-- X − r の先頭係数（1 次）は 1。 -/
theorem prc_Xsub_lead (K : Field268) (r : K.ring.carrier) :
    prcXsub K r 1 = K.ring.one := by
  show K.ring.add (psSingle K.ring K.ring.one 1 1) (psC K.ring (K.ring.neg r) 1)
    = K.ring.one
  rw [show psSingle K.ring K.ring.one 1 1 = K.ring.one from if_pos rfl,
    show psC K.ring (K.ring.neg r) 1 = K.ring.zero from if_neg (by omega),
    CRing.add_zero K.ring]

/-- **評価値** ev_α(X − r) = α − r（恒等埋め込みでの評価、打切 2）。 -/
theorem prc_eval_Xsub (K : Field268) (r α : K.ring.carrier) :
    evalSum (evalHomId K.ring) α (prcXsub K r) 2
      = K.ring.add α (K.ring.neg r) := by
  rw [evalSum_id]
  show K.ring.add (K.ring.add K.ring.zero
      (K.ring.mul (prcXsub K r 0) (rpow K.ring α 0)))
      (K.ring.mul (prcXsub K r 1) (rpow K.ring α 1))
    = K.ring.add α (K.ring.neg r)
  have h0 : prcXsub K r 0 = K.ring.neg r := by
    show K.ring.add (psSingle K.ring K.ring.one 1 0) (psC K.ring (K.ring.neg r) 0)
      = K.ring.neg r
    rw [show psSingle K.ring K.ring.one 1 0 = K.ring.zero from if_neg (by omega),
      show psC K.ring (K.ring.neg r) 0 = K.ring.neg r from if_pos rfl,
      K.ring.zero_add]
  have h1 : prcXsub K r 1 = K.ring.one := prc_Xsub_lead K r
  rw [h0, h1]
  have e0 : rpow K.ring α 0 = K.ring.one := rfl
  have e1 : rpow K.ring α 1 = α := K.ring.one_mul α
  rw [e0, e1, CRing.mul_one K.ring (K.ring.neg r), K.ring.one_mul α, K.ring.zero_add]
  exact K.ring.add_comm (K.ring.neg r) α

/-! ## 根の定義と基本補題 -/

/-- **根の定義** — p(r) = 0（恒等埋め込みでの評価が任意の有界打切で 0）。 -/
def prcIsRoot (K : Field268) (p : PS K.ring) (r : K.ring.carrier) : Prop :=
  ∀ N, IsPolyBounded K.ring p N → evalSum (evalHomId K.ring) r p N = K.ring.zero

/-- **一点から根へ** — ある有界点 N₀ で p(r) = 0 なら prcIsRoot（打切安定性
    evalHom_stable で任意の有界打切に伝播する）。 -/
theorem prc_root_of_eval (K : Field268) (p : PS K.ring) (r : K.ring.carrier)
    (N₀ : Nat) (hb : IsPolyBounded K.ring p N₀)
    (heval : evalSum (evalHomId K.ring) r p N₀ = K.ring.zero) :
    prcIsRoot K p r := by
  intro M hM
  cases Nat.le_total N₀ M with
  | inl h =>
    rw [evalHom_stable (evalHomId K.ring) r p N₀ hb M h]
    exact heval
  | inr h =>
    have e := evalHom_stable (evalHomId K.ring) r p M hM N₀ h
    rw [← e]
    exact heval

/-- **非自明性** — 非零元 a があれば 1 ≠ 0（1 = 0 なら a = 1·a = 0·a = 0）。 -/
theorem prc_one_ne_zero (K : Field268) {a : K.ring.carrier}
    (ha : a ≠ K.ring.zero) : K.ring.one ≠ K.ring.zero := by
  intro h
  apply ha
  have e : a = K.ring.mul K.ring.one a := (K.ring.one_mul a).symm
  rw [h, CRing.zero_mul K.ring a] at e
  exact e

/-! ## 因子定理 -/

/-- **因子定理** — p が N+1 有界（次数 ≤ N）で r が p の根なら、p = (X−r)·q
    となる余因子 q（N 有界、次数 ≤ N−1）が存在する。field_division_exists で
    p を (X−r) で割り、商 q・剰余 rem（定数）を得る。根で rem = p(r) = 0
    （evalHom_mul と ev(X−r)(r) = 0）、余因子 q の次数上界は頂点係数
    （psMul_g_top_coeff268）＋整域性で N まで締める。 -/
theorem prc_root_factor (K : Field268) (p : PS K.ring) (N : Nat)
    (hK1 : K.ring.one ≠ K.ring.zero)
    (hb : IsPolyBounded K.ring p (N + 1)) (r : K.ring.carrier)
    (hr : prcIsRoot K p r) :
    ∃ q, IsPolyBounded K.ring q N ∧ p = psMul K.ring (prcXsub K r) q := by
  have hg2 : IsPolyBounded K.ring (prcXsub K r) 2 := prc_Xsub_bounded K r
  have hglead : prcXsub K r 1 ≠ K.ring.zero := by
    rw [prc_Xsub_lead K r]; exact hK1
  obtain ⟨q, rem, hq, hrem, heq⟩ :=
    field_division_exists K.ring K.invf K.mul_inv_cancel (prcXsub K r) 1 hg2 hglead
      N p hb
  -- p = (q·(X−r)) + rem （成分ごと）
  have hpfun : p = psAdd K.ring (psMul K.ring q (prcXsub K r)) rem := funext heq
  -- 根で rem の定数項 = 0
  have hev0 : evalSum (evalHomId K.ring) r p (N + 4) = K.ring.zero :=
    hr (N + 4) (fun j hj => hb j (by omega))
  have hmul : evalSum (evalHomId K.ring) r (psMul K.ring q (prcXsub K r)) (N + 4)
      = K.ring.mul (evalSum (evalHomId K.ring) r q (N + 1))
          (evalSum (evalHomId K.ring) r (prcXsub K r) 2) :=
    evalHom_mul (evalHomId K.ring) r q (prcXsub K r) (N + 1) 2 hq hg2
  have hgval : evalSum (evalHomId K.ring) r (prcXsub K r) 2 = K.ring.zero := by
    rw [prc_eval_Xsub K r r]; exact K.ring.add_neg r
  have hqgzero : evalSum (evalHomId K.ring) r (psMul K.ring q (prcXsub K r)) (N + 4)
      = K.ring.zero := by
    rw [hmul, hgval]; exact CRing.mul_zero K.ring _
  have hremeval : evalSum (evalHomId K.ring) r rem (N + 4) = rem 0 := by
    rw [evalHom_stable (evalHomId K.ring) r rem 1 hrem (N + 4) (by omega), evalSum_id]
    show K.ring.add K.ring.zero (K.ring.mul (rem 0) (rpow K.ring r 0)) = rem 0
    rw [show rpow K.ring r 0 = K.ring.one from rfl, CRing.mul_one K.ring (rem 0),
      K.ring.zero_add]
  have hrem0 : rem 0 = K.ring.zero := by
    have hkey : evalSum (evalHomId K.ring) r p (N + 4)
        = K.ring.add (evalSum (evalHomId K.ring) r (psMul K.ring q (prcXsub K r)) (N + 4))
            (evalSum (evalHomId K.ring) r rem (N + 4)) := by
      rw [hpfun]
      exact evalHom_add (evalHomId K.ring) r (psMul K.ring q (prcXsub K r)) rem (N + 4)
    rw [hqgzero, hremeval, K.ring.zero_add, hev0] at hkey
    exact hkey.symm
  have hremz : ∀ j, rem j = K.ring.zero := by
    intro j
    cases Nat.eq_zero_or_pos j with
    | inl hj0 => rw [hj0]; exact hrem0
    | inr hjpos => exact hrem j hjpos
  -- 余因子 q の頂点を締める: q N = 0
  have hqN : q N = K.ring.zero := by
    have htop : psMul K.ring q (prcXsub K r) (N + 1)
        = K.ring.mul (q N) (prcXsub K r 1) :=
      psMul_g_top_coeff268 K.ring (prcXsub K r) 1 hg2 q N hq
    have hz : K.ring.mul (q N) (prcXsub K r 1) = K.ring.zero := by
      rw [← htop]
      have h2 : psMul K.ring q (prcXsub K r) (N + 1) = p (N + 1) := by
        rw [heq (N + 1)]
        show psMul K.ring q (prcXsub K r) (N + 1)
            = K.ring.add (psMul K.ring q (prcXsub K r) (N + 1)) (rem (N + 1))
        rw [hremz (N + 1), CRing.add_zero K.ring]
      rw [h2]
      exact hb (N + 1) (by omega)
    rw [prc_Xsub_lead K r, CRing.mul_one K.ring (q N)] at hz
    exact hz
  refine ⟨q, ?_, ?_⟩
  · intro j hj
    cases Nat.lt_or_ge j (N + 1) with
    | inl hlt => rw [show j = N from by omega]; exact hqN
    | inr hge => exact hq j hge
  · funext j
    rw [heq j]
    show K.ring.add (psMul K.ring q (prcXsub K r) j) (rem j)
      = psMul K.ring (prcXsub K r) q j
    rw [hremz j, CRing.add_zero K.ring]
    exact congrFun ((psRing K.ring).mul_comm q (prcXsub K r)) j

/-! ## 相異なる根の判定 -/

/-- **相異なる（Nodup 相当）** — 各要素が後続の全要素と異なる（自前 pairwise≠、
    core の List.Nodup に非依存）。 -/
def prcDistinct {α : Type} : List α → Prop
  | [] => True
  | r :: S => (∀ x, x ∈ S → x ≠ r) ∧ prcDistinct S

/-! ## 本丸: 根の個数 ≤ 次数 -/

/-- **本丸（根の個数 ≤ 次数）** — 体 K 上、p が n+1 有界（次数 ≤ n）で先頭係数
    p n ≠ 0（非零多項式）なら、p の相異なる根のリスト S は length ≤ n。
    n の帰納: 根 r を一つ剥がして p = (X−r)·q へ分解（prc_root_factor）、
    余因子 q は次数 ≤ n−1・先頭係数 q(n−1) ≠ 0、S の残りの相異なる根 r'（≠r）
    は整域性（(r'−r) ≠ 0 かつ ev(p)(r')=ev(X−r)(r')·ev(q)(r')=0）で q の根。 -/
theorem prc_roots_le_degree (K : Field268) :
    ∀ (n : Nat) (p : PS K.ring), IsPolyBounded K.ring p (n + 1) →
      p n ≠ K.ring.zero → ∀ (S : List K.ring.carrier),
      (∀ r ∈ S, prcIsRoot K p r) → prcDistinct S → S.length ≤ n := by
  intro n
  induction n with
  | zero =>
    intro p hb hlead S hS hd
    cases S with
    | nil => exact Nat.le_refl 0
    | cons r S' =>
      exfalso
      have hroot : prcIsRoot K p r := hS r List.mem_cons_self
      have hev : evalSum (evalHomId K.ring) r p 1 = K.ring.zero := hroot 1 hb
      have hp0 : evalSum (evalHomId K.ring) r p 1 = p 0 := by
        rw [evalSum_id]
        show K.ring.add K.ring.zero (K.ring.mul (p 0) (rpow K.ring r 0)) = p 0
        rw [show rpow K.ring r 0 = K.ring.one from rfl, CRing.mul_one K.ring (p 0),
          K.ring.zero_add]
      rw [hp0] at hev
      exact hlead hev
  | succ n ih =>
    intro p hb hlead S hS hd
    cases S with
    | nil => exact Nat.zero_le (n + 1)
    | cons r S' =>
      have hK1 : K.ring.one ≠ K.ring.zero := prc_one_ne_zero K hlead
      have hroot : prcIsRoot K p r := hS r List.mem_cons_self
      obtain ⟨q, hq, hpq⟩ := prc_root_factor K p (n + 1) hK1 hb r hroot
      -- 余因子の先頭係数 q n ≠ 0
      have hqlead : q n ≠ K.ring.zero := by
        have htop : psMul K.ring q (prcXsub K r) (n + 1)
            = K.ring.mul (q n) (prcXsub K r 1) :=
          psMul_g_top_coeff268 K.ring (prcXsub K r) 1 (prc_Xsub_bounded K r) q n hq
        have hcomm : psMul K.ring (prcXsub K r) q = psMul K.ring q (prcXsub K r) :=
          (psRing K.ring).mul_comm (prcXsub K r) q
        have hpg : p (n + 1) = q n := by
          rw [hpq]
          show psMul K.ring (prcXsub K r) q (n + 1) = q n
          rw [congrFun hcomm (n + 1), htop,
            prc_Xsub_lead K r, CRing.mul_one K.ring (q n)]
        rw [← hpg]; exact hlead
      -- 残りの根 r' (≠ r) は q の根
      have hSq : ∀ x ∈ S', prcIsRoot K q x := by
        intro x hx
        have hxr : x ≠ r := hd.1 x hx
        have hxroot : prcIsRoot K p x := hS x (List.mem_cons_of_mem r hx)
        have hpev : evalSum (evalHomId K.ring) x p (2 + (n + 1) + 1) = K.ring.zero :=
          hxroot (2 + (n + 1) + 1) (fun j hj => hb j (by omega))
        have hmulx : evalSum (evalHomId K.ring) x (psMul K.ring (prcXsub K r) q)
              (2 + (n + 1) + 1)
            = K.ring.mul (evalSum (evalHomId K.ring) x (prcXsub K r) 2)
                (evalSum (evalHomId K.ring) x q (n + 1)) :=
          evalHom_mul (evalHomId K.ring) x (prcXsub K r) q 2 (n + 1)
            (prc_Xsub_bounded K r) hq
        have hgx : evalSum (evalHomId K.ring) x (prcXsub K r) 2
            = K.ring.add x (K.ring.neg r) := prc_eval_Xsub K r x
        have hzero : K.ring.mul (K.ring.add x (K.ring.neg r))
            (evalSum (evalHomId K.ring) x q (n + 1)) = K.ring.zero := by
          rw [← hgx, ← hmulx, ← hpq]; exact hpev
        have hne : K.ring.add x (K.ring.neg r) ≠ K.ring.zero := by
          intro habs
          exact hxr (CRing.eq_of_sub_eq_zero K.ring habs)
        have hcomm : K.ring.mul (evalSum (evalHomId K.ring) x q (n + 1))
            (K.ring.add x (K.ring.neg r)) = K.ring.zero := by
          rw [K.ring.mul_comm]; exact hzero
        have hqx : evalSum (evalHomId K.ring) x q (n + 1) = K.ring.zero :=
          mul_eq_zero_left268 K.ring K.invf K.mul_inv_cancel hne hcomm
        exact prc_root_of_eval K q x (n + 1) hq hqx
      have hlen : S'.length ≤ n := ih q hq hqlead S' hSq hd.2
      show S'.length + 1 ≤ n + 1
      omega

end IUT
