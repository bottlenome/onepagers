/-
  IUT/CyclotomeRecoveryLimit.lean — CRL（柱A6 復元円分体の副有限極限 T̂ と実 ℤ₃(1) の
  G-同変明示同一視 Ξ）

  ── 主要成果の分類: **[実／昇格(a)＋本物建設(b)]**（骨格・模型・代理でなく、実非自明
     円分指標 χ=`cgarRecChar`（σ₂→2≠1・cgar で本物に構成）から mono-anabelian に
     復元した円分体の**塔** `zmod (3^{n+1})`（χ 捻り作用つき）を、割り切り遷移
     `zmodTrans` で本物の逆系 `crlSystem` に組み、その逆極限 `crlLimit = T̂`
     （＝復元側 ℤ₃(1)）を**本物に先行建設**する。さらに実 μ 塔の逆極限
     `tmzLimit = T = ℤ₃(1)`（tmz で本物に構成）との間の、成分ごと `cidIso`（M443F 明示
     同型・cmuMap）を貼り合わせた**G-同変両側逆つき明示同一視 `crlIso : T̂ ≅ T`**
     と逆写像 `crlInv` を、遷移整合 `crl_char_compat`/`crl_iso_compat`/`crl_inv_compat`
     を経て完全証明する。復元側の極限対象 T̂ と極限同一視 Ξ は柱A のどこにも存在
     しなかった——crr は各 ℓ 固定の有限切片で止まる。）

  **complete_pct 影響**: A6（mono-anabelian 復元）——crr の正直な限定 (iii)
  「完全な副有限・K̄ レベルは後続（A6 上限 0.6）」の**副有限（極限）部分を正面 discharge**
  する。すなわち crr が各 ℓ 固定で構成した「復元 μ̂ ≅ 実 μ_{3^ℓ} の 1 本の iso」を、
  復元側の**極限対象 T̂ = `crlLimit`** と実 T=ℤ₃(1) の**極限 G-同変同一視 Ξ=`crlIso`**
  へ昇格する（(G2) の discharge）。設計見込み A6 0.55 → 0.62（最終値は独立監査確定・
  過大主張しない）。本ファイル単体では complete_pct は独立監査で反映。

  内容（設計 audit/A6-cyclotome-recovery-canonicity-detail-2026-07-11.md §3.1・CRL-0〜3）:
   * `crlG`/`crlT`/`crl_t_self`/`crl_t_comp`/`crlSystem`/`crlLimit` — 復元側逆系と極限 T̂。CRL-0。
   * `crl_char_compat` — ★復元指標の遷移整合（cli_char_restr＋Int/Nat cast 簿記）。CRL-1。
   * `crlActHom`/`crl_act_one`/`crl_act_mul`/`CrlGModule`/`crlGModule` — T̂ 上の復元 G 作用。CRL-2。
   * `crl_iso_compat`/`crl_inv_compat`/`crlIso`/`crlInv`/`crl_iso_leftinv`/`crl_iso_rightinv`/
     `crl_iso_equivariant` — ★明示同一視 Ξ とその両側逆・G-同変性。CRL-3。

  正直な限定（§4.1 規約により消さない・弱めない・sorry で埋めない）:
   (i)   **mono-theta 円分剛性（[EtTh]）は依然 0**——本モジュールは ℤ₃^× 不定性を殺さない。
         「復元の同一視空間がちょうど実 ℤ₃^× の torsor」の特定は後続 CRC（本ファイルは Ξ の
         建設のみ）。不定性を消すテータ環境は柱E/D 後続（CHARACTERIZE, not KILL）。
   (ii)  **χ を実 π₁^ét の位相連続指標として抽出する本丸は未**——復元入力 χ は依然
         `cgarAct`（実体自己同型の制限）由来。crr 限定 (ii) を弱めず継承。
   (iii) **幾何側は K̄ の μ でも π₁ の幾何的 cyclotome でもない**——μ 塔は各段別々の実円分体
         ℚ(ζ_{3^{n+1}}) に住む（tmz 限定 (ii)(5) 継承）。実数体上の完全 mono-anabelian
         復元（AbsTopIII の実主語・体/環の復元）は後続。
   (iv)  **p = 3・G = Gal(ℚ(ζ_{3^∞})/ℚ) 固定**（G_ℚ の可解商・実 G_K/G_{K_v} でない）。
   (v)   crr の「A6 上限 0.6」正直申告は**消さない**。ただしその根拠のうち「完全な副有限は
         後続」を本ステップが discharge するため、本モジュールは自身の限定として
         「**A6 ≤ 0.65（K̄/幾何 cyclotome・π₁ 連続 χ が未のあいだ）**」を新たに宣言する
         （既存 0.6 申告の削除・弱化ではなく並置＋更新宣言・監査確定は独立）。
   (vi)  crr/tmz/tme/tmi/cra の既存正直申告は一切消さない・弱めない。並置＋昇格のみ。

  全て選択公理不使用（新規 `Classical.choice` を証明本体に導入しない・propext/Quot.sound
  のみ）。禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/
  nth_rewrite/field_simp）不使用。3^ℓ は omega 不可（`zpu_pow_pos`/`zpu_pow_dvd` 再利用）。
  新規イディオム 0（極限貼り合わせ=tmz、cast 簿記=crr/cli、明示同型消費=cid の既確立
  イディオムのみ）。新規ファイル 1 個のみ（共有ファイル IUT.lean/build.sh/dashboard/graph/
  tools は不更新・親が統合）。prefix `crl`。
-/
import IUT.CyclotomeRecoveryReal
import IUT.TateModuleZ3
import IUT.CyclotomicLimitIso

namespace IUT

/-! ## CRL-0: 復元側逆系と極限 T̂ = crlLimit -/

/-- **CRL-0a: 復元側の各段** `crlG n = ℤ/3^{n+1}`（χ 捻り復元円分体の台・添字を
    ctlGal n = Gal(ℚ(ζ_{3^{n+1}})/ℚ) と合わせる）。 -/
def crlG (n : Nat) : Grp := zmod (3 ^ (n + 1))

/-- **CRL-0b: 遷移射** — ℤ/3^{j+1} → ℤ/3^{i+1}（i ≤ j・割り切り剰余 `zmodTrans`）。 -/
def crlT {i j : Nat} (h : i ≤ j) : Hom (crlG j) (crlG i) :=
  zmodTrans (zpu_pow_dvd (Nat.succ_le_succ h))

/-- **CRL-0c: 恒等保存**（`zmodTrans` は自層への遷移で代表を保つ）。 -/
theorem crl_t_self (i : Nat) (y : (crlG i).carrier) : (crlT (Nat.le_refl i)).map y = y := by
  induction y using Quot.ind
  rfl

/-- **CRL-0d: 推移性**（`zmodTrans` の合成は合成の `zmodTrans`）。 -/
theorem crl_t_comp {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) (x : (crlG k).carrier) :
    (crlT hij).map ((crlT hjk).map x) = (crlT (Nat.le_trans hij hjk)).map x := by
  induction x using Quot.ind
  rfl

/-- **CRL-0e: 復元側逆系**（`natSystem` 経由・Nat 添字・(≤)）。 -/
@[reducible] def crlSystem : InverseSystem := natSystem crlG crlT crl_t_self crl_t_comp

/-- **CRL-0f: ★逆極限 T̂ = crlLimit = lim ℤ/3^{n+1}**（χ 捻り復元塔の逆極限・復元側 ℤ₃(1)）。 -/
def crlLimit : Grp := limitGrp crlSystem

/-! ## CRL-1: ★復元指標の遷移整合（本ファイルの貼り合わせ核・実新規） -/

/-- **CRL-1（★復元指標の塔整合・cast 簿記）** — 上段の復元円分指標 χ_{j+1}(s_j) を遷移
    `crlT` で落とすと下段 χ_{i+1}(s_i) に一致する。χ の値は `cgarRecChar.chi σ =
    Quot.mk (cycRigExp σ : Int)`（cgar/M322F 定義）であり、その内実は cli 単数側指標
    `cliChar.val`（＝ ctr_charG・cgar_exp_eq の defeq）。cli の遷移整合正方形
    `cli_char_restr`（＋ s.property で Gal 側整合を移送）と `zpsT` の単発 mod 還元で
    「χ_i(s_i) = χ_j(s_j) % 3^{i+1}」を得、`cycRig_nat_mod_dvd`＋`Quot.sound` で ℤ/3^{i+1}
    の等式に閉じる（crr_nat_mod_toNat 系の Int/Nat cast 簿記）。 -/
theorem crl_char_compat {i j : Nat} (h : i ≤ j) (s : ctlProfinite.carrier) :
    (crlT h).map ((cgarRecChar (j + 1) (by omega)).chi (s.val j))
      = (cgarRecChar (i + 1) (by omega)).chi (s.val i) := by
  have key0 : (cliChar i).map (s.val i) = (zpsT h).map ((cliChar j).map (s.val j)) :=
    (congrArg (cliChar i).map (s.property h).symm).trans (cli_char_restr h (s.val j))
  have key : ((cliChar i).map (s.val i)).val
      = ((cliChar j).map (s.val j)).val % 3 ^ (i + 1) := congrArg Subtype.val key0
  show Quot.mk (modCong (3 ^ (i + 1))).rel ((((cliChar j).map (s.val j)).val : Nat) : Int)
     = Quot.mk (modCong (3 ^ (i + 1))).rel ((((cliChar i).map (s.val i)).val : Nat) : Int)
  apply Quot.sound
  refine cycRig_nat_mod_dvd (3 ^ (i + 1)) _ _ ?_
  rw [Nat.mod_eq_of_lt ((cliChar i).map (s.val i)).property.1]
  exact key.symm

/-! ## CRL-2: ★T̂ 上の復元 G 作用（成分ごと χ 捻り・tmzActHom の復元側鏡像） -/

/-- **CRL-2a: 遷移射は χ 捻り（zmodMul）を保つ**（`cycRec_zmodTrans_mul` の crlT 特化）。 -/
theorem crl_t_zmodMul {i j : Nat} (h : i ≤ j) (x y : (crlG j).carrier) :
    (crlT h).map (zmodMul (3 ^ (j + 1)) x y)
      = zmodMul (3 ^ (i + 1)) ((crlT h).map x) ((crlT h).map y) :=
  cycRec_zmodTrans_mul (zpu_pow_dvd (Nat.succ_le_succ h)) x y

/-- **CRL-2b: ★G = Gal(ℚ(ζ_{3^∞})/ℚ) の T̂ への復元作用** — s ∈ ctlProfinite に対し、
    成分ごと χ 捻り x ↦ χ_{n+1}(s_n)·x（zmodMul）を施す群自己準同型 T̂ → T̂。整合性は
    `crl_t_zmodMul`＋`crl_char_compat`＋s/y の整合族性、map_mul は成分ごと分配
    `crr_zmodMul_add`。tmzActHom の復元側鏡像。 -/
def crlActHom (s : ctlProfinite.carrier) : Hom crlLimit crlLimit where
  map := fun y => ⟨fun n =>
      zmodMul (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi (s.val n)) (y.val n), by
    intro a b hab
    show (crlT hab).map
          (zmodMul (3 ^ (b + 1)) ((cgarRecChar (b + 1) (by omega)).chi (s.val b)) (y.val b))
       = zmodMul (3 ^ (a + 1)) ((cgarRecChar (a + 1) (by omega)).chi (s.val a)) (y.val a)
    rw [crl_t_zmodMul hab, crl_char_compat hab s, y.property hab]⟩
  map_mul := fun y z => by
    apply Subtype.ext
    funext n
    show zmodMul (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi (s.val n))
          ((crlG n).mul (y.val n) (z.val n))
       = (crlG n).mul
          (zmodMul (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi (s.val n)) (y.val n))
          (zmodMul (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi (s.val n)) (z.val n))
    exact crr_zmodMul_add (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi (s.val n))
      (y.val n) (z.val n)

/-- **CRL-2c: 単位則** σ_1 = id（`cgarRecChar.chi_one` 成分ごと＋`zmodOne_mul`）。 -/
theorem crl_act_one (y : crlLimit.carrier) : (crlActHom ctlProfinite.one).map y = y := by
  apply Subtype.ext
  funext n
  show zmodMul (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi (ctlProfinite.one.val n))
        (y.val n) = y.val n
  have hchi : (cgarRecChar (n + 1) (by omega)).chi (ctlProfinite.one.val n)
      = Quot.mk (modCong (3 ^ (n + 1))).rel 1 := (cgarRecChar (n + 1) (by omega)).chi_one
  rw [hchi]
  exact zmodOne_mul (3 ^ (n + 1)) (y.val n)

/-- **CRL-2d: 合成則** σ_{s·t} = σ_s∘σ_t（`cgarRecChar.chi_hom` 成分ごと＋`zmodMul_assoc`）。 -/
theorem crl_act_mul (s t : ctlProfinite.carrier) (y : crlLimit.carrier) :
    (crlActHom (ctlProfinite.mul s t)).map y = (crlActHom s).map ((crlActHom t).map y) := by
  apply Subtype.ext
  funext n
  show zmodMul (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi ((ctlProfinite.mul s t).val n))
        (y.val n)
     = zmodMul (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi (s.val n))
        (zmodMul (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi (t.val n)) (y.val n))
  have hh : (cgarRecChar (n + 1) (by omega)).chi ((ctlProfinite.mul s t).val n)
      = zmodMul (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi (s.val n))
          ((cgarRecChar (n + 1) (by omega)).chi (t.val n)) :=
    (cgarRecChar (n + 1) (by omega)).chi_hom (s.val n) (t.val n)
  rw [hh, zmodMul_assoc]

/-- **CRL-2e: T̂ の実 G-加群構造**（TmzGModule の復元側対応物）。 -/
structure CrlGModule where
  /-- G = Gal(ℚ(ζ_{3^∞})/ℚ) の各元 s の T̂ への群自己準同型。 -/
  act : ctlProfinite.carrier → Hom crlLimit crlLimit
  /-- 単位元の作用は恒等。 -/
  act_one : ∀ y, (act ctlProfinite.one).map y = y
  /-- 合成則。 -/
  act_mul : ∀ s t y, (act (ctlProfinite.mul s t)).map y = (act s).map ((act t).map y)

/-- **CRL-2f: witness**（全フィールド既証明の純レコード）。 -/
def crlGModule : CrlGModule where
  act := crlActHom
  act_one := crl_act_one
  act_mul := crl_act_mul

/-! ## CRL-3: ★明示同一視 Ξ = crlIso : T̂ ≅ T とその両側逆・G-同変性 -/

/-- **CRL-3a-aux: Ξ 遷移整合の指数簿記** — ((a%3^{j+1}).toNat%3^{j+1})%3^{i+1}
    = (a%3^{i+1}).toNat%3^{i+1}（Int/Nat 剰余のネスト・`Int.emod_emod_of_dvd`）。 -/
theorem crl_iso_exp {i j : Nat} (h : i ≤ j) (a : Int) :
    ((a % ((3 ^ (j + 1) : Nat) : Int)).toNat % 3 ^ (j + 1)) % 3 ^ (i + 1)
      = (a % ((3 ^ (i + 1) : Nat) : Int)).toNat % 3 ^ (i + 1) := by
  have hMpos : (0 : Int) < ((3 ^ (j + 1) : Nat) : Int) := by
    have := zpu_pow_pos (j + 1); omega
  have hmpos : (0 : Int) < ((3 ^ (i + 1) : Nat) : Int) := by
    have := zpu_pow_pos (i + 1); omega
  have hgeM : 0 ≤ a % ((3 ^ (j + 1) : Nat) : Int) := Int.emod_nonneg a (by omega)
  have hltM : a % ((3 ^ (j + 1) : Nat) : Int) < ((3 ^ (j + 1) : Nat) : Int) :=
    Int.emod_lt_of_pos a hMpos
  have htoNatM : ((a % ((3 ^ (j + 1) : Nat) : Int)).toNat : Int)
      = a % ((3 ^ (j + 1) : Nat) : Int) := Int.toNat_of_nonneg hgeM
  have hbound : (a % ((3 ^ (j + 1) : Nat) : Int)).toNat < 3 ^ (j + 1) := by omega
  rw [Nat.mod_eq_of_lt hbound]
  have hgem : 0 ≤ a % ((3 ^ (i + 1) : Nat) : Int) := Int.emod_nonneg a (by omega)
  have hltm : a % ((3 ^ (i + 1) : Nat) : Int) < ((3 ^ (i + 1) : Nat) : Int) :=
    Int.emod_lt_of_pos a hmpos
  have hboundm : (a % ((3 ^ (i + 1) : Nat) : Int)).toNat < 3 ^ (i + 1) := by omega
  rw [Nat.mod_eq_of_lt hboundm,
      crr_nat_mod_toNat (a % ((3 ^ (j + 1) : Nat) : Int)).toNat (3 ^ (i + 1)), htoNatM,
      Int.emod_emod_of_dvd a (Int.ofNat_dvd.mpr (zpu_pow_dvd (Nat.succ_le_succ h)))]

/-- **CRL-3a: Ξ の遷移整合（順方向・cast 簿記）** — 成分ごとの明示同型
    `cmuMap (cycMuStd (3^{j+1})) (cmrMu (j+1))`（＝ crrIso=cidIso の map）が、遷移
    `crlT`（復元側）と `tmzT`（実側）の四角を可換にする。両辺を `cycMuStd.log`＝
    (·%3^{j+1}).toNat と `tmz_find_pow`/`tmz_pow_mod` で指数へ落とし、Int/Nat 剰余の
    ネスト簿記（`Int.emod_emod_of_dvd`）で合流する。 -/
theorem crl_iso_compat {i j : Nat} (h : i ≤ j) (x : (crlG j).carrier) :
    (tmzT h).map
        (cmuMap (cycMuStd (3 ^ (j + 1)) (zpu_pow_pos (j + 1))) (cmrMu (j + 1) (by omega)) x)
      = cmuMap (cycMuStd (3 ^ (i + 1)) (zpu_pow_pos (i + 1))) (cmrMu (i + 1) (by omega))
          ((crlT h).map x) := by
  induction x using Quot.ind
  rename_i a
  show (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
        (ctmFind (j + 1) (by omega)
          ((cmrGrp (j + 1) (by omega)).pow (cmrZeta (j + 1) (by omega))
            ((a % ((3 ^ (j + 1) : Nat) : Int)).toNat)).val)
     = (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
        ((a % ((3 ^ (i + 1) : Nat) : Int)).toNat)
  rw [cmr_pow_zeta (j + 1) (by omega) ((a % ((3 ^ (j + 1) : Nat) : Int)).toNat),
      tmz_find_pow (j + 1) (by omega) ((a % ((3 ^ (j + 1) : Nat) : Int)).toNat),
      tmz_pow_mod (i + 1) (by omega)
        ((a % ((3 ^ (j + 1) : Nat) : Int)).toNat % 3 ^ (j + 1)),
      tmz_pow_mod (i + 1) (by omega) ((a % ((3 ^ (i + 1) : Nat) : Int)).toNat)]
  refine congrArg
    (fun k => (cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega)) k) ?_
  exact crl_iso_exp h a

/-- **CRL-3b: ★明示同一視 Ξ = crlIso : T̂ → T**（成分ごと cmuMap=crrIso）。 -/
def crlIso : Hom crlLimit tmzLimit where
  map := fun y => ⟨fun n =>
      cmuMap (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega)) (y.val n), by
    intro a b hab
    show (tmzT hab).map
          (cmuMap (cycMuStd (3 ^ (b + 1)) (zpu_pow_pos (b + 1))) (cmrMu (b + 1) (by omega))
            (y.val b))
       = cmuMap (cycMuStd (3 ^ (a + 1)) (zpu_pow_pos (a + 1))) (cmrMu (a + 1) (by omega))
          (y.val a)
    rw [crl_iso_compat hab (y.val b), y.property hab]⟩
  map_mul := fun y z => by
    apply Subtype.ext
    funext n
    show cmuMap (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega))
          ((crlG n).mul (y.val n) (z.val n))
       = (tmzG n).mul
          (cmuMap (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega))
            (y.val n))
          (cmuMap (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega))
            (z.val n))
    exact cmuMap_mul (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega))
      rfl (y.val n) (z.val n)

/-- **CRL-3c: Ξ⁻¹ の遷移整合（逆向き・cast 簿記）** — 逆向き成分同型
    `cmuMap (cmrMu (j+1)) (cycMuStd (3^{j+1}))` が遷移 `tmzT`/`crlT` の四角を可換に
    する。μ 側の `cmuMap` は `cycStd_pow`（生成元の冪＝class）を経て ℤ/3^{j+1} の Quot へ
    落ち、`tmz_find_pow` の周期性と `cycRig_nat_mod_dvd`＋`Quot.sound` で合流する。 -/
theorem crl_inv_compat {i j : Nat} (h : i ≤ j) (y : (tmzG j).carrier) :
    (crlT h).map
        (cmuMap (cmrMu (j + 1) (by omega)) (cycMuStd (3 ^ (j + 1)) (zpu_pow_pos (j + 1))) y)
      = cmuMap (cmrMu (i + 1) (by omega)) (cycMuStd (3 ^ (i + 1)) (zpu_pow_pos (i + 1)))
          ((tmzT h).map y) := by
  have hcmu : cmuMap (cmrMu (j + 1) (by omega)) (cycMuStd (3 ^ (j + 1)) (zpu_pow_pos (j + 1))) y
      = Quot.mk (modCong (3 ^ (j + 1))).rel ((ctmFind (j + 1) (by omega) y.val : Nat) : Int) :=
    cycStd_pow (3 ^ (j + 1)) (ctmFind (j + 1) (by omega) y.val)
  have hfind : ctmFind (i + 1) (by omega) ((tmzT h).map y).val
      = ctmFind (j + 1) (by omega) y.val % 3 ^ (i + 1) := by
    show ctmFind (i + 1) (by omega)
          ((cmrGrp (i + 1) (by omega)).pow (cmrZeta (i + 1) (by omega))
            (ctmFind (j + 1) (by omega) y.val)).val
       = ctmFind (j + 1) (by omega) y.val % 3 ^ (i + 1)
    rw [cmr_pow_zeta (i + 1) (by omega) (ctmFind (j + 1) (by omega) y.val)]
    exact tmz_find_pow (i + 1) (by omega) (ctmFind (j + 1) (by omega) y.val)
  have hcmu2 : cmuMap (cmrMu (i + 1) (by omega)) (cycMuStd (3 ^ (i + 1)) (zpu_pow_pos (i + 1)))
        ((tmzT h).map y)
      = Quot.mk (modCong (3 ^ (i + 1))).rel
          ((ctmFind (i + 1) (by omega) ((tmzT h).map y).val : Nat) : Int) :=
    cycStd_pow (3 ^ (i + 1)) (ctmFind (i + 1) (by omega) ((tmzT h).map y).val)
  have hL : (crlT h).map
        (cmuMap (cmrMu (j + 1) (by omega)) (cycMuStd (3 ^ (j + 1)) (zpu_pow_pos (j + 1))) y)
      = Quot.mk (modCong (3 ^ (i + 1))).rel ((ctmFind (j + 1) (by omega) y.val : Nat) : Int) := by
    rw [hcmu]; rfl
  have hR : cmuMap (cmrMu (i + 1) (by omega)) (cycMuStd (3 ^ (i + 1)) (zpu_pow_pos (i + 1)))
        ((tmzT h).map y)
      = Quot.mk (modCong (3 ^ (i + 1))).rel
          ((ctmFind (j + 1) (by omega) y.val % 3 ^ (i + 1) : Nat) : Int) := by
    rw [hcmu2, hfind]
  rw [hL, hR]
  apply Quot.sound
  exact cycRig_nat_mod_dvd (3 ^ (i + 1)) (ctmFind (j + 1) (by omega) y.val)
      (ctmFind (j + 1) (by omega) y.val % 3 ^ (i + 1))
      (Nat.mod_mod_of_dvd (ctmFind (j + 1) (by omega) y.val) (Nat.dvd_refl (3 ^ (i + 1)))).symm

/-- **CRL-3d: Ξ⁻¹ = crlInv : T → T̂**（成分ごと逆向き cmuMap）。 -/
def crlInv : Hom tmzLimit crlLimit where
  map := fun y => ⟨fun n =>
      cmuMap (cmrMu (n + 1) (by omega)) (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (y.val n), by
    intro a b hab
    show (crlT hab).map
          (cmuMap (cmrMu (b + 1) (by omega)) (cycMuStd (3 ^ (b + 1)) (zpu_pow_pos (b + 1)))
            (y.val b))
       = cmuMap (cmrMu (a + 1) (by omega)) (cycMuStd (3 ^ (a + 1)) (zpu_pow_pos (a + 1)))
          (y.val a)
    rw [crl_inv_compat hab (y.val b), y.property hab]⟩
  map_mul := fun y z => by
    apply Subtype.ext
    funext n
    show cmuMap (cmrMu (n + 1) (by omega)) (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1)))
          ((tmzG n).mul (y.val n) (z.val n))
       = (crlG n).mul
          (cmuMap (cmrMu (n + 1) (by omega)) (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1)))
            (y.val n))
          (cmuMap (cmrMu (n + 1) (by omega)) (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1)))
            (z.val n))
    exact cmuMap_mul (cmrMu (n + 1) (by omega)) (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1)))
      rfl (y.val n) (z.val n)

/-- **CRL-3e: 左逆** Ξ⁻¹∘Ξ = id（成分ごと `cid_iso_leftinv`）。 -/
theorem crl_iso_leftinv (y : crlLimit.carrier) : crlInv.map (crlIso.map y) = y := by
  apply Subtype.ext
  funext n
  show cmuMap (cmrMu (n + 1) (by omega)) (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1)))
        (cmuMap (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega))
          (y.val n))
     = y.val n
  exact cid_iso_leftinv (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega))
    rfl (y.val n)

/-- **CRL-3f: 右逆** Ξ∘Ξ⁻¹ = id（成分ごと `cid_iso_rightinv`）。 -/
theorem crl_iso_rightinv (y : tmzLimit.carrier) : crlIso.map (crlInv.map y) = y := by
  apply Subtype.ext
  funext n
  show cmuMap (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega))
        (cmuMap (cmrMu (n + 1) (by omega)) (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1)))
          (y.val n))
     = y.val n
  exact cid_iso_rightinv (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega))
    rfl (y.val n)

/-- **CRL-3g: ★Ξ の G-同変性** — Ξ(σ_s y) = σ_s(Ξ y)（成分ごと `crr_iso_equivariant`
    ＝ M443F `cid_galois_equivariant` の実主語適用）。復元側 G 作用 `crlActHom` と実側
    Galois 作用 `tmzActHom` が Ξ で交換する。 -/
theorem crl_iso_equivariant (s : ctlProfinite.carrier) (y : crlLimit.carrier) :
    crlIso.map ((crlActHom s).map y) = (tmzActHom s).map (crlIso.map y) := by
  apply Subtype.ext
  funext n
  show cmuMap (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega))
        (zmodMul (3 ^ (n + 1)) ((cgarRecChar (n + 1) (by omega)).chi (s.val n)) (y.val n))
     = ((cgarAct (n + 1) (by omega)).act (s.val n)).map
        (cmuMap (cycMuStd (3 ^ (n + 1)) (zpu_pow_pos (n + 1))) (cmrMu (n + 1) (by omega))
          (y.val n))
  exact crr_iso_equivariant (n + 1) (by omega) (s.val n) (y.val n)

end IUT
